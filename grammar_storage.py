"""Save and restore computed levels and ambiguity findings."""

import json
import os
from pathlib import Path
import sqlite3
import tempfile

import grammar_engine as implementation


def _json(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), allow_nan=False)


def _open_snapshot(path):
    return sqlite3.connect(Path(path).resolve().as_uri() + "?mode=ro", uri=True)


def _metadata(connection):
    row = connection.execute("SELECT payload FROM metadata").fetchone()
    if row is None:
        raise ValueError("Snapshot has no metadata")
    return json.loads(row[0])


def save_snapshot(path, grammar, records, metadata):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f"{path.name}.{os.getpid()}.", suffix=".tmp", dir=path.parent)
    os.close(descriptor)
    connection = None
    try:
        connection = sqlite3.connect(temporary)
        connection.executescript("""
            CREATE TABLE metadata (payload TEXT NOT NULL);
            CREATE TABLE nodes (id INTEGER PRIMARY KEY, accepting INTEGER NOT NULL,
                                size TEXT NOT NULL, edges TEXT NOT NULL);
            CREATE TABLE roots (name TEXT PRIMARY KEY, node_id INTEGER NOT NULL);
            CREATE TABLE findings (id TEXT PRIMARY KEY, position INTEGER NOT NULL,
                                   owner TEXT, kind TEXT, payload TEXT NOT NULL);
            CREATE INDEX findings_owner ON findings(owner, position);
            CREATE UNIQUE INDEX findings_position ON findings(position);
        """)
        connection.execute("INSERT INTO metadata VALUES (?)", (_json(metadata),))
        identities = {}
        rows = []
        for nonterminal in grammar.nonterminals:
            root = nonterminal.next.trie.root
            if root not in identities:
                pending = [(root, iter(root.children.values()))]
                while pending:
                    node, children = pending[-1]
                    child = next(children, None)
                    if child is not None:
                        if child not in identities:
                            pending.append((child, iter(child.children.values())))
                        continue
                    pending.pop()
                    node_id = len(identities) + 1
                    identities[node] = node_id
                    edges = [[symbol, identities[child]] for symbol, child in node.children.items()]
                    rows.append((node_id, int(node.accepting), str(node.size), _json(edges)))
                    if len(rows) >= 512:
                        connection.executemany("INSERT INTO nodes VALUES (?, ?, ?, ?)", rows)
                        rows.clear()
            connection.execute("INSERT INTO roots VALUES (?, ?)", (_json(nonterminal.name), identities[root]))
        if rows:
            connection.executemany("INSERT INTO nodes VALUES (?, ?, ?, ?)", rows)
        for position, record in enumerate(records):
            record = dict(record)
            record.setdefault("id", position)
            owner = record.get("owner", record.get("nonterminal"))
            connection.execute("INSERT INTO findings VALUES (?, ?, ?, ?, ?)", (
                str(record["id"]), position, _json(owner), record.get("kind"), _json(record),
            ))
        connection.commit()
        connection.close()
        connection = None
        os.replace(temporary, path)
        return metadata
    finally:
        if connection is not None:
            connection.close()
        for candidate in (temporary, temporary + "-journal", temporary + "-wal", temporary + "-shm"):
            try:
                os.unlink(candidate)
            except FileNotFoundError:
                pass


def read_summary(path):
    connection = _open_snapshot(path)
    try:
        return _metadata(connection)
    finally:
        connection.close()


def load_languages(path, grammar):
    connection = _open_snapshot(path)
    try:
        metadata = _metadata(connection)
        roots = dict(connection.execute("SELECT name, node_id FROM roots"))
        expected = {_json(nonterminal.name) for nonterminal in grammar.nonterminals}
        if set(roots) != expected:
            raise ValueError("Snapshot nonterminals do not match this grammar")
        nodes = {}
        for node_id, accepting, size, edges in connection.execute("SELECT id, accepting, size, edges FROM nodes ORDER BY id"):
            children = {symbol: nodes[child_id] for symbol, child_id in json.loads(edges)}
            node = implementation.TrieNode(children, bool(accepting))
            if node.size != int(size):
                raise ValueError("Snapshot trie count is inconsistent")
            nodes[node_id] = node
        languages = []
        for nonterminal in grammar.nonterminals:
            language = implementation.Language()
            language._sentences = implementation.Trie._from_root(nodes[roots[_json(nonterminal.name)]])
            languages.append(language)
        level = metadata["level"]
        for nonterminal, language in zip(grammar.nonterminals, languages):
            nonterminal.previous = implementation.Language()
            nonterminal.next = language
        grammar.iteration = level
        grammar.findings = []
        return metadata
    finally:
        connection.close()


def read_findings(path):
    """Every finding record saved with a level, in the order found."""
    connection = _open_snapshot(path)
    try:
        return [json.loads(row[0]) for row in connection.execute("SELECT payload FROM findings ORDER BY position")]
    finally:
        connection.close()
