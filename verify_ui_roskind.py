import json
from pathlib import Path
import time
from urllib.parse import urlencode
from urllib.request import Request, urlopen


BASE = "http://127.0.0.1:8765"


def request(path, data=None):
    body = None if data is None else json.dumps(data).encode()
    with urlopen(Request(BASE + path, data=body, headers={"Content-Type": "application/json"}), timeout=120) as response:
        return json.load(response)


def finished(level):
    started = time.monotonic()
    while time.monotonic() - started < 600:
        state = request("/api/state")
        if state["status"] != "computing":
            return state
        time.sleep(0.2)
    raise AssertionError(f"Level {level} timed out")


def main():
    state = request("/api/session", {"grammar": "roskind", "memory_limit_mb": 2048})
    for level in range(state["completed_level"] + 1, 6):
        request("/api/advance", {"level": level})
        state = finished(level)
        assert state["status"] == "idle", state
        assert state["completed_level"] == level, state
        item = state["levels"][-1]
        print(json.dumps({"level": level, "seconds": item["seconds"],
                          "findings": item["findings_count"], "memory_bytes": item["memory_bytes"]}), flush=True)
    state = request("/api/state")
    fifth = state["levels"][5]
    assert fifth["findings_count"] == 2, fifth
    assert sum(int(size) for size in fifth["counts"].values()) == 9214018664
    total = int(fifth["counts"]["postfix_expression"])
    page = request("/api/approximation?" + urlencode({"level": 5, "nonterminal": "postfix_expression", "offset": total - 3, "limit": 3}))
    assert len(page["items"]) == 3 and not page["has_more"] and int(page["total"]) == total
    kinds = {}
    sources = {}
    for offset in (0, 50):
        findings = request(f"/api/findings?level=5&offset={offset}&limit=50")
        for item in findings["items"]:
            proof = request("/api/proof?" + urlencode({"id": item["id"]}))
            assert proof["verified"] and proof["production_ids"] and len(proof["derivations"]) >= 2
            kinds[proof["kind"]] = kinds.get(proof["kind"], 0) + 1
            sources.setdefault(proof["owner"], set()).update(proof["production_ids"])
    assert sum(kinds.values()) == 2
    request("/api/settings", {"memory_limit_mb": 64})
    for _ in range(8):      # the languages grow fast, so one of the next levels exceeds 64 MiB
        request("/api/advance", {"level": state["completed_level"] + 1})
        limited = finished(state["completed_level"] + 1)
        if limited["status"] != "idle":
            break
        state = limited
    assert limited["status"] == "limited" and limited["completed_level"] == state["completed_level"], limited
    after = request("/api/approximation?" + urlencode({"level": 5, "nonterminal": "postfix_expression", "offset": total - 3, "limit": 3}))
    assert page == after
    request("/api/settings", {"memory_limit_mb": 2048})
    result = {"verified_level": 5, "findings": kinds,
              "sources": {name: sorted(ids) for name, ids in sources.items()},
              "deep_page_total": str(total), "deep_page_ranks": [row["rank"] for row in page["items"]],
              "memory_stop_preserved_snapshot": True, "level5_seconds": fifth["seconds"],
              "level5_memory_bytes": fifth["memory_bytes"]}
    Path("ui_artifacts").mkdir(exist_ok=True)
    Path("ui_artifacts/roskind-verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
