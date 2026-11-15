"""Parse text, apply NSF CACC repairs, approximate with detection, and report.

This file owns command-line and file handling. The four stages in main() call
modules with the same responsibilities; all verdicts concern the grammar
returned by the repair stage.
"""

import argparse
import os
from pathlib import Path
import sys
import tempfile

from parse import parse_grammar
from repair import repair_caccs
from approximate_and_detect import approximate_and_detect
from report import build_report, render_text


DEFAULT_LEVEL = 6
UNREADABLE, FAILED = 2, 4


class InputError(Exception):
    """The BNF file cannot be read or parsed."""


def read_grammar(path):
    try:
        return parse_grammar(Path(path).read_text(encoding="utf-8-sig"))
    except OSError as error:
        raise InputError(f"Can't read {path}: {error.strerror or error}") from None
    except UnicodeDecodeError:
        raise InputError(f"{path} isn't UTF-8 text") from None
    except ValueError as error:
        raise InputError(str(error)) from None


def check_output_path(path, source):
    """Keep a report from replacing its grammar input."""
    if path.resolve() == source.resolve() or (path.exists() and source.exists() and path.samefile(source)):
        raise ValueError(f"the report would overwrite input file {source}")


def save_report(path, text, source):
    """Write UTF-8 beside the destination and replace it only after success."""
    check_output_path(path, source)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
                                         prefix=f".{path.name}.", suffix=".tmp",
                                         dir=path.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        check_output_path(path, source)
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def positive_level(text):
    try:
        level = int(text)
    except ValueError:
        raise argparse.ArgumentTypeError(f"not an integer: {text}") from None
    if level < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return level


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="check_grammar.py",
        description="Parse BNF, apply NSF CACC repairs, approximate with ambiguity detection, and write a report.")
    parser.add_argument("grammar", metavar="FILE", help="BNF grammar text file")
    parser.add_argument("-o", "--output", metavar="FILE",
                        help="report file (default: <stem>.ambiguity.txt beside the grammar)")
    parser.add_argument("--level", type=positive_level, default=DEFAULT_LEVEL,
                        help=f"check the repaired grammar up to this parse-tree height (default {DEFAULT_LEVEL})")
    args = parser.parse_args(argv)
    if args.grammar == "-" or args.output == "-":
        parser.error("name input and output files; '-' streams are not supported")

    def say(message):
        print(f"check_grammar: {message}", file=sys.stderr, flush=True)

    try:
        source = Path(args.grammar)
        try:
            output = Path(args.output) if args.output is not None else source.with_suffix(".ambiguity.txt")
            check_output_path(output, source)
        except (OSError, ValueError) as error:
            say(f"Can't choose report output: {error}")
            return FAILED
        try:
            original = read_grammar(args.grammar)
        except InputError as error:
            say(str(error))
            return UNREADABLE
        try:
            repairs = repair_caccs(original)
            approximation = approximate_and_detect(repairs.grammar, args.level)
            report = build_report(args.grammar, original, repairs, approximation)
            text = render_text(report)
        except (RuntimeError, ValueError, MemoryError) as error:
            say(f"The run failed: {error}")
            return FAILED
        try:
            save_report(output, text, source)
        except (OSError, ValueError) as error:
            say(f"Can't write report to {output}: {error}")
            return FAILED
    except KeyboardInterrupt:
        say("Interrupted; no partial report was written.")
        return 130
    say(f"report saved to {output}")
    return report["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
