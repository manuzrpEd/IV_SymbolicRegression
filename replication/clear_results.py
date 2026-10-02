"""Remove, or move aside, the committed experiment results so that the chain of REPLICATION.md §5.4 starts from scratch.

    python replication/clear_results.py                                  # list the files, change nothing
    python replication/clear_results.py --yes                            # delete them
    python replication/clear_results.py --move-to replication/reference  # move them, keeping the experiments/phaseN/ layout

Every experiment script skips the runs already in its output file, so with the committed results in place a rerun does
nothing. The committed copies stay in git: `git checkout -- experiments` restores them.
"""

from __future__ import annotations

import argparse
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PATTERNS = ("*.jsonl", "*.json", "*.md", "*.png")


def result_files() -> list[Path]:
    dirs = sorted(d for d in ROOT.glob("experiments/phase*") if d.is_dir())
    return sorted(p for d in dirs for pat in PATTERNS for p in d.glob(pat))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--yes", action="store_true", help="delete the files")
    parser.add_argument("--move-to", type=Path, help="move the files under this directory instead of deleting them")
    args = parser.parse_args()
    files = result_files()
    for p in files:
        print(p.relative_to(ROOT))
    print(f"{len(files)} files")
    if args.move_to:
        for p in files:
            dest = args.move_to / p.relative_to(ROOT)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.move(str(p), str(dest))
        print(f"moved under {args.move_to}")
    elif args.yes:
        for p in files:
            p.unlink()
        print("deleted; `git checkout -- experiments` restores the committed copies")
    else:
        print("nothing changed: pass --yes to delete, or --move-to DIR to move")


if __name__ == "__main__":
    main()
