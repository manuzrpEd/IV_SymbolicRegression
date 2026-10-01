"""Download the two public data files of the applications (README §8.3) into data/ (git-ignored).

    python experiments/fetch_data.py            # both files; skips what is already there
    python experiments/fetch_data.py --only ak   # or --only engel

- ak91.dta: the Mastering 'Metrics extract of Angrist & Krueger (1991), from masteringmetrics.com (329,509 men).
- engel95.csv: the `Engel95` data frame of the R package `np` (CRAN, GPL): Blundell, Chen & Kristensen's (2007)
  FES 1995 sample, 1,655 couples. The CRAN source tarball is downloaded, np/data/Engel95.rda extracted and read
  with pyreadr. If the pinned version has left CRAN, pass --np-version with the current one.

Neither file is redistributed with this repository; both are third-party data under their own terms.
"""

from __future__ import annotations

import argparse
import tarfile
import urllib.request
from pathlib import Path

DATA = Path(__file__).parent.parent / "data"
AK_URL = "https://www.masteringmetrics.com/wp-content/uploads/2015/02/ak91.dta"
NP_VERSION = "0.70-5"


def fetch(url: str, dest: Path) -> None:
    print(f"downloading {url}", flush=True)
    with urllib.request.urlopen(url, timeout=120) as r, dest.open("wb") as f:
        f.write(r.read())


def fetch_ak() -> None:
    dest = DATA / "ak91.dta"
    if dest.exists():
        print(f"{dest} exists")
        return
    fetch(AK_URL, dest)


def fetch_engel(version: str) -> None:
    dest = DATA / "engel95.csv"
    if dest.exists():
        print(f"{dest} exists")
        return
    import pyreadr

    tgz = DATA / f"np_{version}.tar.gz"
    if not tgz.exists():
        try:
            fetch(f"https://cran.r-project.org/src/contrib/np_{version}.tar.gz", tgz)
        except Exception:  # older versions move to the archive
            fetch(f"https://cran.r-project.org/src/contrib/Archive/np/np_{version}.tar.gz", tgz)
    with tarfile.open(tgz) as tar:
        member = tar.getmember("np/data/Engel95.rda")
        member.name = "Engel95.rda"
        tar.extract(member, DATA)
    df = pyreadr.read_r(str(DATA / "Engel95.rda"))["Engel95"]
    df.to_csv(dest, index=False)
    print(f"wrote {dest}: {df.shape[0]} rows, columns {list(df.columns)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--only", choices=["ak", "engel"])
    parser.add_argument("--np-version", default=NP_VERSION)
    args = parser.parse_args()
    DATA.mkdir(exist_ok=True)
    if args.only in (None, "ak"):
        fetch_ak()
    if args.only in (None, "engel"):
        fetch_engel(args.np_version)


if __name__ == "__main__":
    main()
