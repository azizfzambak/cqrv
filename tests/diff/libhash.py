"""Revision R5 (REVIEW_RESPONSE_1 §4; DECISIONS.md 2026-11-16) — the library hash `hashes.library`, mirrored,
and the freshness check of the committed certificates and manifests.

  python -I tests/diff/libhash.py [--release] [--print]

`library_hash(root)` mirrors `CQRV.Certify.libraryHash` over `CQRV.Certify.Audit.libraryFiles`: SHA3-256 of
`path ‖ 0x00 ‖ hex(SHA3-256(content)) ‖ 0x0A` for every `.lean` file under `CQRV/` and `Apps/` plus
`lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, sorted by path (UTF-8 byte order, `/` separators,
relative to the project root), the content as bytes. `mod_library(text)` is `Certify.certJsonModLibrary`:
the certificate.json bytes with the value of `hashes.library` replaced by `null` — the form the hardware
files hash (`certificate_json_sha3_mod_library`).

As a script (CI step "cqr certify", `scripts/check_certify.sh`): every `examples/certs/*/certificate.json`
and `examples/certs/*/manifest.json` must record the hash of the current tree. A stale hash is a WARNING
(exit 0) by default — the certificate was checked against an earlier library; `cqr certify` re-checks it —
and an error (exit 1) with `--release` (`CQRV_RELEASE=1 scripts/check_certify.sh`): at a release every
recorded hash is current. The artifacts of `hw/artifacts/` carry no library hash (their `certificate_json`
is the historical full hash of the certificate they were transpiled from).
"""
import argparse
import glob
import hashlib
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RE_LIBRARY = re.compile(rb'"library":"[0-9a-f]{64}"')


def sha3(data):
    return hashlib.sha3_256(data).hexdigest()


def library_files(root=ROOT):
    """(path, bytes) for the files of the hash, paths relative to `root` with `/`."""
    out = []
    for top in ("CQRV", "Apps"):
        for dirpath, _, files in os.walk(os.path.join(root, top)):
            for f in files:
                if f.endswith(".lean"):
                    p = os.path.join(dirpath, f)
                    out.append((os.path.relpath(p, root).replace(os.sep, "/"), open(p, "rb").read()))
    for f in ("lakefile.lean", "lean-toolchain", "lake-manifest.json"):
        out.append((f, open(os.path.join(root, f), "rb").read()))
    return out


def library_hash(root=ROOT):
    files = sorted(library_files(root), key=lambda pc: pc[0].encode("utf-8"))
    pre = b"".join(p.encode("utf-8") + b"\x00" + sha3(c).encode("ascii") + b"\n" for p, c in files)
    return sha3(pre)


def mod_library(text):
    """certificate.json bytes with `hashes.library` set to null (exactly one occurrence replaced)."""
    out, k = RE_LIBRARY.subn(b'"library":null', text)
    return out if k == 1 else text


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--release", action="store_true", help="a stale recorded hash is an error, not a warning")
    ap.add_argument("--print", action="store_true", help="print the current tree's hash and exit")
    a = ap.parse_args()
    current = library_hash()
    if a.print:
        print(current)
        return 0
    files = sorted(glob.glob(os.path.join(ROOT, "examples", "certs", "*", "certificate.json")) +
                   glob.glob(os.path.join(ROOT, "examples", "certs", "*", "manifest.json")))
    stale, missing = [], []
    for f in files:
        rel = os.path.relpath(f, ROOT).replace(os.sep, "/")
        h = json.load(open(f, encoding="utf-8")).get("hashes", {}).get("library")
        if h is None:
            missing.append(rel)
        elif h != current:
            stale.append(rel)
    for rel in missing:
        print(f"libhash: {rel}: no hashes.library")
    for rel in stale:
        print(f"libhash: {'ERROR' if a.release else 'WARNING'}: {rel}: hashes.library is not the current tree's "
              f"(regenerate with its generator; `--release` makes this blocking)")
    n = len(files) - len(stale) - len(missing)
    print(f"libhash: tree {current[:16]}...; {n} of {len(files)} committed certificates and manifests record it"
          f"{'; ' + str(len(stale)) + ' stale' if stale else ''}{'; ' + str(len(missing)) + ' without' if missing else ''}")
    if missing or (stale and a.release):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
