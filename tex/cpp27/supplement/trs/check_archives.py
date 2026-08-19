#!/usr/bin/env python3
"""Check the shipped TRS against the archived AProVE proofs.

The proofs in out/ were run on an EARLIER, LARGER rule set (79 first-order
rules).  Rules have since been removed, never added, so:

  * SN is inherited -- a subset of a terminating system terminates;
  * WCR is machine-checked by Agda (--local-confluence-check, 0 pairs);
  * Newman's lemma then gives CR for the shipped system.

The one thing that argument needs is that every shipped rule really does
occur, verbatim, in the archived proofs.  That is what this script checks,
so the claim does not rest on a memory of having looked.

    python3 check_archives.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# The archives in out/ keep their original file names, and their text says
# "proof of sigma-fcr.trs": they are the artefacts AProVE produced, and
# renaming them would misrepresent what was run.  The generated input is now
# systemf.trs; only the name changed, which is why the rule texts below still
# match.
#
# Two layouts: this repository (coco/systemf.trs + coco/out/*.txt) and the
# submitted supplement (trs/systemf.trs + trs/{termination,confluence}-aprove.txt).
LAYOUTS = [
    (os.path.join(HERE, "systemf.trs"),
     [("termination", os.path.join(HERE, "out", "sigma-fcr.SN.PROOF.txt")),
      ("confluence", os.path.join(HERE, "out", "sigma-fcr.CR.solvers.txt"))]),
    (os.path.join(HERE, "systemf.trs"),
     [("termination", os.path.join(HERE, "termination-aprove.txt")),
      ("confluence", os.path.join(HERE, "confluence-aprove.txt"))]),
]


def layout() -> tuple[str, list[tuple[str, str]]]:
    for trs, archives in LAYOUTS:
        if os.path.exists(trs) and all(os.path.exists(a) for _, a in archives):
            return trs, archives
    raise SystemExit("check_archives.py: found neither the repository layout "
                     "(out/sigma-fcr.SN.PROOF.txt) nor the supplement layout "
                     "(termination-aprove.txt) next to this script.")


def rules_of(path: str) -> list[str]:
    body = re.search(r"\(RULES(.*?)\n\)", open(path).read(), re.S)
    if body is None:
        raise SystemExit("no (RULES ...) block in " + path)
    return [re.sub(r"\s+", "", ln.strip())
            for ln in body.group(1).split("\n") if "->" in ln.strip()]


def main() -> int:
    trs, archives = layout()
    shipped = rules_of(trs)
    bad = 0
    for label, path in archives:
        blob = re.sub(r"\s+", "", open(path).read())
        missing = [r for r in shipped if r not in blob]
        print("%-12s %-34s %d/%d present" %
              (label, os.path.basename(path), len(shipped) - len(missing),
               len(shipped)))
        for r in missing:
            print("    MISSING:", r)
        bad += len(missing)
    print("OK: the shipped system is a subset of both archived proofs"
          if not bad else "FAILED: %d rule(s) not in an archive" % bad)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
