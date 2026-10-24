"""Runs scripts/CertifyTool.lean (`lake env lean --run`, after `lake build`) for the Stage 8a
tests: Lean's SHA3-256 and the sample certificate (report §8.4.2, §9.5.3)."""

import os
import shutil
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TOOL = os.path.join("scripts", "CertifyTool.lean")


def certify_tool(args, stdin=None):
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("lake not on PATH")
    p = subprocess.run([lake, "env", "lean", "--run", TOOL, *args], cwd=ROOT, input=stdin,
                       capture_output=True, text=True, encoding="utf-8")
    if p.returncode != 0:
        raise SystemExit(f"CertifyTool {' '.join(args)} failed ({p.returncode}): {p.stderr}")
    return p.stdout
