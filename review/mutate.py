"""Mutation test: every plausible bug in a checker must be caught by an `example`.

For each mutation, the module is copied with the theorems removed (so only the
`example ... := by decide` traps can catch the bug), one definition is mutated,
and the copy is compiled. A mutation that still compiles is a hole in the traps.

Usage (from the repo root):
    python3 review/mutate.py
Exit status 1 if any mutation survives.
"""
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
LAKE = pathlib.Path.home() / ".elan/bin/lake"

# file -> (regions to drop as (start_marker, end_marker), mutations as name -> (old, new))
SUITES = {
    "AatLean/Chain.lean": (
        [("/-! ## Связь Bool-проверок", "/-! ## Теоремы-ловушки"),
         ("/-- Общая ловушка", "end AAT")],
        {
            "checkPairs skips a pair": (
                "narrowsB p c && linkedB p c && checkPairs (c :: rest)",
                "narrowsB p c && linkedB p c && checkPairs rest"),
            "checkPairs checks only the last pair": (
                "  | p :: c :: rest => narrowsB p c && linkedB p c && checkPairs (c :: rest)\n",
                "  | p :: c :: rest =>\n    match rest with\n"
                "    | [] => narrowsB p c && linkedB p c\n"
                "    | _  => checkPairs (c :: rest)\n"),
            "narrowsB direction flipped": (
                "child.tools.all (fun x => parent.tools.contains x)",
                "parent.tools.all (fun x => child.tools.contains x)"),
            "narrowsB accepts a shorter child": (
                "child.tools.all (fun x => parent.tools.contains x)",
                "child.tools.all (fun x => parent.tools.contains x) ||\n"
                "    decide (child.tools.length < parent.tools.length)"),
            "linkedB always true": (
                "child.issuer == parent.holder\n", "true\n"),
            "linkedB also matches parent.issuer": (
                "child.issuer == parent.holder\n",
                "child.issuer == parent.holder || child.issuer == parent.issuer\n"),
            "root trust not checked": (
                "if trustedRoots.contains root.issuer && checkPairs chain",
                "if checkPairs chain"),
            "empty chain allowed": (
                "  | [] => .deny\n  | root :: _ =>", "  | [] => .allow\n  | root :: _ =>"),
        },
    ),
    "AatLean/CMap.lean": (
        [("/-! ## 3. Корректность", "/-! ## 4. Ловушки")],
        {
            "6b: closed world ignored": (
                "    | none   => m.star) &&", "    | none   => true) &&"),
            "6b: required args not checked": (
                "    | some e => e.optional || argsHas args k\n",
                "    | some _ => true\n"),
            "6b: named value not checked": (
                "    | some e => check e.c v\n", "    | some _ => true\n"),
            "norm: empty map stays closed": (
                "if m.named.isEmpty && !m.star then { m with star := true } else m", "m"),
            "4p2: child may name any key": (
                "c.named.all (fun (k, _) => (p.get k).isSome || p.star) &&", "true &&"),
            "4p2: child may omit required key": (
                "(c.get k).isSome || (pe.optional && !c.star)", "true"),
            "4p2: omit optional ignores child star": (
                "(c.get k).isSome || (pe.optional && !c.star)", "(c.get k).isSome || pe.optional"),
            "4p2: child may add star": (
                "(!c.star || p.star) &&", "true &&"),
            "4p3: required may become optional": (
                "    | some pe => pe.optional || !ce.optional\n", "    | some _ => true\n"),
            "4p4: constraint not compared": (
                "    | some pe => subsumes pe.c ce.c\n", "    | some _ => true\n"),
        },
    ),
    "AatLean/Constraint.lean": (
        [("/-! ## 3. Корректность", "/-! ## 4. Свидетель")],
        {
            "exact always matches": (
                "  | .exact v, .exact w => w == v\n", "  | .exact _, .exact _ => true\n"),
            "child wildcard accepted under any parent": (
                "  | _, _ => false\n", "  | _, .wildcard => true\n  | _, _ => false\n"),
            "empty child one_of allowed": (
                "!cv.isEmpty && cv.all pv.contains", "cv.all pv.contains"),
            "one_of subset direction flipped": (
                "!cv.isEmpty && cv.all pv.contains", "!cv.isEmpty && pv.all cv.contains"),
            "exact under one_of ignores membership": (
                "  | .oneOf pv, .exact w => pv.contains w\n", "  | .oneOf _, .exact _ => true\n"),
            "range -> exact ignores bounds": (
                "  | .range plo phi, .exact (.num x) => check (.range plo phi) (.num x)\n",
                "  | .range _ _, .exact (.num _) => true\n"),
            "range -> exact accepts non-numbers": (
                "  | .range plo phi, .exact (.num x) => check (.range plo phi) (.num x)\n",
                "  | .range plo phi, .exact (.num x) => check (.range plo phi) (.num x)\n"
                "  | .range _ _, .exact _ => true\n"),
            "equal bound: inclusive child under exclusive parent": (
                "| some p, some c => decide (p.val < c.val) || (decide (p.val = c.val) && (p.incl || !c.incl))",
                "| some p, some c => decide (p.val < c.val) || decide (p.val = c.val)"),
            "missing child lower bound allowed": (
                "  | some _, none => false\n  -- строго внутри",
                "  | some _, none => true\n  -- строго внутри"),
            "upper bound direction flipped": (
                "| some p, some c => decide (c.val < p.val) ||",
                "| some p, some c => decide (p.val < c.val) ||"),
            "range check accepts non-numbers": (
                "  | .range _ _, _ => false\n", "  | .range _ _, _ => true\n"),
            "exclusive lower bound treated as inclusive": (
                "if b.incl then decide (b.val ≤ x) else decide (b.val < x)",
                "decide (b.val ≤ x)"),
        },
    ),
}


def strip(src: str, regions) -> str:
    for start, end in regions:
        i = src.index(start)
        j = src.index(end, i)
        src = src[:i] + src[j:]
    if not src.rstrip().endswith("end AAT"):
        src = src.rstrip() + "\n\nend AAT\n"
    return src


def compiles(path: pathlib.Path) -> bool:
    r = subprocess.run([str(LAKE), "env", "lean", str(path)], cwd=ROOT,
                       capture_output=True, text=True)
    return r.returncode == 0


def main() -> int:
    survivors = []
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        for rel, (regions, muts) in SUITES.items():
            base = strip((ROOT / rel).read_text(), regions)
            b = tmp / "Baseline.lean"
            b.write_text(base)
            if not compiles(b):
                print(f"BASELINE FAILS for {rel}: fix the stripping markers")
                return 2
            for name, (old, new) in muts.items():
                if base.count(old) != 1:
                    print(f"  ?? {rel}: '{name}' — pattern not found exactly once")
                    survivors.append((rel, name))
                    continue
                m = tmp / "Mutant.lean"
                m.write_text(base.replace(old, new))
                caught = not compiles(m)
                print(f"  {'caught ' if caught else 'SURVIVED'}  {rel}: {name}")
                if not caught:
                    survivors.append((rel, name))
    print(f"\n{len(survivors)} surviving mutation(s)")
    return 1 if survivors else 0


if __name__ == "__main__":
    sys.exit(main())
