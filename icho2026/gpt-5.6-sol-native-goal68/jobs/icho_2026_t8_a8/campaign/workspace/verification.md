# Verification record for `icho_2026_t8_a8`

All commands were run from:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t8_a8/campaign/workspace`

## Source identity

Command:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T8_page-4.png icho_2026_source/image/T8_page-3.png
```

Result (exit status 0):

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
55fc19db05fe771eb0403d5fcf611d83ff5a22882b1221129ef689bd8704285a  icho_2026_source/image/T8_page-4.png
d6431350f32953011648ffe537d8d51ed7dc9dfb5a437a6f1c94620d6041055f  icho_2026_source/image/T8_page-3.png
```

These match the hashes recorded in `TASK.json`.

PDF text-layer probe command:

```text
python3 -c "import pymupdf; pdf=pymupdf.open('icho_2026_source/raw/theory_problem.pdf'); keys=('Q8-3','Q8-4','A8-6','8.8','N','R','G','B'); [print(f'page {n}: {[s for s in keys if s in pdf[n-1].get_text(\"text\")]}') for n in (74,75,82)]"
```

Result (exit status 0):

```text
page 74: ['Q8-3', 'N', 'G']
page 75: ['Q8-4', '8.8', 'N', 'R', 'G', 'B']
page 82: ['A8-6', '8.8', 'N', 'R', 'G', 'B']
```

The two question images were visually inspected. Pages 75 and 82 of the
original PDF were separately rendered and visually inspected: page 75
reproduces Q8-4, and page 82 (A8-6) is the blank 8.8 student answer table with
rows `a,b,c,d` and columns `N,R,G,B`.

## Lean compile and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t8_a8.lean
```

Result (exit status 0):

```text
'IChO2026Problems.T8A8.answer_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T8A8.correspondence_unique' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T8A8.condition_a' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T8A8.condition_b' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T8A8.condition_c' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T8A8.condition_d' depends on axioms: [propext, Quot.sound]
```

The `#print axioms` commands are part of the checked Lean source. The output
contains only standard Lean logical axioms and no `sorryAx` or custom axiom.

## Shortcut and formatting checks

Commands:

```text
grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t8_a8.lean
! grep -nE '[[:blank:]]+$|^(<<<<<<<|=======|>>>>>>>)' answer.md verification.md result.json IChO2026Problems/problem_icho_2026_t8_a8.lean
python3 -m json.tool result.json >/dev/null
```

Final result: the first command exits with status 1 and emits no matches (which
is the expected result for a negative `grep`); the second and third commands
exit with status 0 and emit no output. Thus there are no forbidden proof
shortcuts, no trailing-whitespace/conflict-marker errors, and `result.json` is
valid JSON. (`git diff --check` is inapplicable because this isolated workspace
has no Git repository.)
