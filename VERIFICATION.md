# Verification report — `check-lean-claim`, Lean v4.36.0

> **Superseded 2026-11-27.** This report is of the run on Lean v4.36.0 (2026-11-25). The repository is now on Lean v4.35.0 / Mathlib v4.35.0, because Palomar's verifier supports Lean v4.35.0-rc2 to v4.35.0 only. It builds there (`lake build`, all targets, no errors), but `lake check` and `lake comparator` have not been rerun, and the tables below describe v4.36.0.

Date: 2026-11-25. Project: this repository, ported to **Lean v4.36.0** and **Mathlib v4.36.0** (`fc4f59e577fe…`). Tool: https://github.com/AdemBenAbdallah/check-lean-claim (commit `47312730b899`), which calls Lean's own `lake check` and `lake comparator`. I ran everything myself, inside Lean's `bwrap` sandbox, in scratch copies. The scratch copy that was checked is identical to the repository except for `README.md`.

## The port (from v4.30.0)

Four small source edits, no change to any statement:

| File | Change | Why |
|---|---|---|
| `MyersonSetting.lean` | `simpa [smul_eq_mul] using hint_p.smul r` → `exact hint_p.const_mul r` | smul form changed |
| `MirrleesSetting.lean` (3 places) | `convert hraw using 1; ring` → `convert hraw using 1 <;> first \| (funext x; simp) \| ring` | derivative lemma now gives `(fun x => y) / id` |
| `MasterTheorem.lean` | `noncomputable instance TR_preservesColimits` / `QR_preservesLimits` → `theorem` | newer Lean rejects instances with arguments it cannot infer (`hD`, `hθ_pos`, …) |
| `ProductDecomposition.lean` | `simpa using …` → `exact …` | `simpa` no longer closes the goal |

Plus `lean-toolchain`, `lakefile.toml` (Mathlib rev), `lake-manifest.json`, and `README.md`. The nested `docbuild/` project followed the project (v4.36.0 then; now v4.35.0 with doc-gen4 v4.35.0). The module system was not ported at the time of this run; it has been since (2026-11-27, branch `module-system`).
Plain `lake build` (all targets) passes. It prints deprecation warnings only (`dif_pos`, `if_pos`, `if_neg`, `Set.diff_singleton_eq_self`), not fixed.

## The five questions

| # | Question | Result | Evidence |
|---|---|---|---|
| 1 | Assumptions (holes, axioms) | **PASS** on the proof development; **FAIL** from `check.sh` as shipped | see below |
| 2 | The words | PASS (mechanical) | `lake comparator`: same statements as `Challenge.lean`. Only custom syntax: `Linters.lean:78`, `syntax … "witness_for" … : attr`, a new attribute name |
| 3 | The question | PASS (mechanical); independence **NOT CHECKED** | I wrote `Challenge.lean` myself, so by the tool's own rule the comparison does not show the statement is the right one |
| 4 | The run | PASS | run by me, in the sandbox, on this machine |
| 5 | The checker | PASS on the statements' closure; nanoda **NOT CHECKED** on the whole project | see below |

### Question 1: why `check.sh` as shipped says FAIL

`check.sh` runs `lake check` on the project's *default targets*. Here those are the proof development, `Challenge` and `Solution`. `lake check` puts them in one environment. `Challenge.lean` has deliberate `sorry` statements and the same declaration names as `Solution.lean` (the Palomar layout), so Lean stops with `environment already contains 'MechDesign.adj_T_Q' from Challenge`. This is a clash between the layout and the tool, not a bad axiom. The script prints "a checker rejected it" because its message matcher only knows the axiom message.

On a copy whose default targets are the proof development and `Solution` only: `lake check` **exit 0**, "Uses axioms: propext, Quot.sound, Classical.choice". `lake check --paranoid` on the same copy: see question 5.

### Question 5: kernels

| Run | Declarations | Lean default | Lean paranoid | lean4lean | con-leche | con-ron | nanoda |
|---|---|---|---|---|---|---|---|
| `lake check --paranoid` (whole project) | 404,525 | accept | accept | accept | accept | accept | **crash**: "thread has overflowed its stack" (reported as "rejected") |
| `lake comparator --paranoid` (the 8 statements; 12 after the addendum below) | 36,711 | accept | accept | accept | accept | accept | accept |

The nanoda failure is a stack overflow in the checker on a very large export, not a logical rejection. The same crash happened on Lean 4.35.0. I did not find a stack-size option.

### One statement at a time

Each advertised statement checked alone with `lake comparator --paranoid --config <one-statement.json>`, all six kernels:

| # | Statement | Closure (declarations) | Result |
|---|---|---|---|
| 1 | `masterTheorem_existence` | 36,444 | accepted |
| 2 | `masterTheorem_isomorphism` | 36,444 | accepted |
| 3 | `masterTheorem_transferInvariance` | 36,412 | accepted |
| 4 | `masterTheorem_rentExtraction` | 36,610 | accepted |
| 5 | `productDecomposition` | 36,565 | accepted |
| 6 | `revenueEquivalence` | 36,431 | accepted |
| 7 | `taxationPrinciple` | **6,479** | accepted |
| 8 | `adj_T_Q` (definition) | 36,601 | accepted |

Whole project 404,525 → about 36,500 per statement (11 times smaller). The taxation principle needs IC only, so its closure is 62 times smaller.

## What was not done

- `scripts/verify-comparator.sh` (the repository's own external pinned Comparator; needs `cargo`, `go`, `landrun`) was not run.
- Nothing is committed in the Lean repository.
- `Challenge.lean` independence (questions 2 and 3): someone other than the prover would have to write or review it.
- nanoda on the whole-project export.

## Addendum: four monotonicity statements (2026-11-25)

`MechDesigAdjointfunctor/Lean/MonotoneResults.lean` adds four elementary results, advertised in `Challenge.lean` and proved in `Solution.lean`: `auction_winProb_mono`, `auction_payment_mono`, `auction_rent_mono`, `mirrlees_taxPaid_strictMono`. They use no category theory. The advertised statements are now twelve.

`lake comparator --paranoid`, six kernels (Lean, paranoid, lean4lean, nanoda, con-leche, con-ron), run in a scratch copy:

| Run | Result |
|---|---|
| each of the four statements alone | all six kernels accept (24 s, 24 s, 24 s, 47 s) |
| all twelve statements together | all six kernels accept, including nanoda (2 min) |

`lake build` passes. Not committed.
