import MechDesigAdjointfunctor.Lean.Basic

/-!
# MechDesigAdjointfunctor — Root Import

A Lean 4 formalisation of the fibre structure of the forgetful functor Q from
incentive-compatible mechanisms to allocation rules: the transfer is a function of the
allocation (the Taxation Principle) and only the rent is free (Myerson's Revenue
Equivalence Theorem, in the auction and Mirrlees settings).  The adjunction T ⊣ Q is the
categorical packaging of this structure.

## Module structure

| File | Contents |
|------|----------|
| `Framework` | Stage 1 — categories Mech, Alloc; functor Q; Lemma 1.7 |
| `MyersonSetting` | Stage 2 — Myerson auction; SC; Lemma 2.1 |
| `MirrleesSetting` | Stage 3 — Mirrlees taxation; SC-M; Lemma 3.1 |
| `MasterTheorem` | Stage 4 — Transfer Functor T; adjunction T ⊣ Q; Theorem 4.5 |
| `Corollaries` | Stage 5 — Revenue Equivalence; Taxation Principle |
| `ProductDecomposition` | `MechR ≌ AllocR × ℝ≥0` (`equivProd`): `Q` is the first projection, `T r = (r, 0)`; revenue equivalence and `T ⊣ Q` read off it |
-/
