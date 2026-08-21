import MechDesigAdjointfunctor.Lean.MasterTheorem
import MechDesigAdjointfunctor.Lean.MyersonSetting
import MechDesigAdjointfunctor.Lean.MirrleesSetting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Stage 5: Revenue Equivalence and the Taxation Principle as Corollaries

Instantiates the abstract Master Theorem (`MasterTheorem.lean`) in the two
economic settings to recover the classical results as special cases.

## Main declarations

* `MechDesign.Corollaries.revenueEquivalence` — Corollary 5.1: Myerson's Revenue
  Equivalence Theorem is an instance of Theorem 4.5(iii).
* `MechDesign.Corollaries.taxationPrinciple` — Corollary 5.2: the Mirrlees Taxation
  Principle is an instance of Theorem 4.5(iii).

## The proof chain

```
       IC  (ICIRMechanism.hIC)
               ↓
    surplus_ic_sandwich          ← pure IC, no analysis
        ↙            ↘
surplus_lipschitzOn   surplus_hasDerivWithinAt   ← Milgrom–Segal (MVT + squeeze)
        ↘            ↙
        surplus_split            ← the envelope theorem, in surplus form
               ↓
   mechIso_of_sameAlloc_sameRent  +  transfer_eq_of_iso   ← iso in Mech ⟹ equal transfers
               ↓
  masterTheorem_transferInvariance
        ↙               ↘
  Revenue Equivalence     Taxation Principle
  (Myerson 1981)          (Hammond 1979; Rochet 1985)
```

Both corollaries follow from `masterTheorem_transferInvariance_impl.  Only the value function
differs — `myersonValue` vs `mirrleesValue`.  That is the unification claim, and it is
literally the same call with a different `v`.

Note what is **not** on this chain: `adj_T_Q`.  The adjunction is proved structure *about*
the framework, not a lemma the corollaries consume.  The categorical content they do use is
the isomorphism in **Mech** (`transfer_eq_of_iso`).  `transferInvariance_via_T` shows the
route through `T` is genuinely available for normalised mechanisms.

Note also what is **absent from the hypotheses**: neither corollary needs single crossing or
IR.  SC makes `T` a functor; IR orients the adjunction; revenue equivalence needs neither.

## References

* Myerson (1981), *Optimal Auction Design*, Theorem 2
* Riley–Samuelson (1981), *Optimal Auctions*, Theorem 1
* Hammond (1979), *Straightforward Incentive Compatibility*, Theorem 1
* Rochet (1985), *The Taxation Principle*, Proposition 1
-/

open MeasureTheory MechDesign

namespace MechDesign.Corollaries

/-! ### 5.0 Discharging the Lipschitz hypothesis

`surplus_split` no longer assumes the surplus is continuous — it *derives* continuity from
incentive compatibility (`surplus_ic_sandwich` → `surplus_lipschitzOn`).  The price is a
regularity hypothesis on the value function: `v(a, ·)` must be Lipschitz in the type, with a
constant uniform over the allocations the mechanism actually uses.

Here is that hypothesis discharged in the Myerson setting.  It is exactly the standard
assumption that allocation probabilities lie in `[0, 1]`. -/

/-- `∂/∂θ [θ·a] = a`.  The Myerson envelope integrand is the allocation itself. -/
theorem myerson_deriv (a : Myerson.MyersonAlloc) (u : ℝ) :
    deriv (Myerson.myersonValue a) u = a := by
  have h : HasDerivAt (Myerson.myersonValue a) a u := by
    unfold Myerson.myersonValue
    simpa using (hasDerivAt_id u).mul_const a
  exact h.deriv

/-- The Myerson envelope integrand along any allocation is the allocation itself:
`D_r(s) = ∂/∂s [s · r.q s] = r.q s`. -/
theorem myerson_typeDeriv (r : MonotoneAlloc Myerson.MyersonAlloc) (s : ℝ) :
    typeDerivAlongAlloc Myerson.myersonValue r s = r.q s :=
  myerson_deriv (r.q s) s

/-- **The Myerson value function is `1`-Lipschitz in the type along any allocation in
`[-1, 1]`** — in particular along any allocation *probability*.

`v(a, θ) = θ·a`, so `|v(a, θ₂) − v(a, θ₁)| = |a|·|θ₂ − θ₁| ≤ |θ₂ − θ₁|` whenever `|a| ≤ 1`.
Combined with `surplus_lipschitzOn`, this discharges the continuity requirement of
`revenueEquivalence` from IC alone. -/
theorem myerson_lipschitz {a : Myerson.MyersonAlloc} (ha : |a| ≤ 1) (S : Set ℝ) :
    LipschitzOnWith 1 (Myerson.myersonValue a) S := by
  refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, Myerson.myersonValue]
  calc |x * a - y * a| = |a| * |x - y| := by rw [← abs_mul]; ring_nf
    _ ≤ 1 * |x - y| := by gcongr
    _ = |x - y| := one_mul _

/-- **The Mirrlees value function is Lipschitz in the type**, given a bound on its
θ-derivative over the physical domain.

`v(y, θ) = θ·h(y) − g(y/θ)`, so `∂v/∂θ = h(y) + (y/θ²)·g′(y/θ)`.  On `[θ_min, ∞)` with
`θ_min > 0` this is bounded for each income `y`, and uniformly so once the income range is
bounded — which is the economically mild assumption that incomes are bounded.  The bound is
taken as an explicit hypothesis rather than derived, so that the caller can supply whatever
bound their `h`, `g` and income range actually give.

This is the Mirrlees counterpart of `myerson_lipschitz`, and it is what discharges the
continuity requirement of `taxationPrinciple` from IC alone. -/
theorem mirrlees_lipschitz (h g : ℝ → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    {θ_min : ℝ} (hθ_pos : 0 < θ_min) (y : ℝ) (C : NNReal)
    (hbound : ∀ θ ∈ Set.Ici θ_min, ‖h y + (y / θ ^ 2) * deriv g (y / θ)‖₊ ≤ C) :
    LipschitzOnWith C (Mirrlees.mirrleesValue h g y) (Set.Ici θ_min) := by
  refine (convex_Ici θ_min).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun θ => h y + (y / θ ^ 2) * deriv g (y / θ)) (fun θ hθ => ?_) hbound
  have hθ0 : θ ≠ 0 := ne_of_gt (lt_of_lt_of_le hθ_pos (Set.mem_Ici.mp hθ))
  exact (Mirrlees.mirrleesValue_hasDerivAt h g hh hg y θ hθ0).hasDerivWithinAt

/-! ### 5.0b Linking `myersonTransfer` to the abstract `transferFormula`

`MyersonSetting` defines `myersonTransfer q θ = θ·q θ − ∫₀^θ q` independently of the
abstract `transferFormula`, and `myerson_expectedRevenue` (the virtual-valuation result) is
proved about *that*.  Nothing connected the two, so the revenue formula floated free of the
categorical machinery.  These two lemmas connect them. -/

/-- The abstract envelope transfer, instantiated at `v(a, θ) = θ·a`, is the familiar
Myerson expression — with the integral starting at `θ_min` rather than at `0`. -/
theorem myerson_transferFormula (r : MonotoneAlloc Myerson.MyersonAlloc) (θ_min θ : ℝ) :
    transferFormula Myerson.myersonValue θ_min
        (typeDerivAlongAlloc Myerson.myersonValue r) r.q θ
      = θ * r.q θ - ∫ s in θ_min..θ, r.q s := by
  simp only [transferFormula]
  congr 1
  exact intervalIntegral.integral_congr fun s _ => myerson_typeDeriv r s

/-- **`transferFormula` and `myersonTransfer` differ by exactly the rent conceded below
`θ_min`.**

```
transferFormula(θ_min)(θ)  =  myersonTransfer(θ)  +  ∫₀^{θ_min} q
```

They coincide precisely when `θ_min = 0` — which the Master Theorem forbids, since it needs
`θ_min > 0`.  So the two are *not* interchangeable, and the constant that separates them is
the boundary rent `∫₀^{θ_min} q` that the abstract theory leaves free (see D5: revenue
equivalence needs *equal* rent, not zero rent).  This is the honest form of the bridge. -/
theorem myerson_transferFormula_eq_myersonTransfer
    (r : MonotoneAlloc Myerson.MyersonAlloc) (θ_min θ : ℝ)
    (hq_int : ∀ a b, IntervalIntegrable r.q MeasureTheory.volume a b) :
    transferFormula Myerson.myersonValue θ_min
        (typeDerivAlongAlloc Myerson.myersonValue r) r.q θ
      = Myerson.myersonTransfer r.q θ + ∫ s in (0:ℝ)..θ_min, r.q s := by
  rw [myerson_transferFormula r θ_min θ]
  simp only [Myerson.myersonTransfer]
  have hsplit : (∫ s in (0:ℝ)..θ_min, r.q s) + (∫ s in θ_min..θ, r.q s)
      = ∫ s in (0:ℝ)..θ, r.q s :=
    intervalIntegral.integral_add_adjacent_intervals (hq_int 0 θ_min) (hq_int θ_min θ)
  linarith [hsplit]

/-! ### 5.1 Revenue Equivalence (Corollary 5.1) -/

/-- **Corollary 5.1 — Myerson Revenue Equivalence Theorem**.

In the Myerson auction setting (type space `[0,1]`, value function `v(q,θ) = θ*q`,
allocation probabilities `q ∈ [0,1]`), any two BIC-IR mechanisms
`M₁ = (q, t₁)` and `M₂ = (q, t₂)` with the **same allocation rule** `q` and
boundary condition `Vᵢ(0) = 0` satisfy:

  `𝔼[t₁(θ)] = 𝔼[t₂(θ)]`

*Proof*: Instantiate `masterTheorem_transferInvariance_impl with the Myerson value function.
SC holds by `myerson_singleCrossing`.  The expected transfer equals
`𝔼[ψ(θ) · q(θ)]` where `ψ(θ) = θ - (1-F(θ))/f(θ)` is the virtual valuation,
which depends only on `q` and the type distribution `F`.

*Reference*: Myerson (1981), Theorem 2; Riley–Samuelson (1981). -/
theorem revenueEquivalence_impl
    (θ_min : ℝ) (hθ_pos : 0 < θ_min)
    (q₀ : MonotoneAlloc Myerson.MyersonAlloc)
    (m₁ m₂ : ICIRMechanism Myerson.MyersonAlloc Myerson.myersonValue θ_min)
    (hm₁_alloc : m₁ ∈ MechWithAlloc q₀)
    (hm₂_alloc : m₂ ∈ MechWithAlloc q₀)
    (hint : ∀ a b, IntervalIntegrable
      (typeDerivAlongAlloc Myerson.myersonValue q₀)
      MeasureTheory.volume a b)
    -- Continuity is NOT assumed: it is derived from IC, given that the value function is
    -- Lipschitz in the type along each allocation the mechanism uses.  Discharged for
    -- Myerson by `myerson_lipschitz` whenever the allocation is bounded.
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ,
      LipschitzOnWith L₁ (Myerson.myersonValue (m₁.mech.q θ')) (Set.Ici θ_min))
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ,
      LipschitzOnWith L₂ (Myerson.myersonValue (m₂.mech.q θ')) (Set.Ici θ_min))
    -- The envelope condition is NO LONGER ASSUMED — it is derived from IC (Milgrom–Segal).
    -- What remains is `hW`, which in the Myerson setting (`∂v/∂θ = a`) is exactly
    -- **right-continuity of the allocation rule**.  The posted price satisfies it:
    -- see `PostedPrice.postedPrice_hW`.
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (Myerson.myersonValue (q₀.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    -- RELAXED boundary condition: the two mechanisms leave the lowest type the SAME rent.
    -- (Revenue equivalence needs equal rent, not zero rent.)
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  masterTheorem_transferInvariance_impl hθ_pos q₀ hint Myerson.myerson_vDiff
    m₁ m₂ hm₁_alloc hm₂_alloc L₁ hvLip₁ L₂ hvLip₂ hW hV₀ μ

/-- **Myerson expected revenue formula**: for any BIC-IR mechanism with allocation `q`
and `V(0) = 0`, expected revenue equals expected virtual surplus.

  `𝔼_F[t(θ)] = 𝔼_F[ψ(θ) · q(θ)]`   where `ψ(θ) = θ - (1-F(θ))/f(θ)`.

This follows from the transfer formula by integration by parts.
*Reference*: Myerson (1981), Equation (5). -/
theorem myerson_revenueFormula (q : ℝ → ℝ) (F f : ℝ → ℝ)
    (hf_pos : ∀ θ, 0 < f θ)
    (hq_int : ∀ a b, IntervalIntegrable q MeasureTheory.volume a b)
    (hq_cont : Continuous q) (hf_cont : Continuous f)
    (hFf : ∀ θ, HasDerivAt F (f θ) θ)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    ∫ θ in (0:ℝ)..1, Myerson.myersonTransfer q θ * f θ =
    ∫ θ in (0:ℝ)..1, (θ - (1 - F θ) / f θ) * q θ * f θ :=
  Myerson.myerson_expectedRevenue q F f hf_pos hq_int hq_cont hf_cont hFf hF0 hF1

/-! ### 5.2 Taxation Principle (Corollary 5.2) -/

/-- **Corollary 5.2 — Mirrlees Taxation Principle**.

In the Mirrlees taxation setting (type space `[θ_min, θ_max]`, quasilinear value
function `v(y, θ)`), any IC mechanism `(y(θ), c(θ))` with `V(θ_min) = 0` can be
implemented by a **unique** nonlinear tax schedule `T : Y → ℝ` defined by
`T(y) = y - c(y)` on the range of `y(θ)`.

Moreover, any two IC mechanisms with the **same income assignment** `y(θ)` and the same
`V(θ_min)` produce identical tax schedules and hence the same expected tax revenue.

*Proof*: Instantiate `masterTheorem_transferInvariance_impl with the Mirrlees value function.

**On the hypotheses.**  Notice what is *absent*: the Spence–Mirrlees conditions
(`0 < g'`, `StrictMono h`, `StrictMono (l ↦ l · g' l)`) are **not** assumed, because transfer
invariance does not need them.  Single crossing is what makes `T` a functor and what forces
monotonicity of the allocation; it plays no role in revenue equivalence, which is a statement
about IC alone.  Carrying SC here would have overstated what the theorem requires.  (`h` and
`g` are still assumed differentiable — that is genuinely used, via `mirrlees_vDiff`.)

*Reference*: Hammond (1979), Theorem 1; Rochet (1985), Proposition 1; Mirrlees (1971),
Eq. (27). -/
theorem taxationPrinciple_impl
    (h g : ℝ → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    (θ_min : ℝ) (hθ_pos : 0 < θ_min)
    (q₀ : MonotoneAlloc ℝ)
    (m₁ m₂ : ICIRMechanism ℝ (Mirrlees.mirrleesValue h g) θ_min)
    (hm₁_alloc : ∀ θ, m₁.mech.q θ = q₀.q θ)
    (hm₂_alloc : ∀ θ, m₂.mech.q θ = q₀.q θ)
    (hint : ∀ a b, IntervalIntegrable
      (typeDerivAlongAlloc (Mirrlees.mirrleesValue h g) q₀)
      MeasureTheory.volume a b)
    -- Continuity is NOT assumed: it is derived from IC, given Lipschitz-in-the-type.
    -- Discharged by `mirrlees_lipschitz`: `∂v/∂θ = h y + (y/θ²)·g'(y/θ)` is bounded on
    -- `[θ_min, ∞)` for each income, uniformly so once incomes are bounded.
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ,
      LipschitzOnWith L₁ (Mirrlees.mirrleesValue h g (m₁.mech.q θ')) (Set.Ici θ_min))
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ,
      LipschitzOnWith L₂ (Mirrlees.mirrleesValue h g (m₂.mech.q θ')) (Set.Ici θ_min))
    -- The envelope condition is NO LONGER ASSUMED — it is derived from IC (Milgrom–Segal).
    -- `hW` asks the composite `(s,u) ↦ ∂v/∂θ (y(s), u)` to be continuous from the upper
    -- right at the diagonal: the income schedule must be right-continuous, and `∂v/∂θ`
    -- jointly continuous — both standard, and both hold at a bunching region.
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt
        (fun p : ℝ × ℝ => deriv (Mirrlees.mirrleesValue h g (q₀.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    -- RELAXED boundary condition: identical rent at the lowest type (a common `V₀`),
    -- matching what `mirrlees_unique_from_IC` already assumed.
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  masterTheorem_transferInvariance_impl hθ_pos q₀ hint (Mirrlees.mirrlees_vDiff h g hh hg)
    m₁ m₂ hm₁_alloc hm₂_alloc L₁ hvLip₁ L₂ hvLip₂ hW hV₀ μ

/-! ### 5.2b The posted price — why the envelope hypothesis must be one-sided

The mechanism that forces the design of `surplus_split`'s hypothesis.  A **posted price**
with reserve `p`: sell iff `θ ≥ p`, charge `p` on a sale.  It is the canonical optimal
auction under regularity, it is monotone, IC and IR — and its surplus

  `V θ = θ·q θ - t θ = max (θ - p) 0`

has a **kink at `p`**.  It has no two-sided derivative there.

So a `HasDerivAt` envelope hypothesis is not merely inconvenient, it is **unsatisfiable**
for every auction with a reserve price, and `revenueEquivalence` would be inapplicable to
the mechanisms it most wants to talk about.  The right derivative survives the kink — at
`p` it equals `1 = q p` — which is all `integral_eq_sub_of_hasDeriv_right` ever needed.

`postedPrice_hasEnvelope` discharges the hypothesis the framework now takes.
`postedPrice_not_hasDerivAt` shows the hypothesis it used to take is false. -/

namespace PostedPrice

variable {p : ℝ}

/-- Sell iff the type clears the reserve. -/
noncomputable def alloc (p : ℝ) : ℝ → Myerson.MyersonAlloc := fun θ => if p ≤ θ then 1 else 0

/-- Charge the reserve on a sale, nothing otherwise. -/
noncomputable def transfer (p : ℝ) : ℝ → ℝ := fun θ => if p ≤ θ then p else 0

lemma alloc_mono : Monotone (alloc p) := by
  intro a b hab
  rcases le_or_gt p a with ha | ha
  · have hb : p ≤ b := ha.trans hab
    simp [alloc, ha, hb]
  · rcases le_or_gt p b with hb | hb
    · simp [alloc, not_le.mpr ha, hb]
    · simp [alloc, not_le.mpr ha, not_le.mpr hb]

/-- The surplus of the posted price is `max (θ - p) 0` — the kinked function. -/
lemma surplus_eq (θ : ℝ) :
    Myerson.myersonValue (alloc p θ) θ - transfer p θ = max (θ - p) 0 := by
  simp only [Myerson.myersonValue, alloc, transfer]
  split_ifs with h
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ θ - p)]; ring
  · rw [max_eq_right (by linarith [not_le.mp h] : θ - p ≤ (0:ℝ))]; ring

/-- **The posted price satisfies the framework's envelope hypothesis.**
Continuity plus a *right* derivative at every physical type — including at the reserve `p`,
where the right derivative is `1 = q p`. -/
theorem postedPrice_hasEnvelope :
    ContinuousOn (fun s => Myerson.myersonValue (alloc p s) s - transfer p s) (Set.Ioi 0) ∧
    ∀ θ > 0, HasDerivWithinAt
      (fun s => Myerson.myersonValue (alloc p s) s - transfer p s)
      (typeDerivAlongAlloc Myerson.myersonValue ⟨alloc p, alloc_mono⟩ θ) (Set.Ioi θ) θ := by
  have hV : (fun s => Myerson.myersonValue (alloc p s) s - transfer p s)
      = fun s => max (s - p) 0 := funext fun s => surplus_eq s
  constructor
  · rw [hV]
    exact (Continuous.max (continuous_id.sub continuous_const) continuous_const).continuousOn
  · intro θ _
    rw [hV, myerson_typeDeriv ⟨alloc p, alloc_mono⟩ θ]
    change HasDerivWithinAt (fun s => max (s - p) 0) (alloc p θ) (Set.Ioi θ) θ
    by_cases hpθ : p ≤ θ
    · -- Above the reserve: V agrees with `s - p` to the right of θ, slope 1 = q θ.
      have hEq : Set.EqOn (fun s => max (s - p) 0) (fun s => s - p) (Set.Ici θ) := by
        intro s hs
        exact max_eq_left (by linarith [hs, le_trans hpθ hs] : (0:ℝ) ≤ s - p)
      have h1 : HasDerivWithinAt (fun s : ℝ => s - p) 1 (Set.Ioi θ) θ :=
        ((hasDerivAt_id θ).sub_const p).hasDerivWithinAt
      have hres : HasDerivWithinAt (fun s => max (s - p) 0) 1 (Set.Ioi θ) θ :=
        h1.congr (fun s hs => hEq (Set.mem_Ici.mpr (le_of_lt hs)))
          (hEq (Set.mem_Ici.mpr (le_refl θ)))
      simpa [alloc, if_pos hpθ] using hres
    · -- Below the reserve: V is eventually 0 to the right of θ, slope 0 = q θ.
      rw [not_le] at hpθ
      have hev : (fun s => max (s - p) 0) =ᶠ[nhdsWithin θ (Set.Ioi θ)] fun _ => (0:ℝ) := by
        have hmem : Set.Iio p ∈ nhdsWithin θ (Set.Ioi θ) :=
          nhdsWithin_le_nhds (Iio_mem_nhds hpθ)
        filter_upwards [hmem] with s hs
        exact max_eq_right (by linarith [Set.mem_Iio.mp hs] : s - p ≤ (0:ℝ))
      have h0 : HasDerivWithinAt (fun _ : ℝ => (0:ℝ)) 0 (Set.Ioi θ) θ :=
        (hasDerivAt_const θ (0:ℝ)).hasDerivWithinAt
      have : HasDerivWithinAt (fun s => max (s - p) 0) 0 (Set.Ioi θ) θ :=
        h0.congr_of_eventuallyEq hev (max_eq_right (by linarith : θ - p ≤ (0:ℝ)))
      simpa [alloc, if_neg (not_le.mpr hpθ)] using this

/-- **The posted price does NOT satisfy a two-sided envelope hypothesis.**

At the reserve `p` the surplus `max (θ - p) 0` has slope `0` from the left and `1` from the
right, so it has **no** derivative there — for *any* candidate value `c`.

This is the theorem that justifies Phase 0.  The framework previously demanded
`HasDerivAt`, and this shows that demand is unsatisfiable for the canonical optimal
auction: `revenueEquivalence` could not be applied to any mechanism with a reserve. -/
theorem postedPrice_not_hasDerivAt (c : ℝ) :
    ¬ HasDerivAt (fun s => max (s - p) 0) c p := by
  intro h
  have hslope := hasDerivAt_iff_tendsto_slope.mp h
  -- From the left the slope is identically 0.
  have hleft : Filter.Tendsto (slope (fun s => max (s - p) 0) p) (nhdsWithin p (Set.Iio p))
      (nhds c) :=
    hslope.mono_left (nhdsWithin_mono p (fun x hx => ne_of_lt (Set.mem_Iio.mp hx)))
  have hL0 : slope (fun s => max (s - p) 0) p =ᶠ[nhdsWithin p (Set.Iio p)] fun _ => (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxp : x - p ≤ 0 := by linarith [Set.mem_Iio.mp hx]
    simp [slope_def_field, max_eq_right hxp]
  have hc0 : c = 0 :=
    tendsto_nhds_unique (hleft.congr' hL0) tendsto_const_nhds
  -- From the right the slope is identically 1.
  have hright : Filter.Tendsto (slope (fun s => max (s - p) 0) p) (nhdsWithin p (Set.Ioi p))
      (nhds c) :=
    hslope.mono_left (nhdsWithin_mono p (fun x hx => ne_of_gt (Set.mem_Ioi.mp hx)))
  have hR1 : slope (fun s => max (s - p) 0) p =ᶠ[nhdsWithin p (Set.Ioi p)] fun _ => (1:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxp : (0:ℝ) ≤ x - p := by linarith [Set.mem_Ioi.mp hx]
    have hne : x - p ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Set.mem_Ioi.mp hx))
    simp [slope_def_field, max_eq_left hxp, div_self hne]
  have hc1 : c = 1 :=
    tendsto_nhds_unique (hright.congr' hR1) tendsto_const_nhds
  exact absurd (hc0 ▸ hc1 : (0:ℝ) = 1) (by norm_num)

/-- **The posted price also discharges the Lipschitz hypothesis.**  Its allocation is `0` or
`1`, so `myerson_lipschitz` applies.  Together with `postedPrice_hasEnvelope`, the
reserve-price auction now satisfies *every* hypothesis the framework asks of it — continuity
comes free from IC, and the envelope condition is one-sided. -/
theorem postedPrice_lipschitz (θ' : ℝ) (S : Set ℝ) :
    LipschitzOnWith 1 (Myerson.myersonValue (alloc p θ')) S := by
  refine myerson_lipschitz ?_ S
  simp only [alloc]
  split_ifs <;> simp

/-- **The posted price satisfies `hW`** — so the envelope condition is now *derived* for it,
not assumed.

In the Myerson setting `∂v/∂θ (a, u) = a`, so the composite `(s, u) ↦ ∂v/∂θ (q s, u)` is just
`q ∘ fst`, and `hW` reduces to **right-continuity of `q` at `θ`**.  The posted price is
right-continuous: `q` jumps *up* at the reserve and `q p = 1`, so approaching `p` from above
gives `q s = 1 = q p`.  Below the reserve `q` is locally `0`; above it, locally `1`.

Which is the whole point: the reserve-price auction is exactly the mechanism a two-sided
`HasDerivAt` hypothesis excluded, and it sails through the one-sided derivation. -/
theorem postedPrice_hW (θ : ℝ) :
    ContinuousWithinAt
      (fun x : ℝ × ℝ => deriv (Myerson.myersonValue ((⟨alloc p, alloc_mono⟩ :
        MonotoneAlloc Myerson.MyersonAlloc).q x.1)) x.2)
      (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ) := by
  -- The composite collapses to `alloc p ∘ fst` (Myerson: `∂v/∂θ (a, u) = a`).
  have hfun : (fun x : ℝ × ℝ => deriv (Myerson.myersonValue (alloc p x.1)) x.2)
      = fun x : ℝ × ℝ => alloc p x.1 :=
    funext fun x => myerson_deriv _ _
  change ContinuousWithinAt (fun x : ℝ × ℝ => deriv (Myerson.myersonValue (alloc p x.1)) x.2)
    (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)
  rw [hfun]
  -- Right-continuity of the posted-price allocation at θ.
  rcases le_or_gt p θ with hp | hp
  · -- at or above the reserve: `alloc p` is constantly 1 on `Ici θ ×ˢ Ici θ`
    refine ContinuousWithinAt.congr (f := fun _ : ℝ × ℝ => (1 : ℝ))
      continuousWithinAt_const ?_ ?_
    · rintro ⟨s, u⟩ hsu
      simp [alloc, if_pos (le_trans hp (Set.mem_Ici.mp hsu.1))]
    · simp [alloc, if_pos hp]
  · -- strictly below the reserve: `alloc p` is 0 on a whole neighbourhood of `(θ, θ)`
    refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ : ℝ × ℝ => (0 : ℝ))
      continuousWithinAt_const ?_ ?_
    · have hmem : (Set.Iio p ×ˢ (Set.univ : Set ℝ)) ∈
          nhdsWithin ((θ, θ) : ℝ × ℝ) (Set.Ici θ ×ˢ Set.Ici θ) :=
        nhdsWithin_le_nhds (prod_mem_nhds (Iio_mem_nhds hp) Filter.univ_mem)
      filter_upwards [hmem] with x hx
      simp [alloc, if_neg (not_le.mpr (Set.mem_Iio.mp hx.1))]
    · simp [alloc, if_neg (not_le.mpr hp)]

end PostedPrice

/-! ### 5.3 Conditions for failure — where each hypothesis is load-bearing

These were previously three `theorem … : True := trivial` stubs.  A theorem that states
`True` proves nothing, and having them in the file made the development look as though it
covered the failure cases when it does not.  They are recorded here as prose, which is what
they always were.

* **Failure of QI (quasilinearity).**  Without a linear numeraire the surplus
  `V(θ) = v(q θ, θ) − t θ` is not the right coordinate, and the transfer is no longer
  recoverable from `(q, V)`.  `MechHom`'s surplus order — the whole basis of `T`'s
  functoriality (D1) — loses its meaning, and `Q` no longer factors as a forgetful functor.
  *Reference*: Maskin–Riley (1984); Rochet–Choné (1998).

* **Failure of SC (single crossing).**  With multi-dimensional types `θ ∈ ℝᵏ`, `k ≥ 2`, there
  is no total order on types, so `typeDeriv_mono_of_alloc_le` fails and with it
  `Tmech_surplus_mono` — `T` is not a functor.  Note this does **not** touch revenue
  equivalence, which needs neither SC nor IR (see `taxationPrinciple`); it destroys the
  *categorical* half of the story only.
  *Reference*: Rochet (1987); Armstrong (1996); Rochet–Choné (1998).

* **Failure of MON (ironing).**  Without regularity the optimal allocation is non-monotone,
  so it is not an object of **Alloc** at all.  The fix is ironing — replace `q*` by its
  monotone envelope — after which the theory applies to the ironed rule.
  *Reference*: Myerson (1981), §6; Mirrlees (1971), §6; Ebert (1992). -/

end MechDesign.Corollaries
