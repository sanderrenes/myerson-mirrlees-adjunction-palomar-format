import MechDesigAdjointfunctor.Basic

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

namespace MechDesign

open CategoryTheory MeasureTheory

/-- **The adjunction T ⊣ Q** (Theorem 4.3): on the regular subcategories, the transfer
functor `T : AllocR → MechR` is left adjoint to the allocation functor `Q : MechR → AllocR`.

Regularity (`IsRegularAlloc`) is what the envelope theorem consumes at an object: `v`
Lipschitz in the type along the allocation, the envelope integrand right-continuous along the
allocation and interval integrable.  It is a property of the allocation rule alone, so it cuts
both categories at once.

Stating this on all of **Mech** instead, with those conditions as hypotheses quantified over
the objects, would be **vacuous** — see `Corollaries.no_uniform_lipschitz` and
`Corollaries.no_uniform_hW`, which prove no such hypotheses can be satisfied in the Myerson
setting.  `Corollaries.myersonAdjunction` instantiates the statement below, and
`Corollaries.postedPriceObj` supplies an object. -/
noncomputable def adj_T_Q {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} (θ_min : ℝ)
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D)
    (hD : ∀ θ, θ ∈ D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    TR (θ_min := θ_min) hθ_pos hSC hD_Ioi hdiff hintC ⊣ QR (θ_min := θ_min) hSC hD :=
  adj_T_Q_impl θ_min hθ_pos hSC hD hD_Ioi hdiff hintC

/-- **Theorem 4.5(i) — Existence and uniqueness**: for a monotone allocation `r`, the
mechanism `T(r)` is BIC-IR with allocation `r.q`, leaves the lowest type no rent, and carries
the envelope transfer — and it is the **only** such mechanism: every BIC-IR mechanism with
allocation `r.q` and zero rent has the same transfer at every physical type.

Uniqueness is stated on `[θ_min, ∞)` rather than as `∃!` because `IsIC`/`IsIR` constrain a
mechanism only there: two objects may differ below `θ_min` and satisfy every hypothesis, so
structural uniqueness is false.  The content is the envelope theorem, i.e. IC. -/
theorem masterTheorem_existence {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (L : NNReal)
    (hvLip : ∀ θ' : ℝ, LipschitzOnWith L (v (r.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (r.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    ∃ m : ICIRMechanism A v θ_min,
      (m ∈ MechWithAlloc r ∧ ZeroRent m ∧
        ∀ θ, m.mech.t θ = transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ) ∧
      ∀ m' : ICIRMechanism A v θ_min, m' ∈ MechWithAlloc r → ZeroRent m' →
        ∀ θ, θ_min ≤ θ → m'.mech.t θ = m.mech.t θ :=
  masterTheorem_existence_impl hθ_pos hSC hD_Ioi r hdiff hint hintC L hvLip hW

-- Theorem 4.5(ii) — Isomorphism
theorem masterTheorem_isomorphism {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (m : ICIRMechanism A v θ_min) (hm : m ∈ MechWithAlloc r)
    (L : NNReal)
    (hvLip : ∀ θ' : ℝ, LipschitzOnWith L (v (m.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (r.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    (hBC : v (m.mech.q θ_min) θ_min = m.mech.t θ_min) :
    Nonempty (m ≅ Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) :=
  masterTheorem_isomorphism_impl hθ_pos hSC hD_Ioi r hdiff hint hintC m hm L hvLip hW hBC

/-- **Theorem 4.5(iii) — Transfer Invariance**: any two BIC-IR mechanisms with the same
allocation rule and the **same boundary rent** charge the same transfer at every physical type.

Pointwise, not in expectation: this is what the envelope theorem gives, and the expected-revenue
form follows by integrating it against any finite measure (`transferInvariance_integral`) — no
distributional hypothesis enters anywhere. -/
theorem masterTheorem_transferInvariance {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min)
    (r : MonotoneAlloc A)
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hdiff : ∀ a : A, DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (m₁ m₂ : ICIRMechanism A v θ_min)
    (hm₁ : m₁ ∈ MechWithAlloc r) (hm₂ : m₂ ∈ MechWithAlloc r)
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ, LipschitzOnWith L₁ (v (m₁.mech.q θ')) (Set.Ici θ_min))
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ, LipschitzOnWith L₂ (v (m₂.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (r.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min) :
    ∀ θ, θ_min ≤ θ → m₁.mech.t θ = m₂.mech.t θ :=
  masterTheorem_transferInvariance_impl hθ_pos r hint hdiff m₁ m₂ hm₁ hm₂ L₁ hvLip₁ L₂ hvLip₂ hW hV₀

/-- **Revenue Equivalence Theorem** (Myerson 1981): any two BIC-IR mechanisms with the same
allocation rule and the same boundary rent charge the same transfer at every physical type —
hence raise the same expected revenue under any distribution of types. -/
theorem revenueEquivalence
    (θ_min : ℝ) (hθ_pos : 0 < θ_min)
    (q₀ : MonotoneAlloc Myerson.MyersonAlloc)
    (m₁ m₂ : ICIRMechanism Myerson.MyersonAlloc Myerson.myersonValue θ_min)
    (hm₁_alloc : m₁ ∈ MechWithAlloc q₀)
    (hm₂_alloc : m₂ ∈ MechWithAlloc q₀)
    (hint : ∀ a b, IntervalIntegrable
      (typeDerivAlongAlloc Myerson.myersonValue q₀)
      MeasureTheory.volume a b)
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ,
      LipschitzOnWith L₁ (Myerson.myersonValue (m₁.mech.q θ')) (Set.Ici θ_min))
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ,
      LipschitzOnWith L₂ (Myerson.myersonValue (m₂.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (Myerson.myersonValue (q₀.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min) :
    ∀ θ, θ_min ≤ θ → m₁.mech.t θ = m₂.mech.t θ :=
  Corollaries.revenueEquivalence_impl θ_min hθ_pos q₀ m₁ m₂ hm₁_alloc hm₂_alloc hint L₁ hvLip₁ L₂ hvLip₂ hW hV₀

/-- **Mirrlees Taxation Principle** (Hammond 1979; Rochet 1985): an IC mechanism is a
nonlinear tax schedule.  There is a schedule `T` on incomes with `t(θ) = T(y(θ))` at every
physical type, and it is unique on the incomes the mechanism actually assigns.

This is a statement about **one** mechanism, and it costs nothing but incentive compatibility:
no single crossing, no differentiability, no integrability, no measure.  The comparison
statement — two mechanisms with the same income schedule and the same rent levy the same tax —
is revenue equivalence transposed to the Mirrlees setting, and it is a different theorem
(`Corollaries.mirrlees_transferInvariance_impl`). -/
theorem taxationPrinciple (h g : ℝ → ℝ) (θ_min : ℝ)
    (m : ICIRMechanism ℝ (Mirrlees.mirrleesValue h g) θ_min) :
    ∃ T : ℝ → ℝ, (∀ θ, θ_min ≤ θ → m.mech.t θ = T (m.mech.q θ)) ∧
      ∀ T' : ℝ → ℝ, (∀ θ, θ_min ≤ θ → m.mech.t θ = T' (m.mech.q θ)) →
        Set.EqOn T T' (m.mech.q '' Set.Ici θ_min) :=
  taxationPrinciple_impl m

end MechDesign
