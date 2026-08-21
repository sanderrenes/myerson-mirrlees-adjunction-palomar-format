import MechDesigAdjointfunctor.Lean.MasterTheorem
import MechDesigAdjointfunctor.Lean.MyersonSetting
import MechDesigAdjointfunctor.Lean.MirrleesSetting

/-!
# MechDesigAdjointfunctor — Advertised Statement Surface

This is the small, trusted surface a mathematical reader should audit.
It contains the main theorem statement: the adjunction Q ⊣ T that unifies
Myerson's Revenue Equivalence Theorem and the Mirrlees Taxation Principle.

## Main Result

* `MechDesign.adj_T_Q` — The adjunction T ⊣ Q (Theorem 4.3)

## References

* Mac Lane (1978), *Categories for the Working Mathematician*, Chapter IV
* Myerson (1981), *Optimal Auction Design*
* Mirrlees (1971), *An Exploration in the Theory of Optimum Income Taxation*
-/

namespace MechDesign

open CategoryTheory MeasureTheory

/-- **The adjunction T ⊣ Q** (Theorem 4.3): The allocation functor Q : Mech → Alloc
has a right adjoint T : Alloc → Mech. -/
noncomputable def adj_T_Q {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} (θ_min : ℝ)
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D)
    (hD : ∀ θ, θ ∈ D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (L : NNReal)
    (hvLip : ∀ (m : ICIRMechanism A v θ_min) (θ' : ℝ),
        LipschitzOnWith L (v (m.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ (m : ICIRMechanism A v θ_min) (θ : ℝ), θ_min ≤ θ →
        ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (m.mech.q p.1)) p.2)
            (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)) :
    T (θ_min := θ_min) hθ_pos hSC hD_Ioi hdiff hintC hint ⊣ Q (θ_min := θ_min) hSC hD :=
  sorry

/-- **Theorem 4.5(i) — Existence**: For any monotone allocation `r` with
`V(θ_min) = 0`, there exists a **unique** BIC-IR mechanism with allocation `r.q`. -/
theorem masterTheorem_existence {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    ∃! (m : ICIRMechanism A v θ_min),
      m ∈ MechWithAlloc r ∧
      ∀ θ, m.mech.t θ = transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ :=
  sorry

/-- **Theorem 4.5(ii) — Isomorphism**: Every BIC-IR mechanism with allocation `r.q`
and `V(θ_min) = 0` is isomorphic to `T(r)` in **Mech**. -/
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
  sorry

/-- **Theorem 4.5(iii) — Transfer Invariance**: Any two BIC-IR mechanisms with the
same allocation rule and the **same boundary rent** generate the same expected transfer. -/
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
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  sorry

/-- **Revenue Equivalence Theorem** (Myerson 1981): Any two BIC-IR mechanisms with the
same allocation rule generate the same expected revenue. -/
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
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  sorry

/-- **Mirrlees Taxation Principle**: Any two IC mechanisms with the same income
assignment `y(θ)` and the same `V(θ_min)` produce identical tax schedules. -/
theorem taxationPrinciple
    (h g : ℝ → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    (θ_min : ℝ) (hθ_pos : 0 < θ_min)
    (q₀ : MonotoneAlloc ℝ)
    (m₁ m₂ : ICIRMechanism ℝ (Mirrlees.mirrleesValue h g) θ_min)
    (hm₁_alloc : ∀ θ, m₁.mech.q θ = q₀.q θ)
    (hm₂_alloc : ∀ θ, m₂.mech.q θ = q₀.q θ)
    (hint : ∀ a b, IntervalIntegrable
      (typeDerivAlongAlloc (Mirrlees.mirrleesValue h g) q₀)
      MeasureTheory.volume a b)
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ,
      LipschitzOnWith L₁ (Mirrlees.mirrleesValue h g (m₁.mech.q θ')) (Set.Ici θ_min))
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ,
      LipschitzOnWith L₂ (Mirrlees.mirrleesValue h g (m₂.mech.q θ')) (Set.Ici θ_min))
    (hW : ∀ θ, θ_min ≤ θ →
      ContinuousWithinAt (fun p : ℝ × ℝ => deriv (Mirrlees.mirrleesValue h g (q₀.q p.1)) p.2)
        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ))
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  sorry

end MechDesign
