import MechDesigAdjointfunctor.Lean.MyersonSetting
import MechDesigAdjointfunctor.Lean.MirrleesSetting

/-!
# Monotone results: winning probability, payment, rent, tax paid

Counterparts, in the auction, of the Mirrlees monotonicity results
(`Mirrlees.mirrlees_strictMono_rent`, `mirrlees_strictMono_alloc`,
`mirrlees_strictMono_consumption`), and the Mirrlees counterpart for the tax paid.

Auction (`v(a, θ) = θ a`, types `θ ≥ θ_min ≥ 0`), for any incentive-compatible mechanism:

* `auction_winProb_mono` — the probability of winning is non-decreasing (IC alone);
* `auction_payment_mono` — the expected payment is non-decreasing (IC, `θ_min ≥ 0`);
* `auction_rent_mono` — the rent `V(θ) = θ q(θ) − t(θ)` is non-decreasing (IC, `q ≥ 0`).

Income tax:

* `mirrlees_taxPaid_strictMono` — the tax paid is strictly increasing in type when the income
  schedule is strictly increasing and the marginal tax rate is positive.

None of these uses `IR`, and none uses the envelope formula: each follows from the IC inequalities
for two types.
-/

namespace MechDesign.MonotoneResults

/-- **Winning probability is non-decreasing** (auction): IC for two types, added, gives
`(θ₂ − θ₁)(q θ₂ − q θ₁) ≥ 0`. -/
theorem auction_winProb_mono (θ_min : ℝ) (m : Mechanism ℝ)
    (hIC : IsIC Myerson.myersonValue θ_min m) :
    MonotoneOn m.q (Set.Ici θ_min) := by
  intro θ₁ h₁ θ₂ h₂ h12
  by_contra hlt
  rw [not_le] at hlt
  have a := hIC θ₁ θ₂ h₁ h₂
  have b := hIC θ₂ θ₁ h₂ h₁
  simp only [Myerson.myersonValue] at a b
  have hne : θ₁ < θ₂ := by
    rcases h12.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd hlt (lt_irrefl _)
  nlinarith [mul_pos (sub_pos.2 hne) (sub_pos.2 hlt)]

/-- **Expected payment is non-decreasing** (auction, `θ_min ≥ 0`): IC of the lower type gives
`t θ' − t θ ≥ θ (q θ' − q θ) ≥ 0`. -/
theorem auction_payment_mono (θ_min : ℝ) (hθ : 0 ≤ θ_min) (m : Mechanism ℝ)
    (hIC : IsIC Myerson.myersonValue θ_min m) :
    MonotoneOn m.t (Set.Ici θ_min) := by
  intro θ₁ h₁ θ₂ h₂ h12
  have hq : m.q θ₁ ≤ m.q θ₂ := auction_winProb_mono θ_min m hIC h₁ h₂ h12
  have a := hIC θ₁ θ₂ h₁ h₂
  simp only [Myerson.myersonValue] at a
  have hθ₁ : 0 ≤ θ₁ := le_trans hθ h₁
  nlinarith [mul_nonneg hθ₁ (sub_nonneg.2 hq)]

/-- **Rent is non-decreasing** (auction, allocations `≥ 0`): the higher type can report the lower
type's report, so `V θ' ≥ V θ + (θ' − θ) q θ ≥ V θ`. -/
theorem auction_rent_mono (θ_min : ℝ) (m : Mechanism ℝ)
    (hIC : IsIC Myerson.myersonValue θ_min m)
    (hq : ∀ θ, θ_min ≤ θ → 0 ≤ m.q θ) :
    MonotoneOn (fun θ => Myerson.myersonValue (m.q θ) θ - m.t θ) (Set.Ici θ_min) := by
  intro θ₁ h₁ θ₂ h₂ h12
  have b := hIC θ₂ θ₁ h₂ h₁
  have h0 := hq θ₁ h₁
  simp only [Myerson.myersonValue] at b ⊢
  nlinarith [mul_nonneg (sub_nonneg.2 h12) h0]

/-- **Tax paid is strictly increasing in type** (income tax): the tax bill of type `θ` is
`T (y θ)`; `y` is strictly increasing and the marginal tax rate `T′` is positive, so `T` is
strictly increasing and so is the composition.  Stated for `Mirrlees.taxSchedule`, with
consumption `c θ = y θ − T (y θ)`. -/
theorem mirrlees_taxPaid_strictMono (y T : ℝ → ℝ) (θ_min : ℝ)
    (hy : StrictMonoOn y (Set.Ici θ_min))
    (hT : Differentiable ℝ T)
    (hT_pos : ∀ z, 0 < deriv T z) :
    StrictMonoOn (Mirrlees.taxSchedule y (fun θ => y θ - T (y θ))) (Set.Ici θ_min) := by
  have hTm : StrictMono T := by
    rw [← strictMonoOn_univ]
    exact strictMonoOn_of_deriv_pos convex_univ hT.continuous.continuousOn
      (fun z _ => hT_pos z)
  have heq : Mirrlees.taxSchedule y (fun θ => y θ - T (y θ)) = fun θ => T (y θ) := by
    funext θ; simp [Mirrlees.taxSchedule]
  rw [heq]
  exact hTm.comp_strictMonoOn hy

end MechDesign.MonotoneResults
