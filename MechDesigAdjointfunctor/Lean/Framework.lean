import MechDesigAdjointfunctor.Lean.Linters
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.CompleteLattice.Basic

/-!
# Stage 1: Abstract Categorical Framework

Defines the categories **Mech** and **Alloc**, the forgetful functor
**Q : Mech → Alloc**.  

Note: **Alloc** completeness and **Q** preserving limits (the prerequisites for the adjunction Q ⊣ T)
are proved in `MasterTheorem.lean` (see `alloc_hasLimits` and `QR_preservesLimits`).

## Main declarations

* `MechDesign.SingleCrossing` — condition SC
* `MechDesign.IsIC`, `MechDesign.IsIR` — incentive and participation constraints
* `MechDesign.ICIRMechanism` — object type for the category **Mech**
* `MechDesign.MonotoneAlloc` — object type for the category **Alloc**
* `MechDesign.mechCategory`, `MechDesign.allocCategory` — category instances
* `MechDesign.transfer_depends_only_on_alloc` — IC ⟹ the transfer factors through `q`
* `MechDesign.taxSchedule`, `MechDesign.taxationPrinciple_impl` — implementation of the Taxation Principle:
  a schedule on allocations implements any IC mechanism, uniquely on the range
* `MechDesign.Q` — forgetful functor Q : Mech → Alloc
* `MechDesign.IC_implies_monotone` — condition MON from IC + SC (Lemma 1.7 precursor)

## References

* Mac Lane (1978), *Categories for the Working Mathematician*, Chapters III–V
* Myerson (1981), *Optimal Auction Design*, Lemma 2
* Mirrlees (1971), *An Exploration in the Theory of Optimum Income Taxation*, Eq. (27)
-/

open CategoryTheory CategoryTheory.Limits MeasureTheory

namespace MechDesign

/-! ### 1.1 Economic Primitives -/

/-- **Condition SC** (Single Crossing): for any two allocations `a > a'`, the surplus
difference `v a θ - v a' θ` is strictly increasing in type `θ`.  Higher types have a
strictly greater marginal value for higher allocations. -/
def SingleCrossing {A : Type*} [Preorder A] (v : A → ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ (a a' : A), a > a' → StrictMonoOn (fun θ => v a θ - v a' θ) D

/-! ### 1.2 Mechanisms and Incentive Constraints -/

/-- A *direct mechanism* over allocation space `A`: an allocation rule `q : ℝ → A`
paired with a transfer rule `t : ℝ → ℝ`.  Utility is `v(q(θ), θ) - t(θ)` (quasilinear
in the transfer — condition QI is structural). -/
structure Mechanism (A : Type*) where
  q : ℝ → A   -- allocation rule
  t : ℝ → ℝ   -- transfer rule (positive = payment by agent)

/-- **Bayesian Incentive Compatibility (BIC)**: truth-telling is weakly optimal for
every type `θ` regardless of the report `θ'`. -/
def IsIC {A : Type*} (v : A → ℝ → ℝ) (θ_min : ℝ) (m : Mechanism A) : Prop :=
  ∀ θ θ' : ℝ, θ_min ≤ θ → θ_min ≤ θ' →
    v (m.q θ) θ - m.t θ ≥ v (m.q θ') θ - m.t θ'

/-- **Individual Rationality (IR)**: the lowest type `θ_min` receives non-negative
surplus, `V(θ_min) ≥ 0`.

**This is the inequality, not the normalisation `V(θ_min) = 0`.**  The distinction is
structural, not cosmetic:

* With the inequality, the fiber of `Q` over an allocation `r` is a genuine one-parameter
  family, indexed by the boundary rent `V(θ_min) ≥ 0` (see `surplus_split`).  `T(r)` is
  the zero-rent member, hence *initial* in its fiber, and the adjunction runs `T ⊣ Q`
  (`adj_T_Q`).  IR is what orients it — it is used essentially in the counit.
* The normalisation `V(θ_min) = 0` cuts out the full subcategory `Mech₀` (`ZeroRent`),
  on which the counit becomes invertible and `T ⊣ Q` upgrades to an adjoint equivalence
  `AllocR ≌ Mech₀` (`equivAllocMech₀`) — the Taxation Principle.

So `Mech` is *not* the category of normalised mechanisms; `Mech₀` is. -/
def IsIR {A : Type*} (v : A → ℝ → ℝ) (θ_min : ℝ) (m : Mechanism A) : Prop :=
  v (m.q θ_min) θ_min - m.t θ_min ≥ 0

/-- A **BIC-IR mechanism**: a mechanism satisfying both `IsIC` and `IsIR`. -/
structure ICIRMechanism (A : Type*) [Preorder A] (v : A → ℝ → ℝ) (θ_min : ℝ) where
  mech : Mechanism A
  hMono : Monotone mech.q
  hIC   : IsIC v θ_min mech
  hIR   : IsIR v θ_min mech

/-! ### 1.3 The Category **Mech** (Definition 1.4)

Objects: BIC-IR mechanisms.
Morphisms: order-preserving type-space transformations that are simultaneously
compatible with the allocation rule and with the agent's **surplus**. -/

/-- The **surplus** (indirect utility) of a mechanism: `V(θ) = v(q θ, θ) - t θ`.

This is the canonical coordinate for a quasilinear model.  Condition QI says the
numeraire enters utility linearly with coefficient `-1`, which is exactly what makes
`V` well defined and makes the transfer *recoverable* from the pair `(q, V)` via
`t θ = v (q θ) θ - V θ`.  Ordering morphisms by `V` therefore loses no information
about transfers; it merely states the transfer condition in the coordinate the
envelope theorem lives in. -/
def surplus {A : Type*} [Preorder A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (m : ICIRMechanism A v θ_min) (θ : ℝ) : ℝ :=
  v (m.mech.q θ) θ - m.mech.t θ

/-- A morphism `f : m → m'` in **Mech**: the pointwise allocation inequality
`m.q θ ≤ m'.q θ`, together with the **surplus inequality** `V_m θ ≤ V_m' θ` on the
physical domain `[θ_min, ∞)`.

**Design note (why surplus, not transfer).**  Earlier versions ordered morphisms by the
transfer, `hTransf : ∀ θ ≥ θ_min, m.t θ ≤ m'.t θ`.  That field makes `T : Alloc → Mech`
*not a functor*: `t*(r) ≤ t*(r')` does not follow from `r.q ≤ r'.q` for a general `v`
(it needs convexity of `v` in the allocation, which the Mirrlees value function fails).
The transfer mixes the allocation into the comparison.  The surplus does not: by the
envelope formula `V_{T(r)}(θ) = ∫_{θ_min}^θ (∂v/∂s)(r.q s, s) ds`, so
`V_{T(r)} ≤ V_{T(r')}` reduces to a pointwise inequality between the integrands, which
is exactly **single crossing** — an assumption the framework already makes, and one that
holds in both the Myerson and the Mirrlees setting.  See `Tmech_surplus_mono`. -/
@[ext]
structure MechHom {A : Type*} [Preorder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (m m' : ICIRMechanism A v θ_min) : Type where
  hAlloc : ∀ θ, m.mech.q θ ≤ m'.mech.q θ
  hSurp  : ∀ θ : ℝ, θ_min ≤ θ → surplus m θ ≤ surplus m' θ

instance mechHom_subsingleton {A : Type*} [Preorder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    {m m' : ICIRMechanism A v θ_min} : Subsingleton (MechHom m m') := by
  constructor; intro f g
  obtain ⟨fa, fv⟩ := f; obtain ⟨ga, gv⟩ := g
  congr 1

instance mechCategory {A : Type*} [Preorder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} :
    Category (ICIRMechanism A v θ_min) where
  Hom m m'  := MechHom m m'
  id _      :=
    { hAlloc := fun _ => le_rfl
      hSurp  := fun _ _ => le_rfl }
  comp f g  :=
    { hAlloc := fun θ => le_trans (f.hAlloc θ) (g.hAlloc θ)
      hSurp  := fun θ hθ => le_trans (f.hSurp θ hθ) (g.hSurp θ hθ) }
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-! ### 1.4 The Category **Alloc** (Definition 1.5)

Objects: monotone (non-decreasing) allocation rules — condition MON.
Morphisms: order-preserving type transformations compatible with the allocation rule. -/

/-- An object of **Alloc**: an admissible (monotone) allocation rule.  Condition MON
is a consequence of IC + SC; see `IC_implies_monotone`. -/
@[ext]
structure MonotoneAlloc (A : Type*) [Preorder A] where
  q : ℝ → A
  hMono : Monotone q

/-- A morphism `h : r → r'` in **Alloc**: the pointwise inequality `r.q θ ≤ r'.q θ`.
This makes `MonotoneAlloc A` a thin (preorder) category.

**Design note.**  Earlier versions carried an additional *spread monotonicity* field,
`Monotone (fun θ => r'.q θ - r.q θ)`.  It existed solely to prove the transfer-ordered
`T.map`, and it is not needed once **Mech** is ordered by surplus: `T.map` then follows
from single crossing alone (`Tmech_surplus_mono`).  Dropping it makes **Alloc** the
plain pointwise order on monotone allocation rules, as Definition 1.5 intends.

**Design note (D16).**  That field was also the only consumer of `[AddCommGroup A]` and
`[IsOrderedAddMonoid A]` — it is what subtracted in `A`.  The field went; the binders stayed,
unused, until a deletion test removed all 27 of them with no effect on the build.  `A` needs
only to be **ordered**.  The subtraction in `surplus` is in `ℝ`, not `A`. -/
@[ext]
structure AllocHom {A : Type*} [Preorder A]
    (r r' : MonotoneAlloc A) : Type where
  h : ∀ θ, r.q θ ≤ r'.q θ

instance allocHom_subsingleton {A : Type*} [Preorder A]
    {r r' : MonotoneAlloc A} : Subsingleton (AllocHom r r') := by
  constructor; intro f g
  obtain ⟨ha⟩ := f; obtain ⟨ga⟩ := g
  congr 1

instance allocCategory {A : Type*} [Preorder A] :
    Category (MonotoneAlloc A) where
  Hom r r'  := AllocHom r r'
  id _      := { h := fun _ => le_rfl }
  comp f g  := { h := fun θ => le_trans (f.h θ) (g.h θ) }
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-! ### 1.5 The Taxation Principle: transfers factor through the allocation

The classical taxation principle is a statement about **one** mechanism: an IC mechanism does
not need the agent's *type* to compute the payment, only the *allocation* the agent takes.  So
the mechanism can be replaced by a schedule posted on allocations — a nonlinear tax on income,
a price list on quantities — and the direct mechanism is redundant.

This is where it comes from, and it costs nothing but IC.  It is logically prior to everything
in Stages 4–5: no envelope theorem, no single crossing, no differentiability, no integrability,
no measure.  It is also *different in kind* from revenue equivalence, which compares two
mechanisms; this compares two **types** inside one mechanism. -/

/-- **Transfers depend on the type only through the allocation.**

If a mechanism gives two physical types the same allocation, IC forces it to charge them the
same.  Apply IC in both directions: type `θ` reporting `θ'` and type `θ'` reporting `θ`.  The
value terms cancel — they are equal, since the allocations are — and the two inequalities on
the transfers close on each other.

*Reference*: Hammond (1979), Theorem 1; Rochet (1985), Proposition 1. -/
theorem transfer_depends_only_on_alloc {A : Type*} [Preorder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (m : ICIRMechanism A v θ_min) {θ θ' : ℝ} (hθ : θ_min ≤ θ) (hθ' : θ_min ≤ θ')
    (hq : m.mech.q θ = m.mech.q θ') : m.mech.t θ = m.mech.t θ' := by
  have h1 := m.hIC θ θ' hθ hθ'
  have h2 := m.hIC θ' θ hθ' hθ
  rw [hq] at h1
  rw [← hq] at h2
  linarith

/-- **The schedule** the taxation principle produces: the payment posted against an allocation
`a` is what the mechanism charges some type that takes `a`, and off the range it is irrelevant
(set to `0`).  Well defined by `transfer_depends_only_on_alloc` — which type is chosen does not
matter, and `taxSchedule_apply` is the statement that it does not.

In the Mirrlees reading `A` is income and this is the nonlinear tax schedule `T(y)`; in the
Myerson reading it is the price posted against a winning probability. -/
noncomputable def taxSchedule {A : Type*} [Preorder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} (m : ICIRMechanism A v θ_min) (a : A) : ℝ :=
  open Classical in
  if h : ∃ θ, θ_min ≤ θ ∧ m.mech.q θ = a then m.mech.t h.choose else 0

/-- **The taxation principle, existence half**: the mechanism is implemented by its schedule.
Every physical type pays what the schedule posts against the allocation it takes. -/
theorem taxSchedule_apply {A : Type*} [Preorder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} (m : ICIRMechanism A v θ_min)
    {θ : ℝ} (hθ : θ_min ≤ θ) : m.mech.t θ = taxSchedule m (m.mech.q θ) := by
  have hex : ∃ θ', θ_min ≤ θ' ∧ m.mech.q θ' = m.mech.q θ := ⟨θ, hθ, rfl⟩
  rw [taxSchedule, dif_pos hex]
  exact (transfer_depends_only_on_alloc m hex.choose_spec.1 hθ hex.choose_spec.2).symm

/-- **The taxation principle, uniqueness half**: any two schedules that implement the same
mechanism agree wherever it matters — on the allocations the mechanism actually assigns.
(Off that range a schedule is unconstrained, which is why uniqueness is stated as `EqOn` and
not as equality of functions.) -/
theorem taxSchedule_unique {A : Type*} [Preorder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} (m : ICIRMechanism A v θ_min) (T T' : A → ℝ)
    (hT : ∀ θ, θ_min ≤ θ → m.mech.t θ = T (m.mech.q θ))
    (hT' : ∀ θ, θ_min ≤ θ → m.mech.t θ = T' (m.mech.q θ)) :
    Set.EqOn T T' (m.mech.q '' Set.Ici θ_min) := by
  rintro a ⟨θ, hθ, rfl⟩
  rw [← hT θ hθ, hT' θ hθ]

/-- **The taxation principle** (Hammond 1979; Rochet 1985), for a single BIC-IR mechanism:
there is a schedule on allocations that implements it, and it is unique on the range.

Note what is *not* here: no second mechanism, no boundary-rent hypothesis, no regularity.  The
comparison statement — two mechanisms with the same allocation and the same rent charge the
same — is revenue equivalence (`masterTheorem_transferInvariance`), which is a different
theorem and needs the envelope machinery of Stage 4. -/
theorem taxationPrinciple_impl {A : Type*} [Preorder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} (m : ICIRMechanism A v θ_min) :
    ∃ T : A → ℝ, (∀ θ, θ_min ≤ θ → m.mech.t θ = T (m.mech.q θ)) ∧
      ∀ T' : A → ℝ, (∀ θ, θ_min ≤ θ → m.mech.t θ = T' (m.mech.q θ)) →
        Set.EqOn T T' (m.mech.q '' Set.Ici θ_min) :=
  ⟨taxSchedule m, fun _ hθ => taxSchedule_apply m hθ,
    fun T' hT' => taxSchedule_unique m _ T' (fun _ hθ => taxSchedule_apply m hθ) hT'⟩

/-! ### 1.6 The Allocation Functor **Q : Mech → Alloc** (Definition 1.6) -/

/-- **Condition MON from IC + SC** (precursor to Lemma 1.7): every BIC mechanism has a
non-decreasing allocation rule.  Proof sketch: if `q` were decreasing over some
interval, a mimicry deviation by higher types would be profitable, violating IC.
*Reference*: Myerson (1981) Lemma 2; Mirrlees (1971) Eq. (27). -/
lemma IC_implies_monotone {A : Type*} [LinearOrder A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    {D : Set ℝ} (hSC : SingleCrossing v D) (hD : ∀ θ, θ ∈ D)
    (m : ICIRMechanism A v θ_min) : MonotoneOn m.mech.q (Set.Ici θ_min) := by
  intro θ₁ hθ₁ θ₂ hθ₂ h12
  by_contra hlt
  rw [not_le] at hlt
  -- `hlt : m.mech.q θ₂ < m.mech.q θ₁`
  have h1 := m.hIC θ₁ θ₂ hθ₁ hθ₂
  have h2 := m.hIC θ₂ θ₁ hθ₂ hθ₁
  rcases eq_or_lt_of_le h12 with heq | hlt_θ
  · rw [heq] at hlt
    exact lt_irrefl _ hlt
  · have hSC' := hSC (m.mech.q θ₁) (m.mech.q θ₂) hlt
    linarith [hSC' (hD θ₁) (hD θ₂) hlt_θ]

/-- **Q : Mech → Alloc** — the forgetful functor that drops the transfer rule and
retains only the allocation rule.  Well-defined by `IC_implies_monotone`.
*Reference*: Definition 1.6 and the remark on forgetful functors in Section 1.5. -/
noncomputable def Q {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ}
    {θ_min : ℝ} {D : Set ℝ} (_hSC : SingleCrossing v D) (_hD : ∀ θ, θ ∈ D) :
    ICIRMechanism A v θ_min ⥤ MonotoneAlloc A where
  obj m       := ⟨m.mech.q, m.hMono⟩
  map f       := { h := f.hAlloc }
  map_id _     := by apply @Subsingleton.elim _ allocHom_subsingleton
  map_comp _ _ := by apply @Subsingleton.elim _ allocHom_subsingleton

/-! ### 1.7 Q Preserves Colimits (Lemma 1.7) -/

-- **Lemma 1.8**: Q preserves all small colimits because it is the left adjoint in Q ⊣ T.
-- The proof requires `adj_T_Q_impl` (defined in `MasterTheorem.lean`, which imports this
-- file), so it lives there as `MechDesign.TR_preservesColimits` / `MechDesign.QR_preservesLimits`
-- — on the regular subcategories, where the adjunction is not vacuous.
-- *Reference*: Mac Lane (1978), Chapter V, Theorem 5.1 (left adjoints preserve colimits).

end MechDesign
