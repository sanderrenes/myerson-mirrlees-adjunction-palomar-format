import MechDesigAdjointfunctor.Lean.MasterTheorem
import MechDesigAdjointfunctor.Lean.Corollaries
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Basic.NNReal.Defs

/-!
# The product decomposition `MechR ≌ AllocR × ℝ≥0`

The fibre of `Q : MechR ⥤ AllocR` over `r` is a ray indexed by the rent `V_m(θ_min) ≥ 0`
(`surplus_split`).  This file states that fact as one equivalence of categories:

  `Φ : MechR ⥤ AllocR × ℝ≥0`,  `Φ m = (Q m, rent m)`,

where `ℝ≥0` is a thin category with `c ⟶ c'` iff `c ≤ c'`.  Under `Φ`, `Q` is the first
projection and `T r` is `(r, 0)`.

## Why `equivAllocMech₀` does not already say this

`equivAllocMech₀ : AllocR ≌ Mech₀` concerns the full subcategory of **zero-rent** mechanisms.
It is the restriction of `Φ` to the slice `rent = 0`, and it is silent about every mechanism
with positive rent.  Three things in this file are not consequences of it:

* the existence of a mechanism with allocation `r` and rent `c` for **every** `c ≥ 0`
  (`TshiftObj`, essential surjectivity);
* the order on `MechR` is the *product* order, `m ⟶ m'` iff `Q m ⟶ Q m'` and
  `rent m ≤ rent m'` (fullness of `Φ`);
* the rent is a functorial coordinate (`rentFunctor`), which `Mech₀` cannot express because
  its rent is constant.

## Main declarations

* `MechDesign.rent`, `MechDesign.rentFunctor` — the rent coordinate.
* `MechDesign.TshiftObj` — the mechanism with allocation `r` and rent `c`: `(r, t*_r − c)`.
* `MechDesign.productFunctor` — `Φ`.
* `MechDesign.equivProd` — `MechR ≌ AllocR × ℝ≥0`.
* `MechDesign.transfer_eq_of_productFunctor_iso` — revenue equivalence, read off `Φ`.
* `MechDesign.tr_hom_iff` — `T r ⟶ m ↔ r ⟶ Q m`, read off `Φ` (the adjunction, as a check).
-/

open CategoryTheory

namespace MechDesign

section Rent

variable {A : Type*} [LinearOrder A] {v : A → ℝ → ℝ} {θ_min : ℝ}

/-- Individual rationality, in the form the rent coordinate needs. -/
lemma surplus_min_nonneg (m : ICIRMechanism A v θ_min) : 0 ≤ surplus m θ_min := by
  have h := m.hIR
  simpa [IsIR, surplus] using h

/-- The **rent** of a BIC-IR mechanism: the surplus of the lowest type, as a non-negative real. -/
noncomputable def rent (m : ICIRMechanism A v θ_min) : NNReal :=
  ⟨surplus m θ_min, surplus_min_nonneg m⟩

@[simp] lemma coe_rent (m : ICIRMechanism A v θ_min) : (rent m : ℝ) = surplus m θ_min := rfl

/-- Zero rent is exactly `rent m = 0`. -/
lemma rent_eq_zero_iff (m : ICIRMechanism A v θ_min) : rent m = 0 ↔ ZeroRent m := by
  show rent m = 0 ↔ surplus m θ_min = 0
  rw [← NNReal.coe_eq_zero]
  rfl

/-- A morphism in `Mech` raises the rent. -/
lemma rent_le_of_hom {m m' : ICIRMechanism A v θ_min} (f : m ⟶ m') : rent m ≤ rent m' :=
  NNReal.coe_le_coe.1 (f.hSurp θ_min le_rfl)

/-- **The rent as a functor** `MechR ⥤ ℝ≥0`. -/
noncomputable def rentFunctor : MechR A v θ_min ⥤ NNReal where
  obj m := rent m.obj
  map f := homOfLE (rent_le_of_hom f.hom)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end Rent

section ProductFunctor

variable {A : Type*} [LinearOrder A] {v : A → ℝ → ℝ} {θ_min : ℝ}
  {D : Set ℝ} (hSC : SingleCrossing v D) (hD : ∀ θ, θ ∈ D)

/-- **`Φ : MechR ⥤ AllocR × ℝ≥0`**, `m ↦ (Q m, rent m)`. -/
noncomputable def productFunctor : MechR A v θ_min ⥤ AllocR A v θ_min × NNReal :=
  Functor.prod' (QR (θ_min := θ_min) hSC hD) rentFunctor

instance productFunctor_faithful : (productFunctor (θ_min := θ_min) hSC hD).Faithful where
  map_injective := fun {_ _} f g _ => Subsingleton.elim f g

end ProductFunctor

section Decomposition

variable {A : Type*} [LinearOrder A] {v : A → ℝ → ℝ} {θ_min : ℝ}
  (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD : ∀ θ, θ ∈ D)
  (hD_Ioi : Set.Ioi 0 ⊆ D)
  (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
  (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)

include hθ_pos hSC hD_Ioi hdiff hintC

/-- **The mechanism with allocation `r` and rent `c`**: the envelope mechanism `T r` with its
transfer lowered by `c`.  A constant shift of the transfer keeps IC; IR holds because the rent
`c` is non-negative. -/
noncomputable def TshiftObj (r : AllocR A v θ_min) (c : NNReal) : MechR A v θ_min :=
  ⟨{ mech := ⟨r.obj.q,
        fun θ => (Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).mech.t θ - c⟩
     hMono := r.obj.hMono
     hIC := by
       intro θ θ' h1 h2
       have h := (Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).hIC θ θ' h1 h2
       change v (r.obj.q θ) θ -
           (Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).mech.t θ ≥
         v (r.obj.q θ') θ -
           (Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).mech.t θ' at h
       change v (r.obj.q θ) θ -
           ((Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).mech.t θ - c) ≥
         v (r.obj.q θ') θ -
           ((Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).mech.t θ' - c)
       linarith
     hIR := by
       have h0 := surplus_Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC θ_min
       simp only [surplus, intervalIntegral.integral_same] at h0
       change v (r.obj.q θ_min) θ_min -
           ((Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).mech.t θ_min - c) ≥ 0
       have hc : (0 : ℝ) ≤ (c : ℝ) := NNReal.coe_nonneg c
       change v (r.obj.q θ_min) θ_min -
           (Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).mech.t θ_min = 0 at h0
       linarith },
   r.property⟩

/-- The surplus of `TshiftObj r c` is the surplus of `T r` plus the rent `c`. -/
lemma surplus_TshiftObj (r : AllocR A v θ_min) (c : NNReal) (θ : ℝ) :
    surplus (TshiftObj hθ_pos hSC hD_Ioi hdiff hintC r c).obj θ =
      surplus (Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC) θ + c := by
  simp only [surplus, TshiftObj]
  change v (r.obj.q θ) θ -
      ((Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).mech.t θ - c) =
    (v (r.obj.q θ) θ - (Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC).mech.t θ) + c
  ring

/-- The rent of `TshiftObj r c` is `c`. -/
lemma rent_TshiftObj (r : AllocR A v θ_min) (c : NNReal) :
    rent (TshiftObj hθ_pos hSC hD_Ioi hdiff hintC r c).obj = c := by
  apply NNReal.eq
  rw [coe_rent, surplus_TshiftObj, surplus_Tmech]
  simp

/-- **The decomposition of the surplus**: every regular mechanism has surplus
`rent + surplus (T (Q m))`.  This is `surplus_split` read through `surplus_Tmech`. -/
lemma surplus_decomp (m : MechR A v θ_min) :
    ∀ θ, θ_min ≤ θ →
      surplus m.obj θ = (rent m.obj : ℝ) +
        surplus (Tmech hθ_pos hSC hD_Ioi ⟨m.obj.mech.q, m.obj.hMono⟩ hdiff
          m.property.int hintC) θ := by
  intro θ hθ
  rw [surplus_split hθ_pos ⟨m.obj.mech.q, m.obj.hMono⟩ m.property.int hdiff m.obj
      (fun _ => rfl) m.property.lip.choose m.property.lip.choose_spec m.property.cont θ hθ,
    surplus_Tmech]
  rfl

/-- **`Φ` is full**: `m ⟶ m'` as soon as `Q m ⟶ Q m'` and `rent m ≤ rent m'`.  This is where
the envelope formula and single crossing enter. -/
theorem productFunctor_full : (productFunctor (θ_min := θ_min) hSC hD).Full where
  map_surjective {m m'} g := by
    have hrent : rent m.obj ≤ rent m'.obj := leOfHom g.2
    refine ⟨ObjectProperty.homMk
      { hAlloc := g.1.hom.h
        hSurp := ?_ }, Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
    intro θ hθ
    rw [surplus_decomp hθ_pos hSC hD_Ioi hdiff hintC m θ hθ,
      surplus_decomp hθ_pos hSC hD_Ioi hdiff hintC m' θ hθ]
    have hT := Tmech_surplus_mono hθ_pos hSC hD_Ioi ⟨m.obj.mech.q, m.obj.hMono⟩
      ⟨m'.obj.mech.q, m'.obj.hMono⟩ g.1.hom.h hdiff m.property.int m'.property.int hintC θ hθ
    have hc : (rent m.obj : ℝ) ≤ rent m'.obj := NNReal.coe_le_coe.2 hrent
    linarith

/-- **`Φ` is essentially surjective**: every pair `(r, c)` with `c ≥ 0` is the image of
`TshiftObj r c`.  This is the part `equivAllocMech₀` cannot supply, because it only has `c = 0`. -/
theorem productFunctor_essSurj : (productFunctor (θ_min := θ_min) hSC hD).EssSurj where
  mem_essImage X := by
    refine ⟨TshiftObj hθ_pos hSC hD_Ioi hdiff hintC X.1 X.2, ⟨eqToIso ?_⟩⟩
    exact Prod.ext rfl (rent_TshiftObj hθ_pos hSC hD_Ioi hdiff hintC X.1 X.2)

/-- **`Φ` is an equivalence of categories**: faithful (thin), full, essentially surjective. -/
theorem productFunctor_isEquivalence :
    (productFunctor (θ_min := θ_min) hSC hD).IsEquivalence where
  faithful := inferInstance
  full := productFunctor_full (θ_min := θ_min) hθ_pos hSC hD hD_Ioi hdiff hintC
  essSurj := productFunctor_essSurj (θ_min := θ_min) hθ_pos hSC hD hD_Ioi hdiff hintC

/-- **The product decomposition** `MechR ≌ AllocR × ℝ≥0`.

The hypotheses are the ones of `adj_T_Q`; `myersonEquivProd` instantiates them in the Myerson
setting. -/
@[needs_witness]
noncomputable def equivProd : MechR A v θ_min ≌ AllocR A v θ_min × NNReal :=
  haveI := productFunctor_isEquivalence (θ_min := θ_min) hθ_pos hSC hD hD_Ioi hdiff hintC
  (productFunctor (θ_min := θ_min) hSC hD).asEquivalence

/-! ### What the decomposition gives -/

/-- Under `Φ`, the first coordinate of `T r` is `r` and the rent of `T r` is `0`: `Φ (T r) = (r, 0)`. -/
lemma productFunctor_obj_TR (r : AllocR A v θ_min) :
    (productFunctor (θ_min := θ_min) hSC hD).obj
        ((TR hθ_pos hSC hD_Ioi hdiff hintC).obj r) = (r, 0) := by
  refine Prod.ext rfl ?_
  apply NNReal.eq
  simp only [productFunctor, Functor.prod'_obj, rentFunctor, coe_rent, NNReal.coe_zero]
  exact zeroRent_Tmech hθ_pos hSC hD_Ioi r.obj hdiff r.property.int hintC

/-- **Revenue equivalence, read off `Φ`.**  If two regular mechanisms have isomorphic images
`(Q m, rent m)`, then `m ≅ m'` (a fully faithful functor reflects isomorphisms), and an
isomorphism in `Mech` forces equal transfers. -/
theorem transfer_eq_of_productFunctor_iso {m m' : MechR A v θ_min}
    (i : (productFunctor (θ_min := θ_min) hSC hD).obj m ≅
         (productFunctor (θ_min := θ_min) hSC hD).obj m') :
    ∀ θ, θ_min ≤ θ → m.obj.mech.t θ = m'.obj.mech.t θ := by
  have := productFunctor_full (θ_min := θ_min) hθ_pos hSC hD hD_Ioi hdiff hintC
  have j : m ≅ m' := (productFunctor (θ_min := θ_min) hSC hD).preimageIso i
  exact transfer_eq_of_iso ((RegMech v θ_min).ι.mapIso j)

/-- **The adjunction `T ⊣ Q`, as a check, read off `Φ`**: there is a morphism `T r ⟶ m` iff there
is a morphism `r ⟶ Q m`.  In the product, `(r, 0) ⟶ (Q m, rent m)` iff `r ⟶ Q m`, because `0` is the
least element of `ℝ≥0` — which is individual rationality. -/
theorem tr_hom_iff (r : AllocR A v θ_min) (m : MechR A v θ_min) :
    Nonempty ((TR hθ_pos hSC hD_Ioi hdiff hintC).obj r ⟶ m) ↔
      Nonempty (r ⟶ (QR (θ_min := θ_min) hSC hD).obj m) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨(QR (θ_min := θ_min) hSC hD).map f⟩
  · rintro ⟨g⟩
    have := productFunctor_full (θ_min := θ_min) hθ_pos hSC hD hD_Ioi hdiff hintC
    have h0 : rent ((TR hθ_pos hSC hD_Ioi hdiff hintC).obj r).obj ≤ rent m.obj := by
      have := congrArg Prod.snd
        (productFunctor_obj_TR (θ_min := θ_min) hθ_pos hSC hD hD_Ioi hdiff hintC r)
      change rent ((TR hθ_pos hSC hD_Ioi hdiff hintC).obj r).obj = 0 at this
      rw [this]; exact zero_le
    obtain ⟨f, _⟩ := (productFunctor (θ_min := θ_min) hSC hD).map_surjective
      (X := (TR hθ_pos hSC hD_Ioi hdiff hintC).obj r) (Y := m)
      ((g : (QR (θ_min := θ_min) hSC hD).obj ((TR hθ_pos hSC hD_Ioi hdiff hintC).obj r) ⟶
          (QR (θ_min := θ_min) hSC hD).obj m), homOfLE h0)
    exact ⟨f⟩

end Decomposition

/-! ### The advertised form

`Challenge.lean` states the decomposition without the new definitions `rent` and `productFunctor`,
so that the audited surface stays small.  `Φ` is faithful because **Mech** is thin, so the
equivalence `equivProd` is exactly two facts:

* *full* — `m ⟶ m'` iff `Q m ⟶ Q m'` and the rent does not decrease;
* *essentially surjective* — every allocation occurs with every rent `c ≥ 0`. -/

/-- **Product decomposition** (advertised as `productDecomposition`). -/
theorem productDecomposition_impl {A : Type*} [LinearOrder A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D)
    (hD : ∀ θ, θ ∈ D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    (∀ m m' : MechR A v θ_min,
      Nonempty (m ⟶ m') ↔
        (Nonempty ((QR (θ_min := θ_min) hSC hD).obj m ⟶ (QR (θ_min := θ_min) hSC hD).obj m') ∧
          surplus m.obj θ_min ≤ surplus m'.obj θ_min)) ∧
    (∀ (r : AllocR A v θ_min) (c : ℝ), 0 ≤ c →
      ∃ m : MechR A v θ_min,
        (QR (θ_min := θ_min) hSC hD).obj m = r ∧ surplus m.obj θ_min = c) := by
  refine ⟨fun m m' => ⟨?_, ?_⟩, fun r c hc => ?_⟩
  · rintro ⟨f⟩
    exact ⟨⟨(QR (θ_min := θ_min) hSC hD).map f⟩, f.hom.hSurp θ_min le_rfl⟩
  · rintro ⟨⟨g⟩, hs⟩
    have := productFunctor_full (θ_min := θ_min) hθ_pos hSC hD hD_Ioi hdiff hintC
    have h0 : rent m.obj ≤ rent m'.obj := NNReal.coe_le_coe.1 hs
    obtain ⟨f, _⟩ := (productFunctor (θ_min := θ_min) hSC hD).map_surjective
      (X := m) (Y := m') (g, homOfLE h0)
    exact ⟨f⟩
  · refine ⟨TshiftObj hθ_pos hSC hD_Ioi hdiff hintC r ⟨c, hc⟩, rfl, ?_⟩
    have h := rent_TshiftObj hθ_pos hSC hD_Ioi hdiff hintC r ⟨c, hc⟩
    exact congrArg (fun x : NNReal => (x : ℝ)) h

/-! ### Non-vacuity -/

/-- **The product decomposition, instantiated in the Myerson setting.**  Every hypothesis of
`equivProd` is discharged from properties of `Myerson.myersonValue` alone, as for
`Corollaries.myersonAdjunction`; `Corollaries.postedPriceObj` supplies an object. -/
@[witness_for MechDesign.equivProd]
noncomputable def myersonEquivProd (θ_min : ℝ) (hθ_pos : 0 < θ_min) :
    MechR Myerson.MyersonAlloc Myerson.myersonValue θ_min ≌
      AllocR Myerson.MyersonAlloc Myerson.myersonValue θ_min × NNReal :=
  equivProd hθ_pos Myerson.myerson_singleCrossing (fun θ => Set.mem_univ θ)
    (Set.subset_univ _) Myerson.myerson_vDiff Corollaries.myerson_intC

end MechDesign
