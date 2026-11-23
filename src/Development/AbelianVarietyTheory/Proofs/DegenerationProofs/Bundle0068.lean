module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsChartUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.CrdIso

variable {X : Scheme.{0}}

theorem rr {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem mem_res {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (resG X h a) ↔ x ∈ V ∧ x ∈ X.basicOpen a := by
  erw [Scheme.basicOpen_res]
  rfl

theorem isUnit_res {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (hV : V ≤ X.basicOpen a) :
    IsUnit (resG X h a) := by
  have hu : IsUnit (resG X (X.basicOpen_le a) a) := X.toRingedSpace.isUnit_res_basicOpen a
  have := hu.map (resG X hV)
  rwa [rr] at this

theorem cancel {V : X.Opens} {J : Type} (a : J → Γ(X, V)) (ha : ∀ x ∈ V, ∃ j, x ∈ X.basicOpen (a j))
    {u u' : Γ(X, V)} (h : ∀ j, u * a j = u' * a j) : u = u' := by
  apply TopCat.Presheaf.section_ext X.sheaf V
  intro x hx
  obtain ⟨j, hj⟩ := ha x hx
  have hu := (Scheme.mem_basicOpen X (a j) x hx).1 hj
  have := congrArg (X.presheaf.germ V x hx).hom (h j)
  rw [map_mul, map_mul] at this
  exact hu.mul_right_cancel this

theorem exists_unit {V : X.Opens} {J : Type} (a b : J → Γ(X, V))
    (ha : ∀ x ∈ V, ∃ j, x ∈ X.basicOpen (a j)) (hb : ∀ j, X.basicOpen (a j) ≤ X.basicOpen (b j))
    (hab : ∀ j k, b j * a k = b k * a j) : ∃ w : Γ(X, V)ˣ, ∀ j, b j = w.val * a j := by
  have hu : ∀ j, IsUnit (resG X (X.basicOpen_le (a j)) (a j)) := fun j => isUnit_res _ _ le_rfl
  have hq : ∀ j, ∃ q : Γ(X, X.basicOpen (a j)), resG X (X.basicOpen_le (a j)) (b j) =
      q * resG X (X.basicOpen_le (a j)) (a j) := fun j =>
    ⟨resG X (X.basicOpen_le (a j)) (b j) * ↑(hu j).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcov : V ≤ ⨆ j, X.basicOpen (a j) := fun x hx => TopologicalSpace.Opens.mem_iSup.2 (ha x hx)
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j => X.basicOpen (a j)) q := by
    intro i j
    change resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q i) =
      resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q j)
    have hV : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ V := inf_le_left.trans (X.basicOpen_le _)
    have e1 := congrArg (resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq j)
    have e3 := congrArg (resG X hV) (hab i j)
    rw [map_mul, rr, rr] at e1 e2
    rw [map_mul, map_mul, e1, e2] at e3
    have u := (isUnit_res hV (a i) inf_le_left).mul (isUnit_res hV (a j) inf_le_right)
    apply u.mul_right_cancel
    linear_combination e3
  obtain ⟨r, hr'⟩ : ∃ r : Γ(X, V), ∀ j, resG X (X.basicOpen_le (a j)) r = q j :=
    (X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (a j)) V
      (fun j => homOfLE (X.basicOpen_le _)) hcov q hcomp).exists
  have key : ∀ j, b j = r * a j := by
    intro j
    refine X.sheaf.eq_of_locally_eq' (fun j => X.basicOpen (a j)) V
      (fun j => homOfLE (X.basicOpen_le _)) hcov _ _ fun k => ?_
    change resG X (X.basicOpen_le (a k)) _ = resG X (X.basicOpen_le (a k)) _
    apply (hu k).mul_right_cancel
    rw [← map_mul, hab j k, map_mul, map_mul, hr', hq k]
    ring
  have hunit : IsUnit r := by
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x hx => ?_
    obtain ⟨j, hj⟩ := ha x hx
    have := hb j hj
    rw [key j, Scheme.basicOpen_mul] at this
    exact (Scheme.mem_basicOpen X r x hx).1 this.1
  exact ⟨hunit.unit, key⟩

theorem exists_pt (x : X) :
    ∃ (K : Type) (_ : Field K) (p : Sp K ⟶ X), ∀ U : X.Opens, ⊤ ≤ p ⁻¹ᵁ U ↔ x ∈ U := by
  refine ⟨X.residueField x, inferInstance, X.fromSpecResidueField x, fun U => ?_⟩
  have e := Scheme.fromSpecResidueField_apply x
  constructor
  · intro hU
    have := hU (Set.mem_univ (IsLocalRing.closedPoint (X.residueField x)))
    exact e _ ▸ this
  · intro hx y _
    exact (congrArg (· ∈ U) (e y)).mpr hx

theorem mem_chart {H : LB X} (t : H.Sec) (l : H.ι) {x : X} (hx : x ∈ nonzeroLocus t) (hl : x ∈ H.U l) :
    x ∈ X.basicOpen (t.f l) := by
  have hu := SecRatio.isUnit_res t l (V := nonzeroLocus t ⊓ H.U l) inf_le_left inf_le_right
  have : x ∈ X.basicOpen (resG X (inf_le_right : nonzeroLocus t ⊓ H.U l ≤ _) (t.f l)) := by
    rw [Scheme.basicOpen_of_isUnit _ hu]; exact ⟨hx, hl⟩
  exact ((mem_res _ _ _).1 this).2

variable {H H' : LB X} {J : Type} {s : J → H.Sec} {s' : J → H'.Sec}

theorem val_prop (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v)
    {K : Type} [Field K] (x : Sp K ⟶ X) (i : H.ι) (i' : H'.ι) (hi : ⊤ ≤ x ⁻¹ᵁ H.U i)
    (hi' : ⊤ ≤ x ⁻¹ᵁ H'.U i') :
    ∃ c : Kˣ, ∀ j, valR x _ ((s' j).f i') = c * valR x _ ((s j).f i) := by
  have h1 : Crd H s x (fun j => valR x _ ((s j).f i)) := ⟨i, 1, hi, fun j => by simp⟩
  have h2 : Crd H' s' x (fun j => valR x _ ((s' j).f i')) := ⟨i', 1, hi', fun j => by simp⟩
  exact CrdCalc.crd_unique (h K x _ h1) h2

theorem exists_chart_unit [IsReduced X] (hs : ⨆ j, nonzeroLocus (s j) = ⊤)
    (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v)
    (i : H.ι) (i' : H'.ι) : ∃ w : Γ(X, H'.U i' ⊓ H.U i)ˣ, ∀ j,
      resG X inf_le_left ((s' j).f i') = w.val * resG X inf_le_right ((s j).f i) := by
  have hv : ∀ x ∈ H'.U i' ⊓ H.U i, ∃ (K : Type) (_ : Field K) (φ : Γ(X, H'.U i' ⊓ H.U i) →+* K) (c : Kˣ),
      (∀ j, φ (resG X inf_le_left ((s' j).f i')) = c * φ (resG X inf_le_right ((s j).f i))) ∧
      ∀ f, IsUnit (φ f) ↔ x ∈ X.basicOpen f := by
    intro x hx
    obtain ⟨K, _, p, hp⟩ := exists_pt x
    obtain ⟨c, hc⟩ := val_prop h p i i' ((hp _).2 hx.2) ((hp _).2 hx.1)
    refine ⟨K, inferInstance, CrdCalc.valHom p _ ((hp _).2 hx), c, fun j => ?_, fun f => ?_⟩
    · rw [← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res _ _ ((hp _).2 hx),
        CrdCalc.valR_res _ _ ((hp _).2 hx), hc]
    · rw [← CrdCalc.valR_eq, CrdCalc.isUnit_valR_iff _ _ ((hp _).2 hx), hp]
  apply exists_unit
  · intro x hx
    have : x ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj hx.2⟩⟩
  · intro j x hx
    have hx' := X.basicOpen_le _ hx
    obtain ⟨K, _, φ, c, hc, hunit⟩ := hv x hx'
    rw [← hunit, hc, Units.isUnit_units_mul, hunit]
    exact hx
  · intro j k
    rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' := X.basicOpen_le _ hx
    obtain ⟨K, _, φ, c, hc, hunit⟩ := hv x hx'
    have := (hunit _).2 hx
    rw [map_sub, map_mul, map_mul, hc, hc] at this
    exact (this.ne_zero (by ring)).elim

theorem exists_iso_of_crd : ∀ (X : Scheme.{0}) [IsIntegral X] (H H' : LB X) (J : Type) (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → (∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v) → ∃ w : LB.Iso H H', w.IsGen ∧ ∀ j (x : X) (i : H.ι) (i' : H'.ι), x ∈ H.U i → x ∈ H'.U i' → gs (𝟙 X) x _ ((s' j).f i') = gs (𝟙 X) x _ (w.s (i', i)).val * gs (𝟙 X) x _ ((s j).f i) := by
  intro X _ H H' J s s' _ _ hs h
  choose w hw using exists_chart_unit hs h
  refine ⟨⟨fun p => w p.2 p.1⟩, ?_, ?_⟩
  · rintro ⟨i', i⟩ ⟨k', k⟩
    apply Units.ext
    have hi' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U i' := inf_le_left.trans inf_le_left
    have hi : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U i := inf_le_left.trans inf_le_right
    have hk' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U k' := inf_le_right.trans inf_le_left
    have hk : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U k := inf_le_right.trans inf_le_right
    refine cancel (V := H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k)) (fun j => resG X hi ((s j).f i)) ?_ fun j => ?_
    · intro x hx
      have : x ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
      exact ⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj (hi hx)⟩⟩
    · have e1 := congrArg (resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw i i' j)
      have e2 := congrArg (resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw k k' j)
      rw [map_mul, rr, rr] at e1 e2
      have e3 := SecRatio.compat_res (s j) i k hi hk
      have e4 := SecRatio.compat_res (s' j) i' k' hi' hk'
      have e5 : ((res (le_inf hi hk) (H.g i k))⁻¹).val * resG X (le_inf hi hk) (H.g i k).val = 1 :=
        Units.inv_mul _
      change resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w i i').val *
          resG X hi ((s j).f i) =
        resG X (le_inf hi' hk') (H'.g i' k').val * ((res (le_inf hi hk) (H.g i k))⁻¹).val *
          resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val * resG X hi ((s j).f i)
      rw [← e1, e4, e2, e3]
      linear_combination (-(resG X (le_inf hi' hk') (H'.g i' k').val *
        resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val *
        resG X hk ((s j).f k))) * e5
  · intro j x i i' hi hi'
    have hx : (𝟙 X : X ⟶ X) x ∈ H'.U i' ⊓ H.U i := ⟨hi', hi⟩
    have e := congrArg (gs (𝟙 X) x (H'.U i' ⊓ H.U i)) (hw i i' j)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx] at e
    exact e

end GlobalTheory.ZH.CrdIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClassicalPointOfLargeTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_finset_closure_eq_top {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {X : Scheme.{0}}
    (s : X ⟶ Sp o) [LocallyOfFiniteType s] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ t : Finset Γ(X, W), Subring.closure (t : Set Γ(X, W)) = ⊤ := by
  have h1 : (s.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (algebraMap ℤ o).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h4 := (h1.comp h2).comp h3
  have h5 : (algebraMap ℤ Γ(X, W)).FiniteType := by
    convert h4 using 1
    exact RingHom.ext_int _ _
  obtain ⟨t, ht⟩ := (RingHom.finiteType_algebraMap.1 h5).out
  refine ⟨t, ?_⟩
  rw [Algebra.adjoin_int] at ht
  exact top_unique fun x _ => (show x ∈ subalgebraOfSubring (Subring.closure (t : Set Γ(X, W))) from
    ht ▸ Algebra.mem_top)

theorem exists_factor_of_closure {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* C) (j : B →+* C)
    (hj : Function.Injective j) {t : Set A} (ht : Subring.closure t = ⊤) (h : ∀ a ∈ t, φ a ∈ j.range) :
    ∃ ψ : A →+* B, j.comp ψ = φ := by
  have h1 : ∀ a, φ a ∈ j.range := fun a =>
    (Subring.closure_le.2 (show t ⊆ (j.range.comap φ : Subring A) from h)) (ht ▸ Subring.mem_top a)
  let e : B ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ hx => hj (congrArg Subtype.val hx), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict j.range h1), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, h1 a⟩)

theorem preimage_comp_eq_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens)
    (hne : (U₀ : Set M.Z).Nonempty) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R)
    (hu : ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom)
    {K : Type} [Field K] (t : Sp K ⟶ U₀.toScheme) (a : R) :
    (Spec.preimage (t ≫ u₀)).hom a = M.val (t ≫ U₀.ι) a := by
  have hle : (⊤ : U₀.toScheme.Opens) ≤ U₀.ι ⁻¹ᵁ U₀ := fun x _ => x.2
  have hs : Function.Surjective (U₀.ι.appLE U₀ ⊤ hle).hom := by
    have : IsIso (U₀.ι.appLE U₀ ⊤ hle) := inferInstance
    exact (asIso (U₀.ι.appLE U₀ ⊤ hle)).commRingCatIsoToRingEquiv.surjective
  obtain ⟨f, hf⟩ := hs ((u₀.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  have key : ∀ (L : Type) [Field L] (x : Sp L ⟶ U₀.toScheme),
      (Spec.preimage (x ≫ u₀)).hom a = valF (x ≫ U₀.ι) U₀ f := by
    intro L _ x
    rw [preimage_apply, ← valR_appLE x u₀ (U := ⊤) (V := ⊤) le_top (le_preimage_top _), ← hf,
      valR_appLE x U₀.ι hle (le_preimage_top _)]
    rfl
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hne)
  have h1 := key Ω (IsOpenImmersion.lift U₀.ι M.pt hr)
  rw [hu _ (IsOpenImmersion.lift_fac _ _ _), IsOpenImmersion.lift_fac, Spec.preimage_map] at h1
  rw [key K t]
  refine (RatModel.val_eq ?_ h1.symm).symm
  rintro _ ⟨w, rfl⟩
  exact (t w).2

theorem exists_fac_of_large_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → Nonempty (Q.Fac y u) := by
  intro o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y hy
  have hO := hB.ov
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    RatModel.norm_val_le_one (y := y) rfl (x := algebraMap o Ω a) ((M.O _).algebraMap_mem a)
  have hat : S.At M y y₀ := fun _ => rfl
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y (le_preimage_top y)
  haveI := hA.ft
  haveI := M.lft
  obtain ⟨t, ht⟩ := exists_finset_closure_eq_top M.s hW
  refine ⟨y₀, t.image (fun f => (((valMap y W hyW).hom f : OO p) : PadicAlgCl p)), hn, fun u hu => ?_⟩
  have hj : Function.Injective u.j := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V)
      ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (congrArg Subtype.val h))
  obtain ⟨ψ, hψ⟩ := exists_factor_of_closure (valMap y W hyW).hom u.j hj ht (by
    intro a ha
    obtain ⟨x, hx⟩ := hu _ (Finset.mem_image_of_mem _ ha)
    obtain ⟨v, hv⟩ := (u.norm_le x).1 (by rw [hx]; exact (mem_OO_iff _).1 (Subtype.prop _))
    exact ⟨v, Subtype.ext (by rw [← hx, ← hv]; rfl)⟩)
  let yV : Sp u.V ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec
  have hfac : spMap u.j ≫ yV = y := by
    rw [← specMap_valMap_fromSpec hW y hyW, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    rfl
  have hg : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V ≫ yV = gPt p ≫ y := by
    have e : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V = gPt p ≫ spMap u.j := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [← hfac, ← Category.assoc, e, Category.assoc]
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) w)]
    rw [← hg] at hw
    exact hw
  refine ⟨⟨hat, yV, hfac, IsOpenImmersion.lift U₀.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩⟩
  rw [← Spec.map_preimage (IsOpenImmersion.lift U₀.ι _ hr ≫ Q.u₀)]
  congr 1
  ext a
  apply (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective
  have h1 := preimage_comp_eq_val M U₀ hO.ne S.R Q.u₀ Q.u₀_pt
    (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ IsOpenImmersion.lift U₀.ι _ hr) a
  rw [Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, hg, ← hat a, Spec.preimage_comp,
    Spec.preimage_map] at h1
  exact h1.trans (DFunLike.congr_fun u.fac a).symm

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology

theorem exists_lift_valR {O T : Type} [CommRing O] [IsLocalRing O] [CommRing T] [IsLocalRing T] (π : O →+* T)
    [IsLocalHom π] {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (c : Sp O ⟶ X) (ce : Sp T ⟶ Y)
    (h : ce ≫ i = spMap π ≫ c) (U : Y.Opens) (hU : ⊤ ≤ ce ⁻¹ᵁ U) (f : Γ(Y, U)) :
    ∃ (U' : X.Opens) (f' : Γ(X, U')), ⊤ ≤ c ⁻¹ᵁ U' ∧ π (valR c U' f') = valR ce U f := by
  have hy : ce (cpt T) ∈ U := hU trivial
  obtain ⟨a, ha⟩ := i.stalkMap_surjective (ce (cpt T)) ((Y.presheaf.germ U _ hy).hom f)
  obtain ⟨U', hU', f', rfl⟩ := X.presheaf.germ_exist a
  have hcl : spMap π (cpt T) = cpt O := IsLocalRing.comap_closedPoint π
  have h1 : (spMap π ≫ c) (cpt T) ∈ U' := by rw [← h]; exact hU'
  have h2 : ⊤ ≤ c ⁻¹ᵁ U' := (top_le_iff_cpt c U').2 (by rw [← hcl]; exact h1)
  refine ⟨U', f', h2, toStkA_injective ?_⟩
  rw [toStkA_map_valR π c U' _ h2, toStkA_valR_eq_gs ce U _ hU, ← h, ← gs_pull ce i _ U' hU',
    gs_eq ce _ U hy, gs_eq ce _ (i ⁻¹ᵁ U') hU', ← Scheme.Hom.germ_stalkMap_apply ce U _ hy,
    ← Scheme.Hom.germ_stalkMap_apply ce (i ⁻¹ᵁ U') _ hU', ← ha]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply i U' _ hU' f').symm

variable {p : ℕ} [Fact p.Prime]

theorem exists_finite_values {V : Type} [CommRing V] (j : V →+* OO p) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K₀] (hj : ∀ x, (j x : PadicAlgCl p) ∈ K₀) {X : Scheme.{0}} (s : X ⟶ Sp V)
    [LocallyOfFiniteType s] (c : Sp (OO p) ⟶ X) (hc : c ≫ s = spMap j) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      ∀ (U : X.Opens), ⊤ ≤ c ⁻¹ᵁ U → ∀ f, ((valR c U f : OO p) : PadicAlgCl p) ∈ K := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := c (cpt _)) (U := ⊤) trivial
  have hWt : ⊤ ≤ c ⁻¹ᵁ W := (top_le_iff_cpt c W).2 hyW
  have hft : (s.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  letI := (s.appLE ⊤ W le_top).hom.toAlgebra
  obtain ⟨t, ht⟩ := hft.1
  let φ : Γ(X, W) →+* PadicAlgCl p := (OO p).subtype.comp (CrdCalc.valHom c W hWt)
  have hφ : ∀ f, φ f = ((valR c W f : OO p) : PadicAlgCl p) := fun f => by
    rw [CrdCalc.valR_eq c W hWt]; rfl
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W)))) :=
    haveI : Finite (φ '' (t : Set Γ(X, W))) := ((t.finite_toSet).image φ).to_subtype
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨K₀ ⊔ IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W))), inferInstance, ?_⟩
  set K := K₀ ⊔ IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W)))
  have hall : ∀ f, φ f ∈ K := fun f => by
    have hf : f ∈ Algebra.adjoin Γ(Sp V, ⊤) (t : Set Γ(X, W)) := ht ▸ trivial
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact (le_sup_right : _ ≤ K) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      refine (le_sup_left : _ ≤ K) ?_
      have e : (s.appLE ⊤ W le_top ≫ c.appLE W ⊤ hWt ≫ (Scheme.ΓSpecIso (CommRingCat.of (OO p))).hom) =
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom ≫ CommRingCat.ofHom j := by
        rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality]
        refine congrArg (· ≫ _) ((Scheme.Hom.appLE_comp_appLE c s ⊤ W ⊤ le_top hWt).trans ?_)
        simp only [hc]
        rfl
      have e' : CrdCalc.valHom c W hWt (algebraMap Γ(Sp V, ⊤) Γ(X, W) r) =
        j ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r) := congrArg (fun q => q.hom r) e
      have := hj ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r)
      rw [← e'] at this
      exact this
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  intro U hU f
  obtain ⟨g, hgU, hyg⟩ := hW.exists_basicOpen_le ⟨c (cpt _), hU trivial⟩ hyW
  have hgt : ⊤ ≤ c ⁻¹ᵁ X.basicOpen g := (top_le_iff_cpt c _).2 hyg
  have := hW.isLocalization_basicOpen g
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) (resG X hgU f)
  have e2 := congrArg (valR c (X.basicOpen g)) e
  rw [CrdCalc.valR_mul c _ hgt, CrdCalc.valR_res c hgU hgt] at e2
  have r1 : ∀ b : Γ(X, W), valR c (X.basicOpen g) (algebraMap Γ(X, W) Γ(X, X.basicOpen g) b) = valR c W b :=
    fun b => CrdCalc.valR_res c (X.basicOpen_le g) hgt b
  rw [r1, r1] at e2
  have hu : IsUnit (valR c W g) := (CrdCalc.isUnit_valR_iff c W hWt g).2 hgt
  have hg0 : φ (g ^ n) ≠ 0 := by
    rw [map_pow, hφ]
    exact pow_ne_zero _ (hu.map (OO p).subtype).ne_zero
  have e3 : ((valR c U f : OO p) : PadicAlgCl p) = φ a / φ (g ^ n) := by
    rw [eq_div_iff hg0, hφ, hφ]
    exact congrArg Subtype.val e2
  rw [e3]
  exact div_mem (hall _) (hall _)

theorem exists_tendsto (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {r : ℝ}
    (hr : r < 1) (ω : ℕ → PadicAlgCl p) (hK : ∀ e, ω e ∈ K) (h : ∀ e, ‖ω (e + 1) - ω e‖ ≤ r ^ (e + 1)) :
    ∃ a, Tendsto ω atTop (𝓝 a) := by
  have hc : CauchySeq ω := cauchySeq_of_le_geometric r r hr fun e => by
    rw [dist_comm, dist_eq_norm, ← pow_succ']; exact h e
  haveI : FiniteDimensional ℚ_[p] K.toSubmodule := inferInstanceAs (FiniteDimensional ℚ_[p] K)
  obtain ⟨a, -, ha⟩ := cauchySeq_tendsto_of_isComplete K.toSubmodule.complete_of_finiteDimensional hK hc
  exact ⟨a, ha⟩

theorem hasSum_of_levels {Ix : Type} {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) (x : Ix → PadicAlgCl p)
    (s : ℕ → PadicAlgCl p) (a : PadicAlgCl p) (hs : Tendsto s atTop (𝓝 a))
    (h : ∀ e, ∃ S : Finset Ix, ∀ T, S ⊆ T → ‖s e - ∑ i ∈ T, x i‖ ≤ r ^ (e + 1)) : HasSum x a := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have h1 := (Metric.tendsto_nhds.1 hs) (ε / 2) (half_pos hε)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr).comp (tendsto_add_atTop_nat 1)
  have h3 := h2.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨e, he1, he2⟩ := (h1.and h3).exists
  obtain ⟨S, hS⟩ := h e
  refine ⟨S, fun T hT => ?_⟩
  have := hS T hT
  rw [← dist_eq_norm, dist_comm] at this
  have h4 := dist_triangle (∑ i ∈ T, x i) (s e) a
  simp only [Function.comp] at he2
  linarith

end GlobalTheory.ZH.IntegralSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoIsMonHomOfIsGtOfRangeEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem ker_le_ker_of_range_subset_of_isReduced {X T Y : Scheme.{0}} [IsReduced T] (f : X ⟶ Y)
    [IsClosedImmersion f] (g : T ⟶ Y) (h : Set.range g ⊆ Set.range f) : f.ker ≤ g.ker := by
  refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker g
    ⟨Set.range f, f.isClosedEmbedding.isClosed_range⟩ h)
  rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  exact f.range_subset_ker_support

theorem exists_iso_isMonHom_of_isGt_of_range_eq :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Over (Sp k)) (E E' : SplitExt (Sp k)) (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (f : G ⟶ Y) (f' : G' ⟶ Y), E.IsGt G → E'.IsGt G' → IsClosedImmersion f.left → IsClosedImmersion f'.left → Set.range f.left = Set.range f'.left → η[G] ≫ f = η[G'] ≫ f' → ∃ e : G ≅ G', IsMonHom e.hom ∧ e.hom ≫ f' = f := by
  intro k _ _ Y E E' G G' _ _ _ _ f f' h h' hf hf' hr h1
  have hs := (UnitRigidity.smooth_geometricallyConnected_of_isGt E G h).1
  have hs' := (UnitRigidity.smooth_geometricallyConnected_of_isGt E' G' h').1
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have : IsReduced G'.left := isReduced_of_smooth_of_isReduced G'.hom
  have hk : f'.left.ker = f.left.ker :=
    le_antisymm (ker_le_ker_of_range_subset_of_isReduced _ _ hr.le)
      (ker_le_ker_of_range_subset_of_isReduced _ _ hr.ge)
  have := IsClosedImmersion.isIso_lift f'.left f.left hk
  have hl := IsClosedImmersion.lift_fac f'.left f.left hk.le
  let e : G ≅ G' := Over.isoMk (asIso (IsClosedImmersion.lift f'.left f.left hk.le)) (by
    rw [asIso_hom, ← Over.w f', reassoc_of% hl, Over.w f])
  have he : e.hom ≫ f' = f := Over.OverMorphism.ext hl
  have : Mono f' := Over.mono_of_mono_left f'
  refine ⟨e, isMonHom_of_isGt_of_one k E E' G G' h h' e.hom ?_, he⟩
  rw [← cancel_mono f', Category.assoc, he, h1]

end GlobalTheory
end

