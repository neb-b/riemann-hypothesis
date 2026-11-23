module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : _root_.GlobalTheory.ZH.RatModel o Ω) in
theorem _root_.GlobalTheory.ZH.RatModel.locallyOfFiniteType_int [Algebra.FiniteType ℤ o] :
    LocallyOfFiniteType (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) := by
  haveI := M.lft
  haveI : LocallyOfFiniteType (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  infer_instance


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : _root_.GlobalTheory.ZH.RatModel o Ω) in
theorem _root_.GlobalTheory.ZH.RatModel.flat_int [CharZero Ω] (π : M.Z ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ) : Flat π := by
  rw [Flat.iff_flat_stalkMap]
  intro x
  haveI : CharZero (M.Z.presheaf.stalk x) :=
    RingHom.charZero ((M.O x).val.toRingHom.comp
      (M.stalkEquiv x).toRingHom)
  let q : PrimeSpectrum ℤ := π x
  haveI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra ((Spec.structureSheaf ℤ).presheaf.stalk q) (M.Z.presheaf.stalk x) :=
    (π.stalkMap x).hom.toAlgebra
  have hflat : Module.Flat ℤ (M.Z.presheaf.stalk x) := inferInstance
  have hT : @IsScalarTower ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q)
      (M.Z.presheaf.stalk x)
      (StructureSheaf.stalkAlgebra ℤ q).toSMul this.toSMul (AddCommGroup.toIntModule _).toSMul := by
    refine @IsScalarTower.mk ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q)
      (M.Z.presheaf.stalk x)
      (StructureSheaf.stalkAlgebra ℤ q).toSMul this.toSMul (AddCommGroup.toIntModule _).toSMul
      (fun n s m => ?_)
    have h1 := @Algebra.smul_def' ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
      (StructureSheaf.stalkAlgebra ℤ q) n s
    have h2 : @algebraMap ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra ℤ q) n = n :=
      eq_intCast _ n
    rw [h2] at h1
    erw [h1]
    rw [mul_smul, Int.cast_smul_eq_zsmul]
  exact (@Module.flat_iff_of_isLocalization ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
    (StructureSheaf.stalkAlgebra ℤ q) q.asIdeal.primeCompl (StructureSheaf.IsLocalization.to_stalk ℤ q)
    (M.Z.presheaf.stalk x) _ _ _ hT).mpr hflat

end GlobalTheory.ZH.RatModel

namespace GlobalTheory.ZH


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
theorem _root_.GlobalTheory.ZH.classical_points_and_local_regularity :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [Algebra.FiniteType ℤ o] [CharZero Ω]
      (M : _root_.GlobalTheory.ZH.RatModel o Ω)
      (U₀ : M.Z.Opens), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z →
      ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty →
        ∀ z : M.Z, IsClosed ({z} : Set M.Z) →
        (∃ (p : ℕ) (_ : Fact p.Prime)
          (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
          M.Cen U₁ z y) ∧
        ∀ φ ∈ M.ringOn U₁,
          (∀ (p : ℕ) [Fact p.Prime]
            (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
            M.Cen U₁ z y →
            ‖M.val (_root_.GlobalTheory.ZH.gPt p ≫ y) φ‖ ≤ 1) →
          φ ∈ M.O z) ∧ JacobsonSpace M.Z) := by
  intro o Ω _ _ _ _ _ M U₀ hN
  haveI := _root_.GlobalTheory.ZH.RatModel.locallyOfFiniteType_int M
  haveI : Flat (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) := M.flat_int _
  refine ⟨fun U₁ _ hU₁ z hz => ⟨?_, ?_⟩,
    _root_.GlobalTheory.jacobsonSpace_of_locallyOfFiniteType_int (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o))⟩
  · obtain ⟨p, hp, y, h1, h2⟩ := _root_.GlobalTheory.padicAlgCl_integral_points.1 M.Z
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) z hz U₁ hU₁
    exact ⟨p, hp, y, h1, h2⟩
  · intro φ hφ hb
    obtain ⟨f, rfl⟩ :=
      (_root_.GlobalTheory.ZH.RatModel.mem_ringOn_iff_exists hU₁).1 hφ
    haveI := _root_.GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hN z
    haveI : IsIntegrallyClosed (M.Z.presheaf.stalk z) :=
      IsIntegrallyClosed.of_equiv (M.stalkEquiv z).symm
    have hbounded : ∀ (p : ℕ) [Fact p.Prime]
        (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
        y (_root_.GlobalTheory.ZH.cPt p) = z →
        Set.range (_root_.GlobalTheory.ZH.gPt p ≫ y) ⊆ U₁ →
        ‖_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valF
          (_root_.GlobalTheory.ZH.gPt p ≫ y) U₁ f‖ ≤ 1 := by
      intro p _ y hy hr
      have hle := hb p y ⟨hy, hr⟩
      rwa [_root_.GlobalTheory.ZH.RatModel.val_valF hr] at hle
    haveI : Nonempty U₁ := hU₁.to_subtype
    obtain ⟨p, hp, hpx⟩ := _root_.GlobalTheory.exists_prime_residueField_eq_zero
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) hz
    haveI : Fact p.Prime := ⟨hp⟩
    have hm := _root_.GlobalTheory.mem_range_stalk_of_forall_norm_le_one
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) hz hpx (φ := f) fun K _ y hy hyx => by
        haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
        have e : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) ≫ y =
            spMap K.val.toRingHom ≫
              Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y := by
          rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
          rfl
        have h1 : (spMap (integralClosureToPadicAlgClIntegers K) ≫ y) (cPt p) =
            y (IsLocalRing.closedPoint (integralClosure ℤ_[p] K)) := by
          refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg y ?_)
          exact IsLocalRing.comap_closedPoint (integralClosureToPadicAlgClIntegers K)
        have h2 : Set.range (gPt p ≫ (spMap (integralClosureToPadicAlgClIntegers K) ≫ y)) ⊆ U₁ := by
          rw [e]
          rintro _ ⟨q, rfl⟩
          exact hy (Set.mem_univ (spMap K.val.toRingHom q))
        have h3 : valF (gPt p ≫ (spMap (integralClosureToPadicAlgClIntegers K) ≫ y)) U₁ f =
            (((Scheme.ΓSpecIso (.of K)).hom
              ((Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE
                U₁ ⊤ hy f) : K) : PadicAlgCl p) := by
          rw [e]
          have ht : ⊤ ≤ (spMap K.val.toRingHom ≫
              (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y)) ⁻¹ᵁ U₁ :=
            fun q _ => hy (Set.mem_univ (spMap K.val.toRingHom q))
          rw [valF, dite_eq_left ht]
          have eqn : (spMap K.val.toRingHom ≫
              (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y)).appLE U₁ ⊤ ht ≫
              (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).hom =
              (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE U₁ ⊤ hy ≫
              (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom K.val.toRingHom := by
            rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap K.val.toRingHom) _ U₁ ⊤ ⊤ hy le_rfl, Category.assoc]
            rfl
          exact congrArg (fun g => g.hom f) eqn
        rw [← h3]
        exact hbounded p (spMap (integralClosureToPadicAlgClIntegers K) ≫ y) (h1.trans hyx) h2
    obtain ⟨W, hW, ψ, hzW, -, hs⟩ :=
      _root_.GlobalTheory.exists_germToFunctionField_eq_of_mem_range_stalk hm (W := ⊤) trivial
    have hg : ∀ (W : M.Z.Opens) [Nonempty W], genericPoint M.Z ∈ W := fun W h =>
      ((genericPoint_spec M.Z).mem_open_set_iff W.isOpen).mpr (by simpa using h)
    haveI : Nonempty (W ⊓ U₁ : M.Z.Opens) := ⟨⟨_, hg W, hg U₁⟩⟩
    have h := M.Z.germToFunctionField_injective (W ⊓ U₁)
      ((M.Z.presheaf.germ_res_apply (homOfLE inf_le_left) _ _ ψ).trans
        (hs.trans (M.Z.presheaf.germ_res_apply (homOfLE inf_le_right) _ _ f).symm))
    rw [_root_.GlobalTheory.ZH.RatModel.mem_O]
    refine ⟨W, ψ, hzW, ?_⟩
    have hne := M.nonempty_inf ⟨z, hzW⟩ hU₁
    have hv := congrArg (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valF M.pt _) h
    rwa [M.valF_resG _ hne,
      M.valF_resG _ hne] at hv

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsRegular
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.MinorModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem locallyOfFiniteType_int [Algebra.FiniteType ℤ o] :
    LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  haveI := M.lft
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  infer_instance

theorem flat_int_sections [CharZero Ω] (U : M.Z.Opens) : Module.Flat ℤ Γ(M.Z, U) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨n, hn⟩, ha⟩
  rw [Submodule.mem_bot]
  rcases (U : Set M.Z).eq_empty_or_nonempty with hU | hU
  · obtain rfl : U = ⊥ := SetLike.coe_injective hU
    exact Subsingleton.elim _ _
  · have h : n • M.res U hU a = 0 := by
      rw [← map_zsmul, show n • a = 0 from ha, map_zero]
    exact (map_eq_zero_iff _ (M.res_injective U hU)).1
      ((smul_eq_zero.1 h).resolve_left (nonZeroDivisors.ne_zero hn))

theorem flat_int [CharZero Ω] (π : M.Z ⟶ Sp ℤ) : Flat π := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : M.Z.affineOpens => U)
    (iSup_affineOpens_eq_top _) fun U => ?_
  have e : (π.appLE ⊤ U le_top).hom =
      (algebraMap ℤ Γ(M.Z, U)).comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom := by
    have e' : ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv ≫ π.appLE ⊤ U le_top).hom = algebraMap ℤ Γ(M.Z, U) :=
      RingHom.ext_int _ _
    rw [← e', ← CommRingCat.hom_comp, Iso.hom_inv_id_assoc]
  rw [e]
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.bijective)
    (RingHom.flat_algebraMap_iff.2 (flat_int_sections M U))

end GlobalTheory.ZH.MinorModel

namespace GlobalTheory.ZH.MinorModel

end GlobalTheory.ZH.MinorModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineOpenRingOnEqAdjoinInv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

section

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_of_mul_pow_mem_of_inv_mem {S : Subalgebra o Ω} {d x : Ω} (hd : d ≠ 0) (hi : d⁻¹ ∈ S) {n : ℕ}
    (h : x * d ^ n ∈ S) : x ∈ S := by
  have := S.mul_mem h (S.pow_mem hi n)
  rwa [_root_.mul_assoc, ← mul_pow, mul_inv_cancel₀ hd, one_pow, _root_.mul_one] at this

theorem exists_mul_eq_of_eq_div {R : Subalgebra o Ω} (h : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (x : Ω) :
    ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h x
  by_cases h0 : b = 0
  · exact ⟨0, R.zero_mem, 1, R.one_mem, one_ne_zero, by simp [h0]⟩
  · exact ⟨a, ha, b, hb, h0, div_mul_cancel₀ a h0⟩

theorem exists_adjoin_inv_eq (R B : Subalgebra o Ω) (A : Set Ω) (hR : R.FG) (hB : B.FG)
    (hRf : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (hBf : ∀ x : Ω, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) (hA : A.Finite) :
    ∃ a ∈ R, ∃ c ∈ B, a ≠ 0 ∧ c ≠ 0 ∧
      Algebra.adjoin o (insert c⁻¹ (B : Set Ω)) = Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) ∧
      A ⊆ Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) := by
  obtain ⟨d, hdR, hd0, hd⟩ := exists_mul_pow_mem_of_fg (B ⊔ Algebra.adjoin o A) R
    (hB.sup (Subalgebra.fg_def.2 ⟨_, hA, rfl⟩)) hRf
  obtain ⟨c, hcB, hc0, hc⟩ := exists_mul_pow_mem_of_fg (R ⊔ Algebra.adjoin o {d⁻¹}) B
    (hR.sup (Subalgebra.fg_def.2 ⟨_, Set.finite_singleton _, rfl⟩)) hBf
  obtain ⟨m, hm⟩ := hd c (le_sup_left (a := B) hcB)
  have ha0 : d * (c * d ^ m) ≠ 0 := mul_ne_zero hd0 (mul_ne_zero hc0 (pow_ne_zero _ hd0))
  set S := Algebra.adjoin o (insert (d * (c * d ^ m))⁻¹ (R : Set Ω)) with hS
  set S' := Algebra.adjoin o (insert c⁻¹ (B : Set Ω)) with hS'
  have hRS : ∀ x ∈ R, x ∈ S := fun x hx => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
  have haS : (d * (c * d ^ m))⁻¹ ∈ S := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hdS : d⁻¹ ∈ S := by
    have := S.mul_mem haS (hRS _ hm)
    convert this using 1
    field_simp
  have hcS : c⁻¹ ∈ S := by
    have := S.mul_mem haS (hRS _ (R.mul_mem hdR (R.pow_mem hdR m)))
    convert this using 1
    field_simp
  have h1 : ∀ x ∈ B ⊔ Algebra.adjoin o A, x ∈ S := fun x hx => by
    obtain ⟨n, hn⟩ := hd x hx
    exact mem_of_mul_pow_mem_of_inv_mem hd0 hdS (hRS _ hn)
  have hcS' : c⁻¹ ∈ S' := Algebra.subset_adjoin (Set.mem_insert _ _)
  have h2 : ∀ x ∈ R ⊔ Algebra.adjoin o {d⁻¹}, x ∈ S' := fun x hx => by
    obtain ⟨n, hn⟩ := hc x hx
    exact mem_of_mul_pow_mem_of_inv_mem hc0 hcS' (Algebra.subset_adjoin (Set.mem_insert_of_mem _ hn))
  have hdS' : d⁻¹ ∈ S' := h2 _ (le_sup_right (a := R) (Algebra.subset_adjoin (Set.mem_singleton _)))
  refine ⟨_, R.mul_mem hdR hm, c, hcB, ha0, hc0, le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_),
    fun x hx => h1 x (le_sup_right (a := B) (Algebra.subset_adjoin hx))⟩
  · rintro x (rfl | hx)
    · exact hcS
    · exact h1 x (le_sup_left (a := B) hx)
  · rintro x (rfl | hx)
    · have := S'.mul_mem hdS' (S'.mul_mem hcS' (S'.pow_mem hdS' m))
      rwa [inv_pow, ← mul_inv, ← mul_inv] at this
    · exact h2 x (le_sup_left (a := R) hx)

namespace RatModel

variable {M : RatModel o Ω}

theorem fg_ringOn {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) :
    (M.ringOn V).FG := by
  have := M.lft
  have h1 : (M.s.appLE ⊤ V le_top).hom.FiniteType := M.s.finiteType_appLE (isAffineOpen_top _) hV _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (M.sectionsEquiv V hne).toRingHom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (M.sectionsEquiv V hne).surjective
  have h4 := h3.comp (h1.comp h2)
  have e : (M.sectionsEquiv V hne).toRingHom.comp ((M.s.appLE ⊤ V le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom) = algebraMap o (M.ringOn V) :=
    RingHom.ext fun a => Subtype.ext ((coe_sectionsEquiv V hne _).trans (M.valF_constFn hne a))
  rw [e, RingHom.finiteType_algebraMap] at h4
  exact (Subalgebra.fg_iff_finiteType _).2 h4

theorem nonempty_basicOpen {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) {g : Γ(M.Z, V)}
    (hg : valF M.pt V g ≠ 0) : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  apply hg
  rw [(basicOpen_eq_bot_iff g).1 (SetLike.coe_injective h), ← M.res_apply V hne, map_zero]

theorem ringOn_basicOpen {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) {g : Γ(M.Z, V)}
    (hg0 : valF M.pt V g ≠ 0) :
    M.ringOn (M.Z.basicOpen g) = Algebra.adjoin o (insert (valF M.pt V g)⁻¹ (M.ringOn V : Set Ω)) := by
  have hg := nonempty_basicOpen hne hg0
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hg).1 hx
    have := hV.isLocalization_basicOpen g
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
    have h1 := congrArg (M.res _ hg) ha
    have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
      fun t => M.res_resG (M.Z.basicOpen_le g) hg t
    rw [map_mul, map_pow, h2, h2, res_apply, res_apply, res_apply] at h1
    refine mem_of_mul_pow_mem_of_inv_mem hg0 (Algebra.subset_adjoin (Set.mem_insert _ _)) (n := n) ?_
    rw [h1]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ((mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
  · rintro x (rfl | hx)
    · exact mem_ringOn.2 fun z hz =>
        ((isUnit_O_iff _).1 ((isUnit_valF_iff (M.Z.basicOpen_le g hz) g).2 hz)).2
    · exact ringOn_anti (M.Z.basicOpen_le g) hx

end RatModel

end

theorem exists_affineOpen_ringOn_eq_adjoin_inv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (R : Subalgebra o Ω) (A : Set Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → A.Finite → ∀ W : M.Z.Opens, (W : Set M.Z).Nonempty → ∃ (U₀ : M.Z.Opens) (a : Ω), U₀ ≤ W ∧ (U₀ : Set M.Z).Nonempty ∧ IsAffineOpen U₀ ∧ a ∈ R ∧ a ≠ 0 ∧ M.ringOn U₀ = Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) ∧ A ⊆ M.ringOn U₀ := by
  intro o Ω _ _ _ M R A hR hRf hA W ⟨w, hw⟩
  obtain ⟨V, hV, hwV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := W) hw
  have hne : (V : Set M.Z).Nonempty := ⟨w, hwV⟩
  obtain ⟨a, ha, c, hc, ha0, hc0, he, hAS⟩ := exists_adjoin_inv_eq R (M.ringOn V) A hR
    (RatModel.fg_ringOn hV hne) (exists_mul_eq_of_eq_div hRf) (exists_mul_eq_of_eq_div fun x => by
      obtain ⟨a, b, -, h⟩ := RatModel.exists_eq_div hV hne x
      exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _,
        (RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩, h⟩) hA
  obtain ⟨g, rfl⟩ := (RatModel.mem_ringOn_iff_exists hne).1 hc
  have h := (RatModel.ringOn_basicOpen hV hne hc0).trans he
  exact ⟨M.Z.basicOpen g, a, (M.Z.basicOpen_le g).trans hVW, RatModel.nonempty_basicOpen hne hc0,
    hV.basicOpen g, ha, ha0, h, h ▸ hAS⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulPowMemOOfIsAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem exists_mul_pow_mem_O_of_isAffineOpen {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty)
    {u φ : Ω} (hu0 : u ≠ 0) (hu : ∀ z ∈ V, u ∈ M.O z) (hφ : ∀ z ∈ V, u⁻¹ ∈ M.O z → φ ∈ M.O z) :
    ∃ n : ℕ, ∀ z ∈ V, φ * u ^ n ∈ M.O z := by
  obtain ⟨g, rfl⟩ := (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 hu)
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have h0 : g = 0 := (basicOpen_eq_bot_iff g).1 (SetLike.coe_injective h)
    exact hu0 (by rw [h0, ← M.res_apply V hne, map_zero])
  obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hg (x := φ)).1 (mem_ringOn.2 fun z hz =>
    hφ z (M.Z.basicOpen_le g hz)
      ((isUnit_O_iff _).1 ((isUnit_valF_iff (M.Z.basicOpen_le g hz) g).2 hz)).2)
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, res_apply, res_apply, res_apply] at h1
  exact ⟨n, fun z hz => h1 ▸ valF_mem_O hz a⟩


variable (M) in
theorem noetherianSpace_of_isNoetherianRing [IsNoetherianRing o] : TopologicalSpace.NoetherianSpace M.Z := by
  have := M.lft
  have := M.qc
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  have : AlgebraicGeometry.IsNoetherian M.Z := {}
  infer_instance

theorem exists_forall_mul_pow_mem_O [IsNoetherianRing o] (W : M.Z.Opens)
    {u φ : Ω} (hu0 : u ≠ 0) (hu : ∀ z ∈ W, u ∈ M.O z) (hφ : ∀ z ∈ W, u⁻¹ ∈ M.O z → φ ∈ M.O z) :
    ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ W, φ * u ^ C ∈ M.O z := by
  have := M.noetherianSpace_of_isNoetherianRing
  have hmono : ∀ z ∈ W, ∀ m n : ℕ, m ≤ n → φ * u ^ m ∈ M.O z → φ * u ^ n ∈ M.O z := by
    intro z hz m n hmn h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [pow_add, ← _root_.mul_assoc]
    exact mul_mem h (pow_mem (hu z hz) k)
  have hcov : (W : Set M.Z) ⊆ ⋃ n : ℕ, {z | φ * u ^ n ∈ M.O z} := by
    intro z hz
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (U := W) (x := z) hz
    obtain ⟨n, hn⟩ := exists_mul_pow_mem_O_of_isAffineOpen hV ⟨z, hzV⟩ hu0 (fun w hw => hu w (hle hw))
      (fun w hw => hφ w (hle hw))
    exact Set.mem_iUnion.2 ⟨n, hn z hzV⟩
  obtain ⟨s, hs⟩ := (TopologicalSpace.NoetherianSpace.isCompact (W : Set M.Z)).elim_finite_subcover _
    (fun n => M.isOpen_setOf_mem_O _) hcov
  refine ⟨s.sup id, fun C hC z hz => ?_⟩
  obtain ⟨n, hn, h⟩ := Set.mem_iUnion₂.1 (hs hz)
  exact hmono z hz n C ((Finset.le_sup (f := id) hn).trans hC) h

theorem exists_forall_mul_prod_div_pow_mem_O :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o] (J : Type)
      (t : J → Ω) (W : M.Z.Opens) (j : J), (∀ z ∈ W, M.Div t j z) → ∀ (I : Finset J) (φ : Ω),
      (∀ z ∈ W, (∀ i ∈ I, M.Div t i z) → φ ∈ M.O z) → (∀ i ∈ I, t i ≠ 0) →
      ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ W, φ * (∏ i ∈ I, t i / t j) ^ C ∈ M.O z := by
  intro o Ω _ _ _ M _ J t W j hj I φ hφ hI
  by_cases hW : ∃ z, z ∈ W
  swap
  · exact ⟨0, fun _ _ z hz => (hW ⟨z, hz⟩).elim⟩
  obtain ⟨z₀, hz₀⟩ := hW
  have hj0 : t j ≠ 0 := (hj z₀ hz₀).1
  have hu0 : (∏ i ∈ I, t i / t j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => div_ne_zero (hI i hi) hj0
  refine exists_forall_mul_pow_mem_O W hu0 (fun z hz => prod_mem fun i _ => (hj z hz).2 i) fun z hz hinv => ?_
  refine hφ z hz fun i hi => ((hj z hz).div_iff_isUnit i).2 ((isUnit_O_iff _).2 ⟨div_ne_zero (hI i hi) hj0, ?_⟩)
  have hmem := mul_mem (prod_mem (S := M.O z) (t := I.erase i) fun k _ => (hj z hz).2 k) hinv
  have e : (∏ k ∈ I.erase i, t k / t j) * (∏ k ∈ I, t k / t j)⁻¹ = (t i / t j)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← _root_.mul_assoc, Finset.mul_prod_erase I (fun k => t k / t j) hi, mul_inv_cancel₀ hu0]
  exact e ▸ hmem

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianTorusExtensionOfPotentialModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_semiAbelian_model_torusExtension_of_potModel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'), Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧ ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧ Nonempty (TorusExtension (specialFibre V' G)) := by
  intro V _ _ _ _ K _ _ _ _ A _ hP
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, hW, G, _, hmod, hG⟩ := hP
  have hinj : Function.Injective (algebraMap V W) := by
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  haveI hKL : FiniteDimensional K L := by
    letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
    haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
    haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
    exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)
  obtain ⟨W', _, _, _, hW', _, hfin', hinj', -, hG', hT⟩ := _root_.GlobalTheory.exists_finite_dvr_torusExtension_specialFibre W G hG
  obtain ⟨_, hK', e', hmod'⟩ := _root_.GlobalTheory.SS.model_finite_ext V K A L W e G hmod W' hfin' hinj'
  letI : Algebra V W' := ((algebraMap W W').comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W W' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨FractionRing W', inferInstance, inferInstance, hK', W', inferInstance, inferInstance, inferInstance, hW',
    inferInstance, inferInstance, inferInstance, Module.Finite.trans W W', hinj'.comp hinj, e',
    baseChange W W' G, inferInstance, hG', hmod', hT⟩

end GlobalTheory.SS
end

