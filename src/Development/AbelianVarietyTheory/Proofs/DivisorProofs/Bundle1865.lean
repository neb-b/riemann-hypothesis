module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh
open GlobalTheory.TopForm

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AdaptedFrame


open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
theorem exists_basis_dFun {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ)
    [SmoothOfRelativeDimension D p] {O : Y.Opens} {x : Y} (hxO : x ∈ O) :
    ∃ (U : Y.Opens) (f : Fin D → Γ(Y, U)) (b : Module.Basis (Fin D) Γ(Y, U) (Omega (algX p U))),
      U ≤ O ∧ x ∈ U ∧ IsAffineOpen U ∧ ∀ i, b i = dFun (algX p U) (f i) := by
  classical
  obtain ⟨V, hV, hx, hVO⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hxO
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  letI := (algX p (Y.basicOpen (t : Γ(Y, V)))).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k Γ(Y, Y.basicOpen (t : Γ(Y, V))) := h₂
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    ‹Algebra.IsStandardSmoothOfRelativeDimension D k Γ(Y, Y.basicOpen (t : Γ(Y, V)))›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨_, fun i => P.val (e.symm i), P.basisKaehler.reindex e, (Y.basicOpen_le _).trans hVO, hxt,
    hV.basicOpen _, fun i => by simp⟩

theorem linearIndependent_tmul_D {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] {J : Type} (f : J → A)
    (hf : ∀ j, f j ∈ IsLocalRing.maximalIdeal A)
    (h : LinearIndependent (IsLocalRing.ResidueField A) (fun j =>
      ((IsLocalRing.maximalIdeal A).toCotangent ⟨f j, hf j⟩ : IsLocalRing.CotangentSpace A))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun j => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f j)) := by
  have hs : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) :=
    IsLocalRing.residue_surjective
  have hinj := GlobalTheory.SmoothTangent.kerCotangentToTensor_injective k A (IsLocalRing.ResidueField A) hs
  have hker : IsLocalRing.maximalIdeal A = RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) :=
    IsLocalRing.ker_residue.symm
  let c := Ideal.Cotangent.equivOfEq _ _ hker
  let e : IsLocalRing.CotangentSpace A →ₗ[A] IsLocalRing.ResidueField A ⊗[A] Ω[A⁄k] :=
    KaehlerDifferential.kerCotangentToTensor k A (IsLocalRing.ResidueField A) ∘ₗ c.toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) := hinj.comp c.injective
  have := h.map' (e.extendScalarsOfSurjective hs) (LinearMap.ker_eq_bot.2 he)
  have key : ⇑(e.extendScalarsOfSurjective hs) ∘ (fun j =>
      ((IsLocalRing.maximalIdeal A).toCotangent ⟨f j, hf j⟩ : IsLocalRing.CotangentSpace A)) =
      fun j => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f j) := by
    funext j
    simp only [Function.comp_apply, LinearMap.extendScalarsOfSurjective_apply, e, LinearMap.comp_apply,
    LinearEquiv.coe_coe, c]
    rw [Ideal.Cotangent.equivOfEq_toCotangent, KaehlerDifferential.kerCotangentToTensor_toCotangent]
    rfl
  rw [key] at this
  exact this


open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
theorem formallySmooth_residueField {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    (p : X ⟶ Sp k) {n : ℕ} [SmoothOfRelativeDimension n p] {U : X.Opens} (hU : IsAffineOpen U)
    (y : X) (hy : y ∈ U) [Algebra k (X.presheaf.stalk y)]
    (h : algebraMap k (X.presheaf.stalk y) = (X.presheaf.germ U y hy).hom.comp (algX p U)) :
    Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk y)) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hy).hom.toAlgebra
  letI : Algebra k Γ(X, U) := (algX p U).toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' h
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  have hft : (algX p U).FiniteType := by
    have h₀ := HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    exact RingHom.FiniteType.comp h₀
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  haveI : Algebra.FiniteType k Γ(X, U) := hft
  haveI : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  haveI : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk y) :=
    Algebra.EssFiniteType.of_isLocalization _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  haveI : Algebra.EssFiniteType k (X.presheaf.stalk y) :=
    Algebra.EssFiniteType.comp k Γ(X, U) (X.presheaf.stalk y)
  haveI : Algebra.EssFiniteType (X.presheaf.stalk y) (IsLocalRing.ResidueField (X.presheaf.stalk y)) :=
    inferInstance
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk y)) :=
    Algebra.EssFiniteType.comp k (X.presheaf.stalk y) _
  exact Algebra.FormallySmooth.of_perfectField


open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
theorem exists_adapted_frame : ∀ {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {n : ℕ} [SmoothOfRelativeDimension n p] (y : X) {J : Type}
    [Fintype J] (f : J → X.presheaf.stalk y)
    (hf : ∀ j, f j ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y)),
    LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y))
      (fun j => ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).toCotangent ⟨f j, hf j⟩ :
        IsLocalRing.CotangentSpace (X.presheaf.stalk y))) →
    ∃ (U : X.Opens) (hy : y ∈ U) (z : Fin n → Γ(X, U)) (e : J → Fin n), Function.Injective e ∧
      (∀ j, X.presheaf.germ U y hy (z (e j)) = f j) ∧ IsFrame (dOn p z) := by
  classical
  intro X p n _ y J _ f hf hli

  choose V hyV s hs using fun j => X.presheaf.germ_exist (x := y) (f j)
  let O : X.Opens := ⟨⋂ j, (V j : Set X), isOpen_iInter_of_finite fun j => (V j).isOpen⟩
  have hyO : y ∈ O := Set.mem_iInter.2 hyV
  have hOV (j : J) : O ≤ V j := fun _ hx => Set.mem_iInter.1 hx j
  obtain ⟨U, x, b, hUO, hyU, hU, hb⟩ := exists_basis_dFun p n hyO
  let z₀ : J → Γ(X, U) := fun j => resG X (hUO.trans (hOV j)) (s j)
  have hz₀ (j : J) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j := by
    rw [germ_resG]
    exact hs j

  let a : J → Fin n → Γ(X, U) := fun j l => b.repr (dFun (algX p U) (z₀ j)) l
  have ha (j : J) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l) := by
    conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]
    simp only [hb, a]

  letI iΓ : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  letI iA : Algebra ℂ (X.presheaf.stalk y) :=
    ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra
  letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  haveI : IsScalarTower ℂ Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := formallySmooth_residueField (n := n) p hU y hyU rfl
  have hw := linearIndependent_tmul_D (k := ℂ) f hf hli
  let ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y) :=
    (IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom
  let ab : J → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) := fun j l => ρ (a j l)
  have hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab := by
    let wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y]
        Ω[(X.presheaf.stalk y)⁄ℂ] :=
      fun l => 1 ⊗ₜ KaehlerDifferential.D ℂ (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))
    refine LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_
    have key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab =
        fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y]
          KaehlerDifferential.D ℂ (X.presheaf.stalk y) (f j) := by
      funext j
      rw [Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]
      have e1 := congrArg (KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)) (ha j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at e1
      change KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D ℂ Γ(X, U) (z₀ j)) = _ at e1
      rw [KaehlerDifferential.map_D] at e1
      change KaehlerDifferential.D ℂ (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1
      rw [e1, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      change _ = 1 ⊗ₜ (a j l • KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D ℂ Γ(X, U) (x l)))
      rw [KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l),
        TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]
      rfl
    rw [key]
    exact hw

  obtain ⟨e, he, hdet⟩ := _root_.GlobalTheory.extend_linearIndependent_rows_by_standard_basis ab hab
  let z : Fin n → Γ(X, U) := Function.extend e z₀ x
  let c : Matrix (Fin n) (Fin n) Γ(X, U) :=
    Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))
  have hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l) := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simp only [z, c, Matrix.of_apply, he.extend_apply]
      exact ha j
    · simp only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
      simp [Pi.single_apply]
  have hform : dOn p z = c.det • dOn p x := dForm_eq_det_smul z x c hdz
  have hρ : ρ c.det ≠ 0 := by
    have hm : c.map ρ = Matrix.of (Function.extend e ab
        (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)))) := by
      ext i l
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        simp only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]
      · simp only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
        by_cases hil : l = i
        · subst hil
          simp
        · simp [Pi.single_apply, hil]
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hm).trans_ne hdet
  have hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ
  have hyW : y ∈ X.basicOpen c.det := (X.mem_basicOpen c.det y hyU).2 hunit
  have hWU : X.basicOpen c.det ≤ U := X.basicOpen_le _
  refine ⟨X.basicOpen c.det, hyW, fun i => resG X hWU (z i), e, he, fun j => ?_, ?_⟩
  · rw [germ_resG]
    simp only [z, he.extend_apply]
    exact hz₀ j
  · have hx : IsFrame (dOn p x) := ⟨hU, isFreeGen_dForm x b hb⟩
    have h1 := hx.res (hU.basicOpen c.det) hWU
    refine ⟨hU.basicOpen c.det, ?_⟩
    rw [← resForm_dOn hWU, hform, resForm_smul]
    exact h1.gen.smul_iff.2 (RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det)

end GlobalTheory.AdaptedFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem stalkClosedPointTo_ger {V : Type} [CommRing V] [IsLocalRing V] {Y : Scheme.{0}} (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W) :
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (ger _ hy g) = GlobalTheory.TangentOrigin.evalPt x W h g := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have := congrArg (fun φ => φ.hom g) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp only [GlobalTheory.TangentOrigin.evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
  congr!

theorem val_eq_lift_residue {k K : Type} [CommRing k] [Field K] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens}
    (x : Sp K ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hy : ptOf x ∈ O) (hj : ptOf x ∈ B.U i)
    (f : H0 p B O) :
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom :=
      Scheme.isLocalHom_stalkClosedPointTo' (R := K) x
    H0.val x i hO hi f = IsLocalRing.ResidueField.lift (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom
      ((Y.residue (ptOf x)).hom (germ i (ptOf x) hy hj f)) := by
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := K) x
  rw [H0.val_apply, H0.germ_apply]
  exact (stalkClosedPointTo_ger x _ _ _ (memInf hy hj)).symm.trans
    (IsLocalRing.ResidueField.lift_residue_apply _ _).symm

open GlobalTheory.CompHt (genVal)
open GlobalTheory.AllWt (exOf secZ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ratGen_of_birOn : ∀ {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw),
    Nonempty (Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) → GlobalTheory.DegVal.BirOn U Z (wtOf Dw la 0) → RatGen X Z U la := by
  intro Y X Z r U la ⟨M⟩ hB
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M h
  have hgen := isGenericPoint_of_lift M h hz hO
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hη : ptOf (z ≫ M.σ) ∈ U₀ X Z := (le_iff_ptOf_mem _ _).1 hU
  have hdense : closure (M.σ '' Set.univ) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (dense_U₀ X Z).closure_eq]
    refine closure_mono fun u hu => ?_
    have hu' : ⊤ ≤ resPt u ⁻¹ᵁ U₀ X Z := (le_iff_ptOf_mem _ _).2 ((ptOf_resPt u).symm ▸ hu)
    obtain ⟨w, hw, -⟩ := M.existsUnique_lift (resPt u) hu'
    refine ⟨ptOf w, trivial, ?_⟩
    rw [← ptOf_comp, hw, ptOf_resPt]
  have hgen' : IsGenericPoint (ptOf (z ≫ M.σ)) Set.univ := by
    have := hgen.image M.σ.continuous
    rwa [hdense] at this
  refine ⟨ptOf (z ≫ M.σ), hη, hgen', ?_⟩
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) (z ≫ M.σ)).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := Om Z) (z ≫ M.σ)
  set ψ := IsLocalRing.ResidueField.lift (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) (z ≫ M.σ)).hom
    with hψ
  have e₁ : (z ≫ M.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  have hO₂ : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  have key : ∀ (i : (L₀ X Z la).ι) (hi : ptOf (z ≫ M.σ) ∈ (L₀ X Z la).U i), ∃ T : Om Z, T ≠ 0 ∧
      ∀ g : Cusp Z U la, ψ (((Y₀ X Z).residue (ptOf (z ≫ M.σ))).hom
        (germ i (ptOf (z ≫ M.σ)) hη hi (cuspSec X Z U la g))) = T * genVal Z g.1 := by
    intro i hi
    have hi' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (L₀ X Z la).U i := (le_iff_ptOf_mem _ _).2 hi
    have hk₂ : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (i PUnit.unit) := (le_iff_ptOf_mem _ _).2 (mem_pull.1 hi)
    have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U (i PUnit.unit) := e₁ ▸ hk₂
    obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) (i PUnit.unit) hk₁
    have hQ₂ : X.F.ChartFr (i PUnit.unit) ((z ≫ M.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
    refine ⟨((∏ ix, t ix ^ exOf Dw la 0 ix : (Om Z)ˣ) : Om Z)⁻¹, inv_ne_zero (Units.ne_zero _), fun g => ?_⟩
    have v₈ := evR_eq_val_secOf ⟨g.1, cusp_le_secZ Z U la g.2⟩ hO₂ hQ₂ ht
    have v₅ : H0.val (z ≫ M.σ) i hU hi' (cuspSec X Z U la g) = H0.val (B := X.LL (exOf Dw la 0))
        ((z ≫ M.σ) ≫ inc₀ X Z) (i PUnit.unit) hO₂ hk₂ (secOf X _ ⟨g.1, cusp_le_secZ Z U la g.2⟩) :=
      H0.val_pull (inc₀ X Z) le_rfl (z ≫ M.σ) i hU hi' hO₂ hk₂ _
    have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
    rw [← val_eq_lift_residue (z ≫ M.σ) i hU hi' hη hi, v₅, v₆, v₈, inv_mul_cancel_left₀ (Units.ne_zero _)]
  have hmap : ∀ v w : Cusp Z U la, ∃ q ∈ ratField (Set.range (cuspSec X Z U la)) (ptOf (z ≫ M.σ)) hη,
      ψ q = genVal Z v.1 / genVal Z w.1 := by
    intro v w
    obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ X Z la) (ptOf (z ≫ M.σ))
    obtain ⟨T, hT, hv⟩ := key i hi
    refine ⟨_, Subfield.subset_closure ⟨i, hi, _, _, ⟨v, rfl⟩, ⟨w, rfl⟩, rfl⟩, ?_⟩
    refine (map_div₀ ψ _ _).trans ?_
    rw [hv, hv, mul_div_mul_left _ _ hT]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Cusp Z U la, genVal Z v₀.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB.1 (LinearMap.ext fun v => hc v)
  have hsub : (⊤ : IntermediateField c.F (Om Z)).toSubfield ≤
      (ratField (Set.range (cuspSec X Z U la)) (ptOf (z ≫ M.σ)) hη).map ψ := by
    rw [← hB.2, GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      obtain ⟨q, hq, e⟩ := hmap ⟨a • v₀.1, Submodule.smul_mem _ a v₀.2⟩ v₀
      refine ⟨q, hq, e.trans ?_⟩
      show genVal Z (a • v₀.1) / genVal Z v₀.1 = _
      rw [map_smul, Algebra.smul_def, mul_div_cancel_right₀ _ hv₀]
    · rintro _ ⟨v, w, rfl⟩
      exact hmap v w
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨q', hq', e⟩ := hsub (show ψ q ∈ (⊤ : IntermediateField c.F (Om Z)).toSubfield from trivial)
  exact (ψ.injective e) ▸ hq'

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHeisenbergInvariantFormEqSmulDiagonalInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostDiagUniq

theorem eq_smul_diagInt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ),
      l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
        l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro D ψ hψ κ _ l hl hinv μ hμ
  exact GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral D.host.F ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) κ l hl hinv μ hμ

end GlobalTheory.HostDiagUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilOperatorDiagonalIntegralHeisenbergPoiStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilOperator_diagonalIntegral_heisenberg_point : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), IsLagrAt σ W v C →
    ∀ d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = M.co.e x) →
    ∀ dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' dd →
    ∀ omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
    IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    ∀ l : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ z : Matrix (Fin d) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l (dd.rho ψ (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) Φ) = l Φ) →
    ∀ r₀ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ,
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), Rest (evFin F v) φ r₀) →
    ∀ c₀ : ℂ, c₀ ≠ 0 → ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) →
    ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) (ρ₀ : ℂ),
    (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l (omd p Φ) = ρ₀ * l Φ) →
    ∀ Φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), ∀ Φ₁ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
    Acts (evFin F v) (omd p) Φ Φ₁ → ∀ z : Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      diagW (psiAt ψ v) μ Φ₁ (locCo M.co v (z * Cᵀ)) = ρ₀ * diagW (psiAt ψ v) μ Φ (locCo M.co v
        (((((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₂₁) * z) * Cᵀ)) := by
  first | exact @GlobalTheory.InertLagChar.diagW_omd_point | exact GlobalTheory.InertLagChar.diagW_omd_point | (intros; apply GlobalTheory.InertLagChar.diagW_omd_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullbackStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K) {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, IsTangent (ub σ k)) ∧ (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ ub σ k) ∧ ∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w := by
  first | exact @GlobalTheory.KSExist.exists_frame_of_isGrpPullback | exact GlobalTheory.KSExist.exists_frame_of_isGrpPullback | (intros; apply GlobalTheory.KSExist.exists_frame_of_isGrpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective : GlobalTheory.Published.IsolatedNonKltDivisor → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → 1 ≤ D → letI := algebraΓOfHom q; ∀ (N₀ : LB X) (r : ℕ) (x : X), 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → IsClosed ({x} : Set X) → (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → (((D + 1).choose 2 : ℕ) : ℝ) ^ e < (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e) → ∃ (m' : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m' ∧ D₀.Eff ∧ (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = interNumRed ℂ C ![N₀] / r) ∧ x ∈ U ∧ (∀ y ∈ U, y ≠ x → KltAt q D (qWeil D₀ m') y) ∧ ¬ KltAt q D (qWeil D₀ m') x := by
  first | exact @GlobalTheory.KollarApp.isolatedNonKlt_smooth | exact GlobalTheory.KollarApp.isolatedNonKlt_smooth | (intros; apply GlobalTheory.KollarApp.isolatedNonKlt_smooth <;> assumption)
end

