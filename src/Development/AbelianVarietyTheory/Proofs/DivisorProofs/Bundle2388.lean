module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNotMemMaximalIdealPowSucc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ReducedFibre

theorem pow_notMem_maximalIdeal_pow_succ {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) (hreg : π ∈ nonZeroDivisors R) (k : ℕ) :
    π ^ k ∉ maximalIdeal R ^ (k + 1) := by
  intro h
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h1 : π ^ k * (1 - π * c) = 0 := by
    linear_combination hc
  have h2 : 1 - π * c = 0 := (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hreg k)).mp h1
  have hmem : π ∈ maximalIdeal R := by rw [hπ]; exact Ideal.mem_span_singleton_self π
  exact (mem_maximalIdeal π).mp hmem (isUnit_iff_exists_inv.mpr ⟨c, by linear_combination -h2⟩)

theorem adicCompletion_dvr {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) (hreg : π ∈ nonZeroDivisors R)
    (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    ∃ _ : IsDomain (AdicCompletion (maximalIdeal R) R),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal R) R) ∧
      Irreducible (algebraMap R (AdicCompletion (maximalIdeal R) R) π) := by
  haveI := AdicCompletion.isLocalRing_of_fg fg
  haveI := AdicCompletion.isAdicComplete_of_fg fg
  refine GlobalTheory.isDiscreteValuationRing_of_maximalIdeal_eq_span ?_ ?_
  · rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg, hπ, Ideal.map_span, Set.image_singleton]
  · rintro ⟨k, hk⟩
    rw [← map_pow] at hk
    have h := congrArg (AdicCompletion.eval (maximalIdeal R) R (k + 1)) hk
    rw [show algebraMap R (AdicCompletion (maximalIdeal R) R) (π ^ k) =
      AdicCompletion.of (maximalIdeal R) R (π ^ k) from rfl, AdicCompletion.eval_of, map_zero,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top] at h
    exact pow_notMem_maximalIdeal_pow_succ hπ hreg k h

end GlobalTheory.ReducedFibre

namespace GlobalTheory.ReducedFibre

theorem exists_notMem_mul_eq_zero {A : Type*} [CommRing A] [IsReduced A]
    {Q : Ideal A} (hQ : Q ∈ minimalPrimes A) {x : A} (hx : x ∈ Q) :
    ∃ s : A, s ∉ Q ∧ s * x = 0 := by
  haveI : Q.IsPrime := hQ.1.1
  have hsub := IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes Q hQ
    (Localization.AtPrime Q)
  have hmem : algebraMap A (Localization.AtPrime Q) x ∈ maximalIdeal _ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hx
  have hnil : IsNilpotent (algebraMap A (Localization.AtPrime Q) x) := by
    rw [nilpotent_iff_mem_prime]
    intro Q' hQ'
    have h1 : (⟨Q', hQ'⟩ : PrimeSpectrum (Localization.AtPrime Q)) =
        ⟨maximalIdeal _, inferInstance⟩ := Subsingleton.elim _ _
    rw [show Q' = maximalIdeal _ from congrArg PrimeSpectrum.asIdeal h1]
    exact hmem
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ x).mp hnil.eq_zero
  exact ⟨s, s.2, hs⟩

theorem exists_cdvr_of_flat_of_isReduced :
    ∀ (V C : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing C] [Algebra V C]
      [Module.Flat V C], Nontrivial (C ⧸ (maximalIdeal V).map (algebraMap V C)) →
      IsReduced (C ⧸ (maximalIdeal V).map (algebraMap V C)) →
      ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
        (h : C →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
        ∀ ϖ : V, Irreducible ϖ → Irreducible (h (algebraMap V C ϖ)) := by
  intro V C _ _ _ _ _ _ hnt hred
  set J : Ideal C := (maximalIdeal V).map (algebraMap V C) with hJ
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (C ⧸ J)
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (C ⧸ J)) ≤ M)
  haveI : Q.IsPrime := hQ.1.1
  set P : Ideal C := Q.comap (Ideal.Quotient.mk J) with hP
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  let R := Localization.AtPrime P
  have hJP : J ≤ P := fun x hx => by
    rw [hP, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Q.zero_mem
  have hmax : maximalIdeal R = (maximalIdeal V).map (algebraMap V R) := by
    rw [IsScalarTower.algebraMap_eq V C R, ← Ideal.map_map, ← hJ,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    refine le_antisymm ?_ (Ideal.map_mono hJP)
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨s', hs', hs'a⟩ := exists_notMem_mul_eq_zero hQ (show Ideal.Quotient.mk J a ∈ Q from ha)
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
    have hsP : s ∈ P.primeCompl := hs'
    have hsa : s * a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_mul]; exact hs'a)
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap C R s) := IsLocalization.map_units R (⟨s, hsP⟩ : P.primeCompl)
    have := Ideal.mem_map_of_mem (algebraMap C R) hsa
    rw [map_mul] at this
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp this
  have hspan : ∀ ϖ : V, Irreducible ϖ → maximalIdeal R = Ideal.span {algebraMap V R ϖ} := by
    intro ϖ hϖ
    rw [hmax, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hreg : ∀ v : V, v ≠ 0 → algebraMap V R v ∈ nonZeroDivisors R := by
    intro v hv
    haveI : Module.Flat V R := Module.Flat.trans V C R
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero hv)
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => h ?_, fun x hx => h ?_⟩
    · show v • x = v • (0 : R)
      rw [smul_zero, Algebra.smul_def, hx]
    · show v • x = v • (0 : R)
      rw [smul_zero, Algebra.smul_def, mul_comm, hx]
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible V
  have fg : (maximalIdeal R).FG := ⟨{algebraMap V R ϖ₀}, by rw [hspan ϖ₀ hϖ₀]; simp⟩
  haveI := AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hd, hdvr, -⟩ := adicCompletion_dvr (hspan ϖ₀ hϖ₀) (hreg ϖ₀ hϖ₀.ne_zero) fg
  refine ⟨AdicCompletion (maximalIdeal R) R, inferInstance, hd, hdvr,
    (algebraMap R (AdicCompletion (maximalIdeal R) R)).comp (algebraMap C R),
    AdicCompletion.isAdicComplete_of_fg fg, fun ϖ hϖ => ?_⟩
  obtain ⟨-, -, hirr⟩ := adicCompletion_dvr (hspan ϖ hϖ) (hreg ϖ hϖ.ne_zero) fg
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact hirr

end GlobalTheory.ReducedFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOfGroupSchemeIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolOfIso

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem relAmple_pull_of_affine (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w)
    (hf : ∀ U' : S'.Opens, IsAffineOpen U' → ∃ U : S.Opens, IsAffineOpen U ∧ U' ≤ f ⁻¹ᵁ U) (hA : RelAmple A L) :
    RelAmple A' L' := by
  intro U' hU'
  obtain ⟨U, hU, le⟩ := hf U' hU'
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA U hU
  have le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy => (congrArg (fun q => q y ∈ U) h.w).mpr (le hy)
  let ψ := φ.resLE (A.hom ⁻¹ᵁ U) (A'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (A'.hom ∣_ U') (A.hom ∣_ U) (f.resLE U U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict A.hom U).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict A'.hom U').flip.paste_horiz h
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc,
        Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine U := hU
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have hP' := linComb_isLB L' hL' (K := Fin N) (fun _ => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A' L' U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L U N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A' L' U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((f.resLE U U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

theorem sym_pull_of_iso [GrpObj A] [GrpObj A'] (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w) (hs : Sym A L) : Sym A' L' := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hs (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le' : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy =>
    (congrArg (fun q => q y ∈ U) h.1.w).mpr hy
  have hψ : φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  obtain ⟨t', ht'⟩ := gen_chartPull (chartPullSame L
    (fun k => ![(A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ (GrpObj.inv : A' ⟶ A').left, (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι] k ≫ φ) _ _
    (φ.resLE _ _ le') fun k => by
      fin_cases k
      · show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _
        rw [Category.assoc, PolBaseChange.inv_comm h, ← Category.assoc, ← hψ, Category.assoc]
      · exact hψ.symm) t ht
  exact exists_down hw hL hL' t' ht'

end GlobalTheory.PolOfIso

namespace GlobalTheory

theorem polarisation_of_iso :
    ∀ (S : Scheme.{0}) (P : PolAV S) (B : Over S) [GrpObj B] (e : B ≅ P.A), IsMonHom e.hom → ∀ L : LB B.left, L.IsLB → LBIso L (P.L.pull e.hom.left) → IsProper B.hom ∧ SmoothOfRelativeDimension P.g B.hom ∧ Sym B L ∧ RelAmple B L ∧ KTriv B L := by
  intro S P B _ e he L hL ⟨w, hw⟩
  have h := isGrpPullback_of_iso e
  have hw' := (isGen_iff w).1 hw
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) h.1 P.isAb.proper,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim,
    PolOfIso.sym_pull_of_iso h P.isLB hL hw' P.sym,
    PolOfIso.relAmple_pull_of_affine h.1 P.isLB hL hw' (fun U hU => ⟨U, hU, fun _ hy => hy⟩) P.ample,
    kTriv_pull h P.isLB hL hw' P.ktriv⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalisationGenericSmoothCover
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped TensorProduct

namespace GlobalTheory.GenSmoothCover

theorem isPullback_rat (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] [IsFractionRing k K] :
    IsPullback (spMap (algebraMap k K)) (spMap (algebraMap ℚ K)) (spMap (Int.castRingHom k))
      (spMap (algebraMap ℤ ℚ)) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance
  have := Algebra.isPushout_of_isLocalization (nonZeroDivisors ℤ) ℚ k K
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout ℤ k ℚ K)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem genericFibre [IsIntegral X] (h : IsArithVar p D) {K : Type} [Field K] [Algebra k K]
    [IsFractionRing k K] {Y : Scheme.{0}} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap k K))) :
    ∃ _ : IsIntegral Y, topologicalKrullDim Y = D ∧ j (genericPoint Y) = genericPoint X := by
  have := h.isDomain
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨_, hd⟩ := RegGenSmooth.ringKrullDim_chart h H i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have hinj : Function.Injective (algebraMap A (K ⊗[k] A)) := IsLocalization.injective _ hle
  obtain ⟨i₀, _, H₀⟩ := exists_affine_chart_of_isPullback H i hi
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback H inferInstance
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
  have := flat_specMap_localization (nonZeroDivisors k) K
  have : Flat j := MorphismProperty.of_isPullback H.flip this
  let η : Spec (.of (K ⊗[k] A)) := (⟨⊥, inferInstance⟩ : PrimeSpectrum _)
  have e₁ : topologicalKrullDim (closure {i₀ η} : Set Y) = D :=
    (topologicalKrullDim_closure_eq_ringKrullDim_quotient q i₀ η).trans
      ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).trans hd)
  have e₂ : j (i₀ η) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, H₀.w, Scheme.Hom.comp_apply, ← genericPoint_eq_of_isOpenImmersion i]
    congr 1
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)
  have e₃ : closure {i₀ η} = Set.univ :=
    Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1
      (j.isEmbedding.isInducing.specializes_iff.1 (e₂ ▸ genericPoint_specializes _))
  have : IrreducibleSpace Y := (irreducibleSpace_def Y).2 (by
    rw [Set.top_eq_univ, ← e₃]; exact isIrreducible_singleton.closure)
  have hr (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    have := GenSpread.isIso_stalkMap_of_flat j y
    exact isReduced_of_injective (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.symm
      (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.symm.injective
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  rw [e₃, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq] at e₁
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced Y, e₁, ?_⟩
  rw [← e₂, (genericPoint_spec Y).eq (show IsGenericPoint (i₀ η) Set.univ from e₃)]

theorem exists_closure (hp : IsProjOver p) {K : Type} [Field K] [Algebra k K] [IsFractionRing k K] {W : Scheme.{0}}
    [IsIntegral W] (w : W ⟶ X) (q : W ⟶ Sp K) (hw : w ≫ p = q ≫ spMap (algebraMap k K)) (hq : IsProjOver q) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y) (j : W ⟶ Y), j ≫ ρ = w ∧ IsProjOver (ρ ≫ p) ∧
      IsPullback j q (ρ ≫ p) (spMap (algebraMap k K)) ∧ IsSchemeTheoreticallyDominant j ∧ QuasiCompact j := by
  obtain ⟨M, i, _, rfl⟩ := hq
  have B := ProjSpace.isPullback_baseChange M (algebraMap k K)
  have hP := ProjSpace.isProjOver_pullback hp (ProjSpace.isProjOver_pspace_str k M)
  let π := pullback.fst p (PSpace.str k M) ≫ p
  have : IsProper π := CommonModel.isProper_of_isProjOver hP
  let j : W ⟶ pullback p (PSpace.str k M) :=
    pullback.lift w (i ≫ ProjSpace.baseChange M (algebraMap k K)) (by rw [hw, Category.assoc, Category.assoc, B.w])
  have hj₁ : j ≫ pullback.fst _ _ = w := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = i ≫ ProjSpace.baseChange M (algebraMap k K) := pullback.lift_snd _ _ _
  have G := IsPullback.of_hasPullback π (spMap (algebraMap k K))
  let c := G.lift j (i ≫ PSpace.str K M) (by rw [reassoc_of% hj₁, hw])
  have hc₁ : c ≫ pullback.fst _ _ = j := G.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = i ≫ PSpace.str K M := G.lift_snd _ _ _
  let t := B.lift (pullback.fst π (spMap (algebraMap k K)) ≫ pullback.snd _ _) (pullback.snd _ _)
    (by rw [Category.assoc, ← pullback.condition, G.w])
  have ht₁ : t ≫ _ = _ := B.lift_fst _ _ _
  have ht₂ : t ≫ _ = _ := B.lift_snd _ _ _
  have : IsSeparated (t ≫ PSpace.str K M) := by rw [ht₂]; infer_instance
  have : IsSeparated t := IsSeparated.of_comp t (PSpace.str K M)
  have hct : c ≫ t = i := B.hom_ext (by rw [Category.assoc, ht₁, reassoc_of% hc₁, hj₂])
    (by rw [Category.assoc, ht₂, hc₂])
  have : IsClosedImmersion (c ≫ t) := by rwa [hct]
  have : IsClosedImmersion c := .of_comp c t
  have := flat_specMap_localization (nonZeroDivisors k) K
  have := mono_specMap_localization (nonZeroDivisors k) K
  have : QuasiCompact j := by rw [← hc₁]; infer_instance
  have H := (isPullback_toImage_of_isClosedImmersion j c _ hc₁).flip.paste_vert G
  rw [hc₂] at H
  refine ⟨j.image, j.imageι ≫ pullback.fst _ _, inferInstance, j.toImage, by simp [hj₁], ?_, ?_, inferInstance,
    inferInstance⟩
  · rw [Category.assoc]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hP
  · rw [Category.assoc]
    exact H

theorem exists_isCov_genSmooth : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ), IsArithVar p D → ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y),
      FlagChain.IsCov p D ρ ∧ GenSmooth (ρ ≫ p) D := by
  intro hP k _ X p _ D h
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isNoetherianRing
  let K := FractionRing k
  have G := IsPullback.of_hasPullback p (spMap (algebraMap k K))
  set f := pullback.fst p (spMap (algebraMap k K))
  set q := pullback.snd p (spMap (algebraMap k K))
  obtain ⟨_, hd, hf⟩ := genericFibre h G
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ G h.isProjOver
  obtain ⟨W, s, U, _, hsm, hW, hU, hiso⟩ := WeakRes.weak_resolution hP K _ q D hq hd
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have : IsProper (s ≫ q) := CommonModel.isProper_of_isProjOver hW
  have hdW : topologicalKrullDim W = D :=
    (OpenDim.topologicalKrullDim_eq_of_isIso_restrict K _ W q (s ≫ q) s inferInstance inferInstance rfl U hU hiso).trans hd
  obtain ⟨Y, ρ, _, j, hj, hY, H, _, _⟩ := exists_closure h.isProjOver (s ≫ f) (s ≫ q)
    (by rw [Category.assoc, Category.assoc, G.w]) hW
  have : IsProper (ρ ≫ p) := CommonModel.isProper_of_isProjOver hY
  have : IsFinite (spMap (Int.castRingHom k)) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h.finite)
  have H' := H.paste_vert (isPullback_rat k K)
  have : Flat (j ≫ (ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_over_fractionField (K := ℚ) _ _ H'.w.symm
  have hfl : Flat ((ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_schemeDominant_of_isDedekindDomain j _
  have hA : IsArithVar (ρ ≫ p) D :=
    ⟨h.isDomain, h.finite, ‹_›, hY, hfl, IntModel.topologicalKrullDim_eq_succ Int.not_isField H' hdW⟩
  obtain ⟨_, -, hjη⟩ := genericFibre hA H
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (s ⁻¹ᵁ U : W.Opens).toScheme := ⟨inv (s ∣_ U) ⟨x, hx⟩⟩
  have : IsIntegral (s ⁻¹ᵁ U : W.Opens).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have e : ((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ = (s ∣_ U ≫ U.ι) ≫ f := by
    rw [Category.assoc, hj, morphismRestrict_ι, Category.assoc]
  have eη : ((s ⁻¹ᵁ U).ι ≫ j) (genericPoint _) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hjη]
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion f := MorphismProperty.of_isPullback G.flip this
  refine ⟨Y, ρ, ‹_›, ⟨hA, ?_, ?_⟩, fun σ => ?_⟩
  · rw [← eη, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hf]
  · have h₁ := PullbackFinitePoint.residueDegree_ne_zero_of_surjectiveOnStalks ((s ∣_ U ≫ U.ι) ≫ f) (genericPoint _)
    rw [← e, CurveDegreesCompare.residueDegree_comp, eη] at h₁
    exact left_ne_zero_of_mul h₁
  · have : LocallyOfFinitePresentation (ρ ≫ p) := inferInstance
    exact ⟨⟨AlgChart (ρ ≫ p) σ D, id, ModelCharts.exists_chart H (RegGenSmooth.injective_of_charZero σ)⟩⟩

end GlobalTheory.GenSmoothCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtR
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev ptR (χ : D.X) : Spec (CommRingCat.of R) ⟶ D.P.A.left :=
  (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ D.c χ).left

def unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) :
    (FractionRing R)ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
    (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).toMonoidHom

def Reads (κ : D.X → (FractionRing R)ˣ) : Prop :=
  ∃ g : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptR D χ) (fun _ => -1)),
    (∀ χ, (g χ).IsGen) ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi χ) r z J = unitAt r z (κ χ) * val (g χ) (r ≫ jK R) z J

def lead {X : Type} [AddCommGroup X] (κ : X → (FractionRing R)ˣ) (k : ℕ) (α mu : X) : (FractionRing R)ˣ :=
  κ mu ^ k * (κ (mu + α) * (κ mu)⁻¹ * (κ α)⁻¹)

end GlobalTheory.ThFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefAtPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam


open GlobalTheory.HalfBC in
theorem refAt_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (I : Ideal R) (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg ρ D.toPre D'), RefAt (pol D) ρ D' hD.xe (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf ρ)) := by
  intro R R' _ _ _ _ ρ hρ I D D' hD
  letI := D'.P.isAb.comm
  have gp := pull_grp hD
  refine ⟨sqOf gp, lamIso gp hD.w, gp, isSquare_sqOf gp, isGen_lamIso gp hD.w hD.w_gen, fun a => hD.c_pr a,
    fun κ hκ a b z J J' hJ hJ' => ?_⟩
  obtain rfl : κ = GlobalTheory.ArcPull.genMap hρ := by
    have : Mono (jK R) := Wit.mono_jK
    refine (cancel_mono (jK R)).1 (hκ.trans ?_)
    rw [← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]
  rw [← GlobalTheory.FactorPull.tau_lam hD hρ a b hJ hJ']
  refine congrArg₂ (· * ·) ?_ ((Wit.exists_tau D.toPre (hD.xe a) (hD.xe b)).choose_spec.2 _ _ z J hJ).symm
  symm
  show gw (lamIso gp hD.w) _ z (fun I => J (_ ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I))
    (fun I => J' (_ ≫ GlobalTheory.PrimCocycle.lamφ D'.P.A I)) = _
  refine (gw_lamIso gp hD.w _ z _ _ (fun I => by
      have := hJ ((lift (toUnit (TK R') ≫ D'.c a) (toUnit (TK R') ≫ D'.c b)).left ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I)
      erw [← pt_sqOf gp I]
      exact this) (fun I => hJ' _)).trans ?_
  refine Finset.prod_congr rfl fun I _ => ?_
  show _ = gw hD.w _ z _ _ ^ _
  erw [Category.assoc, ← sqOf_lamφ gp I]
  rfl

end GlobalTheory.MumFam
end
end

