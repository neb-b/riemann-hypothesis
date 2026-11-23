module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCompletionResidueEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EtaleCompletionResidue

open Polynomial

theorem exists_finite_free_local_residue_equiv (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (M : Type)
    [Field M] (m : ResidueField B →+* M) (hmf : m.Finite) (hmu : m.FormallyUnramified) :
    ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (ψ₀ : B →+* C) (_ : IsLocalHom ψ₀) (E : M ≃+* ResidueField C),
      IsNoetherianRing C ∧ Function.Injective ψ₀ ∧ ψ₀.Flat ∧ (maximalIdeal B).map ψ₀ = maximalIdeal C ∧
      ((residue C).comp ψ₀).Finite ∧ ((residue C).comp ψ₀).FormallyUnramified ∧ (E : M →+* ResidueField C).comp m = ResidueField.map ψ₀ := by
  letI : Algebra (ResidueField B) M := m.toAlgebra
  haveI : FiniteDimensional (ResidueField B) M := hmf
  haveI : Algebra.FormallyUnramified (ResidueField B) M := hmu
  haveI : Algebra.IsSeparable (ResidueField B) M := (Algebra.FormallyUnramified.iff_isSeparable _ _).1 inferInstance
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField B) M
  have hm := minpoly.monic pb.isIntegral_gen
  have hirr := minpoly.irreducible pb.isIntegral_gen
  obtain ⟨F, hF, hdeg, hFm⟩ := Polynomial.lifts_and_degree_eq_and_monic (f := residue B)
    (Polynomial.mem_lifts_of_surjective residue_surjective _) hm
  have hg : Irreducible (F.map (residue B)) := hF ▸ hirr
  haveI : Fact (Irreducible (F.map (residue B))) := ⟨hg⟩
  haveI hfin : Module.Finite B (AdjoinRoot F) := .of_basis (AdjoinRoot.powerBasis' hFm).basis
  haveI : Module.Free B (AdjoinRoot F) := .of_basis (AdjoinRoot.powerBasis' hFm).basis
  have hqf : IsField (AdjoinRoot F ⧸ (maximalIdeal B).map (AdjoinRoot.of F)) := by
    have hR : IsField (AdjoinRoot (F.map (residue B))) := Field.toIsField _
    exact MulEquiv.isField hR (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).toRingEquiv.toMulEquiv
  have hJ : ((maximalIdeal B).map (algebraMap B (AdjoinRoot F))).IsMaximal := by
    rw [AdjoinRoot.algebraMap_eq]
    exact Ideal.Quotient.maximal_of_isField _ hqf
  haveI : IsLocalRing (AdjoinRoot F) := by
    haveI : Algebra.IsIntegral B (AdjoinRoot F) := inferInstance
    refine IsLocalRing.of_unique_max_ideal ⟨_, hJ, fun P hP => ?_⟩
    have hc : (P.comap (algebraMap B (AdjoinRoot F))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
    have h1 : P.comap (algebraMap B (AdjoinRoot F)) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hc
    have hle : (maximalIdeal B).map (algebraMap B (AdjoinRoot F)) ≤ P := Ideal.map_le_iff_le_comap.2 h1.ge
    exact (hJ.eq_of_le hP.ne_top hle).symm
  have hmax : maximalIdeal (AdjoinRoot F) = (maximalIdeal B).map (algebraMap B (AdjoinRoot F)) :=
    (IsLocalRing.eq_maximalIdeal hJ).symm
  haveI hloc : IsLocalHom (algebraMap B (AdjoinRoot F)) := by
    constructor
    intro x hx
    by_contra h
    have h2 : algebraMap B (AdjoinRoot F) x ∈ maximalIdeal (AdjoinRoot F) := by
      rw [hmax]; exact Ideal.mem_map_of_mem _ h
    exact h2 hx
  have hinj : Function.Injective (algebraMap B (AdjoinRoot F)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    change AdjoinRoot.mk F (C x) = 0 at hx
    rw [AdjoinRoot.mk_eq_zero] at hx
    refine hFm.not_dvd_of_natDegree_lt (Polynomial.C_ne_zero.2 h0) ?_ hx
    rw [natDegree_C, natDegree_eq_of_degree_eq hdeg]
    exact minpoly.natDegree_pos pb.isIntegral_gen
  haveI : IsNoetherianRing (AdjoinRoot F) := isNoetherian_of_tower B inferInstance
  let e₁ : ResidueField (AdjoinRoot F) ≃+* AdjoinRoot (F.map (residue B)) :=
    (Ideal.quotEquivOfEq hmax).trans (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).toRingEquiv
  have he₁ : e₁.toRingHom.comp (ResidueField.map (algebraMap B (AdjoinRoot F))) = AdjoinRoot.of (F.map (residue B)) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    show e₁ (ResidueField.map _ (residue B x)) = _
    rw [ResidueField.map_residue]
    exact (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).commutes x
  let pb' := AdjoinRoot.powerBasis (hFm.map (residue B)).ne_zero
  have hmin : minpoly (ResidueField B) pb.gen = minpoly (ResidueField B) pb'.gen := by
    rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic (hFm.map (residue B)), hF]
  let e₂ : M ≃ₐ[ResidueField B] AdjoinRoot (F.map (residue B)) := pb.equivOfMinpoly pb' hmin
  let Eq' : M ≃+* ResidueField (AdjoinRoot F) := e₂.toRingEquiv.trans e₁.symm
  have hE : Eq'.toRingHom.comp m = ResidueField.map (algebraMap B (AdjoinRoot F)) := by
    ext x
    have h1 : e₁ (ResidueField.map (algebraMap B (AdjoinRoot F)) x) = AdjoinRoot.of (F.map (residue B)) x :=
      congrArg (fun q => q x) he₁
    have h2 : e₂ (m x) = AdjoinRoot.of (F.map (residue B)) x := by
      rw [← AdjoinRoot.algebraMap_eq]
      exact e₂.commutes x
    show e₁.symm (e₂ (m x)) = _
    rw [h2, ← h1, RingEquiv.symm_apply_apply]
  have hψfin : (algebraMap B (AdjoinRoot F)).Finite := RingHom.finite_algebraMap.mpr hfin
  refine ⟨AdjoinRoot F, inferInstance, inferInstance, algebraMap B (AdjoinRoot F), hloc, Eq', inferInstance,
    hinj, RingHom.flat_algebraMap_iff.mpr inferInstance, hmax.symm,
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ residue_surjective) hψfin, ?_, hE⟩
  rw [← ResidueField.map_comp_residue, ← hE]
  exact RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective)
    (RingHom.FormallyUnramified.comp hmu (RingHom.FormallyUnramified.of_surjective Eq'.surjective))

theorem exists_etaleCompletion_residue_equiv : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (M : Type) [Field M] (m : ResidueField O →+* M), m.Finite → m.FormallyUnramified → ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ψ : O →+* A) (_ : IsLocalHom ψ) (E : M ≃+* ResidueField A), IsCN A ∧ IsEtaleCompletion ψ ∧ ((residue A).comp ψ).FormallyUnramified ∧ (E : M →+* ResidueField A).comp m = ResidueField.map ψ := by
  intro O _ _ _ _ _ _ M _ m hmf hmu
  have hOn : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  obtain ⟨C, _, _, ψ₀, hψl, E₀, hCn, hψi, hψf, hψm, hψfin, hψfu, hE⟩ :=
    exists_finite_free_local_residue_equiv O M m hmf hmu
  haveI := hCn
  haveI := hψl
  let A := AdicCompletion (maximalIdeal C) C
  let j : C →+* A := algebraMap C A
  haveI : Module.Flat C A := AdicCompletion.flat_of_isNoetherian _
  have hbij : Function.Bijective (ResidueField.map j) := AdicCompletion.residueField_map_bijective C
  have hcomp : (residue A).comp (j.comp ψ₀) = (ResidueField.map j).comp ((residue C).comp ψ₀) := by
    ext b
    simp [ResidueField.map_residue]
  have hAn : IsNoetherianRing A := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _
  have hAc : IsAdicComplete (maximalIdeal A) A := inferInstance
  have hjl : IsLocalHom j := inferInstance
  have hji : Function.Injective j := AdicCompletion.of_injective (maximalIdeal C) C
  let ψ : O →+* A := j.comp ψ₀
  have hloc : IsLocalHom ψ := inferInstance
  have het : IsEtaleCompletion ψ := by
    refine ⟨?_, ?_, ?_⟩
    · exact RingHom.Flat.comp hψf (RingHom.flat_algebraMap_iff.2 inferInstance)
    · show (maximalIdeal O).map (j.comp ψ₀) = _
      rw [← Ideal.map_map, hψm, AdicCompletion.maximalIdeal_eq_map]
    · show ((residue A).comp (j.comp ψ₀)).Finite
      rw [hcomp]
      exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ hbij.2) hψfin
  have hur : ((residue A).comp ψ).FormallyUnramified := by
    show ((residue A).comp (j.comp ψ₀)).FormallyUnramified
    rw [hcomp]
    exact RingHom.FormallyUnramified.comp hψfu (RingHom.FormallyUnramified.of_surjective hbij.2)
  obtain ⟨hd, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed O
  obtain ⟨hAd, hAi⟩ := GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed O A ψ hOn hd hic hAn hAc hloc het hur
  haveI := hAd
  have hψinj : Function.Injective ψ := hji.comp hψi
  haveI : CharZero A := charZero_of_injective_ringHom hψinj
  let E : M ≃+* ResidueField A := E₀.trans (RingEquiv.ofBijective _ hbij)
  refine ⟨A, inferInstance, hAd, inferInstance, ψ, hloc, E, ⟨hAn, hAi, hAc, inferInstance⟩, het, hur, ?_⟩
  ext x
  obtain ⟨b, rfl⟩ := residue_surjective x
  have h2 := congrArg (fun t => t (residue O b)) hE
  simp only [RingHom.comp_apply, ResidueField.map_residue] at h2
  show ResidueField.map j (E₀ (m (residue O b))) = _
  have h3 : E₀ (m (residue O b)) = residue C (ψ₀ b) := h2
  rw [h3]
  simp only [ψ, ResidueField.map_residue, RingHom.comp_apply]

end GlobalTheory.EtaleCompletionResidue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLiftImmersion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtLift

theorem exists_etale_to_affineSpace {k : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec k) [Smooth f]
    (x : X) : ∃ (V : X.Opens) (n : ℕ) (u : V.toScheme ⟶ 𝔸(Fin n; Spec k)), x ∈ V ∧ Etale u ∧
      u ≫ (𝔸(Fin n; Spec k) ↘ Spec k) = V.ι ≫ f := by
  obtain ⟨U, hU, V, hV, hxV, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hs
  have hmap : Etale (AffineSpace.map (Fin n) hU.fromSpec) :=
    MorphismProperty.of_isPullback (P := @Etale) (AffineSpace.isPullback_map (n := Fin n) hU.fromSpec).flip inferInstance
  have hSg : Etale (Spec.map (CommRingCat.ofHom g)) := HasRingHomProperty.Spec_iff.mpr hg
  refine ⟨V, n, hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫ (AffineSpace.SpecIso (Fin n) _).inv ≫
    AffineSpace.map (Fin n) hU.fromSpec, hxV, inferInstance, ?_⟩
  simp only [Category.assoc, AffineSpace.map_over, AffineSpace.SpecIso_inv_over_assoc, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, hgC]
  rw [CommRingCat.ofHom_hom, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, hV.isoSpec_hom_fromSpec_assoc]

theorem exists_surjective_appTop {Y P : Scheme.{0}} (j : Y ⟶ P) [IsImmersion j] (y : Y) (U : Y.Opens)
    (hy : y ∈ U) : ∃ W : P.Opens, j y ∈ W ∧ j ⁻¹ᵁ W ≤ U ∧ Function.Surjective (j ∣_ W).appTop := by
  obtain ⟨O, hO, hOU⟩ := j.isEmbedding.isInducing.isOpen_iff.mp U.isOpen
  have hyC : j y ∈ (j.coborderRange : Set P) := subset_coborder ⟨y, rfl⟩
  have hyO : j y ∈ O := by
    rw [← Set.mem_preimage, hOU]; exact hy
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWs⟩ := P.isBasis_affineOpens.exists_subset_of_mem_open
    (show j y ∈ O ∩ (j.coborderRange : Set P) from ⟨hyO, hyC⟩) (hO.inter j.coborderRange.isOpen)
  refine ⟨W, hxW, ?_, ?_⟩
  · intro z hz
    show z ∈ (U : Set Y)
    rw [← hOU]
    exact (hWs hz).1
  · have : IsAffine W := hW
    have key : Set.range (j ∣_ W) = (Scheme.Opens.ι W) ⁻¹' closure (Set.range j) := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        apply subset_closure
        refine ⟨(j ⁻¹ᵁ W).ι z, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
      · intro hx
        have hxW' : (Scheme.Opens.ι W) x ∈ (W : Set P) := by
          rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
        have hxC : (Scheme.Opens.ι W) x ∈ (j.coborderRange : Set P) := (hWs hxW').2
        have h3 : (Scheme.Opens.ι W) x ∈ closure (Set.range j) ∩ coborder (Set.range j) := ⟨hx, hxC⟩
        rw [closure_inter_coborder] at h3
        obtain ⟨z, hz⟩ := h3
        have hzW : z ∈ j ⁻¹ᵁ W := by
          show j z ∈ W; rw [hz]; exact hxW'
        obtain ⟨z', hz'⟩ : z ∈ Set.range (j ⁻¹ᵁ W).ι := by
          rw [Scheme.Opens.range_ι]; exact hzW
        refine ⟨z', (Scheme.Opens.ι W).isOpenEmbedding.injective ?_⟩
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hz', hz]
    have : IsClosedImmersion (j ∣_ W) := by
      refine .of_isPreimmersion _ ?_
      rw [key]
      exact isClosed_closure.preimage (Scheme.Opens.ι W).continuous
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (j ∣_ W)).2

end GlobalTheory.Mum.EtLift


open GlobalTheory.Mum.EtLift in
theorem GlobalTheory.Mum.exists_etale_coords_lift_immersion : ∀ (R : Type) [CommRing R] [IsLocalRing R] (N : ℕ) (Y : Over (Sp (ResidueField R))), Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N), IsImmersion j → j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → ∀ y : Y.left, ∃ (W0 : (PSpace R N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O ∧ (O : Set Y.left) ⊆ j ⁻¹' W0 ∧ τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R N ∧ Etale e ∧ e ≫ pullback.snd _ _ = O.ι ≫ Y.hom ∧ ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0 := by
  intro R _ _ N Y hsm j hj hjs y
  have : Smooth Y.hom := hsm
  obtain ⟨V, g, u, hyV, hu, huo⟩ := exists_etale_to_affineSpace (k := CommRingCat.of (ResidueField R)) Y.hom y
  have huo' : u ≫ (𝔸(Fin g; Sp (ResidueField R)) ↘ Sp (ResidueField R)) = V.ι ≫ Y.hom := huo
  obtain ⟨W, hyW, hWV, hsurj⟩ := exists_surjective_appTop j y V hyV
  let u' : (j ⁻¹ᵁ W).toScheme ⟶ 𝔸(Fin g; Sp (ResidueField R)) := Y.left.homOfLE hWV ≫ u
  have hu' : Etale u' := by
    have : Etale (Y.left.homOfLE hWV) := inferInstance
    exact inferInstanceAs (Etale (Y.left.homOfLE hWV ≫ u))
  choose s hs using fun i : Fin g => hsurj (u'.appTop (AffineSpace.coord (Sp (ResidueField R)) i))
  let τ0 : W.toScheme ⟶ 𝔸(Fin g; Sp R) := AffineSpace.homOfVector (W.ι ≫ PSpace.str R N) s
  have hP := AffineSpace.isPullback_map (n := Fin g) (spMap (residue R))
  have hfst : u' ≫ AffineSpace.map (Fin g) (spMap (residue R)) = (j ∣_ W) ≫ τ0 := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, AffineSpace.map_over, τ0, AffineSpace.homOfVector_over, u']
      rw [reassoc_of% huo', Scheme.homOfLE_ι_assoc, ← Category.assoc (j ∣_ W), morphismRestrict_ι,
        Category.assoc, hjs]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord, τ0,
        AffineSpace.homOfVector_appTop_coord]
      exact (hs i).symm
  refine ⟨W, g, τ0, j ⁻¹ᵁ W, u' ≫ hP.isoPullback.hom, hyW, fun z hz => hz,
    AffineSpace.homOfVector_over _ _, inferInstance, ?_, ?_⟩
  · simp only [Category.assoc, IsPullback.isoPullback_hom_snd, u']
    rw [huo', Scheme.homOfLE_ι_assoc]
  · intro T t w hw
    have hfst' : Y.left.homOfLE hWV ≫ u ≫ AffineSpace.map (Fin g) (spMap (residue R)) = (j ∣_ W) ≫ τ0 := by
      rw [← Category.assoc]; exact hfst
    rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst]
    rw [hfst', ← Category.assoc]
    congr 1
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, hw]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenMultipleHermitianPositiveCombination
section
open Matrix

namespace GlobalTheory.Desc.HermComb

theorem lat_basis (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ)
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
      ∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let b := Module.finBasis ℤ Λ
  refine ⟨_, b.ofZLatticeBasis ℝ Λ, fun x => ⟨fun hx k => ⟨b.repr ⟨x, hx⟩ k, ?_⟩, fun h => ?_⟩⟩
  · exact b.ofZLatticeBasis_repr_apply ℝ Λ ⟨x, hx⟩ k
  · choose m hm using h
    have hx : x = ∑ k, m k • (b k : Fin g → ℂ) := by
      conv_lhs => rw [← (b.ofZLatticeBasis ℝ Λ).sum_repr x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hm k, Module.Basis.ofZLatticeBasis_apply, Int.cast_smul_eq_zsmul]
    rw [hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2

theorem int_of_den_dvd (q : ℚ) (D : ℕ) (h : q.den ∣ D) : ∃ m : ℤ, (D : ℚ) * q = m := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * q.num, ?_⟩
  push_cast
  rw [mul_comm (q.den : ℚ) k, mul_assoc, mul_comm (q.den : ℚ), Rat.mul_den_eq_num]

theorem common_den (n r : ℕ) (c₀ : ℚ) (c : Fin r → ℚ) (M : Fin r → Matrix (Fin n) (Fin n) ℚ) :
    ∃ D : ℕ, 1 ≤ D ∧ (∃ m : ℤ, (D : ℚ) * c₀ = m) ∧ (∀ i, ∃ m : ℤ, (D : ℚ) * c i = m) ∧
      ∀ i k l, ∃ m : ℤ, (D : ℚ) * M i k l = m := by
  classical
  let S : Finset ℚ := insert c₀ (Finset.univ.image c ∪
    Finset.univ.image (fun x : Fin r × Fin n × Fin n => M x.1 x.2.1 x.2.2))
  have hdv : ∀ q ∈ S, q.den ∣ ∏ q ∈ S, q.den := fun q hq => Finset.dvd_prod_of_mem _ hq
  refine ⟨∏ q ∈ S, q.den, Finset.prod_pos fun (q : ℚ) _ => q.den_pos, int_of_den_dvd _ _ (hdv _ ?_),
    fun i => int_of_den_dvd _ _ (hdv _ ?_), fun i k l => int_of_den_dvd _ _ (hdv _ ?_)⟩
  · simp [S]
  · simp [S]
  · simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨(i, k, l), rfl⟩)

end GlobalTheory.Desc.HermComb

namespace GlobalTheory.Desc.HermComb

theorem main : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∀ (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₁.mulVec (star m)).im) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₂.mulVec (star m)).im) →
    ∃ (N a₀ r : ℕ) (a : Fin r → ℕ) (F : Fin r → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), 1 ≤ N ∧ 1 ≤ a₀ ∧ Even N ∧ Even a₀ ∧
      (∀ i, Even (a i)) ∧ (∀ i, ∀ l ∈ Λ, F i l ∈ Λ) ∧
      ∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ H₁.mulVec (star w)) =
        (a₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) + ∑ i, (a i : ℂ) * (F i z ⬝ᵥ H₂.mulVec (star (F i w))) := by
  intro g Λ hd hs H₁ H₂ h₁ h₂ hp₁ hp₂ hi₁ hi₂
  obtain ⟨n, e, he⟩ := lat_basis g Λ hd hs
  have hek : ∀ k, e k ∈ Λ := fun k => (he _).2 fun j =>
    ⟨if k = j then 1 else 0, by rw [e.repr_self, Finsupp.single_apply]; split_ifs <;> simp⟩
  obtain ⟨γ, hγ, hsa⟩ := _root_.GlobalTheory.herm_gamma g H₁ H₂ h₁ h₂ hp₁
  obtain ⟨Tq, hT⟩ := _root_.GlobalTheory.herm_endo_matrix_rat g n e H₁ H₂ hp₁ (fun k l => hi₁ _ (hek k) _ (hek l))
    (fun k l => hi₂ _ (hek k) _ (hek l)) γ hγ
  obtain ⟨hB, hBT⟩ := GlobalTheory.T.posDef_real_gram_pair_hermitian_forms g n e H₁ H₂ h₁ h₂ hp₁ hp₂ γ hγ
  rw [← hT] at hBT
  obtain ⟨c₀, r, c, p, hc₀, hc, hid⟩ := GlobalTheory.T.exists_unit_eq_positive_squares_times_selfAdjoint n Tq _ hB hBT
  have hform := GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity g H₁ H₂ γ hγ hsa c₀ r c p (GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map g n e γ Tq hT c₀ r c p hid)
  obtain ⟨D, hD1, ⟨m₀, hm₀⟩, hci, hM⟩ := common_den n r c₀ c (fun i => Polynomial.aeval Tq (p i))
  choose m hm using hci
  have hm₀p : 0 < m₀ := by
    have : (0 : ℚ) < m₀ := by rw [← hm₀]; exact mul_pos (by exact_mod_cast hD1) hc₀
    exact_mod_cast this
  have hmp : ∀ i, 0 ≤ m i := fun i => by
    have : (0 : ℚ) ≤ m i := by rw [← hm i]; exact (mul_pos (by exact_mod_cast hD1) (hc i)).le
    exact_mod_cast this
  refine ⟨2 * D ^ 3, 2 * D ^ 2 * m₀.toNat, r, fun i => 2 * (m i).toNat,
    fun i => D • Polynomial.aeval γ (p i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 1 ≤ D ^ 3 := Nat.one_le_pow _ _ hD1; omega
  · have h1 : 1 ≤ D ^ 2 := Nat.one_le_pow _ _ hD1
    have h2 : 1 ≤ m₀.toNat := by omega
    nlinarith
  · exact even_two_mul _
  · rw [mul_assoc]; exact even_two_mul _
  · exact fun i => even_two_mul _
  · exact fun i => _root_.GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix g n Λ e he γ Tq hT (p i) D (hM i)
  · intro z w
    have hm₀' : ((m₀.toNat : ℕ) : ℂ) = (D : ℂ) * (c₀ : ℂ) := by
      have : ((m₀.toNat : ℤ) : ℚ) = (D : ℚ) * c₀ := by rw [Int.toNat_of_nonneg hm₀p.le, hm₀]
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    have hm' : ∀ i, (((m i).toNat : ℕ) : ℂ) = (D : ℂ) * (c i : ℂ) := fun i => by
      have : (((m i).toNat : ℤ) : ℚ) = (D : ℚ) * c i := by rw [Int.toNat_of_nonneg (hmp i), hm i]
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    have hsc : ∀ a b : Fin g → ℂ, (D • a) ⬝ᵥ H₂.mulVec (star (D • b)) = (D : ℂ) * D * (a ⬝ᵥ H₂.mulVec (star b)) := by
      intro a b
      rw [star_nsmul, mulVec_smul, dotProduct_smul, smul_dotProduct, nsmul_eq_mul, nsmul_eq_mul]; ring
    simp only [LinearMap.smul_apply, hsc]
    rw [hform z w]
    push_cast [hm₀', hm']
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring

end GlobalTheory.Desc.HermComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentsThetaSystemBigOddPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem bigSizes_of (g N r : ℕ) (hN : 1 + 2 * g * 2 ^ g < N)
    (hr : 6 * (N ^ g * g.factorial) + 2 * (N ^ g * g.factorial) * (g * 4 ^ g) < r) :
    1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N ∧
    2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) * N
      < (r * N : ℕ) ∧
    6 * (N ^ g * g.factorial) < r * N := by
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have e1 : (2 : ℝ) ^ ((g : ℝ) / 2) ≤ 2 ^ g := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e2 : (2 : ℝ) ^ ((g : ℝ) / 2 - 1) ≤ 2 ^ g := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e3 : (3 / 2 : ℝ) ^ g ≤ 2 ^ g := pow_le_pow_left₀ (by norm_num) (by norm_num) g
  have hNpos : 0 < N := by omega
  refine ⟨?_, ?_, ?_⟩
  · have hN' : ((1 + 2 * g * 2 ^ g : ℕ) : ℝ) < N := by exact_mod_cast hN
    push_cast at hN'
    have : 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) ≤ 2 * g * 2 ^ g := by gcongr
    linarith
  · set X : ℕ := N ^ g * g.factorial
    have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg _
    have hr' : ((6 * X + 2 * X * (g * 4 ^ g) : ℕ) : ℝ) < r := by exact_mod_cast hr
    push_cast at hr'
    have hC : (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) ≤ g * 4 ^ g := by
      have h4 : (4 : ℝ) ^ g = 2 ^ g * 2 ^ g := by rw [← mul_pow]; norm_num
      rw [h4, ← _root_.mul_assoc]
      have hp1 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ g := by positivity
      have hp2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by positivity
      gcongr
    have h1 : 2 * (X : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) < r := by
      have : 2 * (X : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1))
          ≤ 2 * X * (g * 4 ^ g) := by gcongr
      have h6 : (0 : ℝ) ≤ 6 * X := by positivity
      linarith
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    push_cast
    exact mul_lt_mul_of_pos_right h1 hNr
  · have h1 : 6 * (N ^ g * g.factorial) < r := by omega
    calc 6 * (N ^ g * g.factorial) < r := h1
      _ ≤ r * N := Nat.le_mul_of_pos_right r hNpos

theorem bigSizes : ∀ (g n : ℕ), n.Prime → Odd n → ∃ k j : ℕ, 2 ≤ k ∧ 1 ≤ j ∧ ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω), S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  intro g n hp _
  have hn : 1 < n := hp.one_lt
  set k := (1 + 2 * g * 2 ^ g) + 2 with hk
  set N₀ := (n ^ k) ^ 2 with hN₀
  set M := 6 * (N₀ ^ g * g.factorial) + 2 * (N₀ ^ g * g.factorial) * (g * 4 ^ g) with hM
  refine ⟨k, M + 1, by omega, by omega, ?_⟩
  intro o Ω _ _ _ S hg hN hr
  have hkN : 1 + 2 * g * 2 ^ g < N₀ := by
    have h1 : k < n ^ k := Nat.lt_pow_self hn
    have h2 : n ^ k ≤ (n ^ k) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hjr : M < n ^ (M + 1) := by
    have := Nat.lt_pow_self (n := M + 1) hn
    omega
  unfold GlobalTheory.ZH.ThetaSys.Big
  rw [hg, hN, hr]
  exact bigSizes_of g N₀ (n ^ (M + 1)) hkN hjr

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLineBundlePullbackSpecLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.LocalPullGen

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (L : LB X), L.IsLB →
    ∀ p : (𝟙_ (Over (Sp R))).left ⟶ X, ∃ ρ : LB.Gen (L.pull p), ρ.IsGen := by
  intro R _ _ X L hL p
  exact ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := R) L hL (K := PUnit) (fun _ => p) (fun _ => 1)

end GlobalTheory.LocalPullGen
end

