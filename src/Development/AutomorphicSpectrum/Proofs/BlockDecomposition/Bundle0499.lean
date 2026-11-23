module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478
public import GroundTheory.AutomorphicForms.AnisotropicUnitaryHeight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
public import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0486
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleBoundOfJointAnisotropic
section
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.FormHeight

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

section Forms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ}

theorem sigR_conj (R : Type) [CommRing R] [Algebra F R] :
    sigR R (conj F E).toAlgHom = conjBase F E R := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem hermValue_eq_hR (R : Type) [CommRing R] [Algebra F R] (H : Matrix (Fin n) (Fin n) E)
    (x : Fin n → R ⊗[F] E) : hermValue F H R x = hR R (conj F E).toAlgHom H x x := by
  rw [hR, sigR_conj]
  simp only [hermValue, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc]
  rfl

theorem coords_algebraMap_mul_inclR (s : AF F) (z : E) :
    coords (Module.finBasis F E) (AF F)
        (algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z) =
      s • Reduction.ratVec (fun k => (Module.finBasis F E).repr z k) := by
  have e : algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z = s • ((1 : AF F) ⊗ₜ[F] z) := by
    simp [inclR, Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
  rw [e, map_smul]
  congr 1
  funext k
  simp [coords, Reduction.ratVec, Algebra.TensorProduct.basis_repr_tmul]

theorem exists_adelicNorm_hermPoly_le (H : Matrix (Fin n) (Fin n) E) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2 :=
  exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos (hermPoly H (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)

theorem one_le_mul_hgt_sq (J H : Matrix (Fin n) (Fin n) E) {C : ℝ}
    (hCb : ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2)
    (g : GAd (conj F E).toAlgHom J) {ξ : Fin n → E} (hξ : ξ ≠ 0)
    (s : GroundTheory.Global.IdeleGroup F) (hs : 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ))
    {z : E} (hz : z ≠ 0)
    (he : hR (AF F) (conj F E).toAlgHom H
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ)
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ) =
      algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) z) :
    1 ≤ C * hgt (conj F E).toAlgHom J g ξ ^ 2 := by
  set b := Module.finBasis F E with hb
  set v := (matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ with hv
  set y : Fin (Bridge.dimN F E n) → AF F := resVec (ι := Fin n) b (AF F) v with hy
  have ey : Reduction.ratVec (Bridge.cvec F ξ) ᵥ*
      (Bridge.trG (conj F E).toAlgHom J g : Matrix _ _ (AF F)) = y := by
    rw [Bridge.ratVec_cvec, Bridge.trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hy, hv, map_inv]
  have hfy : Reduction.HasFiniteContent y := by
    rw [← ey]
    exact Reduction.hasFiniteContent_height _ (Bridge.cvec_ne_zero hξ)
  have hz' : (fun k => b.repr z k) ≠ 0 := by
    intro h0
    apply hz
    apply b.repr.injective
    ext k
    simpa using congrFun h0 k
  have e : (fun k => MvPolynomial.aeval y (hermPoly H b k)) =
      (s : AF F) • Reduction.ratVec (fun k => b.repr z k) := by
    funext k
    rw [aeval_hermPoly, hermCoords, hy, ofResVec_resVec, hermValue_eq_hR, he,
      coords_algebraMap_mul_inclR]
  have hfz : Reduction.HasFiniteContent (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e]
    exact (Reduction.hasFiniteContent_ratVec hz').smul s
  have h1 : 1 ≤ Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e, Reduction.adelicNorm_smul (Reduction.hasFiniteContent_ratVec hz')]
    exact one_le_mul_of_one_le_of_one_le hs (Reduction.one_le_adelicNorm_ratVec hz')
  exact h1.trans (hCb y hfy hfz)

end Forms

theorem min_le_of_one_le_mul_sq {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) (h : 1 ≤ D * t ^ 2) :
    min 1 D⁻¹ ≤ t := by
  by_cases h1 : 1 ≤ t
  · exact (min_le_left _ _).trans h1
  · replace h1 := not_le.1 h1
    have h3 : 1 ≤ D * t := by
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hD.le)
      nlinarith
    refine (min_le_right _ _).trans ?_
    rw [inv_le_iff_one_le_mul₀ hD, mul_comm]
    exact h3

theorem exists_pos_le_hgt_of_forms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (H : M → Matrix (Fin n) (Fin n) E) (L : Set (GAd σ J)), (∀ ξ : Fin n → E, (∀ j, hE σ (H j) ξ ξ = 0) → ξ = 0) → (∀ g ∈ L, ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (H j) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (H j) ξ ξ)) → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ := by
  intro F E _ _ _ _ _ σ hCM n J _ M _ H L hzero hL
  obtain ⟨hF, hEc, h2, hc⟩ := hCM
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  cases nonempty_fintype M
  choose C hC hCb using fun j => exists_adelicNorm_hermPoly_le (F := F) (H j)
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => (hC j).le
  have hD : 0 < 1 + ∑ j, C j := by linarith
  refine ⟨min 1 (1 + ∑ j, C j)⁻¹, lt_min one_pos (inv_pos.2 hD), fun g hg ξ hξ => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, hE (conj F E).toAlgHom (H j) ξ ξ ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hξ (hzero ξ hno)
  obtain ⟨s, hs, he⟩ := hL g hg j
  have h1 := one_le_mul_hgt_sq J (H j) (hCb j) g hξ s hs hj (he ξ)
  have ht : 0 ≤ hgt (conj F E).toAlgHom J g ξ := Reduction.adelicNorm_nonneg _
  have hle : C j ≤ 1 + ∑ j, C j := by
    have := Finset.single_le_sum (f := C) (fun i _ => (hC i).le) (Finset.mem_univ j)
    linarith
  exact min_le_of_one_le_mul_sq hD ht
    (h1.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)))

end GlobalTheory.CompanionTheory.ParCocompact.FormHeight

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IndicatorMemSBOfIsClopen
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.WeilM Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory GlobalTheory.CompanionTheory.ThetaCoord
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

namespace GlobalTheory.CompanionTheory.ThetaCoord.Cont

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def ratA (ξ : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (ξ i)

theorem continuous_finOf : Continuous (finOf : (κ → AF F) → κ → FiniteAdeleRing (𝓞 F) F) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

private theorem continuous_infiniteAdeleRing_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  first
  | exact (InfiniteAdeleRing.homeomorph_mixedSpace F).continuous
  | (rw [show (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        fun x => (fun v : {w : InfinitePlace F // w.IsReal} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1),
          fun v : {w : InfinitePlace F // w.IsComplex} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) from rfl]
     exact Continuous.prodMk
      (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _))
      (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)))

theorem continuous_infOf : Continuous (infOf : (κ → AF F) → κ → mixedEmbedding.mixedSpace F) := by
  exact continuous_pi fun i => continuous_infiniteAdeleRing_ringEquiv_mixedSpace.comp (continuous_fst.comp (continuous_apply i))

theorem indicator_mem_SB_of_isClopen {X : Type} [TopologicalSpace X] {V : Set X} (hV : IsClopen V) (hc : IsCompact V) :
    V.indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  refine ⟨fun s => ?_, ?_⟩
  · have h := Set.indicator_const_preimage V s (1 : ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h <;> rw [h]
    · exact isOpen_univ
    · exact hV.isOpen
    · exact hV.isClosed.isOpen_compl
    · exact isOpen_empty
  · exact HasCompactSupport.intro' hc hV.isClosed fun x hx => by simp [hx]

private theorem totallyDisconnectedSpace_finiteAdeleRing :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  let f : FiniteAdeleRing (𝓞 F) F → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun x v => x v
  have hf : Continuous f := by
    first
    | exact RestrictedProduct.continuous_coe
    | fun_prop
  have hi : Function.Injective f := by
    first
    | exact RestrictedProduct.coe_injective
    | exact fun x y h => Subtype.ext h
  refine ⟨fun s _ hs => ?_⟩
  have h1 : (f '' s).Subsingleton := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h1 (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))


open GroundTheory.Global in
theorem exists_clopen_superset [Fintype κ] {S : Set (κ → FiniteAdeleRing (𝓞 F) F)} (hS : IsCompact S) :
    ∃ V, IsClopen V ∧ IsCompact V ∧ S ⊆ V := by
  classical
  haveI := totallyDisconnectedSpace_finiteAdeleRing (F := F)
  have hB : TopologicalSpace.IsTopologicalBasis {s : Set (κ → FiniteAdeleRing (𝓞 F) F) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  have hx : ∀ x ∈ S, ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsClopen C ∧ IsCompact C ∧ x ∈ C := by
    intro x _
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
    obtain ⟨C, hCc, hxC, hCK⟩ := hB.mem_nhds_iff.1 hKx
    exact ⟨C, hCc, hK.of_isClosed_subset hCc.isClosed hCK, hxC⟩
  choose! C hCc hCk hxC using hx
  obtain ⟨t, htS, ht, hcov⟩ := hS.elim_finite_subcover_image (fun x hx => (hCc x hx).isOpen)
    (fun x hx => Set.mem_biUnion hx (hxC x hx))
  refine ⟨⋃ x ∈ t, C x, ⟨ht.isClosed_biUnion fun x hx => (hCc x (htS hx)).isClosed,
    isOpen_biUnion fun x hx => (hCc x (htS hx)).isOpen⟩, ht.isCompact_biUnion fun x hx => hCk x (htS hx), hcov⟩

theorem infOf_ratA_add [Fintype κ] (ξ : κ → F) (a : κ → AF F) :
    infOf (ratA ξ + a) = (fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) + infOf a := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (ξ i) + (a i).1) =
    mixedEmbedding F (ξ i) + InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1
  rw [map_add (f := _), InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F]

theorem finOf_ratA_add (ξ : κ → F) (a : κ → AF F) :
    finOf (ratA ξ + a) = (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finOf a := rfl


open scoped Classical in
theorem pure_bound [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F))
    {K : Set (κ → AF F)} (hK : IsCompact K) :
    ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖pureA F f g (ratA ξ + a)‖ ≤ u ξ := by
  obtain ⟨hgl, hgc⟩ := hg
  obtain ⟨M, hM⟩ := hgl.continuous.bounded_above_of_compact_support hgc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R0, hR0⟩ := (hK.image continuous_infOf).isBounded.exists_norm_le
  have hD : IsCompact ((fun q : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) => q.1 - q.2) ''
      (tsupport g ×ˢ (finOf '' K))) :=
    (hgc.isCompact.prod (hK.image continuous_finOf)).image continuous_sub
  obtain ⟨V, hVc, hVk, hDV⟩ := exists_clopen_superset hD
  obtain ⟨k, hk⟩ := GlobalTheory.CompanionTheory.ThetaAdm.summable_weight F (indicator_mem_SB_of_isClopen hVc hVk)
  have hC : ∀ z, (1 + ‖z‖) ^ k * ‖f z‖ ≤
      2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := fun z => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f z
    simpa [norm_iteratedFDeriv_zero] using this
  obtain ⟨C, hCdef⟩ : ∃ C, C = 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := ⟨_, rfl⟩
  rw [← hCdef] at hC
  have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hC 0)
  obtain ⟨R, hR, hRdef⟩ : ∃ R : ℝ, 0 ≤ R ∧ R = max R0 0 := ⟨_, le_max_right _ _, rfl⟩
  refine ⟨fun ξ => (M * (C * (1 + R) ^ k)) *
    (‖V.indicator (fun _ => (1 : ℂ)) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ *
      ((1 + ‖(fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F)‖) ^ k)⁻¹), hk.mul_left _, ?_⟩
  intro ξ a ha
  beta_reduce
  have hpure : pureA F f g (ratA ξ + a) =
      f ((fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) + infOf a) *
        g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finOf a) := by
    show f (infOf (ratA ξ + a)) * g (finOf (ratA ξ + a)) = _
    rw [infOf_ratA_add, finOf_ratA_add]
  rw [hpure, norm_mul]
  generalize hp : (fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) = p
  generalize hy : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) = y
  have hRa : ‖infOf a‖ ≤ R := hRdef ▸ (hR0 _ ⟨a, ha, rfl⟩).trans (le_max_left _ _)
  have hf1 : ‖f (p + infOf a)‖ ≤ C * (1 + R) ^ k * ((1 + ‖p‖) ^ k)⁻¹ := by
    have h0 : ‖p‖ ≤ ‖p + infOf a‖ + ‖infOf a‖ := by
      simpa using norm_sub_le (p + infOf a) (infOf a)
    have h1 : 1 + ‖p‖ ≤ (1 + ‖p + infOf a‖) * (1 + R) := by
      nlinarith [norm_nonneg (p + infOf a), norm_nonneg (infOf a)]
    have hpos : 0 < 1 + ‖p‖ := by positivity
    have h2 : (1 + ‖p‖) ^ k ≤ (1 + ‖p + infOf a‖) ^ k * (1 + R) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hpos.le h1 k
    have h3 := hC (p + infOf a)
    rw [le_mul_inv_iff₀ (by positivity)]
    calc ‖f (p + infOf a)‖ * (1 + ‖p‖) ^ k
        ≤ ‖f (p + infOf a)‖ * ((1 + ‖p + infOf a‖) ^ k * (1 + R) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ((1 + ‖p + infOf a‖) ^ k * ‖f (p + infOf a)‖) * (1 + R) ^ k := by ring
      _ ≤ C * (1 + R) ^ k := mul_le_mul_of_nonneg_right h3 (by positivity)
  have hg1 : ‖g (y + finOf a)‖ ≤ M * ‖V.indicator (fun _ => (1 : ℂ)) y‖ := by
    by_cases hyV : y ∈ V
    · rw [Set.indicator_of_mem hyV, norm_one, mul_one]
      exact hM _
    · have hz : g (y + finOf a) = 0 := by
        by_contra hne
        apply hyV
        apply hDV
        exact ⟨(y + finOf a, finOf a), ⟨subset_tsupport g hne, ⟨a, ha, rfl⟩⟩, by simp⟩
      rw [hz, norm_zero]
      exact mul_nonneg hM0 (norm_nonneg _)
  calc ‖f (p + infOf a)‖ * ‖g (y + finOf a)‖
      ≤ (C * (1 + R) ^ k * ((1 + ‖p‖) ^ k)⁻¹) * (M * ‖V.indicator (fun _ => (1 : ℂ)) y‖) :=
        mul_le_mul hf1 hg1 (norm_nonneg _) (by positivity)
    _ = M * (C * (1 + R) ^ k) * (‖V.indicator (fun _ => (1 : ℂ)) y‖ * ((1 + ‖p‖) ^ k)⁻¹) := by ring


open scoped Classical in
theorem schA_bound [Fintype κ] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Continuous Φ ∧ ∀ K : Set (κ → AF F), IsCompact K →
      ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖Φ (ratA ξ + a)‖ ≤ u ξ := by
  refine Submodule.span_induction (p := fun Φ _ => Continuous Φ ∧ ∀ K : Set (κ → AF F), IsCompact K →
      ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖Φ (ratA ξ + a)‖ ≤ u ξ) ?_ ?_ ?_ ?_ hΦ
  · rintro x ⟨f, g, hg, rfl⟩
    refine ⟨?_, fun K hK => pure_bound f hg hK⟩
    show Continuous fun x => f (infOf x) * g (finOf x)
    exact (f.continuous.comp continuous_infOf).mul (hg.1.continuous.comp continuous_finOf)
  · refine ⟨continuous_const, fun K _ => ⟨0, summable_zero, fun ξ a _ => by simp⟩⟩
  · rintro x y _ _ ⟨hxc, hxb⟩ ⟨hyc, hyb⟩
    refine ⟨hxc.add hyc, fun K hK => ?_⟩
    obtain ⟨u, hu, hub⟩ := hxb K hK
    obtain ⟨v, hv, hvb⟩ := hyb K hK
    exact ⟨u + v, hu.add hv, fun ξ a ha => (norm_add_le _ _).trans (add_le_add (hub ξ a ha) (hvb ξ a ha))⟩
  · rintro c x _ ⟨hxc, hxb⟩
    refine ⟨hxc.const_smul c, fun K hK => ?_⟩
    obtain ⟨u, hu, hub⟩ := hxb K hK
    refine ⟨fun ξ => ‖c‖ * u ξ, hu.mul_left _, fun ξ a ha => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hub ξ a ha) (norm_nonneg _)

end GlobalTheory.CompanionTheory.ThetaCoord.Cont

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalCommutesProjectionFamily
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.LeviComm

section Ring

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem pfr_swap (hF : PFr s Jm Xm Ym) : PFr s Jm Ym Xm :=
  ⟨hF.ss, hF.herm, hF.yy, hF.xx, hF.yx⟩

theorem row_mul {g : Matrix (Fin n) (Fin n) R} (hF : PFr s Jm Xm Ym) (hg : cT s g * Jm * g = Jm) {d d' : Fin r → R}
    (hX : g * Xm = Xm * diagonal d) (hY : g * Ym = Ym * diagonal d') :
    cT s Ym * Jm * g = diagonal d * (cT s Ym * Jm) := by
  have h1 : cT s (diagonal d') * diagonal d = 1 := by
    have e := pgram_unitary hg Ym Xm
    rw [hY, hX, hF.yx, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * diagonal d
        = cT s (diagonal d') * (cT s Ym * Jm * Xm) * diagonal d := by rw [hF.yx, Matrix.mul_one]
      _ = 1 := by rw [← e]; simp only [Matrix.mul_assoc]
  have h2 : diagonal d * cT s (diagonal d') = 1 := mul_eq_one_comm.1 h1
  have h3 : cT s (diagonal d') * (cT s Ym * Jm * g) = cT s Ym * Jm := by
    have e : cT s (g * Ym) * Jm * g = cT s Ym * Jm := by
      conv_rhs => rw [← hg]
      simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    rw [hY, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * (cT s Ym * Jm * g) = cT s (diagonal d') * cT s Ym * Jm * g := by
          simp only [Matrix.mul_assoc]
      _ = cT s Ym * Jm := e
  calc cT s Ym * Jm * g = diagonal d * cT s (diagonal d') * (cT s Ym * Jm * g) := by rw [h2, Matrix.one_mul]
    _ = diagonal d * (cT s Ym * Jm) := by rw [Matrix.mul_assoc, h3]

theorem comm_vecMulVec {m : ℕ} {g : Matrix (Fin n) (Fin n) R} {C : Matrix (Fin n) (Fin m) R}
    {A : Matrix (Fin m) (Fin n) R} {d : Fin m → R} (hC : g * C = C * diagonal d) (hA : A * g = diagonal d * A)
    (i : Fin m) : g * vecMulVec (fun k => C k i) (A i) = vecMulVec (fun k => C k i) (A i) * g := by
  ext a b
  have e1 : ∑ k, g a k * C k i = C a i * d i := by
    have := congrFun (congrFun hC a) i
    rwa [Matrix.mul_apply, Matrix.mul_diagonal] at this
  have e2 : ∑ k, A i k * g k b = d i * A i b := by
    have := congrFun (congrFun hA i) b
    rwa [Matrix.mul_apply, Matrix.diagonal_mul] at this
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  calc ∑ k, g a k * (C k i * A i b) = (∑ k, g a k * C k i) * A i b := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = C a i * (d i * A i b) := by rw [e1, mul_assoc]
    _ = C a i * ∑ k, A i k * g k b := by rw [e2]
    _ = ∑ k, C a i * A i k * g k b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem lineProj_map (C D : Matrix (Fin n) (Fin r) E) (i : Fin r) :
    (lineProj σ J C D i).map (inclR (F := F) (AF F)) =
      vecMulVec (fun k => adMat F C k i)
        (((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) i) := by
  have e : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) =
      (cT (σ : E →+* E) D * J).map (inclR (F := F) (AF F)) := by
    unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul]
  rw [e]
  ext a b
  exact map_mul (inclR (F := F) (AF F)) (C a i) ((cT (σ : E →+* E) D * J) i b)

theorem leviMin_comm_projFam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (m) (hm : m ∈ leviMin σ J X Y) (k) :
    (matHom _ σ J m).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) =
      (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J m).1 := by
  obtain ⟨d, d', hX, hY⟩ := hm
  have hF := pfrA h hJ hW
  have hg := unitaryA_matHom m
  rcases k with i | i
  · simp only [projFam, Sum.elim_inl]
    rw [lineProj_map]
    exact comm_vecMulVec hX (row_mul hF hg hX hY) i
  · simp only [projFam, Sum.elim_inr]
    rw [lineProj_map]
    exact comm_vecMulVec hY (row_mul (pfr_swap hF) hg hY hX) i

end GlobalTheory.CompanionTheory.ParCocompact.LeviComm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEq
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.ClozelPurity

theorem EopV_val (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ) (i j : Fin a) (φ : π.V) : (EopV π τ i j φ).1 = Eop τ i j φ.1 := by
  simp [EopV, Eop, lieS_apply, CuspSub.op_val, act]

end GlobalTheory.CompanionTheory.ClozelPurity

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SameSpanTransferMatricesStatement
section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_span_transfer_matrices : ∀ {K : Type} [Field K] {n r : ℕ} (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K), LinearIndependent K c → Submodule.span K (Set.range c) = Submodule.span K (Set.range C) → ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), C = T * c ∧ c = L * C ∧ L * T = 1 := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq | exact GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq | (intros; apply GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq <;> assumption)
end

