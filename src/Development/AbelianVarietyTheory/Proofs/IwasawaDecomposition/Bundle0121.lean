module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalToGlobal.Divisibility.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetUnfold
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.Unfold

theorem tsum_indicator_coset_complex {G : Type} [Group G] (Γ K : Subgroup G) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (x : G) :
    ∑' γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ℂ) (γ • x)
      = ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ℂ) *
        {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}.indicator 1 x := by
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : IsTopologicalGroup G := isTopologicalGroup_of_discreteTopology
  have h := congrArg ENNReal.toReal (GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin x)
  rw [ENNReal.tsum_toReal_eq (fun γ => by
    by_cases hγ : γ • x ∈ (fun y => a⁻¹ * y) ⁻¹' (K : Set G)
    · rw [Set.indicator_of_mem hγ]; simp
    · rw [Set.indicator_of_notMem hγ]; simp)] at h
  have h2 := congrArg (fun r : ℝ => (r : ℂ)) h
  simp only [Complex.ofReal_tsum] at h2
  convert h2 using 1
  · congr 1; funext γ
    by_cases hγ : γ • x ∈ (fun y => a⁻¹ * y) ⁻¹' (K : Set G)
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]; simp
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hγ]; simp
  · by_cases hx : x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem unfold_coset (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G)
    [Countable Γ] (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (hK : IsOpen (K : Set G)) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (f : G → ℂ)
    (hfl : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x)
    (hf : IntegrableOn f ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)) ν) :
    IntegrableOn f {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} (ν.restrict 𝓖) ∧
    ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ℂ) *
      ∫ x in {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}, f x ∂(ν.restrict 𝓖)
      = ∫ x in (fun y => a⁻¹ * y) ⁻¹' (K : Set G), f x ∂ν := by
  set A := (fun y => a⁻¹ * y) ⁻¹' (K : Set G) with hAdef
  set C := {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} with hCdef
  set n := {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard with hndef
  have hA : MeasurableSet A := (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hC : MeasurableSet C := (GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK a).measurableSet
  have hn : n ≠ 0 := ((Set.ncard_pos hfin).2 ⟨1, Γ.one_mem, by simp⟩).ne'
  have hcount : ∀ x, ∑' γ : Γ, A.indicator (1 : G → ENNReal) (γ • x) = (n : ENNReal) * C.indicator 1 x :=
    GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin
  have hcountC : ∀ x, ∑' γ : Γ, A.indicator (1 : G → ℂ) (γ • x) = (n : ℂ) * C.indicator 1 x :=
    tsum_indicator_coset_complex Γ K a hfin
  have hφ : Integrable (A.indicator f) ν := hf.integrable_indicator hA
  have hpt : ∀ (γ : Γ) x, A.indicator f (γ • x) = A.indicator (1 : G → ℂ) (γ • x) * f x := by
    intro γ x
    have : f (γ • x) = f x := hfl γ γ.2 x
    by_cases hx : γ • x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, this]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hptE : ∀ (γ : Γ) x,
      ‖A.indicator f (γ • x)‖ₑ = A.indicator (1 : G → ENNReal) (γ • x) * ‖f x‖ₑ := by
    intro γ x
    have : f (γ • x) = f x := hfl γ γ.2 x
    by_cases hx : γ • x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, this]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, eNorm_zero]
  have hmeasγ : ∀ γ : Γ, AEStronglyMeasurable (fun x => A.indicator f (γ • x)) (ν.restrict 𝓖) := by
    intro γ
    exact (hφ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_smul γ ν).quasiMeasurePreserving).restrict
  have hlin : ∑' γ : Γ, ∫⁻ x in 𝓖, ‖A.indicator f (γ • x)‖ₑ ∂ν = ∫⁻ x, ‖A.indicator f x‖ₑ ∂ν :=
    (h𝓖.lintegral_eq_tsum'' (fun x => ‖A.indicator f x‖ₑ)).symm
  have hlin2 : ∑' γ : Γ, ∫⁻ x in 𝓖, ‖A.indicator f (γ • x)‖ₑ ∂ν
      = (n : ENNReal) * ∫⁻ x in C, ‖f x‖ₑ ∂(ν.restrict 𝓖) := by
    rw [← lintegral_tsum (fun γ => (hmeasγ γ).eNorm)]
    simp_rw [hptE, ENNReal.tsum_mul_right, hcount]
    rw [← lintegral_indicator hC, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ C
    · simp [Set.indicator_of_mem hx, hndef]
    · simp [Set.indicator_of_notMem hx]
  have hCU : C = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' A := by
    ext x
    simp only [hCdef, hAdef, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
      have : a⁻¹ * (γ⁻¹ * (γ * a * k)) = k := by group
      simpa [this] using hk
    · rintro ⟨γ, hγ⟩
      exact ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, hγ, by group⟩
  have hintγ : ∀ γ : Γ, IntegrableOn f ((fun x => (γ : G) * x) ⁻¹' A) ν := by
    intro γ
    have := ((measurePreserving_mul_left ν (γ : G)).integrableOn_comp_preimage
      (measurableEmbedding_mulLeft (γ : G)) (f := f) (s := A)).2 hf
    have hfeq : f ∘ (fun x => (γ : G) * x) = f := funext fun x => hfl γ γ.2 x
    rwa [hfeq] at this
  have hmeasC : AEStronglyMeasurable f ((ν.restrict 𝓖).restrict C) := by
    have : AEStronglyMeasurable f (ν.restrict C) := by
      rw [hCU, aestronglyMeasurable_iUnion_iff]
      exact fun γ => (hintγ γ).aestronglyMeasurable
    exact this.mono_measure (Measure.restrict_mono subset_rfl Measure.restrict_le_self)
  have hfinC : ∫⁻ x in C, ‖f x‖ₑ ∂(ν.restrict 𝓖) ≠ ⊤ := by
    intro htop
    have h1 := hlin2.symm.trans hlin
    rw [htop, ENNReal.mul_top (by exact_mod_cast hn)] at h1
    exact hφ.hasFiniteIntegral.ne h1.symm
  have hintC : IntegrableOn f C (ν.restrict 𝓖) := ⟨hmeasC, hfinC.lt_top⟩
  refine ⟨hintC, ?_⟩
  rw [← integral_indicator hA, h𝓖.integral_eq_tsum'' _ hφ,
    ← integral_tsum hmeasγ (by rw [hlin]; exact hφ.hasFiniteIntegral.ne)]
  simp_rw [hpt, tsum_mul_right, hcountC]
  rw [← integral_indicator hC, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ C
  · simp [Set.indicator_of_mem hx, hndef]
  · simp [Set.indicator_of_notMem hx]

end GlobalTheory.Unfold

namespace GlobalTheory.Unfold

theorem integral_fundamentalDomain_eq_sum_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ Ω : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (Ω : Set G) → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ Ω, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.Finite) → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ i, IntegrableOn (fun k => f (h i * k)) Ω ν) → IntegrableOn f 𝓖 ν ∧ ∫ x in 𝓖, f x ∂ν = ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard : ℕ) : ℂ)⁻¹ * ∫ k in (Ω : Set G), f (h i * k) ∂ν := by
  intro G _ _ _ _ _ ν _ Γ Ω _ 𝓖 h𝓖 hΩ ι _ h huniq hfin f hfl hf
  set C : ι → Set G := fun i => {x : G | ∃ γ ∈ Γ, ∃ k ∈ Ω, x = γ * h i * k} with hCdef
  have hC : ∀ i, MeasurableSet (C i) := fun i =>
    (GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ Ω hΩ (h i)).measurableSet
  have hpos : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard ≠ 0 := fun i =>
    ((Set.ncard_pos (hfin i)).2 ⟨1, Γ.one_mem, by simp⟩).ne'
  have hpre : ∀ i, (fun y => h i * y) ⁻¹' ((fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G)) = Ω := by
    intro i; ext k; simp
  have hA : ∀ i, IntegrableOn f ((fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G)) ν := by
    intro i
    refine ((measurePreserving_mul_left ν (h i)).integrableOn_comp_preimage
      (measurableEmbedding_mulLeft (h i))).1 ?_
    rw [hpre]; exact hf i
  have hAint : ∀ i, ∫ x in (fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G), f x ∂ν
      = ∫ k in (Ω : Set G), f (h i * k) ∂ν := by
    intro i
    have := (measurePreserving_mul_left ν (h i)).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft (h i)) f ((fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G))
    rw [hpre] at this
    exact this.symm
  have hU := fun i => unfold_coset ν Γ Ω 𝓖 h𝓖 hΩ (h i) (hfin i) f hfl (hA i)
  have hF : f = fun x => ∑ i, (C i).indicator f x := by
    funext x
    obtain ⟨i, hi, hu⟩ := huniq x
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show x ∈ C i from hi)]
    · intro j _ hj
      exact Set.indicator_of_notMem (s := C j) (fun hx => hj (hu j hx)) f
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hint : ∀ i, Integrable ((C i).indicator f) (ν.restrict 𝓖) := fun i =>
    (integrable_indicator_iff (hC i)).2 (hU i).1
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hF]
    exact integrable_finsetSum _ fun i _ => hint i
  · have h1 : ∫ x in 𝓖, f x ∂ν = ∫ x in 𝓖, ∑ i, (C i).indicator f x ∂ν := by
      conv_lhs => rw [hF]
    rw [h1, integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator (hC i), ← hAint i, ← (hU i).2]
    have : (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos i
    rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]

end GlobalTheory.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawNormClassSumFock
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix
open scoped ComplexOrder

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K)

theorem classSum_gram_posDef (s : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (hpos : ∀ w, w ≠ 0 → 0 < B w w) (hsym : ∀ w w', star (B w w') = B w' w)
    (ψ : C.V → W) (hψ : ∀ x, ψ x = 0 → x = 0) (hs : ∀ x y, s (C.pair x y) = B (ψ x) (ψ y)) :
    (C.H.map s).PosDef := by
  classical
  have hnn : ∀ w, 0 ≤ B w w := fun w => by
    by_cases h : w = 0
    · simp [h]
    · exact (hpos w h).le
  have hw : ∀ c, (0 : ℂ) < ((C.wt c : ℂ))⁻¹ := fun c => inv_pos.2 (by exact_mod_cast C.wt_pos c)
  have hc : ∀ f g : C.Cl → C.V, s (C.csum f g) = ∑ c, ((C.wt c : ℂ))⁻¹ * B (ψ (f c)) (ψ (g c)) := by
    intro f g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CSD.csum, map_sum, map_mul, map_inv₀, map_natCast, hs]
  have hsemi : (C.H.map s).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, CSD.H, Matrix.of_apply, hc, star_sum, star_mul', hsym,
        star_inv₀, star_natCast]
    · intro x
      have e : star x ⬝ᵥ (C.H.map s) *ᵥ x = ∑ c, ((C.wt c : ℂ))⁻¹ *
          B (∑ i, x i • ψ ((C.basis i : C.Cl → C.V) c)) (∑ j, x j • ψ ((C.basis j : C.Cl → C.V) c)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, CSD.H, Matrix.of_apply, hc, map_sum, LinearMap.sum_apply,
          LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, Pi.star_apply,
          starRingEnd_apply, RingHom.id_apply]
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (hw c).le (hnn _)
  rw [hsemi.posDef_iff_det_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : C.csum (C.I v) (C.I v) = 0 := by
    rw [C.csum_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : ∑ j, C.H i j * v j = 0 := congrFun hv0 i
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h2, mul_zero]
  have h2 := hc (C.I v) (C.I v)
  rw [h1, map_zero, eq_comm, Finset.sum_eq_zero_iff_of_nonneg fun c _ => mul_nonneg (hw c).le (hnn _)] at h2
  apply hv
  apply C.I_injective
  rw [map_zero]
  funext c
  refine hψ _ ?_
  by_contra hne
  exact (mul_pos (hw c) (hpos _ hne)).ne' (h2 c (Finset.mem_univ c))

theorem majAt_stdFrame_classSum (v : InfinitePlace K) (hv : ∀ a, v.embedding (star a) = starRingEnd ℂ (v.embedding a))
    (hH : (C.H.map v.embedding).PosDef) (x y : C.Forms) :
    Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x y = v.embedding (C.csum x.1 y.1) := by
  have hI : ∀ z : C.Forms, C.I (C.basis.equivFun z) = z.1 := fun z => by simp [CSD.I_apply]
  have h1 : Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin C.dim)) (stdFrame C.H) v (C.basis.equivFun x) (C.basis.equivFun y) := by
    have h2 : ∀ z : C.Forms, Formalism.HermitianLatticesTheory.vecAt C.basis v z =
        Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin C.dim)) v (C.basis.equivFun z) := by
      intro z; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h2]
  have hm : metOf (stdFrame C.H v) = C.H.map v.embedding := (frameOfSpec _ _ hH).2
  rw [h1, majAt_eq, hm, ← hI x, ← hI y, C.csum_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, hv, Finset.mul_sum, Pi.star_apply,
    starRingEnd_apply, mul_assoc]

end ClassSum

section Pair

variable {E K ι : Type} [Field E] [Field K] [StarRing K] [Fintype ι] {n : ℕ}

theorem map_pairVr_one (emb : ι → E →+* K) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (hs : ∀ a, s (star a) = starRingEnd ℂ (s a)) (F F' : VV K lam) :
    s (pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) F F') = nfL lam (MvPolynomial.map s F.1) (MvPolynomial.map s F'.1) := by
  have h := pairVr_nfAll emb (1 : Matrix (Fin n) (Fin n) E) lam s (stdFrC (embAt s emb))
    (fun τ => by simp [stdFrC, gramC]) F F' (fun m => hs _)
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (stdFrC (n := n) (embAt s emb)).1 = AlgHom.id ℂ _ := blockAct_one
  rw [h, e, nfL_apply]
  simp [stdFrC]

end Pair

theorem GStep.lawNorm : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h [Fintype S.Cl], S.LawNorm emb σ lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF _ h inst x
  have hv : ∀ a, (InfinitePlace.mk σ).embedding (star a) = starRingEnd ℂ ((InfinitePlace.mk σ).embedding a) := by
    intro a
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e, hF.sig_star]
    · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hF.sig_star]
  have hre : ∀ a, ((InfinitePlace.mk σ).embedding a).re = (σ a).re := by
    intro a
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e]
    · rw [e, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  have hH : ((S.csd emb lam h).H.map (InfinitePlace.mk σ).embedding).PosDef :=
    classSum_gram_posDef (S.csd emb lam h) _ (nfL lam) (ps_nfL_pos lam) (ps_nfL_symm lam)
      (fun F : VV K lam => MvPolynomial.map (InfinitePlace.mk σ).embedding F.1)
      (fun F hF0 => Subtype.ext (MvPolynomial.map_injective _ (RingHom.injective _) (hF0.trans (map_zero _).symm)))
      (fun F F' => map_pairVr_one emb lam _ hv F F')
  have h1 := majAt_stdFrame_classSum (S.csd emb lam h) (InfinitePlace.mk σ) hv hH x x
  refine (congrArg Complex.re h1).trans ?_
  rw [hre]
  congr 1
  have hi : inst = (S.csd emb lam h).finCl := Subsingleton.elim _ _
  subst hi
  unfold CSD.csum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  have h2 : (S.csd emb lam h).wt c = Nat.card (S.Stab c) := (@Nat.card_eq_fintype_card _ (_)).symm
  rw [h2]
  congr 1
  exact (ipFr_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (fr0 emb σ n) (fun τ => by simp [fr0, stdFrC, gramC]) _ _
    (fun m => hF.sig_star _)).symm

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalDilatedClass
section
noncomputable section

namespace GlobalTheory.Mem.Col2.DilFv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem exists_red_equiv {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (I : Ideal R) (u : M ≃ₗ[R] M') :
    ∃ e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] (M' ⧸ (I • (⊤ : Submodule R M'))),
      ∀ x, e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u x) := by
  have h : (I • (⊤ : Submodule R M)).map (u : M →ₗ[R] M') = I • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  refine ⟨(Submodule.Quotient.equiv _ _ u h).extendScalarsOfSurjective Ideal.Quotient.mk_surjective, fun x => rfl⟩

theorem exists_red_dual {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (u : M →ₗ[R] R ⧸ I) :
    ∃ φ : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I] (R ⧸ I), ∀ x, φ (Submodule.Quotient.mk x) = u x := by
  have h : (I • (⊤ : Submodule R M)) ≤ LinearMap.ker u := by
    refine Submodule.smul_le.2 fun r hr x _ => ?_
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
  exact ⟨(Submodule.liftQ _ u h).extendScalarsOfSurjective Ideal.Quotient.mk_surjective, fun x => rfl⟩

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) {T : ℕ}

theorem fv_mk (h : A.Ok T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have hex : ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x :=
    exists_red_dual P.1.asIdeal
      { toFun := fun x : A.N c.1 (S.rep c) => A.f c.1 (S.rep c) P x
        map_add' := fun x y => h.f_add _ _ P x x.2 y y.2
        map_smul' := fun a x => h.f_smul _ _ P a x x.2 }
  unfold TDat.fv
  rw [dite_eq_left hex]
  exact hex.choose_spec x

theorem exists_act_equiv (h : A.Ok T) (b : S.β) (g : S.G b) (d : S.D b) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : A.N b (g • d) = M) :
    ∃ u : A.N b d ≃ₗ[𝓞 E] M, ∀ x, (u x : Fin n → E) = (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ (x : Fin n → E) := by
  subst hM
  have h1 : ∀ x : Fin n → E, (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ
      ((S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  have h2 : ∀ x : Fin n → E, (S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ
      ((S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨{ toFun := fun x => ⟨(S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x.1, (h.N_act b g d x.1).2 x.2⟩
            invFun := fun y => ⟨(S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ y.1,
              (h.N_act b g d _).1 (by rw [h1]; exact y.2)⟩
            map_add' := fun x y => Subtype.ext (Matrix.mulVec_add _ x.1 y.1)
            map_smul' := fun a x => Subtype.ext (Matrix.mulVec_smul _ a x.1)
            left_inv := fun x => Subtype.ext (h2 _)
            right_inv := fun y => Subtype.ext (h1 _) }, fun x => rfl⟩

theorem dil_fv : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → ∀ P a c,
    ∃ e : A.lv P (S.cl c.1 (A.diaPt P a c)) ≃ₗ[Res P.1] A.lv P c,
      ∀ x, A.fv P (S.cl c.1 (A.diaPt P a c)) x = (a : Res P.1) * A.fv P c (e x) := by
  intro E K _ _ _ _ n S ST A T _ h P a c
  obtain ⟨g, hmv⟩ : ∃ g : S.G c.1, g • S.rep (S.cl c.1 (A.diaPt P a c)) = A.diaPt P a c :=
    (MulAction.orbitRel (S.G c.1) (S.D c.1)).symm (Quotient.exact (S.rp_spec c.1 (Quotient.mk _ (A.diaPt P a c))))
  obtain ⟨u, hu⟩ := exists_act_equiv A h c.1 g (S.rep (S.cl c.1 (A.diaPt P a c)))
    (A.N c.1 (S.rep c)) (by rw [hmv]; exact h.dia_N _ _ _ _)
  obtain ⟨e, he⟩ := exists_red_equiv P.1.asIdeal u
  refine ⟨e, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have e1 := fv_mk A h P (S.cl c.1 (A.diaPt P a c)) x
  have e2 := fv_mk A h P c (u x)
  have e3 := h.f_act c.1 g (S.rep (S.cl c.1 (A.diaPt P a c))) P x
  rw [hmv, ← hu] at e3
  have e4 := h.dia_f c.1 P a (S.rep c) (u x)
  refine e1.trans (e3.symm.trans (e4.trans ?_))
  exact congrArg _ (e2.symm.trans (congrArg _ (he x).symm))

end GlobalTheory.Mem.Col2.DilFv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLaws
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.TDat

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) {T : ℕ}

theorem exists_fv (h : A.Ok T) (P : ST) (c : S.Cl) :
    ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  let g : A.N c.1 (S.rep c) →ₗ[𝓞 E] Res P.1 :=
    { toFun := fun x => A.f c.1 (S.rep c) P x
      map_add' := fun x y => h.f_add _ _ _ _ x.2 _ y.2
      map_smul' := fun a x => by
        have := h.f_smul _ _ P a _ x.2
        simp only [RingHom.id_apply]
        rw [Submodule.coe_smul, this]
        rfl }
  have hk : P.1.asIdeal • (⊤ : Submodule (𝓞 E) (A.N c.1 (S.rep c))) ≤ LinearMap.ker g := by
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    show Ideal.Quotient.mk P.1.asIdeal a * g x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  let g' : A.lv P c →ₗ[𝓞 E] Res P.1 := Submodule.liftQ _ g hk
  refine ⟨{ toFun := g', map_add' := g'.map_add, map_smul' := ?_ }, fun x => rfl⟩
  intro r x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact g'.map_smul a x

theorem fv_mk (h : A.Ok T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have hx := A.exists_fv h P c
  unfold fv
  rw [dite_eq_left hx]
  exact hx.choose_spec x

theorem fv_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.fv P c ≠ 0 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne c.1 (S.rep c) P
  intro h0
  have := A.fv_mk h P c ⟨x, hx⟩
  rw [h0] at this
  exact hne this.symm

theorem exists_f_eq_one (h : A.Ok T) (b : S.β) (d : S.D b) (P : ST) : ∃ e ∈ A.N b d, A.f b d P e = 1 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne b d P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (A.f b d P x)⁻¹
  refine ⟨a • x, (A.N b d).smul_mem a hx, ?_⟩
  rw [h.f_smul b d P a x hx, ha]
  exact inv_mul_cancel₀ hne

theorem te_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.te T P c ≠ 0 := by
  have hx : ∃ t : A.dnN c.1 (S.rep c) P, ∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧
      (t : Fin n → E) = (T : 𝓞 E) • e := by
    obtain ⟨e, he, h1⟩ := A.exists_f_eq_one h c.1 (S.rep c) P
    exact ⟨⟨_, (h.te_mem _ _ P e he h1).1⟩, e, he, h1, rfl⟩
  unfold te
  rw [dite_eq_left hx]
  obtain ⟨e, he, h1, ht⟩ := hx.choose_spec
  intro h0
  rw [Submodule.Quotient.mk_eq_zero] at h0
  apply (h.te_mem _ _ P e he h1).2
  rw [← ht]
  have := Submodule.mem_map_of_mem (f := (A.dnN c.1 (S.rep c) P).subtype) h0
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
  exact this

end GlobalTheory.Mem.Col2.TDat

namespace GlobalTheory.Mem.Col2

theorem fv_te_laws : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T →
    (∀ P c (x : A.N c.1 (S.rep c)), A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x) ∧
    (∀ P c, A.fv P c ≠ 0) ∧ ∀ P c, A.te T P c ≠ 0 :=
  fun A _ _ h => ⟨A.fv_mk h, A.fv_ne_zero h, A.te_ne_zero h⟩

end GlobalTheory.Mem.Col2
end

