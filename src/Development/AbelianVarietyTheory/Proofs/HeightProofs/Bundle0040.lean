module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0037
public import Formalism.RealPlaceAnalysis.FinalF

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrobeniusFixesOfSplitsCompletelyIntermediate
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
open scoped Pointwise

namespace GlobalTheory.SplitCriterion

theorem frob_fix_of_ncard_primes_eq_finrank (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N]
    [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard
      = Module.finrank K M) (σ : N ≃ₐ[K] N) (hσ : GlobalTheory.NT.IsFrob N 𝔭 σ) : ∀ x ∈ M, σ x = x := by
  have := 𝔭.isPrime
  obtain ⟨P, hP, hPo, hx⟩ := hσ
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hq : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.ne_bot
  have hfix : σ⁻¹ • P = P := by
    symm
    refine hPm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun x hxP => ?_
    rw [Ideal.mem_inv_pointwise_smul_iff]
    have h1 := P.add_mem (hx x) (P.pow_mem_of_mem hxP _ (Nat.pos_of_ne_zero hq))
    rw [sub_add_cancel] at h1
    exact h1
  let f : (N ≃ₐ[K] N) → Ideal (𝓞 M) := fun σ => (σ⁻¹ • P).under (𝓞 M)
  have hker : ∀ σ τ, σ⁻¹ * τ ∈ M.fixingSubgroup → f σ = f τ := by
    intro σ τ e
    have e' := (IntermediateField.mem_fixingSubgroup_iff _ _).1 e
    ext x
    simp only [f, Ideal.under, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff]
    have : (σ⁻¹ * τ) • algebraMap (𝓞 M) (𝓞 N) x = algebraMap (𝓞 M) (𝓞 N) x := by
      apply RingOfIntegers.ext
      exact e' _ (x : M).2
    rw [mul_smul, inv_smul_eq_iff] at this
    rw [this]
  have hr : Set.range f = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨inferInstance, ⟨?_⟩⟩
      simp only [f]
      rw [Ideal.under_under]
      exact Ideal.LiesOver.over
    · rintro ⟨hQ, hQo⟩
      obtain ⟨P', hP', hPo'⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 N)))
      have : P'.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans P' Q _
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 N) (N ≃ₐ[K] N) P P'
        (hPo.over.symm.trans this.over)
      exact ⟨g⁻¹, by simp only [f]; rw [inv_inv, ← hg]; exact hPo'.over.symm⟩
  have hs : (fun Q : HeightOneSpectrum (𝓞 M) => Q.asIdeal) ''
      {Q | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal} = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩
    · rintro ⟨hQ, hQo⟩
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQo.over.symm, rfl⟩
  rw [← Set.ncard_image_of_injective _ (fun _ _ e => HeightOneSpectrum.ext e), hs, ← hr,
    IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq] at h
  let F : (N ≃ₐ[K] N) ⧸ M.fixingSubgroup → Set.range f :=
    Quotient.lift (fun g => ⟨f g, g, rfl⟩) fun a b e =>
      Subtype.ext (hker a b (QuotientGroup.leftRel_apply.1 e))
  have hF : Function.Surjective F := by
    rintro ⟨_, g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hinj : Function.Injective F := (hF.bijective_of_nat_card_le h.ge).1
  have h1 : F (QuotientGroup.mk 1) = F (QuotientGroup.mk σ) := by
    apply Subtype.ext
    change f 1 = f σ
    simp only [f]
    rw [hfix, inv_one, one_smul]
  have h2 := QuotientGroup.eq.1 (hinj h1)
  rw [inv_one, one_mul] at h2
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h2

end GlobalTheory.SplitCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeRelationOfLocallyUniformLimit
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped Topology ContDiff

namespace GlobalTheory.TypeSum.CoefClos

theorem integral_rder_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant] (c : ℝ → G) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ a b, c (a + b) = c a * c b) (h h' : G → ℂ) (hh : Continuous h) (hh' : Continuous h')
    (hs : HasCompactSupport h) (hs' : HasCompactSupport h')
    (hd : ∀ x, HasDerivAt (fun t => h (x * c t)) (h' x) 0) : ∫ x, h' x ∂μ = 0 := by
  have i0 : Integrable h μ := hh.integrable_of_hasCompactSupport hs
  have i1 : Integrable h' μ := hh'.integrable_of_hasCompactSupport hs'
  have pt : ∀ x, ∫ t in Set.Ioc (0 : ℝ) 1, h' (x * c t) = h (x * c 1) - h x := by
    intro x
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (f := fun t => h (x * c t))
      (f' := fun t => h' (x * c t)) (fun r _ => ?_)
      ((hh'.comp (continuous_const.mul hc)).intervalIntegrable 0 1)
    · simpa only [h0, mul_one] using this
    · have h1 : HasDerivAt (fun t => h (x * c r * c t)) (h' (x * c r)) (r - r) := by
        rw [sub_self]; exact hd _
      have h2 := h1.comp_sub_const r r
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [mul_assoc, ← hadd, add_sub_cancel]
  have hint : Integrable (Function.uncurry fun (x : G) (t : ℝ) => h' (x * c t))
      (μ.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hcont : Continuous (Function.uncurry fun (x : G) (t : ℝ) => h' (x * c t)) :=
      hh'.comp (continuous_fst.mul (hc.comp continuous_snd))
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => i1.comp_mul_right (c t), ?_⟩
    simp only [Function.uncurry_apply_pair, fun t => integral_mul_right_eq_self (μ := μ) (fun x => ‖h' x‖) (c t)]
    exact integrable_const _
  have sw := integral_integral_swap hint
  simp only [pt, fun t => integral_mul_right_eq_self (μ := μ) h' (c t)] at sw
  rw [integral_sub (i0.comp_mul_right _) i0, integral_mul_right_eq_self h, sub_self] at sw
  simpa using sw.symm

variable {n : ℕ} {ε : Fin n → Bool}

noncomputable def mkU (g : Mx n) (hg : g ∈ UJset ε) : UJ ε :=
  ⟨(isUnit_of_UJ hg).unit, show inUJ ε _ from hg⟩

theorem umat_mkU (g : Mx n) (hg : g ∈ UJset ε) : umat (mkU g hg) = g := rfl

theorem umat_emb (ε : Fin n → Bool) : Topology.IsClosedEmbedding (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1

theorem CSm.continuous {f : Mx n → ℂ} (h : CSm ε f) : Continuous fun g : UJ ε => f (umat g) := by
  obtain ⟨F, h1, -, h3⟩ := h
  exact ((h3 [] (by simp)).congr fun g hg => (h1 g hg).symm).comp_continuous (umat_emb ε).continuous fun g => g.2

theorem cSm_of_contDiff (φ : Mx n → ℂ) (hφ : ContDiff ℝ ∞ (fun y : Fin n → Fin n → ℂ => φ (Matrix.of y))) :
    CSm ε φ := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  have hφ' : ContDiff ℝ ∞ φ := by
    let L : Mx n →L[ℝ] (Fin n → Fin n → ℂ) :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
    exact hφ.comp L.contDiff
  let F : List (Mx n) → Mx n → ℂ := fun l => l.foldr (fun X f g => fderiv ℝ f g (g * X)) φ
  have hF : ∀ l, ContDiff ℝ ∞ (F l) := by
    intro l
    induction l with
    | nil => exact hφ'
    | cons X l ih =>
      exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_id.mul contDiff_const)
  refine ⟨F, fun _ _ => rfl, fun l _ X _ g _ => ?_, fun l _ => (hF l).continuous.continuousOn⟩
  have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).const_mul g
  have h2 : HasFDerivAt (F l) (fderiv ℝ (F l) g) (g * NormedSpace.exp ((0 : ℝ) • X)) := by
    rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact (((hF l).differentiable (by simp)) g).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h3
  exact h3

def IsTest (ε : Fin n → Bool) (φ : Mx n → ℂ) : Prop := CSm ε φ ∧ HasCompactSupport fun g : UJ ε => φ (umat g)

theorem IsTest.integrable {φ F : Mx n → ℂ} (hφ : IsTest ε φ) (hF : CSm ε F) :
    Integrable (fun g : UJ ε => φ (umat g) * F (umat g)) (muG ε) :=
  (hφ.1.continuous.mul hF.continuous).integrable_of_hasCompactSupport hφ.2.mul_right

theorem exists_adjoint_ltr (x : Ltr ε) {φ : Mx n → ℂ} (hφ : IsTest ε φ) : ∃ ψ, IsTest ε ψ ∧ ∀ F, CSm ε F →
    ∫ g : UJ ε, φ (umat g) * ltrF x F (umat g) ∂(muG ε) = ∫ g : UJ ε, ψ (umat g) * F (umat g) ∂(muG ε) := by
  haveI : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  rcases x with ⟨X, hX⟩ | ⟨k, hk⟩
  · let c : ℝ → UJ ε := fun t => mkU (NormedSpace.exp (t • X)) (exp_mem_UJ hX t)
    have hc : Continuous c := (umat_emb ε).isInducing.continuous_iff.2 (continuous_exp_smul X)
    have h0 : c 0 = 1 := (umat_emb ε).injective (by
      change NormedSpace.exp ((0 : ℝ) • X) = 1
      simp)
    have hadd : ∀ a b, c (a + b) = c a * c b := fun a b => (umat_emb ε).injective (exp_add_smul X a b)
    have ht : IsTest ε (rder X φ) := by
      refine ⟨hφ.1.rder hX, hφ.2.mono' fun g hg => ?_⟩
      by_contra hn
      apply hg
      have h1 := notMem_tsupport_iff_eventuallyEq.1 hn
      have h2 : Filter.Tendsto (fun t => g * c t) (𝓝 0) (𝓝 g) := by
        have h4 : Continuous fun t => g * c t := continuous_const.mul hc
        simpa only [h0, mul_one] using h4.tendsto 0
      have h3 : (fun t : ℝ => φ (umat g * NormedSpace.exp (t • X))) =ᶠ[𝓝 0] fun _ => 0 := h2.eventually h1
      show deriv _ 0 = 0
      rw [h3.deriv_eq, deriv_const]
    refine ⟨(-1 : ℂ) • rder X φ, ⟨ht.1.smul _, ht.2.mul_left⟩, fun F hF => ?_⟩
    have key := integral_rder_eq_zero (muG ε) c hc h0 hadd (fun g => φ (umat g) * F (umat g))
      (fun g => rder X φ (umat g) * F (umat g) + φ (umat g) * rder X F (umat g))
      (hφ.1.continuous.mul hF.continuous)
      ((ht.1.continuous.mul hF.continuous).add (hφ.1.continuous.mul (hF.rder hX).continuous))
      hφ.2.mul_right (ht.2.mul_right.add hφ.2.mul_right) (fun g => by
        have := (hφ.1.hasDerivAt hX g.2).fun_mul (hF.hasDerivAt hX g.2)
        simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at this
        exact this)
    rw [integral_add (ht.integrable hF) (hφ.integrable (hF.rder hX))] at key
    simp only [Pi.smul_apply, smul_eq_mul, neg_mul, one_mul, integral_neg]
    exact eq_neg_of_add_eq_zero_right key
  · have hkU := K_le_UJ hk
    have hk' : k⁻¹ ∈ Kset ε := by
      refine ((maximal_compact_facts n ε).2.2.2.2 _).2 ⟨inv_mem_UJ hkU, ?_⟩
      rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)]
      exact Unitary.star_mem hk.1
    refine ⟨fun g => φ (g * k⁻¹), ⟨hφ.1.rt hk', ?_⟩, fun F hF => ?_⟩
    · exact hφ.2.comp_homeomorph (Homeomorph.mulRight (mkU k⁻¹ (K_le_UJ hk')))
    · rw [← integral_mul_right_eq_self (fun g : UJ ε => φ (umat g * k⁻¹) * F (umat g)) (mkU k hkU)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      show φ (umat g) * F (umat g * k) = φ (umat g * k * k⁻¹) * F (umat g * k)
      rw [Matrix.mul_assoc, mul_inv_UJ hkU, Matrix.mul_one]

theorem exists_adjoint_word (u : List (Ltr ε)) : ∀ {φ : Mx n → ℂ}, IsTest ε φ → ∃ ψ, IsTest ε ψ ∧ ∀ F, CSm ε F →
    ∫ g : UJ ε, φ (umat g) * wordF u F (umat g) ∂(muG ε) = ∫ g : UJ ε, ψ (umat g) * F (umat g) ∂(muG ε) := by
  induction u with
  | nil => exact fun hφ => ⟨_, hφ, fun _ _ => rfl⟩
  | cons x u ih =>
    intro φ hφ
    obtain ⟨ψ, h1, h2⟩ := exists_adjoint_ltr x hφ
    obtain ⟨χ, h3, h4⟩ := ih h1
    exact ⟨χ, h3, fun F hF => (h2 _ (hF.wordF u)).trans (h4 F hF)⟩

theorem eq_zero_of_test (H : UJ ε → ℂ) (hH : Continuous H)
    (h : ∀ φ, IsTest ε φ → ∫ g : UJ ε, φ (umat g) * H g ∂(muG ε) = 0) (y : UJ ε) : H y = 0 := by
  by_contra hy
  have hc : Continuous fun g => (star (H y) * H g).re := by fun_prop
  have hpos : 0 < (star (H y) * H y).re := by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  have hU : {g | 0 < (star (H y) * H g).re} ∈ 𝓝 y := (isOpen_lt continuous_const hc).mem_nhds hpos
  have hemb : Topology.IsClosedEmbedding (fun g : UJ ε => (Matrix.of.symm (umat g) : Fin n → Fin n → ℂ)) :=
    umat_emb ε
  rw [hemb.isInducing.nhds_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.1 hU
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hV
  have hψ : Continuous fun g : UJ ε => φ (Matrix.of.symm (umat g)) := hφd.continuous.comp hemb.continuous
  have hψc : HasCompactSupport fun g : UJ ε => φ (Matrix.of.symm (umat g)) := hφc.comp_isClosedEmbedding hemb
  have ht : IsTest ε (fun g => (φ (Matrix.of.symm g) : ℂ)) :=
    ⟨cSm_of_contDiff _ (Complex.ofRealCLM.contDiff.comp hφd), hψc.comp_left Complex.ofReal_zero⟩
  have hi : Integrable (fun g : UJ ε => star (H y) * ((φ (Matrix.of.symm (umat g)) : ℂ) * H g)) (muG ε) :=
    ((ht.1.continuous.mul hH).integrable_of_hasCompactSupport ht.2.mul_right).const_mul _
  have h1 := integral_re hi
  rw [integral_const_mul, h _ ht] at h1
  have h2 : 0 < ∫ g : UJ ε, φ (Matrix.of.symm (umat g)) * (star (H y) * H g).re ∂(muG ε) := by
    refine (hψ.mul hc).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := y) hψc.mul_right (fun g => ?_) ?_
    · by_cases h0 : φ (Matrix.of.symm (umat g)) = 0
      · rw [h0, zero_mul]; exact le_rfl
      · exact mul_nonneg (hφr ⟨_, rfl⟩).1 (le_of_lt (hVU (hφs (subset_tsupport _ h0))))
    · rw [hφ1, one_mul]; exact hpos.ne'
  refine h2.ne' ?_
  simp only [mul_left_comm (star (H y)), RCLike.re_to_complex, Complex.re_ofReal_mul] at h1
  simpa using h1

end GlobalTheory.TypeSum.CoefClos
end

