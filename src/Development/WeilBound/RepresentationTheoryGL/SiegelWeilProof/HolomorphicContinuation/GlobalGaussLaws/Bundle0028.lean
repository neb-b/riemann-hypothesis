module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0027

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivStep
section
noncomputable section

open Topology Metric

namespace PositivityTheory.Rg.Sw.Glob

namespace DilDH

variable {E : Type} [MetricSpace E] [ProperSpace E]

theorem deriv_step {U : Set ℂ} (hU : IsOpen U) {g : ℂ → E → ℂ}
    (hc : ContinuousOn (fun p : ℂ × E => g p.1 p.2) (U ×ˢ Set.univ))
    (hd : ∀ u, DifferentiableOn ℂ (fun z => g z u) U) :
    ContinuousOn (fun p : ℂ × E => deriv (fun z => g z p.2) p.1) (U ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨z0, u0⟩ := p
  have hz0 : z0 ∈ U := hp.1
  have hopen : IsOpen (U ×ˢ (Set.univ : Set E)) := hU.prod isOpen_univ
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU z0 hz0
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall z0 (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hunif : ∀ᶠ u in 𝓝 u0, ∀ w ∈ closedBall z0 (2 * r), dist (g w u) (g w u0) < ε * r / 2 := by
    apply (isCompact_closedBall z0 (2 * r)).eventually_forall_of_forall_eventually
    intro w hw
    have hwU : w ∈ U := hK hw
    have hcont : ContinuousAt (fun p : ℂ × E => g p.1 p.2) (w, u0) :=
      hc.continuousAt (hopen.mem_nhds ⟨hwU, trivial⟩)
    have h1 : Filter.Tendsto (fun q : E × ℂ => g q.2 q.1) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp (continuous_swap.tendsto (u0, w))
    have h2 : Filter.Tendsto (fun q : E × ℂ => g q.2 u0) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp ((continuous_snd.prodMk continuous_const).tendsto (u0, w))
    have hε' : 0 < ε * r / 4 := by positivity
    filter_upwards [Metric.tendsto_nhds.1 h1 _ hε', Metric.tendsto_nhds.1 h2 _ hε'] with q hq1 hq2
    calc dist (g q.2 q.1) (g q.2 u0)
        ≤ dist (g q.2 q.1) (g w u0) + dist (g q.2 u0) (g w u0) := dist_triangle_right _ _ _
      _ < ε * r / 4 + ε * r / 4 := add_lt_add hq1 hq2
      _ = ε * r / 2 := by ring
  have hd0 : ContinuousAt (deriv fun z => g z u0) z0 :=
    ((hd u0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)
  have e1 := (continuous_fst.tendsto (z0, u0)).eventually
    (Metric.tendsto_nhds.1 hd0 (ε / 2) (by positivity))
  have e2 := (continuous_fst.tendsto (z0, u0)).eventually (Metric.ball_mem_nhds z0 hr0)
  have e3 := (continuous_snd.tendsto (z0, u0)).eventually hunif
  filter_upwards [e1, e2, e3] with q hq1 hq2 hq3
  obtain ⟨z, u⟩ := q
  simp only at hq1 hq2 hq3 ⊢
  have hzU : closedBall z r ⊆ closedBall z0 (2 * r) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    calc dist w z0 ≤ dist w z + dist z z0 := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hw hq2.le
      _ = 2 * r := by ring
  have hcu : deriv (fun z => g z u) z = Complex.cderiv r (fun z => g z u) z :=
    (Complex.cderiv_eq_deriv hU (hd u) hr0 (hzU.trans hK)).symm
  have hcu0 : deriv (fun z => g z u0) z = Complex.cderiv r (fun z => g z u0) z :=
    (Complex.cderiv_eq_deriv hU (hd u0) hr0 (hzU.trans hK)).symm
  have hsph : sphere z r ⊆ U := sphere_subset_closedBall.trans (hzU.trans hK)
  have hdiff : dist (Complex.cderiv r (fun z => g z u) z) (Complex.cderiv r (fun z => g z u0) z)
      < ε * r / 2 / r := by
    rw [dist_eq_norm]
    apply Complex.norm_cderiv_sub_lt hr0
    · intro w hw
      rw [← dist_eq_norm]
      exact hq3 w (hzU (sphere_subset_closedBall hw))
    · exact (hd u).continuousOn.mono hsph
    · exact (hd u0).continuousOn.mono hsph
  have hhalf : ε * r / 2 / r = ε / 2 := by field_simp
  rw [hhalf] at hdiff
  have hfirst : dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z) < ε / 2 := by
    rw [hcu, hcu0]
    exact hdiff
  calc dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z0)
      ≤ dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z)
        + dist (deriv (fun z => g z u0) z) (deriv (fun z => g z u0) z0) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hq1
    _ = ε := by ring

def scaleL (m n : ℕ) (s : ℝ) (X : Fin n → ℝ) : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun u := fun i j => u i j * (Real.exp (s * X j) : ℂ)
  invFun u := fun i j => u i j * (Real.exp (-(s * X j)) : ℂ)
  map_add' u v := by funext i j; simp [add_mul]
  map_smul' r u := by funext i j; simp [Complex.real_smul, mul_assoc]
  left_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]
  right_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]

end DilDH

theorem schScale : SchScale := by
  intro m n f s X a hf
  obtain ⟨S, hS⟩ := hf
  refine ⟨a • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (DilDH.scaleL m n s X).toContinuousLinearEquiv S, ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, smul_eq_mul, ← hS]
  rfl

theorem contDeriv : ContDeriv := by
  intro m n U hU f hc hd r
  induction r generalizing f with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ k ih =>
    have h1 := DilDH.deriv_step hU hc hd
    have h2 : ∀ u, DifferentiableOn ℂ (fun z => deriv (fun z => f z u) z) U :=
      fun u => (hd u).deriv hU
    have h3 := ih (fun z u => deriv (fun z => f z u) z) h1 h2
    simpa only [iteratedDeriv_succ'] using h3

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussM
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

private theorem fromBlocks_unitary_and_conj_JJ_eq {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Xᴴ * X + Yᴴ * Y = 1)
    (h2 : Xᴴ * Y = Yᴴ * X) :
    (fromBlocks X (-Y) Y X)ᴴ * fromBlocks X (-Y) Y X = 1 ∧
      (fromBlocks X (-Y) Y X)ᴴ * JJ n * fromBlocks X (-Y) Y X = JJ n := by
  constructor
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
    simp [h2]
    rw [h1, add_comm, h1, fromBlocks_one]
  · rw [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [h2]
    exact ⟨by rw [add_comm, h1], by rw [← neg_add, h1]⟩

private theorem exists_normalizing_factor_of_left_inverse {n : ℕ} (X Y A B : Matrix (Fin n) (Fin n) ℂ) (h : A * X + B * Y = 1) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, (X * R)ᴴ * (X * R) + (Y * R)ᴴ * (Y * R) = 1 := by
  classical
  set M := Xᴴ * X + Yᴴ * Y with hM
  have hpsd : M.PosSemidef :=
    (posSemidef_conjTranspose_mul_self X).add (posSemidef_conjTranspose_mul_self Y)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hq : star v ⬝ᵥ M *ᵥ v = 0 := by rw [hMv, dotProduct_zero]
    simp_rw [hM, add_mulVec, dotProduct_add, ← mulVec_mulVec, dotProduct_mulVec _ _ (X *ᵥ v),
      dotProduct_mulVec _ _ (Y *ᵥ v), vecMul_conjTranspose, star_star] at hq
    have h2 := (add_eq_zero_iff_of_nonneg (dotProduct_star_self_nonneg _)
      (dotProduct_star_self_nonneg _)).mp hq
    have hx := dotProduct_star_self_eq_zero.mp h2.1
    have hy := dotProduct_star_self_eq_zero.mp h2.2
    apply hv
    rw [← one_mulVec v, ← h, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hx, hy, mulVec_zero,
      mulVec_zero, add_zero]
  open scoped MatrixOrder in
  obtain ⟨S, hSS, hSa⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, S * S = M ∧ Sᴴ = S :=
    ⟨CFC.sqrt M, CFC.sqrt_mul_sqrt_self M hpsd.nonneg, (CFC.sqrt_nonneg M).isSelfAdjoint⟩
  have hS : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdet
    rw [← hSS, det_mul, h0, zero_mul]
  refine ⟨S⁻¹, ?_⟩
  simp only [conjTranspose_mul, conjTranspose_nonsing_inv, hSa]
  calc S⁻¹ * Xᴴ * (X * S⁻¹) + S⁻¹ * Yᴴ * (Y * S⁻¹) = S⁻¹ * (S * S) * S⁻¹ := by
        rw [hSS, hM]; noncomm_ring
    _ = 1 := by rw [← mul_assoc, nonsing_inv_mul _ hS, one_mul, mul_nonsing_inv _ hS]

private theorem exists_mul_lower_zero_and_inK_of_normalized (n : ℕ) (y : GR n) (X Y C D R : Matrix (Fin n) (Fin n) ℂ)
    (hb : C * X + D * Y = 0) (hR : (X * R)ᴴ * (X * R) + (Y * R)ᴴ * (Y * R) = 1)
    (hiso' : (X * R)ᴴ * (Y * R) = (Y * R)ᴴ * (X * R)) (hC : toBlocks₂₁ (mR y) = C)
    (hD : toBlocks₂₂ (mR y) = D) :
    ∃ (p : ↥(GR n)) (k : ↥(GR n)), y = p * k ∧ toBlocks₂₁ (mR p) = 0 ∧ InK (mR k) := by
  obtain ⟨hU, hS⟩ := fromBlocks_unitary_and_conj_JJ_eq (X * R) (Y * R) hR hiso'
  generalize hkv : fromBlocks (X * R) (-(Y * R)) (Y * R) (X * R) = kv at hU hS
  have hU' : kv * kvᴴ = 1 := mul_eq_one_comm.mp hU
  have hu : (⟨kv, kvᴴ, hU', hU⟩ : GL (Fin n ⊕ Fin n) ℂ) ∈ GR n := hS
  refine ⟨y * ⟨_, hu⟩, (⟨_, hu⟩ : GR n)⁻¹, (mul_inv_cancel_right y _).symm, ?_, ?_⟩
  · have hm : mR (y * ⟨_, hu⟩) = mR y * kv := rfl
    rw [hm, ← hkv, ← fromBlocks_toBlocks (mR y), fromBlocks_multiply, toBlocks_fromBlocks₂₁, hC, hD,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hb, Matrix.zero_mul]
  · refine ⟨(⟨_, hu⟩ : GR n)⁻¹.2, ?_⟩
    have hm : mR (⟨_, hu⟩ : GR n)⁻¹ = kvᴴ := rfl
    rw [hm, conjTranspose_conjTranspose]
    exact hU'

theorem iwaGR : IwaGR := by
  intro n y
  classical
  have hprod : mR y * mR y⁻¹ = 1 := by simp [mR]
  have hG : InG (mR y⁻¹) := (y⁻¹).2
  have hiso : (toBlocks₁₁ (mR y⁻¹))ᴴ * toBlocks₂₁ (mR y⁻¹) =
      (toBlocks₂₁ (mR y⁻¹))ᴴ * toBlocks₁₁ (mR y⁻¹) := by
    have h := congrArg toBlocks₁₁ hG
    rw [← fromBlocks_toBlocks (mR y⁻¹), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at h
    simp at h
    exact (neg_add_eq_zero.mp h).symm
  have hb := hprod
  rw [← fromBlocks_toBlocks (mR y), ← fromBlocks_toBlocks (mR y⁻¹), fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_inj] at hb
  obtain ⟨R, hR⟩ := exists_normalizing_factor_of_left_inverse _ _ _ _ hb.1
  have hiso' : (toBlocks₁₁ (mR y⁻¹) * R)ᴴ * (toBlocks₂₁ (mR y⁻¹) * R) =
      (toBlocks₂₁ (mR y⁻¹) * R)ᴴ * (toBlocks₁₁ (mR y⁻¹) * R) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ _ R, hiso, Matrix.mul_assoc]
  exact exists_mul_lower_zero_and_inK_of_normalized n y _ _ _ _ R hb.2.2.1 hR hiso' rfl rfl

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocE
section
noncomputable section

set_option linter.unusedSectionVars false

open scoped TensorProduct
open IsDedekindDomain NumberField GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sigI (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : intLoc F E v →+* intLoc F E v :=
  (sigR (Fv F v) σ).restrict (intLoc F E v) (intLoc F E v) (fun _ hx => sigR_mem_intLoc σ hx)

theorem sigI_coe (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : intLoc F E v) :
    ((sigI σ v z : intLoc F E v) : Fv F v ⊗[F] E) = sigR (Fv F v) σ z := rfl

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem sigI_sigI (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F)) (z : intLoc F E v) :
    sigI σ v (sigI σ v z) = z := Subtype.ext (sigR_sigR σ hσ (Fv F v) (z : Fv F v ⊗[F] E))

theorem fixed_eq_tmul (σ : E →ₐ[F] E) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F))
    (z : Fv F v ⊗[F] E) (hz : sigR (Fv F v) σ z = z) : ∃ a : Fv F v, z = a ⊗ₜ[F] (1 : E) := by
  let φ : E →ₗ[F] E := σ.toLinearMap - LinearMap.id
  have hex : Function.Exact (Algebra.linearMap F E) φ := by
    intro y
    constructor
    · intro hy
      have : σ y = y := by have := hy; simp only [φ, LinearMap.sub_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply,
        sub_eq_zero] at this; exact this
      obtain ⟨c, hc⟩ := (hfix y).1 this
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      simp [φ]
  have hex' := Module.Flat.lTensor_exact (Fv F v) hex
  have hφ : φ.lTensor (Fv F v) z = 0 := by
    have key : ∀ w : Fv F v ⊗[F] E, φ.lTensor (Fv F v) w = sigR (Fv F v) σ w - w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp [φ, sigR, TensorProduct.tmul_sub]
      | add y w hy hw => rw [map_add (f := _), hy, hw, map_add (f := _)]; abel
    rw [key, hz, sub_self]
  obtain ⟨w, hw⟩ := (hex' z).1 hφ
  refine ⟨TensorProduct.rid F (Fv F v) w, ?_⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [LinearMap.lTensor_tmul, Algebra.linearMap_apply, TensorProduct.rid_tmul]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add y w hy hw => rw [map_add (f := _), hy, hw, map_add (f := _), TensorProduct.add_tmul]

theorem mem_of_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (h : a ⊗ₜ[F] (1 : E) ∈ intLoc F E v) :
    a ∈ v.adicCompletionIntegers F := by
  have h1 := absFin_le_one_of_mem_intLoc h
  rw [absFin_tmul_one] at h1
  exact (Valued.toNormedField.norm_le_one_iff).1 (by exact_mod_cast h1)

theorem tmul_one_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (h : a ∈ v.adicCompletionIntegers F) :
    a ⊗ₜ[F] (1 : E) ∈ intLoc F E v := by
  simpa using tmul_mem_intLoc (E := E) h (1 : 𝓞 E)

theorem nontrivial_intLoc (v : HeightOneSpectrum (𝓞 F)) : Nontrivial (intLoc F E v) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : ((0 : intLoc F E v) : Fv F v ⊗[F] E) = ((1 : intLoc F E v) : Fv F v ⊗[F] E) := congrArg Subtype.val h
  have := congrArg (absFin F v) h'
  rw [ZeroMemClass.coe_zero, OneMemClass.coe_one, absFin_zero, absFin_one] at this
  exact zero_ne_one this

theorem orbit_abs {R : Type} [CommRing R] (s : R →+* R) (hss : ∀ z, s (s z) = z)
    (hloc : ∀ z, s z = z → IsUnit z ∨ IsUnit (1 - z)) (𝔪 𝔫 : Ideal R) (h𝔪 : 𝔪.IsMaximal) (h𝔫 : 𝔫.IsMaximal) :
    𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap s := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hn1, hn2⟩ := hne
  have hsurj : Function.Surjective s := fun y => ⟨s y, hss y⟩
  have hcc : ∀ I : Ideal R, (I.comap s).comap s = I := by
    intro I; ext z; rw [Ideal.mem_comap, Ideal.mem_comap, hss]
  have hm' : (𝔪.comap s).IsMaximal := Ideal.comap_isMaximal_of_surjective s hsurj
  have hn' : (𝔫.comap s).IsMaximal := Ideal.comap_isMaximal_of_surjective s hsurj
  have hn3 : 𝔫.comap s ≠ 𝔪 := by
    intro h; apply hn2; rw [← h, hcc]
  have hn4 : 𝔫.comap s ≠ 𝔪.comap s := by
    intro h; apply hn1; rw [← hcc 𝔫, h, hcc]
  have c1 : 𝔪 ⊔ 𝔫 = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 h𝔫 (Ne.symm hn1)
  have c2 : 𝔪 ⊔ 𝔫.comap s = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 hn' (Ne.symm hn3)
  have c3 : 𝔪.comap s ⊔ 𝔫 = ⊤ := Ideal.IsMaximal.coprime_of_ne hm' h𝔫 (Ne.symm hn2)
  have c4 : 𝔪.comap s ⊔ 𝔫.comap s = ⊤ := Ideal.IsMaximal.coprime_of_ne hm' hn' (Ne.symm hn4)
  have d1 : 𝔪 ⊔ 𝔫 * 𝔫.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left c1).trans c2
  have d2 : 𝔪.comap s ⊔ 𝔫 * 𝔫.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left c3).trans c4
  have e1 : 𝔫 * 𝔫.comap s ⊔ 𝔪 = ⊤ := by rw [sup_comm]; exact d1
  have e2 : 𝔫 * 𝔫.comap s ⊔ 𝔪.comap s = ⊤ := by rw [sup_comm]; exact d2
  have d3 : 𝔫 * 𝔫.comap s ⊔ 𝔪 * 𝔪.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left e1).trans e2
  have h1 : (1 : R) ∈ 𝔫 * 𝔫.comap s ⊔ 𝔪 * 𝔪.comap s := by rw [d3]; exact Submodule.mem_top
  obtain ⟨y, hy, x, hx, hxy⟩ := Submodule.mem_sup.1 h1
  have hxm : x ∈ 𝔪 := (Ideal.mul_le_left : 𝔪 * 𝔪.comap s ≤ 𝔪) hx
  have hyn : y ∈ 𝔫 := (Ideal.mul_le_left : 𝔫 * 𝔫.comap s ≤ 𝔫) hy
  have hyn'' : y ∈ 𝔫.comap s := (Ideal.mul_le_right : 𝔫 * 𝔫.comap s ≤ 𝔫.comap s) hy
  have hyn' : s y ∈ 𝔫 := Ideal.mem_comap.1 hyn''
  have hzm : x * s x ∈ 𝔪 := Ideal.mul_mem_right _ _ hxm
  have hfz : s (x * s x) = x * s x := by rw [map_mul, hss, mul_comm]
  have h1z : 1 - x * s x ∈ 𝔫 := by
    have hx' : x = 1 - y := by rw [← hxy]; ring
    have e : 1 - x * s x = y + s y - y * s y := by rw [hx', map_sub, map_one]; ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hyn hyn') (Ideal.mul_mem_right _ _ hyn)
  rcases hloc _ hfz with hu | hu
  · exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ hzm hu)
  · exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ h1z hu)

theorem isUnit_tmul (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletionIntegers F)ˣ) :
    IsUnit (⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ :
      intLoc F E v) := by
  refine ⟨⟨_, ⟨((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) ⊗ₜ[F] (1 : E),
    tmul_one_mem v _ (u⁻¹ : (v.adicCompletionIntegers F)ˣ).1.2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · show ((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) * (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul, Units.mul_inv]; rfl
  · show (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) *
      ((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul, Units.inv_mul]; rfl

theorem fixed_local (σ : E →ₐ[F] E) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F))
    (z : intLoc F E v) (hz : sigI σ v z = z) : IsUnit z ∨ IsUnit (1 - z) := by
  obtain ⟨a, ha⟩ := fixed_eq_tmul σ hfix v (z : Fv F v ⊗[F] E) (by rw [← sigI_coe]; exact congrArg Subtype.val hz)
  have haO : a ∈ v.adicCompletionIntegers F := mem_of_tmul_mem v a (ha ▸ z.2)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, haO⟩ : v.adicCompletionIntegers F) with hu | hu
  · left
    obtain ⟨u, hu⟩ := hu
    have e : z = ⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ :=
      Subtype.ext (by rw [ha, hu])
    rw [e]; exact isUnit_tmul v u
  · right
    obtain ⟨u, hu⟩ := hu
    have e : 1 - z = ⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ := by
      apply Subtype.ext
      rw [hu]
      show (1 : Fv F v ⊗[F] E) - (z : Fv F v ⊗[F] E) = (1 - a) ⊗ₜ[F] (1 : E)
      rw [ha, TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
    rw [e]; exact isUnit_tmul v u

theorem orbit (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ 𝔪 : Ideal (intLoc F E v), 𝔪.IsMaximal ∧ ∀ 𝔫 : Ideal (intLoc F E v), 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap (sigI σ v) := by
  have := nontrivial_intLoc (E := E) v
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (intLoc F E v)
  exact ⟨𝔪, h𝔪, fun 𝔫 h𝔫 => orbit_abs (sigI σ v) (sigI_sigI σ hσ v) (fixed_local σ hfix v) 𝔪 𝔫 h𝔪 h𝔫⟩

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VacKOf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF
  PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH PositivityTheory.Rg.Sw.Glob.VacI PositivityTheory.Rg.Sw.Glob.VacJ PositivityTheory.Rg.Sw.Glob.VacK

private theorem cnt_true_add_cnt_false {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem vacK_of : GZSch → LawN → LawNbar → LocMul → LNe → VacK := by
  intro hGZ hN hNb hLM hLNe
  unfold PositivityTheory.Rg.Sw.Glob.VacK
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL e hlev k hk
  have hl0 : l τ ≠ 0 := hLNe D ψ θ l hC.hψ hC.hθ hC.hl τ
  have hc0 : 0 < cLoc l τ := VacF.cpos hl0
  have hSch : ∀ K : ℂ, IsSch (DG (m := V.rank) (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) :=
    fun K => VacE.isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) hc0 VacF.tabs K
  obtain ⟨u, u', φ, hu, hu', hφ, hkm⟩ := VacG.kak (mR k) hk
  have hdu : IsUnit u.det := Matrix.isUnit_det_of_left_inverse hu
  have hdu' : IsUnit u'.det := Matrix.isUnit_det_of_left_inverse hu'
  have hk_eq : k = VacB.mkG (mM u) (VacB.inG_mM u hdu) * VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1 *
      VacB.mkG (mM u') (VacB.inG_mM u' hdu') := by
    apply Subtype.ext
    apply Units.ext
    change mR k = mR (VacB.mkG (mM u) (VacB.inG_mM u hdu)) * mR (VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1) *
      mR (VacB.mkG (mM u') (VacB.inG_mM u' hdu'))
    rw [VacB.mR_mkG, VacB.mR_mkG, VacB.mR_mkG]
    exact hkm
  have hLM' := hLM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC L hL
  have h1 : L (VacB.mkG (mM u') (VacB.inG_mM u' hdu')) (DG 1 (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    rw [hlev _ u' hdu' (VacB.mR_mkG _ _) _ (hSch 1)]
    exact VacH.levF_unitary e u' hu' 1 _
  have h2 := VacJ.rot_gen hC hl0 hN hNb hLM hGZ L hL e hlev φ hφ
    (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)))
  have h3 : ∀ K : ℂ, L (VacB.mkG (mM u) (VacB.inG_mM u hdu)) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    intro K
    rw [hlev _ u hdu (VacB.mR_mkG _ _) _ (hSch K)]
    exact VacH.levF_unitary e u hu K _
  have hLk : L k (DG 1 (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)) *
        (∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (VacE.rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ))) *
        (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    rw [hk_eq, hLM' (VacB.mkG (mM u) (VacB.inG_mM u hdu) * VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1)
      (VacB.mkG (mM u') (VacB.inG_mM u' hdu')) _ (hSch 1), h1,
      hLM' (VacB.mkG (mM u) (VacB.inG_mM u hdu)) (VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1) _ (hSch _), h2, h3]
  have hsu : star u.det = u.det⁻¹ := by
    have h := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hsu' : star u'.det = u'.det⁻¹ := by
    have h := congrArg Matrix.det hu'
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hm : (V.rank : ℤ) = ((cnt (epsT (tLoc l τ) ε) true + cnt (epsT (tLoc l τ) ε) false : ℕ) : ℤ) := by
    rw [cnt_true_add_cnt_false]
  have hX : (∏ j, Complex.exp (Complex.I * (φ j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Complex.exp_ne_zero _
  have hXinv : ∏ j, Complex.exp (-(Complex.I * (φ j : ℂ))) = (∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹ := by
    simp only [Complex.exp_neg, Finset.prod_inv_distrib]
  have hK : 1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)) *
      (∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (VacE.rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ))) *
      (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e)) =
      jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) k (Complex.I • 1) := by
    rw [VacI.jF_kak e _ _ k u u' φ hu hu' hφ hkm, VacK.prodF, hsu, hsu', hm, hXinv]
    exact VacK.alg _ _ _ hdu.ne_zero hdu'.ne_zero hX e _ _
  rw [VacC.vac_eq, hLk]
  funext v
  rw [VacC.dg_const, VacC.dg_const, hK]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

