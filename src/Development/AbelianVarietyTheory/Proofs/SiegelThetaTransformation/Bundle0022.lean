module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaEisensteinConvergeBounded
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisAutomorphyLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicit
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EmbeddingCompatibleWithWeilAndDenominator

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesOfSchwartzIsHolomorphic
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.EisHeat

section Lines

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]


omit [FiniteDimensional ℂ X] in
theorem deriv_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : X → V} {p : X}
    (hf : DifferentiableAt ℂ f p) (v : X) :
    HasDerivAt (fun s : ℂ => f (p + s • v)) (fderiv ℂ f p v) 0 := by
  have h : HasDerivAt (fun s : ℂ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 h (by simp)

theorem deriv_two {f : X → ℂ} {U : Set X} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {p : X}
    (hp : p ∈ U) (v w : X) :
    deriv (fun s : ℂ => deriv (fun t : ℂ => f (p + s • v + t • w)) 0) 0 =
      fderiv ℂ (fderiv ℂ f) p v w := by
  have h1 : DifferentiableAt ℂ (fderiv ℂ f) p :=
    (SCV.analyticAt_of_differentiableOn hf (hU.mem_nhds hp)).fderiv.differentiableAt
  have h2 := (deriv_line h1 v).clm_apply (hasDerivAt_const (0 : ℂ) w)
  have h3 : ∀ᶠ s : ℂ in 𝓝 0, p + s • v ∈ U := by
    have : Continuous fun s : ℂ => p + s • v := by fun_prop
    exact this.continuousAt.eventually_mem (by simpa using hU.mem_nhds hp)
  have h4 : (fun s : ℂ => deriv (fun t : ℂ => f (p + s • v + t • w)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℂ f (p + s • v) w :=
    h3.mono fun s hs => (deriv_line (hf.differentiableAt (hU.mem_nhds hs)) w).deriv
  rw [h4.deriv_eq, h2.deriv]
  simp

end Lines

variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem imH_isHermitian (Z : Matrix (Fin N) (Fin N) ℂ) : (imH Z).IsHermitian := by
  unfold imH IsHermitian
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← neg_sub Z, smul_neg,
    ← neg_smul]
  congr 1
  simp

theorem eventually_posDef (δ : ℝ) {p : CF Ψ N N × CF Ψ n N × CF Ψ n N}
    (hp : ∀ τ, (imH (p.1 τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef) :
    ∀ᶠ q : CF Ψ N N × CF Ψ n N × CF Ψ n N in 𝓝 p,
      ∀ τ, (imH (q.1 τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef := by
  refine Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
    (fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
      imH (q.1 τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) (fun i j => ?_) (fun q => ?_) p (hp τ)
  · change Continuous fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
      (2 * I)⁻¹ * (q.1 τ i j - star (q.1 τ j i)) - ((δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) i j
    fun_prop
  · refine (imH_isHermitian _).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one]
    simp

theorem isOpen_dom : IsOpen {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := by
  refine isOpen_iff_mem_nhds.2 fun p hp => ?_
  have := eventually_posDef Ψ 0 (p := p) (fun τ => by simpa using hp τ)
  filter_upwards [this] with q hq τ
  simpa using hq τ


open Classical in
noncomputable def dir {m : ℕ} (τ : Ψ) (k : Fin m) (a : Fin N) : CF Ψ m N :=
  fun σ i j => if σ = τ ∧ k = i ∧ a = j then 1 else 0


open Classical in
theorem heat_iff {D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : DifferentiableOn ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
      {p | (p.1 : CM Ψ N N) ∈ Hn Ψ N}) :
    IsHeat Ψ D ↔ ∀ Z z z', (Z : CM Ψ N N) ∈ Hn Ψ N → ∀ (τ : Ψ) (a b : Fin N),
      2 * Real.pi * I * fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
        (Z, z, z') (dir Ψ τ a b, 0, 0) =
      ∑ k, fderiv ℂ (fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2))
        (Z, z, z') (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b) := by
  have key : ∀ {m : ℕ} (x : CF Ψ m N) (τ : Ψ) (k : Fin m) (a : Fin N) (s : ℂ),
      x + s • dir Ψ τ k a =
        (fun σ => Matrix.of (x σ) + if σ = τ then Matrix.single k a s else 0 : CM Ψ m N) := by
    intro m x τ k a s
    funext σ i j
    change x σ i j + s * (if σ = τ ∧ k = i ∧ a = j then 1 else 0) =
      x σ i j + (if σ = τ then Matrix.single k a s else 0 : Matrix (Fin m) (Fin N) ℂ) i j
    by_cases h : σ = τ
    · simp [h, Matrix.single]
    · simp [h]
  have main : ∀ (Z : CF Ψ N N) (z z' : CF Ψ n N), (Z : CM Ψ N N) ∈ Hn Ψ N →
      ∀ (τ : Ψ) (a b : Fin N),
      (2 * Real.pi * I * fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
        (Z, z, z') (dir Ψ τ a b, 0, 0) =
      ∑ k, fderiv ℂ (fderiv ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2))
        (Z, z, z') (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b)) ↔
      2 * Real.pi * I * deriv (fun s : ℂ =>
        D (fun σ => Matrix.of (Z σ) + if σ = τ then Matrix.single a b s else 0) z z') 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ =>
        D Z (fun σ => Matrix.of (z σ) + if σ = τ then Matrix.single k a s else 0)
          (fun σ => Matrix.of (z' σ) + if σ = τ then Matrix.single k b t else 0)) 0) 0 := by
    intro Z z z' hZ τ a b
    have hp : ((Z, z, z') : CF Ψ N N × CF Ψ n N × CF Ψ n N) ∈
      {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := hZ
    rw [← (deriv_line (hD.differentiableAt ((isOpen_dom Ψ).mem_nhds hp)) _).deriv]
    simp only [← deriv_two (isOpen_dom Ψ) hD hp]
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
    simp only [key]
  exact ⟨fun h Z z z' hZ τ a b => (main Z z z' hZ τ a b).2 (h.2 Z hZ z z' τ a b),
    fun h => ⟨hD, fun Z hZ z z' τ a b => (main Z z z' hZ τ a b).1 (h Z z z' hZ τ a b)⟩⟩

theorem isHeat_tsum {ι : Type} {D : ι → CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : ∀ i, IsHeat Ψ (D i))
    (hle : ∀ p : CF Ψ N N × CF Ψ n N × CF Ψ n N, (p.1 : CM Ψ N N) ∈ Hn Ψ N → ∃ t ∈ 𝓝 p,
      ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ q ∈ t, ‖D i q.1 q.2.1 q.2.2‖ ≤ u i) :
    IsHeat Ψ fun Z z z' => ∑' i, D i Z z z' := by
  have h0 := SCV.hasSumLocallyUniformlyOn_of_locally_normal
    (F := fun i (q : CF Ψ N N × CF Ψ n N × CF Ψ n N) => D i q.1 q.2.1 q.2.2)
    (U := {p | (p.1 : CM Ψ N N) ∈ Hn Ψ N}) hle
  have hd := SCV.differentiableOn_of_hasSumLocallyUniformlyOn (isOpen_dom Ψ) h0 fun i => (hD i).1
  have h1 := SCV.hasSumLocallyUniformlyOn_fderiv (isOpen_dom Ψ) h0 fun i => (hD i).1
  have h2 := SCV.hasSumLocallyUniformlyOn_fderiv (isOpen_dom Ψ) h1 fun i p hp =>
    (SCV.analyticAt_of_differentiableOn (hD i).1
      ((isOpen_dom Ψ).mem_nhds hp)).fderiv.differentiableAt.differentiableWithinAt
  refine (heat_iff Ψ hd).2 fun Z z z' hZ τ a b => ?_
  have hp : ((Z, z, z') : CF Ψ N N × CF Ψ n N × CF Ψ n N) ∈
    {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := hZ
  have s1 := fun v => (h1.hasSum hp).mapL (ContinuousLinearMap.apply ℂ ℂ v)
  have s2 := fun v w => ((h2.hasSum hp).mapL (ContinuousLinearMap.apply ℂ _ v)).mapL
    (ContinuousLinearMap.apply ℂ ℂ w)
  simp only [ContinuousLinearMap.apply_apply] at s1 s2
  refine ((s1 _).mul_left _).unique ?_
  simp only [fun i => (heat_iff Ψ (hD i).1).1 (hD i) Z z z' hZ τ a b]
  exact hasSum_sum fun k _ => s2 _ _

theorem isHeat_const_mul {D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D) (c : ℂ) :
    IsHeat Ψ fun Z z z' => c * D Z z z' := by
  refine ⟨hD.1.const_mul c, fun Z hZ z z' τ a b => ?_⟩
  simp only [deriv_const_mul_field', deriv_const_mul_field]
  rw [← Finset.mul_sum, ← hD.2 Z hZ z z' τ a b]
  ring

variable [NumberField E] [IsCMField E]

theorem hFac_inv_bound (n N : ℕ) {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ K : ℝ, ∀ γ ∈ UU E N, ∀ Z ∈ Hn Ψ N, Z ∈ HnGe Ψ N δ → ∀ z z' : CM Ψ n N,
      (∀ τ a b, ‖Z τ a b‖ ≤ B) → (∀ τ a b, ‖z τ a b‖ ≤ B) → (∀ τ a b, ‖z' τ a b‖ ≤ B) →
      ‖(hFac Ψ γ Z z z')⁻¹‖ ≤
        K * ‖(hFac Ψ γ (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) (0 : CM Ψ n N) 0)⁻¹‖ := by
  obtain ⟨c, hc, hcmp⟩ := norm_det_denom_compare N δ (B + B) hδ
  refine ⟨∏ _τ : Ψ, (c ^ n)⁻¹ *
    Real.exp (‖2 * (π : ℂ) * I‖ * ∑ _k : Fin n, ∑ _a : Fin N, B * ∑ _b : Fin N, δ⁻¹ * B),
    fun γ hγ Z hZ hZ' z z' hB hz hz' => ?_⟩
  rw [EisTrans.hFac_zero, hFac, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, norm_prod,
    norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have hr := (HermComp.row_rel _ (HAct.map_mem τ.1 hγ)).2
  have hd := (((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
  have hd0 := (((unitary_act_halfSpace E Ψ N γ hγ).2 _ (Base.I_mem_Hn Ψ)).1 τ).1
  rw [mul_inv, norm_mul, mul_right_comm (c ^ n)⁻¹]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
  · unfold hDen at hd hd0 ⊢
    change γ.toBlocks₂₂.map τ.1 * (γ.toBlocks₂₁.map τ.1)ᴴ =
      γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ at hr
    generalize γ.toBlocks₂₁.map τ.1 = C at *
    generalize γ.toBlocks₂₂.map τ.1 = D at *
    have h1 : (C * Dᴴ).IsHermitian := by
      unfold IsHermitian
      rw [conjTranspose_mul, conjTranspose_conjTranspose, hr]
    have h2 : (C * Cᴴ + D * Dᴴ).PosDef := by
      have e : C * Cᴴ + D * Dᴴ = (C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D) *
          (C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D)ᴴ := by
        simp only [Matrix.mul_smul, Matrix.mul_one, conjTranspose_add, conjTranspose_smul,
          Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, hr, Complex.star_def, Complex.conj_I,
          smul_add, smul_smul, neg_smul, Matrix.mul_neg, smul_neg, I_mul_I, neg_neg, one_smul]
        abel
      rw [e]
      exact PosDef.mul_conjTranspose_self _
        (Matrix.vecMul_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (Ne.isUnit hd0)))
    have h3 := (hcmp C D (Z τ) h1 h2 (hZ' τ) fun a b => (norm_add_le _ _).trans
      (add_le_add (hB τ a b) (by simpa using hB τ b a))).1
    rw [norm_inv, norm_inv, norm_pow, norm_pow, ← mul_inv, ← mul_pow]
    have h4 := norm_pos_iff.2 hd0
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h3 n)
  · rw [← Complex.exp_neg]
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_neg, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hb := EisTrans.entry_bound hδ hr hd (hZ' τ)
    refine norm_sum_le_of_le _ fun k _ => norm_sum_le_of_le _ fun a _ => ?_
    rw [norm_mul]
    refine mul_le_mul (hz' τ k a) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hz' τ k a))
    rw [Matrix.mulVec, dotProduct]
    refine norm_sum_le_of_le _ fun b _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hb a b) (hz τ k b) (norm_nonneg _) (by positivity)

end GlobalTheory.SW.EisHeat


open GlobalTheory.SW.EisHeat in
theorem GlobalTheory.SW.isHeat_eis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsHeat Ψ (eis Ψ φ) := by
  rintro E _ _ _ Ψ hΨ n N hn hN φ ⟨R, hR, hφ⟩
  refine isHeat_tsum Ψ (D := fun U : Lag E N => eisTerm Ψ U.2.choose φ)
    (fun U => isHeat_const_mul Ψ (isHeat_hFac_inv E Ψ n N _ U.2.choose_spec.1) _) fun p hp => ?_
  obtain ⟨B, hB⟩ := (GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds E _ _ R φ hR hφ).2.2.2.2.1
  obtain ⟨δ₀, hδ₀, hI⟩ := EisTrans.exists_mem_HnGe Ψ (Base.I_mem_Hn (N := N) Ψ)
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.SW.theta_eis_bounded E Ψ hΨ n N hn hN R δ₀ hR hδ₀
  have hs := (hC φ hφ B hB _ hI).1
  obtain ⟨δ, hδ, hp'⟩ := EisTrans.exists_mem_HnGe Ψ hp
  have h1 := eventually_posDef Ψ (δ / 2) (p := p) fun τ => by
    have h : (((δ / 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
      PosDef.one.smul (by exact_mod_cast half_pos hδ)
    convert PosDef.posSemidef_add (hp' τ) h using 1
    rw [sub_add, ← sub_smul]
    congr 2
    push_cast
    ring
  obtain ⟨K, hK⟩ := hFac_inv_bound Ψ n N (half_pos hδ) (‖p‖ + 1)
  have h2 : ∀ᶠ q : CF Ψ N N × CF Ψ n N × CF Ψ n N in 𝓝 p, ‖q‖ < ‖p‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt_const (lt_add_one _)
  refine ⟨_, (h1.and h2).and ((isOpen_dom Ψ).mem_nhds hp), _, hs.mul_left K, fun U q hq => ?_⟩
  obtain ⟨⟨q1, q2⟩, q3⟩ := hq
  have e : ∀ {m : ℕ} (x : CF Ψ m N), ‖x‖ ≤ ‖q‖ → ∀ τ a b, ‖x τ a b‖ ≤ ‖p‖ + 1 :=
    fun x hx τ a b => (norm_le_pi_norm _ b).trans <| (norm_le_pi_norm _ a).trans <|
      (norm_le_pi_norm x τ).trans <| hx.trans q2.le
  simp only [eisTerm]
  rw [norm_mul, norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hK _ U.2.choose_spec.1 _ q3 (fun τ => (q1 τ).posSemidef) _ _
    (e _ (norm_fst_le q)) (e _ ((norm_fst_le q.2).trans (norm_snd_le q)))
    (e _ ((norm_snd_le q.2).trans (norm_snd_le q)))) (norm_nonneg _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelOperatorHermitianEisensteinSeries
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.EisSiegel

variable {N : ℕ}

theorem det_growth (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : D * Cᴴ = C * Dᴴ)
    (hQ : (C * Z + D).det ≠ 0) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ (C *ᵥ v ≠ 0 → 0 < c) ∧ ∀ t : ℝ, ‖(C * Z + D).det‖ * (1 + t * c) ≤
      ‖(C * (Z + (I * t) • vecMulVec v (star v)) + D).det‖ := by
  have hH : (C * Dᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h]
  set Q := C * Z + D with hQdef
  have hU : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
  set x : Fin N → ℂ := (Q⁻¹)ᴴ *ᵥ v with hx
  have hxv : Qᴴ *ᵥ x = v := by
    rw [hx, mulVec_mulVec, ← conjTranspose_mul, nonsing_inv_mul _ hU, conjTranspose_one, one_mulVec]
  have hsx : star x = star v ᵥ* Q⁻¹ := by
    rw [hx, star_mulVec, conjTranspose_conjTranspose]
  have hs := im_quad_denom C D Z hH x
  rw [← hQdef, hxv] at hs
  refine ⟨(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re,
    (Complex.nonneg_iff.1 (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ x))).1,
    fun hv => (Complex.pos_iff.1 (hZ.dotProduct_mulVec_pos fun h0 => hv ?_)).1, fun t => ?_⟩
  · rw [← hxv, hQdef, conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec x Zᴴ, h0,
      mulVec_zero, zero_add, mulVec_mulVec, ← h, ← mulVec_mulVec, h0, mulVec_zero]
  · have e : C * (Z + (I * t) • vecMulVec v (star v)) + D =
        Q * (1 + vecMulVec ((I * t) • (Q⁻¹ *ᵥ (C *ᵥ v))) (star v)) := by
      rw [Matrix.mul_add Q, Matrix.mul_one, mul_vecMulVec, mulVec_smul, mulVec_mulVec,
        mul_nonsing_inv _ hU, one_mulVec, Matrix.mul_add, ← smul_vecMulVec, mul_vecMulVec,
        mulVec_smul, hQdef]
      abel
    rw [e, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, norm_mul,
      dotProduct_smul, dotProduct_mulVec (star v), ← hsx]
    generalize (star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re = c at hs
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) (Complex.re_le_norm _)) (norm_nonneg _)
    simp only [smul_eq_mul, add_re, one_re, mul_re, mul_im, I_re, I_im, zero_mul, one_mul,
      ofReal_re, ofReal_im, hs]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}


omit [NumberField E] [IsCMField E] in
theorem pushZ_mem {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ} (ht : 0 ≤ t) :
    pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have hP : ((t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a))).PosSemidef :=
    (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht)
  have := imH_add_I_smul (Z τ) _ hP.1
  rw [smul_smul] at this
  exact this ▸ (hZ τ).add_posSemidef hP

omit [NumberField E] [IsCMField E] in
theorem dropZ_pushZ (Z : CM Ψ (N + 1) (N + 1)) (t : ℝ) :
    dropZ Ψ (pushZ Ψ Z (Pi.single 0 1) t) = dropZ Ψ Z := by
  funext τ
  ext a b
  simp [dropZ, pushZ, vecMulVec_apply]

theorem hDen_growth {γ : M2 E N} (hγ : γ ∈ UU E N) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N)
    (v : Fin N → E) (τ : Ψ) :
    (hDen Ψ γ Z τ).det ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ (γ.toBlocks₂₁ *ᵥ v ≠ 0 → 0 < c) ∧ ∀ t : ℝ,
      ‖(hDen Ψ γ Z τ).det‖ * (1 + t * c) ≤ ‖(hDen Ψ γ (pushZ Ψ Z v t) τ).det‖ := by
  have h0 := (((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
  obtain ⟨c, h1, h2, h3⟩ := det_growth _ _ _ (HermComp.row_rel _ (HAct.map_mem τ.1 hγ)).2 h0
    (hZ τ) (fun a => τ.1 (v a))
  refine ⟨h0, c, h1, fun hv => h2 fun h => hv ?_, h3⟩
  funext a
  apply τ.1.injective
  rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
  exact congrFun h a

theorem norm_term_le {γ : M2 E N} (hγ : γ ∈ UU E N) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N)
    (v : Fin N → E) (φ : Matrix (Fin n) (Fin N) E → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖eisTerm Ψ γ φ (pushZ Ψ Z v t) 0 0‖ ≤ ‖eisTerm Ψ γ φ Z 0 0‖ := by
  simp only [eisTerm, EisTrans.hFac_zero, norm_mul, norm_inv, norm_prod, norm_pow]
  refine mul_le_mul_of_nonneg_left (inv_anti₀ ?_ ?_) (norm_nonneg _)
  · exact Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.2 (hDen_growth Ψ hγ hZ v τ).1) _
  · refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun τ _ => ?_
    obtain ⟨-, c, h1, -, h3⟩ := hDen_growth Ψ hγ hZ v τ
    refine pow_le_pow_left₀ (norm_nonneg _) (le_trans ?_ (h3 t)) _
    exact le_mul_of_one_le_right (norm_nonneg _) (by nlinarith [mul_nonneg ht h1])

theorem term_tendsto_zero (hΨ : IsType Ψ) (hn : n ≠ 0) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) (hv : γ.toBlocks₂₁ *ᵥ v ≠ 0)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    Tendsto (fun t : ℝ => eisTerm Ψ γ φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  have hne : Nonempty Ψ := by
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : σ ∈ Ψ
    · exact ⟨⟨σ, h⟩⟩
    · exact ⟨⟨_, not_not.1 ((hΨ σ).not.1 h)⟩⟩
  simp only [eisTerm, EisTrans.hFac_zero, ← Finset.prod_inv_distrib]
  have h1 : ∀ τ : Ψ, Tendsto (fun t : ℝ => ((hDen Ψ γ (pushZ Ψ Z v t) τ).det ^ n)⁻¹) atTop
      (𝓝 0) := by
    intro τ
    obtain ⟨h0, c, -, h2, h3⟩ := hDen_growth Ψ hγ hZ v τ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv, norm_pow]
    refine Tendsto.inv_tendsto_atTop ((tendsto_pow_atTop hn).comp (tendsto_atTop_mono h3 ?_))
    exact Tendsto.const_mul_atTop (norm_pos_iff.2 h0)
      (tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const (h2 hv)))
  have h2 := (tendsto_finsetProd Finset.univ fun τ _ => h1 τ).const_mul (weil Ψ γ φ 0)
  rwa [Finset.prod_const, zero_pow (Finset.card_univ.trans_ne Fintype.card_ne_zero), mul_zero] at h2

end GlobalTheory.SW.EisSiegel


open GlobalTheory.SW.EisSiegel in
theorem GlobalTheory.SW.eis_siegel_operator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → ∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => eis Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 (eis Ψ (dropF φ) (dropZ Ψ Z) 0 0)) := by
  intro E _ _ _ Ψ hΨ n N hn hN φ hφ Z hZ
  obtain ⟨ι, hι, hsurj⟩ := _root_.GlobalTheory.SW.Emb.exists_embedding E Ψ hΨ n N hn
  let j : Lag E N → Lag E (N + 1) := fun V =>
    ⟨botSpan (ι V.2.choose), _, (hι _ V.2.choose_spec.1).1, rfl⟩
  have hj : Function.Injective j := fun V W h => Subtype.ext (by
    rw [← V.2.choose_spec.2, ← W.2.choose_spec.2]
    exact ((hι _ V.2.choose_spec.1).2.2.2.2 _ W.2.choose_spec.1).1 (congrArg Subtype.val h))
  unfold eis
  rw [← tsum_extend_zero hj]
  refine tendsto_tsum_of_dominated_convergence
    ((eis_automorphy_linear E Ψ hΨ n (N + 1) hn hN φ hφ Z hZ).1 0 0) (fun U => ?_) ?_
  · by_cases hU : ∃ V, j V = U
    · obtain ⟨V, rfl⟩ := hU
      rw [hj.extend_apply]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      obtain ⟨a1, -, a3, a4, -⟩ := hι _ V.2.choose_spec.1
      rw [(_root_.GlobalTheory.SW.weil_parabolic E Ψ hΨ n (N + 1) hn φ hφ).2 _ (j V).2.choose_spec.1 _ a1
        (j V).2.choose_spec.2 _ (pushZ_mem Ψ hZ _ ht)]
      simp only [eisTerm, EisTrans.hFac_zero, a3, dropZ_pushZ]
      rw [← a4 φ hφ, dropF]
      congr 2
      ext k a
      refine Fin.cases rfl (fun _ => rfl) a
    · rw [Function.extend_apply' _ _ _ hU]
      refine term_tendsto_zero Ψ hΨ (by omega) U.2.choose_spec.1 hZ _ (fun h0 => hU ?_) φ
      obtain ⟨γ, hγ, e⟩ := hsurj _ U.2.choose_spec.1 fun a => by
        simpa using congrFun h0 a
      let V : Lag E N := ⟨botSpan γ, γ, hγ, rfl⟩
      refine ⟨V, Subtype.ext ?_⟩
      rw [← U.2.choose_spec.2, e]
      exact ((hι _ V.2.choose_spec.1).2.2.2.2 _ hγ).2 V.2.choose_spec.2
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht U
    exact norm_term_le Ψ U.2.choose_spec.1 hZ _ φ ht
end

