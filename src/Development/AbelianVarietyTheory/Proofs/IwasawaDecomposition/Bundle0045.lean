module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedVacuumDeriv
section
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.MovedVac

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}

set_option linter.unusedSectionVars false

def omL (J : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V →L[ℝ] ℝ :=
  ((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).flip.comp (J.toContinuousLinearEquiv : V →L[ℝ] V)).flip

theorem omL_apply (x y : V) : omL J x y = omJ J x y := rfl

theorem omL_self (hJ : ∀ x, J (J x) = -x) (x : V) : omL J x x = 0 := by
  have := omJ_skew hJ x x
  rw [omL_apply]; linarith

theorem abs_omJ_le (x y : V) : |omJ J x y| ≤ ‖x‖ * ‖y‖ := by
  have := abs_real_inner_le_norm x (J y)
  rwa [J.norm_map] at this

theorem calc' (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) :
    (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧
    (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (omJ J w y : ℂ)) • ρ w f) ∧
    (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (omJ J v w : ℂ)) • ρ w f) :=
  have := DCalc.dH_calculus V B (omL J) ρ (omL_self hJ) h f hf
  ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩

theorem norm_sub_le (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (u z : V) :
    ‖ρ (u + z) f - ρ u f‖ ≤ ‖dH ρ z f‖ + π * (‖u‖ * ‖z‖) * ‖f‖ := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ρ (u + s • z) f) (fderiv ℝ (fun u => ρ u f) (u + s • z) z) s := by
    intro s
    have h2 : HasDerivAt (fun s : ℝ => u + s • z) z s := by
      simpa using ((hasDerivAt_id s).smul_const z).const_add u
    exact (ContDiff.differentiable hf (by simp) _).hasFDerivAt.comp_hasDerivAt s h2
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun s : ℝ => ρ (u + s • z) f)
    (C := ‖dH ρ z f‖ + π * (‖u‖ * ‖z‖) * ‖f‖) (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => ?_)
  · simpa using this
  · have e : omJ J (u + s • z) z = omJ J u z := by
      rw [← omL_apply, map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        omL_self hJ, smul_zero, add_zero, omL_apply]
    rw [(calc' hJ h hf).2.2.1, e]
    refine (_root_.norm_sub_le _ _).trans ?_
    rw [h.2.2.1, norm_smul, h.2.2.1]
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have := abs_omJ_le (J := J) u z
    gcongr

theorem integrable_coef (h : IsHeis (omJ J) ρ) (f : B) {φ : V → ℂ} (hφ : Continuous φ) (K : ℝ) (n : ℕ)
    (hb : ∀ u, ‖φ u‖ ≤ K * ‖u‖ ^ n) : Integrable fun u => gau u • φ u • ρ u f := by
  refine Integrable.mono' (((Osc.integrable_pow_gau (V := V) n).const_mul K).mul_const ‖f‖)
    (continuous_gau.smul (hφ.smul (h.2.2.2 f))).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_smul, norm_smul, h.2.2.1]
  calc ‖gau u‖ * (‖φ u‖ * ‖f‖) ≤ ‖gau u‖ * (K * ‖u‖ ^ n * ‖f‖) := by gcongr; exact hb u
    _ = _ := by ring

theorem cont_coef (v : V) : Continuous fun u : V => (2 * π * I * (omJ J v u : ℂ)) :=
  continuous_const.mul (Complex.continuous_ofReal.comp (omL J v).continuous)

theorem norm_coef (v u : V) : ‖(2 * π * I * (omJ J v u : ℂ))‖ ≤ (2 * π * ‖v‖) * ‖u‖ := by
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_ofNat]
  rw [mul_assoc (2 * π)]
  have := abs_omJ_le (J := J) v u
  gcongr

theorem integrable_dH (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v : V) :
    Integrable fun u => gau u • dH ρ v (ρ u f) := by
  simp only [(calc' hJ h hf).2.2.2, smul_add]
  exact (h.integrable _).add (integrable_coef h f (cont_coef v) (2 * π * ‖v‖) 1 fun u => by
    rw [pow_one]; exact norm_coef v u)

theorem integrable_dH_dH (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (p q : V) :
    Integrable fun u => gau u • dH ρ p (dH ρ q (ρ u f)) := by
  have c1 := calc' hJ h hf
  have c2 := calc' hJ h (c1.1 q)
  have e : ∀ u, gau u • dH ρ p (dH ρ q (ρ u f)) = gau u • dH ρ p (ρ u (dH ρ q f)) +
      (gau u • (2 * π * I * (omJ J q u : ℂ)) • ρ u (dH ρ p f) +
        gau u • ((2 * π * I * (omJ J q u : ℂ)) * (2 * π * I * (omJ J p u : ℂ))) • ρ u f) := by
    intro u
    rw [c1.2.2.2 q, dH_add _ (c2.2.1 u) (Osc.sm_smul _ (c1.2.1 u)), dH_smul _ _ (c1.2.1 u), c1.2.2.2 p,
      smul_add, smul_add, smul_add, smul_smul _ _ (ρ u f)]
  simp only [e]
  refine (integrable_dH hJ h (c1.1 q) p).add ((integrable_coef h _ (cont_coef q) (2 * π * ‖q‖) 1 fun u => by
    rw [pow_one]; exact norm_coef q u).add (integrable_coef h _ ((cont_coef q).mul (cont_coef p))
      ((2 * π * ‖q‖) * (2 * π * ‖p‖)) 2 fun u => ?_))
  rw [norm_mul]
  calc _ ≤ ((2 * π * ‖q‖) * ‖u‖) * ((2 * π * ‖p‖) * ‖u‖) :=
        mul_le_mul (norm_coef q u) (norm_coef p u) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem integral_dH_dH (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (p q : V) :
    ∫ u, gau u • dH ρ p (dH ρ q (ρ u f)) = dH ρ p (dH ρ q (proj h f)) := by
  have c1 := calc' hJ h hf
  have sP : Sm ρ (proj h f) := (Osc.good_proj hJ h f).sm hJ
  have e1 : dH ρ q (proj h f) = ∫ u, gau u • dH ρ q (ρ u f) := by
    have := dH_integral V B (omL J) ρ (omL_self hJ) h V volume (fun u => gau u • ρ u f)
      (fun u => Osc.sm_smul _ (c1.2.1 u)) (h.integrable f) sP q
      (by simp only [dH_smul _ _ (c1.2.1 _)]; exact integrable_dH hJ h hf q)
    simpa only [dH_smul _ _ (c1.2.1 _), proj_apply] using this
  have s2 : ∀ u, Sm ρ (dH ρ q (ρ u f)) := fun u => (calc' hJ h (c1.2.1 u)).1 q
  have := dH_integral V B (omL J) ρ (omL_self hJ) h V volume (fun u => gau u • dH ρ q (ρ u f))
      (fun u => Osc.sm_smul _ (s2 u)) (integrable_dH hJ h hf q) (e1 ▸ (calc' hJ h sP).1 q) p
      (by simp only [dH_smul _ _ (s2 _)]; exact integrable_dH_dH hJ h hf p q)
  rw [e1, this]
  simp only [dH_smul _ _ (s2 _)]

theorem integral_quad (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f)
    {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) :
    (Integrable fun u => gau u • quad ρ c p q (ρ u f)) ∧
      ∫ u, gau u • quad ρ c p q (ρ u f) = quad ρ c p q (proj h f) := by
  have hi : ∀ i ∈ Finset.univ, Integrable fun u => c i • gau u • dH ρ (p i) (dH ρ (q i) (ρ u f)) :=
    fun i _ => (integrable_dH_dH hJ h hf (p i) (q i)).smul (c i)
  simp only [quad, Finset.smul_sum, smul_comm (gau _) (c _)]
  refine ⟨MeasureTheory.integrable_finsetSum _ hi, ?_⟩
  rw [MeasureTheory.integral_finsetSum _ hi]
  simp only [integral_smul, integral_dH_dH hJ h hf]

theorem moved_vacuum_deriv : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (a : ℝ → V →L[ℝ] V) (X : V →L[ℝ] V), a 0 = 1 → HasDerivAt a X 0 → (∀ t x y, omJ J (a t x) (a t y) = omJ J x y) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (omJ J) X c p q → (∃ C : ℝ, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x, ‖(∫ u, gau u • ρ (a t u) (proj h x)) - proj h x‖ ≤ C * |t| * ‖x‖) ∧ ∃ lam : ℂ, ∀ x, HasDerivAt (fun t : ℝ => ∫ u, gau u • ρ (a t u) (proj h x)) (quad ρ c p q (proj h x) + lam • proj h x) 0 := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h a X a0 ha hom κ _ c p q hq
  obtain ⟨⟨C, hC⟩, -, hl⟩ := VacBd.vacuum_bound V B J ρ hJ h
  have sP : ∀ x, Sm ρ (proj h x) := fun x => (Osc.good_proj hJ h x).sm hJ
  obtain ⟨K, hK0, hK⟩ := ha.hasFDerivAt.isBigO_sub.exists_nonneg
  have hK := hK.bound
  simp only [a0, sub_zero, Real.norm_eq_abs] at hK
  set b : V → ℝ := fun u => |C| * K * (‖u‖ ^ 1 * ‖gau u‖) + π * K * ‖proj h‖ * (‖u‖ ^ 2 * ‖gau u‖) with hb
  have bi : Integrable b :=
    ((Osc.integrable_pow_gau 1).const_mul _).add ((Osc.integrable_pow_gau 2).const_mul _)
  have key : ∀ t, ‖a t - 1‖ ≤ K * |t| → ∀ x u,
      ‖gau u • ρ (a t u) (proj h x) - gau u • ρ u (proj h x)‖ ≤ b u * ‖x‖ * |t| := by
    intro t ht x u
    have hz : ‖a t u - u‖ ≤ K * |t| * ‖u‖ := by
      have := (a t - 1).le_opNorm u
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at this
      exact this.trans (by gcongr)
    have h1 := norm_sub_le hJ h (sP x) u (a t u - u)
    rw [add_sub_cancel] at h1
    have h2 : ‖dH ρ (a t u - u) (proj h x)‖ ≤ |C| * (K * |t| * ‖u‖) * ‖x‖ :=
      (hC _ _).trans (by gcongr; exact le_abs_self C)
    have h3 : π * (‖u‖ * ‖a t u - u‖) * ‖proj h x‖ ≤ π * (‖u‖ * (K * |t| * ‖u‖)) * (‖proj h‖ * ‖x‖) := by
      gcongr; exact (proj h).le_opNorm x
    rw [← smul_sub, norm_smul]
    calc _ ≤ ‖gau u‖ * (|C| * (K * |t| * ‖u‖) * ‖x‖ + π * (‖u‖ * (K * |t| * ‖u‖)) * (‖proj h‖ * ‖x‖)) := by
          gcongr; linarith
      _ = _ := by simp only [hb]; ring
  refine ⟨⟨∫ u, b u, ?_⟩, ?_⟩
  · filter_upwards [hK] with t ht x
    have i1 : Integrable fun u => gau u • ρ (a t u) (proj h x) := (h.twist (a t) (hom t)).integrable _
    have e : proj h x = ∫ u, gau u • ρ u (proj h x) := (Osc.proj_proj hJ h x).symm
    calc _ = ‖∫ u, (gau u • ρ (a t u) (proj h x) - gau u • ρ u (proj h x))‖ := by
          rw [integral_sub i1 (h.integrable _), ← e]
      _ ≤ ∫ u, b u * ‖x‖ * |t| :=
          norm_integral_le_of_norm_le ((bi.mul_const _).mul_const _) (Filter.Eventually.of_forall (key t ht x))
      _ = _ := by rw [integral_mul_const, integral_mul_const]; ring
  · choose l hl using hl
    refine ⟨-∑ i, c i * l (p i) (q i), fun x => ?_⟩
    have hG : ∀ u, fderiv ℝ (fun u => ρ u (proj h x)) u (X u) =
        quad ρ c p q (ρ u (proj h x)) - ρ u (quad ρ c p q (proj h x)) :=
      GlobalTheory.Mem.Lift.fderiv_eq_quad_comm V B (omL J) ρ (omL_self hJ) h X κ c p q hq _ (sP x)
    obtain ⟨i1, e1⟩ := integral_quad hJ h (sP x) c p q
    have i2 := h.integrable (quad ρ c p q (proj h x))
    have i3 : Integrable fun u => gau u • fderiv ℝ (fun u => ρ u (proj h x)) u (X u) := by
      simp only [hG, smul_sub]; exact i1.sub i2
    have e3 : ∫ u, gau u • fderiv ℝ (fun u => ρ u (proj h x)) u (X u) =
        quad ρ c p q (proj h x) + (-∑ i, c i * l (p i) (q i)) • proj h x := by
      simp only [hG, smul_sub]
      rw [integral_sub i1 i2, e1, Osc.proj_proj hJ, ← proj_apply h, neg_smul, sub_eq_add_neg, Finset.sum_smul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [quad, map_sum, map_smul, hl, smul_smul]
    rw [← e3]
    have i4 : Integrable fun u =>
        ContinuousLinearMap.toSpanSingleton ℝ (gau u • fderiv ℝ (fun u => ρ u (proj h x)) u (X u)) :=
      ((ContinuousLinearMap.smulRightL ℝ ℝ B 1).integrable_comp i3)
    have := (hasFDerivAt_integral_of_dominated_loc_of_lip' (𝕜 := ℝ) (μ := volume)
      (F := fun (t : ℝ) (u : V) => gau u • ρ (a t u) (proj h x)) (x₀ := 0)
      (F' := fun u => ContinuousLinearMap.toSpanSingleton ℝ (gau u • fderiv ℝ (fun u => ρ u (proj h x)) u (X u)))
      (bound := fun u => b u * ‖x‖) (s := {t | ‖a t - 1‖ ≤ K * |t|}) hK
      (fun t _ => ((h.twist (a t) (hom t)).integrable _).aestronglyMeasurable)
      ((h.twist (a 0) (hom 0)).integrable _) i4.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u t ht => by
        simpa only [a0, ContinuousLinearMap.one_apply, sub_zero, Real.norm_eq_abs] using key t ht x u)
      (bi.mul_const _) (Filter.Eventually.of_forall fun u => ?_)).2.hasDerivAt
    · rw [ContinuousLinearMap.integral_apply i4] at this
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using this
    · have h2 : HasDerivAt (fun t => a t u) (X u) 0 := by
        simpa using ha.clm_apply (hasDerivAt_const (0 : ℝ) u)
      have h3 := (ContDiff.differentiable (sP x) (by simp) u).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h2
        (by simp [a0])
      exact (h3.const_smul (gau u)).hasFDerivAt

end GlobalTheory.Mem.Lift.MovedVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialEvalZeroOfVanishingRationalSkewHermi
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem eval_upt_eq_zero_of_skew (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hQ : ∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 →
      MvPolynomial.eval (upt (ratPt S)) Q = 0)
    (Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) :
    MvPolynomial.eval (upt Y) Q = 0 := by
  classical
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => by simp [hc]
  have hσc : ∀ (σ : L →+* ℂ) x, σ (c x) = ComplexEmbedding.conjugate σ x := fun σ x => by
    rw [ComplexEmbedding.conjugate_coe_eq]; exact IsCMField.complexEmbedding_complexConj L σ x

  let B := NumberField.canonicalEmbedding.latticeBasis L
  let b : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → L := fun k => NumberField.integralBasis L k
  have hB : ∀ k, B k = fun σ => σ (b k) := fun k => by
    funext σ; rw [NumberField.canonicalEmbedding.latticeBasis_apply, NumberField.canonicalEmbedding.apply_at]
  have H1 : ∀ σ₀ : L →+* ℂ, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ,
      ∀ σ, ∑ k, a k * σ (b k) = if σ = σ₀ then 1 else 0 := by
    intro σ₀
    refine ⟨B.repr (Pi.single σ₀ 1), fun σ => ?_⟩
    have := congrFun (B.sum_repr (Pi.single σ₀ 1)) σ
    simpa [Finset.sum_apply, hB, Pi.single_apply] using this
  choose a ha using H1

  let S : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → Matrix (Fin n) (Fin n) L := fun J =>
    Matrix.of fun u v => (if u = J.1 ∧ v = J.2.1 then b J.2.2 else 0) -
      (if u = J.2.1 ∧ v = J.1 then c (b J.2.2) else 0)
  let r : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → (L →+* ℂ) × Fin n × Fin n → ℂ :=
    fun J => upt (ratPt (S J))
  have hSk : ∀ J u v, S J u v + c (S J v u) = 0 := by
    intro J u v
    simp only [S, Matrix.of_apply, map_sub]
    split_ifs <;> simp only [map_zero, hcc, sub_zero, zero_sub, add_zero, zero_add] <;>
      first | ring1 | (exfalso; tauto)
  have hskew : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ,
      (∑ J, (t J : L) • S J) + ((∑ J, (t J : L) • S J).map c)ᵀ = 0 := by
    intro t; ext u v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_ratCast, Matrix.zero_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun J _ => ?_
    rw [← mul_add, hSk, mul_zero]
  have hrat : ∀ t : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℚ,
      (fun p => ∑ J, (t J : ℂ) * r J p) = upt (ratPt (∑ J, (t J : L) • S J)) := by
    intro t; funext p
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [r, upt, ratPt, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      map_sum, map_mul, map_ratCast]

  let Q' := MvPolynomial.bind₁ (fun p => ∑ J, MvPolynomial.X J * MvPolynomial.C (r J p)) Q
  have heval : ∀ z, MvPolynomial.eval z Q' = MvPolynomial.eval (fun p => ∑ J, z J * r J p) Q := by
    intro z
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) z Q' = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext p
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have hQ' : Q' = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Rat.cast : ℚ → ℂ))
      (fun _ => Set.infinite_range_of_injective Rat.cast_injective) fun z hz => ?_
    choose t ht using fun J => hz J (Set.mem_univ _)
    have hz' : z = fun J => (t J : ℂ) := by funext J; exact (ht J).symm
    rw [heval, hz', hrat, hQ _ (hskew t), map_zero]

  let z : Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ :=
    fun J => (1 / 2) * ∑ σ₀, Y σ₀ J.1 J.2.1 * a σ₀ J.2.2
  have key : ∀ u v (τ : L →+* ℂ), ∑ k, z (u, v, k) * τ (b k) = (1 / 2) * Y τ u v := by
    intro u v τ
    calc ∑ k, z (u, v, k) * τ (b k)
        = ∑ k, ∑ σ₀, (1 / 2) * (Y σ₀ u v * (a σ₀ k * τ (b k))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [z, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          ring
      _ = ∑ σ₀, (1 / 2) * (Y σ₀ u v * ∑ k, a σ₀ k * τ (b k)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = (1 / 2) * Y τ u v := by
          simp only [ha, mul_ite, mul_one, mul_zero]
          simp
  have hcomb : upt Y = fun p => ∑ J, z J * r J p := by
    funext ⟨σ, u, v⟩
    have e1 : ∀ J, r J (σ, u, v) = (if u = J.1 ∧ v = J.2.1 then σ (b J.2.2) else 0) -
        (if u = J.2.1 ∧ v = J.1 then ComplexEmbedding.conjugate σ (b J.2.2) else 0) := by
      intro J
      simp only [r, upt, ratPt, S, Matrix.map_apply, Matrix.of_apply, map_sub]
      simp only [apply_ite σ, map_zero, hσc]
    simp only [e1, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e2 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n),
        (∑ x, ∑ x_1, ∑ x_2, if p = x then if q = x_1 then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k := by
      intro f p q
      rw [Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp),
        Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    have e3 : ∀ (f : Fin n → Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ℂ) (p q : Fin n),
        (∑ x, ∑ x_1, ∑ x_2, if q = x_1 then if p = x then f x x_1 x_2 else 0 else 0) = ∑ k, f p q k := by
      intro f p q
      rw [Finset.sum_eq_single p (fun x _ hx => by simp [Ne.symm hx]) (by simp),
        Finset.sum_eq_single q (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    rw [e2 (fun x x_1 x_2 => z (x, x_1, x_2) * σ (b x_2)),
      e3 (fun x x_1 x_2 => z (x, x_1, x_2) * (ComplexEmbedding.conjugate σ) (b x_2)), key, key, hY σ]
    simp only [upt, Matrix.neg_apply, Matrix.transpose_apply]
    ring
  rw [hcomb, ← heval, hQ', map_zero]

end GlobalTheory.AlgWtHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShift
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_of_cofinite_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ)
    (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite →
    (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) →
    Φ B *ᵥ v ∈ S := by
  intro n ι _ _ Φ hΦ S v B F hF hS
  choose Q hQ using hΦ.poly
  let M : ℂ → Matrix (Fin n) (Fin n) ℂ := fun s => B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ)
  let x : ℂ → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ :=
    fun s => Sum.elim (fun p => M s p.1 p.2) (fun p => (M s)⁻¹ p.1 p.2)
  let g : ℂ → ι → ℂ := fun s i => ∑ j, MvPolynomial.eval (x s) (Q i j) * v j
  have hMc : Continuous M := by
    fun_prop
  have hdetB : IsUnit (B.val).det := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  have hM0 : M 0 = B.val := by simp [M]
  have hinvc : ContinuousAt (fun s => (M s)⁻¹) 0 := by
    have h1 : ContinuousAt Inv.inv (M 0) := by
      apply continuousAt_matrix_inv
      rw [hM0]
      exact NormedRing.inverse_continuousAt hdetB.unit
    exact h1.comp hMc.continuousAt
  have hxc : ContinuousAt x 0 := by
    rw [continuousAt_pi]
    rintro (p | p)
    · exact ((continuous_apply p.2).comp ((continuous_apply p.1).comp hMc)).continuousAt
    · exact ((continuous_apply p.2).comp (continuous_apply p.1)).continuousAt.comp hinvc
  have hgc : ContinuousAt g 0 := by
    rw [continuousAt_pi]
    intro i
    apply tendsto_finsetSum
    intro j _
    exact (((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp hxc).mul continuousAt_const

  have hgC : ∀ s, ∀ C : GL (Fin n) ℂ, C.val = M s → g s = Φ C *ᵥ v := by
    intro s C hC
    funext i
    simp only [g, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hQ i j C]
    have hx : x s = Sum.elim (fun p => C.val p.1 p.2) (fun p => (C⁻¹).val p.1 p.2) := by
      funext q
      rcases q with p | p
      · simp [x, hC]
      · simp [x, Matrix.coe_units_inv, hC]
    rw [hx]
  have hg0 : g 0 = Φ B *ᵥ v := hgC 0 B hM0.symm
  have hdetev : ∀ᶠ s in nhds (0:ℂ), IsUnit (M s).det := by
    have hc : ContinuousAt (fun s => (M s).det) 0 := hMc.matrix_det.continuousAt
    have : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    have hne : (M 0).det ≠ 0 := by rw [hM0]; exact hdetB.ne_zero
    filter_upwards [hc.eventually (this.mem_nhds hne)] with s hs
    exact isUnit_iff_ne_zero.2 hs
  have hFev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, s ∉ F := by
    have hcl : IsClosed (F \ {0}) := (hF.diff).isClosed
    have hmem : (F \ {0})ᶜ ∈ nhds (0:ℂ) := hcl.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hs1 hs2
    intro hsF
    exact hs1 ⟨hsF, hs2⟩
  have hev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, g s ∈ S := by
    filter_upwards [hFev, nhdsWithin_le_nhds hdetev] with s hs hdet
    rw [hgC s (Matrix.nonsingInvUnit (M s) hdet) rfl]
    exact hS s hs _ rfl
  have ht : Filter.Tendsto g (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (Φ B *ᵥ v)) := by
    rw [← hg0]
    exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  exact (Submodule.closed_of_finiteDimensional S).mem_of_tendsto ht hev

end GlobalTheory.AlgWtHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialRepTransvectionEntries
section
open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem eval_transvection_polynomial_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (Polynomial.X : Polynomial ℂ)) a b) = transvection i j c a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem eval_transvection_polynomial_neg_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (-Polynomial.X : Polynomial ℂ)) a b) = transvection i j (-c) a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem eval_aeval_mv {σ : Type} (g : σ → Polynomial ℂ) (Q : MvPolynomial σ ℂ) (s : ℂ) :
    Polynomial.eval s (MvPolynomial.aeval g Q) = MvPolynomial.eval (fun v => (g v).eval s) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

theorem polyRep_transvection_entries_poly :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ →
      ∀ (i j : Fin n), i ≠ j → ∃ P : ι → ι → Polynomial ℂ, ∀ (s : ℂ) (B : GL (Fin n) ℂ),
        B.val = transvection i j s → ∀ a b, Φ B a b = (P a b).eval s := by
  intro n ι _ _ Φ hΦ i j hij
  choose Q hQ using hΦ.poly
  let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Polynomial ℂ :=
    Sum.elim (fun p => transvection i j (Polynomial.X : Polynomial ℂ) p.1 p.2)
      (fun p => transvection i j (-Polynomial.X : Polynomial ℂ) p.1 p.2)
  refine ⟨fun a b => MvPolynomial.aeval g (Q a b), ?_⟩
  intro s B hB a b
  have hinv : (B⁻¹).val = transvection i j (-s) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hB]
    have := transvection_mul_transvection_same (R := ℂ) i j hij s (-s)
    rw [this, add_neg_cancel, transvection_zero]
  rw [hQ a b B, eval_aeval_mv]
  congr 2
  funext v
  rcases v with p | p
  · simp [g, eval_transvection_polynomial_X_entry, hB]
  · simp [g, eval_transvection_polynomial_neg_X_entry, hinv]

end GlobalTheory
end

