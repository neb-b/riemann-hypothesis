module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.UnitaryModelOfMultiplicityGardingDensity
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.DenseWeakVectors
section
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.KFinSmoothW

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Dense

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma umat_mem_UJset (h : UpqRep.UJ ε) : umat h ∈ UJset ε := h.2

lemma one_mem_UJset : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  exact (UpqRep.UJ ε).one_mem

lemma cont_orbit {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ) (u : H) :
    Continuous (fun h : UpqRep.UJ ε => τ (umat h) u) := (hτ.2.2 u).comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun h => h.2)

lemma gv_sub_norm_le [CompleteSpace H] {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hτ : IsURepOn (UJset ε) τ)
    (Φr : Matrix (Fin n) (Fin n) ℂ → ℝ) (hΦc : Continuous Φr) (hΦ0 : ∀ x, 0 ≤ Φr x)
    (hint : Integrable (fun h : UpqRep.UJ ε => Φr (umat h)) (muG ε))
    (h1 : ∫ h, Φr (umat h) ∂(muG ε) = 1) (u : H) (δ : ℝ)
    (hsupp : ∀ h : UpqRep.UJ ε, Φr (umat h) ≠ 0 → ‖τ (umat h) u - u‖ ≤ δ) :
    ‖gv ε τ (fun x => (Φr x : ℂ)) u - u‖ ≤ δ := by
  have hc := cont_orbit hτ u
  have hI1 : Integrable (fun h : UpqRep.UJ ε => Φr (umat h) • τ (umat h) u) (muG ε) := by
    refine Integrable.mono' (hint.mul_const ‖u‖) ?_ ?_
    · exact ((hΦc.comp (continuous_coeMatrix ε)).smul hc).aestronglyMeasurable
    · filter_upwards with h
      rw [norm_smul, hτ.2.1 _ (umat_mem_UJset h), Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]
  have hI2 : Integrable (fun h : UpqRep.UJ ε => Φr (umat h) • u) (muG ε) := hint.smul_const u
  have hgv : gv ε τ (fun x => (Φr x : ℂ)) u = ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε) := by
    unfold gv
    congr 1
  have hu : ∫ h, Φr (umat h) • u ∂(muG ε) = u := by
    rw [integral_smul_const, h1, one_smul]
  have hdiff : ∫ h, Φr (umat h) • (τ (umat h) u - u) ∂(muG ε) =
      ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε) - u := by
    simp_rw [smul_sub]
    rw [integral_sub hI1 hI2, hu]
  rw [hgv, ← hdiff]
  calc ‖∫ h, Φr (umat h) • (τ (umat h) u - u) ∂(muG ε)‖
      ≤ ∫ h, Φr (umat h) * δ ∂(muG ε) := by
        refine norm_integral_le_of_norm_le (hint.mul_const δ) ?_
        filter_upwards with h
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]
        by_cases hz : Φr (umat h) = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_left (hsupp h hz) (hΦ0 _)
    _ = δ := by rw [integral_mul_const, h1, one_mul]

def qd (x : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖x i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2

lemma qd_contDiff : ContDiff ℝ ∞ (qd (n := n)) := by
  unfold qd
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℝ).comp ((contDiff_apply_apply ℝ i j).sub contDiff_const)

lemma qd_one : qd (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [qd]

lemma qd_eq_trace (x : Matrix (Fin n) (Fin n) ℂ) :
    qd x = (Matrix.trace ((x - 1)ᴴ * (x - 1))).re := by
  simp only [qd, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Matrix.sub_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

lemma qd_conj (a m : Matrix (Fin n) (Fin n) ℂ) (h1 : a * aᴴ = 1) (h2 : aᴴ * a = 1) :
    qd (a * m * aᴴ) = qd m := by
  rw [qd_eq_trace, qd_eq_trace]
  have e : a * m * aᴴ - 1 = a * (m - 1) * aᴴ := by
    rw [mul_sub, sub_mul, mul_one, h1]
  have e2 : (a * (m - 1) * aᴴ)ᴴ * (a * (m - 1) * aᴴ) = a * ((m - 1)ᴴ * (m - 1)) * aᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc aᴴ a, h2, Matrix.one_mul]
  rw [e, e2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

lemma dist_lt_of_qd_lt {x : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 < r) (h : qd x < r ^ 2) :
    dist x 1 < r := by
  rw [dist_eq_norm, Matrix.norm_lt_iff hr]
  intro i j
  have hle : ‖(x - 1) i j‖ ^ 2 ≤ qd x := by
    unfold qd
    rw [Matrix.sub_apply]
    calc ‖x i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
        ≤ ∑ j', ‖x i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖x i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖x i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j'‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun i' => ∑ j', ‖x i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg ((x - 1) i j)]

end Dense

theorem dense_weak_vectors : StepDenseW := by
  intro n ε H _ _ _ τ hτ W hW

  let R : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] H) := fun g => (τ g).comp W.subtypeL
  have hR : ContinuousWithinAt R (UJset ε) 1 :=
    continuousWithinAt_clm_apply.2 fun y => hτ.2.2 (y : H) 1 one_mem_UJset
  obtain ⟨r, hr, hr'⟩ := Metric.continuousWithinAt_iff.mp hR (1 / 2) (by norm_num)
  have hτ1 : τ 1 = 1 := hτ.1.1
  have hclose : ∀ g ∈ UJset ε, dist g 1 < r → ∀ w ∈ W, ‖τ g w - w‖ ≤ ‖w‖ / 2 := by
    intro g hg hd w hw
    have h1 := hr' hg hd
    rw [dist_eq_norm] at h1
    have h2 := (R g - R 1).le_opNorm ⟨w, hw⟩
    have h3 : (R g - R 1) ⟨w, hw⟩ = τ g w - w := by
      simp [R, hτ1]
    rw [h3] at h2
    have h4 : ‖(⟨w, hw⟩ : W)‖ = ‖w‖ := rfl
    rw [h4] at h2
    calc ‖τ g w - w‖ ≤ ‖R g - R 1‖ * ‖w‖ := h2
      _ ≤ (1 / 2) * ‖w‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
      _ = ‖w‖ / 2 := by ring

  have hr2 : 0 < r ^ 2 := by positivity
  let ψ : ContDiffBump (0 : ℝ) := ⟨r ^ 2 / 2, r ^ 2, half_pos hr2, half_lt_self hr2⟩
  let Φ0 : Matrix (Fin n) (Fin n) ℂ → ℝ := fun x => ψ (qd x)
  have hΦ0c : Continuous Φ0 := ψ.continuous.comp qd_contDiff.continuous
  have hsupp0 : ∀ x, Φ0 x ≠ 0 → dist x 1 < r := by
    intro x hx
    have hb : qd x ∈ Function.support ψ := hx
    rw [ψ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hb
    exact dist_lt_of_qd_lt hr (lt_of_le_of_lt (le_abs_self _) hb)
  have hcs : HasCompactSupport Φ0 := by
    refine HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) ?_
    intro x hx
    by_contra hne
    exact hx (Metric.mem_closedBall.2 (hsupp0 x hne).le)
  have hcomp : Continuous (fun h : UpqRep.UJ ε => Φ0 (umat h)) := hΦ0c.comp (continuous_coeMatrix ε)
  have hint : Integrable (fun h : UpqRep.UJ ε => Φ0 (umat h)) (muG ε) :=
    hcomp.integrable_of_hasCompactSupport (hcs.comp_isClosedEmbedding (isClosedEmbeddingMatrix n ε).1)
  have hpos : 0 < ∫ h, Φ0 (umat h) ∂(muG ε) := by
    rw [integral_pos_iff_support_of_nonneg (fun h => ψ.nonneg) hint]
    apply IsOpen.measure_pos
    · exact isOpen_ne_fun hcomp continuous_const
    · refine ⟨1, ?_⟩
      show ψ (qd (umat (1 : UpqRep.UJ ε))) ≠ 0
      have h1 : umat (1 : UpqRep.UJ ε) = 1 := rfl
      rw [h1, qd_one, ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)]
      exact one_ne_zero
  set c := ∫ h, Φ0 (umat h) ∂(muG ε) with hc
  refine ⟨fun x => ((Φ0 x / c : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((ψ.contDiff.comp qd_contDiff).div_const c)
  · exact hcs.comp_left (g := fun t : ℝ => ((t / c : ℝ) : ℂ)) (by simp)
  · intro a ha m
    have hu1 : a * aᴴ = 1 := by
      have := Unitary.mul_star_self_of_mem ha.1
      rwa [Matrix.star_eq_conjTranspose] at this
    have hu2 : aᴴ * a = 1 := by
      have := Unitary.star_mul_self_of_mem ha.1
      rwa [Matrix.star_eq_conjTranspose] at this
    simp only [Φ0, qd_conj a m hu1 hu2]
  · intro w hw
    refine gv_sub_norm_le hτ (fun x => Φ0 x / c) (hΦ0c.div_const c)
      (fun x => div_nonneg ψ.nonneg hpos.le) (hint.div_const c)
      (by rw [integral_div, ← hc, div_self hpos.ne']) w (‖w‖ / 2) ?_
    intro h hz
    have hne : Φ0 (umat h) ≠ 0 := by
      intro h0
      apply hz
      show Φ0 (umat h) / c = 0
      rw [h0, zero_div]
    exact hclose _ (umat_mem_UJset h) (hsupp0 _ hne) w hw

end PI.KFinSmoothW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.Garding
section
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.KFinSmoothW

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Gard

def mMeas (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _

attribute [local instance] mMeas

lemma mBorel (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := by
  exact ⟨rfl⟩

attribute [local instance] mBorel

lemma mBorelN (n : ℕ) : @BorelSpace (Matrix (Fin n) (Fin n) ℂ)
    (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
      (@SeminormedAddCommGroup.toPseudoMetricSpace _
        (@NormedAddCommGroup.toSeminormedAddCommGroup _ Matrix.normedAddCommGroup)))) (mMeas n) := by
  exact ⟨rfl⟩

attribute [local instance] mBorelN

lemma mLocCpt (n : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := by
  exact inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))

attribute [local instance] mLocCpt

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {N : WithTop ℕ∞}

lemma contDiff_mat_iff {f : E → Matrix (Fin n) (Fin n) ℂ} :
    ContDiff ℝ N f ↔ ∀ i j, ContDiff ℝ N (fun x => f x i j) := by
  exact contDiff_pi.trans (forall_congr' fun i => contDiff_pi)

lemma contDiff_mat_mul {f g : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiff ℝ N f)
    (hg : ContDiff ℝ N g) : ContDiff ℝ N (fun x => f x * g x) := by
  rw [contDiff_mat_iff] at hf hg ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hf i k).mul (hg k j)

lemma contDiff_mat_conjT {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => (f x)ᴴ) := by
  rw [contDiff_mat_iff] at hf ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.comp (hf j i)

end Calc

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

lemma umat_closedEmb (ε : Fin n → Bool) :
    IsClosedEmbedding (umat : UpqRep.UJ ε → Matrix (Fin n) (Fin n) ℂ) := by
  exact ⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, (range_coeMatrix ε) ▸ isClosed_pseudoUnitary ε⟩

lemma umat_measEmb (ε : Fin n → Bool) :
    MeasurableEmbedding (umat : UpqRep.UJ ε → Matrix (Fin n) (Fin n) ℂ) := by
  exact (umat_closedEmb ε).measurableEmbedding

lemma umat_mem (h : UpqRep.UJ ε) : umat h ∈ UJset ε := by
  exact h.2

lemma umat_inv (γ : UpqRep.UJ ε) : umat γ⁻¹ = Jm ε * (umat γ)ᴴ * Jm ε := by
  exact coeMatrix_inv_eq ε γ

lemma umat_mul_inv (γ : UpqRep.UJ ε) : umat γ * umat γ⁻¹ = 1 := by
  exact Units.mul_inv (γ : (Matrix (Fin n) (Fin n) ℂ)ˣ)

lemma cont_orbit {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ) (x : H) :
    Continuous (fun h : UpqRep.UJ ε => τ (umat h) x) := by
  exact (hτ.2.2 x).comp_continuous (continuous_coeMatrix ε) (fun h => umat_mem h)

lemma integrable_orbit {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    (Ψ : UpqRep.UJ ε → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) (x : H) :
    Integrable (fun h => Ψ h • τ (umat h) x) (muG ε) := by
  exact (hΨ.smul (cont_orbit hτ x)).integrable_of_hasCompactSupport hΨc.smul_right

lemma tau_gv {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (x : H)
    (γ : UpqRep.UJ ε) :
    τ (umat γ) (gv ε τ Φ x) =
      ∫ h, Φ (Jm ε * (umat γ)ᴴ * Jm ε * umat h) • τ (umat h) x ∂(muG ε) := by
  have hint := integrable_orbit hτ (fun h => Φ (umat h)) (hΦ.comp (continuous_coeMatrix ε))
    (hΦc.comp_isClosedEmbedding (umat_closedEmb ε)) x
  rw [gv, ← (τ (umat γ)).integral_comp_comm hint]
  have key := integral_mul_left_eq_self (μ := muG ε)
    (fun h' => Φ (Jm ε * (umat γ)ᴴ * Jm ε * umat h') • τ (umat h') x) γ
  beta_reduce at key
  rw [← key]
  congr 1
  funext h
  rw [show umat (γ * h) = umat γ * umat h from rfl, ← Matrix.mul_assoc,
    coeMatrix_left_inv ε _ (umat_mem γ), Matrix.one_mul, hτ.1.2 _ (umat_mem γ) _ (umat_mem h), map_smul]
  rfl

def Lsm (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : H →L[ℝ] ℂ →L[ℝ] H :=
  (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] H →L[ℝ] H).flip

lemma Lsm_apply (v : H) (c : ℂ) : Lsm H v c = c • v := rfl

lemma locInt {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ) (x : H) :
    LocallyIntegrable (fun t => τ t x) (Measure.map umat (muG ε)) := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  rw [(umat_measEmb ε).integrableOn_map_iff]
  exact (cont_orbit hτ x).continuousOn.integrableOn_compact ((umat_closedEmb ε).isCompact_preimage hK)

private theorem matrix_norm_mul_le_card_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    ‖A * B‖ ≤ m * ‖A‖ * ‖B‖ := by
  have h0 : 0 ≤ (m : ℝ) * ‖A‖ * ‖B‖ := by positivity
  rw [Matrix.norm_le_iff h0]
  intro i j
  rw [Matrix.mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin m, ‖A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
          (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = m * ‖A‖ * ‖B‖ := by simp [mul_assoc]

theorem stepGarding_main : StepGarding := by
  intro n ε H _ _ _ τ hτ Φ hΦ hΦc x
  unfold SmoothJ SmoothOnH
  intro g₀ hg₀
  have hl : (Jm ε * g₀ᴴ * Jm ε) * g₀ = 1 := coeMatrix_left_inv ε g₀ hg₀
  have hr : g₀ * (Jm ε * g₀ᴴ * Jm ε) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hl
  set A : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun p => Jm ε * pᴴ * Jm ε with hA
  have hAc : ContDiff ℝ ∞ A :=
    contDiff_mat_mul (contDiff_mat_mul contDiff_const (contDiff_mat_conjT contDiff_id)) contDiff_const

  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ tsupport Φ ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hΦc.isCompact.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity,
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  set c : ℝ := (n : ℝ) * ‖g₀‖ with hc
  have hc0 : 0 ≤ c := by positivity
  set U : Set (Matrix (Fin n) (Fin n) ℂ) := {p | (n : ℝ) * c * ‖A p - A g₀‖ < 1 / 2} with hU
  have hUo : IsOpen U :=
    isOpen_lt (continuous_const.mul ((hAc.continuous.sub continuous_const).norm)) continuous_const
  have hg₀U : g₀ ∈ U := by
    show (n : ℝ) * c * ‖A g₀ - A g₀‖ < 1 / 2
    simp

  have hk : ∀ p ∈ U, ∀ y, Φ (A p * (-y)) ≠ 0 → ‖y‖ ≤ 2 * c * R := by
    intro p hp y hy
    have hp' : (n : ℝ) * c * ‖A p - A g₀‖ < 1 / 2 := hp
    have hz : ‖A p * (-y)‖ ≤ R := by
      have h0 := hR (subset_tsupport _ hy)
      simpa using h0
    have h1 : -y = g₀ * (A g₀ * (-y)) := by
      rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
    have h2 : A g₀ * (-y) = A p * (-y) - (A p - A g₀) * (-y) := by
      rw [Matrix.sub_mul]
      abel
    have e1 := matrix_norm_mul_le_card_mul g₀ (A g₀ * (-y))
    have e2 := matrix_norm_mul_le_card_mul (A p - A g₀) (-y)
    rw [← h1, norm_neg] at e1
    rw [norm_neg] at e2
    have e3 : ‖A g₀ * (-y)‖ ≤ ‖A p * (-y)‖ + ‖(A p - A g₀) * (-y)‖ := by
      rw [h2]
      exact norm_sub_le _ _
    have e4 : ‖A g₀ * (-y)‖ ≤ R + n * ‖A p - A g₀‖ * ‖y‖ := by linarith
    have e5 : ‖y‖ ≤ c * (R + n * ‖A p - A g₀‖ * ‖y‖) := by
      calc ‖y‖ ≤ n * ‖g₀‖ * ‖A g₀ * (-y)‖ := e1
        _ ≤ c * (R + n * ‖A p - A g₀‖ * ‖y‖) := by
          rw [hc]
          exact mul_le_mul_of_nonneg_left e4 (by positivity)
    have e6 : c * (n * ‖A p - A g₀‖ * ‖y‖) ≤ 1 / 2 * ‖y‖ := by
      have h3 := mul_le_mul_of_nonneg_right hp'.le (norm_nonneg y)
      linarith
    linarith
  have hgs : ∀ (p y : Matrix (Fin n) (Fin n) ℂ), p ∈ U → y ∉ Metric.closedBall 0 (2 * c * R) →
      Φ (A p * (-y)) = 0 := by
    intro p y hp hy
    by_contra h
    exact hy (mem_closedBall_zero_iff.mpr (hk p hp y h))
  have hGs : ContDiff ℝ ∞ (fun q : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      Φ (A q.1 * (-q.2))) :=
    hΦ.comp (contDiff_mat_mul (hAc.comp contDiff_fst) contDiff_snd.neg)
  have hconv := MeasureTheory.contDiffOn_convolution_right_with_param (𝕜 := ℝ)
    (μ := Measure.map umat (muG ε)) (f := fun t => τ t x) (n := ⊤) (Lsm H)
    (g := fun p y => Φ (A p * (-y))) hUo (isCompact_closedBall 0 (2 * c * R)) hgs (locInt hτ x)
    hGs.contDiffOn
  refine ⟨U, fun p => MeasureTheory.convolution (fun t => τ t x) (fun y => Φ (A p * (-y))) (Lsm H)
    (Measure.map umat (muG ε)) 0, hUo, hg₀U, ?_, ?_⟩
  · have h2 : ContDiffOn ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ => (p, (0 : Matrix (Fin n) (Fin n) ℂ))) U :=
      contDiffOn_id.prodMk contDiffOn_const
    have h4 : Set.MapsTo (fun p : Matrix (Fin n) (Fin n) ℂ => (p, (0 : Matrix (Fin n) (Fin n) ℂ))) U
        (U ×ˢ Set.univ) := fun p hp => ⟨hp, Set.mem_univ _⟩
    have h5 := ContDiffOn.comp hconv h2 h4
    exact h5
  · intro g _ hg
    have hgl : (Jm ε * gᴴ * Jm ε) * g = 1 := coeMatrix_left_inv ε g hg
    have hgr : g * (Jm ε * gᴴ * Jm ε) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hgl
    let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨g, Jm ε * gᴴ * Jm ε, hgr, hgl⟩
    let γ : UpqRep.UJ ε := ⟨u, hg⟩
    have hγ : umat γ = g := rfl
    beta_reduce
    rw [← hγ, tau_gv hτ Φ hΦ.continuous hΦc x γ, hγ, MeasureTheory.convolution_def,
      (umat_measEmb ε).integral_map]
    congr 1
    funext h
    rw [Lsm_apply, zero_sub, neg_neg]

end Gard

theorem garding_vectors_smooth : StepGarding := by
  exact Gard.stepGarding_main

end PI.KFinSmoothW
end
end

