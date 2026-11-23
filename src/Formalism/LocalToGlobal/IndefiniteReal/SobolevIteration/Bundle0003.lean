module

public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfBdd
section
noncomputable section

open Formalism.L2.Theta Formalism.IndefR.Datum Matrix Filter Topology
open scoped ComplexOrder

namespace Formalism.IndefR.Tow.SobPf

section Gen

variable {n : ℕ}

theorem det_G_unit {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsUnit G.det := by
  rw [isUnit_iff_ne_zero]
  have h1 := hs.2.2.det_pos.ne'
  rw [Matrix.det_mul] at h1
  exact left_ne_zero_of_mul h1

theorem det_UH_unit {G g : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    IsUnit g.det := by
  have h : gᴴ * G * g = G := hg
  have h' := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h'
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h'
  exact hG.ne_zero h'.symm

theorem inv_mem_UH {G g : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have hd := det_UH_unit hG hg
  have h : gᴴ * G * g = G := hg
  show (g⁻¹)ᴴ * G * g⁻¹ = G
  calc (g⁻¹)ᴴ * G * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * G * g) * g⁻¹ := by rw [h]
    _ = (g * g⁻¹)ᴴ * G * (g * g⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
    _ = G := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one, one_mul, mul_one]

theorem conj_mem_lieG {G g X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieG G) : g⁻¹ * X * g ∈ lieG G := by
  have hd := det_UH_unit hG hg
  have h : gᴴ * G * g = G := hg
  have hX' : Xᴴ * G + G * X = 0 := hX
  have e0 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hd
  have e1 : G * g⁻¹ = gᴴ * G := by
    calc G * g⁻¹ = gᴴ * G * g * g⁻¹ := by rw [h]
      _ = gᴴ * G := by rw [Matrix.mul_assoc, e0, Matrix.mul_one]
  have e2 : (g⁻¹)ᴴ * G = G * g := by
    calc (g⁻¹)ᴴ * G = (g⁻¹)ᴴ * (gᴴ * G * g) := by rw [h]
      _ = (g * g⁻¹)ᴴ * G * g := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G * g := by rw [e0, Matrix.conjTranspose_one, Matrix.one_mul]
  show (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem deriv_clm_inv (A B : H →L[ℂ] H) (hBA : ∀ v, B (A v) = v) (f : ℝ → H) :
    deriv (fun t => A (f t)) 0 = A (deriv f 0) := by
  by_cases hf : DifferentiableAt ℝ f 0
  · exact ((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hf.hasDerivAt).deriv
  · have hAf : ¬ DifferentiableAt ℝ (fun t => A (f t)) 0 := by
      intro h
      apply hf
      have e : (fun t => B (A (f t))) = f := funext fun t => hBA (f t)
      rw [← e]
      exact (B.restrictScalars ℝ).differentiableAt.comp 0 h
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hAf, map_zero]

theorem dRep_rep {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) (hG : IsUnit G.det) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (u : H) :
    dRep π X (π g u) = π g (dRep π (g⁻¹ * X * g) u) := by
  have hd := det_UH_unit hG hg
  have hY := conj_mem_lieG hG hg hX
  have hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) (π g u)) =
      fun t : ℝ => π g (π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) := by
    funext t
    have he : NormedSpace.exp (t • X) * g = g * NormedSpace.exp (t • (g⁻¹ * X * g)) := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul,
        Matrix.exp_conj' g (t • X) ((Matrix.isUnit_iff_isUnit_det _).2 hd)]
      simp only [← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul]
    calc π (NormedSpace.exp (t • X)) (π g u) = π (NormedSpace.exp (t • X) * g) u := by
          rw [hπ.2.1 _ (expS_mem_UH hX t) _ hg]; rfl
      _ = π (g * NormedSpace.exp (t • (g⁻¹ * X * g))) u := by rw [he]
      _ = π g (π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) := by
          rw [hπ.2.1 _ hg _ (expS_mem_UH hY t)]; rfl
  have hBA : ∀ v, π g⁻¹ (π g v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← hπ.2.1 _ (inv_mem_UH hG hg) _ hg, Matrix.nonsing_inv_mul _ hd, hπ.1]
    rfl
  show deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) (π g u)) 0 =
    π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) 0)
  rw [hfun]
  exact deriv_clm_inv (π g) (π g⁻¹) hBA _

theorem dL_rep {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) (hG : IsUnit G.det) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ lieG G) (u : H) :
    dL π l (π g u) = π g (dL π (l.map fun X => g⁻¹ * X * g) u) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    show dRep π X (dL π l (π g u)) = π g (dRep π (g⁻¹ * X * g) (dL π (l.map fun X => g⁻¹ * X * g) u))
    rw [ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)), dRep_rep hπ hG hg (hl X (by simp)) _]

end Gen

theorem foldBddK_of (h4 : SobChart) : FoldBddK := by
  intro n H _ _ G s π hs hπ w hw l hl
  have hG := det_G_unit hs
  have hc1 : Cont1 := continuity_of_sobolev_chart h4 foldCont_holds
  have hcont : ContinuousOn (fun k : Fin n → Fin n → ℂ => dL π l (π (Matrix.of k) w))
      {k | Matrix.of k ∈ KAt G s} := by
    intro k0 hk0
    have hk0K : Matrix.of k0 ∈ KAt G s := hk0
    have hk0U : Matrix.of k0 ∈ Formalism.QuantumDeterminants.UH G := hk0K.1
    have hd := det_UH_unit hG hk0U
    have hl' : ∀ X ∈ l.map (fun X => (Matrix.of k0)⁻¹ * X * Matrix.of k0), X ∈ lieG G := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact conj_mem_lieG hG hk0U (hl Y hY)
    refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδ'⟩ := hc1 G s π hs hπ w hw _ hl' ε hε
    have hO : IsOpen {k : Fin n → Fin n → ℂ |
        ∀ i j, ‖((Matrix.of k0)⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ} := by
      have hc : ∀ i j, Continuous fun k : Fin n → Fin n → ℂ =>
          ‖((Matrix.of k0)⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ := fun i j =>
        (((continuous_const.matrix_mul
          (continuous_id' : Continuous fun k : Fin n → Fin n → ℂ => Matrix.of k)).matrix_elem i j).sub
            continuous_const).norm
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt (hc i j) continuous_const
    have hk0O : ∀ i j, ‖((Matrix.of k0)⁻¹ * Matrix.of k0) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ := by
      intro i j
      rw [Matrix.nonsing_inv_mul _ hd, sub_self, norm_zero]
      exact hδ
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO k0 hk0O
    refine ⟨ρ, hρ, fun {k} hk hdk => ?_⟩
    have hkK : Matrix.of k ∈ KAt G s := hk
    have hkU : Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := hkK.1
    have hg : (Matrix.of k0)⁻¹ * Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := mul_mem_UH₂ G _ (inv_mem_UH hG hk0U) _ hkU
    have hnear := hρO (Metric.mem_ball.2 hdk)
    have hkk : π (Matrix.of k) w = π (Matrix.of k0) (π ((Matrix.of k0)⁻¹ * Matrix.of k) w) := by
      rw [← ContinuousLinearMap.comp_apply, ← hπ.2.1 _ hk0U _ hg, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
    rw [dist_eq_norm]
    rw [hkk, dL_rep hπ hG hk0U l hl, dL_rep hπ hG hk0U l hl, ← map_sub, hπ.2.2.1 _ hk0U]
    exact hδ' _ hg hnear
  have hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isCompact_KAt hs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  exact ⟨C, fun k hk => hC (Matrix.of.symm k) hk⟩

end Formalism.IndefR.Tow.SobPf

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfKer
section
noncomputable section

open Formalism.IndefR.Datum Matrix MeasureTheory Topology Filter

namespace Formalism.IndefR.Tow.SobPf

variable {n : ℕ}

def qr (k : Fin n → Fin n → ℂ) : ℝ := ∑ a, ∑ j, ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2

def qP : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ :=
  ∑ a, ∑ j, (MvPolynomial.X (Sum.inr (a, j)) - MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℂ) a j)) *
    (MvPolynomial.X (Sum.inl (a, j)) - MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℂ) a j))

theorem evP_qP (k : Fin n → Fin n → ℂ) : evP (qP (n := n)) k = (qr k : ℂ) := by

  have hδ : ∀ a j : Fin n, starRingEnd ℂ ((1 : Matrix (Fin n) (Fin n) ℂ) a j) =
      (1 : Matrix (Fin n) (Fin n) ℂ) a j := by
    intro a j; rw [Matrix.one_apply]; split_ifs <;> simp
  have hz : ∀ z : ℂ, starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [evP, qP, qr, map_sum, map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Sum.elim_inl, Sum.elim_inr, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hz, map_sub, hδ]

theorem continuous_qr : Continuous (qr (n := n)) := by

  unfold qr
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun j _ =>
    ((continuous_apply_apply a j).sub continuous_const).norm.pow 2

theorem qr_nonneg (k : Fin n → Fin n → ℂ) : 0 ≤ qr k := by
  unfold qr
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem qr_one : qr (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by

  simp [qr]

private theorem norm_sub_one_sq_le_qr (k : Fin n → Fin n → ℂ) (a j : Fin n) :
    ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2 ≤ qr k := by
  unfold qr
  exact le_trans (Finset.single_le_sum (f := fun j => ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ j))
    (Finset.single_le_sum (f := fun a => ∑ j, ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ ^ 2)
      (fun a _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ a))

private theorem mem_ball_one_of_qr_lt_sq {r : ℝ} (hr : 0 < r) (k : Fin n → Fin n → ℂ) (h : qr k < r ^ 2) :
    k ∈ Metric.ball (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) r := by
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  intro a
  rw [dist_pi_lt_iff hr]
  intro j
  rw [dist_eq_norm]
  show ‖k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j‖ < r
  have h1 := lt_of_le_of_lt (norm_sub_one_sq_le_qr k a j) h
  nlinarith [norm_nonneg (k a j - (1 : Matrix (Fin n) (Fin n) ℂ) a j)]

private theorem integrable_of_continuous_of_isHaarK {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s)
    {μ : Measure (Fin n → Fin n → ℂ)} (hμ : IsHaarK G s μ) {f : (Fin n → Fin n → ℂ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  haveI := hμ.1
  have hae : ∀ᵐ k ∂μ, k ∈ {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := hμ.2.1
  have hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isCompact_KAt hs
  have h := hf.continuousOn.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h

theorem polyKernel_holds : PolyKernel := by
  intro n G s hs μ hμ U hU η hη
  haveI := hμ.1
  have hKae : ∀ᵐ k ∂μ, Matrix.of k ∈ KAt G s := hμ.2.1
  have hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isCompact_KAt hs
  obtain ⟨M, hM⟩ := hK.bddAbove_image (continuous_qr (n := n)).continuousOn
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = max M 0 + 1 := ⟨_, rfl⟩
  have hMR : M < R := by rw [hRdef]; linarith [le_max_left M 0]
  have hRpos : 0 < R := by rw [hRdef]; linarith [le_max_right M 0]
  have hRinv : 0 < R⁻¹ := inv_pos.2 hRpos
  have hbK : ∀ k : Fin n → Fin n → ℂ, Matrix.of k ∈ KAt G s →
      0 ≤ 1 - R⁻¹ * qr k ∧ 1 - R⁻¹ * qr k ≤ 1 := by
    intro k hk
    have h0 : qr k ≤ M := hM (Set.mem_image_of_mem qr
      (show k ∈ {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} from hk))
    have h2 : R⁻¹ * qr k ≤ 1 := by
      calc R⁻¹ * qr k ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (by linarith) hRinv.le
        _ = 1 := inv_mul_cancel₀ hRpos.ne'
    have h3 : 0 ≤ R⁻¹ * qr k := mul_nonneg hRinv.le (qr_nonneg k)
    constructor <;> linarith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (r ^ 2) R := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact lt_min (pow_pos hr 2) hRpos
  have hεr : ε ≤ r ^ 2 := by rw [hεdef]; exact min_le_left _ _
  have hεR : R⁻¹ * ε ≤ 1 := by
    calc R⁻¹ * ε ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (by rw [hεdef]; exact min_le_right _ _) hRinv.le
      _ = 1 := inv_mul_cancel₀ hRpos.ne'
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 1 - R⁻¹ * ε := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 - R⁻¹ * (ε / 2) := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβdef]; linarith
  have hαβ : β < α := by rw [hβdef, hαdef]; nlinarith [mul_pos hRinv hε]
  have hα0 : 0 < α := by rw [hαdef]; nlinarith [mul_pos hRinv hε]
  have hbW : ∀ k : Fin n → Fin n → ℂ, ε ≤ qr k → 1 - R⁻¹ * qr k ≤ β := by
    intro k hk
    have := mul_le_mul_of_nonneg_left hk hRinv.le
    rw [hβdef]; linarith
  have hbV : ∀ k : Fin n → Fin n → ℂ, qr k < ε / 2 → α ≤ 1 - R⁻¹ * qr k := by
    intro k hk
    have := mul_le_mul_of_nonneg_left hk.le hRinv.le
    rw [hαdef]; linarith
  have hVmeas : MeasurableSet {k : Fin n → Fin n → ℂ | qr k < ε / 2} :=
    measurableSet_lt (continuous_qr (n := n)).measurable measurable_const
  have hμV : 0 < μ {k : Fin n → Fin n → ℂ | qr k < ε / 2} := by
    refine hμ.2.2.2 _ (isOpen_lt continuous_qr continuous_const) ⟨Matrix.of.symm 1, ?_, ?_⟩
    · show qr (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) < ε / 2
      rw [qr_one]; positivity
    · exact one_mem_KAt G s
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (μ {k : Fin n → Fin n → ℂ | qr k < ε / 2}).toReal := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmdef]; exact ENNReal.toReal_pos hμV.ne' (measure_ne_top μ _)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos hη hm) ((div_lt_one hα0).2 hαβ)
  obtain ⟨g, hgdef⟩ : ∃ g : (Fin n → Fin n → ℂ) → ℝ, g = fun k => (1 - R⁻¹ * qr k) ^ N := ⟨_, rfl⟩
  have hgk : ∀ k, g k = (1 - R⁻¹ * qr k) ^ N := fun k => by rw [hgdef]
  have hg_cont : Continuous g := by
    rw [hgdef]; exact (continuous_const.sub (continuous_const.mul continuous_qr)).pow N
  have hg_int : Integrable g μ := integrable_of_continuous_of_isHaarK hs hμ hg_cont
  have hg_nn : ∀ᵐ k ∂μ, 0 ≤ g k := hKae.mono fun k hk => by rw [hgk]; exact pow_nonneg (hbK k hk).1 N
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ k, g k ∂μ := ⟨_, rfl⟩
  have hI : α ^ N * m ≤ I := by
    have h1 : α ^ N * m ≤ ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε / 2}, g k ∂μ := by
      rw [hmdef]
      have h := setIntegral_ge_of_const_le hVmeas (measure_ne_top μ _)
        (fun k (hk : k ∈ {k : Fin n → Fin n → ℂ | qr k < ε / 2}) =>
          (show α ^ N ≤ g k by rw [hgk]; exact pow_le_pow_left₀ hα0.le (hbV k hk) N))
        hg_int.integrableOn
      refine le_trans (le_of_eq ?_) h
      first
        | rfl
        | exact mul_comm _ _
        | ring1
        | (simp only [Measure.real]; ring1)
        | (simp [Measure.real, mul_comm]; done)
    have h2 : ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε / 2}, g k ∂μ ≤ ∫ k, g k ∂μ :=
      setIntegral_le_integral hg_int hg_nn
    rw [hIdef]; linarith
  have hIpos : 0 < I := lt_of_lt_of_le (mul_pos (pow_pos hα0 N) hm) hI
  have hcm : ∫ k, I⁻¹ * g k ∂μ = I⁻¹ * ∫ k, g k ∂μ := by
    first
      | exact integral_const_mul I⁻¹ _
      | exact integral_mul_left I⁻¹ _
  have hnr : ∀ x : ℝ, 0 ≤ x → ‖(x : ℂ)‖ = x := fun x hx => by
    first
      | exact Complex.norm_of_nonneg hx
      | (rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx])
      | simp [abs_of_nonneg hx]
  obtain ⟨q, hqdef⟩ : ∃ q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ,
      q = MvPolynomial.C ((I⁻¹ : ℝ) : ℂ) *
        (MvPolynomial.C 1 - MvPolynomial.C ((R⁻¹ : ℝ) : ℂ) * qP) ^ N := ⟨_, rfl⟩
  have hF : ∀ k, evP q k = ((I⁻¹ * g k : ℝ) : ℂ) := by
    intro k
    have hq := evP_qP k
    simp only [evP] at hq ⊢
    rw [hqdef, hgk]
    simp only [map_mul, map_pow, map_sub, MvPolynomial.eval_C, hq]
    push_cast
    ring
  have hgI : Integrable (fun k => ((I⁻¹ * g k : ℝ) : ℂ)) μ := (hg_int.const_mul I⁻¹).ofReal
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · rw [show evP q = fun k => ((I⁻¹ * g k : ℝ) : ℂ) from funext hF]
    exact hgI
  · simp only [hF]
    have hc : ∫ k, ((I⁻¹ * g k : ℝ) : ℂ) ∂μ = ((∫ k, I⁻¹ * g k ∂μ : ℝ) : ℂ) := by
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
        | exact (integral_ofReal (𝕜 := ℂ))
    rw [hc, hcm, ← hIdef, inv_mul_cancel₀ hIpos.ne', Complex.ofReal_one]
  · simp only [hF]
    have hae : (fun k => ‖((I⁻¹ * g k : ℝ) : ℂ)‖) =ᵐ[μ] fun k => I⁻¹ * g k := by
      filter_upwards [hg_nn] with k hk
      exact hnr _ (mul_nonneg (inv_nonneg.2 hIpos.le) hk)
    rw [integral_congr_ae hae, hcm, ← hIdef, inv_mul_cancel₀ hIpos.ne']
  · simp only [hF]
    have hWU : {k : Fin n → Fin n → ℂ | qr k < ε} ⊆ U := fun k hk =>
      hball (mem_ball_one_of_qr_lt_sq hr k (lt_of_lt_of_le hk hεr))
    have hWc : MeasurableSet {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ :=
      (measurableSet_lt (continuous_qr (n := n)).measurable measurable_const).compl
    have hni : Integrable (fun k => ‖((I⁻¹ * g k : ℝ) : ℂ)‖) μ := hgI.norm
    have step1 : ∫ k in Uᶜ, ‖((I⁻¹ * g k : ℝ) : ℂ)‖ ∂μ ≤
        ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, ‖((I⁻¹ * g k : ℝ) : ℂ)‖ ∂μ :=
      setIntegral_mono_set hni.integrableOn (ae_of_all _ fun k => norm_nonneg _)
        (Set.compl_subset_compl.2 hWU).eventuallySubset
    have step2 : ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, ‖((I⁻¹ * g k : ℝ) : ℂ)‖ ∂μ ≤
        ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, I⁻¹ * β ^ N ∂μ := by
      refine setIntegral_mono_ae_restrict hni.integrableOn (integrable_const _).integrableOn ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' hWc]
      filter_upwards [hKae] with k hkK hkW
      have hkW' : ε ≤ qr k := by
        by_contra hc
        exact hkW (not_le.1 hc)
      have hb := hbK k hkK
      rw [hnr _ (mul_nonneg (inv_nonneg.2 hIpos.le) (by rw [hgk]; exact pow_nonneg hb.1 N)), hgk]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.1 (hbW k hkW') N) (inv_nonneg.2 hIpos.le)
    have step3 : ∫ k in {k : Fin n → Fin n → ℂ | qr k < ε}ᶜ, I⁻¹ * β ^ N ∂μ ≤ I⁻¹ * β ^ N := by
      rw [setIntegral_const, smul_eq_mul]
      refine mul_le_of_le_one_left (mul_nonneg (inv_nonneg.2 hIpos.le) (pow_nonneg hβ0 N)) ?_
      first
        | exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
        | exact measureReal_le_one
        | simp
    have hβN : β ^ N = (β / α) ^ N * α ^ N := by
      rw [div_pow, div_mul_cancel₀ _ (pow_pos hα0 N).ne']
    have h4 : β ^ N < η * I := by
      calc β ^ N = (β / α) ^ N * α ^ N := hβN
        _ < (η * m) * α ^ N := mul_lt_mul_of_pos_right hN (pow_pos hα0 N)
        _ = η * (α ^ N * m) := by ring
        _ ≤ η * I := mul_le_mul_of_nonneg_left hI hη.le
    have step4 : I⁻¹ * β ^ N < η := by
      calc I⁻¹ * β ^ N < I⁻¹ * (η * I) := mul_lt_mul_of_pos_left h4 (inv_pos.2 hIpos)
        _ = η := by rw [mul_comm η, ← mul_assoc, inv_mul_cancel₀ hIpos.ne', one_mul]
    linarith

end Formalism.IndefR.Tow.SobPf

end
end

