module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChiLIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0171
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LoeZeroOfPsd
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

section gram

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

def gramH (h : α → H) : α → α → ℂ := fun P Q => ⟪h Q, h P⟫_ℂ

theorem qf_gramH (Y : Finset α) (h : α → H) (c : α → ℂ) :
    PBA.qf Y (gramH h) c = ⟪∑ P ∈ Y, conj (c P) • h P, ∑ P ∈ Y, conj (c P) • h P⟫_ℂ := by
  unfold PBA.qf gramH
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring

theorem psd_gramH (Y : Finset α) (h : α → H) : TB.PSDOn Y (gramH h) := by
  rw [PBA.psd_iff_qf]
  refine ⟨fun P _ Q _ => (inner_conj_symm (𝕜 := ℂ) (h P) (h Q)).symm, fun c => ?_⟩
  rw [qf_gramH]
  exact inner_self_nonneg (𝕜 := ℂ)

def Loe (Y : Finset α) (A B : α → α → ℂ) : Prop := TB.PSDOn Y fun P Q => B P Q - A P Q

theorem loe_iff (Y : Finset α) (A B : α → α → ℂ) :
    Loe Y A B ↔ (∀ x ∈ Y, ∀ y ∈ Y, B y x - A y x = conj (B x y - A x y)) ∧
      ∀ c, (PBA.qf Y A c).re ≤ (PBA.qf Y B c).re := by
  unfold Loe
  rw [PBA.psd_iff_qf]
  have e : ∀ c, PBA.qf Y (fun P Q => B P Q - A P Q) c = PBA.qf Y B c - PBA.qf Y A c := by
    intro c; unfold PBA.qf; simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring
  simp only [e, Complex.sub_re, sub_nonneg]

theorem loe_trans {Y : Finset α} {A B C : α → α → ℂ} (h1 : Loe Y A B) (h2 : Loe Y B C) : Loe Y A C := by
  rw [loe_iff] at h1 h2 ⊢
  refine ⟨fun x hx y hy => ?_, fun c => (h1.2 c).trans (h2.2 c)⟩
  have a := h1.1 x hx y hy
  have b := h2.1 x hx y hy
  have : C y x - A y x = (C y x - B y x) + (B y x - A y x) := by ring
  rw [this, a, b, ← map_add (f := _)]; ring_nf

theorem loe_zero_of_psd {Y : Finset α} {B : α → α → ℂ} (h : TB.PSDOn Y B) : Loe Y (fun _ _ => 0) B := by
  unfold Loe; simpa using h

theorem psd_of_loe_zero {Y : Finset α} {B : α → α → ℂ} (h : Loe Y (fun _ _ => 0) B) : TB.PSDOn Y B := by
  unfold Loe at h; simpa using h

theorem qf_mix {N : Type} [Fintype N] (Y : Finset α) (A : N → α → α → ℂ) (θ : N → ℝ) (M : ℝ) (c : α → ℂ) :
    PBA.qf Y (fun p q => (M : ℂ) * ∑ n, (θ n : ℂ) * A n p q) c = (M : ℂ) * ∑ n, (θ n : ℂ) * PBA.qf Y (A n) c := by
  unfold PBA.qf
  have e' : ∀ x y, conj (c x) * ((M : ℂ) * ∑ n, (θ n : ℂ) * A n x y) * c y =
      ∑ n, (M : ℂ) * ((θ n : ℂ) * (conj (c x) * A n x y * c y)) := by
    intro x y
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp_rw [e']
  rw [swap3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]

theorem norm_mix_sq {N : Type} [Fintype N] (lam : N → ℂ) (W : N → H) :
    ‖∑ n, lam n • W n‖ ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
  have h1 : ‖∑ n, lam n • W n‖ ≤ ∑ n, ‖lam n‖ * ‖W n‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_smul _ _).le)
  have h2 : (∑ n, ‖lam n‖ * ‖W n‖) ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun n => Real.sqrt ‖lam n‖)
      (fun n => Real.sqrt ‖lam n‖ * ‖W n‖)
    have e1 : ∀ n, Real.sqrt ‖lam n‖ * (Real.sqrt ‖lam n‖ * ‖W n‖) = ‖lam n‖ * ‖W n‖ := fun n => by
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have e2 : ∀ n, Real.sqrt ‖lam n‖ ^ 2 = ‖lam n‖ := fun n => Real.sq_sqrt (norm_nonneg _)
    have e3 : ∀ n, (Real.sqrt ‖lam n‖ * ‖W n‖) ^ 2 = ‖lam n‖ * ‖W n‖ ^ 2 := fun n => by
      rw [mul_pow, e2]
    simp only [e1, e2, e3] at this
    exact this
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem loe_convex {N : Type} [Fintype N] (Y : Finset α) (lam : N → ℂ) (h : N → α → H) :
    Loe Y (gramH fun P => ∑ n, lam n • h n P)
      (fun P Q => ((∑ n, ‖lam n‖ : ℝ) : ℂ) * ∑ n, ((‖lam n‖ : ℝ) : ℂ) * gramH (h n) P Q) := by
  rw [loe_iff]
  constructor
  · intro x _ y _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gramH, map_sub, map_mul, map_sum, Complex.conj_ofReal, inner_conj_symm]
  · intro c
    have eW : ∑ P ∈ Y, conj (c P) • ∑ n, lam n • h n P = ∑ n, lam n • ∑ P ∈ Y, conj (c P) • h n P := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun P _ => by rw [mul_comm]
    rw [qf_gramH, eW, qf_mix]
    simp only [qf_gramH]
    have hre : ∀ x : H, (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := fun x => by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) x; simpa using this
    rw [Complex.re_ofReal_mul, Complex.re_sum, hre]
    simp only [Complex.re_ofReal_mul, hre]
    exact norm_mix_sq lam _

theorem loe_congr {Y : Finset α} {A A' B B' : α → α → ℂ} (hA : ∀ x ∈ Y, ∀ y ∈ Y, A x y = A' x y)
    (hB : ∀ x ∈ Y, ∀ y ∈ Y, B x y = B' x y) (h : Loe Y A B) : Loe Y A' B' :=
  psd_congr (fun x hx y hy => by rw [hA x hx y hy, hB x hx y hy]) h

theorem loe_refl (Y : Finset α) (A : α → α → ℂ) : Loe Y A A := by
  unfold Loe
  refine psd_congr (k := fun _ _ => (0 : ℂ)) (fun x _ y _ => by ring) ?_
  rw [PBA.psd_iff_qf]; exact ⟨fun _ _ _ _ => by simp, fun c => by simp [PBA.qf]⟩

theorem loe_add {Y : Finset α} {A B A' B' : α → α → ℂ} (h : Loe Y A B) (h' : Loe Y A' B') :
    Loe Y (fun x y => A x y + A' x y) (fun x y => B x y + B' x y) := by
  rw [loe_iff] at h h' ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy; have b := h'.1 x hx y hy
    have : B y x + B' y x - (A y x + A' y x) = (B y x - A y x) + (B' y x - A' y x) := by ring
    rw [this, a, b, ← map_add (f := _)]; ring_nf
  · have e : ∀ K K' : α → α → ℂ, PBA.qf Y (fun x y => K x y + K' x y) c = PBA.qf Y K c + PBA.qf Y K' c := by
      intro K K'; unfold PBA.qf; simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.add_re, Complex.add_re]
    linarith [h.2 c, h'.2 c]

theorem loe_smul {Y : Finset α} {A B : α → α → ℂ} (r : ℝ) (hr : 0 ≤ r) (h : Loe Y A B) :
    Loe Y (fun x y => (r : ℂ) * A x y) (fun x y => (r : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    rw [← mul_sub, ← mul_sub, a, map_mul, Complex.conj_ofReal]
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (r : ℂ) * K x y) c = (r : ℂ) * PBA.qf Y K c := by
      intro K; unfold PBA.qf; simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (h.2 c) hr

theorem loe_sum {ι : Type} (s : Finset ι) {Y : Finset α} {A B : ι → α → α → ℂ} (h : ∀ i ∈ s, Loe Y (A i) (B i)) :
    Loe Y (fun x y => ∑ i ∈ s, A i x y) (fun x y => ∑ i ∈ s, B i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using loe_refl Y (fun _ _ => (0 : ℂ))
  | insert b t hb ih =>
    have h1 := loe_add (h b (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine loe_congr (fun x _ y _ => ?_) (fun x _ y _ => ?_) h1
    · rw [Finset.sum_insert hb]
    · rw [Finset.sum_insert hb]

theorem loe_diag {Y : Finset α} {A B : α → α → ℂ} (ω : α → ℝ) (h : Loe Y A B) :
    Loe Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * A x y) (fun x y => (ω x : ℂ) * (ω y : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    have : (ω y : ℂ) * (ω x : ℂ) * B y x - (ω y : ℂ) * (ω x : ℂ) * A y x = (ω y : ℂ) * (ω x : ℂ) * (B y x - A y x) := by
      ring
    rw [this, a]; simp only [map_mul, map_sub, Complex.conj_ofReal]; ring
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * K x y) c =
        PBA.qf Y K (fun x => (ω x : ℂ) * c x) := by
      intro K; unfold PBA.qf
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        simp only [map_mul, Complex.conj_ofReal]; ring
    rw [e, e]
    exact h.2 _

theorem loe_scale {Y : Finset α} {K : α → α → ℂ} (hK : TB.PSDOn Y K) {r r' : ℝ} (hr : 0 ≤ r' - r) :
    Loe Y (fun x y => (r : ℂ) * K x y) (fun x y => (r' : ℂ) * K x y) := by
  have h := loe_smul (r' - r) hr (loe_zero_of_psd hK)
  unfold Loe at h ⊢
  refine psd_congr (fun x _ y _ => ?_) h
  push_cast; ring

theorem gramH_smul (c : ℂ) (h : α → H) :
    gramH (fun P => c • h P) = fun P Q => ((‖c‖ ^ 2 : ℝ) : ℂ) * gramH h P Q := by
  funext P Q
  unfold gramH
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, mul_comm (conj c) c, Complex.mul_conj']
  push_cast; ring

end gram

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OuterInt
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section outer

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]


set_option maxHeartbeats 1000000 in
theorem outer_int (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hFc : ContinuousOn F (B.GV k r)) (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)) (hBs : MeasurableSet Bs)
    (hBsf : U.muXi k r 0 0 σ Bs < ⊤)
    (hdom : ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
      ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ) :
    Integrable (fun p => theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS ∧
      ∫ p, theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p ∂S.μSS =
        ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
          ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hsW : SigmaFinite S.μW := Dx2.OrbJ.sigmaF S.haarW
  have hsW' : SigmaFinite S.μW' := Dx2.OrbJ.sigmaF S.haarW'
  have hfW : IsFiniteMeasure S.μW := ⟨by rw [hW1]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure S.μW' := ⟨by rw [hW1']; exact ENNReal.one_lt_top⟩
  set γ := U.mMap k r 0 (U.hMat σ d) γ0 with hγ
  have hγG : γ ∈ B.GV k r := by
    have := (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
    exact this
  set f : B.SS k r → (Wq →L[ℂ] Wp) := fun p => theta0 S.z σ.symm p • D.orbIntegrand S γ F p with hf
  have hfm : AEStronglyMeasurable f S.μSS :=
    (theta0_meas S.z σ.symm).aestronglyMeasurable.smul (Dx3.integrand_aesm S hγG hFc)

  have hSS := muSS_eq S hN
  set P := (S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r)) with hP
  have hfm' : AEStronglyMeasurable f (P.map (TN k r)) := by rw [← hSS]; exact hfm
  have hTm : AEMeasurable (TN k r) P := TN_meas.aemeasurable
  set P2 := (S.μW.prod S.μW').prod ((QN k r).prod (QN k r)) with hP2
  have hsw := Dx2.SL.measurePreserving_prod_middle_swap S.μW (QN k r) S.μW' (QN k r)
  set G2 : (Mt k r × Mt k r) × ((U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) → (Wq →L[ℂ] Wp) :=
    fun x => f (TN k r ((x.1.1, x.2.1), (x.1.2, x.2.2))) with hG2
  have hG2e : G2 = (f ∘ TN k r) ∘ (Dx2.SL.swap4 (α := Mt k r) (β := U.RC k r 0 × (G.UT r → ℂ)) (γ := Mt k r)
      (δ := U.RC k r 0 × (G.UT r → ℂ))).symm := by
    funext x; rfl
  have hfTm : AEStronglyMeasurable (f ∘ TN k r) P := hfm'.comp_aemeasurable hTm
  have hG2m : AEStronglyMeasurable G2 P2 := by
    rw [hG2e]
    exact hfTm.comp_measurePreserving (hsw.symm _)

  have hae : ∀ᵐ x ∂(S.μW.prod S.μW'), Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  have hin := fun x : Mt k r × Mt k r => fun hx : Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' =>
    inner_int S z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom x.1 x.2 hx.1 hx.2
  have hG2i : Integrable G2 P2 := by
    rw [integrable_prod_iff hG2m]
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with x hx using (hin x hx).1
    · refine Integrable.of_bound hG2m.norm.integral_prod_right' (M * (U.muXi k r 0 0 σ Bs).toReal) ?_
      filter_upwards [hae] with x hx
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hin x hx).2.2

  have hfTi : Integrable (f ∘ TN k r) P := by
    have := (hsw.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f ∘ TN k r)
    rw [← this, ← hG2e]; exact hG2i
  refine ⟨?_, ?_⟩
  · rw [hSS]; exact (integrable_map_measure hfm' hTm).2 hfTi
  · rw [hSS, integral_map hTm hfm']
    have e := (hsw.symm _).integral_comp' (f ∘ TN k r)
    change ∫ x, (f ∘ TN k r) x ∂P = _
    rw [← e]
    change ∫ x, G2 x ∂P2 = _
    rw [hP2, integral_prod G2 hG2i]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx using (hin x hx).2.1

theorem orbJ_mMap (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0))
    (w : Equiv.Perm (Fin (r + 1))) (dd : Fin (r + 1) → ℂ) (hdd : ∀ a, dd a ≠ 0)
    (hZw : Zhat k r S.z S.z' (U.mMap k r 0 (U.hMat σ d) γ0) = C2.monoP w dd)
    (hw : ∀ a : Fin r, w.symm a.castSucc = (σ a).castSucc)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hFc : ContinuousOn F (B.GV k r)) (hr : 1 ≤ r) (R : ℝ)
    (hFs : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) :
    D.orbJ S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) F =
      ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
        ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  obtain ⟨M, Bs, hBs, hBsf, hdom⟩ := slice_dom k r hr σ d hd F hFc R hFs
  obtain ⟨hint, heq⟩ := outer_int S hN hW1 hW1' z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom
  have hγG : U.mMap k r 0 (U.hMat σ d) γ0 ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
  have hw' : ∀ a : Fin r, w.symm a.castSucc = (σ.symm.symm a).castSucc := by simpa using hw
  have hnc := theta0_normCut S hγG hdd hZw σ.symm hw'
  have hex : ∃ θ, D.IsNormCut S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) θ ∧
      Integrable (fun p => θ p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS :=
    ⟨_, hnc, hint⟩
  unfold D.orbJ
  rw [dite_eq_left hex, Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq S _ _ hrel
    (Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq S _ w dd hγG hdd hZw) F hex.choose _ hex.choose_spec.1 hnc
    hex.choose_spec.2 hint, heq]

end outer

end Formalism.FourierDecayAlt.P.PBM
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothOfRegularity
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ellw

variable {d : ℕ}

def pdc : List (Fin d) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | i :: w, u => fun x => fderiv ℝ (pdc w u) x (Pi.single i 1)

structure SOp (d : ℕ) where
  ord : ℕ
  a : (k : Fin (ord + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ

def SOp.app (P : SOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x

def SOp.tr (P : SOp d) (φ : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d,
    (-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x

def SOp.symb (P : SOp d) (x ξ : Fin d → ℝ) : ℂ :=
  ∑ w : Fin P.ord → Fin d, (∏ i, (ξ (w i) : ℂ)) * P.a (Fin.last P.ord) w x

end ellw

def EllRegW : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : ι → SOp d) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ),
    IsOpen U → (∀ j k w, ContDiffOn ℝ ∞ ((P j).a k w) U) → ContinuousOn u U →
    (∀ j (φ : (Fin d → ℝ) → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, u x * (P j).tr φ x = 0) →
    (∀ x ∈ U, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∃ j, (P j).symb x ξ ≠ 0) →
    ContDiffOn ℝ ∞ u U

def GRegJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (u u' : ℕ → ℝ) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' →
    J ∈ Gr.FFlM ((2 * r + k + 1 : ℕ) : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Q.CV k r (Y : ℂ) J g = c • J g) →
    Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') J

theorem transfer_smooth_of_regularity (hR : GRegJ) : JfSmoothBuilt := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hce := JfS.class_eigenvalue_constant 100 E Wp Wq S T f χ ν' m₀ top A₀ le_rfl hB v
  obtain ⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, hCC, _⟩ := hv v
  have hpos : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
  have hA' : 100 * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ := hA
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    Formalism.FourierDecayAlt.P.CutMP.thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA'
  have hF := Gr.jf_mem_FFlM (T v).base A₀ (2 * S.G.r + S.G.k + 1) (f v) hThr (hCC _)
  obtain ⟨_, _, _, _, _, hTy, hTy'⟩ := hplace
  have hS := hR S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ _ (B.JF (T v).base (f v)) hTy hTy' hF
    (fun Y => ⟨_, hce.2 Y⟩)
  have hsub : ∀ g, g ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v →
      g ∈ Q.Glev S.G.k S.G.r 0 ∩ Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun g hg => ⟨hg.1, (JfS.mem_om_of_mem_omP S T v hg.1.1 hg.2).2⟩
  obtain ⟨_, hL, hRt, hU⟩ := hF
  refine ⟨fun g₀ hg₀ => hS g₀ (hsub g₀ hg₀), fun g hg n hn => hL g (hsub g hg) n hn,
    fun g hg n hn => hRt g (hsub g hg) n hn, fun g hg h hh h' hh' => hU g (hsub g hg) h hh h' hh'⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

