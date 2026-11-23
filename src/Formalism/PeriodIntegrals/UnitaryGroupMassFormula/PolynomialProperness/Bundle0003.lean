module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.NsqMulVecLe
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness

theorem hpkInvol : HpkInvol := fun k r => ⟨GN.hpk_herm k r, GN.hpk_sq k r⟩

theorem gvGroup : GVGroup := fun _ _ =>
  ⟨fun _ hg _ hh => GN.mul_mem hg hh,
    fun _ hg => ⟨GN.inv_eq hg, GN.inv_mem hg, GN.mul_inv hg, GN.inv_mul hg⟩⟩

theorem normInv : NormInv := GN.polynomial_normInv

theorem zhatBound : ZhatBound := GN.zhat_norm_linear_bound

theorem nsq_eq_norm {n : ℕ} (x : Fin n → ℂ) : nsq x = ∑ i, ‖x i‖ ^ 2 := by
  unfold nsq
  exact Finset.sum_congr rfl fun i _ => Complex.normSq_eq_norm_sq _

theorem nsq_mulVec_le {k r : ℕ} (g : B.Mat k r) (x : Fin (2 * r + k + 1) → ℂ) :
    nsq (g *ᵥ x) ≤ B.gN g ^ 2 * nsq x := by
  rw [GN.gN_sq]
  have h1 : ∀ i, ‖(g *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖g i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
    intro i
    have e : (g *ᵥ x) i = ∑ j, g i j * x j := rfl
    rw [e]
    have h2 : ‖∑ j, g i j * x j‖ ≤ ∑ j, ‖g i j‖ * ‖x j‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    calc ‖∑ j, g i j * x j‖ ^ 2 ≤ (∑ j, ‖g i j‖ * ‖x j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ ≤ (∑ j, ‖g i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [nsq_eq_norm, nsq_eq_norm]
  calc ∑ i, ‖(g *ᵥ x) i‖ ^ 2 ≤ ∑ i, (∑ j, ‖g i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = GN.hs g * ∑ j, ‖x j‖ ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        unfold GN.hs
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => (Complex.normSq_eq_norm_sq _).symm

theorem gN_sq_cols {k r : ℕ} (g : B.Mat k r) : B.gN g ^ 2 = ∑ j, nsq (g *ᵥ bvec j) := by
  rw [GN.gN_sq]
  have e : ∀ j i, (g *ᵥ bvec j) i = g i j := by
    intro j i
    simp [bvec, mulVec, dotProduct, Pi.single_apply]
  unfold GN.hs nsq
  simp only [e]
  exact Finset.sum_comm

theorem gnFacts : GNFacts := fun _ _ =>
  ⟨GN.gN_nonneg, GN.gN_mul_le, nsq_mulVec_le, gN_sq_cols⟩

theorem fmul_apply (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    fmul k r z c b i = ∑ a, c a b * fvec k r z a i := by
  unfold fmul
  rw [Finset.sum_apply]
  rfl

theorem fmulBound : FmulBound := by
  intro k r z
  refine ⟨∑ i, (∑ a, ‖fvec k r z a i‖) ^ 2, fun c b => ?_⟩
  have h1 : ∀ i, ‖fmul k r z c b i‖ ≤ mx c * ∑ a, ‖fvec k r z a i‖ := by
    intro i
    rw [fmul_apply, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (GN.entry_le_mx c a b) (norm_nonneg _)
  rw [nsq_eq_norm]
  calc ∑ i, ‖fmul k r z c b i‖ ^ 2 ≤ ∑ i, (mx c * ∑ a, ‖fvec k r z a i‖) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h1 i) 2
    _ = (∑ i, (∑ a, ‖fvec k r z a i‖) ^ 2) * mx c ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

theorem herm_sum_left {n : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (u : ι → ℂ)
    (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    herm H (∑ c, u c • x c) y = ∑ c, u c * herm H (x c) y := by
  unfold herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← mulVecLin_apply, map_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, mulVecLin_apply, dotProduct_smul, smul_eq_mul]

theorem herm_sum_right {n : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ)
    (w : ι → ℂ) (y : ι → Fin n → ℂ) :
    herm H x (∑ d, w d • y d) = ∑ d, star (w d) * herm H x (y d) := by
  unfold herm
  rw [star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem mulVec_fmul (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) :
    g *ᵥ fmul k r z c b = ∑ a, c a b • (g *ᵥ fvec k r z a) := by
  unfold fmul
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← mulVecLin_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, mulVecLin_apply]

theorem zhatMove : ZhatMove := by
  intro k r z z' γ σ s' v u' hσ _ hv hu
  ext a b
  have hσi : σ * σ⁻¹ = 1 := GN.mul_inv hσ
  have key : ∀ x y : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) ((σ⁻¹ * γ * s') *ᵥ x) y = herm (Hpk k r) ((γ * s') *ᵥ x) (σ *ᵥ y) := by
    intro x y
    rw [← GN.herm_mulVec hσ, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hσi,
      Matrix.one_mul]
  show herm (Hpk k r) ((σ⁻¹ * γ * s') *ᵥ fvec k r z' b) (fvec k r z a) = _
  rw [key, hv a, ← mulVec_mulVec, hu b, mulVec_fmul]
  unfold fmul
  rw [herm_sum_right]
  simp only [herm_sum_left]
  simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [Zhat]
  ring

end PI.PolynomialProperness
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnipotentFixesFrameVector
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness

lemma one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  · simp
  · simp
  · simp

lemma UW_fix {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    (b : Fin (r + 1)) : h *ᵥ fvec k r z b = fvec k r z b := by
  unfold fvec
  split_ifs with hb
  · exact (hh.2.1 _).1
  · exact hh.2.2

lemma unipotent_fixes_frame_vector (hU : UMapFrame) {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z)
    {n0 : B.Mat k r} (hn : n0 ∈ N0set k r z) (b : Fin (r + 1)) :
    n0 *ᵥ fvec k r z b = fvec k r z b := by
  have hS : n0 ∈ Sset k r z := ⟨1, one_mem_UW k r z, n0, hn.1, (Matrix.one_mul _).symm⟩
  rw [((hU k r z hz).1 n0 hS).1 b, hn.2]
  simp [Matrix.one_apply]

lemma sg_frame (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z) {n0 h : B.Mat k r}
    {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hn : n0 ∈ N0set k r z) (hv : v ∈ UTset (r + 1)) (hh : h ∈ UWset k r z) :
    n0 * tauM k r z v * h ∈ B.GV k r ∧
      ∀ b, (n0 * tauM k r z v * h) *ᵥ fvec k r z b = fmul k r z v b := by
  obtain ⟨hτN, hτf, -⟩ := hT k r z hz v hv
  have hmul := (hG k r).1
  refine ⟨hmul _ (hmul _ hn.1.1 _ hτN.1) _ hh.1, fun b => ?_⟩
  rw [← Matrix.mulVec_mulVec, UW_fix hh, ← Matrix.mulVec_mulVec, hτf b]
  simp only [fmul, Matrix.mulVec_sum, Matrix.mulVec_smul, unipotent_fixes_frame_vector hU hz hn]

theorem frameS_of (hU : UMapFrame) (hG : GVGroup) : FrameS := by
  intro k r z hz s hs
  have hs' := hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨hf, hut, -⟩ := (hU k r z hz).1 _ hs'
  exact ⟨(hG k r).1 _ hh.1 _ hm.1, uMap k r z (h * m), hut, hf⟩

theorem frameSg_of (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) : FrameSg := by
  intro k r z z' γ hstd σ hσ
  obtain ⟨n0, hn, v, hv, hvL, h, hh, rfl⟩ := hσ
  obtain ⟨h1, h2⟩ := sg_frame hU hT hG hstd.2.1 hn hv hh
  exact ⟨h1, v, hv, hvL, h2⟩

theorem frameSg'_of (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) : FrameSg' := by
  intro k r z z' γ hstd σ hσ
  obtain ⟨n0, hn, v, hv, hPv, h, hh, rfl⟩ := hσ
  obtain ⟨h1, h2⟩ := sg_frame hU hT hG hstd.2.2 hn hv hh
  exact ⟨h1, v, hv, hPv, h2⟩

end PI.PolynomialProperness
end
end

