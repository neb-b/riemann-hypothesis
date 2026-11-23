module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableGeneral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0242
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0235
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0248
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0226
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableOfTransport
section
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Tr

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fs_tr (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ Ψ : RadSp k r z z' π π') :
    fs μ l Φ Ψ c t = (κ : ℂ)⁻¹ * ∫ c'' : Cf (r - l.succ) 0, wtI 0 c'' *
      pairAt μi (T Φ) (T Ψ) (glue 0 (shiftV l.succ (Function.update c l t)) c'') := by
  have hjl : (0 : Fin (r - l.succ + 1)).val + l.succ.val = l.succ.val := by simp
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  unfold fs
  rw [← (shEqJ_mp l.succ l.succ 0 hjl).integral_comp', ← integral_const_mul]
  congr 1; funext c''
  rw [wtI_shEqJ, glue_shEqJ l.succ l.succ 0 hjl (Function.update c l t) (Function.update c l t) (fun _ _ => rfl), hT]
  field_simp

theorem level_one_square_integrable_of_transport (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ : RadSp k r z z' π π') (c₀ : Fin (r - l.succ) → ℂ) (h : LevelSquareIntegrable μi 0 (T Φ) c₀) :
    LevelSquareIntegrable μ l.succ Φ (Function.update c l t) :=
  level_square_integrable_of_transport μ l.succ (Function.update c l t) μi T κ hκ hT Φ c₀ h

end Tr

end Formalism.FourierDecayAlt.P5.HerD
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneSubPowLe
section
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

theorem qU_pos : 0 < qU := by
  unfold qU
  have hβ : U.betaU ≠ 0 := Formalism.FourierDecayAlt.P.scale_matching.2.1
  have hc : 0 < ‖U.betaU‖ / (2 * Real.pi) := div_pos (norm_pos_iff.2 hβ) (by positivity)
  exact_mod_cast Real.toNNReal_pos.2 hc

theorem qU_coe (N : ℕ) : (((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) ^ N : NNReal) : ℝ) : ℂ) = ((qU ^ N : ℝ) : ℂ) := by
  unfold qU; push_cast; rfl

theorem exists_hMat_n (a : C.LPt) (ha : ∀ b ∈ a, 1 ≤ b.1 ∧ b.2 ≠ 0) (n : ℕ) (hn : D.ptSize a = n) :
    ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), U.hMat σ d = D.ptMatN a n := by
  subst hn
  obtain ⟨σ, d, -, hM⟩ := PBJ.Asm.exists_hMat a ha
  exact ⟨σ, d, hM⟩

section vec

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem vec_om {n : ℕ} (vec : C.LPt → V) (Φ0 : G.Mat n → V) (hΦ0 : PBJ.KCls Φ0)
    (hV : ∀ (a : C.LPt) (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), D.IsLocPt a n → U.hMat σ d = D.ptMatN a n →
      vec a = U.PhiTop (p := n) (s := 0) U.betaU σ d Φ0 fun x => x.elim0)
    (H : C.LPt) (hH : ∀ b ∈ H, 1 ≤ b.1 ∧ b.2 ≠ 0) (m : ℕ) (hn : D.ptSize H + (m + 1 + 1) = n) :
    ∃ (σh : Equiv.Perm (Fin (D.ptSize H))) (dh : Fin (D.ptSize H) → ℂ) (Ψ0 : G.Mat (D.ptSize H + (m + 1 + 1)) → V),
      (∀ i, dh i ≠ 0) ∧ PBJ.KCls Ψ0 ∧
      (∀ t c : ℂ, t ≠ 0 → c ≠ 0 → vec (H ++ [(m + 1, t), (1, c)]) =
        (((qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))))⁻¹ : ℝ) : ℂ) •
          G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) t c) ∧
      (∀ z : ℂ, z ≠ 0 → vec (H ++ [(m + 1 + 1, z)]) =
        (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) z) := by
  subst hn
  have hβ : U.betaU ≠ 0 := Formalism.FourierDecayAlt.P.scale_matching.2.1
  obtain ⟨σh, dh, hdh, hMh⟩ := PBJ.Asm.exists_hMat H hH
  refine ⟨σh, dh, Φ0, hdh, hΦ0, ?_, ?_⟩
  · intro t c ht hc
    set a := H ++ [(m + 1, t), (1, c)] with ha
    have hloc : D.IsLocPt a (D.ptSize H + (m + 1 + 1)) := by
      refine ⟨fun b hb => ?_, ?_⟩
      · rcases List.mem_append.1 hb with hb | hb
        · exact hH b hb
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact ⟨by omega, ht⟩
          · exact ⟨le_rfl, hc⟩
      · rw [ha, PBJ.Asm.ptSize_append]; simp [D.ptSize]
    obtain ⟨σ, d, hM⟩ := exists_hMat_n a hloc.1 _ hloc.2
    have hdb : ∀ i, PBJ.Om.dB (m + 1) t c i ≠ 0 := by
      intro i
      induction i using Fin.addCases with
      | left j => simp only [PBJ.Om.dB, PBJ.Fub.dQ, Fin.addCases_left]; exact ht
      | right j => simp only [PBJ.Om.dB, PBJ.Fub.dQ, Fin.addCases_right]; exact hc
    have e1 := PBJ.Asm.ptMatN_append H [(m + 1, t), (1, c)]
    have hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat (PBJ.Om.σB (m + 1)) (PBJ.Om.dB (m + 1) t c)) := by
      rw [hM, hMh, PBJ.Om.hMat_block, ← PBJ.Asm.ptMatN_block]; exact e1
    rw [hV a σ d hloc hM, PBJ.fubini_head_last_part U.betaU (D.ptSize H) (m + 1 + 1) σ d σh dh (PBJ.Om.σB (m + 1))
      (PBJ.Om.dB (m + 1) t c) V Φ0 hdh hdb hM' hΦ0]
    rw [PBJ.Om.omBlock_eq U.betaU (m + 1) t c, qU_coe, smul_smul, Fintype.card_fin]
    have hq : (qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))) : ℝ) ≠ 0 := pow_ne_zero _ qU_pos.ne'
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hq, Complex.ofReal_one, one_smul]
    rfl
  · intro z hz
    set a := H ++ [(m + 1 + 1, z)] with ha
    have hloc : D.IsLocPt a (D.ptSize H + (m + 1 + 1)) := by
      refine ⟨fun b hb => ?_, ?_⟩
      · rcases List.mem_append.1 hb with hb | hb
        · exact hH b hb
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl
          exact ⟨by omega, hz⟩
      · rw [ha, PBJ.Asm.ptSize_append]; simp [D.ptSize]
    obtain ⟨σ, d, hM⟩ := exists_hMat_n a hloc.1 _ hloc.2
    have hMb : U.hMat (Fin.revPerm : Equiv.Perm (Fin (m + 1 + 1))) (fun _ => z) =
        D.ptMatN [(m + 1 + 1, z)] (D.ptSize [(m + 1 + 1, z)]) := by
      rw [PBJ.Asm.hMat_rev]; exact (PBJ.Asm.ptMatN_long (m + 1 + 1) z).symm
    have hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat Fin.revPerm (fun _ => z)) := by
      rw [hM, hMh, hMb]; exact PBJ.Asm.ptMatN_append H [(m + 1 + 1, z)]
    rw [hV a σ d hloc hM, PBJ.fubini_head_last_part U.betaU (D.ptSize H) (m + 1 + 1) σ d σh dh Fin.revPerm (fun _ => z) V Φ0
      hdh (fun _ => hz) hM' hΦ0]
    rw [PBJ.Om.omLong_eq U.betaU (m + 1) z, qU_coe, smul_smul]
    have hq : (qU ^ Fintype.card (G.UT (m + 1 + 1)) : ℝ) ≠ 0 := pow_ne_zero _ qU_pos.ne'
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hq, Complex.ofReal_one, one_smul]

end vec

section rho

theorem one_sub_pow_le (u : ℝ) (hu0 : 0 ≤ u) (n : ℕ) : 1 - u ^ n ≤ n * (1 - u) := by
  have := one_add_mul_le_pow (a := u - 1) (by linarith) n
  simp only [add_sub_cancel] at this
  linarith

theorem rho_fac (δ : ℝ) (hδ : 0 < δ) (k N : ℕ) (u : ℝ) (hu1 : δ ≤ u) (hu2 : u ≤ 1) :
    |√(u ^ k) * √((u⁻¹) ^ N)| ≤ √((δ⁻¹) ^ N) ∧
      |√(u ^ k) * √((u⁻¹) ^ N) - 1| ≤ (k + N * (δ⁻¹) ^ N) * (1 - u) := by
  have hu0 : 0 < u := lt_of_lt_of_le hδ hu1
  have hk0 : 0 ≤ u ^ k := pow_nonneg hu0.le k
  have hk1 : u ^ k ≤ 1 := pow_le_one₀ hu0.le hu2
  have hi1 : 1 ≤ u⁻¹ := one_le_inv₀ hu0 |>.2 hu2
  have hiδ : u⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hu1
  have hN1 : 1 ≤ (u⁻¹) ^ N := one_le_pow₀ hi1
  have hNδ : (u⁻¹) ^ N ≤ (δ⁻¹) ^ N := pow_le_pow_left₀ (by positivity) hiδ N
  set f := √(u ^ k) * √((u⁻¹) ^ N) with hf
  have hf0 : 0 ≤ f := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hf2 : f ^ 2 = u ^ k * (u⁻¹) ^ N := by
    rw [hf, mul_pow, Real.sq_sqrt hk0, Real.sq_sqrt (by positivity)]
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg hf0, hf]
    calc √(u ^ k) * √((u⁻¹) ^ N) ≤ 1 * √((δ⁻¹) ^ N) := by
          refine mul_le_mul ?_ (Real.sqrt_le_sqrt hNδ) (Real.sqrt_nonneg _) zero_le_one
          rw [Real.sqrt_le_one]; exact hk1
      _ = √((δ⁻¹) ^ N) := one_mul _
  ·
    have h1 : |f - 1| ≤ |f ^ 2 - 1| := by
      have : f ^ 2 - 1 = (f - 1) * (f + 1) := by ring
      rw [this, abs_mul]
      have : 1 ≤ |f + 1| := by rw [abs_of_nonneg (by linarith)]; linarith
      nlinarith [abs_nonneg (f - 1)]
    have hA : 1 - u ^ k ≤ k * (1 - u) := one_sub_pow_le u hu0.le k
    have hB : (u⁻¹) ^ N - 1 ≤ N * (δ⁻¹) ^ N * (1 - u) := by
      have e : (u⁻¹) ^ N - 1 = (u⁻¹) ^ N * (1 - u ^ N) := by
        rw [mul_sub, mul_one, ← mul_pow, inv_mul_cancel₀ hu0.ne', one_pow]
      rw [e]
      have hC := one_sub_pow_le u hu0.le N
      have h0 : 0 ≤ 1 - u ^ N := by linarith [pow_le_one₀ (n := N) hu0.le hu2]
      calc (u⁻¹) ^ N * (1 - u ^ N) ≤ (δ⁻¹) ^ N * (N * (1 - u)) :=
            mul_le_mul hNδ hC h0 (by positivity)
        _ = N * (δ⁻¹) ^ N * (1 - u) := by ring
    have h2 : |f ^ 2 - 1| ≤ (k + N * (δ⁻¹) ^ N) * (1 - u) := by
      rw [hf2]
      have e : u ^ k * (u⁻¹) ^ N - 1 = u ^ k * ((u⁻¹) ^ N - 1) - (1 - u ^ k) := by ring
      rw [e]
      have ha : 0 ≤ u ^ k * ((u⁻¹) ^ N - 1) := mul_nonneg hk0 (by linarith)
      have hb : u ^ k * ((u⁻¹) ^ N - 1) ≤ N * (δ⁻¹) ^ N * (1 - u) :=
        le_trans (mul_le_of_le_one_left (by linarith) hk1) hB
      rw [abs_le]; constructor <;> nlinarith
    linarith

theorem rho_bound (TT ε0 dH0 MK mK : ℝ) (hTT : 0 < TT) (hε0 : 0 < ε0) (hdH0 : 0 ≤ dH0) (hmK : 0 < mK)
    (k N m : ℕ) (l1 x y c : ℂ) (hl1 : l1 ≠ 0) (hx : x ≠ 0) (hy0 : y ≠ 0) (hc0 : c ≠ 0) (hyM : ‖y‖ ≤ MK)
    (hym : mK ≤ ‖y‖) (hnc : Complex.normSq c = ‖x‖ ^ (2 * (m + 1)) * ‖y‖ ^ 2)
    (hA : ε0 ≤ dH0 * ‖l1 * x⁻¹‖ ^ (2 * (m + 1)) * (Complex.normSq c - TT)) :
    |√((Complex.normSq c - TT) ^ k) / ‖c‖ ^ k * √((Complex.normSq c / (Complex.normSq c - TT)) ^ N)| ≤
        √(((ε0 / (max dH0 1 * ‖l1‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N) ∧
      |√((Complex.normSq c - TT) ^ k) / ‖c‖ ^ k * √((Complex.normSq c / (Complex.normSq c - TT)) ^ N) - 1| ≤
        ((k : ℝ) + N * ((ε0 / (max dH0 1 * ‖l1‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N) *
          (TT / mK ^ 2) * ‖x‖⁻¹ ^ (2 * (m + 1)) := by
  set n := 2 * (m + 1) with hn
  set δ := ε0 / (max dH0 1 * ‖l1‖ ^ n * (max MK 1) ^ 2) with hδ
  set GG := Complex.normSq c - TT with hGG
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hl1pos : 0 < ‖l1‖ := norm_pos_iff.2 hl1
  have hncpos : 0 < Complex.normSq c := by rw [hnc]; positivity
  have hnt : ‖l1 * x⁻¹‖ ^ n = ‖l1‖ ^ n * (‖x‖ ^ n)⁻¹ := by
    rw [norm_mul, norm_inv, mul_pow, inv_pow]
  rw [hnt] at hA
  have hGGpos : 0 < GG := by
    by_contra hle
    have : dH0 * (‖l1‖ ^ n * (‖x‖ ^ n)⁻¹) * GG ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hle)
    linarith
  set u := GG / Complex.normSq c with hu
  have hu0 : 0 ≤ u := div_nonneg hGGpos.le hncpos.le
  have huy : u * ‖y‖ ^ 2 = GG * (‖x‖ ^ n)⁻¹ := by
    rw [hu, hnc]; field_simp
  have hu1 : δ ≤ u := by
    have hden : 0 < max dH0 1 * ‖l1‖ ^ n * (max MK 1) ^ 2 := by positivity
    rw [hδ, div_le_iff₀ hden]
    have hyM' : ‖y‖ ^ 2 ≤ (max MK 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hyM.trans (le_max_left _ _)) 2
    calc ε0 ≤ dH0 * (‖l1‖ ^ n * (‖x‖ ^ n)⁻¹) * GG := hA
      _ = dH0 * ‖l1‖ ^ n * (u * ‖y‖ ^ 2) := by rw [huy]; ring
      _ ≤ max dH0 1 * ‖l1‖ ^ n * (u * (max MK 1) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
            (mul_le_mul_of_nonneg_left hyM' hu0) (by positivity) (by positivity)
      _ = u * (max dH0 1 * ‖l1‖ ^ n * (max MK 1) ^ 2) := by ring
  have hu2 : u ≤ 1 := by
    rw [hu, div_le_one hncpos, hGG]; linarith
  have h1u : 1 - u ≤ TT / mK ^ 2 * (‖x‖ ^ n)⁻¹ := by
    have e : 1 - u = TT / Complex.normSq c := by
      rw [hu, hGG]; field_simp; ring
    rw [e, hnc]
    have hmy : mK ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hmK.le hym 2
    calc TT / (‖x‖ ^ n * ‖y‖ ^ 2) ≤ TT / (‖x‖ ^ n * mK ^ 2) :=
          div_le_div_of_nonneg_left hTT.le (by positivity) (mul_le_mul_of_nonneg_left hmy (by positivity))
      _ = TT / mK ^ 2 * (‖x‖ ^ n)⁻¹ := by field_simp
  have hρu : √(GG ^ k) / ‖c‖ ^ k * √((Complex.normSq c / GG) ^ N) = √(u ^ k) * √((u⁻¹) ^ N) := by
    have hinv : Complex.normSq c / GG = u⁻¹ := by rw [hu, inv_div]
    rw [hinv]
    congr 1
    have hcn : ‖c‖ ^ 2 = Complex.normSq c := (Complex.normSq_eq_norm_sq c).symm
    have hGu : GG = u * ‖c‖ ^ 2 := by rw [hcn, hu, div_mul_cancel₀ _ hncpos.ne']
    rw [hGu, mul_pow, Real.sqrt_mul (pow_nonneg hu0 _), ← pow_mul, mul_comm 2, pow_mul,
      Real.sqrt_sq (pow_nonneg (norm_nonneg _) _)]
    have : ‖c‖ ^ k ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hc0)
    field_simp
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨hb1, hb2⟩ := rho_fac δ hδpos k N u hu1 hu2
  rw [hρu]
  refine ⟨hb1, hb2.trans ?_⟩
  rw [mul_assoc, inv_pow ‖x‖ n]
  exact mul_le_mul_of_nonneg_left h1u (by positivity)

end rho

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section defs

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Proper (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n) (Cs : Set (B.Mat k n))
    (U : Set (B.Mat k n)) : Prop :=
  ∀ y ∈ U, ∃ V ∈ 𝓝 y, ∃ K : Set (PBQ.XP k p ρ), IsCompact K ∧ ∀ g ∈ V, g ∈ B.GV k n → ∀ x, PBQ.GoodP Bj x → x ∉ K →
    ∀ ξ, PBG.InR B0 ξ → D.castM e (PBQ.sP Bj x) * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∉ Cs

end defs

def PbWords : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (i : ℕ) (hi : i ≤ n) (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    (∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g) →
    IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → (∀ g ∈ U, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0) →
    Proper Bj B0 e Cs U →
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)), ∀ y ∈ U, y ∈ B.GV k n →
      D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w ew y =
        PBQ.pbF Bj B0 e (D.uwG k n B0.z B0.z' H i hi w ew) y

def PbLoc : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    B.CkOn ⊤ (B.GV k n) H → IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → Proper Bj B0 e Cs U →
    ∀ y ∈ U, y ∈ B.GV k n → CapelliWordSumExpansion.Loc ⊤ (PBQ.pbF Bj B0 e H) y

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVNonloc
section
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def hsLE {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] (Eρ : Wp' →L[ℂ] Wp') :
    (Wq' →L[ℂ] Wp') →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq') => Wp') :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => B.hsVec (Eρ.comp X)
      map_add' := fun X Y => by rw [ContinuousLinearMap.comp_add]; unfold B.hsVec; rfl
      map_smul' := fun c X => by rw [ContinuousLinearMap.comp_smul]; exact PBL.hsVec_smul c _ }

theorem hsLE_apply {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] (Eρ : Wp' →L[ℂ] Wp')
    (X : Wq' →L[ℂ] Wp') : hsLE Eρ X = B.hsVec (Eρ.comp X) := rfl

theorem vecV_nonloc {P : M.Par} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp']
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (Bs : B.RealPlaceData P.k P.r Wp' Wq')
    (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp')) (Q : C.LPt)
    (hQ : ¬ D.IsLocPt Q (P.r + 1)) : D.vecV Bs ν' m₀ F Q = 0 := by
  unfold D.vecV
  rw [dite_eq_right (fun h => hQ h.1)]

theorem gN_top_gram {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (a : List C.Letter)
    (ha : D.AdmAt S v a) :
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (Fi : I → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : I → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] PBL.HV S v),
      (∀ i, 0 ≤ c i) ∧ (∀ i, KB.CptCoef (p v).T.base (Fi i)) ∧
      ∀ P Q : C.LPt, KB.gN (PBL.setC S p F) v ε (S.G.r + 1) a P Q =
        ∑ i, (c i : ℂ) * ⟪(omN S a.length Q : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S Q)),
          (omN S a.length P : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S P))⟫_ℂ := by
  classical
  have hgpos := PBL.g_pos_of_built hB
  have hTT := (PBL.pdG_of_built hB v).2
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGr, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hcutw : KB.CutWord (D.parOf S v) (p v).l0 a := by
    obtain ⟨w, hw⟩ := ha
    rw [hl0, ← hw]
    exact PBD.cutWord_of_adm S hGr (PBCut.cutInside_of_built hB) w v
  have hInD' : KB.InDDplus2 (D.parOf S v) (p v).l0 (p v).T.base Cb (p v).Θ := by rw [hl0]; exact hInD
  have hTh : ∀ e : Wd.Ix (Fin a.length), ∃ F' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      KB.CptCoef (p v).T.base F' ∧ ∀ Q, (p v).V ((p v).Θ.Θ a e (F v ε)) Q = (p v).V F' Q := by
    intro e
    obtain ⟨F', hF', -, hV⟩ := Formalism.FourierDecayAlt.P.theta_compact_support _ _ (D.parOf S v) (p v) (F v ε) a e Cb hInD'
      (hF v ε hε) hcutw
    exact ⟨F', hF', hV⟩
  choose Fe hFe hVe using hTh
  have hΓ : PBL.ΓS S (S.G.r + 1) = 1 := by simp [PBL.ΓS, D.GamLev]
  refine ⟨Wd.Ix (Fin a.length) × M.Ty (D.parOf S v), inferInstance,
    fun i => PBL.del2 S p v a i.1 i.2 / (PBL.ΓS S (S.G.r + 1) * S.sizeAt v a), fun i => Fe i.1,
    fun i => hsLE ((p v).TP.E i.2), fun i => ?_, fun i => hFe i.1, fun P Q => ?_⟩
  · rw [hΓ, one_mul]
    exact div_nonneg (PBL.second_defect_nonneg S p v a i.1 i.2) (PBL.sizeAt_nonneg S v a)
  by_cases hloc : D.IsLocPt P (S.G.r + 1) ∧ D.IsLocPt Q (S.G.r + 1)
  · obtain ⟨hPl, hQl⟩ := hloc
    have hPs : D.IsLocPt (PBL.stdS S P) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hPl
    have hQs : D.IsLocPt (PBL.stdS S Q) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hQl
    rw [PBL.gN_setC hB, PBL.rr_top_eq Formalism.FourierDecayAlt.P.vector_valued_types (p v) (F v ε) a _ _ hPs hQs]
    unfold Top.topOf
    rw [Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    dsimp only
    have e1 := hVe e (PBL.stdS S P)
    have e2 := hVe e (PBL.stdS S Q)
    unfold KB.Pl.V at e1 e2
    rw [e1, e2, inner_smul_left, inner_smul_right, hsLE_apply, hsLE_apply]
    have hin : ⟪B.hsVec (((p v).TP.E ρ).comp ((p v).V (Fe e) (PBL.stdS S Q))),
        B.hsVec (((p v).TP.E ρ).comp ((p v).V (Fe e) (PBL.stdS S P)))⟫_ℂ =
        B.hsInner (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ (Fe e) (PBL.stdS S P)))
          (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ (Fe e) (PBL.stdS S Q))) := rfl
    rw [hin]
    set TT := Formalism.QuantumDeterminants.Tz S.G.k S.G.r (p v).T.base.z * Formalism.QuantumDeterminants.Tz S.G.k S.G.r (p v).T.base.z' with hTTdef
    by_cases h1 : 0 < D.ptG TT S.G.r (PBL.stdS S P)
    · by_cases h2 : 0 < D.ptG TT S.G.r (PBL.stdS S Q)
      · have hw1 : 0 ≤ Top.wPt TT S.G.r (PBL.stdS S P) ^ a.length :=
          pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h1.le) _
        have hw2 : 0 ≤ Top.wPt TT S.G.r (PBL.stdS S Q) ^ a.length :=
          pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h2.le) _
        have hd1 : Top.dH (D.parOf S v) (p v).l0 TT a (PBL.stdS S P) e ρ =
            √(Top.wPt TT S.G.r (PBL.stdS S P) ^ a.length) * √((Top.cW (D.parOf S v) (p v).l0 a e ρ).re) := by
          unfold Top.dH; exact Real.sqrt_mul hw1 _
        have hd2 : Top.dH (D.parOf S v) (p v).l0 TT a (PBL.stdS S Q) e ρ =
            √(Top.wPt TT S.G.r (PBL.stdS S Q) ^ a.length) * √((Top.cW (D.parOf S v) (p v).l0 a e ρ).re) := by
          unfold Top.dH; exact Real.sqrt_mul hw2 _
        rw [hd1, hd2]
        unfold omN PBL.del2
        rw [← hTT]
        simp only [Complex.conj_ofReal]
        push_cast
        ring
      · rw [PBL.vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, PBL.hsInner_zero_right']
        simp
    · rw [PBL.vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, PBD.hsInner_zero_left]
      simp
  · rw [PBL.gN_setC_zero hB F v ε (S.G.r + 1) a P Q hloc]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hPl : D.IsLocPt P (S.G.r + 1)
    · have hQl : ¬ D.IsLocPt Q (S.G.r + 1) := fun h => hloc ⟨hPl, h⟩
      have hQs : ¬ D.IsLocPt (PBL.stdS S Q) (S.G.r + 1) := fun h =>
        hQl ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h)
      unfold KB.Pl.V
      dsimp only
      rw [vecV_nonloc (p v).T.base (p v).ν' (p v).m₀ (Fe i.1) (PBL.stdS S Q) hQs, map_zero, smul_zero,
        inner_zero_left, mul_zero]
    · have hPs : ¬ D.IsLocPt (PBL.stdS S P) (S.G.r + 1) := fun h =>
        hPl ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h)
      unfold KB.Pl.V
      dsimp only
      rw [vecV_nonloc (p v).T.base (p v).ν' (p v).m₀ (Fe i.1) (PBL.stdS S P) hPs, map_zero, smul_zero,
        inner_zero_right, mul_zero]

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end

