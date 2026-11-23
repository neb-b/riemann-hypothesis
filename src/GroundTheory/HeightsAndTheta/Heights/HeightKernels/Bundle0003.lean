module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

theorem sq_coord_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (hY : Y.PosDef)
    (i : ι) (v : ι → ℝ) : v i ^ 2 ≤ Y⁻¹ i i * qf Y v := by
  have hU : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hsymm : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set w : ι → ℝ := Y⁻¹ *ᵥ Pi.single i 1 with hw
  have hYw : Y *ᵥ w = Pi.single i 1 := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have hwY : ∀ x : ι → ℝ, w ⬝ᵥ (Y *ᵥ x) = x i := by
    intro x
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hYw]
    simp [dotProduct, Pi.single_apply]
  have hxY : ∀ x : ι → ℝ, x ⬝ᵥ (Y *ᵥ w) = x i := by
    intro x
    rw [hYw]
    simp [dotProduct, Pi.single_apply]
  have hwi : w i = Y⁻¹ i i := by
    rw [hw]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hpos : 0 < Y⁻¹ i i := hY.inv.diag_pos
  have hnn : ∀ t : ℝ, 0 ≤ qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
    intro t
    have h0 : 0 ≤ (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) := by
      have := hY.posSemidef.dotProduct_mulVec_nonneg (v - t • w)
      simpa using this
    have hexp : (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) =
        qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hwY, hwY, hxY, hwi]
      simp only [qf]
      ring
    linarith
  have h := hnn (v i / Y⁻¹ i i)
  have hne : Y⁻¹ i i ≠ 0 := ne_of_gt hpos
  have e : qf Y v - 2 * (v i / Y⁻¹ i i) * v i + (v i / Y⁻¹ i i) ^ 2 * Y⁻¹ i i =
      qf Y v - v i ^ 2 / Y⁻¹ i i := by
    field_simp
    ring
  rw [e] at h
  have h2 : v i ^ 2 / Y⁻¹ i i ≤ qf Y v := by linarith
  rwa [div_le_iff₀ hpos, mul_comm] at h2

end KCoord

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

variable {m n : Type*} [Fintype m] [Fintype n]

theorem posDef_fromBlocks_diag {A : Matrix m m ℝ} {D : Matrix n n ℝ} (hA : A.PosDef)
    (hD : D.PosDef) : (fromBlocks A 0 0 D).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hD.1) fun x hx => ?_
  have hsplit : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hsplit]
  have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  by_cases hl : x ∘ Sum.inl = 0
  · have hr : x ∘ Sum.inr ≠ 0 := by
      intro hr
      apply hx
      funext i
      cases i with
      | inl i => exact congrFun hl i
      | inr i => exact congrFun hr i
    have := hD.dotProduct_mulVec_pos hr
    linarith
  · have := hA.dotProduct_mulVec_pos hl
    linarith

end KCoord

variable {g : ℕ}

namespace KCoord

def unip (X : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks 1 X 0 1

noncomputable def diagInv (Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ 0 0 Y

theorem siegelGram_eq (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    siegelGram X Y = (unip X)ᵀ * diagInv Y * unip X := by
  have hXt : Xᵀ = X := hX
  simp [siegelGram, unip, diagInv, fromBlocks_transpose, fromBlocks_multiply, hXt, add_comm]

theorem unip_mem (X : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    unip X ∈ symplecticGroup (Fin g) ℝ := by
  have hXt : Xᵀ = X := hX
  rw [SymplecticGroup.mem_iff]
  simp [unip, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hXt]

theorem diagInv_mem (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    diagInv Y ∈ symplecticGroup (Fin g) ℝ := by
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hYt : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hYit : Y⁻¹ᵀ = Y⁻¹ := by rw [Matrix.transpose_nonsing_inv, hYt]
  rw [SymplecticGroup.mem_iff]
  simp [diagInv, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hYt, hYit,
    Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet]

theorem unip_isUnit (X : Matrix (Fin g) (Fin g) ℝ) : IsUnit (unip X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [unip]

theorem siegelGram_mem_posDef (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
    siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef := by
  rw [siegelGram_eq X Y hX]
  refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _
    (SymplecticGroup.transpose_mem (unip_mem X hX)) (diagInv_mem Y hY)) (unip_mem X hX), ?_⟩
  have hD : (diagInv Y).PosDef := posDef_fromBlocks_diag hY.inv hY
  have hinj : Function.Injective (unip X).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (unip_isUnit X)
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

end KCoord

namespace KCoord

theorem existsUnique_siegelGram (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)
    (hS : G ∈ symplecticGroup (Fin g) ℝ) (hG : G.PosDef) :
    ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
      XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2 := by
  have hGt : Gᵀ = G := by
    have := hG.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hS' := hS
  rw [SymplecticGroup.mem_iff, hGt] at hS'
  have hGb := Matrix.fromBlocks_toBlocks G
  set A := G.toBlocks₁₁ with hAdef
  set B := G.toBlocks₁₂ with hBdef
  set C := G.toBlocks₂₁ with hCdef
  set D := G.toBlocks₂₂ with hDdef
  have hGt' := hGt
  rw [← hGb] at hS' hGt'
  simp only [fromBlocks_transpose, Matrix.J, fromBlocks_multiply] at hS' hGt'
  obtain ⟨e1, e2, -, -⟩ := Matrix.fromBlocks_inj.mp hS'
  obtain ⟨t1, -, t3, -⟩ := Matrix.fromBlocks_inj.mp hGt'
  simp at e1 e2
  have hBA : B * A = A * C := by
    have := e1
    rwa [add_neg_eq_zero] at this
  have hAD : A * D = 1 + B * B := by
    have h1 : A * D = B * B - (B * B + -(A * D)) := by abel
    rw [h1, e2]; abel
  have hA : A.PosDef := hG.submatrix Sum.inl_injective
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hAiA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAdet
  have hAAi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAdet
  have hAit : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, t1]
  have hCt : Bᵀ = C := t3
  have k : A⁻¹ * B = C * A⁻¹ := by
    calc A⁻¹ * B = A⁻¹ * B * (A * A⁻¹) := by rw [hAAi, Matrix.mul_one]
      _ = A⁻¹ * (B * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * C) * A⁻¹ := by rw [hBA]
      _ = C * A⁻¹ := by rw [← Matrix.mul_assoc A⁻¹ A C, hAiA, Matrix.one_mul]
  have hX : (A⁻¹ * B).IsSymm := by
    show (A⁻¹ * B)ᵀ = A⁻¹ * B
    rw [Matrix.transpose_mul, hAit, hCt, k]
  have hY : (A⁻¹).PosDef := hA.inv
  have hYinv : (A⁻¹)⁻¹ = A := Matrix.nonsing_inv_nonsing_inv A hAdet
  refine ⟨(A⁻¹ * B, A⁻¹), ⟨hX, hY, ?_⟩, ?_⟩
  · show G = siegelGram (A⁻¹ * B) A⁻¹
    rw [siegelGram, hYinv]
    conv_lhs => rw [← hGb]
    congr 1
    · rw [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
    · rw [k, Matrix.mul_assoc, hAiA, Matrix.mul_one]
    · have hD : D = A⁻¹ * (1 + B * B) := by
        rw [← hAD, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
      rw [hD, k, Matrix.mul_add, Matrix.mul_one]
      congr 1
      calc A⁻¹ * (B * B) = A⁻¹ * B * (A * A⁻¹) * B := by
            rw [hAAi, Matrix.mul_one, Matrix.mul_assoc]
        _ = C * A⁻¹ * A * A⁻¹ * B := by rw [← k]; simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (A⁻¹ * B) := by simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (C * A⁻¹) := by rw [k]
  · rintro ⟨X', Y'⟩ ⟨hX', hY', hG'⟩
    have hY'det : IsUnit Y'.det := (Matrix.isUnit_iff_isUnit_det Y').1 hY'.isUnit
    have h11 : A = Y'⁻¹ := by
      rw [hAdef, hG']; simp [siegelGram]
    have h12 : B = Y'⁻¹ * X' := by
      rw [hBdef, hG']; simp [siegelGram]
    have hYY : Y' = A⁻¹ := by
      rw [h11, Matrix.nonsing_inv_nonsing_inv Y' hY'det]
    have hXX : X' = A⁻¹ * B := by
      rw [h12, ← hYY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y' hY'det, Matrix.one_mul]
    simp only [Prod.mk.injEq]
    exact ⟨hXX, hYY⟩

end KCoord

theorem SiegelCoordinates.intersectionNumber_baseChange : SiegelCoordinates.Statement := fun _ =>
  ⟨fun X Y hX hY => KCoord.siegelGram_mem_posDef X Y hX hY,
    fun G hS hG => KCoord.existsUnique_siegelGram G hS hG⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordWeak
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace KCoord

section Mean

variable {S : Type*} [Fintype S]

theorem card_pos_real [Nonempty S] : (0 : ℝ) < Fintype.card S := by
  exact_mod_cast Fintype.card_pos

theorem finMean_mono [Nonempty S] {f h : S → ℝ} (hfh : ∀ s, f s ≤ h s) : finMean f ≤ finMean h :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => hfh s) card_pos_real.le

theorem finMean_add (f h : S → ℝ) : finMean (fun s => f s + h s) = finMean f + finMean h := by
  simp [finMean, Finset.sum_add_distrib, add_div]

theorem finMean_sub (f h : S → ℝ) : finMean (fun s => f s - h s) = finMean f - finMean h := by
  simp [finMean, Finset.sum_sub_distrib, sub_div]

theorem finMean_const_mul (c : ℝ) (f : S → ℝ) : finMean (fun s => c * f s) = c * finMean f := by
  simp [finMean, ← Finset.mul_sum, mul_div_assoc]

theorem finMean_const [Nonempty S] (c : ℝ) : finMean (fun _ : S => c) = c := by
  have h := (card_pos_real (S := S)).ne'
  simp only [finMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Mean

theorem mul_log_le (G a : ℝ) (hG : 0 ≤ G) (ha : 0 < a) :
    G * log (1 + a) ≤ π / 192 * a ^ 2 + 48 / π * G ^ 2 := by
  have h1 : log (1 + a) ≤ a := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + a by linarith)
    linarith
  have h2 : G * log (1 + a) ≤ G * a := mul_le_mul_of_nonneg_left h1 hG
  have hpi : 0 < π := Real.pi_pos
  have h3 : π / 192 * a ^ 2 + 48 / π * G ^ 2 - G * a = (π * a - 96 * G) ^ 2 / (192 * π) := by
    field_simp
    ring
  have h4 : 0 ≤ (π * a - 96 * G) ^ 2 / (192 * π) := by positivity
  linarith

theorem posLog_le_half_log (ρ : ℝ) (hρ : 0 < ρ) :
    posLog (1 / ρ) ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by
  have hx : 0 < 1 + (ρ ^ 2)⁻¹ := by positivity
  have h0 : 0 ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by
    have : 0 ≤ log (1 + (ρ ^ 2)⁻¹) := Real.log_nonneg (by
      have : 0 ≤ (ρ ^ 2)⁻¹ := by positivity
      linarith)
    linarith
  have h1 : log (1 / ρ) ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by
    have e : log (1 / ρ) = 1 / 2 * log ((ρ ^ 2)⁻¹) := by
      rw [one_div, Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    rw [e]
    have : log ((ρ ^ 2)⁻¹) ≤ log (1 + (ρ ^ 2)⁻¹) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  simp only [Real.posLog]
  exact max_le h0 h1

end KCoord

theorem WeakMatrixArithmetic.intersectionNumber_baseChange : WeakMatrixArithmetic.Statement := by
  intro C₀ hC₀
  refine ⟨64 * (33 + C₀), by positivity, ?_⟩
  intro g _ S _ _ ρ Φ hρ hΦ hmean
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hG : (0 : ℝ) ≤ g := by linarith
  set L := log (2 * (g : ℝ)) with hL
  have hLge : log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : (1 / 2 : ℝ) < log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hLpos : 1 / 2 < L := by linarith
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi : 0 < π := Real.pi_pos
  set x : S → ℝ := fun s => (ρ s ^ 2)⁻¹ with hx
  set E : S → ℝ := fun s => g * log (1 + 1 / ρ s) + C₀ * g * L with hE
  set K : ℝ := 48 / π * (g : ℝ) ^ 2 + C₀ * g * L with hK

  have hEx : ∀ s, E s ≤ π / 192 * x s + K := by
    intro s
    have h := KCoord.mul_log_le (g : ℝ) (1 / ρ s) hG (by have := (hρ s).1; positivity)
    have e : (1 / ρ s) ^ 2 = x s := by simp [hx, one_div, inv_pow]
    rw [e] at h
    simp only [hE, hK]
    linarith

  have hK' : K ≤ (32 + C₀) * ((g : ℝ) ^ 2 * L) := by
    have h1 : 48 / π * (g : ℝ) ^ 2 ≤ 32 * ((g : ℝ) ^ 2 * L) := by
      have hg2 : 0 ≤ (g : ℝ) ^ 2 := by positivity
      have : 48 / π ≤ 16 := by
        rw [div_le_iff₀ hpi]; linarith
      have h16 : 16 * (g : ℝ) ^ 2 ≤ 32 * ((g : ℝ) ^ 2 * L) := by nlinarith
      nlinarith
    have h2 : C₀ * g * L ≤ C₀ * ((g : ℝ) ^ 2 * L) := by
      have : (g : ℝ) * L ≤ (g : ℝ) ^ 2 * L := by
        have : (g : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this (by linarith)
      have := mul_le_mul_of_nonneg_left this hC₀
      linarith [mul_assoc C₀ (g : ℝ) L]
    simp only [hK]
    linarith
  have hgL : 0 ≤ (g : ℝ) ^ 2 * L := by have := sq_nonneg (g : ℝ); nlinarith

  have hmx : π / 192 * finMean x ≤ Φ + K := by
    have h1 : finMean (fun s => π / 96 * x s - E s) ≥ finMean (fun s => π / 192 * x s - K) :=
      KCoord.finMean_mono fun s => by have := hEx s; linarith
    have h2 : finMean (fun s => π / 192 * x s - K) = π / 192 * finMean x - K := by
      rw [KCoord.finMean_sub, KCoord.finMean_const_mul, KCoord.finMean_const]
    have h3 : finMean (fun s => π / 96 * x s - E s) ≤ Φ := hmean
    linarith
  have hmx' : finMean x ≤ 64 * (Φ + K) := by
    have : finMean x ≤ 192 / π * (Φ + K) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
      linarith
    have hΦK : 0 ≤ Φ + K := by
      have : 0 ≤ K := by simp only [hK]; positivity
      linarith
    have : 192 / π ≤ 64 := by rw [div_le_iff₀ hpi]; linarith
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  ·
    show finMean x ≤ _
    nlinarith
  ·
    show finMean E ≤ _
    have h0 : finMean E ≤ finMean (fun s => π / 192 * x s + K) := KCoord.finMean_mono hEx
    have h0' : finMean (fun s => π / 192 * x s + K) = π / 192 * finMean x + K := by
      rw [KCoord.finMean_add, KCoord.finMean_const_mul, KCoord.finMean_const]
    have h1 : finMean E ≤ π / 192 * finMean x + K := h0.trans h0'.le
    nlinarith
  ·
    have hpt : ∀ s, posLog (1 / ρ s) ≤ 1 / 2 * log (1 + x s) := fun s =>
      KCoord.posLog_le_half_log (ρ s) (hρ s).1
    have h1 := KCoord.finMean_mono hpt
    rw [KCoord.finMean_const_mul] at h1
    have hj : finMean (fun s => log (1 + x s)) ≤ log (1 + finMean x) := by
      have hcard := (KCoord.card_pos_real (S := S))
      have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := Finset.univ)
        (w := fun _ : S => (1 : ℝ) / Fintype.card S) (p := fun s => 1 + x s)
        (fun _ _ => by positivity)
        (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
        (fun s _ => by
          show (0 : ℝ) < 1 + x s
          have : 0 ≤ x s := by simp only [hx]; positivity
          linarith)
      simp only [smul_eq_mul] at hJ
      have e1 : ∑ s, 1 / (Fintype.card S : ℝ) * log (1 + x s) = finMean fun s => log (1 + x s) := by
        simp [finMean, ← Finset.mul_sum, div_eq_inv_mul]
      have e2 : ∑ s, 1 / (Fintype.card S : ℝ) * (1 + x s) = 1 + finMean x := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, finMean]
        field_simp
      rw [e1, e2] at hJ
      exact hJ
    linarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHadamardPSD
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset
open scoped ComplexOrder

namespace HadamardPSDAux

theorem det_eq_zero_of_diag_eq_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    {i : Fin n} (hi : A i i = 0) : A.det = 0 := by
  have h0 : star (Pi.single i (1 : ℂ)) ⬝ᵥ A *ᵥ Pi.single i 1 = 0 := by
    simpa using hi
  have hcol := (hA.dotProduct_mulVec_zero_iff).mp h0
  refine det_eq_zero_of_column_eq_zero i fun k => ?_
  simpa using congrFun hcol k

theorem le_of_diag_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hpos : ∀ i, 0 < (A i i).re) : ‖A.det‖ ≤ ∏ i, ‖A i i‖ := by
  set d : Fin n → ℝ := fun i => (A i i).re with hd_def
  have hAd : ∀ i, A i i = (d i : ℂ) := by
    intro i
    obtain ⟨-, him⟩ := Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))
    exact Complex.ext (by simp [d]) (by simp [← him])
  set c : Fin n → ℝ := fun i => (Real.sqrt (d i))⁻¹ with hc_def
  have hc : ∀ i, 0 < c i := fun i => inv_pos.mpr (Real.sqrt_pos.mpr (hpos i))
  have hcd : ∀ i, c i * c i * d i = 1 := by
    intro i
    simp only [c]
    rw [← mul_inv, Real.mul_self_sqrt (hpos i).le, inv_mul_cancel₀ (hpos i).ne']
  obtain ⟨D, hD_def⟩ : ∃ D : Matrix (Fin n) (Fin n) ℂ, D = diagonal fun i => (c i : ℂ) := ⟨_, rfl⟩
  have hD : Dᴴ = D := by simp [hD_def, diagonal_conjTranspose]
  have hB : (D * A * D).PosSemidef := by simpa [hD] using hA.conjTranspose_mul_mul_same D
  have hBdiag : ∀ i, (D * A * D) i i = 1 := by
    intro i
    simp only [hD_def, diagonal_mul, mul_diagonal, hAd]
    exact_mod_cast (by linarith [hcd i] : c i * d i * c i = 1)
  have htr : ∑ i, hB.1.eigenvalues i = n := by
    have h := hB.1.trace_eq_sum_eigenvalues
    simp only [Matrix.trace, Matrix.diag_apply, hBdiag] at h
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    simpa using (congrArg Complex.re h).symm
  have hprod : ∏ i, hB.1.eigenvalues i ≤ 1 := by
    calc ∏ i, hB.1.eigenvalues i ≤ ∏ i, Real.exp (hB.1.eigenvalues i - 1) :=
          prod_le_prod₀ (fun i _ => hB.eigenvalues_nonneg i)
            (fun i _ => by linarith [Real.add_one_le_exp (hB.1.eigenvalues i - 1)])
      _ = Real.exp (∑ i, (hB.1.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
      _ = 1 := by simp [sum_sub_distrib, htr]
  have hnormB : ‖(D * A * D).det‖ ≤ 1 := by
    have h1 : (D * A * D).det = ((∏ i, hB.1.eigenvalues i : ℝ) : ℂ) := by
      rw [hB.1.det_eq_prod_eigenvalues]; push_cast; rfl
    rw [h1, Complex.norm_of_nonneg (prod_nonneg fun i _ => hB.eigenvalues_nonneg i)]
    exact hprod
  have hdetB : (D * A * D).det = (((∏ i, c i) ^ 2 : ℝ) : ℂ) * A.det := by
    simp only [det_mul, hD_def, det_diagonal]
    push_cast
    ring
  have key : ‖(D * A * D).det‖ * ∏ i, d i = ‖A.det‖ := by
    rw [hdetB, norm_mul, Complex.norm_of_nonneg (by positivity)]
    calc (∏ i, c i) ^ 2 * ‖A.det‖ * ∏ i, d i = ‖A.det‖ * ∏ i, (c i * c i * d i) := by
          rw [prod_mul_distrib, prod_mul_distrib]; ring
      _ = ‖A.det‖ := by simp [hcd]
  have hnd : ∀ i, ‖A i i‖ = d i := fun i => by rw [hAd i, Complex.norm_of_nonneg (hpos i).le]
  rw [← key, prod_congr rfl fun i _ => hnd i]
  calc ‖(D * A * D).det‖ * ∏ i, d i ≤ 1 * ∏ i, d i :=
        mul_le_mul_of_nonneg_right hnormB (prod_nonneg fun i _ => (hpos i).le)
    _ = ∏ i, d i := one_mul _

end HadamardPSDAux

theorem HadamardPSD.proof : HadamardPSD.Statement := by
  intro n A hA
  by_cases h : ∃ i, A i i = 0
  · obtain ⟨i, hi⟩ := h
    rw [HadamardPSDAux.det_eq_zero_of_diag_eq_zero hA hi, norm_zero]
    exact prod_nonneg fun _ _ => norm_nonneg _
  · push Not at h
    refine HadamardPSDAux.le_of_diag_pos hA fun i => ?_
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))
    rcases hre.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (Complex.ext heq.symm him.symm) (h i)

end GroundTheory.Heights₂.Heights
end

