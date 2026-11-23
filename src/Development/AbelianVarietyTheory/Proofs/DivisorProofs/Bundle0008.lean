module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseAddLePowMulChooseAdd
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

private theorem choose_succ_mul_succ_eq_mul_choose (c n : ℕ) :
    (((c + (n + 1)).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1)
      = ((c : ℝ) + n + 1) * (((c + n).choose n : ℕ) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (c + n) n
  have h' : (c + (n + 1)).choose (n + 1) * (n + 1) = (c + n + 1) * (c + n).choose n := by
    rw [show c + (n + 1) = c + n + 1 by ring]
    linarith
  exact_mod_cast h'

theorem choose_add_le_pow_mul_choose_add (a b : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (h : (a : ℝ) ≤ b + y * (b + 1)) (n : ℕ) :
    (((a + n).choose n : ℕ) : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hA := choose_succ_mul_succ_eq_mul_choose a n
    have hB := choose_succ_mul_succ_eq_mul_choose b n
    have hCa : (0 : ℝ) ≤ (((a + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hCb : (0 : ℝ) ≤ (((b + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hlin : (a : ℝ) + n + 1 ≤ (1 + y) * ((b : ℝ) + n + 1) := by
      nlinarith [mul_nonneg hy hn]
    have hfac : (0 : ℝ) ≤ (1 + y) * ((b : ℝ) + n + 1) :=
      mul_nonneg (by linarith) (by positivity)
    have hpow : (0 : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) :=
      mul_nonneg (pow_nonneg (by linarith) n) hCb
    rw [← mul_le_mul_iff_of_pos_right hpos]
    rw [hA, mul_assoc, hB]
    calc ((a : ℝ) + n + 1) * (((a + n).choose n : ℕ) : ℝ)
        ≤ ((1 + y) * ((b : ℝ) + n + 1)) * ((1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ)) :=
          mul_le_mul hlin ih hCa hfac
      _ = (1 + y) ^ (n + 1) * (((b : ℝ) + n + 1) * (((b + n).choose n : ℕ) : ℝ)) := by ring

theorem exp_le_one_add_of_le_tenth (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 10) :
    Real.exp x ≤ 1 + 53 / 50 * x := by
  have hx : |x| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have hb := Real.exp_bound hx (n := 3) (by norm_num)
  have h2 := (abs_le.mp hb).2
  rw [abs_of_nonneg h0] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have hx2 : x ^ 2 ≤ x / 10 := by nlinarith
  have hx3 : x ^ 3 ≤ x / 100 := by nlinarith
  nlinarith

theorem choose_rank_ratio_le :
    ∀ (D T a : ℕ) (ρ : ℝ), 2 ≤ D → 20 * D ≤ T → 0 ≤ ρ → ρ ≤ 1 / 4 → (a : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) → (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) ≤ 1 / 10 → (((a + D).choose D : ℕ) : ℝ) ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) := by
  intro D T a ρ hD hT hρ0 hρ1 ha hε
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hT' : (20 : ℝ) * D ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hbD : (T - 1 - D) + D = T - 1 := by omega
  have hbR : ((T - 1 - D : ℕ) : ℝ) = T - 1 - D := by
    have h3 : (T - 1 - D) + D + 1 = T := by omega
    have h := congrArg (fun k : ℕ => (k : ℝ)) h3
    push_cast at h
    linarith
  have hρ' : 0 < 1 - ρ := by linarith
  have hTD : 0 < (T : ℝ) - D := by linarith
  have hden : 0 < (1 - ρ) * ((T : ℝ) - D) := mul_pos hρ' hTD
  have hnum0 : (0 : ℝ) ≤ 2 * D + 5 + ρ * T := by nlinarith [mul_nonneg hρ0 hTpos.le]
  have hy0 : (0 : ℝ) ≤ (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := div_nonneg hnum0 hden.le
  have hyb : (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1)
      = (2 * D + 5 + ρ * T) / (1 - ρ) := by
    rw [hbR]
    field_simp
    ring
  have hab : (a : ℝ) ≤ ((T - 1 - D : ℕ) : ℝ)
      + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1) := by
    rw [hyb, hbR]
    have key : ((T : ℝ) + D + 4) / (1 - ρ) ≤ (T - 1 - D) + (2 * D + 5 + ρ * T) / (1 - ρ) := by
      rw [div_le_iff₀ hρ', add_mul, div_mul_cancel₀ _ hρ'.ne']
      nlinarith [mul_nonneg hρ0 (by linarith : (0 : ℝ) ≤ D + 1)]
    linarith
  have h1 := choose_add_le_pow_mul_choose_add a (T - 1 - D) _ hy0 hab D
  rw [hbD] at h1
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) := Nat.cast_nonneg _
  have hDy : (D : ℝ) * ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))
      = (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by ring
  have hε0 : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by
    rw [← hDy]; exact mul_nonneg (Nat.cast_nonneg _) hy0
  have hpow : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ Real.exp ((D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) := by
    rw [← hDy, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))]) D
  have hexp := exp_le_one_add_of_le_tenth _ hε0 hε
  have hu : (57 / 80 : ℝ) * T ≤ (1 - ρ) * (T - D) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - ρ) hTD.le]
  have hnum : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) := mul_nonneg (Nat.cast_nonneg _) hnum0
  have h2 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))
      ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T) :=
    div_le_div_of_nonneg_left hnum (by positivity) hu
  have e1 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T)
      = (80 / 57) * ((D : ℝ) * (2 * D + 5) / T) + (80 / 57) * ((D : ℝ) * ρ) := by
    field_simp
  have e2 : (D : ℝ) * (2 * D + 5) / T ≤ (9 / 2) * ((D : ℝ) ^ 2 / T) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hTpos.le
  have e3 : 7 * (D : ℝ) ^ 2 / T = 7 * ((D : ℝ) ^ 2 / T) := by ring
  have hq : (0 : ℝ) ≤ (D : ℝ) ^ 2 / T := by positivity
  have hdr : (0 : ℝ) ≤ (D : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ0
  have hfin : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ 1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ) := by
    rw [e3]
    nlinarith
  calc (((a + D).choose D : ℕ) : ℝ)
      ≤ (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D * (((T - 1).choose D : ℕ) : ℝ) := h1
    _ ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hfin hC

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulOneSubLeChoose
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem choose_mul_one_sub_le_choose (N M D : ℕ) (x : ℝ) (hx : 0 ≤ x) (hDM : D ≤ M) (hMN : M ≤ N)
    (h : (N : ℝ) - M ≤ x * ((N : ℝ) - D + 1)) :
    ∀ k ≤ D, ((N.choose k : ℕ) : ℝ) * (1 - k * x) ≤ ((M.choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hkD : k ≤ D := by omega
    have ih' := ih hkD
    have hkM : k ≤ M := by omega
    have hkN : k ≤ N := by omega
    have eN : ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq N k
      rw [← Nat.cast_sub hkN]
      exact_mod_cast h
    have eM : ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq M k
      rw [← Nat.cast_sub hkM]
      exact_mod_cast h
    have hk1 : (k : ℝ) + 1 ≤ D := by exact_mod_cast hk
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
    have hA : (0 : ℝ) ≤ ((N.choose k : ℕ) : ℝ) := by positivity
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity

    have hbr : (0 : ℝ) ≤ x * ((N : ℝ) - k) + x * k * ((N : ℝ) - M) - ((N : ℝ) - M) := by
      have h1 : x * ((N : ℝ) - D + 1) ≤ x * ((N : ℝ) - k) := by
        apply mul_le_mul_of_nonneg_left _ hx
        linarith
      have h2 : 0 ≤ x * k * ((N : ℝ) - M) := by
        have : (0 : ℝ) ≤ (N : ℝ) - M := by linarith
        positivity
      linarith
    have hstep : ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x)
        ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h3 : ((N.choose k : ℕ) : ℝ) * (1 - k * x) * ((M : ℝ) - k)
          ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) :=
        mul_le_mul_of_nonneg_right ih' (by linarith)
      have h4 := mul_nonneg hA hbr
      nlinarith [h3, h4]
    have goal' : ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
        ≤ ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      rw [eM]
      calc ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
          = ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) * (1 - ((k : ℝ) + 1) * x) := by ring
        _ = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x) := by rw [eN]
        _ ≤ _ := hstep
    push_cast
    exact le_of_mul_le_mul_right goal' hpos

theorem share_bound_of_jet_count :
    ∀ (D T a : ℕ) (ρ δ d : ℝ), 2 ≤ D → D + 1 ≤ T → 0 ≤ ρ → ρ ≤ 1 / 2 → T + D + 3 ≤ a → (a : ℝ) ≤ ((T : ℝ) + D + 3) / (1 - ρ) → 0 ≤ δ → 0 ≤ d → d ≤ (((a + D).choose D : ℕ) : ℝ) * δ → (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by
  intro D T a ρ δ d hD hDT hρ0 hρ hTa ha hδ hd0 hd
  have hT1 : 1 ≤ T := by omega
  have hT : (0 : ℝ) < T := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    linarith
  have hTr : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub hT1]
    simp
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hTa' : (T : ℝ) + D + 3 ≤ a := by exact_mod_cast hTa
  have hxnn : 0 ≤ 4 * (D : ℝ) / T + ρ := by positivity

  have key := choose_mul_one_sub_le_choose (a + D) (T - 1) D (4 * (D : ℝ) / T + ρ) hxnn
    (by omega) (by omega) (by
      push_cast
      rw [hTr]
      have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
      have hamul : (a : ℝ) * (1 - ρ) ≤ (T : ℝ) + D + 3 := (le_div_iff₀ h1ρ).mp ha
      have h4 : 4 * (D : ℝ) ≤ 4 * (D : ℝ) / T * ((a : ℝ) + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hT]
        have : (0 : ℝ) ≤ 4 * D := by positivity
        nlinarith
      nlinarith [h4, hamul, hρ0, hD2]) D le_rfl
  have hc : 1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ) ≤ 1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ) := by
    have e : (D : ℝ) * (4 * (D : ℝ) / T + ρ) = 4 * ((D : ℝ) ^ 2 / T) + D * ρ := by ring
    have h1 : 0 ≤ (D : ℝ) ^ 2 / T := by positivity
    have h2 : 0 ≤ (D : ℝ) * ρ := by positivity
    rw [e]
    linarith
  have hB : (0 : ℝ) ≤ (((a + D).choose D : ℕ) : ℝ) * δ := by positivity
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by positivity
  rcases le_or_gt (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) 0 with h | h
  · have : (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hd0
    linarith
  · calc (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d
        ≤ (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_left hd h.le
      _ ≤ (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_right hc hB
      _ = ((((a + D).choose D : ℕ) : ℝ) * (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ))) * δ := by ring
      _ ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := mul_le_mul_of_nonneg_right key hδ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.DimCodim

section

attribute [local instance low] specializationOrder

theorem dim_add_le_of_le_coheight {S W : Type*} [TopologicalSpace S] [TopologicalSpace W]
    [QuasiSober S] [T0Space S] [QuasiSober W] [T0Space W] {j : W → S} (hj : Continuous j)
    (hi : Function.Injective j) (c : ℕ∞) (h : ∀ w, c ≤ Order.coheight (j w)) :
    topologicalKrullDim W + c ≤ topologicalKrullDim S := by
  have hmono : StrictMono j := by
    intro x y hxy
    refine lt_of_le_of_ne ?_ (fun hxy' => hxy.ne (hi hxy'))
    exact (show y ⤳ x from hxy.le).map hj
  rw [topologicalKrullDim, topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := W)),
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))]
  rcases isEmpty_or_nonempty W with hW | hW
  · rw [Order.krullDim_eq_bot]
    simp
  · have : Nonempty S := ⟨j hW.some⟩
    rw [Order.krullDim_eq_iSup_height_of_nonempty,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add,
      WithBot.coe_le_coe, ENat.iSup_add]
    refine iSup_le fun w => le_trans ?_
      (le_iSup (fun a : S => Order.height a + Order.coheight a) (j w))
    exact add_le_add (Order.height_le_height_apply_of_strictMono j hmono w) (h w)

end

end GlobalTheory.DimCodim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedCoverAffineNbhdMapsIntoAffine
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem closedCover_affine_nbhd_maps_into_affine :
    ∀ (Y Y₁ Y₂ X : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) [IsClosedImmersion j₁]
      [IsClosedImmersion j₂] (a₁ : Y₁ ⟶ X) (a₂ : Y₂ ⟶ X),
      (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) →
      (∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → a₁ y₁ = a₂ y₂) →
      ∀ y : Y, ∃ (W : Y.Opens) (U : X.affineOpens), IsAffineOpen W ∧ y ∈ W ∧
        j₁ ⁻¹ᵁ W ≤ a₁ ⁻¹ᵁ U.1 ∧ j₂ ⁻¹ᵁ W ≤ a₂ ⁻¹ᵁ U.1 := by
  intro Y Y₁ Y₂ X j₁ j₂ _ _ a₁ a₂ hcov hagree y
  have hinj₁ := j₁.isClosedEmbedding.injective
  have hinj₂ := j₂.isClosedEmbedding.injective

  obtain ⟨x, hx₁, hx₂⟩ : ∃ x : X, (∀ w, j₁ w = y → a₁ w = x) ∧ (∀ w, j₂ w = y → a₂ w = x) := by
    rcases hcov y with ⟨y₁, h₁⟩ | ⟨y₂, h₂⟩
    · refine ⟨a₁ y₁, fun w hw => ?_, fun w hw => ?_⟩
      · rw [hinj₁ (hw.trans h₁.symm)]
      · exact (hagree y₁ w (h₁.trans hw.symm)).symm
    · refine ⟨a₂ y₂, fun w hw => hagree w y₂ (hw.trans h₂.symm), fun w hw => ?_⟩
      rw [hinj₂ (hw.trans h₂.symm)]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  set C : Set Y := j₁.base '' ((a₁ ⁻¹ᵁ U : Set Y₁)ᶜ) ∪ j₂.base '' ((a₂ ⁻¹ᵁ U : Set Y₂)ᶜ) with hCdef
  have hC : IsClosed C :=
    (j₁.isClosedEmbedding.isClosedMap _ (a₁ ⁻¹ᵁ U).isOpen.isClosed_compl).union
      (j₂.isClosedEmbedding.isClosedMap _ (a₂ ⁻¹ᵁ U).isOpen.isClosed_compl)
  have hyC : y ∉ C := by
    rintro (⟨w, hw, hwy⟩ | ⟨w, hw, hwy⟩)
    · exact hw (by simpa [hx₁ w hwy] using hxU)
    · exact hw (by simpa [hx₂ w hwy] using hxU)
  obtain ⟨W, hW, hyW, hWC⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨Cᶜ, hC.isOpen_compl⟩) (show y ∈ Cᶜ from hyC)
  refine ⟨W, ⟨U, hU⟩, hW, hyW, ?_, ?_⟩
  · intro w hw
    by_contra hn
    exact hWC hw (Or.inl ⟨w, hn, rfl⟩)
  · intro w hw
    by_contra hn
    exact hWC hw (Or.inr ⟨w, hn, rfl⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAlgCharEqArgMulAbs
section
open NumberField

namespace GlobalTheory.Div.CMAlgChar

theorem place_factor (z : ℂ) (hz : z ≠ 0) (a b w0 : ℤ) (hab : a + b = w0) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * a - w0) *
      (((‖z‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) *
        ((‖(starRingEnd ℂ) z‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ)) =
      z ^ a * (starRingEnd ℂ z) ^ b := by
  rw [Complex.norm_conj]
  set r : ℂ := ((‖z‖ : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by simp [hr, hz]
  rw [← Complex.cpow_add _ _ hr0]
  have hsum : ((((w0 : ℝ) / 2 : ℝ)) : ℂ) + ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ((w0 : ℤ) : ℂ) := by
    push_cast; ring
  rw [hsum, Complex.cpow_intCast]
  have hc : starRingEnd ℂ z = r ^ 2 / z := by
    rw [eq_div_iff hz, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hr]
    push_cast; rfl
  rw [hc]
  subst hab
  have he : 2 * a - (a + b) = a - b := by ring
  rw [he, div_zpow, div_zpow, zpow_sub₀ hz, zpow_sub₀ hr0, zpow_add₀ hr0, pow_two, mul_zpow]
  field_simp

theorem fiber_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] [DecidableEq (E →+* ℂ)]
    [DecidableEq (InfinitePlace E)]
    (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  have h1 : InfinitePlace.mk φ = w ↔ InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
    rw [w.mk_embedding]
  rw [h1, InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [← h, ComplexEmbedding.involutive_conjugate E]
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [h, ComplexEmbedding.involutive_conjugate E]

theorem embedding_ne_conjugate {E : Type} [Field E] [IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hc := IsTotallyComplex.isComplex w
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
    ComplexEmbedding.isReal_iff] at hc
  exact hc h.symm

theorem algChar_eq_arg_mul_abs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by
  intro E _ _ _ n w0 hn k hk
  classical
  have hfib : ∀ f : (E →+* ℂ) → ℂ, ∏ φ, f φ =
      ∏ w : InfinitePlace E, (f w.embedding * f (ComplexEmbedding.conjugate w.embedding)) := by
    intro f
    rw [← Finset.prod_fiberwise Finset.univ (fun φ => InfinitePlace.mk φ) f]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [fiber_eq w, Finset.prod_pair (embedding_ne_conjugate w)]
  rw [hfib (fun φ => ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ)),
    hfib (fun φ => φ k ^ n φ), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hz : w.embedding k ≠ 0 := (map_ne_zero _).2 hk
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact place_factor _ hz _ _ _ (hn _)

end GlobalTheory.Div.CMAlgChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesProdOneAddMul
section
open MvPolynomial

namespace GlobalTheory

theorem coeff_allOnes_prod_one_add_mul {σ : Type} {L : ℕ} (m : Fin L → MvPolynomial σ ℂ)
    (a : MvPolynomial σ ℂ) :
    AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ ((∏ i, (1 + MvPolynomial.X (Sum.inl i) *
        MvPolynomial.rename Sum.inr (m i))) * MvPolynomial.rename Sum.inr a))
      (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) = (∏ i, m i) * a := by
  have hr : ∀ q : MvPolynomial σ ℂ, sumAlgEquiv ℂ (Fin L) σ (rename Sum.inr q) = C q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [sumAlgEquiv_C_inl]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p c hp => rw [map_mul, map_mul, hp, rename_X, sumAlgEquiv_X_inr, map_mul]
  have hx : ∀ i : Fin L, sumAlgEquiv ℂ (Fin L) σ (X (Sum.inl i)) = X i := fun i =>
    sumAlgEquiv_X_inl ℂ (Fin L) σ i
  have cmC : ∀ {τ : Type} (n : τ →₀ ℕ) (p : MvPolynomial τ (MvPolynomial σ ℂ)) (c : MvPolynomial σ ℂ),
      AddMonoidAlgebra.coeff (p * C c) n = AddMonoidAlgebra.coeff p n * c := by
    intro τ n p c; rw [mul_comm, coeff_C_mul, mul_comm]
  set e : Fin L →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ) with he
  have hmono : ∀ t : Finset (Fin L),
      AddMonoidAlgebra.coeff (∏ i ∈ t, (X i * C (m i) : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) e =
        if t = Finset.univ then ∏ i, m i else 0 := by
    intro t
    rw [Finset.prod_mul_distrib, ← map_prod, cmC]
    have hX : (∏ i ∈ t, (X i : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) =
        monomial (∑ i ∈ t, Finsupp.single i 1) 1 := by
      rw [monomial_sum_one]; rfl
    rw [hX, coeff_monomial]
    by_cases ht : t = Finset.univ
    · subst ht
      have : (∑ i ∈ (Finset.univ : Finset (Fin L)), Finsupp.single i 1) = e := by
        ext j; simp [he, Finsupp.finsetSum_apply, Finsupp.single_apply]
      simp [this]
    · obtain ⟨j, hj⟩ : ∃ j, j ∉ t := by
        by_contra h; push_neg at h; exact ht (Finset.eq_univ_iff_forall.mpr h)
      have : (∑ i ∈ t, Finsupp.single i 1) ≠ e := by
        intro h
        have := congrArg (fun f => f j) h
        simp [he, Finsupp.finsetSum_apply, Finsupp.single_apply, hj] at this
      simp [this, ht]
  rw [map_mul, hr, cmC, map_prod]
  simp_rw [map_add (f := _), map_one, map_mul, hr, hx]
  rw [Finset.prod_one_add, coeff_sum, Finset.sum_eq_single Finset.univ]
  · rw [hmono]; simp
  · intro t _ ht; rw [hmono, if_neg ht]
  · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSum
section
namespace GlobalTheory.ColumnSumLemma
open Matrix
theorem colSum {A : Type} [CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (a : Fin r → A) :
    Matrix.mulVec C a = ∑ i, a i • Matrix.transpose C i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem main : ∀ {A : Type} [inst : CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A), y ∈ Submodule.span A ((fun (i : Fin r) ↦ Matrix.transpose C i) '' I) ↔ ∃ (a : Fin r → A), (∀ l ∉ I, a l = (0 : A)) ∧ Matrix.mulVec C a = y := by
  intro A _ n r C I y
  rw [Finsupp.mem_span_image_iff_linearCombination]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, fun k hk => ?_, ?_⟩
    · exact Finsupp.notMem_support_iff.mp (fun h => hk (hl h))
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i; simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm a, fun k hk => ?_, ?_⟩
    · by_contra h
      exact (Finsupp.mem_support_iff.mp hk) (ha k h)
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i; simp
end GlobalTheory.ColumnSumLemma
end

