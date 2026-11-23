module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlaceStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLattice_carry_iff_forall_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ y : GL (Fin n) (E ⊗[F] Ad F), (∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M) ↔ ∀ v : HeightOneSpectrum (𝓞 F), ∀ x, x ∈ loc v L ↔ (bc (prV (E := E) v) y).1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.Carry.carry_iff | exact GlobalTheory.St.G.Carry.carry_iff | (intros; apply GlobalTheory.St.G.Carry.carry_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeArithmetic
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.AmpArith

theorem v_part (k r f j : ℕ) (v : ℝ) (hr : 1 ≤ r) (hv : 1 ≤ v) :
    v ^ (k * (r - j) * f) *
        ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f
      ≤ 2 ^ (r ^ 2 * f) := by
  have hv0 : v ≠ 0 := by positivity
  have h2v : 0 ≤ 2 * v := by positivity
  have hexp : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  have hneg : (2 * v) ^ (-((r : ℝ) * k)) = ((2 * v) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg h2v, show ((r : ℝ) * k) = ((r * k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have key : ((2 * v) ^ (r * k))⁻¹ * 1 * (2 : ℝ) ^ (r * k + r ^ 2) = 2 ^ (r ^ 2) / v ^ (r * k) := by
    rw [mul_pow, pow_add]
    field_simp
  have hle : v ^ (k * (r - j) * f) ≤ v ^ (r * k * f) := by
    apply pow_le_pow_right₀ hv
    have : r - j ≤ r := Nat.sub_le r j
    calc k * (r - j) * f ≤ k * r * f := by gcongr
    _ = r * k * f := by ring
  rw [hneg, hexp, key, div_pow, ← pow_mul, ← pow_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
  calc v ^ (k * (r - j) * f) * 2 ^ (r ^ 2 * f) ≤ v ^ (r * k * f) * 2 ^ (r ^ 2 * f) := by gcongr
  _ = 2 ^ (r ^ 2 * f) * v ^ (r * k * f) := by ring

theorem exponent_bound (CH C R F : ℝ) (hCH : 0 ≤ CH) (hC : 100 * (CH + 10) ≤ C) (hR : 1 ≤ R)
    (hF : 0 ≤ F) :
    R ^ 2 * F + 3 * (2 * (R + 1) ^ 2 * F) + 3 * (2 * (R + 1) ^ 2 * F)
        + ((2 * R + 2) + 3 + CH * (2 * R + 2)) * (80 * R ^ 4 * F)
      ≤ C * (2 * R + 2) ^ 2 * F * (C * R ^ 4) := by
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR4 : R ^ 2 ≤ R ^ 4 := by nlinarith
  have hR41 : 1 ≤ R ^ 4 := le_trans hR2 hR4
  have hS : 1 ≤ (R + 1) ^ 2 := by nlinarith
  have hP0 : 0 ≤ R ^ 4 * (R + 1) ^ 2 := by positivity
  have e1 : R ^ 2 ≤ R ^ 4 * (R + 1) ^ 2 := by
    calc R ^ 2 ≤ R ^ 4 := hR4
    _ = R ^ 4 * 1 := by ring
    _ ≤ R ^ 4 * (R + 1) ^ 2 := by gcongr
  have e2 : (R + 1) ^ 2 ≤ R ^ 4 * (R + 1) ^ 2 := by
    calc (R + 1) ^ 2 = 1 * (R + 1) ^ 2 := by ring
    _ ≤ R ^ 4 * (R + 1) ^ 2 := by gcongr
  have e3 : R ^ 4 * (2 * R + 5) ≤ 5 * (R ^ 4 * (R + 1) ^ 2) := by
    have : 2 * R + 5 ≤ 5 * (R + 1) ^ 2 := by nlinarith
    calc R ^ 4 * (2 * R + 5) ≤ R ^ 4 * (5 * (R + 1) ^ 2) := by gcongr
    _ = 5 * (R ^ 4 * (R + 1) ^ 2) := by ring
  have e4 : R ^ 4 * (2 * R + 2) ≤ 2 * (R ^ 4 * (R + 1) ^ 2) := by
    have : 2 * R + 2 ≤ 2 * (R + 1) ^ 2 := by nlinarith
    calc R ^ 4 * (2 * R + 2) ≤ R ^ 4 * (2 * (R + 1) ^ 2) := by gcongr
    _ = 2 * (R ^ 4 * (R + 1) ^ 2) := by ring
  have hC1 : 1000 ≤ C := by linarith
  have hCC : 413 + 160 * CH ≤ 4 * C ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left e1 hF, mul_le_mul_of_nonneg_left e2 hF,
    mul_le_mul_of_nonneg_left e3 hF, mul_le_mul_of_nonneg_left e4 (mul_nonneg hF hCH),
    mul_le_mul_of_nonneg_left hCC (mul_nonneg hF hP0)]

theorem b_part (CH C : ℝ) (hCH : 0 ≤ CH) (hC : 100 * (CH + 10) ≤ C) (r m f : ℕ) (b v : ℝ)
    (hm : m = 2 * r + 2) (hr : 1 ≤ r) (hb : 2 ≤ b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) :
    2 ^ (r ^ 2 * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)
        * (8 * r * b ^ (CH * m)) ^ (80 * r ^ 4 * f)
      ≤ (b ^ (C * (m : ℝ) ^ 2 * f)) ^ (C * (r : ℝ) ^ 4) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hmR : (m : ℝ) = 2 * r + 2 := by rw [hm]; push_cast; ring
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have f1 : (2 : ℝ) ^ (r ^ 2 * f) ≤ b ^ ((r : ℝ) ^ 2 * f) := by
    rw [show ((r : ℝ) ^ 2 * f) = ((r ^ 2 * f : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hb _
  have h8v : 8 * v ≤ b ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h4 : 4 ≤ b ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hb0.le]
  have f2 : (8 * v) ^ (2 * (r + 1) ^ 2 * f) ≤ b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f)) := by
    rw [show (3 * (2 * ((r : ℝ) + 1) ^ 2 * f)) = 3 * ((2 * (r + 1) ^ 2 * f : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_mul_natCast hb0.le]
    exact pow_le_pow_left₀ (by linarith) h8v _
  have hn : 8 * r ≤ 2 ^ (m + 3) := by
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : 2 ^ r ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add]
    omega
  have h8r : 8 * (r : ℝ) ≤ b ^ ((m : ℝ) + 3) := by
    rw [show ((m : ℝ) + 3) = ((m + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    calc 8 * (r : ℝ) = ((8 * r : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ (m + 3) : ℕ) : ℝ) := by exact_mod_cast hn
    _ = (2 : ℝ) ^ (m + 3) := by push_cast; ring
    _ ≤ b ^ (m + 3) := pow_le_pow_left₀ (by norm_num) hb _
  have h3 : 8 * (r : ℝ) * b ^ (CH * m) ≤ b ^ ((m : ℝ) + 3 + CH * m) := by
    rw [Real.rpow_add hb0]
    exact mul_le_mul_of_nonneg_right h8r (Real.rpow_nonneg hb0.le _)
  have f3 : (8 * (r : ℝ) * b ^ (CH * m)) ^ (80 * r ^ 4 * f)
      ≤ b ^ (((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
    rw [Real.rpow_mul_natCast hb0.le ((m : ℝ) + 3 + CH * m) (80 * r ^ 4 * f)]
    exact pow_le_pow_left₀ (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) h3 _
  have p2 : 0 ≤ (8 * v) ^ (2 * (r + 1) ^ 2 * f) := pow_nonneg (by linarith) _
  have hE := exponent_bound CH C (r : ℝ) (f : ℝ) hCH hC hr1 (Nat.cast_nonneg f)
  calc
    _ ≤ b ^ ((r : ℝ) ^ 2 * f) * b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f))
        * b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f))
        * b ^ (((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
      apply mul_le_mul _ f3 (pow_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) _)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hb0.le _))
          (Real.rpow_nonneg hb0.le _))
      apply mul_le_mul _ f2 p2 (mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hb0.le _))
      exact mul_le_mul f1 f2 p2 (Real.rpow_nonneg hb0.le _)
  _ = b ^ ((r : ℝ) ^ 2 * f + 3 * (2 * ((r : ℝ) + 1) ^ 2 * f) + 3 * (2 * ((r : ℝ) + 1) ^ 2 * f)
        + ((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
      rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
  _ ≤ b ^ (C * (m : ℝ) ^ 2 * f * (C * (r : ℝ) ^ 4)) := by
      apply Real.rpow_le_rpow_of_exponent_le hb1
      rw [hmR]; push_cast; linarith [hE]
  _ = _ := Real.rpow_mul hb0.le _ _

theorem regroup {A B D G Pi H T G' Y U : ℝ} (hA : 0 ≤ A * D) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hG0 : 0 ≤ G) (hPi : 0 ≤ Pi) (hT : 0 ≤ T) (hU : A * D ≤ U) (hY : U * B * B * H ≤ Y)
    (hG : G ≤ G') : A * B * B * D * (G * Pi * H * T) ≤ G' * Pi * Y * T := by
  have hU0 : 0 ≤ U := le_trans hA hU
  have hBBH : 0 ≤ B * B * H := mul_nonneg (mul_nonneg hB hB) hH
  have hGPT : 0 ≤ G * Pi * T := mul_nonneg (mul_nonneg hG0 hPi) hT
  have hY0 : 0 ≤ Y := le_trans (mul_nonneg (mul_nonneg (mul_nonneg hU0 hB) hB) hH) hY
  calc A * B * B * D * (G * Pi * H * T) = (A * D) * (B * B * H) * (G * Pi * T) := by ring
  _ ≤ U * (B * B * H) * (G * Pi * T) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hU hBBH) hGPT
  _ = (U * B * B * H) * (G * Pi * T) := by ring
  _ ≤ Y * (G * Pi * T) := mul_le_mul_of_nonneg_right hY hGPT
  _ ≤ Y * (G' * Pi * T) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG hPi) hT) hY0
  _ = G' * Pi * Y * T := by ring

end GlobalTheory.AmpArith


open GlobalTheory.AmpArith in
theorem GlobalTheory.amplitude_arithmetic : ∀ CH : ℝ, 0 ≤ CH → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (k r m f j : ℕ) (b v Del S Cs P : ℝ), m = 2 * r + 2 → 1 ≤ j → j ≤ r → r + 2 ≤ k → 1 ≤ f → 2 ≤ b → 1 ≤ v → 2 * v ≤ b → 0 < P → Del = P ^ 2 → 1 ≤ S → (v ^ (k * (r - j) * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) * (8 * v) ^ (2 * (r + 1) ^ 2 * f) * ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * ((16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j) * f) * (P ^ (k - 1 - j))⁻¹ * (8 * r * b ^ (CH * m)) ^ (80 * r ^ 4 * f) * S ^ (-(Cs * k))) ≤ (C / k) ^ ((j : ℝ) * ((k : ℝ) - 1 - j) * f) * Del ^ (-(((k : ℝ) - 1 - j) / 2)) * (b ^ (C * (m : ℝ) ^ 2 * f)) ^ (C * (r : ℝ) ^ 4) * S ^ (-(Cs * k)) := by
  intro CH hCH
  refine ⟨100 * (CH + 10), ?_⟩
  intro C hC k r m f j b v Del S Cs P hm hj1 hjr hrk hf hb hv hvb hP hDel hS
  have hv0 : 0 ≤ v := by linarith
  have hb0 : 0 < b := by linarith
  have hr : 1 ≤ r := le_trans hj1 hjr
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hcast : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
    rw [Nat.cast_sub (by omega : j ≤ k - 1), Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hPi : Del ^ (-(((k : ℝ) - 1 - j) / 2)) = (P ^ (k - 1 - j))⁻¹ := by
    rw [hDel, ← Real.rpow_natCast P 2, ← Real.rpow_mul hP.le,
      show ((2 : ℕ) : ℝ) * (-(((k : ℝ) - 1 - j) / 2)) = -(((k - 1 - j : ℕ) : ℝ)) by
        rw [hcast]; push_cast; ring,
      Real.rpow_neg hP.le, Real.rpow_natCast]
  have hG : (16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j) * f)
      ≤ (C / k) ^ ((j : ℝ) * ((k : ℝ) - 1 - j) * f) := by
    rw [show ((j : ℝ) * ((k : ℝ) - 1 - j) * f) = ((j * (k - 1 - j) * f : ℕ) : ℝ) by
      rw [Nat.cast_mul, Nat.cast_mul, hcast], Real.rpow_natCast]
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    have h1 := Real.pi_lt_d2
    have h2 := Real.exp_one_lt_d9
    have hpe : Real.pi * Real.exp 1 < 3.15 * 2.7182818286 :=
      mul_lt_mul'' h1 h2 Real.pi_pos.le (Real.exp_pos 1).le
    nlinarith
  rw [hPi]
  exact GlobalTheory.AmpArith.regroup
    (mul_nonneg (pow_nonneg hv0 _) (pow_nonneg (mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (by positivity) _) zero_le_one) (by positivity)) _))
    (pow_nonneg (by linarith) _)
    (pow_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) _)
    (pow_nonneg (by positivity) _)
    (inv_nonneg.mpr (pow_nonneg hP.le _))
    (Real.rpow_nonneg (by linarith) _)
    (GlobalTheory.AmpArith.v_part k r f j v hr hv)
    (GlobalTheory.AmpArith.b_part CH C hCH hC r m f b v hm hr hb hv hvb)
    hG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHyps
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SizesProof

theorem vand_pos {n : ℕ} {x : Fin n → ℝ} (h : StrictAnti x) : 0 < Formalism.MainNotions.S.vand x :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb => sub_pos.2 (h (Finset.mem_filter.1 hb).2)

theorem sizes_of_hyp : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), D.host.rdE ≤ large₂.sc.b →
    HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes D large₂ Cl Cg CT := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 hb h
  obtain ⟨⟨-, -, hmf, hfk, -, -, -, -, -, -, -, hg1, hg1', hg2, hg2', -, -, -, hv, -, -, hgap, hT, hCl, hCl0⟩, -, -⟩ := h
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb1 : 1 < large₂.sc.b := lt_trans (by simpa using Real.exp_lt_exp.2 (zero_lt_one (α := ℝ))) hbe
  have hm : D.R.m = 2 * D.R.rS + 2 := by
    have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (1 : ℝ) ≤ D.R.k * large₂.sc.b := by nlinarith
  have h8 : (1 : ℝ) ≤ (D.R.k * large₂.sc.b) ^ 8 := one_le_pow₀ hkb
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 1 ≤ gg D := by unfold gg; nlinarith
  have hu : ∀ w τ, StrictAnti (uS D w τ) := fun w τ => by
    have hk0 : D.R.k = (D.R.k - 1) + 1 := by have := D.R.m_add_three_le_k; omega
    have key : ∀ (i : ℕ) (hi : i + 1 < D.R.k), uS D w τ ⟨i + 1, hi⟩ < uS D w τ ⟨i, by omega⟩ := fun i hi => by
      have a := (D.hcW w τ).u_gt_v ⟨i, by omega⟩
      have b := (D.hcW w τ).v_gt_u ⟨i, by omega⟩
      unfold uS; exact_mod_cast b.trans a
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih => exact (key c hc).trans (ih (by omega) hc')
  refine ⟨hL, Real.log_exp _, hbe, hm, hr, D.what₂.card_Tau, hCl, hmf.trans hfk, hv, hrd, rfl, hrd ▸ hb, hgg, ?_, ?_, ?_,
    fun w => (hT w).2, fun w τ => ⟨vand_pos (hu w τ), ?_⟩, ?_⟩
  · rw [two_mul, Real.rpow_add (by linarith)]
    exact mul_le_mul hg1' hg2' (by linarith) (by linarith)
  · have : large₂.sc.b ^ (8 : ℝ) ≤ large₂.sc.b ^ Cg := by
      refine le_trans ?_ (hg1.trans hg1')
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) (by nlinarith) 8
    exact (Real.rpow_le_rpow_left_iff hb1).1 this
  · refine le_trans ?_ (hg1.trans hg1')
    exact le_trans (by nlinarith) (le_self_pow₀ hkb (by norm_num))
  · have h1 : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
    have h2 : 0 < D.host.rdE := by linarith
    have h3 : 0 < gg D := by linarith
    have h4 : 0 < VV D τ := mul_pos (D.dsig_pos τ) (Finset.prod_pos fun i _ => by positivity)
    have h5 := vand_pos (hu w τ)
    unfold Tcrit; positivity
  · intro τ
    have hp : 0 ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 := by positivity
    have key : ∀ (i : ℕ) (hi : i + 1 < 2 * D.R.rS + D.R.k + 1),
        Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ ⟨i, by omega⟩ - lamD D τ ⟨i + 1, hi⟩ := fun i hi => by
      have := hgap τ ⟨i, by omega⟩ (by simpa [hr] using hi)
      have h0 : (0 : ℝ) ≤ D.R.r * (D.R.m : ℝ) ^ 10 := by positivity
      exact lt_of_le_of_lt (le_add_of_nonneg_right h0) this
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih =>
      have := key c hc
      have := ih (by omega) hc'
      linarith

end GlobalTheory.Amp.SizesProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellExponentialChartStrictDifferentiableSumma
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens.Deriv

def dg (k r : ℕ) (c : Fin r → ℂ) (j : Fin (2 * r + k + 1)) : ℂ :=
  if hj : j.val < r then c ⟨j.val, hj⟩
  else if hj2 : j.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - j.val, by omega⟩))⁻¹

theorem bigCell_eq (k r : ℕ) (c : Fin r → ℂ) :
    bigCell k r c 1 = wC k r * Matrix.diagonal (dg k r c) := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [wC, bigCell, dg]
  split_ifs <;> simp

def sg (k r : ℕ) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if j.val < r ∨ r + k < j.val then ⟨2 * r + k - j.val, by omega⟩ else j

theorem sg_sg (k r : ℕ) (j : Fin (2 * r + k + 1)) : sg k r (sg k r j) = j := by
  have := j.isLt
  have hv : ∀ i : Fin (2 * r + k + 1), (sg k r i).val =
      if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
    intro i; simp only [sg]; split_ifs <;> rfl
  apply Fin.ext
  rw [hv, hv]
  split_ifs <;> omega

theorem wC_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    wC k r i j = if i = sg k r j then 1 else 0 := by
  have := j.isLt
  have := i.isLt
  have hv : (sg k r j).val =
      if j.val < r ∨ r + k < j.val then 2 * r + k - j.val else j.val := by
    simp only [sg]; split_ifs <;> rfl
  simp only [wC, bigCell, esI, Matrix.one_apply, Fin.ext_iff, hv, star_one, inv_one]
  split_ifs <;> first | rfl | omega

theorem wC_mul_wC (k r : ℕ) : wC k r * wC k r = 1 := by
  ext i j
  simp only [Matrix.mul_apply, wC_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (sg k r j)]
  · simp [sg_sg]
  · intro b _ hb; simp [hb]
  · simp

def umL {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : lieE S →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := um
  map_add' X Y := by ext i j; apply Complex.ext <;> simp [um, unrealify]
  map_smul' a X := by ext i j; apply Complex.ext <;> simp [um, unrealify]

theorem dg_one (k r : ℕ) : dg k r (fun a => 1 + (0 : Fin r → ℂ) a) = fun _ => 1 := by
  funext j; simp only [dg]; split_ifs <;> simp

theorem dg_contOn (k r : ℕ) (j : Fin (2 * r + k + 1)) :
    ContinuousOn (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a) j) (Metric.ball 0 1) := by
  simp only [dg]
  split_ifs with h1 h2
  · fun_prop
  · fun_prop
  · apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [mem_ball_zero_iff] at hx
    have h3 := (norm_le_pi_norm x ⟨2 * r + k - j.val, by omega⟩).trans_lt hx
    rw [star_ne_zero]
    intro h
    have : x ⟨2 * r + k - j.val, by omega⟩ = -1 := by linear_combination h
    rw [this] at h3
    simp at h3

theorem dg_deriv (k r : ℕ) (j : Fin (2 * r + k + 1)) :
    ∃ D : (Fin r → ℂ) →L[ℝ] ℂ,
      HasStrictFDerivAt (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a) j) D 0 ∧
      ∀ x, D x = torD k r x j j := by
  simp only [dg, torD, Matrix.diagonal_apply_eq]
  by_cases h1 : j.val < r
  · simp only [dif_pos h1]
    exact ⟨_, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
      ⟨j.val, h1⟩).hasStrictFDerivAt.const_add 1, fun x => rfl⟩
  · by_cases h2 : j.val ≤ r + k
    · simp only [dif_neg h1, dif_pos h2, dif_neg (not_lt.2 h2)]
      exact ⟨0, hasStrictFDerivAt_const _ _, fun x => rfl⟩
    · simp only [dif_neg h1, dif_neg h2, dif_pos (not_le.1 h2)]
      set a : Fin r := ⟨2 * r + k - j.val, by omega⟩
      let L : (Fin r → ℂ) →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a)
      have hL : HasStrictFDerivAt (fun x : Fin r → ℂ => 1 + L x) L 0 := L.hasStrictFDerivAt.const_add 1
      have hi : HasStrictDerivAt (fun z : ℂ => z⁻¹) (-((1 + L 0) ^ 2)⁻¹) (1 + L 0) :=
        hasStrictDerivAt_inv (by simp)
      have := (hi.hasStrictFDerivAt.restrictScalars ℝ).comp (0 : Fin r → ℂ) hL
      refine ⟨_, this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_), fun x => ?_⟩
      · simp [L]
      · simp [L]

theorem torD_eq (k r : ℕ) (x : Fin r → ℂ) : torD k r x = Matrix.diagonal fun j => torD k r x j j := by
  simp only [torD, Matrix.diagonal_apply_eq]

theorem um_zero {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : um (0 : lieE S) = 0 := (umL S).map_zero

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_um_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (L : E →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    HasStrictFDerivAt (fun v => NormedSpace.exp (L v)) (LinearMap.toContinuousLinearMap L) 0 := by
  have h1 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin m) (Fin m) ℂ → _)
      (1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ)
      (LinearMap.toContinuousLinearMap L 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  exact h1.comp 0 (LinearMap.toContinuousLinearMap L).hasStrictFDerivAt

theorem exp_um_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (L : E →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    Continuous (fun v => NormedSpace.exp (L v)) :=
  NormedSpace.exp_continuous.comp (LinearMap.toContinuousLinearMap L).continuous

theorem diag_deriv (k r : ℕ) :
    ∃ D : (Fin r → ℂ) →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      HasStrictFDerivAt (fun x : Fin r → ℂ => Matrix.diagonal (dg k r (fun a => 1 + x a))) D 0 ∧
      ∀ x, D x = torD k r x := by
  choose D hD hD' using dg_deriv k r
  have h1 : HasStrictFDerivAt (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a))
      (ContinuousLinearMap.pi D) 0 := hasStrictFDerivAt_pi.2 hD
  let L : (Fin (2 * r + k + 1) → ℂ) →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin (2 * r + k + 1)) ℝ ℂ)
  refine ⟨_, L.hasStrictFDerivAt.comp 0 h1, fun x => ?_⟩
  rw [torD_eq]
  change Matrix.diagonal (fun j => D j x) = _
  simp only [hD']

theorem chart_deriv_mat (k r : ℕ) :
    ∃ D : EE k r →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      HasStrictFDerivAt (chart k r) D 0 ∧ ∀ v, D v = dchart k r v := by
  obtain ⟨D, hD, hD'⟩ := diag_deriv k r
  let P : EE k r →L[ℝ] (Fin r → ℂ) := (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  have h2 : HasStrictFDerivAt (fun v : EE k r => Matrix.diagonal (dg k r (fun a => 1 + v.2.1 a)))
      (D.comp P) 0 :=
    HasStrictFDerivAt.comp (0 : EE k r) (f := P) (by rw [map_zero]; exact hD) P.hasStrictFDerivAt
  have h1 := exp_um_deriv (E := EE k r)
    (-((umL (Nset k r)).comp ((LinearMap.fst ℝ _ _).comp (LinearMap.fst ℝ _ _))))
  have h3 := exp_um_deriv (E := EE k r)
    ((umL (Formalism.FourierDecayAlt.B2.UWb k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  have h4 := exp_um_deriv (E := EE k r)
    ((umL (Nset k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.fst ℝ _ _)))
  have h := (((h1.mul' (h2.const_mul (wC k r))).mul' h3).mul' h4).const_mul (wC k r)
  refine ⟨_, h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_), fun v => ?_⟩
  · simp only [chart, bigCell_eq]
    rfl
  · have e : dg k r (fun _ => 1) = fun _ => 1 := by simpa using dg_one k r
    simp [e, P, dchart, umL, um_zero]
    change wC k r * (wC k r * um v.1.2) + (wC k r * (wC k r * um v.2.2) +
      (wC k r * (wC k r * D v.2.1) + wC k r * (-um v.1.1 * wC k r))) = _
    simp only [hD', ← mul_assoc, wC_mul_wC, one_mul, mul_neg, neg_mul]
    abel

theorem chart_deriv (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧
      ∀ v, D v = dchart k r v i j := by
  obtain ⟨D, hD, hD'⟩ := chart_deriv_mat k r
  let L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  refine ⟨_, L.hasStrictFDerivAt.comp 0 hD, fun v => ?_⟩
  change D v i j = _
  rw [hD']

theorem chart_contOn (k r : ℕ) : ContinuousOn (chart k r) (Metric.ball 0 1) := by
  have h1 := exp_um_cont (E := EE k r)
    (-((umL (Nset k r)).comp ((LinearMap.fst ℝ _ _).comp (LinearMap.fst ℝ _ _))))
  have h3 := exp_um_cont (E := EE k r)
    ((umL (Formalism.FourierDecayAlt.B2.UWb k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  have h4 := exp_um_cont (E := EE k r)
    ((umL (Nset k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.fst ℝ _ _)))
  have h5 : ContinuousOn (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a)) (Metric.ball 0 1) :=
    continuousOn_pi.2 (dg_contOn k r)
  have h6 : ContinuousOn (fun v : EE k r => dg k r (fun a => 1 + v.2.1 a)) (Metric.ball 0 1) := by
    refine h5.comp (f := fun v : EE k r => v.2.1) (by fun_prop) fun v hv => ?_
    rw [mem_ball_zero_iff] at hv ⊢
    exact ((norm_fst_le v.2).trans (norm_snd_le v)).trans_lt hv
  have h2 : ContinuousOn (fun v : EE k r => Matrix.diagonal (dg k r (fun a => 1 + v.2.1 a)))
      (Metric.ball 0 1) :=
    (Continuous.matrix_diagonal continuous_id).comp_continuousOn h6
  have h := (continuousOn_const (c := wC k r)).mul
    (((h1.continuousOn.mul ((continuousOn_const (c := wC k r)).mul h2)).mul h3.continuousOn).mul
      h4.continuousOn)
  refine h.congr fun v _ => ?_
  simp only [chart, bigCell_eq]
  rfl

end

theorem chart_zero (k r : ℕ) : chart k r 0 = 1 := by
  have e : dg k r (fun _ => 1) = fun _ => 1 := by simpa using dg_one k r
  simp [chart, bigCell_eq, um_zero, e, wC_mul_wC]

theorem chart_strict : ∀ (k r : ℕ), chart k r 0 = 1 ∧ ContinuousOn (chart k r) (Metric.ball 0 1) ∧
    ∀ i j, ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧
      ∀ v, D v = dchart k r v i j :=
  fun k r => ⟨chart_zero k r, chart_contOn k r, chart_deriv k r⟩

end GlobalTheory.CellDens.Deriv
end
end

