module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.TreeLeafParameterArithmeticOfBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

namespace GlobalTheory.BigTop.Fun.PolBound

theorem log_le_posLog' (y : ℝ) : Real.log y ≤ Real.posLog y := by
  unfold Real.posLog; exact le_max_right _ _

theorem posLog_le_of_log_le {y B : ℝ} (hy : Real.log y ≤ B) (hB : 0 ≤ B) : Real.posLog y ≤ B := by
  unfold Real.posLog; exact max_le hB hy

theorem pol_core {C Q f m k t lb Lb : ℝ} (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hf0 : 0 ≤ f) (hf : f ≤ Q) (hm0 : 0 ≤ m)
    (hm : m ≤ Q) (hk0 : 0 ≤ k) (hk : k ≤ Q) (ht0 : 0 ≤ t) (ht : t ≤ Q) (hlb0 : 0 ≤ lb) (hlb : lb ≤ Q)
    (hLb : Lb ≤ 20 * Q) :
    100000 * C ^ 3 * f * m ^ 2 * (k + m * (t + (k + m + 5) + 1)) ^ 2 *
      ((k + m - 1) * (k + m * (t + (k + m + 5) + 1)) * lb + C * f ^ 2 * (k + m) ^ 6 * Lb) ≤
      13000000000 * C ^ 4 * Q ^ 16 := by
  set N := k + m * (t + (k + m + 5) + 1) with hNdef
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hN0 : 0 ≤ N := by positivity
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hN : N ≤ 10 * Q ^ 2 := by
    have h1 : t + (k + m + 5) + 1 ≤ 9 * Q := by linarith
    have h2 : m * (t + (k + m + 5) + 1) ≤ Q * (9 * Q) := mul_le_mul hm h1 (by positivity) hQ0
    nlinarith
  have hr : k + m - 1 ≤ 2 * Q := by linarith
  have hnr0 : 0 ≤ k + m := by linarith
  have hnr : k + m ≤ 2 * Q := by linarith
  have i1 : (k + m - 1) * N * lb ≤ (2 * Q) * (10 * Q ^ 2) * Q := by
    have a : (k + m - 1) * (N * lb) ≤ (2 * Q) * (N * lb) := mul_le_mul_of_nonneg_right hr (by positivity)
    have b : N * lb ≤ (10 * Q ^ 2) * Q := mul_le_mul hN hlb hlb0 (by positivity)
    have c : (2 * Q) * (N * lb) ≤ (2 * Q) * ((10 * Q ^ 2) * Q) := mul_le_mul_of_nonneg_left b (by positivity)
    calc (k + m - 1) * N * lb = (k + m - 1) * (N * lb) := by ring
      _ ≤ _ := a.trans c
      _ = _ := by ring
  have i2 : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) := by
    have a : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * f ^ 2 * (k + m) ^ 6 * (20 * Q) :=
      mul_le_mul_of_nonneg_left hLb (by positivity)
    have b : C * f ^ 2 * (k + m) ^ 6 ≤ C * Q ^ 2 * (2 * Q) ^ 6 := by gcongr
    exact a.trans (mul_le_mul_of_nonneg_right b (by positivity))
  have hQ4 : Q ^ 4 ≤ Q ^ 9 := pow_le_pow_right₀ hQ (by norm_num)
  have hinner : (k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb ≤ 1300 * C * Q ^ 9 := by
    have e1 : (2 * Q) * (10 * Q ^ 2) * Q = 20 * Q ^ 4 := by ring
    have e2 : C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) = 1280 * C * Q ^ 9 := by ring
    have e3 : 20 * Q ^ 4 ≤ 20 * C * Q ^ 9 := by
      have : Q ^ 4 ≤ C * Q ^ 9 := hQ4.trans (le_mul_of_one_le_left (by positivity) hC)
      linarith
    linarith
  have hpre0 : 0 ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 := by positivity
  have hpre : 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 := by gcongr
  calc 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * ((k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb)
      ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * (1300 * C * Q ^ 9) := mul_le_mul_of_nonneg_left hinner hpre0
    _ ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 * (1300 * C * Q ^ 9) :=
        mul_le_mul_of_nonneg_right hpre (by positivity)
    _ = 13000000000 * C ^ 4 * Q ^ 16 := by ring

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun.PolBound

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem rpow_mono {x a b : ℝ} (hx : 1 ≤ x) (h : a ≤ b) : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx h

theorem factors_le {D : D7} (L : SizeData₂ D) (hS : SizesAt L) (T : ℕ) (hT : L.Ct + 1 ≤ T) :
    (D.R.f : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.m : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.k : ℝ) ≤ L.sc.x ^ (T + 9) ∧
      (D.R.t : ℝ) ≤ L.sc.x ^ (T + 9) ∧ Real.log L.sc.b ≤ L.sc.x ^ (T + 9) ∧ 0 ≤ Real.log L.sc.b ∧
      Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ 20 * L.sc.x ^ (T + 9) := by
  obtain ⟨hN, hM, hK, hKR, hTt, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, hPde, -⟩ := hS
  set x := L.sc.x with hxdef
  have hx1 : 1 ≤ x := L.sc.one_lt_alt.le
  have hx0 : 0 ≤ x := by linarith
  have he0 : 0 < L.sc.eps := L.sc.eps_pos
  have he1 : L.sc.eps < 1 / 52 := L.sc.eps_lt
  have hth : szTh L = L.sc.eps / 100 := rfl
  have hpow : ∀ j : ℕ, j ≤ T + 9 → x ^ j ≤ x ^ (T + 9) := fun j hj => pow_le_pow_right₀ hx1 hj
  have hrp : ∀ (a : ℝ) (j : ℕ), a ≤ j → x ^ a ≤ x ^ j := fun a j h => by
    rw [← Real.rpow_natCast]; exact rpow_mono hx1 h

  have hLd : L.sc.L = x ^ L.sc.eps := by rw [hxdef]; rfl
  have hlb : Real.log L.sc.b = x ^ L.sc.eps := by
    show Real.log (Real.exp L.sc.L) = _
    rw [Real.log_exp]; exact hLd
  have hLx : x ^ L.sc.eps ≤ x := by
    have := hrp L.sc.eps 1 (by norm_num; linarith); simpa using this

  have hm : (D.R.m : ℝ) ≤ x := by
    have hd1 : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0 _
    have h1 : Real.sqrt (x * L.sc.delta1) ≤ x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : x ^ szTh L * Real.sqrt (x * L.sc.delta1) ≤ x ^ szTh L * x ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx0 _)
    rw [← Real.rpow_add (by linarith)] at h2
    have h3 : x ^ (szTh L + 1 / 2) ≤ x ^ (1 : ℕ) := hrp _ 1 (by rw [hth]; push_cast; linarith)
    linarith [hM.2, pow_one x]
  have hk : (D.R.k : ℝ) ≤ x ^ 5 := hK.2.trans (hrp _ 5 (by rw [hth]; push_cast; linarith))
  have hn : (D.R.n : ℝ) ≤ x ^ 3 := hN.2.trans (hrp _ 3 (by rw [hth]; push_cast; linarith))
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hf : (D.R.f : ℝ) ≤ x ^ 5 := by
    have h := hKR.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h2 : (D.R.m : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hm0 hm 2
    have h3 : (D.R.m : ℝ) ^ 2 * D.R.n ≤ x ^ 2 * x ^ 3 := mul_le_mul h2 hn (Nat.cast_nonneg _) (by positivity)
    calc (D.R.f : ℝ) ≤ _ := h
      _ ≤ _ := h3
      _ = x ^ 5 := by ring
  have ht : (D.R.t : ℝ) ≤ x ^ T := by
    refine hTt.2.trans (hrp _ T ?_)
    have : L.Ct + szTh L ≤ L.Ct + 1 := by rw [hth]; linarith
    linarith
  have hQ5 : x ^ 5 ≤ x ^ (T + 9) := hpow 5 (by omega)
  have hQ8 : x ^ 8 ≤ x ^ (T + 9) := hpow 8 (by omega)
  have hQ1 : x ≤ x ^ (T + 9) := by simpa using hpow 1 (by omega)
  refine ⟨hf.trans hQ5, hm.trans hQ1, hk.trans hQ5, ht.trans (hpow T (by omega)), by rw [hlb]; linarith,
    by rw [hlb]; positivity, ?_⟩

  have hb : Real.posLog L.sc.b ≤ x := posLog_le_of_log_le (by rw [hlb]; exact hLx) hx0
  have hnr : Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) ≤ 2 * x ^ 5 := by
    refine posLog_le_of_log_le ((Real.log_le_self (Nat.cast_nonneg _)).trans ?_) (by positivity)
    push_cast
    have : (D.R.m : ℝ) ≤ x ^ 5 := hm.trans (by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 5))
    linarith
  have hg : ∀ i : Fin 2, Real.posLog (D.host.g i : ℝ) ≤ x := fun i => by
    refine posLog_le_of_log_le ((hG i i).2.2.trans ?_) hx0
    rw [hLd, ← Real.rpow_add (by linarith)]
    have := hrp (szTh L + L.sc.eps) 1 (by rw [hth]; push_cast; linarith)
    simpa using this
  have hp1 : Real.posLog (D.host.pde : ℝ) ≤ x := posLog_le_of_log_le (hPde.1.trans (hLd ▸ hLx)) hx0
  have hp2 : Real.posLog (D.host.pde' : ℝ) ≤ x := posLog_le_of_log_le (hPde.2.trans (hLd ▸ hLx)) hx0
  have hdE : Real.posLog |((discr D.host.E : ℤ) : ℝ)| ≤ 6 * x ^ 8 := by
    refine posLog_le_of_log_le ?_ (by positivity)
    have e := logdE_eq_rd D
    unfold logdE at e
    rw [e]
    have hlr : Real.log D.host.rdE ≤ 2 * x ^ 3 + x := by
      have h1 := UpperTheory.Ram.Rd.log_rdE_le D.host
      have h2 : Real.log (D.R.n : ℝ) ≤ x ^ 3 := (Real.log_le_self (Nat.cast_nonneg _)).trans hn
      have hq : Real.log D.host.q ≤ x := hQD.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      have hd : Real.log D.host.d ≤ x := hQD.2.2.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      linarith
    have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    calc 2 * (D.R.f : ℝ) * Real.log D.host.rdE ≤ 2 * (D.R.f : ℝ) * (2 * x ^ 3 + x) :=
          mul_le_mul_of_nonneg_left hlr (by positivity)
      _ ≤ 2 * x ^ 5 * (2 * x ^ 3 + x) := by gcongr
      _ ≤ 6 * x ^ 8 := by
          have : x ^ 6 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
          nlinarith
  have hprod : Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ Real.posLog L.sc.b + Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) +
      Real.posLog (D.host.g 0 : ℝ) + Real.posLog (D.host.g 1 : ℝ) + Real.posLog (D.host.pde : ℝ) +
      Real.posLog (D.host.pde' : ℝ) + Real.posLog |((discr D.host.E : ℤ) : ℝ)| := by
    refine (log_le_posLog' _).trans ?_
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    exact Real.posLog_mul
  have h8 : x ^ 5 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
  have h18 : x ≤ x ^ 8 := by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 8)
  have := hg 0
  have := hg 1
  refine hprod.trans ?_
  linarith

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.BigTop.Fun.PolBound

end GlobalTheory.BigTop.Fun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsFifthEstimate
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cloud_mem_Icc_Sc {D : D7} (L : SizeData₂ D) (τ i : ℕ) :
    0 ≤ cloud D τ i ∧ (cloud D τ i : ℝ) ≤ L.Sc := by
  unfold cloud
  split_ifs with h
  · dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]
    unfold GlobalTheory.SignedHC.GridData.extend
    split_ifs with h2
    · obtain ⟨h0, h1⟩ := L.cloud_v ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩) ⟨i - 2, h2⟩
      refine ⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩
      have hf := Int.floor_le ((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩)
      have hf' : (((⌊(D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤
          (((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩ : ℚ) : ℝ) := by exact_mod_cast hf
      push_cast at hf' ⊢
      linarith
    · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩
  · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩

theorem Lc_le_of_cloud_le {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) (S : ℝ) (h0 : 0 ≤ S) (hcl : ∀ τ i, 0 ≤ O.cl τ i ∧ (O.cl τ i : ℝ) ≤ S) :
    (O.Lc : ℝ) ≤ S := by
  have hL : O.Lc ≤ ⌊S⌋₊ := by
    unfold FunData.Lc
    refine Finset.sup_le fun τ _ => ?_
    rw [Nat.le_floor_iff h0]
    obtain ⟨a0, a1⟩ := hcl τ 2
    obtain ⟨b0, -⟩ := hcl τ O.k
    have h : ((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) ≤ O.cl τ 2 := by omega
    have h' : (((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) : ℝ) ≤ ((O.cl τ 2 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (O.Lc : ℝ) ≤ (⌊S⌋₊ : ℝ) := by exact_mod_cast hL
    _ ≤ S := Nat.floor_le h0

theorem Sc_le_scale_b {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.Sc ≤ L.sc.b := by
  have hk := P.kS_le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hn : (1 : ℝ) ≤ D.R.n := by
    unfold Ranks.n
    exact_mod_cast D.R.ord_pos
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hw : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.x * L.sc.b / L.sc.X' ≤ L.sc.x * L.sc.b := div_le_self (by positivity) hX
      _ ≤ L.sc.b * (L.sc.x * D.R.n) := by nlinarith [mul_nonneg (mul_pos hx hb).le (sub_nonneg.2 hn)]
  have hS := L.Sc_pos
  nlinarith

theorem mul_pow_le_exp_rpow {eps : ℝ} (heps : 0 < eps) (a : ℕ) (A : ℝ) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x, x0 ≤ x → A * x ^ a ≤ Real.exp (x ^ eps) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((a : ℝ) + 1) ≤ eps * n := ⟨⌈((a : ℝ) + 1) / eps⌉₊, by
    have := Nat.le_ceil (((a : ℝ) + 1) / eps)
    rw [div_le_iff₀ heps] at this
    linarith⟩
  refine ⟨max 1 (|A| * n.factorial), le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hy : 0 ≤ x ^ eps := Real.rpow_nonneg hx0 _
  have h1 := Real.pow_div_factorial_le_exp (x ^ eps) hy n
  have h2 : (x ^ eps) ^ n = x ^ (eps * n) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
  have h3 : x ^ (((a + 1 : ℕ)) : ℝ) ≤ x ^ (eps * n) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  rw [Real.rpow_natCast] at h3
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hAx : |A| * n.factorial ≤ x := (le_max_right _ _).trans hx
  have hxa : 0 ≤ x ^ a := pow_nonneg hx0 a
  have e2 : |A| * x ^ a * n.factorial ≤ x ^ (a + 1) :=
    calc |A| * x ^ a * n.factorial = x ^ a * (|A| * n.factorial) := by ring
      _ ≤ x ^ a * x := mul_le_mul_of_nonneg_left hAx hxa
      _ = x ^ (a + 1) := (pow_succ x a).symm
  have e3 : |A| * x ^ a ≤ x ^ (a + 1) / n.factorial := by rw [le_div_iff₀ hf]; exact e2
  rw [h2] at h1
  calc A * x ^ a ≤ |A| * x ^ a := mul_le_mul_of_nonneg_right (le_abs_self A) hxa
    _ ≤ x ^ (a + 1) / n.factorial := e3
    _ ≤ x ^ (eps * n) / n.factorial := by gcongr
    _ ≤ _ := h1

theorem design_lines_of_ranks (x eps B : ℝ) (c k m f t : ℕ) (hx : 20480 ≤ x) (heps : eps ≤ 1)
    (hm : 2 ≤ m) (hmf : m ≤ f) (hfk : f ≤ k) (hkt : k + m + 4 ≤ t)
    (ht : (t : ℝ) ≤ x ^ c) (hto : x ^ 377 ≤ (t : ℝ)) (hk : (k : ℝ) ≤ 2 * x ^ (9 / 2 + 10 * eps))
    (hB : 25 * x ^ (6 * c) ≤ B) :
    (m : ℝ) * f * (((k + m * (t + (k + m + 5) + 1) : ℕ) : ℝ)) ^ 2 ≤ B ∧
      80 * ((k : ℝ) + m - 1) ^ 4 ≤ (((k + m * (t + (k + m + 5) + 1) : ℕ) : ℝ)) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  constructor
  · have hN : k + m * (t + (k + m + 5) + 1) ≤ 5 * t ^ 2 := by
      have h1 : t + (k + m + 5) + 1 ≤ 4 * t := by omega
      have h2 : m * (t + (k + m + 5) + 1) ≤ t * (4 * t) := Nat.mul_le_mul (by omega) h1
      nlinarith
    have hP : m * f * (k + m * (t + (k + m + 5) + 1)) ^ 2 ≤ 25 * t ^ 6 := by
      have h1 : m * f ≤ t * t := Nat.mul_le_mul (by omega) (by omega)
      have h2 : (k + m * (t + (k + m + 5) + 1)) ^ 2 ≤ (5 * t ^ 2) ^ 2 := Nat.pow_le_pow_left hN 2
      calc m * f * (k + m * (t + (k + m + 5) + 1)) ^ 2 ≤ (t * t) * (5 * t ^ 2) ^ 2 := Nat.mul_le_mul h1 h2
        _ = 25 * t ^ 6 := by ring
    have hP' : ((m * f * (k + m * (t + (k + m + 5) + 1)) ^ 2 : ℕ) : ℝ) ≤ ((25 * t ^ 6 : ℕ) : ℝ) := by
      exact_mod_cast hP
    push_cast at hP'
    have ht6 : (t : ℝ) ^ 6 ≤ (x ^ c) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) ht 6
    rw [← pow_mul, mul_comm c 6] at ht6
    push_cast
    linarith
  · have hkr : (k : ℝ) ≤ 2 * x ^ 15 := by
      have e : x ^ (9 / 2 + 10 * eps) ≤ x ^ ((15 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
      rw [Real.rpow_natCast] at e
      linarith
    have hmk : (m : ℝ) ≤ k := by exact_mod_cast (le_trans hmf hfk)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hr0 : 0 ≤ (k : ℝ) + m - 1 := by linarith
    have hr : (k : ℝ) + m - 1 ≤ 4 * x ^ 15 := by linarith
    have hr4 : ((k : ℝ) + m - 1) ^ 4 ≤ (4 * x ^ 15) ^ 4 := pow_le_pow_left₀ hr0 hr 4
    have e1 : (4 * x ^ 15) ^ 4 = 256 * x ^ 60 := by ring
    have e2 : 20480 * x ^ 60 ≤ x ^ 377 := by
      have a1 : 20480 * x ^ 60 ≤ x * x ^ 60 := mul_le_mul_of_nonneg_right hx (pow_nonneg hx0 _)
      have a2 : x * x ^ 60 = x ^ 61 := by ring
      have a3 : x ^ 61 ≤ x ^ 377 := pow_le_pow_right₀ hx1 (by norm_num)
      linarith
    have e3 : (t : ℝ) ≤ (((k + m * (t + (k + m + 5) + 1) : ℕ) : ℝ)) := by
      have : t ≤ k + m * (t + (k + m + 5) + 1) := by nlinarith
      exact_mod_cast this
    nlinarith

end GlobalTheory.BigTop.Fun

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigTop.Fun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsSeventhEstimate
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.RamSum

section Norms

variable {F : Type} [Field F] [NumberField F]

theorem isPrimePow_absNorm (v : HeightOneSpectrum (𝓞 F)) : IsPrimePow (Ideal.absNorm v.asIdeal) := by
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact FiniteField.isPrimePow_card _

theorem sum_log_absNorm_le (S : Finset (HeightOneSpectrum (𝓞 F))) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ v ∈ S, (n : 𝓞 F) ∈ v.asIdeal) :
    ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal) ≤ Module.finrank ℚ F * Real.log n := by
  have h1 : ∏ v ∈ S, v.asIdeal ∣ Ideal.span {(n : 𝓞 F)} :=
    Finset.prod_dvd_of_coprime (fun v _ w _ hvw => (HeightOneSpectrum.isCoprime_of_ne v w hvw))
      fun v hv => Ideal.dvd_span_singleton.2 (h v hv)
  have h2 := map_dvd Ideal.absNorm h1
  rw [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h2
  have h3 := Nat.le_of_dvd (by positivity) h2
  have h4 : ∀ v ∈ S, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := fun v _ => by
    exact_mod_cast (isPrimePow_absNorm v).ne_zero
  rw [← Real.log_prod h4, ← Real.log_pow]
  refine Real.log_le_log (Finset.prod_pos fun v hv => lt_of_le_of_ne (Nat.cast_nonneg _) (h4 v hv).symm) ?_
  exact_mod_cast h3

end Norms

theorem leaves_of_sum {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) (C b : ℝ) (hL : 0 ≤ Real.log b) (h0 : O.sv0 ∈ O.S0) (hq : ∀ q ∈ O.S0, IsPrimePow (O.qq q))
    (hS : ∑ q ∈ O.S0, Real.log (O.qq q) ≤ 21 * (O.f * Real.log b)) (hc : ∀ q ∈ O.S0, O.cc q ≤ 2)
    (hP : 42 * (O.f * Real.log b) ≤ O.PPF C b) : PrimePowerModuliSumBound O C b ∧ LeafCS O b := by
  classical
  have hfL : 0 ≤ O.f * Real.log b := by positivity
  have hlq : 0 < Real.log (O.qq O.sv0) := Real.log_pos (by exact_mod_cast (hq _ h0).one_lt)
  have hP0 : 0 ≤ O.PPF C b := by linarith
  refine ⟨⟨hq, ?_⟩, ?_⟩
  · unfold FunData.Sig0
    rw [← Finset.add_sum_erase _ _ h0] at hS ⊢
    have e1 : ∑ q ∈ O.S0.erase O.sv0, (O.ee C b q : ℝ) * Real.log (O.qq q) =
        2 * ∑ q ∈ O.S0.erase O.sv0, Real.log (O.qq q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq' => ?_
      simp [FunData.ee, Finset.ne_of_mem_erase hq']
    have e2 : (O.ee C b O.sv0 : ℝ) * Real.log (O.qq O.sv0) ≤ O.PPF C b + Real.log (O.qq O.sv0) := by
      have h := Nat.floor_le (div_nonneg hP0 hlq.le)
      rw [le_div_iff₀ hlq] at h
      simp only [FunData.ee, if_true]
      push_cast
      linarith
    rw [e1]
    linarith
  · unfold LeafCS FunData.cS
    have e1 : ∑ q ∈ O.S0, (O.cc q : ℝ) * Real.log (O.qq q) ≤ 2 * ∑ q ∈ O.S0, Real.log (O.qq q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq' => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)
      exact_mod_cast hc q hq'
    linarith

theorem ramifiedPlaces_sum_log_absNorm_le {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) (s : Formalism.BasicNotions.Scale)
    (hg : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * s.L)) (h1 : (D.host.pde : ℝ) < s.X')
    (h2 : (D.host.pde' : ℝ) < s.X') (h3 : ((GlobalTheory.ChiGrid.q0 D : ℕ) : ℝ) < s.X') :
    ∑ v ∈ P.S0, Real.log (Ideal.absNorm v.asIdeal) ≤ 21 * (D.R.f * Real.log s.b) := by
  have p0 := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
  have p1 := (D.host.g_prime 0).pos
  have p2 := (D.host.g_prime 1).pos
  have p3 := D.host.pde_prime.pos
  have p4 := D.host.pde'_prime.pos
  have hF : Module.finrank ℚ D.host.F = D.R.f := by
    rw [D.host.finrank_hostF, Ranks.f, Ranks.n]
  have key := sum_log_absNorm_le P.S0
    (n := GlobalTheory.ChiGrid.q0 D * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')) (by positivity) fun v hv => by
      rw [Nat.cast_mul]
      rcases P.mem_S0_of_sum_eq.1 hv with rfl | hv
      · exact Ideal.mul_mem_right _ _ P.basePlace_over_qZero
      · exact Ideal.mul_mem_left _ _ (Formalism.L2.DIV.mem_primesOf.1 hv).2
  rw [hF] at key
  refine key.trans ?_
  have hb : Real.log s.b = s.L := Real.log_exp _
  have hX : s.X' ≤ Real.exp s.L :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith [s.eps_pos]))
  have hl : ∀ {n : ℕ} {y : ℝ}, 0 < n → (n : ℝ) ≤ Real.exp y → Real.log n ≤ y := fun hn h =>
    (Real.log_le_iff_le_exp (by exact_mod_cast hn)).2 h
  have a0 := hl p0 (h3.le.trans hX)
  have a1 := hl p1 (hg 0)
  have a2 := hl p2 (hg 1)
  have a3 := hl p3 (h1.le.trans hX)
  have a4 := hl p4 (h2.le.trans hX)
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), hb, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

theorem le_PPF {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) {C b : ℝ} (hC : 42 ≤ C) (hb : 1 ≤ b) (hf : 1 ≤ O.f) (hn : 1 ≤ O.nr) (h1 : 1 ≤ O.g1) (h2 : 1 ≤ O.g2)
    (h3 : 1 ≤ O.pd) (h4 : 1 ≤ O.pd') (h5 : O.dE ≠ 0) : 42 * (O.f * Real.log b) ≤ O.PPF C b := by
  have hf' : (1 : ℝ) ≤ O.f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ O.nr := by exact_mod_cast hn
  have h1' : (1 : ℝ) ≤ O.g1 := by exact_mod_cast h1
  have h2' : (1 : ℝ) ≤ O.g2 := by exact_mod_cast h2
  have h3' : (1 : ℝ) ≤ O.pd := by exact_mod_cast h3
  have h4' : (1 : ℝ) ≤ O.pd' := by exact_mod_cast h4
  have h5' : (1 : ℝ) ≤ |(O.dE : ℝ)| := by exact_mod_cast Int.one_le_abs h5
  have hl : 0 ≤ Real.log b := Real.log_nonneg hb
  have e1 : Real.log b ≤ Real.log (b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)|) := by
    refine Real.log_le_log (by linarith) ?_
    calc b = b * 1 * 1 * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have e2 : (O.f : ℝ) ≤ (O.f : ℝ) ^ 2 := le_self_pow₀ hf' two_ne_zero
  have e3 : (1 : ℝ) ≤ (O.nr : ℝ) ^ 6 := one_le_pow₀ hn'
  unfold FunData.PPF
  calc 42 * (O.f * Real.log b) = 42 * O.f * 1 * Real.log b := by ring
    _ ≤ _ := by gcongr

end GlobalTheory.BigTop.Fun.RamSum

namespace GlobalTheory.BigTop.Fun

open RamSum

end GlobalTheory.BigTop.Fun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointGenericFibreOfActsStar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosGeneric

theorem rosatiAdj_generic_of_actsAs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g → ActsAs U.toUnifPre (o.onB.act (star a)) (fun χ => star (star a) • χ) g' → RosatiAdj A.A A.L (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom) (U.gen.inv ≫ (Over.pullback (jK R)).map g' ≫ U.gen.hom) :=
  rosatiAdj_generic_of_cube _root_.GlobalTheory.Mum.linEnd_adjoint_lbIso

end GlobalTheory.Mum.RosGeneric
end

