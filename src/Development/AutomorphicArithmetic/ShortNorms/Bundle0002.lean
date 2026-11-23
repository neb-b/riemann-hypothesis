module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0002
public import Development.AutomorphicArithmetic.CoprimeRanks.SecondSetNoRelation
public import Development.AutomorphicArithmetic.ShortNorms.typePrimesN
public import Development.AutomorphicArithmetic.ShortNorms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ShortNorms.MulLogLeRpowEventually
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

private theorem mul_log_le_rpow_eventually (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → C * Real.log x ≤ x ^ a := by
  have h := (isLittleO_log_rpow_atTop ha).bound (show (0:ℝ) < 1 / C by positivity)
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp h
  refine ⟨max x1 1, fun x hx => ?_⟩
  have hx1' := hx1 x (le_trans (le_max_left _ _) hx)
  have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hpow : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith) a
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hpow] at hx1'
  calc C * Real.log x ≤ C * (1 / C * x ^ a) := by gcongr
    _ = x ^ a := by field_simp

theorem UpperTheory.T3.qdBig :
    ∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (Y : ℝ) (q d : ℕ), s.eps = eps → x0 ≤ s.x →
      RankVal s R → s.J ≤ C0 → PairWin s Y → WinPair eps Y q d → (4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d) ∧ 100 ≤ d := by
  intro eps C0 he0 he1
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps he0 he1
  have hC1pos : 0 < max C0 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨x2, hx2⟩ := mul_log_le_rpow_eventually (eps / 5 / max C0 1) 814 (by positivity) (by norm_num)
  refine ⟨max (max x1 x2) 6, ?_⟩
  intro s R Y q d hs hx hR hJ hP hW
  have hxx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx6 : (6:ℝ) ≤ s.x := le_trans (le_max_right _ _) hx
  have hX0 : 0 < s.x := by linarith
  obtain ⟨-, -, hr5, -, -, -, -, -, -, -, -, -, -, ht401, -⟩ := hx1 s R hs hxx1 hR
  rw [show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast] at hr5
  rw [show (401:ℝ) = ((401:ℕ):ℝ) by norm_num, Real.rpow_natCast] at ht401
  have hJ1 : s.J ≤ max C0 1 := le_trans hJ (le_max_left _ _)
  have hYlo : s.x ^ (1 / max C0 1) ≤ Y := hP.rpow_inv_le hJ1
  have hYe : s.x ^ (eps / 5 / max C0 1) ≤ Y ^ (eps / 5) := by
    have h : s.x ^ (eps / 5 / max C0 1) = (s.x ^ (1 / max C0 1)) ^ (eps / 5) := by
      rw [← Real.rpow_mul hX0.le]
      congr 1
      field_simp
    rw [h]
    exact Real.rpow_le_rpow (by positivity) hYlo (by positivity)
  have hlogx := hx2 s.x hxx2
  have hq := hW.q_lo
  have hqlog : 407 * Real.log s.x < Real.log q := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast hW.q_prime.pos
  have hqbig : s.x ^ (407:ℕ) < (q:ℝ) := by
    rw [← Real.log_lt_log_iff (by positivity) hq0, Real.log_pow]
    push_cast
    linarith
  have ht0 : (0:ℝ) ≤ R.t := by positivity
  have hr0 : (0:ℝ) ≤ R.r := by positivity
  have htr : (R.t:ℝ) * R.r ≤ s.x ^ 401 * s.x ^ 5 := mul_le_mul ht401 hr5 hr0 (by positivity)
  have e1 : s.x ^ 401 * s.x ^ 5 = s.x ^ 406 := by ring
  have e2 : s.x ^ 407 = s.x * s.x ^ 406 := by ring
  have h3 : (216:ℝ) ≤ s.x ^ 406 := by
    have a1 : s.x ^ 3 ≤ s.x ^ 406 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have a2 : (6:ℝ) ^ 3 ≤ s.x ^ 3 := pow_le_pow_left₀ (by norm_num) hx6 3
    norm_num at a2
    linarith
  have h4 : 6 * s.x ^ 406 ≤ s.x * s.x ^ 406 := mul_le_mul_of_nonneg_right hx6 (by positivity)
  have hqR : ((4 * R.t * R.r + 2 : ℕ) : ℝ) < q := by
    push_cast
    nlinarith
  have hqR' : ((102 : ℕ) : ℝ) < q := by
    push_cast
    nlinarith
  have hqN : 4 * R.t * R.r + 2 < q := by exact_mod_cast hqR
  have hqN' : 102 < q := by exact_mod_cast hqR'
  have hqd : q ≤ d + 1 := Nat.le_of_dvd (Nat.succ_pos _) hW.d_q
  generalize 4 * R.t * R.r = P at *
  omega
end

-- bundled from Development.AutomorphicArithmetic.ShortNorms.levelData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

private theorem mod_small (C eps : ℝ) (hC : 1 ≤ C) (he : 0 < eps) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, 3 * x ^ (eps / 5) * Real.log x ^ 2 * C < x ^ eps := by
  have hc : 0 < 1 / (4 * C) := by positivity
  have h1 := (isLittleO_log_rpow_atTop (show 0 < eps / 5 by positivity)).bound hc
  obtain ⟨x₀, hx⟩ := Filter.eventually_atTop.1 (h1.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨x₀, fun x hxx => ?_⟩
  obtain ⟨ha, hb⟩ := hx x hxx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _), abs_of_nonneg hl0] at ha
  have hu : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow hb (by positivity)
  have he5 : x ^ eps = (x ^ (eps / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  rw [he5]
  generalize x ^ (eps / 5) = u at ha hu ⊢
  generalize Real.log x = l at ha hl0 ⊢
  have h2 : 4 * C * l ≤ u := by
    have := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4 * C by positivity)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
  have h3 : l ≤ u := by nlinarith
  have h4 : 4 * C * l * l ≤ u * u := mul_le_mul h2 h3 hl0 (by linarith)
  have h5 : u ^ 3 ≤ u ^ 5 := pow_le_pow_right₀ hu (by norm_num)
  have h6 : 0 < u ^ 3 := by positivity
  have h7 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ u by linarith)
  nlinarith

theorem UpperTheory.T3.levelData :
    UpperTheory.T3.ShortNorm → UpperTheory.T3.SmallOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ,
      ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → UpperTheory.T3.ModAt s.x eps N d →
      ∃ (g : Fin 2 → ℕ) (p p' q0 : ℕ), (∀ i, (g i).Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 ∧
          GlobalTheory.Mem.An.NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) ∧
        p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧ p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧
        (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 ∧ ∀ i, p ≠ g i ∧ p' ≠ g i := by
  intro hN hS
  obtain ⟨C8, hC, hA⟩ := UpperTheory.T3.exists_three_primes_one_mod_le_rpow hS
  refine ⟨C8, hC, fun eps he he' => ?_⟩
  obtain ⟨x1, h1⟩ := UpperTheory.T3.typePrimesN hN eps he
  obtain ⟨x2, h2⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x3, h3⟩ := mod_small C8 eps hC he
  refine ⟨max x1 (max x2 x3), fun s R N d hs hx hR hM => ?_⟩
  obtain ⟨hx1, hx23⟩ := max_le_iff.1 hx
  obtain ⟨hx2, hx3⟩ := max_le_iff.1 hx23
  obtain ⟨-, -, hr5, hkr, -⟩ := h2 s R hs hx2 hR
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  obtain ⟨g, hg, hg01, hgd⟩ := h1 s.x hx1 N d R.k R.r hM hk (hk.trans hkr) hr5
  obtain ⟨-, -, hd, hN0, hdN, hlog⟩ := hM
  have hN30 : 30 ≤ N := le_trans (by omega) (Nat.le_of_dvd hN0 hdN)
  obtain ⟨p, p', q0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩ := hA N hN30
  have hb : s.b = Real.exp (s.x ^ eps) := by rw [← hs]; rfl
  rw [hb]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlt : (N : ℝ) ^ C8 < Real.exp (s.x ^ eps) := by
    rw [Real.rpow_def_of_pos hNpos]
    exact Real.exp_lt_exp.2 ((mul_le_mul_of_nonneg_right hlog (by linarith)).trans_lt (h3 s.x hx3))
  have hb1 : 1 ≤ Real.exp (s.x ^ eps) := Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast hk
  have hkb : Real.exp (s.x ^ eps) ≤ (R.k : ℝ) * Real.exp (s.x ^ eps) := le_mul_of_one_le_left (by linarith) hk1
  have hY : Real.exp (s.x ^ eps) ≤ ((R.k : ℝ) * Real.exp (s.x ^ eps)) ^ 8 :=
    hkb.trans (le_self_pow₀ (hb1.trans hkb) (by norm_num))
  refine ⟨g, p, p', q0, hg, hg01, hgd, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, fun i => ⟨?_, ?_⟩⟩
  · intro h
    have := (hg i).2.1
    rw [← h] at this
    linarith
  · intro h
    have := (hg i).2.1
    rw [← h] at this
    linarith
end

