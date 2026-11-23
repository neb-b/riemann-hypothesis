module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCloudLe
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_cloud_le : SzRow (fun C D L => (4 * L.Sc ≤ L.LaG * L.sc.b' / D.R.k) ∧
    (4 * C.P.CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.LaG * L.sc.b') ∧
    (Real.log (D.s.Del : ℝ) ≤ L.sc.x ^ (L.sc.eps / 4) / 2)) := by
  intro eps he he' C hC
  refine ⟨0, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps (cD + 11) 1 1 0 (by positivity) (by linarith) one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) cD 1 (1 / 2) 0 le_rfl (by positivity) (by norm_num)
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hCD : 1 ≤ C.P.CDelG := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  refine ⟨max (max x1 x2) (max x3 (128 * C.P.CDelG)), fun D L hε hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hΛ : 1 ≤ L.LaG := by
    rw [hV.La_eq]
    refine le_trans ?_ ((h1 L.sc hε hx1).2.2 C.GK hLa).1
    exact Real.one_le_rpow hx1'.le L.sc.eps_pos.le
  have hp1 : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hx1'.le hcD
  have hDel : (D.s.Del : ℝ) = (⌈L.sc.x ^ cD⌉₊ : ℝ) := by
    rw [hV.Del_eq]; simp [Delv]
  have hD2 : (D.s.Del : ℝ) ≤ 2 * L.sc.x ^ cD := by
    rw [hDel]
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)
    linarith
  have hD1 : 1 ≤ (D.s.Del : ℝ) := by
    rw [hDel]; exact hp1.trans (Nat.le_ceil _)
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (by positivity) hV.ranks.2.2.1.1
  have hk : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℕ) := by
    refine hV.ranks.2.2.1.2.trans ?_
    have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hε]; push_cast; linarith)
    rw [Real.rpow_natCast] at this
    linarith
  have hb : L.sc.x ^ cD * L.sc.x ^ (11 : ℕ) ≤ L.sc.b' := by
    have h := h2 L.sc.x hx2
    have e1 : L.sc.x ^ cD * L.sc.x ^ (11 : ℕ) = Real.exp ((cD + 11) * Real.log L.sc.x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0, Real.rpow_def_of_pos hx0, mul_comm]; norm_num
    have e2 : L.sc.b' = L.sc.x * Real.exp (L.sc.x ^ eps - L.sc.x ^ (eps / 3)) := by
      simp only [Scale.b', Scale.a, Scale.b, Scale.X', Scale.L, hε, Real.exp_sub]; ring
    rw [e1, e2]
    have h5 : Real.exp ((cD + 11) * Real.log L.sc.x) ≤ Real.exp (L.sc.x ^ eps - L.sc.x ^ (eps / 3)) :=
      Real.exp_le_exp.2 (by simp only [pow_zero, mul_one, one_mul] at h; linarith)
    have h6 := Real.exp_pos (L.sc.x ^ eps - L.sc.x ^ (eps / 3))
    nlinarith
  have key : 16 * C.P.CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.LaG * L.sc.b' := by
    have hk2 : (D.R.k : ℝ) ^ 2 ≤ (2 * L.sc.x ^ (5 : ℕ)) ^ 2 := by gcongr
    have hb0 : 0 ≤ L.sc.b' := le_trans (by positivity) hb
    calc 16 * C.P.CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)
        ≤ 16 * C.P.CDelG * (2 * L.sc.x ^ (5 : ℕ)) ^ 2 * (2 * L.sc.x ^ cD) := by gcongr
      _ = (128 * C.P.CDelG) * (L.sc.x ^ cD * L.sc.x ^ (10 : ℕ)) := by ring
      _ ≤ L.sc.x * (L.sc.x ^ cD * L.sc.x ^ (10 : ℕ)) := by gcongr
      _ = L.sc.x ^ cD * L.sc.x ^ (11 : ℕ) := by ring
      _ ≤ L.sc.b' := hb
      _ ≤ L.LaG * L.sc.b' := le_mul_of_one_le_left hb0 hΛ
  have hP : 0 ≤ (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hk0, L.Sc_eq]
    nlinarith
  · nlinarith
  · have h := h3 L.sc.x hx3
    simp only [pow_zero, mul_one, Real.rpow_zero] at h
    have h7 : Real.log (D.s.Del : ℝ) ≤ Real.log (2 * L.sc.x ^ cD) := Real.log_le_log (by linarith) hD2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h7
    have h8 := Real.log_two_lt_d9
    rw [hε]
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLaRhoBot
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_la_rho_bot : SzRow (fun _ _ L => SizeLa L ∧ SizeRho L ∧ SizeBot L) := by
  intro eps he he' C hC
  have hLa1 : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (eps + eps / 100)
    (2 * C.GK.La * CN ^ 2) 2 (by linarith)
  obtain ⟨x3, h3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    ((2 + 8 * eps + eps / 100) + -(eps / 8) + eps + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 32 0 (by linarith)
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    (eps / 100 + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 2 1 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max (max x1 x2) (max x3 x4)) 1, ?_⟩⟩⟩
  intro D L hε hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hone⟩ := hx
  have hpos : 0 < L.sc.x := by linarith
  obtain ⟨hlo, hhi⟩ := (h1 L.sc hε hx1).2.2 C.GK hLa1
  rw [← hV.La_eq] at hlo hhi
  have hup : L.LaG ≤ L.sc.x ^ (eps + eps / 100) := by
    have := h2 _ hx2
    rw [hε] at hhi
    calc L.LaG ≤ _ := hhi
      _ = 2 * C.GK.La * CN ^ 2 * L.sc.x ^ eps * Real.log L.sc.x ^ 2 := by ring
      _ ≤ _ := this
  refine ⟨⟨hlo, ?_⟩, ?_, ?_⟩
  · simpa only [szTh, hε] using hup
  · have hn := hV.ranks.n_le
    obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hV.ranks
    have h3' := h3 _ hx3
    have h4' := h4 _ hx4
    simp only [Real.rpow_add hpos, pow_zero, pow_one, mul_one] at h3' h4'
    rw [← Real.rpow_add hpos 2, ← Real.rpow_add hpos (2 + 8 * eps) (eps / 100), ← Real.rpow_add hpos (9 / 2),
      ← Real.rpow_add hpos eps (eps / 100)] at h3'
    rw [← Real.rpow_add hpos (9 / 2), ← Real.rpow_add hpos eps (eps / 100)] at h4'
    have hL0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hpos _).le hlo
    unfold SizeRho szNst szTh Scale.delta1
    rw [hε] at hn hk ⊢
    have hkpos : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hpos _) hk
    have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hone
    rw [← add_div, div_le_iff₀ hkpos]
    have hA : 4 * (2 * (D.R.n : ℝ) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps * L.LaG ≤
        4 * (2 * (2 * L.sc.x ^ (2 + 8 * eps + eps / 100)) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps *
          L.sc.x ^ (eps + eps / 100) := by gcongr
    have hB : L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.LaG ≤
        L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.sc.x ^ (eps + eps / 100) := by gcongr
    have hK : L.sc.x ^ (-2 : ℝ) * L.sc.x ^ (9 / 2 + 10 * eps) ≤ L.sc.x ^ (-2 : ℝ) * D.R.k := by gcongr
    linarith
  · intro t
    have := hV.bT_le t
    unfold szNst
    exact this

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowRankSizes
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_rankSizes : SzRow (fun _ _ L => SizeN L ∧ SizeM L ∧ SizeK L ∧ SizeT L ∧ SizeTT L ∧ SizeDe2 L ∧ SizeLw L) := by
  intro eps h0 h1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (100 / eps * (2 * C.P.Cpde) + 4455), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog' : 100 / eps * (2 * C.P.Cpde) + 4455 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hq : 0 < 100 / eps := by positivity
  have hC1 : 1 ≤ C.P.Cpde := hV.host.one_le
  have hlog : 100 / eps + 4455 ≤ Real.log L.sc.x := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * C.P.Cpde by linarith) hq.le
    linarith
  have hth : szTh L = eps / 100 := by rw [szTh, he]
  have hth0 : 0 ≤ szTh L := by rw [hth]; positivity
  have h2C : 2 * C.P.Cpde ≤ L.sc.x ^ szTh L := by
    rw [Real.rpow_def_of_pos hx0, hth]
    have a : 2 * C.P.Cpde ≤ Real.log L.sc.x * (eps / 100) := by
      have b : 100 / eps * (2 * C.P.Cpde) * (eps / 100) = 2 * C.P.Cpde := by field_simp
      have c : 100 / eps * (2 * C.P.Cpde) * (eps / 100) ≤ Real.log L.sc.x * (eps / 100) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have := Real.add_one_le_exp (Real.log L.sc.x * (eps / 100))
    linarith
  have h2 : 2 ≤ L.sc.x ^ szTh L := by linarith
  have hneg : L.sc.x ^ (-szTh L) ≤ 1 / 2 := by
    rw [Real.rpow_neg hx0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hlo : ∀ a : ℝ, L.sc.x ^ (a - szTh L) ≤ L.sc.x ^ a := fun a =>
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hhi : ∀ a : ℝ, 2 * L.sc.x ^ a ≤ L.sc.x ^ (a + szTh L) := fun a => by
    rw [Real.rpow_add hx0, mul_comm]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this
  have n2 : (D.R.n : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) := by
    refine (hV.ranks.n_le_of_o hV.host.o_le).trans ?_
    rw [Real.rpow_add hx0 (2 + 8 * L.sc.eps), mul_comm]
    exact mul_le_mul_of_nonneg_left h2C (by positivity)
  obtain ⟨⟨n1, -⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, -⟩ := hV.ranks
  obtain ⟨-, ⟨t1, t2⟩, d2, -, -, hLw, -⟩ := hV.host
  have hs := Real.sqrt_nonneg (L.sc.x * L.sc.delta1)
  have hd1 : 0 ≤ L.sc.delta1 := by unfold Scale.delta1; positivity
  refine ⟨⟨(hlo _).trans n1, n2⟩, ⟨?_, ?_⟩, ⟨(hlo _).trans k1, k2.trans (hhi _)⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hneg hs
    linarith
  · exact m2.trans (mul_le_mul_of_nonneg_right h2 hs)
  · have h := D.R.rank_add_five_le
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  · exact L.t_win.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
  · have := mul_le_mul_of_nonneg_right hneg (mul_nonneg hn.le hd1)
    calc L.sc.x ^ (-szTh L) * D.R.n * L.sc.delta1 = L.sc.x ^ (-szTh L) * (D.R.n * L.sc.delta1) := by ring
      _ ≤ 1 / 2 * (D.R.n * L.sc.delta1) := this
      _ = L.sc.delta1 * D.R.n / 2 := by ring
      _ ≤ _ := t1
  · exact t2.trans (le_of_eq (by unfold szNst; ring))
  · unfold SizeDe2
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact d2
  · unfold SizeLw
    rw [hLw, Lwv, he]
    have a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1 := Nat.ceil_lt_add_one (by positivity)
    have a3 : 100 / eps = 10 / 3 * (30 / eps) := by ring
    have a4 : 4455 * Real.log L.sc.x ≤ Real.log L.sc.x ^ 2 := by nlinarith
    push_cast
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSigGaps
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rankVal_crude (s : Scale) (R : Ranks) (hx : 2 ≤ s.x) (h : RankVal s R) :
    (0 < (R.n : ℝ) ∧ (R.n : ℝ) ≤ s.x ^ 4) ∧ (R.m : ℝ) ≤ s.x ^ 2 ∧ (R.k : ℝ) ≤ s.x ^ 6 := by
  have hn1 := h.n_lo
  have hn2 := h.n_le'
  obtain ⟨-, ⟨-, hm⟩, ⟨-, hk⟩, -⟩ := h
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have he' := s.eps_lt
  refine ⟨⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hn1, ?_⟩, ?_, ?_⟩
  · have h1 : s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ ((3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; norm_num)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 3 := by positivity
    have h3 : s.x ^ 4 = s.x * s.x ^ 3 := by ring
    nlinarith
  · have h1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have h2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
      apply Real.sqrt_le_iff.2
      refine ⟨hx0.le, ?_⟩
      nlinarith
    nlinarith
  · have h1 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 5 := by positivity
    have h3 : s.x ^ 6 = s.x * s.x ^ 5 := by ring
    nlinarith

theorem gap_crude (x C k m t : ℝ) (hx : 2 ≤ x) (hC : C ≤ x) (hk0 : 0 ≤ k) (hm0 : 0 ≤ m) (ht0 : 0 ≤ t)
    (hm : m ≤ x ^ 2) (hk : k ≤ x ^ 6) (ht : t ≤ x ^ 401) :
    C * k * m ^ 4 + (k + m * (t + 1)) * m ^ 10 < x ^ 430 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have a1 : C * k * m ^ 4 ≤ x * x ^ 6 * (x ^ 2) ^ 4 := by
    have : C * k * m ^ 4 ≤ x * k * m ^ 4 := by gcongr
    refine this.trans ?_
    gcongr
  have a2 : (1 : ℝ) ≤ x ^ 401 := one_le_pow₀ hx1
  have a3 : (k + m * (t + 1)) * m ^ 10 ≤ (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 := by gcongr
  have a4 : x * x ^ 6 * (x ^ 2) ^ 4 = x ^ 15 := by ring
  have a5 : (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 = x ^ 26 + 2 * x ^ 423 := by ring
  have a6 : x ^ 15 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a7 : x ^ 26 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a8 : (2 : ℝ) ^ 7 ≤ x ^ 7 := by gcongr
  have a9 : x ^ 430 = x ^ 7 * x ^ 423 := by ring
  have a10 : 0 < x ^ 423 := by positivity
  have a11 : 2 ^ 7 * x ^ 423 ≤ x ^ 7 * x ^ 423 := by gcongr
  rw [a9]
  rw [a4] at a1
  rw [a5] at a3
  generalize x ^ 423 = y at *
  linarith

theorem base_sizes_ge (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (n : ℕ), s.eps = eps → x0 ≤ s.x →
    0 < (n : ℝ) → (n : ℝ) ≤ s.x ^ 4 → s.x ^ 430 ≤ s.b ∧ s.x ^ 430 ≤ s.b' ∧ s.x ^ 430 ≤ s.w'' n := by
  obtain ⟨x0, h0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps 434 1 1 0 (by positivity)
    (by linarith) one_pos
  refine ⟨x0, fun s n hs hx hn0 hn => ?_⟩
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have h1 := h0 s.x hx
  rw [← hs] at h1
  simp only [pow_zero, one_mul, mul_one] at h1
  have hX0 : 0 < s.X' := Real.exp_pos _
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have h2 : s.x ^ 434 * s.X' ≤ s.b := by
    have e : s.x ^ 434 = Real.exp (434 * Real.log s.x) := by
      rw [show (434 : ℝ) = ((434 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
    rw [e, Scale.X', Scale.b, Scale.L, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h3 : s.x ^ 430 ≤ s.x ^ 434 := pow_le_pow_right₀ hx1 (by norm_num)
  have h4 : s.x ^ 434 ≤ s.b / s.X' := (le_div_iff₀ hX0).2 h2
  have h5 : 0 < s.x ^ 434 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · exact h3.trans ((le_mul_of_one_le_right h5.le hX1).trans h2)
  · have e : s.b' = s.x * (s.b / s.X') := by rw [Scale.b', Scale.a]; ring
    rw [e]
    exact h3.trans (h4.trans (le_mul_of_one_le_left (h5.le.trans h4) hx1))
  · have e : s.w'' n = (s.b / s.X') / n := by
      rw [Scale.w'', Scale.b', Scale.a]; field_simp
    rw [e, le_div_iff₀ hn0]
    refine le_trans ?_ h4
    calc s.x ^ 430 * n ≤ s.x ^ 430 * s.x ^ 4 := by gcongr
      _ = s.x ^ 434 := by ring

theorem szRow_sig_gaps : SzRow (fun C D L => (∀ τ, (∀ (i : ℕ) (h : i + 1 < D.R.k - 1), gapS D C.P.Cgap < (((D.hc τ).v ⟨i, by omega⟩ - (D.hc τ).v ⟨i + 1, h⟩ : ℚ) : ℝ)) ∧ (∀ (hk : 2 ≤ D.R.k) (hm : 0 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ + (D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ)) ∧ (∀ (j : ℕ) (h : j + 1 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)))) := by
  intro eps he _ C hC
  obtain ⟨x0, hx0⟩ := base_sizes_ge eps he
  refine ⟨430, fun cD hcD => ⟨430, fun ch hch => ⟨max x0 (max 2 C.P.Cgap), fun D L hs hx hV => ?_⟩⟩⟩
  have hxa : x0 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C.P.Cgap ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  obtain ⟨⟨hn0, hn⟩, hm, hk⟩ := rankVal_crude L.sc D.R hx2 hV.ranks
  obtain ⟨hb, hb', hw⟩ := hx0 L.sc D.R.n hs hxa hn0 hn
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by
    have h1 := L.t_win.2
    rw [hV.Ct_eq, hC.1.2.2.2.2.2.2.2.2.2, show (401 : ℝ) = ((401 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
    exact h1
  have hg : gapS D C.P.Cgap < L.sc.x ^ 430 := by
    have := gap_crude L.sc.x C.P.Cgap D.R.k D.R.m D.R.t hx2 hxC (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hm hk ht
    unfold gapS Ranks.N
    push_cast
    exact this
  have hp : 0 < L.sc.x ^ 430 := by positivity
  have hpow : ∀ c : ℝ, 430 ≤ c → L.sc.x ^ 430 ≤ (⌈L.sc.x ^ c⌉₊ : ℝ) := by
    intro c hc
    refine le_trans ?_ (Nat.le_ceil _)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; exact hc)
  obtain ⟨hv, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
  have hb1 : ∀ τ, L.sc.x ^ 430 ≤ (b1 τ : ℝ) := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at h1
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
      rw [htop τ ⟨t, htT⟩ hteq.symm]
      have h2 := L.bT_ge ⟨t, htT⟩
      have h3 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by
        exact_mod_cast Int.floor_nonneg.2 (div_nonneg (by linarith) (by linarith))
      push_cast
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have h3 := Int.le_ceil L.sc.b
        have h4 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (hthick τ h2).1
        linarith
      · rw [hthin τ ⟨(D.eTau τ).2, h1, h2⟩]
        exact hw.trans (Int.le_ceil _)
  generalize L.sc.x ^ 430 = y at *
  intro τ
  refine ⟨fun i h => ?_, fun hk2 hm0 => ?_, fun j h => ?_⟩
  · rw [hv, hv]
    have e : D.R.k - 2 - i = (D.R.k - 2 - (i + 1)) + 1 := by omega
    simp only [e]
    have := hpow cD hcD
    unfold Delv
    push_cast
    linarith
  · rw [hv, (hbj τ _).1]
    have := hb1 τ
    simp only [Nat.sub_self]
    push_cast
    linarith
  · rw [(hbj τ _).1, (hbj τ _).1]
    have := hpow ch hch
    unfold h0v
    push_cast
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowThinSizeGe
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_thinSize_ge : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.Cw ≤ L.sc.w'' D.R.n ∧ L.sc.b ^ C.P.cw ≤ L.sc.w'' D.R.n)) := by
  intro eps he he' C hC
  obtain ⟨x1, h1⟩ := GlobalTheory.scale_poly_comparison eps (5 * |(C.P.Cw : ℝ)|) (1 / 10) he (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 16, fun D L hs hx hV => ?_⟩⟩⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx16 : (16 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hone : (1 : ℝ) ≤ L.sc.x := by linarith
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  obtain ⟨⟨hn1, -⟩, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  rw [hs] at hn1 hk1 hk2
  have h2 : (2 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow (by norm_num) hx16 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have e : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [e] at h
  have hup : ∀ a b : ℝ, 1 / 4 + a ≤ b → 2 * L.sc.x ^ a ≤ L.sc.x ^ b := fun a b hab => by
    calc 2 * L.sc.x ^ a ≤ L.sc.x ^ ((1 : ℝ) / 4) * L.sc.x ^ a :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _)
      _ = L.sc.x ^ (1 / 4 + a) := (Real.rpow_add hx0 _ _).symm
      _ ≤ L.sc.x ^ b := Real.rpow_le_rpow_of_exponent_le hone hab
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := hV.ranks.n_le'.trans (hup _ _ (by norm_num))
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := hk2.trans (hup _ _ (by linarith))
  have hn0 : (1 : ℝ) ≤ D.R.n := (Real.one_le_rpow hone (by linarith)).trans hn1
  have hk0 : (1 : ℝ) ≤ D.R.k := (Real.one_le_rpow hone (by linarith)).trans hk1
  obtain ⟨-, -, -, -, -, hw, -⟩ := h1 L.sc hs hx1
  obtain ⟨hw, -, -⟩ := hw D.R.n (by exact_mod_cast hn0) hn3
  have hb1 : (1 : ℝ) ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hA : (1 : ℝ) ≤ L.sc.b ^ ((1 : ℝ) - 1 / 10) := Real.one_le_rpow hb1 (by norm_num)
  have hB : (1 : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := Real.one_le_rpow hone (by positivity)
  have hcw : C.P.cw = 9 / 10 := hC.2.2.2.2.1
  have hkC : (D.R.k : ℝ) ^ (C.P.Cw : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := by
    calc (D.R.k : ℝ) ^ (C.P.Cw : ℝ) ≤ (D.R.k : ℝ) ^ |(C.P.Cw : ℝ)| :=
          Real.rpow_le_rpow_of_exponent_le hk0 (le_abs_self _)
      _ ≤ (L.sc.x ^ (5 : ℝ)) ^ |(C.P.Cw : ℝ)| :=
          Real.rpow_le_rpow (by linarith) hk5 (abs_nonneg _)
      _ = L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := (Real.rpow_mul hx0.le _ _).symm
  refine ⟨?_, ?_⟩
  · refine hkC.trans (le_trans ?_ hw)
    exact le_mul_of_one_le_left (by linarith) hA
  · rw [hcw, show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num]
    exact le_trans (le_mul_of_one_le_right (by linarith) hB) hw

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValBOfInc
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem valB_of_inc : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT) (v : X.A.vT) (p p₁ : M.Pt), X.fm.seenP w = true → v ∈ V → M.Inc v p p₁ → Co.valB w V p₁ = Co.valB w (V.erase v) p := by
  intro D u X i M Co w V v p p₁ hw hv hI
  obtain ⟨-, hoff, x, -, -, hk, -⟩ := hI
  have key : ∀ v', (if X.fm.seenP w = true ∧ v' ∉ V then ((p₁.2 v').1.L : Set _) else (p₁.2 v').ker) =
      (if X.fm.seenP w = true ∧ v' ∉ V.erase v then ((p.2 v').1.L : Set _) else (p.2 v').ker) := by
    intro v'
    by_cases h : v' = v
    · subst h
      rw [if_neg (fun h => h.2 hv), if_pos ⟨hw, Finset.notMem_erase _ _⟩, hk]
    · rw [hoff v' h]
      have : v' ∈ V.erase v ↔ v' ∈ V := by simp [h]
      simp only [this]
  unfold PtModel.Coord.valB
  simp only [key]

end GlobalTheory.LvT
end

