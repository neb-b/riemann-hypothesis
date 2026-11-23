module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0072

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeDel
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeDel : SzRow (fun _ _ L => SizeDel L) := by
  intro eps he he' C hC
  refine ⟨412, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (cD + 12) 1 he one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) cD 1 (1 / 2) 0 le_rfl
    (by positivity) (by norm_num)
  obtain ⟨x4, h4⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  have hCp : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x5, h5⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he he' hCp
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max x5 32), fun D L hε hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hx5, hx6⟩ := hx
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hΛ : 1 ≤ L.LaG := by
    rw [hV.La_eq]
    refine le_trans ?_ ((h1 L.sc hε hx1).2.2 C.GK hLa).1
    exact Real.one_le_rpow hx1'.le L.sc.eps_pos.le
  have hp1 : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hx1'.le (by linarith)
  have hDel : (D.s.Del : ℝ) = (⌈L.sc.x ^ cD⌉₊ : ℝ) := by
    rw [hV.Del_eq]; simp [Delv]
  have hD2 : (D.s.Del : ℝ) ≤ 2 * L.sc.x ^ cD := by
    rw [hDel]
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)
    linarith
  have hD0 : L.sc.x ^ cD ≤ (D.s.Del : ℝ) := by
    rw [hDel]; exact Nat.le_ceil _
  have hD1 : 1 ≤ (D.s.Del : ℝ) := hp1.trans hD0
  obtain ⟨hf, hm, hr, hkr, -, hL, -, -, -, -, -, -, -, -, hN, -, -⟩ := h4 L.sc D.R hε hx4 hV.ranks
  obtain ⟨-, -, -, -, -, hrd1, -, hrd, -, -⟩ := h5 L.sc D.R D.host hε hx5 hV.ranks hV.host
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (by positivity) hV.ranks.2.2.1.1
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℕ) := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    rw [← Real.rpow_natCast]; push_cast; linarith
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ (402 : ℕ) := by
    rw [← Real.rpow_natCast]; push_cast; exact hN
  have hθ : L.sc.x ^ szTh L ≤ L.sc.x := by
    have : L.sc.x ^ szTh L ≤ L.sc.x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [szTh, hε]; linarith)
    rwa [Real.rpow_one] at this
  have hθ0 : 0 < L.sc.x ^ szTh L := by positivity
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hn : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    have : D.R.n ≤ D.R.f := by simp only [Ranks.f]; omega
    exact_mod_cast this
  obtain ⟨hw, hwb, -⟩ := (h2 L.sc hε hx2).2.2.2.2.2.1 D.R.n hn1 hn
  have hw' : L.sc.x ^ cD * L.sc.x ^ (12 : ℕ) ≤ L.sc.w'' D.R.n := by
    rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_add hx0] at hw
    rw [← Real.rpow_natCast]; push_cast; exact hw
  have h412 : L.sc.x ^ (412 : ℕ) ≤ (D.s.Del : ℝ) := by
    refine le_trans ?_ hD0
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by push_cast; exact hcD)
  have key : 16 * L.sc.x * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n := by
    calc 16 * L.sc.x * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)
        ≤ 16 * L.sc.x * (L.sc.x ^ (5 : ℕ)) ^ 2 * (2 * L.sc.x ^ cD) := by gcongr
      _ = 32 * (L.sc.x ^ cD * L.sc.x ^ (11 : ℕ)) := by ring
      _ ≤ L.sc.x * (L.sc.x ^ cD * L.sc.x ^ (11 : ℕ)) := by gcongr
      _ = L.sc.x ^ cD * L.sc.x ^ (12 : ℕ) := by ring
      _ ≤ _ := hw'
  have hP : 0 ≤ (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) := by positivity
  have hwΛ : L.sc.w'' D.R.n ≤ L.LaG * L.sc.b' := by
    have hb0 : 0 ≤ L.sc.b' := le_trans (le_trans (by positivity) hw') hwb
    exact hwb.trans (le_mul_of_one_le_left hb0 hΛ)
  have hxP : (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.sc.x * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) :=
    le_mul_of_one_le_left hP hx1'.le
  have hθP : L.sc.x ^ szTh L * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) ≤
      L.sc.x * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) := mul_le_mul_of_nonneg_right hθ hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ L.sc.x ^ (402 : ℕ) * L.sc.x ^ 10 := by gcongr
      _ = L.sc.x ^ (412 : ℕ) := by rw [← pow_add]
      _ ≤ _ := h412
  · calc L.sc.x ^ szTh L * D.R.m * D.R.N D.R.m ≤ L.sc.x * L.sc.x * L.sc.x ^ (402 : ℕ) := by gcongr
      _ = L.sc.x ^ (404 : ℕ) := by ring
      _ ≤ L.sc.x ^ (412 : ℕ) := pow_le_pow_right₀ hx1'.le (by norm_num)
      _ ≤ _ := h412
  · have h := h3 L.sc.x hx3
    simp only [pow_zero, mul_one, Real.rpow_zero] at h
    have h7 : Real.log (D.s.Del : ℝ) ≤ Real.log (2 * L.sc.x ^ cD) := Real.log_le_log (by linarith) hD2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h7
    have h8 := Real.log_two_lt_d9
    rw [hε]
    linarith
  · rw [L.Sc_eq]
    linarith
  · have hmk : (D.R.m : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : D.R.m ≤ D.R.k)
    calc L.sc.x ^ szTh L * D.R.m * D.R.k * (D.s.Del : ℝ)
        ≤ L.sc.x ^ szTh L * D.R.k * D.R.k * (D.s.Del : ℝ) := by gcongr
      _ ≤ _ := by linarith
  · rw [le_div_iff₀ hk0, L.Sc_eq]
    linarith
  · linarith
  · have hv : Real.log D.host.v ≤ L.sc.x := by
      refine le_trans ?_ (hrd.trans hL)
      unfold Host.v
      exact Real.log_le_log (by linarith) (by linarith)
    have hk3 : L.sc.x ^ (3 : ℕ) ≤ (D.R.k : ℝ) := by
      refine le_trans ?_ hV.ranks.2.2.1.1
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hε]; push_cast; linarith)
    calc L.sc.x ^ szTh L * D.R.m * Real.log D.host.v ≤ L.sc.x ^ szTh L * D.R.m * L.sc.x := by gcongr
      _ ≤ L.sc.x * L.sc.x * L.sc.x := by gcongr
      _ = L.sc.x ^ (3 : ℕ) := by ring
      _ ≤ _ := hk3

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeGSizeWords
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem log_le_of_le_two_mul_pow_eight {x a y k g : ℝ} (hx : 1 < x) (ha : a ≤ 5) (hy : 0 ≤ y) (hk0 : 0 < k)
    (hk : k ≤ 2 * x ^ a) (hg0 : 0 < g) (hg : g ≤ 2 * (k * Real.exp y) ^ 8) :
    Real.log g ≤ 40 * Real.log x + 9 * y + 9 := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h1 : Real.log k ≤ Real.log 2 + a * Real.log x := by
    have := Real.log_le_log hk0 hk
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 a).ne', Real.log_rpow hx0] at this
  have h2 : Real.log g ≤ Real.log 2 + 8 * (Real.log k + y) := by
    have := Real.log_le_log hg0 hg
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_mul hk0.ne' (Real.exp_pos y).ne', Real.log_exp, Nat.cast_ofNat] at this
  have h3 : a * Real.log x ≤ 5 * Real.log x := mul_le_mul_of_nonneg_right ha hlx.le
  linarith

theorem szRow_sizeG : SzRow (fun _ _ L => SizeG L) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow eps (eps + eps / 100) 40 9 1 0 he.le
    (by linarith) one_pos
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨x0, ?_⟩⟩⟩
  intro D L hLe hx hV i j
  obtain ⟨-, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, hg, -⟩ := hV.host
  have hx1 := L.sc.one_lt_alt
  have hxp : 0 < L.sc.x := by linarith
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk1
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  refine ⟨(hg i).1, (hg i).2.trans (by linarith [(hg j).1]), ?_⟩
  have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le (by positivity) (hg i).1
  have hL0 : 0 ≤ L.sc.L := (Real.rpow_pos_of_pos hxp _).le
  have h1 := log_le_of_le_two_mul_pow_eight hx1 (by rw [hLe]; linarith) hL0 hk0 hk2 hg0 (hg i).2
  have h2 := hx0 L.sc.x hx
  have h3 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (eps + eps / 100) := by
    simp only [szTh, Scale.L, hLe]
    rw [← Real.rpow_add hxp, add_comm]
  rw [h3]
  simp only [Scale.L, hLe] at h1
  rw [pow_zero, mul_one, one_mul] at h2
  exact h1.trans h2

theorem szRow_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) :=
  szRow_and_imp.1 _ _ szRow_sizeG szRow_card_words_le

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeKRel
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX


set_option maxHeartbeats 800000 in
theorem sizeKRel_of_rankVal {D : D7} (L : SizeData₂ D) (hR : RankVal L.sc D.R)
    (hK : 100 + 8 * |L.CGam| ≤ L.sc.x ^ (L.sc.eps / 1000)) (hrd : Real.log D.host.rdE ≤ L.sc.L) :
    SizeKRel L := by
  unfold SizeKRel szTh rankBudget
  generalize L.sc = s at *
  generalize L.CGam = c at *
  generalize Real.log D.host.rdE = ρ at *
  generalize D.R = R at *
  have hn2 := hR.n_le
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, -⟩ := hR
  have hx := s.one_lt_alt
  have hxp : 0 < s.x := lt_trans one_pos hx
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hc0 := abs_nonneg c
  have hc1 := le_abs_self c
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun h => Real.rpow_le_rpow_of_exponent_le hx.le h
  have pos : ∀ a : ℝ, 0 < s.x ^ a := fun a => Real.rpow_pos_of_pos hxp a
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx.le h
  have mul : ∀ {u v a b : ℝ}, u ≤ s.x ^ a → 0 ≤ v → v ≤ s.x ^ b → u * v ≤ s.x ^ (a + b) := by
    intro u v a b hu hv hv'
    rw [Real.rpow_add hxp]
    exact mul_le_mul hu hv' hv (pos _).le
  have mulL : ∀ {u v a b : ℝ}, s.x ^ a ≤ u → s.x ^ b ≤ v → s.x ^ (a + b) ≤ u * v := by
    intro u v a b hu hv
    rw [Real.rpow_add hxp]
    exact mul_le_mul hu hv (pos _).le ((pos _).le.trans hu)
  have pw : ∀ {u a : ℝ} (j : ℕ), 0 ≤ u → u ≤ s.x ^ a → u ^ j ≤ s.x ^ (a * j) := by
    intro u a j hu h
    rw [Real.rpow_mul_natCast hxp.le]
    exact pow_le_pow_left₀ hu h j
  have ab : ∀ {a C : ℝ}, C ≤ 100 → C * s.x ^ a ≤ s.x ^ (s.eps / 1000 + a) :=
    fun hC => mul (by linarith) (pos _).le le_rfl
  have hsq : Real.sqrt (s.x * s.delta1) = s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
    have : s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hxp, Real.rpow_one]; rfl
    rw [this, Real.sqrt_eq_rpow, ← Real.rpow_mul hxp.le]
    congr 1; ring
  rw [hsq] at hm1 hm2
  have h2m := R.two_le_m
  have hmk := R.m_add_three_le_k
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hkr' : (R.k : ℝ) ≤ R.r := by exact_mod_cast hkr
  have hfk : (R.f : ℝ) ≤ R.k := by exact_mod_cast R.f_le_k
  have hfn : (R.f : ℝ) = 2 * R.n := by unfold Ranks.f; push_cast; ring
  have h2m' : (2 : ℝ) ≤ R.m := by exact_mod_cast h2m
  have k5 : (5 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 5 ≤ R.k)
  have n0 : (0 : ℝ) ≤ R.n := by positivity
  have f0 : (0 : ℝ) ≤ R.f := by positivity
  have m0 : (0 : ℝ) ≤ R.m := by positivity
  have hf : (R.f : ℝ) ≤ s.x ^ (s.eps / 1000 + (2 + 8 * s.eps + s.eps / 100)) := by
    have := ab (C := 4) (a := 2 + 8 * s.eps + s.eps / 100) (by norm_num)
    linarith
  have hf2 : s.x ^ (2 + 8 * s.eps) ≤ (R.f : ℝ) := by linarith
  have hk : (R.k : ℝ) ≤ s.x ^ (s.eps / 1000 + (9 / 2 + 10 * s.eps)) :=
    hk2.trans (ab (by norm_num))
  have hm : (R.m : ℝ) ≤ s.x ^ (s.eps / 1000 + (1 / 2 - s.eps / 16)) :=
    hm2.trans (ab (by norm_num))
  have hL : s.L ≤ s.x ^ s.eps := le_rfl
  have hL1 : 1 ≤ s.L := one e0.le
  have L0 : 0 ≤ s.L := by linarith
  have hlog : ∀ y : ℝ, 5 ≤ y → 1 ≤ Real.log y := by
    intro y hy
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlk := hlog _ k5
  have hlr := hlog R.r (by linarith)
  have hsx : Real.sqrt s.x = s.x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hR0 : s.x ^ ((2 + 8 * s.eps) + -s.eps) ≤ (R.n : ℝ) * s.x ^ (-s.eps) := mulL hn1 le_rfl
  have hlf0 : 0 ≤ Real.log R.f := Real.log_natCast_nonneg _
  have hlf : Real.log R.f ≤ s.x ^ ((1 : ℝ) / 5) := by
    have h1 := Real.log_le_rpow_div f0 (show (0 : ℝ) < 1 / 30 by norm_num)
    have h2 : (R.f : ℝ) ^ ((1 : ℝ) / 30) ≤ s.x ^ ((1 : ℝ) / 10) := by
      calc (R.f : ℝ) ^ ((1 : ℝ) / 30) ≤ (s.x ^ (3 : ℝ)) ^ ((1 : ℝ) / 30) :=
            Real.rpow_le_rpow f0 (hf.trans (mono (by linarith))) (by norm_num)
        _ = _ := by rw [← Real.rpow_mul hxp.le]; norm_num
    have h3 := (ab (C := 30) (a := 1 / 10) (by norm_num)).trans (mono (b := 1 / 5) (by linarith))
    linarith
  have hlf2 : Real.log R.f ^ 2 ≤ s.x ^ ((2 : ℝ) / 5) :=
    (pw 2 hlf0 hlf).trans (mono (by norm_num))
  have hm4 : 4 * s.x ^ ((2 : ℝ) / 5) ≤ R.m :=
    ((ab (by norm_num)).trans (mono (by linarith))).trans hm1
  have h25 : 1 ≤ s.x ^ ((2 : ℝ) / 5) := one (by norm_num)
  have hthL : s.x ^ (s.eps / 100) * s.L ≤ R.f :=
    ((mul le_rfl L0 hL).trans (mono (by linarith))).trans hf2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ hk1
    refine (mul (mul (mul (mul le_rfl (by positivity) (pw 5 m0 hm)) f0 hf) L0 hL) (pos _).le le_rfl).trans (mono ?_)
    push_cast; linarith
  · refine le_trans ?_ hk1
    have h8 : 8 * c ≤ s.x ^ (s.eps / 1000) := by linarith
    refine (mul (mul (mul h8 (by positivity) (pw 5 m0 hm)) f0 hf) L0 hL).trans (mono ?_)
    push_cast; linarith
  · rw [hsx]
    refine hk.trans (le_trans (mono ?_) (mulL (mulL le_rfl hn1) hR0))
    linarith
  · rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith), sq]
    refine hk.trans (le_trans (mono ?_) (mulL (mulL hR0 hR0) hm1))
    linarith
  · refine le_trans ?_ hk1
    refine (mul (pw 2 m0 hm) L0 hL).trans (mono ?_)
    push_cast; linarith
  · refine le_trans ?_ hk1
    have h1 : Real.log s.x ≤ s.x ^ (1 : ℝ) := by
      rw [Real.rpow_one]; linarith [Real.log_le_sub_one_of_pos hxp]
    rw [hsx]
    refine (mul (mul hm (pos _).le le_rfl) (Real.log_nonneg hx.le) h1).trans (mono ?_)
    linarith
  · refine le_trans ?_ (hk1.trans (le_mul_of_one_le_right (by linarith) hlk))
    refine (mul (mul le_rfl (by positivity) (pw 6 m0 hm)) L0 hL).trans (mono ?_)
    push_cast; linarith
  · refine le_trans ?_ (hk1.trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hlk)))
    refine (mul_le_mul_of_nonneg_left hrd (by positivity)).trans ?_
    refine (mul (mul (mul le_rfl (by positivity) (pw 3 m0 hm)) L0 hL) L0 hL).trans (mono ?_)
    push_cast; linarith
  · refine Real.le_sqrt_of_sq_le ?_
    have h1 : R.m ≤ 2 * R.rS + 2 := by
      obtain ⟨j, hj⟩ := R.m_even
      unfold Ranks.rS; omega
    have h2 : (R.m : ℝ) ≤ 2 * R.rS + 2 := by exact_mod_cast h1
    linarith
  · have h1 : (R.m : ℝ) ≤ (R.m : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have h2 : (R.m : ℝ) ^ 2 ≤ (R.m : ℝ) ^ 2 * s.L := le_mul_of_one_le_right (by positivity) hL1
    linarith
  · have h1 : Real.log (Real.log s.b) ≤ s.L := by
      unfold Scale.b
      rw [Real.log_exp]
      linarith [Real.log_le_sub_one_of_pos (show 0 < s.L by linarith)]
    have h2 : (R.f : ℝ) ≤ R.r * R.f := le_mul_of_one_le_left f0 (by linarith)
    have h3 : (R.r : ℝ) * R.f ≤ R.r * R.f * Real.log R.r := le_mul_of_one_le_right (by positivity) hlr
    have h4 := mul_le_mul_of_nonneg_left h1 (pos (s.eps / 100)).le
    linarith
  · exact hthL.trans (le_mul_of_one_le_right f0 hlk)
  · rw [hfn]
    exact mul_le_mul_of_nonneg_right (le_trans h2m' (le_self_pow₀ (by linarith) (by norm_num))) n0
  · exact (hfk.trans hkr').trans (le_self_pow₀ (by linarith) (by norm_num))

theorem szRow_sizeKRel : SzRow (fun _ _ L => SizeKRel L) := by
  intro eps he0 he1 C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, hx1⟩ := hostBounds eps C.P.Cpde he0 he1 hC8
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 ((100 + 8 * |C.CGam|) ^ (eps / 1000)⁻¹), ?_⟩⟩⟩
  intro D L hLe hx hV
  refine sizeKRel_of_rankVal L hV.ranks ?_ ?_
  · rw [hV.CGam_eq, hLe]
    have h0 : (0 : ℝ) ≤ 100 + 8 * |C.CGam| := by positivity
    calc 100 + 8 * |C.CGam| = ((100 + 8 * |C.CGam|) ^ (eps / 1000)⁻¹) ^ (eps / 1000) :=
          (Real.rpow_inv_rpow h0 (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hx) (by positivity)
  · exact (hx1 L.sc D.R D.host hLe ((le_max_left _ _).trans hx) hV.ranks hV.host).2.2.2.2.2.2.2.1

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTOLower
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem factor_products_le_rpow_three_hundred_seventy_seven (x c W Dy k f m d : ℝ) (hx : 1 ≤ x) (hc0 : 0 ≤ c) (hc : c ^ 4 ≤ x)
    (hW0 : 0 ≤ W) (hW : W ^ 4 ≤ x ^ 330) (hD0 : 0 ≤ Dy) (hD : Dy ≤ x ^ 12)
    (hk0 : 0 ≤ k) (hk : k ≤ x ^ 5) (hf0 : 0 ≤ f) (hm : 1 ≤ m) (hkf : k * f / m ≤ x ^ 7)
    (hd : 1 / x ≤ d) :
    (c * W) ^ 4 * Dy ^ 3 * k * f * x / (m * d) ≤ x ^ 377 ∧ Dy * k / m ≤ x ^ 377 := by
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < m := by linarith
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hd' : 1 / d ≤ x := by
    rw [div_le_iff₀ hd0]
    rw [div_le_iff₀ hx0] at hd
    linarith
  refine ⟨?_, ?_⟩
  · calc (c * W) ^ 4 * Dy ^ 3 * k * f * x / (m * d)
        = c ^ 4 * W ^ 4 * Dy ^ 3 * (k * f / m) * x * (1 / d) := by field_simp
      _ ≤ x * x ^ 330 * (x ^ 12) ^ 3 * x ^ 7 * x * x := by gcongr
      _ = x ^ 376 := by ring
      _ ≤ x ^ 377 := pow_le_pow_right₀ hx (by norm_num)
  · calc Dy * k / m ≤ Dy * k := div_le_self (by positivity) hm
      _ ≤ x ^ 12 * x ^ 5 := by gcongr
      _ = x ^ 17 := by ring
      _ ≤ x ^ 377 := pow_le_pow_right₀ hx (by norm_num)

theorem szRow_TO_lower : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ^ 4 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ C.T.Cp / ((D.R.m : ℝ) * L.de2) ≤ ((TOv L.sc : ℕ) : ℝ)) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) * D.R.k / D.R.m ≤ ((TOv L.sc : ℕ) : ℝ))) := by
  intro eps he he' C hC
  obtain ⟨x1, hx1⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps he he'
  have hCp : C.T.Cp = 1 := hC.2.2.2.2.2.2.2.1
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  have hCP : 1000 ≤ C.T.CP := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 (C.T.CP ^ 4), ?_⟩⟩⟩
  intro D L hLe hx V
  simp only [max_le_iff] at hx
  obtain ⟨hxa, hxP⟩ := hx
  obtain ⟨-, -, hr, hkr, -, -, hL1, -, hZ, hD, hkf, -⟩ := hx1 L.sc D.R hLe hxa V.ranks
  have hxx := L.sc.one_lt_alt
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by
      have := D.R.two_le_m
      have := D.R.m_le_f
      unfold Ranks.n
      omega
    exact_mod_cast this
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact V.host.2.2.1
  have hT : L.sc.x ^ (377 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := Nat.le_ceil _
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hZ0 : 0 ≤ zBase L := by
    unfold zBase
    have : (0:ℝ) ≤ L.sc.L := by linarith
    positivity
  have hZ' : zBase L ≤ L.sc.x ^ ((687 : ℝ) / 100) := hZ
  set x := L.sc.x with hxdef
  have hx1' : 1 ≤ x := hxx.le
  have hx0 : 0 < x := by linarith
  have cast : ∀ n : ℕ, x ^ ((n : ℕ) : ℝ) = x ^ n := fun n => Real.rpow_natCast x n
  have hPe : zBase L ^ C.T.eP = zBase L ^ (12 : ℕ) := by
    rw [heP]; first | rfl | exact_mod_cast Real.rpow_natCast _ 12
  have hd' : 1 / x ≤ L.de2 := by
    refine le_trans ?_ hd
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx1' (by rw [hLe]; linarith)
  have hW : (zBase L ^ (12 : ℕ)) ^ 4 ≤ x ^ 330 := by
    calc (zBase L ^ (12 : ℕ)) ^ 4 = zBase L ^ 48 := by ring
      _ ≤ (x ^ ((687 : ℝ) / 100)) ^ 48 := by gcongr
      _ = x ^ ((687 : ℝ) / 100 * ((48 : ℕ) : ℝ)) := (Real.rpow_mul_natCast hx0.le _ _).symm
      _ ≤ x ^ ((330 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)
      _ = x ^ 330 := cast 330
  have hk : (D.R.k : ℝ) ≤ x ^ 5 := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (by exact_mod_cast hr)
  have hT' : x ^ 377 ≤ ((TOv L.sc : ℕ) : ℝ) := by exact_mod_cast hT
  obtain ⟨a, b⟩ := factor_products_le_rpow_three_hundred_seventy_seven x C.T.CP (zBase L ^ (12 : ℕ)) ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ)
    D.R.k D.R.f D.R.m L.de2 hx1' (by linarith) hxP (by positivity) hW (Nat.cast_nonneg _)
    (by exact_mod_cast hD) (Nat.cast_nonneg _) hk (Nat.cast_nonneg _) (by linarith)
    (by exact_mod_cast hkf) hd'
  refine ⟨?_, b.trans hT'⟩
  rw [hPe, hCp]
  first
    | (rw [Real.rpow_one]; exact a.trans hT')
    | (rw [pow_one]; exact a.trans hT')

end GlobalTheory.EX
end

