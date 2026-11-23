module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTOPPLeB
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem f_mul_r_mul_L_le_pow_fourteen (s : Scale) (R : Ranks) (hx : 2 ≤ s.x) (hR : RankVal s R) :
    (R.f : ℝ) * (R.r : ℝ) * s.L ≤ s.x ^ 14 := by
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 ≤ s.x := by linarith
  have he0 := s.eps_pos
  have he1 := s.eps_lt
  obtain ⟨⟨-, hn⟩, ⟨-, hm⟩, ⟨-, hk⟩, -⟩ := hR
  have hpow : ∀ (a : ℝ) (n : ℕ), a ≤ n → s.x ^ a ≤ s.x ^ n := fun a n h => by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 h
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ 3 := by
    have h3 := hpow (2 + 8 * s.eps) 3 (by push_cast; linarith)
    have h2 : (R.f : ℝ) = 2 * (R.n : ℝ) := by simp [Ranks.f]
    rw [h2]
    linarith
  have hk5 : (R.k : ℝ) ≤ 2 * s.x ^ 5 := by
    have h5 := hpow (9 / 2 + 10 * s.eps) 5 (by push_cast; linarith)
    linarith
  have hm1 : (R.m : ℝ) ≤ 2 * s.x := by
    have hd : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hsq : Real.sqrt (s.x * s.delta1) ≤ s.x := by
      calc Real.sqrt (s.x * s.delta1) ≤ Real.sqrt (s.x ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [mul_le_mul_of_nonneg_left hd hx0]
        _ = s.x := Real.sqrt_sq hx0
    linarith
  have hx5 : s.x ≤ s.x ^ 5 := by
    have h4 : 1 ≤ s.x ^ 4 := one_le_pow₀ hx1
    nlinarith
  have hr : (R.r : ℝ) ≤ 4 * s.x ^ 5 := by
    have h1 : R.r ≤ R.k + R.m := Nat.sub_le _ _
    have h2 : (R.r : ℝ) ≤ R.k + R.m := by exact_mod_cast h1
    linarith
  have hL : s.L ≤ s.x := by
    calc s.x ^ s.eps ≤ s.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = s.x := Real.rpow_one _
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg hx0 _
  have h16 : (16 : ℝ) ≤ s.x ^ 5 := by
    have h1 : (2 : ℝ) ^ 5 ≤ s.x ^ 5 := pow_le_pow_left₀ (by norm_num) hx 5
    norm_num at h1
    linarith
  have hx3 := pow_nonneg hx0 3
  have hx5' := pow_nonneg hx0 5
  calc (R.f : ℝ) * R.r * s.L ≤ (4 * s.x ^ 3) * (4 * s.x ^ 5) * s.x :=
        mul_le_mul (mul_le_mul hf hr (by positivity) (by linarith)) hL hL0
          (mul_nonneg (by linarith) (by linarith))
    _ = 16 * s.x ^ 9 := by ring
    _ ≤ s.x ^ 5 * s.x ^ 9 := mul_le_mul_of_nonneg_right h16 (pow_nonneg hx0 9)
    _ = s.x ^ 14 := by ring

theorem szRow_TO_PP_le_b : SzRow (fun C D L => (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ))) := by
  intro eps heps heps' C hC
  obtain ⟨-, -, -, -, -, -, -, -, heP, -, -, -, -, hCP, -, hLast⟩ := hC
  have hCb : 1 ≤ C.T.Cb := hLast C.T.Cb (by simp [FC.cLast])
  obtain ⟨x1, hx1⟩ := GlobalTheory.scale_poly_comparison eps (1259 + C.T.Cb) (1 / 2) heps (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max x1 2) (4 * C.T.CP ^ 3), fun D L hLe hx hV => ?_⟩⟩⟩
  have hxK : 4 * C.T.CP ^ 3 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxx1 : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1' : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have hCP0 : 0 ≤ C.T.CP := by linarith

  have hXb := (hx1 L.sc hLe hxx1).2.2.1
  have hX' : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx0 _)
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0 _)
  have hxc : L.sc.x ^ (1259 + C.T.Cb) ≤ L.sc.b ^ (1 / 2 : ℝ) :=
    le_trans (le_mul_of_one_le_right (Real.rpow_nonneg hx0 _) hX') hXb
  have hbh : L.sc.b ^ (1 / 2 : ℝ) ≤ L.sc.b := by
    calc L.sc.b ^ (1 / 2 : ℝ) ≤ L.sc.b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
      _ = L.sc.b := Real.rpow_one _

  have hz : zBase L ≤ L.sc.x ^ 14 := f_mul_r_mul_L_le_pow_fourteen L.sc D.R hx2 hV.ranks
  obtain ⟨⟨hn1, -⟩, -, -, -⟩ := hV.ranks
  have hn : 1 ≤ (D.R.n : ℝ) := le_trans (Real.one_le_rpow hx1' (by linarith [L.sc.eps_pos])) hn1
  have hf1 : 1 ≤ (D.R.f : ℝ) := by
    have h2 : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by simp [Ranks.f]
    rw [h2]
    linarith
  have hr1 : 1 ≤ (D.R.r : ℝ) := by
    have h2 := D.R.two_le_m
    have h3 : 1 ≤ D.R.r := by
      unfold Ranks.r
      omega
    exact_mod_cast h3
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1' (le_of_lt L.sc.eps_pos)
  have hz1 : 1 ≤ zBase L := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hL1
  have hz0 : 0 ≤ zBase L := by linarith
  have hz12 : zBase L ^ (12 : ℝ) = zBase L ^ (12 : ℕ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hP1 : 1 ≤ C.T.CP * zBase L ^ (12 : ℝ) := by
    rw [hz12]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hz1)
  have hP2 : C.T.CP * zBase L ^ (12 : ℝ) ≤ C.T.CP * L.sc.x ^ 168 := by
    rw [hz12]
    apply mul_le_mul_of_nonneg_left _ hCP0
    calc zBase L ^ 12 ≤ (L.sc.x ^ 14) ^ 12 := pow_le_pow_left₀ hz0 hz 12
      _ = L.sc.x ^ 168 := by ring
  have hT1 : (1 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := by
    have h1 : 0 < TOv L.sc := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxpos _)
    exact_mod_cast h1
  have hT2 : ((TOv L.sc : ℕ) : ℝ) ≤ 2 * L.sc.x ^ 377 := by
    have h1 : ((TOv L.sc : ℕ) : ℝ) < L.sc.x ^ (377 : ℝ) + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0 _)
    have h2 : L.sc.x ^ (377 : ℝ) = L.sc.x ^ (377 : ℕ) := by
      rw [show (377 : ℝ) = ((377 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : 1 ≤ L.sc.x ^ (377 : ℕ) := one_le_pow₀ hx1'
    rw [h2] at h1
    linarith
  have hCb1 : 1 ≤ L.sc.x ^ C.T.Cb := Real.one_le_rpow hx1' (by linarith)
  have hW : (C.T.CP * zBase L ^ (12 : ℝ)) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤
      L.sc.x ^ (1259 + C.T.Cb) := by
    have h1 : (C.T.CP * zBase L ^ (12 : ℝ)) ^ 3 ≤ (C.T.CP * L.sc.x ^ 168) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hP2 3
    have h2 : ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ (2 * L.sc.x ^ 377) ^ 2 := pow_le_pow_left₀ (by linarith) hT2 2
    have h3 := mul_le_mul h1 h2 (by positivity) (pow_nonneg (mul_nonneg hCP0 (pow_nonneg hx0 _)) _)
    have h4 : (C.T.CP * L.sc.x ^ 168) ^ 3 * (2 * L.sc.x ^ 377) ^ 2 = 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 := by ring
    have h5 : 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 ≤ L.sc.x ^ 1259 := by
      calc 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 ≤ L.sc.x * L.sc.x ^ 1258 :=
            mul_le_mul_of_nonneg_right hxK (pow_nonneg hx0 _)
        _ = L.sc.x ^ 1259 := by ring
    have h6 : L.sc.x ^ (1259 : ℕ) * L.sc.x ^ C.T.Cb = L.sc.x ^ (1259 + C.T.Cb) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hxpos]
      norm_num
    rw [← h6]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0 _)
    rw [← h4] at h5
    exact le_trans h3 h5
  beta_reduce
  rw [heP]
  generalize ((TOv L.sc : ℕ) : ℝ) = T at hT1 hW ⊢
  generalize C.T.CP * zBase L ^ (12 : ℝ) = P at hP1 hW ⊢
  have hTP : T * P ≤ P ^ 3 * T ^ 2 := by
    have hP3 : P ≤ P ^ 3 := by nlinarith [one_le_pow₀ (n := 2) hP1]
    have hT' : T ≤ T ^ 2 := by nlinarith
    calc T * P ≤ T ^ 2 * P ^ 3 := mul_le_mul hT' hP3 (by linarith) (by positivity)
      _ = P ^ 3 * T ^ 2 := by ring
  have hW' : P ^ 3 * T ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ) := by
    have h1 : P ^ 3 * T ^ 2 ≤ P ^ 3 * T ^ 2 * L.sc.x ^ C.T.Cb :=
      le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by linarith) 3) (sq_nonneg T)) hCb1
    linarith
  have hTPx : T * P * L.sc.x ^ C.T.Cb ≤ P ^ 3 * T ^ 2 * L.sc.x ^ C.T.Cb :=
    mul_le_mul_of_nonneg_right hTP (Real.rpow_nonneg hx0 _)
  refine ⟨?_, ?_, ?_, hW'⟩
  · linarith
  · linarith
  · linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTopsBandBottoms
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bandWidth_real_inequality_le_inv_sq {x e n δ k La A c : ℝ} (hx : 1 < x) (hδ : δ ≤ 1)
    (hn : n ≤ 2 * x ^ (2 + 8 * e)) (hn0 : 0 ≤ n) (hk : x ^ (9 / 2 + 10 * e) ≤ k) (hLa0 : 0 ≤ La)
    (hLa : La ≤ A * Real.log x ^ 2 * x ^ e) (hc : 0 ≤ c)
    (h1 : 32 * A * x ^ (2 + 10 * e) * Real.log x ^ 2 ≤ x ^ (5 / 2 + 10 * e))
    (h2 : 2 * c * A * x ^ e * Real.log x ^ 3 ≤ x ^ (5 / 2 + 10 * e)) :
    4 * (2 * n * δ) * x ^ e * La / k + c * Real.log x * La / k ≤ x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hk0 : 0 < k := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hk
  have he0 : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (2 + 10 * e) = x ^ (2 + 8 * e) * x ^ e * x ^ e := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ (5 / 2 + 10 * e) = x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hnδ : n * δ ≤ 2 * x ^ (2 + 8 * e) := (mul_le_of_le_one_right hn0 hδ).trans hn
  have t1 : 4 * (2 * n * δ) * x ^ e * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc 4 * (2 * n * δ) * x ^ e * La = 8 * (n * δ) * x ^ e * La := by ring
      _ ≤ 8 * (2 * x ^ (2 + 8 * e)) * x ^ e * (A * Real.log x ^ 2 * x ^ e) := by
          gcongr
      _ = (32 * A * x ^ (2 + 10 * e) * Real.log x ^ 2) / 2 := by rw [e1]; ring
      _ ≤ _ := by linarith
  have t2 : c * Real.log x * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc c * Real.log x * La ≤ c * Real.log x * (A * Real.log x ^ 2 * x ^ e) := by gcongr
      _ = (2 * c * A * x ^ e * Real.log x ^ 3) / 2 := by ring
      _ ≤ _ := by linarith
  rw [← add_div, div_le_iff₀ hk0]
  have t3 : x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) ≤ x ^ (-2 : ℝ) * k :=
    mul_le_mul_of_nonneg_left hk (Real.rpow_pos_of_pos hx0 _).le
  linarith

theorem szRow_tops_band_bottoms :
    SzRow (fun C D L => ((D.host.TT.card : ℝ) ≤ Nstar L) ∧ (rhoP L C.P.Crho ≤ L.sc.x ^ (-2 : ℝ)) ∧
      (∀ t, (L.bT t : ℝ) ≤ L.sc.b' + Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k)) := by
  intro eps h0 h1 C hC
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hrho : 1 ≤ C.P.Crho := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨CN, x1, hx1⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  obtain ⟨x2, hx2⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (2 + 10 * eps) (5 / 2 + 10 * eps) (32 * (2 * C.GK.La * CN ^ 2)) 2 (by linarith)
  obtain ⟨x3, hx3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (5 / 2 + 10 * eps) (2 * C.P.Crho * (2 * C.GK.La * CN ^ 2)) 3 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 (max x2 x3), fun D L he hx V => ⟨?_, ?_, ?_⟩⟩⟩⟩
  · have := V.host.2.1.2
    unfold LevelStarExponents.Nstar
    linarith
  · have hx1' : x1 ≤ L.sc.x := (le_max_left _ _).trans hx
    have hx2' : x2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
    have hx3' : x3 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
    obtain ⟨-, -, hK⟩ := hx1 L.sc he hx1'
    obtain ⟨hlo, hup⟩ := hK C.GK hLa
    have hxp : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
    have a2 := hx2 _ hx2'
    have a3 := hx3 _ hx3'
    rw [← he] at a2 a3
    unfold rhoP LevelStarExponents.Nstar
    rw [V.La_eq]
    have hδ : L.sc.delta1 ≤ L.sc.x ^ (-(L.sc.eps / 100)) :=
      Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by have := L.sc.eps_pos; linarith)
    have hδ0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hxp.le _
    have hn : (D.R.n : ℝ) * L.sc.delta1 ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) := by
      calc (D.R.n : ℝ) * L.sc.delta1
          ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-(L.sc.eps / 100)) :=
            mul_le_mul V.ranks.n_le hδ hδ0 (by positivity)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hxp]; congr 2; ring
    have key := bandWidth_real_inequality_le_inv_sq (A := 2 * C.GK.La * CN ^ 2) (c := C.P.Crho) L.sc.one_lt_alt (le_refl (1 : ℝ))
      hn (mul_nonneg (Nat.cast_nonneg _) hδ0) V.ranks.2.2.1.1 ((Real.rpow_pos_of_pos hxp _).le.trans hlo)
      (hup.trans (le_of_eq (by ring))) (by linarith) a2 a3
    rw [mul_one, ← mul_assoc 2] at key
    exact key
  · exact V.bT_le

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowWindowLength
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem lA_le_pow_seven {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (hV : Val C cD ch L) :
    lA L ≤ L.sc.x ^ (7 : ℝ) := by
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hk : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ) := by
    have h1 := hV.ranks.2.2.1.2
    have h2 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by
      have := D.R.two_le_m
      have := D.R.m_le_f
      unfold Ranks.n
      omega
    exact_mod_cast this
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact hV.host.2.2.1
  have hd' : L.sc.x ^ (-1 : ℝ) ≤ L.de2 :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) hd
  have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hdp := L.thickDensity_pos
  unfold lA
  rw [div_le_iff₀ (by positivity)]
  have e7 : L.sc.x ^ (7 : ℝ) * L.sc.x ^ (-1 : ℝ) = L.sc.x ^ (5 : ℝ) * L.sc.x ^ (1 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  calc (D.R.k : ℝ) * L.sc.x ^ L.sc.eps ≤ (2 * L.sc.x ^ (5 : ℝ)) * L.sc.x ^ (1 : ℝ) := by gcongr
    _ = L.sc.x ^ (7 : ℝ) * (2 * L.sc.x ^ (-1 : ℝ)) := by
        rw [mul_assoc, ← e7]; ring
    _ ≤ L.sc.x ^ (7 : ℝ) * ((D.R.m : ℝ) * L.de2) := by gcongr

theorem nN_div_m_le {C : FC} (hCt : C.Ct = 401) {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (hV : Val C cD ch L) :
    (D.R.n : ℝ) * D.R.N D.R.m / D.R.m ≤ 4 * L.sc.x ^ (404 : ℝ) := by
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hn : (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (3 : ℝ) := by
    have h1 := hV.ranks.n_le'
    have h2 : L.sc.x ^ ((9 : ℝ) / 4) ≤ L.sc.x ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    linarith
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ (401 : ℝ) := by
    have h := L.t_win.2
    rwa [hV.Ct_eq, hCt] at h
  have hm2 := D.R.two_le_m
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hN : D.R.N D.R.m ≤ 2 * D.R.t * D.R.m := by
    have h := D.R.rank_add_five_le
    have h1 : D.R.k + 1 ≤ D.R.t := by omega
    unfold Ranks.N
    nlinarith
  have hN' : (D.R.N D.R.m : ℝ) ≤ 2 * D.R.t * D.R.m := by exact_mod_cast hN
  rw [div_le_iff₀ hm]
  have e : L.sc.x ^ (404 : ℝ) = L.sc.x ^ (3 : ℝ) * L.sc.x ^ (401 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  calc (D.R.n : ℝ) * D.R.N D.R.m ≤ (2 * L.sc.x ^ (3 : ℝ)) * (2 * D.R.t * D.R.m) := by gcongr
    _ ≤ (2 * L.sc.x ^ (3 : ℝ)) * (2 * L.sc.x ^ (401 : ℝ) * D.R.m) := by gcongr
    _ = 4 * L.sc.x ^ (404 : ℝ) * D.R.m := by rw [e]; ring

theorem szRow_windowLength : SzRow (fun C D L => (∀ l : ℕ, 11 ≤ l → ∃ j : ℕ, lA L ≤ ((l : ℝ) - 1) ^ j ∧ 2 * j + 2 ≤ D.host.Lw) ∧ ((D.host.Lw : ℝ) ≤ C.P.CLw * Real.log L.sc.x) ∧ ((L.j0 : ℝ) ≤ C.P.Cj0 * Real.log L.sc.x)) := by
  intro eps h0 h1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (60 / eps + 34), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog : 60 / eps + 34 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hq : 0 < 60 / eps := by positivity
  have hLw : D.host.Lw = Lwv L.sc := hV.host.2.2.2.2.2.1
  have hCt : C.Ct = 401 := by
    have h := hC.1
    unfold FC.Fixed at h
    tauto
  refine ⟨fun l hl => ⟨⌈7 * Real.log L.sc.x⌉₊, ?_, ?_⟩, ?_, ?_⟩
  · have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
    have he1 : Real.exp 1 ≤ (l : ℝ) - 1 := by
      have := Real.exp_one_lt_d9
      linarith
    calc lA L ≤ L.sc.x ^ (7 : ℝ) := lA_le_pow_seven hV
      _ = Real.exp (7 * Real.log L.sc.x) := by rw [Real.rpow_def_of_pos hx0, mul_comm]
      _ ≤ Real.exp ((⌈7 * Real.log L.sc.x⌉₊ : ℕ) * 1) := by
          rw [mul_one]; exact Real.exp_le_exp.2 (Nat.le_ceil _)
      _ = Real.exp 1 ^ ⌈7 * Real.log L.sc.x⌉₊ := Real.exp_nat_mul _ _
      _ ≤ ((l : ℝ) - 1) ^ ⌈7 * Real.log L.sc.x⌉₊ := by gcongr
  · have : ⌈7 * Real.log L.sc.x⌉₊ ≤ ⌈(405 : ℝ) * Real.log L.sc.x⌉₊ := Nat.ceil_mono (by linarith)
    rw [hLw, Lwv]; omega
  · rw [hLw, hC.2.2.1, Lwv, he]
    have a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1 := Nat.ceil_lt_add_one (by positivity)
    have a3 : 60 / eps = 2 * (30 / eps) := by ring
    push_cast
    linarith
  · rw [hV.logFiveDepth_eq, hC.2.2.2.1]
    have hb := nN_div_m_le hCt hV
    have hm2 := D.R.two_le_m
    have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
    have hn : (0 : ℝ) < D.R.n := by
      have : 0 < D.R.n := by
        have := D.R.two_le_m
        have := D.R.m_le_f
        unfold Ranks.n
        omega
      exact_mod_cast this
    have hN : (0 : ℝ) < D.R.N D.R.m := by
      have h := D.R.m_add_three_le_k
      have : 0 < D.R.N D.R.m := by unfold Ranks.N; omega
      exact_mod_cast this
    have hy : 0 < (D.R.n : ℝ) * D.R.N D.R.m / D.R.m := by positivity
    have l4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have l2 := Real.log_two_gt_d9
    have l2' := Real.log_two_lt_d9
    have l5 : Real.log 4 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
    have hl : Real.log ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ Real.log 4 + 404 * Real.log L.sc.x := by
      refine (Real.log_le_log hy hb).trans (le_of_eq ?_)
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
    have hlb : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ 400 * Real.log L.sc.x := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    have a1 : (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 400 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : ((⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ : ℕ) : ℝ) ≤ (⌈(400 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) := by
      exact_mod_cast Nat.ceil_mono hlb
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupleChainSharpColumnValuationOfTwisted
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwSharp

variable {D : D7} {u : D.what₂.Word}

theorem weight_eq (X Y : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j)) :
    (X.fm.lam j τ).w a = (Y.fm.lam j τ).w a := by
  have h := (X.fm.lam_eq j hj τ a).trans (Y.fm.lam_eq j hj τ a).symm
  exact_mod_cast h

theorem weightSup_eq (X Y : Ch D u) (τ : D.what₂.Tau) : TauWeight X τ = TauWeight Y τ := by
  unfold TauWeight
  refine Finset.sup_congr rfl fun i hi => Finset.sup_congr rfl fun a _ => ?_
  rw [weight_eq X Y i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) τ a]

theorem exponent_eq (X Y : Ch D u) : ETpi X = ETpi Y := by
  unfold ETpi Wt; simp only [weightSup_eq X Y]

theorem tupleChainSharpColumnValuation_of_twisted : ∀ (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup),
    Step0Tie Tw u μ → Conclusion5Sharp (tw Tw u μ) → TupleChainSharpColumnValuation Tw u μ := by
  intro D u Tw μ hT h w hw c n hc hn x hx
  have hw' : OverT (tw Tw u μ) w := hw.trans (Tw.A_T u μ).symm
  have hown : ET (own D u) w = EatT D u w := rfl
  have hE : ET (tw Tw u μ) w = EatT D u w := by
    rw [← hown]; unfold ET
    rw [exponent_eq (tw Tw u μ) (own D u)]
    show (if (Tw.fm u μ).seenP w = true then _ else _) = _
    rw [(hT w hw).1]
  obtain ⟨y, hy, e⟩ := h w hw' c n hc (hE ▸ hn) (Tw.e0 u μ x) ((hT w hw).2 x hx)
  refine ⟨y, hy, e.trans ?_⟩
  show _ • (D.chTw u μ).col ((Tw.fm u μ).emb 0 (Tw.e0 u μ x)) = _
  rw [Tw.embed_mul_block_embedding]

end GlobalTheory.LvT.TwSharp
end
end

