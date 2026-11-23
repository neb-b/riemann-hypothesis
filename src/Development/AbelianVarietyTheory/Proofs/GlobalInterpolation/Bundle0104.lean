module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TameGeneratorWindow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InjectiveOfOrder
section
noncomputable section

namespace GlobalTheory.ClassDuty

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField GlobalTheory.EX GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow

theorem exists_large (eps A : ℝ) (he : 0 < eps) (hA : 0 < A) :
    ∃ x0 : ℝ, ∀ x ≥ x0, A * (x ^ (eps / 5) * Real.log x ^ 2) < x ^ (eps / 3) ∧ 2 ≤ x ^ (eps / 16) ∧ 44 ^ 3 ≤ x := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 2 * eps / 15) (by positivity)).bound
    (c := 1 / (2 * A)) (by positivity)
  have h' := (tendsto_rpow_atTop (y := eps / 16) (by positivity)).eventually_ge_atTop 2
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp ((h.and h').and (Filter.eventually_ge_atTop ((44 : ℝ) ^ 3)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨h1, h3⟩, h2⟩ := hx0 x hx
  have hx0 : 0 < x := by linarith [show (0 : ℝ) < 44 ^ 3 by norm_num]
  refine ⟨?_, h3, h2⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at h1
  have e : x ^ (eps / 3) = x ^ (eps / 5) * x ^ (2 * eps / 15) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hp : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos hx0 _
  have hq : 0 < x ^ (2 * eps / 15) := Real.rpow_pos_of_pos hx0 _
  have h4 : A * Real.log x ^ 2 ≤ x ^ (2 * eps / 15) / 2 := by
    calc A * Real.log x ^ 2 ≤ A * (1 / (2 * A) * x ^ (2 * eps / 15)) := by gcongr
      _ = _ := by field_simp
  rw [e]
  nlinarith

theorem poly_lt {x w y : ℝ} (hx : 44 ^ 3 ≤ x) (hw : Real.log x ≤ w) (hy : 500 * w < y) :
    8 * x ^ (406 : ℝ) < Real.exp y := by
  have hx0 : 0 < x := by linarith [show (0 : ℝ) < 44 ^ 3 by norm_num]
  have hx1 : 1 ≤ x := by linarith [show (1 : ℝ) < 44 ^ 3 by norm_num]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  calc 8 * x ^ (406 : ℝ) ≤ x * x ^ (406 : ℝ) := by
        gcongr; linarith [show (8 : ℝ) < 44 ^ 3 by norm_num]
    _ = x ^ (407 : ℝ) := by rw [show (407 : ℝ) = 1 + 406 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    _ = Real.exp (Real.log x * 407) := Real.rpow_def_of_pos hx0 _
    _ < Real.exp y := Real.exp_lt_exp.2 (by linarith)


set_option maxHeartbeats 1000000 in
theorem windowsAt_of (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (C : FC) (hC : Std C) :
    ∃ x0 : ℝ, ∀ (cD ch : ℝ) (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L → ParameterChoice' D L →
      WindowsAt L C.P.CY ∧ L.sc.X' ≤ lJ L := by
  have h8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hY : 1 ≤ C.P.CY := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨x1, h1⟩ := exists_large eps (500 + 2 * C.P.Cpde + 2 * C.P.CY) he (by linarith)
  obtain ⟨x2, h2⟩ := rank_basic_bounds eps he he'
  obtain ⟨x3, h3⟩ := hostBounds eps C.P.Cpde he he' h8
  refine ⟨max x1 (max x2 x3), fun cD ch D L hs hx h P => ?_⟩
  obtain ⟨hA, h16, h44⟩ := h1 _ ((le_max_left _ _).trans hx)
  obtain ⟨hf, hm, hr, hkr, -, -, hL1, -, -, -, -, -, -, ht, hN, hm1, hm2⟩ :=
    h2 _ _ hs (((le_max_left _ _).trans (le_max_right _ _)).trans hx) h.ranks
  obtain ⟨-, hq, -, hd, hcond, -, -, -, hp, hp'⟩ :=
    h3 _ _ _ hs (((le_max_right _ _).trans (le_max_right _ _)).trans hx) h.ranks h.host
  obtain ⟨⟨hn1, hn2⟩, ⟨hm1', hm2'⟩, ⟨hk1, hk2⟩, -⟩ := h.ranks
  have hg := h.host.2.2.2.2.1
  have hqp : D.host.q.Prime := D.host.hyp.1
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  subst hs
  clear h1 h2 h3 hx
  set s := L.sc with hs
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx1.le h
  have hlog : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9, show (3 : ℝ) < 44 ^ 3 by norm_num]
  set w := s.x ^ (s.eps / 5) * Real.log s.x ^ 2 with hw
  have h5 : 1 ≤ s.x ^ (s.eps / 5) := one (by linarith)
  have hl2 : Real.log s.x ≤ Real.log s.x ^ 2 := le_self_pow₀ hlog two_ne_zero
  have hlw : Real.log s.x ≤ w := hl2.trans (le_mul_of_one_le_left (sq_nonneg _) h5)
  have h5w : s.x ^ (s.eps / 5) ≤ w := le_mul_of_one_le_right (by linarith) (hlog.trans hl2)
  have hw1 : 1 ≤ w := hlog.trans hlw
  set u := s.x ^ (s.eps / 3) with hu
  have hA1 : 500 * w < u := (mul_le_mul_of_nonneg_right (by linarith only [h8, hY]) (by linarith only [hw1])).trans_lt hA
  have hA2 : 2 * C.P.Cpde * w < u :=
    (mul_le_mul_of_nonneg_right (by linarith only [h8, hY]) (by linarith only [hw1])).trans_lt hA
  have hA3 : 2 * C.P.CY * w < u :=
    (mul_le_mul_of_nonneg_right (by linarith only [h8, hY]) (by linarith only [hw1])).trans_lt hA
  have hcond' : Real.log ((D.host.QS : ℝ) * D.host.q * D.host.d) ≤ 2 * w := by rw [hw, ← mul_assoc]; exact hcond
  have hpw : Real.log D.host.pde < u := by
    refine lt_of_le_of_lt ?_ hA2
    rw [hw, ← mul_assoc]; exact hp
  have hpw' : Real.log D.host.pde' < u := by
    refine lt_of_le_of_lt ?_ hA2
    rw [hw, ← mul_assoc]; exact hp'
  have hX : s.X' = Real.exp u := rfl
  have hpoly : 8 * s.x ^ (406 : ℝ) < s.X' := poly_lt h44 hlw hA1
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by linarith)
  have hu2 : 2 * u ≤ s.L := by
    have : s.L = s.x ^ (2 * s.eps / 3) * u := by
      rw [hu, ← Real.rpow_add hx0, Scale.L]; congr 1; ring
    rw [this]
    have := h16.trans (mono (b := 2 * s.eps / 3) (by linarith))
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hXb : s.X' * s.X' ≤ s.b := by
    rw [hX, ← Real.exp_add, Scale.b]; exact Real.exp_le_exp.2 (by linarith)
  have hXb' : s.X' ≤ s.b := (le_mul_of_one_le_left (by linarith) hX1).trans hXb
  have hb1 : 1 ≤ s.b := hX1.trans hXb'
  have hk5 : (D.R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.2 hkr).trans hr
  have hk0 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : 1 ≤ D.R.k)
  have hm0 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hn0 : (1 : ℝ) ≤ D.R.n := (one (by linarith)).trans hn1
  have hlt : ∀ p : ℕ, p.Prime → Real.log p < u → (p : ℝ) < s.X' := fun p hp h =>
    (Real.log_lt_iff_lt_exp (by exact_mod_cast hp.pos)).1 h
  refine ⟨⟨⟨⟨hn1, hn2, ?_⟩, ⟨?_, ?_⟩, hk1, hk2⟩, ⟨?_, ?_, ?_, ?_, hn2, hk2⟩, ⟨((D.R.k : ℝ) * s.b) ^ 8, le_rfl, ?_, ?_, hg⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
  · have : s.x ^ (1 : ℝ) ≤ D.R.n := (mono (by linarith)).trans hn1
    rw [Real.rpow_one] at this
    have : (4 : ℝ) ≤ D.R.n := by linarith [show (4 : ℝ) < 44 ^ 3 by norm_num]
    exact_mod_cast this
  · rw [← Real.sqrt_eq_rpow]; exact hm1'
  · rw [← Real.sqrt_eq_rpow]; exact hm2'
  · exact (mono (by linarith)).trans hm1
  · have : s.x ^ (1 / 2 : ℝ) = s.x ^ (s.eps / 16) * s.x ^ (1 / 2 - s.eps / 16) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [this]
    exact hm2.trans (mul_le_mul_of_nonneg_right h16 (by positivity))
  · have h1 : s.x ^ (1 / 3 : ℝ) ≤ D.R.m := (mono (by linarith)).trans hm1
    have h2 : (44 : ℝ) ≤ s.x ^ (1 / 3 : ℝ) := by
      calc (44 : ℝ) = ((44 : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ _ := Real.rpow_le_rpow (by positivity) h44 (by norm_num)
    exact_mod_cast h2.trans h1
  · linarith
  · have e : (((D.R.k : ℝ) * s.b) ^ 8) ^ (1 / 4 : ℝ) = ((D.R.k : ℝ) * s.b) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]; norm_num
    have c0 : (0 : ℝ) < (LevelStarExponents.condE D : ℝ) := by
      have := hqp.pos; have := hdp.pos; have := D.host.QS_pos
      unfold LevelStarExponents.condE; push_cast; positivity
    have c1 : (LevelStarExponents.condE D : ℝ) ^ C.P.CY ≤ s.b := by
      rw [Real.rpow_def_of_pos c0]
      refine le_trans (Real.exp_le_exp.2 ?_) hXb'
      have : Real.log (LevelStarExponents.condE D : ℝ) ≤ 2 * w := by
        unfold LevelStarExponents.condE; push_cast; exact hcond'
      have := mul_le_mul_of_nonneg_right this (show 0 ≤ C.P.CY by linarith)
      linarith only [this, hA3]
    have c2 : (D.R.r : ℝ) ^ 4 ≤ s.b := by
      calc (D.R.r : ℝ) ^ 4 ≤ (s.x ^ (5 : ℝ)) ^ 4 := by gcongr
        _ = s.x ^ (20 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
        _ ≤ s.x ^ (406 : ℝ) := mono (by norm_num)
        _ ≤ s.b := by linarith [one (show (0 : ℝ) ≤ 406 by norm_num)]
    rw [e]
    calc (D.R.r : ℝ) ^ 4 * (LevelStarExponents.condE D : ℝ) ^ C.P.CY ≤ s.b * s.b := by gcongr
      _ = (1 * s.b) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · have c2 : 2 * (D.R.k : ℝ) ^ 8 ≤ s.b := by
      calc 2 * (D.R.k : ℝ) ^ 8 ≤ 2 * (s.x ^ (5 : ℝ)) ^ 8 := by gcongr
        _ = 2 * s.x ^ (40 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
        _ ≤ 2 * s.x ^ (406 : ℝ) := by linarith [mono (show (40 : ℝ) ≤ 406 by norm_num)]
        _ ≤ s.b := by linarith [one (show (0 : ℝ) ≤ 406 by norm_num)]
    calc 2 * ((D.R.k : ℝ) * s.b) ^ 8 = 2 * (D.R.k : ℝ) ^ 8 * s.b ^ 8 := by ring
      _ ≤ s.b * s.b ^ 8 := by gcongr
      _ = s.b ^ 9 := by ring
  · exact hlt _ hqp (by linarith)
  · exact hlt _ hdp (by linarith)
  · exact hlt _ D.host.pde_prime hpw
  · exact hlt _ D.host.pde'_prime hpw'
  · have hb0 : 0 < s.b := by linarith
    have e : s.X'' D.R.n = s.x * D.R.n * s.X' := by
      unfold Scale.X'' Scale.w'' Scale.b' Scale.a
      field_simp
    rw [e]
    exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hx1.le hn0)
  · have c1 := (rank_mul_le hx0 (Nat.cast_nonneg _) hf hN).trans (mono (b := 406) (by norm_num))
    linarith [one (show (0 : ℝ) ≤ 406 by norm_num)]
  · have hw'' : s.w'' D.R.n ≤ s.b := by
      have e : s.w'' D.R.n = s.b / (D.R.n * s.X') := by
        unfold Scale.w'' Scale.b' Scale.a
        field_simp
      rw [e]
      exact div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le hn0 hX1)
    have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have hS : L.Sc ≤ s.b := ((le_mul_of_one_le_left L.Sc_pos.le hk0).trans P.kS_le).trans hw''
    have hE : L.etaSz ≤ s.b :=
      ((le_mul_of_one_le_left L.etaSz_pos.le (one_le_mul_of_one_le_of_one_le hm0 (by linarith))).trans P.mteta).trans hw''
    have hh : 3 * hWidth L ≤ 15 * s.b := by
      have := P.t_le_eta
      unfold hWidth; linarith
    have hh0 : 0 < 3 * hWidth L := by
      have := L.Sc_pos; have := L.etaSz_pos
      unfold hWidth; linarith
    have hlg : Real.log (3 * hWidth L) ≤ 4 * s.L := by
      have c1 := Real.log_le_log hh0 hh
      rw [Real.log_mul (x := 15) (by norm_num) (by linarith), Scale.b, Real.log_exp] at c1
      have c2 : Real.log 15 ≤ 3 := by
        rw [Real.log_le_iff_le_exp (by norm_num), show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
        have := Real.exp_one_gt_d9
        have h7 : 7 ≤ Real.exp 1 * Real.exp 1 := by nlinarith only [this]
        nlinarith only [this, h7]
      linarith
    have hmt : (D.R.m : ℝ) + D.R.t ≤ 2 * s.x ^ (401 : ℝ) := by
      have := mono (show (1 : ℝ) ≤ 401 by norm_num)
      rw [Real.rpow_one] at this
      linarith
    have e : s.x ^ (406 : ℝ) = s.x ^ (5 : ℝ) * s.x ^ (401 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
    unfold lJ
    rw [le_div_iff₀ (lJ_den_pos L)]
    have hl0 : 0 ≤ Real.log (3 * hWidth L) := by
      apply Real.log_nonneg
      have := L.Sc_pos; have := L.etaSz_pos
      unfold hWidth; linarith
    calc s.X' * ((D.R.k : ℝ) * ((D.R.m : ℝ) + D.R.t) * Real.log (3 * hWidth L))
        ≤ s.X' * (s.x ^ (5 : ℝ) * (2 * s.x ^ (401 : ℝ)) * (4 * s.L)) := by gcongr
      _ = s.X' * (8 * s.x ^ (406 : ℝ)) * s.L := by rw [e]; ring
      _ ≤ s.X' * s.X' * s.L := by gcongr
      _ ≤ (1 * s.b) * s.L := by rw [one_mul]; exact mul_le_mul_of_nonneg_right hXb (by linarith)
      _ ≤ (D.R.m : ℝ) * s.b * s.L := by gcongr

end GlobalTheory.ClassDuty

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.MuOffMove

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem ordDet_congr {E : Type} [Field E] [NumberField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {N₁ N₂ : Submodule (𝓞 E) (Sp E n)} (h : localization₂ P.asIdeal N₁ = localization₂ P.asIdeal N₂) : ordDet P N₁ = ordDet P N₂ := by
  unfold ordDet frameAt
  rw [h]

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

theorem natCast_mem_under (Q : HeightOneSpectrum (𝓞 X.E)) (p : ℕ) :
    ((p : ℕ) : 𝓞 X.F) ∈ Q.asIdeal.under (𝓞 X.F) ↔ ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal := by
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast]

theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem level_notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (Pr.T u : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩
  · exact notMem_of_mem_QE hsel h (hPr.T_prime u) hS

theorem mem_vT (hPr : Pr.Ok) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal := by
  have h0 : Pr.piT u ≠ 0 := by
    refine left_ne_zero_of_mul (b := X.conjO (Pr.piT u)) ?_
    rw [hPr.piT_norm u]
    exact_mod_cast (hPr.T_prime u).ne_zero
  refine ⟨decoFin_mem_of_mem_divs, fun h => ?_⟩
  unfold Primes.vT divs
  have hf : {P : HeightOneSpectrum (𝓞 X.E) | Pr.piT u ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {Pr.piT u}) (by simpa using h0)).subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  rw [dite_eq_left hf]
  simpa using h

theorem conjP_notMem_vT (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vT u) : conjPrime₂ P ∉ Pr.vT u :=
  fun h => conj_piT_notMem hPr u ⟨P, hP⟩ ((mem_conjP _ _).1 ((mem_vT hPr u _).1 h))


open Classical in
def term (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)

theorem term_finite (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (Function.mulSupport (term sel SB mU N)).Finite := by
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  refine ((GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.preimage hinj.injOn).subset fun v hv h0 => hv ?_
  unfold term
  split_ifs
  · rfl
  · rw [h0, zpow_zero, Units.val_one]

open Classical in
theorem term_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ} (hU : ∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) {n : ℕ}
    {N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)} (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂) (hA : AgreeOff (Pr.T u) N₁ N₂)
    (v : HeightOneSpectrum (𝓞 X.F)) :
    term sel (rowSG Pr sel mu) mU N₁ v =
      (∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * term sel (rowSG Pr sel mu) mU N₂ v := by
  by_cases hv : ∃ P ∈ Pr.vT u, P.under (𝓞 X.F) = v
  · obtain ⟨P, hP, hPv⟩ := hv
    have hPv' : P.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal hPv
    have hc := conjP_notMem_vT hPr hP
    have hsp := (split_of_conj_ne₂ X P v hX (fun e => hc (e.symm ▸ hP)) hPv').2
    have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = {P} := by
      ext Q
      rw [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun ⟨hQ, hQv⟩ => ?_, fun e => e ▸ ⟨hP, hPv⟩⟩
      exact ((hsp Q).1 (congrArg HeightOneSpectrum.asIdeal hQv)).resolve_right fun e => hc (e ▸ hQ)
    have hno : ¬ ∃ Q ∈ rowSG Pr sel mu, Q.asIdeal.under (𝓞 X.F) = v.asIdeal := by
      rintro ⟨Q, hQ, hQv⟩
      refine level_notMem_rowSG hPr hsel hS hQ ?_
      rw [← natCast_mem_under, hQv, ← hPv', natCast_mem_under]
      exact T_mem hPr u ⟨P, hP⟩
    unfold term
    rw [hfil, Finset.prod_singleton, if_neg hno, if_neg hno, ← Units.val_mul]
    congr 1
    unfold idxExp
    rcases (hsp (sel v)).1 (hsel v) with e | e
    · rw [e, ← zpow_add]
      congr 1
      ring
    · rw [e, hU P hP, GlobalTheory.OrdDetConj.ordDet_conjP h₁, GlobalTheory.OrdDetConj.ordDet_conjP h₂, inv_zpow', inv_zpow', ← zpow_add]
      congr 1
      ring
  · have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun Q hQ e => hv ⟨Q, hQ, e⟩
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
      intro h
      rw [← hPr.piT_norm u] at h
      rcases (sel v).isPrime.mem_or_mem h with h | h
      · exact hv ⟨sel v, (mem_vT hPr u _).2 h, HeightOneSpectrum.ext (hsel v)⟩
      · exact hv ⟨conjPrime₂ (sel v), (mem_vT hPr u _).2 ((mem_conjP _ _).2 h),
          HeightOneSpectrum.ext ((under_conjP hX _).trans (hsel v))⟩
    unfold term
    rw [hfil, Finset.prod_empty, one_mul, ordDet_congr (hA _ hT)]

theorem muOff_move : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (n : ℕ) (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → (∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) → IsSdLat N₁ → IsSdLat N₂ → AgreeOff (Pr.T u) N₁ N₂ → muOff sel (rowSG Pr sel mu) mU N₁ = (∏ P ∈ Pr.vT u, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * muOff sel (rowSG Pr sel mu) mU N₂ := by
  intro X Pr sel S mu u mU n N₁ N₂ hX hPr hsel hS _ hU h₁ h₂ hA
  classical
  change ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₁ v = _ * ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₂ v
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 X.F) =>
      ∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) ⊆
      ((Pr.vT u).image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    by_contra hn
    apply hv
    refine Finset.prod_eq_one fun P hP => absurd ?_ hn
    rw [Finset.mem_filter] at hP
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨P, hP.1, hP.2⟩)
  rw [finprod_congr (term_eq (mu := mu) hX hPr hsel hS hU h₁ h₂ hA),
    finprod_mul_distrib ((Finset.finite_toSet _).subset hsub) (term_finite hsel _ mU h₂),
    finprod_eq_prod_of_mulSupport_subset _ hsub,
    Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]

end GlobalTheory.MuOffMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWHlatIff
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem mem_locW_hlat_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok), S.Ok → ∀ (w : Pl.Pl) (x : (S.hlat emb lam h).V), x ∈ locW Pl w (S.hlat emb lam h).L ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  intro E K ι _ _ _ _ _ _ _ emb Pl pw hv n S lam h hS w x
  unfold locW
  simp only [vl_mem_span_intW_iff Pl pw hv]
  unfold Formalism.HermitianLatticesTheory.localization₂
  constructor
  · rintro ⟨s, hs, hsx⟩ c
    exact ⟨s, hs, hsx c⟩
  · classical
    intro hx
    choose t ht htx using hx
    have : ∀ b, Finite (MulAction.orbitRel.Quotient (S.G b) (S.D b)) := hS.fin_orb
    let _ : Fintype S.Cl := Fintype.ofFinite _
    refine ⟨∏ c, t c, Submonoid.prod_mem _ fun c _ => ht c, fun c => ?_⟩
    have hc := (delAtr emb lam (S.Lsh c.1 (S.rep c))).smul_mem (∏ d ∈ Finset.univ.erase c, t d) (htx c)
    rw [← mul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ c)] at hc
    exact hc

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOnePrimeElements
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_host : ∀ (R : Ranks) (H : Host R) (M p : ℕ), 1 ≤ M → NormOne H.d M p → (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)}) ∧ p % M = 1 % M := by
  intro R H M p _ h
  obtain ⟨π, hN, hB, hA⟩ := h
  have h' : GlobalTheory.Mem.An.NormOne H.d M p := ⟨π.1, π.2, hN, hB, hA⟩
  exact ⟨(GlobalTheory.Mem.An.normOne_iff_host R H M p).1 h',
    (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd H.d M p (by have := H.hyp.2.2.2.1; omega) h').1⟩

end GlobalTheory.EX
end

