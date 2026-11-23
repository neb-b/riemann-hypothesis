module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0274
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0229
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FmSmulLeft
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0254
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAsm
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem gl_isLocPt_snoc {a : C.LPt} {j m : ℕ} (ha : D.IsLocPt a j) (hm : 1 ≤ m) {c : ℂ} (hc : c ≠ 0) :
    D.IsLocPt (a ++ [(m, c)]) (j + m) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact ha.1 x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hm, hc⟩
  · rw [← ha.2]
    simp [D.ptSize, List.map_append, List.sum_append]

theorem gl_fsv (σ z : ℂ) : P5.fsv σ z = G.psi (-U.betaU) (1 * σ * z) := by
  rw [TBBx1.fsv_eq]
  unfold G.psi U.betaU Formalism.QuantumDeterminants.cStd
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
  push_cast
  ring

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gl_inner_self (u : H) : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

end vec

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

theorem nPt_append_one (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j + 1 ≤ P.r) (c : ℂ) :
    TBB.nPt P.k P.r TT (a ++ [(1, c)]) = TBB.nPt P.k P.r TT a * KB.levW P (j + 1) c := by
  let GG := D.ptGG TT (a ++ [(1, c)])
  let GG' := D.ptGG TT a
  have happend : ∀ (l : C.LPt) (b : ℕ), b + D.ptSize l = j + 1 →
      C.nAux P.k P.r GG (fun _ _ => 1) b (l ++ [(1, c)]) =
        C.nAux P.k P.r GG' (fun _ _ => 1) b l * KB.levW P (j + 1) c := by
    intro l
    induction l with
    | nil =>
      intro b hb
      change b + 0 = j + 1 at hb
      rw [Nat.add_zero] at hb
      subst b
      have htop : j + 1 ≠ P.r + 1 := by omega
      have hexp : C.Mlev P.k P.r (j + 1) + 1 - 3 = C.Mlev P.k P.r (j + 1) - 2 := by ring
      simp only [List.nil_append, C.nAux, KB.levW, Nat.add_sub_cancel, htop, false_and,
        if_false, Nat.cast_one, one_mul, mul_one, hexp]
    | cons x l ih =>
      rcases x with ⟨s, t⟩
      intro b hb
      change b + (s + D.ptSize l) = j + 1 at hb
      have htop : b + s - 1 ≠ P.r + 1 := by omega
      simp only [List.cons_append, C.nAux, htop, false_and, if_false, ih (b + s) (by omega), mul_assoc]
  exact happend a 1 (by rw [ha.2, Nat.add_comm])

theorem nPt_nonneg_loc (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j ≤ P.r) :
    0 ≤ TBB.nPt P.k P.r TT a := by
  have hnonneg : ∀ (l : C.LPt) (b : ℕ), b + D.ptSize l ≤ P.r + 1 →
      0 ≤ C.nAux P.k P.r (D.ptGG TT a) (fun _ _ => 1) b l := by
    intro l
    induction l with
    | nil =>
      intro b _
      simp [C.nAux]
    | cons x l ih =>
      rcases x with ⟨s, t⟩
      intro b hb
      change b + (s + D.ptSize l) ≤ P.r + 1 at hb
      have htop : b + s - 1 ≠ P.r + 1 := by omega
      simp only [C.nAux, htop, false_and, if_false, one_mul]
      exact mul_nonneg (zpow_nonneg (norm_nonneg _) _) (ih (b + s) (by omega))
  exact hnonneg a 1 (by rw [ha.2]; omega)

theorem levW_nonneg_low (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) (c : ℂ) : 0 ≤ KB.levW P (j + 1) c := by
  simp only [KB.levW]
  rw [if_neg (by omega)]
  exact zpow_nonneg (norm_nonneg _) _

theorem glFibre : GLFibre := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn j hj w hw hN a b ha hb
  have hPS : KB.PStd := Formalism.FourierDecayAlt.P.standard_pairing_of_heads Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  have hjr : j ≤ P.r := by omega
  obtain ⟨φ, -, hφi, hφ, hφs⟩ := hPS hA Wp Wq P p F j hjr w a b ha hb Cb hCb hF hw.1
  set K : ℝ := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
    TBB.normC nn w with hK
  have hae : (fun c => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) =ᵐ[volume]
      fun c => (K : ℂ) * φ c := by
    filter_upwards [Formalism.FourierDecayAlt.P.TBBx1.ae_ne_zero] with c hc
    rw [hφ c hc]
    unfold TBB.NP
    rw [nPt_append_one P _ a j ha hj c, nPt_append_one P _ b j hb hj c,
      Real.sqrt_mul (nPt_nonneg_loc P _ a j ha hjr), Real.sqrt_mul (nPt_nonneg_loc P _ b j hb hjr)]
    have hl := Real.mul_self_sqrt (levW_nonneg_low P j hj c)
    rw [hK]
    have : Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (KB.levW P (j + 1) c) *
        (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) * Real.sqrt (KB.levW P (j + 1) c)) / TBB.normC nn w =
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) / TBB.normC nn w *
          KB.levW P (j + 1) c := by
      calc _ = Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
              TBB.normC nn w * (Real.sqrt (KB.levW P (j + 1) c) * Real.sqrt (KB.levW P (j + 1) c)) := by ring
        _ = _ := by rw [hl]
    rw [this]
    push_cast
    ring
  refine ⟨(hφi.const_mul (K : ℂ)).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul]
  have h0 := hφs 0
  simp only [P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_mul,
    Formalism.FourierDecayAlt.P.PBASM.waveG_zero_eq_self] at h0
  rw [h0]
  unfold TBB.NP
  congr 1
  unfold KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨ha, hb⟩, dite_eq_left hjr]
  rfl

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGermW
section
namespace Formalism.FourierDecayAlt.P.CutBP.GLG

open Formalism.FourierDecayAlt

noncomputable section

theorem zpow_two_nat (x : ℝ) (e : ℤ) (n : ℕ) (he : e = 2 * (n : ℤ)) : x ^ e = (x ^ n) ^ 2 := by
  subst he
  rw [show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul']

theorem nPt_block {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (t c : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 1, t), (1, c)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h *
        ((‖t‖ ^ ((m + 1) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m))) ^ 2 *
          (‖c‖ ^ (U.Mlev P.k (P.r - (b + (m + 2) - 1)) - 2)) ^ 2) := by
  have e : h ++ [(m + 1, t), (1, c)] = (h ++ [(m + 1, t)]) ++ [(1, c)] := by simp
  have hs1 : D.ptSize (h ++ [(m + 1, t)]) = b - 1 + (m + 1) := by
    simp only [D.ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hh ⊢
    omega
  unfold TBB.nPt
  rw [e, PBD.weight_product_append, PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hs1, hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega), if_neg (by omega), mul_assoc]
  congr 2
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1) + (m + 1) - 1 = b + m := by omega
    rw [e1]
    push_cast [Nat.cast_sub (show b + (m + 2) - 1 ≤ P.r from hi), Nat.cast_sub (show b + m ≤ P.r + 1 by omega)]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1 + (m + 1)) + 1 - 1 = b + (m + 2) - 1 := by omega
    rw [e1]
    have h3 : 2 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 := by omega
    push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring

theorem nPt_long {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (z : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 2, z)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h * (‖z‖ ^ ((m + 2) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m - 1))) ^ 2 := by
  unfold TBB.nPt
  rw [PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega)]
  congr 1
  apply zpow_two_nat
  unfold C.Mlev U.Mlev
  have e1 : 1 + (b - 1) + (m + 2) - 1 = b + (m + 2) - 1 := by omega
  rw [e1]
  have h3 : 1 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 + m := by omega
  push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
  rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutBP.GLG
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGram
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)

theorem formC_zero_l (y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hy : PBL.CV (p.T.bs j) y) : p.form j hj w 0 y = 0 := by
  have h := PBL.form_slC p j hj w 0 0 y 1 PBL.cv_zero PBL.cv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem formC_zero_r (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) : p.form j hj w x 0 = 0 := by
  have h := PBL.form_srC p j hj w x 0 0 1 hx PBL.cv_zero PBL.cv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem formC_smul_l (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w (c • x) y = c * p.form j hj w x y := by
  have h := PBL.form_slC p j hj w 0 x y c PBL.cv_zero hx hy
  rwa [zero_add, formC_zero_l p j hj w y hy, zero_add] at h

theorem formC_smul_r (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w x (c • y) = conj c * p.form j hj w x y := by
  have h := PBL.form_srC p j hj w x 0 y c hx PBL.cv_zero hy
  rwa [zero_add, formC_zero_r p j hj w x hx, zero_add] at h

end forms

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopA
section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

private theorem isLocPt_and_ptG_pos_of_vec_ne_zero {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt) (hQ : p.V G Q ≠ 0) :
    D.IsLocPt Q (P.r + 1) ∧ 0 < D.ptG (TBB.TTp p) P.r Q := by
  by_contra hn
  exact hQ (by unfold KB.Pl.V D.vecV; exact dif_neg hn)

private theorem vecV_eq_zero_of_not_isLocPt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt) (hQ : ¬ D.IsLocPt Q (P.r + 1)) :
    D.vecV p.T.base p.ν' p.m₀ G Q = 0 := by
  unfold D.vecV
  exact dif_neg fun hh => hQ hh.1

private theorem hsInner_zero_left_right_and_hsVec_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X : Wq →L[ℂ] Wp) :
    B.hsInner 0 X = 0 ∧ B.hsInner X 0 = 0 ∧ B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
    unfold B.hsVec
    rfl
  unfold B.hsInner
  rw [h0]
  exact ⟨inner_zero_right _, inner_zero_left _, rfl⟩

private theorem rr_succ_eq_ite_hsInner_else_leading {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Q Q' : C.LPt) :
    p.RR F (P.r + 1) w Q Q' =
      if w = [] then B.hsInner (p.V F Q) (p.V F Q')
      else Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w Q Q' := by
  unfold KB.Pl.RR D.RRplace
  by_cases hl : D.IsLocPt Q (P.r + 1) ∧ D.IsLocPt Q' (P.r + 1)
  · rw [dite_eq_left hl, dif_neg (by omega), if_pos rfl]
    rfl
  · rw [dif_neg hl]
    have hz : ∀ G : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
        D.vecV p.T.base p.ν' p.m₀ G Q = 0 ∨ D.vecV p.T.base p.ν' p.m₀ G Q' = 0 := by
      intro G
      rcases not_and_or.mp hl with h | h
      · exact Or.inl (vecV_eq_zero_of_not_isLocPt p G Q h)
      · exact Or.inr (vecV_eq_zero_of_not_isLocPt p G Q' h)
    split_ifs with hw
    · rcases hz F with h | h
      · show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')
        rw [h, (hsInner_zero_left_right_and_hsVec_zero _).1]
      · show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')
        rw [h, (hsInner_zero_left_right_and_hsVec_zero _).2.1]
    · unfold Top.topOf
      symm
      refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
      rcases hz (p.Θ.Θ w e F) with h | h
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, mul_zero]
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, mul_zero]

theorem top_level_gram : TopGram1 := by
  intro Wp Wq _ _ _ _ _ _ P p nn F w Cb hCb hF hw hnn
  have hnc : 0 < TBB.normC nn w := by
    unfold TBB.normC
    apply List.prod_pos
    intro a ha
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    exact hnn l.2
  by_cases hw0 : w = []
  · subst hw0
    refine ⟨Unit, inferInstance, fun _ => 1 / TBB.normC nn [], fun _ => F,
      fun _ => GermRateSplit.hsLE (ContinuousLinearMap.id ℂ Wp), fun _ => by positivity, fun _ => hF, ?_⟩
    intro Q Q'
    rw [TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_pos rfl, Fintype.sum_unique, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    simp only [ContinuousLinearMap.id_comp, List.length_nil, omT, pow_zero, Real.sqrt_one, mul_one]
    unfold B.hsInner
    push_cast
    ring
  · have hT : ∀ e : Wd.Ix (Fin w.length), ∃ F', KB.CptCoef p.T.base F' ∧
        (∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w e F g = F' g) ∧ ∀ a, p.V (p.Θ.Θ w e F) a = p.V F' a :=
      fun e => Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hw
    choose G hG _ hGV using hT
    refine ⟨Wd.Ix (Fin w.length) × M.Ty P, inferInstance,
      fun i => √(Top.cW P p.l0 w i.1 i.2).re * √(Top.cW P p.l0 w i.1 i.2).re / TBB.normC nn w,
      fun i => G i.1, fun i => GermRateSplit.hsLE (p.TP.E i.2), fun i => by positivity, fun i => hG i.1, ?_⟩
    intro Q Q'
    rw [TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_neg hw0]
    unfold Top.topOf
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hV : ∀ a, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) a = p.V (G e) a := hGV e
    rw [hV, hV, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    have key : ∀ R : C.LPt, p.V (G e) R ≠ 0 →
        √(TBB.nPt P.k P.r (TBB.TTp p) R) *
            Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w R e ρ =
          omT p w.length R * √(Top.cW P p.l0 w e ρ).re := by
      intro R hR
      have hpos := (isLocPt_and_ptG_pos_of_vec_ne_zero p (G e) R hR).2
      have hwp : 0 ≤ Top.wPt (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r R :=
        div_nonneg (Complex.normSq_nonneg _) hpos.le
      unfold Top.dH omT
      rw [Real.sqrt_mul (pow_nonneg hwp _)]
      unfold TBB.TTp
      ring
    by_cases hz : p.V (G e) Q = 0 ∨ p.V (G e) Q' = 0
    · rcases hz with h | h
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2,
          inner_zero_right]
        simp
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2,
          inner_zero_left]
        simp
    · push Not at hz
      have hreal : √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') /
            TBB.normC nn w *
            (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ *
              Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) =
          √(Top.cW P p.l0 w e ρ).re * √(Top.cW P p.l0 w e ρ).re / TBB.normC nn w *
            (omT p w.length Q' * omT p w.length Q) := by
        rw [div_mul_eq_mul_div,
          show √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') *
              (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) =
              (√(TBB.nPt P.k P.r (TBB.TTp p) Q) *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ) *
              (√(TBB.nPt P.k P.r (TBB.TTp p) Q') *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) by ring,
          key Q hz.1, key Q' hz.2]
        ring
      unfold B.hsInner
      have hc := congrArg (fun x : ℝ => (x : ℂ) *
        inner ℂ (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q'))) (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q)))) hreal
      push_cast at hc ⊢
      linear_combination hc

private theorem continuousAt_omT_append_last_of_ptG_pos {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (N m : ℕ) (h : C.LPt) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (hG : 0 < D.ptG (TBB.TTp p) P.r (h ++ [(m, c0)])) :
    ContinuousAt (fun c : ℂ => omT p N (h ++ [(m, c)])) c0 := by
  have hgg : (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) =
      fun c => (Complex.normSq c - TBB.TTp p, c) := by
    funext c
    simp [D.ptGG, D.ptLast]
  have hn : ContinuousAt (fun c : ℂ => TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m, c)])) c0 := by
    have h1 := (LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) m h 1).continuousAt
      (x := (D.ptGG (TBB.TTp p) (h ++ [(m, c0)]), c0))
      ((isOpen_univ.prod isOpen_compl_singleton).mem_nhds ⟨trivial, hc0⟩)
    have h2 : ContinuousAt (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) c0 := by
      rw [hgg]
      exact ((Complex.continuous_normSq.sub continuous_const).prodMk continuous_id).continuousAt
    exact h1.comp (f := fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) h2
  have hw : ContinuousAt (fun c : ℂ => Top.wPt (TBB.TTp p) P.r (h ++ [(m, c)])) c0 := by
    unfold Top.wPt
    exact (Complex.continuous_normSq.comp (LastBlockContinuity.ptMatN_cont h m (P.r + 1)).matrix_det).continuousAt.div
      (LastBlockContinuity.ptG_cont (TBB.TTp p) P.r h m).continuousAt hG.ne'
  unfold omT
  exact (hn.sqrt).mul ((hw.pow N).sqrt)

theorem top_level_Y_continuity : YCont := by
  intro Wp Wq _ _ _ _ _ _ P p F' hF N m h hh hm hsz c0 hc0
  have hc0' : c0 ≠ 0 := hc0
  have hA := LastBlockContinuity.smulV_continuousAt P p F' hF h hh m hm hsz (fun c => omT p N (h ++ [(m, c)]))
    (ContinuousLinearMap.id ℂ Wp) c0 hc0' (fun hG => continuousAt_omT_append_last_of_ptG_pos p N m h c0 hc0' hG)
  simp only [ContinuousLinearMap.id_comp] at hA
  exact hA.continuousWithinAt

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

