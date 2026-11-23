module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0117
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusId
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterLiftOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0066
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0155
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0193
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0067
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvMulVecOfFixedVector
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.XFibreOfParts

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SymbolOperatorFieldHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SymbolOperatorExtension

variable {d : ℕ}

def ext (S : SOp d) (n : ℕ) (w : Fin n → Fin d) : (Fin d → ℝ) → ℂ :=
  if h : n < S.ord + 1 then S.a ⟨n, h⟩ w else fun _ => 0

theorem ext_fin (S : SOp d) (k : Fin (S.ord + 1)) (w : Fin k → Fin d) : ext S k w = S.a k w := by
  unfold ext
  rw [dite_eq_left k.isLt]

theorem ext_last (S : SOp d) (w : Fin S.ord → Fin d) : ext S S.ord w = S.a (Fin.last S.ord) w := by
  unfold ext
  rw [dite_eq_left (Nat.lt_succ_self _)]
  rfl

theorem ext_top (S : SOp d) (w : Fin (S.ord + 1) → Fin d) : ext S (S.ord + 1) w = fun _ => 0 := by
  unfold ext
  rw [dite_eq_right (lt_irrefl _)]

theorem ext_contDiffOn (S : SOp d) {O : Set (Fin d → ℝ)} (hS : ∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) (n : ℕ)
    (w : Fin n → Fin d) : ContDiffOn ℝ ∞ (ext S n w) O := by
  unfold ext
  split_ifs with h
  · exact hS _ _
  · exact contDiffOn_const

theorem app_eq (S : SOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    S.app u x = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, ext S n w x * pdc (List.ofFn w) u x := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ w : Fin n → Fin d, ext S n w x * pdc (List.ofFn w) u x)]
  unfold SOp.app
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ext_fin]

theorem pdc_contDiffOn {O : Set (Fin d → ℝ)} (hO : IsOpen O) {u : (Fin d → ℝ) → ℂ} {m : ℕ}
    (hu : ContDiffOn ℝ (m : WithTop ℕ∞) u O) :
    ∀ (l : List (Fin d)) (k : ℕ), l.length + k ≤ m → ContDiffOn ℝ (k : WithTop ℕ∞) (pdc l u) O
  | [], k, h => hu.of_le (by exact_mod_cast (show k ≤ m by simpa using h))
  | i :: l, k, h => by
    have ih := pdc_contDiffOn hO hu l (k + 1) (by simp at h; omega)
    have h1 : ContDiffOn ℝ (k : WithTop ℕ∞) (fderiv ℝ (pdc l u)) O :=
      ih.fderiv_of_isOpen hO (by push_cast; exact le_rfl)
    show ContDiffOn ℝ (k : WithTop ℕ∞) (fun x => fderiv ℝ (pdc l u) x (Pi.single i 1)) O
    exact h1.clm_apply contDiffOn_const

theorem pdc_diffAt {O : Set (Fin d → ℝ)} (hO : IsOpen O) {u : (Fin d → ℝ) → ℂ} {m : ℕ}
    (hu : ContDiffOn ℝ (m : WithTop ℕ∞) u O) (l : List (Fin d)) (hl : l.length + 1 ≤ m) {x : Fin d → ℝ}
    (hx : x ∈ O) : DifferentiableAt ℝ (pdc l u) x :=
  ((pdc_contDiffOn hO hu l 1 hl).differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx)

theorem fderiv_apply_sum (f : (Fin d → ℝ) → ℂ) (x v : Fin d → ℝ) :
    fderiv ℝ f x v = ∑ i, (v i : ℂ) * fderiv ℝ f x (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (v i) : Fin d → ℝ) = v i • (Pi.single i 1 : Fin d → ℝ) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, map_smul, Complex.real_smul]

theorem sum_fin_succ_fun {n : ℕ} (g : (Fin (n + 1) → Fin d) → ℂ) :
    ∑ w, g w = ∑ i : Fin d, ∑ w : Fin n → Fin d, g (Fin.cons i w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp g, Fintype.sum_prod_type]
  rfl

def cD (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (n : ℕ) (w : Fin n → Fin d) (x : Fin d → ℝ) : ℂ :=
  fderiv ℝ (ext S n w) x (V x)

def cE (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) : (n : ℕ) → (Fin n → Fin d) → (Fin d → ℝ) → ℂ
  | 0, _, _ => 0
  | n + 1, w, x => ext S n (Fin.tail w) x * ((V x (w 0) : ℝ) : ℂ)

def fieldOp (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) : SOp d :=
  ⟨S.ord + 1, fun k w x => cD S V k w x + cE S V k w x⟩

theorem cD_top (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (w : Fin (S.ord + 1) → Fin d) (x : Fin d → ℝ) :
    cD S V (S.ord + 1) w x = 0 := by
  simp [cD, ext_top]

theorem fieldOp_app (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    (fieldOp S V).app u x = ∑ n ∈ Finset.range (S.ord + 1 + 1),
      ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x := by
  unfold SOp.app fieldOp
  exact Fin.sum_univ_eq_sum_range
    (fun n => ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x) (S.ord + 1 + 1)

end SymbolOperatorExtension

open SymbolOperatorExtension in
theorem symbol_operator_field_holds : SOpField := by
  intro d S V O hO hS hV
  refine ⟨fieldOp S V, rfl, ?_, ?_, ?_⟩
  · intro k w
    show ContDiffOn ℝ ∞ (fun x => cD S V k w x + cE S V k w x) O
    refine ContDiffOn.add ?_ ?_
    · exact ((ext_contDiffOn S hS k w).fderiv_of_isOpen hO (by simp)).clm_apply hV
    · rcases k with ⟨_ | n, hk⟩
      · exact contDiffOn_const
      · have hv : ContDiffOn ℝ ∞ (fun x => ((V x (w 0) : ℝ) : ℂ)) O := by
          have := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hV (w 0))
          simpa [Function.comp_def] using this
        exact (ext_contDiffOn S hS n _).mul hv
  · intro u hu x hx
    have hdiff : ∀ n ∈ Finset.range (S.ord + 1), ∀ w : Fin n → Fin d,
        DifferentiableAt ℝ (ext S n w) x ∧ DifferentiableAt ℝ (pdc (List.ofFn w) u) x := by
      intro n hn w
      refine ⟨((ext_contDiffOn S hS n w).differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx),
        pdc_diffAt hO hu _ ?_ hx⟩
      have := Finset.mem_range.mp hn
      simp only [List.length_ofFn]
      omega
    have key : ∀ n ∈ Finset.range (S.ord + 1),
        fderiv ℝ (fun y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y) x (V x) =
          ∑ w : Fin n → Fin d, (cD S V n w x * pdc (List.ofFn w) u x +
            ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x) := by
      intro n hn
      rw [fderiv_fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y)
        (fun w _ => (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [fderiv_fun_mul (hdiff n hn w).1 (hdiff n hn w).2, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
        fderiv_apply_sum (pdc (List.ofFn w) u), Finset.mul_sum, add_comm]
      congr 1
      · simp only [cD]; ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
        rfl
    have hR : fderiv ℝ (S.app u) x (V x) = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d,
        (cD S V n w x * pdc (List.ofFn w) u x +
          ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x) := by
      have hSu : S.app u = fun y => ∑ n ∈ Finset.range (S.ord + 1),
          ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y := funext (app_eq S u)
      rw [hSu, fderiv_fun_sum (A := fun n y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y)
        (fun n hn => DifferentiableAt.fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y) fun w _ =>
        (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]
      exact Finset.sum_congr rfl key
    have hsplit : ∀ n, ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x =
        ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x +
          ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x := by
      intro n
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => add_mul _ _ _
    have hD : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x =
        ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x := by
      rw [Finset.sum_range_succ]
      simp [cD_top]
    have hE : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x =
        ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d,
          ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x := by
      rw [Finset.sum_range_succ']
      simp only [cE, zero_mul, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [sum_fin_succ_fun, Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.cons_zero, Fin.tail_cons, List.ofFn_succ, Fin.cons_succ]
    rw [fieldOp_app]
    simp only [hsplit]
    rw [Finset.sum_add_distrib, hD, hE, ← Finset.sum_add_distrib]
    show _ = fderiv ℝ (S.app u) x (V x)
    rw [hR]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_add_distrib]
  · intro x _ ξ
    show ∑ w : Fin (S.ord + 1) → Fin d, (∏ i, (ξ (w i) : ℂ)) * (cD S V (S.ord + 1) w x + cE S V (S.ord + 1) w x) = _
    simp only [cD_top, zero_add, cE]
    rw [sum_fin_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.tail_cons, Fin.cons_succ]
    unfold SOp.symb
    simp only [dotProduct]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ext_last]
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TLFinal
section
namespace Formalism.FourierDecayAlt.P

theorem lift_of_x : Formalism.FourierDecayAlt.TL.LiftX :=
  lift_of_x_of_parts lift_zero_order lift_closed_under_operations
    (x_fibre_of_parts big_cell_values omega_polynomial_facts capelli_vector_frame capelli_vector_equivariance)


set_option maxHeartbeats 400000 in
theorem top_lift_exists : Formalism.FourierDecayAlt.TL.TopLiftExists3 := by
  classical
  refine ⟨11, by norm_num, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hl1 hlk hD
  obtain ⟨hA, hcap, hxi⟩ := actual_algebra_facts Wp Wq P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 hD
  obtain ⟨hmono, hzero, hadd, hsmul, hmul⟩ := lift_closed_under_operations Wp Wq P Bs
  have hF := lift_of_functions Wp Wq P Bs X L hD.2.2.1
  have hX := lift_of_x Wp Wq P Bs X μ L st l0 hD
  have hK := lift_capelli_operators Wp Wq P Bs X μ L st l0 hD
  have hpoly : ∀ (p : Polynomial ℂ) (a : Q.Pr ↥(Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
      TL.Lifts P Bs 0 0 a → TL.Lifts P Bs 0 0 (Polynomial.aeval a p) := by
    intro p a ha
    have hpow : ∀ m : ℕ, TL.Lifts P Bs 0 0 (a ^ m) := by
      intro m
      induction m with
      | zero => simpa using hF.1
      | succ m ih => simpa [pow_succ] using hmul 0 0 0 0 _ _ ih ha
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa using hadd 0 0 _ _ hp hq
    | monomial m c =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact hsmul 0 0 _ c (hpow m)
  have hn : P.r + 1 ≤ 2 * P.r + P.k + 1 := by omega
  have hSys : TL.LiftSys L st (2 * P.r + P.k + 1) (TL.Lifts P Bs) :=
    { mono := fun h1 h2 h => hmono _ _ _ _ _ h1 h2 h
      zero := hzero
      add := fun h1 h2 => hadd _ _ _ _ h1 h2
      smul := fun z h => hsmul _ _ _ z h
      one := hF.1
      mul := fun h1 h2 => hmul _ _ _ _ _ _ h1 h2
      fns := hF.2
      x := fun Y _ => hX Y
      xi := fun Y hY _ => by
        obtain ⟨p, hp⟩ := hxi Y hY
        rw [hp]
        exact hpoly p _ (hX Y)
      cap := fun Y hY => by
        rw [← hcap Y hY]
        exact hK Y }
  have hWL := TL.wordLiftOfParts word_recursion
    (letter_lift_of_parts TL.basicLift l_shape m_shape_of_l_shape)
  have hAdm : ∀ w : List C.Letter, KB.CutWord P l0 w → Fr.admitted st (D.positionted w) := by
    intro w hw
    have hM : M.CutWord P l0 (D.positionted w) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [D.positionted, List.map_ofFn]
        exact List.nodup_ofFn.mpr (fun a b h => h)
      · intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact ⟨by simp, by simpa using hw.1 i⟩
      · rw [D.positionted, List.pairwise_ofFn]
        intro i j hij
        simpa using hw.2 i j (ne_of_lt hij)
    obtain ⟨h1, h2, h3, h4⟩ := cut_admissible interlacing_sign q_positive_interlacing q_positive_shift
      types_interlace realPoints_statement P hD.1.1 l0 hl1 hlk (Fin w.length) (D.positionted w) hM
    refine ⟨h1, h2, ?_, h4⟩
    rw [hD.2.2.2.2.1, hD.2.2.2.2.2.1]
    exact h3
  have hLift : ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∃ Dop : B.DiffOp P.k P.r Wp Wq,
      KB.CutWord P l0 w → ∃ (nf : ℕ) (fib : Fin nf → B.Mat P.k P.r → C6.EndH Wp Wq),
        (∀ j, C6.FibBound Bs (fib j)) ∧
        C6.InDDPlus Bs fib ∅ (w.length * (2 * P.r + P.k + 1))
          (11 * w.length * (P.r + 1) * (2 * P.r + P.k + 1)) Dop ∧
        TL.RadIs P Bs Dop (((Fr.ofWord L st (D.positionted w)).F * TL.bTA L (D.positionted w)) e Wd.e1).1 := by
    intro w e
    by_cases hw : KB.CutWord P l0 w
    · have h := hWL _ (Fin w.length) P.r (2 * P.r + P.k + 1) L st (TL.Lifts P Bs) (D.positionted w) hA hSys hn
        (hAdm w hw) e
      have hl : (D.positionted w).length = w.length := List.length_ofFn
      rw [hl] at h
      obtain ⟨nf, fib, Dop, h1, h2, h3⟩ := h
      exact ⟨Dop, fun _ => ⟨nf, fib, h1, h2, h3⟩⟩
    · obtain ⟨Dop, -⟩ := identity_operator P.k P.r Wp Wq Bs
      exact ⟨Dop, fun h => absurd h hw⟩
  choose Dw hDw using hLift
  obtain ⟨D0, hD0, hD0F⟩ := identity_operator P.k P.r Wp Wq Bs
  refine ⟨⟨fun w e F => if w = [] then F else B.opApply (Dw w e) F, fun e F => by simp⟩, ?_, ?_⟩
  · intro w hw F hFc Φ hΦ e
    dsimp only
    have hact : ∀ (M0 : Wd.SlopeTestRemainingChoices (Fin w.length) (Q.Pr ↥(Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
        P5.act M0 (Top.firstStateVector Φ) e = (M0 e Wd.e1).1 Φ := by
      intro M0
      unfold P5.act Top.firstStateVector
      rw [Finset.sum_eq_single Wd.e1]
      · exact congrArg _ (if_pos rfl)
      · intro b _ hb
        have hb' : ¬ (b = fun _ => 0) := hb
        rw [if_neg hb', map_zero]
      · simp
    rw [hact]
    by_cases hne : w = []
    · subst hne
      simp only [if_true]
      have h1 : (Fr.ofWord L st (D.positionted ([] : List C.Letter))).F * P5.bTall L (D.positionted ([] : List C.Letter)) = 1 := by
        simp [D.positionted, Fr.ofWord, P5.bTall, P5.bTl, Wd.bT, Fr.Start.frame]
      have he : e = Wd.e1 := funext fun i => (Nat.not_lt_zero _ i.2).elim
      rw [h1, he]
      change Top.IsRadOf P Bs Φ F
      exact hΦ
    · rw [if_neg hne]
      obtain ⟨nf, fib, -, -, hR⟩ := hDw w e hw
      exact hR F hFc Φ hΦ
  · intro w hw e
    dsimp only
    by_cases hne : w = []
    · refine ⟨0, fun j => j.elim0, 0, 0, D0, fun j => j.elim0, ?_, by norm_num <;> positivity,
        by norm_num <;> positivity, ?_⟩
      · convert hD0 using 2
      · intro F g _
        rw [if_pos hne, hD0F]
    · obtain ⟨nf, fib, h1, h2, -⟩ := hDw w e hw
      refine ⟨nf, fib, _, _, Dw w e, h1, h2, ?_, ?_, ?_⟩
      · push_cast
        nlinarith [show (0:ℝ) ≤ (w.length:ℝ) * (2 * (P.r:ℝ) + P.k + 1) by positivity]
      · push_cast
        nlinarith [show (0:ℝ) ≤ (w.length:ℝ) * (2 * (P.r:ℝ) + P.k + 1) by positivity]
      · intro F g _
        rw [if_neg hne]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorToSymbolOperator
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace IdentityZeroOperators

variable {d : ℕ}

def idOp (d : ℕ) : SOp d := ⟨0, fun _ _ _ => 1⟩

def zeroOp (d m : ℕ) : SOp d := ⟨m, fun _ _ _ => 0⟩

lemma idOp_app (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : (idOp d).app u x = u x := by
  change ∑ k : Fin 1, ∑ w : Fin k → Fin d, (1 : ℂ) * pdc (List.ofFn w) u x = u x
  rw [Fin.sum_univ_one]
  change ∑ w : Fin 0 → Fin d, (1 : ℂ) * pdc (List.ofFn w) u x = u x
  simp [pdc]

lemma idOp_symb (x ξ : Fin d → ℝ) : (idOp d).symb x ξ = 1 := by
  change ∑ w : Fin 0 → Fin d, (∏ i : Fin 0, (ξ (w i) : ℂ)) * (1 : ℂ) = 1
  simp

lemma zeroOp_app (m : ℕ) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : (zeroOp d m).app u x = 0 := by
  simp [SOp.app, zeroOp]

lemma zeroOp_symb (m : ℕ) (x ξ : Fin d → ℝ) : (zeroOp d m).symb x ξ = 0 := by
  simp [SOp.symb, zeroOp]

lemma word (hF : SOpField) (O : Set (Fin d → ℝ)) (hO : IsOpen O) :
    ∀ Vs : List ((Fin d → ℝ) → (Fin d → ℝ)), (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) →
    ∃ S : SOp d, S.ord = Vs.length ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ (Vs.length : WithTop ℕ∞) u O → ∀ x ∈ O,
        S.app u x = vfW Vs u x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = (Vs.map fun V => ((ξ ⬝ᵥ V x : ℝ) : ℂ)).prod := by
  intro Vs
  induction Vs with
  | nil =>
    intro _
    exact ⟨idOp d, rfl, fun _ _ => contDiffOn_const, fun u _ x _ => by simp [idOp_app, vfW],
      fun x _ ξ => by simp [idOp_symb]⟩
  | cons V Vs ih =>
    intro hV
    obtain ⟨S, hSo, hSc, hSa, hSs⟩ := ih (fun W hW => hV W (List.mem_cons_of_mem _ hW))
    obtain ⟨S', hS'o, hS'c, hS'a, hS's⟩ := hF d S V O hO hSc (hV V List.mem_cons_self)
    refine ⟨S', by rw [hS'o, hSo]; rfl, hS'c, ?_, ?_⟩
    · intro u hu x hx
      have hl : (V :: Vs).length = S.ord + 1 := by rw [hSo]; rfl
      rw [hl] at hu
      have hu0 : ContDiffOn ℝ (Vs.length : WithTop ℕ∞) u O :=
        hu.of_le (by rw [hSo]; exact_mod_cast Nat.le_succ _)
      rw [hS'a u hu x hx]
      have he : S.app u =ᶠ[nhds x] vfW Vs u := by
        filter_upwards [hO.mem_nhds hx] with y hy
        exact hSa u hu0 y hy
      simp only [vfW, vfD]
      rw [he.fderiv_eq]
    · intro x hx ξ
      rw [hS's x hx ξ, hSs x hx ξ]
      simp

end IdentityZeroOperators

open IdentityZeroOperators in
theorem vector_to_symbol_operator : VOpToSOpOfSteps := by
  intro hF hL hLin d m P O hO hP
  induction P with
  | nil =>
    exact ⟨zeroOp d m, rfl, fun _ _ => contDiffOn_const, fun u _ x _ => by simp [zeroOp_app, WOp.app],
      fun x _ ξ => by simp [zeroOp_symb, WOp.symb]⟩
  | cons t P ih =>
    obtain ⟨T, hTo, hTc, hTa, hTs⟩ := ih (fun s hs => hP s (List.mem_cons_of_mem _ hs))
    obtain ⟨hlen, hsm⟩ := hP t List.mem_cons_self
    obtain ⟨S, hSo, hSc, hSa, hSs⟩ := word hF O hO t.2 hsm
    obtain ⟨S', hS'o, hS'c, hS'a, hS's⟩ := hL d S m O (by rw [hSo]; exact hlen) hSc
    obtain ⟨R, hRo, hRc, hRa, hRs⟩ := hLin d S' T t.1 O (hS'o.trans hTo.symm) hS'c hTc
    refine ⟨R, hRo.trans hS'o, hRc, ?_, ?_⟩
    · intro u hu x hx
      rw [hRa, hS'a, hSa u (hu.of_le (by exact_mod_cast hlen)) x hx, hTa u hu x hx]
      simp [WOp.app]
    · intro x hx ξ
      rw [hRs, hS's, hSs x hx ξ, hTs x hx ξ, hSo]
      simp only [WOp.symb, List.map_cons, List.sum_cons]
      split_ifs <;> simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

