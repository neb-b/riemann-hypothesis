module

public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

section MatSub

variable {A : Type} [Ring A] [Algebra ℂ A]

def matSub (C : Subalgebra ℂ A) (n : Type) [Fintype n] [DecidableEq n] : Subalgebra ℂ (Matrix n n A) where
  carrier := {M | ∀ i j, M i j ∈ C}
  mul_mem' := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM i k) (hN k j)
  add_mem' := by
    intro M N hM hN i j
    exact Subalgebra.add_mem _ (hM i j) (hN i j)
  algebraMap_mem' := by
    intro c i j
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs
    · exact C.algebraMap_mem c
    · exact C.zero_mem

theorem mem_matSub {C : Subalgebra ℂ A} {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n A} :
    M ∈ matSub C n ↔ ∀ i j, M i j ∈ C := by
  exact Iff.rfl

variable {S : Type} [Fintype S] [DecidableEq S] (C : Subalgebra ℂ A)

theorem eU_mem (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro x y
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact C.one_mem
  · exact C.zero_mem

theorem io_mem {x : A} (hx : x ∈ C) : (io x : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact C.zero_mem

theorem lift_mem_matrix_algebra {M : M2 A} (hM : ∀ i j, M i j ∈ C) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  rw [mem_matSub]
  intro i j
  simp only [lift0, Matrix.map_apply]
  exact io_mem C (hM i j)

theorem ins_mem (a : S) {M : M2 (SlopeTestRemainingChoices S A)} (hM : M ∈ matSub (matSub C (Ix S)) (Fin 2)) :
    ins a M ∈ matSub C (Ix S) := by
  unfold ins
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (eU_mem C a i j) ?_
  exact mem_matSub.1 hM i j

theorem transpose_mem {n : Type} [Fintype n] [DecidableEq n] {C' : Subalgebra ℂ A} {M : Matrix n n A}
    (hM : M ∈ matSub C' n) : Mᵀ ∈ matSub C' n := by
  exact mem_matSub.2 fun i j => mem_matSub.1 hM j i

theorem Rh0_mem (a : S) (D : ℂ) : (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  have hP : (P0 a : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) :=
    mem_matSub.2 fun i j => eU_mem C a j i
  unfold Rh0
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) D) hP) _

theorem Rht0_mem (a : S) (D : ℂ) : (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  have hQ : (Q0 a : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) :=
    mem_matSub.2 fun i j => eU_mem C a i j
  unfold Rht0
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) D) hQ) _

theorem TTw_mem {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) (Y : ℂ) :
    TTw QQ w Y ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  induction w generalizing Y with
  | nil =>
    simp only [TTw]
    exact lift_mem_matrix_algebra C (hQ Y)
  | cons l w ih =>
    simp only [TTw]
    split_ifs
    · exact Subalgebra.mul_mem _ (ih Y) (Rh0_mem C _ _)
    · exact Subalgebra.mul_mem _ (Rht0_mem C _ _) (ih Y)

theorem RRw_mem {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) :
    RRw QQ w ∈ matSub C (Ix S) := by
  induction w with
  | nil =>
    simp only [RRw]
    exact Subalgebra.one_mem _
  | cons l w ih =>
    simp only [RRw]
    refine Subalgebra.mul_mem _ ih (ins_mem C _ ?_)
    split_ifs
    · exact TTw_mem C hQ w _
    · exact transpose_mem (TTw_mem C hQ w _)

theorem commute_io {f : A} {M : SlopeTestRemainingChoices S A} (hM : M ∈ matSub (Subalgebra.centralizer ℂ {f}) (Ix S)) :
    Commute (io f : SlopeTestRemainingChoices S A) M := by
  have h : ∀ i j, f * M i j = M i j * f := by
    intro i j
    have hm := mem_matSub.1 hM i j
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact hm f (Set.mem_singleton f)
  show (io f : SlopeTestRemainingChoices S A) * M = M * io f
  ext i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact h i j

end MatSub

section Act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem pr_fst_sum {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (s : Finset ι) (g : ι → Pr V) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  first
    | exact Prod.fst_sum (s := s) (f := g)
    | (classical
       induction s using Finset.induction_on with
       | empty => simp only [Finset.sum_empty]; rfl
       | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl)

theorem pr_fst_mul {V : Type} [AddCommGroup V] [Module ℂ V] (m n : Pr V) : (m * n).1 = m.1 * n.1 := rfl

theorem pr_fst_zero {V : Type} [AddCommGroup V] [Module ℂ V] : (0 : Pr V).1 = 0 := rfl

theorem act_mul (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Ix S → RadSp k r z z' π π') :
    act (M * N) x = act M (act N x) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [act, Matrix.mul_apply, pr_fst_sum, pr_fst_mul, LinearMap.sum_apply, Module.End.mul_apply,
    map_sum]
  exact Finset.sum_comm

theorem act_io (f : Pr (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') (a : Ix S) :
    act (io f) x a = f.1 (x a) := by
  simp only [act, io, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), pr_fst_zero, LinearMap.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Act

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem hsInner_smul_left (a : ℂ) (U V : Wq →L[ℂ] Wp) : B.hsInner (a • U) V = a * B.hsInner U V := by
  have e : Formalism.FourierDecayAlt.B.hsVec (a • U) = a • Formalism.FourierDecayAlt.B.hsVec U := by
    unfold Formalism.FourierDecayAlt.B.hsVec
    rw [← WithLp.toLp_smul]
    first
      | rfl
      | (congr 1; funext i; simp)
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [e, inner_smul_right]

theorem pairAt_mulOp (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (Wv Φ) Ψ c = fsv s (c l) * pairAt μ Φ Ψ c := by
  unfold pairAt
  simp_rw [hW Φ c, hsInner_smul_left]
  exact MeasureTheory.integral_const_mul _ _

theorem glue_succ_update (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  simp only [glue]
  rw [dite_eq_right (by rw [Fin.val_succ]; omega)]
  simp

theorem form_mulOp (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (u y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    form μ l.succ (act (io (mkP Wv Wv')) u) y (Function.update c l t) =
      fsv s t * form μ l.succ u y (Function.update c l t) := by
  unfold form
  have h : ∀ (c' : Cf r l.succ) (a : Ix S), pairAt μ (act (io (mkP Wv Wv')) u a) (y a) (glue l.succ (Function.update c l t) c') =
      fsv s t * pairAt μ (u a) (y a) (glue l.succ (Function.update c l t) c') := by
    intro c' a
    rw [act_io]
    have e : (mkP Wv Wv' : Pr (RadSp k r z z' π π')).1 = Wv := rfl
    rw [e, pairAt_mulOp μ l s Wv hW, glue_succ_update]
  simp_rw [h, ← Finset.mul_sum, mul_left_comm _ (fsv s t)]
  exact MeasureTheory.integral_const_mul _ _

end Wave

section StepParts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)

theorem stepTwistFromParts : StepTwistFromParts (S := S) P z z' π π' X μ L st K l0 := by
  intro hD hPW hWS hWC hWK w hw l s Wv Wv' hW hW' x y hx hy c _
  refine ⟨hWK w hw l s Wv Wv' hW hW' x hx, fun t _ => ?_⟩
  obtain ⟨hwave, hc1, hc2, hp⟩ := hWS hD.2.2.1 l s Wv Wv' hW hW'
  have hbT : bTl L l w * Vw (mkP Wv Wv') s w = io (mkP Wv Wv') * bTl L l w :=
    hPW ℂ _ S (site L l) (mkP Wv Wv') (mkP Wv' Wv) s w hwave hc1 hc2 hp hw.1.1
  have hQ : ∀ Y i j, QQi L st l.succ Y i j ∈ Subalgebra.centralizer ℂ {mkP Wv Wv'} := by
    intro Y i j
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (hWC l s Wv Wv' hW hW' Y i j).eq
  have hcomm : io (mkP Wv Wv') * RRi L st l.succ w = RRi L st l.succ w * io (mkP Wv Wv') :=
    (commute_io (RRw_mem _ hQ w)).eq
  simp only [P5.ph, RRform]
  rw [← act_mul (bTl L l w) (Vw (mkP Wv Wv') s w) x, hbT, act_mul (io (mkP Wv Wv')) (bTl L l w) x,
    ← act_mul (RRi L st l.succ w) (io (mkP Wv Wv')), ← hcomm, act_mul (io (mkP Wv Wv')), form_mulOp μ l s Wv Wv' hW]
  ring

end StepParts

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RhoAntitoneOfInterlacing
section
open Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P

theorem lambda_side_inequality : C7.LamSide := by
  unfold C7.LamSide C7.LamInterlaces
  rintro k r u u' lam l Y hl hlk ⟨hA, hL⟩ ⟨-, hL'⟩ - i
  constructor
  · intro hli
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 1 := ⟨⟨l - 1, by omega⟩, rfl⟩
    have hji : j ≤ i := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam i ≤ lam j := hA.antitone hji
    have h1 := (hL j).1 (by omega)
    have h2 := (hL' j).1 (by omega)
    rw [show (j : ℕ) + 1 = l by omega] at h1 h2
    exact lt_min (lt_of_le_of_lt hi1 h1) (lt_of_le_of_lt hi1 h2)
  · intro hil
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2 * r + 1), (j : ℕ) = l - 2 := ⟨⟨l - 2, by omega⟩, rfl⟩
    have hij : i ≤ j := Fin.le_iff_val_le_val.2 (by omega)
    have hi1 : lam j ≤ lam i := hA.antitone hij
    have h1 := (hL j).2 (by omega)
    have h2 := (hL' j).2 (by omega)
    rw [show (j : ℕ) + 2 = l by omega] at h1 h2
    exact max_lt (lt_of_lt_of_le h1 hi1) (lt_of_lt_of_le h2 hi1)

theorem rho_antitone_of_interlacing {k : ℕ} {u u' ρ : ℕ → ℝ} (h : I.Interlaces k u u' ρ) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k - 1 → ρ j ≤ ρ i := by
  intro i j hi hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hin ih =>
    have h1 := h n (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := h (n + 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h3 := ih (by omega)
    linarith [h1.2.2.1, h2.1]

theorem rho_side_inequality : C7.RhoSide := by
  unfold C7.RhoSide C7.Between
  intro k u u' ρ l Y hl hlk hI hB i hi
  have hi' : 1 ≤ i ∧ i ≤ k - 1 := by simpa using hi
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  · intro hli
    have h1 := hI l (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI l i hl hli hi'.2
    have h3 : ρ l + 1 / 2 ≤ min (u l) (u' l) := le_min h1.1 h1.2.1
    linarith
  · intro hil
    have h1 := hI (l - 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := rho_antitone_of_interlacing hI i (l - 1) hi'.1 (by omega) (by omega)
    rw [show l - 1 + 1 = l by omega] at h1
    have h3 : max (u l) (u' l) + 1 / 2 ≤ ρ (l - 1) := by
      rcases le_total (u l) (u' l) with h | h
      · rw [max_eq_right h]; exact h1.2.2.2
      · rw [max_eq_left h]; exact h1.2.2.1
    linarith

theorem sign_prod_of_split_at_index (s : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) (hpos : ∀ j ∈ s, j < m → 0 < g j)
    (hneg : ∀ j ∈ s, m ≤ j → g j < 0) : 0 < (-1 : ℝ) ^ (s.filter (m ≤ ·)).card * ∏ j ∈ s, g j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ih' := ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
      (fun j hj => hneg j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert ha, Finset.filter_insert]
    by_cases hma : m ≤ a
    · rw [if_pos hma, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.1 h).1), pow_succ]
      have := hneg a (Finset.mem_insert_self a s) hma
      nlinarith
    · rw [if_neg hma]
      have := hpos a (Finset.mem_insert_self a s) (by omega)
      nlinarith

theorem polynomial_sign : C7.PSign := by
  unfold C7.PSign
  intro k r u u' ρ lam l Y hl hlk hL hL' hI hB
  have hside := lambda_side_inequality k r u u' lam l Y hl hlk hL hL' hB
  have hrho := rho_side_inequality k u u' ρ l Y hl hlk hI hB
  have hB' := hB
  unfold C7.Between at hB'
  have hA : 0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) := by
    have hprod : ∏ s, (Y + lam s) = ∏ j ∈ Finset.range (k + 2 * r + 1),
        (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) j := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [dif_pos s.isLt, Fin.eta]
    have key := sign_prod_of_split_at_index (Finset.range (k + 2 * r + 1))
      (fun j => if h : j < k + 2 * r + 1 then Y + lam ⟨j, h⟩ else 1) (l - 1)
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).2 (show j + 1 < l by omega)
        linarith [hB'.2])
      (fun j hj hjm => by
        have hj' : j < k + 2 * r + 1 := Finset.mem_range.1 hj
        simp only [dif_pos hj']
        have := (hside ⟨j, hj'⟩).1 (show l ≤ j + 1 by omega)
        linarith [hB'.1])
    have hcard : ((Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·)).card = (k - l) + 2 * (r + 1) := by
      rw [(show (Finset.range (k + 2 * r + 1)).filter (l - 1 ≤ ·) = Finset.Ico (l - 1) (k + 2 * r + 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega), Nat.card_Ico]
      omega
    rw [hcard, pow_add, pow_mul, neg_one_sq, one_pow, mul_one] at key
    rw [hprod]
    exact key
  have hB2 : 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y := by
    unfold I.xpoly
    have key := sign_prod_of_split_at_index (Finset.Icc 1 (k - 1)) (fun i => Y + ρ i) l
      (fun i hi hil => show 0 < Y + ρ i by linarith [(hrho i hi).2 hil])
      (fun i hi hli => show Y + ρ i < 0 by linarith [(hrho i hi).1 hli])
    have hcard : ((Finset.Icc 1 (k - 1)).filter (l ≤ ·)).card = k - l := by
      rw [(show (Finset.Icc 1 (k - 1)).filter (l ≤ ·) = Finset.Icc l (k - 1) by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega), Nat.card_Icc]
      omega
    rw [hcard] at key
    exact key
  refine ⟨hA, hB2, ?_⟩
  have h := abs_of_pos hA
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h
  exact h

theorem roots_outside_jointly : C7.RootsOutJoint := by
  unfold C7.RootsOutJoint LE.Sys.RootsOut
  intro S u u' l hl hlk hI hI' hB s hs
  have hb := hB _ hs
  have key := lambda_side_inequality S.k S.r u u' S.lam l (-S.lam s) hl hlk hI hI' hb s
  unfold C7.Between at hb
  rw [neg_neg] at hb
  by_cases h : l ≤ s.val + 1
  · have := key.1 h
    linarith [hb.1]
  · have := key.2 (by omega)
    linarith [hb.2]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3

theorem sgn_step (s : ℕ) : s * (s - 1) / 2 + (s + 1) * (s + 1 - 1) / 2 = s * s := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 1) * (s + 1 - 1) / 2 * 2 = (s + 1) * (s + 1 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 1)).two_dvd
  have h3 : s * (s - 1) + (s + 1) * (s + 1 - 1) = 2 * (s * s) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 1) * (s + 1 - 1) = B at *
  generalize s * s = C at *
  omega

theorem sgn_step2 (s : ℕ) : s * (s - 1) / 2 + (s + 2) * (s + 2 - 1) / 2 = s * (s + 1) + 1 := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 2) * (s + 2 - 1) / 2 * 2 = (s + 2) * (s + 2 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 2)).two_dvd
  have h3 : s * (s - 1) + (s + 2) * (s + 2 - 1) = 2 * (s * (s + 1) + 1) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel, show n + 1 + 2 - 1 = n + 2 by omega]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 2) * (s + 2 - 1) = B at *
  generalize s * (s + 1) = C at *
  omega

theorem neg_one_pow_sq (s : ℕ) : (-1 : ℂ) ^ (s * s) = (-1) ^ s := by
  rcases Nat.even_or_odd s with h | h
  · rw [Even.neg_one_pow h, Even.neg_one_pow (h.mul_left s)]
  · rw [Odd.neg_one_pow h, Odd.neg_one_pow (h.mul h)]

theorem sign_permutation_identity : SignE := by
  intro s
  refine ⟨?_, ?_⟩
  · unfold sgnW; rw [← pow_add, sgn_step, neg_one_pow_sq]
  · unfold sgnW; rw [← pow_add, sgn_step2, pow_succ, Even.neg_one_pow (Nat.even_mul_succ_self s)]; ring

theorem sgnW_succ (m : ℕ) : sgnW (m + 1) = (-1) ^ m * sgnW m := by
  have h := (sign_permutation_identity m).1
  have hsq : sgnW m * sgnW m = 1 := by
    unfold sgnW; rw [← pow_add, ← two_mul, pow_mul]; simp
  calc sgnW (m + 1) = (sgnW m * sgnW m) * sgnW (m + 1) := by rw [hsq, one_mul]
    _ = sgnW m * (sgnW m * sgnW (m + 1)) := by ring
    _ = (-1) ^ m * sgnW m := by rw [h]; ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordIntegralScaling
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordIntegralScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem int_list {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (L : ι → E →L[ℂ] E) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => L i (φ i p)).sum) μ ∧
      ∫ p, (l.map fun i => L i (φ i p)).sum ∂μ = (l.map fun i => L i (∫ p, φ i p ∂μ)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : Integrable (φ i) μ := h i (by simp)
    obtain ⟨hl1, hl2⟩ := ih (fun j hj => h j (by simp [hj]))
    have hLi : Integrable (fun p => L i (φ i p)) μ := (L i).integrable_comp hi
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hLi.add hl1, ?_⟩
    rw [integral_add hLi hl1, hl2, ContinuousLinearMap.integral_comp_comm _ hi]

theorem smul_list {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (L : ι → E →L[ℂ] E)
    (x : ι → E) : c • (l.map fun i => L i (x i)).sum = (l.map fun i => L i (c • x i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, smul_add, ih, List.map_cons, List.sum_cons, map_smul]

variable {k r : ℕ}

theorem lr_nrm (v : List (Mat k r)) :
    (B4.lr [] v).map B4.nrm = B4.lr [] (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) := by
  simp [B4.lr, B4.nrm, List.map_map, Function.comp_def]

theorem rw_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (Mat k r)) (f : Mat k r → E) :
    Rw v f = B4.pn (B4.lr [] v) • Rw (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) f := by
  have h := B4.W_nrm (B4.lr [] v) f
  rw [lr_nrm, ← B4.dLR_eq, ← B4.dLR_eq] at h
  exact h

end Formalism.FourierDecayAlt.P.WordIntegralScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

