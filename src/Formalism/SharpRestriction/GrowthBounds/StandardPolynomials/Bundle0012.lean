module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0011
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0014
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PolyUpperBoundDelta

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoBlockNeZero
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section TDs

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem TD_wLetBL {Cde E : ℝ} (x : X.TT × Bool) (b : SegBlock (segS X.TT j) X.m)
    (hk : BLk C0 Cde CE1 CE2 X E j b) :
    TD C0 CE1 CE2 X j b (wLet X x) =
      (if segNext X.TT j = x.1.val then hhDegs X.TT X.aT X.bT x else 0) +
        ∑ i, (if segPos X.TT j i = x.1.val then hhDegs X.TT X.aT X.bT x else 0) := by
  have ho : b.oPlus ≤ segAPlus X.TT X.aT j := hk.2.2.2.1
  obtain ⟨t, bb⟩ := x
  have hterm : ∀ i : Fin (segS X.TT j),
      ((∑ c : Fin (X.m + 1), (b.rz i c * wLet X (t, bb) ((topOdd X j i, true), c) +
          b.ry i c * wLet X (t, bb) ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * wLet X (t, bb) ((topOdd X j i, true), 0) +
          b.sg i * wLet X (t, bb) ((topOdd X j i, false), 0) + b.w i * wLet X (t, bb) ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) *
            wLet X (t, bb) ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * wLet X (t, bb) ((topOdd X j i, true), 0) +
          b.o i * wLet X (t, bb) ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i *
            wLet X (t, bb) ((topOdd X j i, false), Fin.succ 0))) =
      (if segPos X.TT j i = t.val then hhDegs X.TT X.aT X.bT (t, bb) else 0) := by
    intro i
    have hodd := (pos_mem X.TT j i).2
    by_cases h : segPos X.TT j i = t.val
    · have ht : topOdd X j i = t := Subtype.ext h
      subst ht
      rw [if_pos h]
      cases bb
      · have w1 : ∀ c, wLet X (topOdd X j i, false) ((topOdd X j i, true), c) = 0 := fun c => if_neg (by simp)
        have w2 : ∀ c, wLet X (topOdd X j i, false) ((topOdd X j i, false), c) = 1 := fun c => if_pos rfl
        simp only [w1, w2, mul_zero, mul_one, zero_add, add_zero]
        have hd := hk.1.2.2 i
        have hPC : (X.seg C0 CE1 CE2 j).P X.p i * coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i =
            segATop X.TT X.aT j i - ∑ c, b.ry i c := Nat.mul_div_cancel' hd.2
        have hdeg : hhDegs X.TT X.aT X.bT (topOdd X j i, false) = segATop X.TT X.aT j i := by
          show hhDeg X.aT X.bT (segPos X.TT j i) false = X.aT (segPos X.TT j i)
          unfold hhDeg
          simp [hodd]
        have hin : (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
            b.sg i + (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i)
            else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) =
            coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i := by
          split_ifs with hs
          · have := (hk.2.2.1 i hs).2.2.1
            omega
          · rfl
        rw [hin, hPC, hdeg]
        have := hd.1
        omega
      · have w1 : ∀ c, wLet X (topOdd X j i, true) ((topOdd X j i, true), c) = 1 := fun c => if_pos rfl
        have w2 : ∀ c, wLet X (topOdd X j i, true) ((topOdd X j i, false), c) = 0 := fun c => if_neg (by simp)
        simp only [w1, w2, mul_zero, mul_one, zero_add, add_zero]
        have hd := hk.1.2.1 i
        have hPA : (X.seg C0 CE1 CE2 j).P X.p i * coarseA X.p (X.seg C0 CE1 CE2 j) b i =
            (X.seg C0 CE1 CE2 j).bTop i - ∑ c, b.rz i c := Nat.mul_div_cancel' hd.2
        have hdeg : hhDegs X.TT X.aT X.bT (topOdd X j i, true) = (X.seg C0 CE1 CE2 j).bTop i := by
          show hhDeg X.aT X.bT (segPos X.TT j i) true = X.bT (segPos X.TT j i)
          unfold hhDeg
          simp [hodd]
        have hin : (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
            coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i + b.w i
            else coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i + b.o i) = coarseA X.p (X.seg C0 CE1 CE2 j) b i := by
          split_ifs with hs
          · have := (hk.2.2.1 i hs).2.1
            omega
          · have := (hk.2.1 i (not_lt.1 hs)).1
            omega
        rw [hin, hPA, hdeg]
        have := hd.1
        omega
    · have w0 : ∀ b' c, wLet X (t, bb) ((topOdd X j i, b'), c) = 0 := fun b' c =>
        if_neg (fun e => h (congrArg (fun z : X.TT × Bool => z.1.val) e))
      rw [if_neg h]
      simp only [w0, mul_zero, add_zero, Finset.sum_const_zero, ite_self]
  have hend : (segAPlus X.TT X.aT j - b.oPlus) * wLet X (t, bb) ((topEnd X j, true), 0) +
      b.oPlus * wLet X (t, bb) ((topEnd X j, true), Fin.succ 0) +
      (X.seg C0 CE1 CE2 j).bPlus * wLet X (t, bb) ((topEnd X j, false), Fin.succ 0) =
      (if segNext X.TT j = t.val then hhDegs X.TT X.aT X.bT (t, bb) else 0) := by
    have hev := (next_mem X.TT j).2
    by_cases h : segNext X.TT j = t.val
    · have ht : topEnd X j = t := Subtype.ext h
      subst ht
      rw [if_pos h]
      cases bb
      · have w1 : ∀ c, wLet X (topEnd X j, false) ((topEnd X j, true), c) = 0 := fun c => if_neg (by simp)
        have w2 : ∀ c, wLet X (topEnd X j, false) ((topEnd X j, false), c) = 1 := fun c => if_pos rfl
        simp only [w1, w2, mul_zero, mul_one, zero_add]
        show X.bT (segNext X.TT j) = hhDeg X.aT X.bT (segNext X.TT j) false
        unfold hhDeg
        simp [hev]
      · have w1 : ∀ c, wLet X (topEnd X j, true) ((topEnd X j, true), c) = 1 := fun c => if_pos rfl
        have w2 : ∀ c, wLet X (topEnd X j, true) ((topEnd X j, false), c) = 0 := fun c => if_neg (by simp)
        simp only [w1, w2, mul_zero, mul_one, add_zero]
        rw [Nat.sub_add_cancel ho]
        show X.aT (segNext X.TT j) = hhDeg X.aT X.bT (segNext X.TT j) true
        unfold hhDeg
        simp [hev]
    · have w0 : ∀ b' c, wLet X (t, bb) ((topEnd X j, b'), c) = 0 := fun b' c =>
        if_neg (fun e => h (congrArg (fun z : X.TT × Bool => z.1.val) e))
      rw [if_neg h]
      simp only [w0, mul_zero, add_zero]
  unfold TD
  rw [Finset.sum_congr rfl fun i _ => hterm i, add_assoc, add_assoc, ← add_assoc ((segAPlus X.TT X.aT j - b.oPlus) * _),
    hend, add_comm]

theorem TD_wN (b : SegBlock (segS X.TT j) X.m) :
    TD C0 CE1 CE2 X j b (wN X) = blockOrd X.p (X.seg C0 CE1 CE2 j) b := by
  unfold TD blockOrd oEff
  simp only [normal_weight_vector_zero_eq_zero, wN_vecS, normal_weight_covector_zero, wN_covS, mul_zero, mul_one, zero_add, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∑ c : Fin (X.m + 1), (b.rz i c * wN X ((topOdd X j i, true), c) + b.ry i c * wN X ((topOdd X j i, false), c)) =
      (∑ c : Fin (X.m + 1), if (c : ℕ) = 0 then 0 else b.rz i c) + b.ry i 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [normal_weight_vector_zero_eq_zero, wN_vecS, normal_weight_covector_zero, wN_covS, mul_zero, mul_one, zero_add, add_zero, Fin.val_zero, if_true,
      Fin.val_succ, Nat.succ_ne_zero, if_false]
    ring
  rw [h1]
  split_ifs <;> ring

end TDs

section Sym

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O]

def BalHom (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (s : Syms O C0 CE1 CE2 X) : Prop :=
  ∀ j (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ) (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ),
      Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL → IsWeightedHomogeneous ω' (s j)
        (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (β j) ω' ωL)

theorem symPolBL (h2 : 2 ≤ numSeg X.TT) {E : ℝ} (β : GlobalTheory X) (hβ : ∀ j, BLk C0 Cde CE1 CE2 X E j (β j))
    (s : Syms O C0 CE1 CE2 X) (hs : BalHom O C0 CE1 CE2 X β s) :
    symFam (KK O) X.p C0 CE1 CE2 X β s ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) := by
  classical
  unfold Pol
  rw [mem_restrictSupport_iff]
  intro μ hμ x
  have hwh : IsWeightedHomogeneous (wLet X x) (symFam (KK O) X.p C0 CE1 CE2 X β s)
      (∑ j, TD C0 CE1 CE2 X j (β j) (wLet X x)) :=
    IsWeightedHomogeneous.prod _ _ _ (fun j _ => ioBlock_wh' C0 CE1 CE2 X j O 0 (β j) (wLet X x) (fun _ _ _ => rfl)
      (fun _ => rfl) rfl (s j) (hs j))
  have h1 := hwh (mem_support_iff.1 (Finset.mem_coe.1 hμ))
  rw [weight_wLet] at h1
  rw [h1, Finset.sum_congr rfl fun j _ => TD_wLetBL C0 CE1 CE2 X j x (β j) (hβ j),
    ← natPartSum X.TT h2 (fun s => if s = x.1.val then hhDegs X.TT X.aT X.bT x else 0), Finset.sum_ite_eq',
    if_pos x.1.2]

theorem symNdBL (β : GlobalTheory X) (s : Syms O C0 CE1 CE2 X) (hs : BalHom O C0 CE1 CE2 X β s) :
    IsWeightedHomogeneous (wN X) (symFam (KK O) X.p C0 CE1 CE2 X β s) (ordFam C0 CE1 CE2 X β) := by
  have hwh : IsWeightedHomogeneous (wN X) (symFam (KK O) X.p C0 CE1 CE2 X β s)
      (∑ j, TD C0 CE1 CE2 X j (β j) (wN X)) :=
    IsWeightedHomogeneous.prod _ _ _ (fun j _ => ioBlock_wh' C0 CE1 CE2 X j O 0 (β j) (wN X)
      (fun x c c' => by
        rcases x with ⟨t, bb⟩
        cases bb
        · rw [wN_covS, wN_covS]
        · rw [wN_vecS, wN_vecS])
      (fun l => by rw [normal_weight_vector_zero_eq_zero, normal_weight_covector_zero, wN_vecS, wN_covS])
      (by rw [normal_weight_vector_zero_eq_zero, normal_weight_covector_zero, wN_vecS, wN_covS]) (s j) (hs j))
  have e : ∑ j, TD C0 CE1 CE2 X j (β j) (wN X) = ordFam C0 CE1 CE2 X β :=
    Finset.sum_congr rfl fun j _ => TD_wN C0 CE1 CE2 X j (β j)
  rwa [e] at hwh

theorem ioBlock_coeff (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (u : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) (μ : BV C0 CE1 CE2 X j →₀ ℕ) :
    (ioBlock (KK O) X.p C0 CE1 CE2 X j b u).coeff (ioExp C0 CE1 CE2 X j b μ) = u.coeff μ := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial ν c =>
    rw [ioBlock_monomial, coeff_monomial, coeff_monomial]
    by_cases h : ν = μ
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg fun e => h (ioExp_inj C0 CE1 CE2 X hp j b e)]
  | add p q hp' hq' => rw [ioBlock_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp', hq']

theorem ioBlock_ne_zero (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    {u : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)} (hu : u ≠ 0) : ioBlock (KK O) X.p C0 CE1 CE2 X j b u ≠ 0 := by
  intro h
  apply hu
  ext μ
  rw [← ioBlock_coeff hp j b u μ, h]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem ioD_ne_zero (hp : 0 < X.p) {mu : ℝ} (β : GlobalTheory X) (j : Fin (numSeg X.TT))
    {u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O)} (hu : u ≠ 0) :
    ioD O C0 CE1 CE2 mu X β j u ≠ 0 := by
  intro h
  refine ioBlock_ne_zero (C0 := C0) (CE1 := CE1) (CE2 := CE2) hp j (β j) (u := u) hu ?_
  show digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) * ioD O C0 CE1 CE2 mu X β j u = 0
  rw [h, mul_zero]

end Sym

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ThresholdStandardSeventeen
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem error_exponent_lower_bound {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) (h1 : 17 ≤ CE1) (h2 : 17 ≤ CE2) (hc : 1 ≤ X.c) :
    localOrderCap C0 X + (X.c : ℝ) * ka1 X + X.N1 * (X.k * X.Q) + X.c * (X.k * X.Q) ≤ X.E0 C0 CE1 CE2 := by
  have hp5 : (5 : ℝ) ≤ X.p := by exact_mod_cast St.p5
  have hp : (0 : ℝ) < X.p := by linarith
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have hk : (1 : ℝ) ≤ X.k := by have := St.N1k; linarith
  have hk0 : (0 : ℝ) < X.k := by linarith
  have hQ : (1 : ℝ) ≤ X.Q := one_le_pow₀ (by linarith)
  have hcr : (1 : ℝ) ≤ X.c := by exact_mod_cast hc
  have hLa : (0 : ℝ) ≤ X.La C0 := by have := St.La1; linarith
  have ha : (0 : ℝ) ≤ X.a := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ X.b' := St.bpos.le
  have A1 : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 := by positivity
  have B1 : 0 ≤ X.b' / (X.p : ℝ) := by positivity
  have L0 : 0 ≤ X.La C0 * X.a / (X.p * X.k) := by positivity
  have L2 : 0 ≤ X.La C0 * X.b' / X.k := by positivity
  have e1 : X.La C0 * X.N1 * X.a / (X.p * X.k) = X.N1 * (X.La C0 * X.a / (X.p * X.k)) := by ring
  have hL1 : X.La C0 * X.a / (X.p * X.k) ≤ X.La C0 * X.N1 * X.a / (X.p * X.k) := by
    rw [e1]; exact le_mul_of_one_le_left L0 hN1
  have e2 : X.La C0 / X.k * (4 * (X.a : ℝ) / X.p) = 4 * (X.La C0 * X.a / (X.p * X.k)) := by
    field_simp
  have e3 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) = (X.a : ℝ) / (X.p : ℝ) ^ 2 * (16 / X.p) := by
    field_simp
    ring
  have h16 : 16 / (X.p : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hp]; linarith
  have e4 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) ≤ 4 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) := by
    rw [e3, mul_comm 4]; exact mul_le_mul_of_nonneg_left h16 A1
  have e5 : 2 * X.La C0 * X.b' / X.k = 2 * (X.La C0 * X.b' / X.k) := by ring
  have e6 : 3 * X.b' / (X.p : ℝ) = 3 * (X.b' / X.p) := by ring
  have hO : localOrderCap C0 X ≤ 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) +
      4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k) := by
    unfold localOrderCap
    rw [add_mul, e2, e5, e6]
    linarith
  have L1 : 0 ≤ X.La C0 * X.N1 * X.a / (X.p * X.k) := le_trans L0 hL1
  have hfirst : 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) +
      4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k) ≤
      CE1 * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k) := by
    have hs : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k := by
      linarith
    have := mul_le_mul_of_nonneg_right h1 hs
    linarith
  have hkQ : 1 ≤ X.k * X.Q := one_le_mul_of_one_le_of_one_le hk hQ
  have hT : 0 ≤ X.k * X.N1 * X.Q * X.c := by positivity
  have t1 : X.k * X.N1 * X.Q * X.c ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := by
    have : X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = (X.k * X.Q) * (X.k * X.N1 * X.Q * X.c) := by ring
    rw [this]; exact le_mul_of_one_le_left hT hkQ
  have t2 : (X.N1 : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c := by
    have h0 : 0 ≤ (X.N1 : ℝ) * (X.k * X.Q) := by positivity
    have : X.k * X.N1 * X.Q * X.c = (X.N1 * (X.k * X.Q)) * X.c := by ring
    rw [this]; exact le_mul_of_one_le_right h0 hcr
  have t3 : (X.c : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c := by
    have h0 : 0 ≤ (X.c : ℝ) * (X.k * X.Q) := by positivity
    have : X.k * X.N1 * X.Q * X.c = (X.c * (X.k * X.Q)) * X.N1 := by ring
    rw [this]; exact le_mul_of_one_le_right h0 hN1
  have t4 : (X.c : ℝ) * ka1 X = 13 * (X.k * X.N1 * X.Q * X.c) := by unfold ka1; ring
  have hT2 : 0 ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := le_trans hT t1
  have hsecond : (X.c : ℝ) * ka1 X + X.N1 * (X.k * X.Q) + X.c * (X.k * X.Q) ≤ CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := by
    have : CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = CE2 * (X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c) := by ring
    rw [this, t4]
    have := mul_le_mul_of_nonneg_right h2 hT2
    linarith
  unfold Loc.E0 errorTermBound
  linarith

theorem room_of_std {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) (h1 : 17 ≤ CE1) (h2 : 17 ≤ CE2)
    (n : ℕ) (hn1 : 1 ≤ n) (hnc : n ≤ X.c) (β : GlobalTheory X)
    (hβ : ∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) (a0 : Fin (numSeg X.TT) → ℕ)
    (ha0 : ∀ j, (a0 j : ℤ) + ∑ i : Fin (segS X.TT j),
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤ (X.seg C0 CE1 CE2 j).A0 X.p)
    (j0 j : Fin (numSeg X.TT)) :
    usedX X β a0 j0 (rot _ j) ≤ segAPlus X.TT X.aT j - (β j).oPlus := by
  classical
  set j' := rot _ j with hj'
  have hp0 : 0 < X.p := St.pP.pos
  have hqG : X.p ^ segG X.TT j' ≤ X.p ^ X.G' := Nat.pow_le_pow_right hp0 (St.segB j').1
  have hq1 : 1 ≤ X.p ^ segG X.TT j' := Nat.one_le_pow _ _ hp0

  have hN2 : (∑ i : Fin (segS X.TT j'), X.p ^ (segDists X.TT j').get i *
      ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0)) ≤ X.N1 * ((X.m + 1) * X.p ^ X.G') := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin (segS X.TT j'))), X.p ^ (segDists X.TT j').get i *
        ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0) ≤ (X.m + 1) * X.p ^ X.G' := by
      intro i _
      have hd := (hβ j').1.1 i
      have s1 : (∑ c : Fin X.m, (β j').rz i c.succ) ≤ X.m * (X.seg C0 CE1 CE2 j').P X.p i := by
        have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin X.m)) (fun c => (β j').rz i c.succ)
          ((X.seg C0 CE1 CE2 j').P X.p i) (fun c _ => (hd c.succ).1.le)
        simpa using this
      have s2 : (β j').ry i 0 ≤ (X.seg C0 CE1 CE2 j').P X.p i := (hd 0).2.le
      calc X.p ^ (segDists X.TT j').get i * ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0)
          ≤ X.p ^ (segDists X.TT j').get i * ((X.m + 1) * (X.seg C0 CE1 CE2 j').P X.p i) :=
            Nat.mul_le_mul_left _ (by linarith)
        _ = (X.m + 1) * (X.p ^ (segDists X.TT j').get i * (X.seg C0 CE1 CE2 j').P X.p i) := by ring
        _ = (X.m + 1) * X.p ^ segG X.TT j' := by rw [pd_mul_P]
        _ ≤ (X.m + 1) * X.p ^ X.G' := Nat.mul_le_mul_left _ hqG
    have := Finset.sum_le_card_nsmul _ _ _ hi
    rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ (St.segB j').2)

  have hN3 : X.c * (X.m * (X.p ^ segG X.TT j' - 1)) + (if j' = j0 then X.c else 0) ≤ X.c * ((X.m + 1) * X.p ^ X.G') := by
    obtain ⟨q', hq'⟩ : ∃ q', X.p ^ segG X.TT j' = q' + 1 := ⟨X.p ^ segG X.TT j' - 1, by omega⟩
    have hite : (if j' = j0 then X.c else 0) ≤ X.c := by split_ifs <;> omega
    have e : X.p ^ segG X.TT j' - 1 = q' := by omega
    rw [e]
    have h3 : X.m * q' + 1 ≤ (X.m + 1) * X.p ^ X.G' := by
      calc X.m * q' + 1 ≤ (X.m + 1) * (q' + 1) := by nlinarith
        _ ≤ (X.m + 1) * X.p ^ X.G' := Nat.mul_le_mul_left _ (hq' ▸ hqG)
    calc X.c * (X.m * q') + (if j' = j0 then X.c else 0) ≤ X.c * (X.m * q') + X.c := by omega
      _ = X.c * (X.m * q' + 1) := by ring
      _ ≤ X.c * ((X.m + 1) * X.p ^ X.G') := Nat.mul_le_mul_left _ h3
  have hnat : usedX X β a0 j0 j' ≤ (X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) +
      X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G') := by
    unfold usedX
    linarith

  have hsum : ∑ i : Fin (segS X.TT j'), (if (i : ℕ) < (X.seg C0 CE1 CE2 j').sigma then ((β j').sg i : ℤ) else 0) =
      ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · rw [((hβ j').2.1 i (not_lt.1 h)).2.2.2]; rfl
  have hA := ha0 j'
  rw [hsum] at hA
  have hAr : ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤ ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ) := by
    exact_mod_cast hA
  have hfl : ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ) ≤
      ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j' : ℕ) : ℝ) := Int.floor_le _
  have hqr : (0 : ℝ) < ((X.p ^ segG X.TT j' : ℕ) : ℝ) := by exact_mod_cast hq1
  have hN1 : ((X.p ^ segG X.TT j' : ℕ) : ℝ) * ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤
      (X.a : ℝ) - X.E0 C0 CE1 CE2 := by
    have := (le_div_iff₀ hqr).1 (hAr.trans hfl)
    linarith

  have hc1 : 1 ≤ X.c := le_trans hn1 hnc
  have hka : 0 ≤ ka1 X := by
    unfold ka1
    have hk : (0 : ℝ) ≤ X.k := by have := St.N1k; have : (0 : ℝ) ≤ X.N1 := Nat.cast_nonneg _; linarith
    have hQ : (0 : ℝ) ≤ X.Q := by unfold Loc.Q; positivity
    positivity
  have hoP : ((β j).oPlus : ℝ) ≤ localOrderCap C0 X + (X.c : ℝ) * ka1 X := by
    have h := (hβ j).2.2.2.2
    have hcn : ((X.c - n : ℕ) : ℝ) ≤ (X.c : ℝ) := by exact_mod_cast Nat.sub_le _ _
    have := mul_le_mul_of_nonneg_right hcn hka
    linarith
  have haP : (X.a : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ) := (St.winA _ (next_mem X.TT j).1).1
  have hE := error_exponent_lower_bound St h1 h2 hc1
  have hreal : ((usedX X β a0 j0 j' + (β j).oPlus : ℕ) : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ) := by
    have hcast : ((usedX X β a0 j0 j' : ℕ) : ℝ) ≤
        (((X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) +
      X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G') : ℕ) : ℝ) := by exact_mod_cast hnat
    have hk : X.k = (X.m : ℝ) + 1 := rfl
    have hQ : X.Q = (X.p : ℝ) ^ X.G' := rfl
    push_cast at hcast hN1 ⊢
    rw [hk, hQ] at hE
    linarith
  have : usedX X β a0 j0 j' + (β j).oPlus ≤ segAPlus X.TT X.aT j := by exact_mod_cast hreal
  omega

theorem threshold_standard_seventeen : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => (17 ≤ CE1 ∧ 17 ≤ CE2) ∧
    ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 17) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ a1 a2 _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      ⟨⟨a1, a2⟩, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩

theorem restRoom : RestRoom :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h X hD hH hc n hn1 hnc β hβ a0 ha0 j0 j =>
    room_of_std (h.2 X hD hH hc) h.1.1 h.1.2 n hn1 hnc β hβ a0 ha0 j0 j) threshold_standard_seventeen

end Formalism.MainNotions.ColumnSystems.Pf
end
end

