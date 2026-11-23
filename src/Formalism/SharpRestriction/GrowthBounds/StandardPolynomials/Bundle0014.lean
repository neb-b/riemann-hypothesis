module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultMk
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0012

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.StdPolyEq
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Exp

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def rPl (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : MonH X :=
  (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0) ((β j).rz i 0)) +
    (∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, false), c.succ) ((β j).ry i c.succ)) +
    ∑ c : Fin X.m, Finsupp.single ((topEnd X j, false), c.succ) (L.γ j c)

def zPart (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  ∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)))

def nPart (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, false), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0)) +
    ∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ)

def stdE (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : MonH X :=
  rPl L j + Finsupp.single ((topEnd X j, true), 0) (segAPlus X.TT X.aT j - (β j).oPlus) + zPart C0 CE1 CE2 X β j +
    nPart C0 CE1 CE2 X β j

theorem stdPoly_eq (O : Type) [CommRing O] [IsDomain O] (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (hsg : ∀ i : Fin (segS X.TT j), ¬ (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma → (β j).sg i = 0) :
    L.stdPoly O j = monomial (stdE L j) 1 := by
  classical
  have hd : digitMon (KK O) C0 CE1 CE2 X j (β j) = monomial (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
      (Finsupp.single ((topOdd X j i, true), c) ((β j).rz i c) +
        Finsupp.single ((topOdd X j i, false), c) ((β j).ry i c))) 1 := by
    unfold digitMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have hs : sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) = monomial (∑ i : Fin (segS X.TT j),
      if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i)
      else 0) 1 := by
    unfold sTopMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
    · simp
  have hu : (∏ l : Fin (BDk C0 CE1 CE2 mu X β j).T.t,
      ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
        (Fin.castSucc l))) ^ (BDk C0 CE1 CE2 mu X β j).T.z l) =
      monomial (∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
          ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))) 1 := by
    rw [← uTop_sum (X.seg C0 CE1 CE2 j) (fun i => Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
          ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))), monomial_sum_one]
    refine Finset.prod_congr rfl fun l _ => ?_
    unfold scalZ
    rw [ioD_scal, ← pow_mul, X_pow_eq_monomial]
    rfl
  have hx : ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
          (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t))) ^ (BDk C0 CE1 CE2 mu X β j).zPlus =
      monomial (Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1))) (segAPlus X.TT X.aT j - (β j).oPlus)) 1 := by
    unfold scalZ
    rw [ioD_scalLast, X_pow_eq_monomial]
    rfl
  have hxi : (∏ c, ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m
      (BDk C0 CE1 CE2 mu X β j).T.t c)) ^ L.γ j c) =
      monomial (∑ c : Fin X.m, Finsupp.single ((topEnd X j, false), c.succ) (L.γ j c)) 1 := by
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    unfold xiVar
    rw [ioD_end β j 1 (by omega) _ (by rfl), X_pow_eq_monomial]
    rfl
  unfold LvDat.stdPoly
  simp only [map_mul, map_prod, map_pow]
  rw [hd, hs, hu, hx, hxi]
  simp only [monomial_mul, one_mul]
  congr 1
  unfold stdE rPl zPart nPart
  have hi : ∀ i : Fin (segS X.TT j),
      (∑ c : Fin (X.m + 1), (Finsupp.single ((topOdd X j i, true), c) ((β j).rz i c) +
        Finsupp.single ((topOdd X j i, false), c) ((β j).ry i c))) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i)
      else 0) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
          ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))) =
      Finsupp.single ((topOdd X j i, true), 0) ((β j).rz i 0) +
      (∑ c : Fin X.m, Finsupp.single ((topOdd X j i, false), c.succ) ((β j).ry i c.succ)) +
      Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i))) +
      Finsupp.single ((topOdd X j i, false), 0) ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0) +
      ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ) := by
    intro i
    rw [Fin.sum_univ_succ, Finset.sum_add_distrib, Finsupp.single_add]
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · simp only [if_pos h]
      abel
    · simp only [if_neg h, hsg i h, mul_zero, Finsupp.single_zero]
      abel
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin (segS X.TT j)))) rfl (fun i _ => hi i)
  simp only [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_add_distrib] at hsum ⊢
  have key : ∀ (a b c d e x y u1 u2 u3 : MonH X), u1 + u2 + u3 = a + b + c + d + e →
      u1 + u2 + (u3 + x + y) = a + b + y + x + c + (d + e) := by
    intro a b c d e x y u1 u2 u3 h
    have : u1 + u2 + (u3 + x + y) = (u1 + u2 + u3) + (x + y) := by abel
    rw [this, h]
    abel
  rw [key _ _ _ _ _ _ _ _ _ _ hsum]

end Exp

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TopOddNeEndAny
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Mk

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

theorem mono_two (v1 v2 : VarH X) (a b : ℕ) :
    (monomial (Finsupp.single v1 a + Finsupp.single v2 b) (1 : KK O) : RHH O X) =
      MvPolynomial.X v1 ^ a * MvPolynomial.X v2 ^ b := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

theorem softMk (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (C0 CE1 CE2 : ℝ) (a : IM X) :
    SoftOK S.w (fMk O C0 CE1 CE2 X a) (oMk C0 CE1 CE2 X a) (monomial (aMk C0 CE1 CE2 X a) 1) (dgMk C0 CE1 CE2 X a) := by
  rcases a with x | x | x | c
  · have h := softKSP S hS hD x.1 x.2 ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
    rw [sgKS_powP] at h
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ segG X.TT x.1) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) ((X.seg C0 CE1 CE2 x.1).P X.p x.2)) 1) _
    rw [mono_two]
    exact h
  · have h := softKW S hS hD x.1 x.2.1 x.2.2
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topOdd X x.1 x.2.1, true), x.2.2.succ) 1 +
      Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2.1)) 1) _
    rw [mono_two, pow_one]
    exact h
  · have h := softKS S hS hD x.1 x.2
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) 1) 1) _
    rw [mono_two, pow_one]
    exact h
  · have h := softLoc S.w hD h2 c
    show SoftOK S.w _ _ (monomial (∑ j : Fin (numSeg X.TT),
      Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j - 1)) 1) _
    rw [monomial_sum_one]
    have e : ∏ j : Fin (numSeg X.TT), (monomial (Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1)))
        (X.p ^ segG X.TT j - 1)) (1 : KK O) : RHH O X) = sgLoc O X := by
      unfold sgLoc
      exact Finset.prod_congr rfl fun j _ => by rw [X_pow_eq_monomial]
    rw [e]
    exact h

theorem fMk_pol (C0 CE1 CE2 : ℝ) (a : IM X) :
    fMk O C0 CE1 CE2 X a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgMk C0 CE1 CE2 X a) := by
  rcases a with x | x | x | c
  · exact mem_Pol_iff.2 fun l => by
      have h := (mem_Pol_iff.1 (kS_pol (O := O) x.1 x.2) l).pow ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
      rw [smul_eq_mul] at h
      exact h
  · exact kW_pol x.1 x.2.1 _
  · exact kS_pol x.1 x.2
  · exact loc_pol _

end Mk

section Deg

variable {X : Loc}

theorem topStart_inj (X : Loc) : Function.Injective (topStart X) := by
  intro j j' h
  have h1 : (evenTops X.TT).get j = (evenTops X.TT).get j' := congrArg Subtype.val h
  have hnd : (evenTops X.TT).Nodup := Finset.sort_nodup _ _
  exact hnd.get_inj_iff.mp h1

theorem topOdd_ne_endAny (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (j' : Fin (numSeg X.TT)) :
    topOdd X j i ≠ topEnd X j' := by
  intro h
  have h1 : (segPos X.TT j i).val = (segNext X.TT j').val := congrArg (fun x : X.TT => (x.val : ℕ)) h
  exact (pos_mem X.TT j i).2 (h1 ▸ (next_mem X.TT j').2)

theorem pd_le (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    X.p ^ (segDists X.TT j).get i ≤ X.p ^ segG X.TT j :=
  Nat.pow_le_pow_right hD.1.pos (dist_pos_lt X.TT j i).2.le

theorem dgMk_le (hD : D1num X) (hG : ∀ j, segG X.TT j ≤ X.G') (C0 CE1 CE2 : ℝ) (a : IM X) (l : X.TT × Bool) :
    dgMk C0 CE1 CE2 X a l ≤ X.p ^ X.G' := by
  have hp : 1 ≤ X.p := hD.1.one_lt.le
  have hpG : ∀ j, X.p ^ segG X.TT j ≤ X.p ^ X.G' := fun j => Nat.pow_le_pow_right hp (hG j)
  have h1 : 1 ≤ X.p ^ X.G' := Nat.one_le_pow _ _ hp
  have hdl : ∀ j i, X.p ^ (segDists X.TT j).get i ≤ X.p ^ X.G' := fun j i => (pd_le hD j i).trans (hpG j)
  have hso : ∀ j i, topStart X j ≠ topOdd X j i := by
    intro j i h
    have h2 : (segStart X.TT j).val = (segPos X.TT j i).val := congrArg (fun x : X.TT => (x.val : ℕ)) h
    exact (pos_mem X.TT j i).2 (h2 ▸ (start_mem X.TT j).2)
  rcases a with x | x | x | x
  · obtain ⟨-, hdG⟩ := dist_pos_lt X.TT x.1 x.2
    have hPd : (X.seg C0 CE1 CE2 x.1).P X.p x.2 * X.p ^ (segDists X.TT x.1).get x.2 = X.p ^ segG X.TT x.1 := by
      show X.p ^ (segG X.TT x.1 - (segDists X.TT x.1).get x.2) * _ = _
      rw [← pow_add, Nat.sub_add_cancel hdG.le]
    have hPle : (X.seg C0 CE1 CE2 x.1).P X.p x.2 ≤ X.p ^ segG X.TT x.1 := by
      rw [← hPd]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    simp only [dgMk, dgKS, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp)
    · rw [mul_one, add_zero, hPd]
      exact hpG _
    · rw [mul_zero, zero_add, mul_one]
      exact hPle.trans (hpG _)
    · simp
  · simp only [dgMk, dgKW, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp [Ne.symm (hso x.1 x.2.1)])
    · simpa using h1
    · simpa using hdl x.1 x.2.1
    · simp
  · simp only [dgMk, dgKS, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp)
    · simpa using hdl x.1 x.2
    · simpa using h1
    · simp
  · simp only [dgMk, dgLoc, dX]
    by_cases hex : ∃ j0, (topStart X j0, true) = l
    · obtain ⟨j0, hj0⟩ := hex
      rw [Finset.sum_eq_single j0]
      · rw [if_pos hj0, mul_one]
        exact (Nat.sub_le _ _).trans (hpG j0)
      · intro j _ hj
        rw [if_neg, mul_zero]
        intro h
        apply hj
        apply topStart_inj X
        rw [← hj0] at h
        exact (Prod.mk.inj h).1
      · intro h
        exact absurd (Finset.mem_univ j0) h
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro j _
        rw [if_neg (fun h => hex ⟨j, h⟩), mul_zero]

theorem dgMk_Y (C0 CE1 CE2 : ℝ) (a : IM X) (j' : Fin (numSeg X.TT)) : dgMk C0 CE1 CE2 X a (topEnd X j', false) = 0 := by
  rcases a with x | x | x | x <;>
    simp [dgMk, dgKS, dgKW, dgLoc, dX, topOdd_ne_endAny]

end Deg

section Sums

variable {X : Loc}

theorem bMk_eq (C0 CE1 CE2 : ℝ) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) :
    (∑ i : Fin (segS X.TT j), (β j).sg i • ((Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j) +
        Finsupp.single ((topOdd X j i, false), 0) ((X.seg C0 CE1 CE2 j).P X.p i) : MonH X))) +
    ((∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, (β j).rz i c.succ • ((Finsupp.single ((topOdd X j i, true), c.succ) 1 +
        Finsupp.single ((topStart X j, true), 0) (X.p ^ (segDists X.TT j).get i) : MonH X))) +
    ((∑ i : Fin (segS X.TT j), (β j).ry i 0 • ((Finsupp.single ((topStart X j, true), 0) (X.p ^ (segDists X.TT j).get i) +
        Finsupp.single ((topOdd X j i, false), 0) 1 : MonH X))) +
      Finsupp.single ((topStart X j, true), 0) (X.c * (X.m * (X.p ^ segG X.TT j - 1))))) = bMk C0 CE1 CE2 X β j := by
  unfold bMk
  simp only [Finsupp.single_add, smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]
  ext k
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_apply', Finsupp.single_apply]
  by_cases hs : ((topStart X j, true), (0 : Fin (X.m + 1))) = k
  · subst hs
    simp [Finset.mul_sum, mul_add, Finset.sum_add_distrib, Fin.succ_ne_zero]
    try simp only [mul_comm, mul_left_comm]
    try abel
    try ring_nf
  · simp only [hs, if_false, Finset.sum_const_zero, zero_add, add_zero]
    try simp only [mul_comm, mul_left_comm]
    try abel
    try ring_nf

theorem sum_aMk (C0 CE1 CE2 : ℝ) (β : GlobalTheory X) :
    ∑ a, multMk X β a • aMk C0 CE1 CE2 X a = ∑ j, bMk C0 CE1 CE2 X β j := by
  simp only [← bMk_eq C0 CE1 CE2 β, Finset.sum_add_distrib]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_sigma]
    rfl
  congr 1
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
    rfl
  congr 1
  · rw [Fintype.sum_sigma]
    rfl
  · simp only [multMk, aMk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.smul_sum, Finsupp.smul_single,
      smul_eq_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    ring

end Sums

end Formalism.MainNotions.ColumnSystems.Pf
end
end

