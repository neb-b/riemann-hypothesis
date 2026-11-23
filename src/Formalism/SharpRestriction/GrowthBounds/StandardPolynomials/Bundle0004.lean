module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.DensitySumsAndDomination

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColsDef
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

structure ColSys (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O) (mu : ℝ) (β : GlobalTheory X)
    (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) where
  ι : Type
  fin : Fintype ι
  Kc : ι → MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)
  dK : ι → Fin (2 * segS X.TT j + 1) → ℕ
  pl : ι → MonH X
  fC : ι → RHH O X
  oC : ι → ℕ
  dgC : ι → X.TT × Bool → ℕ
  a0 : ℕ
  KInt : ∀ a, Kc a ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)
  KPol : ∀ a, Kc a ∈ Pol (KK O) X.m (dK a)
  digit_le_one : ∀ a i, dK a i ≤ 1
  dKsum : ∀ i, ∑ a, dK a i = (L.LL j).deg i
  Kprod : ∏ a, Kc a = G
  facC : ∀ a, IsFac w (fC a) (oC a)
    (monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)))
  homC : ∀ a, HomW (ndHom X) (oC a)
    (monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)))
  fPol : ∀ a, fC a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC a)
  polC : ∀ a, monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC a)
  plQ : ∀ a l, multideg (pl a) l ≤ X.p ^ X.G'
  dgCQ : ∀ a l, dgC a l ≤ X.p ^ X.G'
  dgCY : ∀ a j', dgC a (topEnd X j', false) = 0
  a0le : (a0 : ℤ) + ∑ i : Fin (segS X.TT j), (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤
    (X.seg C0 CE1 CE2 j).A0 X.p
  plSum : ∑ a, pl a = Finsupp.single ((topStart X j, true), 0) ((X.seg C0 CE1 CE2 j).Qj X.p * a0) +
    ∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)))
  oSum : ∑ a, oC a = (∑ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i *
      (L.LL j).deg ⟨2 * (i : ℕ), by have := i.2; omega⟩) + (L.LL j).deg ⟨2 * segS X.TT j, by omega⟩

def ColsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β) (j : Fin (numSeg X.TT)) (y : Tx X.m (L.LL j)),
      y ∈ sAll (L.LL j) (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr →
      Nonempty (ColSys C0 CE1 CE2 X O S.w (mm + (n : ℝ) * ka1 X) β L j (psiR (KK O) (L.LL j) y))

def RestCols : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoDVariableLastEqTopEnd
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def tgStdE (L : LvDat C0 CE1 CE2 mu X β) : TgPlace X → Bool → Fin (X.m + 1) → ℕ
  | ⟨j, some i⟩, true, c => (β j).rz i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
      (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) else 0)
  | ⟨j, some i⟩, false, c => (β j).ry i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) else 0)
  | ⟨j, none⟩, true, c => if c = 0 then segAPlus X.TT X.aT j - (β j).oPlus else 0
  | ⟨j, none⟩, false, c => Fin.cases 0 (L.γ j) c

def tgStdX (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) : MonH X :=
  Finsupp.equivFunOnFinite.symm fun v => tgStdE L ((Equiv.ofBijective _ (tgTop_bij X h2)).symm v.1.1) v.1.2 v.2

theorem tgStdX_at (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) (pl : TgPlace X) (b : Bool) (c : Fin (X.m + 1)) :
    tgStdX h2 L ((tgTop X pl, b), c) = tgStdE L pl b c := by
  unfold tgStdX
  rw [Finsupp.equivFunOnFinite_symm_apply_apply]
  show tgStdE L ((Equiv.ofBijective _ (tgTop_bij X h2)).symm (tgTop X pl)) b c = _
  rw [Equiv.ofBijective_symm_apply_apply]

variable (O : Type) [CommRing O] [IsDomain O]

theorem tg_ioD_Z (j : Fin (numSeg X.TT)) (l : Fin (X.seg C0 CE1 CE2 j).t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t (Fin.castSucc l))) =
      MvPolynomial.X ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), 0) ^
        (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  have h := MvPolynomial.aeval_X (R := KK O) (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^
    symLev X.p C0 CE1 CE2 X j v) (Sum.inr (Fin.castSucc l, false))
  rw [sv_Z, sl_Z] at h
  exact h

theorem ioD_variable_last_eq_top_end (j : Fin (numSeg X.TT)) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
      (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t))) = MvPolynomial.X ((topEnd X j, true), 0) := by
  have h := MvPolynomial.aeval_X (R := KK O) (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^
    symLev X.p C0 CE1 CE2 X j v) (Sum.inr (Fin.last _, false))
  rw [symbol_variable_last, symbol_level_last, pow_one] at h
  exact h

theorem tg_ioD_xi (j : Fin (numSeg X.TT)) (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c)) =
      MvPolynomial.X ((topEnd X j, false), c.succ) := by
  have h := MvPolynomial.aeval_X (R := KK O) (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^
    symLev X.p C0 CE1 CE2 X j v) (Sum.inl (Fin.last (2 * segS X.TT j + 1), c))
  rw [sv_xi, sl_xi, pow_one] at h
  exact h

theorem prod_pow_ite_zero_eq {M : Type} [CommMonoid M] {k : ℕ} (f : Fin (k + 1) → M) (a : ℕ) :
    ∏ c, f c ^ (if c = 0 then a else 0) = f 0 ^ a := by
  rw [Finset.prod_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tg_stdPoly_eq (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) :
    L.stdPoly O j = segMon O X j (tgStdX h2 L) := by
  have hz : ∀ i c, tgStdX h2 L ((topOdd X j i, true), c) = tgStdE L ⟨j, some i⟩ true c :=
    fun i c => tgStdX_at h2 L ⟨j, some i⟩ true c
  have hy : ∀ i c, tgStdX h2 L ((topOdd X j i, false), c) = tgStdE L ⟨j, some i⟩ false c :=
    fun i c => tgStdX_at h2 L ⟨j, some i⟩ false c
  have hx : ∀ c, tgStdX h2 L ((topEnd X j, true), c) = tgStdE L ⟨j, none⟩ true c :=
    fun c => tgStdX_at h2 L ⟨j, none⟩ true c
  have hx' : ∀ c, tgStdX h2 L ((topEnd X j, false), c) = tgStdE L ⟨j, none⟩ false c :=
    fun c => tgStdX_at h2 L ⟨j, none⟩ false c
  unfold segMon LvDat.stdPoly
  simp only [hz, hy, hx, hx', tgStdE, map_mul, map_prod, map_pow, ioD_variable_last_eq_top_end, tg_ioD_xi]
  have e1 : ∏ l : Fin (BDk C0 CE1 CE2 mu X β j).T.t,
      (ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
        (Fin.castSucc l)))) ^ (BDk C0 CE1 CE2 mu X β j).T.z l =
      ∏ i : Fin (segS X.TT j), if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        ((MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i) else 1 := by
    rw [← tg_prod_uTop (X.seg C0 CE1 CE2 j) (fun i => ((MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^
      (X.seg C0 CE1 CE2 j).P X.p i) ^ (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))]
    refine Finset.prod_congr rfl fun l _ => ?_
    exact congrArg (fun y => y ^ (BDk C0 CE1 CE2 mu X β j).T.z l) (tg_ioD_Z (mu := mu) (β := β) O j l)
  rw [e1]
  have e2 : ∏ c : Fin (X.m + 1), ((MvPolynomial.X ((topEnd X j, true), c) : RHH O X) ^
        (if c = 0 then segAPlus X.TT X.aT j - (β j).oPlus else 0) *
      MvPolynomial.X ((topEnd X j, false), c) ^ (Fin.cases 0 (L.γ j) c : ℕ)) =
      MvPolynomial.X ((topEnd X j, true), 0) ^ (segAPlus X.TT X.aT j - (β j).oPlus) *
        ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, false), c.succ) ^ L.γ j c := by
    rw [Finset.prod_mul_distrib, prod_pow_ite_zero_eq (fun c => (MvPolynomial.X ((topEnd X j, true), c) : RHH O X)),
      Fin.prod_univ_succ]
    simp
  rw [e2]
  have e3 : ∀ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
      ((MvPolynomial.X ((topOdd X j i, true), c) : RHH O X) ^ ((β j).rz i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
        (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
          (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) else 0)) *
      MvPolynomial.X ((topOdd X j i, false), c) ^ ((β j).ry i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) else 0))) =
      (∏ c : Fin (X.m + 1), ((MvPolynomial.X ((topOdd X j i, true), c) : RHH O X) ^ (β j).rz i c *
        MvPolynomial.X ((topOdd X j i, false), c) ^ (β j).ry i c)) *
      ((if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^ ((X.seg C0 CE1 CE2 j).P X.p i *
            (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).w i)) *
          MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i) else 1) *
       (if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        ((MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i) else 1)) := by
    intro i
    simp only [pow_add]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      prod_pow_ite_zero_eq (fun c => (MvPolynomial.X ((topOdd X j i, true), c) : RHH O X)),
      prod_pow_ite_zero_eq (fun c => (MvPolynomial.X ((topOdd X j i, false), c) : RHH O X)), Finset.prod_mul_distrib]
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos hi, if_pos hi, if_pos hi, if_neg (by omega)]
      ring
    · rw [if_neg hi, if_neg hi, if_neg hi, if_pos (by omega), mul_zero, pow_zero, ← pow_mul]
      ring
  rw [Finset.prod_congr rfl fun i _ => e3 i, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  unfold digitMon sTopMon
  show _ * _ * (_ * MvPolynomial.X ((topEnd X j, true), 0) ^ (segAPlus X.TT X.aT j - (β j).oPlus) * _) = _
  ring

theorem tg_std_eq (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) (Std : MonH X)
    (h : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) : Std = tgStdX h2 L := by
  have e : (monomial Std (1 : KK O) : RHH O X) = monomial (tgStdX h2 L) 1 := by
    rw [h, tg_mono_split O X h2]
    exact Finset.prod_congr rfl fun j _ => tg_stdPoly_eq O h2 L j
  exact MvPolynomial.monomial_left_injective (one_ne_zero) e

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SegmentBlockOfMonomial
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem prod_uTop {M : Type} [CommMonoid M] {s : ℕ} (S : SegData s) (f : Fin s → M) :
    ∏ i, f i = (∏ i : Fin s, if (i : ℕ) < S.sigma then f i else 1) * ∏ l : Fin S.t, f (uTop S l) := by
  classical
  have h1 : ∏ l : Fin S.t, f (uTop S l) = ∏ i : Fin s, if S.sigma ≤ i.val then f i else 1 := by
    rw [← Finset.prod_filter]
    refine Finset.prod_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro l _
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
    · intro l _ l' _ h
      apply Fin.ext
      have h' : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
      omega
    · intro i hi
      have hi' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
      have := i.2
      exact ⟨⟨i.val - S.sigma, by unfold SegData.t; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _),
        Fin.ext (by show S.sigma + (i.val - S.sigma) = i.val; omega)⟩
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < S.sigma
  · rw [if_pos h, if_neg (by omega), mul_one]
  · rw [if_neg h, if_pos (by omega), one_mul]

def mEps (K : Type) [CommRing K] {s r : ℕ} (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    MvPolynomial (Fin (2 * s + 1) × Fin r) K :=
  (∏ i, ∏ c, (X (chW i, c) ^ ez i c * X (chE i, c) ^ ey i c)) * ∏ c, X (chU s, c) ^ ax c

section A

variable (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))

def ezA (A : MonH X) (i : Fin (segS X.TT j)) (c : Fin X.m) : ℕ :=
  A ((topOdd X j i, true), c.succ) / (X.seg C0 CE1 CE2 j).P X.p i
def eyA (A : MonH X) (i : Fin (segS X.TT j)) (c : Fin X.m) : ℕ :=
  A ((topOdd X j i, false), c.succ) / (X.seg C0 CE1 CE2 j).P X.p i
def axA (A : MonH X) (c : Fin X.m) : ℕ := A ((topEnd X j, true), c.succ)
def z0A (A : MonH X) (i : Fin (segS X.TT j)) : ℕ := A ((topOdd X j i, true), 0) / (X.seg C0 CE1 CE2 j).P X.p i
def y0A (A : MonH X) (i : Fin (segS X.TT j)) : ℕ := A ((topOdd X j i, false), 0) / (X.seg C0 CE1 CE2 j).P X.p i

def segmentBlockOfMonomial (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ) (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) :
    SegBlock (segS X.TT j) X.m where
  rz := fun i c => A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i
  ry := fun i c => A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i
  o := fun i => if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else
    jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + y0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c
  w := fun i => if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then du (chW i) + ∑ c, ezA C0 CE1 CE2 X j A i c else 0
  sg := fun i => if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then y0A C0 CE1 CE2 X j A i else 0
  oPlus := jp + du (chU _) + ∑ c, axA X j A c

theorem ioA_X (v : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) :
    ioA (KK O) X.p C0 CE1 CE2 X j (MvPolynomial.X v) =
      MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioA
  rw [aeval_X]

theorem ioA_mEps (ez ey : Fin (segS X.TT j) → Fin X.m → ℕ) (ax : Fin X.m → ℕ) :
    ioA (KK O) X.p C0 CE1 CE2 X j (rename (chainEmb (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (mEps (KK O) ez ey ax)) =
      (∏ i, ∏ c : Fin X.m, ((MvPolynomial.X ((topOdd X j i, true), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^ ez i c *
        (MvPolynomial.X ((topOdd X j i, false), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^ ey i c)) *
      ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, true), c.succ) ^ ax c := by
  unfold mEps
  simp only [map_mul, map_prod, map_pow, rename_X, chainEmb, ioA_X]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun c _ => ?_
    have a1 := symbol_variable_lower_letter C0 CE1 CE2 X j i c
    have a2 := symbol_level_lower_letter C0 CE1 CE2 X j i c
    have a3 := sv_E C0 CE1 CE2 X j i c
    have a4 := sl_E C0 CE1 CE2 X j i c
    unfold chW chE
    rw [a1, a2, a3, a4]
  · refine Finset.prod_congr rfl fun c _ => ?_
    have a1 := sv_U C0 CE1 CE2 X j c
    have a2 := sl_U C0 CE1 CE2 X j c
    unfold chU
    rw [a1, a2, pow_one]

theorem segMon_eq (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ) (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X)
    (γ : Fin X.m → ℕ)
    (hz0 : ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
      coarseA X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i - (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).w i =
        z0A C0 CE1 CE2 X j A i)
    (hy0 : A ((topEnd X j, false), 0) = 0) (hγ : ∀ c : Fin X.m, A ((topEnd X j, false), c.succ) = γ c) :
    segMon O X j A =
      digitMon (KK O) C0 CE1 CE2 X j (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) *
        sTopMon (KK O) X.p C0 CE1 CE2 X j (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) *
      (ioA (KK O) X.p C0 CE1 CE2 X j (rename (chainEmb (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t)
          (mEps (KK O) (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A))) *
        ioA (KK O) X.p C0 CE1 CE2 X j (∏ l : Fin (X.seg C0 CE1 CE2 j).t,
          (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              z0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) *
            MvPolynomial.X (scalS (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l))) *
        ioA (KK O) X.p C0 CE1 CE2 X j
          (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last _)) ^ A ((topEnd X j, true), 0)) *
        ioA (KK O) X.p C0 CE1 CE2 X j (∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t c) ^ γ c)) := by
  classical
  set P := fun i => (X.seg C0 CE1 CE2 j).P X.p i with hP
  set Xz : Fin (segS X.TT j) → Fin (X.m + 1) → RHH O X := fun i c => MvPolynomial.X ((topOdd X j i, true), c) with hXz
  set Xy : Fin (segS X.TT j) → Fin (X.m + 1) → RHH O X := fun i c => MvPolynomial.X ((topOdd X j i, false), c) with hXy

  have i2 : ioA (KK O) X.p C0 CE1 CE2 X j (∏ l : Fin (X.seg C0 CE1 CE2 j).t,
          (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              z0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) *
            MvPolynomial.X (scalS (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l))) =
      ∏ l : Fin (X.seg C0 CE1 CE2 j).t, ((fun i => (Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i *
        (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i) (uTop (X.seg C0 CE1 CE2 j) l)) := by
    simp only [map_prod, map_mul, map_pow, ioA_X]
    refine Finset.prod_congr rfl fun l _ => ?_
    unfold scalZ scalS
    rw [sv_Z, sl_Z, sv_Z, sl_Z]
    rfl
  have i3 : ioA (KK O) X.p C0 CE1 CE2 X j
      (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last _)) ^ A ((topEnd X j, true), 0)) =
      MvPolynomial.X ((topEnd X j, true), 0) ^ A ((topEnd X j, true), 0) := by
    rw [map_pow, ioA_X]
    unfold scalZ
    rw [symbol_variable_last, symbol_level_last, pow_one]
    rfl
  have i4 : ioA (KK O) X.p C0 CE1 CE2 X j
      (∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t c) ^ γ c) =
      ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, false), c.succ) ^ γ c := by
    simp only [map_prod, map_pow, ioA_X]
    refine Finset.prod_congr rfl fun c _ => ?_
    unfold xiVar
    rw [sv_xi, sl_xi, pow_one]
  rw [ioA_mEps, i2, i3, i4]

  have hS : sTopMon (KK O) X.p C0 CE1 CE2 X j (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) =
      ∏ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (fun i => (Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i * (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i) i else 1 := by
    unfold sTopMon
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos h, if_pos h, hz0 i h]
      have : (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).sg i = y0A C0 CE1 CE2 X j A i := by
        show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = _
        rw [if_pos h]
      rw [this, pow_mul, pow_mul]
    · rw [if_neg h, if_neg h]
  rw [hS]

  have hodd : ∀ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
      (Xz i c ^ A ((topOdd X j i, true), c) * Xy i c ^ A ((topOdd X j i, false), c)) =
      (∏ c : Fin (X.m + 1), (Xz i c ^ (A ((topOdd X j i, true), c) % P i) * Xy i c ^ (A ((topOdd X j i, false), c) % P i))) *
      ((Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i * (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i) *
      ∏ c : Fin X.m, ((Xz i c.succ ^ P i) ^ ezA C0 CE1 CE2 X j A i c * (Xy i c.succ ^ P i) ^ eyA C0 CE1 CE2 X j A i c) := by
    intro i
    have e1 : ∀ c : Fin (X.m + 1), Xz i c ^ A ((topOdd X j i, true), c) * Xy i c ^ A ((topOdd X j i, false), c) =
        (Xz i c ^ (A ((topOdd X j i, true), c) % P i) * Xy i c ^ (A ((topOdd X j i, false), c) % P i)) *
        ((Xz i c ^ P i) ^ (A ((topOdd X j i, true), c) / P i) * (Xy i c ^ P i) ^ (A ((topOdd X j i, false), c) / P i)) := by
      intro c
      conv_lhs => rw [← Nat.mod_add_div (A ((topOdd X j i, true), c)) (P i),
        ← Nat.mod_add_div (A ((topOdd X j i, false), c)) (P i)]
      rw [pow_add, pow_add, pow_mul, pow_mul]
      ring
    rw [Finset.prod_congr rfl fun c _ => e1 c, Finset.prod_mul_distrib, mul_assoc]
    congr 1
    rw [Fin.prod_univ_succ]
    rfl
  unfold segMon digitMon
  rw [Finset.prod_congr rfl fun i _ => hodd i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_uTop (X.seg C0 CE1 CE2 j) (fun i => (Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i * (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i)]
  have hend : ∏ c : Fin (X.m + 1), ((MvPolynomial.X ((topEnd X j, true), c) : RHH O X) ^ A ((topEnd X j, true), c) *
      MvPolynomial.X ((topEnd X j, false), c) ^ A ((topEnd X j, false), c)) =
      (∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, true), c.succ) ^ axA X j A c) *
      MvPolynomial.X ((topEnd X j, true), 0) ^ A ((topEnd X j, true), 0) *
      ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, false), c.succ) ^ γ c := by
    rw [Fin.prod_univ_succ, hy0, pow_zero, mul_one, Finset.prod_mul_distrib]
    simp only [hγ]
    unfold axA
    ring
  rw [hend]
  show (∏ i, ∏ c : Fin (X.m + 1), (Xz i c ^ (A ((topOdd X j i, true), c) % P i) *
      Xy i c ^ (A ((topOdd X j i, false), c) % P i))) * _ * _ * _ =
    (∏ i, ∏ c : Fin (X.m + 1), (Xz i c ^ (A ((topOdd X j i, true), c) % P i) *
      Xy i c ^ (A ((topOdd X j i, false), c) % P i))) * _ * _
  ring

end A

end Formalism.MainNotions.ColumnSystems.Pf
end
end

