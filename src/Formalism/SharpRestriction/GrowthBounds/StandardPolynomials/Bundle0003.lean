module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.PreSys
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

structure PreSys (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O) (mu : ℝ) (β : GlobalTheory X)
    (L : LvDat C0 CE1 CE2 mu X β) (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) (Std : MonH X) where
  ιC : Fin (numSeg X.TT) → Type
  finC : ∀ j, Fintype (ιC j)
  Kc : ∀ j, ιC j → MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)
  dK : ∀ j, ιC j → Fin (2 * segS X.TT j + 1) → ℕ
  pl : ∀ j, ιC j → MonH X
  fC : ∀ j, ιC j → RHH O X
  oC : ∀ j, ιC j → ℕ
  dgC : ∀ j, ιC j → X.TT × Bool → ℕ
  fH : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → RHH O X
  oH : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ
  dgH : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → X.TT × Bool → ℕ
  ιM : Type
  finM : Fintype ιM
  multM : ιM → ℕ
  fM : ιM → RHH O X
  aM : ιM → MonH X
  oM : ιM → ℕ
  dgM : ιM → X.TT × Bool → ℕ
  fR : RHH O X
  R : MonH X
  oR : ℕ
  dR : X.TT × Bool → ℕ

  KInt : ∀ j a, Kc j a ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)
  KPol : ∀ j a, Kc j a ∈ Pol (KK O) X.m (dK j a)
  digit_le_one : ∀ j a i, dK j a i ≤ 1
  dKsum : ∀ j i, ∑ a, dK j a i = (L.LL j).deg i
  Kprod : ∀ j, ∏ a, Kc j a = G j

  facC : ∀ j a, IsFac w (fC j a) (oC j a)
    (monomial (pl j a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc j a)))
  homC : ∀ j a, HomW (ndHom X) (oC j a)
    (monomial (pl j a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc j a)))
  liftC : ∀ j a, lift1 X O w (fC j a) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC j a)
  polC : ∀ j a, monomial (pl j a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc j a)) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC j a)
  plQ : ∀ j a l, multideg (pl j a) l ≤ X.p ^ X.G'
  plY : ∀ j a j', multideg (pl j a) (topEnd X j', false) = 0

  facH : ∀ j i, IsFac w (fH j i) (oH j i) (ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i))
  homH : ∀ j i, HomW (ndHom X) (oH j i) (ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i))
  liftH : ∀ j i, lift1 X O w (fH j i) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgH j i)
  polH : ∀ j i, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgH j i)

  facM : ∀ a, IsFac w (fM a) (oM a) (monomial (aM a) 1)
  homM : ∀ a, ndM X (aM a) = oM a
  liftM : ∀ a, lift1 X O w (fM a) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgM a)
  polM : ∀ a l, multideg (aM a) l = dgM a l

  rigA : InA fR
  rigLift : lift1 X O w fR =
    (w ^ oR) • ((∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) * monomial R 1)
  rigHom : HomW (ndHom X) oR
    ((∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) * monomial R 1)
  rigPol : (∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) * monomial R 1 ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dR
  rigInt : InA ((∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) *
    (monomial R 1 : RHH O X))

  dgCQ : ∀ j a l, dgC j a l ≤ X.p ^ X.G'
  dgHQ : ∀ j i l, dgH j i l ≤ X.p ^ X.G'
  dgMQ : ∀ a l, dgM a l ≤ X.p ^ X.G'
  dgCY : ∀ j a j', dgC j a (topEnd X j', false) = 0
  dgHY : ∀ j i j', dgH j i (topEnd X j', false) = 0
  dgMY : ∀ a j', dgM a (topEnd X j', false) = 0
  degEq : ∀ l, dR l + ((∑ j, ∑ a, dgC j a l) + ((∑ j, ∑ i, L.lv j i * dgH j i l) + ∑ a, multM a * dgM a l)) =
    hhDegs X.TT X.aT X.bT l
  stdEq : Std = R + ((∑ j, ∑ a, pl j a) + ∑ a, multM a • aM a)

  clean : ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
    ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 1 →
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g'
      (fR * ((∏ j, ∏ a, fC j a) * ((∏ j, ∏ i, fH j i ^ L.lv j i) * ∏ a, fM a ^ multM a)))
      (ordFam C0 CE1 CE2 X β + X.c)
  total : fR * ((∏ j, ∏ a, fC j a) * ((∏ j, ∏ i, fH j i ^ L.lv j i) * ∏ a, fM a ^ multM a)) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT)
  ordEq : oR + ((∑ j, ∑ a, oC j a) + ((∑ j, ∑ i, L.lv j i * oH j i) + ∑ a, multM a * oM a)) = ordFam C0 CE1 CE2 X β

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TgProdPlaces
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev TgPlace (X : Loc) := Σ j : Fin (numSeg X.TT), Option (Fin (segS X.TT j))

def tgTop (X : Loc) : TgPlace X → X.TT
  | ⟨j, none⟩ => topEnd X j
  | ⟨j, some i⟩ => topOdd X j i

theorem tg_end_ne_odd (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : topEnd X j ≠ topOdd X j i := by
  intro h
  have e : segNext X.TT j = segPos X.TT j i := congrArg Subtype.val h
  exact (pos_mem X.TT j i).2 (e ▸ (next_mem X.TT j).2)

theorem tgTop_mem (X : Loc) (pl : TgPlace X) (b : Bool) (c : Fin (X.m + 1)) :
    ((tgTop X pl, b), c) ∈ segVars X pl.1 := by
  obtain ⟨j, a⟩ := pl
  cases a with
  | none => exact Or.inl rfl
  | some i => exact Or.inr ⟨i, rfl⟩

theorem tgTop_inj (X : Loc) : Function.Injective (tgTop X) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  have hj : j = j' := by
    by_contra hne
    have h1 := tgTop_mem X ⟨j, a⟩ true 0
    have h2 := tgTop_mem X ⟨j', a'⟩ true 0
    rw [← h] at h2
    exact Set.disjoint_left.1 (segVars_disj X j j' hne) h1 h2
  subst hj
  cases a with
  | none =>
    cases a' with
    | none => rfl
    | some i => exact absurd h (tg_end_ne_odd X j i)
  | some i =>
    cases a' with
    | none => exact absurd h.symm (tg_end_ne_odd X j i)
    | some i' => rw [topOdd_inj X j h]

theorem tgTop_surj (X : Loc) (h2 : 2 ≤ numSeg X.TT) : Function.Surjective (tgTop X) := by
  rintro ⟨t, ht⟩
  by_cases he : Even t.val
  · obtain ⟨j0, hj0⟩ := List.mem_iff_get.mp ((ev_mem X.TT t).mpr ⟨ht, he⟩)
    obtain ⟨j, hj⟩ := (rot_bij (numSeg X.TT)).2 j0
    refine ⟨⟨j, none⟩, Subtype.ext ?_⟩
    show segNext X.TT j = t
    rw [next_eq, hj]
    exact hj0
  · obtain ⟨j, hj⟩ := odd_covered X.TT h2 t ht he
    have hs := Finset.mem_filter.mp hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (mem_dists.mpr ⟨t, hs, rfl⟩)
    refine ⟨⟨j, some i⟩, Subtype.ext ?_⟩
    show segPos X.TT j i = t
    unfold segPos
    rw [hi, posAdd_cdist]

theorem tgTop_bij (X : Loc) (h2 : 2 ≤ numSeg X.TT) : Function.Bijective (tgTop X) :=
  ⟨tgTop_inj X, tgTop_surj X h2⟩

theorem tg_prod_places {M : Type} [CommMonoid M] (X : Loc) (h2 : 2 ≤ numSeg X.TT) (f : X.TT → M) :
    ∏ t, f t = ∏ j, (f (topEnd X j) * ∏ i, f (topOdd X j i)) := by
  rw [← (tgTop_bij X h2).prod_comp f, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Fintype.prod_option]
  rfl

theorem tg_mono_split (O : Type) [CommRing O] [IsDomain O] (X : Loc) (h2 : 2 ≤ numSeg X.TT) (A : MonH X) :
    (monomial A (1 : KK O) : RHH O X) = ∏ j, segMon O X j A := by
  rw [MvPolynomial.monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
    Fintype.prod_prod_type, tg_prod_places X h2]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold segMon
  simp only [Fintype.prod_bool, Finset.prod_mul_distrib]
  ring

theorem tg_prod_uTop {M : Type} [CommMonoid M] {s : ℕ} (S : SegData s) (g : Fin s → M) :
    ∏ l : Fin S.t, g (uTop S l) = ∏ i : Fin s, if S.sigma ≤ i.val then g i else 1 := by
  rw [← Finset.prod_filter]
  refine Finset.prod_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro l _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
  · intro l _ l' _ h
    have : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  · intro i hi
    have hi' : S.sigma ≤ i.val := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    refine ⟨⟨i.val - S.sigma, by unfold SegData.t; have := i.2; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    apply Fin.ext
    show S.sigma + (i.val - S.sigma) = i.val
    omega

end Formalism.MainNotions.ColumnSystems.Pf
end
end

