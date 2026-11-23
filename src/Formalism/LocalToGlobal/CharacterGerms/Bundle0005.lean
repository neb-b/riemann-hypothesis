module

public import Formalism.LocalToGlobal.CharacterGerms.Interface
public import Formalism.FrobeniusBaseCase.Statement

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
section
noncomputable section
open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

def blockBd (l n m i y : ℕ) : ℝ :=
  if y = 0 then 0 else bdP l i n n y + ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)

def chBd (l n m u : ℕ) : ℝ := (u : ℝ) * (n * gam l + m / ((l : ℝ) - 1))

def Windows (S : ℕ) (G : Set ℕ) : Prop := 0 ∈ G ∧ ∀ Y0 : ℕ, ∃ y ∈ G, Y0 ≤ y ∧ y < Y0 + S

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def _root_.Formalism.L2.FormalSeriesBounds.RowData.rkF (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => (X.G g).ty (Sum.inl c) = a).card

structure Flag (X : RowData C V d I J) where
  en : ∀ g a, Fin (X.rkF g a) → I g
  en_inj : ∀ g a, Function.Injective (en g a)
  en_ty : ∀ g a c, (X.G g).ty (Sum.inl (en g a c)) = a

def Flag.letter {X : RowData C V d I J} (F : Flag X) (g : Fin 2) (a : ZMod d) {N : ℕ}
    (x : Fin N × Fin (X.rkF g a)) : Fin N × WV I := (x.1, ⟨g, F.en g a x.2⟩)

def bg (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

inductive GlobalTheory (d : ℕ) where

  | bi (g : Fin 2) (a : ZMod d) (i y : ℕ)

  | ch (g : Fin 2) (a : ZMod d) (u : ℕ)

  | mon (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ)

namespace GlobalTheory

def what₂ (n : ℕ) : GlobalTheory d → ℕ
  | bi _ _ _ _ => n
  | ch _ _ _ => n
  | mon _ _ N => N

variable (X : RowData C V d I J) (F : Flag X)

def poly : (b : GlobalTheory d) → MvPolynomial (Fin (b.what₂ X.n) × WV I) C
  | bi g a i y =>
      MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) X.n) ^ (V.l ^ i * y) *
        MvPolynomial.rename (F.letter (1 - g) (a + (i : ZMod d)))
          (minorK C X.n (X.rkF (1 - g) (a + (i : ZMod d))) X.n) ^ y
  | ch g a u => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) X.n) ^ u
  | mon g e N => ∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rkF g a) (e a))

def kind (n : ℕ) : (b : GlobalTheory d) → Fin (b.what₂ n) → Option (Fin 2 × ZMod d × ZMod d)
  | bi g a i _ => fun _ => some (g, a, a + (i : ZMod d))
  | ch _ _ _ => fun _ => none
  | mon _ _ _ => fun _ => none

def wt : GlobalTheory d → Fin 2 → ZMod d → ℕ → ℕ
  | bi g a i y => fun g' a' k =>
      (if g' = g ∧ a' = a ∧ k = X.n then V.l ^ i * y else 0) +
        (if g' = 1 - g ∧ a' = a + (i : ZMod d) ∧ k = X.n then y else 0)
  | ch g a u => fun g' a' k => if g' = g ∧ a' = a ∧ k = X.n then u else 0
  | mon g e N => fun g' a' k => if g' = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g a') then e a' k else 0

def Attains (b : GlobalTheory d) (c : ℝ) : Prop :=
  ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
    ∃ gr : Fin (b.what₂ X.n) → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
      V.v (ValOf X.hL (b.poly X F) (b.kind X.n) gr) ≤ ((c : ℝ) : WithTop ℝ)

end GlobalTheory

def BiSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), X.Alt → 5 ≤ V.l → 1 ≤ X.n →
    ∀ g a, X.big g a → ∀ i : ℕ, Odd i → i < d →
      Windows (S0 V.l i X.n) {y | (GlobalTheory.bi g a i y).Attains X F (blockBd V.l X.n X.m i y)}

def CHSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), ∀ g a, X.big g a → ∀ u : ℕ,
      (X.Alt → (GlobalTheory.ch g a u).Attains X F (chBd V.l X.n X.m u)) ∧
      ((∀ a, X.big g a) → (GlobalTheory.ch g a u).Attains X F ((u : ℝ) * (X.m / ((V.l : ℝ) - 1))))

def monDegAll (X : RowData C V d I J) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ a : ZMod d, monDeg N (X.rkF g a) (e a)

def MONSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (g : Fin 2) (e : ZMod d → ℕ → ℕ)
    (N : ℕ),
      (GlobalTheory.mon g e N).Attains X F ((monDegAll X g e N : ℝ) / ((V.l : ℝ) - 1)) ∧
      ((∀ a ρ, monAl N (X.rkF g a) (e a) ρ < V.l) → (GlobalTheory.mon g e N).Attains X F 0)

def ValBlocks {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o))
    (Z : Finset Orb) (nW : ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ),
    (∀ o ∈ Z, ∀ p ∈ L o, p.1.Attains (X o) (F o) p.2) →
    (∑ o ∈ Z, ((L o).map fun p => p.1.what₂ (X o).n).sum) ≤ nW →
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun p => p.1.wt (X o) g a k).sum = ga o g a k) →
    ν ≤ ∑ o ∈ Z, ((L o).map Prod.snd).sum

def restDeg (bgr : ZMod d → Fin 2) (n : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ g : Fin 2, ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, if g = bgr a ∧ k = n then 0 else k * ga g a k

structure WtHyp {Orb : Type} (k K : ℕ) (Z : Finset Orb) (bgr : ZMod d → Fin 2)
    (rk : Orb → Fin 2 → ZMod d → ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (Wa ea : Orb → ZMod d → ℕ)
    (rest : ℝ) : Prop where
  supp : ∀ z ∈ Z, ∀ g a k', ga z g a k' ≠ 0 → 1 ≤ k' ∧ k' ≤ rk z g a
  main : ∀ z ∈ Z, ∀ a, ga z (bgr a) a (k - 1) = Wa z a + ea z a
  rest_eq : rest = ∑ z ∈ Z, ((restDeg bgr (k - 1) (ga z) K : ℝ) +
    ∑ a, ((k : ℝ) - 1) * ((ea z a : ℕ) : ℝ))

def ValBlocksC {C : Type} [Field C] {V : VF C} {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
    [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V 2 (I o) (J o))
    (F : ∀ o, Flag (X o)) (nW : ℕ) (gaC : Orb → ZMod 2 → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (GlobalTheory 2 × ℝ),
    (∀ o, ∀ p ∈ L o, p.1.Attains (X o) (F o) p.2) →
    (∀ o, ∀ p ∈ L o, ∀ g e N, p.1 = GlobalTheory.mon g e N → ∃ s : ZMod 2, ∀ a k, a ≠ s → e a k = 0) →
    2 * (∑ o, ((L o).map fun p => p.1.what₂ (X o).n).sum) ≤ nW →
    (∀ o s k, ((L o).map fun p => p.1.wt (X o) 0 s k + p.1.wt (X o) 1 (s + 1) k).sum = gaC o s k) →
    ν ≤ ∑ o, ((L o).map Prod.snd).sum

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

section OneGroup

variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

def LatticeInclusionFormsInjective (X : Cart V d I J) : Prop :=
  ∀ (S : Sys X) (c : I) (i : ℕ) (n : I ⊕ J), V.Ge (-(i : ℝ)) (S.cur c i n)

def Eq16 (X : Cart V d I J) : Prop :=
  ∀ (a : ZMod d) (u : I → C) (x : ℕ → I ⊕ J → C), X.Good a u x → ∀ i : ℕ, 1 ≤ i →
      (∀ k, V.Ge (-((i : ℝ) - 1)) (x i (Sum.inl k))) ∧
        ∀ κ, V.Ge (-(max 1 ((i : ℝ) - 1))) (x i (Sum.inr κ))

def TExistsUnique (X : Cart V d I J) : Prop := ∀ S : Sys X, ∃! t : I → MvPowerSeries I C, S.IsT t

def SysExists (X : Cart V d I J) : Prop :=
  ∀ u : I → I → C, (∀ c x, V.Ge 0 (u c x)) → (∀ c x, X.ty (Sum.inl x) ≠ X.ty (Sum.inl c) → u c x = 0) →
    V.v (Matrix.of u).det = 0 → ∃ S : Sys X, S.tan = u

end OneGroup

section Rows

variable {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
  [∀ g, Fintype (J g)]

def toW (g : Fin 2) (u : I g → C) : WV I → C := fun w => if h : w.1 = g then u (h ▸ w.2) else 0

def hPullW {ι ι' : Type} [Fintype ι] [Fintype ι'] (H : MvPowerSeries (WV I) C)
    (e : ι → WV I → C) (e' : ι' → WV I → C) : MvPowerSeries (ι ⊕ ι') C :=
  MvPowerSeries.subst (fun w : WV I =>
    (∑ c : ι, e c w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
      ∑ b : ι', e' b w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)) H

def WtGe2 (V : VF C) (i : ℕ) (w : ℝ) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (h : MvPowerSeries (ι ⊕ ι') C) : Prop :=
  ∀ μ : ι ⊕ ι' →₀ ℕ, ((w : ℝ) : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ h) +
    ((((∑ c : ι, μ (Sum.inl c) : ℕ) : ℝ) * (r1 V.l i - del V.l i) +
      ((∑ b : ι', μ (Sum.inr b) : ℕ) : ℝ) * (r2 V.l - del V.l i) : ℝ) : WithTop ℝ)

def WtGe1 (V : VF C) (i : ℕ) (w : ℝ) {ι : Type} (h : MvPowerSeries ι C) : Prop :=
  ∀ μ : ι →₀ ℕ, ((w : ℝ) : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ h) +
    (((μ.degree : ℝ) * (r1 V.l i - del V.l i) : ℝ) : WithTop ℝ)

def mainM (V : VF C) (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (Φ : ι' → ι → C) :
    MvPowerSeries (ι ⊕ ι') C :=
  ((V.l : C) ^ expE V.l i)⁻¹ • ∑ b : ι', ∑ c : ι,
    Φ b c • (MvPowerSeries.X (Sum.inl c) ^ (V.l ^ i) * MvPowerSeries.X (Sum.inr b))

def hRows (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) : MvPowerSeries (PVar n0) C :=
  ∑ ρ : Fin n0, MvPowerSeries.subst
    (Sum.elim (fun c => (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar n0) C))
      (fun b => MvPowerSeries.X (Sum.inr (ρ, b)))) H

namespace RowData

variable (X : RowData C V d I J)

def SatIn (g : Fin 2) (a : ZMod d) {N : ℕ} (u : Fin N → I g → C) : Prop :=
  IsSat V u ∧ ∀ c x, (X.G g).ty (Sum.inl x) ≠ a → u c x = 0

def hM (g : Fin 2) (a : ZMod d) (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) : MvPowerSeries (ι ⊕ ι') C :=
  hPullW (X.hL g a (a + (i : ZMod d))) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))

def MConcl (g : Fin 2) (a : ZMod d) (i : ℕ) (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C)
    (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C) :
    Prop :=
  (X.n ≤ n0 + (i + 1) * X.j' + X.j ∧ n0 ≤ X.n) ∧
  IsSat V e ∧
  (∃ A : Fin n0 → Fin X.n → C, (∀ c b, V.Ge 0 (A c b)) ∧ ∀ c x, e c x = ∑ b, A c b * U b x) ∧
  (∃ Y : Matrix (Fin X.n) (Fin X.n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧
    ∀ b x, v' b x = ∑ b', Y b b' * U' b' x) ∧
  (∀ b c, V.Ge 0 (Φ b c)) ∧
  (∀ (b : Fin X.n) (c : Fin n0), b.val < n0 → Φ b c = if b.val = c.val then -1 else 0) ∧
  WtGe2 V i (1 / ((V.l : ℝ) - 1)) (X.hM g a i e v' - mainM V i Φ) ∧
  (∀ μ : Fin n0 ⊕ Fin X.n →₀ ℕ, (∀ b, μ (Sum.inr b) = 0) →
    MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0)

def CurveSystemVanishing (g : Fin 2) (a : ZMod d) (i : ℕ) (n0 : ℕ) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C) : Prop :=
  ∃ (S : Sys (X.G g)) (t : I g → MvPowerSeries (I g) C) (em : Fin n0 ↪ I g)
    (Φt : Fin n0 → J g → C),
    S.IsT t ∧ (∀ c, S.tan (em c) = e c) ∧ (∀ c x, S.al (em c) 1 x = 0) ∧
    (∀ c κ, V.Ge 0 (Φt c κ)) ∧
    (∀ b c, Φ b c = ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k) ∧
    ∀ κ : J g, (X.G g).ty (Sum.inr κ) = a + (i : ZMod d) →
      WtGe1 V i 0
        (MvPowerSeries.subst (fun x : I g =>
            ∑ c : Fin n0, e c x • (MvPowerSeries.X c : MvPowerSeries (Fin n0) C)) (S.ze t κ) -
          ((V.l : C) ^ expE V.l i)⁻¹ • ∑ c : Fin n0,
            Φt c κ • (MvPowerSeries.X c : MvPowerSeries (Fin n0) C) ^ (V.l ^ i))

def MPlusConcl (g : Fin 2) (a : ZMod d) (n0 : ℕ) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C) : Prop :=
  ∀ μ : Fin n0 ⊕ Fin X.n →₀ ℕ, (∑ c, μ (Sum.inl c)) < V.l ^ 2 → (∑ b, μ (Sum.inr b)) < V.l →
    V.Ge 0 (MvPowerSeries.coeff μ (X.hM g a 1 e v' - mainM V 1 Φ))

def LemmaM : Prop :=
  X.Alt → 5 ≤ V.l → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ i : ℕ, Odd i → i < d →
    ∀ (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C), X.SatIn g a U →
      X.SatIn (1 - g) (a + (i : ZMod d)) U' →
      ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
        X.MConcl g a i U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a i n0 e v' Φ

def LemmaMPlus : Prop :=
  X.Alt → 5 ≤ V.l → 1 < d → ∀ (g : Fin 2) (a : ZMod d), X.big g a →
    ∀ (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C), X.SatIn g a U →
      X.SatIn (1 - g) (a + ((1 : ℕ) : ZMod d)) U' →
      ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
        X.MConcl g a 1 U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a 1 n0 e v' Φ ∧ X.MPlusConcl g a n0 e v' Φ

def hGood (g : Fin 2) (a : ZMod d) (i : ℕ) {n0 : ℕ} (hn : n0 ≤ X.n) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) : MvPowerSeries (Fin n0 ⊕ Fin n0) C :=
  X.hM g a i e (fun b : Fin n0 => v' (Fin.castLE hn b))

def restrictedCurveSystemSeries (g : Fin 2) (a : ZMod d) (i : ℕ) {n0 : ℕ} (hn : n0 ≤ X.n) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) : MvPowerSeries (PVar n0) C :=
  hRows n0 (X.hGood g a i hn e v' - mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0))

def MtoHM : Prop :=
  ∀ (g : Fin 2) (a : ZMod d) (i : ℕ) (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C)
    (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
    X.MConcl g a i U U' n0 e v' Φ → ∀ hn : n0 ≤ X.n,
      hRows n0 (X.hGood g a i hn e v') = hP C V.l i n0 (X.restrictedCurveSystemSeries g a i hn e v') ∧
      HM1 V.v V.l i n0 (X.restrictedCurveSystemSeries g a i hn e v') ∧ HM2 (X.restrictedCurveSystemSeries g a i hn e v') ∧
      (i = 1 → X.MPlusConcl g a n0 e v' Φ → HSeparatedRowSum V.v V.l n0 (X.restrictedCurveSystemSeries g a i hn e v'))

def AdaptedChainData : Prop :=
  X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ i : ℕ, Odd i → i < d →
    ∀ U : Fin X.n → I g → C, X.SatIn g a U →
      ∃ (S : Sys (X.G g)) (N1 : ℕ) (D : Formalism.BaseCaseIdentities.Data C (Fin N1) (I g)),
        D.v = V.v ∧ D.l = V.l ∧ D.i = i ∧
        (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x) ∧
        (∀ c, D.lev c < Formalism.BaseCaseIdentities.Kn i →
          (X.G g).ty (Sum.inl c) = a + ((2 * D.lev c : ℕ) : ZMod d)) ∧
        X.n ≤ N1 + (Formalism.BaseCaseIdentities.Kn i + 1) * X.j' ∧
        ∃ A : Fin N1 → Fin X.n → C, (∀ δ b, V.Ge 0 (A δ b)) ∧
          ∀ δ x, S.al (D.ι δ) 0 x = ∑ b, A δ b * U b x

end RowData

end Rows

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.MemVarsProdAll
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

abbrev Knd (d : ℕ) := Option (Fin 2 × ZMod d × ZMod d)

section Place

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}

def kindAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (kind : ∀ i, Fin (what₂ i) → Knd d) (ρ : Fin N) : Knd d :=
  if h : ∃ s, pl s = ρ then kind h.choose.1 h.choose.2 else none

def grAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C) (ρ : Fin N) :
    MvPowerSeries (WV I) C :=
  if h : ∃ s, pl s = ρ then gr h.choose.1 h.choose.2 else 1

def prodAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) :
    MvPolynomial (Fin N × WV I) C :=
  ∏ i, MvPolynomial.rename (fun x : Fin (what₂ i) × WV I => (pl ⟨i, x.1⟩, x.2)) (P i)

theorem kindAll_pl {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (kind : ∀ i, Fin (what₂ i) → Knd d) (s : Σ i : Fin K, Fin (what₂ i)) : kindAll pl kind (pl s) = kind s.1 s.2 := by
  unfold kindAll
  have hex : ∃ s', pl s' = pl s := ⟨s, rfl⟩
  rw [dite_eq_left hex]
  have hc : hex.choose = s := hpl hex.choose_spec
  rw [hc]

theorem mem_vars_prodAll {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} {P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C}
    {ρ : Fin N} {w : WV I} (h : (ρ, w) ∈ (prodAll pl P).vars) :
    ∃ s : Σ i : Fin K, Fin (what₂ i), pl s = ρ ∧ (s.2, w) ∈ (P s.1).vars := by
  unfold prodAll at h
  have h1 := MvPolynomial.vars_prod _ h
  rw [Finset.mem_biUnion] at h1
  obtain ⟨i, -, hi⟩ := h1
  have h2 := MvPolynomial.vars_rename _ _ hi
  rw [Finset.mem_image] at h2
  obtain ⟨⟨r, w'⟩, hw', heq⟩ := h2
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨⟨i, r⟩, rfl, hw'⟩

end Place

section Rows

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  {N K : ℕ} {what₂ : Fin K → ℕ}

private lemma forall_support_ne_zero_iff_forall_mem_vars {R0 : Type} [Field R0] {α β : Type} (Q : MvPolynomial (α × β) R0)
    (ρ : α) (T : β → Prop) :
    (∀ μ ∈ Q.support, ∀ w, μ (ρ, w) ≠ 0 → T w) ↔ (∀ w, (ρ, w) ∈ Q.vars → T w) := by
  constructor
  · intro H w hw
    obtain ⟨μ, hμ, hx⟩ := (MvPolynomial.mem_vars_iff_mem_support _).1 hw
    exact H μ hμ w (Finsupp.mem_support_iff.1 hx)
  · intro H μ hμ w hx
    exact H w ((MvPolynomial.mem_vars_iff_mem_support _).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hx⟩)

theorem rowsOK_iff (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop) {N : ℕ} (P : MvPolynomial (Fin N × WV I) C)
    (kind : Fin N → Knd d) : RowsOK G alt P kind ↔
      (∀ ρ g a a', kind ρ = some (g, a, a') → alt ∧ Odd (a' - a).val ∧
        ∀ w, (ρ, w) ∈ P.vars → OnLeafV G g a a' w) ∧
      (∀ ρ, kind ρ = none → ∃ g : Fin 2, ∀ w : WV I, (ρ, w) ∈ P.vars → w.1 = g) := by
  unfold RowsOK
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
    · obtain ⟨h1a, h1b, h1c⟩ := h1 ρ g a a' hk
      exact ⟨h1a, h1b, (forall_support_ne_zero_iff_forall_mem_vars P ρ (OnLeafV G g a a')).1 h1c⟩
    · obtain ⟨g, hg⟩ := h2 ρ hk
      exact ⟨g, (forall_support_ne_zero_iff_forall_mem_vars P ρ (fun w => w.1 = g)).1 hg⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
    · obtain ⟨h1a, h1b, h1c⟩ := h1 ρ g a a' hk
      exact ⟨h1a, h1b, (forall_support_ne_zero_iff_forall_mem_vars P ρ (OnLeafV G g a a')).2 h1c⟩
    · obtain ⟨g, hg⟩ := h2 ρ hk
      exact ⟨g, (forall_support_ne_zero_iff_forall_mem_vars P ρ (fun w => w.1 = g)).2 hg⟩

theorem rowsOK_prodAll (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop)
    {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) (kind : ∀ i, Fin (what₂ i) → Knd d)
    (h : ∀ i, RowsOK G alt (P i) (kind i)) : RowsOK G alt (prodAll pl P) (kindAll pl kind) := by
  rw [rowsOK_iff]
  have h' := fun i => (rowsOK_iff G alt (P i) (kind i)).1 (h i)
  refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
  · by_cases hex : ∃ s, pl s = ρ
    · obtain ⟨s, rfl⟩ := hex
      rw [kindAll_pl hpl] at hk
      obtain ⟨h1, h2, h3⟩ := (h' s.1).1 s.2 g a a' hk
      refine ⟨h1, h2, fun w hw => ?_⟩
      obtain ⟨s', hs', hw'⟩ := mem_vars_prodAll hw
      have hss := hpl hs'
      subst hss
      exact h3 w hw'
    · exfalso
      unfold kindAll at hk
      rw [dite_eq_right hex] at hk
      cases hk
  · by_cases hex : ∃ s, pl s = ρ
    · obtain ⟨s, rfl⟩ := hex
      rw [kindAll_pl hpl] at hk
      obtain ⟨g, hg⟩ := (h' s.1).2 s.2 hk
      refine ⟨g, fun w hw => ?_⟩
      obtain ⟨s', hs', hw'⟩ := mem_vars_prodAll hw
      have hss := hpl hs'
      subst hss
      exact hg w hw'
    · refine ⟨0, fun w hw => ?_⟩
      obtain ⟨s', hs', -⟩ := mem_vars_prodAll hw
      exact absurd ⟨s', hs'⟩ hex

end Rows

def JetProdSt : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)]
    (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (N K : ℕ) (what₂ : Fin K → ℕ)
    (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N), Function.Injective pl →
    ∀ (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) (kind : ∀ i, Fin (what₂ i) → Knd d)
      (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C),
      ValOf hL (prodAll pl P) (kindAll pl kind) (grAll pl gr) = ∏ i, ValOf hL (P i) (kind i) (gr i)

end Formalism.L2.FormalSeriesBounds
end
end

