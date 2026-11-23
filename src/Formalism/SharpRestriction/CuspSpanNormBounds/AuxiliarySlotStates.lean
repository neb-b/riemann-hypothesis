module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.TopsChoicePartA

open Formalism.QuantumDeterminants

abbrev Mat (k0 r : ℕ) := Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ

abbrev Vec (k0 r : ℕ) := Fin (2 * r + (k0 + 1) + 1) → ℂ

structure Lev where
  k0 : ℕ
  r : ℕ
  z : Vec k0 r
  z' : Vec k0 r
  Wp : Type
  Wq : Type
  [nWp : NormedAddCommGroup Wp]
  [iWp : InnerProductSpace ℂ Wp]
  [fWp : FiniteDimensional ℂ Wp]
  [nWq : NormedAddCommGroup Wq]
  [iWq : InnerProductSpace ℂ Wq]
  [fWq : FiniteDimensional ℂ Wq]
  π : Mat k0 r → (Wp →L[ℂ] Wp)
  π' : Mat k0 r → (Wq →L[ℂ] Wq)
  μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ

attribute [instance] Lev.nWp Lev.iWp Lev.fWp Lev.nWq Lev.iWq Lev.fWq

namespace Lev

abbrev Hom (L : Lev) := L.Wq →L[ℂ] L.Wp

abbrev PF (L : Lev) := (Fin (L.r + 1) → ℂ) → L.Hom

abbrev POp (L : Lev) := Op (L.r + 1) L.Hom

abbrev GF (L : Lev) := Mat L.k0 L.r → L.Hom

def T (L : Lev) : ℝ := Tz (L.k0 + 1) L.r L.z
def T' (L : Lev) : ℝ := Tz (L.k0 + 1) L.r L.z'

def xv (L : Lev) : Vec L.k0 L.r := if h : 0 < L.r then bvec (eI (L.k0 + 1) L.r ⟨0, h⟩) else L.z
def xv' (L : Lev) : Vec L.k0 L.r := if h : 0 < L.r then bvec (eI (L.k0 + 1) L.r ⟨0, h⟩) else L.z'

def flat (L : Lev) (v : Vec L.k0 L.r) : Vec L.k0 L.r := fun j => herm (Hpk (L.k0 + 1) L.r) (bvec j) v

def yv (L : Lev) (g : Mat L.k0 L.r) : Vec L.k0 L.r := g⁻¹ *ᵥ L.xv

def QQ (L : Lev) (Y : ℂ) : Fin 2 → Fin 2 → (L.GF → L.GF) :=
  QQop (m := 2 * L.r + L.k0) (EabH (Hpk (L.k0 + 1) L.r)) (((2 * L.r + L.k0 + 1 : ℕ) : ℂ) / 2) Y
    (fun g => L.yv g) (fun g => L.flat (L.yv g)) L.xv' (L.flat L.xv')

def KKop (L : Lev) : Set L.GF :=
  EqF (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' ∩ {J | ∃ ε : ℝ, 0 < ε ∧ J ∈ KKeps (L.k0 + 1) L.r L.z L.z' ε}

def B (L : Lev) (J : L.GF) : L.PF := Btr (L.k0 + 1) L.r L.z L.z' L.μsec J

def Rad (L : Lev) (Θ : L.GF → L.GF) (R : L.POp) : Prop :=
  HasRadialPart (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' L.μsec L.KKop Θ R

def BD (L : Lev) : Set (Fin (L.r + 1) → ℂ) := BDom (L.k0 + 1) L.r L.z L.z'

def IsRadQQ (L : Lev) (R : ℂ → Matrix (Fin 2) (Fin 2) L.POp) : Prop :=
  ∀ (Y : ℂ) (a b : Fin 2), L.Rad (L.QQ Y a b) (R Y a b) ∧ LocalOn L.BD (R Y a b) ∧
    ∀ U : Set (Fin (L.r + 1) → ℂ), IsOpen U → U ⊆ L.BD → LocalOn U (R Y a b)

end Lev

section OpMat

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def idOp : Op m E := fun f => f

def zeroOp : Op m E := fun _ => 0

def omMul {ι κ ν : Type*} [Fintype κ] (M : Matrix ι κ (Op m E)) (N : Matrix κ ν (Op m E)) :
    Matrix ι ν (Op m E) :=
  fun a b f => ∑ c, M a c (N c b f)

def omApply {ι κ : Type*} [Fintype κ] (M : Matrix ι κ (Op m E)) (x : κ → (Fin m → ℂ) → E) :
    ι → (Fin m → ℂ) → E :=
  fun a => ∑ b, M a b (x b)

def oneOM {ι : Type*} [DecidableEq ι] : Matrix ι ι (Op m E) := fun a b => if a = b then idOp else zeroOp

end OpMat

def Pflip : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ik jl => if ik.1 = jl.2 ∧ ik.2 = jl.1 then 1 else 0

def Rh (D : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ik jl => ((if ik = jl then D else 0) - Pflip ik jl) / (D - 1)

abbrev Letter := Bool × ℝ

abbrev Word := List Letter

abbrev AuxiliarySlotStates (n : ℕ) := Fin n → Fin 2

def e1s (n : ℕ) : AuxiliarySlotStates n := fun _ => 0

structure Mod (m : ℕ) (E : Type*) (n : ℕ) where
  RR : Matrix (AuxiliarySlotStates n) (AuxiliarySlotStates n) (Op m E)
  TT : ℂ → Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E)
  q : ℂ → ℂ

section Words

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def modStart (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op m E)) (q : ℂ → ℂ) : Mod m E 0 where
  RR := oneOM
  TT := fun Y a b => Q Y a.1 b.1
  q := q

def stepPlus {n : ℕ} (Ya : ℝ) (M : Mod m E n) : Mod m E (n + 1) where
  RR := fun α β f => ∑ γ : AuxiliarySlotStates n, M.RR (Fin.tail α) γ (M.TT (Ya : ℂ) (α 0, γ) (β 0, Fin.tail β) f)
  TT := fun Y a b f => ∑ ρ : Fin 2,
    M.TT Y (a.1, Fin.tail a.2) (ρ, Fin.tail b.2) (Rh (Y - (Ya : ℂ)) (ρ, a.2 0) (b.1, b.2 0) • f)
  q := fun Y => M.q Y * ((Y - (Ya : ℂ)) + 1) / (Y - (Ya : ℂ))

def stepMinus {n : ℕ} (Yb : ℝ) (M : Mod m E n) : Mod m E (n + 1) where
  RR := fun α β f => ∑ γ : AuxiliarySlotStates n, M.RR (Fin.tail α) γ (M.TT (Yb : ℂ) (β 0, γ) (α 0, Fin.tail β) f)
  TT := fun Y a b f => ∑ ρ : Fin 2,
    Rh ((Yb : ℂ) - Y) (a.1, b.2 0) (ρ, a.2 0) • M.TT Y (ρ, Fin.tail a.2) (b.1, Fin.tail b.2) f
  q := fun Y => M.q Y * ((Yb : ℂ) - Y) / (((Yb : ℂ) - Y) - 1)

def step {n : ℕ} (l : Letter) (M : Mod m E n) : Mod m E (n + 1) :=
  if l.1 then stepPlus l.2 M else stepMinus l.2 M

def wordMod (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op m E)) (q : ℂ → ℂ) : (w : Word) → Mod m E w.length
  | [] => modStart Q q
  | l :: w => step l (wordMod Q q w)

end Words

def Admissible (I : Set ℝ) (w : Word) : Prop :=
  (∀ l ∈ w, l.2 ∈ I) ∧ w.Pairwise (fun a b => 2 < |a.2 - b.2|)

def Interlace {k0 : ℕ} (u : Fin (k0 + 1) → ℝ) (ρ : Fin k0 → ℝ) : Prop :=
  ∀ j : Fin k0, ρ j < u j.castSucc ∧ u j.succ < ρ j

section Vectors

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def vLetter (c : Fin m) (l : Letter) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  if l.1 then Tmat c (l.2 : ℂ) else TmatV c (l.2 : ℂ)

def bT (c : Fin m) : (w : Word) → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op m E)
  | [] => oneOM
  | l :: w => fun α β f => vLetter c l (α 0) (β 0) (bT c w (Fin.tail α) (Fin.tail β) f)

end Vectors

namespace Lev

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def betaB (L : Lev) (φ ψ : L.PF) : ℂ :=
  ∫ x : Fin (L.r + 1) → ℂ, (((∏ a : Fin L.r, Complex.normSq (cOf x a))⁻¹ : ℝ) : ℂ) *
    Formalism.MainNotions.S.hsInner (φ x) (ψ x)

def form (L : Lev) {ι : Type*} [Fintype ι] (M : Matrix ι ι L.POp) (x y : ι → L.PF) : ℂ :=
  ∑ a, L.betaB (omApply M x a) (y a)

def matNorm {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖

def Eword (L : Lev) (w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1))) (F : L.GF) :
    L.GF :=
  w.foldr (fun ab f => EabH (Hpk (L.k0 + 1) L.r) ab.1 ab.2 f) F

end Lev

section Waves

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end Waves

namespace Lev

def UUset (L : Lev) (g : Mat L.k0 L.r) : Set (Mat L.k0 L.r) :=
  {h | h ∈ UWset (L.k0 + 1) L.r L.z' ∧ h *ᵥ (g⁻¹ *ᵥ L.z) = g⁻¹ *ᵥ L.z}

def blockU (L : Lev) (h : Matrix (Fin L.k0) (Fin L.k0) ℂ) : Mat L.k0 L.r :=
  fun i j =>
    if hi : L.r ≤ i.val ∧ i.val < L.r + L.k0 then
      (if hj : L.r ≤ j.val ∧ j.val < L.r + L.k0 then h ⟨i.val - L.r, by omega⟩ ⟨j.val - L.r, by omega⟩ else 0)
    else (if i = j then 1 else 0)

def IsFrameU (L : Lev) (g f : Mat L.k0 L.r) : Prop :=
  f ∈ UH (Hpk (L.k0 + 1) L.r) ∧
    (∀ a : Fin L.r, f *ᵥ bvec (eI (L.k0 + 1) L.r a) = bvec (eI (L.k0 + 1) L.r a) ∧
      f *ᵥ bvec (esI (L.k0 + 1) L.r a) = bvec (esI (L.k0 + 1) L.r a)) ∧
    ∀ j : Fin L.k0,
      herm (Hpk (L.k0 + 1) L.r) (f *ᵥ bvec (wI (L.k0 + 1) L.r j.castSucc.castSucc)) (g⁻¹ *ᵥ L.z) = 0 ∧
      herm (Hpk (L.k0 + 1) L.r) (f *ᵥ bvec (wI (L.k0 + 1) L.r j.castSucc.castSucc)) L.z' = 0

open Classical in
def frameU (L : Lev) (g : Mat L.k0 L.r) : Mat L.k0 L.r :=
  if h : ∃ f, L.IsFrameU g f then Classical.choose h else 1

def isoSub (L : Lev) (g : Mat L.k0 L.r) (ρ : Fin L.k0 → ℝ) : Submodule ℂ L.Wq :=
  sSup {S | Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos L.k0)
    (fun h => L.π' (L.frameU g * L.blockU h * (L.frameU g)⁻¹)) (lowK (Formalism.MainNotions.S.allPos L.k0) ρ) S}

def HomU (L : Lev) (g : Mat L.k0 L.r) : Set L.Hom :=
  {T | ∀ h ∈ L.UUset g, (L.π (g * h * g⁻¹)).comp T = T.comp (L.π' h)}

def lineSet (L : Lev) (g : Mat L.k0 L.r) (ρ : Fin L.k0 → ℝ) : Set L.Hom :=
  {T | T ∈ L.HomU g ∧ ∀ v ∈ (L.isoSub g ρ)ᗮ, T v = 0}

def IsHSProj (L : Lev) (P : L.Hom →L[ℂ] L.Hom) (S : Set L.Hom) : Prop :=
  P.comp P = P ∧ (∀ A B, Formalism.MainNotions.S.hsInner (P A) B = Formalism.MainNotions.S.hsInner A (P B)) ∧
    (∀ A, P A ∈ S) ∧ ∀ A ∈ S, P A = A

open Classical in
def lineP (L : Lev) (g : Mat L.k0 L.r) (ρ : Fin L.k0 → ℝ) : L.Hom →L[ℂ] L.Hom :=
  if h : ∃ P, L.IsHSProj P (L.lineSet g ρ) then Classical.choose h else 0

def pt (L : Lev) (x : Fin (L.r + 1) → ℂ) : Mat L.k0 L.r := bigCell (L.k0 + 1) L.r (cOf x) (L.μsec (zOf x))

def GGx (L : Lev) (x : Fin (L.r + 1) → ℂ) : ℝ := Complex.normSq (zOf x) - L.T * L.T'

end Lev

noncomputable def sCut {k0 : ℕ} (u u' : Fin (k0 + 1) → ℝ) (I : Set ℝ) : ℝ := by
  classical
  exact if h : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ ρ : Fin k0 → ℝ, Interlace u ρ → Interlace u' ρ →
      ∀ Y ∈ I, 0 < s * (xPoly ρ (Y : ℂ)).re then Classical.choose h else 1

def Lev.down (Lt : Lev) (i r' : ℕ) (h : i + r' = Lt.r) : Lev where
  k0 := Lt.k0
  r := r'
  z := fun p => Lt.z ⟨p.val + i, by omega⟩
  z' := fun p => Lt.z' ⟨p.val + i, by omega⟩
  Wp := Lt.Wp
  Wq := Lt.Wq
  π := fun g => Lt.π (fun p q => ιLev (Lt.k0 + 1) i r' g (Fin.cast (by omega) p) (Fin.cast (by omega) q))
  π' := fun g => Lt.π' (fun p q => ιLev (Lt.k0 + 1) i r' g (Fin.cast (by omega) p) (Fin.cast (by omega) q))
  μsec := Lt.μsec

section Prods

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Tprod (Y : ℂ) : (i : ℕ) → i ≤ m → Matrix (Fin 2) (Fin 2) (Op (m + 1) E)
  | 0, _ => oneOM
  | i + 1, h => omMul (Tmat (⟨i, by omega⟩ : Fin (m + 1)) Y) (Tprod Y i (by omega))

def bTprod (w : Word) : (i : ℕ) → i ≤ m → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op (m + 1) E)
  | 0, _ => oneOM
  | i + 1, h => omMul (bT (⟨i, by omega⟩ : Fin (m + 1)) w) (bTprod w i (by omega))

def uw (w : Word) (i : ℕ) (h : i ≤ m) : AuxiliarySlotStates w.length → Op (m + 1) E :=
  fun β => bTprod w i h β (e1s _)

end Prods

namespace Lev

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def dw (L : Lev) {n : ℕ} (N : ℕ) (c : AuxiliarySlotStates n → (Fin L.k0 → ℝ) → ℝ) (α : AuxiliarySlotStates n)
    (p : Fin (L.r + 1) → ℂ) (A : L.Hom) : L.Hom :=
  ((Complex.normSq (zOf p) / L.GGx p) ^ N : ℝ) • ∑ᶠ ρ : Fin L.k0 → ℝ, ((c α ρ : ℝ) : ℂ) • L.lineP (L.pt p) ρ A

def act (L : Lev) (h n h' n' : Mat L.k0 L.r) (F : L.GF) : L.GF := fun g =>
  (psi (L.k0 + 1) L.r L.z cStd n * star (psi (L.k0 + 1) L.r L.z' cStd n')) •
    ((L.π h).comp ((F (h⁻¹ * n⁻¹ * g * n' * h')).comp (L.π' h'⁻¹)))

def IsInv (L : Lev) (Θ : L.GF → L.GF) : Prop :=
  ∀ h ∈ UWset (L.k0 + 1) L.r L.z, ∀ n ∈ Nset (L.k0 + 1) L.r, ∀ h' ∈ UWset (L.k0 + 1) L.r L.z',
    ∀ n' ∈ Nset (L.k0 + 1) L.r, ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F →
      ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), Θ (L.act h n h' n' F) g = L.act h n h' n' (Θ F) g

def EwordV (L : Lev) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1))) (a : Mat L.k0 L.r → V) :
    Mat L.k0 L.r → V :=
  w.foldr (fun ab f => EabH (Hpk (L.k0 + 1) L.r) ab.1 ab.2 f) a

def wmod (L : Lev) (R : ℂ → Matrix (Fin 2) (Fin 2) L.POp) (sg : ℝ) (u u' : Fin (L.k0 + 1) → ℝ)
    (w : Word) : Mod (L.r + 1) L.Hom w.length :=
  wordMod (fun Y a b => fun φ => ((sg : ℝ) : ℂ) • R Y a b φ) (fun Y => qPoly L.T L.T' u u' Y) w

end Lev

namespace Lev

end Lev

section Deg

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Deg

end Formalism.MainNotions.S.TopsChoicePartA
