module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def idem {a b : ℕ} {w : Pl E} (L : Subgroup (GLw a w × GLw b w)) : LF a b w :=
  (L : Set (GLw a w × GLw b w)).indicator fun _ => ((L.relIndex (K2 a b w) : ℕ) : ℂ)

structure LocData (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where

  T : Finset (Pl E)

  S₀ : Finset (Pl E)
  Bad : Finset (Pl E)
  μ : ∀ w : Pl E, (w.adicCompletion E)ˣ →* ℂˣ
  ϖ : ∀ w : Pl E, (w.adicCompletion E)ˣ

  c : Pl E → (Fin n → ℤ) →₀ ℂ

  K' : ∀ w : Pl E, Subgroup (GLw n w)
  X : ∀ w : Pl E, Finset (GLw n w)
  e : ∀ w : Pl E, GLw n w → ℂ

  L : ∀ (a : ℕ) (w : Pl E), Subgroup (GLw a w × GLw (n - a) w)
  fix : ∀ (a : ℕ) (w : Pl E), LF a (n - a) w

  b : ∀ w : Pl E, GLw n w
  KB : ∀ w : Pl E, Subgroup (UL n w)

namespace LocData

variable {n : ℕ} (d : LocData E n)

def P : Finset (Pl E) := d.T ∪ d.S₀

def idx (w : Pl E) : Finset (Finset (Fin (n / 2)) × GLw n w) :=
  if w ∈ d.T then Finset.univ ×ˢ {1} else if w ∈ d.S₀ then {∅} ×ˢ d.X w else {(∅, 1)}

abbrev kap (w : Pl E) : Type := d.idx w

def lev (a : ℕ) (w : Pl E) : Subgroup (GLw a w × GLw (n - a) w) :=
  if w ∈ d.T then I2 a (n - a) w else if w ∈ d.S₀ ∪ d.Bad then d.L a w else K2 a (n - a) w

def lev₂ (a : ℕ) (w : Pl E) : Subgroup (GLw a w × GLw (n - a) w) := if w ∈ d.S₀ ∪ d.Bad then d.L a w else K2 a (n - a) w

def sgn (a : ℕ) (w : Pl E) : ℂ := (d.μ w ((-1) ^ (a * (n - a))) : ℂˣ)

def admitted (n a : ℕ) (s : Finset (Fin (n / 2))) : Prop :=
  (s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2) ∧ (symIdx n (a % 2 = 1) s).card = a ∧
    (symIdx n ((n - a) % 2 = 1) sᶜ).card = n - a

def qT (a : ℕ) (w : Pl E) (s : Finset (Fin (n / 2))) : LF a (n - a) w := fun y =>
  if h : admitted n a s then (d.c w).sum fun x t => t * (-qh w) ^ (-vRes n a (lOf x) s) *
    (((I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) * dc2 w (d.ϖ w) (restr x _ h.2.1) (restr x _ h.2.2) y else 0

def mac (a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ) (x y : GLw n w) : LF a (n - a) w := fun m =>
  (d.sgn a w * ((d.X w).card : ℂ))⁻¹ * phiMu (Nat.add_sub_of_le ha) w (d.μ w) f x y m

def diag {a : ℕ} {w : Pl E} (f : d.kap w → LF a (n - a) w) (x y : d.kap w) : LF a (n - a) w := if x = y then f x else 0

def eL (a : ℕ) : LM d.kap a (n - a) :=
  ⟨fun w => d.diag fun _ => idem (d.lev a w), fun w => idem (d.lev a w), fun w => idem (d.lev₂ a w)⟩

def betaL (a : ℕ) (ha : a ≤ n) : LM d.kap a (n - a) :=
  ⟨fun w x y => if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else d.mac a ha w (d.e w) x.1.2 y.1.2,
    (d.eL a).s, (d.eL a).t⟩

def hc (a : ℕ) (ha : a ≤ n) (w : Pl E) (k : ℕ) : LF a (n - a) w :=
  (d.sgn a w)⁻¹ • RS.ctT (Nat.add_sub_of_le ha) w (d.μ w) (d.ϖ w : w.adicCompletion E) k

def hL (a : ℕ) (ha : a ≤ n) (w : Pl E) (k : ℕ) (intersection_update_fsHerm_neg_one : Bool) : LM d.kap a (n - a) :=
  ⟨(d.eL a).m, if intersection_update_fsHerm_neg_one then (d.eL a).s else Function.update (d.eL a).s w (d.hc a ha w k),
    if intersection_update_fsHerm_neg_one then Function.update (d.eL a).t w (d.hc a ha w k) else (d.eL a).t⟩

def fixL (a : ℕ) : LM d.kap a (n - a) :=
  ⟨fun w => d.diag fun _ => if w ∈ d.T then idem (d.lev a w) else d.sgn a w • idem (d.lev a w),
    fun w => if w ∈ d.Bad then d.fix a w else idem (d.lev a w), (d.eL a).t⟩

def one (w : Pl E) (x y : d.kap w) : ℂ := if x = y then 1 else 0

def B : Finset (Pl E) := d.T ∪ d.S₀ ∪ d.Bad

def KU (w : Pl E) : Subgroup (UL n w) :=
  if w ∈ d.T then iwU n w (d.b w) else if w ∈ d.S₀ then (d.K' w).subgroupOf (UL n w) else if w ∈ d.Bad then d.KB w else KL n w

def g₀ (w : Pl E) : UL n w → ℂ :=
  if w ∈ d.T then fun y => (d.c w).sum fun x t =>
    t * (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) * fU n w (d.b w) (d.ϖ w) (lOf x) y
  else if w ∈ d.S₀ then fun y => d.e w y.1 else U.lone (d.KU w)

def gU (m : ℕ) (w : Pl E) : UL n w → ℂ := U.lpow (d.KU w) (d.g₀ w) m

def hU (w : Pl E) (k : ℕ) : UL n w → ℂ := fun u => Tj ℂ n (Ov E w) (d.ϖ w : w.adicCompletion E) k u.1

structure Ok : Prop where
  disj : Disjoint d.T d.S₀ ∧ Disjoint d.T d.Bad ∧ Disjoint d.S₀ d.Bad
  unif : ∀ w, ordL (d.ϖ w : w.adicCompletion E) = 1
  cone : ∀ w ∈ d.T, (↑(d.c w).support : Set (Fin n → ℤ)) ⊆ coneGL n 2
  K' : ∀ w ∈ d.S₀, IsOpen (d.K' w : Set (GLw n w)) ∧ d.K' w ≤ GlobalTheory.LFun.KGL w (n := n) ∧
    (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ d.K' w, k * k' * k⁻¹ ∈ d.K' w) ∧ (∀ x ∈ d.X w, x ∈ GlobalTheory.LFun.KGL w (n := n)) ∧
    (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ d.X w, x⁻¹ * k ∈ d.K' w) ∧ IsHk (d.K' w) (d.e w)
  L : ∀ a ≤ n, ∀ w ∈ d.S₀ ∪ d.Bad, ∃ L₁ L₂, d.L a w = Subgroup.prod L₁ L₂ ∧ IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) L₁ ∧
    IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n := (n - a))) L₂
  LS : ∀ a (ha : a ≤ n), ∀ w ∈ d.S₀, ∀ m ∈ d.L a w, m ∈ leviOf (Nat.add_sub_of_le ha) w (d.K' w) ∧
    d.μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1
  fix : ∀ a ≤ n, ∀ w ∈ d.Bad, IsHecke (d.L a w) (d.fix a w)

def Good (w : Pl E) : Prop :=
  IsSplitAt w ∧ w ∉ d.T ∧ w ∉ d.S₀ ∧ w ∉ d.Bad ∧ ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → d.μ w u = 1

def IsGen (a : ℕ) (ha : a ≤ n) (L : LM d.kap a (n - a)) : Prop := L = d.eL a ∨ ∃ w k intersection_update_fsHerm_neg_one, d.Good w ∧ L = d.hL a ha w k intersection_update_fsHerm_neg_one

end LocData

def LM.Eqv {κ : Pl E → Type} {a b : ℕ} (P : Finset (Pl E)) (L L' : LM κ a b) : Prop :=
  (∀ w ∈ P, L.m w = L'.m w) ∧ (∀ w ∉ P, L.s w = L'.s w) ∧ L.t = L'.t

def LocOk : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n),
  (∀ w, Nonempty (d.kap w)) ∧ (d.betaL a ha).Ok d.P ∧ (d.fixL a).Ok d.P ∧ ∀ L, d.IsGen a ha L → L.Ok d.P

def LocComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n),
  ∀ L L', d.IsGen a ha L → d.IsGen a ha L' →
    (L.mul L').Eqv d.P (L'.mul L) ∧ (L.mul L'.adj).Eqv d.P (L'.adj.mul L) ∧
      ((d.betaL a ha).mul L).Eqv d.P (L.mul (d.betaL a ha)) ∧ ((d.betaL a ha).mul L.adj).Eqv d.P (L.adj.mul (d.betaL a ha))

def SphComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (f f' : LF a b w),
  IsHecke (K2 a b w) f → IsHecke (K2 a b w) f' → mconv f f' = mconv f' f

def IdemAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
  (L : Subgroup (GLw a w × GLw b w)), IsOpen (L : Set (GLw a w × GLw b w)) → L ≤ K2 a b w →
  IsHecke L (idem L) ∧ lfStar (idem L) = idem L ∧ ∀ f : LF a b w, IsHecke L f →
    mconv (idem L) f = f ∧ mconv f (idem L) = f ∧ IsHecke L (lfStar f)

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchS
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def gpow {w : Pl E} (f : GLw n w → ℂ) : ℕ → GLw n w → ℂ
  | 0 => f
  | N + 1 => gconv f (gpow f N)

def mpow {w : Pl E} (X : Finset (GLw n w)) (Φ : GLw n w → GLw n w → GLw a w × GLw b w → ℂ) :
    ℕ → GLw n w → GLw n w → GLw a w × GLw b w → ℂ
  | 0 => Φ
  | N + 1 => fun x z m => ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (Φ x y) (mpow X Φ N y z) m

def splitPlaceMackeyTraceTwist (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (X : Finset (GLw n w)) (f : GLw n w → ℂ) (N : ℕ)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) *
    (((X.card : ℂ))⁻¹ * ∑ x ∈ X, mpow X (phi3 h w f) N x x m)

def SplitPlaceConstantTermPowers : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) →
    (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') →
    ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') →
    ∀ f : GLw n w → ℂ, IsHk K' f → ∀ (N : ℕ) (m : GLw a w × GLw b w),
      ct h w (gpow f N) m = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, mpow X (phi3 h w f) N x x m

def MatchSplitPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a : ℕ) (w : Pl E), IsSplitAt w →
    (∀ g : GLw n w, g ∈ UL n w) → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ) (K' : Subgroup (GLw n w)),
    IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') →
    IsLevel (MonoidHom.id _) (KL n w) (K'.subgroupOf (UL n w)) →
    ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') →
    ∀ f : GLw n w → ℂ, IsHk K' f → ∀ (ha : a ≤ n) (N : ℕ),
      Match n a (n - a) w μ (fun u : UL n w => gpow f N (u : GLw n w)) (splitPlaceMackeyTraceTwist (Nat.add_sub_cancel' ha) w μ X f N)

end PositivityTheory.Rg.BcB.F.MS

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
section
noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.MT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open Formalism.UG (ordL)

def lone2 (a b : ℕ) (w : Pl E) : GLw a w × GLw b w → ℂ :=
  (((iwGL a w).prod (iwGL b w) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)).indicator
    fun _ => ((((iwGL a w).prod (iwGL b w)).relIndex ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) : ℕ) : ℂ)

def mpow (w : Pl E) (f : GLw a w × GLw b w → ℂ) : ℕ → GLw a w × GLw b w → ℂ
  | 0 => lone2 a b w
  | k + 1 => mconv f (mpow w f k)

def admitted (n a : ℕ) (s : Finset (Fin (n / 2))) : Prop :=
  s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2 ∧
    (symIdx n (a % 2 = 1) s).card = a ∧ (symIdx n ((n - a) % 2 = 1) sᶜ).card = n - a

def entT (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) {J : Type} [Fintype J] (c : J → ℂ) (x : J → Fin n → ℤ)
    (s : Finset (Fin (n / 2))) (y : GLw a w × GLw (n - a) w) : ℂ :=
  if h : admitted n a s then
    ∑ j, c j * (-qh w) ^ (-vRes n a (lOf (x j)) s) *
      dcos a w (tdiag ϖ (restr (x j) _ h.2.2.2.1)) y.1 * dcos (n - a) w (tdiag ϖ (restr (x j) _ h.2.2.2.2)) y.2
  else 0

def cR (n a : ℕ) (w : Pl E) (b : GLw n w) : ℂ :=
  (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ * ((iwGL a w).relIndex (GlobalTheory.LFun.KGL w (n := a)) : ℕ) *
    ((iwGL (n - a) w).relIndex (GlobalTheory.LFun.KGL w (n := (n - a))) : ℕ)

def MatchT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ w : Pl E, ¬ IsSplitAt w → ∀ (n a : ℕ), a ≤ n → ∀ (b : GLw n w), IsWitt n w b →
    ∀ ϖ : (w.adicCompletion E)ˣ, IsUnifAt ϖ → ∀ (J : Type) [Fintype J] (c : J → ℂ) (x : J → Fin n → ℤ),
      (∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) → ∀ k : ℕ, 1 ≤ k →
      Match n a (n - a) w 1 (lpow (iwU n w b) (fun γ => ∑ j, c j * fU n w b ϖ (lOf (x j)) γ) k)
        (fun y => cR n a w b ^ k * ∑ s, mpow w (entT n w ϖ a c x s) k y)

def FUMul : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w),
    IsWitt n w b → ∀ ϖ : (w.adicCompletion E)ˣ, IsUnifAt ϖ → ∀ l l' : Fin (n / 2) → ℤ, Cone l → Cone l' →
      lconv (fU n w b ϖ l) (fU n w b ϖ l') = fun γ => (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ * fU n w b ϖ (l + l') γ

def DcosMul : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ →
    ∀ (a b : ℕ) (x x' : Fin a → ℤ) (y y' : Fin b → ℤ), Antitone x → Antitone x' → Antitone y → Antitone y' →
      mconv (fun m : GLw a w × GLw b w => dcos a w (tdiag ϖ x) m.1 * dcos b w (tdiag ϖ y) m.2)
        (fun m => dcos a w (tdiag ϖ x') m.1 * dcos b w (tdiag ϖ y') m.2) =
      fun m => ((((iwGL a w).prod (iwGL b w)).relIndex ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) : ℕ) : ℂ)⁻¹ *
        (dcos a w (tdiag ϖ (x + x')) m.1 * dcos b w (tdiag ϖ (y + y')) m.2)

def MatchLin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (J : Type) [Fintype J] (c : J → ℂ) (f : J → UL n w → ℂ) (φ : J → GLw a w × GLw b w → ℂ),
    (∀ j, Continuous (f j) ∧ HasCompactSupport (f j) ∧ Continuous (φ j) ∧ HasCompactSupport (φ j)) →
    (∀ j, Match n a b w μ (f j) (φ j)) → Match n a b w μ (fun γ => ∑ j, c j * f j γ) (fun y => ∑ j, c j * φ j y)

def CtMul : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w →
    ∀ μ : (w.adicCompletion E)ˣ →* ℂˣ, (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) →
    ∀ f g : UL n w → ℂ, IsHecke (KL n w) f → IsHecke (KL n w) g →
      ctMu (Nat.add_sub_cancel' ha) w μ (lconv f g) =
        mconv (ctMu (Nat.add_sub_cancel' ha) w μ f) (ctMu (Nat.add_sub_cancel' ha) w μ g)

def MatchSplit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w →
    ∀ μ : (w.adicCompletion E)ˣ →* ℂˣ, (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) →
    ∀ f : UL n w → ℂ, IsHecke (KL n w) f → ∀ k : ℕ, 1 ≤ k →
      Match n a (n - a) w μ (lpow (KL n w) f k) (mconv (ctMu (Nat.add_sub_cancel' ha) w μ f)
        (Nat.rec (ctMu (Nat.add_sub_cancel' ha) w μ (lone (KL n w))) (fun _ g => mconv (ctMu (Nat.add_sub_cancel' ha) w μ f) g) (k - 1)))

def MatchSplitOf : Prop := M3 → CtMul → MatchSplit

end PositivityTheory.Rg.BcB.F.MT

end
end

