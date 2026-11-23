module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW

@[expose] public section

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.Kd.K4

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def InvMod (X : Tower Ω ε) (M m : ℕ) (a : X.Kˣ) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ h : X.Kˣ, X.sl (ofSL γ) (a : X.K) = a * (h : X.K) ^ m


open Classical in
def img (Γ : Subgroup SL(2, ℤ)) (M : ℕ) [NeZero M] : Finset SL(2, ZMod M) :=
  Finset.univ.filter fun γ => γ ∈ Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))

def trM (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (a : X.Khat l) : X.Fn l :=
  ∑ γ ∈ img (Gam N l) M, X.act l ((g * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) fun u => (u 0) ^ w • a

def CgF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a b : X.Fn l) : Prop :=
  ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (a u - b u) = 0

def Rep (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a : X.Kˣ) (x : X.Khat l) : Prop :=
  AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n a

def PolMod (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (t : X.Fn l) : Prop :=
  ∃ c : Fin (w + 1) → X.Khat l, (∀ i, ∃ f ∈ X.Un (l ^ n), Rep X l n f (c i)) ∧
    ∀ u, t u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i

end UpperTheory.Kd.K4

end
