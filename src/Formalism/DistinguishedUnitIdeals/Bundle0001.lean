module

public import Mathlib
public import Formalism.DistinguishedUnitIdeals.Statement

@[expose] public section

-- bundled from Formalism.DistinguishedUnitIdeals.CoprimeProd
section
noncomputable section

namespace Formalism.ExponentWindows

def SatDist : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (d : ℕ) (p : PowerSeries O), UnitDist ϖ d p →
      ∀ (k N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * z ∈ Ideal.span {p ^ k} →
        z ∈ Ideal.span {p ^ k}

def ConstDist : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (d : ℕ) (p : PowerSeries O), UnitDist ϖ d p → 1 ≤ d →
      ∀ (c : O) (y N : ℕ) (a : PowerSeries O),
        PowerSeries.C (ϖ ^ N) * (PowerSeries.C c - PowerSeries.C (ϖ ^ y) * a) ∈ Ideal.span {p} →
        ϖ ^ y ∣ c

end Formalism.ExponentWindows
end
end

-- bundled from Formalism.DistinguishedUnitIdeals.IsCocycle
section
noncomputable section

namespace Formalism.ExponentWindows.E

structure Base (O : Type) [CommRing O] where
  ℓ : ℕ
  φ : PowerSeries O →ₐ[O] PowerSeries O
  γ : PowerSeries O →ₐ[O] PowerSeries O
  comm : ∀ a, φ (γ a) = γ (φ a)

def Base.q {O : Type} [CommRing O] (B : Base O) : PowerSeries O :=
  PowerSeries.X + PowerSeries.C (B.ℓ : O)

def Base.p {O : Type} [CommRing O] (B : Base O) (s : ℕ) : PowerSeries O := (⇑B.φ)^[s] B.q

structure Lat {O : Type} [CommRing O] (B : Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] where

  φ : ZMod n → V →+ V

  γ : ZMod n → V →+ V
  φ_semi : ∀ i (a : PowerSeries O) (v : V), φ i (a • v) = B.φ a • φ i v
  γ_semi : ∀ i (a : PowerSeries O) (v : V), γ i (a • v) = B.γ a • γ i v
  comm : ∀ i (v : V), φ i (γ (i - 1) v) = γ i (φ i v)

  N : ZMod n → Submodule (PowerSeries O) V

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def Lat.phiIt (L : Lat B n V) (i : ZMod n) : ℕ → V → V
  | 0, v => v
  | k + 1, v => L.φ (i + (k + 1 : ℕ)) (Lat.phiIt L i k v)

def Lat.pull (L : Lat B n V) (i : ZMod n) (k : ℕ) : Submodule (PowerSeries O) V :=
  Submodule.span (PowerSeries O) (L.phiIt i k '' (L.N i : Set V))

def sm (a : PowerSeries O) (S : Submodule (PowerSeries O) V) : Submodule (PowerSeries O) V :=
  S.map (LinearMap.lsmul (PowerSeries O) V a)

def dv (a : PowerSeries O) (S : Submodule (PowerSeries O) V) : Submodule (PowerSeries O) V :=
  S.comap (LinearMap.lsmul (PowerSeries O) V a)

def Lat.Ic (L : Lat B n V) (c : ZMod n) (w : V) : Prop :=
  L.γ c w - w ∈ sm PowerSeries.X (L.N c)

def Lat.dφ (L : Lat B n V) (m : ZMod n → V) : ZMod n → V := fun i => L.φ i (m (i - 1)) - m i

def Lat.dγ (L : Lat B n V) (m : ZMod n → V) : ZMod n → V := fun i => L.γ i (m i) - m i

def Lat.IsCocycle (L : Lat B n V) (y z : ZMod n → V) : Prop := L.dγ y = L.dφ z

def Lat.IsCobound (L : Lat B n V) (y z : ZMod n → V) : Prop :=
  ∃ m : ZMod n → V, y = L.dφ m ∧ z = L.dγ m

end

structure LatHom {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V V' : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] [AddCommGroup V'] [Module (PowerSeries O) V']
    (L : Lat B n V) (L' : Lat B n V') where
  f : V →ₗ[PowerSeries O] V'
  φ_comm : ∀ i v, f (L.φ i v) = L'.φ i (f v)
  γ_comm : ∀ i v, f (L.γ i v) = L'.γ i (f v)
  map_N : ∀ i v, v ∈ L.N i → f v ∈ L'.N i

end Formalism.ExponentWindows.E
end
end

-- bundled from Formalism.DistinguishedUnitIdeals.UnivPart
section
noncomputable section

namespace Formalism.ExponentWindows

def NbThin {K D : Type} [Field K] [AddCommGroup D] [Module K D] (k : ℤ) : Submodule K D :=
  if k < 0 then ⊥ else ⊤

def NbUp {K D : Type} [Field K] [AddCommGroup D] [Module K D] (b : ℤ) (C : Submodule K D)
    (k : ℤ) : Submodule K D :=
  if k < -b then ⊥ else if k < 0 then C else ⊤

def NbDown {K D : Type} [Field K] [AddCommGroup D] [Module K D] (b : ℤ) (F : Submodule K D)
    (k : ℤ) : Submodule K D :=
  if k < 0 then ⊥ else if k < b then F else ⊤

def IsFilt {K D : Type} [Field K] [AddCommGroup D] [Module K D] (Fil : ℤ → Submodule K D) : Prop :=
  Antitone Fil ∧ (∃ lo : ℤ, Fil lo = ⊤) ∧ (∃ hi : ℤ, Fil hi = ⊥)

def Rounding : Prop :=
  ∀ (K D : Type) [Field K] [AddCommGroup D] [Module K D] (Fil : ℤ → Submodule K D)
    (G S η g b : ℤ), IsFilt Fil → 0 ≤ G → 0 ≤ S → 0 ≤ η → G ≤ g → S ≤ g → η ≤ g → g < b →
    ((∀ u, Fil u ≠ Fil (u + 1) → -G ≤ u ∧ u ≤ G) →
      ∀ i, NbThin (i - g) ≤ Fil (-i) ∧ Fil (-i) ≤ NbThin (i + g)) ∧
    ((∀ u, Fil u ≠ Fil (u + 1) → (b ≤ u ∧ u ≤ b + S) ∨ (-η ≤ u ∧ u ≤ η)) →
      ∀ i, NbUp b (Fil b) (i - g) ≤ Fil (-i) ∧ Fil (-i) ≤ NbUp b (Fil b) (i + g)) ∧
    ((∀ u, Fil u ≠ Fil (u + 1) → (-b - S ≤ u ∧ u ≤ -b) ∨ (-η ≤ u ∧ u ≤ η)) →
      ∀ i, NbDown b (Fil (-η)) (i - g) ≤ Fil (-i) ∧ Fil (-i) ≤ NbDown b (Fil (-η)) (i + g))

end Formalism.ExponentWindows
end
end

