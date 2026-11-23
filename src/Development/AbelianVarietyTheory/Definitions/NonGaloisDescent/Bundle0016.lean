module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

namespace GlobalTheory.LamTie

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def TeichTriv (χ : Formalism.L2.Host.HChar H.E) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 H.E), OverP H H.pde w ∨ OverP H H.pde' w →
    ∀ x : (w.adicCompletion H.E)ˣ, x ^ (Ideal.absNorm w.asIdeal - 1) = 1 → χ.loc w x = 1

variable {H} {χ χ' : Formalism.L2.Host.HChar H.E}

theorem isUnitAt_of_pow_eq_one {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {x : (w.adicCompletion E)ˣ}
    (hx : x ^ (Ideal.absNorm w.asIdeal - 1) = 1) : IsUnitAt w x := by
  have h1 : Ideal.absNorm w.asIdeal - 1 ≠ 0 := by have := GlobalTheory.Mem.WildChar.one_lt_absNorm w; omega
  have := congrArg (fun y : (w.adicCompletion E)ˣ => Valued.v (y : w.adicCompletion E)) hx
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this
  exact (pow_eq_one_iff_left h1).1 this

namespace TeichTriv

theorem of_unr (h : ∀ w, OverP H H.pde w ∨ OverP H H.pde' w → χ.UnrAt w) : TeichTriv H χ :=
  fun w hw x hx => h w hw x (isUnitAt_of_pow_eq_one hx)

end TeichTriv

end Host

namespace LamDat

variable {D : D7} (Z : LamDat D)

def Teich : Prop := ∀ a, TeichTriv D.host (Z.chi a)

variable {Z}

end LamDat

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsLamTieFull (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → (∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i) ∧
    ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      (∀ lam : X.abelian₂ i, ∃ (j a : Fin D.R.m) (s : ℕ), IsLam X Z i (atSide X (X.sideL i lam) ι) lam j a s ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)) ∧
      ∀ (j a : Fin D.R.m) (s : ℕ) (b : Bool), 1 ≤ s → s ≤ BlochKatoReduction.Gen.NFun D.R + 1 →
        ∃ lam : X.abelian₂ i, X.sideL i lam = b ∧ IsLam X Z i (atSide X b ι) lam j a s ∧
          IsThOf X i (atSide X b ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

variable {X} {Z : LamDat D}

theorem isLamTieFull_of_labels (J A : ∀ i, X.abelian₂ i → Fin D.R.m) (S : ∀ i, X.abelian₂ i → ℕ)
    (hS : ∀ i, X.NonzeroIndexPlace i → ∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i)
    (hι : ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      ∀ lam : X.abelian₂ i, IsLam X Z i (atSide X (X.sideL i lam) ι) lam (J i lam) (A i lam) (S i lam) ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) (S i lam) (Z.kap (J i lam) (A i lam) (S i lam)) (cond0 D.host Z.w0)
          (Z.lam0 (X.l i) (J i lam) (A i lam)))
    (hall : ∀ i, X.NonzeroIndexPlace i → ∀ (j a : Fin D.R.m) (s : ℕ) (b : Bool), 1 ≤ s → s ≤ BlochKatoReduction.Gen.NFun D.R + 1 →
      ∃ lam : X.abelian₂ i, X.sideL i lam = b ∧ J i lam = j ∧ A i lam = a ∧ S i lam = s) : IsLamTieFull X Z := fun i hi => by
  obtain ⟨ι, h1, h2⟩ := hι i hi
  refine ⟨hS i hi, ι, h1, fun lam => ⟨_, _, _, h2 lam⟩, fun j a s b hs hs' => ?_⟩
  obtain ⟨lam, rfl, rfl, rfl, rfl⟩ := hall i hi j a s b hs hs'
  exact ⟨lam, rfl, h2 lam⟩

namespace IsLamTieFull

end IsLamTieFull

end Record

end GlobalTheory.LamTie
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw

variable (D : D7)

def SupG : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b g, ∀ f ∈ D.nexp.Bsup i j b,
  D.nexp.actG i j b g f ∈ D.nexp.Bsup i j b

def SupFull : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (D.nexp.Bsup i j b).FG ∧
  Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) = ⊤

def SupHk : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ f ∈ D.nexp.Bsup i j b,
  D.nexp.hkF i j b k P f ∈ D.nexp.Bsup i j b

def UnivSup (E : XD D) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M,
  (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (D.ntw.S0 i) → Disjoint Q (D.nexp.lev i j b a) →
  ∃ Xi : DelQM D.host (D.ntw.l i) Q M →₀ D.nexp.Fm i j b,
    D.nexp.thU i j b Q M a = Xi.sum (fun δ f => f ⊗ₜ[D.ntw.O i] AddMonoidAlgebra.single δ (1 : D.ntw.O i)) ∧
    ∀ δ, Xi δ ∈ Fm0 D.nexp i j b ∧ ((D.ntw.l i : D.ntw.O i) ^ c) • Xi δ ∈ D.nexp.Bsup i j b

def HkComm : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P k' P', HkIdx i k P → HkIdx i k' P' →
  Commute (D.nexp.hkF i j b k P) (D.nexp.hkF i j b k' P')

def OffRange : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → (∀ j, j ∉ Finset.Icc 1 D.R.m → ∀ b, Subsingleton (D.nexp.Fm i j b)) ∧
  ∀ s P, D.ntw.hEig i s 0 P = 1

def HkSS : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
  V0 D.nexp i j b ≤ ⨆ ev, (Eigsp D.nexp i j b ev ⊓ V0 D.nexp i j b)

end GlobalTheory.SupLaw
end
end

