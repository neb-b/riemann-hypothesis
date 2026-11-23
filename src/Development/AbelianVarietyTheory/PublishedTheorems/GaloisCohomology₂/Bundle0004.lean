module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsLeKsOfGood
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Cyc

namespace GlobalTheory.Published

def FontaineEtale : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), GlobalTheory.Per.IsStd P AI →
    ∀ (K : FinExt l) (s : ℕ) (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l), IsIo (AI.εroot s) io →
      (∀ (LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
        ∃ (n : ℕ) (d : Fin n → TW (RW LL) T),
          (∀ i, d i ∈ FonD AI K LL io T) ∧
          (∀ z ∈ FonD AI K LL io T, ∃ w : Fin n → WCb l,
            (∀ i, w i ∈ Eur io ∧ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.actWCbHom (g : GQ l) (w i) = w i) ∧
            z = ∑ i, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w i : RW LL) • d i) ∧
          (∀ z ∈ EurT LL io T, ∃ w : Fin n → WCb l, (∀ i, w i ∈ Eur io) ∧
            z = ∑ i, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w i : RW LL) • d i) ∧
          Function.Bijective fun w : Fin n → WCb l =>
            ∑ i, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w i : RW LL) • d i) ∧
      ((∃ m : ℕ, K.1 ≤ Ks K m) → ∀ x : WCb l,
        (x ∈ Eur io ∧ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.actWCbHom (g : GQ l) x = x) ↔
          ∃ (n : ℕ) (a : Fin n → WCb l) (xb : Fin n → OCb l), (∀ i, a i ∈ E0 io) ∧
            (∀ i, ∃ (c : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ (c : Om l) ^ m = 1 ∧
              IsTiltOf (c : Om l) m (xb i)) ∧
            x = ∑ i, a i * inclW l (WittVector.teichmuller l (xb i)))

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
section
open Polynomial

namespace GlobalTheory.Published

def GreenCuspidal : Prop := GlobalTheory.GLq.Green

theorem GreenCuspidal.green (h : GreenCuspidal) : GlobalTheory.GLq.Green := h

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
section
noncomputable section

open Polynomial GlobalTheory.GLq

namespace GlobalTheory.Published

def IsRegularChar (g d : ℕ) {K : Type} [Field K] (θ : Kˣ →* ℂˣ) : Prop :=
  ∀ i j, i < d → j < d → θ ^ g ^ i = θ ^ g ^ j → i = j

def GreenRegularCharacters : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = d →
    ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ,
      (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧
        ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 →
          τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧
      (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) ∧
      ∀ χ : Gn g d → ℂ, IsCusp χ → ∃ θ, IsRegularChar g d θ ∧ χ = τ θ

end GlobalTheory.Published

end
end

