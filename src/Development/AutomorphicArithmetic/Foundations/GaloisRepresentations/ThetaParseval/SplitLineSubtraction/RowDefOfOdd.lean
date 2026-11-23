module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

section Alg

variable {Γ k : Type} [Group Γ] [CommRing k]

def dg {t : ℕ} (a : Fin t → Γ →* kˣ) : Γ →* GL (Fin t) k where
  toFun g := ⟨Matrix.diagonal fun i => (a i g : k), Matrix.diagonal fun i => (((a i g)⁻¹ : kˣ) : k),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [Matrix.diagonal_mul_diagonal])

abbrev cp {n : ℕ} (r : Γ →* GL (Fin n) k) (g : Γ) : k[X] := (r g : Matrix (Fin n) (Fin n) k).charpoly

abbrev lin {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ) : k[X] := ∏ i, (X - C (a i g : k))

end Alg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def unrPol (S : Multiset ℂ) (m : ℤ) : ℂ[X] := (S.map fun z => X - C (z ^ (-m))).prod

def Above (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂ)
    (J : (E →+* Qbar l) → Multiset ℤ) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw),
    IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      (∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (J τ)) ∧
      ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = unrPol S (deg g)

def Cl (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂ)
    (J : (E →+* Qbar l) → Multiset ℤ) : Prop :=
  (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → FrobEig ι r w S) ∧ Above ι r w S J

variable [IsCMField E]

def SatU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ B




def wtJumps {n : ℕ} (lam : DomWeight n) : Multiset ℤ := Finset.univ.val.map fun k : Fin n => (k : ℤ) - lam.w k

structure IsUp {n t : ℕ} (U : Submodule ℂ (UA E n → ℂ)) (lam : (E →+* ℂ) → DomWeight n) (κ : HChar E) (m : (E →+* ℂ) → ℤ)
    (U' : Submodule ℂ (UA E (n + t) → ℂ)) (lam' : (E →+* ℂ) → DomWeight (n + t)) (ψ : Fin t → HChar E)
    (p : Fin t → (E →+* ℂ) → ℤ) : Prop where
  aut : IsAutRepU U'
  wt : ∀ τ, HasWeightAt U' τ (lam' τ)
  alg : ∀ i, IsAlgPos (ψ i) (p i)
  inf : ∀ τ, wtJumps (lam' τ) = (wtJumps (lam τ)).map (· + m τ) + Finset.univ.val.map fun i => -p i τ
  sat : ∀ w, IsSplitAt w → κ.UnrAt w → (∀ i, (ψ i).UnrAt w) → ∀ B, SatU U w B → ∃ B', SatU U' w B' ∧
    algSat (n + t) (normV w) B' = (algSat n (normV w) B).map (· * ((κ.val w : ℂˣ) : ℂ)⁻¹) +
      Finset.univ.val.map fun i => (((ψ i).val w : ℂˣ) : ℂ)


variable (E) in
def TwoUp (n : ℕ) : Prop :=
  ∀ (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight n, (∀ τ, HasWeightAt U τ (lam τ)) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), IsSplitAt w₀ →
    ∃ (t : ℕ) (κ : HChar E) (m : (E →+* ℂ) → ℤ) (U₁ U₂ : Submodule ℂ (UA E (n + t) → ℂ))
      (lam₁ lam₂ : (E →+* ℂ) → DomWeight (n + t)) (ψ₁ ψ₂ : Fin t → HChar E) (p₁ p₂ : Fin t → (E →+* ℂ) → ℤ),
      Odd (n + t) ∧ IsAlgPos κ m ∧ IsUp U lam κ m U₁ lam₁ ψ₁ p₁ ∧ IsUp U lam κ m U₂ lam₂ ψ₂ p₂ ∧
        (∀ i j, ψ₁ i ≠ ψ₂ j) ∧ κ.UnrAt w₀ ∧ ∀ i, (ψ₁ i).UnrAt w₀


end UpperTheory.Gal.TP.Sub

end
