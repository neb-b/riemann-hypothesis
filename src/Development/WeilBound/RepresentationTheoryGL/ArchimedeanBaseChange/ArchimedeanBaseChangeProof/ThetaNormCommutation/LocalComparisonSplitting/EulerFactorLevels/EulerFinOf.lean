module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.Fin

open PositivityTheory.Rg.BcB.G8

def Good {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) : Prop :=
  (∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) ∧
  ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧
    (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0

def DcCount : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K Γ : Subgroup G) (δ : G)
  (f : G → ℂ), IsOpen (K : Set G) → IsCompact (K : Set G) → Good θ K δ → Γ ≤ twCent θ δ →
  (∀ x : G, Finite (Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)) → Finite (Γ ⊓ cptPart (twCent θ δ) : Subgroup G) →
  (Finite (DoubleCoset.Quotient ((Γ.subgroupOf (twCent θ δ) : Subgroup (twCent θ δ)) : Set (twCent θ δ))
    ((cptPart (twCent θ δ)).subgroupOf (twCent θ δ) : Set (twCent θ δ)))) →
  (∀ x, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) →
  {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k)) ≠ 0}.Finite →
    dcSum Γ K (fun x => f (x⁻¹ * δ * θ x)) = mass θ Γ δ * twOrb θ K δ f

def MassProd : Prop := ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G') (δ : G) (δ' : G'),
  mass (θ.prodMap θ') (Γ.prod Γ') (δ, δ') = mass θ Γ δ * mass θ' Γ' δ'

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def UnitAE : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
  ∀ᶠ (w : {w : GlobalTheory.BCT.Pl E // w ∈ S}) in cofinite, ∀ (y : GLw a w.1 × GLw b w.1), y = (locEl a w.1 δ₁, locEl b w.1 δ₂) →
    y ∈ K2 (E := E) a b w.1 ∧ (∀ g : GLw a w.1 × GLw b w.1, g⁻¹ * y * ((thL a w.1).prodMap (thL b w.1)) g ∈ K2 (E := E) a b w.1 →
      ∃ t ∈ twCent ((thL a w.1).prodMap (thL b w.1)) y, t⁻¹ * g ∈ K2 (E := E) a b w.1) ∧
    cptPart (twCent ((thL a w.1).prodMap (thL b w.1)) y) ≤ K2 (E := E) a b w.1

def LocGood : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (w : Pl E)
  (y : GLw a w × GLw b w), (nrmL a w y.1).val.charpoly.Separable → (nrmL b w y.2).val.charpoly.Separable →
  Good ((thL a w).prodMap (thL b w)) (K2 a b w) y

def LocSupp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (w : Pl E)
  (y : GLw a w × GLw b w), (nrmL a w y.1).val.charpoly.Separable → (nrmL b w y.2).val.charpoly.Separable →
  (∀ C : Set (GLw a w × GLw b w), IsCompact C → {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set _)
    (K2 (E := E) a b w : Set (GLw a w × GLw b w)) | ∃ k ∈ K2 (E := E) a b w,
      (Quotient.out q * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (Quotient.out q * k) ∈ C}.Finite) ∧
  ∀ (K' : Subgroup (GLw a w × GLw b w)) (f : GLw a w × GLw b w → ℂ), IsOpen (K' : Set (GLw a w × GLw b w)) → K' ≤ K2 a b w →
    IsHecke K' f → ∀ x, (rStab fun k : K2 (E := E) a b w => f ((x * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * k))).index ≠ 0

def RatFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ)
  (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
  Good (thP E a b) ((Kf E a).prod (Kf E b)) (ratF E a δ₁, ratF E b δ₂) ∧
  (∀ x : Gf E a b, Finite (gam δ₁ δ₂ ⊓ ((Kf E a).prod (Kf E b)).map (MulAut.conj x).toMonoidHom : Subgroup (Gf E a b))) ∧
  Finite (gam δ₁ δ₂ ⊓ cptPart (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂)) : Subgroup (Gf E a b)) ∧
  Finite (DoubleCoset.Quotient
    ((((gam δ₁ δ₂).subgroupOf (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))) : Subgroup (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))) :
      Set (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂)))
    ((((cptPart (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))).subgroupOf (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))) :
      Subgroup (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))) : Set (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))))

def SuppFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)),
  IsSection S → ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
    {q : DoubleCoset.Quotient (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Set (Gf E a b))
      (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) |
      ∃ k ∈ (Kf E a).prod (Kf E b), orbFn S φ₁ φ₂ δ₁ δ₂ (Quotient.out q * k) ≠ 0}.Finite ∧
    {q : DoubleCoset.Quotient (gam δ₁ δ₂ : Set (Gf E a b)) (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) |
      ∃ k ∈ (Kf E a).prod (Kf E b), orbFn S φ₁ φ₂ δ₁ δ₂ (Quotient.out q * k) ≠ 0}.Finite

def EulerFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)),
  IsSection S → ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
    twOrb (thP E a b) ((Kf E a).prod (Kf E b)) (ratF E a δ₁, ratF E b δ₂) (finFn S φ₁ φ₂) =
      ∏ᶠ w ∈ S, twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w)

def FinHalfOf : Prop := DcCount → MassProd → RatFin → SuppFin → EulerFin → KfOC → FinLevel → FinHalf

def SuppFinOf : Prop := LocSupp → UnitAE → RatFin → LocGood → SuppFin

end PositivityTheory.Rg.BcB.G8.Fin

end
