module

public import Mathlib
public import Formalism.HarderNarasimhan.StatementPl

@[expose] public section

open Module NumberField Finset

noncomputable section

namespace Formalism.HermiteSiegelSlopes

open Formalism.HN

section Defs

variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

def degT (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  -Real.log (ht b X L) / (2 * (nPl K : ℝ))

end Defs

def BaseChange : Prop :=
  ∀ (F E ι : Type) [Field F] [NumberField F] [StarRing F] [_root_.NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [StarRing E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    [Fintype ι] [DecidableEq ι]
    (XF : InfinitePlace F → Matrix ι ι ℂ) (XE : InfinitePlace E → Matrix ι ι ℂ),
    (∀ v, IsUnit (XF v).det) → (∀ w, IsUnit (XE w).det) →
    (∀ (w : InfinitePlace E) (x : ι → F),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun E ι) XE w (fun i => algebraMap F E (x i)) =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun F ι) XF (w.comap (algebraMap F E)) x) →
    ∀ M : Submodule (𝓞 F) (ι → F), M.FG →
      rkK (Submodule.span (𝓞 E) ((fun (x : ι → F) (i : ι) => algebraMap F E (x i)) '' (M : Set (ι → F))))
        = rkK M ∧
      degT (Pi.basisFun E ι) XE
          (Submodule.span (𝓞 E) ((fun (x : ι → F) (i : ι) => algebraMap F E (x i)) '' (M : Set (ι → F))))
        = degT (Pi.basisFun F ι) XF M

end Formalism.HermiteSiegelSlopes
