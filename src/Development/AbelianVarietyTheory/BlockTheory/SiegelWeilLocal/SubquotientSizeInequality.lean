module

public import Mathlib
public import Formalism.HarderNarasimhan.StatementPl

@[expose] public section

open Module NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality

open Formalism.HN Formalism.HermitianLatticesTheory

section Dist

variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

def ptAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (y : V) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fcoord b X v y)

def spanAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (S : Submodule (𝓞 K) V) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ (ptAt b X v '' (S : Set V))

def distAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (S : Submodule (𝓞 K) V) (y : V) : ℝ :=
  Metric.infDist (ptAt b X v y) (spanAt b X v S : Set (EuclideanSpace ℂ ι))

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K] in
theorem norm_ptAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (y : V) : ‖ptAt b X v y‖ = normAt b X v y := by
  simp [ptAt, normAt, cnorm, EuclideanSpace.norm_eq]

end Dist

end GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality
