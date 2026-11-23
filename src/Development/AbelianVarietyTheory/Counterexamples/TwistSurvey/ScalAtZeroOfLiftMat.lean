module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix

namespace GlobalTheory.ScalarConjugation

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

section Abstract

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem maj_eq_zero {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K)
    (h : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x x = 0) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x y = 0 := by
  have hc : ∀ i, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i = 0 := by
    have hs : ∑ i, ((Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) : ℝ) : ℂ) = 0 := by
      rw [← h]
      unfold Formalism.HermitianLatticesTheory.majAt
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    have hr : ∑ i, Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) = 0 := by
      exact_mod_cast hs
    intro i
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg _).1 hr i (Finset.mem_univ i))
  unfold Formalism.HermitianLatticesTheory.majAt
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, star_zero, zero_mul]

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

end Abstract

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

end Concrete

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.MainNotions

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


end Comparison₂

end GlobalTheory.ScalarConjugation
