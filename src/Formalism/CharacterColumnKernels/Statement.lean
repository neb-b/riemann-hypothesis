module

public import Mathlib

@[expose] public section

open Finset Polynomial

noncomputable section

namespace Formalism.NG

section Idem

variable {T A : Type*} [CommRing T] [Ring A] [Algebra T A]

end Idem

section Pres

variable {R : Type*} [Ring R] {m g : Type*} [Fintype m] [Fintype g]

def relSpan (Θ : Matrix m g R) : Submodule R (g → R) := Submodule.span R (Set.range Θ)

abbrev Coker (Θ : Matrix m g R) : Type _ := (g → R) ⧸ relSpan Θ

def relMap (O : Type*) [CommRing O] (M : Type*) [AddCommGroup M] [Module R M] [Module O M]
    [SMulCommClass R O M] (Θ : Matrix m g R) : (g → M) →ₗ[O] (m → M) where
  toFun v i := ∑ j, Θ i j • v j
  map_add' v w := by ext i; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext i; simp [Finset.smul_sum, smul_comm]

end Pres

section DVR

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

abbrev KO : Type _ := FractionRing O ⧸ (1 : Submodule O (FractionRing O))

def matQ {ι : Type*} [Fintype ι] (A : Matrix ι ι O) : (ι → KO O) →ₗ[O] (ι → KO O) :=
  relMap O (KO O) A

end DVR

def StatLenKer : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι O),
    Module.length O (LinearMap.ker (matQ O A)) = IsDiscreteValuationRing.addVal O A.det

def bigMat {R O : Type*} [CommRing O] {g d : Type*} (ρ : R → Matrix d d O) (Θ : Matrix g g R) :
    Matrix (g × d) (g × d) O :=
  fun p q => ρ (Θ p.1 q.1) p.2 q.2

abbrev baseChange {T : Type*} (T' : Type*) [CommRing T] [CommRing T'] [Algebra T T'] (J : Ideal T) :
    Type _ :=
  T' ⧸ Ideal.map (algebraMap T T') J

end Formalism.NG
