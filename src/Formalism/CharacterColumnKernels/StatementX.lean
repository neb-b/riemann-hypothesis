module

public import Formalism.CharacterColumnKernels.Statement

@[expose] public section

open Finset Polynomial

noncomputable section

namespace Formalism.NG

def matEnd (O M : Type*) [CommRing O] [AddCommGroup M] [Module O M] (d : Type*) [Fintype d]
    [DecidableEq d] : Matrix d d O →+* Module.End O (d → M) where
  toFun A := relMap O M A
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, Matrix.one_apply, ite_smul, Finset.sum_ite_eq]
  map_mul' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    show (∑ j, (A * B) i j • v j) = ∑ k, A i k • ∑ j, B k j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  map_zero' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap]
  map_add' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, add_smul, Finset.sum_add_distrib]

def LatQ {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type*) [Fintype d] [DecidableEq d] (_ρ : R →+* Matrix d d O) : Type _ := d → KO O

section LatQ
variable {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (d : Type*) [Fintype d] [DecidableEq d] (ρ : R →+* Matrix d d O)

instance : AddCommGroup (LatQ O d ρ) := inferInstanceAs (AddCommGroup (d → KO O))
instance : Module O (LatQ O d ρ) := inferInstanceAs (Module O (d → KO O))
instance : Module R (LatQ O d ρ) :=
  Module.compHom (d → KO O) ((matEnd O (KO O) d).comp ρ)

end LatQ

def StatKerHomRect : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m g d : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)] (P : Matrix m g R),
    Module.length O (LinearMap.ker (relMap O (KO O)
        (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2))) =
      Module.length O (Coker P →ₗ[R] LatQ O d ρ)

end Formalism.NG
