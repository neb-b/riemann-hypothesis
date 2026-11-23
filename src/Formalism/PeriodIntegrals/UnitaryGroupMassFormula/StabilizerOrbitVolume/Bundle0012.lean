module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0008
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVDx
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem gramR_add_sub {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J (x + W) - gramR R σ J x - gramR R σ J W = gramB R σ J x W := by
  funext i j
  simp [gramR, gramB, hR, Formalism.UG.hform, Matrix.sub_apply, Matrix.add_apply, map_add (f := _), add_mul, mul_add,
    Finset.sum_add_distrib] <;> ring

theorem gramB_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W W' : Fin n → Fin M → R ⊗[F] E) :
    gramB R σ J x (W + W') = gramB R σ J x W + gramB R σ J x W' := by
  funext i j
  simp [gramB, hR, Formalism.UG.hform, Matrix.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib] <;> ring

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHC
section
noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def hermO {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ) :
    AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
    ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [AddSubgroup.coe_add, Matrix.add_apply, map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro i j k
    simp only [ZeroMemClass.coe_zero, Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [NegMemClass.coe_neg, Matrix.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSA
section
noncomputable section

open IsDedekindDomain NumberField

namespace PI.VolStabSW

def SAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (FiniteAdeleRing (𝓞 F) F)),
    IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)) →
    ∀ x : FiniteAdeleRing (𝓞 F) F, ∃ a : F, x - algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U

theorem sAf_holds : SAf := by
  intro F _ _ U hU x
  obtain ⟨N, hN, hNU⟩ := PI.InvTopW.finite_neighbourhood_second F (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU.mem_nhds U.zero_mem)
  obtain ⟨m, hm, hmx⟩ := PIW.AdelClassFin.DictRing.af_denom (F := F) x
  obtain ⟨β, y, hy, e⟩ := PIW.AdelClassFin.DictRing.af_approx (F := F) _ hmx (m * N) (Nat.mul_pos hm (by omega))
  refine ⟨(β : F) / m, ?_⟩
  have hm0 : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hu : (m : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((m : F)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) m, ← map_mul, mul_inv_cancel₀ hm0, map_one]
  have hβ : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β = algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F) :=
    IsScalarTower.algebraMap_apply (𝓞 F) F _ β
  have hdiv : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((m : F)⁻¹) := by
    rw [div_eq_mul_inv, map_mul]
  have key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) = (N : FiniteAdeleRing (𝓞 F) F) * y := by
    rw [hdiv, ← hβ]
    push_cast at e
    linear_combination algebraMap F (FiniteAdeleRing (𝓞 F) F) ((m : F)⁻¹) * e -
      (x - (N : FiniteAdeleRing (𝓞 F) F) * y) * hu
  rw [key]
  exact hNU y hy

end PI.VolStabSW
end
end

