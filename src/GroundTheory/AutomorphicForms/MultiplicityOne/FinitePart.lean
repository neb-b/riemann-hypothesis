module

public import Mathlib
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteFactor
public import GroundTheory.AutomorphicForms.SmoothRep

@[expose] public section

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep (normOneGL (K := K) (n := n)) H)

abbrev archRep : UnitaryRep (ArchUnits K n) H := σ.compHom (archProj K n) continuous_archProj

variable (V₀ : Submodule ℂ H) [CompleteSpace V₀] (hV₀ : (archRep σ).IsInvariant V₀)

def archType : UnitaryRep (ArchUnits K n) V₀ := (archRep σ).restrict V₀ hV₀

def homArch : Submodule ℂ (V₀ →L[ℂ] H) := (archType σ V₀ hV₀).intertwiners (archRep σ)

theorem finProj_comp_mem_homArch (w : AdelicGLn.FiniteAdelicGL K n) {S : V₀ →L[ℂ] H}
    (hS : S ∈ homArch σ V₀ hV₀) : σ (finProj K n w) ∘L S ∈ homArch σ V₀ hV₀ := by
  intro A v
  show σ (finProj K n w) (S (archType σ V₀ hV₀ A v)) = σ (archProj K n A) (σ (finProj K n w) (S v))
  rw [hS A v]
  show σ (finProj K n w) (σ (archProj K n A) (S v)) = σ (archProj K n A) (σ (finProj K n w) (S v))
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, finProj_mul_archProj_comm]

def HomSpace : Type _ := homArch σ V₀ hV₀

instance : AddCommGroup (HomSpace σ V₀ hV₀) := inferInstanceAs (AddCommGroup (homArch σ V₀ hV₀))

instance : Module ℂ (HomSpace σ V₀ hV₀) := inferInstanceAs (Module ℂ (homArch σ V₀ hV₀))

def finRep : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (HomSpace σ V₀ hV₀) where
  toFun w :=
    { toFun := fun S => (⟨σ (finProj K n w) ∘L (S : homArch σ V₀ hV₀).1,
        finProj_comp_mem_homArch σ V₀ hV₀ w (S : homArch σ V₀ hV₀).2⟩ : homArch σ V₀ hV₀)
      map_add' := fun S S' => Subtype.ext (ContinuousLinearMap.comp_add _ _ _)
      map_smul' := fun c S => Subtype.ext (ContinuousLinearMap.comp_smul _ _ _) }
  map_one' := by
    refine LinearMap.ext fun S => Subtype.ext ?_
    show σ (finProj K n 1) ∘L (S : homArch σ V₀ hV₀).1 = (S : homArch σ V₀ hV₀).1
    rw [map_one, UnitaryRep.map_one]
    exact ContinuousLinearMap.id_comp _
  map_mul' w w' := by
    refine LinearMap.ext fun S => Subtype.ext ?_
    show σ (finProj K n (w * w')) ∘L (S : homArch σ V₀ hV₀).1 =
      σ (finProj K n w) ∘L (σ (finProj K n w') ∘L (S : homArch σ V₀ hV₀).1)
    rw [map_mul, UnitaryRep.map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

section Admissible

variable {σ V₀}
variable {U₀ : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hV₀U : V₀ ≤ fixedSubspace σ U₀)


variable {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]

end Admissible

end MultiplicityOne

end

end GroundTheory.Automorphic
