module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StMajorantTransport
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def MajorantTransport.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ M : Majorant h v, ∃ (d : ℕ) (κ : ℝ), ∀ g : archUnitary h v,
    ∃ T : (InfinitePlace E → ι → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ y, ‖T y‖ = M.len (invApply g y)) ∧
      ∀ (L : Submodule ℤ (InfinitePlace E → ι → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L],
        ZLattice.covolume (ZLattice.comap ℝ L T.symm.toLinearMap) = κ * ZLattice.covolume L

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StTraceHermNondegenerate
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

def traceHerm (h : HermitianForm F E W) (v : Basis ι E W) : LinearMap.BilinForm ℚ (ι → E) :=
  LinearMap.mk₂ ℚ
    (fun y z => Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)))
    (fun y₁ y₂ z => by simp only [map_add (f := _), LinearMap.add_apply])
    (fun c y z => by
      have e1 : v.equivFun.symm (c • y) = (algebraMap ℚ E c) • v.equivFun.symm y := by
        rw [← LinearEquiv.map_smul, algebraMap_smul]
      have e2 : conjHom F E (algebraMap ℚ E c) = algebraMap ℚ E c :=
        RingHom.map_rat_algebraMap _ _
      rw [e1, LinearMap.map_smulₛₗ₂, e2, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul,
        smul_eq_mul])
    (fun y z₁ z₂ => by simp only [map_add (f := _)])
    (fun c y z => by
      have e1 : v.equivFun.symm (c • z) = (algebraMap ℚ E c) • v.equivFun.symm z := by
        rw [← LinearEquiv.map_smul, algebraMap_smul]
      rw [e1, LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])

theorem traceHerm_apply (h : HermitianForm F E W) (v : Basis ι E W) (y z : ι → E) :
    traceHerm h v y z = Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)) := rfl

def TraceHermNondegenerate.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  (traceHerm h v).Nondegenerate

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Complement

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def IsHyperbolicPair (h : HermitianForm F E W) (v w : W) : Prop :=
  h.toSesq v v = 0 ∧ h.toSesq w w = 0 ∧ h.toSesq v w = 1

def hypComplement (h : HermitianForm F E W) (v w : W) : Submodule E W :=
  LinearMap.ker (h.toSesq v) ⊓ LinearMap.ker (h.toSesq w)

theorem mem_hypComplement {h : HermitianForm F E W} {v w x : W} :
    x ∈ hypComplement h v w ↔ h.toSesq v x = 0 ∧ h.toSesq w x = 0 := by
  simp [hypComplement]

def ComplementForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ v w : W, IsHyperbolicPair h v w →
    ∃ h' : HermitianForm F E (hypComplement h v w), ∀ x y, h'.toSesq x y = h.toSesq x y

end Complement

namespace GaussianPlane

end GaussianPlane

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectCovering
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

def SemidirectCovering.Statement (H L N : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [SecondCountableTopology L] [T2Space L] [MeasurableSpace L]
    [BorelSpace L] [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] : Prop :=
  ∀ (i : L →* H) (q : H →* L) (j : N →* H), Continuous i → Continuous q → IsClosedEmbedding j →
    (∀ l, q (i l) = l) → (∀ g, q g = 1 ↔ g ∈ j.range) →
    ∀ (μL : Measure L) [μL.IsHaarMeasure] (μN : Measure N) [μN.IsHaarMeasure],
    (∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j) →
    ∀ (Γ : Subgroup H) (C : Set N) (T : Set L), IsCompact C → MeasurableSet T → μL T < ⊤ →
      (∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C) → (∀ l, ∃ γ ∈ Γ, q γ * l ∈ T) →
      ∀ (ν : Measure H) [ν.IsHaarMeasure],
        ∃ S : Set H, MeasurableSet S ∧ ν S < ⊤ ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ S

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnfoldAlongSubgroup
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal

noncomputable section

def UnfoldAlongSubgroup.Statement (G Y : Type*) [Group G] [MeasurableSpace G] [MeasurableSpace Y] :
    Prop :=
  ∀ (μ : Measure G) (H : Subgroup G) [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (ρ : Measure Y) [SFinite ρ] (s : Y → G),
    Measurable (fun p : H × Y => (p.1 : G) * s p.2) →
    (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ x, f (x * s y) ∂ν ∂ρ) →
    ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ H →
    ∀ (FD : Set G) (FD₀ : Set H), IsFundamentalDomain Γ FD μ →
      IsFundamentalDomain (Γ.subgroupOf H) FD₀ ν →
    ∀ f : G → ℝ≥0∞, Measurable f → (∀ x : H, ∀ g, f (x * g) = f g) →
      ∫⁻ g in FD, f g ∂μ = ν FD₀ * ∫⁻ y, f (s y) ∂ρ

section Inhabitants

theorem measurableSingletonClass_cyclicTwo : MeasurableSingletonClass C2 :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

attribute [local instance] measurableSingletonClass_cyclicTwo

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnfoldingTorus
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def UnfoldingTorus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ)
    (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ ∀ FD : Set (archUnitary h v),
      IsFundamentalDomain (vecStabGroup h v La x₀) FD μ → ∀ t : ℝ, 0 < t →
        μ (FD ∩ {g | M.len (invApply g (vecAt v x₀)) < t}) =
          c * ∫⁻ b : InfinitePlace E → ℂ,
            {b : InfinitePlace E → ℂ | M.len (fun w => b w • vecAt v x₀ w) < t}.indicator
              (fun b => ∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) b

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVectorOrbits
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Units

variable (E : Type*) [Field E] [NumberField E]

def congruenceUnits (N : ℕ) : Subgroup (𝓞 E)ˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})).toMonoidHom).ker

omit [NumberField E] in
variable {E} in
theorem mem_congruenceUnits {N : ℕ} {ε : (𝓞 E)ˣ} :
    ε ∈ congruenceUnits E N ↔ (ε : 𝓞 E) - 1 ∈ Ideal.span {(N : 𝓞 E)} := by
  rw [congruenceUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq]

def CongruenceUnitsFiniteIndex.Statement : Prop :=
  ∀ N : ℕ, 0 < N → (congruenceUnits E N).index ≠ 0

end Units

section Groups

def BoundedIndexSubgroupsFinite.Statement (G : Type*) [AddCommGroup G] : Prop :=
  ∀ A B : AddSubgroup G, B.FG → A ≤ B → ∀ C : ℕ,
    {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C}.Finite

end Groups

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def IsotropicScaling.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (La : AddSubgroup W) (x₀ : W), IsLattice E La → IsIntegralOn h La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 → ∃ N : ℕ, 0 < N ∧ ∀ ε ∈ congruenceUnits E N,
      ∃ γ ∈ latticeStab h La, γ • x₀ = ((ε : 𝓞 E) : E) • x₀

end Spaces

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

