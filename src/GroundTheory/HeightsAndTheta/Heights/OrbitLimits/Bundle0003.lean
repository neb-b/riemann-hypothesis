module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

def InvertibleIndexMul.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (M N P : AddSubgroup Ω) (η : Type) [Fintype η] (g h : η → Ω),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) → (∀ b ∈ B, ∀ z ∈ N, b * z ∈ N) → (∀ b ∈ B, ∀ z ∈ P, b * z ∈ P) →
    (∀ i, g i ≠ 0) → (∀ i, h i ≠ 0) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * g i ∈ B) → (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * h i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i,
      ((∃ b : B, b ∉ m ∧ (b : Ω) * g i ∈ M) ∧ ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * g i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * h i ∈ N) ∧ ∀ z ∈ N, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * h i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * (g i * h i) ∈ P) ∧
        ∀ z ∈ P, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * (g i * h i))) →
      0 < genIndex M B.toAddSubgroup ∧ 0 < genIndex N B.toAddSubgroup ∧
        genIndex P B.toAddSubgroup = genIndex M B.toAddSubgroup * genIndex N B.toAddSubgroup

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeImageZLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.mixedEmbedding

noncomputable def latticeImage (F : Type*) [Field F] (L : AddSubgroup F) : Submodule ℤ (mixedSpace F) :=
  (L.map (mixedEmbedding F).toAddMonoidHom).toIntSubmodule

theorem mem_latticeImage {F : Type*} [Field F] (L : AddSubgroup F) (y : mixedSpace F) :
    y ∈ latticeImage F L ↔ ∃ x ∈ L, mixedEmbedding F x = y := by
  change y ∈ L.map (mixedEmbedding F).toAddMonoidHom ↔ _
  simp


open scoped Classical in
def LatticeImageZLattice.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (L : AddSubgroup F), L.FG →
    (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) →
      ∃ _ : DiscreteTopology (latticeImage F L), IsZLattice ℝ (E := mixedSpace F) (latticeImage F L)

end GroundTheory.Heights₂.Heights.Targets
end

