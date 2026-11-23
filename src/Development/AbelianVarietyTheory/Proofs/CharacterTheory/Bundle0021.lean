module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.IrreducibleCharacters.CuspidalCharacters
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsSimpleModuleOfFinrankEnd
section
namespace GlobalTheory.CuspCharCompare

open CuspElliptic GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
open scoped MonoidAlgebra

section Group

variable {G : Type} [Group G]

theorem isSimpleModule_of_finrank_end {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module R M]
    [Module ℂ M] [IsScalarTower ℂ R M] [SMulCommClass R ℂ M] [IsSemisimpleModule R M]
    (h : Module.finrank ℂ (Module.End R M) = 1) : IsSimpleModule R M := by
  have hE : Nontrivial (Module.End R M) := Module.nontrivial_of_finrank_eq_succ h
  have hM : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact not_subsingleton (Module.End R M) inferInstance
  have : Nontrivial (Submodule R M) := (Submodule.nontrivial_iff R).2 hM
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨U', hU⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h
    (U.subtype ∘ₗ U.projectionOnto U' hU)
  by_cases h0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := LinearMap.congr_fun hc x
    rw [h0, zero_smul] at this
    have h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x := by
      simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)
    rw [← h2, ← this]; rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have := LinearMap.congr_fun hc (c⁻¹ • x)
    have h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x := by
      simp [smul_smul, h0]
    rw [← h2, this]
    exact Subtype.property _

variable [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end Group

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

end GlobalTheory.CuspCharCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL


open Polynomial in
theorem _root_.GlobalTheory.CuspGL.star_virt_eq_inv : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ),
    χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G → ∀ g, star (χ g) = χ g⁻¹ := by
  intro G _ _ χ hχ
  have := Fintype.ofFinite G
  unfold _root_.GlobalTheory.BI.Virt at hχ
  induction hχ using AddSubgroup.closure_induction with
  | mem ψ hψ =>
    obtain ⟨n, ρ, h⟩ := hψ
    intro g
    have key := _root_.GlobalTheory.BadShare.ZCalc.character_inv (FDRep.of ρ) g
    simp only [h, Algebra.algebraMap_self, RingHom.id_apply]
    exact key.symm
  | zero => intro g; simp
  | add ψ φ _ _ h₁ h₂ => intro g; simp [h₁ g, h₂ g]
  | neg ψ _ h₁ => intro g; simp [h₁ g]

end GlobalTheory.CuspGL
end

