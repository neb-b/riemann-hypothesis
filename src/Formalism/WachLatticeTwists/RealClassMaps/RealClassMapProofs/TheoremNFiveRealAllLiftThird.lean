module

public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapSecondPlace
public import Formalism.WachLatticeTwists.SplitClassesAll.Statement
public import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
public import Mathlib
public import Formalism.CoboundaryTransfers.Statement
public import Formalism.CoboundaryTransfers.StatementAPI
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
public import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistTheoremFromTorsionBound
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Bundle0001
public import Formalism.WachLatticeTwists.Statement
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
public import Formalism.WachLatticeTwists.HodgeTateChains.InvariantsCohomologyData
public import Formalism.CharacterColumnKernels.Statement
public import Formalism.CharacterColumnKernels.StatementPsi
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Imports
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Complete
public import Formalism.WachLatticeTwists.TorsionLengthCounts.Bundle0001
public import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
public import Formalism.WachLatticeTwists.HodgeTateChains.Statement
public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.Bundle0002
public import Formalism.LagrangeIdealLifts.Statement
public import Formalism.CoboundaryTransfers.GammaStableTransfers.Bundle0001
public import Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bundle0001
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocBK
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bridge
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Statement
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
public import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0001
public import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
public import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.LocLift
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.Bundle0001
public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsPowSmulIntegral
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG (uElt Ymod ColNNJ colPsi uRep colRelJ KO)
open Formalism.RepresentationBoundsCohomology.BR (yY)
open Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology (lcH1)
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff IsFGTop)

theorem lc_of_torsion (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    (r : G →* A) (χ : G →* T'ˣ) (E : A)
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hur : Continuous fun g : G => uElt r χ g)
    {M : Type} [AddCommGroup M] [Module O M] (htors : ∀ m : M, ∃ c : O, c ≠ 0 ∧ c • m = 0)
    (ψ : Ymod r χ E →ₗ[O] M) : IsLocallyConstant fun g => ψ (yY r χ E g) := by
  have hfg : IsFGTop O (Ymod r χ E) := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective ((Ymod r χ E).subtype.restrictScalars O) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : O × (Ymod r χ E) => q.1 • (q.2 : A))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : O, a ≠ 0 ∧ ∀ y : Ymod r χ E, a • ψ y = 0 := by
    obtain ⟨s, hs⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Ymod r χ E => htors (ψ y)
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span O (s : Set (Ymod r χ E)) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hx
      rw [hc, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have hopen := hfg.isOpen_mulSub hO ha
  have hy : Continuous fun g => yY r χ E g :=
    Continuous.subtype_mk (f := fun g => (uElt r χ g - 1) * E)
      ((hur.sub continuous_const).mul continuous_const) _
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  refine ⟨(fun g => yY r χ E g - yY r χ E g₀) ⁻¹' _, hopen.preimage (hy.sub continuous_const), ?_, ?_⟩
  · show yY r χ E g₀ - yY r χ E g₀ ∈ Formalism.RepresentationBoundsCohomology.LOC.mulSub a (Ymod r χ E)
    rw [sub_self]
    exact zero_mem _
  · rintro g ⟨z, hz⟩
    have hz' : a • z = yY r χ E g - yY r χ E g₀ := hz
    have h1 : ψ (yY r χ E g - yY r χ E g₀) = 0 := by
      rw [← hz', map_smul, hka]
    rw [map_sub, sub_eq_zero] at h1
    exact h1

theorem colPsi_lc (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T')
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hur : Continuous fun g : G => uElt r χ g)
    {M : Type} [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M] [IsScalarTower O A M]
    (htors : ∀ m : M, ∃ c : O, c ≠ 0 ∧ c • m = 0)
    {ι : Type} [DecidableEq ι] (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) :
    Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) ∈ lcH1 (uRep O (M := M) r χ) := by
  refine ⟨colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ, ?_, rfl⟩
  let ψ : Ymod r χ E →ₗ[O] M :=
    (φ ∘ₗ (colRelJ r χ E e₁ δ D j Kc k0).mkQ ∘ₗ LinearMap.inl A (Ymod r χ E) _).restrictScalars O
  exact lc_of_torsion p r χ E hO hA hur htors ψ

theorem pi_ko_torsion (O : Type) [CommRing O] [IsDomain O] (d : Type) [Fintype d] (m : d → KO O) :
    ∃ c : O, c ≠ 0 ∧ c • m = 0 := by
  classical
  have h1 : ∀ y : KO O, ∃ c : O, c ≠ 0 ∧ c • y = 0 := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) x
      refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
      exact ⟨a, by rw [Algebra.smul_def, mul_comm]; exact hab.symm⟩
  choose c hc0 hc using fun i => h1 (m i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.2 fun i _ => hc0 i, ?_⟩
  funext i
  rw [Pi.smul_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, hc i, smul_zero]
  rfl





end Formalism.RepresentationBoundsCohomology.FIN
