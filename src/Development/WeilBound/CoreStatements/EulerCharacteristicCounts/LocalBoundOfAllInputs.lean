module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.ExistsCochain

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace PositivityTheory.LocalTateOrthogonality.Bk

section Cochains

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem B1_le_Z1f (A : GRep G Qp LL O) : B1 A.ρ ≤ finiteCocycles PD A.ρ := by
  rintro _ ⟨v, rfl⟩
  refine ⟨⟨?_, fun g h => ?_⟩, v ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · have : cob A.ρ v = fun g => A.ρ g v + -v := funext fun g => sub_eq_add_neg _ _
    rw [this]
    exact (A.cont v).add continuous_const
  · change A.ρ (g * h) v - v = A.ρ g v - v + A.ρ g (A.ρ h v - v)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel
  · change (A.ρ g v - v) ⊗ₜ[Qp] (1 : B) = A.ρ g v ⊗ₜ[Qp] PD.actB g 1 - _
    rw [map_one, sub_tmul]

theorem lc_mk {V X : Type} [AddCommGroup V] [Module O V] [TopologicalSpace V] [ContinuousAdd V]
    [TopologicalSpace X] {M : Submodule O V} (hM : IsOpen (M : Set V)) {c : X → V}
    (hc : Continuous c) : IsLocallyConstant fun g => (Submodule.Quotient.mk (c g) : V ⧸ M) := by
  refine IsLocallyConstant.iff_isOpen_fiber.mpr fun y => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have : (fun g => (Submodule.Quotient.mk (c g) : V ⧸ M)) ⁻¹' {Submodule.Quotient.mk y} =
      (fun g => c g + -y) ⁻¹' (M : Set V) := by
    ext g
    simp [Submodule.Quotient.eq, sub_eq_add_neg]
  rw [this]
  exact hM.preimage (hc.add continuous_const)

variable {PD}

theorem cobO_of_cobL [ContinuousAdd LL] {L1 : Lattice (O := O) (charRep (cycLL PD LL))}
    (hL1 : IsOpen (L1.T : Set LL)) {z : G × G → LL} (h : CobL PD z) : CobO PD L1 z := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨fun g => Submodule.Quotient.mk (f g), ⟨lc_mk hL1 hf, fun _ => trivial⟩, rfl⟩

variable {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
  {m : A.V →ₗ[LL] A'.V →ₗ[LL] LL} {L1 : Lattice (O := O) (charRep (cycLL PD LL))}

omit [TopologicalSpace G] [TopologicalSpace LL] in
theorem mk_liftD {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (c : V ⧸ L.T) :
    Submodule.Quotient.mk (liftD L c) = c := (Submodule.Quotient.mk_surjective L.T c).choose_spec

def pairD (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL)) (hm : IsDualLat1 PD LA LA' m) :
    ↥LA.T →+ (A'.V ⧸ LA'.T) →ₗ[O] (LL ⧸ L1.T) :=
  AddMonoidHom.mk' (fun t => LA'.T.mapQ L1.T ((m t.1).restrictScalars O) fun y hy => by
      obtain ⟨a, ha⟩ := (hm.2 y).1 hy t.1 t.2
      rw [hL1]
      exact ⟨a, ha.symm⟩)
    fun t t' => by
      apply Submodule.linearMap_qext
      ext y
      simp

theorem mk_cupLD (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hm : IsDualLat1 PD LA LA' m) (d : G → A.V) (hd : ∀ g, d g ∈ LA.T) (c : G → A'.V ⧸ LA'.T)
    (p : G × G) : (Submodule.Quotient.mk (cupLD LA' m d c p) : LL ⧸ L1.T) =
      pairD hL1 hm ⟨d p.1, hd _⟩ (actD LA' p.1 (c p.2)) := by
  conv_rhs => rw [← mk_liftD LA' (c p.2)]
  rfl

theorem cobO_cup_iff (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hm : IsDualLat1 PD LA LA' m) (d : G → A.V) (hd : ∀ g, d g ∈ LA.T) (b : G → A'.V) :
    CobO PD L1 (cupLD LA' m d fun g => Submodule.Quotient.mk (b g)) ↔
      CobO PD L1 (cupL A'.ρ m d b) := by
  unfold CobO
  simp only [mk_cupLD hL1 hm d hd]
  rfl

theorem exists_of_mem_HfD {c : G → A'.V ⧸ LA'.T} (hc : c ∈ HfD PD LA') :
    ∃ b ∈ finiteCocycles PD A'.ρ, c = fun g => Submodule.Quotient.mk (b g) := by
  obtain ⟨_, ⟨b, hb, rfl⟩, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨b + cob A'.ρ x, (finiteCocycles PD A'.ρ).add_mem hb (B1_le_Z1f PD A' ⟨x, rfl⟩), rfl⟩

theorem hfD_le (hT : IsOpen (LA'.T : Set A'.V)) : HfD PD LA' ≤ divisibleCocycles LA' := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := exists_of_mem_HfD hc
  refine ⟨lc_mk hT hb.1.1, fun g h => ?_⟩
  change _ = Submodule.Quotient.mk (b g + A'.ρ g (b h))
  exact congrArg Submodule.Quotient.mk (hb.1.2 g h)

end Cochains

end PositivityTheory.LocalTateOrthogonality.Bk
