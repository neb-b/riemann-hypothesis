module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0193
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0187
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

namespace PositivityTheory.HtPt.Qak

theorem exists_pairEquiv {ι κ : Type} (e : ι ≃ κ) (m : κ → ℕ) (n : ι → ℕ) (h : ∀ s, m (e s) = n s) :
    ∃ g : (Σ τ, {p : Fin (m τ) × Fin (m τ) // p.1 < p.2}) ≃ (Σ s, {lk : Fin (n s) × Fin (n s) // lk.2 < lk.1}),
      ∀ (s : ι) (i j : Fin (m (e s))) (hij : i < j),
        g ⟨e s, ⟨(i, j), hij⟩⟩ = ⟨s, ⟨(Fin.cast (h s) j, Fin.cast (h s) i), hij⟩⟩ := by
  let e1 : (Σ s, {p : Fin (m (e s)) × Fin (m (e s)) // p.1 < p.2}) ≃ (Σ τ, {p : Fin (m τ) × Fin (m τ) // p.1 < p.2}) :=
    Equiv.sigmaCongrLeft (β := fun τ => {p : Fin (m τ) × Fin (m τ) // p.1 < p.2}) e
  let e2 : ∀ s, {p : Fin (m (e s)) × Fin (m (e s)) // p.1 < p.2} ≃ {lk : Fin (n s) × Fin (n s) // lk.2 < lk.1} := fun s =>
    { toFun := fun p => ⟨(Fin.cast (h s) p.1.2, Fin.cast (h s) p.1.1), p.2⟩
      invFun := fun p => ⟨(Fin.cast (h s).symm p.1.2, Fin.cast (h s).symm p.1.1), p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨e1.symm.trans (Equiv.sigmaCongrRight e2), fun s i j hij => ?_⟩
  have h1 : e1.symm ⟨e s, ⟨(i, j), hij⟩⟩ = ⟨s, ⟨(i, j), hij⟩⟩ := e1.symm_apply_apply ⟨s, ⟨(i, j), hij⟩⟩
  rw [Equiv.trans_apply, h1]
  rfl

theorem reindex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K L : Type) [Field K] [Field L] [Algebra K L] (v : ∀ s : CMType H ⊕ CMType H, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) L), AlgebraicIndependent K (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) → ∃ T : FlagVar Dw → L, AlgebraicIndependent K T ∧ Set.range T = Set.range (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ ∀ (s : CMType H ⊕ CMType H) (i j : Fin (Dw.mult (Small.labelC s))) (hij : i < j), T ⟨Small.labelC s, ⟨(i, j), hij⟩⟩ = v s (Fin.cast (Small.mult_labelC Dw s) j) (Fin.cast (Small.mult_labelC Dw s) i) := by
  intro E _ _ _ H Dw K L _ _ _ v hv
  obtain ⟨g, hg⟩ := exists_pairEquiv (Small.labelEquiv H) Dw.mult (labelRk Dw) (Small.mult_labelC Dw)
  refine ⟨(fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∘ g,
    hv.comp g g.injective, g.surjective.range_comp _, fun s i j hij => ?_⟩
  exact congrArg (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)
    (hg s i j hij)

end PositivityTheory.HtPt.Qak
