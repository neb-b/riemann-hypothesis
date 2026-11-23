module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_splitExt_isGt_of_torusExtension :
    ∀ (K : Type) [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G],
      Nonempty (TorusExtension G) → ∃ E : SplitExt (Spec (CommRingCat.of K)), E.IsGt G := by
  intro K _ G _ _ ⟨T⟩
  let _ := T.addCommGroup
  let _ := T.free
  let _ := T.finite
  let _ := T.grpB
  obtain ⟨O, h₁, h₂, h₃, h⟩ := _root_.GlobalTheory.exists_gtDatum_of_splitTorus_extension (Spec (CommRingCat.of K)) T.X G T.B T.isAbelian T.q T.i
    T.q_hom T.i_hom T.q_flat T.q_surjective T.q_quasiCompact T.isKernel
  obtain ⟨d, -, -⟩ := h T.isAbelian
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem nonempty_torusExtension_of_isGt {K : Type} [Field K] (E : SplitExt (Spec (.of K)))
    (G : Over (Spec (.of K))) [GrpObj G] (h : E.IsGt G) : Nonempty (TorusExtension G) := by
  obtain ⟨d⟩ := h
  have := E.free
  have := E.finite
  have := d.q_affine
  exact ⟨
    { X := E.X
      B := E.B
      isAbelian := E.isAbelian
      q := d.q
      q_hom := d.q_hom
      q_flat := d.q_flat
      q_surjective := d.q_surjective
      q_quasiCompact := inferInstance
      i := d.i
      i_hom := d.i_hom
      isKernel := d.isKernel }⟩

theorem isSemiAbelian_of_isGt : ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G],
    E.IsGt G → IsSemiAbelian G := by
  intro S E G _ hc h
  obtain ⟨hs, hg⟩ := UnitRigidity.smooth_geometricallyConnected_of_isGt E G h
  obtain ⟨d⟩ := h
  have := d.q_affine
  have := E.isAbelian.proper
  refine ⟨hc, hs, ?_, ?_, hg, fun Ω _ _ p => ?_⟩
  · rw [← Over.w d.q]
    infer_instance
  · rw [← Over.w d.q]
    infer_instance
  · exact nonempty_torusExtension_of_isGt _ _ (GtBaseChange.isGt_extBC p E G d)

end GlobalTheory
end

