module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelLawsCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

instance finite_levelMod : Finite (LevelMod Dw l) := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ (LevelMod Dw l) := Module.Finite.trans (𝓞 E) _
  have hM : (l.M : ℤ) ≠ 0 := by have := l.three_le; omega
  apply Module.finite_of_fg_torsion
  intro q
  refine ⟨⟨(l.M : ℤ), mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
  change (l.M : ℤ) • (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a = 0
  rw [natCast_zsmul, ← map_nsmul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Moduli.LevelAction.mem_of_modN l ⟨a, rfl⟩)

instance finite_levelAut : Finite (LevelAut Dw l) :=
  Finite.of_injective (fun g : LevelAut Dw l => (g : LevelMod Dw l → LevelMod Dw l)) DFunLike.coe_injective

theorem frMap_id_iff {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y' ↔ y = y' := by
  obtain ⟨hu, hr, -⟩ := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y
  exact ⟨fun h => hu _ _ hr h, fun h => h ▸ hr⟩

section Laws

variable {G : Type} [Group G] (R : RelFam Xo c G)

variable {R}

end Laws

end General

section Record

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

end Record

end GlobalTheory.LevelLawsCompare
