module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.ExistsCtxOkOfPins
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HostElementIdempotentModTwo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.AtRecord

theorem isRelTraceOneIdempotentModTwo_hostElement {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    IdemTwo (H.w0 : E) := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 : (H.w0 : E) + cc (H.w0 : E) = 1 := by
    have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
    rw [map_add (f := _), map_one] at this
    exact (congrArg _ (H.bar_eq _).symm).trans this
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have h3 : (H.rt : E) ^ 2 = -(16 * k + 7) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast, hk] at this
    exact this.trans (by push_cast; rfl)
  refine ⟨((2 * k + 1 : ℕ) : E), isIntegral_natCast _, ?_⟩
  rw [eq_sub_of_add_eq' h1]
  push_cast
  linear_combination (-(1 / 4 : E)) * h3 - (1 / 4 : E) * (2 * (H.w0 : E) - 1 + (H.rt : E)) * h2

end GlobalTheory.Ker.AtRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelMapsRankZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Models.RankZero

namespace GlobalTheory.LevelMapsAnyRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def unitSim (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower _ _ _ _ _ := ⟨0, by simp⟩
  inv _ _ := ⟨LinearMap.id, fun _ => ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩⟩
  mult _ _ _ _ := by simp

theorem levelMaps_rank_zero (hD : D.p + D.q = 0) : ToroidalLevelCompatibility (H := H) (D := D) := by
  intro l l₂ Xo Xo₂ hd
  have hsub := subsingleton_La hD
  obtain ⟨hs, hG⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  obtain ⟨hs₂, hG₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo₂
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨r, hr⟩ : ∃ r : Xo₂.X ⟶ Xo.X, r ≫ Xo.s = Xo₂.s ≫ spMap (levelFieldIncl hA) :=
    ⟨(Xo₂.s ≫ spMap (levelFieldIncl hA)) ≫ inv Xo.s, by simp⟩
  obtain ⟨m⟩ := nonempty_sabMap hG₂ hG r
  have haut : ∀ g : Sim D, Xo₂.LevAut g (Iso.refl _) := fun g => by
    obtain ⟨ν⟩ := nonempty_sabMap hG₂ hG₂ (Iso.refl Xo₂.X).hom
    exact ⟨Category.id_comp _, ν, fun _ => sec_comm hG₂ ν.cart.1.w _ _, fun _ => sec_comm hG₂ ν.cart.1.w _ _⟩
  refine ⟨r, levelFieldIncl hA, m, coe_levelFieldIncl hA, hr, fun _ => sec_comm hG m.cart.1.w _ _,
    fun _ => sec_comm hG m.cart.1.w _ _, fun g _ => ⟨Iso.refl _, haut g, Category.id_comp _⟩, fun c c₂ hc => ?_⟩
  have hring : (IntermediateField.inclusion c₂.le).toRingHom.comp (levelFieldIncl hA) =
      (IntermediateField.inclusion hc.le).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom := by
    ext x
    exact coe_levelFieldIncl hA x
  have w : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫
        spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hr, pullback.condition_assoc, Category.assoc, GlobalTheory.Models.RankZero.spMap_comp,
      GlobalTheory.Models.RankZero.spMap_comp, hring]
  have e₁ := pullback.lift_fst _ _ w
  have e₂ := pullback.lift_snd _ _ w
  have i₀ : IsIso (spMap (IntermediateField.inclusion hc.le).toRingHom) := by
    have : IsIso (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 ⟨IntermediateField.inclusion_injective hc.le,
        fun x => ⟨⟨x.1, hc.ge x.2⟩, rfl⟩⟩
    exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom)))
  have i₁ : IsIso (pullback.lift _ _ w) := IsIso.of_isIso_fac_right e₂
  refine ⟨pullback.lift _ _ w, e₁, e₂, inferInstance, inferInstance, inferInstance, fun k _ _ y y' h => ⟨?_, ?_⟩⟩
  · obtain rfl := (cancel_mono _).1 h
    exact ⟨unitSim D, Iso.refl _, ⟨by simp [unitSim], fun a => by rw [Subsingleton.elim (_ - a) 0]; exact zero_mem _,
      fun a => ⟨0, Subsingleton.elim _ _⟩⟩, haut _, Category.id_comp _,
      congrArg (y ≫ ·) (Category.comp_id _).symm⟩
  · intro g _ _ _ _
    exact ⟨fun a => by rw [Subsingleton.elim (g.f l₂.M a - a) 0]; exact zero_mem _,
      fun a => ⟨0, Subsingleton.elim _ _⟩⟩

theorem levelMaps (D : Datum H) : ToroidalLevelCompatibility (H := H) (D := D) := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
  · exact levelMaps_rank_zero h
  · exact (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H D h).1

end GlobalTheory.LevelMapsAnyRank
end

