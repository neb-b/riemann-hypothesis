module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsHolToPointAndExp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExpEqOfPeriodsOfMarking

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientPointModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem heckePoints_of_laws :
    Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
        1 ≤ D.p + D.q → ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun hL _ => heckePoints_of_parts_comm hL LiePull.lieMult_pull obj_pull ObjMaps.id_comp_cancel
    obj_isAbelianScheme_dim_rigidified_sym (moduli_rep_of_base ObjMaps.id_comp_cancel)
    (exists_tateIso_heckeQuotient SimAlg.sim_group) (exists_heckeQuotient_triple_of_laws hL)
    (weilIs_along_hom hL.globalFns) LieEtale.lieMult_iff_of_etale (lam_iso_of_weil_pairings hL)
    (exists_quotient_by_finite_group_of_points hL)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.HomExt

theorem mem_range_or_exists_dvr {W Z : Scheme.{0}} (i : W ⟶ Z) [IsPreimmersion i] [Flat i]
    [IsDominant i] [QuasiCompact i] [IsLocallyNoetherian Z] (z : Z) :
    z ∈ Set.range i ∨ ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T)
      (_ : IsDiscreteValuationRing T) (a : Sp T ⟶ Z) (c : Sp (FractionRing T) ⟶ W),
      c ≫ i = spMap (algebraMap T (FractionRing T)) ≫ a ∧ a (IsLocalRing.closedPoint T) = z := by
  obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes z
  have hξ' := genericPoints_subset_range_of_isDominant i hξ
  by_cases hne : ξ = z
  · exact .inl (hne ▸ hξ')
  obtain ⟨O, _, _, -, a, h₀, h₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
  obtain ⟨c, hc⟩ := exists_lift_of_range_subset i
    (spMap (algebraMap O (FractionRing O)) ≫ a) (by
      rintro _ ⟨t, rfl⟩
      have : spMap (algebraMap O (FractionRing O)) t = (⊥ : PrimeSpectrum O) := by
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap O (FractionRing O)) t.asIdeal = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
      rw [Scheme.Hom.comp_apply, this]
      exact h₀ ▸ hξ')
  exact .inr ⟨O, inferInstance, inferInstance, inferInstance, a, c, hc, h₁⟩

theorem finite_torsion_points {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsSemiAbelian G)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ X) {n : ℕ} (hn : 0 < n) :
    Finite {x : Over.mk t ⟶ G // x ^ n = 1} := by
  haveI := hG.comm
  have := (semiAbelian_torsion_finite_and_closedPoint_finiteOrder AbTorsionFinite.finite_torsion).1
    Ω ((Over.pullback t).obj G) (hG.fibres Ω t) n hn
  let e := TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp Ω))) t (Category.id_comp _)
  refine Finite.of_injective
    (β := {x : 𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G // x ^ n = 1})
    (fun x ↦ ⟨e.symm x.1, (map_pow e.symm x.1 n).symm.trans
      ((congrArg e.symm x.2).trans (map_one e.symm))⟩) fun a b h ↦ ?_
  exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))

theorem locallyQuasiFinite_of_torsion {X : Scheme.{0}} (z : X ⟶ Sp ℤ) [LocallyOfFiniteType z]
    {G G' Γ : Over X} [GrpObj G] [GrpObj G'] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hG' : IsSemiAbelian G') (p : Γ ⟶ G) (q : Γ ⟶ G') [LocallyOfFiniteType p.left]
    (hext : ∀ {T : Scheme.{0}} (a b : T ⟶ Γ.left), a ≫ p.left = b ≫ p.left →
      a ≫ q.left = b ≫ q.left → a = b)
    (key : ∀ (k : Type) [Field k] (c : Sp k ⟶ Γ.left) (n : ℕ),
      c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left → c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left) :
    LocallyQuasiFinite p.left := by
  have : JacobsonSpace Γ.left := jacobsonSpace_of_locallyOfFiniteType_int (p.left ≫ G.hom ≫ z)
  have : JacobsonSpace G.left := jacobsonSpace_of_locallyOfFiniteType_int (G.hom ≫ z)
  refine locallyQuasiFinite_of_finite_fibres_closedPoints p.left fun w hw ↦ ?_
  have hσ : IsClosed ({p.left w} : Set G.left) := p.left.closedPoints_subset_preimage_closedPoints hw
  generalize p.left w = σ at hσ
  have : Finite (G.left.residueField σ) :=
    (jacobson_closedPoints_tools_int G.left (G.hom ≫ z)).2.1 σ hσ
  let t₀ : Sp (G.left.residueField σ) ⟶ X := G.left.fromSpecResidueField σ ≫ G.hom
  have := SemiAbTorsion.finite_points_over z G (G.left.residueField σ) t₀
  let x₀ : Over.mk t₀ ⟶ G := Over.homMk (G.left.fromSpecResidueField σ) rfl
  have hn : 0 < Nat.card (Over.mk t₀ ⟶ G) := Nat.card_pos
  have hx₀ : x₀ ^ Nat.card (Over.mk t₀ ⟶ G) = 1 := pow_card_eq_one'
  generalize Nat.card (Over.mk t₀ ⟶ G) = n at hn hx₀
  let Ω := AlgebraicClosure (G.left.residueField σ)
  let r : Sp Ω ⟶ Sp (G.left.residueField σ) := spMap (algebraMap (G.left.residueField σ) Ω)
  let y : Sp Ω ⟶ G.left := r ≫ G.left.fromSpecResidueField σ
  have hy : σ ∈ Set.range y :=
    ⟨default, (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply σ _)⟩
  let r' : Over.mk (y ≫ G.hom) ⟶ Over.mk t₀ := Over.homMk r (Category.assoc _ _ _).symm
  have := finite_torsion_points hG' (y ≫ G.hom) hn
  refine (finite_preimage_of_finite_lifts p.left y ?_).subset
    (Set.preimage_mono (Set.singleton_subset_iff.mpr hy))
  let l : {x : Sp Ω ⟶ Γ.left // x ≫ p.left = y} → (Over.mk (y ≫ G.hom) ⟶ Γ) := fun x ↦
    Over.homMk x.1 (by
      change x.1 ≫ Γ.hom = y ≫ G.hom
      rw [← Over.w p, ← Category.assoc, x.2])
  have hl (x) : (l x ≫ q) ^ n = 1 := by
    have e : l x ≫ p = r' ≫ x₀ := Over.OverMorphism.ext x.2
    have h₁ : l x ≫ p ^ n = l x ≫ (1 : Γ ⟶ G) := by
      rw [SemiAbTorsion.comp_pow_points, e, ← SemiAbTorsion.comp_pow_points, hx₀, MonObj.comp_one,
        MonObj.comp_one]
    have h₂ : l x ≫ q ^ n = l x ≫ (1 : Γ ⟶ G') :=
      Over.OverMorphism.ext (key Ω x.1 n (congrArg CommaMorphism.left h₁))
    rwa [SemiAbTorsion.comp_pow_points, MonObj.comp_one] at h₂
  refine Finite.of_injective (β := {x : Over.mk (y ≫ G.hom) ⟶ G' // x ^ n = 1})
    (fun x ↦ ⟨l x ≫ q, hl x⟩) fun a b h ↦ Subtype.ext (hext _ _ (a.2.trans b.2.symm) ?_)
  exact congrArg (fun u ↦ u.1.left) h

end GlobalTheory.HomExt


open GlobalTheory GlobalTheory.HomExt in
theorem GlobalTheory.existsUnique_hom_extension_semiAbelian_normal :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (X U : Scheme.{0}) (j : U ⟶ X), (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f := by
  rintro H X U j ⟨hX, z, _, -⟩ _ _ _ _ G G' _ _ hG hG' f hf
  have := hG.smooth
  have := hG'.smooth
  have := hG.quasiCompact
  have := hG'.quasiCompact
  have := hG'.separated
  have : GlobalTheory.IsNormalScheme X := (GlobalTheory.isNormalScheme_iff X).mpr hX
  have : GlobalTheory.IsNormalScheme G.left := (GlobalTheory.isNormalScheme_iff _).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX)
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let u : pullback G.hom j ⟶ G.left := pullback.fst G.hom j
  let φ : pullback G.hom j ⟶ G'.left := f.left ≫ pullback.fst G'.hom j
  have hw : f.left ≫ pullback.snd G'.hom j = pullback.snd G.hom j := Over.w f
  have huφ : u ≫ G.hom = φ ≫ G'.hom := by
    rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hw]
  have : IsDominant u := isDominant_pullback_fst_of_isOpenMap j G.hom G.hom.isOpenMap
  have : IsPreimmersion u := inferInstanceAs (IsPreimmersion (pullback.fst G.hom j))
  have : Flat u := inferInstanceAs (Flat (pullback.fst G.hom j))
  have : QuasiCompact u := inferInstanceAs (QuasiCompact (pullback.fst G.hom j))
  have hus := isIso_stalkMap_of_flat_of_surjectiveOnStalks u
  have : GlobalTheory.IsNormalScheme (pullback G.hom j) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap u
  let Γ := graphClosure G.hom G'.hom u φ huφ
  let p : Γ ⟶ G.left := graphClosure.fst G.hom G'.hom u φ huφ
  let q : Γ ⟶ G'.left := graphClosure.snd G.hom G'.hom u φ huφ
  let i : pullback G.hom j ⟶ Γ := graphClosure.incl G.hom G'.hom u φ huφ
  have hip : i ≫ p = u := graphClosure.incl_fst ..
  have hiq : i ≫ q = φ := graphClosure.incl_snd ..
  have hpq : p ≫ G.hom = q ≫ G'.hom := graphClosure.condition ..
  have hpb := graphClosure.isPullback_incl G.hom G'.hom u φ huφ
  have : IsPreimmersion i := MorphismProperty.of_isPullback hpb ‹IsPreimmersion u›
  have : Flat i := MorphismProperty.of_isPullback hpb ‹Flat u›
  have : QuasiCompact i := graphClosure.quasiCompact_incl ..
  have : IsSchemeTheoreticallyDominant i := graphClosure.schemeDominant_incl ..
  have : IsDominant i := inferInstance
  have : IsReduced Γ := graphClosure.isReduced ..
  have : LocallyOfFiniteType p := graphClosure.locallyOfFiniteType_fst ..
  have : QuasiCompact p := graphClosure.quasiCompact_fst ..
  have : IsSeparated p := graphClosure.isSeparated_fst ..
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian (G.hom ≫ z)
  have : IsLocallyNoetherian Γ := LocallyOfFiniteType.isLocallyNoetherian p
  have : Surjective p := by
    refine ⟨fun σ ↦ ?_⟩
    rcases HomExt.mem_range_or_exists_dvr u σ with ⟨w, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩
    · exact ⟨i w, by rw [← Scheme.Hom.comp_apply, hip]⟩
    obtain ⟨F, s, -, -, hs₂, hs⟩ := HomExt.exists_hom_along_dvr H j hG hG' f T _ a c hc
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom (a ≫ G.hom) = pullback.snd G.hom (a ≫ G.hom) := Over.w F
    obtain ⟨l, ⟨hl, -⟩, -⟩ := graphClosure.existsUnique_lift G.hom G'.hom u φ huφ a
      (s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hF, reassoc_of% hs₂])
      (spMap (algebraMap T (FractionRing T))) c hc.symm hs
    exact ⟨l (IsLocalRing.closedPoint T), by rw [← hl]; rfl⟩
  let Γ' : Over X := Over.mk (p ≫ G.hom)
  let p' : Γ' ⟶ G := Over.homMk p rfl
  let q' : Γ' ⟶ G' := Over.homMk q hpq.symm
  have : LocallyOfFiniteType p'.left := ‹LocallyOfFiniteType p›
  have : LocallyQuasiFinite p := by
    refine HomExt.locallyQuasiFinite_of_torsion z hG' p' q'
      (fun a b ↦ graphClosure.hom_ext G.hom G'.hom u φ huφ) fun k _ x n hx ↦ ?_
    rcases HomExt.mem_range_or_exists_dvr i (x default) with hw | ⟨T, _, _, _, a, c, hc, ha⟩
    · obtain ⟨c, rfl⟩ := HomExt.exists_lift_of_range_subset i x (by
        rintro _ ⟨t, rfl⟩
        rwa [Subsingleton.elim t default])
      exact HomExt.comp_pow_eq_one_of_pullback_hom j f p' q' _ c
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hip.symm)
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hiq.symm) n hx
    obtain ⟨F, s, _, hs₁, hs₂, hs⟩ := HomExt.exists_hom_along_dvr H j hG hG' f T _ (a ≫ p) c
      (by rw [← reassoc_of% hc, hip])
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom ((a ≫ p) ≫ G.hom) =
      pullback.snd G.hom ((a ≫ p) ≫ G.hom) := Over.w F
    have hb : s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom) = a ≫ q := by
      have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk ((a ≫ p) ≫ G.hom)) (X := G')
        (spMap (algebraMap T (FractionRing T)))
        (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) (by
          change (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hF,
            reassoc_of% hs₂]))
        (b := Over.homMk (a ≫ q) (by
          change (a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc, Category.assoc, hpq]))
        (hs.trans (by
          change _ = spMap (algebraMap T (FractionRing T)) ≫ a ≫ q
          rw [← reassoc_of% hc, hiq]))
      exact congrArg CommaMorphism.left this
    let r : Sp (IsLocalRing.ResidueField T) ⟶ Sp T := spMap (IsLocalRing.residue T)
    have hr : x default ∈ Set.range (r ≫ a) := by
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      exact (Scheme.Hom.comp_apply r a _).trans
        ((congrArg a (IsLocalRing.comap_closedPoint (IsLocalRing.residue T))).trans ha)
    rw [HomExt.field_point_comp_eq_iff _ _ x _ ⟨default, rfl⟩,
      ← HomExt.field_point_comp_eq_iff (Z := Γ'.left) _ _ (r ≫ a) _ hr] at hx ⊢
    exact HomExt.comp_pow_eq_one_of_pullback_hom _ F p' q' (r ≫ a) (r ≫ s)
      (by rw [Category.assoc, hs₁, Category.assoc]; rfl)
      (by rw [Category.assoc, hb, Category.assoc]; rfl) n hx
  have : IsIso p := by
    have : IsPreimmersion (i ≫ p) := by rwa [hip]
    have : Flat (i ≫ p) := by rwa [hip]
    have : IsDominant (i ≫ p) := by rwa [hip]
    have : QuasiCompact (i ≫ p) := by rwa [hip]
    exact HomExt.isIso_of_densePart i p
  obtain ⟨ψ, hψ, huψ⟩ := graphClosure.exists_extension_of_isIso_fst G.hom G'.hom u φ huφ
  let F : G ⟶ G' := Over.homMk ψ hψ.symm
  have hF : (Over.pullback j).map F = f := by
    ext1
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans huψ
    · exact (Over.w _).trans hw.symm
  refine ⟨F, ⟨?_, hF⟩, fun F' hF' ↦ pullback_map_injective_of_flat j (hF'.2.trans hF.symm)⟩
  have : IsMonHom ((Over.pullback j).map F) := hF ▸ hf
  exact isMonHom_of_pullback_of_flat j F
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvr
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullSpread

section Pairing

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}

theorem weilIs_pow_left (hW : Out.WeilSt) {n : ℕ} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) (m : ℕ) : Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := by
  induction m with
  | zero => rwa [zero_add, pow_one, pow_one]
  | succ m ih =>
    rw [pow_succ x, pow_succ c]
    exact (hW S P n T).2.1 _ _ _ _ _ ih h

theorem weilIs_lower (hW : Out.WeilSt) {n m : ℕ} (hm : 0 < m) (hu : IsUnit ((n * m : ℕ) : Γ(T.left, ⊤)))
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * m) = 1) (hy : y ^ (n * m) = 1)
    (h : Out.WeilIs P.A P.L ((n * m : ℕ) : ℤ) x y c) : Out.WeilIs P.A P.L n (x ^ m) (y ^ m) (c ^ m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h₁ := CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₁
  exact ((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁

theorem eq_one_of_weilIs_one {K : Type} [Field K] (hW : Out.WeilSt) {x : Sp K ⟶ S} {n : ℕ}
    {y : Over.mk x ⟶ P.A} {c : Kˣ} (h : Out.WeilIs P.A P.L n 1 y (unitOn c)) : c = 1 := by
  have h₁ := (hW S P n _).2.1 _ _ _ _ _ h h
  rw [_root_.mul_one] at h₁
  have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
  exact mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)

end Pairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem rt_sq (H : Host E) (n N : ℕ) : RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  have e : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
    change 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
    ring
  simp [e, H.sqrt_neg_disc_sq]

def GeomAt (D : Datum H) {S : Scheme.{0}} (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) {k : Type} [Field k]
    (x : Sp k ⟶ S) (β : RZ H n N →+* k) : Prop :=
  DetCond D t.act x (β (RZ.rt H n N)) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      (I.ζ N : k) = β (RZ.ze H n N) ∧ ∀ a, toUnit _ ≫ lev a = I.ev N a

theorem GeomAt.push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (ν : SABMap t' t f)
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {lev' : D.La → (𝟙_ (Over S') ⟶ t'.G)}
    (hl : ∀ a, (lev' a).left ≫ ν.φ = f ≫ (lev a).left) {k : Type} [Field k] {y : Sp k ⟶ S'} {β : RZ H n N →+* k}
    (h : GeomAt D t' lev' y β) : GeomAt D t lev (y ≫ f) β := by
  obtain ⟨hdet, I, hI, hA⟩ := h
  have hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F) := by
    obtain ⟨w, hw, -⟩ := ν.lin
    exact ⟨w, hw⟩
  refine ⟨(detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ k y _).1 hdet,
    ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I,
    hI, fun a => ?_⟩
  · obtain ⟨g, rfl⟩ := (ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, ← ν.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL
      (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm
      (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc
  · apply Over.OverMorphism.ext
    show _ = (I.ev N a).left ≫ ν.φ
    rw [← hA, Over.comp_left, Over.comp_left, ObjPull.toUnit_left', ObjPull.toUnit_left', Category.assoc, hl]
    exact Category.assoc _ _ _

theorem geomAt_of_dense (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsReduced S] [ConnectedSpace S]
    (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (hN : 0 < N)
    (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S)
      (β : RZ H n N →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ GeomAt D t lev x β})
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : RZ H n N →+* K) (hx : x ≫ s = spMap β) :
    GeomAt D t lev x β := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  let P : Out.PolAV S :=
    { A := t.G, g := g, smoothDim := hg, L := t.PP.L, isLB := t.PP.isLB, ample := ha, ktriv := hk
      isAb := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
      rigid := ObjDim.rigidified
      sym := ObjDim.sym }
  have hdet : DetCond D t.act x (β (RZ.rt H n N)) :=
    _root_.GlobalTheory.DetSpread.detCond_of_dense E H D S t.G g t.act _ s _ hg (rt_sq H n N) (hd.mono fun p hp => by
      obtain ⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩ := hp
      exact ⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩) K x β hx
  refine ⟨hdet, ?_⟩
  have hdim : g = Module.finrank ℚ E / 2 * (D.p + D.q) :=
    ObjDim.dim_eq_of_detCond D t.act x (by rw [← map_pow, rt_sq, map_neg, map_natCast]) hdet
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback t.G.hom x) hg)
  have e₀ : ∀ {K : Type} [Field K] (x : Sp K ⟶ S),
      (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) = toUnit (Over.mk x) := fun x =>
    Over.OverMorphism.ext (ObjPull.toUnit_left' (Over.mk x)).symm
  have hcard : ∀ m, 0 < m → Nat.card {z : Over.mk x ⟶ t.G // z ^ m = 1} = m ^ Module.finrank ℤ D.La := fun m hm => by
    rw [finrank_int_lattice D, ← hdim]
    exact (hL.mulN S P m hm).2.2.2.2 K x (Nat.cast_ne_zero.2 hm.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.TateTower.tateIso_of_levels E H D K (Over.mk x ⟶ t.G) (fun c z => z ≫ t.act.act c)
    (fun n z z' c => Out.WeilIs t.G t.PP.L n z z' (unitOn c)) N (β (RZ.ze H n N)) _ id
    (fun i => toUnit _ ≫ lev i) hN
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m z z' c hn hm hz hz' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact weilIs_lower P hL.weil hm u' hz hz' h)
    (fun m hm => by
      have hn := Nat.mul_pos hN hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := _root_.GlobalTheory.exists_levelIsometry_of_dense hL E H D S P t.act.act _ s (RZ.ze H n N) _
        id lev (N * m) m hn (hd.mono fun p hp => by
          obtain ⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩ := hp
          exact ⟨K, inferInstance, x, β, I.ζ (N * m), I.ev (N * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn,
            I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn,
            by rw [← h₃, ← I.ζ_pow N m hN hm, Units.val_pow_eq_pow_val],
            fun i => (I.tower N m hN hm _).trans ((h₄ i).symm.trans (congrArg (· ≫ lev i) (e₀ x).symm))⟩)
          K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := _root_.GlobalTheory.TorsIsometry.ker_and_onto E H D K (Over.mk x ⟶ t.G)
        (fun z z' c => Out.WeilIs t.G t.PP.L (N * m : ℕ) z z' (unitOn c)) (N * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => eq_one_of_weilIs_one P hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, fun i => (h₇ i).trans (congrArg (· ≫ lev i) (e₀ x))⟩)
  exact ⟨I, hI, fun a => (hA a).symm⟩

theorem fullObj_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (s : Sp V ⟶ Sp (RZ H n N)) (t : SAB H (Sp V)) (lv : D.La → (𝟙_ (Over (Sp V)) ⟶ t.G)) (tK : SAB H (Sp K)) (ν : SABMap tK t (spMap (algebraMap V K))) (lvK : D.La → (𝟙_ (Over (Sp K)) ⟶ tK.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ a, (lvK a).left ≫ ν.φ = spMap (algebraMap V K) ≫ (lv a).left) → FullObj D (spMap (algebraMap V K) ≫ s) tK lvK → FullObj D s t lv := by
  intro hL _ E _ _ _ H D n N V K _ _ _ _ _ _ s t lv tK ν lvK hN hp ha hk hadd hker hl o
  refine ⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩
  have : CharZero V := (Spec.preimage x).hom.charZero
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  let Ω := AlgebraicClosure K
  let y : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  obtain ⟨b, hb⟩ : ∃ b : RZ H n N →+* Ω, y ≫ spMap (algebraMap V K) ≫ s = spMap b :=
    ⟨(Spec.preimage (y ≫ spMap (algebraMap V K) ≫ s)).hom, (Spec.map_preimage _).symm⟩
  have hΩ : GeomAt D t lv (y ≫ spMap (algebraMap V K)) b := GeomAt.push ν hl (o.geom Ω y b hb)
  have hdense : Dense {(⊥ : PrimeSpectrum V)} := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp
  refine geomAt_of_dense hL s t lv hN hp ha hk (Dense.mono ?_ hdense) k x β hx
  rintro _ rfl
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, _, b, ⟨(⊥ : PrimeSpectrum Ω), ?_⟩,
    (Category.assoc _ _ _).trans hb, hΩ⟩
  apply PrimeSpectrum.ext
  show Ideal.comap (algebraMap V K) (Ideal.comap (algebraMap K Ω) ⊥) = ⊥
  rw [Ideal.comap_bot_of_injective _ (algebraMap K Ω).injective,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)]

end GlobalTheory.FullSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsHolToModulipointExpOfHolomorphicPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isHolTo_point_and_exp_of_isHolPeriods :
    ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsOpen B → IsHolPeriods D' ty B P → (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → IsHolTo B y ∧ IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) :=
  fun hθ hL => HolPeriods.isHolTo_point_and_exp (UnifPoint.point_eq_iff_isometry_closed hθ hL) exp_eq_of_periods_of_marking
    (exists_local_period_lift hθ hL) PeriodCoord.exists_period_coordinates InjHol.bijective_fderiv_of_injOn
    SubfieldChart.exists_holomorphic_chart

end GlobalTheory
end

