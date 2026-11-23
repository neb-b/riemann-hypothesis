module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSpecialOfLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj
open MonObj
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusFibre

open GlobalTheory.SplitTorus (torusMap bcIso)

theorem isClosedImmersion_special_of_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Type) [Field K] [Algebra R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G], IsSemiAbelian G →
    ∀ (r : ℕ) (u : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r ⟶ G), IsMonHom u →
    Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u) →
    IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map u).left := by
  intro R _ _ _ K _ _ G _ hG r u hu hmono
  let k := IsLocalRing.ResidueField R
  let Ω := AlgebraicClosure k
  refine _root_.GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension R k Ω (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r) G u ?_
  let p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  obtain ⟨E⟩ := hG.fibres Ω p
  let v := (bcIso p (Fin r → ℤ)).hom ≫ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u
  have hv : IsClosedImmersion v.left := by
    refine GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension Ω _ E r v inferInstance fun q hq φ hφ h => hφ ?_
    have hsep : IsSeparated G.hom := hG.separated
    have e1 : torusMap _ φ ≫ (bcIso p (Fin r → ℤ)).hom =
        (bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ) :=
      (GlobalTheory.SplitTorus.comm_bcMap_iff p _ _).1 (GlobalTheory.SplitTorus.torusMap_bcMap p φ)

    have hΩ : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map (torusMap _ φ ≫ u) =
        (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map 1 := by
      rw [Functor.map_comp, Functor.map_one, ← cancel_epi (bcIso p (ZMod q)).hom, MonObj.comp_one,
        ← Category.assoc]
      change ((bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ)) ≫ _ = _
      rw [← e1, Category.assoc]
      exact h

    have hk := _root_.GlobalTheory.baseChange_map_eq_of_fieldExtension R k Ω _ _ _ _ hΩ
    have hf : torusMap _ φ ≫ u = 1 :=
      GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow R (ZMod q) G hsep _ _ (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one R (ZMod q) G _ inferInstance hk)

    let pK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R K))
    have hK' : (Over.pullback pK).map (torusMap _ φ) = (Over.pullback pK).map (torusMap _ 0) := by
      rw [← cancel_mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u)]
      change (Over.pullback pK).map (torusMap _ φ) ≫ (Over.pullback pK).map u =
        (Over.pullback pK).map (torusMap _ 0) ≫ (Over.pullback pK).map u
      rw [← Functor.map_comp, ← Functor.map_comp, hf, GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]
    rw [GlobalTheory.SplitTorus.pullback_map_torusMap, GlobalTheory.SplitTorus.pullback_map_torusMap,
      cancel_epi, cancel_mono] at hK'
    exact GlobalTheory.SplitTorus.torusMap_injective hK'
  have : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u = (bcIso p (Fin r → ℤ)).inv ≫ v := by
    simp [v]
  rw [this, Over.comp_left]
  haveI : IsIso (bcIso p (Fin r → ℤ)).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (bcIso p (Fin r → ℤ)).inv))
  exact IsClosedImmersion.comp _ _

end GlobalTheory.TorusFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem cDvr_of_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  intro R R' _ _ _ _ _ _ ρ hR hE
  obtain ⟨hdvr, -, hc0⟩ := hR
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hinj, hfin⟩ := hE
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI := hnoeth
  haveI := hic
  have hinj' : Function.Injective (algebraMap R R') := hinj
  haveI : Ring.DimensionLEOne R' := Ring.DimensionLEOne.of_isIntegral R R'
  haveI : IsDedekindDomain R' := { }
  have hnf : ¬ IsField R' := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj' h)
  have hdvr' : IsDiscreteValuationRing R' := ((IsDiscreteValuationRing.TFAE R' hnf).out 1 3).2 (inferInstance : IsDedekindDomain R')
  exact ⟨hdvr', hcomp, charZero_of_injective_algebraMap hinj'⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCompletionOfQuasiFiniteGaloisRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QFEtale

theorem isEtaleCompletion_of_galRigid : ∀ (O R : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (f : O →+* R) [IsLocalHom f], IsAdicComplete (maximalIdeal R) R → (∀ p : Ideal R, p.IsPrime → (maximalIdeal O).map f ≤ p → p = maximalIdeal R) → ((residue R).comp f).Finite → ringKrullDim O ≤ ringKrullDim R → GalRigid f → IsEtaleCompletion f ∧ ((residue R).comp f).FormallyUnramified := by
  intro O R _ _ _ _ _ _ _ _ _ _ f _ hRc hqf hfin hdim hrig
  haveI hOn : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  letI : Algebra (ResidueField O) (ResidueField R) := (ResidueField.map f).toAlgebra
  have hres : (residue R).comp f = (ResidueField.map f).comp (residue O) := by
    ext o; simp [ResidueField.map_residue]
  have hfin' : (ResidueField.map f).Finite := by
    rw [hres] at hfin; exact RingHom.Finite.of_comp_finite hfin
  haveI : Module.Finite (ResidueField O) (ResidueField R) := hfin'
  let M := separableClosure (ResidueField O) (ResidueField R)
  let m : ResidueField O →+* M := algebraMap (ResidueField O) M
  have hmf : m.Finite := RingHom.finite_algebraMap.2 inferInstance
  haveI : Algebra.IsSeparable (ResidueField O) M := inferInstance
  haveI : Algebra.FormallyUnramified (ResidueField O) M := Algebra.FormallyUnramified.of_isSeparable _ _
  have hmu : m.FormallyUnramified := RingHom.formallyUnramified_algebraMap.2 inferInstance
  obtain ⟨A, _, _, _, ψ, hψl, E, hAcn, hψe, hψu, hE⟩ := _root_.GlobalTheory.EtaleCompletionResidue.exists_etaleCompletion_residue_equiv O M m hmf hmu
  obtain ⟨hAn, hAi, hAc, hA0⟩ := hAcn
  let u' : A →+* ResidueField R := (algebraMap M (ResidueField R)).comp ((E.symm : ResidueField A →+* M).comp (residue A))
  have hu' : ∀ a, u' a = 0 ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff _ (algebraMap M (ResidueField R)).injective,
      map_eq_zero_iff _ E.symm.injective]
  have hker : RingHom.ker u' = maximalIdeal A := by ext a; exact hu' a
  have hc : (residue R).comp f = u'.comp ψ := by
    ext o
    have h1 := RingHom.congr_fun hE (residue O o)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ResidueField.map_residue] at h1
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ← h1, RingEquiv.symm_apply_apply, m]
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.EtaleCompletionLift.exists_extension O A R (ResidueField R) ψ f u' (residue R) hψe hψu hRc
    inferInstance hker (ker_residue) hc (fun r => residue_surjective _)
  have hbm : ∀ a, b a ∈ maximalIdeal R ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff, ← hu', ← RingHom.comp_apply, hb2]
  haveI hbl : IsLocalHom b := ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((hbm a).2 ((mem_maximalIdeal a).2 h)) ha⟩
  have hbfin : b.Finite := by
    refine _root_.GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite A R b hAc (fun p hp h => hqf p hp ?_) ?_
    · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact h
    · refine RingHom.Finite.of_comp_finite (f := ψ) ?_
      rw [RingHom.comp_assoc, hb1]; exact hfin
  have hbinj : Function.Injective b := _root_.GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le A R b hbfin ((_root_.GlobalTheory.ringKrullDim_le_of_isEtaleCompletion O A ψ hψe).trans hdim)
  obtain ⟨R', _, _, _, θ, hR'cn, hθl, hθi, hθf, hfix⟩ := _root_.GlobalTheory.GalCover.exists_isCN_galois_of_finite A R b ⟨hAn, hAi, hAc, hA0⟩ hbfin hbinj
  let q := ringExpChar M
  haveI : ExpChar M q := ringExpChar.expChar M
  haveI : ExpChar (ResidueField R) q := expChar_of_injective_algebraMap (algebraMap M (ResidueField R)).injective q
  have hpi : ∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a) := by
    intro x
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem M q x
    obtain ⟨a, ha⟩ := residue_surjective (E y)
    refine ⟨n, a, ?_⟩
    rw [← RingHom.comp_apply, hb2, ← hy]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ha, RingEquiv.symm_apply_apply]
  have hbsurj : Function.Surjective b := by
    intro r
    refine hfix r fun σ hσ hσb => hrig R' θ σ hR'cn hθi hθf hσ (fun o => ?_) (fun r => _root_.GlobalTheory.ResFix.sigma_fix_mod_max A R R' b θ q σ hpi hσb r) r
    rw [← hb1]; exact hσb (ψ o)
  have hmapsurj : Function.Surjective (ResidueField.map b) := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hbsurj r
    exact ⟨residue A a, ResidueField.map_residue _ _⟩
  have hres2 : (residue R).comp f = (ResidueField.map b).comp ((residue A).comp ψ) := by
    rw [← hb1]; ext o; simp [ResidueField.map_residue]
  refine ⟨⟨?_, ?_, hfin⟩, ?_⟩
  · rw [← hb1]; exact RingHom.Flat.comp hψe.1 (RingHom.Flat.of_bijective ⟨hbinj, hbsurj⟩)
  · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact map_maximalIdeal_of_surjective b hbsurj
  · rw [hres2]; exact RingHom.FormallyUnramified.comp hψu (RingHom.FormallyUnramified.of_surjective hmapsurj)

end GlobalTheory.QFEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def IsFinSub {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S)
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)) : Prop :=
  (∀ V : S.Opens, IsAffineOpen V → ∀ a : Γ(S, V), (gp.app V).hom a ∈ F V) ∧
  (∀ (V V' : S.Opens) (hle : V' ≤ V), IsAffineOpen V → IsAffineOpen V' → ∀ x ∈ F V,
    ((Sp K).presheaf.map (homOfLE (gp.preimage_mono hle)).op).hom x ∈ F V') ∧
  (∀ V : S.Opens, IsAffineOpen V → ∀ (f : Γ(S, V)) (x : Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f)), x ∈ F (S.basicOpen f) →
    ∃ (k : ℕ) (y : Γ(Sp K, gp ⁻¹ᵁ V)), y ∈ F V ∧
      ((Sp K).presheaf.map (homOfLE (gp.preimage_mono (S.basicOpen_le f))).op).hom y =
        ((Sp K).presheaf.map (homOfLE (gp.preimage_mono (S.basicOpen_le f))).op).hom ((gp.app V).hom f) ^ k * x) ∧
  (∀ V : S.Opens, IsAffineOpen V → ∃ t : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ t, y ∈ F V) ∧
    ∀ x ∈ F V, ∃ c : Γ(Sp K, gp ⁻¹ᵁ V) → Γ(S, V), x = ∑ y ∈ t, (gp.app V).hom (c y) * y)

abbrev resK {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W : S.Opens} (h : W ≤ V) :
    Γ(Sp K, gp ⁻¹ᵁ V) →+* Γ(Sp K, gp ⁻¹ᵁ W) :=
  ((Sp K).presheaf.map (homOfLE (gp.preimage_mono h)).op).hom

def finFam {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens) : Subring Γ(Sp K, gp ⁻¹ᵁ W) :=
  ⨅ i, (Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
    resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _))).comap (resK gp (inf_le_left : W ⊓ V i ≤ W))

theorem resK_app {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W : S.Opens} (h : W ≤ V) (a : Γ(S, V)) :
    resK gp h ((gp.app V).hom a) = (gp.app W).hom ((S.presheaf.map (homOfLE h).op).hom a) := by
  rw [resK, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, gp.naturality]
  rfl

theorem resK_resK {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W X : S.Opens} (h : W ≤ V) (h' : X ≤ W)
    (x : Γ(Sp K, gp ⁻¹ᵁ V)) : resK gp h' (resK gp h x) = resK gp (h'.trans h) x := by
  rw [resK, resK, resK, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem mem_finFam {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens) (x : Γ(Sp K, gp ⁻¹ᵁ W)) :
    x ∈ finFam gp V t W ↔ ∀ i, resK gp (inf_le_left : W ⊓ V i ≤ W) x ∈ Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
      resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)) := by
  simp [finFam, Subring.mem_iInf]

theorem finFam_range {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens) (a : Γ(S, W)) : (gp.app W).hom a ∈ finFam gp V t W := by
  rw [mem_finFam]
  intro i
  rw [resK_app]
  exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)

theorem finFam_res {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W W' : S.Opens) (hle : W' ≤ W) (x : Γ(Sp K, gp ⁻¹ᵁ W))
    (hx : x ∈ finFam gp V t W) : resK gp hle x ∈ finFam gp V t W' := by
  rw [mem_finFam] at hx ⊢
  intro i
  have hii : W' ⊓ V i ≤ W ⊓ V i := inf_le_inf_right _ hle
  have e : resK gp (inf_le_left : W' ⊓ V i ≤ W') (resK gp hle x) =
      resK gp hii (resK gp (inf_le_left : W ⊓ V i ≤ W) x) := by
    rw [resK_resK, resK_resK]
  rw [e]
  have hm : resK gp hii (resK gp (inf_le_left : W ⊓ V i ≤ W) x) ∈ (Subring.closure _).map (resK gp hii) := ⟨_, hx i, rfl⟩
  rw [RingHom.map_closure] at hm
  refine Subring.closure_mono ?_ hm
  rintro _ ⟨y, hy | ⟨z, hz, rfl⟩, rfl⟩
  · obtain ⟨a, rfl⟩ := hy
    exact Or.inl ⟨_, (resK_app gp hii a).symm⟩
  · exact Or.inr ⟨z, hz, by rw [resK_resK]⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.ZH

namespace GlobalTheory.UPoinc.USum

def IsTwVal {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A}
    (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀)
    (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]))
    (U : ThetaGrp P.A P.L N T), α.IsGen ∧ SymLift P.A P.L N N x U ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      gs r z ⊤ v * (val α (r ≫ (ptSecT P.A h).left) z J * val τ (r ≫ β.left) z J).val =
        (GlobalTheory.CommPairing.tval U (r ≫ (ptSecT P.A h).left) z J * val α (r ≫ (ptSecT P.A (x * h)).left) z J).val *
          sval (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => 1) θ
            (r ≫ (ptSecT P.A ((x * h) ^ m)).left ≫ (β ▷ P.A).left) z J

def wtChar {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (a : S.Gam) :
    T →+ ZMod S.N where
  toFun t := ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) a)
  map_zero' := by simp [eStd]
  map_add' := by
    intro s t
    rw [← map_add (f := _)]
    congr 1
    simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

abbrev genPt {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) : Over (Sp R) := Over.mk (spMap ψ)

def genTo {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) : genPt ψ ⟶ baseOver (Sp R) :=
  Over.homMk (spMap ψ) (Category.comp_id _)

def IsGenLab {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω')
    (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left)
    (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)) : Prop :=
  IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a ∧ IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a' ∧
    LBIso P₀.L (ρ.P.L.pull a) ∧ LBIso P₀.L (ρ'.P.L.pull a') ∧
    (∀ b, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = (x b).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt b).left) ∧
    ∀ k, x (lab k) = genTo _ ≫ ρ.pt k

end GlobalTheory.UPoinc.USum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenericFibreFractionFieldMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem isGrpPullback_genMap : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (h : IsGrpPullback G' G (spMap ρ) β), IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G) (spMap (fracMap ρ hρ)) (genMap hρ β h.1.w) := by
  intro R R' _ _ _ _ ρ hρ G' _ G _ β h
  have n : IsGrpPullback ((Over.pullback (jK R')).obj G') G (spMap (fracMap ρ hρ) ≫ jK R)
      (genMap hρ β h.1.w ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_pullback G' (jK R')).comp h).congr (jK_comp_spMap ρ hρ) (genMap_fst hρ β h.1.w).symm
  exact IsGrpPullback.cancel (isGrpPullback_pullback G (jK R)) n (genMap_snd hρ β h.1.w)

end GlobalTheory.Mum.GenDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHExists

theorem dotProduct_pullback {g n : ℕ} (J : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (H : Matrix (Fin n) (Fin n) ℂ)
    (z w : Fin g → ℂ) :
    z ⬝ᵥ ((LinearMap.toMatrix' J).transpose * H * (LinearMap.toMatrix' J).map star).mulVec (star w) =
      J z ⬝ᵥ H.mulVec (star (J w)) := by
  have e : ((LinearMap.toMatrix' J).map star).mulVec (star w) = star (J w) := by
    rw [← LinearMap.toMatrix'_mulVec J w]
    generalize LinearMap.toMatrix' J = N
    funext a
    simp [Matrix.mulVec, dotProduct, star_sum, _root_.mul_comm]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    LinearMap.toMatrix'_mulVec]

theorem isHermitian_pullback {g n : ℕ} (N : Matrix (Fin n) (Fin g) ℂ) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) : (N.transpose * H * N.map star).IsHermitian := by
  have e : N.transpose = (N.map star).conjTranspose := by
    ext a b
    simp
  rw [e]
  exact Matrix.isHermitian_conjTranspose_mul_mul _ hH

theorem exists_isAH : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (L : LB A.left) (u : HolUnif A L g), ∃ (M : LB A.left) (u' : HolUnif A M g) (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), M.IsLB ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsAH H χ := by
  intro A _ g hA L u
  obtain ⟨Q, v, i, r, J, R, m, -, hi, -, hm, hJ, -, -, -, hRJ⟩ :=
    GlobalTheory.HolUnifHom.exists_linear_factor A g hA (GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u) L u
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v', Hm, χ', -, hAH, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  obtain ⟨J', hJ', hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v'
    hv1 hv2 i hi
  have hinj : ∀ z, J' z = 0 → z = 0 := by
    intro z hz
    have h0 : J z = 0 := LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by
      rw [← map_smul, ← v.ker, hJ, ← hJ', map_smul, hz, smul_zero, v'.ker]
      exact v'.Λ.zero_mem
    have h1 := hRJ z
    rw [h0, map_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast (show m ≠ 0 by omega))
  obtain ⟨u₁, hex, hΛ₁, hfr⟩ := GlobalTheory.exists_holUnif_linComb A Q.A L Q.L g Q.g u v' PUnit (fun _ => i)
    (fun _ => J') (fun _ => 1) (fun _ z => hJ' z)
  have hmem : ∀ l : u₁.Λ, J' (l : Fin g → ℂ) ∈ v'.Λ := fun l => hJΛ _ (hΛ₁ ▸ l.2)
  refine ⟨_, u₁, (LinearMap.toMatrix' J').transpose * Hm * (LinearMap.toMatrix' J').map star,
    fun l => χ' ⟨J' l.1, hmem l⟩, LB.isLB_linComb Q.isLB _ _, hex, hΛ₁, isHermitian_pullback _ hAH.1,
    fun z hz => ?_, fun l => hAH.2.2.1 _, ?_⟩
  · rw [dotProduct_pullback]
    exact hAH.2.1 _ fun h => hz (hinj z h)
  intro l j z hz
  rw [hex] at hz
  have hz' : ⊤ ≤ (v'.ex (J' z)).left ⁻¹ᵁ Q.L.U (j PUnit.unit) := by
    rw [hJ' z]
    exact (CubeValues.le_preimage_wchart (u.ex z).left Q.L (fun _ => i.left) j).1 hz PUnit.unit
  have e1 : u₁.fr j z = v'.fr (j PUnit.unit) (J' z) := by simpa using hfr j z
  have e2 : u₁.fr j (z + l) = v'.fr (j PUnit.unit) (J' z + J' l) := by simpa using hfr j (z + l)
  rw [e1, e2, dotProduct_pullback, dotProduct_pullback]
  exact hAH.2.2.2 ⟨J' l.1, hmem l⟩ (j PUnit.unit) (J' z) hz'

end GlobalTheory.AHExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def IsPullPt {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg φ D D') {T : Over (Sp R)} {T' : Over (Sp R')} (h : T'.left ⟶ T.left) (ξ : GtPt D T) (ξ' : GtPt D' T') : Prop :=
  ξ'.b.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ ξ.b.left ∧
  ∀ χ : D'.X, ∃ hψ : ∀ κ : Fin 4,
      DegPre.gtφT D' T' ξ'.b χ κ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ DegPre.gtφT D T ξ.b (hD.xe χ) κ,
    LB.Gen.Maps (LB.linCombIso hD.w _ DegPre.gtε) (ξ'.s χ)
      (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ DegPre.gtε _ hψ (ξ.s (hD.xe χ)))

end GlobalTheory.Mum
end
end

