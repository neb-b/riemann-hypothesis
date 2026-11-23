module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2236

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOfFieldExtensionPullbackProper
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem abelian_of_field_of_pullback : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Sp K)) [GrpObj G] (B : Over (Sp K')) [GrpObj B] (φ : B.left ⟶ G.left) (g : ℕ), IsSemiAbelian G → IsGrpPullback B G (spMap i) φ → IsProper B.hom → SmoothOfRelativeDimension g B.hom → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom := by
  intro K K' _ _ i G _ B _ φ g hG h hP hB
  have hc := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have : Flat (spMap i) := inferInstance
  have : Surjective (spMap i) := inferInstance
  have : UniversallyClosed G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hp : IsProper G.hom := ⟨⟩
  have : ConnectedSpace G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) (𝟙 _) (𝟙 _) G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (eSec G (default : PrimeSpectrum K))
  have hd' : SmoothOfRelativeDimension d B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback h.1 hd
  have e : d = g := ReciprocityTheory.ChartRestriction.G.H1.dim_unique B.hom hd' hB (eSec B (default : PrimeSpectrum K'))
  subst e
  exact ⟨⟨hc, inferInstance, hp, inferInstance⟩, hd⟩

end GlobalTheory.Mum.GenDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismExtOfDensePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem abelianScheme_end_ext_of_dense : ∀ (W : Scheme.{0}) [IsIntegral W] (G : Over W) [GrpObj G], IsAbelianScheme G → ∀ (Ω : Type) [Field Ω] (pt : Sp Ω ⟶ W), Dense (Set.range pt) → ∀ (f f' : G ⟶ G), pullback.fst G.hom pt ≫ f.left = pullback.fst G.hom pt ≫ f'.left → f = f' := by
  intro W _ G _ hG Ω _ pt hpt f f' h
  have : Smooth G.hom := hG.smooth
  have : IsProper G.hom := hG.proper
  have : IsDominant pt := ⟨hpt⟩
  have : QuasiCompact pt := inferInstance
  have := IsSchemeTheoreticallyDominant.of_isDominant pt
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom pt) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G.hom pt).flip
  exact Over.OverMorphism.ext (ext_of_schDom G.hom ((Over.w f).trans (Over.w f').symm)
    (pullback.fst G.hom pt) h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHodgeFiltrationFunctionalExtendsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_hodgeFiltration_functional_extends : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∃ H : FirstDeRham (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∀ c : F1 (A.hom ≫ 𝟙 (Sp R)), H c = ψ c := by
  first | exact @GlobalTheory.AbelianExtend.abelianScheme_hodgeFiltration_functional_extends' | exact GlobalTheory.AbelianExtend.abelianScheme_hodgeFiltration_functional_extends' | (intros; apply GlobalTheory.AbelianExtend.abelianScheme_hodgeFiltration_functional_extends' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleBundlesDescendFgSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.AbFGSpread

theorem sym_transfer {X Y : Scheme.{0}} {L : LB X} {N : LB Y} (hL : L.IsLB) (hN : N.IsLB) (jX : X ⟶ X)
    (jj : Y ⟶ Y) (φ : Y ⟶ X) (e : jj ≫ φ = φ ≫ jX) (hw : LBIso N (L.pull φ)) (hs : LBIso (N.pull jj) N) :
    LBIso ((L.pull jX).pull φ) (L.pull φ) := by
  have h1 : LBIso ((L.pull jX).pull φ) (L.pull (jj ≫ φ)) := by
    rw [e]; exact (FibreNef.lbIso_pull_comp hL jX φ).symm
  have h2 : LBIso (L.pull (jj ≫ φ)) ((L.pull φ).pull jj) := FibreNef.lbIso_pull_comp hL φ jj
  have h3 : LBIso ((L.pull φ).pull jj) (N.pull jj) := RigidBundleGlue.LBIso.pull hw.symm jj
  have p := fun (f : Y ⟶ X) => pull_isLB hL f
  refine LBIso.trans (pull_isLB (pull_isLB hL jX) φ) (p _) (p φ) h1 ?_
  refine LBIso.trans (p _) (pull_isLB (p φ) _) (p φ) h2 ?_
  refine LBIso.trans (pull_isLB (p φ) _) (pull_isLB hN _) (p φ) h3 ?_
  exact LBIso.trans (pull_isLB hN _) hN (p φ) hs hw

theorem sym_of_pull {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (jX : X ⟶ X) (jj : Y ⟶ Y) (φ : Y ⟶ X)
    (e : jj ≫ φ = φ ≫ jX) (hs : LBIso ((L.pull jX).pull φ) (L.pull φ)) :
    LBIso ((L.pull φ).pull jj) (L.pull φ) := by
  have p := fun {Z : Scheme.{0}} (f : Z ⟶ X) => pull_isLB hL f
  have h1 : LBIso ((L.pull φ).pull jj) (L.pull (jj ≫ φ)) := (FibreNef.lbIso_pull_comp hL φ jj).symm
  have h2 : LBIso (L.pull (jj ≫ φ)) ((L.pull jX).pull φ) := by
    rw [e]; exact FibreNef.lbIso_pull_comp hL jX φ
  refine LBIso.trans (pull_isLB (p φ) _) (p _) (p φ) h1 ?_
  exact LBIso.trans (p _) (pull_isLB (p jX) _) (p φ) h2 hs

theorem spread_to_fg_subfield : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (k₀ : IntermediateField ℚ K) (A₀ : Over (Sp k₀)) (_ : GrpObj A₀) (π : A.left ⟶ A₀.left) (L₀ M₀ : LB A₀.left), k₀.FG ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap (algebraMap k₀ K)) π ∧ L₀.IsLB ∧ M₀.IsLB ∧ RelAmple A₀ L₀ ∧ RelAmple A₀ M₀ ∧ LBIso (L₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) L₀ ∧ LBIso (M₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) M₀ ∧ LBIso L (L₀.pull π) ∧ LBIso M (M₀.pull π) := by
  intro K _ _ A _ hA L M hL hM hLa hMa hLs hMs
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ A.left A.hom
    (GlobalTheory.ProjSpace.isProjOver_of_relAmple hLa)
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K₀ (Over.mk p₀) A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ A.left p₀ A.hom φ L hL sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ A.left p₀ A.hom φ M hM sq
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have sub : ∀ t : Finset K, t ⊆ s → (t : Set K) ⊆ K₁ := fun t ht =>
    PolCountableDescent.subset_closure_of_subset ht
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : A.left ⟶ A₁.left := sq₁.lift φ (A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, PolCountableDescent.spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ K₁ h (sub s₁ (fun y hy => by simp [s, hy])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hLL⟩ := H₂ K₁ h (sub s₂ (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨M₁, hM₁, hMM⟩ := H₃ K₁ h (sub s₃ (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨hab₁, -⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₁ K K₁.subtype A₁ A ψ hG hA
  have : IsProper A₁.hom := hab₁.proper
  have e₁ := PolDescent.inv_left_comp hG
  have symL := sym_transfer hL₁ hL _ _ ψ e₁ hLL hLs
  have symM := sym_transfer hM₁ hM _ _ ψ e₁ hMM hMs
  obtain ⟨s₄, H₄⟩ := lbIso_descends_to_subfield_containing_finset K₁ K K₁.subtype A₁ A ψ _ L₁ hG.1
    inferInstance inferInstance (pull_isLB hL₁ _) hL₁ symL
  obtain ⟨s₅, H₅⟩ := lbIso_descends_to_subfield_containing_finset K₁ K K₁.subtype A₁ A ψ _ M₁ hG.1
    inferInstance inferInstance (pull_isLB hM₁ _) hM₁ symM
  let t : Finset K := s ∪ s₄ ∪ s₅
  let k₀ : IntermediateField ℚ K := IntermediateField.adjoin ℚ (t : Set K)
  let K₂ : Subfield K := k₀.toSubfield
  have mem₂ : ∀ y ∈ t, y ∈ K₂ := fun y hy => IntermediateField.subset_adjoin ℚ (t : Set K) hy
  have h₁₂ : K₁ ≤ K₂ := Subfield.closure_le.2 (fun y hy => mem₂ y (by simp [t, Finset.mem_coe.1 hy]))
  have rng : ∀ u : Finset K, u ⊆ t → (u : Set K) ⊆ Set.range K₂.subtype := fun u hu y hy =>
    ⟨⟨y, mem₂ y (hu hy)⟩, rfl⟩
  let inc₂ := spMap (Subfield.inclusion h₁₂)
  let A₂ : Over (Sp K₂) := (Over.pullback inc₂).obj A₁
  have hP : IsGrpPullback A₂ A₁ inc₂ (pullback.fst A₁.hom inc₂) := isGrpPullback_pullback A₁ inc₂
  let χ : A₂.left ⟶ A₁.left := pullback.fst A₁.hom inc₂
  let π : A.left ⟶ A₂.left := pullback.lift ψ (A.hom ≫ spMap K₂.subtype)
    (by rw [hψ₂, Category.assoc, PolCountableDescent.spMap_subtype_comp h₁₂])
  have hπ₁ : π ≫ χ = ψ := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ A₂.hom = A.hom ≫ spMap K₂.subtype := pullback.lift_snd _ _ _
  have hG₂ : IsGrpPullback A A₂ (spMap K₂.subtype) π :=
    IsGrpPullback.cancel hP (by rw [PolCountableDescent.spMap_subtype_comp h₁₂, hπ₁]; exact hG) hπ₂
  obtain ⟨hab₂, -⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₂ K K₂.subtype A₂ A π hG₂ hA
  have e₂ := PolDescent.inv_left_comp hP
  have symL₂ := H₄ K₂ (Subfield.inclusion h₁₂) K₂.subtype rfl (rng s₄ (fun y hy => by simp [t, hy]))
    A₂ χ hP.1
  have symM₂ := H₅ K₂ (Subfield.inclusion h₁₂) K₂.subtype rfl (rng s₅ (fun y hy => by simp [t, hy]))
    A₂ χ hP.1
  have isoL : LBIso L ((L₁.pull χ).pull π) := by
    refine LBIso.trans hL (pull_isLB hL₁ _) (pull_isLB (pull_isLB hL₁ _) _) hLL ?_
    rw [← hπ₁]; exact FibreNef.lbIso_pull_comp hL₁ χ π
  have isoM : LBIso M ((M₁.pull χ).pull π) := by
    refine LBIso.trans hM (pull_isLB hM₁ _) (pull_isLB (pull_isLB hM₁ _) _) hMM ?_
    rw [← hπ₁]; exact FibreNef.lbIso_pull_comp hM₁ χ π
  refine ⟨k₀, A₂, inferInstance, π, L₁.pull χ, M₁.pull χ, ⟨t, rfl⟩, hab₂, hG₂, pull_isLB hL₁ _,
    pull_isLB hM₁ _, ?_, ?_, sym_of_pull hL₁ _ _ χ e₂ symL₂, sym_of_pull hM₁ _ _ χ e₂ symM₂, isoL, isoM⟩
  · exact AmpleDescent.relAmple_of_fieldExtension K₂ K K₂.subtype A₂ A π _ L hab₂ hG₂ (pull_isLB hL₁ _) hL isoL hLa
  · exact AmpleDescent.relAmple_of_fieldExtension K₂ K K₂.subtype A₂ A π _ M hab₂ hG₂ (pull_isLB hM₁ _) hM isoM hMa

end GlobalTheory.AbFGSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AlgClosedHomDescent

theorem hom_descends : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (B B' : Over (Sp Ω)) [GrpObj B] [GrpObj B'] (b : B.left ⟶ A.left) (b' : B'.left ⟶ A'.left), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback B A (spMap j) b → IsGrpPullback B' A' (spMap j) b' → ∀ f : B ⟶ B', IsMonHom f → ∃ f₀ : A ⟶ A', IsMonHom f₀ ∧ b ≫ f₀.left = f.left ≫ b' := by
  intro K Ω _ _ _ _ j A A' _ _ B B' _ _ b b' hA hA' hB hB' f hf
  let Ωb := AlgebraicClosure Ω
  let io : Ω →+* Ωb := algebraMap Ω Ωb
  letI : Algebra K Ωb := (io.comp j).toAlgebra
  have hJ : spMap io ≫ spMap j = spMap (algebraMap K Ωb) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  let P := (Over.pullback (spMap (algebraMap K Ωb))).obj A
  let P' := (Over.pullback (spMap (algebraMap K Ωb))).obj A'
  have hP : IsGrpPullback P A (spMap (algebraMap K Ωb)) (pullback.fst _ _) := isGrpPullback_pullback A _
  have hP' : IsGrpPullback P' A' (spMap (algebraMap K Ωb)) (pullback.fst _ _) := isGrpPullback_pullback A' _

  let u : P.left ⟶ B.left := hB.1.lift (pullback.fst A.hom _) (pullback.snd A.hom _ ≫ spMap io)
    (by rw [pullback.condition, Category.assoc, hJ])
  let u' : P'.left ⟶ B'.left := hB'.1.lift (pullback.fst A'.hom _) (pullback.snd A'.hom _ ≫ spMap io)
    (by rw [pullback.condition, Category.assoc, hJ])
  have hu₁ : u ≫ b = pullback.fst A.hom _ := hB.1.lift_fst _ _ _
  have hu₂ : u ≫ B.hom = P.hom ≫ spMap io := hB.1.lift_snd _ _ _
  have hu₁' : u' ≫ b' = pullback.fst A'.hom _ := hB'.1.lift_fst _ _ _
  have hu₂' : u' ≫ B'.hom = P'.hom ≫ spMap io := hB'.1.lift_snd _ _ _
  have hPB : IsGrpPullback P B (spMap io) u :=
    hB.cancel (hP.congr hJ.symm hu₁.symm) hu₂
  have hPB' : IsGrpPullback P' B' (spMap io) u' :=
    hB'.cancel (hP'.congr hJ.symm hu₁'.symm) hu₂'

  let fb : P ⟶ P' := Over.homMk (pullback.lift (u ≫ f.left ≫ b') (pullback.snd A.hom _) (by
      rw [Category.assoc, Category.assoc, hB'.1.w, ← Category.assoc f.left, Over.w f, ← Category.assoc, hu₂,
        Category.assoc, hJ]; rfl))
    (pullback.lift_snd _ _ _)
  have hfb₁ : fb.left ≫ pullback.fst A'.hom _ = u ≫ f.left ≫ b' := pullback.lift_fst _ _ _
  have hfb₂ : fb.left ≫ P'.hom = P.hom := Over.w fb
  have hfbu : u ≫ f.left = fb.left ≫ u' := by
    apply hB'.1.hom_ext
    · rw [Category.assoc, Category.assoc, hu₁', hfb₁]
    · rw [Category.assoc, Over.w f, hu₂, Category.assoc, hu₂', ← Category.assoc, hfb₂]
  have hfbm : IsMonHom fb :=
    ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff Ω Ωb io).2 B B' P P' u u' f fb hPB hPB' hfbu).2 hf

  obtain ⟨g, hg, hge⟩ := _root_.GlobalTheory.ChowRigid.chow_rigidity K Ωb A A' hA hA' fb hfbm
  let L := algebraicClosure K Ωb
  have hbij : Function.Bijective (algebraMap K L) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsIso (CommRingCat.ofHom (algebraMap K L)) := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  haveI : IsIso (spMap (algebraMap K L)) := by unfold spMap; infer_instance
  let q := pullback.fst A.hom (spMap (algebraMap K L))
  let q' := pullback.fst A'.hom (spMap (algebraMap K L))

  let f₀ : A ⟶ A' := Over.homMk (inv q ≫ g.left ≫ q') (by
    have hg' : g.left ≫ pullback.snd A'.hom (spMap (algebraMap K L)) = pullback.snd A.hom _ := Over.w g
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc g.left, hg', ← pullback.condition,
      IsIso.inv_hom_id_assoc])
  have hq : q ≫ f₀.left = g.left ≫ q' := by
    show q ≫ inv q ≫ g.left ≫ q' = _
    rw [IsIso.hom_inv_id_assoc]
  have hf₀ : IsMonHom f₀ :=
    ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K L (algebraMap K L)).2 A A' _ _ q q' f₀ g
      (isGrpPullback_pullback A _) (isGrpPullback_pullback A' _) hq).1 hg
  refine ⟨f₀, hf₀, ?_⟩
  have hepi : Epi u := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff Ω Ωb io).1 B.left P.left B.hom P.hom u hPB.1).1
  rw [← cancel_epi u, ← Category.assoc, hu₁, ← GlobalTheory.Spread.bcMap_fst A.hom L.val, Category.assoc, hq, hge, hfb₁]

end GlobalTheory.AlgClosedHomDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionRingHomExtPadicAlgClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.AdicExt

def ballIdeal {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (φ : R →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (c : ℝ) (hc : 0 ≤ c) : Ideal R where
  carrier := {x | ‖φ x‖ ≤ c}
  zero_mem' := by simpa using hc
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  smul_mem' := fun a b hb => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb

theorem mem_ballIdeal {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] {φ : R →+* K}
    {hφ : ∀ x, ‖φ x‖ ≤ 1} {c : ℝ} {hc : 0 ≤ c} {x : R} : x ∈ ballIdeal φ hφ c hc ↔ ‖φ x‖ ≤ c := Iff.rfl

theorem exists_bound {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (φ : R →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (I : Ideal R) (hI : I.FG) (h : ∀ x ∈ I, ‖φ x‖ < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ n : ℕ, ∀ x ∈ I ^ n, ‖φ x‖ ≤ c ^ n := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨c, hc0, hc1, hs⟩ : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x ∈ s, ‖φ x‖ ≤ c := by
    refine ⟨(s.sup fun x => ‖φ x‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun x hx => ?_⟩
    · have : (s.sup fun x => ‖φ x‖₊ : NNReal) < 1 :=
        (Finset.sup_lt_iff (by simp)).2 fun x hx => h x (Ideal.subset_span hx)
      exact_mod_cast this
    · have : ‖φ x‖₊ ≤ (s.sup fun x => ‖φ x‖₊ : NNReal) := Finset.le_sup (f := fun x => ‖φ x‖₊) hx
      exact_mod_cast this
  have h1 : Ideal.span (s : Set R) ≤ ballIdeal φ hφ c hc0 := Ideal.span_le.2 fun x hx => hs x hx
  refine ⟨c, hc0, hc1, fun n => ?_⟩
  induction n with
  | zero => intro x _; simpa using hφ x
  | succ n ih =>
    have : Ideal.span (s : Set R) ^ (n + 1) ≤ ballIdeal φ hφ (c ^ (n + 1)) (pow_nonneg hc0 _) := by
      rw [pow_succ, Ideal.mul_le]
      intro a ha b hb
      rw [mem_ballIdeal, map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih a ha) (h1 hb) (norm_nonneg _) (pow_nonneg hc0 _)
    exact fun x hx => this hx

theorem norm_le_of_mem_smul_top {R A K : Type} [CommRing R] [CommRing A] [Algebra R A] [NormedField K]
    [IsUltrametricDist K] (F : A →+* K) (hF : ∀ x, ‖F x‖ ≤ 1) (J : Ideal R) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x ∈ J, ‖F (algebraMap R A x)‖ ≤ c) (y : A) (hy : y ∈ J • (⊤ : Submodule R A)) :
    ‖F y‖ ≤ c := by
  refine Submodule.smul_induction_on (p := fun y => ‖F y‖ ≤ c) hy (fun a ha w _ => ?_) (fun a b ha hb => ?_)
  · rw [Algebra.smul_def, map_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hF w)).trans (h a ha)
  · rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem ringHom_ext_of_norm {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K]
    (I : Ideal R) (hI : I.FG) (F G : AdicCompletion I R →+* K) (hF : ∀ x, ‖F x‖ ≤ 1) (hG : ∀ x, ‖G x‖ ≤ 1)
    (h : ∀ x ∈ I, ‖F (algebraMap R _ x)‖ < 1) (e : ∀ a, F (algebraMap R _ a) = G (algebraMap R _ a)) :
    F = G := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_bound (F.comp (algebraMap R _)) (fun x => hF _) I hI h
  ext r
  have key : ∀ n : ℕ, ‖F r - G r‖ ≤ c ^ n := by
    intro n
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I R n r)
    have hm : r - algebraMap R _ a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub, ← ha, sub_eq_zero]
      rfl
    have h1 := norm_le_of_mem_smul_top F hF _ _ (pow_nonneg hc0 n) (hc n) _ hm
    have h2 := norm_le_of_mem_smul_top G hG _ _ (pow_nonneg hc0 n)
      (fun x hx => by rw [← e]; exact hc n x hx) _ hm
    have : F r - G r = F (r - algebraMap R _ a) + - G (r - algebraMap R _ a) := by
      rw [map_sub, map_sub, e]; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1) key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem completion_ringHom_ext : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (p : ℕ) [Fact p.Prime] (f g : AdicCompletion (maximalIdeal O) O →+* OO p), IsLocalHom (f.comp (algebraMap O _)) → (∀ a, f (algebraMap O _ a) = g (algebraMap O _ a)) → f = g := by
  intro O _ _ _ p _ f g hf e
  have := ringHom_ext_of_norm (maximalIdeal O) (maximalIdeal O).fg_of_isNoetherianRing
    ((OO p).subtype.comp f) ((OO p).subtype.comp g)
    (fun x => (mem_OO_iff _).1 (f x).2) (fun x => (mem_OO_iff _).1 (g x).2)
    (fun x hx => (not_isUnit_OO_iff _).1 fun hu =>
      (IsLocalRing.mem_maximalIdeal x).1 hx (hf.map_nonunit x hu))
    (fun a => congrArg Subtype.val (e a))
  ext r
  exact RingHom.congr_fun this r

end GlobalTheory.AdicExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosurePointFactorsThroughFiniteLocalSubalgebStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algClosurePoint_factors_through_finite_local_subalgebra : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Z : Scheme.{0}) (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z), k ≫ π = (TF (R := R) (Kb R)).hom → ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧ ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k := by
  first | exact @GlobalTheory.Mum.finpt_factor | exact GlobalTheory.Mum.finpt_factor | (intros; apply GlobalTheory.Mum.finpt_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseOfIsImmersionProjectiveCompleteNoeth
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_of_isImmersion_isProjOver :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
      ∀ (W P : Scheme.{0}) (j : W ⟶ P) (p : P ⟶ Spec (CommRingCat.of R)),
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p → IsImmersion j → Alg (j ≫ p) I := by
  intro R _ _ I hI W P j p hp hj
  have hpb : IsProjBy p := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver p).2 hp
  have hprop : IsProper p := GlobalTheory.AbLaw.isProper_of_isProjBy R P p hpb
  have hA : Alg p I := _root_.GlobalTheory.FormalAlg.alg_of_isProjBy R I hI P p hpb
  have hjac : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  have hsep : IsSeparated p := inferInstance
  have hU : Alg (j.coborderRange.ι ≫ p) I :=
    _root_.GlobalTheory.FormalAlg.alg_comp_of_isOpenImmersion R I hjac P _ p j.coborderRange.ι hsep inferInstance hA
  have hsepU : IsSeparated (j.coborderRange.ι ≫ p) := inferInstance
  have hW := _root_.GlobalTheory.FormalAlg.alg_of_isClosedImmersion R I _ W (j.coborderRange.ι ≫ p) j.liftCoborder hsepU inferInstance hU
  rwa [← Category.assoc, Scheme.Hom.liftCoborder_ι] at hW

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSurfaceFibreIsProjOverZmodDimLeOneStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (X := (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  first | exact @GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le | exact GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le | (intros; apply GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValueStatement
section
alias GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue :=
  GlobalTheory.PtExt.Dat.lift_coc
end

