module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifLeaves
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisAltTail
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusEndChar

theorem main : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (f : G ⟶ G), IsMonHom f → letI := E.addCommGroup; ∃! ρ : E.X →+ E.X, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ f ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ χ) := by
  intro k _ G _ _ E f hf
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  haveI : IsMonHom E.q := E.q_hom
  haveI : IsMonHom E.i := E.i_hom
  haveI : IsProper E.B.hom := E.isAbelian.proper
  haveI : ConnectedSpace (Sp k) := by
    have : PreconnectedSpace (PrimeSpectrum k) := by
      refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint k) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
      exact (IsLocalRing.specializes_closedPoint y).mem_closure
    exact (⟨inferInstance⟩ : ConnectedSpace (PrimeSpectrum k))
  have hk : E.i ≫ f ≫ E.q = toUnit _ ≫ η[E.B] :=
    splitTorus_hom_proper_trivial_local k E.X E.B (E.i ≫ f ≫ E.q) inferInstance
  let τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X :=
    E.isKernel.lift (E.i ≫ f) (toUnit _) (by rw [Category.assoc, hk])
  have hτ : τ ≫ E.i = E.i ≫ f := E.isKernel.lift_fst _ _ _
  have hmono : Mono E.i := E.isKernel.mono_fst_of_mono
  have hτm : IsMonHom τ := by
    constructor
    · rw [← cancel_mono E.i, Category.assoc, hτ, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono E.i, Category.assoc, Category.assoc, hτ, IsMonHom.mul_hom_assoc (f := E.i),
        IsMonHom.mul_hom (f := f), IsMonHom.mul_hom (f := E.i), tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hτ]
  obtain ⟨ρ, hρ⟩ := SplitTorusHom.exists_addMonoidHom (S := Sp k) τ
  refine ⟨ρ, ⟨τ, hτ, fun χ => Units.ext ?_⟩, ?_⟩
  · rw [chV_val, hρ]
  · rintro ρ' ⟨τ', hτ', hρ'⟩
    have hττ : τ' = τ := by rw [← cancel_mono E.i, hτ', hτ]
    subst hττ
    ext χ
    apply SplitTorusHom.charUnit_injective (S := Sp k)
    rw [← hρ', chV_val, hρ]

end GlobalTheory.TorusEndChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFlatPointAtGenericPoints
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem injective_of_flat_of_range_subset_genericPoints :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (X : Scheme.{0}) (s : X ⟶ Sp R) (x : Sp K ⟶ X) (β : R →+* K), Flat s → Set.range x ⊆ genericPoints X → x ≫ s = spMap β → Function.Injective β := by
  intro R K _ _ _ X s x β hs hx hxs
  set pt : Sp K := IsLocalRing.closedPoint K with hpt
  have hp : x pt ∈ genericPoints X := hx ⟨_, rfl⟩
  let g₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hg₀ : g₀ ⤳ s (x pt) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s hg₀
  have h₁ : closure ({x pt} : Set X) ⊆ closure {y} :=
    specializes_iff_closure_subset.mp hy
  have h₂ : closure ({y} : Set X) ⊆ closure {x pt} :=
    hp.2 isIrreducible_singleton.closure h₁
  have hyx : y = x pt :=
    (hy.antisymm (specializes_iff_closure_subset.mpr h₂)).eq
  have h₃ : (x ≫ s) pt = g₀ := by
    rw [Scheme.Hom.comp_apply, ← hyx, e]
  rw [hxs] at h₃
  have h₄ : (spMap β pt).asIdeal = RingHom.ker β := by
    show Ideal.comap β (IsLocalRing.maximalIdeal K) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  rw [h₃] at h₄
  exact (RingHom.injective_iff_ker_eq_bot β).mpr h₄.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBasOfPreimageEq
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isBas_of_preimage_eq (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i] (C : Type)
    [Category.{0} C] (V : C → X.Opens) (V₀ : C → X₀.Opens) (hV : ∀ T, i ⁻¹ᵁ V T = V₀ T) (h : IsBas V₀) :
    IsBas V := by
  have hle : ∀ (t : C) (U : X.Opens), V₀ t ≤ i ⁻¹ᵁ U → V t ≤ U := by
    intro t U htU z hz
    obtain ⟨w, rfl⟩ := i.surjective z
    have hw : w ∈ V₀ t := by rw [← hV t]; exact hz
    exact htU hw
  have hmem : ∀ (t : C) (y : X₀), y ∈ V₀ t → i y ∈ V t := by
    intro t y hy
    rw [← hV t] at hy
    exact hy
  have hmem' : ∀ (t : C) (y : X₀), i y ∈ V t → y ∈ V₀ t := by
    intro t y hy
    rw [← hV t]
    exact hy
  refine ⟨fun x U hx ↦ ?_, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t, hyt, htU⟩ := h.1 y (i ⁻¹ᵁ U) hx
    exact ⟨t, hmem t y hyt, hle t U htU⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t₃, a₁, a₂, hy₃, h₃U⟩ := h.2 t₁ t₂ y (i ⁻¹ᵁ U) hx (hmem' t₁ y h₁) (hmem' t₂ y h₂)
    exact ⟨t₃, a₁, a₂, hmem t₃ y hy₃, hle t₃ U h₃U⟩

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolToBaseChangeComplexIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem isHolTo_bc_iff : ∀ (R : Type) [CommRing R] (σ : R →+* ℂ) (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp ℂ)
    (f : X' ⟶ X), IsPullback f s' s (spMap σ) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V)
    (y : V → (Sp ℂ ⟶ X')), (∀ b ∈ B, y b ≫ s' = spMap (RingHom.id ℂ)) →
    (IsHolTo B y ↔ IsHolTo B (fun b => y b ≫ f)) := by
  intro R _ σ X X' s s' f H V _ _ B y hy
  refine ⟨fun h => GlobalTheory.HolFibre.isHolTo_comp h f, fun h => ?_⟩
  have hB : IsOpen B := by
    have := (h ⊤ 0).1
    simpa using this
  refine GlobalTheory.HolFibre.isHolTo_of_isPullback H h ?_
  intro U g
  have hc := GlobalTheory.HolFibre.isHolTo_const (E := V) hB (spMap (RingHom.id ℂ)) U g
  have e : {b ∈ B | ⊤ ≤ (y b ≫ s') ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ (spMap (RingHom.id ℂ)) ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [hy b hb]
  rw [e]
  exact ⟨hc.1, hc.2.congr fun b hb => by simp only [hy b hb.1]⟩

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdealThickeningImmersionOfIsPullbackSquareZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

theorem appLE_comp_spMap_hom (R C : Type) [CommRing R] [CommRing C] (σ : R →+* C) (X : Scheme.{0})
    (s : X ⟶ Sp C) (U : X.Opens) :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (s ≫ spMap σ).appLE ⊤ U le_top).hom =
      (algebraMap C (Sec s U)).comp σ := by
  ext r
  have k1 := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)).hom r)
  have k2 := congr($(Scheme.Hom.comp_appLE s (spMap σ) ⊤ U le_top).hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
  refine k2.trans ?_
  exact (congrArg (s.appLE ⊤ U le_top).hom k1).symm

theorem isThick_of_isPullback_quotient : ∀ (R C : Type) [CommRing R] [CommRing C] (σ : R →+* C) (J : Ideal R),
    J ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp C) (s₀ : X₀ ⟶ Sp (R ⧸ J)) (i : X₀ ⟶ X),
    IsPullback i s₀ (s ≫ spMap σ) (spMap (Ideal.Quotient.mk J)) → IsThick (J.map σ) s i := by
  intro R C _ _ σ J hJ X X₀ s s₀ i h
  have hβ : Function.Surjective (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := Ideal.Quotient.mk_surjective
  have hpo : ∀ U : X.affineOpens, IsPushout
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (s ≫ spMap σ).appLE ⊤ U.1 le_top)
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) (i.app U.1)
      ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv ≫ s₀.appLE ⊤ (i ⁻¹ᵁ U.1) le_top) := by
    intro U
    have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U.1) (UY := i ⁻¹ᵁ U.1) le_top
      le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
        (isAffineOpen_top _) U.2)
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  haveI := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk J))
    Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance
  · exact LiftSys.surjective_of_isPullback_sqZero (I := J) (by rw [hJ]; rfl) Ideal.Quotient.mk_surjective
      (Ideal.mk_ker) h
  · intro U
    have P := hpo U
    have htop := CommRingCat.closure_range_union_range_eq_top_of_isPushout P
    rw [← RingHom.range_eq_top, ← top_le_iff, ← htop, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨z, rfl⟩)
    · exact ⟨y, rfl⟩
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨_, congr($(P.w).hom r)⟩
  · intro U b
    have hk := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout (hpo U) hβ
    have hk' : RingHom.ker (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom = J := Ideal.mk_ker
    rw [hk', appLE_comp_spMap_hom] at hk
    rw [Ideal.map_map]
    exact RingHom.mem_ker.symm.trans (by rw [hk]; exact Iff.rfl)

end GlobalTheory.LBLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatOfInt
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh
variable {D : D7} {r g : ℕ}

theorem isMod_of (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (hm : Formalism.L2.Pj.ModelW W hr X)
    (hp : ∀ ρ, tauE D ρ ∈ X.Ψ) : IsMod W hr X := by
  have hpsi : ∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, h⟩ => h ▸ hp ρ⟩
    have h1 := (X.cmType τ).1 h
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.StdRat.tauE_cm D τ).2 (fun ⟨ρ, hρ⟩ => h1 (hρ ▸ hp ρ))
    exact ⟨ρ, hρ.symm⟩
  obtain ⟨ρ⟩ : Nonempty D.what₂.Tau := by
    by_contra hne
    have h := GlobalTheory.StdRat.tauE_cm D D.host.φ₀
    obtain ⟨ρ, -⟩ := h.2 (fun ⟨ρ, _⟩ => hne ⟨ρ⟩)
    exact hne ⟨ρ⟩
  refine ⟨hm, hpsi, ?_⟩
  have h1 := X.κ0_sign ⟨tauE D ρ, hp ρ⟩
  have h2 := xi_zero_im_pos D ρ
  rcases X.κ0_xi with h | h
  · rw [h, hm.2]; ring
  · exfalso
    rw [h, hm.2] at h1
    simp [map_ofNat] at h1
    linarith

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisLineBundleCechTensor
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isFrame_tens : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  intro X C _ V hV L L' u u' ⟨τ, hτg, hτf⟩ ⟨τ', hτ'g, hτ'f⟩
  dsimp only [IsFrame, IsGenOn, tens]
  refine ⟨fun T p ↦ res (inf_le_inf_left (V T) (inf_le_left : L.U p.1 ⊓ L'.U p.2 ≤ L.U p.1)) (τ T p.1) *
      res (inf_le_inf_left (V T) (inf_le_right : L.U p.1 ⊓ L'.U p.2 ≤ L'.U p.2)) (τ' T p.2), ?_, ?_⟩
  · intro T p q
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτg T p.1 q.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'g T p.2 q.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L.U p.1 ⊓ L.U q.1 := ⟨⟨hy.1.1, hy.1.2.1⟩, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L'.U p.2 ⊓ L'.U q.2 := ⟨⟨hy.1.1, hy.1.2.2⟩, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ L.U p.1 ⊓ L'.U p.2 ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.2, hy.2⟩
    have m4 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := hy.1
    have m5 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m3, gm_res (𝟙 X) y _ m4, gm_res (𝟙 X) y _ m5]
    rw [h1, h2]
    ac_rfl
  · intro T T' a p
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτf T T' a p.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'f T T' a p.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L.U p.1 := ⟨hy.1, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L'.U p.2 := ⟨hy.1, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := ⟨hV a hy.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m1, gm_res (𝟙 X) y _ m2, gm_res (𝟙 X) y _ m3]
    rw [h1, h2]
    ac_rfl

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisRestrictFinerOpens
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem res_res_frameRestrict {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isFrame_restrict : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) (C' : Type) [Category.{0} C'] (V' : C' → X.Opens) (hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T) (H : C' ⥤ C) (hH : ∀ T, V' T ≤ V (H.obj T)), IsFrame L V hV u → IsFrame L V' hV' fun T T' a ↦ res (hH T') (u _ _ (H.map a)) := by
  intro X C _ V hV L u C' _ V' hV' H hH ⟨τ, hgen, hcomp⟩
  refine ⟨fun T m ↦ res (inf_le_inf_right (L.U m) (hH T)) (τ (H.obj T) m), fun T m m' ↦ ?_, fun T T' a m ↦ ?_⟩
  · have key := congrArg (res (inf_le_inf_right (L.U m') (inf_le_inf_right (L.U m) (hH T)))) (hgen (H.obj T) m m')
    simp only [map_mul, res_res_frameRestrict] at key
    simpa only [map_mul, res_res_frameRestrict] using key
  · have key := congrArg (res (inf_le_inf_right (L.U m) (hH T'))) (hcomp (H.obj T) (H.obj T') (H.map a) m)
    simp only [map_mul, res_res_frameRestrict] at key
    simpa only [map_mul, res_res_frameRestrict] using key

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiplicativeOneCocycleOpensOfIsLineBundleFra
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.FrameCoc

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(X, U)ˣ) :
    res h (res h' x) = res (h.trans h') x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isCoc_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → IsFrame L V hV u → IsCoc V hV u := by
  intro X C _ V hV L u hL hF T T' T'' a b
  obtain ⟨τ, -, hτ⟩ := hF
  have key : ∀ m : L.ι, res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (u T T'' (a ≫ b)) =
      res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (res (hV b) (u T T' a) * u T' T'' b) := by
    intro m
    have h1 := hτ T T'' (a ≫ b) m
    have h2 := congrArg (res (inf_le_inf_right (L.U m) (hV b))) (hτ T T' a m)
    have h3 := hτ T' T'' b m
    rw [res_res', map_mul, res_res', h3] at h2
    rw [h1] at h2
    apply mul_right_cancel (b := τ T'' m)
    rw [h2, map_mul, res_res', ← _root_.mul_assoc]
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun m => V T'' ⊓ L.U m) (V T'') (fun m => homOfLE inf_le_left) ?_ _ _ ?_
  · rw [← inf_iSup_eq, hL.cover, inf_top_eq]
  · intro m
    exact congrArg Units.val (key m)

end GlobalTheory.LBObs.FrameCoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinear
section
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PELU

theorem isPeriod_comp_realLinear {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ}
    (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (M : Matrix (Fin g) (Fin g) ℂ) (hP₀ : IsPeriod D ρ P₀) (hR : Function.Injective R)
    (hRρ : ∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re)
    (hE : ∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) :
    IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP₀
  have hsurj : Function.Surjective R := LinearMap.injective_iff_surjective.mp hR
  let e : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo R hR
  have he : ∀ z, e z = R z := fun z => rfl
  let ec := e.toContinuousLinearEquiv
  refine ⟨?_, ?_, ?_, ?_, M, hM, hpos, ?_⟩
  · intro a x
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, h1, hRρ]
  · exact hR.comp h2
  · let f : (R.toAddMonoidHom.comp P₀).range → P₀.range := fun z =>
      ⟨ec.symm z.1, by
        obtain ⟨z, x, rfl⟩ := z
        exact ⟨x, (e.symm_apply_apply (P₀ x)).symm⟩⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact ec.symm.continuous.comp continuous_subtype_val
    have hi : Function.Injective f := by
      intro z w h
      apply Subtype.ext
      have := congrArg (fun u : P₀.range => ec u.1) h
      simpa [f] using this
    exact DiscreteTopology.of_continuous_injective hf hi
  · have : Set.range (R.toAddMonoidHom.comp P₀) = R '' Set.range P₀ := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact hsurj
  · intro x y
    exact hE x y

end GlobalTheory.PELU
end

