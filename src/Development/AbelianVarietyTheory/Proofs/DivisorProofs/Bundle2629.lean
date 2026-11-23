module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2544
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsSurjectiveOfLargerAlgClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabels_surjective_of_larger_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (N : ℕ), 1 ≤ N → ∀ (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)), LabExt em lab lab' → (∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x) → ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x := by
  first | exact @GlobalTheory.Mum.Desc.lab_onto_of_labExt | exact GlobalTheory.Mum.Desc.lab_onto_of_labExt | (intros; apply GlobalTheory.Mum.Desc.lab_onto_of_labExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfPairExistsTorsionInjectiveUpToEquiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif J D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → (∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, QkToAkU U.toUnifPre F k p x ∧ x ^ k = 1) ∧ ∀ (p p' : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x → QkPt.Equiv D.toPre F p p' := by
  first | exact @GlobalTheory.TInj.torsPt_exists_inj | exact GlobalTheory.TInj.torsPt_exists_inj | (intros; apply GlobalTheory.TInj.torsPt_exists_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFraStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_translate_liesOver_product_torsionFrame : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (w₀ : W0 𝔪.U.toUnifPre), w₀.IsGen → ∀ (ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), ρA.IsGen → ∀ (x₁ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e₁ : FrAt x₁), IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) x₁ e₁ → ∀ (g₁ : GtPtF 𝔪.D.toPre (FractionRing V)) (w₁ : Frm 𝔪.D.toPre (FractionRing V) 1 g₁.b), (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₁ o ∧ o.IsZero) → w₁.IsGen → 𝔪.Over' w₀ g₁ w₁ x₁ e₁ → ∀ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 → ∀ (g₀ : GtPtF 𝔪.D.toPre (FractionRing V)), IsTor χ g₀ → ∀ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (xτ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 → p.g = g₀ → QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p xτ → ∀ (g₂ : GtPtF 𝔪.D.toPre (FractionRing V)), g₁.IsAdd g₀ g₂ → ∀ (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b), (∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w₁ (𝟙 _) z J) → ∀ (x₂ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), x₂ = x₁ * xτ → ∃ e₂ : FrAt x₂, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) x₂ e₂ ∧ 𝔪.Over' w₀ g₂ w₂ x₂ e₂ := by
  first | exact @GlobalTheory.Poinc.Tors.Translate.over_translate | exact GlobalTheory.Poinc.Tors.Translate.over_translate | (intros; apply GlobalTheory.Poinc.Tors.Translate.over_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointSectionAlongSpreadingTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.SpreadTorSection

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  show Spec.map (𝟙 _) = _
  exact Spec.map_id _

theorem spMap_injective' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have := congrArg (fun u => (Spec.preimage u).hom) h
  simpa [spMap, Spec.preimage_map] using this

theorem range_sub {W κ : Type} [CommRing W] [IsLocalRing W] [Field κ] {B : Scheme.{0}} (ψ : Sp W ⟶ B)
    (Wo : B.Opens) (c : W →+* κ) [IsLocalHom c] (y : Sp κ ⟶ Wo.toScheme) (e : spMap c ≫ ψ = y ≫ Wo.ι) :
    Set.range ψ ⊆ Set.range Wo.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨p, hp⟩ : ∃ p : Sp κ, (spMap c p : PrimeSpectrum W) = closedPoint W :=
    ⟨closedPoint κ, comap_closedPoint c⟩
  have hx : x ⤳ spMap c p := by
    have := specializes_closedPoint (R := W) x
    rw [← hp] at this
    exact this
  refine (hx.map ψ.continuous).mem_open Wo.isOpen ?_
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  have := Set.mem_range_self (f := Wo.ι) (y p)
  rwa [Scheme.Opens.range_ι] at this

def powChar {A X : Type} [CommRing A] [AddCommGroup X] (u : Aˣ) (c : X →+ ℤ) : Multiplicative X →* Aˣ :=
  (zpowersHom Aˣ u).comp (AddMonoidHom.toMultiplicative c)

theorem powChar_apply {A X : Type} [CommRing A] [AddCommGroup X] (u : Aˣ) (c : X →+ ℤ) (χ : Multiplicative X) :
    powChar u c χ = u ^ c (Multiplicative.toAdd χ) := rfl

theorem powChar_map {o A A' X : Type} [CommRing o] [CommRing A] [CommRing A'] [AddCommGroup X] (g : o →+* A)
    (f : A →+* A') (u : oˣ) (c : X →+ ℤ) (χ : Multiplicative X) :
    ((powChar (Units.map (f.comp g).toMonoidHom u) c χ : A'ˣ) : A') = f (powChar (Units.map g.toMonoidHom u) c χ) := by
  rw [powChar_apply, powChar_apply,
    show Units.map (f.comp g).toMonoidHom u = Units.map f.toMonoidHom (Units.map g.toMonoidHom u) from rfl,
    ← map_zpow]
  rfl

theorem powChar_val {o K X : Type} [CommRing o] [Field K] [AddCommGroup X] (g : o →+* K) (u : oˣ)
    (c : X →+ ℤ) (χ : Multiplicative X) :
    ((powChar (Units.map g.toMonoidHom u) c χ : Kˣ) : K) = g u ^ c (Multiplicative.toAdd χ) := by
  rw [powChar_apply, Units.val_zpow_eq_zpow_val]; rfl

theorem bc_point {W L X : Type} [CommRing W] [CommRing L] [AddCommGroup X] (f : W →+* L)
    {GW : Over (Sp W)} [GrpObj GW] {GLf : Over (Sp L)} [GrpObj GLf] {n : GLf.left ⟶ GW.left}
    (hn : IsGrpPullback GLf GW (spMap f) n) (j : splitTorus (Sp W) X ⟶ GW)
    (τW : Multiplicative X →* Wˣ) (τL : Multiplicative X →* Lˣ) (hτ : ∀ χ, (τL χ : L) = f (τW χ : W))
    (zW : Over.mk (spMap (RingHom.id W)) ⟶ splitTorus (Sp W) X)
    (hzW : ∀ χ, GlobalTheory.UU.chV zW χ = unitOn (τW (Multiplicative.ofAdd χ)))
    (zL : Over.mk (spMap (RingHom.id L)) ⟶ splitTorus (Sp L) X)
    (hzL : ∀ χ, GlobalTheory.UU.chV zL χ = unitOn (τL (Multiplicative.ofAdd χ))) :
    spMap f ≫ (zW ≫ j).left = (zL ≫ GlobalTheory.TorusPart.pullTorus hn j).left ≫ n := by
  have key : zL.left ≫ GlobalTheory.SplitTorus.bcMap (spMap f) X = spMap f ≫ zW.left := by
    refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w zL, Category.assoc, Over.w zW]
      change spMap (RingHom.id L) ≫ spMap f = spMap f ≫ spMap (RingHom.id W)
      rw [spMap_id', spMap_id', Category.id_comp, Category.comp_id]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
        Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      have e1 := (GlobalTheory.UU.chV_val zL χ).symm.trans (congrArg Units.val (hzL χ))
      have e2 := (GlobalTheory.UU.chV_val zW χ).symm.trans (congrArg Units.val (hzW χ))
      exact e1.trans ((GlobalTheory.ToricOverField.unitOn_val_map f _ _ (hτ _)).trans (congrArg _ e2.symm))
  rw [Over.comp_left, Over.comp_left, Category.assoc, GlobalTheory.TorusPart.pullTorus_left,
    ← Category.assoc zL.left, key, Category.assoc]

theorem trait_section : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁] (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂] (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left) (ρ : D₂.toPre.X →+ D₁.toPre.X), Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (c : D₁.toPre.X →+ ℤ), (∀ (κ : Type) [Field κ] (b : V₁ →+* κ) (hb : ∀ y ∈ maximalIdeal V₁ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G₁.left) (hm : IsGrpPullback Gκ G₁ (spMap b) m) (τ : Multiplicative D₁.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₁ ζ) ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₁.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ ξ₁' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb hm).left ≫ m ≫ β₁) → ∃ (κ : Type) (_ : Field κ) (b : V₂ →+* κ) (hb : ∀ y ∈ maximalIdeal V₂ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) (_ : GrpObj Gκ) (m : Gκ.left ⟶ G₂.left) (hm : IsGrpPullback Gκ G₂ (spMap b) m) (τ : Multiplicative D₂.toPre.X →* κˣ) (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₂.toPre.X), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₂ ζ) ^ (c.comp ρ) χ) ∧ (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) ∧ spMap b ≫ ξ₂' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₂.gt 0) hb hm).left ≫ m ≫ β₂ := by
  intro B H _ _ hH V₁ _ _ _ G₁ _ _ D₁ A₁ U₁ ξ₁ β₁ V₂ _ _ _ G₂ _ _ D₂ A₂ U₂ ξ₂ β₂ ρ hS o _ s o₁ o₂ hs₁ hs₂ k ζ hk hζ
    Wo h ξ₁' ξ₂' hh hξ₁ hξ₂ c hyp
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c', b₂, hb₂, Gκ, _, m, hm,
    m₂, hm₂, hψ, _, hα, hc', hαψ, hc'ψ, hnφ, hmφ, hjn, hjm⟩ := hS
  haveI := hc'

  have hrange : Set.range ψ ⊆ Set.range Wo.ι :=
    range_sub ψ Wo c' (spMap b₂ ≫ ξ₂') (by rw [hc'ψ, Category.assoc, hξ₂])
  let ψ' := IsOpenImmersion.lift Wo.ι ψ hrange
  have hψ' : ψ' ≫ Wo.ι = ψ := IsOpenImmersion.lift_fac _ _ _
  have e₁ : spMap α ≫ ψ' = spMap b₁ ≫ ξ₁' := by
    rw [← cancel_mono Wo.ι, Category.assoc, hψ', hαψ, Category.assoc, hξ₁]
  have e₂ : spMap c' ≫ ψ' = spMap b₂ ≫ ξ₂' := by
    rw [← cancel_mono Wo.ι, Category.assoc, hψ', hc'ψ, Category.assoc, hξ₂]

  let oW : o →+* W := (Spec.preimage (ψ ≫ s)).hom
  have hoW : spMap oW = ψ ≫ s := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (ψ ≫ s)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have ho₁ : α.comp oW = b₁.comp o₁ := spMap_injective' (by
    rw [spMap_comp', spMap_comp', hoW, ← Category.assoc, hαψ, Category.assoc, hs₁])
  have ho₂ : c'.comp oW = b₂.comp o₂ := spMap_injective' (by
    rw [spMap_comp', spMap_comp', hoW, ← Category.assoc, hc'ψ, Category.assoc, hs₂])

  have hζu : IsUnit ζ := IsUnit.of_pow_eq_one hζ (by omega)
  let u := hζu.unit
  have hu : (u : o) = ζ := hζu.unit_spec
  let τW := powChar (Units.map oW.toMonoidHom u) c
  obtain ⟨zW, hzW⟩ := GlobalTheory.ToricOverField.exists_point (RingHom.id W) τW
  let τΩ := powChar (Units.map (α.comp oW).toMonoidHom u) c
  obtain ⟨zΩ, hzΩ⟩ := GlobalTheory.ToricOverField.exists_point (RingHom.id Ω) τΩ
  have hτΩ : ∀ χ, (τΩ (Multiplicative.ofAdd χ) : Ω) = b₁ (o₁ ζ) ^ c χ := fun χ => by
    rw [powChar_val, ho₁, hu]; rfl
  have hyp₁ := hyp Ω b₁ hb₁ GΩ n₁ hn₁ τΩ hτΩ zΩ hzΩ
  have hbcΩ := bc_point α hn j τW τΩ (fun χ => powChar_map oW α u c χ) zW hzW zΩ hzΩ

  haveI : IsSeparated H.hom := hH.separated
  haveI : IsDominant (spMap α) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical α).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hα]; exact bot_le)⟩
  have hd : ψ' ≫ h = (zW ≫ j).left ≫ φW := by
    refine ext_of_isDominant_of_isSeparated H.hom ?_ (spMap α) ?_
    · simp only [Category.assoc]
      rw [hh, hψ', hψ.1.w, ← Category.assoc, Over.w (zW ≫ j)]
      change ψ = spMap (RingHom.id W) ≫ ψ
      rw [spMap_id', Category.id_comp]
    · rw [← Category.assoc, e₁, Category.assoc, hyp₁, ← hjn, ← hnφ, ← Category.assoc (spMap α), hbcΩ,
        Category.assoc]

  let τ₁ := powChar (Units.map (c'.comp oW).toMonoidHom u) c
  obtain ⟨zκ, hzκ⟩ := GlobalTheory.ToricOverField.exists_point (RingHom.id κ) τ₁
  have hbcκ := bc_point c' hm j τW τ₁ (fun χ => powChar_map oW c' u c χ) zW hzW zκ hzκ
  let τ₂ : Multiplicative D₂.toPre.X →* κˣ := powChar (Units.map (c'.comp oW).toMonoidHom u) (c.comp ρ)
  refine ⟨κ, inferInstance, b₂, hb₂, Gκ, inferInstance, m₂, hm₂, τ₂, zκ ≫ GlobalTheory.SplitTorus.torusMap _ ρ,
    fun χ => ?_, fun χ => ?_, ?_⟩
  · rw [powChar_val, ho₂, hu]; rfl
  · apply Units.ext
    rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
      GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
      ← GlobalTheory.UU.chV_val, hzκ]
    rfl
  · rw [← Category.assoc (spMap b₂), ← e₂, Category.assoc, hd, ← Category.assoc (spMap c'), hbcκ,
      Category.assoc zκ, ← hjm, ← hmφ]
    simp only [Category.assoc]

end GlobalTheory.SpreadTorSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapCommutesEndomorphisms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endU_gtTorus_comp {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (E : EndU U.toUnifPre) {κ : Type} [Field κ] {a : V →+* κ} (ha : ∀ x ∈ maximalIdeal V ^ (0 + 1), a x = 0)
    {G₀ : Over (Sp κ)} [GrpObj G₀] {φ : G₀.left ⟶ G.left} (h : IsGrpPullback G₀ G (spMap a) φ) (f₀ : G₀ ⟶ G₀)
    (hf : f₀.left ≫ φ = φ ≫ E.aG.left) :
    GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h ≫ f₀ =
      GlobalTheory.SplitTorus.torusMap (Sp κ) E.h ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h := by
  obtain ⟨t, ht, hi⟩ := E.i_lin 0
  have htm := GlobalTheory.Poinc.Eq8.eq_torusMap_of_torusEndOf E.h t ht
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift ha h
  have e : f₀.left ≫ GlobalTheory.TorusPart.thickLift ha h =
      GlobalTheory.TorusPart.thickLift ha h ≫ ((Over.pullback (thick V (maximalIdeal V) 0)).map E.aG).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, hf, Category.assoc]
      simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
        Over.w]
  have hc := GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e (U.gt 0).i
  unfold GlobalTheory.TorusPart.gtTorus
  rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

def pullEnd {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (u : G ⟶ G) : G' ⟶ G' :=
  Over.homMk (h.1.lift (φ ≫ u.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h.1.lift_snd _ _ _)

theorem pullEnd_left {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (u : G ⟶ G) : (pullEnd h u).left ≫ φ = φ ≫ u.left :=
  h.1.lift_fst _ _ _

theorem over_of_two_pullbacks {B S₁ : Scheme.{0}} {H : Over B} {G₁ : Over S₁} {X Y : Scheme.{0}} {ξ₁ : S₁ ⟶ B}
    {β₁ : G₁.left ⟶ H.left} (h₁ : IsPullback β₁ G₁.hom H.hom ξ₁) {φW : Y ⟶ H.left} {n : X ⟶ Y} {n₁ : X ⟶ G₁.left}
    {f₀ : X ⟶ X} {FW : Y ⟶ Y} {Fm : H.left ⟶ H.left} {a : G₁.left ⟶ G₁.left}
    (e1 : f₀ ≫ n = n ≫ FW) (e2 : FW ≫ φW = φW ≫ Fm) (e3 : n ≫ φW = n₁ ≫ β₁) (e4 : a ≫ β₁ = β₁ ≫ Fm)
    (e5 : a ≫ G₁.hom = G₁.hom) (e6 : f₀ ≫ n₁ ≫ G₁.hom = n₁ ≫ G₁.hom) : f₀ ≫ n₁ = n₁ ≫ a := by
  apply h₁.hom_ext
  · rw [Category.assoc, ← e3, ← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, e3, Category.assoc,
      Category.assoc, e4]
  · rw [Category.assoc, e6, Category.assoc, e5]

theorem spread₂_endU_comm : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (Fm : H ⟶ H) (E₁ : EndU U₁.toUnifPre) (E₂ : EndU U₂.toUnifPre), E₁.aG.left ≫ β₁ = β₁ ≫ Fm.left → E₂.aG.left ≫ β₂ = β₂ ≫ Fm.left → ∀ y, ρ (E₂.h y) = E₁.h (ρ y) := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ h₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ h₂ ρ hsp
    Fm E₁ E₂ hE₁ hE₂
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c, b₂, hb₂, Gκ, _, m, hm, m₂, hm₂,
    hW, hj, hα, -, -, -, hnφ, hmφ, hjΩ, hjκ⟩ := hsp
  let FW := pullEnd hW Fm
  have hFW : FW.left ≫ φW = φW ≫ Fm.left := pullEnd_left hW Fm

  have key : j ≫ FW = GlobalTheory.SplitTorus.torusMap _ E₁.h ≫ j := by
    have : IsSchemeTheoreticallyDominant (spMap α) :=
      GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hα
    have : IsSeparated H.hom := hH.separated
    have : IsSeparated GW.hom := MorphismProperty.of_isPullback hW.1 this
    have : Flat (splitTorusAff ZU D₁.toPre.X).hom :=
      (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
    have : Flat (splitTorus (Sp W) D₁.toPre.X).hom := inferInstanceAs (Flat (pullback.snd _ _))
    refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap α) _) ?_
    let FΩ := pullEnd hn FW
    have hFΩ : FΩ.left ≫ n = n ≫ FW.left := pullEnd_left hn FW
    have hover : FΩ.left ≫ n₁ = n₁ ≫ E₁.aG.left :=
      over_of_two_pullbacks h₁.1 hFΩ hFW hnφ hE₁ (Over.w E₁.aG)
        (by rw [hn₁.1.w, ← Category.assoc, Over.w FΩ])
    have e1 := GlobalTheory.TorusPart.pullTorus_comp hn hn FW FΩ hFΩ j
    have e2 := GlobalTheory.TorusPart.pullTorus_torusMap_comp hn j E₁.h
    have e3 := endU_gtTorus_comp U₁ E₁ hb₁ hn₁ FΩ hover
    rw [hjΩ, e3] at e1
    rw [hjΩ] at e2
    rw [← GlobalTheory.TorusPart.pullTorus_left hn, ← GlobalTheory.TorusPart.pullTorus_left hn, e1, e2]

  let Fκ := pullEnd hm FW
  have hFκ : Fκ.left ≫ m = m ≫ FW.left := pullEnd_left hm FW
  have hover₂ : Fκ.left ≫ m₂ = m₂ ≫ E₂.aG.left :=
    over_of_two_pullbacks h₂.1 hFκ hFW hmφ hE₂ (Over.w E₂.aG)
      (by rw [hm₂.1.w, ← Category.assoc, Over.w Fκ])
  have hmono := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₂.gt 0) hb₂ hm₂).1
  have e := congrArg (GlobalTheory.TorusPart.pullTorus hm) key
  rw [GlobalTheory.TorusPart.pullTorus_comp hm hm FW Fκ hFκ j, GlobalTheory.TorusPart.pullTorus_torusMap_comp hm j, hjκ, Category.assoc,
    endU_gtTorus_comp U₂ E₂ hb₂ hm₂ Fκ hover₂, ← Category.assoc, ← Category.assoc,
    ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp] at e
  have : Nonempty (Sp κ) := inferInstance
  have e' := GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 e)
  intro y
  exact DFunLike.congr_fun e' y

end GlobalTheory.Poinc.Sep.Spz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem pullback_map_eq_of_pullTorus_eq {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {p : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G p φ) {X : Type} [AddCommGroup X]
    (f g : splitTorus S X ⟶ G) (e : GlobalTheory.TorusPart.pullTorus h f = GlobalTheory.TorusPart.pullTorus h g) :
    (Over.pullback p).map f = (Over.pullback p).map g := by
  have k : GlobalTheory.SplitTorus.bcMap p X ≫ f.left = GlobalTheory.SplitTorus.bcMap p X ≫ g.left := by
    rw [← GlobalTheory.TorusPart.pullTorus_left h f, ← GlobalTheory.TorusPart.pullTorus_left h g, e]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k]
  · simp only [Over.pullback_map_left, pullback.lift_snd]

theorem spread₂_surjective : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → Function.Surjective ρ := by
  intro B H _ _ hH V₁ _ _ _ _ G₁ _ _ _ D₁ A₁ U₁ ξ₁ β₁ _ V₂ _ _ _ _ G₂ _ _ _ D₂ A₂ U₂ ξ₂ β₂ _ ρ hS
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c, b₂, hb₂, Gκ, _, m, hm,
    m₂, hm₂, hGW, hj, -, hc, -, -, -, -, hΩj, hκj⟩ := hS
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := GlobalTheory.TorusOnto.exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  haveI := hj
  let f : splitTorus (Sp W) F ⟶ GW := GlobalTheory.SplitTorus.torusMap (Sp W) l ≫ j
  have e0 : (1 : splitTorus (Sp W) F ⟶ GW) = GlobalTheory.SplitTorus.torusMap (Sp W) (0 : D₁.toPre.X →+ F) ≫ j := by
    rw [GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]

  have hκ : GlobalTheory.TorusPart.pullTorus hm f = GlobalTheory.TorusPart.pullTorus hm 1 := by
    rw [e0, GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hκj, ← Category.assoc,
      ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, hlρ,
      AddMonoidHom.zero_comp]
  letI : Algebra W κ := c.toAlgebra
  letI : Algebra (ResidueField W) κ := (ResidueField.lift c).toAlgebra
  haveI : IsScalarTower W (ResidueField W) κ :=
    IsScalarTower.of_algebraMap_eq' (ResidueField.lift_comp_residue c).symm
  have hbc : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange W κ).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange W κ).map 1 :=
    pullback_map_eq_of_pullTorus_eq hm f 1 hκ

  have hk := _root_.GlobalTheory.baseChange_map_eq_of_fieldExtension W (ResidueField W) κ _ _ f 1 hbc
  have hsep : IsSeparated GW.hom :=
    (GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ ψ H GW φW hGW hH).separated
  have hf1 : f = 1 := GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow W F GW hsep f 1 (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one W F GW f inferInstance hk)

  have hf0 : GlobalTheory.SplitTorus.torusMap (Sp W) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp W) 0 ≫ j := hf1.trans e0
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus hn) hf0
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩj] at e2
  haveI := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₁.gt 0) hb₁ hn₁).1
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.Poinc.Sep.Spz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionsSameFamilyProportional
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem Trait.exp_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (a₁ b₁ a₂ b₂ : W), T.Exp a₁ b₁ s₁ F → T.Exp a₂ b₂ s₂ F → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom (b₂ * a₁)) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom (b₁ * a₂)) * sval s₂ p' z J := by
  intro R _ _ _ hB D C W _ _ _ T k hk F s₁ s₂ a₁ b₁ a₂ b₂ h₁ h₂ Z p p' hpp' z J hJ
  obtain ⟨σ₁, ⟨τ₁, f₁, hc₁, hp₁, he₁⟩, hg₁⟩ := h₁
  obtain ⟨σ₂, ⟨τ₂, f₂, hc₂, hp₂, he₂⟩, hg₂⟩ := h₂
  have hf : f₁ = f₂ := funext fun x =>
    (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB T.D'.toPre.P.isLB T.hD.w T.hD.w_gen (Fin 4)
      (T.D'.toPre.famφB x) (D.toPre.famφB (T.hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull T.hD x)
      (F.f (T.hD.xe x))).unique (hp₁ x) (hp₂ x)
  subst hf
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  have hGc := hGs.geomConnected
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero W _ bW T.D' T.A T.G T.U.toUnifPre k 2 ![1, -1] ![τ₁, τ₂]
    ![f₁, f₁] (fun i => by fin_cases i; exacts [he₁, he₂])).2 hGc (fun α j => by simp [Fin.sum_univ_two, Out.scal])
  have hτ : τ₁ = τ₂ := SecOps.sec_ext fun j => by
    have := H j
    simpa [Fin.sum_univ_two, Out.scal, add_neg_eq_zero] using this
  subst hτ
  choose J' hJ' using fun ψ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (ψ z)
  have c₁ := hc₁ Z p z J J' hJ hJ'
  have c₂ := hc₂ Z p z J J' hJ hJ'
  have g₁ := hg₁ Z p p' hpp' z J hJ
  have g₂ := hg₂ Z p p' hpp' z J hJ
  have m : ∀ a b : W, gs p z ⊤ (scal T.G.hom (a * b)) = gs p z ⊤ (scal T.G.hom a) * gs p z ⊤ (scal T.G.hom b) :=
    fun a b => by
      rw [show scal T.G.hom (a * b) = scal T.G.hom a * scal T.G.hom b by simp only [scal, map_mul]]
      exact gs_mul p z ⊤ (show p z ∈ (⊤ : T.G.left.Opens) from trivial) _ _
  have key : gs p z ⊤ (scal T.G.hom b₂) * sval σ₁ p z J = gs p z ⊤ (scal T.G.hom b₁) * sval σ₂ p z J := by
    rw [c₁, c₂]; ring
  rw [g₁, g₂] at key
  rw [m, m]
  linear_combination key

end GlobalTheory.Mum
end
end

