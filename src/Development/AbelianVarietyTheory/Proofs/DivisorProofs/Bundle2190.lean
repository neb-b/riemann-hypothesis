module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsEllipticCurveTwoAdic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.CompHt GlobalTheory.ChowHt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ImageModel

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω]

structure IsModelOf (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ)
    {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : HermLB p) (ψ : Ω →+* X.functionField)
    (s : W → L.B.Sec) : Prop where

  arith : IsArithVar p D

  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X

  bij : Function.Bijective ψ

  base : ∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)

  ratio : ∀ (w w' : W) (i : L.B.ι) (h : genericPoint X ∈ L.B.U i),
    ψ (ev w) * fnOf _ h ((s w').f i) = ψ (ev w') * fnOf _ h ((s w).f i)

  bpf : ⨆ w, nonzeroLocus (s w) = ⊤

  fs : ∃ (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W),
      IsFrame Nm W b g A ∧ (∀ k, (gw k : V) = ∑ j, g j k • b j) ∧ (∀ j, b j = ∑ k, c k j • (gw k : V)) ∧
      ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K))),
        (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2)

end GlobalTheory.ImageModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open GlobalTheory.DeRham (push push_comp push_congr push_id push_mul)
open GlobalTheory.AbDual (isMonHom_one push_one)

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

section Push

variable {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)

theorem isMonHom_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero]; exact isMonHom_one A A
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem push_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    haveI := isMonHom_id_pow A n
    push κ t ((𝟙 A) ^ n : A ⟶ A) = (n : R) • LinearMap.id := by
  induction n with
  | zero =>
    haveI := isMonHom_id_pow A 0
    rw [push_congr κ t (pow_zero (𝟙 A)), push_one, Nat.cast_zero, zero_smul]
  | succ n ih =>
    haveI := isMonHom_id_pow A n
    haveI := isMonHom_id_pow A (n + 1)
    haveI : IsMonHom ((𝟙 A) ^ n * 𝟙 A) := inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))
    rw [push_congr κ t (pow_succ (𝟙 A) n), push_mul, ih, push_id, Nat.cast_succ, add_smul, one_smul]

end Push

theorem bijective_push {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)
    {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (f : A ⟶ B) (h : B ⟶ A)
    [IsMonHom f] [IsMonHom h] (m : ℕ) (hm : IsUnit (m : R)) (e₁ : f ≫ h = 𝟙 A ^ m) (e₂ : h ≫ f = 𝟙 B ^ m) :
    Function.Bijective (push κ t f) := by
  haveI := isMonHom_id_pow A m
  haveI := isMonHom_id_pow B m
  have k₁ : ∀ x, push κ t h (push κ t f x) = (m : R) • x := fun x ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₁, push_id_pow]; rfl
  have k₂ : ∀ y, push κ t f (push κ t h y) = (m : R) • y := fun y ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₂, push_id_pow]; rfl
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨push κ t h ((↑hm.unit⁻¹ : R) • y), ?_⟩⟩
  · have e := congrArg (push κ t h) hxy
    rw [k₁, k₁] at e
    exact (hm.smul_left_cancel).1 e
  · rw [k₂, smul_smul, hm.mul_val_inv, one_smul]

end GlobalTheory.PolPrimeTo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.EndoHom

theorem isMonHom_of_prod_pow {S : Scheme.{0}} {A C : Over S} [GrpObj A] [GrpObj C] [IsCommMonObj C]
    (pr : Fin 8 → (A ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over S) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ A, ∀ a, x ≫ pr a = y a)
    (f : A ⟶ A) (e : Fin 8 → Fin 8 → ℤ)
    (hf : ∀ a, f ≫ pr a = ((List.finRange 8).map fun b => pr b ^ e a b).prod) : IsMonHom f := by
  refine isMonHom_of_mul f fun T x y => ?_
  obtain ⟨z, -, hu⟩ := huniq T (fun a => ((x * y) ≫ f) ≫ pr a)
  refine (hu ((x * y) ≫ f) fun a => rfl).trans (hu ((x ≫ f) * (y ≫ f)) fun a => ?_).symm
  have hpre : ∀ {T : Over S} (w : T ⟶ A) (a : Fin 8),
      w ≫ f ≫ pr a = ((List.finRange 8).map fun b => (w ≫ pr b) ^ e a b).prod := fun {T} w a => by
    let φ : (A ⟶ C) →* (T ⟶ C) := MonoidHom.mk' (w ≫ ·) fun g₁ g₂ => MonObj.comp_mul w g₁ g₂
    have h := map_list_prod φ ((List.finRange 8).map fun b => pr b ^ e a b)
    rw [List.map_map] at h
    rw [hf a]
    refine h.trans (congrArg List.prod (List.map_congr_left fun b _ => ?_))
    exact map_zpow φ (pr b) (e a b)
  have := hpr
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hpre, hpre, hpre]
  simp only [MonObj.mul_comp, mul_zpow]
  exact (List.prod_map_mul).symm

theorem isMonHom_of_isGrpPullback_endo {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (hg : IsGrpPullback G' G b φ) (f : G ⟶ G) (hf : IsMonHom f)
    (f₀ : G' ⟶ G') (h : f₀.left ≫ φ = φ ≫ f.left) : IsMonHom f₀ := by
  obtain ⟨f', hf', he⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hg f hf
  have : f' = f₀ := Over.OverMorphism.ext (hg.1.hom_ext (he.trans h.symm) ((Over.w f').trans (Over.w f₀).symm))
  exact this ▸ hf'

end GlobalTheory.Poinc.EndoHom


open GlobalTheory.Poinc.EndoHom in
theorem GlobalTheory.Poinc.isMonHom_of_same_rechart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → ∀ E, IsMonHom (ε' E) := by
  intro g n F W Z i X ε hD c₀ hc R' fg frac hth hev ρ' ε' hS E
  obtain ⟨c, -, pr, hpr, huniq, -, hε⟩ := hD
  have hE : IsMonHom (ε E) := isMonHom_of_prod_pow pr hpr huniq (ε E) E (hε E)
  obtain ⟨P₀, a, a', ε₀, h₁, h₂, -, -, hε₀, -⟩ := hS
  have h₀ : IsMonHom (ε₀ E) := isMonHom_of_isGrpPullback_endo h₁ (ε E) hE (ε₀ E) (hε₀ E).1
  have : IsSchemeTheoreticallyDominant (spMap (X.S.rechart c₀ hc R' fg frac hth hev).R.val.toRingHom) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ Subtype.val_injective
  have := ρ'.P.isAb.smooth
  have := ρ'.P.isAb.proper
  exact GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback h₂ h₂ (ε₀ E) (ε' E) (hε₀ E).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

variable {R : Type} [CommRing R] [IsDomain R]

theorem gm_jK_unitOn (w : Rˣ) (z : (TK R).left) :
    gm (toUnit (TK R)).left z ⊤ (unitOn w) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)) := by
  have e : (toUnit (TK R)).left = 𝟙 _ ≫ jK R := by simp
  rw [e, ← gm_pull (𝟙 _) (jK R) z ⊤ trivial]
  congr 1
  apply Units.ext
  have := congrArg (fun q => q.hom (w : R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

theorem tauCoord_mul_unit {Q : Data R} {a b : Q.X} {k : (FractionRing R)ˣ} (h : Q.TauCoord a b k) (w : Rˣ) :
    Q.TauCoord a b (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := by
  obtain ⟨u, hu, hv⟩ := h
  let ρ : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ := unitOn w⁻¹
  refine ⟨⟨fun j => res le_top ρ * u.s j⟩, fun i j => ?_, fun z J hJ => ?_⟩
  · show res _ (res le_top ρ * u.s i) = _ * res _ (res le_top ρ * u.s j)
    rw [map_mul, map_mul, InhTate.res_res, InhTate.res_res, hu i j]
    exact mul_left_comm _ _ _
  · rw [hv z J hJ]
    have hm := hJ.mem (lamPts (Q.c a) (Q.c b)) (toUnit (TK R)).left
    show _ = _ * gm _ z _ (res le_top ρ * u.s _)
    erw [MonoidHom.map_mul, gm_res _ z le_top hm]
    have e3 : gm (toUnit (TK R)).left z ⊤ ρ =
        (gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)))⁻¹ := by
      rw [← gm_jK_unitOn, ← MonoidHom.map_inv]
      exact congrArg _ (MonoidHom.map_inv _ _)
    have e4 : unitOn (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) =
        unitOn k * unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := MonoidHom.map_mul _ _ _
    rw [e3, e4, MonoidHom.map_mul]
    have : val u (toUnit (TK R)).left z J = gm (toUnit (TK R)).left z _ (u.s _) := rfl
    rw [this, _root_.mul_assoc, mul_inv_cancel_left]
    rfl

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperUniformisedSemiAbelianOverOpenInAbLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnifProperOpen

theorem isProper_of_polGeneric_of_abLocus : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.UU.CDVR V →
    ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ φ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) φ → (∀ x, x ∈ abLocus G) → IsProper G.hom := by
  intro V _ _ _ hV A G _ _ hG φ hφ hab
  haveI := hV.1
  haveI := hV.2.2
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hφ
  obtain ⟨L, hL⟩ := GlobalTheory.UU.polarisation_extends l₁ V A G hG e he
  obtain ⟨P, rfl⟩ := GlobalTheory.CubicalPackage.exists_package l₁ V hV A G hG e he L hL
  obtain ⟨w, hw⟩ := hL
  have hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))
  have h0 : IsAbelianScheme (thickObj V (maximalIdeal V) 0 G) := by
    have h₂ := IsSemiAbelian.pullback (thick V (maximalIdeal V) 0) G hG
    letI := hF.toField
    exact ⟨h₂.comm, h₂.smooth, GlobalTheory.ArcNotAbelian.isProper_fibre G hG _ _ p (hab _), h₂.geomConnected⟩
  obtain ⟨P₀, h₀⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal V) 0 P
  let s : GlobalTheory.UU.HidaSetting V A G := ⟨hV, hG, e, he, P, w, hw, PUnit, GlobalTheory.UU.TQ.abelian _ h0 PUnit, P₀, h₀,
    GlobalTheory.UU.SettingConsistentExample.ab_even h0 PUnit P₀⟩
  obtain ⟨D, U, -, -, -⟩ := GlobalTheory.uniformisation_dvr_unconditional V A G s
  let g := U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus G hG _ hF (thick V (maximalIdeal V) 0) p (hab _)
    D.toPre.X g.i g.i_hom
  exact (GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hV.2.1 D A G hG U hs).proper

theorem exists_polGeneric_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
    (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V),
    Function.Injective φ → ∃ (A' : PolAV (Sp (FractionRing V))) (ψ : A'.A.left ⟶ ((Over.pullback (spMap φ)).obj G).left),
    IsGrpPullback A'.A ((Over.pullback (spMap φ)).obj G) (jK V) ψ := by
  intro R _ _ A G _ gen hgen V _ _ φ hφ
  have hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hφ
  let ψ : FractionRing R →+* FractionRing V := IsFractionRing.lift hinj'
  have hg : spMap ψ ≫ jK R = jK V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [ψ, IsFractionRing.lift_algebraMap]
  obtain ⟨A', eA, heA, -⟩ := GlobalTheory.GoodReductionUnif.exists_baseChange GlobalTheory.polBaseChange_holds (spMap ψ) A
  have h₁ := GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (spMap ψ) A.A eA heA
  have h₂ := GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK R) G gen hgen
  have h₃ := h₁.comp h₂
  refine ⟨A', pullback.lift ((eA.inv.left ≫ pullback.fst A.A.hom (spMap ψ)) ≫ gen.inv.left ≫
    pullback.fst G.hom (jK R)) (A'.A.hom ≫ jK V) (by rw [h₃.1.w, hg, Category.assoc]), ?_⟩
  exact (isGrpPullback_pullback G (spMap φ)).cancel (h₃.congr hg (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)

theorem range_spMap_away (R : Type) [CommRing R] (f : R) :
    Set.range (spMap (algebraMap R (Localization.Away f))) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  have e : ⇑(spMap (algebraMap R (Localization.Away f))) = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) := by
    ext x : 1
    simp [spMap, Spec.map_base]
    rfl
  rw [e]
  exact PrimeSpectrum.localization_away_comap_range _ f

theorem isProper_away (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R]
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) (hgen : IsMonHom gen.hom) (f : R) (hf : f ≠ 0)
    (hab : ∀ z ∈ Set.range (spMap (algebraMap R (Localization.Away f))), z ∈ abLocus G) :
    IsProper (pullback.snd G.hom (spMap (algebraMap R (Localization.Away f)))) := by
  haveI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : IsNoetherianRing (Localization.Away f) := IsLocalization.isNoetherianRing (Submonoid.powers f) _ inferInstance
  set j := spMap (algebraMap R (Localization.Away f)) with hj
  let Gf := (Over.pullback j).obj G
  haveI hGf : IsSemiAbelian Gf := IsSemiAbelian.pullback j G hG
  haveI := hGf.separated
  haveI := hGf.quasiCompact
  haveI := hGf.smooth
  haveI : IsIntegral Gf.left := GlobalTheory.isIntegral_left_of_isSemiAbelian Gf
  change IsProper Gf.hom
  refine _root_.GlobalTheory.TraitProper.isProper_of_lift_genericPoint (Localization.Away f) Gf.left Gf.hom ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+* V, spMap φ = y ≫ j := ⟨(Spec.preimage (y ≫ j)).hom, by simp [spMap]⟩
  let p₀ : Sp K := (⊥ : PrimeSpectrum K)
  have h₁ : x p₀ = genericPoint Gf.left := hx ⟨p₀, rfl⟩
  have h₂ : (x ≫ Gf.hom ≫ j) p₀ = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, h₁, GlobalTheory.ProperOfAbelianFibres.apply_genericPoint_of_flat]
    exact genericPoint_eq_bot_of_affine (CommRingCat.of R)
  rw [← Category.assoc, hxy, Category.assoc, ← hφ] at h₂
  have h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥ := congrArg PrimeSpectrum.asIdeal h₂
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) := by simp [ha]
    rw [h₃] at this
    simpa using this
  haveI : CharZero V := charZero_of_injective_ringHom hinj
  let GV := (Over.pullback (spMap φ)).obj G
  have hGV : IsSemiAbelian GV := IsSemiAbelian.pullback (spMap φ) G hG
  have habV : ∀ z, z ∈ abLocus GV := fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (spMap φ)) z).1
      (hab _ ⟨y z, by rw [hφ, Scheme.Hom.comp_apply]⟩)
  obtain ⟨A', ψ, hψ⟩ := exists_polGeneric_pullback R A G gen hgen V φ hinj
  have hpV : IsProper GV.hom := isProper_of_polGeneric_of_abLocus V ⟨inferInstance, inferInstance, inferInstance⟩ A' GV hGV ψ hψ habV
  let xV : Sp K ⟶ GV.left := pullback.lift (x ≫ pullback.fst G.hom j) (spMap (algebraMap V K)) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [hxy]
    rw [Category.assoc, hφ])
  have hE : ValuativeCriterion.Existence GV.hom := by
    have h : UniversallyClosed GV.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq GV.hom :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  have e₁ : spMap (algebraMap V K) ≫ l.l = xV := l.fac_left
  have e₂ : l.l ≫ GV.hom = 𝟙 _ := l.fac_right
  refine ⟨pullback.lift (l.l ≫ pullback.fst G.hom (spMap φ)) y ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [e₂]
    rw [Category.id_comp, hφ]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, e₁]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, pullback.lift_snd]
      exact hxy.symm

theorem isProper_restrict : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G →
    IsProper (G.hom ∣_ W) := by
  intro R _ _ _ hR D A G _ _ hG U W hW
  obtain ⟨⟨hN, -, -, -⟩, hc⟩ := hR
  haveI := hN
  haveI := hc
  let I := {f : R // f ≠ 0 ∧ ∀ z ∈ Set.range (spMap (algebraMap R (Localization.Away f))), z ∈ W}
  refine GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom (I := I)
    (fun i => spMap (algebraMap R (Localization.Away i.1))) (fun i => pullback.snd G.hom _)
    (fun i => pullback.fst G.hom _) (fun i => IsPullback.of_hasPullback _ _) (fun _ => ⊤) (fun i => ?_) W
    (fun i => ?_) (fun z hz => ?_)
  · exact IsZariskiLocalAtTarget.restrict
      (isProper_away R A G hG U.gen U.gen_hom i.1 i.2.1 fun z hz => hW (i.2.2 z hz)) ⊤
  · rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact i.2.2 _ ⟨_, rfl⟩
  · obtain ⟨_, ⟨f, rfl⟩, hzf, hfW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen
    have hr := range_spMap_away R f
    have hzf' : z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := hzf
    have hfW' : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ (W : Set (Sp R)) := hfW
    have hf : f ≠ 0 := by
      rintro rfl
      exact hzf' (zero_mem _)
    refine ⟨⟨f, hf, fun z' hz' => hfW' (by rw [hr] at hz'; exact hz')⟩, ?_⟩
    obtain ⟨a, ha⟩ : z ∈ Set.range (spMap (algebraMap R (Localization.Away f))) := by rw [hr]; exact hzf'
    exact ⟨⟨a, trivial⟩, ha⟩

end GlobalTheory.UnifProperOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.IdemImage

theorem isSemiAbelian_image : ∀ (S : Scheme.{0}) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ e : G' ⟶ G', IsMonHom e → e ≫ e = e → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (inc : G ⟶ G') (pr : G' ⟶ G), IsSemiAbelian G ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G ∧ pr ≫ inc = e := by
  intro S G' _ _ hG e he hee
  have hsm : GlobalTheory.SS.SmConn G' :=
    ⟨hG.comm, hG.smooth, hG.separated, hG.quasiCompact, hG.geomConnected⟩
  obtain ⟨G, hgrp, inc, pr, hG₁, hinc, hpr, hip, hpi⟩ :=
    GlobalTheory.SS.smConn_idempotent_splits S G' hsm e he hee
  exact ⟨G, hgrp, hG₁.1, inc, pr,
    GlobalTheory.SS.isSemiAbelian_of_retract S G' G hG hG₁ inc pr hpr hip, hinc, hpr, hip, hpi⟩

end GlobalTheory.Mum.IdemImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumScaleSectionsByConstantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyDatum_scale_sections_by_constant : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)) (a : K) (th : x.P.L.Sec) (hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus th), (∀ i, th.f i = constFn x.P.A.hom _ a * x.th.f i) → (∀ i, σ'.f i = constFn G.hom _ a * σ.f i) → KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, x.v, x.basis⟩ G L σ' y := by
  first | exact @GlobalTheory.KeyEven.keyOn_scale | exact GlobalTheory.KeyEven.keyOn_scale | (intros; apply GlobalTheory.KeyEven.keyOn_scale <;> assumption)
end

