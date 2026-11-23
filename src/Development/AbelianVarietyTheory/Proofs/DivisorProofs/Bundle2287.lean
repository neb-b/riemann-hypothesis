module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantOneFormsAbelianSchemeFiniteProjective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvFormProj

theorem finite_projective_of_locally_projective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (h : ∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
      (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
      (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
      (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ) :
    Module.Finite R M ∧ Module.Projective R M := by
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iProj ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iProj
  haveI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (ϕ g) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.1) (Localization.Away g.1) (ϕ g)).2 (hϕ g)
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

theorem finite_projective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (GlobalTheory.InvForm.InvForm A).subtype)) → Module.Finite R (GlobalTheory.InvForm.InvForm A) ∧ Module.Projective R (GlobalTheory.InvForm.InvForm A) := by
  intro R _ A _ g _ hsm hbc
  haveI : SmoothOfRelativeDimension g A.hom := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  apply finite_projective_of_locally_projective
  intro q
  let e : Spec (CommRingCat.of R) ⟶ A.left := η[A].left
  have he : e ≫ A.hom = 𝟙 _ := by simp [e]
  obtain ⟨V, hV, hqV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens)
    (show e q ∈ (⊤ : A.left.Opens) from trivial)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := q) (u := (e ⁻¹ᵁ V).1) hqV (e ⁻¹ᵁ V).2
  refine ⟨r, hr, ?_⟩
  let y : Sp (Localization.Away r) ⟶ A.left := spMap (algebraMap R (Localization.Away r)) ≫ e
  have hy : ⊤ ≤ y ⁻¹ᵁ V := by
    intro t _
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this
  have hs : y ≫ A.hom = spMap (algebraMap R (Localization.Away r)) := by
    simp only [y, Category.assoc, he, Category.comp_id]
  let φ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := V) y hy hs
  letI : Algebra (Sec A.hom V) (Localization.Away r) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R (Sec A.hom V) (Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  haveI : Algebra.Smooth R (Sec A.hom V) := smooth_sec_affine A.hom ⟨V, hV⟩
  have hb := hbc (Opposite.op ⟨V, hV⟩)
  exact ⟨Localization.Away r ⊗[Sec A.hom V] Ω[Sec A.hom V⁄R], inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, _,
    hb.comp (TensorProduct.isBaseChange (Sec A.hom V) Ω[Sec A.hom V⁄R] (Localization.Away r))⟩

end GlobalTheory.InvFormProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAddOfIsSecDiffIsSecAdd
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isAdd_of_isSecDiff_isSecAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A, (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ (u : Fn1 A) (g : Fn2 A), IsSecDiff n S u → IsSecAdd n S g → IsAdd u g := by
  intro R _ A _ _ n hR b _ S _ u g hu hg D _ _ D' _ _ φ x y
  let x' : Pt A D' := spOver φ ≫ x
  let y' : Pt A D' := spOver φ ≫ y
  obtain ⟨D1, _, _, ψ1, z1, h1, hz1⟩ := hR D' x'
  obtain ⟨E, _, _, ψ2, w, h2, hw⟩ := hR D1 (spOver ψ1 ≫ y')
  let ψ : D' →ₐ[R] E := ψ2.comp ψ1
  let z : Pt A E := spOver ψ2 ≫ z1
  have hψ : spOver ψ = spOver ψ2 ≫ spOver ψ1 := (spOver_comp ψ1 ψ2).symm
  have hz : z ^ n = spOver ψ ≫ x' := by
    rw [show z = spOver ψ2 ≫ z1 from rfl, ← comp_pow, hz1, hψ, Category.assoc]
  have hw' : w ^ n = spOver ψ ≫ y' := by rw [hw, hψ, Category.assoc]
  have hmul : spOver φ ≫ (x * y) = (spOver φ ≫ x) * (spOver φ ≫ y) := comp_mul _ _ _
  have hzw : (z * w) ^ n = spOver ψ ≫ spOver φ ≫ (x * y) := by
    rw [mul_pow, hz, hw', hmul, comp_mul]
  have hc (t : Pt A D) : spOver ψ ≫ spOver φ ≫ t = spOver (ψ.comp φ) ≫ t := by
    rw [← Category.assoc, spOver_comp]
  have hinj : Function.Injective ψ := fun _ _ h ↦ h1.injective (h2.injective h)
  apply hinj
  have e1 := hg D' x' y' E ψ z w hz hw'
  have e2 := hg D x y E (ψ.comp φ) z w (hz.trans (hc x)) (hw'.trans (hc y))
  rw [AlgHom.comp_apply] at e2
  have e3 := hu D D' φ (x * y) E ψ (z * w) hzw
  rw [hmul] at e3
  have e4 := hu D D' φ x E ψ z hz
  have e5 := hu D D' φ y E ψ w hw'
  simp only [map_sub]
  linear_combination e1 - e2 - e3 + e4 + e5

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem valR_comp_app {Y Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Y) (m : Y ⟶ Z) (O : Z.Opens)
    (f : Γ(Z, O)) : valR (z ≫ m) O f = valR z (m ⁻¹ᵁ O) ((m.app O).hom f) := by
  by_cases h : ⊤ ≤ z ⁻¹ᵁ (m ⁻¹ᵁ O)
  · rw [valR_eq_ev _ _ h, valR_eq_ev (z ≫ m) O h, ← GlobalTheory.FlagMod.ev_appLE z m le_rfl h h, Scheme.Hom.appLE_eq_app]
  · rw [valR, valR, dif_neg h]
    exact dif_neg h

theorem le_preimage_of_red {Y : Scheme.{0}} {B : Type} [CommRing B] {x : Sp B ⟶ Y} {w : Sp (DualNumber B) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) : ⊤ ≤ w ⁻¹ᵁ O := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (DualNumber B) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← hw] at this
  exact this

theorem valR_resG {Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Z) {U V : Z.Opens} (e : V ≤ U)
    (h : ⊤ ≤ z ⁻¹ᵁ V) (a : Γ(Z, U)) : valR z V (resG Z e a) = valR z U a := by
  calc
    valR z V (resG Z e a) = GlobalTheory.FlagMod.ev z V h (resG Z e a) := valR_eq_ev z V h _
    _ = GlobalTheory.FlagMod.ev z U (GlobalTheory.FlagMod.le_preimage_mono e h) a :=
      GlobalTheory.FlagMod.ev_res z e h _ a
    _ = valR z U a := (valR_eq_ev z U _ a).symm

theorem isAffineHom_of_field {K : Type} [Field K] {X : Scheme.{0}} (x0 : Sp K ⟶ X) : IsAffineHom x0 := by
  refine ⟨fun U _ => ?_⟩
  by_cases h : (default : PrimeSpectrum K) ∈ x0 ⁻¹ᵁ U
  · have e : x0 ⁻¹ᵁ U = ⊤ := eq_top_iff.2 fun p _ => by
      rwa [Subsingleton.elim (α := PrimeSpectrum K) p default]
    rw [e]
    exact isAffineOpen_top _
  · have e : x0 ⁻¹ᵁ U = ⊥ := eq_bot_iff.2 fun p hp => by
      rw [Subsingleton.elim (α := PrimeSpectrum K) p default] at hp
      exact (h hp).elim
    rw [e]
    exact isAffineOpen_bot _

theorem IsChartPt.of_le {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
    (hd : LogKS.IsField W₀ d) {Ω₀ Ω : Z.Opens} (h0 : Ω₀ ≤ Ω) (h1 : Ω ≤ W₀) {n : ℕ} {u : Fin n → (epsR K ⟶ A)}
    {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B]
    [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B))
    (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω₀)) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω₀ (d Ω₀) u θ Wo g x l) :
    IsChartPt A' m m' Ω (d Ω) u θ Wo g x l := by
  obtain ⟨h₁, h₂, h₃⟩ := hl
  refine ⟨h₁, GlobalTheory.FlagMod.le_preimage_mono h0 h₂, fun f => ?_⟩
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω₀ := hxΩ
  have hw : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω₀ := fun a =>
    le_preimage_of_red ((isTransl_transl _ x hx (u a)).red (hut a)) hxΩ
  rw [← valR_resG _ h0 h₂, h₃, chartVal, chartVal, hd.2.2 Ω Ω₀ h0 h1, valR_resG _ h0 hxm, valR_resG _ h0 hxm]
  simp only [valR_resG _ h0 (hw _)]

end GlobalTheory.CechKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicKb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LabBC

open GlobalTheory GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem qkExt_id' {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C]
    [Algebra (FractionRing R) C] {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

theorem isAlgebraic_kb {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁)
    (hρ : ρ.Finite) [Algebra (FractionRing R) (Kb R₁)]
    (hc : ∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) =
      algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r))) :
    Algebra.IsAlgebraic (FractionRing R) (Kb R₁) := by
  letI : Algebra R R₁ := ρ.toAlgebra
  have h1 : ∀ r : R, algebraMap R (Kb R₁) r = algebraMap R₁ (Kb R₁) (ρ r) := fun r => by
    rw [IsScalarTower.algebraMap_apply R (FractionRing R₁) (Kb R₁), IsScalarTower.algebraMap_apply R R₁ (FractionRing R₁),
      IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (Kb R₁)]
    rfl
  haveI : IsScalarTower R R₁ (Kb R₁) := IsScalarTower.of_algebraMap_eq fun r => h1 r
  haveI : IsScalarTower R (FractionRing R) (Kb R₁) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [h1, hc, IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (Kb R₁)]
  haveI : Module.Finite R R₁ := hρ
  haveI : Algebra.IsAlgebraic R R₁ := Algebra.IsAlgebraic.of_finite R R₁
  haveI : Algebra.IsAlgebraic R₁ (Kb R₁) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R₁) (K := FractionRing R₁)).2 inferInstance
  haveI : Algebra.IsAlgebraic R (Kb R₁) := Algebra.IsAlgebraic.trans R R₁ (Kb R₁)
  exact (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := FractionRing R)).1 inferInstance

theorem galEqN_of_rel {R R₁ : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁]
    [IsLocalRing R₁] (ρ : R →+* R₁) (hρ : FinExt ρ) (D : DegData R (maximalIdeal R))
    (D₁ : DegData R₁ (maximalIdeal R₁)) (hD : IsPullDeg ρ D.toPre D₁.toPre) (A : PolAV (Sp (FractionRing R)))
    (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (hfib : IsFib ρ A A₁ a) (lab : Labels D.toPre A)
    (n : ℕ) (hn : 1 ≤ n) (hGal : GalEqN n lab) [Algebra (FractionRing R) (Kb R₁)]
    (em : Kb R →ₐ[FractionRing R] Kb R₁) (lab₁ : Labels D₁.toPre A₁)
    (hc : ∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) =
      algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r)))
    (hrel : ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k)
      (p' : QkPt D₁.toPre (Kb R₁) k), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y →
      IsPullGtF ρ hD (Kb R₁) p₁.g p'.g → (lab₁ k p').left ≫ a = spMap em.toRingHom ≫ (lab k p).left) :
    GalEqN n lab₁ := by
  obtain ⟨ga, hga, hpb, -⟩ := hfib
  have hK : algebraMap (FractionRing R) (Kb R₁) = (algebraMap (FractionRing R₁) (Kb R₁)).comp ga :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, hga, hc])
  haveI : Algebra.IsAlgebraic (FractionRing R) (Kb R₁) := isAlgebraic_kb ρ hρ.2.2 hc
  let mu : Kb R₁ →ₐ[FractionRing R] Kb R := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hsurj : Function.Surjective em := fun z => by
    obtain ⟨w, hw⟩ := (Algebra.IsAlgebraic.algHom_bijective (em.comp mu)).2 z
    exact ⟨mu w, hw⟩
  let τ : Kb R ≃ₐ[FractionRing R] Kb R₁ := AlgEquiv.ofBijective em ⟨em.toRingHom.injective, hsurj⟩
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  have hG := hL.globalFns
  have hB := D.tau_bimult
  have hB₁ := D₁.tau_bimult
  have hF : Compat ρ (Kb R₁) := hc
  intro σ₁ j P P' hPP'
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn
  set e : Kb R →+* Kb R₁ := em.toRingHom with he_def
  set e' : Kb R₁ →+* Kb R := τ.symm.toAlgHom.toRingHom with he'_def
  set s₁ : Kb R₁ →+* Kb R₁ := σ₁.toRingHom with hs₁_def
  have hee' : e.comp e' = RingHom.id _ := RingHom.ext fun x => τ.apply_symm_apply x
  have hfσ : s₁.comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R₁) := by
    rw [hK, ← RingHom.comp_assoc]
    exact congrArg (fun f => f.comp ga) σ₁.comp_algebraMap
  have hfσ₁ : s₁.comp (algebraMap (FractionRing R₁) (Kb R₁)) = algebraMap (FractionRing R₁) (Kb R₁) :=
    σ₁.comp_algebraMap
  have hfe : e.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R₁) := em.comp_algebraMap
  have hfe' : e'.comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R) :=
    τ.symm.toAlgHom.comp_algebraMap
  have hfid : (RingHom.id (Kb R₁)).comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R₁) :=
    RingHom.id_comp _

  let σ : Kb R →ₐ[FractionRing R] Kb R :=
    τ.symm.toAlgHom.comp ((({ σ₁.toRingHom with commutes' := fun x => RingHom.congr_fun hfσ x } : Kb R₁ →ₐ[FractionRing R] Kb R₁)).comp em)
  have hσ_def : σ.toRingHom = e'.comp (s₁.comp e) := rfl
  have hfσR : σ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    σ.comp_algebraMap
  have hes : e.comp σ.toRingHom = s₁.comp e := by
    rw [hσ_def, ← RingHom.comp_assoc, hee', RingHom.id_comp]
  obtain ⟨q, rfl⟩ := pullQk_surjective hD hG hF hB hB₁ P
  obtain ⟨q', rfl⟩ := pullQk_surjective hD hG hF hB hB₁ P'
  have hq' : q' = qkExt hB s₁ hfσ q := by
    apply GlobalTheory.QkPullEquiv.pullQk_injective hD hG hF hB hB₁
    rw [(qkExt_iff hB₁ s₁ hfσ₁ _ _).1 hPP',
      (qkExt_iff hB₁ s₁ hfσ₁ _ _).1 (GlobalTheory.QkRationalExt.qkExt_pullQk hD hG hB hB₁ hF hF s₁ hfσ hfσ₁ q)]
  have hid : ∀ z : QkPt D.toPre (Kb R₁) (n ^ j), qkExt hB (RingHom.id _) hfid z = z := fun z =>
    ((qkExt_iff hB _ hfid z z).1 (qkExt_id' z)).symm

  have hpq : ∀ z : QkPt D.toPre (Kb R₁) (n ^ j), QkExt e (qkExt hB e' hfe' z) z := fun z => by
    rw [qkExt_iff hB e hfe, GlobalTheory.QkRationalExt.qkExt_qkExt hB e' hfe' e hfe (RingHom.id _) hfid hee', hid]
  have hσpp : QkExt σ.toRingHom (qkExt hB e' hfe' q) (qkExt hB e' hfe' q') := by
    rw [qkExt_iff hB _ hfσR, GlobalTheory.QkRationalExt.qkExt_qkExt hB e' hfe' σ.toRingHom hfσR (e'.comp s₁)
      (by rw [RingHom.comp_assoc, hfσ, hfe']) (by rw [hσ_def, RingHom.comp_assoc, RingHom.comp_assoc, hee',
        RingHom.comp_id]), hq', GlobalTheory.QkRationalExt.qkExt_qkExt hB s₁ hfσ e' hfe' (e'.comp s₁) _ rfl]
  have hgal := hGal σ j _ _ hσpp
  have h₁ := hrel _ hk _ _ _ (hpq q) ((eq_pullQk_iff hD hG hF hB hB₁ q _).1 rfl).1
    ((eq_pullQk_iff hD hG hF hB hB₁ q _).1 rfl).2
  have h₂ := hrel _ hk _ _ _ (hpq q') ((eq_pullQk_iff hD hG hF hB hB₁ q' _).1 rfl).1
    ((eq_pullQk_iff hD hG hF hB hB₁ q' _).1 rfl).2
  apply hpb.1.hom_ext
  · rw [h₂, Category.assoc, h₁, hgal, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', hes]
  · rw [Category.assoc, Over.w (lab₁ (n ^ j) (pullQk hD hG hF hB hB₁ q')), Over.w (lab₁ (n ^ j) (pullQk hD hG hF hB hB₁ q))]
    show jFK (R := R₁) (Kb R₁) = spMap s₁ ≫ jFK (R := R₁) (Kb R₁)
    rw [spMap_comp', hfσ₁]

end GlobalTheory.Mum.LabBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLineBundlePullbackOfTranslates
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem isAmpleLB_pull_fst_of_translates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (c : Pic A.left) (V : A.left.Opens), cls L hL = c → IsAffineOpen V → IsLocus c V → ∀ (T : Over (Sp R)) [IsAffine T.left] (n : ℕ) (a : Fin n → (T ⟶ A)), ⨆ i, ((fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ → (∀ i, GlobalTheory.CechPic.pull (a i).left c + GlobalTheory.CechPic.pull ((a i)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0) → GlobalTheory.IsAmpleLB (L.pull (fst A T).left) := by
  intro R _ _ A _ hA L hL c V hc hV hloc T _ n a hcov hrel
  haveI : IsProper A.hom := hA.proper
  have hL' : (L.pull (fst A T).left).IsLB := LB.isLB_pull hL _
  have h2 : (lbPow (L.pull (fst A T).left) 2).IsLB := GlobalTheory.isLB_lbPow hL' 2
  have hcls : cls _ h2 = 2 • CechPic.pull (fst A T).left c := by
    rw [cls_lbPow hL' 2 h2, cls_pull hL _ hL', hc]
  have hsec : ∀ i, ∃ s : (lbPow (L.pull (fst A T).left) 2).Sec, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s =
      (fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V := fun i =>
    IsLocus.exists_sec h2 (hcls ▸ _root_.GlobalTheory.SquareLocus.translate_mul_inv_isLocus (Sp R) A hA c V hloc T (a i) (hrel i))
  choose s hs using hsec
  exact isAmpleLB_of_cover hL' (by norm_num) s (by simp only [hs]; exact hcov)
    fun i => (hs i).symm ▸ GlobalTheory.T.isAffineOpen_preimage_add_inf_preimage_sub_grpScheme R A V hV T (a i)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCanForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {A : Over (Sp R)}

theorem fv_form (β : Form (A.hom ≫ 𝟙 _)) {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) : fv β.1 D D' φ x = 0 := by
  simpa only [fv, GlobalTheory.Cris.ev] using β.2 (trivMap φ x) rfl rfl

variable [GrpObj A] {p : ℕ} {G : PDivGroup p R}

def formDat (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) : Dat t ⟨_, hβ⟩ where
  f := β.1
  cl := rfl
  g := fun _ _ _ _ _ ↦ 0
  add := fun _ _ _ _ _ _ φ _ _ ↦ by simp [fv_form]
  h := 0
  res := fun n ↦ by simp [fv_form]

theorem isCan_form : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A),
    ∃ w : G.omega, (∀ n, w.1 n = cotVal β.1 (t.y n)) ∧ IsCan t ⟨_, hβ⟩ (G.rigOfOmega w) := by
  intro R _ A _ p G t β hβ
  refine ⟨⟨(formDat t β hβ).om, fun n ↦ _root_.GlobalTheory.PtExt.OmRes.cotMap_res_om R A p G t _ (formDat t β hβ) n⟩, fun n ↦ ?_,
    formDat t β hβ, 0, _, fun n ↦ ?_, fun _ ↦ rfl, rfl⟩
  · change cotVal β.1 (t.y n) - dUnit (R := R) (0 : G.A n) = _
    rw [dUnit, map_zero, sub_zero]
  · change (0 : _) = 0 - (fv β.1 _ _ _ _ - fv β.1 _ _ _ _ - fv β.1 _ _ _ _) - cobOne R (G.A n) 0
    simp [fv_form]

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  first | exact @GlobalTheory.TwistFlat.isClosedImmersion_kerι | exact GlobalTheory.TwistFlat.isClosedImmersion_kerι | (intros; apply GlobalTheory.TwistFlat.isClosedImmersion_kerι <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrictStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDominant_of_isIso_restrict' : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → IsDominant s := by
  first | exact @GlobalTheory.Discrepancy.isDominant_of_isIso_restrict | exact GlobalTheory.Discrepancy.isDominant_of_isIso_restrict | (intros; apply GlobalTheory.Discrepancy.isDominant_of_isIso_restrict <;> assumption)
end

