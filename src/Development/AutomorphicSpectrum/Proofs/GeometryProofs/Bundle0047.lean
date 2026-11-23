module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PPshLocal
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal
section
namespace GlobalTheory.CompanionTheory.AnForm.PshLocal

open Filter Topology ReciprocityTheory.AnForm.A

theorem isPsh_mono {n : ℕ} {V W : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (hWV : W ⊆ V)
    (h : IsPsh V φ) : IsPsh W φ := by
  unfold ReciprocityTheory.AnForm.A.IsPsh at h ⊢
  obtain ⟨hu, hm⟩ := h
  exact ⟨hu.mono hWV, fun z w hzw => hm z w fun ζ hζ => hWV (hzw ζ hζ)⟩

theorem isPsh_of_locally :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ), IsOpen U →
      (∀ z ∈ U, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) →
      ReciprocityTheory.AnForm.A.IsPsh U φ := by
  intro n U φ hU hloc
  have hloc' : ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ IsPsh W φ := by
    intro p hp
    obtain ⟨V, hV, hpV, hψ⟩ := hloc p hp
    exact ⟨V ∩ U, hV.inter hU, ⟨hpV, hp⟩, Set.inter_subset_right, isPsh_mono Set.inter_subset_left hψ⟩
  have hlocg : ∀ k : ℕ, ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
      IsPsh W (fun x => max (φ x) (-(k : ℝ))) := by
    intro k p hp
    obtain ⟨W, hW, hpW, hWU, hψ⟩ := hloc' p hp
    exact ⟨W, hW, hpW, hWU, GroundTheory.Heights₂.Heights.NineStatements.PshLocal.isPsh_max hψ _⟩
  have husc := GroundTheory.Heights₂.Heights.NineStatements.PshLocal.usc hloc'
  unfold ReciprocityTheory.AnForm.A.IsPsh
  refine ⟨husc, ?_⟩
  intro z w hzw
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))
  let F : ℝ → ℝ := fun θ => φ (z + circleMap 0 1 θ • w)
  let f : ℕ → ℝ → ℝ := fun k θ => max (F θ) (-(k : ℝ))
  have hcore : ∀ k : ℕ, IntervalIntegrable (f k) MeasureTheory.volume 0 (2 * Real.pi) ∧
      max (φ z) (-(k : ℝ)) ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f k θ := fun k =>
    GroundTheory.Heights₂.Heights.NineStatements.PshLocal.core hU (hlocg k) z w hzw (c := -(k : ℝ))
      (fun θ => le_max_right _ _)
  have hint : ∀ k, MeasureTheory.Integrable (f k) μ := fun k =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mp (hcore k).1
  have hanti : ∀ θ, Antitone fun k : ℕ => f k θ := by
    intro θ
    refine antitone_nat_of_succ_le fun k => ?_
    show max (F θ) (-(((k + 1 : ℕ)) : ℝ)) ≤ max (F θ) (-(k : ℝ))
    push_cast
    exact max_le_max le_rfl (by linarith)
  have htend : ∀ θ, Tendsto (fun k : ℕ => f k θ) atTop (𝓝 (F θ)) := by
    intro θ
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈-F θ⌉₊) fun k hk => ?_
    have hc := Nat.le_ceil (-F θ)
    have hk' : ((⌈-F θ⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    exact max_eq_left (by linarith)
  have hlow : ∀ k : ℕ, 2 * Real.pi * φ z ≤ ∫ θ, f k θ ∂μ := by
    intro k
    have h1 := le_trans (le_max_left (φ z) (-(k : ℝ))) (hcore k).2
    rw [intervalIntegral.integral_of_le h2π] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 h2π
    rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at h3
  have hFmeas : MeasureTheory.AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hint k).aestronglyMeasurable)
      (Filter.Eventually.of_forall htend)
  have hGnn : ∀ (k : ℕ) θ, 0 ≤ f 0 θ - f k θ := fun k θ => sub_nonneg.mpr (hanti θ (Nat.zero_le k))
  have hFle : ∀ θ, F θ ≤ f 0 θ := fun θ => le_max_left _ _
  have hGint : MeasureTheory.Integrable (fun θ => f 0 θ - F θ) μ := by
    refine ⟨(hint 0).aestronglyMeasurable.sub hFmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun θ => sub_nonneg.mpr (hFle θ))]
    have hlim : ∀ θ, Tendsto (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop
        (𝓝 (ENNReal.ofReal (f 0 θ - F θ))) :=
      fun θ => (ENNReal.continuous_ofReal.tendsto _).comp ((htend θ).const_sub _)
    have hterm : ∀ k : ℕ, ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ ≤
        ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) := by
      intro k
      have e := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun θ => f 0 θ - f k θ)
        ((hint 0).sub (hint k)) (Filter.Eventually.of_forall (hGnn k))
      rw [← e, MeasureTheory.integral_sub (hint 0) (hint k)]
      exact ENNReal.ofReal_le_ofReal (by linarith [hlow k])
    calc ∫⁻ θ, ENNReal.ofReal (f 0 θ - F θ) ∂μ
        = ∫⁻ θ, liminf (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop ∂μ := by
          congr 1
          funext θ
          exact ((hlim θ).liminf_eq).symm
      _ ≤ liminf (fun k : ℕ => ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ) atTop :=
          MeasureTheory.lintegral_liminf_le' fun k => ((hint 0).sub (hint k)).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) :=
          Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hterm)
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hFint : MeasureTheory.Integrable F μ :=
    ((hint 0).sub hGint).congr (Filter.Eventually.of_forall fun θ => by simp)
  have hlimI := MeasureTheory.integral_tendsto_of_tendsto_of_antitone hint hFint
    (Filter.Eventually.of_forall hanti) (Filter.Eventually.of_forall htend)
  have hge : 2 * Real.pi * φ z ≤ ∫ θ, F θ ∂μ := ge_of_tendsto' hlimI hlow
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mpr hFint, ?_⟩
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le h2π]
  have h4 := mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr h2π)
  rwa [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul] at h4

end GlobalTheory.CompanionTheory.AnForm.PshLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularEverywhereIsIntegral
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germ_top_stalk_closed_point {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {q : X}
    (hq : ξ (IsLocalRing.closedPoint Ω) ⤳ q) :
    X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) ≫ X.presheaf.stalkSpecializes hq ≫ Scheme.stalkClosedPointTo ξ
      = ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
  have e : ∀ (f : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ ξ ⁻¹ᵁ ⊤),
      (Spec (CommRingCat.of Ω)).presheaf.map f.op = 𝟙 _ := fun f => (Spec (CommRingCat.of Ω)).presheaf.map_id _
  erw [e]
  simp

theorem algebraMap_mem_regAt' {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (h : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (p : Cpt ξ) (o : O) :
    algebraMap O Ω o ∈ regAt ξ p := by
  obtain ⟨q, hq⟩ := p
  refine ⟨X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)), ?_⟩
  have h1 := germ_top_stalk_closed_point ξ hq
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
      = CommRingCat.ofHom (algebraMap O Ω) := by
    have : s.appTop ≫ ξ.appTop = (ξ ≫ s).appTop := by simp
    rw [reassoc_of% this, h]
    simp
  have h3 := congrArg (fun f => f.hom o) h2
  have h4 := congrArg (fun f => f.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  rw [CommRingCat.hom_ofHom] at h3
  refine Eq.trans ?_ (h4.trans h3)
  rfl

theorem isIntegral_of_forall_valuationSubring' {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (hf : Function.Injective (algebraMap R Ω)) (a : Ω)
    (H : ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap R Ω r ∈ V) → a ∈ V) : IsIntegral R a := by
  have hall : a ∈ ⨅ V : {V : ValuationSubring Ω // Set.range (algebraMap R Ω) ⊆ V.toSubring}, V.1.toSubring :=
    Subring.mem_iInf.mpr fun V => H V.1 fun r => V.2 ⟨r, rfl⟩
  rw [iInf_valuationSubring_superset, Subalgebra.mem_toSubring, mem_integralClosure_iff] at hall
  let g : R →+* Subring.closure (Set.range (algebraMap R Ω)) :=
    (algebraMap R Ω).codRestrict _ fun r => Subring.subset_closure ⟨r, rfl⟩
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => hf (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    have hle : Subring.closure (Set.range (algebraMap R Ω)) ≤ (algebraMap R Ω).range :=
      Subring.closure_le.mpr fun z hz => hz
    obtain ⟨r, rfl⟩ := hle hy
    exact ⟨r, rfl⟩
  let e := RingEquiv.ofBijective g hg
  have hcomp : (algebraMap R Ω).comp (e.symm : _ →+* R) =
      (RingHom.id Ω).comp (algebraMap (Subring.closure (Set.range (algebraMap R Ω))) Ω) := by
    ext x
    have : g (e.symm x) = x := e.apply_symm_apply x
    exact congrArg Subtype.val this
  exact IsIntegral.map_of_comp_eq (e.symm : _ →+* R) (RingHom.id Ω) hcomp hall

theorem isIntegral_and_isAlgebraic_of_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ a : Ω, ((∀ p : Cpt ξ, a ∈ regAt ξ p) → IsIntegral O a) ∧ ((∀ p ∈ genFibre O ξ, a ∈ regAt ξ p) → IsAlgebraic O a) := by
  intro X Ω _ ξ O _ _ _ s _ h hinj _ a
  refine ⟨fun ha => isIntegral_of_forall_valuationSubring' hinj a fun V hV => ?_, fun ha => ?_⟩
  · obtain ⟨p, hp, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper X Ω ξ O s h V hV
    exact hp (ha p)
  · haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj
    letI := FractionRing.liftAlgebra O Ω
    haveI : IsScalarTower O (FractionRing O) Ω := inferInstance
    refine (IsFractionRing.isAlgebraic_iff O (FractionRing O) Ω).2 (IsIntegral.isAlgebraic
      (isIntegral_of_forall_valuationSubring' (algebraMap (FractionRing O) Ω).injective a fun V hV => ?_))
    have hO : ∀ o : O, algebraMap O Ω o ∈ V := fun o => by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω]
      exact hV _
    obtain ⟨p, hp, hu⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper X Ω ξ O s h V hO
    refine hp (ha p fun o ho => ?_)
    have hne : algebraMap O Ω o ≠ 0 := fun h0 => ho (hinj (by simpa using h0))
    have hreg := algebraMap_mem_regAt' ξ s h p o
    have hinv : (algebraMap O Ω o)⁻¹ ∈ V := by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω, ← map_inv₀]
      exact hV _
    obtain ⟨g, hg, hga⟩ := hu _ hreg hne hinv
    obtain ⟨u, rfl⟩ := hg
    refine ⟨hne, hreg, ⟨(u⁻¹ : (X.presheaf.stalk p.1)ˣ).1, ?_⟩⟩
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hga, ← map_mul, Units.inv_mul, map_one]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorSumDualNumber
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanMul

abbrev red (C : Type) [CommRing C] : Sp C ⟶ Sp (DualNumber C) :=
  spMap (TrivSqZeroExt.fstHom C C C).toRingHom

theorem red_surj (C : Type) [CommRing C] (p : Sp (DualNumber C)) : ∃ q : Sp C, red C q = p := by
  let P : PrimeSpectrum (DualNumber C) := p
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ P.asIdeal := by
    intro a ha
    have h0 : a.fst = 0 := ha
    have h2 : a * a = 0 := by
      ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    have : a * a ∈ P.asIdeal := by rw [h2]; exact zero_mem _
    rcases P.isPrime.mem_or_mem this with h | h <;> exact h
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  haveI := P.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  refine ⟨(⟨_, hprime⟩ : PrimeSpectrum C), ?_⟩
  have e : PrimeSpectrum.comap (TrivSqZeroExt.fstHom C C C).toRingHom ⟨_, hprime⟩ = P := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom P.asIdeal) = P.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  exact e

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)


include hU in
theorem top_le {C : Type} [CommRing C] (t : Sp (DualNumber C) ⟶ X) (u : Γ(X, U) →+* C)
    (h : red C ≫ t = spMap u ≫ hU.fromSpec) : ⊤ ≤ t ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := red_surj C p
  show t (red C q) ∈ U
  have e : t (red C q) = hU.fromSpec (spMap u q) := by
    have := congrArg (fun f : Sp C ⟶ X => f q) h
    simpa using this
  rw [e]
  exact hU.range_fromSpec.subset (Set.mem_range_self _)

def ringOf {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem ringOf_spec {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) :
    spMap (ringOf t h) ≫ hU.fromSpec = t := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec t hU (isAffineOpen_top (Spec (CommRingCat.of A))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : spMap (ringOf t h) = Spec.map (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) := by
    unfold ringOf spMap
    rw [CommRingCat.ofHom_hom]
  rw [e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

include hU in
theorem ring_inj {A : Type} [CommRing A] {f g : Γ(X, U) →+* A}
    (h : spMap f ≫ hU.fromSpec = spMap g ≫ hU.fromSpec) : f = g := by
  rw [cancel_mono] at h
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

theorem ringOf_eq {A : Type} [CommRing A] {t : Sp A ⟶ X} (h : ⊤ ≤ t ⁻¹ᵁ U) {f : Γ(X, U) →+* A}
    (e : t = spMap f ≫ hU.fromSpec) : ringOf t h = f :=
  ring_inj hU ((ringOf_spec hU t h).trans e)

variable {S : Scheme.{0}} {C : Type} [CommRing C] (y : Sp C ⟶ S)

def redO : Over.mk y ⟶ epsAt y :=
  Over.homMk (red C) (by
    have h : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (algebraMap C (DualNumber C)) = RingHom.id C := by
      ext a; simp
    show red C ≫ spMap (algebraMap C (DualNumber C)) ≫ y = y
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    simp)

def projO : epsAt y ⟶ Over.mk y :=
  Over.homMk (spMap (algebraMap C (DualNumber C))) rfl

theorem comp_one_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem comp_mul_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) (a b : T ⟶ G) :
    f ≫ (a * b) = (f ≫ a) * (f ≫ b) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  intro S G _ U hU C _ y u hu v w hv hw φ ψ χ hφ hψ hχ hs ev ew
  have rv : redO y ≫ v = 1 := Over.OverMorphism.ext hv
  have rw' : redO y ≫ w = 1 := Over.OverMorphism.ext hw
  have rvw : redO y ≫ (v * w) = 1 := by rw [comp_mul_O, rv, rw', _root_.one_mul]
  have r1 : redO y ≫ (1 : epsAt y ⟶ G) = 1 := comp_one_O _
  have lv : red C ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans hu
  have lw : red C ≫ w.left = spMap u ≫ hU.fromSpec := hw.trans hu
  have lvw : red C ≫ (v * w).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) rvw).trans hu
  have l1 : red C ≫ (1 : epsAt y ⟶ G).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) r1).trans hu
  have hv' := top_le hU _ u lv
  have hw' := top_le hU _ u lw
  have hvw := top_le hU _ u lvw
  have h1 := top_le hU _ u l1
  have e1 : (1 : epsAt y ⟶ G).left = spMap ((algebraMap C (DualNumber C)).comp u) ≫ hU.fromSpec := by
    have p1 : projO y ≫ (1 : Over.mk y ⟶ G) = 1 := comp_one_O _
    have p2 : spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left = (1 : epsAt y ⟶ G).left :=
      congrArg (fun f => CommaMorphism.left f) p1
    rw [← p2, hu, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw) = u := by
    apply ring_inj hU
    have : spMap ((TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw)) =
        red C ≫ spMap (ringOf (v * w).left hvw) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc, ringOf_spec hU, lvw]
  have hχ' : ringOf (v * w).left hvw = χ := by
    ext s
    · rw [hχ]
      exact RingHom.congr_fun hfst s
    · have key := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom.hom
        (_root_.GlobalTheory.CompanionTheory.Ar.SqAdd.tan_mul_add S G C y v w hv hw U hv' hw' hvw h1 s)
      rw [map_add (f := _), map_add (f := _)] at key
      change ringOf (v * w).left hvw s + ringOf (1 : epsAt y ⟶ G).left h1 s =
        ringOf v.left hv' s + ringOf w.left hw' s at key
      rw [ringOf_eq hU h1 e1, ringOf_eq hU hv' ev, ringOf_eq hU hw' ew] at key
      have := congrArg TrivSqZeroExt.snd key
      have h0 : TrivSqZeroExt.snd (((algebraMap C (DualNumber C)).comp u) s) = 0 := by
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, h0, add_zero] at this
      rw [hs, this]
  rw [← hχ', ringOf_spec hU]

end GlobalTheory.CompanionTheory.Ar.TanMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationRingCentreInChart
section
noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

theorem isUnit_valuationSubring_iff {Ω' : Type} [Field Ω'] (W : ValuationSubring Ω') (w : W) :
    IsUnit w ↔ (w : Ω') ≠ 0 ∧ (w : Ω')⁻¹ ∈ W := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_right_inv
    have hv' : (w : Ω') * (v : Ω') = 1 := congrArg Subtype.val hv
    refine ⟨left_ne_zero_of_mul_eq_one hv', ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hv']
    exact v.2
  · rintro ⟨h0, h1⟩
    refine IsUnit.of_mul_eq_one (⟨(w : Ω')⁻¹, h1⟩ : W) (Subtype.ext ?_)
    exact mul_inv_cancel₀ h0

theorem exists_domBy_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω Ω' : Type) [Field Ω] [Field Ω'] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (i : Ω →+* Ω') (W : ValuationSubring Ω') (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k j, i (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ W) → ∃ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q ∧ DomBy W.toSubring i ξ q := by
  intro K _ J _ Ω Ω' _ _ y X ξ hall htie i W c hy hW
  classical
  let x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩
  let M : PModel ℤ x :=
    { X := X
      ξ := ξ
      s := specZIsTerminal.from _
      hover := specZIsTerminal.hom_ext _ _
      all := hall
      tie := htie }
  have hxc : x c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have hch : ∀ a ∈ chRing ℤ x c, i a ∈ W := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a h =>
      obtain ⟨j, rfl⟩ := h
      have e : x j / x c = ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) := by
        simp only [x, Finset.prod_div_distrib]
      show i (x j / x c) ∈ W
      rw [e, map_prod]
      exact prod_mem fun k _ => hW k (j k)
    | algebraMap r =>
      rw [eq_intCast, map_intCast]
      exact intCast_mem W r
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  let φ : chRing ℤ x c →+* W :=
    (i.comp (chRing ℤ x c).toSubring.subtype).codRestrict W.toSubring fun a => hch a a.2
  let P : Ideal (chRing ℤ x c) := (IsLocalRing.maximalIdeal W).comap φ
  have hPp : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨q, ⟨hq, hP⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.chart_prime_point ℤ Ω _ x M c hxc P hPp
  have hu : ∀ u (hu : u ∈ chRing ℤ x c), i u ≠ 0 → (i u)⁻¹ ∈ W → unitAt M.ξ q u := by
    intro u hu h0 h1
    by_contra hn
    have hm : (⟨u, hu⟩ : chRing ℤ x c) ∈ P := (hP ⟨u, hu⟩).2 hn
    exact (IsLocalRing.mem_maximalIdeal _).1 hm
      ((isUnit_valuationSubring_iff W (φ ⟨u, hu⟩)).2 ⟨h0, h1⟩)
  have hv : ∀ v (hv : v ∈ chRing ℤ x c), unitAt M.ξ q v → (i v)⁻¹ ∈ W := by
    intro v hv h
    have hm : (⟨v, hv⟩ : chRing ℤ x c) ∉ P := fun hm => (hP ⟨v, hv⟩).1 hm h
    have : IsUnit (φ ⟨v, hv⟩) := by
      by_contra hn
      exact hm ((IsLocalRing.mem_maximalIdeal _).2 hn)
    exact ((isUnit_valuationSubring_iff W (φ ⟨v, hv⟩)).1 this).2
  have hdesc := (_root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation ℤ Ω _ x M c q hq).2
  refine ⟨q, hq, fun a ha => ?_, fun a ha ha0 hinv => ?_⟩
  · obtain ⟨u, huc, v, hvc, hvu, rfl⟩ := (hdesc a).1 ha
    rw [map_div₀, div_eq_mul_inv]
    exact mul_mem (hch u huc) (hv v hvc hvu)
  · obtain ⟨u, huc, v, hvc, hvu, rfl⟩ := (hdesc a).1 ha
    have hv0 : v ≠ 0 := hvu.1
    have hu0 : u ≠ 0 := fun h => ha0 (by rw [h, zero_div])
    have hiu : i u ≠ 0 := (map_ne_zero i).2 hu0
    have hiv : i v ≠ 0 := (map_ne_zero i).2 hv0
    have e : (i u)⁻¹ = (i (u / v))⁻¹ * (i v)⁻¹ := by
      rw [map_div₀]
      field_simp
    have hU : unitAt M.ξ q u := hu u huc hiu (e ▸ mul_mem hinv (hv v hvc hvu))
    have e2 : (u / v)⁻¹ = v * u⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    rw [e2]
    exact mul_mem hvu.2.1 hU.2.2

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

