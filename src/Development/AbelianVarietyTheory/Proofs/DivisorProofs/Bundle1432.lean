module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NegOneNotSqSqrtTwo
public import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PLocDict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.DotAddRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralRationalPairFundDomainEqIterated
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Pointwise

namespace GlobalTheory.PeriodicIterated

section General

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]

theorem prod_isAddFundamentalDomain (Γ₁ : AddSubgroup V) (Γ : AddSubgroup (V × V))
    (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁) (μ : Measure V) [SFinite μ]
    (𝓕₁ : Set V) (h : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) :
    IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) (μ.prod μ) := by
  refine ⟨h.nullMeasurableSet.prod h.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h.ae_covers
    filter_upwards [h1, h2] with p ha hb
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    exact ⟨⟨((a : V), (b : V)), (hΓ _).2 ⟨a.2, b.2⟩⟩, ha, hb⟩
  · intro g g' hne
    have hset : ∀ k : Γ, k +ᵥ (𝓕₁ ×ˢ 𝓕₁) =
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁) +ᵥ 𝓕₁) ×ˢ
          ((⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁) +ᵥ 𝓕₁) := by
      intro k
      ext ⟨x, y⟩
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod, AddSubgroup.vadd_def,
        AddSubgroup.coe_neg, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
    show μ.prod μ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₁)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₁))) = 0
    rw [hset g, hset g', Set.prod_inter_prod, Measure.prod_prod]
    by_cases h1 : (g : V × V).1 = (g' : V × V).1
    · have h2 : (g : V × V).2 ≠ (g' : V × V).2 := by
        intro h2
        exact hne (Subtype.ext (Prod.ext h1 h2))
      have := h.aedisjoint (i := ⟨(g : V × V).2, ((hΓ _).1 g.2).2⟩)
        (j := ⟨(g' : V × V).2, ((hΓ _).1 g'.2).2⟩) (fun h' => h2 (congrArg Subtype.val h'))
      rw [show μ _ = 0 from this, mul_zero]
    · have := h.aedisjoint (i := ⟨(g : V × V).1, ((hΓ _).1 g.2).1⟩)
        (j := ⟨(g' : V × V).1, ((hΓ _).1 g'.2).1⟩) (fun h' => h1 (congrArg Subtype.val h'))
      rw [show μ _ = 0 from this, zero_mul]

theorem lintegral_fundamentalDomain_eq_iterated (Γ₁ : AddSubgroup V) [Countable Γ₁]
    (Γ : AddSubgroup (V × V)) (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁)
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (mW : MeasurableSpace (V × V)) (hmW : mW = Prod.instMeasurableSpace)
    (ν : @Measure (V × V) mW) (hν : @Measure.IsAddHaarMeasure _ _ _ mW ν)
    (𝓕 : Set (V × V)) (h𝓕 : @IsAddFundamentalDomain Γ _ _ _ mW 𝓕 ν)
    (𝓕₁ : Set V) (h𝓕₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) :
    ∃ c₁ : ENNReal, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ ∀ G : V × V → ENNReal, @Measurable _ _ mW _ G →
      (∀ γ ∈ Γ, ∀ w, G (γ + w) = G w) →
      ∫⁻ w in 𝓕, G w ∂ν = c₁ * ∫⁻ x in 𝓕₁, ∫⁻ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  subst hmW
  haveI := hν
  haveI : Countable Γ := by
    have hinj : Function.Injective (fun k : Γ =>
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁), (⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁))) := by
      intro k k' hk
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk
      exact Subtype.ext (Prod.ext hk.1 hk.2)
    exact hinj.countable
  have hmeq := Measure.isAddLeftInvariant_eq_smul ν (μ.prod μ)
  set c : NNReal := Measure.addHaarScalarFactor ν (μ.prod μ)
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν (μ.prod μ)
  have hν' : ν = (c : ENNReal) • μ.prod μ := by
    rw [← ENNReal.smul_def]; exact hmeq
  refine ⟨(c : ENNReal), by exact_mod_cast hcpos.ne', ENNReal.coe_ne_top, fun G hG hper => ?_⟩
  have hD : IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) ν :=
    (prod_isAddFundamentalDomain Γ₁ Γ hΓ μ 𝓕₁ h𝓕₁).mono (by rw [hν']; exact Measure.smul_absolutelyContinuous)
  rw [h𝓕.setLIntegral_eq hD G (fun g x => hper g g.2 x), hν', Measure.restrict_smul,
    lintegral_smul_measure, ← Measure.prod_restrict, lintegral_prod _ hG.aemeasurable, smul_eq_mul]

end General

end GlobalTheory.PeriodicIterated

namespace GlobalTheory.PeriodicIterated

theorem countable_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  exact (AddMonoidHom.rangeRestrict_surjective _).countable

theorem mem_ratPair_iff_ratVec (F : Type) [Field F] [NumberField F] (κ : Type)
    (w : (κ → AF F) × (κ → AF F)) :
    w ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ ↔
      w.1 ∈ GlobalTheory.ThetaParseval.ratVec F κ ∧ w.2 ∈ GlobalTheory.ThetaParseval.ratVec F κ := by
  rw [GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff, GlobalTheory.ThetaParseval.mem_ratVec_iff,
    GlobalTheory.ThetaParseval.mem_ratVec_iff]
  constructor
  · rintro ⟨y, z, rfl⟩
    exact ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ⟨y, z, Prod.ext hy hz⟩

theorem lintegral_ratPair_fundamentalDomain_eq_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ (𝓕 : Set ((κ → AF F) × (κ → AF F))), @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
    ∃ c₁ : ENNReal, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) →
      ∫⁻ w in 𝓕, G w ∂ν = c₁ * ∫⁻ x in 𝓕₁, ∫⁻ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  intro F _ _ κ _ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := countable_ratVec F κ
  haveI := hμ
  exact lintegral_fundamentalDomain_eq_iterated (GlobalTheory.ThetaParseval.ratVec F κ)
    (GlobalTheory.WeilUnitaryTransport.ratPair F κ) (mem_ratPair_iff_ratVec F κ) μ (borel _)
    (Prod.borelSpace (α := κ → AF F) (β := κ → AF F)).measurable_eq.symm ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁

end GlobalTheory.PeriodicIterated

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocElEventuallyMem
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.FinFib

section Generic

variable {G : Type} [Group G]

def twR (θ : G →* G) (x y : G) : Prop := ∃ g, y = g⁻¹ * x * θ g

theorem twR_equiv (θ : G →* G) : Equivalence (twR θ) := by
  constructor
  · intro x
    exact ⟨1, by simp⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

def cls (θ : G →* G) (x : G) : TwCl θ := Quot.mk (twR θ) x

theorem cls_eq_iff (θ : G →* G) (x y : G) : cls θ x = cls θ y ↔ twR θ x y :=
  ⟨fun h => (twR_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem cls_rep (θ : G →* G) (c : TwCl θ) : cls θ c.rep = c := Quot.out_eq c

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locEl_eventually_mem (n : ℕ) (δ : GL (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
  filter_upwards [UnitStable.eventually_mem_KGL δ, UnitStable.eventually_mem_KGL (δ * thE E n δ)] with w h1 h2
  unfold locEl
  split_ifs
  · exact h2
  · exact h1

end GlobalTheory.BCT.FinFib

namespace GlobalTheory.BCT.FinFib

end GlobalTheory.BCT.FinFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayDescentRange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem localization_away_descent_range :
 ∀ (k : Type) [Field k] (P : Polynomial k) (T : Finset (Localization.Away P)), ∃ F : Finset k, ∀ (R : Subring k), (F : Set k) ⊆ R → ∀ (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → ∀ t ∈ T, t ∈ (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h).range := by
  classical
  intro k _ P T
  have hs : ∀ t : Localization.Away P, ∃ (f : Polynomial k) (n : ℕ),
      IsLocalization.mk' (Localization.Away P) f
        (⟨P ^ n, n, rfl⟩ : Submonoid.powers P) = t := by
    intro t
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers P) t
    obtain ⟨n, hn⟩ := s.2
    exact ⟨f, n, by congr 1; exact Subtype.ext hn⟩
  choose f n hfn using hs
  refine ⟨T.biUnion (fun t => (f t).coeffs), ?_⟩
  intro R hF P₁ h hP t ht
  have hlift : f t ∈ Polynomial.lifts R.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro m
    by_cases hm : (f t).coeff m = 0
    · exact ⟨0, by simp [hm]⟩
    · have : (f t).coeff m ∈ (T.biUnion (fun t => (f t).coeffs) : Set k) := by
        simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
        exact ⟨t, ht, Polynomial.coeff_mem_coeffs hm⟩
      exact ⟨⟨_, hF this⟩, rfl⟩
  obtain ⟨f₁, hf₁⟩ := (Polynomial.mem_lifts _).mp hlift
  refine ⟨IsLocalization.mk' (Localization.Away P₁) f₁
    (⟨P₁ ^ n t, n t, rfl⟩ : Submonoid.powers P₁), ?_⟩
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, hf₁,
    Polynomial.map_pow, hP]
  have key := IsLocalization.mk'_spec' (Localization.Away P) (f t)
    (⟨P ^ n t, n t, rfl⟩ : Submonoid.powers P)
  rw [hfn t] at key
  exact key.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayPolynomialSubringLiftInjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.descentLocInj : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∀ (R : Subring k) (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → Function.Injective (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h) := by
  intro k _ P hP R P₁ h _
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers P₁) z
  simp only at hz ⊢
  unfold IsLocalization.Away.lift at hz
  rw [IsLocalization.lift_mk'_spec, mul_zero] at hz
  have h2 := hz
  have hinj : Function.Injective (algebraMap (Polynomial k) (Localization.Away P)) :=
    IsLocalization.injective (Localization.Away P) (powers_le_nonZeroDivisors_of_noZeroDivisors hP)
  have h3 : f.map R.subtype = 0 := by
    apply hinj
    simpa using h2
  have h4 : f = 0 := by
    have := Polynomial.map_injective R.subtype Subtype.val_injective
    exact this (by simpa using h3)
  subst h4
  simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantChartPointCentreFactorTwo
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartGraph

theorem maj_cpt_le_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (cpt X x z) τ v ≤ 2 * X.maj x τ v ∧ X.maj x τ v ≤ 2 * X.maj (cpt X x z) τ v := by
  intro E _ _ _ r X x z hxo hz τ v
  have hx : x ∈ X.dom := ModeHalfA.dom_of_orth X hxo
  have ho : X.IsOrtho x := hxo
  have hZ := _root_.GlobalTheory.ChartGraph.zN_graphCoord_le E r X z hz
  have hy : X.xZ x (graphCoord X z) ∈ X.dom := OrthonormalChartBounds.xZ_mem_dom X hx ho (by linarith)
  obtain ⟨hdet, hcol⟩ := _root_.GlobalTheory.ChartGraph.cols_graph E r X x z τ
  have heq := _root_.GlobalTheory.MajCols.maj_eq_of_cols E r X (cpt X x z) (X.xZ x (graphCoord X z)) τ (chartMatrixTopBlock X z τ)
    (by rw [hdet]; exact one_ne_zero) (Data.gramPos_det_ne X hy τ) hcol v
  obtain ⟨h1, h2⟩ := UnipMove.MajH.maj_xZ' X hx ho (ρ := 1 / 50) (by norm_num) (by norm_num) hZ τ v
  have h0 : 0 ≤ X.maj x τ v := by
    rw [ModeHalfA.maj_orth X hxo]; exact Finset.sum_nonneg fun _ _ => by positivity
  rw [heq]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.ChartGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsSumEqDefinitePairsSum
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem marked_field_pairs_sum_eq_definite_pairs_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ := by
  intro p _ G ha hn wt sel hsel Kf f r K φ hr hf hφ
  obtain ⟨e, he⟩ := GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd p G ha hn sel hsel
  unfold markedSumIrr dSumIrr
  convert GlobalTheory.finsum_ite_eq_of_equiv _ _ e (fun a : Cls G => wt (Quot.out a).pol * (Quot.out a).term Kf f r K φ)
    (fun b : DCls G => wt (Quot.out b).pol * (Quot.out b).term Kf f r K φ) fun q => by
    obtain ⟨hpol, hterm⟩ := he q
    show wt (Quot.out (e q).1).pol * (Quot.out (e q).1).term Kf f r K φ = wt (Quot.out q.1).pol * (Quot.out q.1).term Kf f r K φ
    rw [hpol, hterm Kf f r K φ hr hf hφ]

end GlobalTheory.LKDef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaTransformMeas

open Filter Topology
open scoped Classical

section

variable (F : Type) [Field F] [NumberField F]

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_pureA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    Continuous (GlobalTheory.WeilM.pureA F f g) := by
  have h1 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 :=
    continuous_pi fun i => (continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  have h2 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => (x i).2 :=
    continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  exact (f.continuous.comp h1).mul (hg.1.continuous.comp h2)

theorem continuous_of_mem_schA {κ : Type} [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact continuous_pureA F f hg
  | zero => exact continuous_const
  | add _ _ _ _ h1 h2 => exact h1.add h2
  | smul c _ _ h => exact h.const_smul c

theorem countable_field : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

end

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)) := by
  intro F _ _ ψ hψ κ _ Φ hΦ
  letI : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
  haveI : BorelSpace ((κ → AF F) × (κ → AF F)) := ⟨rfl⟩
  haveI := countable_field F
  have hc := continuous_of_mem_schA F hΦ
  let T : (κ → F) → (κ → AF F) × (κ → AF F) → ℂ := fun ξ w =>
    GlobalTheory.WeilM.schr ψ w Φ (fun i => algebraMap F (AF F) (ξ i))
  have hT : ∀ ξ, Continuous (T ξ) := by
    intro ξ
    simp only [T, GlobalTheory.WeilM.schr]
    refine (hψ.1.comp ?_).mul (hc.comp ?_)
    · fun_prop
    · fun_prop
  have hs : ∀ w, Summable fun ξ => T ξ w := by
    intro w
    have h := GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F w.1 hΦ)
    refine Summable.of_norm_bounded h.norm fun ξ => ?_
    simp only [T, GlobalTheory.WeilM.schr, norm_mul, hψ.2.1, one_mul]
    exact le_rfl
  change Measurable fun w => ∑' ξ, T ξ w
  exact measurable_of_tendsto_metrizable' (atTop : Filter (Finset (κ → F)))
    (f := fun s w => ∑ ξ ∈ s, T ξ w) (fun s => Finset.measurable_sum s fun ξ _ => (hT ξ).measurable)
    (tendsto_pi_nhds.2 fun w => (hs w).hasSum)

end GlobalTheory.ThetaTransformMeas

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ProjField

def NormChart {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (N₀ : LB B.left) : Prop :=
  ∃ (W V : Over (Sp k)) (π : W ⟶ V) (a : W ⟶ B) (U : B.left.Opens) (N : LB (V ⊗ B).left) (n : N.Sec),
    IsFinite π.left ∧ IsOpenImmersion a.left ∧ Nonempty W.left ∧ LocallyOfFiniteType W.hom ∧
    IsAffineOpen U ∧ (U : Set B.left).Nonempty ∧ N.IsLB ∧ LBIso N (N₀.pull (snd V B).left) ∧
    ∀ x : (V ⊗ B).left, x ∈ Out.nonzeroLocus n ↔
      ∀ z : (W ⊗ B).left, (π ▷ B).left z = x → z ∈ ((fst W B ≫ a) * snd W B).left ⁻¹ᵁ U

end GlobalTheory.ProjField
end
end

