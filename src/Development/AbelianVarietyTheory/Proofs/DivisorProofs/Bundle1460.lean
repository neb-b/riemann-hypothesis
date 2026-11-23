module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnValuationRings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneFormSkew
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC

open GlobalTheory.SmoothForms (gelfA)
open Formalism.REAL (GlRel qdet)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem qdet_mem {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (X : Fin m → Fin m → B) (S : Subalgebra ℂ B)
    (hS : ∀ a b, X a b ∈ S) (u : ℂ) : qdet X u ∈ S := by
  unfold qdet Formalism.REAL.qminor
  refine S.sum_mem fun π _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine S.add_mem ?_ (hS _ _)
  split_ifs
  exacts [S.algebraMap_mem _, S.zero_mem]

end General

end GlobalTheory.LeviHC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusSecPullLin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

variable {R : Type} [CommRing R] {m N : ℕ}

def lin (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : Fin (m + 1) → (O1 R N).Sec :=
  fun i => ∑ j, GlobalTheory.AbLaw.cst (PSpace.str R N) ⊤ (a i j) • coord R N j

def dom (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : (PSpace R N).Opens := ⨆ i, nonzeroLocus (lin a i)

theorem iSup_nonzeroLocus_secPull_lin (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) :
    ⨆ i, nonzeroLocus (GlobalTheory.Cartier.secPull (lin a i) (dom a).ι) = ⊤ := by
  simp only [GlobalTheory.Cartier.nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup]
  exact (dom a).ι_preimage_self

def proj (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : (dom a).toScheme ⟶ PSpace R m :=
  toProj ((dom a).ι ≫ PSpace.str R N) (fun i => GlobalTheory.Cartier.secPull (lin a i) (dom a).ι)
    (iSup_nonzeroLocus_secPull_lin a)

def liftDom {X : Scheme.{0}} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (φ : X ⟶ PSpace R N)
    (h : φ ⁻¹ᵁ dom a = ⊤) : X ⟶ (dom a).toScheme :=
  IsOpenImmersion.lift (dom a).ι φ (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x ∈ φ ⁻¹ᵁ dom a := h.ge trivial
    exact hx)

theorem liftDom_fac {X : Scheme.{0}} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (φ : X ⟶ PSpace R N)
    (h : φ ⁻¹ᵁ dom a = ⊤) : liftDom a φ h ≫ (dom a).ι = φ :=
  IsOpenImmersion.lift_fac _ _ _

end GlobalTheory.SpanVA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedPosValuationDvdUniformiser
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

open IsDedekindDomain

namespace GlobalTheory.InertiaUnram

theorem valuationSubring_valuation_lt_one_iff {L : Type} [Field L] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (x : L) : v.valuationSubring.valuation x < 1 ↔ v x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    Valuation.mem_valuationSubring_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [map_inv₀, not_le]
    constructor
    · rintro (h | h)
      · exact absurd h hx
      · exact (one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).1 h
    · intro h
      exact Or.inr ((one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).2 h)

theorem mem_iff_valuation_le_one (L S : Type) [Field L] [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra S L] [IsFractionRing S L] (W : ValuationSubring L) (hS : ∀ s : S, algebraMap S L s ∈ W)
    (P : HeightOneSpectrum S) (hP : P.asIdeal = GlobalTheory.ProlongConj.primeBelow S W hS) (x : L) :
    x ∈ W ↔ P.valuation L x ≤ 1 := by
  have hS' : ∀ s : S, algebraMap S L s ∈ (P.valuation L).valuationSubring := fun s =>
    (Valuation.mem_valuationSubring_iff _ _).2 (P.valuation_le_one s)
  have key : ∀ s : S, W.valuation (algebraMap S L s) < 1 ↔
      (P.valuation L).valuationSubring.valuation (algebraMap S L s) < 1 := by
    intro s
    rw [valuationSubring_valuation_lt_one_iff, ← GlobalTheory.ProlongConj.mem_primeBelow S hS, ← hP]
    exact (P.valuation_lt_one_iff_mem s).symm
  have hW : W = (P.valuation L).valuationSubring :=
    le_antisymm (GlobalTheory.ProlongConj.le_of_valuation_lt_one_iff S hS hS' key)
      (GlobalTheory.ProlongConj.le_of_valuation_lt_one_iff S hS' hS fun s => (key s).symm)
  rw [hW, Valuation.mem_valuationSubring_iff]

theorem mem_inertia_of_mem_inertia (K L S : Type) [Field K] [Field L] [Algebra K L] [CommRing S] [IsDomain S]
    [IsDedekindDomain S] [Algebra S L] [IsFractionRing S L] [MulSemiringAction (L ≃ₐ[K] L) S]
    (hact : ∀ (g : L ≃ₐ[K] L) (s : S), algebraMap S L (g • s) = g (algebraMap S L s))
    (P : HeightOneSpectrum S) (W : ValuationSubring L) (hW : ∀ x, x ∈ W ↔ P.valuation L x ≤ 1)
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L)) : σ ∈ inertia K W := by
  set v := P.valuation L with hv
  have hWeq : W = v.valuationSubring := by
    ext x
    rw [hW, Valuation.mem_valuationSubring_iff]
  have hS : ∀ s : S, algebraMap S L s ∈ W := fun s => (hW _).2 (P.valuation_le_one s)
  have aux : ∀ τ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), ∀ x, v x ≤ 1 → v (τ x) ≤ 1 ∧ v (τ x - x) < 1 := by
    intro τ hτ x hx
    have hτ' := AddSubgroup.mem_inertia.mp hτ
    obtain ⟨s, t, hs1, e⟩ := GlobalTheory.ProlongConj.exists_den S W hS ((hW x).2 hx)
    have hsP : s ∉ P.asIdeal := by
      intro hm
      have h1 : W.valuation (algebraMap S L s) < 1 := by
        rw [hWeq, valuationSubring_valuation_lt_one_iff]
        exact (P.valuation_lt_one_iff_mem s).2 hm
      rw [hs1] at h1
      exact lt_irrefl _ h1
    have va : v (algebraMap S L s) = 1 :=
      le_antisymm (P.valuation_le_one s) (not_lt.1 fun h => hsP ((P.valuation_lt_one_iff_mem s).1 h))
    have hdiff : ∀ u : S, v (τ (algebraMap S L u) - algebraMap S L u) < 1 := by
      intro u
      rw [← hact, ← map_sub]
      exact (P.valuation_lt_one_iff_mem _).2 (hτ' u)
    have va' : v (τ (algebraMap S L s)) = 1 := by
      have h := Valuation.map_add_eq_of_lt_right v (x := τ (algebraMap S L s) - algebraMap S L s)
        (y := algebraMap S L s) (by rw [va]; exact hdiff s)
      rw [sub_add_cancel, va] at h
      exact h
    have hs0 : algebraMap S L s ≠ 0 := fun h => by rw [h, map_zero] at va; exact zero_ne_one va
    have hs0' : τ (algebraMap S L s) ≠ 0 := fun h => by rw [h, map_zero] at va'; exact zero_ne_one va'
    have hx' : x = algebraMap S L t / algebraMap S L s := by rw [← e]; field_simp
    have hτx : τ x = τ (algebraMap S L t) / τ (algebraMap S L s) := by rw [hx', map_div₀]
    constructor
    · rw [hτx, map_div₀, va', div_one, ← hact]
      exact P.valuation_le_one _
    · have : τ x - x = ((τ (algebraMap S L t) - algebraMap S L t) * algebraMap S L s -
          algebraMap S L t * (τ (algebraMap S L s) - algebraMap S L s)) /
          (τ (algebraMap S L s) * algebraMap S L s) := by
        rw [hτx, hx']; field_simp; ring
      rw [this, map_div₀, map_mul v (τ _), va, va', _root_.mul_one, div_one]
      refine Valuation.map_sub_lt v ?_ ?_
      · rw [map_mul, va, _root_.mul_one]; exact hdiff t
      · rw [map_mul]
        calc v (algebraMap S L t) * v (τ (algebraMap S L s) - algebraMap S L s)
            ≤ 1 * v (τ (algebraMap S L s) - algebraMap S L s) :=
              mul_le_mul_left (P.valuation_le_one t) _
          _ < 1 := by rw [_root_.one_mul]; exact hdiff s
  rw [mem_inertia_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hW, hW]
    constructor
    · intro h
      have h2 := (aux σ hσ _ h).1
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h2
    · intro h
      exact (aux σ⁻¹ (inv_mem hσ) x h).1
  · rw [hWeq, valuationSubring_valuation_lt_one_iff]
    exact (aux σ hσ x ((hW x).1 hx)).2

theorem valuation_le_of_fixed (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L]
    [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L]
    (P : HeightOneSpectrum (integralClosure R L)) (π : R) (hπ : Irreducible π) (y : L)
    (hy : ∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) (hlt : P.valuation L y < 1) :
    P.valuation L y ≤ P.valuation L (algebraMap K L (algebraMap R K π)) := by
  rw [GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx R K L P π hπ, ← _root_.GlobalTheory.InertiaDVR.card_inertia_eq_ramificationIdx R K L P]
  exact _root_.GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia R K L P y hy hlt

theorem div_uniformiser_mem : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (W : ValuationSubring L), IsAbove R K W.toSubring →
    ∀ π : R, Irreducible π → ∀ y : L, (∀ τ ∈ inertia K W, τ y = y) → y ∈ W.nonunits →
    y / algebraMap K L (algebraMap R K π) ∈ W := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ W hW π hπ y hy hyW
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hc : SMulCommClass (L ≃ₐ[K] L) R L := ⟨fun g r x => by
    rw [← IsScalarTower.algebraMap_smul K r x, ← IsScalarTower.algebraMap_smul K r (g • x)]
    exact map_smul g _ _⟩
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : IsFractionRing (integralClosure R L) L := integralClosure.isFractionRing_of_finite_extension K L
  have hR : ∀ r : R, algebraMap R L r ∈ W := by
    intro r
    have : algebraMap R K r ∈ W.toSubring.comap (algebraMap K L) := by rw [hW]; exact ⟨r, rfl⟩
    exact this
  have hS : ∀ s : integralClosure R L, algebraMap (integralClosure R L) L s ∈ W :=
    fun s => GlobalTheory.ProlongConj.mem_of_isIntegral W hR s.2
  set c : L := algebraMap K L (algebraMap R K π) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, map_ne_zero_iff _ (algebraMap K L).injective,
      map_ne_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hcW : W.valuation c < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    have h1 : (algebraMap R K π)⁻¹ ∈ W.toSubring.comap (algebraMap K L) := by
      change algebraMap K L _ ∈ W
      rw [map_inv₀]; exact hinv
    rw [hW] at h1
    obtain ⟨s, hs⟩ := h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one s (IsFractionRing.injective R K ?_)
    rw [map_mul, hs, map_one, mul_inv_cancel₀]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).1 (by rw [← hc_def]; exact hc0)
  set P0 := GlobalTheory.ProlongConj.primeBelow (integralClosure R L) W hS
  have hP0 : P0 ≠ ⊥ := by
    intro h
    have hm : algebraMap R (integralClosure R L) π ∈ P0 := by
      rw [GlobalTheory.ProlongConj.mem_primeBelow, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R K L]
      exact hcW
    rw [h, Ideal.mem_bot] at hm
    apply hc0
    rw [hc_def, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (integralClosure R L) L, hm,
      map_zero]
  let P : HeightOneSpectrum (integralClosure R L) := ⟨P0, inferInstance, hP0⟩
  have hWv := mem_iff_valuation_le_one L (integralClosure R L) W hS P rfl
  have hI : ∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ ∈ inertia K W :=
    mem_inertia_of_mem_inertia K L (integralClosure R L) (fun _ _ => rfl) P W hWv
  have hlt : P.valuation L y < 1 := by
    rcases (ValuationSubring.mem_nonunits_iff_or W).1 hyW with h | h
    · rw [h, map_zero]; exact zero_lt_one
    · by_contra hge
      push_neg at hge
      apply h
      rw [hWv, map_inv₀]
      have h1 : P.valuation L y ≤ 1 := (hWv y).1 ((W.valuation_le_one_iff y).1 (le_of_lt (W.mem_nonunits_iff.1 hyW)))
      rw [le_antisymm h1 hge, inv_one]
  have key := valuation_le_of_fixed R K L P π hπ y (fun σ hσ => hy σ (hI σ hσ)) hlt
  rw [hWv, map_div₀]
  have hv0 : P.valuation L c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  rw [div_le_one₀ (zero_lt_iff.2 hv0)]
  exact key

end GlobalTheory.InertiaUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramified
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRed

theorem natCast_ne_zero_of_residue {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {m : ℕ} (h : (m : ResidueField R) ≠ 0) : (m : K) ≠ 0 := by
  intro h0
  apply h
  have h1 : (m : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, map_zero, h0])
  rw [← map_natCast (residue R), h1, map_zero]

theorem torsionUnramified_pow_of_tateUnramified {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    {V : ValuationSubring Ω} {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {l : ℕ} [Fact l.Prime] (hl : (l : K) ≠ 0) (h : TateUnramified A V l) (n : ℕ) :
    TorsionUnramified A V (l ^ n) := by
  intro σ hσ x hx
  obtain ⟨t, rfl⟩ := _root_.GlobalTheory.Published.tate_lev_surj l (ptOver K Ω ⟶ A) (_root_.GlobalTheory.SepClosedDiv.exists_pow_eq K Ω A hA l hl) n x hx
  rw [← lev_galTate, h σ hσ]
  rfl

theorem infinite_torsionUnramified_of_tateUnramified :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
      [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
      (V : ValuationSubring Ω), IsAbove R K V.toSubring →
      ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
      ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → TateUnramified A V l →
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V _ A _ _ hA l hp hl h
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hp.out.two_le) fun n => ⟨?_, ?_⟩
  · rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  · exact torsionUnramified_pow_of_tateUnramified hA (natCast_ne_zero_of_residue hl) h n

end GlobalTheory.AbVarRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainTsumRationalTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.ThetaUnfoldInt

theorem integral_fundamentalDomain_tsum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ h : (κ → AF F) → ℂ, Continuous h →
      (∃ B : ℝ, ∀ x : κ → AF F, Summable (fun η : κ → F => ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖) ∧
        ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ ≤ B) →
      ∫ x in 𝓕₁, ∑' η : κ → F, h ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ = ∫ u, h u ∂μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AF F) := borel _
  intro μ hμ 𝓕₁ h𝓕 hfin h hc hB
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨B, hB⟩ := hB
  haveI : Countable F := by
    have b := Module.finBasis ℚ F
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (GlobalTheory.ThetaUnfold.ratEquiv F κ)
  have hcont : ∀ η : κ → F, Continuous fun x => h ((fun i => algebraMap F (AF F) (η i)) + x) :=
    fun η => hc.comp (continuous_const.add continuous_id)
  have hreidx : ∀ f : (κ → AF F) → ENNReal,
      ∫⁻ x, f x ∂μ = ∑' η : κ → F, ∫⁻ x in 𝓕₁, f ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ := by
    intro f
    rw [h𝓕.lintegral_eq_tsum' f, ← ((GlobalTheory.ThetaUnfold.ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
    refine tsum_congr fun ξ => ?_
    simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
    rfl
  have hpt : ∀ x, ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ₑ ≤ ENNReal.ofReal B := by
    intro x
    obtain ⟨hs, hle⟩ := hB x
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal hle
  have hfinite : ∑' η : κ → F, ∫⁻ x in 𝓕₁, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum fun η => (hcont η).measurable.enorm.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hint : Integrable h μ := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    show ∫⁻ a, ‖h a‖ₑ ∂μ < ⊤
    rw [hreidx fun a => ‖h a‖ₑ]
    exact hfinite.lt_top
  rw [integral_tsum (fun η => (hcont η).aestronglyMeasurable) hfinite,
    h𝓕.integral_eq_tsum' h hint, ← ((GlobalTheory.ThetaUnfold.ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
  rfl

end GlobalTheory.ThetaUnfoldInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormDbar
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem dbarAt_congr {n : ℕ} {γ δ : V n → Alt n} {v : V n} (h : γ =ᶠ[𝓝 v] δ) :
    dbarAt γ v = dbarAt δ v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS : (fun x => (bas n).repr (γ x) S) =ᶠ[𝓝 v] fun x => (bas n).repr (δ x) S := h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx
  show GlobalTheory.dbar _ v (coordVec a) • _ = GlobalTheory.dbar _ v (coordVec a) • _
  rw [GlobalTheory.dbar_congr hS]

end GlobalTheory.CxForm
end

