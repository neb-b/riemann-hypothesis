module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0453
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0617
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
section
namespace GlobalTheory.OTY.TwEst

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def wt (A : WeightedAtlas n Y ι La) (E : La) (β : ι → Y → ℂ) (z : Y → V n) (y : Y) : ℝ :=
  -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap (jdet A z) y)

def quot (A : WeightedAtlas n Y ι La) (h β : ι → Y → ℂ) (y : Y) : ℂ :=
  h (A.pick y) y / β (A.pick y) y


open scoped Classical in
def ext0 {Y : Type*} (U : Set Y) (f : U → ℂ) (y : Y) : ℂ :=
  if hy : y ∈ U then f ⟨y, hy⟩ else 0

theorem extendByZeroOnSubset_apply_coe {Y : Type*} (U : Set Y) (f : U → ℂ) (y : U) : ext0 U f y = f y := by
  simp [ext0, y.2]

end

end GlobalTheory.OTY.TwEst

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.nz_facts {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (L Λ : La) (s : Fin n → ι → Y → ℂ) (τ : ι → Y → ℂ) (C : ℝ) (hC0 : 0 < C)
    (hsq : ∀ y, A.sqn L s y ≤ 1) (hC : ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) (y : Y) (hy : y ∈ nz A τ) :
    y ∉ A.zeroSet s ∧ psi A L s y ≤ 0 ∧
      -psi A L s y ≤ (n : ℝ) * (-Real.log (A.nsq Λ τ y)) + (n : ℝ) * Real.log C := by
  have hτy : τ (A.pick y) y ≠ 0 := hy
  have hτ0 : 0 < A.nsq Λ τ y := by
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr hτy) 2) (Real.exp_pos _)
  have hs0 : 0 < A.sqn L s y := by
    by_contra hle
    push_neg at hle
    have := hC y
    nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hz' : ∀ k, s k (A.pick y) y = 0 := hz
    have : A.sqn L s y = 0 := by
      unfold WeightedAtlas.sqn WeightedAtlas.nsq
      simp [hz']
    linarith
  · unfold psi
    have := Real.log_nonpos hs0.le (hsq y)
    nlinarith
  · unfold psi
    have h1 : Real.log (A.nsq Λ τ y) ≤ Real.log C + Real.log (A.sqn L s y) := by
      rw [← Real.log_mul hC0.ne' hs0.ne']
      exact Real.log_le_log hτ0 (hC y)
    have := mul_le_mul_of_nonneg_left h1 hn
    nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinSumSmoothSectionDbarEnergyLe
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isSSec_finset_sum_and_n1_le_card_mul_sum (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (C : Cover A) (la : La) (T : Finset Y) (F : Y → ι → Y → ℂ)
    (hF : ∀ P ∈ T, A.IsSSec (A.kap + la) (F P)) :
    A.IsSSec (A.kap + la) (fun i y => ∑ P ∈ T, F P i y) ∧
      n1 C la (fun i y => ∑ P ∈ T, F P i y) ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, n1 C la (F P) := by
  refine ⟨⟨fun i => ?_, fun i j y hi hj => ?_⟩, ?_⟩
  · exact ContDiffOn.sum (fun P hP => (hF P hP).1 i)
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun P hP => (hF P hP).2 i j y hi hj)
  ·
    have key : ∀ a : Fin C.m,
        (∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P (C.idx a) y) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
      intro a
      set i := C.idx a with hi
      set e := A.chart i with he
      have hball : Metric.ball (C.c a) (C.r a) ⊆ e.target :=
        Metric.ball_subset_closedBall.trans (C.sub a)
      have hdiff : ∀ P ∈ T, ∀ v ∈ Metric.ball (C.c a) (C.r a),
          DifferentiableAt ℝ (F P i ∘ e.symm) v := fun P hP v hv =>
        ((hF P hP).1 i).differentiableOn (by simp) |>.differentiableAt
          (e.open_target.mem_nhds (hball hv))

      have hcont : ∀ P ∈ T, ContinuousOn (fun v => ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))) (Metric.ball (C.c a) (C.r a)) := by
        intro P hP
        have hfd : ContinuousOn (fderiv ℝ (F P i ∘ e.symm)) e.target :=
          ((hF P hP).1 i).continuousOn_fderiv_of_isOpen e.open_target (by simp)
        have hph : ContinuousOn (fun v => A.ph la i (e.symm v)) e.target :=
          (A.smooth_ph la i).continuousOn
        refine ENNReal.continuous_ofReal.comp_continuousOn ?_
        refine ContinuousOn.mul ?_ ((hph.mono hball).neg.rexp)
        refine continuousOn_finsetSum _ (fun j _ => ?_)
        refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
        unfold wdb
        refine ContinuousOn.div_const (ContinuousOn.add ?_ (continuousOn_const.mul ?_)) _
        · exact (hfd.clm_apply continuousOn_const).mono hball
        · exact (hfd.clm_apply continuousOn_const).mono hball
      have hpt : ∀ v ∈ Metric.ball (C.c a) (C.r a),
          ENNReal.ofReal ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P i y) ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))
          ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) := by
        intro v hv
        have hfun : (fun y => ∑ P ∈ T, F P i y) ∘ e.symm = fun w => ∑ P ∈ T, (F P i ∘ e.symm) w := rfl
        rw [hfun]
        have hs : ∀ j, wdb n j (fun w => ∑ P ∈ T, (F P i ∘ e.symm) w) v
            = ∑ P ∈ T, wdb n j (F P i ∘ e.symm) v := fun j => wdb_sum T (fun P hP => hdiff P hP v hv)
        simp only [hs]
        have hE := Real.exp_pos (-A.ph la i (e.symm v))
        have hreal : (∑ j, ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))
            ≤ (T.card : ℝ) * ∑ P ∈ T, (∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
              Real.exp (-A.ph la i (e.symm v)) := by
          rw [← Finset.sum_mul, ← mul_assoc, Finset.sum_comm, Finset.mul_sum]
          refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) hE.le
          calc ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2
              ≤ (∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
            _ ≤ (T.card : ℝ) * ∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2 :=
                sq_sum_le_card_mul_sum_sq
        refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
      calc _ ≤ ∫⁻ v in Metric.ball (C.c a) (C.r a), (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) :=
            lintegral_mono_ae ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).2
              (Filter.Eventually.of_forall hpt))
        _ = _ := by
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
            lintegral_finsetSum' _ (fun P hP => (hcont P hP).aemeasurable
              Metric.isOpen_ball.measurableSet)]
    unfold n1
    calc _ ≤ ∑ a, (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) :=
          Finset.sum_le_sum fun a _ => key a
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetOfRingHomCompEqOfFinite
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem finite_setOf_ringHom_comp_eq_of_finite : ∀ (A Ω K : Type) [CommRing A] [CommRing Ω] [Field K]
    (φ : A →+* Ω) (ρ : A →+* K), φ.Finite → Set.Finite {τ : Ω →+* K | τ.comp φ = ρ} := by
  intro A Ω K _ _ _ φ ρ hφ
  classical
  letI : Algebra A Ω := φ.toAlgebra
  haveI : Module.Finite A Ω := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := Ω)
  haveI : Algebra.IsIntegral A Ω := Algebra.IsIntegral.of_finite A Ω
  have hint : ∀ g : Ω, ∃ p : Polynomial A, p.Monic ∧ p.eval₂ φ g = 0 := fun g => by
    obtain ⟨q, hq, he⟩ := Algebra.IsIntegral.isIntegral (R := A) g
    exact ⟨q, hq, he⟩
  choose p hpm hpe using hint
  let F : (Ω →+* K) → (s → K) := fun τ g => τ g
  apply Set.Finite.of_finite_image (f := F)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun g : s => (((p g).map ρ).roots.toFinset : Set K))
      (fun _ => Finset.finite_toSet _)) ?_
    rintro _ ⟨τ, hτ, rfl⟩ g _
    have hτ' : τ.comp φ = ρ := hτ
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm g).map ρ).ne_zero, Polynomial.IsRoot, Polynomial.eval_map,
      ← hτ', ← Polynomial.hom_eval₂, hpe, map_zero]
  · intro τ₁ h₁ τ₂ h₂ he
    have h₁' : τ₁.comp φ = ρ := h₁
    have h₂' : τ₂.comp φ = ρ := h₂
    ext x
    have hx : x ∈ Submodule.span A (s : Set Ω) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact congrFun he ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy =>
      rw [Algebra.smul_def, map_mul, map_mul, hy]
      congr 1
      exact (RingHom.congr_fun h₁' a).trans (RingHom.congr_fun h₂' a).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalResidueTensorInjective
section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem mem_smul_top_iff_wSub {p : ℕ} [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (x : D.La) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.La) ↔ x ∈ wSub D w0 r := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun c hc z _ => ?_) (fun u v hu hv => add_mem hu hv)
    exact Submodule.subset_span ⟨c, hc, z, rfl⟩
  · intro hx
    suffices H : ∀ b : D.O, b • x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.La) by simpa using H 1
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, z', rfl⟩ := hz
      intro b
      rw [smul_smul, ← Algebra.commutes, ← smul_smul]
      exact Submodule.smul_mem_smul (M := D.La) hc Submodule.mem_top
    | zero => intro b; rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => intro b; rw [smul_add]; exact add_mem (hu b) (hv b)
    | smul a u _ hu => intro b; rw [smul_smul]; exact hu (b * a)

theorem latQuot_free : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ),
    w0.IsMaximal →
    ∃ g : D.La →+ (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r), Function.Surjective g ∧
      (∀ (c : 𝓞 D.F) (x : D.La), g (algebraMap (𝓞 D.F) D.O c • x) = Ideal.Quotient.mk (w0 ^ r) c • g x) ∧
      ∀ x, g x = 0 ↔ x ∈ GlobalTheory.UPel.HT.EtLev.wSub D w0 r := by
  intro p _ D w0 r hw
  letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := projective_La_int D
  haveI := D.finLa
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  obtain ⟨g, hs, hk⟩ := GlobalTheory.T.exists_surjective_pi_quotient_pow_ker_eq w0 hw r _ (GlobalTheory.T.finrank_La_ringOfIntegers' D)
  refine ⟨g.toAddMonoidHom, hs, fun c x => ?_, fun x => ?_⟩
  · show g (c • x) = _
    rw [map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    rfl
  · show g x = 0 ↔ _
    rw [hk]
    exact mem_smul_top_iff_wSub D w0 r x

end GlobalTheory.UPel.HT.EtLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsAffineOpenOfFlatScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.CechDR

theorem flat_sec (R' : Type) [CommRing R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (hs : Flat s')
    (U : X'.affineOpens) : Module.Flat R' (Sec s' U.1) := by
  have h1 : (s'.appLE ⊤ U.1 le_top).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) s' hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h2 : (secMap s' U.1).hom.Flat := by
    exact RingHom.Flat.comp h0 h1
  exact h2

end GlobalTheory.CechDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartGroupLawEvalRightUnitStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_groupLaw_eval_right_unit : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A)}) A] {d : ℕ} (x : Fin d → A) (ev : MvPowerSeries (Fin d) O →ₐ[O] A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p x ev → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, ev (op μ (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0) i) = x i := by
  first | exact @GlobalTheory.chart_unit | exact GlobalTheory.chart_unit | (intros; apply GlobalTheory.chart_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalIsomorphismTransport
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_rep_pow_of_le : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r r' : ℕ), r ≤ r' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Etale H.hom → (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → ∃ (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom ∧ Etale K.hom ∧ (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x := by
  intro p _ D R _ b N w0 r r' hrr' S _ s o H i hHf hHe hi hH
  haveI := hHf
  haveI := hHe
  have hmh := o.act.hom

  let kil : ∀ (T : Over S) (x : T ⟶ o.A), Ideal (𝓞 D.F) := fun T x =>
    { carrier := {c | x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1}
      add_mem' := by
        intro a c ha hc
        simp only [Set.mem_ofPred_eq] at ha hc ⊢
        rw [map_add (f := _), o.act.add, comp_mul, ha, hc, _root_.mul_one]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        have h0 := o.act.add 0 0
        rw [add_zero] at h0
        have h1 : x ≫ o.act.act 0 = x ≫ o.act.act 0 * x ≫ o.act.act 0 := by rw [← comp_mul, ← h0]
        exact mul_eq_left.1 h1.symm
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hc ⊢
        rw [map_mul, o.act.mul, ← Category.assoc, hc, one_comp] }
  obtain ⟨s0, hs0⟩ := IsNoetherian.noetherian (w0 ^ r)
  have hgen : ∀ (T : Over S) (x : T ⟶ o.A),
      (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ↔
        ∀ c : s0, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T x
    constructor
    · intro h c
      exact h c (hs0 ▸ Submodule.subset_span c.2)
    · intro h c hc
      have hle : Submodule.span (𝓞 D.F) (s0 : Set (𝓞 D.F)) ≤ kil T x :=
        Submodule.span_le.2 fun c hc => h ⟨c, hc⟩
      rw [← hs0] at hc
      exact hle hc
  have hle : w0 ^ r' ≤ w0 ^ r := Ideal.pow_le_pow_right hrr'
  have hmono : ∀ (T : Over S) (y y' : T ⟶ H), y ≫ i = y' ≫ i → y = y' := by
    intro T y y' e
    have hk : ∀ c ∈ w0 ^ r', (y' ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
      rw [Category.assoc, hi c hc, comp_one]
    exact (hH T _ hk).unique e rfl
  have hf0 : ∀ c : s0, ∃ f : H ⟶ H, f ≫ i = i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := by
    intro c
    refine (hH H _ fun c' hc' => ?_).exists
    rw [Category.assoc, ← o.act.mul, ← map_mul]
    exact hi _ (Ideal.mul_mem_right _ _ hc')
  choose f hf using hf0
  obtain ⟨e, he⟩ := (hH _ (1 : 𝟙_ (Over S) ⟶ o.A) fun c _ => one_comp _).exists
  have htr : ∀ (T : Over S) (h : T ⟶ H), (∀ c : s0, h ≫ f c = h ≫ toUnit H ≫ e) ↔
      ∀ c ∈ w0 ^ r, (h ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T h
    rw [hgen]
    refine forall_congr' fun c => ⟨fun e1 => ?_, fun e1 => ?_⟩
    · have e2 := congrArg (· ≫ i) e1
      simp only [Category.assoc, hf, he, comp_one] at e2
      rw [Category.assoc]
      exact e2
    · apply hmono
      simp only [Category.assoc, hf, he, comp_one]
      rw [← Category.assoc]
      exact e1
  obtain ⟨U, hUc, hU⟩ := GlobalTheory.LevCover.ClopenCond.forall_finite (T := H)
    (P := fun (c : s0) (T' : Over S) (h : T' ⟶ H) => h ≫ f c = h ≫ toUnit H ≫ e)
    fun c => GlobalTheory.LevCover.clopenCond_eq (f c) (toUnit H ≫ e)
  obtain ⟨K, iK, hKf, hKe, hiKm, hiK⟩ := GlobalTheory.LevCover.exists_sub U hUc
  refine ⟨K, iK ≫ i, hKf, hKe, ?_, ?_⟩
  · exact (htr K iK).1 ((hU K iK).2 ((hiK K iK).2 ⟨𝟙 _, Category.id_comp _⟩))
  · intro T x hx
    have hx' : ∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => hx c (hle hc)
    obtain ⟨y0, hy0, -⟩ := hH T x hx'
    have hr : Set.range y0.left ⊆ U := (hU T y0).1 ((htr T y0).2 (by rw [hy0]; exact hx))
    obtain ⟨y, hy⟩ := (hiK T y0).1 hr
    refine ⟨y, show y ≫ iK ≫ i = x by rw [← Category.assoc, hy, hy0], fun y' hy' => ?_⟩
    haveI := hiKm
    apply (cancel_mono iK).1
    apply hmono
    rw [Category.assoc, Category.assoc, hy', ← Category.assoc, hy, hy0]

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourFRLeMinGOfSizeG
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem four_f_r_le_k_pow_eight (R : Ranks) : 4 * R.f * R.r ≤ R.k ^ 8 := by
  have hf : R.f ≤ R.k := by
    unfold Ranks.f Ranks.n
    exact R.f_le_k
  have h2 := R.two_le_m
  have h3 := R.m_add_three_le_k
  have hr : R.r ≤ 2 * R.k := by
    unfold Ranks.r
    omega
  have hk : 2 ≤ R.k := by omega
  have h6 : 8 ≤ R.k ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hk 6)
  calc 4 * R.f * R.r ≤ 4 * R.k * (2 * R.k) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hf) hr
    _ = 8 * R.k ^ 2 := by ring
    _ ≤ R.k ^ 6 * R.k ^ 2 := Nat.mul_le_mul_right _ h6
    _ = R.k ^ 8 := by ring

theorem four_f_r_le_min_g_of_sizeG {D : D7} (L : SizeData₂ D) (h : SizeG L) : Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D := by
  have hb : (1 : ℝ) ≤ L.sc.b := by
    unfold Scale.b Scale.L
    exact Real.one_le_exp (Real.rpow_nonneg (le_trans zero_le_one L.sc.one_lt_alt.le) _)
  have key : ∀ i : Fin 2, 4 * D.R.f * D.R.r ≤ D.host.g i := by
    intro i
    have h1 := (h i i).1
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have h2 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 :=
      pow_le_pow_left₀ hk (le_mul_of_one_le_right hk hb) 8
    have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2.trans h1
    exact (four_f_r_le_k_pow_eight D.R).trans h3
  unfold Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound
  exact le_min (key 0) (key 1)

theorem four_f_r_le_min_g_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x →
    ∀ i : Fm.Ix x, Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound (Fm.D x i) := by
  intro eps Fm
  refine ⟨0, fun x _ hx i => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := Fm.sizes x hx i
  exact four_f_r_le_min_g_of_sizeG _ hG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreMulKTorsorHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_fibre_mulK_torsor_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left), y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left → ∃! a : GlobalTheory.UPel.HT.Hecke.heckeSub o LinearMap.id (N * k), y ≫ (GlobalTheory.UPel.HT.Hecke.transl a.1).left = y' := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.FibreMulK.fibre_mulK) | (exact GlobalTheory.UPel.HT.Hecke.FibreMulK.fibre_mulK) | (intros; apply GlobalTheory.UPel.HT.Hecke.FibreMulK.fibre_mulK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSublevelTailLeOfFiniteStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_sublevel_tail_le_of_finite : ∀ (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞) (x : Y → ℝ), Measurable x → ∫⁻ y, g y ∂μ < ⊤ → Measurable g → ∀ ε : ℝ≥0∞, 0 < ε → ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by
  first | exact @GlobalTheory.lintegral_sublevel_tail_le | exact GlobalTheory.lintegral_sublevel_tail_le | (intros; apply GlobalTheory.lintegral_sublevel_tail_le <;> assumption)
end

