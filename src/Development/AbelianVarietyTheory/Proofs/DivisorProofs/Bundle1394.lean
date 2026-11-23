module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwise
section
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem sq_le_sum_enorm_sq_lintegral_bound
    (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ) (hg : ∀ a, Continuous (g a))
    (hfg : ∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) :
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  by_cases hi : MeasureTheory.Integrable (fun x => f x ^ 2) μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi
      (MeasureTheory.ae_of_all _ (fun x => sq_nonneg (f x)))]
    have hm : ∀ a, Measurable (fun x => ‖g a x‖ₑ ^ 2) := fun a =>
      ((hg a).measurable.enorm).pow_const 2
    calc ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 ∂μ := by
          refine MeasureTheory.lintegral_mono (fun x => ?_)
          calc ENNReal.ofReal (f x ^ 2) ≤ ENNReal.ofReal (C * ∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_le_ofReal (hfg x)
            _ = ENNReal.ofReal C * ENNReal.ofReal (∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_mul' (Finset.sum_nonneg (fun a _ => sq_nonneg _))
            _ = ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 := by
                rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
                congr 1
                refine Finset.sum_congr rfl (fun a _ => ?_)
                rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      _ = ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
          rw [MeasureTheory.lintegral_const_mul _ (Finset.measurable_sum _ (fun a _ => hm a))]
          congr 1
          exact MeasureTheory.lintegral_finsetSum Finset.univ (fun a _ => hm a)
  · rw [MeasureTheory.integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfChartsSurjectiveImage
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotAbelian

theorem isAbelianScheme_of_charts_of_surjective :
    ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) [GrpObj A] [GrpObj G] (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) [∀ j, GrpObj (B j)] (ψ : ∀ j, (B j).left ⟶ G.left),
    IsAbelianScheme A → IsCommMonObj G → Surjective Q.left → (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) →
    (∀ j, IsAbelianScheme (B j)) → IsAbelianScheme G := by
  intro S 𝒰 A G _ _ Q B _ ψ hA hG hQ hψ hB
  have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have hsm : Smooth G.hom := GlobalTheory.GroupGlue.of_charts @Smooth hψ fun j => (hB j).smooth
  have hpr : IsProper G.hom := GlobalTheory.GroupGlue.of_charts @IsProper hψ fun j => (hB j).proper
  have hw : Q.left ≫ G.hom = A.hom := Over.w Q
  have := hA.geomConnected
  have : GeometricallyConnected (Q.left ≫ G.hom) := by rw [hw]; infer_instance
  exact ⟨hG, hsm, hpr, GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp Q.left G.hom⟩

end GlobalTheory.QuotAbelian
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutLaurentCoeffSubConst
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LaurentAut

open scoped ContDiff

theorem hasDerivAt_integral_cpt {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 ℂ] [ProperSpace 𝕜] {H : Type} [TopologicalSpace H] [T2Space H]
    [MeasurableSpace H] [OpensMeasurableSpace H] (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {Φ Φ' : 𝕜 → H → ℂ} {x₀ : 𝕜}
    {C : Set H} (hC : IsCompact C) (hc : ∀ t, Continuous (Φ t)) (hc' : Continuous fun p : 𝕜 × H => Φ' p.1 p.2)
    (h0 : ∀ t ∈ Metric.closedBall x₀ 1, ∀ y ∉ C, Φ t y = 0 ∧ Φ' t y = 0)
    (hd : ∀ t y, HasDerivAt (Φ · y) (Φ' t y) t) :
    HasDerivAt (fun t => ∫ y, Φ t y ∂μ) (∫ y, Φ' x₀ y ∂μ) x₀ := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ 1).prod hC).exists_bound_of_continuousOn hc'.continuousOn
  have hx : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  have hc0 : Continuous (Φ' x₀) := hc'.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := C.indicator fun _ => B)
    (Metric.closedBall_mem_nhds x₀ one_pos) ?_
    ((hc x₀).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).1))
    (hc0.integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).2)).aestronglyMeasurable
    (.of_forall fun y t ht => ?_) ?_ (.of_forall fun y t _ => hd t y)).2
  · filter_upwards [Metric.closedBall_mem_nhds x₀ one_pos] with t ht
    exact ((hc t).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 t ht y hy).1)).aestronglyMeasurable
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy]; exact hB (t, y) ⟨ht, hy⟩
    · rw [Set.indicator_of_notMem hy, (h0 t ht y hy).2, norm_zero]
  · exact (integrable_indicator_iff hC.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] {N : ℕ}
  {j : H →* G} {ι : H →* Matrix (Fin N) (Fin N) ℂ}

variable [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1)
include hι h1

variable [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]


end Abstract

section Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {N : ℕ} {ι : GInf σ J →* Matrix (Fin N) (Fin N) ℂ}
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1) {f : Matrix (Fin N) (Fin N) ℂ → ℝ}
include hι h1

variable {x : Matrix (Fin n) (Fin 1) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ}

end Unitary



end GlobalTheory.LaurentAut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IntCoefExt

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem nval_nonneg_iff {e : ℕ} (he : 0 < e) (x : K') : 0 ≤ nval V e x ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    simp [nval_zero, vV]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ he', zero_mul]
  exact_mod_cast Iff.rfl

theorem exists_nat_pos {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {ι : K →+* K'} {e : ℕ}
    (ho : OverLa la V ι e) : ∃ N : ℕ, N ≠ 0 ∧ 0 < vV V (N : K') := by
  have hN : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm la.asIdeal, hN, ?_⟩
  have h1 := ho.2 (Ideal.absNorm la.asIdeal : K)
  rw [map_natCast] at h1
  rw [h1]
  refine mul_pos (by exact_mod_cast ho.1) ?_
  have h2 : la.valuation K (Ideal.absNorm la.asIdeal : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) _).2 (Ideal.absNorm_mem la.asIdeal)
    simpa using this
  have h0 : la.valuation K (Ideal.absNorm la.asIdeal : K) ≠ 0 := by
    simpa using hN
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
  simp only [vLa]
  omega

theorem exists_overLa {K : Type} [Field K] [NumberField K] (ι : K →+* K') {N : ℕ} (hN : N ≠ 0)
    (h : 0 < vV V (N : K')) : ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la V ι e := by
  let u := (valV V (K' := K')).comap ι
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.CommonValuation.exists_centre u
  have hN' : (N : K') ≠ 0 := by
    rw [← map_natCast ι]
    exact (map_ne_zero ι).2 (Nat.cast_ne_zero.2 hN)
  have hNQ : (N : 𝓞 K) ∈ Q := by
    rw [hQm, map_natCast]
    show valV V (ι N) < 1
    rw [map_natCast, ← WithZero.exp_log (valV_ne_zero (V := V) hN'), ← WithZero.exp_zero, WithZero.exp_lt_exp]
    simp only [vV] at h
    omega
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hN (Nat.cast_eq_zero.1 ((Submodule.mem_bot _).1 hNQ))
  let la : HeightOneSpectrum (𝓞 K) := ⟨Q, hQ, h0⟩
  obtain ⟨e, he, hv⟩ := GlobalTheory.CommonValuation.exists_eq_pow la u
    (GlobalTheory.CommonValuation.le_one_of_ringOfIntegers u) (fun r => (hQm r).symm)
  refine ⟨la, e, he, fun a => ?_⟩
  have := hv a
  rw [Valuation.comap_apply] at this
  simp only [vV, vLa, this, WithZero.log_pow, nsmul_eq_mul]
  ring

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem integral_res_iff (T : CDVR) (io' : c'.F →+* T.Fr) (io : c.F →+* T.Fr)
    (h : ∀ a, io' (incF c c' hle a) = io a) (y : letI := io'.toAlgebra; FrPt Xo c' T.Fr) :
    Integral T io' y ↔ Integral T io (letI := io.toAlgebra; letI := io'.toAlgebra; y.res hle h) := by
  have e : ∀ (G : SAB H (Sp T.V)) τ v, IsEigV c' io' G τ v ↔ IsEigV c io G τ v := fun G τ v => by
    unfold IsEigV
    simp only [← embK_incF hle τ, h]
  constructor
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).1 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).2 he), h4⟩, h5⟩
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).2 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).1 he), h4⟩, h5⟩

theorem intAt_iff (f : Rul Xo c) : IntAt Xo c f ↔ ∀ (T : CDVR) (io : c.F →+* T.Fr) (N : ℕ), N ≠ 0 →
    0 < vV T.V (N : T.Fr) → T.FinRes → ∀ y : IntFr Xo c T io, 0 ≤ vV T.V (evI y f) := by
  constructor
  · intro h T io N hN hp hT y
    obtain ⟨la, e, ho⟩ := exists_overLa io hN hp
    exact (nval_nonneg_iff ho.1 _).1 (h la _ ⟨PtV.mk la ho y hT () trivial, rfl⟩)
  · rintro h la _ ⟨⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩, rfl⟩
    obtain ⟨N, hN, hp⟩ := exists_nat_pos ho
    exact (nval_nonneg_iff ho.1 _).2 (h T io N hN hp hy y)

theorem intAt_rulBC_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, (IntAt Xo c' (rulBC hle f) ↔ IntAt Xo c f) := by
  intro E _ _ _ H Dw l Xo c c' hle a n f hf
  have hval := ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2
  rw [intAt_iff, intAt_iff]
  constructor
  · intro h T io N hN hp hT y
    letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
    haveI := c.fin
    haveI := c'.fin
    haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun x => by simp
    haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ _ _
    obtain ⟨L, _, _, g, hL, -, hg⟩ := GlobalTheory.exists_finite_separable_compositum c.F T.Fr c'.F io
    obtain ⟨T', iT, e, ψ, -, he, hv, hψ, -, hfin⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
    obtain ⟨⟨y₁, -, -, φ, hφ, hm⟩, -⟩ := GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T T' io y iT e he hv
    let io' : c'.F →+* T'.Fr := ψ.toRingHom.comp g
    have hio : ∀ x, io' (incF c c' hle x) = (iT.comp io) x := fun x => by
      have := DFunLike.congr_fun hg x
      exact (congrArg ψ this).trans (hψ _)
    have hp' : 0 < vV T'.V (N : T'.Fr) := by
      rw [← map_natCast iT, hv]
      exact mul_pos (by exact_mod_cast he) hp
    have e1 : evI y₁ f = iT (evI y f) := by
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      exact (pos_evR (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φ y.1 y.2.1 y₁.1 hm).trans
        (DFunLike.congr_fun hφ _)
    letI := (iT.comp io).toAlgebra
    letI := io'.toAlgebra
    let y' : IntFr Xo c' T' io' := ⟨y₁.1.ext hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T' io' (iT.comp io) hio _).2 y₁.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y₁ f := hval T'.Fr hio y'.1
    have key := h T' io' N hN hp' (hfin hT) y'
    rw [e2, e1, hv] at key
    exact nonneg_of_mul_nonneg_right key (by exact_mod_cast he)
  · intro h T io' N hN hp hT y'
    let io : c.F →+* T.Fr := io'.comp (incF c c' hle)
    have hio : ∀ x, io' (incF c c' hle x) = io x := fun _ => rfl
    letI := io.toAlgebra
    letI := io'.toAlgebra
    let y : IntFr Xo c T io := ⟨y'.1.res hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T io' io hio _).1 y'.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y f := hval T.Fr hio y'.1
    rw [e2]
    exact h T io N hN hp hT y

end GlobalTheory.IntCoefExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleComp
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.DualityMap

open GlobalTheory.TypeTame

section Comp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def compEquiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (s : H →* G) :
    Representation.Equiv (π.comp s : Representation ℂ H V) (σ.comp s : Representation ℂ H W) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => φ.toIntertwiningMap.isIntertwining' (s g)

end Comp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem isSmooth_comp {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} (h : IsSmooth π) :
    IsSmooth (π.comp (invTranspose n) : Representation ℂ (GL (Fin n) k) V) :=
  fun v => (h v).preimage (continuous_invTranspose n)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isIrreducible_comp {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp (invTranspose n) : Representation ℂ (GL (Fin n) k) V) :=
  GlobalTheory.CosocleComp.isIrreducible_comp (fun g => ⟨_, invTranspose_invTranspose n g⟩) h

def dual (x : IrrGL (k := k)) : IrrGL (k := k) :=
  IrrGL.of (x.rep.comp (invTranspose x.1)) (isSmooth_comp x.2.rep.smooth) (isIrreducible_comp x.2.rep.irr)


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem dual_of {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    dual (IrrGL.of π hs hi) = IrrGL.of (π.comp (invTranspose n)) (isSmooth_comp hs) (isIrreducible_comp hi) :=
  IrrGL.of_eq_of.2 ⟨compEquiv (IrrGL.equivOf π hs hi).symm (invTranspose n)⟩


omit [IsNonarchimedeanLocalField k] in
theorem dual_dual (x : IrrGL (k := k)) : dual (dual x) = x := by
  refine (dual_of _ _ _).trans (Eq.trans (IrrGL.of_eq_of.2 ⟨?_⟩) (IrrGL.of_rep x))
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => ?_
  ext v
  show x.rep (invTranspose x.1 (invTranspose x.1 g)) v = x.rep g v
  rw [invTranspose_invTranspose]

end GlobalTheory.DualityMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeTorsionCoprimeIdealsProduct
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.CoprimeTors

theorem isIsogDeg_of_coprime : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [CommRing O]
    (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) (𝔞 𝔟 : Ideal O), 𝔞 ⊔ 𝔟 = ⊤ →
    ∀ (K₁ K₂ K₃ : Over S) (i₁ : K₁ ⟶ A) (i₂ : K₂ ⟶ A) (i₃ : K₃ ⟶ A), Mono i₁ → Mono i₂ → Mono i₃ →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₁ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔞 x) →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₂ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔟 x) →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₃ x ↔ GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) x) →
    ∀ (d e : ℕ), 0 < e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₃) (d * e) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₂) e →
    GlobalTheory.IwLevel.IsIsogDeg (toUnit K₁) d := by
  intro S A _ _ O _ ρ 𝔞 𝔟 hab K₁ K₂ K₃ i₁ i₂ i₃ _ _ _ h₁ h₂ h₃ d e he hK₃ hK₂
  have h1mem : (1 : O) ∈ 𝔞 ⊔ 𝔟 := hab ▸ Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1mem
  have k₁ : ∀ a ∈ 𝔞, i₁ ≫ ρ.act a = 1 := fun a ha => (h₁ K₁ i₁).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have k₂ : ∀ a ∈ 𝔟, i₂ ≫ ρ.act a = 1 := fun a ha => (h₂ K₂ i₂).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have k₃ : ∀ a ∈ 𝔞 * 𝔟, i₃ ≫ ρ.act a = 1 := fun a ha => (h₃ K₃ i₃).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have hadd : ∀ {T : Over S} (x : T ⟶ A) (a b : O),
      x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := fun x a b => by
    rw [ρ.map_add]; exact MonObj.comp_mul x _ _
  have hone : ∀ {T : Over S} (x : T ⟶ A), x ≫ ρ.act 1 = x := fun x => by
    rw [ρ.map_one, Category.comp_id]
  have e₁ : i₁ ≫ ρ.act v = i₁ := by
    have := hadd i₁ v u
    rw [add_comm v u, huv, hone, k₁ u hu, _root_.mul_one] at this
    exact this.symm
  have e₂ : i₂ ≫ ρ.act u = i₂ := by
    have := hadd i₂ u v
    rw [huv, hone, k₂ v hv, _root_.mul_one] at this
    exact this.symm
  have hm : GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) ((fst K₁ K₂ ≫ i₁) * (snd K₁ K₂ ≫ i₂)) := fun c hc => by
    have := ρ.hom c
    have hc₁ : c ∈ 𝔞 := Ideal.mul_le_left (I := 𝔞) (J := 𝔟) hc
    have hc₂ : c ∈ 𝔟 := Ideal.mul_le_right (I := 𝔞) (J := 𝔟) hc
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, k₁ c hc₁, k₂ c hc₂, MonObj.comp_one,
      MonObj.comp_one, _root_.mul_one]
  obtain ⟨m, hm'⟩ := (h₃ _ _).2 hm
  have hg₁ : GlobalTheory.IwLevel.KilledBy ρ 𝔞 (i₃ ≫ ρ.act v) := fun a ha => by
    rw [Category.assoc, ← ρ.map_mul]; exact k₃ _ (Ideal.mul_mem_mul ha hv)
  have hg₂ : GlobalTheory.IwLevel.KilledBy ρ 𝔟 (i₃ ≫ ρ.act u) := fun b hb => by
    rw [Category.assoc, ← ρ.map_mul, mul_comm]; exact k₃ _ (Ideal.mul_mem_mul hu hb)
  obtain ⟨g₁, hg₁'⟩ := (h₁ _ _).2 hg₁
  obtain ⟨g₂, hg₂'⟩ := (h₂ _ _).2 hg₂
  have iso : IsIso m := by
    refine ⟨⟨lift g₁ g₂, ?_, ?_⟩⟩
    · have hr := ρ.hom v
      have hs := ρ.hom u
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp, ← cancel_mono i₁, Category.assoc, hg₁',
          ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₁, k₂ v hv,
          MonObj.comp_one, _root_.mul_one]
      · rw [Category.assoc, lift_snd, Category.id_comp, ← cancel_mono i₂, Category.assoc, hg₂',
          ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₂, k₁ u hu,
          MonObj.comp_one, _root_.one_mul]
    · rw [← cancel_mono i₃, Category.assoc, hm', MonObj.comp_mul, ← Category.assoc, lift_fst,
        ← Category.assoc, lift_snd, hg₁', hg₂', ← hadd, add_comm, huv, hone, Category.id_comp]
  have hP : GlobalTheory.IwLevel.IsIsogDeg (toUnit (K₁ ⊗ K₂)) (d * e) := by
    rw [toUnit_unique (toUnit (K₁ ⊗ K₂)) (m ≫ toUnit K₃), ← _root_.one_mul (d * e)]
    exact (GlobalTheory.IwLevel.IsIsogDeg.of_isIso m).comp hK₃
  have hpb : IsPullback (fst K₁ K₂) (snd K₁ K₂) (toUnit K₁) (toUnit K₂) :=
    ⟨⟨toUnit_unique _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst c.snd) (fun _ ↦ lift_fst _ _)
      (fun _ ↦ lift_snd _ _) fun c m h₁ h₂ ↦ by ext <;> simp [h₁, h₂]⟩⟩
  have hfst : GlobalTheory.IwLevel.IsIsogDeg (fst K₁ K₂) e := hK₂.of_isPullback (hpb.flip.map (Over.forget S))
  have hcomp : fst K₁ K₂ ≫ toUnit K₁ = toUnit (K₁ ⊗ K₂) := toUnit_unique _ _
  have := hfst.fin; have := hfst.flat; have := hfst.surj
  have := hP.fin; have := hP.flat; have := hP.surj

  obtain ⟨t, -⟩ := (h₂ K₁ (1 : K₁ ⟶ A)).2 fun b _ => by have := ρ.hom b; exact MonObj.one_comp _
  let s : K₁ ⟶ K₁ ⊗ K₂ := lift (𝟙 K₁) t
  have hs : s ≫ fst K₁ K₂ = 𝟙 K₁ := lift_fst _ _
  have hsep : IsSeparated (fst K₁ K₂).left := inferInstance
  have : IsFinite (s.left ≫ (fst K₁ K₂).left) := by
    rw [← Over.comp_left, hs, Over.id_left]; infer_instance
  have : IsFinite s.left := IsFinite.of_comp s.left (fst K₁ K₂).left
  have hsu : s ≫ toUnit (K₁ ⊗ K₂) = toUnit K₁ := toUnit_unique _ _
  have hfin : IsFinite (toUnit K₁).left := by rw [← hsu, Over.comp_left]; infer_instance
  have : Flat ((fst K₁ K₂).left ≫ (toUnit K₁).left) := by rw [← Over.comp_left, hcomp]; infer_instance
  have hflat : Flat (toUnit K₁).left := flat_of_comp_of_flat_of_surjective (fst K₁ K₂).left _
  have : Surjective ((fst K₁ K₂).left ≫ (toUnit K₁).left) := by
    rw [← Over.comp_left, hcomp]; infer_instance
  have hsurj : Surjective (toUnit K₁).left := Surjective.of_comp (fst K₁ K₂).left _
  refine ⟨hfin, hflat, hsurj, fun y => ?_⟩
  have h := GlobalTheory.FinrankComp.finrank_comp_of_const (fst K₁ K₂).left (toUnit K₁).left e hfst.rank y
  rw [← Over.comp_left, hcomp, hP.rank, mul_comm d e] at h
  exact (Nat.eq_of_mul_eq_mul_left he h).symm

end GlobalTheory.IwLevel.CoprimeTors
end
end

