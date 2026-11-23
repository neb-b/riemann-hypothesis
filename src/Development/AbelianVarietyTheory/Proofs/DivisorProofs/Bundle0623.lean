module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.QuotientMetricDivisors.FinalW

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime]

theorem projective_La_int (D : Datum p) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    Module.Projective (𝓞 D.F) D.La := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := D.freeLa
  haveI := D.finLa
  have htor : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : (a : 𝓞 D.F) ≠ 0 := nonZeroDivisors.ne_zero a.2
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) ha0 (Ideal.mem_span_singleton_self (a : 𝓞 D.F))
      (Algebra.IsIntegral.isIntegral (R := ℤ) (a : 𝓞 D.F))
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at he
    obtain ⟨d, hd⟩ := he
    have h1 : e • x = 0 := by
      have : (algebraMap ℤ (𝓞 D.F) e) • x = e • x := by
        rw [algebraMap_smul]
      rw [← this, ← hd, mul_smul]
      change d • (a • x) = 0
      rw [hax, smul_zero]
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h he0
    · exact (Submodule.mem_bot _).2 h
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  have : Module.Flat (𝓞 D.F) D.La := (IsDedekindDomain.flat_iff_torsion_eq_bot).2 htor
  have := Module.finitePresentation_of_finite (𝓞 D.F) D.La
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory.UPel.HT.EtLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPower
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

open TensorProduct WithConv Coalgebra

namespace GlobalTheory.NMul

theorem isAdicComplete_ring_of_module {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

end GlobalTheory.NMul

namespace GlobalTheory.NMul

theorem ev_nmul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n k : ℕ) (i : Fin d),
      c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n k
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A n) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := isAdicComplete_ring_of_module (O := O) p
  have hT := (_root_.GlobalTheory.CEval.continuous_eval p O (G.A n) (Fin d) (c.x n) (c.nil n)).2 (c.ev n) (c.isEval n)
  have hsucc : ∀ (k : ℕ) (j : Fin d), nmul c.μ (k + 1) j =
      subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ j) := by
    intro k j
    simp only [nmul, Function.iterate_succ_apply']
    rfl
  have hmul : ∀ (j : ℕ) (a : G.A n),
      PDiv.mulBy O (G.A n) j a = (toConv (AlgHom.id O (G.A n)) ^ j).ofConv a := fun j a =>
    DFunLike.congr_fun (PDiv.comp_mulBy_pts (AlgHom.id O (G.A n)) j) a
  induction k with
  | zero =>
    intro i
    have h0 : nmul c.μ 0 i = 0 := rfl
    rw [h0, map_zero, hmul]
    simp [c.aug n i]
  | succ k ih =>
    intro i
    have hu : ∀ s, constantCoeff
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s) = 0 := by
      have hc : ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul c.μ k j) = 0 := by
        intro k
        induction k with
        | zero => intro j; rfl
        | succ k ihk =>
          intro j
          rw [hsucc]
          refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_
            (c.isLaw.const j) <;>
          · rintro (l | l)
            · simpa using ihk l
            · simp
      rintro (l | l)
      · simpa using hc k l
      · simp
    let ψ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n :=
      (Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
        (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _).comp (c.ev₂ n)
    have hψ : IsEval p (fun s => c.ev n
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s)) ψ := by
      constructor
      · rintro (l | l)
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inl l), Sum.elim_inl,
            Algebra.TensorProduct.lift_tmul, map_one, mul_one, ih]
          rfl
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inr l), Sum.elim_inr,
            Algebra.TensorProduct.lift_tmul, map_one, one_mul, (c.isEval n).1 l]
          rfl
      · intro m
        obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
        refine ⟨N, fun f hf => ?_⟩
        obtain ⟨y, hy⟩ := hN f hf
        refine ⟨(Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
          (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _) y, ?_⟩
        simp only [ψ, AlgHom.comp_apply, hy, map_mul, map_pow, map_natCast]
    rw [hsucc, hT.1 _ _ ψ hu hψ (c.μ i)]
    simp only [ψ, AlgHom.comp_apply, c.comul n i]
    rw [hmul (k + 1), pow_succ, AlgHom.convMul_apply]
    have e : (toConv (AlgHom.id O (G.A n)) ^ k).ofConv =
        (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) := by
      ext a; exact (hmul k a).symm
    simp only [e]

end GlobalTheory.NMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdDivGroupChartFormsBasisAndDifferentialStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), Function.Bijective (Fintype.linearCombination O c.form) ∧ ∀ (n : ℕ) (f : MvPowerSeries (Fin d) O), constantCoeff f = 0 → PDiv.dUnit (R := O) (c.ev n f) = ∑ i, lin f i • PDiv.dUnit (R := O) (c.x n i) := by
  first | exact @GlobalTheory.chart_form_basis | exact GlobalTheory.chart_form_basis | (intros; apply GlobalTheory.chart_form_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivSubstChainRuleStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pderiv_subst_chain_rule :
    ∀ {R σ τ : Type} [CommRing R] [Fintype σ] [Fintype τ] (a : σ → MvPowerSeries τ R),
      (∀ s, constantCoeff (a s) = 0) → ∀ (f : MvPowerSeries σ R) (k : τ),
        pderiv (R := R) k (subst a f) = ∑ j, subst a (pderiv (R := R) j f) * pderiv (R := R) k (a j) := by
  exact @GlobalTheory.PSChain.pderiv_subst_chain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicDecreasingLimitExtension
section
open ReciprocityTheory.L2DbarEstimates MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff Topology

namespace GlobalTheory.HormanderLimit

theorem exists_tendstoLocallyUniformlyOn_ultrafilter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {F : ℕ → E → ℂ} (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ c ∈ U, ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ k, ∀ z ∈ ball c r, ‖F k z‖ ≤ M)
    (𝒰 : Ultrafilter ℕ) : ∃ f : E → ℂ, TendstoLocallyUniformlyOn F f (𝒰 : Filter ℕ) U := by
  have hpt : ∀ c, ∃ a : ℂ, c ∈ U → Tendsto (fun k => F k c) (𝒰 : Filter ℕ) (𝓝 a) := by
    intro c
    by_cases hc : c ∈ U
    · obtain ⟨r, hr, M, -, hM⟩ := hb c hc
      obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : ℂ) M).ultrafilter_le_nhds
        (𝒰.map fun k => F k c) (by
          rw [le_principal_iff, Ultrafilter.coe_map, mem_map]
          exact Eventually.of_forall fun k => by
            simpa using hM k c (mem_ball_self hr))
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose f hf using hpt
  refine ⟨f, Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε c hc => ?_⟩
  obtain ⟨r, hr, M, hrU, hM⟩ := hb c hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 c (mem_ball_self hr))
  set L : ℝ := (2 * M + 1) / r with hL
  have hL0 : 0 < L := by positivity
  have hlip : ∀ k, ∀ z ∈ ball c r, dist (F k z) (F k c) ≤ L * dist z c := by
    intro k z hz
    refine Complex.dist_le_div_mul_dist_of_mapsTo_ball ((hF k).mono hrU) (fun w hw => ?_) hz
    have := norm_sub_le (F k w) (F k c)
    have h2 : dist (F k w) (F k c) < 2 * M + 1 := by
      rw [dist_eq_norm]
      linarith [hM k w hw, hM k c (mem_ball_self hr)]
    first
      | exact mem_ball.2 h2
      | exact mem_closedBall.2 h2.le
  have hlipf : ∀ z ∈ ball c r, dist (f z) (f c) ≤ L * dist z c := fun z hz =>
    le_of_tendsto ((hf z (hrU hz)).dist (hf c hc)) (Eventually.of_forall fun k => hlip k z hz)
  refine ⟨ball c (min r (ε / (3 * L))), nhdsWithin_le_nhds (ball_mem_nhds c (by positivity)), ?_⟩
  filter_upwards [(Metric.tendsto_nhds.1 (hf c hc)) (ε / 3) (by positivity)] with k hk y hy
  have hy1 : y ∈ ball c r := ball_subset_ball (min_le_left _ _) hy
  have hy2 : dist y c < ε / (3 * L) := (mem_ball.1 hy).trans_le (min_le_right _ _)
  have hy3 : L * dist y c < ε / 3 := by
    rw [lt_div_iff₀ (by positivity)] at hy2
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have h1 := hlipf y hy1
  have h2 := hlip k y hy1
  have h3 := dist_triangle4 (f y) (f c) (F k c) (F k y)
  rw [dist_comm (F k y)] at h2
  rw [dist_comm] at hk
  linarith

theorem enorm_sq_le_lintegral {n : ℕ} {g : V n → ℂ} {c : V n} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) :
    ‖g c‖ₑ ^ 2 ≤ (volume (closedBall (0 : V n) r))⁻¹ * ∫⁻ z in closedBall c r, ‖g z‖ₑ ^ 2 := by
  have hd : DifferentiableOn ℂ (fun z => g (c + z)) (ball 0 r) :=
    hg.comp (by fun_prop) fun z hz => by simpa [mem_ball_iff_norm] using hz
  obtain ⟨-, h1, -⟩ := GlobalTheory.submean_sq_closedBall hr hd
  have h2 := (measurePreserving_add_left (volume : Measure (V n)) c).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft c).measurableEmbedding (fun z => ‖g z‖ₑ ^ 2) (closedBall c r)
  have h3 : (fun z => c + z) ⁻¹' closedBall c r = closedBall 0 r := by
    ext z
    simp [mem_closedBall_iff_norm]
  rw [h3] at h2
  rw [← h2]
  simpa using h1

theorem locally_bounded_of_lintegral {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {F : ℕ → V n → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ z in K, ‖F k z‖ₑ ^ 2 ≤ C) :
    ∀ c ∈ U, ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ k, ∀ z ∈ ball c r, ‖F k z‖ ≤ M := by
  intro c hc
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU c hc
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall c (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  obtain ⟨C, hC, hCk⟩ := hb _ hK (isCompact_closedBall _ _)
  set B : ℝ≥0∞ := (volume (closedBall (0 : V n) r))⁻¹ * C with hB
  have hBt : B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (measure_closedBall_pos _ _ hr0).ne') hC
  refine ⟨r, hr0, Real.sqrt B.toReal, (ball_subset_ball (by linarith)).trans hRU,
    fun k z hz => ?_⟩
  have hsub : closedBall z r ⊆ closedBall c (2 * r) :=
    closedBall_subset_closedBall' (by linarith [mem_ball.1 hz])
  have h1 := enorm_sq_le_lintegral hr0
    ((hF k).mono (ball_subset_closedBall.trans (hsub.trans hK)))
  have h2 : ‖F k z‖ₑ ^ 2 ≤ B :=
    h1.trans (by
      rw [hB]
      gcongr
      exact (lintegral_mono_set hsub).trans (hCk k))
  refine Real.le_sqrt_of_sq_le ?_
  have h3 := ENNReal.toReal_mono hBt h2
  simpa using h3

theorem exists_limit {n : ℕ} {U : Set (V n)} (hU : IsOpen U) (K : ℕ → Set (V n))
    (hKc : ∀ j, IsCompact (K j)) (hKU : ∀ j, K j ⊆ U) (hK : ∀ y ∈ U, ∀ᶠ j in atTop, y ∈ K j)
    {φ : ℕ → V n → ℝ} (hφ : ∀ k, ContinuousOn (φ k) U) (hdec : ∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y)
    {F0 : V n → ℂ} (hF0 : ContinuousOn F0 U) {A : ℝ≥0∞} (hA : A ≠ ⊤) {F : ℕ → V n → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hest : ∀ k, ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F k y‖ ^ 2 * Real.exp (-φ k y)) ≤ A) :
    ∃ f : V n → ℂ, DifferentiableOn ℂ f U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  have hanti : ∀ y ∈ U, Antitone fun k => φ k y := fun y hy =>
    antitone_nat_of_succ_le fun k => hdec k y hy
  have hloc : ∀ S ⊆ U, IsCompact S → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ z in S, ‖F k z‖ₑ ^ 2 ≤ C := by
    intro S hSU hS
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn ((hφ 0).mono hSU)
    obtain ⟨N, hN⟩ := hS.exists_bound_of_continuousOn (hF0.mono hSU)
    refine ⟨ENNReal.ofReal (2 * N ^ 2) * volume S + ENNReal.ofReal (2 * Real.exp M) * A,
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_lt_top.ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA⟩, fun k => ?_⟩
    calc ∫⁻ z in S, ‖F k z‖ₑ ^ 2
        ≤ ∫⁻ z in S, (ENNReal.ofReal (2 * N ^ 2) + ENNReal.ofReal (2 * Real.exp M) *
            ENNReal.ofReal (‖F0 z - F k z‖ ^ 2 * Real.exp (-φ k z))) := by
          refine setLIntegral_mono' hS.measurableSet fun z hz => ?_
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : φ k z ≤ M :=
            (hanti z (hSU hz) (Nat.zero_le k)).trans ((le_abs_self _).trans (hM z hz))
          have h2 : 1 ≤ Real.exp M * Real.exp (-φ k z) := by
            rw [← Real.exp_add]
            exact Real.one_le_exp (by linarith)
          have h3 : ‖F k z‖ ≤ N + ‖F0 z - F k z‖ := by
            have := norm_sub_le (F0 z) (F0 z - F k z)
            rw [sub_sub_cancel] at this
            linarith [hN z hz]
          have h4 : ‖F k z‖ ^ 2 ≤ (N + ‖F0 z - F k z‖) ^ 2 := by gcongr
          have h5 : ‖F0 z - F k z‖ ^ 2 * 1 ≤
              ‖F0 z - F k z‖ ^ 2 * (Real.exp M * Real.exp (-φ k z)) := by gcongr
          nlinarith [sq_nonneg (N - ‖F0 z - F k z‖)]
      _ ≤ _ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          exact (lintegral_mono_set hSU).trans (hest k)
  obtain ⟨f, hf⟩ := exists_tendstoLocallyUniformlyOn_ultrafilter hF
    (locally_bounded_of_lintegral hU hF hloc) (hyperfilter ℕ)
  have hfd : DifferentiableOn ℂ f U :=
    GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn hU hf (Eventually.of_forall hF)
  have hsel : ∀ j : ℕ, ∃ k, j ≤ k ∧ ∀ y ∈ K j, dist (f y) (F k y) < 1 / ((j : ℝ) + 1) := by
    intro j
    have h1 := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hf (K j) (hKU j) (hKc j))
      (1 / ((j : ℝ) + 1)) (by positivity)
    have h2 : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), j ≤ k :=
      Nat.hyperfilter_le_atTop (eventually_ge_atTop j)
    exact (h2.and h1).exists
  choose σ hσ hσK using hsel
  have hlim : ∀ y ∈ U, Tendsto (fun j => F (σ j) y) atTop (𝓝 (f y)) := by
    intro y hy
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hK y hy] with j hj
    rw [dist_comm]
    exact (hσK j y hj).le
  have hmeas : ∀ {g : V n → ℂ}, ContinuousOn g U → ∀ m, AEMeasurable
      (fun y => ENNReal.ofReal (‖F0 y - g y‖ ^ 2 * Real.exp (-φ m y))) (volume.restrict U) := by
    intro g hg m
    exact (ContinuousOn.aemeasurable ((((hF0.sub hg).norm).pow 2).mul (hφ m).neg.rexp)
      hU.measurableSet).ennreal_ofReal
  have hm : ∀ m, ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ m y)) ≤ A := by
    intro m
    calc ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ m y))
        = ∫⁻ y in U, liminf (fun j =>
            ENNReal.ofReal (‖F0 y - F (σ j) y‖ ^ 2 * Real.exp (-φ m y))) atTop := by
          refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
          refine (Tendsto.liminf_eq ?_).symm
          exact ENNReal.tendsto_ofReal
            (((tendsto_const_nhds.sub (hlim y hy)).norm.pow 2).mul_const _)
      _ ≤ liminf (fun j => ∫⁻ y in U,
            ENNReal.ofReal (‖F0 y - F (σ j) y‖ ^ 2 * Real.exp (-φ m y))) atTop :=
          lintegral_liminf_le' fun j => hmeas (hF _).continuousOn m
      _ ≤ A := by
          refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
          filter_upwards [eventually_ge_atTop m] with j hj
          refine le_trans (setLIntegral_mono' hU.measurableSet fun y hy => ?_) (hest (σ j))
          refine ENNReal.ofReal_le_ofReal ?_
          have := hanti y hy (hj.trans (hσ j))
          gcongr
  refine ⟨f, hfd, ?_⟩
  have e : ∀ y, ENNReal.ofReal (‖F0 y - f y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) =
      ⨆ k, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ k y)) := by
    intro y
    rw [ENNReal.mul_iSup]
    exact iSup_congr fun k => (ENNReal.ofReal_mul (by positivity)).symm
  simp_rw [e]
  rw [lintegral_iSup' (hmeas hfd.continuousOn)]
  · exact iSup_le hm
  · filter_upwards [ae_restrict_mem hU.measurableSet] with y hy a b hab
    refine ENNReal.ofReal_le_ofReal ?_
    have := hanti y hy hab
    gcongr

theorem hormander_limit : ∀ {n : ℕ} {U : Set (V n)}, IsOpen U → ∀ (e : V n → ℝ), ContDiffOn ℝ ∞ e U → (∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re) → (∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a}) → ∀ (φ : ℕ → V n → ℝ), (∀ k, ContDiffOn ℝ ∞ (φ k) U) → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → (∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y) → ∀ (F0 : V n → ℂ), ContDiffOn ℝ ∞ F0 U → ∀ (h : V n → ℝ≥0∞), Measurable h → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h y * ENNReal.ofReal (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → ∀ A : ℝ≥0∞, (∀ k, ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ k y)) ≤ A) → ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧ ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  intro n U hU e he hel hec φ hφ hφl hdec F0 hF0 h hh hb A hA
  by_cases hAt : A = ⊤
  · exact ⟨0, differentiableOn_const 0, hAt ▸ le_top⟩
  choose F hF hest using fun k => ReciprocityTheory.ChartRestriction.G.AR.Up.HE.hormander_open hU e he hel hec (φ k)
    (hφ k) (hφl k) F0 hF0 h hh (hb k)
  refine exists_limit hU (fun j => {y | y ∈ U ∧ e y ≤ (j : ℝ)}) (fun j => hec j)
    (fun j y hy => hy.1) (fun y hy => ?_) (fun k => (hφ k).continuousOn) hdec hF0.continuousOn hAt
    hF fun k => (hest k).trans (hA k)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (e y)] with j hj
  exact ⟨hy, hj⟩

end GlobalTheory.HormanderLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpacesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveBundleFormula_of_discrete_spaces : ∀ (q : ℕ) [NeZero q] (N : ℕ), (∀ (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V) → ∀ {E : Spc} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V := by
  first | (exact @GlobalTheory.PBFg.pbf_of_disc) | (exact GlobalTheory.PBFg.pbf_of_disc) | (intros; apply GlobalTheory.PBFg.pbf_of_disc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
    {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G)
    (ψ : P →* Kˣ) :
    LinearMap.range (S.lvlOp r P ψ (idemOf X)).mulVecLin =
      LinearMap.range (S.lvlPr r P ψ * S.V0E r X P ψ).mulVecLin := by
  have hE : LinearMap.range (S.lvlE r P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (lvlIdem P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hV : LinearMap.range (S.V0E r X P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (goodAt X P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hm : S.gaMat r (goodAt X P ψ) = S.gaMat r (idemOf X) * S.gaMat r (lvlIdem P ψ) :=
    (group_action_matrix_hom K S G r).2 _ _
  unfold CSD.lvlOp
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_comp,
    hE, hV, hm, Matrix.mulVecLin_mul, LinearMap.range_comp, Submodule.map_comp]

theorem range_goodProjector_eq_range_goodCoordinates : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    (A : FamIn D.what₂.LL G Pl0 T m) (s : ℕ), A.fam.Ok s → ∀ (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T),
    LinearMap.range (rE D A P ψ t).mulVecLin = LinearMap.range (rV0 D A P ψ t).mulVecLin := by
  intro D G _ _ Pl0 T m A s _ P ψ t
  exact range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E (A.fam.R t).S (A.fam.R t).r A.X P ψ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeOpEqSpanOfFormsTie
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_op_eq_span_of_formsTie :
    ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n k : ℕ} (σ : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W) (V : Matrix (Fin n) (Fin k) K), FormsTie σ j H E op → LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin → LinearMap.range op = Submodule.span ℂ (Set.range fun x => j (V.mulVec x)) := by
  intro K _ _ _ n k σ W _ _ j H E op V h hr
  apply le_antisymm
  · rw [← Submodule.map_top, ← h.span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hm : E.mulVec (Pi.single i 1) ∈ LinearMap.range V.mulVecLin := by
      rw [← hr]
      exact ⟨Pi.single i 1, rfl⟩
    obtain ⟨y, hy⟩ := hm
    refine Submodule.subset_span ⟨y, ?_⟩
    have hy' : V.mulVec y = E.mulVec (Pi.single i 1) := hy
    show j (V.mulVec y) = op (j (Pi.single i 1))
    rw [h.op_eq, hy']
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hm : V.mulVec y ∈ LinearMap.range E.mulVecLin := by
      rw [hr]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hm
    have hx' : E.mulVec x = V.mulVec y := hx
    refine ⟨j x, ?_⟩
    show op (j x) = j (V.mulVec y)
    rw [h.op_eq, hx']

end GlobalTheory
end

