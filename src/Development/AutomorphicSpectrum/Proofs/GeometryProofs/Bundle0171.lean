module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminant
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0004
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SabModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isPrincipal_dim {K : Type} [Field K] {t : SAB H (Sp K)} (_h : IsPrincipal t) :
    ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  letI := t.grp
  haveI hs : IsSemiAbelian t.G := t.semi
  haveI : Smooth t.G.hom := hs.smooth
  haveI : GeometricallyConnected t.G.hom := hs.geomConnected
  have hc := t.G.hom.isConnected_preimage_singleton (IsLocalRing.closedPoint K)
  have hu : t.G.hom ⁻¹' {IsLocalRing.closedPoint K} = Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  haveI : PreconnectedSpace t.G.left := ⟨by rw [← hu]; exact hc.isPreconnected⟩
  exact exists_dim_of_preconnected t.G.hom hc.nonempty.some

def pol {K : Type} [Field K] (t : SAB H (Sp K)) (h : IsPrincipal t) : Out.PolAV (Sp K) where
  A := t.G
  isAb := ⟨inferInstance, t.semi.smooth, h.1, t.semi.geomConnected⟩
  g := (isPrincipal_dim h).choose
  smoothDim := (isPrincipal_dim h).choose_spec
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := h.2.1
  ktriv := h.2.2

end GlobalTheory.CompanionTheory.Ar.SabModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.TopLL

theorem shift {k : Type} [Field k] [NumberField k] (N N' : LogNorms k) (C : ∀ p : Nat.Primes, (k →+* ℂ_[p]) → ℝ)
    (hinf : N.inf = N'.inf) (hfin : ∀ p κ, N.fin p κ = N'.fin p κ + C p κ)
    (hC : {p : Nat.Primes | ∃ κ, C p κ ≠ 0}.Finite) (h : N'.IsAdelic) :
    N.IsAdelic ∧ N.deg = N'.deg - (∑ᶠ p, ∑ κ, C p κ) / Module.finrank ℚ k := by
  constructor
  · refine (h.union hC).subset ?_
    rintro p ⟨κ, hκ⟩
    by_cases hc : C p κ = 0
    · left
      exact ⟨κ, by rw [hfin, hc, add_zero] at hκ; exact hκ⟩
    · right
      exact ⟨κ, hc⟩
  · have h1 : Function.HasFiniteSupport (fun p => N'.finSum p) := by
      refine h.subset ?_
      intro p hp
      obtain ⟨κ, _, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
      exact ⟨κ, hκ⟩
    have h2 : Function.HasFiniteSupport (fun p => ∑ κ, C p κ) := by
      refine hC.subset ?_
      intro p hp
      obtain ⟨κ, _, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
      exact ⟨κ, hκ⟩
    have hs : ∑ᶠ p, N.finSum p = ∑ᶠ p, N'.finSum p + ∑ᶠ p, ∑ κ, C p κ := by
      rw [← finsum_add_distrib h1 h2]
      refine finsum_congr fun p => ?_
      simp only [LogNorms.finSum, hfin, Finset.sum_add_distrib]
    have hk : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
    simp only [LogNorms.deg, hs, hinf]
    field_simp
    ring

theorem corr {E k : Type} [Field E] [NumberField E] [Field k] [NumberField k] (f : E →+* k) (d : ℕ) (hd : d ≠ 0) :
    {p : Nat.Primes | ∃ κ : k →+* ℂ_[p], logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) -
      Real.log ‖((d : ℕ) : ℂ_[p])‖ ≠ 0}.Finite ∧
    ∑ᶠ p : Nat.Primes, ∑ κ : k →+* ℂ_[p], (logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) -
      Real.log ‖((d : ℕ) : ℂ_[p])‖) = Module.finrank ℚ k * (Real.log d - Real.log (rootDiscr E)) := by
  have hdk : (d : k) ≠ 0 := by exact_mod_cast hd
  have hI := _root_.GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
  have hX := GlobalTheory.T.log_norms_of_nonzero_adelic k (d : k) hdk
  have hP := GlobalTheory.T.product_formula_log_norms k (d : k) hdk
  have hD := _root_.GlobalTheory.CompanionTheory.Ar.Fl.different_sum_eq_neg_finrank_mul_log_rootDiscr E
  have hcast : ∀ (p : Nat.Primes) (κ : k →+* ℂ_[p]), κ (d : k) = ((d : ℕ) : ℂ_[p]) := fun _ κ => map_natCast κ d
  constructor
  · refine (hI.union hX).subset ?_
    rintro p ⟨κ, hκ⟩
    by_cases h0 : logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) = 0
    · right
      refine ⟨κ, ?_⟩
      simp only [LogNorms.ofElt, hcast]
      intro h
      exact hκ (by rw [h0, h, sub_zero])
    · left
      exact ⟨_, h0⟩
  · set A : Nat.Primes → ℝ := fun p => ∑ κ : k →+* ℂ_[p],
      logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) with hAdef
    set B : Nat.Primes → ℝ := fun p => (LogNorms.ofElt (d : k)).finSum p with hBdef
    have hAB : ∀ p : Nat.Primes, ∑ κ : k →+* ℂ_[p], (logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E))
        (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[p])‖) = A p - B p := by
      intro p
      simp only [hAdef, hBdef, LogNorms.finSum, LogNorms.ofElt, hcast, Finset.sum_sub_distrib]
    have hA : Function.HasFiniteSupport A := by
      refine hI.subset ?_
      intro p hp
      obtain ⟨κ, _, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
      exact ⟨_, hκ⟩
    have hB : Function.HasFiniteSupport B := hP.1
    have hF : ∀ p : Nat.Primes, (Module.finrank ℚ E : ℝ) * A p = (Module.finrank ℚ k : ℝ) *
        ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := fun p =>
      _root_.GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq E k ℂ_[p] f (fun j => logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
    have hsA : ∑ᶠ p, A p = -(Module.finrank ℚ k : ℝ) * Real.log (rootDiscr E) := by
      have h1 : (Module.finrank ℚ E : ℝ) * ∑ᶠ p, A p =
          (Module.finrank ℚ k : ℝ) * (-(Module.finrank ℚ E : ℝ) * Real.log (rootDiscr E)) := by
        rw [mul_finsum, finsum_congr hF, ← mul_finsum, hD.2]
      apply mul_left_cancel₀ hE
      rw [h1]
      ring
    have hsB : ∑ᶠ p, B p = -(Module.finrank ℚ k : ℝ) * Real.log d := by
      have h2 := hP.2
      have h3 : ∑ s : k →+* ℂ, Real.log ‖s (d : k)‖ = (Module.finrank ℚ k : ℝ) * Real.log d := by
        simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, Embeddings.card,
          nsmul_eq_mul]
      rw [h3] at h2
      simp only [hBdef]
      linarith
    rw [finsum_congr hAB, finsum_sub_distrib hA hB, hsA, hsB]
    ring

theorem degree_frames : FlatDegree → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ))
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (U : Set (Xo.XF c)) (τ : E →+* ℂ)
    (φ : FrameFn Xo c) [NumberField c.F] (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d),
    GlobalTheory.IsKroneckerChar χ → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → IsFlatGen U τ φ FU i →
    (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) →
    N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hFD E _ _ _ H D l Xo c g ty FU i U τ φ _ N _ χ hχ hty hrt hflat hinf hfin
  let f : E →+* c.F := (τ.codRestrict c.F.toSubfield (c.conj τ) :)
  have hf : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), κ.comp (tauIn c τ) = (κ.comp f).comp (algebraMap (𝓞 E) E) :=
    fun _ _ => rfl
  let C : ∀ p : Nat.Primes, (c.F →+* ℂ_[p]) → ℝ := fun p κ => (D.q : ℝ) *
    (logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)
  let N' : LogNorms c.F := ⟨N.inf, fun p κ => N.fin p κ - C p κ⟩
  have hN' : HasNorms U τ φ N' := by
    refine ⟨hinf, fun p κ => ?_⟩
    have e : N'.fin p κ + D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) -
        Real.log ‖((H.d : ℕ) : ℂ_[p])‖) = N.fin p κ := by
      rw [hf]
      simp only [N', C]
      ring
    rw [e]
    exact hfin p κ
  obtain ⟨hA', hdeg'⟩ := hFD E H D l Xo c g ty FU i U τ φ N' χ hχ hty hrt hflat hN'
  have hd : H.d ≠ 0 := NeZero.ne _
  obtain ⟨hc1, hc2⟩ := corr f H.d hd
  have hCfin : {p : Nat.Primes | ∃ κ, C p κ ≠ 0}.Finite := by
    refine hc1.subset ?_
    rintro p ⟨κ, hκ⟩
    exact ⟨κ, right_ne_zero_of_mul hκ⟩
  obtain ⟨hA, hdeg⟩ := shift N N' C rfl (fun p κ => by simp [N']) hCfin hA'
  refine ⟨hA, ?_⟩
  have hsum : ∑ᶠ p, ∑ κ, C p κ = (D.q : ℝ) * (Module.finrank ℚ c.F * (Real.log H.d - Real.log (rootDiscr E))) := by
    rw [← hc2, mul_finsum]
    refine finsum_congr fun p => ?_
    simp only [C, Finset.mul_sum]
  have hF : (Module.finrank ℚ c.F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hsq : 2 * Real.log (Real.sqrt H.d) = Real.log H.d := by
    rw [Real.log_sqrt (Nat.cast_nonneg _)]
    ring
  rw [hdeg, hdeg', hsum, hsq]
  field_simp
  ring

end GlobalTheory.CompanionTheory.Ar.Fl.TopLL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsModuleStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction

open GroundTheory.Heights₂.Heights.Regular

theorem exists_eventually_int_eq_zero {X V J : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fintype J] (v : X → J → V) (x₀ : X)
    (hv : ∀ i, ContinuousAt (fun x => v x i) x₀)
    (hind : ∀ r : J → ℝ, ∑ i, r i • v x₀ i = 0 → r = 0) :
    ∃ ε > (0 : ℝ), ∀ᶠ x in 𝓝 x₀, ∀ m : J → ℤ, ‖∑ i, (m i : ℝ) • v x i‖ < ε → m = 0 := by
  classical
  let T : (J → ℝ) →ₗ[ℝ] V := ∑ i, (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).smulRight (v x₀ i)
  have hT : ∀ r, T r = ∑ i, r i • v x₀ i := fun r => by simp [T, LinearMap.sum_apply]
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro r hr
    exact hind r (by rw [← hT]; exact hr)
  obtain ⟨K, hK0, hK⟩ := T.exists_antilipschitzWith hker
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hb : ∀ r, ‖r‖ ≤ K * ‖T r‖ := fun r => by
    simpa [dist_zero_right] using hK.le_mul_dist r 0
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card J + 1 := ⟨_, rfl⟩
  have hN : 0 < N := by rw [hNdef]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (2 * K * N) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ i, ‖v x i - v x₀ i‖ < δ := by
    refine eventually_all.2 fun i => ?_
    have := (Metric.tendsto_nhds.1 (hv i).tendsto) δ hδ
    simpa [dist_eq_norm] using this
  filter_upwards [hev] with x hx m hm
  obtain ⟨r, hr⟩ : ∃ r : J → ℝ, r = fun i => (m i : ℝ) := ⟨_, rfl⟩
  have hm' : ‖∑ i, r i • v x i‖ < 1 / (2 * K) := by rw [hr]; exact hm
  have hsplit : T r = ∑ i, r i • v x i - ∑ i, r i • (v x i - v x₀ i) := by
    rw [hT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sub]; abel
  have herr : ‖∑ i, r i • (v x i - v x₀ i)‖ ≤ N * (‖r‖ * δ) := by
    calc ‖∑ i, r i • (v x i - v x₀ i)‖ ≤ ∑ i, ‖r i • (v x i - v x₀ i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : J, ‖r‖ * δ := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm r i) (hx i).le (norm_nonneg _) (norm_nonneg _)
      _ = (Fintype.card J : ℝ) * (‖r‖ * δ) := by simp
      _ ≤ N * (‖r‖ * δ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hNdef]; linarith
  have h1 : ‖r‖ ≤ K * (‖∑ i, r i • v x i‖ + N * (‖r‖ * δ)) := by
    refine (hb r).trans (mul_le_mul_of_nonneg_left ?_ hKpos.le)
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by linarith)
  have h2 : K * (N * (‖r‖ * δ)) = ‖r‖ / 2 := by
    rw [hδdef]; field_simp
  have h3 : K * ‖∑ i, r i • v x i‖ < 1 / 2 := by
    have := mul_lt_mul_of_pos_left hm' hKpos
    have h4 : K * (1 / (2 * K)) = 1 / 2 := by field_simp
    linarith
  have h5 : ‖r‖ < 1 := by
    rw [mul_add, h2] at h1
    linarith
  funext i
  have h6 : |(m i : ℝ)| < 1 := by
    have := (norm_le_pi_norm r i).trans_lt h5
    rw [hr] at this
    simpa [Real.norm_eq_abs] using this
  have h7 : |m i| < 1 := by exact_mod_cast h6
  simpa using Int.abs_lt_one_iff.1 h7

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)

theorem P_injective {w : Fin n → ℂ} (hw : w ∈ logCover L.a_le) : Function.Injective (L.P w) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  apply L.unimod.1
  rw [map_zero]
  refine LinearMap.ext fun y => ?_
  have h := L.im w hw x y
  rw [hx] at h
  simp at h
  exact_mod_cast h.symm

theorem real_indep {J : Type*} [Fintype J] (b : Module.Basis J ℤ Λ) {w : Fin n → ℂ}
    (hw : w ∈ logCover L.a_le) (r : J → ℝ) (h : ∑ i, r i • L.P w (b i) = 0) : r = 0 := by
  classical
  funext j
  obtain ⟨u, hu⟩ := L.unimod.2 (b.coord j)
  let ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => (L.P w u ⬝ᵥ L.H (expCover a w) *ᵥ star v).im
      map_add' := fun v v' => by simp [star_add, mulVec_add, dotProduct_add]
      map_smul' := fun t v => by simp [star_smul, mulVec_smul, dotProduct_smul] }
  have h1 : ∀ i, ψ (L.P w (b i)) = if i = j then 1 else 0 := fun i => by
    have h2 := L.im w hw u (b i)
    change (L.P w u ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w (b i))).im = _
    rw [h2, hu]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have h2 := congrArg ψ h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, h1, map_zero, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  simpa using h2

theorem continuousAt_P (x : Λ) {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le) :
    ContinuousAt (fun w => L.P w x) w₀ :=
  (L.hol x).continuousOn.continuousAt ((isOpen_logCover L.a_le).mem_nhds hw)

theorem continuousAt_apply (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1)) (x : Λ)
    {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le) :
    ContinuousAt (fun w => A (expCover a w) (L.P w x)) w₀ := by
  classical
  have hP := continuousAt_P L x hw
  have hexp : ContinuousAt (expCover (n := n) a) w₀ := (continuous_expCover a).continuousAt
  have hAe : ∀ v, ContinuousAt (fun w => A (expCover a w) v) w₀ := fun v =>
    ContinuousAt.comp (f := expCover a) (g := fun z => A z v)
      ((hA v).continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (expCover_mem_ball L.a_le hw))) hexp
  have h1 : (fun w => A (expCover a w) (L.P w x)) = fun w =>
      ∑ i, (L.P w x i) • A (expCover a w) (fun j => if i = j then 1 else 0) := by
    funext w
    exact LinearMap.pi_apply_eq_sum_univ _ _
  rw [h1]
  exact tendsto_finsetSum _ fun i _ =>
    (((continuous_apply i).continuousAt.comp hP).smul (hAe _))

theorem eventually_eq (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1))
    (hex : ∀ w ∈ logCover L.a_le, ∀ x, ∃ y, L.P w y = A (expCover a w) (L.P w x))
    (x y : Λ) {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le)
    (h : L.P w₀ y = A (expCover a w₀) (L.P w₀ x)) :
    ∀ᶠ w in 𝓝 w₀, L.P w y = A (expCover a w) (L.P w x) := by
  haveI := L.free
  haveI := L.fin
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℤ Λ) :=
    ⟨Module.Free.chooseBasis ℤ Λ⟩
  obtain ⟨ε, hε, hev⟩ := exists_eventually_int_eq_zero (fun w i => L.P w (b i)) w₀
    (fun i => continuousAt_P L (b i) hw) (real_indep L b hw)
  have hD : ContinuousAt (fun w => A (expCover a w) (L.P w x) - L.P w y) w₀ :=
    (continuousAt_apply L A hA x hw).sub (continuousAt_P L y hw)
  have hsmall : ∀ᶠ w in 𝓝 w₀, ‖A (expCover a w) (L.P w x) - L.P w y‖ < ε := by
    have h0 := (Metric.tendsto_nhds.1 hD.tendsto) ε hε
    simpa [h, dist_eq_norm] using h0
  filter_upwards [hev, hsmall, (isOpen_logCover L.a_le).mem_nhds hw] with w h1 h2 hwC
  obtain ⟨y', hy'⟩ := hex w hwC x
  have hk : L.P w (y' - y) = ∑ i, ((b.repr (y' - y) i : ℤ) : ℝ) • L.P w (b i) := by
    conv_lhs => rw [← b.sum_repr (y' - y)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
  have hm := h1 (fun i => b.repr (y' - y) i) (by rw [← hk, map_sub, hy']; exact h2)
  have h0 : y' - y = 0 := b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun hm i)
  rw [← sub_eq_zero.1 h0, hy']

theorem eq_of_mem (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1))
    (hex : ∀ w ∈ logCover L.a_le, ∀ x, ∃ y, L.P w y = A (expCover a w) (L.P w x))
    (x y : Λ) {w₀ w₁ : Fin n → ℂ} (h0 : w₀ ∈ logCover L.a_le) (h1 : w₁ ∈ logCover L.a_le)
    (h : L.P w₀ y = A (expCover a w₀) (L.P w₀ x)) :
    L.P w₁ y = A (expCover a w₁) (L.P w₁ x) := by
  classical
  choose φ hφ using fun w : logCover L.a_le => hex w.1 w.2 x
  have hlc : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    have h2 := (continuous_subtype_val.continuousAt (x := w)).eventually
      (eventually_eq L A hA hex x (φ w) w.2 (hφ w))
    filter_upwards [h2] with w' hw'
    exact P_injective L w'.2 ((hφ w').trans hw'.symm)
  haveI : PreconnectedSpace (logCover L.a_le) :=
    Subtype.preconnectedSpace (convex_logCover L.a_le).isPreconnected
  have h2 := hlc.apply_eq_of_preconnectedSpace ⟨w₀, h0⟩ ⟨w₁, h1⟩
  have hy : φ ⟨w₀, h0⟩ = y := P_injective L h0 ((hφ ⟨w₀, h0⟩).trans h.symm)
  rw [← hy, h2]
  exact hφ ⟨w₁, h1⟩

theorem exists_module_of_period_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ))), (∀ c x, DifferentiableOn ℂ (fun z => B z c x) (Metric.ball 0 1)) → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ c x, ∃ y, L.P w y = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x)) → ∃ _ : Module (𝓞 E) Λ, ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ (c : 𝓞 E) x, L.P w (c • x) = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x) := by
  intro E _ _ _ n a g Λ _ L B hB hex
  obtain ⟨w₀, hw₀⟩ := logCover_nonempty L.a_le
  choose f hf using fun c x => hex w₀ hw₀ c x
  have key : ∀ w ∈ logCover L.a_le, ∀ c x, L.P w (f c x) = B (expCover a w) c (L.P w x) :=
    fun w hw c x => eq_of_mem L (fun z => B z c) (fun x => hB c x)
      (fun w hw x => hex w hw c x) x (f c x) hw₀ hw (hf c x)
  have inj := P_injective L hw₀
  have e1 : ∀ x, f 1 x = x := fun x => inj (by rw [hf]; simp)
  have e2 : ∀ c d x, f (c * d) x = f c (f d x) := fun c d x => inj (by
    rw [hf, hf, hf, map_mul, Module.End.mul_apply])
  have e3 : ∀ c, f c 0 = 0 := fun c => inj (by rw [hf]; simp)
  have e4 : ∀ c x y, f c (x + y) = f c x + f c y := fun c x y => inj (by
    rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)])
  have e5 : ∀ c d x, f (c + d) x = f c x + f d x := fun c d x => inj (by
    rw [map_add (f := _), hf, hf, hf, map_add (f := _), LinearMap.add_apply])
  have e6 : ∀ x, f 0 x = 0 := fun x => inj (by rw [hf]; simp)
  exact ⟨{ smul := f, one_smul := e1, mul_smul := e2, smul_zero := e3, smul_add := e4,
           add_smul := e5, zero_smul := e6 }, key⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NoetherianIntegralClosedCover
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx


open TopologicalSpace in
theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{0}} (Z : Closeds X)
    (h : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have hr : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  haveI : IrreducibleSpace (Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    Subtype.irreducibleSpace (by rw [hr]; exact h)
  let f := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Function.Surjective.irreducibleSpace f.symm.continuous f.symm.surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced _


open TopologicalSpace in
theorem exists_integral_closed_cover :
    ∀ (X : Scheme.{0}) [IsNoetherian X], ∃ (n : ℕ) (Z : Fin n → Scheme.{0}) (j : ∀ i, Z i ⟶ X),
      (∀ i, IsIntegral (Z i) ∧ IsClosedImmersion (j i)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (j i) := by
  intro X _
  haveI : Finite (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents X)
  let C : Fin n → Closeds X := fun i =>
    ⟨(e.symm i).1, isClosed_of_mem_irreducibleComponents _ (e.symm i).2⟩
  refine ⟨n, fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subscheme,
    fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subschemeι,
    fun i => ⟨GlobalTheory.CompanionTheory.Ar.Approx.isIntegral_subscheme_vanishingIdeal (C i) (e.symm i).2.1, inferInstance⟩,
    fun x => ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  show x ∈ (e.symm (e _)).1
  rw [Equiv.symm_apply_apply]
  exact mem_irreducibleComponent

end GlobalTheory.CompanionTheory.Ar.Approx
end

