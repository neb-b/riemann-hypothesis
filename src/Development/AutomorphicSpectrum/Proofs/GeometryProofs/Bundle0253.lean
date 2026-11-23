module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPhiNormSq
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionPositive
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0250
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormLowerBoundNearCusp
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PshLogGrowthBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SplitMultiplicativeHopfOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0239
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TeichmullerTestFunction
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemFirstLatticeIff
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValMulLeOfCyclicKer
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0016

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionLimit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.CorrBdd

open ReciprocityTheory.AnForm.A (IsPsh)
open _root_.Metric GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence GlobalTheory.CompanionTheory.Ar.Cusp.CorrPsh
open LevelTowerAlt (lower_centre)
open GroundTheory.Heights₂.Heights.Regular (logCover expCover)

theorem exists_lift {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ} (hz : z ∈ Flat.punct n a 1) :
    ∃ w ∈ logCover h, expCover a w = z := by
  have h1 : ∀ k, ‖z k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hz.1)
  refine ⟨fun k => if k.val < a then Complex.log (z k) else z k, ⟨fun i => ?_, fun k hk => ?_⟩, ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.isLt
    simp only [if_pos hi, Complex.log_re]
    exact Real.log_neg (norm_pos_iff.mpr (hz.2 _ hi)) (h1 _)
  · simp only [if_neg (not_lt.mpr hk)]
    exact h1 k
  · funext k
    by_cases hk : k.val < a
    · simp only [expCover, if_pos hk, Complex.exp_log (hz.2 k hk)]
    · simp only [expCover, if_neg hk]

theorem isPsh_comp_aff {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) {U V : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → ℝ} (h : IsPsh V f) (hUV : ∀ u ∈ U, aff t₀ ρ π u ∈ V) :
    IsPsh U fun u => f (aff t₀ ρ π u) := by
  have hc : Continuous (aff t₀ ρ π) := by
    unfold aff
    fun_prop
  have ha : ∀ (z w : Fin n → ℂ) (ζ : ℂ), aff t₀ ρ π (z + ζ • w) = aff t₀ ρ π z + ζ • ((ρ : ℂ) • (w ∘ π)) := by
    intro z w ζ
    funext i
    simp [aff]
    ring
  refine ⟨h.1.comp (g := aff t₀ ρ π) hc.continuousOn hUV, fun z w hd => ?_⟩
  simp only [ha]
  exact h.2 _ _ fun ζ hζ => by rw [← ha]; exact hUV _ (hd ζ hζ)

theorem one_le_logSize {n : ℕ} (a : ℕ) (u : Fin n → ℂ) : 1 ≤ Flat.logSize a u :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem logSize_le {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {n a₀ : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (π : Equiv.Perm (Fin n))
    (hu : ∀ u ∈ ball (0 : Fin n → ℂ) 1, aff t₀ ρ π u ∈ ball (0 : Fin n → ℂ) 1 ∧
      (χ.γ (aff t₀ ρ π u) ∉ Bd → u ∈ Flat.punct n a₀ 1)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u ∈ Flat.punct n a₀ 1, 1 ≤ Real.log (χ.logR (aff t₀ ρ π u)) ∧
      1 + Real.log (Flat.logSize a₀ u) ≤ A * Real.log (χ.logR (aff t₀ ρ π u)) := by
  classical
  have hρ' : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hbr : ∀ i : Fin n, i.val < a₀ → (π.symm i).val < χ.a ∧ t₀ (π.symm i) = 0 := by
    intro i hi
    let u : Fin n → ℂ := fun k => if k = i then 0 else if t₀ (π.symm k) = 0 then 1 / 2 else 0
    have hu1 : u ∈ ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
      intro k
      simp only [u]
      split_ifs <;> norm_num
    have hb : χ.γ (aff t₀ ρ π u) ∈ Bd := by
      by_contra hn
      exact ((hu u hu1).2 hn).2 i hi (by simp [u])
    obtain ⟨j, hj, h0⟩ := (χ.boundary _ (hu u hu1).1).1 hb
    by_cases hji : π j = i
    · subst hji
      simp only [Equiv.symm_apply_apply]
      exact ⟨hj, by simpa [aff, u] using h0⟩
    · exfalso
      by_cases ht : t₀ j = 0 <;> simp [aff, u, hji, ht, hρ'] at h0
  set A₀ : ℝ := 1 + n * (1 + |Real.log ρ|) with hA₀
  have hA1 : 1 ≤ A₀ := le_add_of_nonneg_right (by positivity)
  refine ⟨2 + Real.log A₀, by linarith [Real.log_nonneg hA1], fun u hu' => ?_⟩
  set t := aff t₀ ρ π u with ht
  have ht1 : ∀ k, ‖t k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 (hu u hu'.1).1)
  have hu1 : ∀ k, ‖u k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hu'.1)
  have hterm : ∀ i : Fin n, 0 ≤ if (i : ℕ) < χ.a then Real.log (1 / ‖t i‖ ^ 2) else 0 := by
    intro i
    split_ifs
    · rw [one_div, Real.log_inv, neg_nonneg]
      exact Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg _) (ht1 i).le)
    · exact le_rfl
  have he : Real.exp 1 ≤ χ.logR t := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hterm i)
  have he1 : 1 ≤ χ.logR t := (Real.one_le_exp zero_le_one).trans he
  have hl1 : 1 ≤ Real.log (χ.logR t) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact he
  have hone : ∀ i : Fin n, i.val < a₀ → |Real.log ‖u i‖| ≤ (1 + |Real.log ρ|) * χ.logR t := by
    intro i hi
    obtain ⟨h1, h2⟩ := hbr i hi
    have h3 : t (π.symm i) = ρ * u i := by simp [ht, aff, h2]
    have h4 : Real.log (1 / ‖t (π.symm i)‖ ^ 2) ≤ χ.logR t := by
      have := Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ (π.symm i))
      rw [if_pos h1] at this
      exact this.trans (le_add_of_nonneg_left (Real.exp_pos 1).le)
    have h5 : 0 < ‖u i‖ := norm_pos_iff.2 (hu'.2 i hi)
    rw [h3, one_div, Real.log_inv, Real.log_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le,
      Real.log_mul hρ.ne' h5.ne'] at h4
    rw [abs_of_neg (Real.log_neg h5 (hu1 i))]
    push_cast at h4
    nlinarith [le_abs_self (Real.log ρ), abs_nonneg (Real.log ρ)]
  have hsz : Flat.logSize a₀ u ≤ A₀ * χ.logR t := by
    have h1 := Finset.sum_le_card_nsmul (Finset.univ.filter fun i : Fin n => i.val < a₀)
      (fun i => |Real.log ‖u i‖|) _ fun i hi => hone i (Finset.mem_filter.1 hi).2
    have h2 : ((Finset.univ.filter fun i : Fin n => i.val < a₀).card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_le_univ _).trans (Fintype.card_fin n).le
    have h3 : 0 ≤ (1 + |Real.log ρ|) * χ.logR t := by positivity
    rw [nsmul_eq_mul] at h1
    unfold Flat.logSize
    nlinarith [mul_le_mul_of_nonneg_right h2 h3]
  have h6 := Real.log_le_log (by linarith [one_le_logSize a₀ u]) hsz
  rw [Real.log_mul (by linarith) (by linarith)] at h6
  exact ⟨hl1, by nlinarith [Real.log_nonneg hA1]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l}
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem near_bdd (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) {U : ((Σ k, J k) → ℂ) → ℝ}
    (hU : Or.𝔐.IsCuspWeight Or.sm U) (hP : ChartPsh Dc (corrW Hd U)) (a : Fin Dc.nCharts)
    (t₀ : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) (ht₀ : t₀ ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) :
    ∃ ε > (0 : ℝ), ∃ C : ℝ, ∀ t ∈ offBd Dc a, ‖t - t₀‖ < ε → |corrW Hd U ((Dc.chart a).γ t)| ≤ C ∧
      U ((Dc.chart a).γ t) ≤ C * Real.log ((Dc.chart a).logR t) ∧
      |phMu Hd ((Dc.chart a).γ t)| ≤ C * Real.log ((Dc.chart a).logR t) := by
  classical
  obtain ⟨a₀, g, Λ, i₁, i₂, L, π, ρ, r, σ, b, G, hρ, hr, hr1, hσ, hb, hGd, hu, hw⟩ :=
    chart_formula hG Or hU a t₀ ht₀
  have hm : 1 ≤ Dc.N - Dc.j := by
    have := Dc.j_le
    have := Dc.two_le_N
    omega
  obtain ⟨ρ₁, C₁, hρ₁, hul⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.uLogBound E _ a₀ g Λ (CMType H) L σ _ b hσ hm hb
  obtain ⟨δ₂, hδ₂, C₂, hlow⟩ := lower_centre L σ b hσ hm hb
  have hGc : ContinuousAt (fun u => |(G u).re|) 0 :=
    (Complex.continuous_re.continuousAt.comp (hGd.continuousOn.continuousAt (ball_mem_nhds _ hr))).abs
  obtain ⟨δ₃, hδ₃, hGb⟩ := Metric.eventually_nhds_iff_ball.1
    (hGc.eventually (gt_mem_nhds (lt_add_one |(G 0).re|)))
  set B := |(G 0).re| + 1 with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨A, hA, hsz⟩ := logSize_le (a₀ := a₀) (Dc.chart a) t₀ hρ π fun u hu' =>
    ⟨(hu u hu').1, fun h => (hu u hu').2.1 ⟨(hu u hu').1, h⟩⟩
  obtain ⟨δ, hδ, d1, d2, d3, d4⟩ : ∃ δ > (0 : ℝ), δ ≤ r ∧ δ ≤ ρ₁ ∧ δ ≤ δ₂ ∧ δ ≤ δ₃ :=
    ⟨min (min r ρ₁) (min δ₂ δ₃), lt_min (lt_min hr hρ₁) (lt_min hδ₂ hδ₃),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hsub : ∀ u ∈ Flat.punct (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ δ, u ∈ Flat.punct (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ 1 :=
    fun u h => ⟨ball_subset_ball (d1.trans hr1) h.1, h.2⟩
  have key : ∀ u ∈ Flat.punct (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ δ, ∃ ld cw gr ℓ : ℝ, ℓ = 1 + Real.log (Flat.logSize a₀ u) ∧ 1 ≤ ℓ ∧
      phMu Hd ((Dc.chart a).γ (aff t₀ ρ π u)) = gr + ld / 2 ∧ U ((Dc.chart a).γ (aff t₀ ρ π u)) = cw ∧
      cw ≤ |C₁| * ℓ ∧ |ld| ≤ |C₁| * ℓ ∧ -C₂ ≤ ld + cw ∧ |gr| ≤ B := by
    intro u hu'
    obtain ⟨w, hlw, rfl⟩ := exists_lift L.a_le (hsub u hu')
    have hn := mem_ball_zero_iff.1 hu'.1
    obtain ⟨e1, e2⟩ := hw w hlw (ball_subset_ball d1 hu'.1) (hsub _ hu')
    obtain ⟨-, b1, b2⟩ := hul w hlw (hn.trans_le d2)
    have hl : 1 ≤ 1 + Real.log (Flat.logSize a₀ (expCover a₀ w)) :=
      le_add_of_nonneg_right (Real.log_nonneg (one_le_logSize _ _))
    have hm' := mul_le_mul_of_nonneg_right (le_abs_self C₁) (zero_le_one.trans hl)
    exact ⟨_, _, _, _, rfl, hl, e1, e2, b1.trans hm', b2.trans hm', hlow w hlw (hn.trans_le d3),
      (hGb _ (ball_subset_ball d4 hu'.1)).le⟩
  have hps : IsPsh (Flat.punct (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ δ) fun u => corrW Hd U ((Dc.chart a).γ (aff t₀ ρ π u)) :=
    isPsh_comp_aff t₀ ρ π (hP a) fun u h => (hu u (hsub u h).1).2.2 (hsub u h)
  obtain ⟨C₃, hC₃⟩ := _root_.LevelTowerAlt.psh_log_growth_bounded _ a₀ δ (B + |C₁|) _ hδ (d1.trans hr1) hps fun u h => by
    obtain ⟨ld, cw, gr, ℓ, h0, h1, e1, e2, b1, b2, -, b4⟩ := key u h
    simp only [corrW, e1, e2, ← h0]
    nlinarith [(abs_le.1 b2).2, (abs_le.1 b4).2]
  have hc : Continuous (affInv t₀ ρ π) := by
    unfold affInv
    fun_prop
  have h00 : affInv t₀ ρ π t₀ = 0 := by
    funext i
    simp [affInv]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 ((hc.tendsto t₀).eventually
    (by rw [h00]; exact ball_mem_nhds _ (half_pos hδ) : ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) (δ / 2) ∈ 𝓝 (affInv t₀ ρ π t₀)))
  refine ⟨ε, hε, |C₃| + |C₂| + B + |C₁| * A, fun t ht hε' => ?_⟩
  have hu2 := hball t (by rwa [mem_ball, dist_eq_norm])
  have hu3 : affInv t₀ ρ π t ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) δ := ball_subset_ball (half_le_self hδ.le) hu2
  have hat := aff_affInv t₀ hρ π t
  have hp1 := (hu _ (ball_subset_ball (d1.trans hr1) hu3)).2.1 (by rw [hat]; exact ht)
  obtain ⟨ld, cw, gr, ℓ, h0, h1, e1, e2, b1, b2, b3, b4⟩ := key _ ⟨hu3, hp1.2⟩
  have h3 := hC₃ _ ⟨hu2, hp1.2⟩
  obtain ⟨s1, s2⟩ := hsz _ hp1
  simp only [hat] at e1 e2 h3 s1 s2
  rw [← h0] at s2
  set R := Real.log ((Dc.chart a).logR t)
  have p1 := abs_nonneg C₁
  have p2 := abs_nonneg C₂
  have p3 := abs_nonneg C₃
  have q1 : |C₁| * ℓ ≤ |C₁| * A * R := by rw [_root_.mul_assoc]; exact mul_le_mul_of_nonneg_left s2 p1
  have q2 : 0 ≤ |C₁| * A := mul_nonneg p1 hA
  have q3 : B ≤ (|C₃| + |C₂| + B) * R := by nlinarith
  have q4 : 0 ≤ |C₁| * ℓ := by positivity
  refine ⟨abs_le.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [corrW, e1, e2]
    linarith [(abs_le.1 b4).1, le_abs_self C₂]
  · linarith [le_abs_self C₃]
  · rw [e2]
    linarith
  · rw [e1]
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [(abs_le.1 b4).1, (abs_le.1 b2).1]
    · linarith [(abs_le.1 b4).2, (abs_le.1 b2).2]

theorem corr_bdd : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → ChartBdd Dc (corrW Hd U) ∧ ∀ a, ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1, ∃ ε > (0 : ℝ), ∃ C : ℝ, ∀ t ∈ offBd Dc a, ‖t - t₀‖ < ε → U ((Dc.chart a).γ t) ≤ C * Real.log ((Dc.chart a).logR t) ∧ |phMu Hd ((Dc.chart a).γ t)| ≤ C * Real.log ((Dc.chart a).logR t) := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or U hU
  have hP := (GlobalTheory.T.cusp_intersection_positive hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU).2.2.1
  refine ⟨fun a t₀ ht₀ => ?_, fun a t₀ ht₀ => ?_⟩
  · obtain ⟨ε, hε, C, h⟩ := near_bdd hG Or hU hP a t₀ ht₀
    exact ⟨ε, hε, C, fun t ht h' => (h t ht h').1⟩
  · obtain ⟨ε, hε, C, h⟩ := near_bdd hG Or hU hP a t₀ ht₀
    exact ⟨ε, hε, C, fun t ht h' => (h t ht h').2⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.CorrBdd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarInt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isArithVar_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ)
    (D : ℕ), IsArithVar p D → IsArithVar t D := by
  intro k _ X p t D hp
  obtain ⟨hdom, hfin, hint, hproj, hflat, hdim⟩ := hp
  have hZ : ∀ f g : X ⟶ Sp ℤ, f = g := fun f g => specZIsTerminal.hom_ext f g
  refine ⟨inferInstance, inferInstance, hint, ?_, ?_, hdim⟩
  · rw [hZ t (GlobalTheory.ShFam.Pad.toSpZ X)]
    exact GlobalTheory.ShFam.Pad.isProjOver_toSpZ hproj
  · rw [hZ (t ≫ spMap (Int.castRingHom ℤ)) (p ≫ spMap (Int.castRingHom k))]
    exact hflat

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsIsoAppOfIsAbelianScheme
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isAbelianScheme_pullback {S S' : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (f : S' ⟶ S) : IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by
      have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

theorem isIso_appTop_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (V : S.Opens) [IsAffine V.toScheme] :
    IsIso (A.hom ∣_ V).appTop := by
  let R : Type := Γ(V.toScheme, ⊤)
  let e : V.toScheme ≅ Sp R := V.toScheme.isoSpec
  let f : Sp R ⟶ S := e.inv ≫ V.ι
  have hf : e.hom ≫ f = V.ι := by simp [f]
  obtain ⟨S₀, B, _, φ, -, hfin, hB, hpb⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring R ((Over.pullback f).obj A) ∅ (isAbelianScheme_pullback A hA f)
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing ℤ S₀
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres B.hom
  have w : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = (A.hom ∣_ V ≫ e.hom) ≫ f := by
    rw [Category.assoc, hf]
    exact (isPullback_morphismRestrict A.hom V).flip.w
  have sq : IsPullback (pullback.lift _ _ w) (A.hom ∣_ V) (pullback.snd A.hom f) e.hom := by
    refine IsPullback.of_right (h₁₂ := pullback.fst A.hom f) (v₁₃ := A.hom) (h₂₂ := f) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [pullback.lift_fst, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  exact GlobalTheory.ProperFunctions.isIso_appTop_baseChange (sq.paste_horiz hpb.1)

theorem isIso_app_of_isAbelianScheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → ∀ U : S.Opens, IsIso (A.hom.app U) := fun _ A _ hA U ↦
  GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens A.hom (fun V ↦
    have : IsAffine V.1.toScheme := V.2
    isIso_appTop_restrict A hA V.1) U

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveHodgePrime
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem af_le_stdLat {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) {F : Type} [Zero F] [One F]
    [DecidableEq F] [Fintype F] (h01 : (0 : F) ≠ 1) {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (p : ℕ)
    (hM : D.M ≤ stdLat RC _) (χ : F → C) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : D.af RC p χ ≤ stdLat RC _ := by
  intro l hl
  have hl1 : D.l1 RC p ≤ stdLat RC _ := by
    refine sup_le hM ?_
    rintro _ ⟨x, hx, rfl⟩
    intro a _
    have : x a ∈ RC := hx a (Set.mem_univ a)
    have h2 : (p : C) * x a ∈ RC := by
      have := RC.mul_mem (natCast_mem RC p) this
      simpa using this
    simpa using h2
  have h3 := hl1 hl
  intro k _
  have h4 : (linMap n χ l) (Pi.single k 1) ∈ RC := h3 _ (Set.mem_univ _)
  have h5 : (linMap n χ l) (Pi.single k 1) = l k := by
    simp only [linMap, Fintype.linearCombination_apply, LinearMap.coe_mk]
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp [h1]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, h0]
    · simp
  rw [h5] at h4
  exact h4

set_option maxHeartbeats 4000000 in
theorem testFacts (hF : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate) (hQ : GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement) (hZ : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement) (hH : GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement) (hOC : GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →  ((chartD e b pq sc w P i).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hAr hpq p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _ hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σ hOrb hSec G c' hc' P i hseq hBase C _ _ _ _ RC hT χ hχ
  classical
  obtain ⟨hAC, ⟨v, hv, hvp⟩, hcomp, hRC⟩ := id hT
  haveI := hAC
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  haveI : CharZero C := (RingHom.charZero_iff (algebraMap Ω C).injective).1 inferInstance
  haveI : Finite (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    simp [Ideal.span_singleton_eq_bot, (Fact.out : p.Prime).ne_zero])
  letI : Fintype (TestPt.NAdd E (D.p + D.q) p) := Fintype.ofFinite _
  have hInt : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun {x} h => ⟨⟨x, (hv _).2 h⟩, rfl⟩⟩
  have hw : algebraMap O C w = algebraMap Ω C (algebraMap O Ω w) := IsScalarTower.algebraMap_apply O Ω C w
  obtain ⟨hO1, -⟩ : (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ True := ⟨hOrb.2.2.2.2.2.2.1.2.1, trivial⟩
  have hp0 : (p : O) ≠ 0 := hOrb.2.2.2.2.2.2.1.1

  obtain ⟨u, hu, hup⟩ := hO1
  have hp1 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have hcd : CharData (CR O y c') p (algebraMap O Ω w)
      (fun (_ : Sg) (a : F) => if a = 0 then (0 : Ω) else 1) := by
    refine ⟨hpΩ, Subalgebra.algebraMap_mem _ w, ?_, h01, fun τ => ⟨by simp, by simp, fun a => ?_⟩⟩
    · obtain ⟨u', hu'⟩ := hu.exists_left_inv
      refine ⟨algebraMap O Ω (u' * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
      have e1 : w ^ (p - 1) = w ^ (p - 2) * w := by
        rw [← pow_succ]; congr 1; omega
      have e2 : (p : O) = u' * w ^ (p - 2) * w := by
        rw [_root_.mul_assoc, ← e1, hup, ← _root_.mul_assoc, hu', _root_.one_mul]
      have := congrArg (algebraMap O Ω) e2
      simpa [map_mul] using this
    · show (if a = 0 then (0 : Ω) else 1) ∈ CR O y c'
      by_cases ha : a = 0
      · simp only [ha, if_true]; exact zero_mem _
      · simp only [ha, if_false]; exact one_mem _
  have hBase' : ((chartD e b pq sc w P i).bc RC).Base RC p (algebraMap O C w) := by
    rw [hw]
    exact (_root_.GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring (chartD e b pq sc w P i) (CR O y c') p (algebraMap O Ω w) _ hcd hBase C RC hRC).2
  have hw0 : algebraMap O C w ≠ 0 := by
    intro h0
    have e1 := congrArg (algebraMap O C) hup
    rw [map_pow, h0, zero_pow (by omega), map_mul, map_natCast] at e1
    exact mul_ne_zero (hu.map (algebraMap O C)).ne_zero hpC e1.symm
  obtain ⟨AA, AW, hAA, hAW, hM, hstab, hFS⟩ := GlobalTheory.T.arith_variety_prime_global_relay E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ
  obtain ⟨hAb, hTi⟩ := _root_.PositivityTheory.Xgn.tight_hopf_order_test hH hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp
  obtain ⟨σ', ee, hfund, hχσ, hσφ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.lifts_eq_frobenius_powers E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ
  have hptors : ∀ x : TestPt.NAdd E (D.p + D.q) p, p • x = 0 := by
    intro x
    ext k
    have : ((p : ℕ) : 𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    simp [nsmul_eq_mul, this]
  have hsec : ∀ x : Fin (D.p + D.q) → F, TestPt.fromNAdd pq (TestPt.toNAdd sc x) = x := by
    intro x
    ext k
    exact hSec.1 (x k)
  have hFlag : GlobalTheory.CompanionTheory.Ar.GR.FlagConcl v p AW.carrier (Pi.basisFun F (Fin (D.p + D.q))) σ' := by
    have h1 := GlobalTheory.T.abelian_factor_tight_field_action (GlobalTheory.T.quotient_zarhin_hodge_tate_subquotient hQ hZ hH) p C v RC hInt hvp hcomp (TestPt.NAdd E (D.p + D.q) p) AA hptors
      (by rw [hAA]; exact hAb) (by rw [hAA]; exact hTi) F (Fin (D.p + D.q) → F) (TestPt.toNAdd sc) (TestPt.fromNAdd pq)
      hsec hstab (by rw [hAA]; rw [hAW] at hFS; exact hFS) (D.p + D.q) (Pi.basisFun F (Fin (D.p + D.q))) σ' hfund
    rw [hAW]
    rw [hAA] at h1
    exact h1
  have hTh := _root_.PositivityTheory.Xgn.teichmuller_test_function E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ σ' ee hχσ
  have hTh' : ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal AW.carrier), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), (fun (τ : Sg) (a : F) => χ τ a) τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig AW.carrier (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal AW.carrier) := by
    rw [hAW]
    exact hTh
  have hleaf := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.w_mul_forms_le_af hZ hH E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp hAb
  have haf : ∀ τ, ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) ≤ stdLat RC _ := fun τ =>
    af_le_stdLat RC h01 _ p hBase'.M_le _ (map_zero (χ τ)) (map_one (χ τ))
  have hseq' : ∀ τ, ((chartD e b pq sc w P i).bc RC).imH RC p τ (fun a => χ τ a) = ((chartD e b pq sc w P i).bc RC).om τ ∧
      ((chartD e b pq sc w P i).bc RC).kerH RC p τ (fun a => χ τ a) = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
    intro τ
    obtain ⟨hbb, h1, h2, h3, h4, h5, h6, h7⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.htLift E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ τ
    obtain ⟨g1, g2⟩ := _root_.PositivityTheory.Xgn.test_group_point_exists hF hQ hZ hH hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp τ hbb h1 h2 h4 h7
    exact _root_.GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin RC p ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) τ hw0 (hleaf τ) (haf τ)
      _ hbb h1 h2 h3 h4 g1 g2 h5 h6
  exact ⟨hleaf, fun τ => (hseq' τ).1, fun τ => (hseq' τ).2,
    GlobalTheory.CompanionTheory.Ar.Num.PtDx.main RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh',
    GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh',
    GlobalTheory.CompanionTheory.Ar.Num.PtInj.kernel_stepGraph RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh'⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameCombined
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∉ SS → ¬ (p : ℤ) ∣ discr E → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC = FinRd.Roots.lieEig Or MC ρC σ := by
  first | exact @PositivityTheory.UnitarySelfGeneration.root_origin_frame_comparison | exact PositivityTheory.UnitarySelfGeneration.root_origin_frame_comparison
end

