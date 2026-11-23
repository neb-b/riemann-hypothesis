module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationHeightIndependence
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNextStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositive
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareSystemPolarVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0132
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableChartAbsDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0124
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrable
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGoodProjFirstCoordinate
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.Coefficients
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.Top

theorem abs_limNum_sub_le {D : ℕ} {σ : Type} {S : AnSys D σ} {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} (Re Re' : Realis S P) (II : IntersectionSystem)
    (w : Fin (D + 1) → σ) (B : ℝ) (ht : 0 < S.t₀)
    (h1 : Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w)))
    (h2 : Tendsto (fun t => Re'.num II t w) (𝓝[>] 0) (𝓝 (Re'.limNum II w)))
    (hb : ∀ t, 0 < t → t ≤ S.t₀ → |Re.num II t w - Re'.num II t w| ≤ B) :
    |Re.limNum II w - Re'.limNum II w| ≤ B := by
  refine le_of_tendsto (h1.sub h2).abs ?_
  filter_upwards [Ioc_mem_nhdsGT ht] with t ht'
  exact hb t ht'.1 ht'.2

theorem coefficients : Coefficients := by
  intro hI D N Ψ _ S thH hth
  obtain ⟨C₂', hC⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.abs_num_sub_num_le hI D (Option (Ψ × Fin N)) S thH hth
  obtain ⟨Cst, hW, hWS⟩ := GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound Ψ N (D + 1)
  have ht : 0 < S.t₀ := (S.reg none).1
  refine ⟨Cst * ((Fintype.card (Option (Ψ × Fin N)) : ℝ) ^ (D + 1)) * C₂',
    fun II hII K _ ι _ P Re => ?_⟩
  obtain ⟨C₃, s₀, -, hag⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.agreementPos hI D (Option (Ψ × Fin N)) S 0 ht
  have hPB : ∀ R : Realis S P, R.PBs II = toWtS (formPoly (D + 1) (R.limNum II)) := fun R => rfl
  have hPBwt : ∀ R : Realis S P,
      R.PBwt II = toWt (formPoly (D + 1) fun w => R.limNum II (some ∘ w)) := fun R => rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hPB]
    exact (hWS _ 0 (formPoly_isHomogeneous_and_eval _ _ _).1).1
  · rw [hPBwt]
    exact (hW _ 0 (formPoly_isHomogeneous_and_eval _ _ _).1).1
  · rw [hPB, hPBwt]
    exact (poly_s_zero Ψ N (D + 1)).1 _
  · intro Re' T α H hdeg hT hH hpot hvc hnef
    have hb := hC II hII K ι P Re Re' T α H hdeg hT hH hpot hvc hnef
    have hlim : ∀ w, |Re.limNum II w - Re'.limNum II w| ≤ C₂' * ∑ p ∈ T, α p * Real.log p :=
      fun w => abs_limNum_sub_le Re Re' II w _ ht ((hag II hII K ι P Re).1 w)
        ((hag II hII K ι P Re').1 w) fun t h0 h1 => hb t h0 h1 w
    have hB0 : 0 ≤ C₂' * ∑ p ∈ T, α p * Real.log p := (abs_nonneg _).trans (hlim fun _ => none)
    have hcard : ((Fintype.card (Ψ × Fin N) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) ≤
        ((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) := by
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) hB0
      rw [Fintype.card_option]
      push_cast
      linarith
    constructor
    · have hhom := ((formPoly_isHomogeneous_and_eval (Option (Ψ × Fin N)) (D + 1) (Re.limNum II)).1).sub
        ((formPoly_isHomogeneous_and_eval (Option (Ψ × Fin N)) (D + 1) (Re'.limNum II)).1)
      have hco : ∀ m, |(formPoly (D + 1) (Re.limNum II) - formPoly (D + 1) (Re'.limNum II)).coeff m| ≤
          ((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) :=
        fun m => by
          rw [coeff_sub]
          exact (formPoly_sub_bound _ _ _ _ _ hlim).1 m
      intro m
      rw [hPB, hPB, ← coeff_sub, ← map_sub]
      calc _ ≤ Cst * (((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) *
            (C₂' * ∑ p ∈ T, α p * Real.log p)) := (hWS _ _ hhom).2 hco m
        _ = _ := by ring
    · have hhom := ((formPoly_isHomogeneous_and_eval (Ψ × Fin N) (D + 1)
          (fun w => Re.limNum II (some ∘ w))).1).sub
        ((formPoly_isHomogeneous_and_eval (Ψ × Fin N) (D + 1) (fun w => Re'.limNum II (some ∘ w))).1)
      have hco : ∀ m, |(formPoly (D + 1) (fun w => Re.limNum II (some ∘ w)) -
          formPoly (D + 1) (fun w => Re'.limNum II (some ∘ w))).coeff m| ≤
          ((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) :=
        fun m => by
          rw [coeff_sub]
          exact ((formPoly_sub_bound _ _ _ _ _ fun w => hlim (some ∘ w)).1 m).trans hcard
      intro m
      rw [hPBwt, hPBwt, ← coeff_sub, ← map_sub]
      calc _ ≤ Cst * (((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) *
            (C₂' * ∑ p ∈ T, α p * Real.log p)) := (hW _ _ hhom).2 hco m
        _ = _ := by ring

end GlobalTheory.CompanionTheory.Ar.PB.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightPolynomialReflectionSum
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_polar {σ : Type} [Fintype σ] {n : ℕ} {α : Type} {l : Filter α} {f : α → (Fin n → σ) → ℝ}
    {a : (Fin n → σ) → ℝ} (c : Fin n → σ → ℝ) (h : ∀ w, Tendsto (fun t => f t w) l (𝓝 (a w))) :
    Tendsto (fun t => polar n (f t) c) l (𝓝 (polar n a c)) := by
  unfold polar
  exact tendsto_finsetSum _ fun w _ => (h w).const_mul _

theorem Realis.limNum_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type}
    {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) {II : IntersectionSystem}
    (hII : IsFullIntersectionSystem II) (hpos : 0 < S.t₀) (π : Equiv.Perm (Fin (D + 1)))
    (w : Fin (D + 1) → σ) : Re.limNum II (w ∘ π) = Re.limNum II w := by
  have hev : (fun t => Re.num II t (w ∘ π)) =ᶠ[𝓝[>] 0] fun t => Re.num II t w := by
    filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
    have h := (hII.1 K ι).1 P (D + 1) (fun j => Re.line (w j) t) π Re.arith
      fun j => Re.line_smooth _ t ht.1 ht.2
    unfold Realis.num
    exact congrArg (· / (Re.deg : ℝ)) h
  unfold Realis.limNum limUnder
  rw [Filter.map_congr hev]

theorem AnSys.degNum_perm {e : ℕ} {σ : Type} (S : AnSys e σ) (π : Equiv.Perm (Fin e)) (w : Fin e → σ) :
    S.degNum (w ∘ π) = S.degNum w :=
  ReciprocityTheory.AnForm.M.mIntSymm S.A (fun j => S.th (w j)) π fun _ => 1

theorem thmA_limit : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (Re.PB II) + eval (fun x => c x + u / 2 * ε x) (Re.PB II) = (tsgPoly (d + 1) kappa (linePoly c ε SY.degPoly)).eval u := by
  intro hI hF II hII K _ ι _ d σ _ SY P Re a₀ ε Q c hc u
  have hpos : 0 < SY.t₀ := (SY.reg a₀).1
  have hposW : 0 < Q.an.SW.t₀ := (Q.an.SW.reg none).1
  obtain ⟨C₃, s₀, -, hAg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.agreementPos hI (d + 1) σ SY 0 hpos
  have hlim := (hAg II hII K ι P Re).1
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ Q.an.SW.t₀ := by
    filter_upwards [Ioc_mem_nhdsGT hposW] with t ht using ⟨ht.1, ht.2⟩
  refine _root_.GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity σ (d + 1) (Re.limNum II) SY.degNum kappa ε a₀ (Re.limNum_perm hII hpos)
    SY.degNum_perm (fun n hn => ?_) c hc u
  have hsq := _root_.GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale hI II hII K ι d σ SY P Re a₀ ε Q n hn
  refine ⟨?_, fun k hk hk2 => ?_⟩
  · have h1 := tendsto_polar (fun _ (x : σ) => (n x : ℝ)) hlim
    have h2 : Tendsto (fun t => polar (d + 2) (Re.num II t) fun _ (x : σ) => (n x : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).1.symm)
    exact tendsto_nhds_unique h1 h2
  · have h1 := tendsto_polar (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) hlim
    have h2 : Tendsto (fun t => -∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t))
          (Q.an.wcoef (fun a => (n a : ℝ)) k i)) (𝓝[>] 0)
        (𝓝 (-∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potH (w r)) Q.an.gH)
          (Q.an.wcoef (fun a => (n a : ℝ)) k i))) :=
      (tendsto_finsetSum _ fun i _ => tendsto_polar _ fun w =>
        (_root_.GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence hI d σ SY a₀ ε Q.an w).2).neg
    have h3 := tendsto_nhds_unique (h1.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).2 k hk hk2)) h2
    let square := Q.an
    let coeff : σ → ℝ := fun a => (n a : ℝ)
    have hcoeff : coeff a₀ = 0 := by simp [coeff, hn]
    have hIntegralIdentity :
        ∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt square.SW.A (fun r => square.SW.potH (w r)) square.gH)
          (square.wcoef coeff k i) =
        2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) := by
      have hSquareLim :=
        _root_.GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence hI d σ SY a₀ ε square
      obtain ⟨-, hnW, hC2W, -, -⟩ := anSys_open_basics (d + 2) (Option σ) square.SW
      obtain ⟨-, hnY, hC2Y, -, -⟩ := anSys_open_basics (d + 1) σ SY
      have hhom (w : Fin (d + 1) → σ) :
          MIntegrable SY.A (fun i => SY.potH (w i)) (fun _ => 1) ∧
            mInt SY.A (fun i => SY.potH (w i)) (fun _ => 1) = SY.degNum w := by
        let : MeasurableSpace SY.X := borel SY.X
        have : BorelSpace SY.X := ⟨rfl⟩
        have hlim := hI.convergenceSigned SY.A SY.Θ SY.L SY.s SY.m SY.W
          SY.potΘ SY.posΘ SY.potL SY.sec SY.snc SY.norm_le
          (fun i => SY.th (w i)) (fun i => SY.ph (w i)) (fun i => SY.phT (w i)) SY.C₅ SY.C SY.t₀
          (fun i => SY.sing (w i)) (fun i => SY.reg (w i)) (fun i => SY.c2 (w i))
          (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
          (fun _ y _ => SY.abs_one_le_log_rW y)
          (TendstoUniformlyOn.tendstoLocallyUniformlyOn (by
            refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
            exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε))
        refine ⟨hlim.1, ?_⟩
        have hDegree : Tendsto (fun t => mInt SY.A (fun i => SY.potT (w i) t) (fun _ => 1))
            (𝓝[>] 0) (𝓝 (SY.degNum w)) :=
          tendsto_const_nhds.congr' (by
            filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
            exact (ReciprocityTheory.AnForm.M.massIndep SY.A (fun i => SY.th (w i))
              (fun i => SY.phT (w i) t) (fun i => (SY.sing (w i)).1)
              (fun i => ((SY.reg (w i)).2.2 t ht.1 ht.2).1)).symm)
        exact tendsto_nhds_unique hlim.2 hDegree

      have hexW := fun i => mInt_sumPot_expand (d + 2) square.SW.X square.SW.A (Option σ) square.SW.open' square.SW.potH
        (square.wcoef coeff k i) square.gH hnW hC2W fun w => (hSquareLim w).1
      have hexY := mInt_sumPot_expand (d + 1) SY.X SY.A σ SY.open' SY.potH
        (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) (fun _ => 1) hnY hC2Y fun w => (hhom w).1
      have hpolW : ∀ i, polar (d + 2) (fun w => mInt square.SW.A (fun r => square.SW.potH (w r)) square.gH) (square.wcoef coeff k i) =
          mInt square.SW.A (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH := fun i => (hexW i).2.symm
      have hpolY : polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) =
          mInt SY.A (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (fun _ => 1) := by
        rw [hexY.2]
        exact Finset.sum_congr rfl fun w _ => by rw [(hhom w).2]

      have hoW : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ square.U n → square.ΦW n z ∈ square.SW.open' := by
        intro n z hz
        rw [square.bdry_eq 0, Set.mem_preimage, square.first_projection_chart_compat n z hz]
        exact square.ΦY_open n _ (by simpa using hz)

      have hcW := fun i => integrableOn_hasSum_paramCover (d + 2) square.SW.X square.SW.A _ _ square.ΦW
        (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH square.coverW
        (fun n z hz r => SqFubini.isC2At_sumPot _ _ _ _ fun a => hC2W a _ (hoW n z (square.B_meas n |>.2 hz)))
        (hexW i).1
      have hcY := integrableOn_hasSum_paramCover (d + 1) SY.X SY.A _ _ square.ΦY
        (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (fun _ => 1) square.coverY
        (fun n z hz r => SqFubini.isC2At_sumPot _ _ _ _ fun a => hC2Y a _ (square.ΦY_open n z (square.B_meas n |>.2 hz)))
        hexY.1

      have hFibreIntegral : ∀ n, ∑ i ∈ Finset.range k,
          ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n},
          square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z =
          2 * kappa k * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n},
            (fun _ => (1 : ℝ)) (square.ΦY n z) * paramDens
              (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z := by
        intro n
        let α : (Fin d → ℂ) → ℝ := fun y => ∑ a, coeff a * square.α n a y
        have hd := GlobalTheory.T.square_parametrized_density_formula d σ SY a₀ ε square coeff hcoeff n k hk hk2
        have hmW : MeasurableSet {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n} := (square.coverW.2.1 n).1
        have hmY : MeasurableSet {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n} := (square.coverY.2.1 n).1
        let F : ℕ → (Fin (d + 2) → ℂ) → ℝ := fun i z =>
          logSin (square.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) * maDens (SqFubini.EW (square.G n) α k i) z
        have hae : ∀ i < k, ∀ᵐ z ∂(volume.restrict {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n}),
            square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z = F i z := by
          intro i hi
          filter_upwards [ae_restrict_of_ae (SqFubini.ae_ne d), ae_restrict_mem hmW] with z hne hz
          have hU : Fin.tail (Fin.tail z) ∈ square.U n := (square.B_meas n).2 hz
          have h1 : square.gH (square.ΦW n z) = logSin (square.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) :=
            square.norm_hom n z hU hne
          have h2 : paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z =
              maDens (SqFubini.EW (square.G n) α k i) z := hd.2 i hi z hU
          rw [h1, h2]
        have hH : ∀ z ∈ {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n},
            (fun _ => (1 : ℝ)) (square.ΦY n z) * paramDens
              (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z =
            maDens (SqFubini.EY (square.G n) α k) z := by
          intro z hz
          have h2 : paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z =
              maDens (SqFubini.EY (square.G n) α k) z := hd.1 z ((square.B_meas n).2 hz)
          rw [h2, one_mul]
        have hFint : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n} :=
          fun i hi => ((hcW i).1 n).congr (hae i hi)
        have hHint : IntegrableOn (maDens (SqFubini.EY (square.G n) α k)) {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n} :=
          (integrableOn_congr_fun hH hmY).1 (hcY.1 n)
        have hpt : ∀ y ∈ square.B n, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
            (2 * kappa k) * ∫ a : ℂ, maDens (SqFubini.EY (square.G n) α k) (Fin.cons a y) := by
          intro y hy
          have hyU : y ∈ square.U n := (square.B_meas n).2 hy
          have hnh : square.U n ∈ 𝓝 y := (square.U_open n).mem_nhds hyU
          have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := ENat.LEInfty.out
          exact GlobalTheory.T.log_sine_monge_ampere_integral hF d k hk hk2 (square.G n) α y
            (by filter_upwards [hnh] with y' hy' using square.G_pos n y' hy')
            (fun p q => ((square.G_smooth n p q).contDiffAt hnh).of_le h2)
            (ContDiffAt.sum fun a _ => contDiffAt_const.mul (((square.α_smooth n a).contDiffAt hnh).of_le h2))
        rw [Finset.sum_congr rfl fun i hi => integral_congr_ae (hae i (Finset.mem_range.1 hi)),
          setIntegral_congr_fun hmY hH]
        exact SqFubini.fibre_sum (square.B n) F _ _ hFint hHint hpt (square.B_meas n).1
      have hsW : HasSum (fun n => ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n},
          square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z)
          (∑ i ∈ Finset.range k, mInt square.SW.A (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH) :=
        hasSum_sum fun i _ => (hcW i).2
      rw [funext hFibreIntegral] at hsW
      rw [Finset.sum_congr rfl fun i _ => hpolW i, hpolY]
      exact hsW.unique (hcY.2.mul_left _)
    rw [h3, hIntegralIdentity]
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LintegralFibreLogNormFinite
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

section Assembly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem setSheetDensity_eq_zero {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ S, g z = 0) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : setSheetDensity S Ψ φ g y w = 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
  · rfl

theorem setSheetDensity_sum {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {τ : Type*} (t : Finset τ) (G : τ → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    setSheetDensity S Ψ φ (fun z => ∑ i ∈ t, G i z) y w = ∑ i ∈ t, setSheetDensity S Ψ φ (G i) y w := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
  · simp

theorem exists_mem_domCell [DecidableEq K] {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) :
    ∃ i, z ∈ domCell i := by
  choose i1 _ using hz
  have : Nonempty ((k : K) → ι k) := ⟨i1⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun i' : (k : K) → ι k => ‖segre z i'‖
  exact ⟨i, hi⟩

theorem segre_ne_zero_of_mem_domCell {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0)
    {i : (k : K) → ι k} (hi : z ∈ domCell i) : segre z i ≠ 0 := by
  choose i1 hi1 using hz
  have h1 : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hi1 k
  intro h0
  have := hi i1
  rw [h0, norm_zero] at this
  exact h1 (norm_le_zero_iff.1 this)

end Assembly

theorem cell_mass_lt_top {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {N : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) (hsQ : s ∉ Q)
    (hnn : ∀ y w, 0 ≤ setSheetDensity (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y w) :
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y) < ⊤ := by
  classical
  set σ : Fin (Fintype.card ((k : K) → ι k)) ≃ ((k : K) → ι k) := (Fintype.equivFin _).symm with hσ
  set G := (domCell i).indicator (absLogNorm A s) with hG
  obtain ⟨hGm, hGi⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant K ι A s a i hA hAa hs
  have hzero := _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts K ι Q _ σ i hQ.2.1.2.1
  have hdim := _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartComponents_dim K ι Q e _ σ i hQ
  have hfin := _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite K ι Q e _ σ i Ψ hQ hΨ hΨ0 hdim
  have hfs := _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum.fibreSum K ι Q e _ σ i N G Ψ hQ hN hGi hΨ0 (_root_.GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ hQ hΨ) hzero hdim hfin
  have hsm : ∀ j, ∀ J ∈ chartComponents (conePts Q) σ i, GroundTheory.Heights₂.Heights.SmoothNear
      (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (chartPot σ i N j) := fun j J hJ =>
    GroundTheory.Heights₂.Heights.smoothNear_chartPot σ i hN (fun x hx => by
      have hx' : x ∈ chartSet (conePts Q) σ i := by
        rw [← hzero]
        exact fun q hq => hx q ((mem_chartComponents.1 hJ).1.2 hq)
      obtain ⟨z, -, hzi, rfl⟩ := hx'
      simpa using hzi) j
  have hint : Integrable (fun y => ∑ J ∈ chartComponents (conePts Q) σ i,
      chartAbsDens J (chartProjMatrix σ Ψ) (chartWeight σ i G) (chartPot σ i N) y) :=
    integrable_finsetSum _ fun J hJ =>
      _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.integrable_chartAbsDens_cellWeight K ι Q e _ σ i Ψ N A s a J hA hAa hs hGm hzero hJ (hfin J hJ) fun R C =>
        _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log _ e J _ _ _ R C (mem_chartComponents.1 hJ).1.1 (hdim J hJ) (hfin J hJ)
          (_root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component K ι Q e _ σ i s a hQ hs hsQ J hJ) fun j => hsm j J hJ
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
  filter_upwards [hfs] with y hy
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : cxPosDens (conePts Q) Ψ (pot N) G y =
      ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot N) G y w := by
    unfold cxPosDens
    exact finsum_congr fun w => finsum_congr fun _ => max_eq_left (hnn y w)
  rw [hpos, hy]
  exact Finset.sum_le_sum fun J _ =>
    GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.chartDens_le_chartAbsDens _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart


open GlobalTheory.CompanionTheory.Ar.Pub.CxChart in
theorem GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  intro K _ ι _ Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ
  classical
  obtain ⟨N, hN, hTw⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist K ι e L hL
  obtain ⟨hnn, hbd⟩ := hTw (conePts Q) Ψ fun z hz => hz.1
  set G : ((k : K) → ι k) → ((Σ k, ι k) → ℂ) → ℝ := fun i => (domCell i).indicator (absLogNorm A s) with hG
  have hG0 : ∀ i z, 0 ≤ G i z := fun i z => Set.indicator_nonneg (fun z _ => by
    unfold absLogNorm
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl) z
  have hWm := fun i => _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant K ι A s a i hA hAa hs
  have hcell : ∀ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) < ⊤ := by
    intro i
    by_cases hi : ∃ z ∈ conePts Q, segre z i ≠ 0
    · obtain ⟨Ψ', hΨ', hΨ0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord K ι Q e i hQ hi
      rw [_root_.GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep K ι Q e Ψ Ψ' N (G i) hQ hΨ hΨ' hN (hWm i).1 (hWm i).2]
      exact cell_mass_lt_top hQ hΨ' hΨ0 hN hA hAa hs hsQ fun y w => (hTw (conePts Q) Ψ' fun z hz => hz.1).1 _ y w (hG0 i)
    · have h0 : ∀ z ∈ conePts Q, G i z = 0 := fun z hz => Set.indicator_of_notMem (fun hzi =>
        hi ⟨z, hz, segre_ne_zero_of_mem_domCell hz.1 hzi⟩) _
      have : ∀ y, cxPosDens (conePts Q) Ψ (pot N) (G i) y = 0 := fun y => by
        unfold cxPosDens
        simp [setSheetDensity_eq_zero (pot N) h0]
      simp [this]
  have hfib := _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ hQ hΨ
  have hcov : ∀ z ∈ conePts Q, |logNormC A s z| ≤ ∑ i, G i z := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_mem_domCell hz.1
    have : |logNormC A s z| = G i z := by
      simp only [hG, Set.indicator_of_mem hi, absLogNorm, if_pos hz.1]
    rw [this]
    exact Finset.single_le_sum (f := fun i => G i z) (fun i _ => hG0 i z) (Finset.mem_univ i)
  have hpt : ∀ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) ≤
      ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
    intro y
    have hnnd : ∀ i, 0 ≤ cxPosDens (conePts Q) Ψ (pot N) (G i) y := fun i =>
      finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnnd i, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold cxPosDens
    simp only [finsum_mem_eq_finite_toFinset_sum _ (hfib y)]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    refine (hbd _ (fun z => ∑ i, G i z) y w hcov).trans ?_
    rw [setSheetDensity_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => le_max_left _ _) (by positivity)
  calc ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|)
      ≤ ∫⁻ y, ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (3 ^ e) * ∑ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum' _ fun i _ =>
          (_root_.GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable K ι Q e Ψ N (G i) hQ hΨ hN (hWm i).1 (hWm i).2).ennreal_ofReal]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.2 fun i _ => hcell i)
end
end

