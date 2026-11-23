module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0816

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictNormalCrossingsDescentEtaleCompletion
section
open AlgebraicGeometry IsLocalRing ReciprocityTheory.AnForm.R GlobalTheory.Toroidal

namespace GlobalTheory.SncDescent

theorem eq_of_le_span_singleton {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {t : R} (ht : t ∈ maximalIdeal R) {Q : Ideal R} [hQ : Q.IsPrime] (h0 : Q ≠ ⊥)
    (hle : Q ≤ Ideal.span {t}) : Q = Ideal.span {t} := by
  refine le_antisymm hle ?_
  rw [Ideal.span_singleton_le_iff_mem]
  by_contra htQ
  refine h0 (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) Q
    (IsNoetherian.noetherian _) (fun x hx => ?_) ?_)
  · obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 (hle hx)
    exact Submodule.smul_mem_smul ht ((hQ.mem_or_mem hx).resolve_left htQ)
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]

theorem exists_rsp {A : Type} [CommRing A] [IsRegularLocalRing A] {m : ℕ} (p : Fin m → A)
    (hp : ∀ i, p i ∈ maximalIdeal A)
    (hind : ∀ a : Fin m → A, ∑ i, a i * p i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ ∏ i ∈ T, r i = ∏ i, p i := by
  classical
  let τ : Fin m → maximalIdeal A := fun i => ⟨p i, hp i⟩
  have hτ : LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent (τ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (g j)
    have h1 : (maximalIdeal A).toCotangent (∑ j, a j • τ j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← ha j]
      rfl
    rw [Ideal.toCotangent_eq_zero] at h1
    have h2 : ∑ j, a j * p j ∈ maximalIdeal A ^ 2 := by
      simpa [τ] using h1
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (hind a h2 i)
  obtain ⟨J, _, t, hs, hd⟩ := GlobalTheory.RegularQuotient.exists_extend A τ hτ
  let e := Fintype.equivFin (J ⊕ Fin m)
  refine ⟨_, Sum.elim t p ∘ e.symm, Finset.univ.map ⟨e ∘ Sum.inr, e.injective.comp Sum.inr_injective⟩,
    ⟨?_, ?_⟩, ?_⟩
  · rw [e.symm.surjective.range_comp, Set.Sum.elim_range]
    exact hs
  · rw [hd, Fintype.card_sum]
  · rw [Finset.prod_map]
    simp

theorem exists_rsp_of_flat {A R : Type} [CommRing A] [IsRegularLocalRing A] [CommRing R] [IsRegularLocalRing R]
    (φ : A →+* R) (hf : φ.Flat) (hm : (maximalIdeal A).map φ = maximalIdeal R) {m : ℕ} (t : Fin m → R)
    (ht : ∀ i, t i ∈ maximalIdeal R)
    (hind : ∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R)
    (D : Ideal A) (hD : D.map φ = Ideal.span {∏ i, t i})
    (hinj : ∀ i i', (Ideal.span {t i}).comap φ = (Ideal.span {t i'}).comap φ → i = i') :
    ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  classical
  algebraize [φ]
  have hloc : IsLocalHom (algebraMap A R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : algebraMap A R a ∈ maximalIdeal R := hm ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 this ha
  have hff : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective A R
  have : IsDomain A := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have := isRegularRing_of_isRegularLocalRing A
  have : UniqueFactorizationMonoid A := uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing isPrincipal_map_away_of_hasProjectiveDimensionLE A
  have hprime : ∀ i, Prime (t i) := fun i => prime_of_not_mem_sq (ht i) fun h => by
    have := hind (Pi.single i 1) (by simpa [Pi.single_apply] using h) i
    simp at this
  have h0 : ∏ i, t i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hprime i).ne_zero
  have hDt : ∀ d ∈ D, ∀ i, t i ∣ φ d := fun d hd i =>
    (Finset.dvd_prod_of_mem t (Finset.mem_univ i)).trans
      (Ideal.mem_span_singleton.1 (hD ▸ Ideal.mem_map_of_mem φ hd))
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ D, d ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => h0 ?_
    rw [h, Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at hD
    exact hD
  have key : ∀ i, ∃ p : A, Prime p ∧ (Ideal.span {t i}).comap φ = Ideal.span {p} := fun i => by
    have hP : (Ideal.span {t i}).IsPrime := (Ideal.span_singleton_prime (hprime i).ne_zero).2 (hprime i)
    have hne : (Ideal.span {t i}).comap φ ≠ ⊥ := fun h => hd0 (by
      rw [← Ideal.mem_bot, ← h]
      exact Ideal.mem_span_singleton.2 (hDt d hd i))
    obtain ⟨p, hp, hpp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hne
    refine ⟨p, hpp, ?_⟩
    have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hpp.ne_zero).2 hpp
    have : (Ideal.span {t i}).LiesOver ((Ideal.span {t i}).comap φ) := ⟨rfl⟩
    obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Ideal.span {p})
      (q := (Ideal.span {t i}).comap φ) (Ideal.span {t i}) ((Ideal.span_singleton_le_iff_mem _).2 hp)
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      have : p ∈ (⊥ : Ideal R).comap φ := hQo.over.le (Ideal.mem_span_singleton_self p)
      exact hpp.ne_zero (hφ (by simpa using this))
    rw [← eq_of_le_span_singleton (ht i) hQ0 hQ]
    exact hQo.over.symm
  choose p hp hP using key
  have htp : ∀ i, t i ∣ φ (p i) := fun i =>
    Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 ((hP i).ge (Ideal.mem_span_singleton_self _)))
  choose u hu using htp
  have hle : D ≤ Ideal.span {∏ i, p i} := fun x hx => by
    rw [Ideal.mem_span_singleton]
    refine Finset.prod_dvd_of_isRelPrime (fun i _ j _ hij => ?_) fun i _ => ?_
    · refine (hp i).irreducible.isRelPrime_iff_not_dvd.2 fun h => hij (hinj i j ?_)
      rw [hP, hP, Ideal.span_singleton_eq_span_singleton]
      exact (hp i).irreducible.associated_of_dvd (hp j).irreducible h
    · rw [← Ideal.mem_span_singleton, ← hP]
      exact Ideal.mem_span_singleton.2 (hDt x hx i)
  have hprod : φ (∏ i, p i) = (∏ i, t i) * ∏ i, u i := by
    simp only [map_prod, hu, Finset.prod_mul_distrib]
  have hU : IsUnit (∏ i, u i) := by
    have := Ideal.map_mono (f := φ) hle
    rw [hD, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_span_singleton, hprod] at this
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left h0).1 (by simpa using this))
  have hu1 : ∀ i, IsUnit (u i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem u (Finset.mem_univ i)) hU
  obtain ⟨n, r, T, hr, hT⟩ := exists_rsp p (fun i => (mem_maximalIdeal _).2 (hp i).not_isUnit) fun a ha i => by
    have h1 := Ideal.mem_map_of_mem φ ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Ideal.map_pow, hm, map_sum] at h1
    have h2 := hind (fun j => φ (a j) * u j) (by
      convert h1 using 2 with j
      rw [map_mul, hu]; ring) i
    rw [mem_maximalIdeal, mem_nonunits_iff] at h2 ⊢
    exact fun h => h2 ((h.map φ).mul (hu1 i))
  refine ⟨n, r, T, hr, ?_⟩
  have h3 : D.map (algebraMap A R) = (Ideal.span {∏ i, p i}).map (algebraMap A R) := by
    change D.map φ = (Ideal.span {∏ i, p i}).map φ
    rw [hD, Ideal.map_span, Set.image_singleton, hprod, Ideal.span_singleton_mul_right_unit hU]
  rw [hT, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R) D, h3, Ideal.comap_map_eq_self_of_faithfullyFlat]

theorem coeff_single_eq_zero {k σ : Type} [Field k] {g : MvPowerSeries σ k}
    (hg : g ∈ maximalIdeal (MvPowerSeries σ k) ^ 2) (s : σ) :
    MvPowerSeries.coeff (Finsupp.single s 1) g = 0 := by
  classical
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]
  rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, maximalIdeal_eq_bot, Ideal.mem_bot] at ha hb
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ, ha, hb]

theorem exists_rsp_of_isEtaleCompletion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type) [Field k] (m e : ℕ) (φ : A →+* ChartRing k m e) (D : Ideal A), IsEtaleCompletion φ → D.map φ = Ideal.span {∏ i : Fin m, bdParam k m e i} → (∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap φ = (Ideal.span {bdParam k m e i'}).comap φ → i = i') → ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  intro A _ _ _ k _ m e φ D hφ hD hinj
  classical
  have hR : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k _
  have hA := (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion φ hφ).1
  refine exists_rsp_of_flat φ hφ.1 hφ.2.1 (bdParam k m e) (fun i => ?_) (fun a ha i => ?_) D hD hinj
  · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
    simp
  · have h := coeff_single_eq_zero ha (Sum.inl i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single i] at h
    · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, maximalIdeal_eq_bot, Ideal.mem_bot]
      rw [bdParam, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial] at h
      simpa using h
    · intro j _ hj
      rw [bdParam, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, if_neg]
      simp [Finsupp.single_le_iff, Finsupp.single_apply, hj.symm]
    · simp

end GlobalTheory.SncDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMeanValueFlagChartInvariantMeasure
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SubmeanChart

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem card_strictLower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  have e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩
      invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_coe, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem nd_eq_dimFl (X : Data E r) : nd X = dimFl E r := by
  unfold nd dimFl
  rw [Fintype.card_prod, card_strictLower, QuadraticCoefficientForms.card_Psi]

theorem cpt_zero (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ a b
  have h1 : mat (nmat X 0) τ = 1 := by
    ext i j
    simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
    by_cases h : j < i
    · rw [dif_pos h, if_neg (ne_of_gt h)]
      rfl
    · rw [dif_neg h]
  show (mat x0 τ * mat (nmat X 0) τ) a b = x0 τ a b
  rw [h1, Matrix.mul_one]
  rfl

theorem differentiable_cpt (X : Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) := by
  rw [differentiable_pi]; intro τ
  rw [differentiable_pi]; intro a
  rw [differentiable_pi]; intro b
  simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  refine Differentiable.fun_sum fun k _ => Differentiable.const_mul ?_ _
  by_cases h : b < k
  · simp only [nmat, dif_pos h]
    fun_prop
  · simp only [nmat, dif_neg h]
    exact differentiable_const _

theorem norm_dmin_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

theorem nfac_of_orth (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : IsOrth X x) : X.nfac la x = 1 := by
  unfold Data.nfac
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
  rw [norm_div, norm_dmin_of_orth X hx, norm_dmin_of_orth X hx, div_one, Real.one_rpow]

theorem pnorm_eq (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

theorem spread_nonneg (X : Data E r) (la : Wt X.Ψ r) (hr : 0 < r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  have i : Fin r := ⟨0, hr⟩
  have h1 := ciInf_le (Set.finite_range fun i => (la τ i : ℝ)).bddBelow i
  have h2 := le_ciSup (Set.finite_range fun i => (la τ i : ℝ)).bddAbove i
  linarith

theorem chartRad_pos (X : Data E r) (la : Wt X.Ψ r) {w : ℝ} (hr : 0 < r) (hw : (∑ τ, X.spread la τ) ≤ w) :
    0 < chartRad E r w := by
  have h0 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => spread_nonneg X la hr τ) hw
  have hf : (0 : ℝ) < fdeg E := by exact_mod_cast (QuadraticCoefficientForms.card_Psi X) ▸ QuadraticCoefficientForms.card_Psi_pos X
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold chartRad
  positivity

end

end GlobalTheory.SubmeanChart

namespace GlobalTheory.SubmeanChart
noncomputable section

theorem submean_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r) (P : Frame X.Ψ r → ℂ), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → DifferentiableOn ℂ P X.dom → ENNReal.ofReal (X.pnorm la P x ^ 2) ≤ ENNReal.ofReal (2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r) * ∫⁻ z in Metric.ball (0 : V (nd X)) (chartRad E r w), ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
  intro E _ _ _ r X la w x P hr hx hw hP
  set ρ := chartRad E r w with hρdef
  have hρ : 0 < ρ := chartRad_pos X la hr hw
  have hch := GlobalTheory.T.normFactor_and_density_near_one_in_flagChart E r X la w x hr hx hw

  set φ : V (nd X) → ℂ := fun z => P (cpt X x z) with hφdef
  have hφ : DifferentiableOn ℂ φ (Metric.ball 0 ρ) :=
    hP.comp (differentiable_cpt X x).differentiableOn fun z hz =>
      (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).1
  have hsub := GlobalTheory.enorm_pow_le_inv_measure_mul_lintegral_ball (volume : Measure (V (nd X))) (a := 0) hρ hφ 2
  have hne : ENNReal.ofReal (Real.pi ^ nd X * ρ ^ (2 * nd X) / ((nd X).factorial : ℝ)) =
      ENNReal.ofReal (Real.pi ^ dimFl E r * ρ ^ (2 * dimFl E r) / ((dimFl E r).factorial : ℝ)) := by
    rw [nd_eq_dimFl]
  rw [GlobalTheory.volume_ball_euclideanSpace_complex (0 : V (nd X)) hρ, Fintype.card_fin, hne] at hsub
  set D := dimFl E r with hD

  have h1 : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ‖φ z‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (1 / 20)) *
        ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    obtain ⟨-, hn, -⟩ := hch z (le_of_lt (mem_ball_zero_iff.1 hz))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [pnorm_eq, mul_pow]
    have he : 1 ≤ Real.exp (1 / 20) * X.nfac la (cpt X x z) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hn (Real.exp_pos (1 / 20)).le
      rwa [← Real.exp_add, show (1 / 20 : ℝ) + -(1 / 20) = 0 by norm_num, Real.exp_zero] at this
    calc ‖φ z‖ ^ 2 = ‖φ z‖ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖φ z‖ ^ 2 * (Real.exp (1 / 20) * X.nfac la (cpt X x z) ^ 2) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by rw [hφdef]; ring

  have hμ : ENNReal.ofReal (Real.exp (-(1 / 10))) • (volume.restrict (Metric.ball (0 : V (nd X)) ρ)) ≤
      (muF X x).restrict (Metric.ball 0 ρ) := by
    have hb : Metric.ball (0 : V (nd X)) ρ ∩ OmF X x = Metric.ball 0 ρ :=
      Set.inter_eq_left.2 fun z hz => (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).1
    rw [muF, restrict_withDensity measurableSet_ball, Measure.restrict_restrict measurableSet_ball, hb,
      ← withDensity_const]
    refine withDensity_mono (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
    exact ENNReal.ofReal_le_ofReal (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).2.2
  have h2 : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ≤
      ENNReal.ofReal (Real.exp (1 / 10)) *
        ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
    have h3 := lintegral_mono' hμ (le_refl (fun z => ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2)))
    rw [lintegral_smul_measure, smul_eq_mul] at h3
    calc _ = ENNReal.ofReal (Real.exp (1 / 10)) * (ENNReal.ofReal (Real.exp (-(1 / 10))) *
          ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            show (1 / 10 : ℝ) + -(1 / 10) = 0 by norm_num, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr

  have h0 : ENNReal.ofReal (X.pnorm la P x ^ 2) = ‖φ 0‖ₑ ^ 2 := by
    rw [pnorm_eq, nfac_of_orth X la hx, mul_one, show φ 0 = P x by simp only [hφdef, cpt_zero], ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

  have hvol : (ENNReal.ofReal (Real.pi ^ D * ρ ^ (2 * D) / (D.factorial : ℝ)))⁻¹ =
      ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_div, mul_pow, ← pow_mul, mul_comm 2 D]
  have hexp : Real.exp (1 / 20) * Real.exp (1 / 10) ≤ 2 := by
    rw [← Real.exp_add]
    calc Real.exp (1 / 20 + 1 / 10) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log two_pos
  have hc : ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
      (ENNReal.ofReal (Real.exp (1 / 20)) * ENNReal.ofReal (Real.exp (1 / 10))) ≤
      ENNReal.ofReal (2 * (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq : 0 ≤ (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D := by positivity
    calc (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D * (Real.exp (1 / 20) * Real.exp (1 / 10))
        ≤ (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D * 2 := mul_le_mul_of_nonneg_left hexp hq
      _ = _ := by ring
  rw [h0]
  calc ‖φ 0‖ₑ ^ 2 ≤ _ := hsub
    _ ≤ ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
          (ENNReal.ofReal (Real.exp (1 / 20)) * (ENNReal.ofReal (Real.exp (1 / 10)) *
            ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x))) := by
        rw [hvol]
        gcongr
        exact h1.trans (by gcongr)
    _ = (ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
          (ENNReal.ofReal (Real.exp (1 / 20)) * ENNReal.ofReal (Real.exp (1 / 10)))) *
            ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
        ring
    _ ≤ _ := by gcongr

end
end GlobalTheory.SubmeanChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicEmbeddedVanishesAdelicStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_isotropic_embedded_vanishes_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁),
    (∀ u, form σ JW (H'.ι *ᵥ u) H'.x = 0) → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))),
      ∀ z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
        symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (1 : Matrix (Fin n) (Fin n) E) * z * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H'.ι)ᵀ) u = 0 := by
  first | exact @GlobalTheory.MixedLagr.symplectic_isotropic_embedded_vanishes | exact GlobalTheory.MixedLagr.symplectic_isotropic_embedded_vanishes | (intros; apply GlobalTheory.MixedLagr.symplectic_isotropic_embedded_vanishes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelicStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_isotropic_plane_vanishes_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁),
    form σ JW H'.x H'.x = 0 → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))),
      ∀ u' ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) u u' = 0 := by
  first | exact @GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes | exact GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes | (intros; apply GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKilledCapelliSpaceFiniteDimensionalOfFinitenStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameKilledCapelliSpace_finiteDimensional_of_finiteness : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ), (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ)) → ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) → (∀ z ∈ Zalg E b, ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q) → FiniteDimensional ℂ (GlobalTheory.CapKilled.space E b L W q) := by
  first | exact @GlobalTheory.CapKilled.finiteDimensional_space | exact GlobalTheory.CapKilled.finiteDimensional_space | (intros; apply GlobalTheory.CapKilled.finiteDimensional_space <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRightStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_part_right : ∀ (F : Type) [Field F] [NumberField F] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ₁' → AF F) → ℂ)), IsTame F T → IsTame F (partR (κ := κ) T) := by
  first | exact @GlobalTheory.TamePartR.isTame_partR | exact GlobalTheory.TamePartR.isTame_partR | (intros; apply GlobalTheory.TamePartR.isTame_partR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFixLine
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.HTLieFix

end GlobalTheory.HTLieFix

namespace GlobalTheory.HTLieFix

theorem one_left' {S : Scheme.{0}} {G X : Over S} [GrpObj G] : (1 : X ⟶ G).left = X.hom ≫ η[G].left := rfl
end GlobalTheory.HTLieFix

namespace GlobalTheory.HTLieFix

theorem mat_ext' {n : ℕ} {C : Type} [CommRing C] {A B : Matrix (Fin n) (Fin n) C}
    (h : ∀ v, A.mulVec v = B.mulVec v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

theorem prod_ofFn_eq' {G : Type} [Monoid G] {V : Type} [AddCommMonoid V] (T : V → G)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, hadd, prod_ofFn_eq' T h0 hadd (fun i => w i.succ)]

end GlobalTheory.HTLieFix
end
end

