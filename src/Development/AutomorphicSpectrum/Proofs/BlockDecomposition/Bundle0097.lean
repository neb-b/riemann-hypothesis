module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorSandwichApprox
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

variable {F : Type} [Field F] [NumberField F]

def ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Set (Fv F v) :=
  {y | Valued.v y ≤ WithZero.exp (-(n : ℤ))}

theorem isClopen_ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : IsClopen (ballV v n) := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-(n : ℤ)))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : ballV v n = {y : Fv F v | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [ballV, Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isClopen_closedBall _ (by simp [hc0])

theorem ballV_subset (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ballV v n ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
  intro y hy
  have h1 : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 : Valued.v y ≤ 1 := le_trans (show Valued.v y ≤ _ from hy) h1
  exact h2

theorem antitone_ballV (v : HeightOneSpectrum (𝓞 F)) : Antitone (ballV (F := F) v) := by
  intro m n hmn y hy
  show Valued.v y ≤ _
  refine le_trans (show Valued.v y ≤ _ from hy) ?_
  rw [WithZero.exp_le_exp]
  omega

theorem iInter_ballV (v : HeightOneSpectrum (𝓞 F)) : ⋂ n, ballV (F := F) v n = {0} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hy
    have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h1 := h (-(Valued.v y).log + 1).toNat
    have h2 : Valued.v y ≤ WithZero.exp (-(((-(Valued.v y).log + 1).toNat : ℕ) : ℤ)) := h1
    conv_lhs at h2 => rw [← WithZero.exp_log hv0]
    rw [WithZero.exp_le_exp] at h2
    have := Int.self_le_toNat (-(Valued.v y).log + 1)
    omega
  · rintro rfl n
    simp [ballV]

theorem nhdsNE_Fv (v : HeightOneSpectrum (𝓞 F)) : (𝓝[≠] (0 : Fv F v)).NeBot := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

theorem tendsto_real_ballV {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam) :
    Tendsto (fun n => lam.real (ballV v n)) atTop (𝓝 0) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  have hfin : ∀ n, lam (ballV v n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono (ballV_subset v n))
  have h := tendsto_measure_iInter_atTop (μ := lam) (s := ballV v)
    (fun n => (isClopen_ballV v n).isOpen.measurableSet.nullMeasurableSet) (antitone_ballV v) ⟨0, hfin 0⟩
  rw [iInter_ballV, measure_singleton] at h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Measure.real, Function.comp_def] using h2

theorem exists_sandwich : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by
  intro F _ _ v lam C g hstd hg0 hg η hη
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  obtain ⟨hcont, hout, hint, -, hone⟩ := hg
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + |C| := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hgK : ∀ s, s ≠ 0 → g s ≤ K := by
    intro s hs
    by_cases hO : s ∈ v.adicCompletionIntegers F
    · have h1 := hint s hO hs
      have h2 : C / (Ideal.absNorm v.asIdeal : ℝ) ≤ |C| :=
        (div_le_self (abs_nonneg C) hq |>.trans' (div_le_div_of_nonneg_right (le_abs_self C) (by linarith)))
      have h3 := (abs_le.1 h1).2
      rw [hKdef]; linarith
    · rw [hout s hO]; exact hK0.le
  have hgi : Integrable g lam := by
    by_contra h
    rw [integral_undef h] at hone
    norm_num at hone
  have hnz : ∀ᵐ s ∂lam, s ≠ 0 := by
    have : ({0}ᶜ : Set (Fv F v)) ∈ ae lam := compl_mem_ae_iff.2 (measure_singleton 0)
    exact this
  have hlim : Tendsto (fun n => K * lam.real (ballV v n)) atTop (𝓝 0) := by
    simpa using (tendsto_real_ballV hstd).const_mul K
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  obtain ⟨B, hB⟩ : ∃ B, B = ballV v n := ⟨_, rfl⟩
  rw [← hB] at hn
  have hBc : IsClopen B := hB ▸ isClopen_ballV v n
  have hBO : B ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := hB ▸ ballV_subset v n
  have h0B : (0 : Fv F v) ∈ B := by rw [hB]; simp [ballV]
  have hBm : MeasurableSet B := hBc.isOpen.measurableSet
  have hBfin : lam B ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono hBO)
  have hcomp : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Formalism.L2.S.S7.AdeleLC.isCompact_integers v
  have hψm : Continuous (Bᶜ.indicator g) := by
    refine continuous_indicator ?_ ?_
    · intro a ha
      rw [hBc.compl.frontier_eq] at ha
      exact absurd ha (Set.notMem_empty a)
    · rw [hBc.compl.isClosed.closure_eq]
      refine hcont.mono ?_
      intro s hs h0
      exact hs (by rw [Set.mem_singleton_iff.1 h0]; exact h0B)
  have hψb : Continuous (B.indicator fun _ => K) :=
    by
    refine continuous_indicator ?_ continuous_const.continuousOn
    intro a ha
    rw [hBc.frontier_eq] at ha
    exact absurd ha (Set.notMem_empty a)
  have hIm : ∫ s, Bᶜ.indicator g s ∂lam = ∫ s in Bᶜ, g s ∂lam := integral_indicator hBm.compl
  have hsplit : ∫ s in B, g s ∂lam + ∫ s in Bᶜ, g s ∂lam = 1 := by
    rw [integral_add_compl hBm hgi, hone]
  have hpos : 0 ≤ ∫ s in B, g s ∂lam := setIntegral_nonneg hBm fun s _ => hg0 s
  have hconst : ∫ s in B, K ∂lam = K * lam.real B := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hup : ∫ s in B, g s ∂lam ≤ K * lam.real B := by
    rw [← hconst]
    refine integral_mono_ae hgi.integrableOn (integrableOn_const hBfin) ?_
    exact ae_restrict_of_ae (hnz.mono fun s hs => hgK s hs)
  have hi1 : Integrable (Bᶜ.indicator g) lam := hgi.indicator hBm.compl
  have hi2 : Integrable (B.indicator fun _ => K) lam :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
  have hIp : ∫ s, (Bᶜ.indicator g s + B.indicator (fun _ => K) s) ∂lam =
      ∫ s in Bᶜ, g s ∂lam + K * lam.real B := by
    rw [integral_add hi1 hi2, hIm, integral_indicator hBm, hconst]
  refine ⟨Bᶜ.indicator g, fun s => Bᶜ.indicator g s + B.indicator (fun _ => K) s, hψm, ?_,
    hψm.add hψb, ?_, fun s => Set.indicator_nonneg (fun s _ => hg0 s) s, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    simp [Set.indicator, hout s hs]
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    have hsB : s ∉ B := fun h => hs (hBO h)
    simp [hsB, hout s hs]
  · intro s hs
    by_cases hsB : s ∈ B
    · simp only [Set.indicator, Set.mem_compl_iff, hsB, not_true_eq_false, if_false, if_true, zero_add]
      exact ⟨hg0 s, hgK s hs⟩
    · simp [Set.indicator, hsB]
  · rw [hIm]; linarith
  · rw [hIp]; linarith

end GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultipliableLocalFactors
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem eventually_valued_algebraMap_eq_one (F : Type) [Field F] [NumberField F] (β : F) (hβ : β ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (algebraMap F (Fv F v) β) = 1 := by
  rw [Filter.eventually_cofinite]
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) β).union
    (HeightOneSpectrum.Support.finite (𝓞 F) β⁻¹)).subset ?_
  intro v hv
  have e : Valued.v (algebraMap F (Fv F v) β) = v.valuation F β :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) β
  rw [Set.mem_ofPred_eq, e] at hv
  rcases lt_or_gt_of_ne hv with h | h
  · refine Set.mem_union_right _ ?_
    show 1 < v.valuation F β⁻¹
    exact ((v.valuation F).one_lt_val_iff (inv_ne_zero hβ)).mpr (by rwa [inv_inv])
  · exact Set.mem_union_left _ h

theorem multipliable_localFactors :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), (∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ β : F, β ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) β) := by
  intro F _ _ S C g hg β hβ
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) :=
    (GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ‖g v (algebraMap F (Fv F v) β) - 1‖ ≤ C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
    filter_upwards [eventually_valued_algebraMap_eq_one F β hβ,
      Set.Finite.compl_mem_cofinite S.finite_toSet] with v hv hvS
    rw [Real.norm_eq_abs, mul_one_div]
    exact hg v hvS _ hv
  have hf : Summable fun v : HeightOneSpectrum (𝓞 F) => g v (algebraMap F (Fv F v) β) - 1 :=
    Summable.of_norm_bounded_eventually hsum hev
  simpa using Real.multipliable_one_add_of_summable hf

end GlobalTheory.CompanionTheory.Mass.MeanV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetConjugateNegOfProd
section
open Formalism.REAL

namespace GlobalTheory.CompanionTheory.Clozel

private theorem neg_one_pow_card_mul_prod_neg_add_conj (u : ℂ) (s : Multiset ℂ) :
    (-1 : ℂ) ^ Multiset.card s * (s.map fun w => -u + (starRingEnd ℂ) w).prod =
      (s.map fun w => u - (starRingEnd ℂ) w).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, ← ih, pow_succ]
    ring

theorem multiset_eq_map_neg_conj_of_polyEq :
    ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n →
      (∀ u : ℂ, (m.map (u + ·)).prod =
        (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) →
      m' = m.map fun z => -(starRingEnd ℂ) z := by
  intro n m m' _ hm' h
  have key : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map fun w => u - (starRingEnd ℂ) w).prod := by
    intro u
    have hc : ((starRingEnd ℂ) ∘ fun w => -(starRingEnd ℂ) u + w) =
        fun w => -u + (starRingEnd ℂ) w := by
      funext w
      simp
    rw [h u, map_mul, map_pow, map_neg, map_one, map_multiset_prod, Multiset.map_map, hc, ← hm',
      neg_one_pow_card_mul_prod_neg_add_conj]
  have hpoly : ((m.map fun z => -z).map fun a => Polynomial.X - Polynomial.C a).prod =
      ((m'.map (starRingEnd ℂ)).map fun a => Polynomial.X - Polynomial.C a).prod := by
    apply Polynomial.funext
    intro u
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def] using key u
  have hroots := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
  have hinv : (m'.map (starRingEnd ℂ)).map (starRingEnd ℂ) = m' := by
    simp [Multiset.map_map, Function.comp_def]
  rw [← hinv, ← hroots, Multiset.map_map]
  exact Multiset.map_congr rfl fun z _ => by simp

end GlobalTheory.CompanionTheory.Clozel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationOfDichotomy
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonStep

theorem isUnit_or_of_add_quot {S : Type} [CommRing S] (ϖ : S)
    (hj : ϖ ∈ (⊥ : Ideal S).jacobson) (hD : Dich ϖ) (a b : S ⧸ Ideal.span {ϖ ^ 2})
    (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨w', hw'⟩ := h.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w'
  have h1 : (a + b) * w - 1 ∈ Ideal.span {ϖ ^ 2} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_add (f := _), map_one]
    rw [hw', sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp h1
  have hu : IsUnit ((a + b) * w) := by
    have hj' : ϖ ∈ Ring.jacobson S := by simpa only [Ideal.jacobson_bot] using hj
    have h2 := Ring.mem_jacobson_iff.mp hj' (ϖ * v)
    have e : (a + b) * w = ϖ * (ϖ * v) + 1 := by linear_combination hv
    rw [e]; exact h2
  have hab : IsUnit (a + b) := isUnit_of_mul_isUnit_left hu
  have hspan : ϖ ^ 0 ∈ Ideal.span {a, b} := by
    obtain ⟨t, ht⟩ := hab.exists_right_inv
    have h3 : (a + b) * t ∈ Ideal.span {a, b} :=
      Ideal.mul_mem_right _ _ (Ideal.add_mem _ (Ideal.subset_span (by simp))
        (Ideal.subset_span (by simp)))
    rw [ht] at h3
    simpa using h3
  rcases hD a b ⟨0, hspan⟩ with h4 | h4
  · right
    exact (isUnit_of_dvd_unit (dvd_add h4 dvd_rfl) hab).map _
  · left
    exact (isUnit_of_dvd_unit (dvd_add dvd_rfl h4) hab).map _

open Polynomial in
theorem step_comp : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  intro S _ ϖ hj hnz hD hA Q n hQ hd hn
  have hRoots : Roots ϖ := GlobalTheory.T.polynomial_roots_of_closed_quotient ϖ hj hnz hD hA
  have hq0 : Q.coeff 0 = Q.eval 0 := Polynomial.coeff_zero_eq_eval_zero Q
  have hspan : ϖ ^ (n + 1) ∈ Ideal.span {Q.coeff 0, ϖ ^ (n + 1)} :=
    Ideal.subset_span (by simp)
  rcases hD (Q.coeff 0) (ϖ ^ (n + 1)) ⟨n + 1, hspan⟩ with hdiv | hdiv
  · refine ⟨0, ?_, ?_⟩
    · rw [← hq0]; exact hdiv
    · rw [zero_pow hd.ne']; exact dvd_zero _
  ·
    have hpow : ϖ ^ (n + 1) ∈ nonZeroDivisors S := pow_mem hnz _
    have hcancel : ∀ x : S, Q.coeff 0 * x = 0 → x = 0 := by
      intro x hx
      obtain ⟨e, he⟩ := hdiv
      have h0 : ϖ ^ (n + 1) * x = 0 := by
        rw [he]; linear_combination e * hx
      exact (mem_nonZeroDivisors_iff_right.mp hpow) x (by rw [mul_comm]; exact h0)
    obtain ⟨c, hc1, i0, hi1, hi2, hi3⟩ := _root_.GlobalTheory.CompanionTheory.NewtonSlope.first_slope ϖ hD hRoots (fun i => Q.coeff i)
      Q.natDegree (n + 1) hd hQ.coeff_natDegree hdiv
    have hs : ∀ i, ∃ t, (i = 0 → t = 1) ∧
        (i ≤ Q.natDegree → Q.coeff i * c ^ i = Q.coeff 0 * t) := by
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact ⟨1, fun _ => rfl, fun _ => by simp⟩
      · by_cases hid : i ≤ Q.natDegree
        · obtain ⟨t, ht⟩ := hc1 i hi hid
          exact ⟨t, fun h => by omega, fun _ => ht⟩
        · exact ⟨0, fun h => by omega, fun h => by omega⟩
    choose s hs0 hsd using hs
    have hunit : IsUnit (s i0) := by
      obtain ⟨t, ht⟩ := hi3
      have h5 : Q.coeff 0 * (s i0 * t - 1) = 0 := by
        have h6 := hsd i0 hi2
        rw [h6] at ht
        linear_combination -ht
      have h7 := hcancel _ h5
      exact IsUnit.of_mul_eq_one t (by linear_combination h7)
    let R : Polynomial S := ∑ i ∈ Finset.range (Q.natDegree + 1),
      Polynomial.C (s i) * Polynomial.X ^ i
    have hRc : ∀ j, j ≤ Q.natDegree → R.coeff j = s j := by
      intro j hj'
      simp only [R, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      simp [Nat.lt_succ_of_le hj']
    have hRe : ∀ y, R.eval y = ∑ i ∈ Finset.range (Q.natDegree + 1), s i * y ^ i := by
      intro y
      simp [R, Polynomial.eval_finsetSum]
    let P : Polynomial (S ⧸ Ideal.span {ϖ ^ 2}) := R.map (Ideal.Quotient.mk _)
    have hP0 : P.coeff 0 = 1 := by
      simp only [P, Polynomial.coeff_map]
      rw [hRc 0 (Nat.zero_le _), hs0 0 rfl, map_one]
    have hPi : IsUnit (P.coeff i0) := by
      simp only [P, Polynomial.coeff_map]
      rw [hRc i0 hi2]
      exact hunit.map _
    have hroot : ∃ y', P.eval y' = 0 := by
      let T := S ⧸ Ideal.span {ϖ ^ 2}
      rcases subsingleton_or_nontrivial T with hT | hT
      · exact ⟨0, Subsingleton.elim _ _⟩
      have hAdd : ∀ a b : T, IsUnit (a + b) → IsUnit a ∨ IsUnit b :=
        isUnit_or_of_add_quot ϖ hj hD
      have unitRoot : ∀ (d : ℕ) (F : Polynomial T), F.Monic → F.natDegree = d →
          ∀ k < d, IsUnit (F.coeff k) → ∃ u : Tˣ, F.eval (u : T) = 0 := by
        intro d
        induction d with
        | zero =>
          intro F hF hdeg k hk
          omega
        | succ d ih =>
          intro F hF hdeg k hk hcoeff
          obtain ⟨x, hx⟩ := hA F hF (by omega)
          by_cases hxu : IsUnit x
          · obtain ⟨u, rfl⟩ := hxu
            exact ⟨u, hx⟩
          let G := F /ₘ (X - C x)
          have hfactor : (X - C x) * G = F := mul_divByMonic_eq_iff_isRoot.mpr hx
          have hG : G.Monic := (monic_X_sub_C x).of_mul_monic_left (hfactor.symm ▸ hF)
          have hGdeg : G.natDegree = d := by
            have h := (monic_X_sub_C x).natDegree_mul hG
            rw [hfactor, hdeg, natDegree_X_sub_C] at h
            omega
          cases k with
          | zero =>
            rw [← hfactor, sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub] at hcoeff
            have hprod : IsUnit (x * G.coeff 0) := by simpa only [neg_neg] using hcoeff.neg
            exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
          | succ k =>
            rw [← hfactor, coeff_X_sub_C_mul, sub_eq_add_neg] at hcoeff
            rcases hAdd _ _ hcoeff with hGu | hneg
            · obtain ⟨u, hu⟩ := ih G hG hGdeg k (by omega) hGu
              exact ⟨u, by rw [← hfactor, eval_mul, hu, mul_zero]⟩
            · have hprod : IsUnit (x * G.coeff (k + 1)) := by
                simpa only [neg_neg] using hneg.neg
              exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
      have htd : P.natTrailingDegree = 0 :=
        Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [hP0]; exact one_ne_zero))
      have hmon : P.reverse.Monic := by
        rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, hP0]
      have hdeg : P.reverse.natDegree = P.natDegree := by
        rw [reverse_natDegree, htd, Nat.sub_zero]
      have hle : i0 ≤ P.natDegree := le_natDegree_of_ne_zero hPi.ne_zero
      have hcoeff : P.reverse.coeff (P.natDegree - i0) = P.coeff i0 := by
        rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
        congr 1
        omega
      obtain ⟨u, hu⟩ := unitRoot P.natDegree P.reverse hmon hdeg (P.natDegree - i0)
        (by omega) (hcoeff.symm ▸ hPi)
      refine ⟨↑(u⁻¹), ?_⟩
      let : Invertible ((u⁻¹ : Tˣ) : T) := (u⁻¹).invertible
      have hre := eval₂_reverse_mul_pow (RingHom.id T) ((u⁻¹ : Tˣ) : T) P
      have hinv : ⅟((u⁻¹ : Tˣ) : T) = (u : T) := by simp
      rw [hinv, eval₂_id, eval₂_id, hu, zero_mul] at hre
      exact hre.symm
    obtain ⟨y', hy'⟩ := hroot
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
    have hRy : ϖ ^ 2 ∣ R.eval y := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      simp only [P, Polynomial.eval_map] at hy'
      rwa [Polynomial.eval₂_at_apply] at hy'
    have hQz : Q.eval (c * y) = Q.coeff 0 * R.eval y := by
      rw [Polynomial.eval_eq_sum_range, hRe, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have h8 := hsd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      rw [mul_pow]
      linear_combination (y ^ i) * h8
    have hn0 : ϖ ^ n ∣ Q.coeff 0 := by rw [hq0]; exact hn
    refine ⟨c * y, ?_, ?_⟩
    · rw [hQz]
      have h9 : ϖ ^ n * ϖ ^ 2 ∣ Q.coeff 0 * R.eval y := mul_dvd_mul hn0 hRy
      refine dvd_trans ?_ h9
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)
    · have h10 : Q.coeff 0 ∣ c ^ Q.natDegree := by
        have h11 := hc1 Q.natDegree hd le_rfl
        simpa [hQ.coeff_natDegree] using h11
      rw [mul_pow]
      exact dvd_mul_of_dvd_left (dvd_trans hn0 h10) _

end GlobalTheory.CompanionTheory.NewtonStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrable
section
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem integrable_prod_detW_rpow : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
    ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro W _ n s hs ν hν
  let μ₀ : Measure (hermC n) := Measure.addHaar
  have hf : ∀ _w : W, Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) μ₀ :=
    fun _ => _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable n s hs μ₀ inferInstance
  have hpi := Integrable.fintype_prod (μ := fun _ : W => μ₀)
    (f := fun _ : W => fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : W => μ₀)]
  exact hpi.smul_measure_nnreal

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end

