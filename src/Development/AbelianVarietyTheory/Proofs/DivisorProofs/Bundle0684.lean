module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonZeroDivisor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonzeroNonunitDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLSeriesEqSumPrincipalPartialSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallinePeriodEqCechDeRhamPeriod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticOnNhdOrbitPol
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.OrbitAnalytic in
theorem analyticOnNhd_orbit_pol : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ (P : Pol p q r s), AnalyticOnNhd ℝ (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) Set.univ ∧ ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) 0 = F.ι ((omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) ^ k) P) := by
  intro p q r s T0 T1 T2 F Z hZ P
  set Y := Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z with hY
  let f : ℕ → ℝ → F.H := fun k t => F.Om (T0.expt (t • Z)) (F.ι ((omAct p q r s Y ^ k) P))
  have hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t := fun k t =>
    hasDerivAt_orbit (fun t => F.Om (T0.expt (t • Z)))
      (fun s t => by simp only [T0.expt_add Z hZ, map_mul]) _ _
      (by simpa only [pow_succ', Module.End.mul_apply] using F.der Z hZ ((omAct p q r s Y ^ k) P)) t
  have h0 : (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) = f 0 := by
    funext t; simp [f]
  rw [h0]
  refine ⟨fun a _ => ?_, fun k => ?_⟩
  · set S : ℝ := 4 * ∑ l, ∑ l', ‖Y l l'‖ with hS
    have hS0 : 0 ≤ S := by positivity
    refine analyticAt_of_bound f hf ((2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖) (S + 1)⁻¹
      (by positivity) (fun k t => ?_) a
    have hb := (_root_.GlobalTheory.FockAnalytic.omAct_pow_norm_le p q r s F.H F.ι (isFockIsometry_of_fockData F) Y P.totalDegree k P le_rfl).2
    simp only [f]
    rw [F.isom]
    refine hb.trans ?_
    rw [← hS, inv_pow, div_inv_eq_mul]
    calc _ ≤ (S + 1) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖ := by
          gcongr; linarith
      _ = _ := by ring
  · have hit : ∀ k, iteratedDeriv k (f 0) = f k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [iteratedDeriv_succ, ih]; funext t; exact (hf k t).deriv
    rw [hit]
    simp [f, T0.expt_zero]

end GlobalTheory.FockAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqv_cechAug_of_isIntegralHom_of_surjective_of_sh : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  first
  | exact @GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | exact GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | (intros; apply GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_cech_level_eq_zero_of_pos : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (m : ℕ), 0 < m → ∀ y : H R (disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k))))) F m, y = 0 := by
  first
  | exact @GlobalTheory.EtC.cech_level_acyclic
  | exact GlobalTheory.EtC.cech_level_acyclic
  | (intros; apply GlobalTheory.EtC.cech_level_acyclic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonZeroDivisorStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_vanishes_away_nonZeroDivisor : ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (n i : ℤ) (z : Ht q (sp R) n i), pull _ (spMap (algebraMap R (FractionRing R))) _ _ z = 0 → ∃ g ∈ nonZeroDivisors R, pull _ (spMap (algebraMap R (Localization.Away g))) _ _ z = 0 := by
  first | (exact @GlobalTheory.EtC.classVanishesAwayNZD) | (exact GlobalTheory.EtC.classVanishesAwayNZD) | (intros; apply GlobalTheory.EtC.classVanishesAwayNZD  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonzeroNonunitDomainStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain : ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B], ¬ IsField B → IsUnit (q : B) → ∀ (n i : ℤ) (x : Ht q (sp B) n i), pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 → ∃ f : B, f ≠ 0 ∧ ¬ IsUnit f ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.classVanishesAway) | (exact GlobalTheory.EtC.classVanishesAway) | (intros; apply GlobalTheory.EtC.classVanishesAway  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEvDefectDvd
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem cobOne_ev_defect_dvd : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → ∃ z, cobOne O (G.A n) (c.ev n s) = (p : O) ^ n • z := by
  intro p _ O E _ _ _ hF G d c f hf n s hs
  have : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  obtain ⟨hf0, -, hfc⟩ := hf
  obtain ⟨κ, -, hκ⟩ := ((series_in_ideal_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1).1 hfc
  obtain ⟨-, hκ0, hrest⟩ := _root_.GlobalTheory.QLog.integral_cob_defect_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hcob := (hrest (p ^ n) s hs).1
  refine ⟨c.ev₂ n κ, ?_⟩
  rw [← (GlobalTheory.T.formalChart_evalSquare_properties p O G d c n s).2.2.2, hcob, map_sub, map_smul,
    (_root_.GlobalTheory.QLog.Chart.ev_nmul_pow p O G d c n).2.1 κ, hκ0 hf0, map_zero, sub_zero, Nat.cast_pow]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeStrip

theorem completedLBoundedInStrips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  intro E _ _ _ I _ φ hφ χ n hu hi hn
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := _root_.GlobalTheory.exists_ideal_character_of_unitary_hchar E χ hu
  have hβ : ∀ β : 𝓞 E, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : E) := by
    intro β h0 h1
    have h0' : (β : E) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, hi (Units.mk0 _ h0')]
    simp only [wt, Units.val_mk0, zpow_neg, Finset.prod_inv_distrib]
  have hle : ∀ a, ‖X a‖ ≤ 1 := fun a => by
    by_cases ha : a = ⊥
    · simp [ha, hX0]
    by_cases ha' : a ⊔ m = ⊤
    · exact (hXn a ha ha').le
    · simp [hXz a ha']
  obtain ⟨r, c, B, M, F, hB, hM, hper, hinv, hdec⟩ := _root_.GlobalTheory.HeckeStrip.heckeSeries_eq_sum_pSeries E I φ n m X hm hX0 hXm hXn hXz hβ
  choose Λ hΛd hΛb hΛe using fun k => _root_.GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded E I φ hφ n hn (M k) (F k) (hM k) (hper k) (hinv k)
  have hB0 : ∀ k, ((B k : ℕ) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hB k).ne'
  refine ⟨fun s => ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * Λ k s, ⟨?_, fun s hs => ?_⟩, ?_⟩
  · intro s
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((differentiableAt_const _).mul ((differentiableAt_id.const_cpow (Or.inl (hB0 k))))).mul ((hΛd k).differentiableAt)
  · refine ⟨∑' a : Ideal (𝓞 E), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s), ?_, ?_⟩
    · rw [GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum E X hX0 hX1 hXm hle s hs]
      convert GlobalTheory.HeckeOne.hasProd_exp hu hs using 1
      simp only [hXP, GlobalTheory.HeckeOne.cf]
    · rw [hdec s hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hΛe k s hs]
      ring
  · intro a b hab
    choose C hC using fun k => hΛb k a b hab
    refine ⟨∑ k, ‖c k‖ * ((B k : ℝ) ^ b * |C k|), fun s h1 h2 => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_natCast_cpow_of_pos (hB k)]
    have hB1 : (1 : ℝ) ≤ (B k : ℝ) := by exact_mod_cast hB k
    gcongr
    exact (hC k s h1 h2).trans (le_abs_self _)

end GlobalTheory.HeckeStrip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffPIterateInvariantDerivationCoord
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.FrobIter

def iterLin {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (u : Fin d → R) (n : ℕ) :
    MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R where
  toFun := (invDer μ u)^[n]
  map_add' := by
    obtain ⟨hadd, -, -⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hμ u
    induction n with
    | zero => intro F G; rfl
    | succ n ih => intro F G; simp only [Function.iterate_succ_apply', ih, hadd]
  map_smul' := by
    obtain ⟨-, hsmul, -⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hμ u
    induction n with
    | zero => intro a F; rfl
    | succ n ih => intro a F; simp only [Function.iterate_succ_apply', ih, hsmul, RingHom.id_apply]

theorem iterLin_apply {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (u : Fin d → R) (n : ℕ) (F : MvPowerSeries (Fin d) R) :
    iterLin hμ u n F = (invDer μ u)^[n] F := rfl

theorem constantCoeff_iterate_invDer_X_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (l : MvPowerSeries (Fin d) Q) (j : Fin d), QL μ ⊤ l → In (RingHom.ker θ) (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ c : Fin d → B, (∀ i, algebraMap B Q (c i) = (p : Q) * coeff (Finsupp.single i p) l) → ∀ u : Fin d → B, constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p ∈ RingHom.ker θ ⊔ Ideal.span {(p : B)} := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL l j hQL hcob hlin c hc u
  classical
  have hp : p.Prime := Fact.out
  have hμ := hL.const
  have hμQ : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ,
      map_zero]
  obtain ⟨b, hbN, hb⟩ := GlobalTheory.T.constantCoeff_iterate_invariantDerivation_mem B Q d μ hμ (RingHom.ker θ) l j hcob hlin u p hp.two_le
  have h3 := _root_.GlobalTheory.QLogInt.coeff_integral_of_QL p B O Q θ hF d μ hL l hQL
  let P : (Fin d →₀ ℕ) → Prop := fun α => α.degree ≤ p ∧ ∀ i, α ≠ Finsupp.single i p
  let h : (Fin d →₀ ℕ) → B := fun α => if hα : P α then (h3 α hα.1 hα.2).choose else 0
  have hh : ∀ α, P α → algebraMap B Q (h α) = coeff α l := fun α hα => by
    simp only [h, dif_pos hα]; exact (h3 α hα.1 hα.2).choose_spec.symm
  let H : MvPowerSeries (Fin d) B := fun α => h α
  have hH : ∀ α, coeff α H = h α := fun α => rfl
  let q : Fin d → Q := fun i => coeff (Finsupp.single i p) l
  have hinj : ∀ i k : Fin d, Finsupp.single i p = Finsupp.single k p ↔ i = k := fun i k =>
    Finsupp.single_left_inj hp.ne_zero
  let G : MvPowerSeries (Fin d) Q :=
    map (algebraMap B Q) H + ∑ i, q i • monomial (Finsupp.single i p) (1 : Q)
  have hG : ∀ α : Fin d →₀ ℕ, α.degree ≤ p → coeff α l = coeff α G := by
    intro α hα
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, map_add (f := _), coeff_map, hH, map_sum, map_smul, coeff_monomial, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    by_cases hP : ∀ i, α ≠ Finsupp.single i p
    · rw [hh α ⟨hα, hP⟩, Finset.sum_eq_zero (fun i _ => if_neg (hP i)), add_zero]
    · push_neg at hP
      obtain ⟨i, rfl⟩ := hP
      have : h (Finsupp.single i p) = 0 := dif_neg fun hα => hα.2 i rfl
      rw [this, map_zero, zero_add, Finset.sum_eq_single i (fun k _ hk => if_neg fun e =>
        hk ((hinj i k).1 e).symm) (by simp), if_pos rfl]

  have hnat : ∀ F : MvPowerSeries (Fin d) B,
      constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[p] (map (algebraMap B Q) F)) =
        algebraMap B Q (constantCoeff ((invDer μ u)^[p] F)) := fun F => by
    rw [← constantCoeff_map, _root_.GlobalTheory.LawDer.map_invDer_iterate B Q (algebraMap B Q) d μ hμ u p F]; rfl
  have hmon : ∀ i : Fin d, monomial (Finsupp.single i p) (1 : Q) =
      map (algebraMap B Q) (monomial (Finsupp.single i p) (1 : B)) := fun i => by
    rw [map_monomial, (algebraMap B Q).map_one]
  have hmono : ∀ i : Fin d, constantCoeff ((invDer μ u)^[p] (monomial (Finsupp.single i p) (1 : B))) =
      (p.factorial : B) * u i ^ p := fun i => by
    have := _root_.GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial B d μ hμ hL.unit hL.comm u (Finsupp.single i p)
    rw [Finsupp.degree_single] at this
    rw [this, Finset.prod_eq_single i (fun k _ hk => by rw [Finsupp.single_apply, if_neg (Ne.symm hk),
      pow_zero]) (by simp), Finsupp.single_eq_same]
  have e1 := _root_.GlobalTheory.LawDer.IterateLocal.constantCoeff_iterate_invDer_congr Q d (up Q μ) hμQ (fun i => algebraMap B Q (u i)) p l G hG
  have e2 : constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[p] G) =
      algebraMap B Q (constantCoeff ((invDer μ u)^[p] H)) +
        ∑ i, q i * algebraMap B Q ((p.factorial : B) * u i ^ p) := by
    rw [← iterLin_apply hμQ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, map_add (f := _), map_sum, map_smul, iterLin_apply, hmon, hnat]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul, map_mul, constantCoeff_C, hnat, hmono]
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear p B d μ hμ hL.unit hL.comm u H
  have hlin1 : ∀ k, coeff (Finsupp.single k 1) H = if k = j then 1 else 0 := fun k => by
    apply hF.inj
    have hPk : P (Finsupp.single k 1) := ⟨by rw [Finsupp.degree_single]; exact hp.one_le, fun i e => by
      rcases (Finsupp.single_eq_single_iff _ _ _ _).1 e with ⟨_, h1⟩ | ⟨h1, _⟩
      · exact hp.one_lt.ne h1
      · exact one_ne_zero h1⟩
    rw [hH, hh _ hPk]
    have := congrFun hlin k
    simp only [lin] at this
    rw [this, Pi.single_apply]
    split_ifs <;> simp
  have hsumX : ∑ k, constantCoeff ((invDer μ u)^[p] (X k)) * coeff (Finsupp.single k 1) H =
      constantCoeff ((invDer μ u)^[p] (X j)) := by
    simp [hlin1]
  rw [hsumX] at hr
  have key : b = constantCoeff ((invDer μ u)^[p] H) + ((p - 1).factorial : B) * ∑ i, c i * u i ^ p := by
    apply hF.inj
    rw [← hb, e1, e2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_mul, map_sum, map_pow, map_natCast]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc, ← Nat.mul_factorial_pred hp.ne_zero]
    push_cast
    ring
  obtain ⟨m, hm⟩ : p ∣ (p - 1).factorial + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  have hmB : ((p - 1).factorial : B) = p * m - 1 := by
    have := congrArg (Nat.cast : ℕ → B) hm
    push_cast at this
    linear_combination this
  have eq : constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p =
      b - p * (r + m * ∑ i, c i * u i ^ p) := by
    rw [key, hmB]
    linear_combination -hr
  rw [eq]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hbN)
    (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 ⟨_, rfl⟩))

end GlobalTheory.FrobIter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityBaseChangeAffineCofilteredLimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuity_baseChange_affine_cofiltered_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S), IsAffine W → ContCone R F ((bc (sch.map r)).mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_bc_affine
  | exact GlobalTheory.EtC.contCone_bc_affine
  | (intros; apply GlobalTheory.EtC.contCone_bc_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityCofilteredLimitRepresentedAffineStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuity_cofiltered_limit_represented_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  first
  | exact @GlobalTheory.contCone_of_represented
  | exact GlobalTheory.contCone_of_represented
  | (intros; apply GlobalTheory.contCone_of_represented <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijectiveStatement
section
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_H2_small_cover_bijective : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull2 := by
  first | exact @GlobalTheory.Cris.small_descent_H2_bijective | exact GlobalTheory.Cris.small_descent_H2_bijective | (intros; apply GlobalTheory.Cris.small_descent_H2_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallinePeriodEqCechDeRhamPeriodStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_period_eq_cechDeRham_period : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : FirstDeRham (str A)) (q : u.Λ →+ ℂ) (per : u.Λ →+ Hol (fibFam u).V), (∀ l, per l = algebraMap ℂ _ (q l)) → IsPeriod (fibUnif u) c per → IsPer u.ex u.Λ (cmp1 (str A) c) q := by
  first | exact @GlobalTheory.PerLink.main | exact GlobalTheory.PerLink.main | (intros; apply GlobalTheory.PerLink.main <;> assumption)
end

