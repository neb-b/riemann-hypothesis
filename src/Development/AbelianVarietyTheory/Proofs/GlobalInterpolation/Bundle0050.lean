module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0043
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.UnitaryThreeIrreduciblePoints
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.GradedCompletionLemmas
public import ReciprocityTheory.GaloisValuations.ArithOfA
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaAndWindowCount
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZeroBounds

theorem explicit_formula_and_window_count :
    (∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm7 D C) ∧ ∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm11 D C := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C', hC', h'⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  exact ⟨⟨C, hC, fun _ => h⟩, ⟨C', hC', fun _ => h'⟩⟩

end GlobalTheory.ZeroBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralPowerExpansion
section
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.Proof.IntegralPowerExpansion

open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram depthSub)

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  · intro h
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer a h
    exact ⟨n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem val_q {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) :
    P.valuation E (qOf P : E) = WithZero.exp (-1) := by
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  rw [e, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 : P.intValuation (qOf P : 𝓞 E) < 1 :=
    (P.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have h2 : ¬ P.intValuation (qOf P : 𝓞 E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact hP.2
  have hx : P.intValuation (qOf P : 𝓞 E) ≠ 0 := by
    intro h0
    exact h2 (h0 ▸ zero_le)
  rw [← WithZero.exp_log hx] at h1 h2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  rw [WithZero.exp_le_exp] at h2
  congr 1
  omega

theorem q_ne_zero {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) : (qOf P : E) ≠ 0 :=
  Nat.cast_ne_zero.2 hP.1.ne_zero

theorem exists_int_add_q_mul {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) {u : E} (hu : IntAt P u) :
    ∃ (k : ℤ) (u' : E), IntAt P u' ∧ u = k + (qOf P : E) * u' := by
  obtain ⟨r, s, hs, h⟩ := hu
  haveI : Fact (qOf P).Prime := ⟨hP.1⟩
  have hc : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
    rw [qOf, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1
    (mem_zmultiples_of_prime_card (g' := Ideal.Quotient.mk P.asIdeal r) hc (mk_ne_zero hs))
  have hm : r - k * s ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_intCast, ← hk, zsmul_eq_mul, sub_self]
  have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hs
  have h2 : algebraMap (𝓞 E) E s * (u - k) = algebraMap (𝓞 E) E (r - k * s) := by
    rw [map_sub, map_mul, map_intCast, ← h]; ring
  have h3 : P.valuation E (u - k) < 1 := by
    have := congrArg (P.valuation E) h2
    rw [map_mul, h1, one_mul, HeightOneSpectrum.valuation_of_algebraMap] at this
    rw [this]
    exact (P.intValuation_lt_one_iff_mem _).2 hm
  have hq := q_ne_zero hP
  refine ⟨k, (u - k) / qOf P, ?_, by field_simp; ring⟩
  rw [intAt_iff_val, map_div₀, val_q hP]
  exact div_le_one_of_le₀ (le_exp_neg_one_of_lt_one h3) zero_le

theorem exists_int_add_q_pow_mul {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) (j : ℕ) {u : E}
    (hu : IntAt P u) : ∃ (k : ℤ) (u' : E), IntAt P u' ∧ u = k + (qOf P : E) ^ j * u' := by
  induction j with
  | zero => exact ⟨0, u, hu, by simp⟩
  | succ j ih =>
    obtain ⟨k, u', hu', e⟩ := ih
    obtain ⟨k', u'', hu'', e'⟩ := exists_int_add_q_mul hP hu'
    refine ⟨k + (qOf P : ℤ) ^ j * k', u'', hu'', ?_⟩
    rw [e, e']
    push_cast
    ring

end GlobalTheory.Proof.IntegralPowerExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemIneSmulIff
section
open NumberField IsDedekindDomain Pointwise

namespace GlobalTheory.PlaceConjQ

theorem eq_of_prime_mem {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have : Fact q.Prime := ⟨hq⟩
  have := v.isPrime
  have := w.isPrime
  have h1 := ((ReciprocityTheory.Gal.liesOver_span_iff q v.asIdeal).2 hv).over
  have h2 := ((ReciprocityTheory.Gal.liesOver_span_iff q w.asIdeal).2 hw).over
  apply HeightOneSpectrum.ext
  ext x
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  have e : Rat.ringOfIntegersEquiv.symm n = algebraMap ℤ (𝓞 ℚ) n :=
    (eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n).trans (eq_intCast (algebraMap ℤ (𝓞 ℚ)) n).symm
  rw [e, ← Ideal.mem_comap, ← Ideal.mem_comap]
  change n ∈ v.asIdeal.under ℤ ↔ n ∈ w.asIdeal.under ℤ
  rw [← h1, ← h2]

end GlobalTheory.PlaceConjQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Proof.NormalFormAtPrime

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Arith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem degOne_of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) (hv : DegOne v)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) : DegOne P := by
  have key : ∀ Q Q' : HeightOneSpectrum (𝓞 E), Q ≠ Q' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal → Q.asIdeal.under (𝓞 F) = v.asIdeal → DegOne Q := by
    intro Q Q' hne hm hQ
    have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← map_mul, ← hm, Ideal.absNorm_algebraMap, ← h2]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm
    have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h1' : Ideal.absNorm Q'.asIdeal ≠ 1 := fun h => Q'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have hq : Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal :=
      (((Nat.Prime.mul_eq_prime_sq_iff hv.1 h1 h1').1 hN).1)
    refine ⟨hq ▸ hv.1, ?_⟩
    rw [hq]
    intro hmem
    have hqv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
    obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} :=
      Ideal.dvd_span_singleton.2 hqv
    have hd : Q.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)}) := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
      exact Ideal.dvd_span_singleton.2 hmem
    rw [hI, Ideal.map_mul, hm, pow_two, mul_assoc, mul_dvd_mul_iff_left Q.ne_bot] at hd
    rcases (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).dvd_or_dvd hd with h | h
    · exact hne (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
    · have hle : I ≤ v.asIdeal := by
        rw [← hQ]
        exact Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
      apply hv.2
      rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]
      exact Ideal.mul_mono_right hle
  obtain ⟨Q, Q', hne, hm⟩ := hs
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, ← hP]
    exact Ideal.map_comap_le
  rcases P.isPrime.mul_le.1 hle with h | h
  · obtain rfl : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
    exact key _ _ hne hm hP
  · obtain rfl : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
    exact key _ _ hne.symm (by rw [hm, mul_comm]) hP

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this

theorem intAt_pow_mul {P : HeightOneSpectrum (𝓞 E)} (k : ℕ) {a : E} (ha : IntAt P a) : IntAt P ((qOf P : E) ^ k * a) := by
  refine IntAt.mul ?_ ha
  simpa using IntAt.coe P ((qOf P : 𝓞 E) ^ k)

theorem intAt_pow_mono {P : HeightOneSpectrum (𝓞 E)} {A A' : ℕ} (h : A ≤ A') {a : E} (ha : IntAt P ((qOf P : E) ^ A * a)) :
    IntAt P ((qOf P : E) ^ A' * a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := intAt_pow_mul k ha
  rwa [← mul_assoc, ← pow_add, add_comm] at this

end Arith

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem sameDC_refl (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : SameDC (Pr := Pr) sharp j P h h :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem sameDC_trans {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h₁ h₂ : AutY X R j}
    (a : SameDC (Pr := Pr) sharp j P h h₁) (b : SameDC (Pr := Pr) sharp j P h₁ h₂) : SameDC (Pr := Pr) sharp j P h h₂ := by
  obtain ⟨r, hr, k, hk, rfl⟩ := a
  obtain ⟨r', hr', k', hk', rfl⟩ := b
  exact ⟨r' * r, mul_mem hr' hr, k * k', mul_mem hk hk', by simp only [mul_assoc]⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

def TwistDegOne (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) : Prop :=
  ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → DegOne P.1

theorem twistDegOne_of_isSel (h2 : Module.finrank X.F X.E = 2) (hsel : IsSel X sel) : TwistDegOne Pr sel mu := by
  classical
  rintro ⟨P, hP⟩ hn
  have hQ : P ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.1 hP).resolve_left hn
  unfold QE at hQ
  split_ifs at hQ with hf
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ
    have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := hf.mem_toFinset.1 hv
    have hg : GoodPl X.E S v := by
      by_contra hg
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 mu.2.2 v)) hg
      exact hv' this
    exact degOne_of_split h2 hg.1 hg.2.1 (hsel v)
  · simp at hQ

variable {Ch sel mu}

variable (Ch sel mu)

end GlobalTheory.Proof.NormalFormAtPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReLtOneOfZero
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroDensityMult

theorem re_lt_one_of_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h : LFunction χ ρ = 0) : ρ.re < 1 := by
  by_contra hc
  push Not at hc
  by_cases h1 : χ = 1
  · have hN : N = 1 := by
      have h := hχ
      rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    rw [LFunction_modOne_eq] at h
    exact riemannZeta_ne_zero_of_one_le_re hc h
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl h1) hc h

theorem log_le {Q N t : ℝ} (hQ : 3 ≤ Q) (hN0 : 0 < N) (hN : N ≤ Q) (ht : |t| ≤ Q + 1) :
    Real.log (N * (|t| + 2)) ≤ 24 * Q ^ ((1 : ℝ) / 8) := by
  have h0 := abs_nonneg t
  have h1 : N * (|t| + 2) ≤ Q ^ 3 := by
    have : N * (|t| + 2) ≤ Q * (Q + 3) := mul_le_mul hN (by linarith) (by linarith) (by linarith)
    have h4 : Q + 3 ≤ Q ^ 2 := by nlinarith
    have h5 : Q * (Q + 3) ≤ Q * Q ^ 2 := mul_le_mul_of_nonneg_left h4 (by linarith)
    have h6 : Q * Q ^ 2 = Q ^ 3 := by ring
    linarith
  have h2 : Real.log (N * (|t| + 2)) ≤ Real.log (Q ^ 3) := Real.log_le_log (by positivity) h1
  have h3 := Real.log_le_rpow_div (x := Q) (ε := (1 : ℝ) / 8) (by linarith) (by norm_num)
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

theorem zero_density_mult : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((∑ p ∈ T, analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 4) := by
  classical
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  obtain ⟨C₂, hC₂, H₂⟩ := _root_.GlobalTheory.ZeroCells.ncard_cells_le
  refine ⟨C₂ * (C₁ * 24), by positivity, ?_⟩
  intro Q hQ T hT
  have hQ0 : 0 < Q := by linarith
  have hcard := H₂ Q hQ T hT
  set g : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) → (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) :=
    fun p => ⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ with hg
  rw [← Finset.coe_image, Set.ncard_coe_finset] at hcard
  push_cast
  rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image g) (g := g)
    (fun p hp => Finset.mem_image_of_mem g hp)]
  have hcell : ∀ c ∈ T.image g, ∑ p ∈ T with g p = c,
      ((analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C₁ * (24 * Q ^ ((1 : ℝ) / 8)) := by
    intro c hc
    obtain ⟨⟨n, χ, z⟩, hz, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨a1, a2, -, -, a5⟩ := hT _ hz
    simp only at a1 a2 a5
    obtain ⟨hfin, hsum⟩ := H₁ (n + 1) χ a2 (⌊z.im⌋ : ℤ)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    have hl : Real.log (((n + 1 : ℕ) : ℝ) * (|((⌊z.im⌋ : ℤ) : ℝ)| + 2)) ≤ 24 * Q ^ ((1 : ℝ) / 8) := by
      refine log_le hQ (by positivity) a1 ?_
      have b1 := Int.floor_le z.im
      have b2 := Int.lt_floor_add_one z.im
      rw [abs_le] at a5 ⊢
      constructor <;> linarith [a5.1, a5.2]
    refine le_trans ?_ (hsum.trans (mul_le_mul_of_nonneg_left hl hC₁.le))
    have hinj : Function.Injective
        (fun ρ : ℂ => (⟨n, χ, ρ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) := by
      intro x y h
      simpa using h
    have e := Finset.sum_image (s := hfin.toFinset)
      (g := fun ρ : ℂ => (⟨n, χ, ρ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))
      (f := fun p => ((analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ)) hinj.injOn
    refine le_trans ?_ e.le
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
    rintro ⟨m, ψ, ρ⟩ hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp, hgp⟩ := hp
    obtain ⟨-, b2, b3, b4, -⟩ := hT _ hp
    simp only [hg] at hgp b2 b3 b4
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 hgp
    have h3 := eq_of_heq h2
    obtain ⟨rfl, h4⟩ := Prod.mk.inj h3
    refine Finset.mem_image.2 ⟨ρ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨by linarith, re_lt_one_of_zero _ b2 b3, ?_, b3⟩
    have c1 := Int.floor_le ρ.im
    have c2 := Int.lt_floor_add_one ρ.im
    rw [← h4, abs_le]
    constructor <;> linarith
  refine (Finset.sum_le_card_nsmul _ _ _ hcell).trans ?_
  rw [nsmul_eq_mul]
  have hp : Q ^ ((1 : ℝ) / 4) = Q ^ ((1 : ℝ) / 8) * Q ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hQ0]; norm_num
  rw [hp]
  calc _ ≤ (C₂ * Q ^ ((1 : ℝ) / 8)) * (C₁ * (24 * Q ^ ((1 : ℝ) / 8))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end GlobalTheory.ZeroDensityMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ToLinNfMatEqSumNfGen
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.QNF

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

theorem toLin'_nfMat_eq_sum_nfGen {E : Type} [Field E] [NumberField E] [StarRing E] (q n c : ℕ) (e : Fin c → ℤ) (z : Fin n → E)
    (y : Fin (n + c) → E) :
    Matrix.toLin' (nfMat n c (q : E) e z) y =
      Loc.inX E n c (fun a => y (Fin.castAdd c a)) + ∑ i, y (Fin.natAdd n i) • nfGen q n c e z i := by
  funext p
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Pi.add_apply, Finset.sum_apply]
  congr 1
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · simp [nfMat, Loc.inX]
    · have : ∀ a : Fin n, Fin.natAdd n b ≠ Fin.castAdd c a := fun a h => by
        have := congrArg Fin.val h
        simp at this; omega
      simp [nfMat, Loc.inX, this]
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · have h1 : Fin.castAdd c a ≠ Fin.natAdd n i := fun h => by
        have := congrArg Fin.val h
        simp at this; omega
      have h2 : ¬ (a.1 = n + i.1) := by omega
      by_cases hi : i.1 = 0
      · have h0 : ∀ h, (⟨0, h⟩ : Fin c) = i := fun h => Fin.ext hi.symm
        have h3 : ¬ (a.1 = n) := by omega
        simp [nfMat, nfGen, Loc.inX, Loc.eN, h1, h3, hi, h0]
        ring
      · simp [nfMat, nfGen, Loc.eN, h1, h2, hi]
    · by_cases hb : b = i
      · subst hb
        simp [nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, mul_comm]
      · have : ¬ (b.1 = i.1) := fun h => hb (Fin.ext h)
        simp [nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, hb, this]

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem image_lamYat_nfMat {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (e : Fin (cOf R j) → ℤ)
    (z : Fin (R.N j) → X.E) :
    (Matrix.toLin' (nfMat (R.N j) (cOf R j) ((qOf P : ℕ) : X.E) e z)) ''
        (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = nfLat P (R.N j) (cOf R j) e z := by
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, mem_lamYat hP, nfLat, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun a => x (Fin.castAdd _ a), (mem_localization_standardLattice _ _).2 fun a => hx _, fun b => x (Fin.natAdd _ b),
      fun b => hx _, toLin'_nfMat_eq_sum_nfGen _ _ _ _ _ _⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    refine ⟨Fin.addCases (motive := fun _ => X.E) l s, fun p => ?_, ?_⟩
    · refine Fin.addCases (fun a => ?_) (fun b => ?_) p
      · simpa using (mem_localization_standardLattice _ _).1 hl a
      · simpa using hs b
    · rw [toLin'_nfMat_eq_sum_nfGen]
      simp

theorem pad_mem_lamYat_iff {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (z : Fin (R.N j) → X.E) :
    (fun l : Fin (R.N j + cOf R j) => if h : l.1 < R.N j then z ⟨l.1, h⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P ↔
      z ∈ stdAt X.E (R.N j) P := by
  rw [mem_lamYat hP]
  constructor
  · intro h
    refine (mem_localization_standardLattice _ _).2 fun a => ?_
    simpa using h (Fin.castAdd _ a)
  · intro h l
    by_cases hl : l.1 < R.N j
    · simpa [hl] using (mem_localization_standardLattice _ _).1 h ⟨l.1, hl⟩
    · simpa [hl] using (mem_lamYat (R := R) (j := j) hP 0).1 (zero_mem _) l

theorem nf_iff_matNF : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs →
    ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h ↔ GlobalTheory.QNF.MatNF Pr R j P h := by
  intro X Pr R j P hP h
  unfold NF MatNF
  refine exists_congr fun e => exists_congr fun z => and_congr_right fun _ => and_congr (pad_mem_lamYat_iff hP z).symm ?_
  rw [← image_lamYat_nfMat hP]
  refine Iff.trans ?_ SetLike.ext'_iff.symm
  rw [Submodule.map_coe, Submodule.map_coe]
  rfl

end GlobalTheory.QNF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylHighestWeightStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceRowOperatorPower_dualWeyl_highestWeight : ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ k : ℕ, ∀ f ∈ dualWeyl ℚ N N ν, gel ℚ N N k f = hcVal ℚ (fun i => (ν i : ℚ)) k • f := by
  first | exact @GlobalTheory.Alc.gel_dualWeyl_rat | exact GlobalTheory.Alc.gel_dualWeyl_rat | (intros; apply GlobalTheory.Alc.gel_dualWeyl_rat <;> assumption)
end

