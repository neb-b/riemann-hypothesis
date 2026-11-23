module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FinitePrimesSumSquaresZero
section
namespace GlobalTheory.CompanionTheory.QuadFin

theorem exists_eq_add_mul_of_mem_adjoin {E : Type*} [Field E] [Algebra ℚ E] (x : E) (c : ℚ)
    (hx : x ^ 2 = algebraMap ℚ E c) {y : E} (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℚ, y = algebraMap ℚ E a + algebraMap ℚ E b * x := by
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hx]⟩
  have hy' : y ∈ Algebra.adjoin ℚ {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  refine Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun u v _ _ hu hv => ?_)
    (fun u v _ _ hu hv => ?_) hy'
  · exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hz]; simp⟩
  · exact ⟨r, 0, by simp⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    exact ⟨a + a', b + b', by simp only [map_add (f := _)]; ring⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    refine ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
    simp only [map_add (f := _), map_mul]
    linear_combination (algebraMap ℚ E b * algebraMap ℚ E b') * hx

theorem not_sq_eq_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (b : ℚ)
    (h : (p : ℚ) = q * b ^ 2) : False := by
  haveI := Fact.mk hq
  have hb : b ≠ 0 := by
    rintro rfl
    have h0 : (p : ℚ) = 0 := by rw [h]; ring
    exact hp.ne_zero (by exact_mod_cast h0)
  have h1 := congrArg (padicValRat q) h
  rw [padicValRat.mul (by exact_mod_cast hq.ne_zero) (pow_ne_zero 2 hb), padicValRat.pow b,
    padicValRat.self hq.one_lt, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd] at h1
  · push_cast at h1
    omega
  · intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm

theorem false_of_sq_eq {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (x : E) (hx : x ^ 2 = -(q : E)) (a b : ℚ)
    (h : (algebraMap ℚ E a + algebraMap ℚ E b * x) ^ 2 = -(p : E)) : False := by
  have hφ : Function.Injective (algebraMap ℚ E) := (algebraMap ℚ E).injective
  have key : algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) + algebraMap ℚ E (2 * a * b) * x = 0 := by
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    linear_combination h - algebraMap ℚ E b ^ 2 * hx
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  by_cases hab : 2 * a * b = 0
  · rw [hab, map_zero, zero_mul, add_zero, map_eq_zero_iff _ hφ] at key
    rcases mul_eq_zero.mp hab with h2a | hb
    · have ha : a = 0 := by linarith
      subst ha
      exact not_sq_eq_of_prime hp hq hpq b (by linear_combination key)
    · subst hb
      nlinarith [sq_nonneg a]
  · have hne : algebraMap ℚ E (2 * a * b) ≠ 0 := (map_ne_zero _).mpr hab
    have hx' : x = -algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) / algebraMap ℚ E (2 * a * b) :=
      eq_div_of_mul_eq hne (by linear_combination key)
    rw [← map_neg, ← map_div₀] at hx'
    rw [hx', ← map_pow, show -(q : E) = algebraMap ℚ E (-(q : ℚ)) by rw [map_neg, map_natCast]] at hx
    have h2 := hφ hx
    nlinarith [sq_nonneg (-(a ^ 2 - q * b ^ 2 + p) / (2 * a * b))]

theorem finite_primes_of_finiteDimensional (E : Type*) [Field E] [CharZero E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)}.Finite := by
  classical
  haveI : Finite (IntermediateField ℚ E) :=
    (Field.exists_primitive_element_iff_finite_intermediateField ℚ E).mp
      ⟨inferInstance, Field.exists_primitive_element ℚ E⟩
  have key : ∀ p q : ℕ, p.Prime → q.Prime → ∀ x y : E, x ^ 2 = -(p : E) → y ^ 2 = -(q : E) →
      IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {y} → p = q := by
    intro p q hp hq x y hx hy he
    by_contra hpq
    have hmem : x ∈ IntermediateField.adjoin ℚ {y} := by
      rw [← he]
      exact IntermediateField.mem_adjoin_simple_self ℚ x
    obtain ⟨a, b, hab⟩ :=
      exists_eq_add_mul_of_mem_adjoin y (-(q : ℚ)) (by rw [hy, map_neg, map_natCast]) hmem
    exact false_of_sq_eq hp hq hpq y hy a b (by rw [← hab]; exact hx)
  have hinj : Function.Injective (fun p : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)} =>
      IntermediateField.adjoin ℚ {Classical.choose p.2.2}) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ he
    exact Subtype.ext (key p q hp.1 hq.1 _ _ (Classical.choose_spec hp.2) (Classical.choose_spec hq.2) he)
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

theorem finite_primes_field (F : Type*) [Field F] [CharZero F] [Algebra ℚ F]
    [Algebra.EssFiniteType ℚ F] : {p : ℕ | p.Prime ∧ ∃ x : F, x ^ 2 = -(p : F)}.Finite := by
  have hfd := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType ℚ F
  refine (@finite_primes_of_finiteDimensional (algebraicClosure ℚ F) _ _ (algebraicClosure ℚ F).algebra' hfd).subset ?_
  rintro p ⟨hp, x, hx⟩
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C (-(p : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hx]⟩
  have hmem : x ∈ algebraicClosure ℚ F := mem_algebraicClosure_iff'.mpr hint
  exact ⟨hp, ⟨x, hmem⟩, Subtype.ext (by simp [hx])⟩

theorem finite_primes_of_isFractionRing (A F : Type*) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] [Field F] [Algebra A F] [IsFractionRing A F] :
    {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective A F)
  haveI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ A F
  haveI : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_comp ℤ ℚ F
  refine (finite_primes_field F).subset ?_
  rintro p ⟨hp, a, b, hb, hab⟩
  have hb' : algebraMap A F b ≠ 0 := fun h0 =>
    hb (IsFractionRing.injective A F (by rw [h0, map_zero]))
  refine ⟨hp, algebraMap A F a / algebraMap A F b, ?_⟩
  have e := congrArg (algebraMap A F) hab
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_zero] at e
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hb')]
  linear_combination e

theorem finite_primes_neg_sq : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  intro σ _ A _ _ _ f hf
  haveI : Algebra.FiniteType ℤ A := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
    refine Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr
      ⟨n, MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i))), ?_⟩
    have hcomp : ((MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i)))).toRingHom).comp
        (MvPolynomial.rename (R := ℤ) e).toRingHom = f := by
      apply MvPolynomial.ringHom_ext'
      · exact RingHom.ext_int _ _
      · intro s
        simp
    intro a
    obtain ⟨p, rfl⟩ := hf a
    exact ⟨MvPolynomial.rename (R := ℤ) e p, RingHom.congr_fun hcomp p⟩
  exact finite_primes_of_isFractionRing A (FractionRing A)

end GlobalTheory.CompanionTheory.QuadFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCell
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (z : Pairs N → ℂ) :
    gramLog hd m (cellMat N z) = logDetFlag N hd m hm z := by
  let e : Fin m ≃ {a : Fin N // (a : ℕ) < m} :=
    { toFun := fun i => ⟨Fin.castLE hm i, i.2⟩, invFun := fun a => ⟨a.1, a.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hdet : (gramHead hd m (cellMat N z)).det =
      (((cellMat N z)ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N z).submatrix
        (Fin.castLE hm) (Fin.castLE hm)).det := by
    rw [← Matrix.det_submatrix_equiv_self e (gramHead hd m (cellMat N z))]
    rfl
  delta GlobalTheory.CompanionTheory.Ar.PB.gramLog ReciprocityTheory.AnForm.P.logDetFlag
  rw [hdet]

theorem contDiffAt_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N) :
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 := by
  have hE : logDetFlag N hd m hm = fun z => 1 / 2 * Real.log |detGram N hd m hm z| :=
    logDetFlag_eq N hd m hm
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) =
      fun z => 1 / 2 * Real.log (detGram N hd m hm z) := by
    funext z
    rw [gramLog_cellMat N hd m hm z, hE]
    simp only [Real.log_abs]
  rw [hf]
  obtain ⟨hC, h0, -⟩ := detGram_deriv N hd m hm
  have hne : detGram N hd m hm 0 ≠ 0 := by
    rw [h0]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hd0 _
  exact contDiffAt_const.mul (hC.contDiffAt.log hne)

theorem levi_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N)
    (w : Pairs N → ℂ) :
    levi (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        hd p.1.2 / (2 * hd p.1.1) * ‖w p‖ ^ 2 else 0 := by
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) = logDetFlag N hd m hm := by
    funext z
    exact gramLog_cellMat N hd m hm z
  rw [hf]
  exact homDensity N hd hd0 m hm w

theorem sigForm_ne_zero (N j : ℕ) (k : Fin N) : sigForm N j k ≠ 0 := by
  delta GlobalTheory.CompanionTheory.Ar.PB.sigForm
  split_ifs <;> norm_num

theorem levi_stepPot_cell : ∀ (N j : ℕ), j ≤ N → ∀ (i : Fin N) (w : Pairs N → ℂ),
    let r : Fin N → ℕ := fun a => if (a : ℕ) < N - j then j + a else a - (N - j)
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 ∧
      levi (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 w =
        ∑ p : Pairs N, if min (r p.1.1) (r p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (r p.1.1) (r p.1.2)
          then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  intro N j hj i w
  dsimp only
  have hs := sigForm_ne_zero N j
  have hσ : ∀ k : Fin N, sigForm N j k = if (k : ℕ) < N - j then -1 else 1 := fun k => rfl
  have G : ∀ m, m ≤ N →
      ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 :=
    fun m hm => contDiffAt_gramLog_cellMat N (sigForm N j) hs m hm
  have Lv : ∀ m, m ≤ N → levi (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        sigForm N j p.1.2 / (2 * sigForm N j p.1.1) * ‖w p‖ ^ 2 else 0 :=
    fun m hm => levi_gramLog_cellMat N (sigForm N j) hs m hm w
  have hi := i.2
  by_cases hij : (i : ℕ) + 1 ≤ j
  · have h1 : N - j + ((i : ℕ) + 1) ≤ N := by omega
    have h0 : N - j ≤ N := by omega
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z) +
          (-1) * gramLog (sigForm N j) (N - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_pos hij]
      ring
    rw [hfun]
    refine ⟨(G _ h1).add (contDiffAt_const.mul (G _ h0)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ h1) (G _ h0) w).trans ?_
    rw [Lv _ h1, Lv _ h0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring
  · have h1 : N - j ≤ N := by omega
    have h2 : (i : ℕ) + 1 - j ≤ N := by omega
    have hN : N ≤ N := le_refl N
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        (gramLog (sigForm N j) N (cellMat N z) + (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) +
          1 * gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_neg hij]
      ring
    have GA : ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) 0 :=
      (G _ hN).add (contDiffAt_const.mul (G _ h1))
    rw [hfun]
    refine ⟨GA.add (contDiffAt_const.mul (G _ h2)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z)) 1 GA (G _ h2) w).trans ?_
    rw [levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ hN) (G _ h1) w]
    rw [Lv _ hN, Lv _ h1, Lv _ h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem log_inv_bounds {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    Real.exp 1 ≤ Real.log (1 / t) ∧ 1 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : Real.exp 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  refine ⟨h1, ?_⟩
  have := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at this

theorem loglog_quot_nonneg {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  obtain ⟨h1, h2⟩ := log_inv_bounds ht hte
  exact div_nonneg (by linarith) (by linarith [Real.exp_pos 1])

theorem epsT_eq_mul (C t : ℝ) :
    epsT C t = C * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) := by
  rw [epsT, mul_div_assoc]

theorem epsT_le_epsT {C C' t : ℝ} (hC : C ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : epsT C t ≤ epsT C' t := by
  rw [epsT_eq_mul, epsT_eq_mul]
  exact mul_le_mul_of_nonneg_right hC (loglog_quot_nonneg ht hte)

theorem mul_epsT_le {C C' t : ℝ} (hC : |C| ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : C * epsT C t ≤ C' * epsT C' t := by
  have hx := loglog_quot_nonneg ht hte
  rw [epsT_eq_mul, epsT_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  have h2 : C ^ 2 ≤ C' ^ 2 := by
    rw [← sq_abs C]
    exact pow_le_pow_left₀ (abs_nonneg C) hC 2
  nlinarith

theorem isPsh_rsmul_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) {ε ε' : ℝ} (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (hε : ε ≤ ε')
    (h : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) :
    IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε') := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hU : (A.chart j).symm y ∈ (th.U x ∩ Set.univ) ∩ Θ.U x := hyU
  have hO1 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' th.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (th.isOpen_U x)
  have hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)
  have hO3 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Set.univ : Set X)) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target isOpen_univ
  have hth2 : ContDiffAt ℝ 2 (th.φ x ∘ (A.chart j).symm) y :=
    ((hth.1 x j).contDiffAt (hO1.mem_nhds ⟨hyt, hU.1.1⟩)).of_le (by norm_cast)
  have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
    ((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)
  have hu2 : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
    ((hu j).contDiffAt (hO3.mem_nhds ⟨hyt, Set.mem_univ _⟩)).of_le (by norm_cast)
  have hP2 : ContDiffAt ℝ 2
      ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y :=
    (hth2.add hu2).add (contDiffAt_const.mul hΘ2)
  have hfun : (th + LocPot.ofFun u + Θ.rsmul ε').φ x ∘ (A.chart j).symm =
      fun z => ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) z +
        (ε' - ε) * (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show th.φ x _ + u _ + ε' * Θ.φ x _ = th.φ x _ + u _ + ε * Θ.φ x _ + (ε' - ε) * Θ.φ x _
    ring
  rw [hfun, levi_add_smul (ε' - ε) hP2 hΘ2 w]
  exact add_nonneg (h x j y ⟨hyt, hyU⟩ w)
    (mul_nonneg (sub_nonneg.2 hε) (hΘp x j y ⟨hyt, hU.2⟩ w))

theorem isRegFamily_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ)
    (C t₀ C' t₁ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hth : IsPotential A th)
    (hs : ∀ y, logNormSec L s y ≤ 0) (hF : IsRegFamily A Θ L s th ph phT C t₀)
    (hC : |C| ≤ C') (ht₁ : 0 < t₁) (ht₁₀ : t₁ ≤ t₀) (hte : t₁ ≤ Real.exp (-Real.exp 1)) :
    IsRegFamily A Θ L s th ph phT C' t₁ := by
  obtain ⟨-, ht₀1, hF⟩ := hF
  have hCC : C ≤ C' := (le_abs_self C).trans hC
  have hr : ∀ y, 0 ≤ rW L s y := fun y => by
    have := hs y
    have := Real.exp_pos 1
    unfold rW
    linarith
  refine ⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF t ht (htt.trans ht₁₀)
  have hte' : t ≤ Real.exp (-Real.exp 1) := htt.trans hte
  have hε := epsT_le_epsT hCC ht hte'
  have hll := (log_inv_bounds ht hte').2
  refine ⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_,
    isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_, fun y hy => ?_,
    fun t' htt' ht' y => ?_⟩
  · have := h4 y
    nlinarith
  · have := h6 y hy hyr
    linarith
  · have := h7 y hy
    have := mul_le_mul_of_nonneg_right hε (hr y)
    linarith
  · have := h8 t' htt' (ht'.trans ht₁₀) y
    have := mul_epsT_le hC (ht.trans_le htt') (ht'.trans hte)
    linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityDiagonalLeviStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_density_diagonal_levi : ∀ (e : ℕ) (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ), ContDiffAt ℝ 2 φ z → (∀ v, levi φ z v = ∑ q, dd q * ‖(M *ᵥ v) q‖ ^ 2) → maDens (fun _ => φ) z = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (∏ q, dd q) * ‖M.det‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | exact GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi <;> assumption)
end

