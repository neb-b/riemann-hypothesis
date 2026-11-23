module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlg
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.HilbertNinety

theorem exists_unit_sigma (K : UQ) (B : InvAlg K) (u : B.A) (hu : u * B.σ u = 1) :
    ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  classical
  letI : Module ℚ B.A := Module.compHom B.A (algebraMap ℚ K.E)
  let b : B.A →+ B.A :=
    { toFun := fun a => a + B.σ a * B.σ u
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add (f := _)]; ring }
  have hb : ∀ a, b a = a + B.σ a * B.σ u := fun a => rfl
  have hbσ : ∀ a, B.σ (b a) = b a * u := by
    intro a
    rw [hb, map_add (f := _), map_mul, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ a)) * hu
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  set e : K.E := algebraMap K.O K.E x with he
  have hce : K.c e - e ≠ 0 := by
    intro h
    rw [sub_eq_zero, he, hxy] at h
    have := IsFractionRing.injective K.O K.E h
    exact hne (by rw [this, sub_self]; exact Ideal.zero_mem _)
  have key : ∀ z : B.A, algebraMap K.E B.A (K.c e - e) * z =
      algebraMap K.E B.A (K.c e) * b z - b (algebraMap K.E B.A e * z) := by
    intro z
    rw [hb, hb, map_mul, B.σ_alg, map_sub]
    ring
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  haveI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
  let S : MaximalSpectrum B.A → Submodule ℚ B.A := fun m =>
    { carrier := {a | b a ∈ m.asIdeal}
      add_mem' := fun {a c} ha hc => by
        change b (a + c) ∈ m.asIdeal
        rw [map_add (f := _)]; exact m.asIdeal.add_mem ha hc
      zero_mem' := by change b 0 ∈ m.asIdeal; rw [map_zero]; exact m.asIdeal.zero_mem
      smul_mem' := fun q a ha => by
        change b (q • a) ∈ m.asIdeal
        rw [map_rat_smul]
        change (algebraMap ℚ K.E q) • b a ∈ m.asIdeal
        rw [Algebra.smul_def]
        exact m.asIdeal.mul_mem_left _ ha }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    have hall : ∀ a, b a ∈ m.asIdeal := fun a => by
      have : a ∈ S m := hm ▸ Submodule.mem_top
      exact this
    have h1 : algebraMap K.E B.A (K.c e - e) ∈ m.asIdeal := by
      have := key 1
      rw [mul_one] at this
      rw [this]
      exact m.asIdeal.sub_mem (m.asIdeal.mul_mem_left _ (hall 1)) (hall _)
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : algebraMap K.E B.A (K.c e - e)⁻¹ * algebraMap K.E B.A (K.c e - e) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hce, map_one]
    rw [← h2]
    exact m.asIdeal.mul_mem_left _ h1
  have h3 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).1 h3
  have hunit : IsUnit (b a) := by
    by_contra hn
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
    apply ha
    exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm
  exact ⟨hunit.unit, by rw [IsUnit.unit_spec]; exact hbσ a⟩

end GlobalTheory.UnitLemma.HilbertNinety
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWindowRadii
section
namespace GlobalTheory.PMonE


open Finset in
theorem _root_.GlobalTheory.PMonE.exists_window_radii : ∀ (F : Type) [NontriviallyNormedField F]
    [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin (k + 1) → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ π : Fin (k + 1) → F, (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) ∧
      (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) =
        ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) ∧
      (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p := by
  intro F _ _ _ p _ _ _ k ϖ hϖ lam hlam hanti hclose
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hl : ∀ j, 0 < ‖lam j‖ := fun j => norm_pos_iff.mpr (hlam j)
  have hρ : ∀ j : Fin k, ∃ y : F, y ^ p ^ (j : ℕ) = lam j.castSucc / lam j.succ :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ (pow_pos (by omega) _)
  choose ρ hρ using hρ
  have hρn : ∀ j : Fin k, ‖ρ j‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ / ‖lam j.succ‖ := fun j => by
    rw [← norm_pow, hρ, norm_div]
  have hρ1 : ∀ j : Fin k, 1 ≤ ‖ρ j‖ := fun j => by
    rw [← one_le_pow_iff_of_nonneg (norm_nonneg _) (pow_pos (by omega : 0 < p) (j : ℕ)).ne', hρn,
      one_le_div (hl _)]
    exact hanti (Fin.castSucc_le_succ j)
  set ρ' : ℕ → F := fun n => if h : n < k then ρ ⟨n, h⟩ else 1 with hρ'
  have hρ'1 : ∀ n, 1 ≤ ‖ρ' n‖ := fun n => by
    simp only [hρ']; split_ifs with h
    · exact hρ1 _
    · simp
  have hρ'ne : ∀ n, ρ' n ≠ 0 := fun n h0 => by
    have := hρ'1 n; rw [h0, norm_zero] at this; linarith
  set P : ℕ → F := fun j => ∏ n ∈ range j, ρ' n with hP
  have hPne : ∀ j, P j ≠ 0 := fun j => prod_ne_zero_iff.mpr fun n _ => hρ'ne n
  have hPsucc : ∀ j, P (j + 1) = P j * ρ' j := fun j => prod_range_succ _ _
  have hPmono : Monotone fun j => ‖P j‖ := by
    refine monotone_nat_of_le_succ fun j => ?_
    simp only [hPsucc, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (hρ'1 j)
  have hP0 : P 0 = 1 := by simp [hP]
  have hc1 : 1 ≤ ‖P k‖ := by
    have := hPmono (Nat.zero_le k); simpa [hP0] using this
  set c := ‖P k‖ with hc
  have hcpos : 0 < c := by linarith
  set N := p ^ (k + 1) - 1 with hN
  have hpk : 2 ≤ p ^ (k + 1) := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  have hNpos : 0 < N := by omega
  have hN1 : p ^ (k + 1) = N + 1 := by omega
  set w : F := (lam 0 * ϖ) ^ p / ((lam (Fin.last k)) ^ p * P k ^ p ^ (k + 1)) with hw
  have hwn : ‖w‖ = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c ^ (N + 1)) := by
    rw [hw]
    simp only [norm_div, norm_mul, norm_pow, hϖ, ← hN1]
    ring
  have hwne : w ≠ 0 := by
    rw [hw]
    exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (hlam 0) (by
      intro h0; rw [h0, norm_zero] at hϖ; exact (inv_pos.mpr hpR).ne' hϖ.symm)))
      (mul_ne_zero (pow_ne_zero _ (hlam _)) (pow_ne_zero _ (hPne k)))
  obtain ⟨π0, hπ0⟩ := IsAlgClosed.exists_pow_nat_eq w hNpos
  have hπ0ne : π0 ≠ 0 := by
    intro h0; rw [h0, zero_pow hNpos.ne'] at hπ0; exact hwne hπ0.symm
  set s := ‖π0‖ with hs
  have hspos : 0 < s := norm_pos_iff.mpr hπ0ne
  have hsN : s ^ N = ‖w‖ := by rw [hs, ← norm_pow, hπ0]
  have hl0 : ‖lam 0‖ / p < ‖lam (Fin.last k)‖ := by
    rw [div_lt_iff₀ hpR, mul_comm]; exact hclose 0 (Fin.last k)
  have hsc : s * c < 1 := by
    have key : (s * c) ^ N < 1 := by
      have hwc : ‖w‖ * c ^ N = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c) := by
        rw [hwn, pow_succ]
        field_simp
      rw [mul_pow, hsN, hwc, div_lt_one (by have := hl (Fin.last k); positivity)]
      calc (‖lam 0‖ / p) ^ p < ‖lam (Fin.last k)‖ ^ p :=
            pow_lt_pow_left₀ hl0 (by positivity) (by omega)
        _ ≤ ‖lam (Fin.last k)‖ ^ p * c :=
            le_mul_of_one_le_right (by have := hl (Fin.last k); positivity) hc1
    exact (pow_lt_one_iff_of_nonneg (by positivity) hNpos.ne').mp key
  refine ⟨fun j => π0 * P j, fun j => ⟨mul_ne_zero hπ0ne (hPne _), ?_⟩, fun j => ?_, ?_⟩
  · rw [norm_mul, ← hs]
    calc s * ‖P j‖ ≤ s * c := mul_le_mul_of_nonneg_left (hPmono (Nat.lt_succ_iff.mp j.isLt)) hspos.le
      _ < 1 := hsc
  · simp only [Fin.val_succ, Fin.coe_castSucc, hPsucc, norm_mul, mul_pow]
    have : ρ' j = ρ j := by simp [hρ', j.isLt]
    rw [this, hρn]
    have := hl j.succ
    field_simp
  · simp only [Fin.val_zero, Fin.val_last, hP0, mul_one, norm_mul, ← hs, ← hc, mul_pow, ← pow_mul]
    rw [← pow_succ, hN1, pow_succ s N, hsN, hwn]
    have := hl (Fin.last k)
    field_simp

end GlobalTheory.PMonE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialTruncatedLogAdditivityDefectCoeffDvd
section
open GlobalTheory.LogU MvPolynomial Finset

namespace GlobalTheory.LogUIntg

lemma single_add_single_eq_iff {i j i' j' : ℕ} :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j = Finsupp.single 0 i' + Finsupp.single 1 j') ↔
      (i = i' ∧ j = j') := by
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma coeff_monomial_two (i j p q : ℕ) (c : ℤ) :
    AddMonoidAlgebra.coeff (monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c)
        (Finsupp.single 0 i + Finsupp.single 1 j) =
      if p = i ∧ q = j then c else 0 := by
  rw [coeff_monomial]
  simp only [single_add_single_eq_iff]

lemma monomial_two_eq (p q : ℕ) (c : ℤ) :
    monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c = C c * X 0 ^ p * X 1 ^ q := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul]
  simp

lemma factorial_dvd_term (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s)
    (hn : n ≤ (s + a) + (s + (K - s - a))) :
    n.factorial * ((n - 1) / 2).factorial ∣
      (s + a).factorial * (s + (K - s - a)).factorial *
        (n.factorial / K * (K.choose s * (K - s).choose a)) := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s a)
  rw [Nat.add_sub_cancel_left] at e1
  have e2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s (K - s - a))
  rw [Nat.add_sub_cancel_left] at e2
  have e3 := Nat.choose_mul_factorial_mul_factorial ha
  have e4 := Nat.choose_mul_factorial_mul_factorial hs
  have e5 : n.factorial / K * K.factorial = n.factorial * (K - 1).factorial := by
    rw [← Nat.mul_factorial_pred (by omega : K ≠ 0), ← mul_assoc,
      Nat.div_mul_cancel (Nat.dvd_factorial (by omega) hKn)]
  rw [← e1, ← e2]
  have key : (s + a).choose s * s.factorial * a.factorial *
      ((s + (K - s - a)).choose s * s.factorial * (K - s - a).factorial) *
        (n.factorial / K * (K.choose s * (K - s).choose a)) =
      n.factorial * ((K - 1).factorial * ((s + a).choose s * (s + (K - s - a)).choose s * s.factorial)) := by
    calc _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          ((K.choose s * s.factorial * ((K - s).choose a * a.factorial * (K - s - a).factorial)) *
            (n.factorial / K)) := by ring
      _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          (n.factorial / K * K.factorial) := by rw [e3, e4]; ring
      _ = _ := by rw [e5]; ring
  rw [key]
  exact mul_dvd_mul (dvd_refl _)
    (dvd_mul_of_dvd_left (Nat.factorial_dvd_factorial (by omega)) _)

def Good (n : ℕ) (f : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∀ i j : ℕ, n ≤ i + j → ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) ∣
    ((i.factorial * j.factorial : ℕ) : ℤ) * AddMonoidAlgebra.coeff f (Finsupp.single 0 i + Finsupp.single 1 j)

lemma good_sub {n : ℕ} {f g : MvPolynomial (Fin 2) ℤ} (hf : Good n f) (hg : Good n g) :
    Good n (f - g) := by
  intro i j h
  rw [coeff_sub, mul_sub]
  exact dvd_sub (hf i j h) (hg i j h)

lemma good_sum {n : ℕ} {ι : Type} (t : Finset ι) (f : ι → MvPolynomial (Fin 2) ℤ)
    (hf : ∀ x ∈ t, Good n (f x)) : Good n (∑ x ∈ t, f x) := by
  intro i j h
  rw [coeff_sum, Finset.mul_sum]
  exact Finset.dvd_sum fun x hx => hf x hx i j h

lemma good_C_mul {n : ℕ} (c : ℤ) {f : MvPolynomial (Fin 2) ℤ} (hf : Good n f) :
    Good n (C c * f) := by
  intro i j h
  rw [coeff_C_mul, mul_left_comm]
  exact Dvd.dvd.mul_left (hf i j h) c

lemma good_atom (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s) :
    Good n (monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
      ((n.factorial / K * (K.choose s * (K - s).choose a) : ℕ) : ℤ)) := by
  intro i j h
  rw [coeff_monomial_two]
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    rw [← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.mpr (factorial_dvd_term n K s a hK1 hKn hs ha h)
  · simp

lemma C_mul_pow_u (m K : ℕ) :
    C (m : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K =
      ∑ s ∈ range (K + 1), ∑ a ∈ range (K - s + 1),
        monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
          ((m * (K.choose s * (K - s).choose a) : ℕ) : ℤ) := by
  rw [show (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = X 0 * X 1 + (X 0 + X 1) by ring,
    add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [monomial_two_eq]
  simp only [Nat.cast_mul, map_mul, map_natCast]
  ring

lemma good_C_mul_pow_u (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  rw [C_mul_pow_u]
  refine good_sum _ _ fun s hs => good_sum _ _ fun a ha => ?_
  rw [Finset.mem_range] at hs ha
  exact good_atom n K s a hK1 hKn (by omega) (by omega)

lemma logPolynomialDefectDivisible_C_mul_X_zero_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 K hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

lemma logPolynomialDefectDivisible_C_mul_X_one_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 0 hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

lemma good_truncLogF (n : ℕ) (u : MvPolynomial (Fin 2) ℤ)
    (hu : ∀ K, 1 ≤ K → K ≤ n → Good n (C ((n.factorial / K : ℕ) : ℤ) * u ^ K)) :
    Good n (truncLogF n u) := by
  unfold truncLogF
  refine good_sum _ _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  have e : ((-1 : MvPolynomial (Fin 2) ℤ) ^ k * ((n.factorial / (k + 1) : ℕ) : MvPolynomial (Fin 2) ℤ) *
      u ^ (k + 1)) = C ((-1) ^ k) * (C ((n.factorial / (k + 1) : ℕ) : ℤ) * u ^ (k + 1)) := by
    simp only [map_pow, map_neg, map_one, map_natCast]; ring
  rw [e]
  exact good_C_mul _ (hu (k + 1) (by omega) (by omega))

theorem good_logDefect (n : ℕ) : Good n (logDefect n) := by
  unfold logDefect
  refine good_sub (good_sub ?_ ?_) ?_
  · exact good_truncLogF n _ fun K h1 h2 => good_C_mul_pow_u n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_zero_pow n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_one_pow n K h1 h2

theorem logDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ,
    ((i.factorial * j.factorial : ℕ) : ℤ) *
        AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  intro n i j h
  exact good_logDefect n i j h

end GlobalTheory.LogUIntg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsFiniteFieldExt
section
open GlobalTheory.UnitLemma Polynomial IsDedekindDomain

noncomputable section
namespace GlobalTheory.FieldUnitsQuotFG

theorem fg_quot_ker {G S : Type} [CommGroup G] [Finite S] (φ : G →* (S → Multiplicative ℤ)) :
    Group.FG (G ⧸ φ.ker) := by
  let e : (S → ℤ) ≃+ Additive (S → Multiplicative ℤ) :=
    { toFun := fun f => Additive.ofMul (fun v => Multiplicative.ofAdd (f v))
      invFun := fun g v => Multiplicative.toAdd (Additive.toMul g v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : Module.Finite ℤ (Additive (S → Multiplicative ℤ)) := Module.Finite.equiv e.toIntLinearEquiv
  have h1 : φ.range.FG := by
    rw [Subgroup.fg_iff_add_fg]
    rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (Subgroup.toAddSubgroup φ.range)]
    exact (Submodule.fg_iff_addSubgroup_fg _).1 (IsNoetherian.noetherian _)
  haveI : Group.FG φ.range := (Group.fg_iff_subgroup_fg _).2 h1
  exact Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom)
    (QuotientGroup.quotientKerEquivRange φ).symm.surjective

variable (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
  [FiniteDimensional K.E L]

theorem finite_spec [IsDedekindDomain (integralClosure K.O L)] :
    Finite (HeightOneSpectrum (integralClosure K.O L)) := by
  set C := integralClosure K.O L
  have hinj : Function.Injective (algebraMap K.O C) := by
    intro a b h
    have h2 : algebraMap K.O L a = algebraMap K.O L b := by
      rw [IsScalarTower.algebraMap_apply K.O C L a, h, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply K.O K.E L, IsScalarTower.algebraMap_apply K.O K.E L] at h2
    exact IsFractionRing.injective K.O K.E ((algebraMap K.E L).injective h2)
  set I := Ideal.map (algebraMap K.O C) (IsLocalRing.maximalIdeal K.O)
  have hI : I ≠ 0 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    intro h0
    have : algebraMap K.O C ϖ ∈ I :=
      Ideal.mem_map_of_mem _ (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
    rw [h0, Submodule.zero_eq_bot, Ideal.mem_bot] at this
    exact hϖ.ne_zero (hinj (this.trans (map_zero _).symm))
  have hall : ∀ v : HeightOneSpectrum C, v.asIdeal ∣ I := by
    intro v
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    have hp : (v.asIdeal.comap (algebraMap K.O C)).IsPrime := Ideal.comap_isPrime _ _
    have hne : v.asIdeal.comap (algebraMap K.O C) ≠ ⊥ := by
      intro h
      exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
    have hmax := hp.isMaximal hne
    rw [IsLocalRing.eq_maximalIdeal hmax]
  have := Ideal.finite_factors hI
  have huniv : (Set.univ : Set (HeightOneSpectrum C)) = {v | v.asIdeal ∣ I} := by
    ext v; simp [hall v]
  exact Set.finite_univ_iff.1 (huniv ▸ this)

def valHom [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L] :
    Lˣ →* (HeightOneSpectrum (integralClosure K.O L) → Multiplicative ℤ) :=
  Pi.monoidHom fun v => WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map ((v.valuation L : Valuation L (WithZero (Multiplicative ℤ))) : L →* WithZero (Multiplicative ℤ)))

theorem valHom_apply [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L]
    (x : Lˣ) (v : HeightOneSpectrum (integralClosure K.O L)) :
    ((valHom K L x v : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.valuation L (x : L) := by
  show ((WithZero.unitsWithZeroEquiv (Units.map ((v.valuation L : Valuation L (WithZero (Multiplicative ℤ))) :
    L →* WithZero (Multiplicative ℤ)) x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _
  rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  rfl

theorem ker_valHom [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L] :
    (valHom K L).ker = intUnits K.O L := by
  ext x
  rw [MonoidHom.mem_ker]
  have key : ∀ y : L, IsIntegral K.O y ↔
      ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L y ≤ 1 := by
    intro y
    constructor
    · intro hy v
      have : y = algebraMap (integralClosure K.O L) L ⟨y, hy⟩ := rfl
      rw [this]
      exact v.valuation_le_one _
    · intro h
      obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L y h
      rw [← hc]
      exact c.2
  have h1 : valHom K L x = 1 ↔ ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L (x : L) = 1 := by
    rw [funext_iff]
    refine forall_congr' fun v => ?_
    rw [← valHom_apply, Pi.one_apply]
    constructor
    · intro h
      rw [h, WithZero.coe_one]
    · intro h
      exact WithZero.coe_injective (h.trans WithZero.coe_one.symm)
  rw [h1]
  show _ ↔ IsIntegral K.O (x : L) ∧ IsIntegral K.O ((x⁻¹ : Lˣ) : L)
  rw [key, key]
  constructor
  · intro h
    refine ⟨fun v => (h v).le, fun v => ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
  · rintro ⟨ha, hb⟩ v
    apply le_antisymm (ha v)
    have hx : v.valuation L (x : L) * v.valuation L ((x⁻¹ : Lˣ) : L) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc 1 = v.valuation L (x : L) * v.valuation L ((x⁻¹ : Lˣ) : L) := hx.symm
      _ ≤ v.valuation L (x : L) * 1 := by gcongr; exact hb v
      _ = v.valuation L (x : L) := mul_one _

theorem fg_units_quot : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
    [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  intro K L _ _ _ _ _
  haveI : IsDedekindDomain (integralClosure K.O L) := integralClosure.isDedekindDomain K.O K.E L
  haveI : IsFractionRing (integralClosure K.O L) L := integralClosure.isFractionRing_of_finite_extension K.E L
  haveI := finite_spec K L
  rw [← ker_valHom K L]
  exact fg_quot_ker _

end GlobalTheory.FieldUnitsQuotFG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramDetEqNormMulGramDetOne
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.InvAlg

theorem gramDet_eq_norm_mul (K : UQ) (B : InvAlg K) (x : B.A) :
    B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by
  classical
  set b := Module.finBasis K.E B.A
  have hM : (Matrix.of fun i j => B.herm x (b i) (b j)) =
      (Algebra.leftMulMatrix b x).transpose * (Matrix.of fun i j => B.herm 1 (b i) (b j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, herm, one_mul,
      Algebra.leftMulMatrix_apply]
    have h := b.sum_repr (x * b i)
    conv_lhs => rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, LinearMap.toMatrix_apply]
    simp
  unfold gramDet
  rw [hM, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det b]

end GlobalTheory.UnitLemma.InvAlg
end

