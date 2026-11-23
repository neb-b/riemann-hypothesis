module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
section
noncomputable section

open scoped UpperHalfPlane

namespace GlobalTheory.Sieg.Model

theorem exponent_exact {c : ℕ} (h : Nat.Coprime c 6) :
    12 * ((c ^ 2 - 1) / 12) + 1 = c ^ 2 ∧ 2 * (((c : ℤ) - (c : ℤ) ^ 2) / 2) = (c : ℤ) - (c : ℤ) ^ 2 := by
  constructor
  · have h2 : ¬ 2 ∣ c := fun hh => by
      have := Nat.dvd_gcd hh (show 2 ∣ 6 by norm_num); rw [h] at this; omega
    have h3 : ¬ 3 ∣ c := fun hh => by
      have := Nat.dvd_gcd hh (show 3 ∣ 6 by norm_num); rw [h] at this; omega
    have h12 : c ^ 2 % 12 = 1 := by
      rw [Nat.pow_mod]
      have : c % 12 = 1 ∨ c % 12 = 5 ∨ c % 12 = 7 ∨ c % 12 = 11 := by omega
      rcases this with h | h | h | h <;> rw [h]
    omega
  · apply Int.mul_ediv_cancel'
    have : (c : ℤ) - (c : ℤ) ^ 2 = -((c : ℤ) * (c - 1)) := by ring
    rw [this]
    exact (dvd_neg).2 (Int.even_mul_pred_self (c : ℤ)).two_dvd

theorem ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

theorem ee_add (z w : ℂ) : ee (z + w) = ee z * ee w := by
  simp only [ee, mul_add, Complex.exp_add]

theorem ee_nat_mul (n : ℕ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  simp only [ee, ← Complex.exp_nat_mul]; congr 1; ring

theorem ee_neg (z : ℂ) : ee (-z) = (ee z)⁻¹ := by
  simp only [ee, ← Complex.exp_neg]; congr 1; ring

theorem norm_ee (z : ℂ) : ‖ee z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  simp [ee, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem norm_ee_lt_one (τ : ℍ) : ‖ee τ‖ < 1 := by
  rw [norm_ee, Real.exp_lt_one_iff]
  have := τ.im_pos
  have h : 0 < 2 * Real.pi * (τ : ℂ).im := by
    have := Real.pi_pos
    simp only [UpperHalfPlane.coe_im]; positivity
  linarith

theorem ee_eq_one {a b : ℚ} (τ : ℍ) (h : ee ((a : ℂ) * τ + b) = 1) : a = 0 ∧ ∃ n : ℤ, (n : ℚ) = b := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h1 : (a : ℂ) * τ + b = n := by
    apply mul_left_cancel₀ hp; rw [hn]; ring
  have him := congrArg Complex.im h1
  simp at him
  have ha : a = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h τ.im_pos.ne'
  refine ⟨ha, n, ?_⟩
  subst ha
  simp at h1
  exact_mod_cast h1.symm

theorem ne_one_of_not_int {y : Fin 2 → ℚ}
    (hy : ¬ (y 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ y 1 ∈ Set.range ((↑) : ℤ → ℚ))) (τ : ℍ) (m : ℕ) :
    1 - ee τ ^ m * ee (pt y τ) ≠ 0 ∧ 1 - ee τ ^ m * (ee (pt y τ))⁻¹ ≠ 0 := by
  constructor
  · intro h
    have h' : ee ((((m : ℚ) + y 0 : ℚ) : ℂ) * τ + (y 1 : ℚ)) = 1 := by
      rw [sub_eq_zero, ← ee_nat_mul, ← ee_add] at h
      rw [h]; congr 1; simp [pt]; ring
    obtain ⟨h0, n, hn⟩ := ee_eq_one τ h'
    exact hy ⟨⟨-m, by push_cast; linarith⟩, ⟨n, hn⟩⟩
  · intro h
    have h' : ee ((((m : ℚ) - y 0 : ℚ) : ℂ) * τ + (-y 1 : ℚ)) = 1 := by
      rw [sub_eq_zero, ← ee_nat_mul, ← ee_neg, ← ee_add] at h
      rw [h]; congr 1; simp [pt]; ring
    obtain ⟨h0, n, hn⟩ := ee_eq_one τ h'
    exact hy ⟨⟨m, by push_cast; linarith⟩, ⟨-n, by push_cast; linarith⟩⟩

theorem hasProd_geom {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) (h : ∀ m : ℕ, 1 - q ^ (m + 1) * a ≠ 0) :
    ∃ P : ℂ, P ≠ 0 ∧ HasProd (fun m : ℕ => 1 - q ^ (m + 1) * a) P := by
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * a)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_succ]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _
  refine ⟨∏' m : ℕ, (1 + -(q ^ (m + 1) * a)), ?_, ?_⟩
  · exact tprod_one_add_ne_zero_of_summable (fun m => by simpa [sub_eq_add_neg] using h m) hs
  · simpa [sub_eq_add_neg] using (multipliable_one_add_of_summable hs).hasProd

theorem hasProd_inv {f : ℕ → ℂ} {P : ℂ} (h : HasProd f P) (hP : P ≠ 0) : HasProd (fun m => (f m)⁻¹) P⁻¹ := by
  have := Filter.Tendsto.inv₀ h hP
  simpa [HasProd, Finset.prod_inv_distrib] using this

theorem hasProd_pow {f : ℕ → ℂ} {P : ℂ} (h : HasProd f P) (k : ℕ) : HasProd (fun m => (f m) ^ k) (P ^ k) := by
  have := Filter.Tendsto.pow h k
  simpa [HasProd, Finset.prod_pow] using this

theorem ee_pt_pow (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ee (pt x τ) ^ c = ee (pt (c • x) τ) := by
  rw [← ee_nat_mul]; congr 1; simp [pt]; ring

theorem multipliable_and_sg_ne_zero {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    Multipliable (fun m : ℕ => cthFac c (ee τ) (ee (pt x τ)) (m + 1)) ∧ 1 - ee (pt x τ) ^ c ≠ 0 ∧ sg c x τ ≠ 0 := by
  have hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa using h.2.2
  have hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact h.2.2 ⟨⟨c * a, by rw [← ha]; push_cast; ring⟩, ⟨c * b, by rw [← hb]; push_cast; ring⟩⟩
  have hq := norm_ee_lt_one τ
  obtain ⟨A, hA, pA⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hx τ (m + 1)).1
  obtain ⟨B, hB, pB⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hx τ (m + 1)).2
  obtain ⟨C, hC, pC⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hc τ (m + 1)).1
  obtain ⟨D, hD, pD⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hc τ (m + 1)).2
  have hP : HasProd (fun m : ℕ => cthFac c (ee τ) (ee (pt x τ)) (m + 1)) (A ^ (c ^ 2) * B ^ (c ^ 2) * (C * D)⁻¹) := by
    have := ((hasProd_pow pA (c ^ 2)).mul (hasProd_pow pB (c ^ 2))).mul (hasProd_inv (pC.mul pD) (mul_ne_zero hC hD))
    simpa only [cthFac, ee_pt_pow, div_eq_mul_inv] using this
  have h1 : 1 - ee (pt x τ) ^ c ≠ 0 := by
    have := (ne_one_of_not_int hc τ 0).1
    rwa [pow_zero, one_mul, ← ee_pt_pow] at this
  have h2 : 1 - ee (pt x τ) ≠ 0 := by
    have := (ne_one_of_not_int hx τ 0).1
    rwa [pow_zero, one_mul] at this
  refine ⟨hP.multipliable, h1, ?_⟩
  unfold sg cth
  rw [hP.tprod_eq]
  have e1 := ee_ne_zero (τ : ℂ)
  have e2 : -ee (pt x τ) ≠ 0 := neg_ne_zero.2 (ee_ne_zero _)
  refine mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ e1) (zpow_ne_zero _ e2)) (pow_ne_zero _ h2)) h1) ?_
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)) (inv_ne_zero (mul_ne_zero hC hD))

theorem summable_exp_abs {a : ℝ} (ha : 0 < a) : Summable fun n : ℤ => Real.exp (-(a * |(n : ℝ)|)) := by
  have hs : Summable fun n : ℕ => Real.exp (-(a * n)) := by
    have := summable_geometric_of_lt_one (Real.exp_pos (-a)).le (Real.exp_lt_one_iff.2 (by linarith))
    refine this.congr fun n => ?_
    rw [← Real.exp_nat_mul]; congr 1; ring
  apply Summable.of_nat_of_neg <;> simpa using hs

theorem summable_pow_exp_abs {a : ℝ} (ha : 0 < a) (k : ℕ) (s : ℝ) :
    Summable fun n : ℤ => |s + n| ^ k * Real.exp (-(2 * a * |s + n|)) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((summable_exp_abs ha).mul_left ((k.factorial : ℝ) / a ^ k * Real.exp (a * |s|)))
  have h1 := Real.pow_div_factorial_le_exp (a * |s + n|) (by positivity) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h2 : |s + n| ^ k ≤ (k.factorial : ℝ) / a ^ k * Real.exp (a * |s + n|) := by
    rw [div_le_iff₀ hk, mul_pow] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have h3 : |(n : ℝ)| ≤ |s + n| + |s| := by
    have := abs_sub (s + n) s
    simpa using this
  calc |s + n| ^ k * Real.exp (-(2 * a * |s + n|))
      ≤ ((k.factorial : ℝ) / a ^ k * Real.exp (a * |s + n|)) * Real.exp (-(2 * a * |s + n|)) := by gcongr
    _ = (k.factorial : ℝ) / a ^ k * Real.exp (-(a * |s + n|)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (k.factorial : ℝ) / a ^ k * Real.exp (a * |s| + -(a * |(n : ℝ)|)) := by
        gcongr; nlinarith
    _ = _ := by rw [Real.exp_add, mul_assoc]

theorem summable_fTerm (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : Summable (fTerm j x τ) := by
  have hy : 0 < τ.im := τ.im_pos
  have hπ := Real.pi_pos
  have hN : (0 : ℝ) < (x 0).den := by exact_mod_cast (x 0).den_pos
  have s1 := summable_pow_exp_abs (a := Real.pi * τ.im / 2) (by positivity) (j - 1) (x 0 : ℝ)
  have s2 := summable_exp_abs (a := Real.pi * τ.im / (x 0).den) (by positivity)
  refine Summable.of_norm_bounded (s1.mul_of_nonneg s2 (fun _ => by positivity) (fun _ => by positivity)) ?_
  rintro ⟨n, d⟩
  unfold fTerm
  split_ifs with h
  · have hν : x 0 + n ≠ 0 := fun h0 => by simp [h0] at h
    have hd : d ≠ 0 := fun h0 => by simp [h0] at h
    have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast Int.one_le_abs hd
    have hint : ((x 0).den : ℚ) * (x 0 + n) = (((x 0).num + (x 0).den * n : ℤ) : ℚ) := by
      push_cast; rw [mul_add, Rat.den_mul_eq_num]
    have hk0 : ((x 0).num + (x 0).den * n : ℤ) ≠ 0 := fun h0 => by
      rw [h0] at hint
      exact hν (by simpa using hint)
    have hν1 : (1 : ℝ) ≤ (x 0).den * |(x 0 : ℝ) + n| := by
      have h1 : (1 : ℝ) ≤ |((((x 0).num + (x 0).den * n : ℤ) : ℚ) : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
      rw [← hint] at h1
      push_cast at h1
      rwa [abs_mul, abs_of_pos hN] at h1
    have hpos : (0 : ℝ) < ((x 0 : ℝ) + n) * d := by exact_mod_cast h
    have habs : ((x 0 : ℝ) + n) * d = |(x 0 : ℝ) + n| * |(d : ℝ)| := by rw [← abs_mul, abs_of_pos hpos]
    have hs : ‖(Int.sign d : ℂ)‖ = 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast Int.abs_sign_of_ne_zero hd
    have hn : ‖((x 0 + n : ℚ) : ℂ)‖ = |(x 0 : ℝ) + n| := by
      rw [Complex.norm_ratCast]; push_cast; rfl
    simp only [norm_mul, norm_pow, hs, hn, norm_ee, one_mul]
    have i1 : (((x 0 + n : ℚ) : ℂ) * d * (τ : ℂ)).im = ((x 0 : ℝ) + n) * d * τ.im := by
      simp [Complex.mul_im]
    have i2 : ((x 1 : ℂ) * d).im = 0 := by simp [Complex.mul_im]
    rw [i1, i2, habs, mul_zero, neg_zero, Real.exp_zero, mul_one,
      mul_assoc (|(x 0 : ℝ) + n| ^ (j - 1)), ← Real.exp_add]
    gcongr
    set u := |(x 0 : ℝ) + n|
    set v := |(d : ℝ)|
    have hu : 0 ≤ u := abs_nonneg _
    have a1 : u ≤ u * v := by nlinarith
    have a2 : v / (x 0).den ≤ u * v := by
      rw [div_le_iff₀ hN]; nlinarith
    have hp : 0 < Real.pi * τ.im := by positivity
    have e : Real.pi * τ.im / (x 0).den * v = Real.pi * τ.im * (v / (x 0).den) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left a1 hp.le, mul_le_mul_of_nonneg_left a2 hp.le]
  · simp only [norm_zero]; positivity

end GlobalTheory.Sieg.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
section
noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

section Formal

variable {R : Type*} [CommRing R]

def Uo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (l * n)

def Vo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then a (n / l) else 0

def dep (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then 0 else a n

def To (k : ℕ) (c : R) (q : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (q * n) + c * (q : R) ^ (k - 1) * Vo q a n

def mul (a b : ℕ → R) : ℕ → R := fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def eis (j : ℕ) (c : R) (a b : ℤ → R) : ℕ → R := fun n =>
  if n = 0 then c else ∑ p ∈ n.divisorsAntidiagonal, a p.1 * (p.1 : R) ^ (j - 1) * b p.2

def Zs (k l : ℕ) (u v : ℤ → R) (F : ℕ → ℕ → R) : ℕ → R := fun n =>
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ x ∈ p.1.divisorsAntidiagonal, ∑ y ∈ p.2.divisorsAntidiagonal,
    if l ∣ p.1 ∨ l ∣ p.2 then 0 else (x.1 : R) ^ (k - 2) * u x.2 * v y.1 * F x.1 y.1

def quo {M : ℕ} (f : ZMod M → R) : ℕ → ℕ → R := fun x x' => f ((x : ZMod M) * (x' : ZMod M)⁻¹)

def lam (B : ℕ) (c a : ℕ → R) : R := ∑ n ∈ Finset.range B, c n * a n

end Formal

section Level

variable {K : Type*} [Field K]

def val (B : ℕ) (c : ℕ → K) (l : ℕ) (α : K) (r : ℕ) (a : ℕ → K) : K := (α ^ r)⁻¹ * lam B c ((Uo l)^[r] a)

def Fser (j M : ℕ) (ζ : K) (b : ℤ → K) (c : K) (u w : ZMod M) : ℕ → K := fun s =>
  if s = 0 then c else ∑ p ∈ s.divisorsAntidiagonal,
    ((if (p.1 : ZMod M) = u then ((p.1 : K) / M) ^ (j - 1) * ζ ^ (w.val * p.2) * b p.2 else 0) -
      (if -(p.1 : ZMod M) = u then (-(p.1 : K) / M) ^ (j - 1) * (ζ ^ (w.val * p.2))⁻¹ * b (-(p.2 : ℤ)) else 0))

end Level

section Bridge

variable {K : Type*} [Field K] [CharZero K]

theorem mul_eq_cmul (f g : ℕ → K) : mul f g = GlobalTheory.KummerEisensteinGalois.cmul f g := by
  funext n
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f i * g j) n

end Bridge

def hat {N : ℕ} (φ : ZMod N → ℂ) (d : ℤ) : ℂ := ∑ y ∈ Finset.range N, φ y * cexp (2 * π * Complex.I * (y * d) / N)

def qs (a : ℕ → ℂ) (τ : ℍ) : ℂ := ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)

def PolyB (a : ℕ → ℂ) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A

def Inv (k L : ℕ) (χ : ℤ → ℂ) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ : ℍ, f (γ • τ) = χ (γ 1 1) * (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k * f τ

def MF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := PolyB a ∧ Inv k L χ (qs a)

def CF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := MF k L χ a ∧ ∃ C : ℝ, ∀ τ : ℍ, ‖qs a τ‖ ^ 2 * τ.im ^ k ≤ C

def ch {N : ℕ} (χ : DirichletCharacter ℂ N) : ℤ → ℂ := fun d => χ (d : ZMod N)

structure Prim (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) : Prop where
  cf : CF k N (ch χ) g
  one : g 1 = 1
  zero : ∀ n : ℕ, ¬ n.Coprime N → g n = 0
  eig : ∀ q : ℕ, q.Prime → ¬ q ∣ N → To k (ch χ q) q g = fun n => g q * g n

structure Wt (L : ℕ) (ρ : ℍ → ℝ) : Prop where
  meas : Measurable ρ
  nonneg : ∀ τ, 0 ≤ ρ τ
  sum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ)) • τ)) 1
  supp : ∃ S : Finset SL(2, ℤ), ∀ τ, ρ τ ≠ 0 → ∃ γ ∈ S, γ • τ ∈ ModularGroup.fd

def pet (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) : ℂ := ∫ τ : ℍ, (ρ τ : ℂ) * (conj (h τ) * f τ * (τ.im : ℂ) ^ k)

structure EigF (k N l : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) : Prop where
  T : ∀ a, MF k (N * l) (ch ε) a → ∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam B c (To k (ch ε q) q a) = t q * lam B c a
  U : ∀ a, MF k (N * l) (ch ε) a → lam B c (Uo l a) = α * lam B c a

def trm (j : ℕ) (s : ℝ) (z : ℂ) : ℂ := (z ^ j)⁻¹ * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ)

def dif (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) : ℤ × ℤ → ℂ := fun x =>
  F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, F (x + (r : ℤ) • v)

def lat (j : ℕ) (s : ℝ) (L : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ) : ℂ :=
  ∑' x : ℤ × ℤ, Φ x * dif L v (dif L v fun y => trm j s ((y.1 : ℂ) * τ + y.2)) x

end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
section
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise

noncomputable section
namespace GlobalTheory.SplitWeil.Model

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountable_and_t2_local_field : SecondCountableTopology k ∧ T2Space k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem nabs_pos (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact_mod_cast distribHaarChar_pos

theorem nabs_mul (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by
  simp [nabs]

theorem nabs_one : nabs k 1 = 1 := by simp [nabs]

theorem om_one {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (Φ : Matrix b a k → ℂ) : om μ (1 : GL a k) (1 : GL b k) Φ = Φ := by
  funext x; simp [om, nabs_one]

theorem om_mul {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ) := by
  funext x
  simp only [om, map_mul, nabs_mul, Real.mul_rpow (nabs_pos _).le (nabs_pos _).le,
    _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Complex.ofReal_mul]
  ring

theorem not_hasConductor_one (c : kˣ) : ¬ HasConductor (1 : AddChar k Circle) c := by
  intro h
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have := (h (c / r)).1 (fun y _ => rfl)
  have hc : valuation k (c : k) ≠ 0 := by simp
  have hr' : valuation k r ≠ 0 := by simpa using hr
  rw [map_div₀, div_le_iff₀ (zero_lt_iff.2 hr')] at this
  have h2 : valuation k (c : k) * valuation k r < valuation k (c : k) * 1 :=
    mul_lt_mul_of_pos_left hr1 (zero_lt_iff.2 hc)
  rw [mul_one] at h2
  exact absurd this (not_le.2 h2)

def ratCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

theorem ratCircle_eq_zero (x : AddCircle (1 : ℚ)) (h : ratCircle x = 0) : x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    have h' : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h'
    refine (AddCircle.coe_eq_zero_iff _).2 ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this : (n : ℚ) = q)

theorem exists_hasConductor : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)⁻¹
  have ht1 : 1 < valuation k t := by
    rw [ht]; exact uniformizer_inv_le_iff.1 le_rfl
  let O : AddSubgroup k := (𝒪[k]).toAddSubgroup
  have hne : (QuotientAddGroup.mk t : k ⧸ O) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact not_le.2 ht1
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let c' : (k ⧸ O) →+ AddCircle (1 : ℚ) := c
  let f : k →+ AddCircle (1 : ℝ) := ratCircle.comp (c'.comp (QuotientAddGroup.mk' O))
  refine ⟨(AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom f, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩⟩
  · by_contra hx
    have hx' : 1 < valuation k x := by simpa using hx
    have h1 := h t (ht ▸ uniformizer_inv_le_iff.2 hx')
    have h2 : AddCircle.toCircle (f t) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h1
    exact hc (ratCircle_eq_zero _ (AddCircle.injective_toCircle one_ne_zero h2))
  · have hy' : (QuotientAddGroup.mk y : k ⧸ O) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      exact hy.trans (by simpa using h)
    show AddCircle.toCircle (ratCircle (c' (QuotientAddGroup.mk y))) = 1
    rw [hy']; simp

theorem KOne_le_KO (n : Type*) [Fintype n] [DecidableEq n] : KOne k n ≤ KO k n :=
  Subgroup.map_le_range _ _

theorem isOpen_int : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer

theorem isCompact_int : IsCompact (𝒪[k] : Set k) :=
  IsNonarchimedeanLocalField.isCompact_closedBall k 1

variable [MeasurableSpace k] [BorelSpace k]

theorem exists_isUnitVol : ∃ ν : Measure k, IsUnitVol ν := by
  let K : TopologicalSpace.PositiveCompacts k := ⟨⟨(𝒪[k] : Set k), isCompact_int⟩, by
    rw [show interior ((⟨(𝒪[k] : Set k), isCompact_int⟩ : TopologicalSpace.Compacts k).carrier) =
      (𝒪[k] : Set k) from isOpen_int.interior_eq]
    exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩

theorem nabs_vol (ν : Measure k) (h : IsUnitVol ν) (x : kˣ) :
    ν (x • (𝒪[k] : Set k)) = ENNReal.ofReal (nabs k x) := by
  have := h.1
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  rw [← distribHaarChar_mul ν x, h.2]; simp [nabs]

theorem nabs_le_one (x : kˣ) (hx : valuation k (x : k) ≤ 1) : nabs k x ≤ 1 := by
  obtain ⟨ν, h⟩ := exists_isUnitVol (k := k)
  have : ν (x • (𝒪[k] : Set k)) ≤ ν (𝒪[k] : Set k) := by
    apply measure_mono
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (show (x : k) ∈ 𝒪[k] from hx) hy
  rw [nabs_vol ν h, h.2] at this
  exact ENNReal.ofReal_le_one.1 this

theorem measurableEmbedding_val (n : Type*) [Fintype n] [DecidableEq n] :
    MeasurableEmbedding (fun g : GL n k => g.val) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  refine MeasurableEmbedding.iff_comap_eq.2 ⟨Units.val_injective, rfl, ?_⟩
  have hB : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    rfl
  rw [this]
  exact (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).measurableSet




omit [MeasurableSpace k] [BorelSpace k] in
theorem om_mem_SB {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    om μ g h Φ ∈ SB (Matrix b a k) := by
  let e : Matrix b a k ≃ₜ Matrix b a k :=
    { toFun := fun x => (h⁻¹ : GL b k).val * x * g.val
      invFun := fun x => h.val * x * (g⁻¹ : GL a k).val
      left_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  have h1 : (Φ ∘ e) ∈ SB (Matrix b a k) :=
    ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
  exact (SB (Matrix b a k)).smul_mem _ h1

end GlobalTheory.SplitWeil.Model
end
end

