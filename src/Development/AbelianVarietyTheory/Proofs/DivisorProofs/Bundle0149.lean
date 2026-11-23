module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAddSelf
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.PosDet

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem det_left {p : Matrix ι ι ℂ} (pp : p * p = p) (g : Matrix ι ι ℂ) :
    (p * g + (1 - p)).det = (p * g * p + (1 - p)).det := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have e : p * g + (1 - p) = (1 + p * (g * (1 - p))) * (p * g * p + (1 - p)) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
  have e2 : g * (1 - p) * p = 0 := by
    simp only [mul_sub, sub_mul, mul_assoc, pp, one_mul, mul_one, sub_self]
  rw [e, det_mul, det_one_add_mul_comm, e2, add_zero, det_one, one_mul]

theorem det_right {p : Matrix ι ι ℂ} (pp : p * p = p) (g : Matrix ι ι ℂ) :
    (g * p + (1 - p)).det = (p * g * p + (1 - p)).det := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have e : g * p + (1 - p) = (p * g * p + (1 - p)) * (1 + ((1 - p) * g) * p) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
  have e2 : p * ((1 - p) * g) = 0 := by
    simp only [mul_sub, sub_mul, pp', one_mul, sub_self]
  rw [e, det_mul, det_one_add_mul_comm, e2, add_zero, det_one, mul_one]

theorem det_compl {p : Matrix ι ι ℂ} (pp : p * p = p) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (p + (1 - p) * g * (1 - p)).det = (p * h + (1 - p)).det * g.det := by
  have qq : (1 - p) * (1 - p) = 1 - p := by
    simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel
  have := det_left qq g
  rw [sub_sub_cancel] at this
  rw [add_comm p, ← this, ← det_mul, add_mul, mul_assoc p, hg, mul_one, add_comm]

theorem det_sign {p : Matrix ι ι ℂ} (pp : p * p = p) : (p - (1 - p)).det * (p - (1 - p)).det = 1 := by
  have : (p - (1 - p)) * (p - (1 - p)) = 1 := by
    simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel
  rw [← det_mul, this, det_one]

theorem half_add_self (X : Matrix ι ι ℂ) : (1 / 2 : ℂ) • (X + X) = X := by module

theorem half_eq {p : Matrix ι ι ℂ} (pp : p * p = p) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (1 / 2 : ℂ) • (1 + (p - (1 - p)) * h * (p - (1 - p)) * g) =
      (p - (1 - p)) * h * (p * g * p - (1 - p) * g * (1 - p)) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have hg' : ∀ x, h * (g * x) = x := fun x => by rw [← mul_assoc, hg, one_mul]
  rw [← half_add_self ((p - (1 - p)) * h * (p * g * p - (1 - p) * g * (1 - p)))]
  congr 1
  simp only [mul_sub, sub_mul, mul_assoc, pp, hg, hg', one_mul, mul_one]; abel

theorem det_diag {p : Matrix ι ι ℂ} (pp : p * p = p) (a : Matrix ι ι ℂ) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (p * a * p - (1 - p) * g * (1 - p)).det =
      (p - (1 - p)).det * (p * a + (1 - p)).det * ((p * h + (1 - p)).det * g.det) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  rw [← det_compl pp hg, det_left pp a, ← det_mul, ← det_mul]
  congr 1
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel

theorem det_block {p : Matrix ι ι ℂ} (pp : p * p = p) {g₁ h₁ g₂ h₂ : Matrix ι ι ℂ} (hg₁ : h₁ * g₁ = 1)
    (hg₂ : h₂ * g₂ = 1) :
    (fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
      (p * g₂ * p - (1 - p) * g₂ * (1 - p))).det =
      g₁.det * g₂.det * ((p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det * (p * (h₂ * g₁) + (1 - p)).det) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have gh : g₂ * h₂ = 1 := mul_eq_one_comm.1 hg₂
  have gh' : ∀ x, g₂ * (h₂ * x) = x := fun x => by rw [← mul_assoc, gh, one_mul]
  have hσ : fromBlocks p (1 - p) (1 - p) p * fromBlocks p (1 - p) (1 - p) p = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> (simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel)
  have e : fromBlocks p (1 - p) (1 - p) p *
      fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
      (p * g₂ * p - (1 - p) * g₂ * (1 - p)) * fromBlocks p (1 - p) (1 - p) p =
      fromBlocks ((p - (1 - p)) * g₂ * (h₂ * g₁ * p + (1 - p))) (p * g₂ * p - (1 - p) * g₁ * (1 - p)) 0
        (p * g₂ * p - (1 - p) * g₁ * (1 - p)) := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    congr 1 <;> (simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, pp, pp', gh', one_mul, mul_one]; abel)
  have d := congrArg det e
  have dσ := congrArg det hσ
  rw [det_mul, det_one] at dσ
  rw [det_mul, det_mul, det_fromBlocks_zero₂₁, det_diag pp g₂ hg₁, det_mul, det_mul, det_right pp,
    ← det_left pp, mul_right_comm, dσ, one_mul] at d
  rw [d]
  linear_combination (g₁.det * g₂.det * ((p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det *
    (p * (h₂ * g₁) + (1 - p)).det)) * det_sign pp

theorem detPlus_identities : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 →
    (∀ g : Matrix ι ι ℂ, gᴴ * s * g = s → dP s g⁻¹ = star (dP s g) ∧
      ((1 / 2 : ℂ) • (1 + gᴴ * g)).det = dP s g * dP s g⁻¹) ∧
    ∀ g₁ g₂ : Matrix ι ι ℂ, g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s →
      (Matrix.fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
        ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂))).det =
        dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁) := by
  intro ι _ _ s hs ss
  obtain ⟨p, hp⟩ : ∃ p : Matrix ι ι ℂ, p = (1 / 2 : ℂ) • (1 + s) := ⟨_, rfl⟩
  have pp : p * p = p := by
    rw [hp]
    simp only [smul_mul_smul_comm, mul_add, add_mul, ss, one_mul, mul_one]
    module
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have hpH : pᴴ = p := by
    rw [hp, conjTranspose_smul, conjTranspose_add, conjTranspose_one, hs]; simp
  have hsp : s = p - (1 - p) := by rw [hp]; module
  have hd : ∀ g, dP s g = (p * g + (1 - p)).det := fun g => by
    unfold dP
    rw [hp, smul_mul_assoc]
    congr 1
    module
  have key : ∀ g : Matrix ι ι ℂ, gᴴ * s * g = s → g⁻¹ * g = 1 ∧ gᴴ = s * g⁻¹ * s := fun g hg => by
    have h1 : s * gᴴ * s * g = 1 := by rw [mul_assoc s, mul_assoc s, hg, ss]
    rw [inv_eq_left_inv h1]
    refine ⟨h1, ?_⟩
    simp only [← mul_assoc, ss, one_mul]
    rw [mul_assoc, ss, mul_one]
  have ds := det_sign pp
  simp only [hd]
  refine ⟨fun g hg => ?_, fun g₁ g₂ hg₁ hg₂ => ?_⟩
  · obtain ⟨h1, h2⟩ := key g hg
    generalize g⁻¹ = h at h1 h2
    have dh := congrArg det h1
    rw [det_mul, det_one] at dh
    constructor
    · rw [← det_conjTranspose, conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hpH, h2]
      have : s * h * s * p + (1 - p) = s * (h * p + (1 - p)) * s := by
        rw [hsp]
        simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
      rw [this, det_mul, det_mul, det_right pp, ← det_left pp, hsp, mul_right_comm, ds, one_mul]
    · rw [h2, hsp, half_eq pp h1, det_mul, det_mul, det_diag pp g h1]
      linear_combination ((p * g + (1 - p)).det * (p * h + (1 - p)).det) * (h.det * g.det) * ds +
        ((p * g + (1 - p)).det * (p * h + (1 - p)).det) * dh
  · obtain ⟨a1, a2⟩ := key g₁ hg₁
    obtain ⟨b1, b2⟩ := key g₂ hg₂
    generalize g₁⁻¹ = h₁ at a1 a2
    generalize g₂⁻¹ = h₂ at b1 b2
    have da := congrArg det a1
    have db := congrArg det b1
    rw [det_mul, det_one] at da db
    have e : Matrix.fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
        ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂)) =
        fromBlocks (s * h₁) 0 0 (s * h₂) *
          fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
            (p * g₂ * p - (1 - p) * g₂ * (1 - p)) := by
      rw [fromBlocks_multiply, a2, b2, hsp, half_eq pp a1, half_eq pp b1]
      simp only [Matrix.zero_mul, add_zero, zero_add]
      congr 1
      · rw [← half_add_self ((p - (1 - p)) * h₁ * (p * g₂))]
        congr 1
        simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp', one_mul, mul_one]; abel
      · rw [← half_add_self ((p - (1 - p)) * h₂ * (-((1 - p) * g₁)))]
        congr 1
        simp only [mul_sub, sub_mul, mul_neg, mul_assoc, pp', one_mul, mul_one]; abel
    rw [e, det_mul, det_fromBlocks_zero₂₁, det_block pp a1 b1, det_mul, det_mul, hsp]
    generalize (p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det * (p * (h₂ * g₁) + (1 - p)).det = T
    linear_combination T * (h₁.det * g₁.det) * (h₂.det * g₂.det) * ds + T * (h₂.det * g₂.det) * da + T * db

end GlobalTheory.RealWeil.PosDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQCoeffIffHasQExpansion
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion (N : ℕ) (f : ℍ → ℂ) (φ : PowerSeries ℂ) :
    _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n φ) ↔
      _root_.GlobalTheory.HasQExpansion (N : ℝ) f φ := by
  rw [_root_.GlobalTheory.QFam.hasQ_iff]
  unfold _root_.GlobalTheory.HasQExpansion
  simp only [Function.Periodic.qParam, Complex.ofReal_natCast]

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem HasQ.coeff_unique {N : ℕ} {f : ℍ → ℂ} {a b : ℕ → ℂ} (hN : 0 < N) (ha : HasQ N f a)
    (hb : HasQ N f b) : a = b := by
  have toSeries : ∀ c : ℕ → ℂ, HasQ N f c → GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk c) := by
    intro c hc τ
    have hs := (hasQ_iff N f c).1 hc τ
    simpa [PowerSeries.coeff_mk, Function.Periodic.qParam] using hs
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hab := GlobalTheory.HasQExpansion.unique hN' (toSeries a ha) (toSeries b hb)
  funext n
  simpa using congrArg (PowerSeries.coeff n) hab

theorem HasQ.fun_unique {N : ℕ} {f g : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g a) :
    f = g := by
  funext τ
  exact (hf τ).unique (hg τ)

theorem hasQ_unique_both :
    (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧
    (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) :=
  ⟨fun _ _ _ _ hN ha hb => HasQ.coeff_unique hN ha hb, fun _ _ _ _ hf hg => HasQ.fun_unique hf hg⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

theorem HasQ.add {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ + g τ) (fun n => a n + b n) := by
  intro τ
  simpa only [add_mul] using (hf τ).add (hg τ)

theorem HasQ.sub {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ - g τ) (fun n => a n - b n) := by
  intro τ
  simpa only [sub_mul] using (hf τ).sub (hg τ)

theorem HasQ.const_mul {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (c : ℂ) (hf : HasQ N f a) :
    HasQ N (fun τ => c * f τ) (fun n => c * a n) := by
  intro τ
  simpa only [mul_assoc] using (hf τ).mul_left c

theorem HasQ.const (N : ℕ) (c : ℂ) :
    HasQ N (fun _ => c) (fun n => if n = 0 then c else 0) := by
  intro τ
  have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) 0
    (fun m hm => by simp [hm])
  simpa using h

theorem HasQ.sum {N : ℕ} {κ : Type*} (s : Finset κ) {f : κ → ℍ → ℂ} {a : κ → ℕ → ℂ}
    (h : ∀ k ∈ s, HasQ N (f k) (a k)) :
    HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n) := by
  intro τ
  simpa only [Finset.sum_mul] using hasSum_sum fun k hk => h k hk τ

theorem hasQ_linear : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by
  intro N
  exact ⟨fun f g a b hf hg => hf.add hg, fun f g a b hf hg => hf.sub hg,
    fun c f a hf => hf.const_mul c, fun c => HasQ.const N c, fun κ s f a h => HasQ.sum s h⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulLevelSubstPow
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem hasQ_mul_spread : ∀ (N M : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → 0 < M → HasQ N f a →
    HasQ (N * M) f (spread M a) := by
  intro N M f a hN hM h τ
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hinj : Function.Injective (fun k : ℕ => M * k) := fun x y hxy =>
    Nat.eq_of_mul_eq_mul_left hM hxy
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro n hn
    simp only [spread]
    rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hn ⟨k, rfl⟩
  · convert h τ using 1
    funext k
    simp only [Function.comp, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left k hM]
    congr 2
    push_cast
    field_simp

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

private lemma hasSum_conv_mul_of_multiplicative {a b : ℕ → ℂ} {e : ℕ → ℂ} {x y : ℂ}
    (he : ∀ m n, e (m + n) = e m * e n)
    (ha : HasSum (fun n => a n * e n) x) (hb : HasSum (fun n => b n * e n) y) :
    HasSum (fun n => conv a b n * e n) (x * y) := by
  have hna : Summable fun n => ‖a n * e n‖ := summable_norm_iff.mpr ha.summable
  have hnb : Summable fun n => ‖b n * e n‖ := summable_norm_iff.mpr hb.summable
  have hS : HasSum (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (a p.1 * e p.1) * (b p.2 * e p.2)) (x * y) := by
    rw [← ha.tsum_eq, ← hb.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb).of_norm.hasSum
  convert hS using 1
  funext n
  rw [conv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, he]
  ring

private lemma mvExp_add_character_germs (N : ℕ) (τ : ℍ) (m n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m + n : ℕ) : ℂ) * τ / N) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / N) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / N) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem HasQ.mul_conv {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ * g τ) (conv a b) :=
  fun τ => hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

theorem hasQ_mul_conv : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b →
    HasQ N (fun τ => f τ * g τ) (conv a b) := by
  intro N f g a b _ hf hg τ
  exact hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQVadd
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem hasQ_vadd : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (b : ℝ), HasQ N f a →
    HasQ N (fun τ => f (b +ᵥ τ))
      (fun n => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N)) := by
  intro N f a b h τ
  have h1 := h (b +ᵥ τ)
  have he : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) =
      fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((b +ᵥ τ : ℍ) : ℂ) / N) := by
    funext n
    rw [UpperHalfPlane.coe_vadd, mul_assoc (a n), ← Complex.exp_add]
    congr 2
    ring
  show HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f (b +ᵥ τ))
  rw [he]
  exact h1

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseDerivativePowerSeriesMulSubstLeibniz
section
open Polynomial

namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

theorem hasse_coe (l : ℕ) (f : R[X]) :
    hasse l (f : PowerSeries R) = ((hasseDeriv l f : R[X]) : PowerSeries R) := by
  ext n
  rw [coeff_hasse, Polynomial.coeff_coe, Polynomial.coeff_coe, hasseDeriv_coeff]

theorem coeff_hasse_congr {l n : ℕ} {φ φ' : PowerSeries R}
    (h : ∀ m ≤ n + l, PowerSeries.coeff m φ = PowerSeries.coeff m φ') :
    PowerSeries.coeff n (hasse l φ) = PowerSeries.coeff n (hasse l φ') := by
  rw [coeff_hasse, coeff_hasse, h _ le_rfl]

theorem coeff_mul_congr {n : ℕ} {φ φ' ψ ψ' : PowerSeries R}
    (h₁ : ∀ m ≤ n, PowerSeries.coeff m φ = PowerSeries.coeff m φ')
    (h₂ : ∀ m ≤ n, PowerSeries.coeff m ψ = PowerSeries.coeff m ψ') :
    PowerSeries.coeff n (φ * ψ) = PowerSeries.coeff n (φ' * ψ') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [h₁ _ (by omega), h₂ _ (by omega)]

theorem hasse_mul (l : ℕ) (φ ψ : PowerSeries R) :
    hasse l (φ * ψ) = ∑ p ∈ Finset.range (l + 1), hasse p φ * hasse (l - p) ψ := by
  ext n
  set M := n + l + 1 with hM
  set f : R[X] := PowerSeries.trunc M φ
  set g : R[X] := PowerSeries.trunc M ψ
  have hf : ∀ m < M, PowerSeries.coeff m φ = PowerSeries.coeff m (f : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hg : ∀ m < M, PowerSeries.coeff m ψ = PowerSeries.coeff m (g : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hpoly : hasse l ((f : PowerSeries R) * (g : PowerSeries R)) =
      ∑ p ∈ Finset.range (l + 1), hasse p (f : PowerSeries R) * hasse (l - p) (g : PowerSeries R) := by
    rw [← Polynomial.coe_mul, hasse_coe, hasseDeriv_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => hasseDeriv i f * hasseDeriv j g) l]
    simp only [hasse_coe]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_hasse_congr (φ' := (f : PowerSeries R) * (g : PowerSeries R)), hpoly, map_sum, map_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpl : p ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    apply coeff_mul_congr
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hf m' (by omega)).symm
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hg m' (by omega)).symm
  · intro m hm
    exact coeff_mul_congr (fun m' hm' => hf m' (by omega)) (fun m' hm' => hg m' (by omega))

end GlobalTheory.PicDiv

namespace GlobalTheory

theorem hasse_mul_subst :
    ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 →
      ((GlobalTheory.PicDiv.hasse l (φ * ψ)).subst a : PowerSeries k) =
        ∑ p ∈ Finset.range (l + 1),
          ((GlobalTheory.PicDiv.hasse p φ).subst a : PowerSeries k) * (GlobalTheory.PicDiv.hasse (l - p) ψ).subst a := by
  intro k _ a φ ψ l ha
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.PicDiv.hasse_mul, ← PowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOneContractionOfEtalePrime
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_contraction_of_etale_prime : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (a : A), a ≠ 0 → algebraMap A (Localization.AtPrime Q) a ∈ P → P.height ≤ 1 →
    (P.comap (algebraMap A (Localization.AtPrime Q))).height = 1 ∧
      P.comap (algebraMap A[X] (Localization.AtPrime Q)) =
        (P.comap (algebraMap A (Localization.AtPrime Q))).map (Polynomial.C : A →+* A[X]) := by
  first | (exact @GlobalTheory.EtaleHeightOne.height_one_and_comap_eq_map_C) | (exact GlobalTheory.EtaleHeightOne.height_one_and_comap_eq_map_C) | (intros; apply GlobalTheory.EtaleHeightOne.height_one_and_comap_eq_map_C  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianNormLift
section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselian_norm_lift : ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (τ : A →+* A), (∀ a, τ (τ a) = a) → IsUnit (2 : A) → (∀ a ∈ I, τ a ∈ I) → ∀ a t₀ : A, IsUnit a → τ a = a → IsUnit t₀ → t₀ * τ t₀ - a ∈ I → ∃ t : A, IsUnit t ∧ t * τ t = a := by
  first | (exact @GlobalTheory.hensel_norm_lift_of_involution) | (exact GlobalTheory.hensel_norm_lift_of_involution) | (intros; apply GlobalTheory.hensel_norm_lift_of_involution <;> assumption)
end

