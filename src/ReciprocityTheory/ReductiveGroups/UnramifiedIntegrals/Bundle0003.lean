module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FrobFixNegOne
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section General

variable {R : Type*} [CommRing R] (p : ℕ)

def FrobFix (x : R) : Prop := ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x

variable {p}

theorem frobFix_iter {x : R} {f : ℕ} (h : (p : R) ∣ x ^ (p ^ f) - x) (k : ℕ) :
    (p : R) ∣ x ^ (p ^ (f * (k + 1))) - x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have e : x ^ (p ^ (f * (k + 1 + 1))) = (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) := by
      rw [← pow_mul, ← pow_add]
      congr 2
    rw [e]
    have h1 : (p : R) ∣ (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) - x ^ (p ^ f) :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have h2 := dvd_add h1 h
    rwa [sub_add_sub_cancel] at h2

theorem frobFix_common {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x ∧ (p : R) ∣ y ^ (p ^ f) - y := by
  obtain ⟨f1, hf1, h1⟩ := hx
  obtain ⟨f2, hf2, h2⟩ := hy
  refine ⟨f1 * f2, Nat.mul_pos hf1 hf2, ?_, ?_⟩
  · have h := frobFix_iter h1 (f2 - 1)
    rwa [Nat.sub_add_cancel hf2] at h
  · have h := frobFix_iter h2 (f1 - 1)
    rwa [Nat.sub_add_cancel hf1, mul_comm] at h

theorem frobFix_mul {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) : FrobFix p (x * y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have e : (x * y) ^ (p ^ f) - x * y = x ^ (p ^ f) * (y ^ (p ^ f) - y) + y * (x ^ (p ^ f) - x) := by
    ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)

private theorem frobFix_add_lemma (hp : p.Prime) (x y : R) (n : ℕ) :
    (p : R) ∣ (x + y) ^ (p ^ n) - (x ^ (p ^ n) + y ^ (p ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : (p : R) ∣ ((x + y) ^ (p ^ n)) ^ p - (x ^ (p ^ n) + y ^ (p ^ n)) ^ p :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have hB : (p : R) ∣ (x ^ (p ^ n) + y ^ (p ^ n)) ^ p - ((x ^ (p ^ n)) ^ p + (y ^ (p ^ n)) ^ p) := by
      rw [add_pow_prime_eq hp, add_sub_cancel_left]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have e : ∀ a : R, a ^ (p ^ (n + 1)) = (a ^ (p ^ n)) ^ p := fun a => by
      rw [pow_succ, pow_mul]
    rw [e, e, e]
    have h := dvd_add hA hB
    rwa [sub_add_sub_cancel] at h

theorem frobFix_add (hp : p.Prime) {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    FrobFix p (x + y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have h3 := frobFix_add_lemma hp x y f
  have e : (x + y) ^ (p ^ f) - (x + y) =
      ((x + y) ^ (p ^ f) - (x ^ (p ^ f) + y ^ (p ^ f))) + (x ^ (p ^ f) - x) + (y ^ (p ^ f) - y) := by
    ring
  rw [e]
  exact dvd_add (dvd_add h3 h1) h2

theorem frobFix_neg_one (hp : p.Prime) : FrobFix p (-1 : R) := by
  refine ⟨1, one_pos, ?_⟩
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [show (-1 : R) ^ (2 ^ 1) - -1 = ((2 : ℕ) : R) by push_cast; ring]
  · rw [pow_one, hodd.neg_one_pow, sub_self]
    exact dvd_zero _

theorem frobFix_neg (hp : p.Prime) {x : R} (hx : FrobFix p x) : FrobFix p (-x) := by
  simpa using frobFix_mul (frobFix_neg_one (R := R) hp) hx

theorem frobFix_zero (hp : p.Prime) : FrobFix p (0 : R) :=
  ⟨1, one_pos, by rw [pow_one, zero_pow hp.ne_zero, sub_zero]; exact dvd_zero _⟩

theorem frobFix_one : FrobFix p (1 : R) :=
  ⟨1, one_pos, by simp⟩

theorem frobFix_root (hp : p.Prime) {x : R} {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n)
    (hx : x ^ n = 1) : FrobFix p x := by
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  have htot : p ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop
  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have key : ∀ m, x ^ m = x ^ (m % n) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hx, one_pow, mul_one]
  have hx' : x ^ (p ^ n.totient) = x := by
    rw [key, htot, ← key, pow_one]
  rw [hx', sub_self]
  exact dvd_zero _

end General

variable (l : ℕ) [Fact l.Prime]

theorem rmu_frob (x : ℂ_[l]) (hx : x ∈ Rmu l) :
    ∃ f : ℕ, 0 < f ∧ ∃ r ∈ Rmu l, x ^ (l ^ f) - x = (l : ℂ_[l]) * r := by
  have hp : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Subring.closure (muP l)), FrobFix l (⟨y, hy⟩ : Rmu l) := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨n, hn, hln, hzn⟩ := hz
      exact frobFix_root hp hn hln (Subtype.ext (by simpa using hzn))
    | zero => exact frobFix_zero hp
    | one => exact frobFix_one
    | add a b ha' hb' ha hb =>
      have e : (⟨a + b, Subring.add_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ + ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_add hp ha hb
    | neg a ha' ha =>
      have e : (⟨-a, Subring.neg_mem _ ha'⟩ : Rmu l) = -⟨a, ha'⟩ := Subtype.ext (by simp)
      rw [e]
      exact frobFix_neg hp ha
    | mul a b ha' hb' ha hb =>
      have e : (⟨a * b, Subring.mul_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ * ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_mul ha hb
  obtain ⟨f, hf, r, hr⟩ := key x hx
  refine ⟨f, hf, r, r.2, ?_⟩
  have h := congrArg Subtype.val hr
  simpa using h

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurNewton
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def newtonBall (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rwa [norm_neg]

theorem newton_exists_poly (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    ∃ Q : Polynomial (newtonBall K), Q.map (newtonBall K).subtype = P := by
  have hp : (↑P.coeffs : Set K) ⊆ newtonBall K := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp (Finset.mem_coe.mp hc)
    exact hP i
  exact ⟨P.toSubring (newtonBall K) hp, Polynomial.map_toSubring P (newtonBall K) hp⟩

theorem newton_eval_ball (Q : Polynomial (newtonBall K)) (a : newtonBall K) :
    (Q.map (newtonBall K).subtype).eval (a : K) = ((Q.eval a : newtonBall K) : K) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (newtonBall K).subtype a

theorem newton_expansion (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∃ k : K, ‖k‖ ≤ 1 ∧ P.eval (x + y) = P.eval x + P.derivative.eval x * y + k * y ^ 2 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion Q ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨k, k.2, ?_⟩
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q (⟨x, hx⟩ + ⟨y, hy⟩)
  have e2 := newton_eval_ball Q ⟨x, hx⟩
  have e3 := newton_eval_ball (Polynomial.derivative Q) ⟨x, hx⟩
  rw [Polynomial.derivative_map]
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow] at h e1 e2 e3
  rw [e1, e2, e3, h]

theorem newton_lipschitz (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.evalSubFactor Q ⟨x, hx⟩ ⟨y, hy⟩
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q ⟨x, hx⟩
  have e2 := newton_eval_ball Q ⟨y, hy⟩
  simp only [AddSubgroupClass.coe_sub, Subring.coe_mul] at h e1 e2
  rw [e1, e2, h, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) k.2

theorem newton_derivative_coeff (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (i : ℕ) :
    ‖P.derivative.coeff i‖ ≤ 1 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  rw [Polynomial.derivative_map, Polynomial.coeff_map]
  exact ((Polynomial.derivative Q).coeff i).2

theorem newton_step (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x : K) (hx : ‖x‖ ≤ 1)
    (h0 : ‖P.eval x‖ < 1) (h1 : ‖P.derivative.eval x‖ = 1) :
    ∃ y : K, ‖y‖ ≤ 1 ∧ ‖P.derivative.eval y‖ = 1 ∧ ‖P.eval y‖ ≤ ‖P.eval x‖ ^ 2 ∧
      ‖y - x‖ ≤ ‖P.eval x‖ := by
  have hd : P.derivative.eval x ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  set t : K := -(P.eval x / P.derivative.eval x) with ht
  have hnt : ‖t‖ = ‖P.eval x‖ := by rw [ht, norm_neg, norm_div, h1, div_one]
  have ht1 : ‖t‖ ≤ 1 := hnt ▸ h0.le
  have hy : ‖x + t‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x t).trans (max_le hx ht1)
  obtain ⟨k, hk, he⟩ := newton_expansion P hP x t hx ht1
  refine ⟨x + t, hy, ?_, ?_, ?_⟩
  · have hl := newton_lipschitz P.derivative (newton_derivative_coeff P hP) (x + t) x hy hx
    rw [add_sub_cancel_left, hnt] at hl
    have hlt : ‖P.derivative.eval (x + t) - P.derivative.eval x‖ < ‖P.derivative.eval x‖ := by
      rw [h1]; exact lt_of_le_of_lt hl h0
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, h1] at this
    exact this
  · have hz : P.eval x + P.derivative.eval x * t = 0 := by
      rw [ht]; field_simp; ring
    rw [he, hz, zero_add, norm_mul, norm_pow, hnt]
    exact mul_le_of_le_one_left (by positivity) hk
  · rw [add_sub_cancel_left, hnt]

end Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem newton_root (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x₀ : K) (hx : ‖x₀‖ ≤ 1)
    (h0 : ‖P.eval x₀‖ < 1) (h1 : ‖P.derivative.eval x₀‖ = 1) :
    ∃ x : K, P.eval x = 0 ∧ ‖x - x₀‖ ≤ ‖P.eval x₀‖ := by
  set c : ℝ := ‖P.eval x₀‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  let S : Type := {x : K // ‖x‖ ≤ 1 ∧ ‖P.eval x‖ < 1 ∧ ‖P.derivative.eval x‖ = 1}
  have step : ∀ s : S, ∃ s' : S, ‖P.eval s'.1‖ ≤ ‖P.eval s.1‖ ^ 2 ∧
      ‖s'.1 - s.1‖ ≤ ‖P.eval s.1‖ := by
    intro s
    obtain ⟨y, hy, hy1, hy2, hy3⟩ := newton_step P hP s.1 s.2.1 s.2.2.1 s.2.2.2
    have : ‖P.eval y‖ < 1 :=
      lt_of_le_of_lt hy2 (pow_lt_one₀ (norm_nonneg _) s.2.2.1 two_ne_zero)
    exact ⟨⟨y, hy, this, hy1⟩, hy2, hy3⟩
  choose g hg1 hg2 using step
  let u : ℕ → S := fun n => Nat.rec ⟨x₀, hx, h0, h1⟩ (fun _ s => g s) n
  have hu0 : (u 0).1 = x₀ := rfl
  have hus : ∀ n, u (n + 1) = g (u n) := fun _ => rfl
  have hval : ∀ n, ‖P.eval (u n).1‖ ≤ c * c ^ n := by
    intro n
    induction n with
    | zero => rw [hu0, pow_zero, mul_one]
    | succ n ih =>
      have hle : ‖P.eval (u n).1‖ ≤ c :=
        ih.trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))
      calc ‖P.eval (u (n + 1)).1‖ ≤ ‖P.eval (u n).1‖ ^ 2 := by rw [hus]; exact hg1 _
        _ = ‖P.eval (u n).1‖ * ‖P.eval (u n).1‖ := sq _
        _ ≤ (c * c ^ n) * c := mul_le_mul ih hle (norm_nonneg _) (by positivity)
        _ = c * c ^ (n + 1) := by ring
  have hdist : ∀ n, dist (u n).1 (u (n + 1)).1 ≤ c * c ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, hus]
    exact (hg2 _).trans (hval n)
  have hcau : CauchySeq (fun n => (u n).1) := cauchySeq_of_le_geometric c c h0 hdist
  obtain ⟨x, hxl⟩ := cauchySeq_tendsto_of_complete hcau
  have hnear : ∀ n, ‖(u n).1 - x₀‖ ≤ c := by
    intro n
    induction n with
    | zero => rw [hu0, sub_self, norm_zero]; exact hc0
    | succ n ih =>
      have h2 : ‖(u (n + 1)).1 - (u n).1‖ ≤ c := by
        rw [← dist_eq_norm, dist_comm]
        exact (hdist n).trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))
      have := IsUltrametricDist.norm_add_le_max ((u (n + 1)).1 - (u n).1) ((u n).1 - x₀)
      rw [sub_add_sub_cancel] at this
      exact this.trans (max_le h2 ih)
  refine ⟨x, ?_, ?_⟩
  · have hl1 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds (P.eval x)) :=
      (P.continuous.tendsto x).comp hxl
    have hl2 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm hval
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 h0).const_mul c
      rwa [mul_zero] at this
    exact tendsto_nhds_unique hl1 hl2
  · have hl : Filter.Tendsto (fun n => ‖(u n).1 - x₀‖) Filter.atTop (nhds ‖x - x₀‖) :=
      (hxl.sub_const x₀).norm
    exact le_of_tendsto' hl hnear

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem mem_Tm {m : ℕ} (hm : 0 < m) (t : ℕ × ℕ × ℕ) :
    t ∈ Tm m ↔ t.1 * t.2.2 = m ∧ t.2.1 < t.2.2 := by
  rw [Tm, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at hx
    exact ⟨Nat.mul_div_cancel' hx.1.1, hx.2⟩
  · obtain ⟨a, b, e⟩ := t
    rintro ⟨h1, h2⟩
    simp only at h1 h2
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have he : m / a = e := by rw [← h1, Nat.mul_div_cancel_left _ ha]
    refine ⟨⟨a, b⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
      exact ⟨⟨⟨e, h1.symm⟩, hm.ne'⟩, by rw [he]; exact h2⟩
    · simp only [he]

theorem Tm_pos {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : 0 < t.1 ∧ 0 < t.2.2 := by
  have h := ((mem_Tm hm t).mp ht).1
  have hpos : 0 < t.1 * t.2.2 := h ▸ hm
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩ <;>
    rw [h0] at hpos <;> simp at hpos

theorem pt_coe {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    ((pt a b e τ : ℍ) : ℂ) = ((a : ℂ) * τ + b) / e := by
  have hz : 0 < (((a : ℂ) * τ + b) / e).im := by
    rw [Complex.div_natCast_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
      UpperHalfPlane.coe_im]
    exact div_pos (mul_pos (by exact_mod_cast ha) τ.im_pos) (by exact_mod_cast he)
  unfold pt
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem DD_ne_zero (τ : ℍ) : DD τ ≠ 0 := by
  exact ModularForm.discriminant_ne_zero τ

theorem smul_of_form {k : ℤ} (g : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    g (γ • τ) = denom γ τ ^ k * g τ := by
  have h := SlashInvariantForm.slash_action_eqn'' g (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) τ
  exact h

theorem isMF_AA : IsMF 12 AA := by
  refine ⟨ModularForm.mcast (by norm_num) (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)), fun τ => ?_⟩
  show (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)) τ = AA τ
  rw [ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_mul, Pi.mul_apply]
  unfold AA
  ring

theorem isMF_DD : IsMF 12 DD := by
  first
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩

theorem IsMF.smul_eq {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = denom γ τ ^ k * f τ := by
  obtain ⟨g, hg⟩ := h
  rw [← hg, ← hg]
  exact smul_of_form g γ τ

theorem AA_smul (γ : SL(2, ℤ)) (τ : ℍ) : AA (γ • τ) = denom γ τ ^ 12 * AA τ := by
  exact isMF_AA.smul_eq γ τ

theorem DD_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD (γ • τ) = denom γ τ ^ 12 * DD τ := by
  exact isMF_DD.smul_eq γ τ

theorem jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ := by
  unfold jT
  rw [AA_smul, DD_smul, mul_div_mul_left _ _ (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ τ))]

theorem IsMF.congr_weight {k k' : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (hk : k = k') : IsMF k' f := by
  subst hk
  exact h

theorem IsMF.add {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ + g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' + g', fun τ => by simp [hf', hg']⟩

theorem IsMF.sub {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ - g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' - g', fun τ => by simp [hf', hg']⟩

theorem IsMF.const_mul {k : ℤ} {f : ℍ → ℂ} (c : ℂ) (hf : IsMF k f) : IsMF k (fun τ => c * f τ) := by
  obtain ⟨f', hf'⟩ := hf
  exact ⟨c • f', fun τ => by simp [hf']⟩

theorem IsMF.mul {k k' : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k' g) :
    IsMF (k + k') (fun τ => f τ * g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f'.mul g', fun τ => by rw [ModularForm.coe_mul, Pi.mul_apply, hf', hg']⟩

theorem IsMF.pow {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (n : ℕ) : IsMF (n * k) (fun τ => f τ ^ n) := by
  induction n with
  | zero =>
    refine IsMF.congr_weight (k := 0) ⟨1, fun τ => ?_⟩ (by simp)
    simp
  | succ n ih =>
    have h := (ih.mul hf).congr_weight (show (n : ℤ) * k + k = ((n + 1 : ℕ) : ℤ) * k by push_cast; ring)
    simpa [pow_succ] using h

theorem zetaC_pow_self {m : ℕ} (hm : 0 < m) : zetaC m ^ m = 1 := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I := by field_simp
  rw [this, Complex.exp_two_pi_mul_I]

theorem zetaC_mem (m : ℕ) : zetaC m ∈ Rm m := by
  exact Subring.subset_closure (Set.mem_singleton _)

theorem Rm_isIntegral {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ∈ Rm m) : IsIntegral ℤ x := by
  have hζ : IsIntegral ℤ (zetaC m) :=
    IsIntegral.of_pow hm (by rw [zetaC_pow_self hm]; exact isIntegral_one)
  have hle : Rm m ≤ (integralClosure ℤ ℂ).toSubring :=
    Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hζ)
  exact hle hx

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem latTau_snd_ne (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

theorem latTau_im_ne (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have h2 := latTau_snd_ne L
  obtain ⟨r, hr⟩ : ∃ r : ℝ, L.ω₁ / L.ω₂ = (r : ℂ) :=
    ⟨(L.ω₁ / L.ω₂).re, Complex.ext (by simp) (by simp [h])⟩
  have h1 : L.ω₁ = (r : ℂ) * L.ω₂ := by rw [← hr, div_mul_cancel₀ _ h2]
  have h3 := (LinearIndependent.pair_iff.mp L.indep) 1 (-r)
    (by rw [Complex.real_smul, Complex.real_smul, h1]; push_cast; ring)
  norm_num at h3

theorem latTau (L : PeriodPair) : ∃ (c : ℂ) (τ : ℍ), IsTauOf L c τ := by
  have h2 := latTau_snd_ne L
  rcases lt_or_gt_of_ne (latTau_im_ne L) with hneg | hpos
  · refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by rw [Complex.neg_im]; linarith⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨-u, v, by push_cast; field_simp; try ring⟩
  · refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, hpos⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨u, v, by field_simp; try ring⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

