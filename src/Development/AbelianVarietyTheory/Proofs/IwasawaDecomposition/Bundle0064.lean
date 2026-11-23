module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0006
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPower
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PhiImage

theorem exists_lim_series {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R] (f : ℕ → R) :
    ∃ L : R, ∀ k, p ^ k ∣ (∑ i ∈ Finset.range k, p ^ i * f i) - L := by
  first
  | exact @_root_.GlobalTheory.LimitSeriesPowSmul.target
  | exact _root_.GlobalTheory.LimitSeriesPowSmul.target
  | (apply _root_.GlobalTheory.LimitSeriesPowSmul.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.LimitSeriesPowSmul.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LimitSeriesPowSmul.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LimitSeriesPowSmul.target ..)

theorem approx {R A : Type} [CommRing R] [CommRing A] (ι : R →+* A) (p : ℕ)
    [IsPrecomplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : A)}) A]
    (φ : A → A) (w : A) (h : ∀ y, ∃ (a : R) (z y' : A), φ y = ι a + w * z + p * φ y') (y : A) :
    ∃ (a : R) (z : A), φ y = ι a + w * z := by
  choose a z nx h using h
  obtain ⟨α, hα⟩ := exists_lim_series (p : R) (fun i => a (nx^[i] y))
  obtain ⟨ζ, hζ⟩ := exists_lim_series (p : A) (fun i => z (nx^[i] y))
  have key : ∀ k, φ y = ι (∑ i ∈ Finset.range k, (p : R) ^ i * a (nx^[i] y)) +
      w * (∑ i ∈ Finset.range k, (p : A) ^ i * z (nx^[i] y)) + (p : A) ^ k * φ (nx^[k] y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Function.iterate_succ_apply', map_add (f := _), map_mul,
        map_pow, map_natCast]
      linear_combination ih + (p : A) ^ k * h (nx^[k] y)
  refine ⟨α, ζ, sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {(p : A)}) inferInstance _ fun k => ?_)⟩
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨u, hu⟩ := hα k
  obtain ⟨v, hv⟩ := hζ k
  have hu' := congrArg ι hu
  rw [map_sub, map_mul, map_pow, map_natCast] at hu'
  exact ⟨ι u + w * v + φ (nx^[k] y), by linear_combination key k + hu' + w * hv⟩

theorem geom_sum_one_add {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (x : R) :
    ∃ c : R, ∑ i ∈ Finset.range p, (x + 1) ^ i = p * c + x ^ (p - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (Polynomial.X : Polynomial ℤ) 1
  have h1 := geom_sum_mul (Polynomial.X + 1 : Polynomial ℤ) p
  have h2 : (Polynomial.X : Polynomial ℤ) ^ p = Polynomial.X ^ (p - 1) * Polynomial.X := by
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
  have h3 : ∑ i ∈ Finset.range p, (Polynomial.X + 1 : Polynomial ℤ) ^ i = (p : Polynomial ℤ) * r + Polynomial.X ^ (p - 1) := by
    refine mul_right_cancel₀ Polynomial.X_ne_zero ?_
    rw [one_pow] at hr
    linear_combination h1 + hr + h2
  refine ⟨Polynomial.aeval x r, ?_⟩
  simpa using congrArg (Polynomial.aeval x) h3

variable {l : ℕ} [Fact l.Prime]

theorem phi_xi (e : Per.Fl l) : ∃ c : Per.Ainf l, Per.φA l (xi e) = l * c + mu e ^ (l - 1) := by
  obtain ⟨c, hc⟩ := geom_sum_one_add (Fact.out : l.Prime) (mu e)
  refine ⟨c, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hc, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, mu, sub_add_cancel]
  congr 1
  refine (GlobalTheory.RingIface.phiA_teich l _).trans ?_
  rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem nat_cancel {A : Type} [CommRing A] (f : ℤ_[l] →+* A) (ht : ∀ x : A, (l : A) * x = 0 → x = 0)
    (m : ℕ) (hm : m ≠ 0) (x y : A) (h : (m : A) * x = m * y) : x = y := by
  have h0 : ((m : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast hm
  have h1 := congrArg f (PadicInt.unitCoeff_spec h0)
  rw [map_natCast, map_mul, map_pow, map_natCast] at h1
  have hp : ∀ (k : ℕ) (x : A), (l : A) ^ k * x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact fun x hx => ht x (ih _ (by linear_combination hx))
  refine sub_eq_zero.1 (hp ((m : ℕ) : ℤ_[l]).valuation _ ?_)
  refine ((PadicInt.unitCoeff h0).isUnit.map f).mul_left_cancel ?_
  rw [mul_zero, ← mul_assoc, ← h1]
  linear_combination h

theorem alg_tower (a : Per.Ainf l) :
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) a := (GlobalTheory.RingIface.tower l a).symm

theorem phiA_alg (a : Per.Ainf l) :
    phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem on_span {R P A : Type} [CommRing R] [CommRing P] [Algebra R P] [CommRing A] (B : Subalgebra R P)
    (j : B →+* A) (zR : ℤ_[l] →+* R) (ht : ∀ x : A, (l : A) * x = 0 → x = 0)
    (φ : A →+* A) (φR : R → R) (hφ : ∀ a, φ (j (algebraMap R B a)) = j (algebraMap R B (φR a)))
    (ξ c : R) (w : A) (hξ : j (algebraMap R B (φR ξ)) = l * (j (algebraMap R B c) + w))
    (hB : ∀ s : P, s ∈ B ↔ s ∈ Submodule.span R {y : P | ∃ n : ℕ,
      ((n.factorial : ℕ) : P) * y = algebraMap R P ξ ^ n}) (s : B) :
    ∃ (a : R) (z : A), φ (j s) = j (algebraMap R B a) + w * z := by
  obtain ⟨s, hs⟩ := s
  have hs' := (hB s).1 hs
  induction hs' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, hn⟩ := hy
    have h1 : ((n.factorial : ℕ) : B) * ⟨y, hs⟩ = algebraMap R B ξ ^ n := Subtype.ext (by simpa using hn)
    have h2 := congrArg (fun t => φ (j t)) h1
    simp only [map_mul, map_natCast, map_pow, hφ, hξ] at h2
    obtain ⟨d, hd⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
    have h3 := congrArg ((j.comp (algebraMap R B)).comp zR) hd
    rw [map_mul, map_natCast, map_pow, map_natCast] at h3
    have h4 : φ (j ⟨y, hs⟩) = j (algebraMap R B (zR d)) * (j (algebraMap R B c) + w) ^ n := by
      refine nat_cancel ((j.comp (algebraMap R B)).comp zR) ht _ n.factorial_ne_zero _ _ ?_
      rw [h2, mul_pow, ← h3, mul_assoc]
      rfl
    obtain ⟨u, hu⟩ := sub_dvd_pow_sub_pow (j (algebraMap R B c) + w) (j (algebraMap R B c)) n
    refine ⟨zR d * c ^ n, j (algebraMap R B (zR d)) * u, ?_⟩
    rw [h4, map_mul, map_mul, map_pow, map_pow]
    linear_combination j (algebraMap R B (zR d)) * hu
  | zero => exact ⟨0, 0, by
      have : (⟨0, hs⟩ : B) = 0 := rfl
      simp [this]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, z, h⟩ := ihx ((hB x).2 hx)
    obtain ⟨a', z', h'⟩ := ihy ((hB y).2 hy)
    have : (⟨x + y, hs⟩ : B) = ⟨x, (hB x).2 hx⟩ + ⟨y, (hB y).2 hy⟩ := rfl
    refine ⟨a + a', z + z', ?_⟩
    rw [this, map_add (f := _), map_add (f := _), h, h', map_add (f := _), map_add (f := _)]
    ring
  | smul r x hx ihx =>
    obtain ⟨a, z, h⟩ := ihx ((hB x).2 hx)
    have : (⟨r • x, hs⟩ : B) = algebraMap R B r * ⟨x, (hB x).2 hx⟩ := Subtype.ext (Algebra.smul_def r x)
    refine ⟨φR r * a, j (algebraMap R B (φR r)) * z, ?_⟩
    rw [this, map_mul, map_mul, h, hφ, map_mul, map_mul]
    ring

end GlobalTheory.MemLoc.PhiImage

namespace GlobalTheory.MemLoc
open PhiImage

theorem phiA_mem_ainf_add : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ w : Per.Acris l, (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) → ∀ y : Per.Acris l, ∃ (a : Per.Ainf l) (z : Per.Acris l), phiA l y = algebraMap (Per.Ainf l) (Per.Acris l) a + w * z := by
  intro l _ e he w hw
  obtain ⟨hc, ht, hd, -⟩ := acris_basic l
  obtain ⟨c, hc'⟩ := phi_xi e
  haveI : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) := WittVector.isAdicCompleteIdealSpanP
  refine approx (algebraMap (Per.Ainf l) (Per.Acris l)) l (phiA l) w fun y => ?_
  obtain ⟨s, y', hy⟩ := hd y 1
  obtain ⟨a, z, h⟩ := on_span (l := l) (Per.Acris0 l) (algebraMap (Per.Acris0 l) (Per.Acris l)) (Per.zA l) ht
    (phiA l) (Per.φA l) (fun a => by rw [alg_tower, alg_tower, phiA_alg]) (xi e) c w
    (by rw [alg_tower, alg_tower, hc', map_add (f := _), map_mul, map_natCast, map_pow, mul_add, hw])
    (mem_Acris0_iff_span l e he) s
  refine ⟨a, z, y', ?_⟩
  rw [hy, map_add (f := _), h, alg_tower, pow_one, map_mul, map_natCast]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqExpLocalChart
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.ExpBallSandwich

section Matrices
variable {n : Type} [Fintype n] [DecidableEq n]

noncomputable def sumAbs (M : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

omit [DecidableEq n] in
theorem sumAbs_nonneg (M : Matrix n n ℂ) : 0 ≤ sumAbs M := by
  unfold sumAbs; positivity

omit [DecidableEq n] in
theorem sumAbs_add_le (A B : Matrix n n ℂ) : sumAbs (A + B) ≤ sumAbs A + sumAbs B := by
  unfold sumAbs
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

omit [DecidableEq n] in
theorem sumAbs_neg (A : Matrix n n ℂ) : sumAbs (-A) = sumAbs A := by
  simp [sumAbs]

omit [DecidableEq n] in
theorem sumAbs_mul_le (A B : Matrix n n ℂ) : sumAbs (A * B) ≤ sumAbs A * sumAbs B := by
  first
  | exact @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le
  | exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le
  | (apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le ..)

section Op
open scoped Matrix.Norms.Operator

theorem row_le_op (M : Matrix n n ℂ) (i : n) : ∑ j, ‖M i j‖ ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have := Finset.le_sup (f := fun i : n => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have h2 : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ _ := NNReal.coe_le_coe.2 this
  simpa using h2

theorem op_le_sumAbs (M : Matrix n n ℂ) : ‖M‖ ≤ sumAbs M := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i : n => ∑ j, ‖M i j‖₊) ≤ ∑ i, ∑ j, ‖M i j‖₊ :=
    Finset.sup_le fun i _ => Finset.single_le_sum (f := fun l => ∑ j, ‖M l j‖₊)
          (fun l _ => by positivity) (Finset.mem_univ i)
  have h2 := NNReal.coe_le_coe.2 this
  simpa [sumAbs] using h2

theorem sumAbs_le_op (M : Matrix n n ℂ) : sumAbs M ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  unfold sumAbs
  calc _ ≤ ∑ _i : n, ‖M‖ := Finset.sum_le_sum fun i _ => row_le_op M i
    _ = _ := by simp

theorem exp_strict (η : ℝ) (hη : 0 < η) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ A B : Matrix n n ℂ,
    sumAbs A < ρ → sumAbs B < ρ →
    sumAbs (NormedSpace.exp A - NormedSpace.exp B - (A - B)) ≤ η * sumAbs (A - B) := by
  have h := (hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)).isLittleO
  have hc : 0 < η / ((Fintype.card n : ℝ) + 1) := by positivity
  have h2 := h.def hc
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨ρ, hρ, h3⟩ := h2
  refine ⟨ρ, hρ, fun A B hA hB => ?_⟩
  have h4 := @h3 (A, B) (by
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
    exact max_lt ((op_le_sumAbs A).trans_lt hA) ((op_le_sumAbs B).trans_lt hB))
  simp only [ContinuousLinearMap.one_apply] at h4
  have h5 := op_le_sumAbs (A - B)
  have h6 := sumAbs_nonneg (A - B)
  calc _ ≤ _ := sumAbs_le_op _
    _ ≤ (Fintype.card n : ℝ) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        refine mul_le_mul_of_nonneg_left (h4.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h5 hc.le
    _ ≤ ((Fintype.card n : ℝ) + 1) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        gcongr; linarith
    _ = _ := by field_simp

end Op

theorem defect_le (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ X Y Z : Matrix n n ℂ,
    sumAbs X < ρ → sumAbs Y < ρ → sumAbs Z < ρ →
    NormedSpace.exp Y = NormedSpace.exp X * NormedSpace.exp Z →
    sumAbs (Y - X - Z) ≤ η * sumAbs (Y - X) + 3 * η * sumAbs Z := by
  obtain ⟨ρ, hρ, h⟩ := exp_strict (n := n) η hη
  refine ⟨min ρ (η / 2), by positivity, fun X Y Z hX hY hZ he => ?_⟩
  rw [lt_min_iff] at hX hY hZ
  have h0 : sumAbs (0 : Matrix n n ℂ) < ρ := by simpa [sumAbs] using hρ
  have key : ∀ W : Matrix n n ℂ, sumAbs W < ρ →
      sumAbs (NormedSpace.exp W - 1 - W) ≤ η * sumAbs W ∧
      sumAbs (NormedSpace.exp W - 1) ≤ 2 * sumAbs W := by
    intro W hW
    have h1 := h W 0 hW h0
    rw [NormedSpace.exp_zero, sub_zero] at h1
    refine ⟨h1, ?_⟩
    have h2 := sumAbs_add_le (NormedSpace.exp W - 1 - W) W
    rw [sub_add_cancel] at h2
    have := sumAbs_nonneg W
    nlinarith
  have e : Y - X - Z = -(NormedSpace.exp Y - NormedSpace.exp X - (Y - X)) +
      ((NormedSpace.exp Z - 1 - Z) + (NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) := by
    rw [he]; noncomm_ring
  have a1 := h Y X hY.1 hX.1
  have a2 := (key Z hZ.1).1
  have a3 := (key Z hZ.1).2
  have a4 : sumAbs (NormedSpace.exp X - 1) ≤ η := by linarith [(key X hX.1).2, hX.2]
  have a5 : sumAbs ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) ≤ η * (2 * sumAbs Z) :=
    (sumAbs_mul_le _ _).trans (mul_le_mul a4 a3 (sumAbs_nonneg _) hη.le)
  rw [e]
  refine (sumAbs_add_le _ _).trans ?_
  rw [sumAbs_neg]
  have a6 := sumAbs_add_le (NormedSpace.exp Z - 1 - Z)
    ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1))
  linarith

end Matrices

end GlobalTheory.ExpBallSandwich
end

