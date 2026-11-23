module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0221
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddValuationFinExt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per

namespace GlobalTheory.Per.Val

variable {l : ℕ} [Fact l.Prime]


open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.exists_norm_eq (x : _root_.Formalism.BasicNotions.Loc.Om l) (hx : x ≠ 0) :
    ∃ q : ℚ, ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hi hx
  have hn : (minpoly ℚ_[l] x).natDegree ≠ 0 := (minpoly.natDegree_pos hi).ne'
  refine ⟨((minpoly ℚ_[l] x).coeff 0).valuation / (minpoly ℚ_[l] x).natDegree, ?_⟩
  have h1 : ‖x‖ = ‖(minpoly ℚ_[l] x).coeff 0‖ ^ (1 / ((minpoly ℚ_[l] x).natDegree : ℝ)) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l) x
  rw [h1, Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg l)]
  congr 1
  have hn' : ((minpoly ℚ_[l] x).natDegree : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.mem_OL_iff (LL : _root_.Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ _root_.Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by
  haveI := LL.2
  unfold _root_.Formalism.BasicNotions.Loc.OL
  rw [mem_integralClosure_iff]
  have hK : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hnorm : ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ = spectralValue (minpoly ℚ_[l] x) := by
    rw [IntermediateField.minpoly_eq x]; rfl
  rw [hnorm, spectralValue_le_one_iff (minpoly.monic hK)]
  constructor
  · intro hi n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, coeff_map]
    simpa using PadicInt.norm_le_one ((minpoly ℤ_[l] x).coeff n)
  · intro h
    have hl : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hK)
    refine ⟨q, hm, ?_⟩
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, ← eval₂_map, hq]
    exact minpoly.aeval ℚ_[l] x


open Classical in
def vf (x : Om l) : WithTop ℚ := if h : x = 0 then ⊤ else ((exists_norm_eq x h).choose : ℚ)

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem exists_rat_vf_eq_norm_eq_rpow_of_ne_zero {x : _root_.Formalism.BasicNotions.Loc.Om l} (hx : x ≠ 0) :
    ∃ q : ℚ, _root_.GlobalTheory.Per.Val.vf x = q ∧ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) :=
  ⟨_, by simp [_root_.GlobalTheory.Per.Val.vf, hx],
    (_root_.GlobalTheory.Per.Val.exists_norm_eq x hx).choose_spec⟩

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem prime_rpow_neg_le_iff (a b : ℚ) :
    (l : ℝ) ^ (-(a : ℝ)) ≤ (l : ℝ) ^ (-(b : ℝ)) ↔ b ≤ a := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  rw [Real.rpow_le_rpow_left_iff hl, neg_le_neg_iff]
  exact_mod_cast Iff.rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem prime_rpow_neg_inj (a b : ℚ) :
    (l : ℝ) ^ (-(a : ℝ)) = (l : ℝ) ^ (-(b : ℝ)) ↔ a = b := by
  constructor
  · intro h
    exact le_antisymm ((prime_rpow_neg_le_iff b a).1 h.ge) ((prime_rpow_neg_le_iff a b).1 h.le)
  · rintro rfl; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_eq_iff (x : _root_.Formalism.BasicNotions.Loc.Om l) (q : ℚ) :
    _root_.GlobalTheory.Per.Val.vf x = (q : WithTop ℚ) ↔ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  by_cases hx : x = 0
  · subst hx
    simp only [_root_.GlobalTheory.Per.Val.vf, dif_pos, norm_zero, WithTop.top_ne_coe, false_iff]
    exact (Real.rpow_pos_of_pos hl _).ne
  · obtain ⟨a, ha, hn⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
    rw [ha, hn, WithTop.coe_eq_coe, prime_rpow_neg_inj]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_zero : _root_.GlobalTheory.Per.Val.vf (0 : _root_.Formalism.BasicNotions.Loc.Om l) = ⊤ := by
  simp [_root_.GlobalTheory.Per.Val.vf]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.le_vf_iff (x : _root_.Formalism.BasicNotions.Loc.Om l) (q : ℚ) :
    (q : WithTop ℚ) ≤ _root_.GlobalTheory.Per.Val.vf x ↔ ‖x‖ ≤ (l : ℝ) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  by_cases hx : x = 0
  · subst hx
    simp only [_root_.GlobalTheory.Per.Val.vf_zero, le_top, norm_zero, true_iff]
    exact (Real.rpow_pos_of_pos hl _).le
  · obtain ⟨a, ha, hn⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
    rw [ha, hn, WithTop.coe_le_coe, prime_rpow_neg_le_iff]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_mul (x y : _root_.Formalism.BasicNotions.Loc.Om l) :
    _root_.GlobalTheory.Per.Val.vf (x * y) =
      _root_.GlobalTheory.Per.Val.vf x + _root_.GlobalTheory.Per.Val.vf y := by
  by_cases hx : x = 0
  · simp [hx, _root_.GlobalTheory.Per.Val.vf_zero]
  by_cases hy : y = 0
  · simp [hy, _root_.GlobalTheory.Per.Val.vf_zero]
  obtain ⟨a, ha, hna⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
  obtain ⟨b, hb, hnb⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hy
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [ha, hb, ← WithTop.coe_add, _root_.GlobalTheory.Per.Val.vf_eq_iff, norm_mul, hna, hnb,
    ← Real.rpow_add hl]
  push_cast
  ring_nf

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_add (x y : _root_.Formalism.BasicNotions.Loc.Om l) :
    min (_root_.GlobalTheory.Per.Val.vf x) (_root_.GlobalTheory.Per.Val.vf y) ≤
      _root_.GlobalTheory.Per.Val.vf (x + y) := by
  by_cases hxy : x + y = 0
  · simp [hxy, _root_.GlobalTheory.Per.Val.vf_zero]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, ha, hna⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
  obtain ⟨b, hb, hnb⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hy
  obtain ⟨c, hc, hnc⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hxy
  rw [ha, hb, hc, ← WithTop.coe_min, WithTop.coe_le_coe]
  have hmax : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
  rw [hna, hnb, hnc] at hmax
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    rw [max_eq_left ((prime_rpow_neg_le_iff b a).2 h), prime_rpow_neg_le_iff] at hmax
    exact hmax
  · rw [min_eq_right h]
    rw [max_eq_right ((prime_rpow_neg_le_iff a b).2 h), prime_rpow_neg_le_iff] at hmax
    exact hmax

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_one : _root_.GlobalTheory.Per.Val.vf (1 : _root_.Formalism.BasicNotions.Loc.Om l) = 0 := by
  have := (_root_.GlobalTheory.Per.Val.vf_eq_iff (1 : _root_.Formalism.BasicNotions.Loc.Om l) 0).2 (by simp)
  exact_mod_cast this

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_l : _root_.GlobalTheory.Per.Val.vf ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l) = 1 := by
  have h : ‖((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l)‖ = (l : ℝ) ^ (-((1 : ℚ) : ℝ)) := by
    have : ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l) = algebraMap ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l) (l : ℚ_[l]) := by simp
    rw [this, PadicAlgCl.norm_extends, Padic.norm_p]
    simp [Real.rpow_neg_one]
  exact_mod_cast (_root_.GlobalTheory.Per.Val.vf_eq_iff _ 1).2 h

def vOm (l : ℕ) [Fact l.Prime] : AddValuation (Om l) (WithTop ℚ) :=
  AddValuation.of vf vf_zero vf_one vf_add vf_mul

end GlobalTheory.Per.Val

namespace GlobalTheory.Per

end GlobalTheory.Per
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfFrobeniusIterateEqXiMul
section
open Formalism
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem dvd_of_constantCoeff (x : Per.Ainf l) (h : WittVector.constantCoeff x = 0) :
    (l : Per.Ainf l) ∣ x := by
  have h0 := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) x 0
  have hI : (Finset.Iic 0 : Finset ℕ) = {0} := by ext i; simp
  rw [hI, Finset.sum_singleton] at h0
  rw [WittVector.constantCoeff_apply] at h
  simpa [h] using h0

theorem constantCoeff_natCast_mul (x : Per.Ainf l) :
    WittVector.constantCoeff ((l : Per.Ainf l) * x) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem iterate_tm (n : ℕ) (y : Per.Fl l) :
    (⇑(Per.φA l))^[n] (Per.tm y) = Per.tm (y ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, ← pow_mul, ← pow_succ]

theorem smod_iff (m : ℕ) (x y : Per.Ainf l) :
    x ≡ y [SMOD ((Ideal.span {(l : Per.Ainf l)}) ^ m • ⊤ : Submodule (Per.Ainf l) (Per.Ainf l))] ↔
      (l : Per.Ainf l) ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem xi_bar_ne_zero (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) :
    WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) ≠ 0 := by
  set e' := (frobeniusEquiv (Per.Fl l) l).symm e with he'
  have hxi : WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) = ∑ i ∈ Finset.range l, e' ^ i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.MemLoc.xi, map_sum, map_pow, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, he']
  have hpow : e' ^ l = e := by
    have := (frobeniusEquiv (Per.Fl l) l).apply_symm_apply e
    rwa [frobeniusEquiv_apply, ← he'] at this
  intro h0
  rw [hxi] at h0
  have h1 := geom_sum_mul e' l
  rw [h0, zero_mul, hpow] at h1
  have he1 : e = 1 := (sub_eq_zero.1 h1.symm)
  apply he.2
  rw [he1, map_one]
  simp

end GlobalTheory.PeriodSol

namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem exists_step (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) (c : Per.Ainf l) :
    ∃ y : Per.Fl l, (l : Per.Ainf l) ∣
      c + ((⇑(Per.φA l))^[n] (Per.tm y) - GlobalTheory.MemLoc.xi e * Per.tm y) := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  set b := WittVector.constantCoeff c
  have hdeg : (C b - C a * X : (Per.Fl l)[X]).degree < ((l ^ n : ℕ) : WithBot ℕ) := by
    have h1 : (C b - C a * X : (Per.Fl l)[X]).degree ≤ 1 := by compute_degree
    exact lt_of_le_of_lt h1 (by exact_mod_cast hq)
  have hmon : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).Monic := monic_X_pow_add hdeg
  have hnd : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
    omega
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  refine ⟨y, dvd_of_constantCoeff _ ?_⟩
  rw [iterate_tm]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hy
  rw [map_add (f := _), map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
    WittVector.constantCoeff_apply (x := Per.tm _), WittVector.teichmuller_coeff_zero,
    WittVector.teichmuller_coeff_zero]
  rw [← hy]
  ring

theorem exists_start (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) :
    ∃ w₀ : Per.Fl l, w₀ ≠ 0 ∧ w₀ ^ (l ^ n) = WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) * w₀ := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  have hq1 : l ^ n - 1 ≠ 0 := by omega
  have hmon : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).Monic := monic_X_pow_sub_C a hq1
  have hnd : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_X_pow_sub_C _]; exact hq1
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy
  refine ⟨y, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow hq1] at hy
    exact xi_bar_ne_zero e he hy.symm
  · rw [← hy, ← pow_succ, Nat.sub_add_cancel hq.le]

theorem period_solution : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), GlobalTheory.MemLoc.IsEps e →
    ∀ n : ℕ, 0 < n → ∃ w : Per.Ainf l, GlobalTheory.MemLoc.xi e * w ≠ 0 ∧
      (⇑(Per.φA l))^[n] w = GlobalTheory.MemLoc.xi e * w := by
  intro l _ e he n hn
  set ξ := GlobalTheory.MemLoc.xi e
  let Φ : Per.Ainf l →+* Per.Ainf l := Per.φA l ^ n
  have hΦ : ∀ x, (⇑(Per.φA l))^[n] x = Φ x := fun x => by simp [Φ, RingHom.coe_pow]
  let F : Per.Ainf l → Per.Ainf l := fun w => Φ w - ξ * w
  have F_sub : ∀ a b, F (a - b) = F a - F b := fun a b => by simp only [F, map_sub]; ring
  have F_lin : ∀ (m : ℕ) a b, F (a + (l : Per.Ainf l) ^ m * b) = F a + (l : Per.Ainf l) ^ m * F b :=
    fun m a b => by simp only [F, map_add (f := _), map_mul, map_pow, map_natCast]; ring
  have step : ∀ (k : ℕ) (w : Per.Ainf l), ∃ w' : Per.Ainf l,
      (l : Per.Ainf l) ^ (k + 1) ∣ F w →
        (l : Per.Ainf l) ^ (k + 2) ∣ F w' ∧ (l : Per.Ainf l) ^ (k + 1) ∣ w' - w := by
    intro k w
    by_cases hw : (l : Per.Ainf l) ^ (k + 1) ∣ F w
    · obtain ⟨c, hc⟩ := hw
      obtain ⟨y, d, hd⟩ := exists_step e he n hn c
      refine ⟨w + (l : Per.Ainf l) ^ (k + 1) * Per.tm y, fun _ => ⟨⟨d, ?_⟩, ⟨Per.tm y, by ring⟩⟩⟩
      rw [F_lin, hc, ← mul_add]
      have : F (Per.tm y) = (⇑(Per.φA l))^[n] (Per.tm y) - ξ * Per.tm y := by simp only [F, hΦ]
      rw [this, hd]; ring
    · exact ⟨w, fun h => absurd h hw⟩
  choose g hg using step
  obtain ⟨w₀, hw₀, hw₀q⟩ := exists_start e he n hn
  let seq : ℕ → Per.Ainf l := fun k => Nat.rec (Per.tm w₀) (fun k w => g k w) k
  have hseq0 : seq 0 = Per.tm w₀ := rfl
  have hseqS : ∀ k, seq (k + 1) = g k (seq k) := fun k => rfl
  have hF0 : (l : Per.Ainf l) ^ (0 + 1) ∣ F (seq 0) := by
    rw [zero_add, pow_one, hseq0]
    apply dvd_of_constantCoeff
    simp only [F, ← hΦ, iterate_tm, map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
      WittVector.teichmuller_coeff_zero, hw₀q]
    exact sub_self _
  have hF : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ F (seq k) := by
    intro k
    induction k with
    | zero => exact hF0
    | succ k ih => rw [hseqS]; exact (hg k (seq k) ih).1
  have hdiff : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ seq (k + 1) - seq k := fun k => by
    rw [hseqS]; exact (hg k (seq k) (hF k)).2
  have hcau : ∀ m d, (l : Per.Ainf l) ^ m ∣ seq m - seq (m + d) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have h2 : (l : Per.Ainf l) ^ m ∣ seq (m + d + 1) - seq (m + d) :=
        (pow_dvd_pow _ (by omega)).trans (hdiff (m + d))
      have : seq m - seq (m + (d + 1)) = (seq m - seq (m + d)) - (seq (m + d + 1) - seq (m + d)) := by
        rw [← add_assoc]; ring
      rw [this]; exact dvd_sub ih h2
  have hcomp : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := seq) (fun {m n} hmn => by
    rw [smod_iff]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcau m d)
  have hL' : ∀ k, (l : Per.Ainf l) ^ k ∣ seq k - L := fun k => (smod_iff k _ _).1 (hL k)
  have hFL : F L = 0 := by
    refine hcomp.toIsHausdorff.haus (F L) fun k => ?_
    rw [smod_iff, sub_zero]
    obtain ⟨c, hc⟩ := hL' k
    have e1 : L = seq k + (l : Per.Ainf l) ^ k * (-c) := by rw [mul_neg, ← hc]; ring
    rw [e1, F_lin]
    exact dvd_add ((pow_dvd_pow _ (Nat.le_succ k)).trans (hF k)) (dvd_mul_right _ _)
  have hL0 : WittVector.constantCoeff L = w₀ := by
    obtain ⟨c, hc⟩ := hL' 1
    obtain ⟨c', hc'⟩ := hdiff 0
    have e1 : L = Per.tm w₀ + (l : Per.Ainf l) * (c' - c) := by
      rw [pow_one] at hc; rw [zero_add, pow_one] at hc'
      rw [mul_sub, ← hc, ← hc', ← hseq0]; ring
    rw [e1, map_add (f := _), constantCoeff_natCast_mul, add_zero, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  refine ⟨L, fun h0 => ?_, ?_⟩
  · have := congrArg WittVector.constantCoeff h0
    rw [map_mul, map_zero, hL0] at this
    exact mul_ne_zero (xi_bar_ne_zero e he) hw₀ this
  · rw [hΦ]; exact sub_eq_zero.1 hFL

end GlobalTheory.PeriodSol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBeta
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWLBeta

theorem exists_beta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ LL : FinExt l, ∃ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β := by
  intro l _ P AI T LL
  have hz := (GlobalTheory.TiedMu.tied_mu_units l P AI T).2.2.2
  let _ : Algebra ℤ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) :=
    ((algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  let f : ↥(OL LL) →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom).comp (OL LL).val.toRingHom
      commutes' := fun z => by
        show ((algebraMap ℤ_[l] ↥LL.1 z) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1] }
  let g : Ainf l →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)).toRingHom.comp AI.ιA
      commutes' := fun z => by
        show Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)
            (AI.ιA (algebraMap ℤ_[l] (Ainf l) z)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [hz, AlgHom.commutes]
        rfl }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun o w => ?_⟩
  show Algebra.TensorProduct.productMap f g (o ⊗ₜ[ℤ_[l]] w) = _
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  show ((o : ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) * ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] AI.ιA w) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end GlobalTheory.HWLBeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasis
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_tensor_coord_of_basis {k V M : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup M] [Module k M] {d : ℕ} (bV : Module.Basis (Fin d) k V) :
    ∃ Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M), (∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b) ∧
      ∀ z, z = ∑ i, bV i ⊗ₜ[k] Φ z i := by
  classical
  let Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M) :=
    (TensorProduct.congr bV.equivFun (LinearEquiv.refl k M)).trans
      ((TensorProduct.comm k _ _).trans (TensorProduct.piScalarRight k k M (Fin d)))
  have h : ∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b := by
    intro v b i
    simp [Φ]
  refine ⟨Φ, h, fun z => ?_⟩
  apply Φ.injective
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  simp only [h, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Finsupp.single_apply, hij]
  · simp

theorem exists_coord_tensor_dR : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), ∃ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (a : ℤ) (z : V ⊗[Qp] BdR), z ∈ FilV PD (LL := LL) (V := V) a ↔ ∀ i, Φ z i ∈ PD.Fil a) ∧ ∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i)) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV
  obtain ⟨Φ, h, hz⟩ := exists_tensor_coord_of_basis (M := BdR) bV
  refine ⟨Φ, fun a z => ⟨?_, fun H => ?_⟩, fun g z => ?_⟩
  · rintro ⟨w, rfl⟩ i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [AlgebraTensorModule.map_tmul, h]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ b.2
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), Pi.add_apply]
      exact add_mem hx hy
  · rw [hz z]
    refine Submodule.sum_mem _ fun i _ => ⟨bV i ⊗ₜ ⟨Φ z i, H i⟩, ?_⟩
    rw [AlgebraTensorModule.map_tmul]
    rfl
  · have hact : ∀ (v : V) (b : BdR), actVdR PD ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ PD.actdR g b := by
      intro v b
      unfold actVdR
      rw [AlgebraTensorModule.map_tmul]
      rfl
    funext i
    conv_lhs => rw [hz z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_apply]
    simp only [hact, h, Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.smul_def]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionCocycleFiniteLevelLiftStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionCocycle_finite_level_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', c ∉ BD LA' → ∀ r : ℕ, (∀ g, (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T) → ∀ n : ℕ, r ≤ n → ∀ hI' : StableSub LA' (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T), ∃ c' ∈ quotientCocycles LA' _ hI', c' ∉ BQ LA' _ hI' ∧ ∀ h, ∃ t ∈ LA'.T, Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) = (algebraMap O LL ϖ) ^ n • liftD LA' (c h) + (algebraMap O LL ϖ) ^ n • t := by
  first | exact @GlobalTheory.TorsionLevel.exists_cocycle_level | exact GlobalTheory.TorsionLevel.exists_cocycle_level | (intros; apply GlobalTheory.TorsionLevel.exists_cocycle_level <;> assumption)
end

