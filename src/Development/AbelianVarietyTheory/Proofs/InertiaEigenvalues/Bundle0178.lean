module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0167

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentCharactersEqAndFrobeniusStable
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

end Descent

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma actD_apply_shift_eq_zero_of_apply_eq_zero {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (g : _root_.GlobalTheory.BK.TameGal K l e a) {x : P.D} {σ : ZMod a}
    (hx : x σ = 0) : Δ.actD g x (σ + g.shift) = 0 := by
  classical
  set f : ZMod a → K⟦X⟧ := fun ρ => if ρ = σ then 0 else 1 with hf
  have hfx : f • _root_.GlobalTheory.BK.cst x = _root_.GlobalTheory.BK.cst x := by
    apply funext; intro ρ; apply funext; intro i
    show f ρ * PowerSeries.C (x ρ i) = PowerSeries.C (x ρ i)
    by_cases h : ρ = σ
    · simp [h, hx]
    · simp [hf, h]
  have key : Δ.actD g x = _root_.GlobalTheory.BK.red (Δ.act g (_root_.GlobalTheory.BK.cst x)) := rfl
  rw [key, ← hfx, _root_.GlobalTheory.BK.Descent.act_smul_tot]
  funext i
  show constantCoeff ((_root_.GlobalTheory.BK.ringAct g f (σ + g.shift)) *
    (Δ.act g (_root_.GlobalTheory.BK.cst x)) (σ + g.shift) i) = 0
  rw [_root_.GlobalTheory.BK.ringAct_apply]
  simp [hf]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma actD_apply_shift_eq_of_apply_eq {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (g : _root_.GlobalTheory.BK.TameGal K l e a) {x y : P.D} {σ : ZMod a}
    (h : x σ = y σ) : Δ.actD g x (σ + g.shift) = Δ.actD g y (σ + g.shift) := by
  have hxy := actD_apply_shift_eq_zero_of_apply_eq_zero Δ g (x := x - y) (σ := σ) (by simp [h])
  rwa [map_sub, Pi.sub_apply, sub_eq_zero] at hxy

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma tameGal_inertia_root_pow (ζ : rootsOfUnity e K) (n : ℕ) (τ : ZMod a) :
    (_root_.GlobalTheory.BK.TameGal.inertia (l := l) (ζ ^ n)).root τ =
      (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, map_one, pow_zero]
    exact _root_.GlobalTheory.BK.TameGal.root_one τ
  | succ n ih =>
    rw [pow_succ, map_mul, _root_.GlobalTheory.BK.TameGal.root_mul,
      _root_.GlobalTheory.BK.TameGal.shift_inertia, sub_zero, ih, pow_succ]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma chars_succ_subset_chars {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (τ : ZMod a) :
    Δ.chars (τ + 1) ⊆ Δ.chars τ := by
  rintro c ⟨x, hx0, hx⟩
  set F : _root_.GlobalTheory.BK.TameGal K l e a := _root_.GlobalTheory.BK.TameGal.fr with hF
  have hFs : F.shift = 1 := _root_.GlobalTheory.BK.TameGal.shift_fr
  have hFis : (F⁻¹).shift = -1 := by
    have hs := _root_.GlobalTheory.BK.TameGal.shift_mul F⁻¹ F
    rw [inv_mul_cancel, _root_.GlobalTheory.BK.TameGal.shift_one, hFs] at hs
    linear_combination -hs
  refine ⟨Δ.actD F⁻¹ x, fun h => hx0 ?_, fun ζ => ?_⟩
  · have hb := actD_apply_shift_eq_of_apply_eq Δ F (x := Δ.actD F⁻¹ x) (y := 0) (σ := τ)
      (by rw [h]; rfl)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
      map_zero, hFs] at hb
  · have hcomm : _root_.GlobalTheory.BK.TameGal.inertia ζ * F⁻¹ =
        F⁻¹ * _root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hF,
        _root_.GlobalTheory.BK.TameGal.fr_mul_inertia, mul_assoc, mul_inv_cancel, mul_one]
    have hroot : (_root_.GlobalTheory.BK.TameGal.inertia (l := l) (ζ ^ l)).root (τ + 1) ^ c.val =
        (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val := by
      rw [tameGal_inertia_root_pow, ← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]
    have hb := actD_apply_shift_eq_of_apply_eq Δ F⁻¹ (σ := τ + 1)
      (x := Δ.actD (_root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l)) x)
      (y := (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val • x)
      (by rw [hx, hroot]; rfl)
    rw [hFis, add_neg_cancel_right, map_smul] at hb
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hb,
      Pi.smul_apply]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma prime_mul_mem_chars_succ_of_mem [NeZero e] {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) {τ : ZMod a} {c : ZMod e}
    (hc : c ∈ Δ.chars τ) :
    (l : ZMod e) * c ∈ Δ.chars (τ + 1) := by
  obtain ⟨d, hd0, hd⟩ := hc
  refine ⟨P.phiD d, fun h => hd0 ?_, fun ζ => ?_⟩
  · have heq : P.phiD (Function.update (0 : P.D) τ (d τ)) = P.phiD 0 := by
      funext σ
      rw [_root_.GlobalTheory.BK.PhiMod.phiD_apply, map_zero]
      by_cases hσ : σ - 1 = τ
      · obtain rfl := eq_add_of_sub_eq hσ
        rw [add_sub_cancel_right, Function.update_self, Pi.zero_apply]
        rw [_root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right] at h
        exact h
      · simp [Function.update_of_ne hσ]
    simpa using congrFun (P.phiD.injective heq) τ
  · rw [_root_.GlobalTheory.BK.Descent.actD_phiD, _root_.GlobalTheory.BK.PhiMod.phiD_apply,
      _root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right, hd, mulVec_smul]
    congr 1
    have hr : (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ =
        (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root (τ + 1) ^ l := by
      rw [← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]
    have he := _root_.GlobalTheory.BK.TameGal.root_pow
      (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ) (τ + 1)
    rw [hr, ← pow_mul, pow_eq_pow_mod _ he, pow_eq_pow_mod ((l : ZMod e) * c).val he,
      ZMod.val_mul, ZMod.val_natCast, Nat.mod_mod, Nat.mod_mul_mod]


open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
theorem _root_.GlobalTheory.BK.chars_eq_and_mul_mem (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K]
    [_root_.GlobalTheory.BK.IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a]
    (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) (Δ : _root_.GlobalTheory.BK.Descent P) :
    (∀ τ σ, Δ.chars τ = Δ.chars σ) ∧
      ∀ τ, ∀ c ∈ Δ.chars τ,
        (l : ZMod e) * c ∈ Δ.chars τ := by
  have hle : ∀ (τ : ZMod a) (n : ℕ),
      Δ.chars (τ + n) ⊆ Δ.chars τ := by
    intro τ n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [← add_assoc]
      exact (chars_succ_subset_chars Δ _).trans ih
  have hsub : ∀ τ σ : ZMod a,
      Δ.chars τ ⊆ Δ.chars σ := by
    intro τ σ
    have hs := hle σ (τ - σ).val
    rwa [ZMod.natCast_zmod_val, add_sub_cancel] at hs
  exact ⟨fun τ σ => (hsub τ σ).antisymm (hsub σ τ),
    fun τ c hc => hsub (τ + 1) τ (prime_mul_mem_chars_succ_of_mem Δ hc)⟩

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
section
noncomputable section

open Formalism.Per Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable {l : ℕ} [Fact l.Prime]

theorem pw_zero (x : Fl l) : pw 0 x = x := by simp [pw]

theorem pw_succ (k : ℤ) (x : Fl l) : pw (k + 1) x = pw k x ^ l := by
  unfold pw
  rw [add_comm, zpow_add, zpow_one]
  rfl

theorem pw_add (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  unfold pw
  rw [zpow_add]
  rfl

theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_zero]
  | succ n ih => rw [Nat.cast_succ, pw_succ, ih, ← pow_mul, pow_succ]

theorem sh_pow (x : Fl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  unfold sh
  rw [map_pow]; push_cast; rfl

theorem l_pos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
theorem two_le_l : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le

theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  have hl := l_pos (l := l)
  induction k using Int.induction_on with
  | zero => simp [pw_zero]
  | succ k ih =>
    rw [pw_succ, sh_pow, norm_pow, ih, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      zpow_add_one₀ hl.ne']
  | pred k ih =>
    have h1 : pw (-(k : ℤ)) x = pw (-(k : ℤ) - 1) x ^ l := by
      rw [← pw_succ]; congr 1; ring
    rw [h1, sh_pow, norm_pow] at ih
    have h2 : (‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ) - 1))) ^ l = ‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← zpow_add_one₀ hl.ne']
      congr 2; ring
    rw [← h2] at ih
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
      (Fact.out : l.Prime).ne_zero).1 ih

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]; simp

def sz (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (n : ℤ) : ℝ :=
  ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))

theorem norm_term (h j : ℕ) (x : Fl l) (n : ℤ) :
    ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖ = sz l h j ‖sh x‖ n := by
  rw [norm_mul, norm_zpow, norm_sh_pw]; rfl

theorem sz_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) (n : ℤ) : 0 ≤ sz l h j r n :=
  mul_nonneg (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hr _)

theorem sz_mono (h j : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (n : ℤ) :
    sz l h j r n ≤ sz l h j s n :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrs (zpow_nonneg l_pos.le _))
    (zpow_nonneg (norm_nonneg _) _)

theorem tendsto_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (sz l h j r) cofinite (𝓝 0) := by
  have hl := l_pos (l := l)
  have hl2 := two_le_l (l := l)
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · have hb : Tendsto (fun n : ℤ => (l : ℝ) ^ n) atBot (𝓝 0) := by
      have := (tendsto_rpow_atBot_of_base_gt_one (l : ℝ) (by linarith)).comp
        ((tendsto_intCast_atBot_iff (R := ℝ)).2 (tendsto_id (α := ℤ) (x := atBot)))
      refine this.congr fun n => ?_
      simp
    refine squeeze_zero (sz_nonneg h j hr) (fun n => ?_) hb
    unfold sz
    rw [norm_l, inv_zpow', neg_neg]
    exact mul_le_of_le_one_right (zpow_nonneg hl.le _)
      (Real.rpow_le_one hr hr1.le (zpow_nonneg hl.le _))
  · rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
    have h1 : Tendsto (fun n : ℕ => l ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (Fact.out : l.Prime).one_lt
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hr hr1).comp h1
    refine squeeze_zero (fun n => sz_nonneg h j hr _) (fun n => ?_) h2
    simp only [Function.comp, sz]
    rw [norm_l, inv_zpow', neg_neg, zpow_natCast, Nat.cast_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hl.le _)
    have : ((n : ℤ) * h + j : ℤ) = ((n * h + j : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
    refine pow_le_pow_of_le_one hr hr1.le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos ?_)
    nlinarith

theorem summable_lam {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} (hx : ‖sh x‖ < 1) :
    Summable fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_term]
  exact tendsto_sz hh j (norm_nonneg _) hx

theorem bdd_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    BddAbove (Set.range (sz l h j r)) :=
  (tendsto_sz hh j hr hr1).bddAbove_range_of_cofinite

theorem gam_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ gam l h j r :=
  Real.iSup_nonneg (sz_nonneg h j hr)

theorem norm_lam_le {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} {r : ℝ} (hx : ‖sh x‖ ≤ r) (hr : r < 1) :
    ‖lam h j x‖ ≤ gam l h j r := by
  have h0 : 0 ≤ r := (norm_nonneg _).trans hx
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gam_nonneg h j h0) fun n => ?_
  rw [norm_term]
  exact (sz_mono h j (norm_nonneg _) hx n).trans (le_ciSup (bdd_sz hh j h0 hr) n)

theorem lam_shift (h j : ℕ) (x : Fl l) : lam h (j + h) x = l * lam h j x := by
  unfold lam
  rw [← tsum_mul_left, ← (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun n : ℤ => (l : ℂ_[l]) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)))]
  refine tsum_congr fun n => ?_
  have h1 : (n * h + ((j + h : ℕ) : ℤ)) = (n + 1) * h + j := by push_cast; ring
  simp only [Equiv.coe_addRight]
  rw [h1, ← mul_assoc, ← zpow_one_add₀ GlobalTheory.RingBasics.p_ne_zero]
  congr 2; ring

theorem lam_pow (h j k : ℕ) (x : Fl l) : lam h j (x ^ l ^ k) = lam h (j + k) x := by
  unfold lam
  refine tsum_congr fun n => ?_
  rw [← pw_nat, ← pw_add]
  congr 3
  push_cast; ring

end GlobalTheory.PSer.Laws

namespace GlobalTheory.PSer

open Laws

theorem lam_hasSum_norm_le_frob : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l), 1 ≤ h → r < 1 →
    ‖sh x‖ ≤ r → HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) (lam h j x) ∧
      ‖lam h j x‖ ≤ gam l h j r ∧ lam h j (x ^ l ^ h) = (l : ℂ_[l]) * lam h j x ∧
      lam h j (x ^ l) = lam h (j + 1) x := by
  intro l _ h j r x hh hr hx
  refine ⟨(summable_lam hh j (hx.trans_lt hr)).hasSum, norm_lam_le hh j hx hr, ?_, ?_⟩
  · rw [lam_pow, lam_shift]
  · have := lam_pow (l := l) h j 1 x
    rwa [pow_one] at this

end GlobalTheory.PSer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLaws
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem gam_norm_natCast_eq (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  simpa using h

theorem gam_exists_max_of_tendsto (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Filter.Tendsto f Filter.cofinite (nhds 0)) : ∃ n₀, ∀ n, f n ≤ f n₀ := by
  by_cases hall : ∀ n, f n = 0
  · exact ⟨0, fun n => by rw [hall n, hall 0]⟩
  push_neg at hall
  obtain ⟨m, hm⟩ := hall
  have hmpos : 0 < f m := lt_of_le_of_ne (hf0 m) (Ne.symm hm)
  have hev : ∀ᶠ n in Filter.cofinite, f n < f m := hf (Iio_mem_nhds hmpos)
  have hfin : {n | ¬ f n < f m}.Finite := Filter.eventually_cofinite.mp hev
  have hmem : m ∈ hfin.toFinset := by simp
  obtain ⟨n₀, hn₀, hmax⟩ := hfin.toFinset.exists_max_image f ⟨m, hmem⟩
  refine ⟨n₀, fun n => ?_⟩
  by_cases hn : f n < f m
  · exact hn.le.trans (hmax m hmem)
  · exact hmax n (by simpa using hn)

theorem gam_laws : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j r) ∧ (∃ n : ℤ, gam l h j r = ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) ∧ 0 ≤ gam l h j r ∧ (0 < r → 0 < gam l h j r) ∧ gam l h j (r ^ l ^ h) = ‖(l : ℂ_[l])‖ * gam l h j r ∧ ∀ s : ℝ, r < s → s < 1 → gam l h j r < gam l h j s := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := gam_norm_natCast_eq l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 < a := by rw [ha]; positivity

  have key : ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∀ n : ℤ, a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j t) ∧
      (∃ n : ℤ, gam l h j t = a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ))) := by
    intro t ht0 ht1
    set f : ℤ → ℝ := fun n => a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) with hf_def
    have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg ht0 _)
    obtain ⟨n₀, hn₀⟩ := gam_exists_max_of_tendsto f hf0 (_root_.GlobalTheory.psers_terms_tendsto_zero l h j t h1 ht0 ht1)
    have hbdd : BddAbove (Set.range f) := ⟨f n₀, by rintro _ ⟨n, rfl⟩; exact hn₀ n⟩
    have hg : gam l h j t = ⨆ n, f n := rfl
    refine ⟨fun n => ?_, n₀, ?_⟩
    · rw [hg]; exact le_ciSup hbdd n
    · rw [hg]; exact le_antisymm (ciSup_le hn₀) (le_ciSup hbdd n₀)
  obtain ⟨hle, n₀, hn₀⟩ := key r hr0 hr1
  refine ⟨hle, ⟨n₀, hn₀⟩, ?_, ?_, ?_, ?_⟩
  · rw [hn₀]; exact mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg hr0 _)
  · intro hr
    exact lt_of_lt_of_le (mul_pos (zpow_pos ha0 _) (Real.rpow_pos_of_pos hr _)) (hle 0)
  ·
    have hq0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hq1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (by positivity)
    obtain ⟨hle', m₀, hm₀⟩ := key (r ^ l ^ h) hq0 hq1
    have shift : ∀ n : ℤ, a ^ (-n) * (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) =
        a * (a ^ (-(n + 1)) * r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ))) := by
      intro n
      have e1 : (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) = r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ)) := by
        rw [← Real.rpow_natCast r (l ^ h), ← Real.rpow_mul hr0]
        congr 1
        have hl0 : (l : ℝ) ≠ 0 := by positivity
        rw [show ((n + 1) * h + j : ℤ) = (h : ℤ) + (n * h + j) by ring, zpow_add₀ hl0 (h : ℤ) (n * h + j), zpow_natCast, Nat.cast_pow]
      have e2 : a ^ (-n) = a * a ^ (-(n + 1)) := by
        rw [show -n = 1 + (-(n + 1)) by ring, zpow_add₀ ha0.ne', zpow_one]
      rw [e1, e2]; ring
    apply le_antisymm
    · rw [hm₀, shift]
      exact mul_le_mul_of_nonneg_left (hle (m₀ + 1)) ha0.le
    · rw [hn₀]
      have := hle' (n₀ - 1)
      rw [shift, show n₀ - 1 + 1 = n₀ by ring] at this
      exact this
  · intro s hrs hs1
    have hs0 : 0 < s := lt_of_le_of_lt hr0 hrs
    obtain ⟨hles, -⟩ := key s hs0.le hs1
    rw [hn₀]
    refine lt_of_lt_of_le ?_ (hles n₀)
    apply mul_lt_mul_of_pos_left _ (zpow_pos ha0 _)
    exact Real.rpow_lt_rpow hr0 hrs (zpow_pos (by positivity) _)

end GlobalTheory
end

