module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryHaarSmallBallLowerBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.HaarSmallBall

variable {n : ℕ} {ε : Fin n → Bool}

lemma toMK_mem_unitary (k : Formalism.REAL.KG ε) : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  ((Formalism.REAL.mem_KG ε (k : Formalism.REAL.UJ ε)).1 k.2).1

lemma toMK_mul' (a b : Formalism.REAL.KG ε) : toMK (a * b) = toMK a * toMK b := rfl

lemma toMK_inv'' (k : Formalism.REAL.KG ε) : toMK k⁻¹ = star (toMK k) := by
  show ((((k : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    Matrix (Fin n) (Fin n) ℂ) = _
  exact Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem (toMK_mem_unitary k))

lemma norm_entry_le_one (k : Formalism.REAL.KG ε) (i j : Fin n) : ‖toMK k i j‖ ≤ 1 :=
  entry_norm_bound_of_unitary (toMK_mem_unitary k) i j

lemma hs_translate_le (a b : Formalism.REAL.KG ε) (η : ℝ)
    (hη : ∀ i j, ‖toMK b i j - toMK a i j‖ ≤ η) :
    Formalism.REAL.hs (toMK (a⁻¹ * b) - 1) ≤ (n : ℝ) * n * ((n : ℝ) * η) ^ 2 := by
  have hA : star (toMK a) * toMK a = 1 := Unitary.star_mul_self_of_mem (toMK_mem_unitary a)
  have heq : toMK (a⁻¹ * b) - 1 = star (toMK a) * (toMK b - toMK a) := by
    rw [toMK_mul', toMK_inv'', Matrix.mul_sub, hA]
  rw [heq]
  have hent : ∀ i j, ‖(star (toMK a) * (toMK b - toMK a)) i j‖ ≤ (n : ℝ) * η := by
    intro i j
    rw [Matrix.mul_apply]
    calc ‖∑ l, star (toMK a) i l * (toMK b - toMK a) l j‖
        ≤ ∑ l, ‖star (toMK a) i l * (toMK b - toMK a) l j‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin n, η := by
          apply Finset.sum_le_sum
          intro l _
          rw [norm_mul, Matrix.star_apply, norm_star, Matrix.sub_apply]
          calc ‖toMK a l i‖ * ‖toMK b l j - toMK a l j‖ ≤ 1 * η :=
                mul_le_mul (norm_entry_le_one a l i) (hη l j) (norm_nonneg _) zero_le_one
            _ = η := one_mul η
      _ = (n : ℝ) * η := by simp
  unfold Formalism.REAL.hs
  calc ∑ i, ∑ j, ‖(star (toMK a) * (toMK b - toMK a)) i j‖ ^ 2
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, ((n : ℝ) * η) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hent i j) 2
    _ = (n : ℝ) * n * ((n : ℝ) * η) ^ 2 := by simp [Finset.sum_const]; ring

noncomputable def cell (h x : ℝ) : Fin (⌊2 / h⌋₊ + 1) :=
  ⟨min ⌊(x + 1) / h⌋₊ ⌊2 / h⌋₊, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma abs_sub_lt_of_cell_eq {h x y : ℝ} (hh : 0 < h) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hc : cell h x = cell h y) : |x - y| < h := by
  have hx' := abs_le.1 hx
  have hy' := abs_le.1 hy
  have ha0 : 0 ≤ (x + 1) / h := div_nonneg (by linarith) hh.le
  have hb0 : 0 ≤ (y + 1) / h := div_nonneg (by linarith) hh.le
  have hfa : ⌊(x + 1) / h⌋₊ ≤ ⌊2 / h⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hfb : ⌊(y + 1) / h⌋₊ ≤ ⌊2 / h⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hc' : ⌊(x + 1) / h⌋₊ = ⌊(y + 1) / h⌋₊ := by
    have := congrArg Fin.val hc
    simp only [cell, min_eq_left hfa, min_eq_left hfb] at this
    exact this
  have h1 := Nat.floor_le ha0
  have h2 := Nat.lt_floor_add_one ((x + 1) / h)
  have h3 := Nat.floor_le hb0
  have h4 := Nat.lt_floor_add_one ((y + 1) / h)
  rw [hc'] at h1 h2
  have hab : |(x + 1) / h - (y + 1) / h| < 1 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have : (x + 1) / h - (y + 1) / h = (x - y) / h := by ring
  rw [this, abs_div, abs_of_pos hh, div_lt_one hh] at hab
  exact hab

end GlobalTheory.HaarSmallBall

namespace GlobalTheory.HaarSmallBall

variable {n : ℕ} {ε : Fin n → Bool}

noncomputable def roundK (h : ℝ) (k : Formalism.REAL.KG ε) :
    Fin n → Fin n → Fin (⌊2 / h⌋₊ + 1) × Fin (⌊2 / h⌋₊ + 1) :=
  fun i j => (cell h (toMK k i j).re, cell h (toMK k i j).im)

lemma norm_sub_lt_of_round_eq {h : ℝ} (hh : 0 < h) {a b : Formalism.REAL.KG ε}
    (hab : roundK h b = roundK h a) (i j : Fin n) : ‖toMK b i j - toMK a i j‖ ≤ 2 * h := by
  have e := congrFun (congrFun hab i) j
  simp only [roundK, Prod.mk.injEq] at e
  have hre := abs_sub_lt_of_cell_eq hh ((Complex.abs_re_le_norm _).trans (norm_entry_le_one b i j))
    ((Complex.abs_re_le_norm _).trans (norm_entry_le_one a i j)) e.1
  have him := abs_sub_lt_of_cell_eq hh ((Complex.abs_im_le_norm _).trans (norm_entry_le_one b i j))
    ((Complex.abs_im_le_norm _).trans (norm_entry_le_one a i j)) e.2
  calc ‖toMK b i j - toMK a i j‖ ≤ |(toMK b i j - toMK a i j).re| + |(toMK b i j - toMK a i j).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * h := by rw [Complex.sub_re, Complex.sub_im]; linarith

theorem smallBall : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → c * δ ^ D ≤ (muK ε {k | Formalism.REAL.hs (toMK k - 1) ≤ δ}).toReal := by
  intro n ε
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, 0, fun δ hδ _ => ?_⟩
    have hset : {k : Formalism.REAL.KG ε | Formalism.REAL.hs (toMK k - 1) ≤ δ} = Set.univ := by
      ext k; simp [Formalism.REAL.hs, hδ.le]
    rw [hset, measure_univ]; simp
  set C : ℝ := 5 * (n : ℝ) ^ 2 with hC
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hCpos : 0 < C := by positivity
  refine ⟨(C ^ (2 * n * n))⁻¹, by positivity, 2 * n * n, fun δ hδ hδ1 => ?_⟩
  set h : ℝ := δ / (2 * (n : ℝ) ^ 2) with hhdef
  have hh : 0 < h := by positivity
  set B : Set (Formalism.REAL.KG ε) := {k | Formalism.REAL.hs (toMK k - 1) ≤ δ} with hB
  set m : ℕ := ⌊2 / h⌋₊ + 1 with hm
  let R : Formalism.REAL.KG ε → Fin n → Fin n → Fin m × Fin m := roundK (ε := ε) h

  have hfib : ∀ g, muK ε (R ⁻¹' {g}) ≤ muK ε B := by
    intro g
    by_cases hne : (R ⁻¹' {g}).Nonempty
    · obtain ⟨a, ha⟩ := hne
      calc muK ε (R ⁻¹' {g}) ≤ muK ε ((fun x => a⁻¹ * x) ⁻¹' B) := by
            apply measure_mono
            intro b hb
            have hab : R b = R a := by
              rw [Set.mem_preimage, Set.mem_singleton_iff] at ha hb; rw [ha, hb]
            show Formalism.REAL.hs (toMK (a⁻¹ * b) - 1) ≤ δ
            refine (hs_translate_le a b (2 * h) (norm_sub_lt_of_round_eq hh hab)).trans ?_
            have : (n : ℝ) * n * ((n : ℝ) * (2 * h)) ^ 2 = δ ^ 2 := by
              rw [hhdef]; field_simp
            rw [this]; nlinarith
        _ = muK ε B := measure_preimage_mul _ _ _
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp
  have hcov : (1 : ENNReal) ≤
      (Fintype.card (Fin n → Fin n → Fin m × Fin m) : ENNReal) * muK ε B := by
    calc (1 : ENNReal) = muK ε Set.univ := measure_univ.symm
      _ = muK ε (⋃ g, R ⁻¹' {g}) := by
          congr 1; ext k; simp
      _ ≤ ∑ g, muK ε (R ⁻¹' {g}) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _g : Fin n → Fin n → Fin m × Fin m, muK ε B := Finset.sum_le_sum fun g _ => hfib g
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card (Fin n → Fin n → Fin m × Fin m) : ℝ) = (m : ℝ) ^ (2 * n * n) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    push_cast; ring
  have hcovR : (1 : ℝ) ≤ (m : ℝ) ^ (2 * n * n) * (muK ε B).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)) hcov
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hcard, ENNReal.toReal_one] at this
    exact this
  have hmδ : (m : ℝ) * δ ≤ C := by
    have hfl : ((⌊2 / h⌋₊ : ℕ) : ℝ) ≤ 2 / h := Nat.floor_le (by positivity)
    have h2h : 2 / h * δ = 4 * (n : ℝ) ^ 2 := by rw [hhdef]; field_simp; ring
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    calc (m : ℝ) * δ = ((⌊2 / h⌋₊ : ℕ) : ℝ) * δ + δ := by rw [hm]; push_cast; ring
      _ ≤ 2 / h * δ + δ := by nlinarith
      _ ≤ C := by rw [h2h, hC]; nlinarith
  have hpow : ((m : ℝ) * δ) ^ (2 * n * n) ≤ C ^ (2 * n * n) :=
    pow_le_pow_left₀ (by positivity) hmδ _
  have hμ0 : 0 ≤ (muK ε B).toReal := ENNReal.toReal_nonneg
  rw [inv_mul_le_iff₀ (by positivity)]
  calc δ ^ (2 * n * n) ≤ δ ^ (2 * n * n) * ((m : ℝ) ^ (2 * n * n) * (muK ε B).toReal) :=
        le_mul_of_one_le_right (by positivity) hcovR
    _ = ((m : ℝ) * δ) ^ (2 * n * n) * (muK ε B).toReal := by rw [mul_pow]; ring
    _ ≤ C ^ (2 * n * n) * (muK ε B).toReal := mul_le_mul_of_nonneg_right hpow hμ0

end GlobalTheory.HaarSmallBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivRealLinearDirection
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

theorem inK_zero' (ε : Fin n → Bool) : inK ε (0 : Mx n) := by
  refine ⟨?_, ?_⟩
  · show (0 : Mx n)ᴴ * Jm ε + Jm ε * 0 = 0
    simp
  · simp

theorem inK_add'' {ε : Fin n → Bool} {X Y : Mx n} (hX : inK ε X) (hY : inK ε Y) : inK ε (X + Y) := by
  obtain ⟨h1, h2⟩ := hX
  obtain ⟨h3, h4⟩ := hY
  refine ⟨?_, ?_⟩
  · have h1' : Xᴴ * Jm ε + Jm ε * X = 0 := h1
    have h3' : Yᴴ * Jm ε + Jm ε * Y = 0 := h3
    show (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Jm ε + Yᴴ * Jm ε + (Jm ε * X + Jm ε * Y)
        = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
      _ = 0 := by rw [h1', h3', add_zero]
  · rw [Matrix.add_mul, Matrix.mul_add, h2, h4]

theorem inK_sum_real {ε : Fin n → Bool} {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ) (hX : ∀ j, inK ε (X j)) :
    inK ε (∑ j, (c j : ℂ) • X j) := by
  classical
  refine Finset.sum_induction _ (inK ε) (fun _ _ ha hb => inK_add'' ha hb) (inK_zero' ε) ?_
  intro j _
  exact inK_smul_real ε (hX j) (c j)

def entryDer (ε : Fin n → Bool) (k : KG ε) (a b : Fin n) : Mx n →ₗ[ℝ] ℂ where
  toFun Y := ∑ l, toMK k a l * Y l b
  map_add' Y Z := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r Y := by
    simp only [Matrix.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Complex.real_smul]
    ring

def entryDerStar (ε : Fin n → Bool) (k : KG ε) (a b : Fin n) : Mx n →ₗ[ℝ] ℂ where
  toFun Y := star (∑ l, toMK k a l * Y l b)
  map_add' Y Z := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, star_add]
  map_smul' r Y := by
    simp only [Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]
    simp only [star_sum, Finset.mul_sum, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem hasDerivAt_coord_lin {ε : Fin n → Bool} (c : Fin n × Fin n × Bool) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => coord ε c (k * expK ε Y t)) (D k Y) 0 := by
  obtain ⟨a, b, f⟩ := c
  have hent : ∀ (k : KG ε) (Y : Mx n), inK ε Y → HasDerivAt (fun t : ℝ => (toMK (k * expK ε Y t)) a b)
      (∑ l, toMK k a l * Y l b) 0 := by
    intro k Y hY
    have e : (fun t : ℝ => (toMK (k * expK ε Y t)) a b) =
        fun t : ℝ => ∑ l, toMK k a l * (NormedSpace.exp ((t : ℂ) • Y)) l b := by
      funext t; simp only [toMK_mul, toMK_expK hY, Matrix.mul_apply]
    rw [e]
    exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_exp_entry_real Y l b).const_mul _
  cases f
  · refine ⟨fun k => entryDerStar ε k a b, fun k Y hY => ?_⟩
    have h := (hent k Y hY).star
    have e1 : (fun t : ℝ => coord ε (a, b, false) (k * expK ε Y t)) =
        fun t => star ((toMK (k * expK ε Y t)) a b) := by
      funext t; simp [coord]
    rw [e1]; exact h
  · refine ⟨fun k => entryDer ε k a b, fun k Y hY => ?_⟩
    have e1 : (fun t : ℝ => coord ε (a, b, true) (k * expK ε Y t)) =
        fun t => (toMK (k * expK ε Y t)) a b := by
      funext t; simp [coord]
    rw [e1]; exact hent k Y hY

theorem hasDerivAt_mono_lin {ε : Fin n → Bool} (s : List (Fin n × Fin n × Bool)) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => mono ε s (k * expK ε Y t)) (D k Y) 0 := by
  induction s with
  | nil =>
    refine ⟨0, fun k Y _ => ?_⟩
    simpa [mono] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | cons c s ih =>
    obtain ⟨Dc, hc⟩ := hasDerivAt_coord_lin (ε := ε) c
    obtain ⟨Ds, hs⟩ := ih
    refine ⟨fun k => mono ε s k • Dc k + coord ε c k • Ds k, fun k Y hY => ?_⟩
    have h := (hc k Y hY).mul (hs k Y hY)
    have e : (fun t : ℝ => mono ε (c :: s) (k * expK ε Y t)) =
        fun t => coord ε c (k * expK ε Y t) * mono ε s (k * expK ε Y t) := by
      funext t; simp [mono]
    rw [e]
    rw [coord_mul_expK_zero hY, mono_mul_expK_zero hY] at h
    refine h.congr_deriv ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring

theorem hasDerivAt_lin_of_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => φ (k * expK ε Y t)) (D k Y) 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, -, rfl⟩ := hx
    exact hasDerivAt_mono_lin s
  | zero =>
    exact ⟨0, fun k Y _ => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y _ _ hx hy =>
    obtain ⟨D₁, d₁⟩ := hx
    obtain ⟨D₂, d₂⟩ := hy
    exact ⟨D₁ + D₂, fun k Y hY => (d₁ k Y hY).add (d₂ k Y hY)⟩
  | smul a x _ hx =>
    obtain ⟨D, dD⟩ := hx
    exact ⟨a • D, fun k Y hY => by simpa using (dD k Y hY).const_mul a⟩

theorem rder_real_linear {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d)
    {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ) (hX : ∀ j, inK ε (X j)) :
    rder ε [∑ j, (c j : ℂ) • X j] φ = ∑ j, (c j : ℂ) • rder ε [X j] φ := by
  obtain ⟨D, hD⟩ := hasDerivAt_lin_of_mem hφ
  have hr : ∀ (Y : Mx n), inK ε Y → ∀ k, rder ε [Y] φ k = D k Y := by
    intro Y hY k
    rw [rder_cons, rder_nil]
    exact (hD k Y hY).deriv
  funext k
  rw [hr _ (inK_sum_real X c hX) k, Finset.sum_apply]
  have e : (∑ j, (c j : ℂ) • X j) = ∑ j, c j • X j :=
    Finset.sum_congr rfl fun j _ => Complex.coe_smul (c j) (X j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, hr _ (hX j) k, Complex.real_smul, smul_eq_mul]

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpanningLieAlgebraCoefSqBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KGap

theorem entry_sq_le_hs {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖Y i j‖ ^ 2 ≤ Formalism.REAL.hs Y := by
  unfold Formalism.REAL.hs
  calc ‖Y i j‖ ^ 2 ≤ ∑ j', ‖Y i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖Y i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖Y i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖Y i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

theorem hs_nonneg' {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs Y := by
  unfold Formalism.REAL.hs; positivity

theorem sup_norm_sq_le_hs {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ^ 2 ≤ Formalism.REAL.hs Y := by
  have h : ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ≤ Real.sqrt (Formalism.REAL.hs Y) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    exact Real.le_sqrt_of_sq_le (entry_sq_le_hs Y i j)
  calc ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ^ 2 ≤ Real.sqrt (Formalism.REAL.hs Y) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = Formalism.REAL.hs Y := Real.sq_sqrt (hs_nonneg' Y)

theorem spanning_coef_bound : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ C : ℝ, 0 ≤ C ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y := by
  intro n ε r X hX
  let Tm : (Fin r → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun c => Matrix.of.symm (∑ j, (c j : ℂ) • X j)
      map_add' := by
        intro a b; funext i k
        simp [add_smul, Finset.sum_add_distrib, Matrix.sum_apply]
      map_smul' := by
        intro t a; funext i k
        simp [Matrix.sum_apply, Finset.mul_sum, mul_assoc] }
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Tm.rangeRestrict (LinearMap.range_rangeRestrict Tm)
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range Tm).subtype (Submodule.ker_subtype _)
  let L : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin r → ℝ) := g ∘ₗ P
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨r * ‖Lc‖ ^ 2, by positivity, ?_⟩
  intro Y hY
  obtain ⟨c0, hc0⟩ := hX Y hY
  have hYW : Matrix.of.symm Y ∈ LinearMap.range Tm := ⟨c0, by simp [Tm, hc0]⟩
  have hPY : P (Matrix.of.symm Y) = ⟨_, hYW⟩ := by
    have := LinearMap.congr_fun hP ⟨_, hYW⟩
    simpa using this
  refine ⟨L (Matrix.of.symm Y), ?_, ?_⟩
  · have h1 := LinearMap.congr_fun hg (P (Matrix.of.symm Y))
    have h2 : Tm (L (Matrix.of.symm Y)) = Matrix.of.symm Y := by
      have := congrArg Subtype.val h1
      change Tm (g (P (Matrix.of.symm Y))) = _ at this
      change Tm (g (P (Matrix.of.symm Y))) = _
      rw [hPY] at this ⊢
      exact this
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simpa [Tm, Matrix.sum_apply] using h3.symm
  · set v := Matrix.of.symm Y with hv
    have hb : ∀ j, (L v) j ^ 2 ≤ ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := by
      intro j
      have h1 : ‖(L v) j‖ ≤ ‖L v‖ := norm_le_pi_norm (L v) j
      have h2 : ‖L v‖ ≤ ‖Lc‖ * ‖v‖ := Lc.le_opNorm v
      have h3 : |(L v) j| ≤ ‖Lc‖ * ‖v‖ := by
        rw [← Real.norm_eq_abs]; exact h1.trans h2
      rw [← mul_pow]
      exact sq_le_sq' (by linarith [abs_le.mp h3]) (abs_le.mp h3).2
    have hv2 : ‖v‖ ^ 2 ≤ Formalism.REAL.hs Y := sup_norm_sq_le_hs Y
    calc ∑ j, (L v) j ^ 2 ≤ ∑ _j : Fin r, ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := Finset.sum_le_sum fun j _ => hb j
      _ = r * ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := by simp; ring
      _ ≤ r * ‖Lc‖ ^ 2 * Formalism.REAL.hs Y := by gcongr

end GlobalTheory.KGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchmidtCompactUnitarySubOneEqTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory

theorem hs_toMK_sub_one {n : ℕ} (ε : Fin n → Bool) (k : KG ε) :
    Formalism.REAL.hs (toMK k - 1) = 2 * (n : ℝ) - 2 * (Matrix.trace (toMK k)).re := by
  have hu : star (toMK k) * toMK k = 1 := Unitary.star_mul_self_of_mem k.2.1
  have hcol : ∀ j, ∑ i, ‖toMK k i j‖ ^ 2 = (1 : ℝ) := by
    intro j
    have h := congrArg Complex.re (congrFun (congrFun hu j) j)
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Complex.re_sum, Complex.one_re] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  have hentry : ∀ i j, ‖(toMK k - 1) i j‖ ^ 2 =
      ‖toMK k i j‖ ^ 2 + (if i = j then 1 - 2 * (toMK k i j).re else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.sub_apply, Matrix.one_apply_eq, if_pos rfl, Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_sub]
      simp
      ring
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, if_neg hij, sub_zero, add_zero]
  unfold Formalism.REAL.hs
  simp_rw [hentry]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib, hcol]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Matrix.trace, Complex.re_sum]
  simp [Matrix.diag]
  ring

end GlobalTheory
end

