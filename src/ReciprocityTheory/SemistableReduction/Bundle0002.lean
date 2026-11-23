module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.NormOrdLengthResidue
section
namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem normOrd_mul_mem_iff {B : Type} [CommRing B] [IsDedekindDomain B] {P : Ideal B}
    [hP : P.IsMaximal] {n : ℕ} {a : B} (ha : a ∈ P ^ n) (ha' : a ∉ P ^ (n + 1)) (b : B) :
    b * a ∈ P ^ (n + 1) ↔ b ∈ P := by
  constructor
  · intro h
    by_contra hb
    have hcop : IsCoprime (Ideal.span {b}) (P ^ (n + 1)) := by
      refine IsCoprime.pow_right ?_
      rw [Ideal.isCoprime_iff_sup_eq]
      obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv hb
      rw [Ideal.eq_top_iff_one, ← hyi]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self b)))
        (Ideal.mem_sup_right hi)
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at hcop
    obtain ⟨y, hy, z, hz, hyz⟩ := hcop
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    apply ha'
    have : a = r * (b * a) + z * a := by
      calc a = (r * b + z) * a := by rw [hyz, one_mul]
        _ = r * (b * a) + z * a := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ hz)
  · intro hb
    rw [pow_succ']
    exact Ideal.mul_mem_mul hb ha

theorem normOrd_le_span_sup {B : Type} [CommRing B] [IsDedekindDomain B] {P : Ideal B}
    [hP : P.IsMaximal] (hP0 : P ≠ ⊥) {n : ℕ} {a : B} (ha : a ∈ P ^ n) (ha' : a ∉ P ^ (n + 1)) :
    P ^ n ≤ Ideal.span {a} ⊔ P ^ (n + 1) := by
  classical
  have hPprime : Prime P := Ideal.prime_of_isPrime hP0 hP.isPrime
  set I := Ideal.span {a} ⊔ P ^ (n + 1) with hI
  have hIdvd : I ∣ P ^ (n + 1) := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨k, hk, hassoc⟩ := (dvd_prime_pow hPprime (n + 1)).mp hIdvd
  have hIk : I = P ^ k := associated_iff_eq.mp hassoc
  have hIle : I ≤ P ^ n := sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ha) (Ideal.pow_le_pow_right (Nat.le_succ n))
  have hPnu : ¬ IsUnit P := by rw [Ideal.isUnit_iff]; exact hP.ne_top
  have hnk : n ≤ k := by
    have : P ^ n ∣ P ^ k := Ideal.dvd_iff_le.mpr (hIk ▸ hIle)
    exact (pow_dvd_pow_iff hPprime.ne_zero hPnu).mp this
  rcases Nat.lt_or_ge n k with h | h
  · exfalso
    have hk' : k = n + 1 := by omega
    apply ha'
    have : a ∈ I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)
    rwa [hIk, hk'] at this
  · have : k = n := by omega
    rw [hIk, this]

theorem normOrd_length_succ (O B : Type) [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (P : Ideal B) [hP : P.IsMaximal] (hP0 : P ≠ ⊥) (n : ℕ) :
    length O (B ⧸ P ^ (n + 1)) = length O (B ⧸ P) + length O (B ⧸ P ^ n) := by
  classical
  obtain ⟨a, ha, ha'⟩ : ∃ a ∈ P ^ n, a ∉ P ^ (n + 1) := by
    by_contra hcon
    push_neg at hcon
    have hle : P ^ n ≤ P ^ (n + 1) := hcon
    have hPprime : Prime P := Ideal.prime_of_isPrime hP0 hP.isPrime
    have hPnu : ¬ IsUnit P := by rw [Ideal.isUnit_iff]; exact hP.ne_top
    have := (pow_dvd_pow_iff hPprime.ne_zero hPnu).mp (Ideal.dvd_iff_le.mpr hle)
    omega
  let φ : B →ₗ[B] B ⧸ P ^ (n + 1) := (P ^ (n + 1)).mkQ ∘ₗ LinearMap.mulRight B a
  have hφ : P ≤ LinearMap.ker φ := by
    intro x hx
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, LinearMap.mulRight_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact (normOrd_mul_mem_iff ha ha' x).mpr hx
  let f : B ⧸ P →ₗ[O] B ⧸ P ^ (n + 1) := (P.liftQ φ hφ).restrictScalars O
  let g : B ⧸ P ^ (n + 1) →ₗ[O] B ⧸ P ^ n :=
    (Submodule.factor (Ideal.pow_le_pow_right (Nat.le_succ n) : P ^ (n + 1) ≤ P ^ n)).restrictScalars O
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      have hx' : x * a ∈ P ^ (n + 1) := by
        have := hx
        simp only [f, φ, LinearMap.restrictScalars_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
          LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
        exact this
      exact (Submodule.Quotient.mk_eq_zero _).mpr ((normOrd_mul_mem_iff ha ha' x).mp hx')
  have hg : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      change (Submodule.Quotient.mk x : B ⧸ P ^ n) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Set.mem_range]
      constructor
      · intro hx
        have hx2 := normOrd_le_span_sup hP0 ha ha' hx
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx2
        obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
        refine ⟨Submodule.Quotient.mk r, ?_⟩
        simp only [f, φ, LinearMap.restrictScalars_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
          LinearMap.mulRight_apply, Submodule.mkQ_apply]
        rw [Submodule.Quotient.eq]
        have : r * a - x = -z := by rw [← hyz]; ring
        rw [this]
        exact neg_mem hz
      · rintro ⟨w, hw⟩
        induction w using Submodule.Quotient.induction_on with
        | H r =>
          simp only [f, φ, LinearMap.restrictScalars_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
            LinearMap.mulRight_apply, Submodule.mkQ_apply] at hw
          rw [Submodule.Quotient.eq] at hw
          have hra : r * a ∈ P ^ n := Ideal.mul_mem_left _ _ ha
          have hd : r * a - x ∈ P ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) hw
          have : x = r * a - (r * a - x) := by ring
          rw [this]
          exact Ideal.sub_mem _ hra hd
  exact Module.length_eq_add_of_exact f g hf hg hex

theorem normOrd_length_pow (O B : Type) [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (P : Ideal B) [P.IsMaximal] (hP0 : P ≠ ⊥) (n : ℕ) :
    length O (B ⧸ P ^ n) = n * length O (B ⧸ P) := by
  induction n with
  | zero =>
    have : Subsingleton (B ⧸ P ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    rw [Module.length_eq_zero_iff.mpr this]
    simp
  | succ n ih =>
    rw [normOrd_length_succ O B P hP0 n, ih]
    push_cast
    ring

theorem normOrd_length_residue (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
    [Module.Finite O B] (Q : Ideal B) [Q.IsMaximal] :
    length O (B ⧸ Q) = Q.inertiaDeg O := by
  classical
  set p := Q.under O with hp
  haveI : p.IsMaximal := Ideal.IsMaximal.under O Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  rw [← Ideal.inertiaDeg_eq_inertiaDeg' p Q, Ideal.inertiaDeg_algebraMap]
  letI : Field (O ⧸ p) := Ideal.Quotient.field p
  haveI : Module.Finite (O ⧸ p) (B ⧸ Q) := Module.Finite.of_restrictScalars_finite O _ _
  rw [← Module.length_eq_finrank]
  have hsurj : Function.Surjective (algebraMap O (O ⧸ p)) := Ideal.Quotient.mk_surjective
  let e : Submodule (O ⧸ p) (B ⧸ Q) ≃o Submodule O (B ⧸ Q) :=
    { toFun := fun N => N.restrictScalars O
      invFun := fun N =>
        { carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun c x hx => by
            obtain ⟨a, rfl⟩ := hsurj c
            rw [algebraMap_smul]
            exact N.smul_mem a hx }
      left_inv := fun N => Submodule.ext fun _ => Iff.rfl
      right_inv := fun N => Submodule.ext fun _ => Iff.rfl
      map_rel_iff' := Iff.rfl }
  have key : ∀ (x y : WithBot ℕ∞) (hx : x ≠ ⊥) (hy : y ≠ ⊥), x = y → x.unbot hx = y.unbot hy := by
    rintro x y hx hy rfl
    rfl
  unfold Module.length
  exact key _ _ _ _ (Order.krullDim_eq_of_orderIso e).symm

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.SJCoreA
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Set Real Filter Topology

def radJ (k : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), r ^ k * exp (-r ^ 2)

def radK (k : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), r ^ k * log r * exp (-r ^ 2)

theorem integrableOn_radJ (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * exp (-r ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := (k : ℝ)) (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) two_pos
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_two]

theorem radJ_eq (k : ℕ) : radJ k = Gamma (((k : ℝ) + 1) / 2) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (k : ℝ)) two_pos (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  rw [radJ, h]
  ring

theorem radJ_pos (k : ℕ) : 0 < radJ k := by
  rw [radJ_eq]
  exact div_pos (Real.Gamma_pos_of_pos (by positivity)) two_pos

theorem radJ_add_two (k : ℕ) : radJ (k + 2) = ((k : ℝ) + 1) / 2 * radJ k := by
  rw [radJ_eq, radJ_eq]
  have h : (((k + 2 : ℕ) : ℝ) + 1) / 2 = ((k : ℝ) + 1) / 2 + 1 := by push_cast; ring
  rw [h, Real.Gamma_add_one (by positivity)]
  ring

theorem integrableOn_radK {k : ℕ} (hk : 1 ≤ k) :
    IntegrableOn (fun r : ℝ => r ^ k * log r * exp (-r ^ 2)) (Ioi 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ((integrableOn_radJ (m + 2)).add (integrableOn_radJ m)).mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r (hr : 0 < r) => ?_)
    have hlog : |log r| ≤ r + r⁻¹ := by
      rcases le_or_gt 0 (log r) with h | h
      · rw [abs_of_nonneg h]
        have := Real.log_le_sub_one_of_pos hr
        have : 0 < r⁻¹ := inv_pos.2 hr
        linarith
      · rw [abs_of_neg h, ← Real.log_inv]
        have := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
        linarith
    have he := exp_pos (-r ^ 2)
    have hpow : r ^ (m + 1) * (r + r⁻¹) = r ^ (m + 2) + r ^ m := by
      field_simp
      ring
    have hmain : r ^ (m + 1) * |log r| ≤ r ^ (m + 2) + r ^ m := by
      rw [← hpow]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos he, abs_of_pos (pow_pos hr _)]
    calc r ^ (m + 1) * |log r| * exp (-r ^ 2) ≤ (r ^ (m + 2) + r ^ m) * exp (-r ^ 2) :=
          mul_le_mul_of_nonneg_right hmain he.le
      _ = r ^ (m + 2) * exp (-r ^ 2) + r ^ m * exp (-r ^ 2) := by ring

theorem tendsto_radK_boundary (m : ℕ) :
    Tendsto (fun r : ℝ => -(1 / 2) * (r ^ (m + 1) * (r * log r) * exp (-r ^ 2))) atTop (𝓝 0) := by
  have hA : Tendsto (fun r : ℝ => (r ^ 2) ^ (m + 3) * exp (-(r ^ 2))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (m + 3)).comp (tendsto_pow_atTop two_ne_zero)
  refine squeeze_zero_norm' ?_ hA
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := by linarith
  have hl0 : 0 ≤ log r := Real.log_nonneg hr
  have hl : log r ≤ r := (Real.log_le_sub_one_of_pos hr0).trans (by linarith)
  have he := exp_pos (-r ^ 2)
  have hp : r ^ (m + 3) ≤ (r ^ 2) ^ (m + 3) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hr (by omega)
  have nn : 0 ≤ r ^ (m + 1) * (r * log r) * exp (-r ^ 2) :=
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hr0.le hl0)) he.le
  have key : r ^ (m + 1) * (r * log r) * exp (-r ^ 2) ≤ (r ^ 2) ^ (m + 3) * exp (-(r ^ 2)) := by
    calc r ^ (m + 1) * (r * log r) * exp (-r ^ 2) ≤ r ^ (m + 1) * (r * r) * exp (-r ^ 2) := by
          gcongr
      _ = r ^ (m + 3) * exp (-r ^ 2) := by ring
      _ ≤ (r ^ 2) ^ (m + 3) * exp (-(r ^ 2)) := mul_le_mul_of_nonneg_right hp he.le
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

theorem radK_add_two {k : ℕ} (hk : 1 ≤ k) :
    radK (k + 2) = ((k + 1) * radK k + radJ k) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x ^ (m + 2) * log x)
      (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h2 : x ^ (m + 2) * x⁻¹ = x ^ (m + 1) := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ hx0, mul_one]
    refine ((hasDerivAt_pow (m + 2) x).mul (Real.hasDerivAt_log hx0)).congr_deriv ?_
    rw [show m + 2 - 1 = m + 1 from rfl, h2]
    push_cast
    ring
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) (x * exp (-x ^ 2)) x := by
    intro x _
    refine (((hasDerivAt_pow 2 x).neg.exp).const_mul (-(1 / 2 : ℝ))).congr_deriv ?_
    simp only [Pi.neg_apply, show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
    ring
  have huv' : IntegrableOn ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => x * exp (-x ^ 2)) (Ioi 0) :=
    (integrableOn_radK (k := m + 3) (by omega)).congr_fun
      (fun r _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hu'v : IntegrableOn ((fun x : ℝ => ((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) *
      fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) (Ioi 0) :=
    IntegrableOn.congr_fun (((integrableOn_radK (k := m + 1) (by omega)).const_mul (-(1 / 2) * ((m : ℝ) + 2))).add
      ((integrableOn_radJ (m + 1)).const_mul (-(1 / 2))))
      (fun r _ => by simp only [Pi.mul_apply, Pi.add_apply]; ring) measurableSet_Ioi
  have hc : Continuous (fun r : ℝ => -(1 / 2) * (r ^ (m + 1) * (r * log r) * exp (-r ^ 2))) := by
    have := Real.continuous_mul_log
    fun_prop
  have hF0 : (-(1 / 2) * ((0 : ℝ) ^ (m + 1) * (0 * log 0) * exp (-(0 : ℝ) ^ 2))) = 0 := by simp
  have h0 : Tendsto ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => -(1 / 2) * exp (-x ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [hF0] at this
    refine this.congr (fun r => ?_)
    simp only [Pi.mul_apply]
    ring
  have hinf : Tendsto ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => -(1 / 2) * exp (-x ^ 2))
      atTop (𝓝 0) :=
    (tendsto_radK_boundary m).congr (fun r => by simp only [Pi.mul_apply]; ring)
  have key : ∫ x in Ioi (0 : ℝ), x ^ (m + 2) * log x * (x * exp (-x ^ 2)) =
      0 - 0 - ∫ x in Ioi (0 : ℝ), (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) *
        (-(1 / 2) * exp (-x ^ 2)) :=
    integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  have e1 : radK (m + 1 + 2) = ∫ x in Ioi (0 : ℝ), x ^ (m + 2) * log x * (x * exp (-x ^ 2)) := by
    rw [radK]
    congr 1
    funext x
    ring
  have e2 : (fun x : ℝ => (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) * (-(1 / 2) * exp (-x ^ 2))) =
      fun x => (-(1 / 2) * ((m : ℝ) + 2)) * (x ^ (m + 1) * log x * exp (-x ^ 2)) +
        (-(1 / 2)) * (x ^ (m + 1) * exp (-x ^ 2)) := by
    funext x
    ring
  rw [e1, key, e2, integral_add ((integrableOn_radK (k := m + 1) (by omega)).const_mul _)
    ((integrableOn_radJ (m + 1)).const_mul _), integral_const_mul, integral_const_mul]
  rw [radK, radJ]
  push_cast
  ring

theorem radRatio_add_two {k : ℕ} (hk : 1 ≤ k) :
    radK (k + 2) / radJ (k + 2) = radK k / radJ k + 1 / ((k : ℝ) + 1) := by
  have hJ := radJ_pos k
  rw [radK_add_two hk, radJ_add_two]
  field_simp

theorem radRatio_odd (m : ℕ) :
    radK (2 * m + 1) / radJ (2 * m + 1) = radK 1 / radJ 1 + (harmonic m : ℝ) / 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h := radRatio_add_two (k := 2 * n + 1) (by omega)
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, h, ih, harmonic_succ]
    push_cast
    field_simp
    ring

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def triChar {p : ℕ} (a : Fin p → ℕ) (b : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  ∏ i, b i i ^ a i

def IsTriEquivariant {p : ℕ} (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  ∀ x b : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → b.det ≠ 0 → b.BlockTriangular id →
    P (x * b) = triChar a b * P x

def colNormSq {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (j : Fin p) : ℝ :=
  ∑ i, ‖x i j‖ ^ 2

def LemmaHStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (a : ∀ s, Fin (p s) → ℕ)
    (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ) (C R : ℝ),
    (∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x) →
    (∀ k : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ,
      (∀ s, k s ∈ Matrix.unitaryGroup (Fin (p s)) ℂ) → ‖P k‖ ≤ C) → 0 ≤ R →
    ∀ x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ, (∀ s, (x s).det ≠ 0) →
      (∀ s j, colNormSq (x s) j ≤ R ^ 2) → ‖P x‖ ≤ C * R ^ (∑ s, ∑ i, a s i)

def TorsionNonvanishStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (θ : V → ℂ) (Λ : AddSubgroup V) (ρ : ℝ) (n : ℕ),
    Differentiable ℂ θ → (∃ z, θ z ≠ 0) →
    (∀ l ∈ Λ, ∀ z, ‖θ (z + l)‖ * Real.exp (-(Real.pi / 2) * ‖z + l‖ ^ 2) =
      ‖θ z‖ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) →
    (∀ v : V, ∃ l ∈ Λ, ‖v - l‖ ≤ ρ) → 5 * ρ < n →
    ∃ l ∈ Λ, θ ((n : ℂ)⁻¹ • l) ≠ 0

def sgn (p : ℕ) {r : ℕ} (k : Fin r) : ℂ := if (k : ℕ) < p then 1 else -1

def jForm (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) : ℂ :=
  ∑ k, sgn p k * (conj (x k) * y k)

def normSq {r : ℕ} (u : Fin r → ℂ) : ℝ := ∑ k, ‖u k‖ ^ 2

def posSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then ‖u k‖ ^ 2 else 0

def negSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then 0 else ‖u k‖ ^ 2

def approxR (r : ℕ) (μ ρ : ℝ) : ℝ := 4 * Real.sqrt r * μ / ρ

def ApproxGraphStatement : Prop :=
  ∀ (r p : ℕ) (μ ρ : ℝ) (X : Fin r → Fin r → ℂ), p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 →
    (∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2) →
    (∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) ∧
    (∀ y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) → y ≠ 0 →
      (jForm p y y).re < 0) ∧
    (∀ v y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) →
      v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p}) →
      ‖jForm p y y‖ ≤ 2 * normSq v)

structure HermForm (K : Type) [Field K] [NumberField K] (r : ℕ) where

  c : K →+* K
  c_invol : ∀ x, c (c x) = x
  c_emb : ∀ (σ : K →+* ℂ) (x : K), σ (c x) = conj (σ x)

  G : Matrix (Fin r) (Fin r) K
  G_herm : ∀ a b, c (G a b) = G b a

def HermForm.h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x y : Fin r → K) : K :=
  ∑ a, ∑ b, S.c (x a) * S.G a b * y b

def embVec {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ) (x : Fin r → K) : Fin r → ℂ := fun a => σ (x a)

def IsIntegralElt {K : Type} [Field K] [NumberField K] (x : K) : Prop := ∃ z : 𝓞 K, (z : K) = x

def IsLattice {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin r → K)) = ⊤

def IsIntegralOn {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, IsIntegralElt (S.h x y)

def IsSelfDual {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  IsIntegralOn S L ∧ ∀ x, (∀ y ∈ L, IsIntegralElt (S.h x y)) → x ∈ L

def majSq {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → K) : ℝ :=
  ∑ i, normSq (Q i *ᵥ embVec (σ i) v)

def ApproxStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [Nonempty ι] (r p : ℕ)
    (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → Fin r → K) (μ ρ : ℝ),
    p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsIntegralOn S L →
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) →
    (∀ j, v j ∈ L) → LinearIndependent K v → (∀ j, majSq σ Q (v j) ≤ μ ^ 2) →
    ∃ la : Fin r → Fin r → K, (∀ j, la j ∈ L) ∧ LinearIndependent K la ∧
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → S.h (la j) (la k) = 0) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
        negSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ≤
          (ρ / 3) ^ 2 * posSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ∧
        (w ≠ 0 → 0 < (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re)) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, (j : ℕ) < p → w j = 0) → w ≠ 0 →
        (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re < 0) ∧
      (∀ i (j : Fin r), (j : ℕ) < p → ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ 2) ∧
      (∀ i (j : Fin r), p ≤ (j : ℕ) →
        ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ (4 * p) * (2 * μ ^ 2))

def OnePolyGrowthStatement : Prop :=
  ∀ (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ), B.Finite → DifferentiableOn ℂ f Bᶜ →
    (∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t ∉ B, f t = P.eval t

def IsHoloGL {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) {y | (Matrix.of y).det ≠ 0}

def leadMinor {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (i : Fin p) : ℂ :=
  (Matrix.of fun a b : Fin (i + 1) => x (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)).det

def BWPolyStatement : Prop :=
  ∀ (p : ℕ) (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ), IsHoloGL P →
    IsTriEquivariant a P →
    ∃ F : MvPolynomial (Fin p × Fin p) ℂ, F.IsHomogeneous (∑ i, a i) ∧
      ∀ x : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → P x = MvPolynomial.eval (fun ij => x ij.1 ij.2) F

end ReciprocityTheory.MultiplicativeHeights
end
end

