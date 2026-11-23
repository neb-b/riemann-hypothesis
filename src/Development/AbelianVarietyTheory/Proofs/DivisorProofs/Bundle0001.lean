module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEvalSubTopLe
section
namespace GlobalTheory

theorem abs_factorial_mul_eval_sub_top_le (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ d) :
    ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℚ) * p.eval (m : ℚ) - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d|
      ≤ C * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
  obtain ⟨C, hC⟩ := exists_nat_ge ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|)
  refine ⟨C, fun m => ?_⟩
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hf : (0 : ℚ) ≤ d.factorial := Nat.cast_nonneg _
  rw [Polynomial.eval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ]
  have e : (d.factorial : ℚ) * (∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i + p.coeff d * (m : ℚ) ^ d)
      - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d
      = (d.factorial : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i := by ring
  rw [e, abs_mul, abs_of_nonneg hf]
  have hX : (0 : ℚ) ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) := by positivity
  have h1 : |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i|
      ≤ (∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i < d := Finset.mem_range.mp hi
    rw [abs_mul, abs_of_nonneg (pow_nonneg hm i)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have a1 : (m : ℚ) ^ i ≤ ((m : ℚ) + 1) ^ i := pow_le_pow_left₀ hm (by linarith) i
    have a2 : ((m : ℚ) + 1) ^ i ≤ ((m : ℚ) + 1) ^ (d - 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have a3 : (1 : ℚ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have a4 : (0 : ℚ) ≤ ((m : ℚ) + 1) ^ (d - 1) := by positivity
    exact a1.trans (a2.trans (le_mul_of_one_le_left a4 a3))
  calc _ ≤ (d.factorial : ℚ) * ((∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left h1 hf
    _ = ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC hX

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsIntClosedLocalizationAndQuotient
section
open IsLocalRing

namespace GlobalTheory

open Polynomial

theorem absIntClosed_localization_and_quotient : ∀ (T : Type) [CommRing T], (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∀ (M : Submonoid T), 0 ∉ M → (IsDomain (Localization M) ∧ ∀ f : Polynomial (Localization M), f.Monic → 0 < f.natDegree → ∃ x : (Localization M), f.eval x = 0)) ∧ (∀ (p : Ideal T), p.IsPrime → (IsDomain (T ⧸ p) ∧ ∀ f : Polynomial (T ⧸ p), f.Monic → 0 < f.natDegree → ∃ x : (T ⧸ p), f.eval x = 0)) := by
  intro T _ ⟨hdom, hroot⟩
  refine ⟨fun M hM => ?_, fun p hp => ?_⟩
  · have hle : M ≤ nonZeroDivisors T := le_nonZeroDivisors_of_noZeroDivisors hM
    haveI : IsDomain (Localization M) := IsLocalization.isDomain_localization hle
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts M f
      (by rw [hf.leadingCoeff]; exact one_mem _)
    obtain ⟨g, hg, hgdeg, hgm⟩ :=
      lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff _).2 hf)
    rw [natDegree_scaleRoots] at hgdeg
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    set s : Localization M :=
      algebraMap T (Localization M) (IsLocalization.commonDenom M f.support f.coeff) with hs
    have hu : IsUnit s := IsLocalization.map_units _ _
    refine ⟨algebraMap T (Localization M) y * ↑hu.unit⁻¹, ?_⟩
    have key := scaleRoots_eval_mul f (algebraMap T (Localization M) y * ↑hu.unit⁻¹) s
    have hsr : s * (algebraMap T (Localization M) y * ↑hu.unit⁻¹) =
        algebraMap T (Localization M) y := by
      rw [mul_left_comm, IsUnit.mul_val_inv, mul_one]
    rw [hsr, ← hg, eval_map, eval₂_hom, hy, map_zero] at key
    exact ((hu.pow _).mul_right_eq_zero).1 key.symm
  · haveI := hp
    haveI : IsDomain (T ⧸ p) := Ideal.Quotient.isDomain p
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl : f ∈ lifts (Ideal.Quotient.mk p) :=
      (mem_lifts _).2 (map_surjective _ Ideal.Quotient.mk_surjective f)
    obtain ⟨g, hg, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic hl hf
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    refine ⟨Ideal.Quotient.mk p y, ?_⟩
    rw [← hg, eval_map, eval₂_hom, hy, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogInvOneSubLeTwoMulAbs
section
open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory

theorem abs_log_inv_one_sub_le_two_mul_abs (y : ℝ) (hy : |y| ≤ 1 / 2) :
    |Real.log (1 - y)⁻¹| ≤ 2 * |y| := by
  have h1 := le_abs_self y
  have h2 := neg_abs_le y
  have h0 := abs_nonneg y
  have hpos : 0 < 1 - y := by linarith
  rw [abs_le]
  constructor
  · rw [Real.log_inv]
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h3 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    have h4 : (1 - y)⁻¹ ≤ 1 + 2 * |y| := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith [mul_nonneg h0 (show (0:ℝ) ≤ |y| - y by linarith), mul_nonneg h0 (show (0:ℝ) ≤ 1 / 2 - |y| by linarith)]
    linarith

theorem tprod_inv_one_sub_pos_and_le_exp :
    ∀ {ι : Type} (y : ι → ℝ) (B : ℝ), (∀ a, |y a| ≤ 1 / 2) → Summable (fun a => |y a|) →
      ∑' a, |y a| ≤ B →
      0 < ∏' a, (1 - y a)⁻¹ ∧ ∏' a, (1 - y a)⁻¹ ≤ Real.exp (2 * B) := by
  intro ι y B hy hs hB
  have hb : ∀ a, |Real.log (1 - y a)⁻¹| ≤ 2 * |y a| :=
    fun a => abs_log_inv_one_sub_le_two_mul_abs _ (hy a)
  have hs2 : Summable (fun a => 2 * |y a|) := hs.mul_left 2
  have hsl : Summable (fun a => Real.log (1 - y a)⁻¹) :=
    Summable.of_norm_bounded hs2 (fun a => by simpa only [Real.norm_eq_abs] using hb a)
  have hp := hsl.hasSum.rexp
  have he : (Real.exp ∘ fun a => Real.log (1 - y a)⁻¹) = fun a => (1 - y a)⁻¹ := by
    funext a
    have h1 := le_abs_self (y a)
    have h2 := hy a
    exact Real.exp_log (inv_pos.mpr (by linarith))
  rw [he] at hp
  rw [hp.tprod_eq]
  refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr ?_⟩
  calc ∑' a, Real.log (1 - y a)⁻¹ ≤ ∑' a, 2 * |y a| :=
        hsl.tsum_le_tsum (fun a => (le_abs_self _).trans (hb a)) hs2
    _ = 2 * ∑' a, |y a| := tsum_mul_left
    _ ≤ 2 * B := by linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMapRingOfIntegersHom
section
open NumberField

namespace GlobalTheory

theorem absNorm_map_ringOfIntegers_hom (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (𝔞 : Ideal (𝓞 E)) :
    Module.finrank ℚ E ∣ Module.finrank ℚ K ∧
      Ideal.absNorm (𝔞.map τ) = Ideal.absNorm 𝔞 ^ (Module.finrank ℚ K / Module.finrank ℚ E) := by
  have hτinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    rw [eq_intCast, map_intCast]
    constructor
    · intro h
      have : ((n : 𝓞 K) : K) = 0 := by rw [h]; rfl
      exact_mod_cast this
    · rintro rfl; simp
  have hinj : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective (K := K)).comp hτinj
  let φ : E →+* K := IsFractionRing.lift hinj
  letI : Algebra E K := φ.toAlgebra
  have hmap : τ = algebraMap (𝓞 E) (𝓞 K) := by
    ext x
    change ((algebraMap (𝓞 K) K).comp τ) x = φ (algebraMap (𝓞 E) E x)
    rw [IsFractionRing.lift_algebraMap]
  have htower := Module.finrank_mul_finrank ℚ E K
  have hE : 0 < Module.finrank ℚ E := Module.finrank_pos
  refine ⟨⟨Module.finrank E K, htower.symm⟩, ?_⟩
  have hq : Module.finrank ℚ K / Module.finrank ℚ E = Module.finrank E K := by
    rw [← htower, Nat.mul_div_cancel_left _ hE]
  rw [hq, hmap, Ideal.absNorm_algebraMap (𝓞 E) (𝓞 K) 𝔞,
    ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedIntegralBasis
section
open PowerSeries

namespace GlobalTheory.LaurentFlagBasis

variable {F : Type} [Field F]

noncomputable def red {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → F := fun a => constantCoeff (y a)

noncomputable def lift {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → LaurentSeries F :=
  fun a => (y a : LaurentSeries F)

lemma exists_primitive {n : ℕ} (u : Fin n → LaurentSeries F) (hu : u ≠ 0) :
    ∃ (i : Fin n) (y : Fin n → PowerSeries F), lift y = (u i)⁻¹ • u ∧ y i = 1 := by
  obtain ⟨l, hl⟩ : ∃ l, u l ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun a => Valued.v (u a))
    ⟨l, Finset.mem_univ _⟩
  have hvl : Valued.v (u l) ≠ 0 := (Valuation.ne_zero_iff _).mpr hl
  have hvi : 0 < Valued.v (u i) := by
    have := hi l (Finset.mem_univ _)
    exact lt_of_lt_of_le (zero_lt_iff.mpr hvl) this
  have hui : u i ≠ 0 := (Valuation.ne_zero_iff _).mp hvi.ne'
  have key : ∀ a, ∃ P : PowerSeries F, (P : LaurentSeries F) = (u i)⁻¹ * u a := by
    intro a
    have := (LaurentSeries.val_le_one_iff_eq_coe F ((u i)⁻¹ * u a)).mp (by
      rw [map_mul, map_inv₀, inv_mul_le_one₀ hvi]
      exact hi a (Finset.mem_univ _))
    exact this
  choose y hy using key
  refine ⟨i, y, funext fun a => ?_, ?_⟩
  · simp [lift, hy]
  · apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [hy, inv_mul_cancel₀ hui, map_one]

lemma exists_indep {n : ℕ} : ∀ (d : ℕ) (U : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)),
    d ≤ Module.finrank (LaurentSeries F) U →
    ∃ y : Fin d → (Fin n → PowerSeries F), (∀ b, lift (y b) ∈ U) ∧
      LinearIndependent F (fun b => red (y b)) := by
  intro d
  induction d with
  | zero =>
    intro U _
    exact ⟨Fin.elim0, fun b => b.elim0, linearIndependent_empty_type⟩
  | succ d ih =>
    intro U hd
    have hU : U ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hd
      omega
    obtain ⟨u, huU, hu0⟩ : ∃ u : Fin n → LaurentSeries F, u ∈ U ∧ u ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot hU
    obtain ⟨i, y0, hy0, hy0i⟩ := exists_primitive u hu0
    let f : U →ₗ[LaurentSeries F] LaurentSeries F := (LinearMap.proj i).comp U.subtype
    let U' : Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := (LinearMap.ker f).map U.subtype
    have hU' : d ≤ Module.finrank (LaurentSeries F) U' := by
      have h1 := LinearMap.finrank_range_add_finrank_ker f
      have h2 : Module.finrank (LaurentSeries F) (LinearMap.range f) ≤ 1 := by
        simpa using Submodule.finrank_le (LinearMap.range f)
      have h3 : Module.finrank (LaurentSeries F) U' =
          Module.finrank (LaurentSeries F) (LinearMap.ker f) :=
        (Submodule.equivMapOfInjective _ U.injective_subtype _).finrank_eq.symm
      omega
    obtain ⟨y, hyU, hyi⟩ := ih U' hU'
    refine ⟨Fin.cons y0 y, ?_, ?_⟩
    · intro b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp only [Fin.cons_zero]; rw [hy0]; exact U.smul_mem _ huU
      · simp only [Fin.cons_succ]
        obtain ⟨z, -, hz⟩ := Submodule.mem_map.mp (hyU b)
        rw [← hz]; exact z.2
    · have e : (fun b => red ((Fin.cons y0 y : Fin (d+1) → Fin n → PowerSeries F) b)) =
          Fin.cons (red y0) (fun b => red (y b)) := by
        ext b; refine Fin.cases ?_ (fun b => ?_) b <;> simp
      rw [e, linearIndependent_finCons]
      refine ⟨hyi, fun hmem => ?_⟩
      have hsub : Submodule.span F (Set.range fun b => red (y b)) ≤
          LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin n => F) i) := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        obtain ⟨z, hz, hzz⟩ := Submodule.mem_map.mp (hyU b)
        have hz0 : (z : Fin n → LaurentSeries F) i = 0 := hz
        have h0 : ((y b i : PowerSeries F) : LaurentSeries F) = 0 := by
          have := congrFun hzz i
          simp only [Submodule.subtype_apply] at this
          rw [← hz0, this]; rfl
        have h00 : y b i = 0 := by
          apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
          rw [map_zero]; exact h0
        simp [red, h00]
      have := hsub hmem
      simp [red, hy0i] at this

lemma greedy {n : ℕ} (V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j)) :
    ∀ m, m ≤ n → ∃ c : Fin m → (Fin n → PowerSeries F), (∀ j : Fin m, lift (c j) ∈ V j) ∧
      LinearIndependent F (fun j => red (c j)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun j => j.elim0, linearIndependent_empty_type⟩
  | succ m ih =>
    intro hm
    obtain ⟨c, hcV, hci⟩ := ih (Nat.le_of_succ_le hm)
    obtain ⟨y, hyV, hyi⟩ := exists_indep (Module.finrank (LaurentSeries F) (V m)) (V m) le_rfl
    have : ∃ b, red (y b) ∉ Submodule.span F (Set.range fun j => red (c j)) := by
      by_contra h; push Not at h
      have h1 : Submodule.span F (Set.range fun b => red (y b)) ≤
          Submodule.span F (Set.range fun j => red (c j)) :=
        Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact h b)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hyi, finrank_span_eq_card hci] at h2
      simp at h2
      have := hV m (by omega)
      omega
    obtain ⟨b, hb⟩ := this
    refine ⟨Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b), ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last, Fin.val_last]; exact hyV b
      · simp only [Fin.snoc_castSucc, Fin.val_castSucc]; exact hcV j
    · have e : (fun j => red ((Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b)) j)) =
          Fin.snoc (α := fun _ => Fin n → F) (fun j => red (c j)) (red (y b)) := by
        ext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
      rw [e, linearIndependent_finSnoc]
      exact ⟨hci, hb⟩

end GlobalTheory.LaurentFlagBasis


open GlobalTheory.LaurentFlagBasis in
theorem GlobalTheory.LaurentFlagBasis.adapted_integral_basis : ∀ (F : Type) [Field F] (n R : ℕ)
    (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W →
    ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n),
      (j : ℕ) < Module.finrank (LaurentSeries F) (W k) →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) :
        LaurentSeries F)) ∈ W k := by
  intro F _ n R W hW
  let V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := fun j =>
    ⨅ (k : Fin (R + 1)) (_ : j < Module.finrank (LaurentSeries F) (W k)), W k
  have hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j) := by
    intro j hj
    by_cases h : ∃ k, j < Module.finrank (LaurentSeries F) (W k)
    · obtain ⟨k, hk⟩ := h
      obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter fun k => j < Module.finrank (LaurentSeries F) (W k)) id
        ⟨k, by simp [hk]⟩
      have hle : W k0 ≤ V j := le_iInf₂ fun k hk => hW (hmin k (by simp [hk]))
      have := Submodule.finrank_mono hle
      simp at hk0
      omega
    · push Not at h
      have hle : ⊤ ≤ V j := le_iInf₂ fun k hk => absurd hk (not_lt.mpr (h k))
      have := Submodule.finrank_mono hle
      rw [finrank_top, Module.finrank_fin_fun] at this
      omega
  obtain ⟨c, hcV, hci⟩ := greedy V hV n le_rfl
  let g : Matrix (Fin n) (Fin n) (PowerSeries F) := Matrix.of fun a j => c j a
  have hunit : IsUnit g := by
    rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_col_iff_isUnit]
    convert hci using 1
    funext j a
    simp [g, red, Matrix.col]
  refine ⟨hunit.unit, fun k j hj => ?_⟩
  have hmem := hcV j
  have hVk : V j ≤ W k := iInf₂_le k hj
  exact hVk hmem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddSumIntegral
section
namespace GlobalTheory.IntegralAddSum

theorem add_sum_integral {A C K B : Type} [CommRing A] [CommRing C] [CommRing K] [CommRing B]
    (φ : A →+* K) (gc : C →+* B) (gk : K →+* B) {x y : B}
    (hx : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ x = ∑ m : Fin n, gc (c m) * gk (b m))
    (hy : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ y = ∑ m : Fin n, gc (c m) * gk (b m)) :
    ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ x + y = ∑ m : Fin n, gc (c m) * gk (b m) := by
  obtain ⟨n, c, b, hb, rfl⟩ := hx
  obtain ⟨n', c', b', hb', rfl⟩ := hy
  refine ⟨n + n', Fin.append c c', Fin.append b b', ?_, ?_⟩
  · intro m
    refine Fin.addCases (fun i => ?_) (fun i => ?_) m
    · rw [Fin.append_left]; exact hb i
    · rw [Fin.append_right]; exact hb' i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

end GlobalTheory.IntegralAddSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddValuationNatCastEqPadicValNat
section
namespace GlobalTheory

theorem addValuation_natCast_eq_padicValNat :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime →
      v (p : C) = 1 → ∀ n : ℕ, n ≠ 0 →
        v (n : C) = (((padicValNat p n : ℕ) : ℝ) : WithTop ℝ) := by
  intro C _ _ v p hp hvp n hn
  have h1 : v (1 : C) = 0 := v.map_one

  have hnat : ∀ m : ℕ, 0 ≤ v (m : C) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h := v.map_add (k : C) 1
      rw [h1] at h
      push_cast
      exact le_trans (le_min ih le_rfl) h
  have hint : ∀ a : ℤ, 0 ≤ v (a : C) := by
    intro a
    obtain ⟨m, rfl | rfl⟩ := a.eq_nat_or_neg
    · simpa using hnat m
    · simpa [v.map_neg] using hnat m

  have hcop : ∀ m : ℕ, Nat.Coprime m p → v (m : C) = 0 := by
    intro m hm
    by_contra hne
    have hpos : 0 < v (m : C) := lt_of_le_of_ne (hnat m) (Ne.symm hne)
    have hbez : ((1 : ℤ)) = (m : ℤ) * Nat.gcdA m p + (p : ℤ) * Nat.gcdB m p := by
      have := Nat.gcd_eq_gcd_ab m p
      rw [hm] at this
      simpa using this
    have hC : (1 : C) = (m : C) * ((Nat.gcdA m p : ℤ) : C) + (p : C) * ((Nat.gcdB m p : ℤ) : C) := by
      have := congrArg (fun z : ℤ => (z : C)) hbez
      simpa using this
    have ha : 0 < v ((m : C) * ((Nat.gcdA m p : ℤ) : C)) := by
      rw [v.map_mul]
      exact lt_of_lt_of_le hpos (le_add_of_nonneg_right (hint _))
    have hb : 0 < v ((p : C) * ((Nat.gcdB m p : ℤ) : C)) := by
      rw [v.map_mul, hvp]
      exact lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_add_of_nonneg_right (hint _))
    have h := v.map_add ((m : C) * ((Nat.gcdA m p : ℤ) : C)) ((p : C) * ((Nat.gcdB m p : ℤ) : C))
    rw [← hC, h1] at h
    exact absurd (lt_of_lt_of_le (lt_min ha hb) h) (lt_irrefl _)

  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (fun {p n : ℕ} => _root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)) (p := p) (n := n)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by simpa using hm)
  have hnd : ¬ p ∣ m := by
    intro hd
    obtain ⟨c, rfl⟩ := hd
    have : p ^ (padicValNat p n + 1) ∣ n := ⟨c, by rw [pow_succ, mul_assoc, ← hm]⟩
    rw [Nat.padicValNat_def] at this
    exact pow_succ_multiplicity_not_dvd (p := p) hn this
  have hcm : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
  have hcast : (n : C) = (p : C) ^ (padicValNat p n) * (m : C) := by
    conv_lhs => rw [hm]
    push_cast
    ring
  rw [hcast, v.map_mul, v.map_pow, hvp, hcop m hcm, add_zero]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinMatrixReducedOfCharpolySeparable
section
open Matrix Polynomial

namespace GlobalTheory

theorem adjoin_matrix_reduced_of_charpoly_separable :
    ∀ (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K), N.charpoly.Separable →
      ∀ g ∈ Algebra.adjoin K {N}, ∀ m : ℕ, g ^ m = 0 → g = 0 := by
  intro K _ n N hsep g hg m hm
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · rw [pow_zero] at hm
    calc g = g * 1 := (mul_one g).symm
      _ = 0 := by rw [hm, mul_zero]
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hg
  obtain ⟨P, rfl⟩ := hg
  have h1 : minpoly K N ∣ P ^ m := minpoly.dvd K N (by rw [map_pow]; exact hm)
  have hs : (minpoly K N).Separable := hsep.of_dvd (Matrix.minpoly_dvd_charpoly N)
  have h2 : minpoly K N ∣ P := (hs.squarefree.dvd_pow_iff_dvd hmpos.ne').mp h1
  obtain ⟨q, hq⟩ := h2
  show aeval N P = 0
  rw [hq, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory
end

