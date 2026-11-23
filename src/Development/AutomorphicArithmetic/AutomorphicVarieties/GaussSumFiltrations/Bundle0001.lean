module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ConstEqZero
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.QUniq

def chr {V : Type} [Fintype V] (μ x : V → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ))

theorem chr_add {V : Type} [Fintype V] (μ x y : V → ℝ) : chr μ (x + y) = chr μ x * chr μ y := by
  simp only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, Complex.exp_add]

theorem chr_add' {V : Type} [Fintype V] (μ ν x : V → ℝ) : chr (μ + ν) x = chr μ x * chr ν x := by
  simp only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, add_mul, Finset.sum_add_distrib, Complex.exp_add]

theorem chr_zero {V : Type} [Fintype V] (μ : V → ℝ) : chr μ 0 = 1 := by simp [chr]

theorem chr_zero' {V : Type} [Fintype V] (x : V → ℝ) : chr 0 x = 1 := by simp [chr]

theorem norm_chr {V : Type} [Fintype V] (μ x : V → ℝ) : ‖chr μ x‖ = 1 := by
  have : (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ)) = ((2 * Real.pi * ∑ v, μ v * x v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [chr, this, Complex.norm_exp_ofReal_mul_I]

theorem exists_chr {V : Type} [Fintype V] (μ : V → ℝ) (h : μ ≠ 0) : ∃ g, chr μ g = -1 := by
  classical
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  have hv' : (μ v : ℂ) ≠ 0 := by exact_mod_cast hv
  refine ⟨Pi.single v (1 / (2 * μ v)), ?_⟩
  have : ∑ w, (μ w : ℂ) * ((Pi.single v (1 / (2 * μ v)) : V → ℝ) w : ℂ) = 1 / 2 := by
    rw [Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]; push_cast; field_simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  rw [chr, this, ← Complex.exp_pi_mul_I]
  congr 1; ring

theorem hasSum_congr' {ι : Type} {f g : ι → ℂ} {d : ℂ} (h : HasSum f d) (e : ∀ i, g i = f i) : HasSum g d := by
  rwa [show g = f from funext e]

private theorem hasSum_average_chr_of_hasSum {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (C : ι → ℂ) (d : ℂ)
    (h : ∀ x, HasSum (fun i => C i * chr (μ i) x) d) (g : V → ℝ) (x : V → ℝ) :
    HasSum (fun i => C i * ((1 + chr (μ i) g) / 2) * chr (μ i) x) d := by
  have h2 := ((h x).add (h (x + g))).div_const 2
  have hd : (d + d) / 2 = d := by ring
  rw [hd] at h2
  refine hasSum_congr' h2 (fun i => ?_)
  rw [chr_add]
  ring

private theorem norm_one_add_chr_div_two_le_one {V : Type} [Fintype V] (μ x : V → ℝ) : ‖(1 + chr μ x) / 2‖ ≤ 1 := by
  rw [norm_div]
  have h1 := norm_add_le (1 : ℂ) (chr μ x)
  rw [norm_one, norm_chr] at h1
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith

theorem kill_freq {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) d) (S : Finset ι) :
    ∃ C : ι → ℂ, (∀ i, ‖C i‖ ≤ ‖B i‖) ∧ (∀ i ∈ S, C i = 0) ∧ ∀ x, HasSum (fun i => C i * chr (μ i) x) d := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact ⟨B, fun i => le_rfl, by simp, h⟩
  · intro j S _ ih
    obtain ⟨C, hCn, hCS, hC⟩ := ih
    by_cases hj : C j = 0
    · refine ⟨C, hCn, fun i hi => ?_, hC⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hj
      · exact hCS i hi
    · have hB : B j ≠ 0 := by
        intro hB0
        apply hj
        have h3 := hCn j
        rw [hB0, norm_zero] at h3
        exact norm_le_zero_iff.mp h3
      obtain ⟨g, hg⟩ := exists_chr (μ j) (hμ j hB)
      refine ⟨fun i => C i * ((1 + chr (μ i) g) / 2), fun i => ?_, fun i hi => ?_,
        fun x => hasSum_average_chr_of_hasSum μ C d hC g x⟩
      · rw [norm_mul]
        calc ‖C i‖ * ‖(1 + chr (μ i) g) / 2‖ ≤ ‖C i‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_one_add_chr_div_two_le_one _ _) (norm_nonneg _)
          _ ≤ ‖B i‖ := by
              rw [mul_one]
              exact hCn i
      · rcases Finset.mem_insert.mp hi with rfl | hi
        · simp [hg]
        · simp [hCS i hi]

theorem const_eq_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) d) : d = 0 := by
  classical
  have hB : Summable B := by
    have h0 := (h 0).summable
    simpa [chr_zero] using h0
  have hnB : Summable (fun i => ‖B i‖) := summable_norm_iff.mpr hB
  have key : ∀ ε > 0, ‖d‖ ≤ ε := by
    intro ε hε
    obtain ⟨S, hS⟩ := (summable_iff_vanishing_norm.mp hnB) ε hε
    obtain ⟨C, hCn, hCS, hC⟩ := kill_freq μ B d hμ h S
    have hC0 := Filter.Tendsto.norm (hC 0)
    refine le_of_tendsto' hC0 (fun t => ?_)
    simp only [chr_zero, mul_one]
    have e1 : ∑ i ∈ t \ S, C i = ∑ i ∈ t, C i :=
      Finset.sum_subset Finset.sdiff_subset (fun i hi hni => hCS i (by
        rw [Finset.mem_sdiff] at hni
        tauto))
    rw [← e1]
    calc ‖∑ i ∈ t \ S, C i‖ ≤ ∑ i ∈ t \ S, ‖C i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ t \ S, ‖B i‖ := Finset.sum_le_sum (fun i _ => hCn i)
      _ ≤ ‖∑ i ∈ t \ S, ‖B i‖‖ := Real.le_norm_self _
      _ ≤ ε := (hS _ Finset.sdiff_disjoint).le
  by_contra hd
  have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have h3 := key (‖d‖ / 2) (by linarith)
  linarith

theorem coef_eq_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (hμ : Function.Injective μ)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) 0) (j : ι) : B j = 0 := by
  classical
  apply neg_eq_zero.mp
  apply const_eq_zero (fun i => μ i + -μ j) (Function.update B j 0) (-B j)
  · intro i hi h0
    have hij : i ≠ j := by
      rintro rfl
      simp at hi
    exact hij (hμ (add_neg_eq_zero.mp h0))
  · intro x
    have h1 := ((h x).mul_left (chr (-μ j) x)).update j 0
    have hc : chr (-μ j) x * chr (μ j) x = 1 := by
      rw [← chr_add', neg_add_cancel, chr_zero']
    have hval : (0 - chr (-μ j) x * (B j * chr (μ j) x) + chr (-μ j) x * 0) = -B j := by
      linear_combination (-B j) * hc
    rw [hval] at h1
    refine hasSum_congr' h1 (fun i => ?_)
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Function.update_of_ne hij, Function.update_of_ne hij, chr_add']
      ring

end GlobalTheory.HilbertThetaSeries.QUniq

private theorem ez_at_imaginary_unit_shift_eq {F : Type} [Field F] [NumberField F] (ζ : F) (x : InfinitePlace F → ℝ) :
    ez ζ (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp)) =
      GlobalTheory.HilbertThetaSeries.QUniq.chr (fun v => reAt v ζ) x *
        Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ζ : ℂ) * Complex.I) := by
  simp only [ez, GlobalTheory.HilbertThetaSeries.QUniq.chr, UpperHalfPlane.coe_mk]
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]


open GlobalTheory.HilbertThetaSeries.QUniq in
theorem GlobalTheory.HilbertThetaSeries.hasQ_unique : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f : Hn F → ℂ) (a b : F → ℂ),
    HasQ f a → HasQ f b → a = b := by
  intro F _ _ _ f a b ha hb
  funext ξ
  have hinj : Function.Injective (fun ζ : F => fun v : InfinitePlace F => reAt v ζ) := by
    intro ζ η hζη
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hv := IsTotallyReal.isReal v
    have h1 := congrFun hζη v
    simp only [reAt] at h1
    apply (InfinitePlace.embedding_of_isReal hv).injective
    rw [← InfinitePlace.embedding_of_isReal_apply hv ζ, ← InfinitePlace.embedding_of_isReal_apply hv η,
      Complex.ofReal_re, Complex.ofReal_re] at h1
    exact h1
  have hsum : ∀ x : InfinitePlace F → ℝ, HasSum (fun ζ => ((a ζ - b ζ) *
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ζ : ℂ) * Complex.I)) *
        chr (fun v => reAt v ζ) x) 0 := by
    intro x
    have h2 := (ha.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp))).sub
      (hb.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp)))
    rw [sub_self] at h2
    refine hasSum_congr' h2 (fun ζ => ?_)
    simp only [ez_at_imaginary_unit_shift_eq]
    ring
  have key := coef_eq_zero (fun ζ : F => fun v => reAt v ζ) _ hinj hsum ξ
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (Complex.exp_ne_zero _))
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.CountSpanInt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
open scoped nonZeroDivisors

namespace GlobalTheory.HilbertThetaSeries.DualIdele

variable {K : Type} [Field K] [NumberField K]

theorem count_span_int (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r)) =
      -WithZero.log (v.valuation K (algebraMap (𝓞 K) K r)) := by
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
    (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]),
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hr, WithZero.log_exp,
    neg_neg]

theorem count_span (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = -WithZero.log (v.valuation K x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ x
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hr : r ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs
  have e : IsLocalization.mk' K r s * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K r :=
    IsLocalization.mk'_spec K r s
  have e2 := congrArg (FractionalIdeal.count K v) (congrArg (FractionalIdeal.spanSingleton (𝓞 K)⁰) e)
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hx) ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hs'),
    count_span_int v hs, count_span_int v hr] at e2
  have e3 := congrArg (v.valuation K) e
  rw [map_mul] at e3
  have hv1 : v.valuation K (algebraMap (𝓞 K) K s) ≠ 0 := (map_ne_zero _).mpr hs'
  have hv2 : v.valuation K (IsLocalization.mk' K r s) ≠ 0 := (map_ne_zero _).mpr hx
  rw [← e3, WithZero.log_mul hv2 hv1] at e2
  linarith

theorem exists_ideal (y : (Af K)ˣ) : ∃ I : FractionalIdeal (𝓞 K)⁰ K, I ≠ 0 ∧
    ∀ w, FractionalIdeal.count K w I = -WithZero.log (Valued.v (pLoc K w (y : Af K))) := by
  have hy := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  refine ⟨∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
    (-WithZero.log (Valued.v (pLoc K w (y : Af K)))), ?_, fun w => ?_⟩
  · refine finprod_induction (fun I : FractionalIdeal (𝓞 K)⁰ K => I ≠ 0) one_ne_zero
      (fun _ _ => mul_ne_zero) fun w => zpow_ne_zero _ ?_
    exact FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot
  · refine FractionalIdeal.count_finprod K w (fun w => -WithZero.log (Valued.v (pLoc K w (y : Af K)))) ?_
    filter_upwards [hy] with v hv
    have : Valued.v (pLoc K v (y : Af K)) = 1 := hv
    rw [this, WithZero.log_one, neg_zero]

theorem genD_of_trace : ∀ (F : Type) [Field F] [NumberField F] (y : (Af F)ˣ) (ξ : F), ξ ≠ 0 → (∀ b : F, (∀ w, w.valuation F b ≤ Valued.v (pLoc F w (y : Af F))) → ∃ n : ℤ, Algebra.trace ℚ F (ξ * b) = n) → ∃ 𝔪, GenD (algebraMap F (Af F) ξ * (y : Af F)) 𝔪 := by
  intro F _ _ y ξ hξ h
  obtain ⟨I, hI, hc⟩ := exists_ideal y
  have hy0 : ∀ w, Valued.v (pLoc F w (y : Af F)) ≠ 0 := fun w =>
    (map_ne_zero _).2 ((FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 w)
  have hmem : ξ ∈ FractionalIdeal.dual ℤ ℚ I := by
    rw [FractionalIdeal.mem_dual hI]
    intro b hb
    obtain ⟨n, hn⟩ := h b fun w => by
      rcases eq_or_ne b 0 with rfl | hb0
      · simp
      have h1 := FractionalIdeal.count_mono F w ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hb0)
        (FractionalIdeal.spanSingleton_le_iff_mem.2 hb)
      rw [hc, count_span w hb0, neg_le_neg_iff] at h1
      exact (WithZero.log_le_log ((map_ne_zero _).2 hb0) (hy0 w)).1 h1
    exact ⟨n, by rw [Algebra.traceForm_apply]; simpa using hn.symm⟩
  have hD := FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
  have hd := coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hd0 : (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := hd ▸ inv_ne_zero hD
  have hs0 : FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ ≠ 0 := (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hξ
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ * (I * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)) ≤ 1 := by
    have h1 := FractionalIdeal.spanSingleton_le_iff_mem.2 hmem
    rw [FractionalIdeal.dual_eq_mul_inv] at h1
    refine (mul_le_mul_left h1 _).trans (le_of_eq ?_)
    rw [hd]
    field_simp
  obtain ⟨𝔪, h𝔪⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hm0 : 𝔪 ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.1 (h𝔪 ▸ mul_ne_zero hs0 (mul_ne_zero hI hd0))
  refine ⟨𝔪, hm0, fun w => ?_⟩
  have h2 := congrArg (FractionalIdeal.count F w) h𝔪
  rw [FractionalIdeal.count_mul F w hs0 (mul_ne_zero hI hd0), FractionalIdeal.count_mul F w hI hd0,
    FractionalIdeal.count_coe F w hm0, FractionalIdeal.count_coe F w (FractionalIdeal.coeIdeal_ne_zero.1 hd0),
    hc, count_span w hξ] at h2
  have h3 : Valued.v (pLoc F w (algebraMap F (Af F) ξ)) = w.valuation F ξ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ξ
  have hx0 : w.valuation F ξ ≠ 0 := (map_ne_zero _).2 hξ
  rw [map_mul, map_mul, h3, ← WithZero.exp_log hx0, ← WithZero.exp_log (hy0 w), ← WithZero.exp_add]
  congr 1
  unfold ordI
  linarith

end GlobalTheory.HilbertThetaSeries.DualIdele
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.FormLat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem symm_of_evenPos {G : Matrix κ κ ℤ} (hG : EvenPos G) : Gᵀ = G := by
  have h := hG.1.1
  ext i j
  have := congrFun (congrFun h i) j
  simp [Matrix.conjTranspose_apply, Matrix.map_apply] at this
  simp only [Matrix.transpose_apply]
  exact_mod_cast this

theorem bf_symm {G : Matrix κ κ ℤ} (hG : Gᵀ = G) (x y : κ → F) : BF G x y = BF G y x := by
  unfold BF
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.transpose_map, hG]

theorem bf_add_left (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G (x + y) z = BF G x z + BF G y z := by
  unfold BF; rw [add_dotProduct]

theorem bf_add_right (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G x (y + z) = BF G x y + BF G x z := by
  unfold BF; rw [Matrix.mulVec_add, dotProduct_add]

theorem bf_smul_left (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G (a • x) y = a * BF G x y := by
  unfold BF; rw [smul_dotProduct, smul_eq_mul]

theorem bf_smul_right (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G x (a • y) = a * BF G x y := by
  unfold BF; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem qf_add {G : Matrix κ κ ℤ} (hG : Gᵀ = G) (x y : κ → F) : QF G (x + y) = QF G x + BF G x y + QF G y := by
  unfold QF
  rw [bf_add_left, bf_add_right, bf_add_right, bf_symm hG y x]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  field_simp
  ring

theorem mem_LL {x : κ → F} : x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]

theorem intCast_isIntegral (n : ℤ) : IsIntegral ℤ (n : F) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)

theorem bf_int (G : Matrix κ κ ℤ) {x y : κ → F} (hx : ∀ i, IsIntegral ℤ (x i)) (hy : ∀ i, IsIntegral ℤ (y i)) :
    IsIntegral ℤ (BF G x y) := by
  unfold BF
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
  exact IsIntegral.sum _ fun i _ => (hx i).mul (IsIntegral.sum _ fun j _ => (intCast_isIntegral _).mul (hy j))

theorem trace_int {x : F} (hx : IsIntegral ℤ x) : ∃ n : ℤ, Algebra.trace ℚ F x = n := by
  have := Algebra.isIntegral_trace (L := ℚ) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
  exact ⟨n, by rw [← hn]; simp⟩

theorem qf_single (G : Matrix κ κ ℤ) (i : κ) (c : F) : QF G (Pi.single i c) = c * ((G i i : F) * c) / 2 := by
  simp [QF, BF, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem qf_int {G : Matrix κ κ ℤ} (hG : EvenPos G) {x : κ → F} (hx : ∀ i, IsIntegral ℤ (x i)) : IsIntegral ℤ (QF G x) := by
  have hs : Gᵀ = G := symm_of_evenPos hG
  have hsingle : ∀ i, IsIntegral ℤ (QF G (Pi.single i (x i))) := by
    intro i
    obtain ⟨m, hm⟩ := hG.2 i
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have : QF G (Pi.single i (x i)) = (m : F) * x i * x i := by
      rw [qf_single, hm]; push_cast; field_simp; ring
    rw [this]
    exact ((intCast_isIntegral m).mul (hx i)).mul (hx i)
  have hvi : ∀ (s : Finset κ) (j : κ), IsIntegral ℤ ((∑ i ∈ s, Pi.single i (x i) : κ → F) j) := by
    intro s j
    rw [Finset.sum_apply]
    exact IsIntegral.sum _ fun i _ => by
      by_cases h : j = i
      · subst h; simpa using hx j
      · simp [Pi.single_apply, h, isIntegral_zero]
  have key : ∀ s : Finset κ, IsIntegral ℤ (QF G (∑ i ∈ s, Pi.single i (x i))) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa [QF, BF] using (isIntegral_zero : IsIntegral ℤ (0 : F))
    · intro i s hi ih
      rw [Finset.sum_insert hi, qf_add hs]
      refine ((hsingle i).add (bf_int G ?_ (hvi s))).add ih
      intro j
      by_cases h : j = i
      · subst h; simpa using hx j
      · simp [Pi.single_apply, h, isIntegral_zero]
  simpa [Finset.univ_sum_single] using key Finset.univ

theorem et_props (x y : F) : et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧
    (IsIntegral ℤ x → et x = 1) := by
  have h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hiff : et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n := by
    unfold et
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
        apply mul_left_cancel₀ h0
        rw [hn]; push_cast; ring
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [hn]; push_cast; ring⟩
  refine ⟨?_, ?_, hiff, fun hx => hiff.mpr (trace_int hx)⟩
  · unfold et; rw [map_add (f := _), Rat.cast_add, mul_add, Complex.exp_add]
  · unfold et
    have : 2 * (Real.pi : ℂ) * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ) =
        ((2 * Real.pi * (Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]

end GlobalTheory.HilbertThetaSeries.FormLat


open GlobalTheory.HilbertThetaSeries.FormLat in
theorem GlobalTheory.HilbertThetaSeries.formLatticeProps : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x y : κ → F, BF G x y = BF G y x ∧ QF G (x + y) = QF G x + BF G x y + QF G y) ∧ (∀ (a : F) (x y : κ → F), BF G (a • x) y = a * BF G x y ∧ QF G (a • x) = a ^ 2 * QF G x ∧ QF G (-x) = QF G x) ∧ (∀ x y z : κ → F, BF G (x + y) z = BF G x z + BF G y z) ∧ (∀ x ∈ LL F κ, IsIntegral ℤ (QF G x) ∧ ∀ y ∈ LL F κ, IsIntegral ℤ (BF G x y)) ∧ (∀ x : κ → F, x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i)) ∧ (∀ (a : F) (x : κ → F), x ∈ aL κ a ↔ ∃ l ∈ LL F κ, x = a • l) ∧ (∀ x y : F, et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧ (IsIntegral ℤ x → et x = 1)) ∧ LL F κ ≤ dualL F G := by
  intro F _ _ κ _ _ G hG
  have hs : Gᵀ = G := symm_of_evenPos hG
  refine ⟨fun x y => ⟨bf_symm hs x y, qf_add hs x y⟩, fun a x y => ⟨bf_smul_left G a x y, ?_, ?_⟩,
    bf_add_left G, fun x hx => ⟨qf_int hG (mem_LL.mp hx), fun y hy => bf_int G (mem_LL.mp hx) (mem_LL.mp hy)⟩,
    fun x => mem_LL, fun a x => ?_, et_props, ?_⟩
  · unfold QF; rw [bf_smul_left, bf_smul_right]; ring
  · unfold QF BF; rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  · unfold aL
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
  · intro y hy l hl
    exact trace_int (bf_int G (mem_LL.mp hy) (mem_LL.mp hl))

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenPos_gramForm_integral_lattice_properties : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x y : κ → F, BF G x y = BF G y x ∧ QF G (x + y) = QF G x + BF G x y + QF G y) ∧ (∀ (a : F) (x y : κ → F), BF G (a • x) y = a * BF G x y ∧ QF G (a • x) = a ^ 2 * QF G x ∧ QF G (-x) = QF G x) ∧ (∀ x y z : κ → F, BF G (x + y) z = BF G x z + BF G y z) ∧ (∀ x ∈ LL F κ, IsIntegral ℤ (QF G x) ∧ ∀ y ∈ LL F κ, IsIntegral ℤ (BF G x y)) ∧ (∀ x : κ → F, x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i)) ∧ (∀ (a : F) (x : κ → F), x ∈ aL κ a ↔ ∃ l ∈ LL F κ, x = a • l) ∧ (∀ x y : F, et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧ (IsIntegral ℤ x → et x = 1)) ∧ LL F κ ≤ dualL F G := by
  first | exact @GlobalTheory.HilbertThetaSeries.formLatticeProps | exact GlobalTheory.HilbertThetaSeries.formLatticeProps | (intros; apply GlobalTheory.HilbertThetaSeries.formLatticeProps <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.NotDvdAbsNormOfNotMem
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.IdeleAbs

theorem not_dvd_absNorm_of_not_mem {F : Type} [Field F] [NumberField F] (p : ℕ) [hp : Fact p.Prime]
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) : ¬ p ∣ Ideal.absNorm w.asIdeal := by
  intro h
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have := w.isPrime
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
  have h1 : ((p : ℕ) : 𝓞 F ⧸ w.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.out.one_lt.ne hx
  have h2 : ((p : ℕ) : 𝓞 F ⧸ w.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa using h2

theorem norm_natCast_eq_one (p : ℕ) [Fact p.Prime] (N : ℕ) (h : ¬ p ∣ N) : ‖((N : ℚ) : ℚ_[p])‖ = 1 := by
  rw [Padic.eq_padicNorm]
  exact_mod_cast (padicNorm.nat_eq_one_iff N).2 h

theorem absF_eq_rat (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (z : (Af F)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → Valued.v (pLoc F w (z : Af F)) = 1) :
    ∃ r : ℚ, 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ absF z = r := by
  have key : ∃ r : ℚ, 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ (r : ℝ) = absF z := by
    refine finprod_induction (fun t : ℝ => ∃ r : ℚ, 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ (r : ℝ) = t) ⟨1, one_pos, by simp, by simp⟩ ?_ ?_
    · rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
      exact ⟨a * b, mul_pos ha hb, by rw [Rat.cast_mul, norm_mul, ha', hb', one_mul], by rw [Rat.cast_mul]⟩
    · intro w
      by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
      · refine ⟨1, one_pos, by simp, ?_⟩
        rw [FinitePlace.norm_def, hz w hw, map_one]
        simp
      · have hne : Valued.v (pLoc F w (z : Af F)) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 (z.isUnit.map (pLoc F w)).ne_zero
        have hN : 0 < Ideal.absNorm w.asIdeal :=
          Nat.pos_of_ne_zero fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
        refine ⟨(Ideal.absNorm w.asIdeal : ℚ) ^ (WithZero.unzero hne).toAdd, zpow_pos (by exact_mod_cast hN) _, ?_, ?_⟩
        · rw [Rat.cast_zpow, norm_zpow, norm_natCast_eq_one p _ (not_dvd_absNorm_of_not_mem p w hw), one_zpow]
        · rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hne]
          push_cast
          rw [WithZero.toAdd_unzero_eq_log hne]
  obtain ⟨r, h1, h2, h3⟩ := key
  exact ⟨r, h1, h2, h3.symm⟩

end GlobalTheory.HilbertThetaSeries.IdeleAbs
end

