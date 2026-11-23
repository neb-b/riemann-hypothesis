module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace SquareTheorem


open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
theorem _root_.GlobalTheory.LocalQuad.SquareTheorem.isSquare_of_norm_sub_one_lt {K : Type*} [NormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (x : K) (h : ‖x - 1‖ < ‖(4 : K)‖) : IsSquare x := by
  have h4 : (4 : K) ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (norm_nonneg _) h)
  set c : K := (x - 1) / 4 with hc
  have hx : x = 1 + 4 * c := by rw [hc]; field_simp; ring
  have hc1 : ‖c‖ < 1 := by
    rw [hc, norm_div, div_lt_one (norm_pos_iff.2 h4)]; exact h
  set r : ℝ := ‖c‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : ∀ z : K, ‖z‖ ≤ r → ‖z ^ 2‖ ≤ r := by
    intro z hz
    rw [norm_pow]
    calc ‖z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ ≤ r := by nlinarith
  let s := Metric.closedBall (0 : K) r
  haveI : CompleteSpace s := Metric.isClosed_closedBall.completeSpace_coe
  have hmem : ∀ z : s, c - (z : K) ^ 2 ∈ s := by
    intro z
    have hz : ‖(z : K)‖ ≤ r := mem_closedBall_zero_iff.1 z.2
    have hu := IsUltrametricDist.norm_add_le_max c (-((z : K) ^ 2))
    rw [norm_neg, ← sub_eq_add_neg] at hu
    exact mem_closedBall_zero_iff.2 (hu.trans (max_le le_rfl (hsq _ hz)))
  let f : s → s := fun z => ⟨c - (z : K) ^ 2, hmem z⟩
  have hf : ContractingWith ‖c‖₊ f := by
    refine ⟨hc1, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have ha : ‖(a : K)‖ ≤ r := mem_closedBall_zero_iff.1 a.2
    have hb : ‖(b : K)‖ ≤ r := mem_closedBall_zero_iff.1 b.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have : (c - (a : K) ^ 2) - (c - (b : K) ^ 2) = ((b : K) + a) * ((b : K) - a) := by ring
    simp only [f, this, norm_mul, coe_nnnorm]
    rw [norm_sub_rev (b : K)]
    exact mul_le_mul_of_nonneg_right
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ha)) (norm_nonneg _)
  haveI : Nonempty s := ⟨⟨0, by simp [s, hr0]⟩⟩
  set z : s := ContractingWith.fixedPoint f hf
  have hz : (z : K) = c - (z : K) ^ 2 := by
    have := ContractingWith.fixedPoint_isFixedPt (f := f) hf
    exact (congrArg Subtype.val this).symm
  exact ⟨1 + 2 * (z : K), by linear_combination hx - 4 * hz⟩

end SquareTheorem


open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
theorem _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : Valued.v (x - 1) < Valued.v (4 : v.adicCompletion F)) : IsSquare x :=
  _root_.GlobalTheory.LocalQuad.SquareTheorem.isSquare_of_norm_sub_one_lt x (Valued.toNormedField.norm_lt_iff.2 h)

end GlobalTheory.LocalQuad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeAlgebraMapOfConjFixed
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem mem_range_algebraMap_of_conj_fixed (F E : Type) [Field F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (e : E) (he : σ e = e) :
    ∃ c : F, algebraMap F E c = e := by
  have := Subalgebra.isSimpleOrder_of_finrank h2
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
  · have hm : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := by
      rw [AlgHom.mem_equalizer]; simpa using he
    rw [h] at hm
    exact Algebra.mem_bot.mp hm
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hm : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
    rw [AlgHom.mem_equalizer] at hm
    have h1 := hσ τ x
    rw [hm] at h1
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact h1.symm

theorem exists_mul_conj_eq_algebraMap (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (R : Type) [CommRing R] [Algebra F R]
    (y : R ⊗[F] E) :
    ∃ n : R, y * Algebra.TensorProduct.map (AlgHom.id F R) σ y = algebraMap R (R ⊗[F] E) n := by
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hσ, hσ, star_star]
  set φ := Algebra.TensorProduct.map (AlgHom.id F R) σ with hφ
  have key : ∀ y z : R ⊗[F] E, ∃ n : R, y * φ z + z * φ y = algebraMap R (R ⊗[F] E) n := by
    intro y z
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨n₁, h₁⟩ := h₁
      obtain ⟨n₂, h₂⟩ := h₂
      exact ⟨n₁ + n₂, by rw [map_add (f := _), map_add (f := _), ← h₁, ← h₂]; ring⟩
    | tmul a e =>
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add z₁ z₂ h₁ h₂ =>
        obtain ⟨n₁, h₁⟩ := h₁
        obtain ⟨n₂, h₂⟩ := h₂
        exact ⟨n₁ + n₂, by rw [map_add (f := _), map_add (f := _), ← h₁, ← h₂]; ring⟩
      | tmul b f =>
        obtain ⟨c, hc⟩ := mem_range_algebraMap_of_conj_fixed F E σ hE h2 hσ
          (e * σ f + f * σ e) (by rw [map_add (f := _), map_mul, map_mul, hinv, hinv]; ring)
        refine ⟨c • (a * b), ?_⟩
        rw [hφ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          AlgHom.id_apply, AlgHom.id_apply, mul_comm b a, ← TensorProduct.tmul_add, ← hc,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  obtain ⟨n, hn⟩ := key y y
  refine ⟨algebraMap F R (1 / 2) * n, ?_⟩
  have h : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
  have h' : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, h, map_one]
  rw [map_mul, ← hn, ← two_mul, ← mul_assoc, h', one_mul]

theorem exists_unit_mul_conj_eq_algebraMap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → ∀ (R : Type) [CommRing R] [Algebra F R] (x : (R ⊗[F] E)ˣ), ∃ n : Rˣ, (x : R ⊗[F] E) * Algebra.TensorProduct.map (AlgHom.id F R) σ (x : R ⊗[F] E) = algebraMap R (R ⊗[F] E) n := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ R _ _ x
  obtain ⟨n, hn⟩ := exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R (x : R ⊗[F] E)
  obtain ⟨m, hm⟩ := exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R ((x⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap F E).injective
  have hnm : n * m = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hn, ← hm, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, mul_one]
  exact ⟨⟨n, m, hnm, by rw [mul_comm, hnm]⟩, hn⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MinkowskiLinearForms
section
namespace GlobalTheory.MinkowskiLinearForms

open MeasureTheory

theorem minkowski_linear_forms {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : Matrix.det A ≠ (0 : ℝ)) {t : ℝ} (ht : (0 : ℝ) < t)
    (hlt : |Matrix.det A| < t ^ Fintype.card ι) :
    ∃ (z : ι → ℤ), z ≠ (0 : ι → ℤ) ∧ ∀ (j : ι), |∑ i : ι, (↑(z i) : ℝ) * A i j| < t := by
  classical
  have hli : LinearIndependent ℝ (fun i => A i) := Matrix.linearIndependent_rows_of_det_ne_zero hA
  let b : Module.Basis ι ℝ (ι → ℝ) := basisOfPiSpaceOfLinearIndependent hli
  have hb : (⇑b : ι → ι → ℝ) = fun i => A i := coe_basisOfPiSpaceOfLinearIndependent hli
  let L : AddSubgroup (ι → ℝ) := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hF := ZSpan.isAddFundamentalDomain' b (volume : Measure (ι → ℝ))
  let s : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ioo (-t) t
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.neg_apply] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    exact ⟨by linarith, by linarith⟩
  have hconv : Convex ℝ s := convex_pi (fun i _ => convex_Ioo (-t) t)
  have hvolF : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |Matrix.det A| := by
    rw [ZSpan.volume_fundamentalDomain]
    congr 3
  have hvols : volume s = ENNReal.ofReal ((2 * t) ^ Fintype.card ι) := by
    simp only [s, Real.volume_pi_Ioo]
    rw [Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (by linarith)]
    congr 2
    ring
  have hlt' : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (ι → ℝ) < volume s := by
    rw [hvolF, hvols, Module.finrank_fintype_fun_eq_card]
    rw [show (2 : ENNReal) ^ Fintype.card ι = ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [mul_pow, mul_comm ((2:ℝ) ^ _)]
    exact mul_lt_mul_of_pos_right hlt (by positivity)
  haveI hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance
  haveI : Countable L := hcount
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hsymm hconv hlt'
  have hxmem : (x : ι → ℝ) ∈ Submodule.span ℤ (Set.range b) := x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    apply hx0
    ext1
    rw [← hc, hc0]
    simp
  · intro j
    have hxj := hxs j (Set.mem_univ j)
    rw [Set.mem_Ioo] at hxj
    have : (x : ι → ℝ) j = ∑ i, (c i : ℝ) * A i j := by
      rw [← hc, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hb, zsmul_eq_mul]
    rw [← this, abs_lt]
    exact hxj

end GlobalTheory.MinkowskiLinearForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneInfinite
section
namespace GlobalTheory.NormOneInfinite

theorem normOne_infinite {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
    (c : Gal(E/F)) (hc : ∀ x : E, (c : E → E) ((c : E → E) x) = x) (h1 : c ≠ (1 : Gal(E/F))) :
    Set.Infinite {l : E | l * (c : E → E) l = (1 : E)} := by
  have hx : ∃ x : E, c x ≠ x := by
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    exact h1 (AlgEquiv.ext fun x => by rw [hall x, AlgEquiv.one_apply])
  obtain ⟨x, hx⟩ := hx
  have hcd : c (x - c x) = -(x - c x) := by
    rw [map_sub, hc x]
    ring
  have hd : x - c x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcn : ∀ n : ℕ, c (n : E) = n := fun n => map_natCast c n
  have h2d : ∀ y : E, y = -y → y = 0 := by
    intro y hy
    have h2 : (2 : E) * y = 0 := by linear_combination hy
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hsub : ∀ n : ℕ, (n : E) - (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = n := (sub_eq_zero.mp h0).symm
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, hcn]
      _ = -(x - c x) := hcd
  have hadd : ∀ n : ℕ, (n : E) + (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = -(n : E) := by linear_combination h0
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, map_neg, hcn]
      _ = -(x - c x) := hcd
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + (x - c x)) / ((n : E) - (x - c x))) ?_ ?_
  · intro n m hnm
    simp only at hnm
    rw [div_eq_div_iff (hsub n) (hsub m)] at hnm
    have h3 : (2 : E) * (x - c x) * ((m : E) - n) = 0 := by linear_combination hnm
    rcases mul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' two_ne_zero
      · exact absurd h' hd
    · exact (Nat.cast_injective (sub_eq_zero.mp h)).symm
  · intro n
    change ((n : E) + (x - c x)) / ((n : E) - (x - c x)) *
      c (((n : E) + (x - c x)) / ((n : E) - (x - c x))) = 1
    rw [map_div₀, map_add (f := _), map_sub c (n : E) (x - c x), hcn, hcd]
    have h4 : (n : E) + -(x - c x) = (n : E) - (x - c x) := by ring
    have h5 : (n : E) - -(x - c x) = (n : E) + (x - c x) := by ring
    rw [h4, h5, div_mul_div_comm, mul_comm ((n : E) - (x - c x))]
    exact div_self (mul_ne_zero (hadd n) (hsub n))

end GlobalTheory.NormOneInfinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneSubRePosOfNormLeHalf
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem eulerTerm_norm_le_rpow (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  have hn0 : 0 < n := by omega
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  have : (0 : ℝ) ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc ‖c‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) := by gcongr
    _ = (n : ℝ) ^ (-s.re) := one_mul _

theorem eulerTerm_norm_le_half (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 1 < s.re) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  refine (eulerTerm_norm_le_rpow n hn c s hc).trans ?_
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem one_sub_re_pos_of_norm_le_half (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) : 0 < (1 - z).re := by
  rw [Complex.sub_re, Complex.one_re]
  have := Complex.re_le_norm z
  linarith

theorem eulerProduct_eq_exp_and_pos :
    ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → (∀ s : ℂ, 1 < s.re → Summable (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) ∧ HasProd (fun i => (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))))) ∧ ∀ e : ι ≃ ι, (∀ i, N (e i) = N i) → (∀ i, c (e i) = starRingEnd ℂ (c i)) → ∀ s : ℂ, 1 < s.re → s.im = 0 → (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).im = 0 ∧ 0 < (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).re := by
  intro ι N c hN hc hsum
  have hsmall : ∀ s : ℂ, 1 < s.re → ∀ i, ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
    fun s hs i => eulerTerm_norm_le_half (N i) (hN i) (c i) s (hc i) hs
  have hne : ∀ s : ℂ, 1 < s.re → ∀ i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
    intro s hs i h
    have := one_sub_re_pos_of_norm_le_half _ (hsmall s hs i)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hsummable : ∀ s : ℂ, 1 < s.re →
      Summable (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    refine Summable.of_norm_bounded ((hsum s.re hs).mul_left (3 / 2)) (fun i => ?_)
    rw [norm_neg, sub_eq_add_neg]
    refine (Complex.norm_log_one_add_half_le_self (by rw [norm_neg]; exact hsmall s hs i)).trans ?_
    rw [norm_neg]
    gcongr
    exact eulerTerm_norm_le_rpow (N i) (hN i) (c i) s (hc i)
  refine ⟨fun s hs => ⟨hsummable s hs, ?_⟩, ?_⟩
  · convert (hsummable s hs).hasSum.cexp using 1
    funext i
    simp only [Function.comp, Complex.exp_neg, Complex.exp_log (hne s hs i)]
  · intro e hNe hce s hs him
    have hsre : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hreal : ∀ i, starRingEnd ℂ (((N i : ℕ) : ℂ) ^ (-s)) = ((N i : ℕ) : ℂ) ^ (-s) := by
      intro i
      rw [hsre, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.conj_ofReal]
    have hterm : ∀ i, starRingEnd ℂ (-Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) =
        -Complex.log (1 - c (e i) * ((N (e i) : ℕ) : ℂ) ^ (-s)) := by
      intro i
      have harg : (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)).arg ≠ Real.pi := by
        rw [Ne, Complex.arg_eq_pi_iff]
        have := one_sub_re_pos_of_norm_le_half _ (hsmall s hs i)
        intro h
        linarith [h.1]
      rw [map_neg, ← Complex.log_conj _ harg, map_sub, map_one, map_mul, hreal, hce, hNe]
    set S := ∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)) with hS
    have hconj : starRingEnd ℂ S = S := by
      rw [hS, Complex.conj_tsum]
      simp_rw [hterm]
      exact Equiv.tsum_eq e (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))
    have hSim : S.im = 0 := Complex.conj_eq_iff_im.mp hconj
    rw [Complex.exp_im, Complex.exp_re, hSim, Real.sin_zero, Real.cos_zero, mul_zero, mul_one]
    exact ⟨rfl, Real.exp_pos _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RayCharacterExtendsToIdeals
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
  UniqueFactorizationMonoid
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory


open UniqueFactorizationMonoid in
theorem exists_multiplicative_ideal_extension :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (c : HeightOneSpectrum (𝓞 K) → ℂ), (∀ P, ¬ m ≤ P.asIdeal → ‖c P‖ = 1) → ∃ X : Ideal (𝓞 K) → ℂ, X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ ∀ P, ¬ m ≤ P.asIdeal → X P.asIdeal = c P := by
  intro K _ _ m c hc
  let d : Ideal (𝓞 K) → ℂ := fun Q =>
    if h : Q.IsPrime ∧ Q ≠ ⊥ then (if m ≤ Q then 0 else c ⟨Q, h.1, h.2⟩) else 0
  have hd : ∀ P : HeightOneSpectrum (𝓞 K), ¬ m ≤ P.asIdeal → d P.asIdeal = c P := by
    intro P hP
    simp only [d]
    rw [dite_eq_left ⟨P.isPrime, P.ne_bot⟩, if_neg hP]
  have hd0 : ∀ Q, m ≤ Q → d Q = 0 := by
    intro Q hQ
    simp only [d]
    split_ifs <;> rfl
  refine ⟨fun I => if I = ⊥ then 0 else ((normalizedFactors I).map d).prod, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · have : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
    simp only [if_neg this]
    rw [← Ideal.one_eq_top, normalizedFactors_one]
    simp
  · intro I J
    by_cases hI : I = ⊥
    · simp [hI]
    by_cases hJ : J = ⊥
    · simp [hJ]
    have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
    simp only [if_neg hI, if_neg hJ, if_neg hIJ]
    rw [normalizedFactors_mul hI hJ, Multiset.map_add (f := _), Multiset.prod_add]
  · intro I hI hm
    simp only [if_neg hI]
    refine Multiset.prod_induction (fun z : ℂ => ‖z‖ = 1) _ ?_ (by simp) ?_
    · intro a b ha hb
      simp [ha, hb]
    · intro a ha
      obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 ha
      have hp : Prime Q := prime_of_normalized_factor Q hQ
      have hle : I ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
      have hQp : Q.IsPrime := Ideal.isPrime_of_prime hp
      have hm' : ¬ m ≤ Q := fun h => hQp.ne_top (top_le_iff.1 (hm ▸ sup_le hle h))
      have := hd ⟨Q, hQp, hp.ne_zero⟩ hm'
      simp only at this
      rw [this]
      exact hc _ hm'
  · intro I hm
    by_cases hI : I = ⊥
    · simp [hI]
    simp only [if_neg hI]
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hm
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.2 ⟨Q, ?_, hd0 Q (le_sup_right.trans hle)⟩
    exact (Ideal.mem_normalizedFactors_iff hI).2 ⟨hQ.isPrime, le_sup_left.trans hle⟩
  · intro P hP
    simp only [if_neg P.ne_bot]
    rw [normalizedFactors_irreducible P.irreducible, normalize_eq]
    simp [hd P hP]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealEqSumClassGroup
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.existsUnique_isPrincipal_mul_classRep {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃! c, (I * (b c : Ideal (𝓞 K))).IsPrincipal := by
  have hI0 : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  have key : ∀ c, (I * (b c : Ideal (𝓞 K))).IsPrincipal ↔
      ClassGroup.mk0 (b c) = (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹ := by
    intro c
    rw [eq_inv_iff_mul_eq_one, mul_comm, ← map_mul]
    rw [ClassGroup.mk0_eq_one_iff]
    rfl
  obtain ⟨c, hc⟩ := hb.2 (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹
  refine ⟨c, (key c).2 hc, fun c' hc' => hb.1 ?_⟩
  simp only
  rw [(key c').1 hc']
  exact hc.symm


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.tsum_isPrincipal_mul_eq {K : Type} [Field K] [NumberField K]
    (B : Ideal (𝓞 K)) (hB : B ≠ ⊥) (F : Ideal (𝓞 K) → ℂ) :
    ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * B).IsPrincipal}, F (I * B) =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B}, F J := by
  let e : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * B).IsPrincipal} →
      {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B} :=
    fun I => ⟨I.1 * B, mul_ne_zero I.2.1 hB, I.2.2, Ideal.mul_le_inf.trans inf_le_right⟩
  have he : Function.Bijective e := by
    constructor
    · intro I I' h
      have h' : I.1 * B = I'.1 * B := congrArg Subtype.val h
      exact Subtype.ext (mul_right_cancel₀ hB h')
    · intro J
      obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 J.2.2.2
      have hI0 : I ≠ ⊥ := by
        rintro rfl
        exact J.2.1 (by rw [hI, Ideal.mul_bot])
      refine ⟨⟨I, hI0, ?_⟩, Subtype.ext ?_⟩
      · rw [mul_comm, ← hI]; exact J.2.2.1
      · show I * B = J.1
        rw [hI, mul_comm]
  exact (Equiv.ofBijective e he).tsum_eq (fun J => F J.1)

end GlobalTheory
end

