module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IntegralStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

noncomputable section

section Cone

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

def cone (a : ι → E) : MvPolynomial ι R →ₐ[R] Polynomial E :=
  aeval fun i => Polynomial.C (a i) * Polynomial.X

theorem cone_homog (a : ι → E) {f : MvPolynomial ι R} {d : ℕ} (hf : f.IsHomogeneous d) :
    cone a f = Polynomial.monomial d (aeval a f) := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have hp : (m.prod fun i k => (Polynomial.C (a i) * Polynomial.X) ^ k) =
      Polynomial.C (m.prod fun i k => a i ^ k) * Polynomial.X ^ d := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
      Finset.prod_pow_eq_pow_sum, hd]
  rw [cone, aeval_monomial, aeval_monomial, hp, Polynomial.algebraMap_apply, ← mul_assoc,
    ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_cone (a : ι → E) (f : MvPolynomial ι R) (n : ℕ) :
    (cone a f).coeff n = aeval a (homogeneousComponent n f) := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff]
  simp_rw [cone_homog a (homogeneousComponent_isHomogeneous _ f), Polynomial.coeff_monomial_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp at h; omega), map_zero]

theorem aeval_mul_homog (q : ι → E) (t : E) {G : MvPolynomial ι R} {m : ℕ} (hG : G.IsHomogeneous m) :
    aeval (fun i => q i * t) G = t ^ m * aeval q G := by
  have h := congrArg ((Polynomial.aeval t : Polynomial E →ₐ[E] E).restrictScalars R)
    (cone_homog (R := R) q hG)
  rw [cone, MvPolynomial.comp_aeval_apply] at h
  simp only [AlgHom.restrictScalars_apply, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Polynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h, mul_comm]

theorem eval_mul_homog {K : Type*} [CommRing K] (q : ι → K) (t : K) {G : MvPolynomial ι K} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => q i * t) G = t ^ m * eval q G := by
  simpa using aeval_mul_homog (R := K) q t hG

end Cone

open MvPolynomial in
theorem exists_cons_one_ne {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    {G : MvPolynomial (Fin (n + 1)) K} (hG : G.IsHomogeneous m) (h0 : G ≠ 0) :
    ∃ c : Fin n → K, eval (Fin.cons 1 c) G ≠ 0 := by
  by_contra! h
  apply h0
  have hX : (X 0 * G : MvPolynomial (Fin (n + 1)) K) = 0 := by
    apply MvPolynomial.funext
    intro p
    rw [map_mul, eval_X, map_zero]
    by_cases hp : p 0 = 0
    · rw [hp, zero_mul]
    · have hq : p = fun i => (Fin.cons 1 (fun k => p k.succ / p 0) : Fin (n + 1) → K) i * p 0 := by
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp
        · simp [div_mul_cancel₀ _ hp]
      have : eval p G = 0 := by
        rw [hq]
        rw [eval_mul_homog _ _ hG, h, mul_zero]
      rw [this, mul_zero]
  exact (mul_eq_zero.mp hX).resolve_left (X_ne_zero _)

section Int

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

end Int

section Homog

open Polynomial

theorem prod_pow_natDegree_coeff' {B : Type*} [CommRing B] {ι : Type*} (s : Finset ι)
    (v : ι → B[X]) (d : ι → ℕ) (hv : ∀ i, (v i).natDegree ≤ 1) :
    (∏ i ∈ s, v i ^ d i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, v i ^ d i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (v i).coeff 1 ^ d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨hDegree, hCoeff⟩ := ih
    have haDegree : (v a ^ d a).natDegree ≤ d a := by
      simpa using natDegree_pow_le_of_le (d a) (hv a)
    have haCoeff : (v a ^ d a).coeff (d a) = (v a).coeff 1 ^ d a := by
      simpa using coeff_pow_of_natDegree_le (m := d a) (hv a)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨natDegree_mul_le.trans (add_le_add haDegree hDegree), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le haDegree hDegree, haCoeff, hCoeff]

end Homog

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix

noncomputable section

theorem det_of_key {m α : Type*} [Fintype m] [DecidableEq m] [LinearOrder α] {R : Type*} [CommRing R]
    (M : Matrix m m R) (κ : m → α) (hκ : Function.Injective κ)
    (h : ∀ i j, κ i < κ j → M i j = 0) : M.det = ∏ i, M i i := by
  letI : LinearOrder m := LinearOrder.lift' (fun i => OrderDual.toDual (κ i))
    (fun a b hab => hκ (OrderDual.toDual.injective hab))
  exact Matrix.det_of_upperTriangular (fun i j hij => h i j hij)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

abbrev Ix (ι : Type*) (r : ℕ) : Type _ := ι × Fin r × Fin r

def sl (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then w (τ, a, b) else 0

def up (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then 0 else w (τ, a, b)

def lu (w : Ix ι r → ℂ) : Ix ι r → ℂ := fun i => ((1 + sl w i.1) * up w i.1) i.2.1 i.2.2

lemma sl_add (h h' : Ix ι r → ℂ) (τ : ι) : sl (h + h') τ = sl h τ + sl h' τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma up_add (h h' : Ix ι r → ℂ) (τ : ι) : up (h + h') τ = up h τ + up h' τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma sl_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : sl (c • h) τ = c • sl h τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma up_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : up (c • h) τ = c • up h τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def luD (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →ₗ[ℂ] (Ix ι r → ℂ) where
  toFun h i := (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2
  map_add' h h' := by
    funext i
    simp only [sl_add, up_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply, Pi.add_apply]
    ring
  map_smul' c h := by
    funext i
    simp only [sl_smul, up_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    ring

def key (e : ι ≃ Fin (Fintype.card ι)) (i : Ix ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.2.1 : ℕ) + i.2.2, toLex ((i.2.1 : ℕ), e i.1))

lemma key_injective (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (key (r := r) e) := by
  rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : a = a' := Fin.ext h2
  have hb : b = b' := Fin.ext (by omega)
  have hτ : τ = τ' := e.injective h3
  subst ha hb hτ
  rfl

lemma key_le_of (e : ι ≃ Fin (Fintype.card ι)) (τ : ι) {a b a' b' : Fin r} (h1 : (a' : ℕ) + b' ≤ a + b)
    (h2 : (a' : ℕ) ≤ a) : key e (τ, a', b') ≤ key e (τ, a, b) := by
  rw [Prod.Lex.le_iff]
  simp only [key, ofLex_toLex]
  rcases h1.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    rw [Prod.Lex.le_iff]
    simp only [ofLex_toLex]
    rcases h2.lt_or_eq with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', le_rfl⟩

lemma luD_apply (w h : Ix ι r → ℂ) (i : Ix ι r) :
    luD w h i = ∑ k, sl h i.1 i.2.1 k * up w i.1 k i.2.2 + ∑ k, (1 + sl w i.1) i.2.1 k * up h i.1 k i.2.2 := by
  show (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2 = _
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]

lemma one_add_sl_zero (w : Ix ι r → ℂ) (τ : ι) {a k : Fin r} (h : a < k) : (1 + sl w τ) a k = 0 := by
  rw [Matrix.add_apply, Matrix.one_apply_ne h.ne]
  simp [sl, not_lt.mpr h.le]

lemma toMatrix_luD_zero (e : ι ≃ Fin (Fintype.card ι)) (w : Ix ι r → ℂ) (i j : Ix ι r)
    (hij : key e i < key e j) : LinearMap.toMatrix' (luD w) i j = 0 := by
  obtain ⟨τ, a, b⟩ := i
  rw [LinearMap.toMatrix'_apply, luD_apply]
  have hne : ∀ a' b' : Fin r, (a' : ℕ) + b' ≤ a + b → (a' : ℕ) ≤ a → (τ, a', b') ≠ j := by
    rintro a' b' h1 h2 rfl
    exact absurd (key_le_of e τ h1 h2) (not_le.mpr hij)
  have hs1 : ∀ k : Fin r, sl (Pi.single j (1 : ℂ)) τ a k * up w τ k b = 0 := by
    intro k
    by_cases hka : k < a
    · by_cases hbk : b < k
      · simp [Pi.single_apply, up, hbk]
      · have := hne a k (by omega) le_rfl
        simp [Pi.single_apply, sl, hka, this]
    · simp [Pi.single_apply, sl, hka]
  have hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single j (1 : ℂ)) τ k b = 0 := by
    intro k
    by_cases hka : a < k
    · rw [one_add_sl_zero w τ hka, zero_mul]
    · by_cases hbk : b < k
      · simp [Pi.single_apply, up, hbk]
      · have := hne k b (by omega) (by omega)
        simp [Pi.single_apply, up, hbk, this]
  rw [Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]
  simp

lemma toMatrix_luD_diag (w : Ix ι r → ℂ) (i : Ix ι r) :
    LinearMap.toMatrix' (luD w) i i = if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by
  obtain ⟨τ, a, b⟩ := i
  rw [LinearMap.toMatrix'_apply, luD_apply]
  have hs1 : ∀ k : Fin r, sl (Pi.single (τ, a, b) (1 : ℂ)) τ a k * up w τ k b =
      if k = b then (if b < a then w (τ, b, b) else 0) else 0 := by
    intro k
    by_cases hkb : k = b
    · subst hkb
      by_cases hka : k < a <;> simp [Pi.single_apply, sl, up, hka]
    · simp [Pi.single_apply, sl, hkb]
  have hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single (τ, a, b) (1 : ℂ)) τ k b =
      if k = a then (if b < a then 0 else 1) else 0 := by
    intro k
    by_cases hka : k = a
    · subst hka
      by_cases hbk : b < k <;> simp [Pi.single_apply, sl, up, hbk]
    · simp [Pi.single_apply, up, hka]
  rw [Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp

theorem det_luD (w : Ix ι r → ℂ) :
    LinearMap.det (luD w) = ∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by
  rw [← LinearMap.det_toMatrix', det_of_key _ (key (r := r) (Fintype.equivFin ι))
    (key_injective _) (fun i j h => toMatrix_luD_zero _ w i j h)]
  exact Finset.prod_congr rfl fun i _ => toMatrix_luD_diag w i

def luD' (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →L[ℝ] (Ix ι r → ℂ) :=
  LinearMap.toContinuousLinearMap ((luD w).restrictScalars ℝ)

lemma hasFDerivAt_entry1 (w : Ix ι r → ℂ) (τ : ι) (a k : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => (1 + sl v τ) a k)
      (if k < a then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, a, k) else 0) w := by
  by_cases hk : k < a
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun v => (1 : Matrix (Fin r) (Fin r) ℂ) a k + v (τ, a, k) := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact (hasFDerivAt_apply (𝕜 := ℝ) (τ, a, k) w).const_add _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) a k := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact hasFDerivAt_const _ _

lemma hasFDerivAt_entry2 (w : Ix ι r → ℂ) (τ : ι) (k b : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => up v τ k b)
      (if b < k then 0 else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, k, b)) w := by
  by_cases hk : b < k
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun _ => (0 : ℂ) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_const _ _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun v => v (τ, k, b) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_apply (𝕜 := ℝ) (τ, k, b) w

theorem hasFDerivAt_lu (w : Ix ι r → ℂ) : HasFDerivAt lu (luD' w) w := by
  rw [hasFDerivAt_pi']
  rintro ⟨τ, a, b⟩
  have hf : (fun v : Ix ι r → ℂ => lu v (τ, a, b)) =
      fun v => ∑ k, (1 + sl v τ) a k * up v τ k b := by
    funext v
    simp only [lu, Matrix.mul_apply]
  rw [hf]
  have hd := HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (hasFDerivAt_entry1 w τ a k).mul (hasFDerivAt_entry2 w τ k b))
  convert (preTransparency := .reducible) hd using 1
  · funext v
    simp only [Finset.sum_apply, Pi.mul_apply]
  · apply ContinuousLinearMap.ext
    intro h
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.sum_apply]
    change luD w h (τ, a, b) = _
    rw [luD_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hka : k < a <;> by_cases hbk : b < k <;> simp [hka, hbk, sl, up] <;> ring

theorem det_luD' (w : Ix ι r → ℂ) :
    (luD' w).det = Complex.normSq (∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1) := by
  rw [← det_luD w, ← Algebra.norm_complex_apply]
  show LinearMap.det ((luD w).restrictScalars ℝ) = _
  exact LinearMap.det_restrictScalars

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfG
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

theorem amgm {k x y : ℝ} (hk : 0 < k) : x * y ≤ (x ^ 2 / k + k * y ^ 2) / 2 := by
  have h : 0 ≤ (x - k * y) ^ 2 / k := by positivity
  have e : (x - k * y) ^ 2 / k = x ^ 2 / k - 2 * (x * y) + k * y ^ 2 := by
    field_simp
    ring
  linarith

theorem I_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : α → ℝ} {g u : α → ℂ}
    {w : α → ℝ≥0∞} {q : ℝ} (hk : ∀ᵐ a ∂μ, 0 < k a) (hw : ∀ᵐ a ∂μ, w a < ⊤) (hq1 : q < 1)
    (hq0 : 0 ≤ q) (hkm : AEMeasurable k μ) (hgm : AEMeasurable g μ) (hum : AEMeasurable u μ)
    (hwm : AEMeasurable w μ)
    (hI : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ < ⊤)
    (hJ : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ ≤
      ENNReal.ofReal q * ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ)
    (h0 : ∫ a, ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ) ∂μ = 0) :
    ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ = 0 := by
  have hWm : AEMeasurable (fun a => (w a).toReal) μ := hwm.ennreal_toReal
  have hF1m : AEMeasurable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    (hkm.mul (hgm.norm.pow_const 2)).mul hWm
  have hF2m : AEMeasurable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ((hum.norm.pow_const 2).div hkm).mul hWm
  have hF1nn : 0 ≤ᵐ[μ] fun a => k a * ‖g a‖ ^ 2 * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) ENNReal.toReal_nonneg
  have hF2nn : 0 ≤ᵐ[μ] fun a => ‖u a‖ ^ 2 / k a * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (div_nonneg (sq_nonneg _) ha.le) ENNReal.toReal_nonneg
  have hA : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (mul_nonneg ha.le (sq_nonneg _)), ENNReal.ofReal_toReal hwa.ne]
  have hB : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) ha.le), ENNReal.ofReal_toReal hwa.ne]
  rw [hA] at hI hJ ⊢
  rw [hB] at hJ
  have hJfin : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ < ⊤ :=
    lt_of_le_of_lt hJ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)
  have hF1i : Integrable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    ⟨hF1m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF1nn).2 hI⟩
  have hF2i : Integrable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ⟨hF2m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF2nn).2 hJfin⟩
  have hint1 : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF1nn hF1m.aestronglyMeasurable
  have hint2 : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF2nn hF2m.aestronglyMeasurable
  have hPm : AEStronglyMeasurable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    ((hum.mul (Complex.continuous_conj.measurable.comp_aemeasurable hgm)).mul
      (Complex.measurable_ofReal.comp_aemeasurable hWm)).aestronglyMeasurable
  have hPbd : ∀ᵐ a ∂μ, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ≤
      (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 := by
    filter_upwards [hk] with a ha
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    have h1 := amgm (k := k a) (x := ‖u a‖) (y := ‖g a‖) ha
    have hW0 : 0 ≤ (w a).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right h1 hW0]
  have hbdi : Integrable (fun a => (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2) μ :=
    (hF2i.add hF1i).div_const 2
  have hPi : Integrable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    Integrable.mono' hbdi hPm hPbd
  have hF1c : Integrable (fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ)) μ := hF1i.ofReal
  have hsplit : (fun a => ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ)) =
      fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ) - u a * conj (g a) * ((w a).toReal : ℂ) := by
    funext a
    rw [sub_mul, sub_mul, mul_assoc (k a : ℂ) (g a) (conj (g a)), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hsplit, integral_sub hF1c hPi, integral_complex_ofReal, sub_eq_zero] at h0
  have hn : 0 ≤ ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := integral_nonneg_of_ae hF1nn
  have hle : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ ≤
      ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
    calc ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ
        = ‖((∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hn]
      _ = ‖∫ a, u a * conj (g a) * ((w a).toReal : ℂ) ∂μ‖ := by rw [h0]
      _ ≤ ∫ a, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ a, (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 ∂μ :=
          integral_mono_ae hPi.norm hbdi hPbd
      _ = ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
          rw [integral_div, integral_add hF2i hF1i]
  have hJr : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ ≤ q * ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := by
    rw [hint1, hint2]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hJ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0] at this
  have hz : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq1.le) hn]
  rw [hint1] at hz
  exact ((ENNReal.toReal_eq_zero_iff _).1 hz).resolve_right hI.ne

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PG

open MvPolynomial

variable {D : ℕ}

noncomputable def lineHom (a w : Fin D → ℂ) : MvPolynomial (Fin D) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval fun i => Polynomial.C (a i) + Polynomial.C (w i) * Polynomial.X

theorem eval_lineHom (a w : Fin D → ℂ) (F : MvPolynomial (Fin D) ℂ) (s : ℂ) :
    (lineHom a w F).eval s = eval (fun i => a i + w i * s) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [lineHom]
  | add p q hp hq => rw [map_add (f := _), Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    simp [lineHom]

end ReciprocityTheory.ChartRestriction.G.AR.Up.PG
end

