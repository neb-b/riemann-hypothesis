module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OffDiagonalMatrixUnitsIrreducible
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem offDiagonal_matrixUnits_irreducible :
    (∀ (r p : ℕ), 0 < p → p < r → ∀ W : Submodule ℂ (Fin r → ℂ),
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W,
        (Matrix.single j k (1 : ℂ)).mulVec v ∈ W ∧ (Matrix.single k j (1 : ℂ)).mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤) := by
  intro r p hp hpr W h
  have hs : ∀ (j k : Fin r) (v : Fin r → ℂ),
      (Matrix.single j k (1 : ℂ)).mulVec v = v k • (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
    intro j k v
    ext i
    rw [Matrix.single_mulVec]
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  have key : ∀ (j k : Fin r) (v : Fin r → ℂ), v k ≠ 0 →
      (Matrix.single j k (1 : ℂ)).mulVec v ∈ W → (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W := by
    intro j k v hv hm
    rw [hs] at hm
    exact (W.smul_mem_iff hv).1 hm
  have up : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v k ≠ 0 →
      (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W :=
    fun j k v hj hk hv hvk => key j k v hvk (h j k hj hk v hv).1
  have down : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v j ≠ 0 →
      (Pi.single k (1 : ℂ) : Fin r → ℂ) ∈ W :=
    fun j k v hj hk hv hvj => key k j v hvj (h j k hj hk v hv).2
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hk' : v k ≠ 0 := hk
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨p, hpr⟩
  have ha : (a : ℕ) < p := hp
  have hb : p ≤ (b : ℕ) := le_rfl
  have hbW : (Pi.single b (1 : ℂ) : Fin r → ℂ) ∈ W := by
    rcases lt_or_ge (k : ℕ) p with hkp | hkp
    · exact down k b v hkp hb hv hk'
    · exact down a b _ ha hb (up a k v ha hkp hv hk') (by simp)
  have haW : (Pi.single a (1 : ℂ) : Fin r → ℂ) ∈ W := up a b _ ha hb hbW (by simp)
  have hall : ∀ i : Fin r, (Pi.single i (1 : ℂ) : Fin r → ℂ) ∈ W := by
    intro i
    rcases lt_or_ge (i : ℕ) p with hi | hi
    · exact up i b _ hi hb hbW (by simp)
    · exact down a i _ ha hi haW (by simp)
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact W.sum_mem fun i _ => W.smul_mem _ (hall i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SubspaceSupAlternative
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem subspace_sup_alternative :
    (∀ (K V Y σ : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype σ] (r : ℕ) (t : σ → Y → Y) (D : Y → Submodule K V → ℝ) (α : ℕ → Y → ℝ) (c Ω : ℝ), Module.finrank K V = r → 1 ≤ Ω → (∀ y W, 0 < D y W) → (∀ i ≤ r, ∀ y, IsLUB (D y '' {W | Module.finrank K W = i}) (α i y)) → (∀ y W₁ W₂, D y W₁ * D y W₂ ≤ D y (W₁ ⊓ W₂) * D y (W₁ ⊔ W₂)) → (∀ s y W, D (t s y) W ≤ Ω * D y W ∧ D y W ≤ Ω * D (t s y) W) → (∀ y W, W ≠ ⊥ → W ≠ ⊤ → ∑ s, D (t s y) W ≤ Fintype.card σ * (c * D y W)) → ∃ C : ℝ, 0 ≤ C ∧ (∀ (y : Y) (i : ℕ), 0 < i → i < r → (∑ s, α i (t s y) ≤ Fintype.card σ * (c * α i y)) ∨ ∃ j : ℕ, 0 < j ∧ j ≤ i ∧ i + j ≤ r ∧ ∀ s, α i (t s y) ≤ C * Real.sqrt (α (i - j) y * α (i + j) y))) := by
  intro K V Y σ _ _ _ _ _ r t D α c Ω hr hΩ hpos hlub hsub hmove hcon
  have hΩ0 : 0 < Ω := by linarith
  refine ⟨2 * Ω ^ 3, by positivity, fun y i hi0 hir => ?_⟩
  have hle : ∀ k ≤ r, ∀ z (W : Submodule K V), Module.finrank K W = k → D z W ≤ α k z :=
    fun k hk z W hW => (hlub k hk z).1 ⟨W, hW, rfl⟩
  have hub : ∀ k ≤ r, ∀ z (b : ℝ), (∀ W : Submodule K V, Module.finrank K W = k → D z W ≤ b) →
      α k z ≤ b := fun k hk z b hb => (hlub k hk z).2 (by
        rintro _ ⟨W, hW, rfl⟩
        exact hb W hW)
  have hex : ∀ b < α i y, ∃ W : Submodule K V, Module.finrank K W = i ∧ b < D y W := by
    intro b hb
    by_contra h
    push Not at h
    exact absurd (hub i hir.le y b h) (not_le.2 hb)
  have hA : 0 < α i y := by
    obtain ⟨W, hW, -⟩ := hex (α i y - 1) (by linarith)
    exact (hpos y W).trans_le (hle i hir.le y W hW)
  set A := α i y with hAdef
  set B := A / (2 * Ω ^ 2) with hBdef
  have hB0 : 0 < B := by positivity
  have hAB : A = 2 * Ω ^ 2 * B := by rw [hBdef]; field_simp
  have hBA : B < A := by
    have : 1 ≤ Ω ^ 2 := one_le_pow₀ hΩ
    nlinarith
  obtain ⟨W₀, hW₀, hBW₀⟩ := hex B hBA
  by_cases hcase : ∀ W : Submodule K V, Module.finrank K W = i → B < D y W → W = W₀
  · left
    have h0 : A = D y W₀ := by
      refine le_antisymm (hub i hir.le y _ fun W hW => ?_) (hle i hir.le y W₀ hW₀)
      by_cases h : B < D y W
      · rw [hcase W hW h]
      · exact (not_lt.1 h).trans hBW₀.le
    have h1 : ∀ s, α i (t s y) ≤ D (t s y) W₀ := by
      intro s
      refine hub i hir.le _ _ fun W hW => ?_
      by_cases h : B < D y W
      · rw [hcase W hW h]
      · have a1 := (hmove s y W).1
        have a2 := (hmove s y W₀).2
        have a3 : Ω * D y W ≤ Ω * B := mul_le_mul_of_nonneg_left (not_lt.1 h) hΩ0.le
        have a4 : Ω * (Ω * B) ≤ Ω * D (t s y) W₀ := by
          have : 0 < Ω ^ 2 * B := by positivity
          nlinarith
        have a5 := le_of_mul_le_mul_left a4 hΩ0
        linarith
    have hb : W₀ ≠ ⊥ := by
      rintro rfl
      rw [finrank_bot] at hW₀
      omega
    have ht : W₀ ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hW₀
      omega
    rw [h0]
    exact (Finset.sum_le_sum fun s _ => h1 s).trans (hcon y W₀ hb ht)
  · right
    push Not at hcase
    obtain ⟨W₁, hW₁, hBW₁, hne⟩ := hcase
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₀
    have hlt : Module.finrank K ↥(W₁ ⊓ W₀) < i := by
      rw [← hW₁]
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hne ?_)
      exact Submodule.eq_of_le_of_finrank_eq (inf_eq_left.1 h) (hW₁.trans hW₀.symm)
    have hsr : Module.finrank K ↥(W₁ ⊔ W₀) ≤ r := hr ▸ Submodule.finrank_le _
    refine ⟨i - Module.finrank K ↥(W₁ ⊓ W₀), by omega, by omega, by omega, fun s => ?_⟩
    set j := i - Module.finrank K ↥(W₁ ⊓ W₀) with hj
    have e1 : D y (W₁ ⊓ W₀) ≤ α (i - j) y := hle _ (by omega) y _ (by omega)
    have e2 : D y (W₁ ⊔ W₀) ≤ α (i + j) y := hle _ (by omega) y _ (by omega)
    have e3 : B ^ 2 ≤ α (i - j) y * α (i + j) y := by
      calc B ^ 2 = B * B := sq B
        _ ≤ D y W₁ * D y W₀ := mul_le_mul hBW₁.le hBW₀.le hB0.le (hpos _ _).le
        _ ≤ _ := hsub y W₁ W₀
        _ ≤ _ := mul_le_mul e1 e2 (hpos _ _).le ((hpos _ _).le.trans e1)
    have e4 : B ≤ Real.sqrt (α (i - j) y * α (i + j) y) := Real.le_sqrt_of_sq_le e3
    have e5 : α i (t s y) ≤ Ω * A := hub i hir.le _ _ fun W hW =>
      (hmove s y W).1.trans (mul_le_mul_of_nonneg_left (hle i hir.le y W hW) hΩ0.le)
    calc α i (t s y) ≤ Ω * A := e5
      _ = 2 * Ω ^ 3 * B := by rw [hAB]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TraceMemPrimeOfPowMulVecMemSmul
section
open NumberField

namespace GlobalTheory

open NumberField Polynomial Matrix in
private lemma charpoly_dvd_pow_card_of_aeval_eq_zero {K : Type} [Field K] {r : ℕ} [NeZero r]
    (N : Matrix (Fin r) (Fin r) K) (φ : K[X]) (h : aeval N φ = 0) : N.charpoly ∣ φ ^ r := by
  let Ω := AlgebraicClosure K
  rw [← Polynomial.map_dvd_map' (algebraMap K Ω), Polynomial.map_pow, ← Matrix.charpoly_map]
  set N' := N.map (algebraMap K Ω)
  have hs := IsAlgClosed.splits N'.charpoly
  have hroot : ∀ μ ∈ N'.charpoly.roots, (φ.map (algebraMap K Ω)).IsRoot μ := by
    intro μ hμ
    have h1 := Matrix.mem_spectrum_of_isRoot_charpoly
      ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).1 hμ)
    have h2 := spectrum.subset_polynomial_aeval N' (φ.map (algebraMap K Ω)) ⟨μ, h1, rfl⟩
    have h3 : aeval N' (φ.map (algebraMap K Ω)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]
      have := Polynomial.aeval_algHom_apply
        (AlgHom.mapMatrix (Algebra.ofId K Ω) : Matrix (Fin r) (Fin r) K →ₐ[K] _) N φ
      rw [h, map_zero] at this
      exact this
    rw [h3, spectrum.zero_eq] at h2
    exact h2
  have hcard : N'.charpoly.roots.card = r := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic _)]
  calc (Multiset.map (fun x ↦ X - C x) N'.charpoly.roots).prod
      ∣ (Multiset.map (fun _ ↦ φ.map (algebraMap K Ω)) N'.charpoly.roots).prod :=
        Multiset.prod_dvd_prod_of_dvd _ _ fun μ hμ => Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)
    _ = (φ.map (algebraMap K Ω)) ^ r := by
        rw [Multiset.map_const', Multiset.prod_replicate, hcard]


open NumberField Polynomial Matrix in
theorem _root_.GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (L : Submodule (𝓞 K) (Fin r → K))
      (N : Matrix (Fin r) (Fin r) K) (P : Ideal (𝓞 K)) (n : ℕ), L.FG →
      Submodule.span K (L : Set (Fin r → K)) = ⊤ → P.IsPrime → (∀ x ∈ L, N.mulVec x ∈ L) →
      (∀ x ∈ L, (N ^ n).mulVec x ∈ P • L) → ∃ z ∈ P, ((z : 𝓞 K) : K) = N.trace := by
  intro K _ _ r L N P n hL hspan hP hN hNn
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, P.zero_mem, by simp [Matrix.trace]⟩
  haveI : NeZero r := ⟨hr.ne'⟩
  set m := n + 1 with hm
  have hNm : ∀ x ∈ L, (N ^ m) *ᵥ x ∈ P • L := fun x hx => by
    rw [hm, pow_succ, ← Matrix.mulVec_mulVec]
    exact hNn _ (hN x hx)
  have hLm : ∀ x ∈ L, (N ^ m) *ᵥ x ∈ L := fun x hx => Submodule.smul_le_right (hNm x hx)
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL
  let f : Module.End (𝓞 K) L :=
    ((Matrix.toLin' (N ^ m)).restrictScalars (𝓞 K)).restrict (fun x hx => by
      show Matrix.toLin' (N ^ m) x ∈ L
      rw [Matrix.toLin'_apply]
      exact hLm x hx)
  have hf : ∀ y : L, ((f y : L) : Fin r → K) = (N ^ m) *ᵥ (y : Fin r → K) := fun y => by
    show Matrix.toLin' (N ^ m) (y : Fin r → K) = _
    exact Matrix.toLin'_apply _ _
  have hpow : ∀ (i : ℕ) (y : L), (((f ^ i) y : L) : Fin r → K) = ((N ^ m) ^ i) *ᵥ (y : Fin r → K) := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih => intro y; rw [pow_succ', Module.End.mul_apply, hf, ih, Matrix.mulVec_mulVec, ← pow_succ']
  have hrange : LinearMap.range f ≤ P • ⊤ := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_smul_top_iff, hf]
    exact hNm _ y.2
  obtain ⟨q, hqm, -, hqc, hq0⟩ := LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (𝓞 K) f P hrange
  have hzero : aeval (N ^ m) q = 0 := by
    have hon : ∀ x ∈ L, (aeval (N ^ m) q) *ᵥ x = 0 := by
      intro x hx
      have := congrArg (fun g : Module.End (𝓞 K) L => ((g ⟨x, hx⟩ : L) : Fin r → K)) hq0
      simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply,
        Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply,
        Submodule.coe_zero] at this
      rw [Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans this
      exact Matrix.smul_mulVec _ _ _
    have h1 : Matrix.toLin' (aeval (N ^ m) q) = 0 :=
      LinearMap.ext_on hspan (fun x hx => by simpa using hon x hx)
    exact Matrix.toLin'.injective (h1.trans (map_zero _).symm)
  have hmpos : 0 < m := by omega
  set φ := expand (𝓞 K) m q with hφdef
  have hφm : φ.Monic := hqm.expand hmpos
  have hφ : aeval N (φ.map (algebraMap (𝓞 K) K)) = 0 := by
    rw [aeval_map_algebraMap, hφdef, expand_aeval, hzero]
  have hdvd := charpoly_dvd_pow_card_of_aeval_eq_zero N _ hφ
  rw [← Polynomial.map_pow] at hdvd
  obtain ⟨χ, hχ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (hφm.pow r) hdvd
  rw [(Matrix.charpoly_monic N).leadingCoeff, C_1, mul_one] at hχ
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have hχm : χ.Monic := by
    have := Matrix.charpoly_monic N
    rw [← hχ] at this
    exact Polynomial.monic_of_injective hinj this
  have hχdvd : χ ∣ φ ^ r := (Polynomial.map_dvd_map _ hinj hχm).1 (hχ ▸ hdvd)
  have hχdeg : χ.natDegree = r := by
    rw [← natDegree_map_eq_of_injective hinj, hχ, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hqπ : q.map (Ideal.Quotient.mk P) = X ^ q.natDegree := by
    ext k
    rw [coeff_map, coeff_X_pow]
    rcases lt_trichotomy k q.natDegree with hk | rfl | hk
    · rw [if_neg hk.ne, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_self (by omega) (hqc k)
    · simp [hqm.coeff_natDegree]
    · rw [if_neg hk.ne', coeff_eq_zero_of_natDegree_lt hk, map_zero]
  have hφπ : φ.map (Ideal.Quotient.mk P) = X ^ (m * q.natDegree) := by
    rw [hφdef, map_expand, hqπ, map_pow, expand_X, ← pow_mul]
  have hdvdπ : χ.map (Ideal.Quotient.mk P) ∣ X ^ (m * q.natDegree * r) := by
    rw [pow_mul, ← hφπ, ← Polynomial.map_pow]
    exact Polynomial.map_dvd _ hχdvd
  haveI : IsDomain (𝓞 K ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X _).1 hdvdπ
  have hχπ : χ.map (Ideal.Quotient.mk P) = X ^ i :=
    eq_of_monic_of_associated (hχm.map _) (monic_X_pow i) hi
  have hir : i = r := by
    have := congrArg natDegree hχπ
    rw [hχm.natDegree_map, natDegree_X_pow, hχdeg] at this
    exact this.symm
  have hcoeff : χ.coeff (r - 1) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := congrArg (fun p => p.coeff (r - 1)) hχπ
    simp only [coeff_map, coeff_X_pow, hir] at this
    rw [this, if_neg (by omega)]
  refine ⟨-χ.coeff (r - 1), P.neg_mem hcoeff, ?_⟩
  rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← hχ, coeff_map]
  show algebraMap (𝓞 K) K (-χ.coeff (r - 1)) = _
  rw [map_neg]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UniformLogExpansionOfPointwise
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma re_det_gram_mul_eq_normSq_det_mul {r i : ℕ} (B : Matrix (Fin r) (Fin i) ℂ)
    (X : Matrix (Fin i) (Fin i) ℂ) :
    ((B * X)ᴴ * (B * X)).det.re = Complex.normSq X.det * (Bᴴ * B).det.re := by
  have h : (B * X)ᴴ * (B * X) = Xᴴ * (Bᴴ * B) * X := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [h, det_mul, det_mul, det_conjTranspose, Complex.star_def,
    show (starRingEnd ℂ) X.det * (Bᴴ * B).det * X.det
      = ((Complex.normSq X.det : ℝ) : ℂ) * (Bᴴ * B).det by
        rw [Complex.normSq_eq_conj_mul_self]; ring,
    Complex.re_ofReal_mul]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma norm_apply_le_one_of_conjTranspose_mul_self_eq_one {r i : ℕ} (Q : Matrix (Fin r) (Fin i) ℂ)
    (hQ : Qᴴ * Q = 1) (j : Fin r) (k : Fin i) : ‖Q j k‖ ≤ 1 := by
  have h := congrFun (congrFun hQ k) k
  simp only [Matrix.mul_apply, conjTranspose_apply, one_apply_eq] at h
  have h' : ∑ l, Complex.normSq (Q l k) = 1 := by
    have : ∑ l, ((Complex.normSq (Q l k) : ℝ) : ℂ) = 1 := by
      rw [← h]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    exact_mod_cast this
  have hle : Complex.normSq (Q j k) ≤ 1 :=
    h' ▸ Finset.single_le_sum (fun l _ => Complex.normSq_nonneg (Q l k)) (Finset.mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at hle
  nlinarith [norm_nonneg (Q j k)]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma exists_mul_right_orthonormal_of_re_det_gram_pos {r i : ℕ} (M : Matrix (Fin r) (Fin i) ℂ)
    (hM : 0 < (Mᴴ * M).det.re) :
    ∃ X : Matrix (Fin i) (Fin i) ℂ, (M * X)ᴴ * (M * X) = 1 := by
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self M
  have hunit : IsUnit (Mᴴ * M) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h; rw [h] at hM; simp at hM
  have hPD := hPSD.posDef_iff_isUnit.mpr hunit
  have hpos := hPD.eigenvalues_pos
  have hspec := hPD.1.spectral_theorem
  have hUU : star (hPD.1.eigenvectorUnitary : Matrix (Fin i) (Fin i) ℂ) *
      (hPD.1.eigenvectorUnitary : Matrix (Fin i) (Fin i) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hPD.1.eigenvectorUnitary.2
  simp only [Unitary.conjStarAlgAut_apply] at hspec
  generalize hPD.1.eigenvalues = lam at hpos hspec
  generalize (hPD.1.eigenvectorUnitary : Matrix (Fin i) (Fin i) ℂ) = U at hspec hUU
  refine ⟨U * diagonal (fun k => ((Real.sqrt (lam k))⁻¹ : ℂ)), ?_⟩
  have e1 : ∀ X : Matrix (Fin i) (Fin i) ℂ, (M * X)ᴴ * (M * X) = Xᴴ * (Mᴴ * M) * X := by
    intro X; simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hspec, conjTranspose_mul, ← star_eq_conjTranspose U]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU,
    Matrix.one_mul, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext k
  have hk := hpos k
  have hs0 : ((Real.sqrt (lam k) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hs' : ((Real.sqrt (lam k) : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℝ) : ℂ) = (lam k : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hk.le
  change star ((Real.sqrt (lam k) : ℂ))⁻¹ * (((lam k : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℂ))⁻¹) = 1
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal, ← hs']
  field_simp

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma exists_pos_uniform_le_sum_log_ratio_det_gram {r i : ℕ}
    (S : Finset (Matrix (Fin r) (Fin r) ℂ))
    (hpt : ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (Mᴴ * M).det.re →
      (∀ a ∈ S, 0 < ((a * M)ᴴ * (a * M)).det.re) ∧
      0 < ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re)) :
    ∃ η : ℝ, 0 < η ∧ ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (Mᴴ * M).det.re →
      η ≤ ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) := by
  set F : Matrix (Fin r) (Fin i) ℂ → ℝ :=
    fun M => ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) with hF
  set K : Set (Matrix (Fin r) (Fin i) ℂ) := {Q | Qᴴ * Q = 1} with hK
  have hK1 : ∀ Q ∈ K, 0 < (Qᴴ * Q).det.re := by
    intro Q hQ
    rw [show Qᴴ * Q = 1 from hQ]
    simp
  have hinv : ∀ (M : Matrix (Fin r) (Fin i) ℂ) (X : Matrix (Fin i) (Fin i) ℂ),
      (M * X)ᴴ * (M * X) = 1 → F (M * X) = F M := by
    intro M X hX
    have hone : Complex.normSq X.det * (Mᴴ * M).det.re = 1 := by
      rw [← re_det_gram_mul_eq_normSq_det_mul, hX]; simp
    have hs : Complex.normSq X.det ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hone; exact zero_ne_one hone
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show a * (M * X) = a * M * X from (Matrix.mul_assoc _ _ _).symm,
      re_det_gram_mul_eq_normSq_det_mul, re_det_gram_mul_eq_normSq_det_mul, mul_div_mul_left _ _ hs]
  have hgram : ∀ B : Matrix (Fin r) (Fin i) ℂ → Matrix (Fin r) (Fin i) ℂ, Continuous B →
      Continuous fun Q => ((B Q)ᴴ * B Q).det.re := by
    intro B hB
    exact Complex.continuous_re.comp
      ((hB.matrix_conjTranspose.matrix_mul hB).matrix_det)
  have hclosed : IsClosed K :=
    isClosed_eq ((continuous_id.matrix_conjTranspose).matrix_mul continuous_id) continuous_const
  have hcomp : IsCompact K := by
    refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hclosed ?_
    intro Q hQ
    simp only [Set.mem_pi, Set.mem_univ, Metric.mem_closedBall, dist_zero_right, forall_const]
    exact fun j k => norm_apply_le_one_of_conjTranspose_mul_self_eq_one Q hQ j k
  have hcont : ContinuousOn F K := by
    refine continuousOn_finsetSum _ fun a _ => ?_
    refine ContinuousOn.log ?_ ?_
    · refine ((hgram _ (continuous_const.matrix_mul continuous_id)).continuousOn).div
        (hgram _ continuous_id).continuousOn ?_
      exact fun Q hQ => (hK1 Q hQ).ne'
    · intro Q hQ
      exact (div_pos ((hpt Q (hK1 Q hQ)).1 a ‹_›) (hK1 Q hQ)).ne'
  by_cases hne : K.Nonempty
  · obtain ⟨Q₀, hQ₀, hmin⟩ := hcomp.exists_isMinOn hne hcont
    refine ⟨F Q₀, (hpt Q₀ (hK1 Q₀ hQ₀)).2, fun M hM => ?_⟩
    obtain ⟨X, hX⟩ := exists_mul_right_orthonormal_of_re_det_gram_pos M hM
    show F Q₀ ≤ F M
    rw [← hinv M X hX]
    exact hmin (show M * X ∈ K from hX)
  · refine ⟨1, one_pos, fun M hM => ?_⟩
    obtain ⟨X, hX⟩ := exists_mul_right_orthonormal_of_re_det_gram_pos M hM
    exact absurd ⟨M * X, hX⟩ hne


open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
theorem _root_.GlobalTheory.uniform_log_expansion_of_pointwise :
    (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, 0 < (((a * M)ᴴ * (a * M)).det.re)) ∧ 0 < ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ η : ℝ, 0 < η ∧ ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → η ≤ ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  intro hpt r S hS hirr
  have key : ∀ i : ℕ, ∃ η : ℝ, 0 < η ∧ (0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ,
      0 < (Mᴴ * M).det.re →
      η ≤ ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re)) := by
    intro i
    by_cases hi : 0 < i ∧ i < r
    · obtain ⟨η, hη, h⟩ := exists_pos_uniform_le_sum_log_ratio_det_gram S
        (fun M hM => hpt r S hS hirr i hi.1 hi.2 M hM)
      exact ⟨η, hη, fun _ _ => h⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hi⟩
  choose η hη hb using key
  have hmem1 : (1 : ℝ) ∈ (Finset.range r).image η ∪ {1} :=
    Finset.mem_union_right _ (Finset.mem_singleton_self 1)
  refine ⟨((Finset.range r).image η ∪ {1}).min' ⟨1, hmem1⟩, ?_, ?_⟩
  · rcases Finset.mem_union.mp (Finset.min'_mem _ ⟨1, hmem1⟩) with hy | hy
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hy
      rw [← hj]
      exact hη j
    · rw [Finset.mem_singleton.mp hy]; exact one_pos
  · intro i hi hir M hM
    exact (Finset.min'_le _ _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem η (Finset.mem_range.mpr hir)))).trans (hb i hi hir M hM)

end GlobalTheory
end

