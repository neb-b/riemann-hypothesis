module

public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.Bundle0001
public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SelectionLemmas
public import Formalism.LogFactorialBounds.LogFactorialProofs.PrimeSum

@[expose] public section

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

theorem log_abs_norm_eq_two_sum (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (a : K) (ha : a ≠ 0) :
    Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| =
      2 * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ := by
  have h := NumberField.InfinitePlace.prod_eq_abs_norm a
  have hm : ∀ w : InfinitePlace K, w.mult = 2 := fun w => by
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w))]
  have hpos : ∀ w : InfinitePlace K, w a ≠ 0 := fun w => by
    rw [← InfinitePlace.norm_embedding_eq]
    simpa using ha
  rw [← Rat.cast_abs, ← h, Real.log_prod (fun w _ => pow_ne_zero _ (hpos w)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hm, Real.log_pow, InfinitePlace.norm_embedding_eq]
  push_cast
  ring

theorem prod_formula' : ProdFormula := by
  intro K _ _ _ _ a ha
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := FractionalIdeal.spanSingleton _ a with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha
  have hfin : {w : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K w I ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  have hvw : ∀ w : HeightOneSpectrum (𝓞 K), vw w a = FractionalIdeal.count K w I := fun w => rfl
  have hsupp : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)) ⊆
      (hfin.toFinset : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    simp only [Function.mem_support, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
    intro h0
    apply hw
    simp [hvw, h0]
  refine ⟨hfin.subset (by simpa using hsupp), ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hpos : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := fun w => by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hN : (|Algebra.norm ℚ a| : ℚ) = ∏ w ∈ hfin.toFinset,
      ((Ideal.absNorm w.asIdeal : ℚ)) ^ FractionalIdeal.count K w I := by
    rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), ← hIdef]
    conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) ?_, map_prod]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    · intro w hw
      simp only [Function.mem_mulSupport, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
      intro h0
      apply hw
      rw [h0, zpow_zero]
  have hlog : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ w ∈ hfin.toFinset,
      (FractionalIdeal.count K w I : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) := by
    have h1 : |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ w ∈ hfin.toFinset,
        ((Ideal.absNorm w.asIdeal : ℝ)) ^ FractionalIdeal.count K w I := by
      rw [← Rat.cast_abs, hN]
      push_cast
      rfl
    rw [h1, Real.log_prod (fun w _ => zpow_ne_zero _ (hpos w))]
    exact Finset.sum_congr rfl fun w _ => Real.log_zpow _ _
  have hB := log_abs_norm_eq_two_sum K a ha
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  calc (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖
      = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / finrank ℚ K := by
        rw [hB]
        field_simp
    _ = ∑ w ∈ hfin.toFinset, lw w * (vw w a : ℝ) := by
        rw [hlog, Finset.sum_div]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hvw, lw]
        ring

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
section
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ReductionFirst

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def Tw (w : HeightOneSpectrum (𝓞 K)) : Submonoid (𝓞 K) where
  carrier := {s | s ∉ w.asIdeal ∧ cO K s ∉ w.asIdeal}
  one_mem' := by
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    exact ⟨h1, by simpa using h1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha h, hb h]
    · rw [map_mul] at h
      rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha' h, hb' h]

theorem cO_coe (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem cO_cO (x : 𝓞 K) : cO K (cO K x) = x := by
  apply RingOfIntegers.ext
  rw [cO_coe, cO_coe, star_star]

theorem cO_mem_Tw {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : cO K s ∈ Tw w :=
  ⟨hs.2, by rw [cO_cO]; exact hs.1⟩

theorem hcompl_le_Tw (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ Tw w := by
  refine Submonoid.closure_le.2 ?_
  rintro s ⟨hs, hs'⟩
  exact ⟨hs, hs' (cO K s) rfl⟩

theorem smul_coe {m : Type*} (r : 𝓞 K) (v : m → K) : r • v = (r : K) • v :=
  (algebraMap_smul K r v).symm

theorem vw_mul (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 ha)
      (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hb)]

theorem vw_pow (w : HeightOneSpectrum (𝓞 K)) (a : K) (m : ℕ) :
    vw w (a ^ m) = (m : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

theorem vw_int_nonneg (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) : 0 ≤ vw w (r : K) := by
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_unit (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (hr : r ∉ w.asIdeal) :
    vw w (r : K) = 0 := by
  classical
  have hr0 : r ≠ 0 := fun h => hr (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {r} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr0
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w hJ]
  have h2 : ¬ w.asIdeal ∣ Ideal.span {r} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hr
  have h3 := mt (Associates.count_ne_zero_iff_dvd hJ w.irreducible).1 h2
  rw [not_not] at h3
  simp [h3]

theorem Tw_ne_zero {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : (s : K) ≠ 0 := by
  intro h
  apply hs.1
  have : s = 0 := RingOfIntegers.ext (by simpa using h)
  rw [this]; exact w.asIdeal.zero_mem

theorem main {n D : ℕ} (H : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin D) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : M.FG) (l g : ℕ) (hl : 0 < l)
    (hdual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H) M, ((l : 𝓞 K) ^ g) • x ∈ M)
    (w : HeightOneSpectrum (𝓞 K)) (e : Fin D → Fin D → K) (he : IsLocBasis (matLat P M) w e) :
    vw w (gramR (quotGram P H) e) ≤ (g : ℤ) * (D : ℤ) * vw w (l : K) :=
  _root_.UpperTheory.Reformulated.B.SelectionLemmas.main H P M hM l g hl hdual w e he

end ReductionFirst

theorem reduction_lemma_first : LemmaRa := by
  intro K _ _ _ _ K0 _ v0 _ n D H _ _ P _ M hM l g hl hdual w e he
  exact ReductionFirst.main H P M hM.fg l g hl hdual w e he

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SpecDet
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section SpecDetAux

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def metMat {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((X v)⁻¹).conjTranspose * (X v)⁻¹

def cv {d : ℕ} (σ : K →+* ℂ) (x : Fin d → K) : Fin d → ℂ := fun i => σ (x i)

lemma star_mulVec_dot {d : ℕ} (A N : Matrix (Fin d) (Fin d) ℂ) (u w : Fin d → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (N *ᵥ (A *ᵥ w)) = star u ⬝ᵥ ((Aᴴ * N * A) *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

lemma majAt_eq {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y =
      star (cv v.embedding x) ⬝ᵥ (metMat X v *ᵥ cv v.embedding y) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
  rw [metMat, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl

lemma cv_mulVec {d : ℕ} (σ : K →+* ℂ) (φ : Matrix (Fin d) (Fin d) K) (x : Fin d → K) :
    cv σ (φ *ᵥ x) = (φ.map σ) *ᵥ cv σ x := by
  ext i
  exact RingHom.map_mulVec σ φ x i

lemma cv_single {d : ℕ} (σ : K →+* ℂ) (a : Fin d) :
    cv σ (Pi.single a (1 : K)) = Pi.single a (1 : ℂ) := by
  ext i
  rcases eq_or_ne i a with rfl | h
  · simp [cv]
  · simp [cv, Pi.single_eq_of_ne h]

lemma single_dot_single {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    star (Pi.single a (1 : ℂ)) ⬝ᵥ (N *ᵥ Pi.single b (1 : ℂ)) = N a b := by
  have hs : star (Pi.single a (1 : ℂ) : Fin d → ℂ) = Pi.single a 1 := by
    ext i
    rcases eq_or_ne i a with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  rw [hs]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

lemma conjT_mul_mul_apply {n : ℕ} (A N : Matrix (Fin n) (Fin n) ℂ) (a a' : Fin n) :
    (Aᴴ * N * A) a a' = star (fun i => A i a) ⬝ᵥ (N *ᵥ fun i => A i a') := by
  have hcol : ∀ c, A *ᵥ Pi.single c (1 : ℂ) = fun i => A i c := by
    intro c
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← single_dot_single (Aᴴ * N * A) a a', ← star_mulVec_dot, hcol, hcol]

lemma detRatio_eq {d : ℕ} (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (φ : Matrix (Fin d) (Fin d) K) (v : InfinitePlace K) :
    detRatio XS XT φ v =
      ((φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding).det.re / (metMat XS v).det.re := by
  have h1 : gram XT v (fun i => φ.mulVec (Pi.single i 1)) =
      (φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding := by
    ext a c
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply]
    rw [majAt_eq, cv_mulVec, cv_mulVec, cv_single, cv_single, star_mulVec_dot, single_dot_single]
  have h2 : gram XS v (fun i => (Pi.single i 1 : Fin d → K)) = metMat XS v := by
    ext a c
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply]
    rw [majAt_eq, cv_single, cv_single, single_dot_single]
  rw [detRatio, h1, h2]

lemma metMat_det_re_ne {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (hX : IsUnit (X v).det) : (metMat X v).det.re ≠ 0 := by
  have hY : ((X v)⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det (X v) hX).ne_zero
  have hm : (metMat X v).det = (Complex.normSq ((X v)⁻¹).det : ℂ) := by
    rw [metMat, Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hm, Complex.ofReal_re]
  exact (Complex.normSq_pos.mpr hY).ne'

lemma det_of_scalar {D : ℕ} (σ : K →+* ℂ) {Ix : Type} [Fintype Ix]
    (Qp : Ix → Submodule K (Fin D → K)) (hind : iSupIndep Qp) (htop : (⨆ p, Qp p) = ⊤)
    (N1 N2 : Matrix (Fin D) (Fin D) ℂ) (c : Ix → ℂ)
    (h : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      star (cv σ x) ⬝ᵥ (N1 *ᵥ cv σ y) = c p * (star (cv σ x) ⬝ᵥ (N2 *ᵥ cv σ y))) :
    N1.det = (∏ p, c p ^ finrank K (Qp p)) * N2.det ∧ ∑ p, finrank K (Qp p) = D := by
  classical
  have hint : DirectSum.IsInternal Qp :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Qp).mpr ⟨hind, htop⟩
  let b := hint.collectedBasis (fun p => Module.finBasis K (Qp p))
  have hcard : Fintype.card (Σ p, Fin (finrank K (Qp p))) = D := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  have hsum : ∑ p, finrank K (Qp p) = D := by
    have hc := hcard
    rw [Fintype.card_sigma] at hc
    simpa using hc
  refine ⟨?_, hsum⟩
  let e := Fintype.equivFinOfCardEq hcard
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin D) (Fin D) K,
      Q = (Pi.basisFun K (Fin D)).toMatrix (b.reindex e) := ⟨_, rfl⟩
  have hQ : Q.det ≠ 0 := by
    have hu := (Pi.basisFun K (Fin D)).isUnit_det (b.reindex e)
    rw [Module.Basis.det_apply, ← hQdef] at hu
    exact hu.ne_zero
  obtain ⟨Qs, hQs⟩ : ∃ M : Matrix (Fin D) (Fin D) ℂ, M = Q.map σ := ⟨_, rfl⟩
  have hQs_det : Qs.det ≠ 0 := by
    rw [hQs, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero σ).mpr hQ
  have hcol : ∀ a, (fun i => Qs i a) = cv σ (b (e.symm a)) := by
    intro a
    ext i
    simp [hQs, hQdef, cv, Module.Basis.toMatrix_apply, Module.Basis.reindex_apply]
  have hmem : ∀ a, b (e.symm a) ∈ Qp (e.symm a).1 := fun a => hint.collectedBasis_mem _ _
  have key : Qsᴴ * N1 * Qs = Matrix.diagonal (fun a => c (e.symm a).1) * (Qsᴴ * N2 * Qs) := by
    ext a a'
    rw [Matrix.diagonal_mul, conjT_mul_mul_apply, conjT_mul_mul_apply, hcol, hcol]
    exact h _ _ (hmem a) _
  have hdet := congrArg Matrix.det key
  simp only [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose] at hdet
  have hne : star Qs.det * Qs.det ≠ 0 := mul_ne_zero (star_ne_zero.mpr hQs_det) hQs_det
  have hprod : ∏ a, c (e.symm a).1 = ∏ p, c p ^ finrank K (Qp p) := by
    rw [Equiv.prod_comp e.symm (fun s => c s.1), Fintype.prod_sigma]
    simp
  rw [← hprod]
  apply mul_right_cancel₀ hne
  linear_combination hdet

lemma detRatio_of_scalar (v : InfinitePlace K) {d : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hS : IsUnit (XS v).det)
    (φ : Matrix (Fin d) (Fin d) K) {Ix : Type} [Fintype Ix]
    (Qp : Ix → Submodule K (Fin d → K)) (hind : iSupIndep Qp) (htop : (⨆ p, Qp p) = ⊤)
    (c : Ix → ℝ)
    (h : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin d → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v (φ.mulVec x) (φ.mulVec y) =
        ((c p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XS v x y) :
    detRatio XS XT φ v = ∏ p, c p ^ finrank K (Qp p) ∧ ∑ p, finrank K (Qp p) = d := by
  obtain ⟨hdet, hsum⟩ := det_of_scalar v.embedding Qp hind htop
    ((φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding) (metMat XS v)
    (fun p => ((c p : ℝ) : ℂ)) (by
      intro p x hx y
      rw [← star_mulVec_dot, ← cv_mulVec, ← cv_mulVec, ← majAt_eq, ← majAt_eq]
      exact h p x hx y)
  refine ⟨?_, hsum⟩
  rw [detRatio_eq, hdet]
  have hm := metMat_det_re_ne XS v hS
  have hc : (∏ p, ((c p : ℝ) : ℂ) ^ finrank K (Qp p)) =
      ((∏ p, c p ^ finrank K (Qp p) : ℝ) : ℂ) := by
    simp [Complex.ofReal_prod]
  rw [hc, Complex.re_ofReal_mul]
  field_simp

end SpecDetAux

theorem spectral_determinant_formula : SpecDet := by
  unfold SpecDet
  intro K _ _ _ v D XQ XE hXQ hXE ι hι J _ d XT XW hXT hXW θ hθ Ix _ Qp Tq hind htop hindT htopT
    hdim s lam hQ hT
  obtain ⟨h1, hsum⟩ :=
    detRatio_of_scalar v XQ XE (hXQ v) ι Qp hind htop (fun p => s * ∏ j, lam j p) hQ
  have h2 : ∀ j, detRatio (XT j) (XW j) (θ j) v = ∏ p, lam j p ^ finrank K (Qp p) := by
    intro j
    obtain ⟨h, -⟩ := detRatio_of_scalar v (XT j) (XW j) (hXT j v) (θ j) (Tq j) (hindT j)
      (htopT j) (lam j) (hT j)
    rw [h]
    exact Finset.prod_congr rfl (fun p _ => by rw [hdim j p])
  rw [h1, Finset.prod_congr rfl (fun j _ => h2 j)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, Finset.prod_pow]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [Finset.prod_pow]

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.WeightedPlaceLogSum
section
open Finset NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

namespace place_log_sum

end place_log_sum

theorem prime_log_sum_bound : PrimeLogSum := by
  intro Y hY s hs
  have hn : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hnR : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn
  have hfl : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  calc ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log (p : ℝ) / (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
        · intro p _ _
          exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ ≤ Real.log (⌊Y⌋₊ : ℝ) + Real.log 4 := Formalism.LogFactorialBounds.sum_primesLE_log_div_le _ hn
    _ ≤ Real.log Y + Real.log 4 := by
        have := Real.log_le_log hnR hfl
        linarith

namespace place_log_sum

end place_log_sum

namespace place_log_sum

end place_log_sum

end Formalism.DivisionValues
end
end

