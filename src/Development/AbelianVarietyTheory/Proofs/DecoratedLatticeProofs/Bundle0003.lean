module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermitianDetNeZeroTwo
section
namespace GlobalTheory

open MvPolynomial Matrix

noncomputable def hermGenericMatrix {κ : Type} [Field κ] (n : ℕ) (e : κ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) κ) :=
  Matrix.of fun i j => X (i, j) + X (j, i) + C e * (X (i, j) - X (j, i))

theorem hermGenericMatrix_map_eval {κ : Type} [Field κ] (n : ℕ) (e : κ)
    (u : Fin n × Fin n → κ) :
    (hermGenericMatrix n e).map (MvPolynomial.eval u) =
      Matrix.of fun i j => u (i, j) + u (j, i) + e * (u (i, j) - u (j, i)) := by
  ext i j
  simp [hermGenericMatrix]

theorem hermGenericMatrix_onto {κ : Type} [Field κ] [CharZero κ] (n : ℕ) (e : κ) (he : e ≠ 0)
    (y : Matrix (Fin n) (Fin n) κ) :
    ∃ u : Fin n × Fin n → κ, (hermGenericMatrix n e).map (MvPolynomial.eval u) = y := by
  refine ⟨fun p => (y p.1 p.2 + y p.2 p.1) / 4 + (y p.1 p.2 - y p.2 p.1) / (4 * e), ?_⟩
  rw [hermGenericMatrix_map_eval]
  ext i j
  simp only [Matrix.of_apply]
  field_simp
  ring

theorem eval_det_affine_matrix {κ ι : Type} [Field κ] {n : ℕ} (c d : Matrix (Fin n) (Fin n) κ)
    (G : Matrix (Fin n) (Fin n) (MvPolynomial ι κ)) (u : ι → κ) :
    MvPolynomial.eval u (c.map C * G + d.map C).det =
      (c * G.map (MvPolynomial.eval u) + d).det := by
  rw [RingHom.map_det, map_add (f := _), map_mul]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

theorem exists_hermitian_det_ne_zero_two :
    ∀ (E κ : Type) [Field E] [CharZero E] [Field κ] (σ : E →+* E) (φ : E →+* κ) (δ : E), δ ≠ 0 → σ δ = -δ → ∀ (n : ℕ) (c d y c' d' y' : Matrix (Fin n) (Fin n) κ), (c * y + d).det ≠ 0 → (c' * y' + d').det ≠ 0 → ∃ x : Matrix (Fin n) (Fin n) E, x.map σ = x.transpose ∧ (c * x.map φ + d).det ≠ 0 ∧ (c' * x.transpose.map φ + d').det ≠ 0 := by
  intro E κ _ _ _ σ φ δ hδ hσ n c d y c' d' y' h h'
  haveI : CharZero κ := (RingHom.charZero_iff φ.injective).mp inferInstance
  have he : φ δ ≠ 0 := (map_ne_zero φ).mpr hδ
  set G := hermGenericMatrix n (φ δ) with hG
  have h1 : (c.map C * G + d.map C).det ≠ 0 := by
    obtain ⟨u, hu⟩ := hermGenericMatrix_onto n (φ δ) he y
    intro h0
    have := eval_det_affine_matrix c d G u
    rw [h0, map_zero, hG, hu] at this
    exact h this.symm
  have h2 : (c'.map C * Gᵀ + d'.map C).det ≠ 0 := by
    obtain ⟨u, hu⟩ := hermGenericMatrix_onto n (φ δ) he y'ᵀ
    intro h0
    have := eval_det_affine_matrix c' d' Gᵀ u
    rw [h0, map_zero, Matrix.transpose_map, hG, hu, Matrix.transpose_transpose] at this
    exact h' this.symm
  have h12 := mul_ne_zero h1 h2
  have key : ∃ m : Fin n × Fin n → ℕ, MvPolynomial.eval (fun p => (m p : κ))
      ((c.map C * G + d.map C).det * (c'.map C * Gᵀ + d'.map C).det) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply h12
    apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → κ))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro x hx
    have hx' : ∀ p, ∃ m : ℕ, (m : κ) = x p := fun p => hx p (Set.mem_univ p)
    choose m hm using hx'
    have : x = fun p => (m p : κ) := funext fun p => (hm p).symm
    rw [this, map_zero]
    exact hcon m
  obtain ⟨m, hm⟩ := key
  rw [map_mul, eval_det_affine_matrix, eval_det_affine_matrix, Matrix.transpose_map, hG,
    hermGenericMatrix_map_eval] at hm
  let x : Matrix (Fin n) (Fin n) E := Matrix.of fun i j =>
    (m (i, j) : E) + (m (j, i) : E) + δ * ((m (i, j) : E) - (m (j, i) : E))
  have hx : x.map φ = Matrix.of fun i j =>
      (m (i, j) : κ) + (m (j, i) : κ) + φ δ * ((m (i, j) : κ) - (m (j, i) : κ)) := by
    ext i j
    simp [x]
  refine ⟨x, ?_, ?_, ?_⟩
  · ext i j
    simp only [x, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, map_add (f := _), map_mul,
      map_sub, map_natCast, hσ]
    ring
  · rw [hx]; exact left_ne_zero_of_mul hm
  · rw [Matrix.transpose_map, hx]; exact right_ne_zero_of_mul hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLogNearOneUnitaryGroupOfFormLinearBound
section
open Matrix Filter Topology

namespace GlobalTheory.UnitaryLog

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open Matrix Filter Topology in
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private lemma linftyOp_norm_le_mul_of_entry_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ δ) : ‖A‖ ≤ n * δ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : A = 0 := Subsingleton.elim _ _
    simp [this]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (h ⟨0, hn⟩ ⟨0, hn⟩)
  lift δ to NNReal using hδ
  rw [linfty_opNorm_def]
  have key : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ n • δ := by
    refine Finset.sup_le fun i _ => ?_
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => ‖A i j‖₊) δ
      (fun j _ => by exact_mod_cast h i j)
    simpa using this
  have := (NNReal.coe_le_coe.2 key)
  simpa [nsmul_eq_mul] using this

open Matrix Filter Topology in
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private lemma norm_entry_le_linftyOp_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  rw [linfty_opNorm_def]
  calc ‖A i j‖ = ((‖A i j‖₊ : NNReal) : ℝ) := rfl
    _ ≤ ((∑ k, ‖A i k‖₊ : NNReal) : ℝ) := by
      exact_mod_cast Finset.single_le_sum (f := fun k => ‖A i k‖₊)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := by
      exact_mod_cast Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)


open Matrix Filter Topology in
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem _root_.GlobalTheory.UnitaryLog.exists_log_unitary (n : ℕ)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ (u : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ), uᴴ * G * u = G → δ ≤ δ₁ →
      (∀ i j, ‖(u - 1) i j‖ ≤ δ) → ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧
        NormedSpace.exp X = u ∧ ∀ i j, ‖X i j‖ ≤ C * δ := by
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] _)) 0 :=
    hasStrictFDerivAt_exp_zero
  set L := hf.localInverse _ _ _ with hL
  set φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => G⁻¹ * Xᴴ * G with hφ
  have hφc : Continuous φ :=
    (continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const
  have hφ0 : Tendsto φ (𝓝 0) (𝓝 0) := by
    simpa [φ] using hφc.tendsto 0
  have hleft : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X :=
    hf.eventually_left_inverse
  have hP : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X ∧
      L (NormedSpace.exp (φ X)) = φ X ∧ L (NormedSpace.exp (-X)) = -X :=
    hleft.and ((hφ0.eventually hleft).and
      ((continuous_neg.tendsto' (0 : Matrix (Fin n) (Fin n) ℂ) 0 neg_zero).eventually hleft))
  obtain ⟨K, s, hs, hK⟩ := hf.to_localInverse.exists_lipschitzOnWith
  have hQ := hf.eventually_right_inverse.and ((hf.localInverse_tendsto.eventually hP).and hs)
  have hL1 : L (NormedSpace.exp 0) = 0 := hf.localInverse_apply_image
  have hs1 : NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) ∈ s := mem_of_mem_nhds hs
  rw [NormedSpace.exp_zero] at hQ hL1 hs1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hQ
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  refine ⟨ε / (2 * ((n : ℝ) + 1)), K * n, by positivity, ?_⟩
  intro u δ hu hδ hentry
  have hnorm : ‖u - 1‖ ≤ n * δ := linftyOp_norm_le_mul_of_entry_le _ δ hentry
  have hsmall : (n : ℝ) * (ε / (2 * ((n : ℝ) + 1))) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hpos]
    nlinarith
  have hdist : dist u 1 < ε := by
    rw [dist_eq_norm]
    calc ‖u - 1‖ ≤ n * δ := hnorm
      _ ≤ n * (ε / (2 * ((n : ℝ) + 1))) := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg n)
      _ < ε := hsmall
  obtain ⟨hexp, ⟨hX, hXφ, hXneg⟩, hus⟩ := hball hdist
  refine ⟨L u, ?_, hexp, ?_⟩
  · have hGu : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 hG
    have hinv : u⁻¹ = G⁻¹ * uᴴ * G := by
      apply Matrix.inv_eq_left_inv
      have hu' := hu
      simp only [Matrix.mul_assoc] at hu' ⊢
      rw [hu', Matrix.nonsing_inv_mul G hG]
    have hexpφ : NormedSpace.exp (φ (L u)) = NormedSpace.exp (-L u) := by
      rw [Matrix.exp_neg, hexp, hinv]
      simp only [φ]
      rw [Matrix.exp_conj' G _ hGu, Matrix.exp_conjTranspose, hexp]
    have heq : φ (L u) = -L u := by
      rw [← hXφ, ← hXneg, hexpφ]
    calc (L u)ᴴ * G + G * L u = G * φ (L u) + G * L u := by
          simp only [φ]
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
            Matrix.one_mul]
      _ = 0 := by rw [heq, Matrix.mul_neg, neg_add_cancel]
  · intro i j
    calc ‖L u i j‖ ≤ ‖L u‖ := norm_entry_le_linftyOp_norm _ i j
      _ = dist (L u) (L 1) := by rw [hL1, dist_zero_right]
      _ ≤ K * dist u 1 := hK.dist_le_mul u hus 1 hs1
      _ ≤ K * (n * δ) := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_left hnorm K.coe_nonneg
      _ = K * n * δ := by ring

end GlobalTheory.UnitaryLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalIdempotentsOfSumMulEqOne
section
noncomputable section

namespace GlobalTheory.AdeleIdempotents

open IsDedekindDomain NumberField

def finiteComponent (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    AdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun x := x.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def infiniteComponent (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    AdeleRing (𝓞 F) F →+* w.Completion where
  toFun x := x.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exists_orthogonal_idempotents_of_sum_mul_eq_one (F : Type) [Field F] [NumberField F]
    (ι : Type) [Fintype ι] (f s : ι → AdeleRing (𝓞 F) F) (h : ∑ i, s i * f i = 1) :
    ∃ e t : ι → AdeleRing (𝓞 F) F, ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧
      ∀ i, t i * f i = e i := by
  classical
  have hinf : ∀ w : InfinitePlace F, ∃ i, (s i).1 w * (f i).1 w ≠ 0 := by
    intro w
    have h1 : ∑ i, (s i).1 w * (f i).1 w = 1 := by
      have := congrArg (infiniteComponent F w) h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_one] at this
      exact this
    by_contra hc
    push_neg at hc
    rw [Finset.sum_eq_zero (fun i _ => hc i)] at h1
    exact zero_ne_one h1
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ i, 1 ≤ Valued.v ((s i).2 v * (f i).2 v) := by
    intro v
    have h1 : ∑ i, (s i).2 v * (f i).2 v = 1 := by
      have := congrArg (finiteComponent F v) h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_one] at this
      exact this
    by_contra hc
    push_neg at hc
    have := Valuation.map_sum_lt (Valued.v) (s := Finset.univ) (g := 1) one_ne_zero
      (fun i _ => hc i)
    rw [h1, map_one] at this
    exact lt_irrefl _ this
  choose a ha using hinf
  choose b hb using hfin
  have hfv : ∀ v, (f (b v)).2 v ≠ 0 := by
    intro v h0
    have := hb v
    rw [h0, mul_zero, map_zero] at this
    exact absurd this (by simp)
  refine ⟨fun i => (fun w => if a w = i then 1 else 0,
      ⟨fun v => if b v = i then 1 else 0, Filter.Eventually.of_forall fun v => by
        dsimp only
        split_ifs
        · exact one_mem _
        · exact zero_mem _⟩),
    fun i => (fun w => if a w = i then ((f i).1 w)⁻¹ else 0,
      ⟨fun v => if b v = i then ((f i).2 v)⁻¹ else 0, (s i).2.2.mono fun v hv => by
        dsimp only
        split_ifs with hbi
        · subst hbi
          have hv' : Valued.v ((s (b v)).2 v) ≤ 1 := hv
          change Valued.v ((f (b v)).2 v)⁻¹ ≤ 1
          refine le_trans ?_ hv'
          calc Valued.v ((f (b v)).2 v)⁻¹ = Valued.v ((f (b v)).2 v)⁻¹ * 1 := (mul_one _).symm
            _ ≤ Valued.v ((f (b v)).2 v)⁻¹ * Valued.v ((s (b v)).2 v * (f (b v)).2 v) :=
              mul_le_mul' le_rfl (hb v)
            _ = Valued.v ((s (b v)).2 v) := by
              rw [← map_mul, mul_comm ((s (b v)).2 v), ← mul_assoc, inv_mul_cancel₀ (hfv v),
                one_mul]
        · exact zero_mem _⟩), ?_, ?_, ?_⟩
  · refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
    · refine (map_sum (infiniteComponent F w) _ _).trans ?_
      change ∑ i, (if a w = i then (1 : w.Completion) else 0) = 1
      simp
    · refine (map_sum (finiteComponent F v) _ _).trans ?_
      change ∑ i, (if b v = i then (1 : v.adicCompletion F) else 0) = 1
      simp
  · intro i j hij
    refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
    · change (if a w = i then (1 : w.Completion) else 0) * (if a w = j then 1 else 0) = 0
      split_ifs with h1 h2
      · exact absurd (h1.symm.trans h2) hij
      all_goals simp
    · change (if b v = i then (1 : v.adicCompletion F) else 0) * (if b v = j then 1 else 0) = 0
      split_ifs with h1 h2
      · exact absurd (h1.symm.trans h2) hij
      all_goals simp
  · intro i
    refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
    · change (if a w = i then ((f i).1 w)⁻¹ else 0) * (f i).1 w = (if a w = i then 1 else 0)
      split_ifs with h1
      · subst h1
        exact inv_mul_cancel₀ (right_ne_zero_of_mul (ha w))
      · simp
    · change (if b v = i then ((f i).2 v)⁻¹ else 0) * (f i).2 v = (if b v = i then 1 else 0)
      split_ifs with h1
      · subst h1
        exact inv_mul_cancel₀ (hfv v)
      · simp

end GlobalTheory.AdeleIdempotents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivAddOne
section
namespace GlobalTheory.ShiftVariables

noncomputable def shiftVars (ι k : Type) [CommRing k] :
    MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i + 1)
    (MvPolynomial.aeval fun i => MvPolynomial.X i - 1)
    (by ext1 i; simp) (by ext1 i; simp)

theorem shiftVars_X (ι k : Type) [CommRing k] (i : ι) :
    shiftVars ι k (MvPolynomial.X i) = MvPolynomial.X i + 1 := by
  change MvPolynomial.aeval (fun i => MvPolynomial.X i + 1) (MvPolynomial.X i) = _
  simp

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental (↥k) c) :
    ∃ (σ : Ω ≃+* Ω), (∀ a ∈ k, (σ : Ω → Ω) a = a) ∧ (σ : Ω → Ω) c = c + (1 : Ω) := by
  classical
  have hs : AlgebraicIndepOn (↥k) id ({c} : Set Ω) :=
    algebraicIndependent_unique_type_iff.mpr (by simpa using hc)
  obtain ⟨t, hct, ht⟩ := exists_isTranscendenceBasis_superset hs
  have hind : AlgebraicIndependent (↥k) ((↑) : t → Ω) := ht.1
  set K := IntermediateField.adjoin (↥k) (Set.range ((↑) : t → Ω)) with hK
  let e := hind.aevalEquivField
  let φ : FractionRing (MvPolynomial t ↥k) ≃ₐ[↥k] FractionRing (MvPolynomial t ↥k) :=
    IsFractionRing.algEquivOfAlgEquiv (K := FractionRing (MvPolynomial t ↥k))
      (L := FractionRing (MvPolynomial t ↥k)) (shiftVars t ↥k)
  let τ : K ≃ₐ[↥k] K := e.symm.trans (φ.trans e)
  have hmem : ∀ i : t, (i : Ω) ∈ K := fun i =>
    IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have he : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i)) = ⟨i, hmem i⟩ := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have he1 : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i + 1)) =
      ⟨i, hmem i⟩ + 1 := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have hτ : ∀ i : t, τ ⟨i, hmem i⟩ = ⟨i, hmem i⟩ + 1 := by
    intro i
    have h0 : e.symm ⟨i, hmem i⟩ = algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i) := by
      rw [AlgEquiv.symm_apply_eq, he]
    change e (φ (e.symm ⟨i, hmem i⟩)) = _
    rw [h0, IsFractionRing.algEquivOfAlgEquiv_algebraMap, shiftVars_X, he1]
  have : Algebra.IsAlgebraic K Ω := ht.isAlgebraic_field
  have : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let σ : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω τ.toRingEquiv
  have hσ : ∀ y : K, σ (y : Ω) = (τ y : Ω) := fun y =>
    IsAlgClosure.equivOfEquiv_algebraMap Ω Ω τ.toRingEquiv y
  refine ⟨σ, fun a ha => ?_, ?_⟩
  · have hak : a ∈ K := IntermediateField.algebraMap_mem K (⟨a, ha⟩ : ↥k)
    have h1 := hσ ⟨a, hak⟩
    have h2 : τ ⟨a, hak⟩ = ⟨a, hak⟩ := τ.commutes (⟨a, ha⟩ : ↥k)
    rw [h2] at h1
    exact h1
  · have hc' : c ∈ t := hct rfl
    have h1 := hσ ⟨c, hmem ⟨c, hc'⟩⟩
    rw [hτ ⟨c, hc'⟩] at h1
    simpa using h1

end GlobalTheory.ShiftVariables
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanMultilinearValues
section
namespace GlobalTheory

theorem finiteDimensional_span_multilinear_values :
    ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      (F : Type) [AddCommGroup F] [Module ℂ F] (T : (∀ i, E i) →ₘₗ[ℂ] F)
      (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) →
      FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by
  intro ι _ E _ _ F _ _ T W hW
  have := hW
  let T' : (∀ i, W i) →ₘₗ[ℂ] F := T.compLinearMap (fun i => (W i).subtype)
  have hset : {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v} = Set.range T' := by
    ext f
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨fun i => ⟨v i, hv i⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨fun i => (w i : E i), fun i => (w i).2, rfl⟩
  have hle : Submodule.span ℂ (Set.range T') ≤ LinearMap.range (PiTensorProduct.lift T') := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ w, by simp⟩
  rw [hset]
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GradedSeriesMulNeZero
section
open Filter Topology Metric Set

namespace GlobalTheory

theorem gradedSeries_mul_ne_zero : ∀ (ι : Type) (deg : ι → ℕ) (a : ι → ℂ) (ρ δ : ℝ) (P Q : ℂ → ℂ), 0 < δ → Differentiable ℂ P → Differentiable ℂ Q → (∀ r : ℝ, 0 < r → r < ρ → Summable fun i => ‖a i‖ * r ^ deg i) → (∀ x : ℝ, 0 < x → x < δ → (∑' i, a i * (x : ℂ) ^ deg i) * P x = Q x) → ∀ X : ℂ, ‖X‖ < ρ → Q X ≠ 0 → P X ≠ 0 := by
  intro ι deg a ρ δ P Q hδ hP hQ hsum hid X hX hQX
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hX
  set F : ℂ → ℂ := fun z => ∑' i, a i * z ^ deg i with hFdef
  have hFd : ∀ z ∈ ball (0 : ℂ) ρ, DifferentiableAt ℂ F z := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    have hr0 : 0 < (‖z‖ + ρ) / 2 := by positivity
    have hrρ : (‖z‖ + ρ) / 2 < ρ := by linarith
    have hD : DifferentiableOn ℂ F (ball 0 ((‖z‖ + ρ) / 2)) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (hsum _ hr0 hrρ)
        (fun i => (differentiable_const _ |>.mul (differentiable_id.pow _)).differentiableOn)
        isOpen_ball (fun i w hw => ?_)
      rw [mem_ball_zero_iff] at hw
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw.le _) (norm_nonneg _)
    exact hD.differentiableAt (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith))
  set G : ℂ → ℂ := fun z => F z * P z - Q z with hGdef
  have hGan : AnalyticOnNhd ℂ G (ball 0 ρ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    exact (((hFd z hz).mul (hP z)).sub (hQ z)).differentiableWithinAt
  have hs0 : 0 < min δ ρ := lt_min hδ hρ
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using (ne_of_gt hx))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), G z = 0 := by
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT hs0] with x hx
    have h1 := hid x hx.1 (lt_of_lt_of_le hx.2 (min_le_left _ _))
    simp only [G, F, h1, sub_self]
  have heq := hGan.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball _ _).isPreconnected (mem_ball_self hρ) hfreq
  have hGX : G X = 0 := heq (by rw [mem_ball_zero_iff]; exact hX)
  intro hPX
  apply hQX
  simp only [G, hPX, mul_zero, zero_sub, neg_eq_zero] at hGX
  exact hGX

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
section
namespace GlobalTheory.SymRes

def FreePos (ρ κ i j : ℕ) : Prop :=
  (i < κ ∧ j < κ ∧ i < j) ∨ (κ ≤ i ∧ i < κ + ρ ∧ j < κ) ∨ (i < κ ∧ κ + ρ < j) ∨ (κ ≤ i ∧ i < j)

def IsPat {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) : Prop :=
  ∀ i j : Fin r, ¬ FreePos ρ κ i.val j.val → g.val i j = (1 : Matrix (Fin r) (Fin r) K) i j

theorem isPat_one {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) : IsPat ρ κ (1 : GL (Fin r) K) := fun _ _ _ => rfl

end GlobalTheory.SymRes
end

