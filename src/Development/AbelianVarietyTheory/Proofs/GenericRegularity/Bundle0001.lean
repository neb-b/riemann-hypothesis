module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AdjoinRatiosOfSpanEqTop
section
namespace GlobalTheory

theorem adjoin_ratios_of_span_eq_top :
    ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω) (m : ℕ) (w : Fin m → R) (k : Fin m), Ideal.span (Set.range w) = ⊤ → (w k : Ω) ≠ 0 → ∀ R' : Subalgebra K Ω, R' = Algebra.adjoin K ((R : Set Ω) ∪ Set.range fun i => (w i : Ω) / (w k : Ω)) → ∃ h : R ≤ R', (w k : Ω)⁻¹ ∈ R' ∧ (Algebra.Smooth K R → Algebra.Smooth K R') ∧ ∀ (L : Type) [Field L] [Algebra K L] (ψ : R →ₐ[K] L), ψ (w k) ≠ 0 → ∃ ψ' : R' →ₐ[K] L, ψ'.comp (Subalgebra.inclusion h) = ψ ∧ ∀ i (hi : (w i : Ω) / (w k : Ω) ∈ R'), ψ' ⟨_, hi⟩ = ψ (w i) / ψ (w k) := by
  intro K Ω _ _ _ R m w k hspan hk R' hR'
  have h : R ≤ R' := by
    rw [hR']; intro x hx; exact Algebra.subset_adjoin (Or.inl hx)
  have hrat : ∀ i, (w i : Ω) / (w k : Ω) ∈ R' := by
    intro i; rw [hR']; exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
  have hinv : (w k : Ω)⁻¹ ∈ R' := by
    have h1 : (1 : R) ∈ Ideal.span (Set.range w) := by rw [hspan]; trivial
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
    have h2 : ∑ i, (a i : Ω) * (w i : Ω) = 1 := by
      have := congrArg (fun x : R => (x : Ω)) ha
      simpa using this
    have h3 : (w k : Ω)⁻¹ = ∑ i, (a i : Ω) * ((w i : Ω) / (w k : Ω)) := by
      simp only [← mul_div_assoc, ← Finset.sum_div, h2, one_div]
    rw [h3]
    exact R'.sum_mem fun i _ => R'.mul_mem (h (a i).2) (hrat i)
  letI : Algebra R R' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K R R' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have halg : ∀ x : R, ((algebraMap R R' x : R') : Ω) = x := fun x => rfl
  have hsurj : ∀ z : Ω, z ∈ R' → ∃ (n : ℕ) (a : R), z * (w k : Ω) ^ n = a := by
    intro z hz
    rw [hR'] at hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · exact ⟨0, ⟨x, hx⟩, by simp⟩
      · exact ⟨1, w i, by field_simp⟩
    | algebraMap r => exact ⟨0, algebraMap K R r, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨n', b, hb⟩ := hy
      refine ⟨n + n', a * w k ^ n' + b * w k ^ n, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨n', b, hb⟩ := hy
      refine ⟨n + n', a * b, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
  haveI hloc : IsLocalization.Away (w k) R' := by
    refine IsLocalization.Away.mk (w k) ?_ ?_ ?_
    · refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
      apply Subtype.ext
      simp [halg, hk]
    · intro s
      obtain ⟨n, a, ha⟩ := hsurj s s.2
      refine ⟨n, a, Subtype.ext ?_⟩
      simpa [halg] using ha
    · intro a b hab
      refine ⟨0, ?_⟩
      have : (a : Ω) = b := by rw [← halg a, ← halg b, hab]
      rw [Subtype.ext this]
  refine ⟨h, hinv, fun hs => ?_, fun L _ _ ψ hψ => ?_⟩
  · haveI : Algebra.Smooth R R' := Algebra.Smooth.of_isLocalization_Away (w k)
    exact Algebra.Smooth.comp K R R'
  · have hu : IsUnit ((ψ : R →+* L) (w k)) := isUnit_iff_ne_zero.2 hψ
    let φ : R' →+* L := IsLocalization.Away.lift (w k) hu
    have hφ : ∀ x : R, φ (algebraMap R R' x) = ψ x := fun x =>
      IsLocalization.Away.lift_eq (w k) hu x
    refine ⟨{ φ with commutes' := fun r => ?_ }, ?_, fun i hi => ?_⟩
    · change φ (algebraMap K R' r) = _
      rw [IsScalarTower.algebraMap_apply K R R', hφ, AlgHom.commutes]
    · ext x; exact hφ x
    · change φ ⟨_, hi⟩ = _
      rw [eq_div_iff hψ, ← hφ, ← hφ, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [halg, hk]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContDiffEvalFun
section
open Filter Topology

namespace GlobalTheory.SmoothPolynomialEvaluation

noncomputable def evalFun {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (v : (Fin d → ℂ) × ℂ) : ℂ :=
  Polynomial.eval v.2 (Polynomial.map (MvPolynomial.eval v.1) p)

lemma contDiff_mvEval {d : ℕ} (q : MvPolynomial (Fin d) ℂ) :
    ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => MvPolynomial.eval v.1 q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    have hX : ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => v.1 i) := (contDiff_apply ℂ (fun _ => ℂ) i).comp contDiff_fst
    simpa using hp.mul hX

lemma contDiff_evalFun {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) :
    ContDiff ℂ 1 (evalFun p) := by
  have h : evalFun p = fun v => ∑ i ∈ Finset.range (p.natDegree + 1),
      MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i := by
    funext v
    unfold evalFun
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
    simp [Polynomial.coeff_map]
  rw [h]
  apply ContDiff.sum
  intro i _
  exact (contDiff_mvEval _).mul (contDiff_snd.pow i)

theorem main : ∀ {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x₀ : Fin d → ℂ) (a : ℂ),
    Polynomial.eval a (Polynomial.map (MvPolynomial.eval x₀) p) = (0 : ℂ) →
    Polynomial.eval a ((Polynomial.derivative : Polynomial ℂ → Polynomial ℂ)
      (Polynomial.map (MvPolynomial.eval x₀) p)) ≠ (0 : ℂ) →
    ∃ (y : (Fin d → ℂ) → ℂ), y x₀ = a ∧ (∃ s ∈ nhds x₀, ContinuousOn y s) ∧
      ∀ᶠ (x : Fin d → ℂ) in nhds x₀,
        Polynomial.eval (y x) (Polynomial.map (MvPolynomial.eval x) p) = (0 : ℂ) := by
  intro d p x₀ a h0 h1
  set q := Polynomial.map (MvPolynomial.eval x₀) p with hq
  have hFs : HasStrictFDerivAt (evalFun p) (fderiv ℂ (evalFun p) (x₀, a)) (x₀, a) :=
    (contDiff_evalFun p).contDiffAt.hasStrictFDerivAt_fderiv one_ne_zero
  have hder : fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ
      = (1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q)) := by
    have h1' : HasFDerivAt (fun z => evalFun p (x₀, z))
        (fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) a :=
      hFs.hasFDerivAt.comp a (hasFDerivAt_prodMk_right x₀ a)
    have h2' : HasFDerivAt (fun z => evalFun p (x₀, z))
        ((1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q))) a :=
      (Polynomial.hasDerivAt q a).hasFDerivAt
    exact h1'.unique h2'
  have hinv : (fderiv ℂ (evalFun p) (x₀, a) ∘L
      ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hder]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext; simp
  let φ := hFs.implicitFunctionDataOfProdDomain hinv
  refine ⟨fun x => (φ.toOpenPartialHomeomorph.symm (evalFun p (x₀, a), x)).2, ?_, ?_, ?_⟩
  · have := (hFs.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds
    simpa only [HasStrictFDerivAt.implicitFunctionOfProdDomain_def,
      ImplicitFunctionData.implicitFunction_apply] using this.mp rfl
  · refine ⟨{x | (evalFun p (x₀, a), x) ∈ φ.toOpenPartialHomeomorph.target}, ?_, ?_⟩
    · apply IsOpen.mem_nhds
      · exact φ.toOpenPartialHomeomorph.open_target.preimage (by fun_prop)
      · simpa only [Set.mem_setOf_eq, φ, HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain,
          HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
          HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain, Prod.fst] using
          φ.map_pt_mem_toOpenPartialHomeomorph_target
    · exact continuous_snd.comp_continuousOn
        (φ.toOpenPartialHomeomorph.continuousOn_symm.comp (by fun_prop) (fun x hx => hx))
  · have := hFs.eventually_apply_implicitFunctionOfProdDomain hinv
    filter_upwards [this] with x hx
    simpa only [HasStrictFDerivAt.implicitFunctionOfProdDomain_def,
      ImplicitFunctionData.implicitFunction_apply, evalFun] using hx.trans h0

end GlobalTheory.SmoothPolynomialEvaluation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContinuousOnNormDiagOfTriangularSqrt
section
open scoped Matrix

namespace GlobalTheory.TriSqrt

lemma det_eq_prod_diag {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    h.det = ∏ j, h j j := by
  have hi : Function.Injective (fun j => toLex (Fintype.equivFin α (t j), w j)) := by
    intro k l hkl
    have h' := toLex.injective hkl
    rw [Prod.mk.injEq] at h'
    exact hinj _ _ ((Fintype.equivFin α).injective h'.1) h'.2
  letI : LinearOrder n := LinearOrder.lift' _ hi
  refine Matrix.det_of_upperTriangular fun k l hkl => ?_
  by_contra hne
  obtain ⟨h1, h2⟩ := hs k l hne
  have hkl' : toLex (Fintype.equivFin α (t l), w l) < toLex (Fintype.equivFin α (t k), w k) := hkl
  simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hkl'
  omega

lemma det_minor {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') (d : n → ℝ)
    (S : Matrix n n ℂ) (hs : ∀ j j', S j j' ≠ 0 → t j = t j' ∧ w j ≤ w j')
    (p : n → Prop) [DecidablePred p] (hp : ∀ c a, S c a ≠ 0 → p a → p c) :
    ((Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))).submatrix
      (Subtype.val : {x // p x} → n) Subtype.val).det
      = ((∏ c ∈ Finset.univ.filter p, ‖S c c‖ ^ 2 * d c : ℝ) : ℂ) := by
  set T : Matrix {x // p x} {x // p x} ℂ := S.submatrix Subtype.val Subtype.val with hT
  have e : (Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))).submatrix
      (Subtype.val : {x // p x} → n) Subtype.val
      = Tᵀ * ((Matrix.diagonal fun j => ((d j.1 : ℝ) : ℂ)) * T.map (starRingEnd ℂ)) := by
    ext a a'
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, hT,
      Matrix.diagonal_apply, Matrix.map_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp)
      (fun c => S c a * ((d c : ℂ) * (starRingEnd ℂ) (S c a')))]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
    have : S c a = 0 := by
      by_contra hne
      exact hc (by simpa using hp c a hne a.2)
    rw [this, zero_mul]
  have hdT : T.det = ∏ c, T c c :=
    det_eq_prod_diag (fun c => t c.1) (fun c => w c.1)
      (fun c c' h1 h2 => Subtype.ext (hinj _ _ h1 h2)) T fun c c' hne => hs _ _ hne
  have hdT' : (T.map (starRingEnd ℂ)).det = (starRingEnd ℂ) T.det := by
    rw [RingHom.map_det]; rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hdT', hdT,
    map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Finset.prod_subtype (p := p) (Finset.univ.filter p) (by simp), Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  have := Complex.mul_conj' (S c c)
  simp only [hT, Matrix.submatrix_apply]
  push_cast
  rw [← this]
  ring

end GlobalTheory.TriSqrt

theorem GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt : ∀ (g : ℕ) (α : Type) [Fintype α] (V : Type) [TopologicalSpace V] (t : Fin g → α) (w : Fin g → ℕ) (d : Fin g → ℝ) (B : Set V) (S Hm : V → Matrix (Fin g) (Fin g) ℂ), (∀ j j', t j = t j' → w j = w j' → j = j') → (∀ j, 0 < d j) → (∀ j j', ContinuousOn (fun b => Hm b j j') B) → (∀ b ∈ B, IsUnit (S b).det ∧ (∀ j j', S b j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') ∧ Hm b = (S b)ᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * (S b).map (starRingEnd ℂ))) → ∀ j, ContinuousOn (fun b => ‖S b j j‖) B := by
  intro g α _ V _ t w d B S Hm hinj hd hc hS j
  classical
  have hH : ContinuousOn Hm B := continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => hc k l
  have hP : ∀ n : ℕ, ContinuousOn (fun b =>
      ∏ c ∈ Finset.univ.filter (fun c => t c = t j ∧ w c < n), ‖S b c c‖ ^ 2 * d c) B := by
    intro n
    have h1 : Continuous fun M : Matrix (Fin g) (Fin g) ℂ =>
        ((M.submatrix (Subtype.val : {c // t c = t j ∧ w c < n} → Fin g) Subtype.val).det).re :=
      Complex.continuous_re.comp (continuous_id.matrix_submatrix _ _).matrix_det
    refine (h1.comp_continuousOn hH).congr fun b hb => ?_
    obtain ⟨-, h2, h3⟩ := hS b hb
    simp only [Function.comp_apply]
    rw [h3, GlobalTheory.TriSqrt.det_minor t w hinj d (S b) h2 (fun c => t c = t j ∧ w c < n), Complex.ofReal_re]
    intro c a hne ha
    obtain ⟨h4, h5⟩ := h2 c a hne
    exact ⟨h4.trans ha.1, by omega⟩
  have hne : ∀ b ∈ B, ∀ c, S b c c ≠ 0 := by
    intro b hb c
    obtain ⟨h1, h2, -⟩ := hS b hb
    rw [GlobalTheory.TriSqrt.det_eq_prod_diag t w hinj _ h2, isUnit_iff_ne_zero] at h1
    exact Finset.prod_ne_zero_iff.1 h1 c (Finset.mem_univ _)
  have hne' : ∀ b ∈ B, (∏ c ∈ Finset.univ.filter (fun c => t c = t j ∧ w c < w j),
      ‖S b c c‖ ^ 2 * d c) * d j ≠ 0 := fun b hb =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun c _ =>
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (hne b hb c))) (hd c).ne') (hd j).ne'
  have hins : Finset.univ.filter (fun c => t c = t j ∧ w c < w j + 1)
      = insert j (Finset.univ.filter (fun c => t c = t j ∧ w c < w j)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : w c = w j
      · exact Or.inl (hinj _ _ h1 h3)
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨rfl, by omega⟩
      · exact ⟨h1, by omega⟩
  refine (((hP (w j + 1)).div ((hP (w j)).mul continuousOn_const) hne').sqrt).congr fun b hb => ?_
  have h0 := hne' b hb
  simp only [Pi.div_apply, Pi.mul_apply]
  rw [hins, Finset.prod_insert (by simp), mul_assoc, mul_comm (d j), mul_div_assoc, div_self h0, mul_one,
    Real.sqrt_sq (norm_nonneg _)]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.EqOfUnitriangularOfEqLowerMul
section
namespace GlobalTheory.UnitriangularLowerMulEq

open Matrix

theorem eq_of_unitriangular_of_eq_lower_mul {S : Type} [inst : CommRing S] {n : ℕ}
    (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), j < i → A i j = (0 : S)) (hA1 : ∀ (i : Fin n), A i i = (1 : S))
    (hA' : ∀ (i j : Fin n), j < i → A' i j = (0 : S)) (hA'1 : ∀ (i : Fin n), A' i i = (1 : S))
    (hL : ∀ (i j : Fin n), i < j → L i j = (0 : S)) (h : A' = L * A) : A' = A := by
  classical
  have hAb : A.BlockTriangular id := fun i j hji => hA i j hji
  have hA'b : A'.BlockTriangular id := fun i j hji => hA' i j hji
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAb]
    simp [hA1]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  have hLeq : L = A' * A⁻¹ := by
    rw [h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have : Invertible A := A.invertibleOfIsUnitDet hu
  have hLb : L.BlockTriangular id := hLeq ▸ hA'b.mul (Matrix.blockTriangular_inv_of_blockTriangular hAb)
  have hoff : ∀ i j, i ≠ j → L i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (hL i j) fun hji => hLb hji
  have hdiag : ∀ i, L i i = 1 := by
    intro i
    have hii := congrFun (congrFun h i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hoff i k (Ne.symm hki), zero_mul])
      (by simp), hA1, mul_one, hA'1] at hii
    exact hii.symm
  have hL1 : L = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hdiag]
    · simp [hoff i j hij, Matrix.one_apply_ne hij]
  rw [h, hL1, Matrix.one_mul]

end GlobalTheory.UnitriangularLowerMulEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsColsDetNeZeroOfMul
section
namespace GlobalTheory

open Matrix

theorem eq_cols_mul_inv_minor_mul_rows {Ω : Type} [Field Ω] {n r : ℕ}
    (π : Matrix (Fin n) (Fin n) Ω) (hπ : π.rank = r) (ι κ : Fin r → Fin n)
    (hd : (π.submatrix ι κ).det ≠ 0) :
    π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id := by
  have hu : IsUnit (π.submatrix ι κ).det := isUnit_iff_ne_zero.mpr hd
  have hC : π.submatrix id κ = π * (1 : Matrix (Fin n) (Fin n) Ω).submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hA : π.submatrix ι κ
      = (1 : Matrix (Fin n) (Fin n) Ω).submatrix ι id * π.submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hrA : (π.submatrix ι κ).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hle : LinearMap.range (π.submatrix id κ).mulVecLin ≤ LinearMap.range π.mulVecLin := by
    rw [hC, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hr : π.rank ≤ (π.submatrix id κ).rank := by
    rw [hπ]
    calc r = (π.submatrix ι κ).rank := hrA.symm
      _ ≤ (π.submatrix id κ).rank := by
        conv_lhs => rw [hA]
        exact Matrix.rank_mul_le_right _ _
  have heq := Submodule.eq_of_le_of_finrank_le hle hr
  have hcol : ∀ j : Fin n, ∃ c : Fin r → Ω, (π.submatrix id κ) *ᵥ c = fun i => π i j := by
    intro j
    have : (fun i => π i j) ∈ LinearMap.range π.mulVecLin :=
      ⟨Pi.single j 1, by ext i; simp⟩
    rw [← heq] at this
    exact this
  choose c hc using hcol
  set X : Matrix (Fin r) (Fin n) Ω := Matrix.of fun a j => c j a with hX
  have h1 : π = π.submatrix id κ * X := by
    ext i j
    have := congrFun (hc j) i
    rw [← this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]
  have h2 : π.submatrix ι id = π.submatrix ι κ * X := by
    ext i j
    have := congrFun (congrFun h1 (ι i)) j
    simpa [Matrix.mul_apply] using this
  rw [h2, Matrix.mul_assoc, ← Matrix.mul_assoc (π.submatrix ι κ)⁻¹, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]
  exact h1

theorem exists_cols_det_ne_zero_of_mul {Ω : Type} [Field Ω] {n r : ℕ}
    (R : Matrix (Fin r) (Fin n) Ω) (u : Matrix (Fin n) (Fin r) Ω) (hd : (R * u).det ≠ 0) :
    ∃ κ : Fin r → Fin n, (R.submatrix id κ).det ≠ 0 := by
  have hu : IsUnit (R * u).det := isUnit_iff_ne_zero.mpr hd
  have hrA : (R * u).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hrR : R.rank = r := by
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height R
    · calc r = (R * u).rank := hrA.symm
        _ ≤ R.rank := Matrix.rank_mul_le_left _ _
  obtain ⟨K, a, ha, hspan, hli⟩ := exists_linearIndependent' Ω R.col
  haveI : Fintype K := Fintype.ofInjective a ha
  have hcard : Fintype.card K = r := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hrR]
  let e : Fin r ≃ K := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have h3 : LinearIndependent Ω (R.submatrix id (a ∘ e)).col := hli.comp e e.injective
  rw [Matrix.linearIndependent_cols_iff_isUnit] at h3
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h3)

theorem rank_minor_factorisation :
    ∀ (Ω : Type) [Field Ω] (n r : ℕ) (π : Matrix (Fin n) (Fin n) Ω), π.rank = r → ∀ ι : Fin r → Fin n, (∀ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 → π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id) ∧ ∀ u : Matrix (Fin n) (Fin r) Ω, π * u = u → (u.submatrix ι id).det ≠ 0 → ∃ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 := by
  intro Ω _ n r π hπ ι
  refine ⟨fun κ hd => eq_cols_mul_inv_minor_mul_rows π hπ ι κ hd, fun u hu hd => ?_⟩
  have h : π.submatrix ι id * u = u.submatrix ι id := by
    ext i j
    have := congrFun (congrFun hu (ι i)) j
    simpa [Matrix.mul_apply] using this
  obtain ⟨κ, hκ⟩ := exists_cols_det_ne_zero_of_mul (π.submatrix ι id) u (h ▸ hd)
  exact ⟨κ, hκ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRingHomOfMulPowMem
section
namespace GlobalTheory

theorem exists_mul_pow_mem_of_fg {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    (A B : Subalgebra O Ω) (hA : A.FG)
    (hB : ∀ x : Ω, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) :
    ∃ d ∈ B, d ≠ 0 ∧ ∀ a ∈ A, ∃ n : ℕ, a * d ^ n ∈ B := by
  classical
  obtain ⟨s, hs⟩ := hA
  have hden : ∀ x : Ω, ∃ b ∈ B, b ≠ 0 ∧ x * b ∈ B := by
    intro x
    obtain ⟨a, ha, b, hb, hb0, hx⟩ := hB x
    exact ⟨b, hb, hb0, by rw [hx]; exact ha⟩
  choose den hdenB hden0 hdenmul using hden
  have hD : ∏ x ∈ s, den x ∈ B := Subalgebra.prod_mem B (fun x _ => hdenB x)
  refine ⟨∏ x ∈ s, den x, hD, Finset.prod_ne_zero_iff.mpr (fun x _ => hden0 x), ?_⟩
  intro a ha
  rw [← hs] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>

    refine ⟨1, ?_⟩
    rw [pow_one, ← Finset.mul_prod_erase s den (Finset.mem_coe.mp hx), ← mul_assoc]
    exact mul_mem (hdenmul x) (Subalgebra.prod_mem B (fun y _ => hdenB y))
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, mul_one]; exact B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : (x + y) * (∏ z ∈ s, den z) ^ (n + m) =
        x * (∏ z ∈ s, den z) ^ n * (∏ z ∈ s, den z) ^ m +
          y * (∏ z ∈ s, den z) ^ m * (∏ z ∈ s, den z) ^ n := by ring
    rw [e]
    exact add_mem (mul_mem hn (pow_mem hD m)) (mul_mem hm (pow_mem hD n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : x * y * (∏ z ∈ s, den z) ^ (n + m) =
        (x * (∏ z ∈ s, den z) ^ n) * (y * (∏ z ∈ s, den z) ^ m) := by ring
    rw [e]
    exact mul_mem hn hm

end GlobalTheory
end

