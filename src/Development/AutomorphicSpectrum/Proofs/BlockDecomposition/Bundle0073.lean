module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0054
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLaw
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sum_eq_sum_set {S : Type} [AddCommMonoid S] (s : Set ι) [Fintype s] (f : ι → S)
    (h : ∀ m, m ∉ s → f m = 0) : ∑ m, f m = ∑ m : s, f m := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ s)) (by simp) f]
  exact (Finset.sum_filter_of_ne fun m _ hm => by_contra fun hs => hm (h m hs)).symm

theorem blk_mul {S : Type} [CommRing S] (s : Set ι) [Fintype s] (x y : Matrix ι ι S)
    (hy : ∀ r, r ∉ s → ∀ c ∈ s, y r c = 0) :
    (x * y).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      x.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) *
        y.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) := by
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact sum_eq_sum_set s _ fun m hm => by rw [hy m hm c c.2, mul_zero]

open Classical in
theorem det_blk_mul (s : Set ι) (p : GL ι R) {q : GL ι R} (hq : q ∈ stab R s) :
    (((p * q : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det =
      ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det *
        ((q : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
  rw [Units.val_mul, blk_mul s _ _ fun r hr c hc => (hq r hr c hc).1, Matrix.det_mul]

open Classical in
theorem det_blk_mul_inv (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det *
      (((p⁻¹ : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det = 1 := by
  rw [← det_blk_mul s p (inv_mem hp), mul_inv_cancel, Units.val_one,
    Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

open Classical in
theorem isUnit_det_blk (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    IsUnit ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det :=
  IsUnit.of_mul_eq_one _ (det_blk_mul_inv s hp)

open Classical in
theorem bdet_val (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    ((bdet s p : Rˣ) : R) = ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
  rw [bdet, dite_eq_left (isUnit_det_blk s hp), IsUnit.unit_spec]

theorem bdet_mul (s : Set ι) {p q : GL ι R} (hp : p ∈ stab R s) (hq : q ∈ stab R s) :
    bdet s (p * q) = bdet s p * bdet s q := by
  classical
  apply Units.ext
  rw [Units.val_mul, bdet_val s (mul_mem hp hq), bdet_val s hp, bdet_val s hq]
  exact det_blk_mul s p hq

theorem bdet_inv (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) : (bdet s p)⁻¹ = bdet s p⁻¹ := by
  classical
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  apply Units.ext
  rw [Units.val_mul, bdet_val s hp, bdet_val s (inv_mem hp), Units.val_one]
  exact det_blk_mul_inv s hp

theorem bdet_univ (g : GL ι R) : bdet (Set.univ : Set ι) g = Matrix.GeneralLinearGroup.det g := by
  classical
  have hs : g ∈ stab R (Set.univ : Set ι) := fun r hr => absurd (Set.mem_univ r) hr
  apply Units.ext
  rw [bdet_val _ hs]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  convert Matrix.det_submatrix_equiv_self (Equiv.Set.univ ι) (g : Matrix ι ι R)
  all_goals (funext x; rfl)

section Top

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isClosed_stab [T2Space R] (s : Set ι) : IsClosed (stab R s : Set (GL ι R)) := by
  have e : (stab R s : Set (GL ι R)) = ⋂ (r : ι) (_ : r ∉ s) (c : ι) (_ : c ∈ s),
      ({g : GL ι R | (g : Matrix ι ι R) r c = 0} ∩
        {g : GL ι R | ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun c =>
    isClosed_iInter fun _ => IsClosed.inter ?_ ?_
  · exact isClosed_eq (Units.continuous_val.matrix_elem r c) continuous_const
  · exact isClosed_eq ((Units.continuous_val.comp continuous_inv).matrix_elem r c) continuous_const

theorem continuousOn_bdet (s : Set ι) :
    ContinuousOn (bdet s) (stab R s : Set (GL ι R)) := by
  classical
  have hm (p : (stab R s : Set (GL ι R))) : (p : GL ι R) ∈ stab R s := p.2
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  constructor
  · refine Continuous.congr (f := fun p : (stab R s : Set (GL ι R)) =>
      (((p : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det)
      ((Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _ |>.matrix_det)
      fun p => (bdet_val s (hm p)).symm
  · refine Continuous.congr (f := fun p : (stab R s : Set (GL ι R)) =>
      ((((p : GL ι R)⁻¹ : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det)
      (((Units.continuous_val.comp continuous_inv).comp continuous_subtype_val).matrix_submatrix _ _ |>.matrix_det)
      fun p => ?_
    show _ = (((bdet s (p : GL ι R))⁻¹ : Rˣ) : R)
    rw [bdet_inv s (hm p), bdet_val s (inv_mem (hm p))]

end Top

section Places

variable {E : Type} [Field E]


open Classical in
theorem bdet_rat (A : Ad E R) (hi : Function.Injective A.i) (s : Set ι) {p : GL ι R}
    (hp : p ∈ stab R s) (hr : p ∈ A.ratGL ι) : ∃ x, bdet s p = Units.map A.i.toMonoidHom x := by
  classical
  obtain ⟨g, rfl⟩ := hr
  set d : E := ((g : Matrix ι ι E).submatrix (Subtype.val : s → ι) Subtype.val).det with hd
  have hval : ((bdet s (Matrix.GeneralLinearGroup.map A.i g) : Rˣ) : R) = A.i d := by
    rw [bdet_val s hp, hd, RingHom.map_det]
    congr 1
  have hd0 : d ≠ 0 := by
    intro h0
    have hu := (bdet s (Matrix.GeneralLinearGroup.map A.i g)).isUnit
    rw [hval, h0, map_zero] at hu
    have h10 : (0 : R) = 1 := by
      have := isUnit_zero_iff.1 hu
      exact this
    exact zero_ne_one (hi (by rw [map_zero, map_one, h10]) : (0 : E) = 1)
  refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
  rw [hval]
  rfl


open Classical in
theorem norm_det_blk (M : Matrix ι ι ℂ) (hM : M ∈ Matrix.unitaryGroup ι ℂ) (s : Set ι)
    (h0 : ∀ r, r ∉ s → ∀ c ∈ s, M r c = 0) :
    ‖(M.submatrix (Subtype.val : s → ι) Subtype.val).det‖ = 1 := by
  have h1 : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.1 hM
  have h2 : ((star M * M).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det = 1 := by
    rw [h1, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]
  rw [blk_mul s _ _ h0, Matrix.det_mul, Matrix.star_eq_conjTranspose, ← Matrix.conjTranspose_submatrix,
    Matrix.det_conjTranspose] at h2
  have h3 : ‖(M.submatrix (Subtype.val : s → ι) Subtype.val).det‖ ^ 2 = 1 := by
    have := congrArg norm h2
    rw [norm_mul, norm_star, norm_one] at this
    rw [sq]; exact this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

theorem det_mem_subring {κ : Type} [Fintype κ] [DecidableEq κ] (O : Subring R) (m : Matrix κ κ R)
    (h : ∀ r c, m r c ∈ O) : m.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => h _ _)

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem lg_eq_zero (A : Ad E R) (hA : A.GoodL) (u : Rˣ) (h1 : (u : R) ∈ A.O)
    (h2 : ((u⁻¹ : Rˣ) : R) ∈ A.O) (hw : ∀ w, ‖A.φ w (u : R)‖ = 1) : A.lg u = 0 := by
  let j : Rˣ →* GL Unit R := Units.map (Matrix.scalar Unit : R →+* Matrix Unit Unit R).toMonoidHom
  have hj : j u ∈ A.kGL Unit := by
    refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
    · simpa [j] using h1
    · have : ((j u)⁻¹ : GL Unit R) = j u⁻¹ := (map_inv j u).symm
      rw [this]
      simpa [j] using h2
    · rw [Matrix.mem_unitaryGroup_iff]
      ext r c
      simp [j, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw w]
  have hdet : Continuous fun g : GL Unit R => (Matrix.GeneralLinearGroup.det g : Rˣ) := by
    rw [Units.continuous_iff]
    constructor
    · exact Units.continuous_val.matrix_det
    · have : (fun g : GL Unit R => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R)) =
          fun g => ((g⁻¹ : GL Unit R) : Matrix Unit Unit R).det := by
        funext g
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      rw [this]
      exact (Units.continuous_val.comp continuous_inv).matrix_det
  have hc : Continuous fun g : GL Unit R => A.lg (Matrix.GeneralLinearGroup.det g) :=
    hA.lgcont.comp hdet
  obtain ⟨C, hC⟩ := (hA.kcpt Unit).exists_bound_of_continuousOn hc.continuousOn
  have hone : A.lg 1 = 0 := by
    have := hA.lgmul 1 1
    rw [mul_one] at this
    linarith
  have hpow : ∀ n : ℕ, A.lg (u ^ n) = n * A.lg u := by
    intro n
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, hA.lgmul, ih]; push_cast; ring
  have hdj : Matrix.GeneralLinearGroup.det (j u) = u := by
    apply Units.ext
    simp [j, Matrix.GeneralLinearGroup.val_det_apply]
  have hb : ∀ n : ℕ, (n : ℝ) * |A.lg u| ≤ C := by
    intro n
    have := hC (j u ^ n) (pow_mem hj n)
    rw [map_pow, hdj, hpow, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at this
    exact this
  by_contra hne
  have hpos : 0 < |A.lg u| := abs_pos.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |A.lg u|)
  have := hb n
  rw [div_lt_iff₀ hpos] at hn
  linarith


open Classical in
theorem lg_bdet (A : Ad E R) (hA : A.GoodL) (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s)
    (hk : p ∈ A.kGL ι) : A.lg (bdet s p) = 0 := by
  classical
  refine lg_eq_zero A hA _ ?_ ?_ fun w => ?_
  · rw [bdet_val s hp]
    exact det_mem_subring _ _ fun r c => (hk.1 _ _).1
  · rw [bdet_inv s hp, bdet_val s (inv_mem hp)]
    exact det_mem_subring _ _ fun r c => (hk.1 _ _).2
  · rw [bdet_val s hp, RingHom.map_det]
    refine (congrArg norm (congrArg Matrix.det ?_)).trans
      (norm_det_blk _ (hk.2 w) s fun r hr c hc => ?_)
    · ext r c; rfl
    · simp [(hp r hr c hc).1]

end Places

theorem bdetLaw : BdetLaw := by
  intro E R _ _ _ _ _ _ _ A hA ι _ _ s
  exact ⟨isClosed_stab s, fun p hp q hq => bdet_mul s hp hq, continuousOn_bdet s,
    fun p hp hr => bdet_rat A hA.iinj s hp hr, fun p hp hk => lg_bdet A hA s hp hk, bdet_univ⟩

end GlobalTheory.CompanionTheory.RgEis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardQuadricUnit
section
open Matrix

namespace GlobalTheory.CompanionTheory.SW.QuadricUnit

open GlobalTheory.CompanionTheory.SW.QuadricCount

theorem char_sum {k α : Type} [AddCommGroup k] (ψ : AddChar k ℂ) (s : Finset α) (f : α → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

section OneVar

variable {k : Type} [Field k] [Fintype k] [DecidableEq k]

theorem sum_sq_eq (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {c : k} (hc : c ≠ 0) :
    ∑ y : k, ψ (c * (y * y)) = ∑ z : k, (quadraticChar k z : ℂ) * ψ (c * z) := by
  have h1 : ∑ y : k, ψ (c * (y * y)) = ∑ z : k, ((quadraticChar k z : ℂ) + 1) * ψ (c * z) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun y : k => y ^ 2)]
    refine Finset.sum_congr rfl fun z _ => ?_
    have h2 : ∀ y ∈ Finset.univ.filter (fun y : k => y ^ 2 = z), ψ (c * (y * y)) = ψ (c * z) := by
      intro y hy
      rw [← (Finset.mem_filter.1 hy).2, pow_two]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have h3 := quadraticChar_card_sqrts hchar z
    have h4 : ((Finset.univ.filter (fun y : k => y ^ 2 = z)).card : ℤ) = quadraticChar k z + 1 := by
      rw [← h3]
      congr 2
      ext y
      simp
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h4
  rw [h1]
  simp_rw [add_mul, one_mul]
  rw [Finset.sum_add_distrib]
  have h5 : ∑ z : k, ψ (c * z) = 0 := by
    simp_rw [mul_comm c]
    rw [AddChar.sum_mulShift c (AddChar.IsPrimitive.of_ne_one hψ)]
    simp [hc]
  rw [h5, add_zero]

theorem sum_sq_scale (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {c t : k}
    (hc : c ≠ 0) (ht : t ≠ 0) :
    ∑ y : k, ψ ((t * c) * (y * y)) = (quadraticChar k t : ℂ) * ∑ y : k, ψ (c * (y * y)) := by
  rw [sum_sq_eq hchar ψ hψ (mul_ne_zero ht hc), sum_sq_eq hchar ψ hψ hc, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft₀ t ht) _ _ fun z => ?_
  have h1 : (quadraticChar k t : ℂ) * (quadraticChar k t : ℂ) = 1 := by
    have := quadraticChar_sq_one ht
    have h2 : (quadraticChar k t) * (quadraticChar k t) = 1 := by rw [← pow_two]; exact this
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h2
  have e : (Equiv.mulLeft₀ t ht) z = t * z := rfl
  rw [e, map_mul (quadraticChar k) t z, Int.cast_mul, show t * c * z = c * (t * z) by ring]
  linear_combination (-(quadraticChar k z : ℂ) * ψ (c * (t * z))) * h1

end OneVar

section Form

variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gauss_scale (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    {B : Matrix ι ι k} (hB : B.IsSymm) (hdet : B.det ≠ 0) {M : ℕ}
    (hM : Fintype.card ι = 2 * M) {t : k} (ht : t ≠ 0) :
    ∑ x, ψ (t * quadForm B x) = ∑ x, ψ (quadForm B x) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  haveI : Invertible (2 : k) := invertibleOfNonzero h2
  let Q : QuadraticForm k (ι → k) := (2 : k)⁻¹ • Matrix.toQuadraticForm' B
  have hQ : ∀ x, Q x = quadForm B x := by
    intro x
    simp [Q, quadForm, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']
  have hsep : (QuadraticMap.associated (R := k) Q).SeparatingLeft := by
    intro x hx
    have hass : ∀ y, x ⬝ᵥ (B *ᵥ y) = 0 := by
      intro y
      have hxy : QuadraticMap.associatedHom k Q x y = 0 := hx y
      have hyx : QuadraticMap.associatedHom k Q y x = 0 := by
        rw [← QuadraticMap.associated_isSymm k Q x y]
        exact hxy
      have e1 := QuadraticMap.associated_eq_self_apply k Q (x + y)
      have e2 := QuadraticMap.associated_eq_self_apply k Q x
      have e3 := QuadraticMap.associated_eq_self_apply k Q y
      simp only [map_add (f := _), LinearMap.add_apply] at e1
      rw [hQ, quadForm_add h2 hB] at e1
      rw [hQ] at e2 e3
      linear_combination e2 + e3 - e1 + hxy + hyx
    have hz : B *ᵥ x = 0 := by
      funext i
      have h3 := hass (Pi.single i 1)
      have hs : x ⬝ᵥ (B *ᵥ (Pi.single i 1)) = (Pi.single i 1 : ι → k) ⬝ᵥ (B *ᵥ x) := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
      rw [hs, single_dotProduct, one_mul] at h3
      exact h3
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hz
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  have hsum : ∀ u : k, ∑ x, ψ (u * quadForm B x) = ∏ i, ∑ y : k, ψ ((u * (w i : k)) * (y * y)) := by
    intro u
    calc ∑ x, ψ (u * quadForm B x)
        = ∑ y : Fin (Module.finrank k (ι → k)) → k, ψ (u * ∑ i, (w i : k) * (y i * y i)) := by
          refine Fintype.sum_equiv e.toLinearEquiv.toEquiv _ _ fun x => ?_
          have h3 := e.map_app x
          rw [hQ, QuadraticMap.weightedSumSquares_apply] at h3
          simp only [Units.smul_def, smul_eq_mul] at h3
          rw [← h3]
          rfl
      _ = ∑ y : Fin (Module.finrank k (ι → k)) → k,
            ∏ i, ψ ((u * (w i : k)) * (y i * y i)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum, char_sum]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [mul_assoc]
      _ = ∏ i, ∑ y : k, ψ ((u * (w i : k)) * (y * y)) := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have h1 := hsum 1
  simp only [one_mul] at h1
  rw [hsum t, h1]
  have hsc : ∀ i, ∑ y : k, ψ ((t * (w i : k)) * (y * y)) =
      (quadraticChar k t : ℂ) * ∑ y : k, ψ ((w i : k) * (y * y)) :=
    fun i => sum_sq_scale hchar ψ hψ (w i).ne_zero ht
  simp_rw [hsc]
  have hfr : Fintype.card (Fin (Module.finrank k (ι → k))) = 2 * M := by
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, hM]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hfr, pow_mul]
  have h3 : (quadraticChar k t : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (quadraticChar_sq_one ht)
  rw [h3, one_pow, one_mul]

theorem card_quadric_unit (hchar : ringChar k ≠ 2) (M : ℕ) (hM : Fintype.card ι = 2 * M)
    (hM1 : 1 ≤ M) (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) {s : k} (hs : s ≠ 0) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ (M - 1) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 :=
    AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  set G : ℂ := ∑ x, ψ (quadForm B x) with hG
  have hGn : ‖G‖ = (Fintype.card k : ℝ) ^ M := by
    have := norm_gauss ψ hψ1 h2 hB hdet hM (t := 1) one_ne_zero
    simpa [hG] using this
  have hrest : ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) = -G := by
    have e1 : ∀ t ∈ Finset.univ.erase (0 : k),
        ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) = ψ (t * (-s)) * G := by
      intro t ht
      rw [gauss_scale hchar ψ hψ1 hB hdet hM (Finset.ne_of_mem_erase ht), mul_neg]
    rw [Finset.sum_congr rfl e1, ← Finset.sum_mul]
    have e2 : ∑ t : k, ψ (t * (-s)) = 0 := by
      rw [AddChar.sum_mulShift (-s) (AddChar.IsPrimitive.of_ne_one hψ1)]
      simp [hs]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at e2
    have e3 : ∑ t ∈ Finset.univ.erase (0 : k), ψ (t * (-s)) = -1 := by
      simp only [zero_mul, AddChar.map_zero_eq_one] at e2
      linear_combination e2
    rw [e3]
    ring
  rw [hrest] at hcount
  have hreal : ((((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ)) : ℂ) = -G := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| =
      (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal, norm_neg, hGn]
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  have hpM : (Fintype.card k : ℝ) ^ M = (Fintype.card k : ℝ) ^ (M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hfac, abs_mul, abs_of_pos hq, hpM] at habs
  exact (mul_right_cancel₀ hq.ne' habs).le

end Form

end GlobalTheory.CompanionTheory.SW.QuadricUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableModSquareLocalizationStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparable_mod_square_localization : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Val0 (S := S ⧸ Ideal.span {ϖ ^ 2}) → ∀ P : Ideal S, P.IsPrime → ∀ f g : S ⧸ compI P, f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨ g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := by
  first | exact @GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span | exact GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span | (intros; apply GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWBlockMatrixFormulaStatement
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detW_block_matrix_formula : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    Matrix.det (1 + Complex.I • b) ≠ 0 → ∀ (v : Fin n → ℂ) (d : ℝ),
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExistsStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_quotient_exists : ∀ {S : Type} [CommRing S] , TF (S := S) → ∀ I J : Ideal S, PdI I → (∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) → ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  first | exact @GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient | exact GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient | (intros; apply GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousSectionQuotientStatement
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_section_quotient : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G] (H : Subgroup G), IsClosed (H : Set G) → ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  first | exact @GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | exact GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | (intros; apply GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section <;> assumption)
end

