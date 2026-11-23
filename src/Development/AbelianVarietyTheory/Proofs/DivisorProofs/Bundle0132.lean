module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_power_localization : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → ∃ N : ℕ, ∀ b ∈ P ^ N, ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (exact GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (intros; apply GlobalTheory.dedekind_pow_maximal_mul_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFrameLeadingMinorsSign
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

open scoped ComplexOrder ComplexConjugate Matrix

namespace GlobalTheory.FlagDomain

theorem gram_eq_transpose_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq_transpose_mul, gram_eq_transpose_mul, Matrix.transpose_mul,
    Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem dmin_sign_of_definite (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (h : X.p0 = 0 ∨ X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (hx : (mat x τ).det ≠ 0) (i : Fin (r + 1)) :
    0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  obtain ⟨ε, hε, hsgn⟩ : ∃ ε : ℝ, ε ^ 2 = 1 ∧ ∀ a : ℕ, a < r → sgn X.p0 a = ε := by
    rcases h with h | h
    · exact ⟨-1, by norm_num, fun a _ => by simp [sgn, h]⟩
    · exact ⟨1, by norm_num, fun a ha => by simp [sgn, h, ha]⟩
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hps : psgn X.p0 i = ε ^ (i : ℕ) := by
    unfold psgn
    rw [Finset.prod_congr rfl (g := fun _ => ε), Finset.prod_const, Finset.card_range]
    intro a ha
    exact hsgn a (lt_of_lt_of_le (Finset.mem_range.1 ha) hi)
  obtain ⟨P, hPdet, hP⟩ := X.signature τ
  set M := mat x τ with hM
  set Q := P⁻¹ * M with hQ
  have hPQ : P * Q = M := Matrix.mul_nonsing_inv_cancel_left P M (isUnit_iff_ne_zero.2 hPdet)
  have hQdet : Q.det ≠ 0 := by
    intro h0
    apply hx
    rw [← hPQ, Matrix.det_mul, h0, mul_zero]
  set N := Q.map (starRingEnd ℂ) with hN
  have hNdet : N.det ≠ 0 := by
    rw [hN, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hQdet
  have hNinj : Function.Injective N.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det N).2 (isUnit_iff_ne_zero.2 hNdet))
  have hH : (Nᴴ * N).PosDef := Matrix.PosDef.conjTranspose_mul_self N hNinj
  have hNt : Nᴴ = Qᵀ := by
    ext a b
    simp [hN, Matrix.conjTranspose_apply]
  have hdiag : Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) = (ε : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rw [Matrix.smul_one_eq_diagonal]
    congr 1
    funext a
    rw [hsgn a a.isLt]
  have hgram : gram τ.1 X.Gm M = (ε : ℂ) • (Nᴴ * N) := by
    rw [← hPQ, GlobalTheory.FlagDomain.gram_mul, hP, hdiag, hNt, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  set e := Fin.castLE hi with he
  have hsub : ((Nᴴ * N).submatrix e e).PosDef := hH.submatrix (Fin.castLE_injective hi)
  have hdpos := Complex.pos_iff.1 hsub.det_pos
  have hd : dmin X.Gm x τ i = ((ε ^ (i : ℕ) : ℝ) : ℂ) * ((Nᴴ * N).submatrix e e).det := by
    simp only [dmin, lminor]
    have hs : ((ε : ℂ) • (Nᴴ * N)).submatrix e e = (ε : ℂ) • ((Nᴴ * N).submatrix e e) := by
      ext a b
      simp
    rw [← hM, hgram, ← he, hs, Matrix.det_smul, Fintype.card_fin]
    push_cast
    rfl
  rw [hd, Complex.re_ofReal_mul, hps, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, hε, one_pow,
    one_mul]
  exact hdpos.1

theorem definite_frame_leading_minors_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ (x : Frame X.Ψ r) (τ : X.Ψ), (mat x τ).det ≠ 0 →
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re :=
  fun E _ _ _ r X h x τ hx i => dmin_sign_of_definite E r X h x τ hx i

end GlobalTheory.FlagDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeCountGenerates
section
open Polynomial

namespace GlobalTheory.PicDiv

theorem degree_count_generates : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (D P₀ P : Ideal A) (Q Q' : I → Ideal A) (f₀ f : A), P₀.IsMaximal → P.IsMaximal → (∀ i, (Q i).IsMaximal) → (∀ i, (Q' i).IsMaximal) → Function.Injective Q' → (∀ i, Q' i ≠ P) → (∀ i, ¬ D ≤ Q' i) → ¬ D ≤ P →
 f₀ ≠ 0 → f ≠ 0 → Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N → f ∈ D → f ∈ P → (∀ i, f ∈ Q' i ^ N) → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀}) →
 Ideal.span {f} = P * D * ∏ i, Q' i ^ N := by
  intro k A _ _ _ _ _ _ N I _ D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hQ'P hDQ' hDP hf₀ hf hspan hfD hfP hfQ' hdeg
  obtain ⟨_hfin, hmax, hmul, hle⟩ := GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A
  have hPne : P ≠ ⊥ := by
    intro h; apply hf; rw [h] at hfP; simpa using hfP
  have hmaxne : ∀ M : Ideal A, M.IsMaximal → M ≠ ⊥ := by
    intro M hM h
    subst h
    exact hPne (hM.eq_of_le hP.ne_top bot_le).symm
  have hDne : D ≠ ⊥ := by
    intro h; exact hDP (h ▸ bot_le)
  have hprodne : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) → (∏ i ∈ s, g i) ≠ ⊥ := by
    intro s g hg
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro i _; rw [Ideal.zero_eq_bot]; exact hg i
  have hpowne : ∀ (M : Ideal A) (n : ℕ), M ≠ ⊥ → M ^ n ≠ ⊥ := by
    intro M n hM
    rw [← Ideal.zero_eq_bot] at hM ⊢
    exact pow_ne_zero n hM
  have hmulne : ∀ (M M' : Ideal A), M ≠ ⊥ → M' ≠ ⊥ → M * M' ≠ ⊥ := by
    intro M M' hM hM'
    rw [← Ideal.zero_eq_bot] at hM hM' ⊢
    exact mul_ne_zero hM hM'
  have htop : Module.finrank k (A ⧸ (⊤ : Ideal A)) = 0 := by
    haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  have hpow : ∀ (M : Ideal A) (n : ℕ), M.IsMaximal → Module.finrank k (A ⧸ M ^ n) = n := by
    intro M n hM
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, htop]
    | succ n ih =>
      rw [pow_succ, hmul _ _ (hpowne M n (hmaxne M hM)) (hmaxne M hM), ih, (hmax M hM).1]
  have hprod : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) →
      Module.finrank k (A ⧸ ∏ i ∈ s, g i) = ∑ i ∈ s, Module.finrank k (A ⧸ g i) := by
    intro s g hg
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top, htop]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul _ _ (hg a) (hprodne s g hg), ih]
  have hPowProd : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) →
      Module.finrank k (A ⧸ ∏ i, R i ^ N) = N * Fintype.card I := by
    intro R hR
    rw [hprod _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))]
    simp only [hpow _ _ (hR _), Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hPowNe : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) → (∏ i, R i ^ N) ≠ ⊥ :=
    fun R hR => hprodne _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))
  have h0 : Module.finrank k (A ⧸ Ideal.span {f₀}) =
      1 + Module.finrank k (A ⧸ D) + N * Fintype.card I := by
    rw [hspan, hmul _ _ (hmulne _ _ (hmaxne _ hP₀) hDne) (hPowNe Q hQ),
      hmul _ _ (hmaxne _ hP₀) hDne, (hmax _ hP₀).1, hPowProd Q hQ]
  have hcop_max : ∀ M M' : Ideal A, M.IsMaximal → M'.IsMaximal → M ≠ M' → IsCoprime M M' := by
    intro M M' hM hM' hne
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have h1 := hM.eq_of_le h le_sup_left
    have h2 := hM'.eq_of_le h le_sup_right
    exact hne (h1.trans h2.symm)
  have hcopD : ∀ M : Ideal A, M.IsMaximal → ¬ D ≤ M → IsCoprime M D := by
    intro M hM hDM
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hDM (le_sup_right.trans (hM.eq_of_le h le_sup_left).ge)
  have hdvd : ∀ M : Ideal A, f ∈ M → M ∣ Ideal.span {f} := fun M hM =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hM)
  have hX : (∏ i, Q' i ^ N) ∣ Ideal.span {f} := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (hcop_max _ _ (hQ' i) (hQ' j) (hinj.ne hij)).pow
    · intro i _; exact hdvd _ (hfQ' i)
  have hPD : P * D ∣ Ideal.span {f} := (hcopD P hP hDP).mul_dvd (hdvd _ hfP) (hdvd _ hfD)
  have hPDX : IsCoprime (P * D) (∏ i, Q' i ^ N) :=
    IsCoprime.mul_left
      (IsCoprime.prod_right fun i _ => (hcop_max P (Q' i) hP (hQ' i) (hQ'P i).symm).pow_right)
      (IsCoprime.prod_right fun i _ => (hcopD (Q' i) (hQ' i) (hDQ' i)).symm.pow_right)
  have hJ : P * D * ∏ i, Q' i ^ N ∣ Ideal.span {f} := hPDX.mul_dvd hPD hX
  apply hle _ _ _ (Ideal.le_of_dvd hJ)
  · rw [hmul _ _ (hmulne _ _ hPne hDne) (hPowNe Q' hQ'), hmul _ _ hPne hDne, (hmax _ hP).1,
      hPowProd Q' hQ']
    rw [h0] at hdeg; exact hdeg
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hf

end GlobalTheory.PicDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendElementOfFieldEqualizerFaithfullyFlat
section
open scoped TensorProduct

namespace GlobalTheory.SymDesc

variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Algebra R R₁]

theorem injective_quotient (Q : Ideal R₁) (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    Function.Injective (algebraMap R (R₁ ⧸ Q)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have : r ∈ Q.comap (algebraMap R R₁) := by
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
    exact hr
  rwa [hQ, Ideal.mem_bot] at this

theorem exists_sub_mem_of_under_eq_bot [IsIntegrallyClosed R] [CharZero R]
    [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q : Ideal R₁) [Q.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    ∃ e : R, s - algebraMap R R₁ e ∈ Q := by
  classical
  let A := R₁ ⧸ Q
  let K₀ := FractionRing A
  let F := FractionRing R
  have hRA : Function.Injective (algebraMap R A) := injective_quotient Q hQ
  have hRK : Function.Injective (algebraMap R K₀) := by
    rw [IsScalarTower.algebraMap_eq R A K₀]
    exact (IsFractionRing.injective A K₀).comp hRA
  haveI : FaithfulSMul R K₀ := (faithfulSMul_iff_algebraMap_injective R K₀).2 hRK
  letI : Algebra F K₀ := FractionRing.liftAlgebra R K₀
  haveI : IsScalarTower R F K₀ := FractionRing.isScalarTower_liftAlgebra R K₀
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hRA
  haveI : Algebra.IsAlgebraic R A := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsAlgebraic R K₀ := (IsFractionRing.isAlgebraic_iff' R A K₀).1 inferInstance
  haveI : Algebra.IsAlgebraic F K₀ :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff R F K₀).1 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  let π : R₁ →+* K₀ := (algebraMap A K₀).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ r : R, π (algebraMap R R₁ r) = algebraMap F K₀ (algebraMap R F r) := by
    intro r
    have hq : (Ideal.Quotient.mk Q) ((algebraMap R R₁) r) = algebraMap R A r := by
      first | rfl | exact Ideal.Quotient.mk_algebraMap _ _ | simp [A]
    simp only [π, RingHom.comp_apply]
    rw [hq, ← IsScalarTower.algebraMap_apply R A K₀, ← IsScalarTower.algebraMap_apply R F K₀]
  obtain ⟨e', he'⟩ := GlobalTheory.mem_range_of_forall_algHom_eq F K₀ inferInstance (π s) (by
    intro Ω _ _ φ₁ φ₂
    have h := hs Ω (φ₁.toRingHom.comp π) (φ₂.toRingHom.comp π) (by
      ext r
      simp only [RingHom.comp_apply, hπ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes])
    simpa using h)
  have hint : IsIntegral R (π s) := by
    have h1 : IsIntegral R (Ideal.Quotient.mk Q s) := Algebra.IsIntegral.isIntegral _
    exact h1.map (IsScalarTower.toAlgHom R A K₀)
  rw [← he'] at hint
  have hint' : IsIntegral R e' :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R F K₀) (algebraMap F K₀).injective).1 hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  refine ⟨y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply IsFractionRing.injective A K₀
  rw [map_zero]
  have h : π (s - algebraMap R R₁ y) = 0 := by
    rw [RingHom.map_sub, hπ, hy, he', sub_self]
  exact h

theorem eq_of_sub_mem [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q Q' : Ideal R₁) [Q.IsPrime] [Q'.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥)
    (hQ' : Q'.comap (algebraMap R R₁) = ⊥) (e e' : R) (he : s - algebraMap R R₁ e ∈ Q)
    (he' : s - algebraMap R R₁ e' ∈ Q') : e = e' := by
  classical
  let F := FractionRing R
  let M := AlgebraicClosure F
  have hRM : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R F M]
    exact (algebraMap F M).injective.comp (IsFractionRing.injective R F)
  haveI : FaithfulSMul R M := (faithfulSMul_iff_algebraMap_injective R M).2 hRM
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRM
  have key : ∀ (P : Ideal R₁) [P.IsPrime], P.comap (algebraMap R R₁) = ⊥ →
      ∃ j : R₁ →+* M, j.comp (algebraMap R R₁) = algebraMap R M ∧ ∀ x ∈ P, j x = 0 := by
    intro P _ hP
    have hRA : Function.Injective (algebraMap R (R₁ ⧸ P)) := injective_quotient P hP
    haveI : FaithfulSMul R (R₁ ⧸ P) := (faithfulSMul_iff_algebraMap_injective R _).2 hRA
    haveI : Module.IsTorsionFree R (R₁ ⧸ P) := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRA
    haveI : Algebra.IsAlgebraic R (R₁ ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let l : (R₁ ⧸ P) →ₐ[R] M := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_, fun x hx => ?_⟩
    · ext r
      simp only [RingHom.comp_apply, Ideal.Quotient.mk_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes]
    · simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  obtain ⟨j, hj, hj0⟩ := key Q hQ
  obtain ⟨j', hj', hj0'⟩ := key Q' hQ'
  have h := hs M j j' (hj.trans hj'.symm)
  have h1 : j s = algebraMap R M e := by
    have := hj0 _ he
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj]
  have h2 : j' s = algebraMap R M e' := by
    have := hj0' _ he'
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj']
  exact hRM (h1.symm.trans (h.trans h2))

end GlobalTheory.SymDesc

namespace GlobalTheory

theorem exists_eq_algebraMap_of_forall_ringHom_eq : ∀ (R R₁ : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ →
    Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) →
    ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by
  intro R R₁ _ _ _ _ _ _ hfin hff s hs
  haveI := hfin
  haveI := hff
  haveI : Algebra.IsIntegral R R₁ := Algebra.IsIntegral.of_finite R R₁
  have hinj : Function.Injective (algebraMap R R₁) := FaithfulSMul.algebraMap_injective R R₁
  have hker : Ideal.comap (algebraMap R R₁) (⊥ : Ideal R₁) ≤ ⊥ := by
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_bot] at hr
    rw [Ideal.mem_bot]
    exact hinj (by rw [hr, map_zero])
  obtain ⟨Q₀, -, hQ₀, hQ₀b⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (⊥ : Ideal R) ⊥ hker
  haveI := hQ₀
  obtain ⟨e, he⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q₀ hQ₀b
  refine ⟨e, fun K _ i₁ => ?_⟩
  let P := RingHom.ker i₁
  haveI : P.IsPrime := RingHom.ker_isPrime i₁
  haveI : P.LiesOver (P.under R) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQo⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R)) (q := P.under R) P bot_le
  have hQb : Q.comap (algebraMap R R₁) = ⊥ := hQo.over.symm
  obtain ⟨e₁, he₁⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q hQb
  have hee := SymDesc.eq_of_sub_mem s hs Q₀ Q hQ₀b hQb e e₁ he he₁
  subst hee
  have hm : s - algebraMap R R₁ e ∈ P := hQP he₁
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  exact hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicitStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_block_change_of_basis_via_two_families_implicit : ∀ {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N),
    (∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) → ∀ (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F),
    (∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) → (∀ k, mu k = ∑ l, A k l • nu l) →
    (∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) →
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  first | exact @GlobalTheory.Div.BlockChangeDet.det_block_change' | exact GlobalTheory.Div.BlockChangeDet.det_block_change' | (intros; apply GlobalTheory.Div.BlockChangeDet.det_block_change' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNearOneMatrixNormBoundsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_near_one_matrix_norm_bounds : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ), (∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) → (n : ℝ) * ε ≤ 1 / 2 → (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  first | exact @GlobalTheory.det_near_one_bounds | exact GlobalTheory.det_near_one_bounds | (intros; apply GlobalTheory.det_near_one_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DigitsSumLeLogbStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digits_sum_le_mul_logb : ∀ (p n : ℕ), p.Prime → (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  first | exact @GlobalTheory.digits_sum_le_logb | exact GlobalTheory.digits_sum_le_logb | (intros; apply GlobalTheory.digits_sum_le_logb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirectedSystemEtaleBaseChangePolynomialStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.directedSystem_etale_baseChange_polynomial : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (i₀ : ι), (∀ k, i₀ ≤ k) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E]
      (E₀ : Type) [CommRing E₀] [Algebra (Polynomial (𝒜 i₀)) E₀] [Algebra.Etale (Polynomial (𝒜 i₀)) E₀],
      (letI : Algebra (Polynomial (𝒜 i₀)) (Polynomial T) :=
          (Polynomial.mapRingHom (𝒜 i₀).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i₀)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) →
    ∃ (Ek : ι → Type) (_ : ∀ k, CommRing (Ek k)) (_ : ∀ k, Algebra (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra (𝒜 k) (Ek k)) (_ : ∀ k, IsScalarTower (𝒜 k) (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra.Etale (Polynomial (𝒜 k)) (Ek k))
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k, (e k).comp (algebraMap (Polynomial (𝒜 k)) (Ek k)) =
          (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 k).subtype)) ∧
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) ∧
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : Ek k), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : Ek k),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ x : E, ∃ k y, e k y = x) := by
  first | (exact @GlobalTheory.directedSystem_etaleBaseChange) | (exact GlobalTheory.directedSystem_etaleBaseChange) | (intros; apply GlobalTheory.directedSystem_etaleBaseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrExistsUnitPowEqMulUniformizerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_exists_unit_pow_eq_mul_uniformizer : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V], Function.Injective (algebraMap T V) →
    ∀ (α : V) (ϖ u : T) (m k : ℕ), Irreducible ϖ → IsUnit u → 0 < k →
    α ^ (m * k) = algebraMap T V (u * ϖ ^ k) →
    ∃ γ : V, IsUnit γ ∧ α ^ m = γ * algebraMap T V ϖ ∧ γ ^ k = algebraMap T V u := by
  first | (exact @GlobalTheory.dvr_pow_mul_eq_unit_mul_pow_unif) | (exact GlobalTheory.dvr_pow_mul_eq_unit_mul_pow_unif) | (intros; apply GlobalTheory.dvr_pow_mul_eq_unit_mul_pow_unif  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrSubringEqTopStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subring_eq_univ_of_uniformizer_generates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (S : Subring V) (π : V), π ∈ S → π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V → (∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1) → (∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) → (∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) → S = ⊤ := by
  first | exact @GlobalTheory.dvrSubring_eq_top | exact GlobalTheory.dvrSubring_eq_top | (intros; apply GlobalTheory.dvrSubring_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionsOfComaximalStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_projections_tensor_of_comaximal : ∀ (R F : Type) [CommRing R] [CommRing F] (a : ℕ) (t : Fin a → (F →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∃ e : Fin a → R ⊗[ℤ] F, ∀ (M : Type) [AddCommGroup M] (Θ : R ⊗[ℤ] F →+* AddMonoid.End M) (i l : Fin a) (m : M), (∀ c : F, Θ (1 ⊗ₜ c) m = Θ (t l c ⊗ₜ 1) m) → Θ (e i) m = if i = l then m else 0 := by
  first | (exact @GlobalTheory.eigenProjections_of_comaximal) | (exact GlobalTheory.eigenProjections_of_comaximal) | (intros; apply GlobalTheory.eigenProjections_of_comaximal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallResidueFieldFunctionalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_forall_residueField_functional' : ∀ (A M : Type) [CommRing A] [IsReduced A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M), (∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) → x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_forall_residueField_functional | exact GlobalTheory.eq_zero_of_forall_residueField_functional | (intros; apply GlobalTheory.eq_zero_of_forall_residueField_functional <;> assumption)
end

