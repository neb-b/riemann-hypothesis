module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieAlgebraSpanned
section
open Matrix

namespace GlobalTheory.TracelessSkewSpan

variable {r : ℕ}

noncomputable def skewSub (A : Matrix (Fin r) (Fin r) ℂ) :
    Submodule ℝ (Matrix (Fin r) (Fin r) ℂ) where
  carrier := {Y | Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    have h : (X + Y).map (starRingEnd ℂ) = X.map (starRingEnd ℂ) + Y.map (starRingEnd ℂ) := by
      ext i j; simp
    rw [transpose_add, h, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᵀ * A + A * X.map (starRingEnd ℂ)) + (Yᵀ * A + A * Y.map (starRingEnd ℂ)) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c Y hY
    simp only [Set.mem_setOf_eq] at *
    have h1 : (c • Y).map (starRingEnd ℂ) = c • Y.map (starRingEnd ℂ) := by
      ext i j; simp [Complex.real_smul]
    rw [transpose_smul, h1, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY, smul_zero]

lemma mem_skewSub {A Y : Matrix (Fin r) (Fin r) ℂ} :
    Y ∈ skewSub A ↔ Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0 := Iff.rfl

lemma eq_zero_of_mem_of_I_smul_mem {A Y : Matrix (Fin r) (Fin r) ℂ} (hA : A.det ≠ 0)
    (h1 : Y ∈ skewSub A) (h2 : Complex.I • Y ∈ skewSub A) : Y = 0 := by
  rw [mem_skewSub] at h1 h2
  have hc : (Complex.I • Y).map (starRingEnd ℂ) = (-Complex.I) • Y.map (starRingEnd ℂ) := by
    ext i j; simp
  rw [transpose_smul, hc, Matrix.smul_mul, Matrix.mul_smul] at h2
  have h3 : Yᵀ * A - A * Y.map (starRingEnd ℂ) = 0 := by
    have : Complex.I • (Yᵀ * A - A * Y.map (starRingEnd ℂ)) = 0 := by
      rw [smul_sub, ← h2, neg_smul]; abel
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h Complex.I_ne_zero
    · exact h
  have h4 : Yᵀ * A = 0 := by
    have : (2 : ℂ) • (Yᵀ * A) = 0 := by
      rw [two_smul]
      calc Yᵀ * A + Yᵀ * A = (Yᵀ * A + A * Y.map (starRingEnd ℂ)) + (Yᵀ * A - A * Y.map (starRingEnd ℂ)) := by abel
        _ = 0 := by rw [h1, h3, add_zero]
    rcases smul_eq_zero.mp this with h | h
    · norm_num at h
    · exact h
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have h5 : Yᵀ = 0 := by
    calc Yᵀ = Yᵀ * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hu, Matrix.mul_one]
      _ = 0 := by rw [h4, Matrix.zero_mul]
  simpa using congrArg Matrix.transpose h5

lemma finrank_skewSub_mul_two_le {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.det ≠ 0) :
    2 * Module.finrank ℝ (skewSub A) ≤ 2 * (r * r) := by
  set u := skewSub A
  let f : (u × u) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ :=
    u.subtype ∘ₗ LinearMap.fst ℝ u u + (Complex.I • LinearMap.id) ∘ₗ u.subtype ∘ₗ LinearMap.snd ℝ u u
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hab' : (a : Matrix (Fin r) (Fin r) ℂ) + Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = 0 := by
      simpa [f] using hab
    have hIb : Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) ∈ u := by
      have : Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = -(a : Matrix (Fin r) (Fin r) ℂ) :=
        eq_neg_of_add_eq_zero_right hab'
      rw [this]; exact u.neg_mem a.2
    have hb : (b : Matrix (Fin r) (Fin r) ℂ) = 0 := eq_zero_of_mem_of_I_smul_mem hA b.2 hIb
    have ha : (a : Matrix (Fin r) (Fin r) ℂ) = 0 := by simpa [hb] using hab'
    ext1
    · exact Subtype.ext ha
    · exact Subtype.ext hb
  have := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_prod, Module.finrank_matrix, Complex.finrank_real_complex] at this
  simp only [Fintype.card_fin] at this
  linarith

theorem mem_span_of_linearIndependent {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.det ≠ 0)
    (v : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ) (hv : LinearIndependent ℝ v)
    (hvu : ∀ i, (v i)ᵀ * A + A * (v i).map (starRingEnd ℂ) = 0 ∧ (v i).trace = 0)
    (Y : Matrix (Fin r) (Fin r) ℂ) (hY : Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0)
    (hYt : Y.trace = 0) : Y ∈ Submodule.span ℝ (Set.range v) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have : Y = 0 := Subsingleton.elim _ _
    rw [this]; exact Submodule.zero_mem _
  set u := skewSub A
  set su := u ⊓ LinearMap.ker ((Matrix.traceLinearMap (Fin r) ℂ ℂ).restrictScalars ℝ)
  have hYsu : Y ∈ su := ⟨hY, by simpa using hYt⟩
  have hle : Submodule.span ℝ (Set.range v) ≤ su := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(hvu i).1, by simpa using (hvu i).2⟩
  have hIu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∈ u := by
    rw [mem_skewSub]
    have hc : (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)).map (starRingEnd ℂ)
        = (-Complex.I) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, neg_smul, add_neg_cancel]
  have hIsu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∉ su := by
    rintro ⟨-, h⟩
    have h' : Matrix.trace (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)) = 0 := by simpa using h
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at h'
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact Complex.I_ne_zero h''
    · exact absurd (by exact_mod_cast h'' : r = 0) hr.ne'
  have hlt : su < u := lt_of_le_of_ne inf_le_left (fun h => hIsu (h ▸ hIu))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : 2 * Module.finrank ℝ u ≤ 2 * (r * r) := finrank_skewSub_mul_two_le hA
  have hspan := finrank_span_eq_card hv
  rw [Fintype.card_fin] at hspan
  have heq : Submodule.span ℝ (Set.range v) = su := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hspan, sq]
    change Module.finrank ℝ su ≤ r * r - 1
    generalize r * r = n at h2 ⊢
    omega
  rw [heq]; exact hYsu

end GlobalTheory.TracelessSkewSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
section
namespace GlobalTheory

def UnramSub {V F : Type} [CommRing V] [Field F] (i : V →+* F) (T : Subring F) : Prop :=
  ∃ (_ : IsDiscreteValuationRing T) (f : V →+* T), (∀ v, (f v : F) = i v) ∧ ∀ π : V, Irreducible π → Irreducible (f π)

namespace UnramSub

variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}

theorem mem {T : Subring F} (h : UnramSub i T) (v : V) : i v ∈ T := by
  obtain ⟨_, f, hf, -⟩ := h
  exact hf v ▸ (f v).2

theorem isDVR {T : Subring F} (h : UnramSub i T) : IsDiscreteValuationRing T := h.1

theorem trans {T₁ T₂ : Subring F} (h₁ : UnramSub i T₁) (h₂ : UnramSub T₁.subtype T₂) : UnramSub i T₂ := by
  obtain ⟨_, f₁, hf₁, hi₁⟩ := h₁
  obtain ⟨_, f₂, hf₂, hi₂⟩ := h₂
  refine ⟨‹_›, f₂.comp f₁, fun v => ?_, fun π hπ => hi₂ _ (hi₁ π hπ)⟩
  rw [RingHom.comp_apply, hf₂, Subring.coe_subtype, hf₁]

theorem le {T₁ T₂ : Subring F} (h₂ : UnramSub T₁.subtype T₂) : T₁ ≤ T₂ := fun z hz => h₂.mem ⟨z, hz⟩

theorem range [IsDomain V] [IsDiscreteValuationRing V] (hi : Function.Injective i) : UnramSub i i.range := by
  let e : V ≃+* i.range := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hi)
  exact ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, e.toRingHom, fun v => rfl,
    fun π hπ => hπ.map e⟩

end UnramSub

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularNearUnitDiagonalOfTwistedGramNear
section
open scoped Matrix

namespace GlobalTheory

theorem ldl_gram_apply {r : ℕ} (ε : Fin r → ℝ) (b : Matrix (Fin r) (Fin r) ℂ) (a c : Fin r) :
    (bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c
      = ∑ j, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

theorem upperTriangular_near_diag_of_gram_near (r : ℕ) (ε : Fin r → ℝ)
    (b : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ) (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hδ : 0 ≤ δ)
    (hrδ : (r : ℝ) * δ ≤ 1 / 100) (htri : ∀ a c : Fin r, c < a → b a c = 0)
    (hG : ∀ a c : Fin r, ‖(bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c
      - Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) a c‖ ≤ 3 * δ) :
    (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) ∧ ∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ := by
  have hD : ∀ j, ‖((ε j : ℝ) : ℂ)‖ = 1 := fun j => by rcases hε j with h | h <;> simp [h]
  have key : ∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ ∧ ∀ c, a < c → ‖b a c‖ ≤ 6 * δ := by
    intro a
    induction a using WellFoundedLT.induction with
    | _ a ih =>
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fin.pos a).ne')
    have hδ1 : δ ≤ 1 / 100 := by nlinarith

    have hR : ∀ c, a ≤ c → ‖∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)‖
        ≤ 36 / 100 * δ := by
      intro c hac
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ j ∈ Finset.univ.erase a,
          ‖b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)‖ ≤ 36 * δ ^ 2 := by
        intro j hj
        have hja : j ≠ a := Finset.ne_of_mem_erase hj
        rw [norm_mul, norm_mul, hD, Complex.norm_conj, mul_one]
        rcases lt_or_gt_of_ne hja with hlt | hgt
        · have h1 := (ih j hlt).2 a hlt
          have h2 := (ih j hlt).2 c (lt_of_lt_of_le hlt hac)
          have := mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
          nlinarith
        · rw [htri j a hgt]; simp; positivity
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [nsmul_eq_mul]
      have hc : ((Finset.univ.erase a).card : ℝ) ≤ r := by
        have := Finset.card_erase_le (s := (Finset.univ : Finset (Fin r))) (a := a)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
      have : ((Finset.univ.erase a).card : ℝ) * (36 * δ ^ 2) ≤ r * (36 * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      nlinarith
    have hsplit : ∀ c, (bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c
        = b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c)
          + ∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c) := by
      intro c
      rw [ldl_gram_apply]
      exact (Finset.add_sum_erase Finset.univ
        (fun j => b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)) (Finset.mem_univ a)).symm

    have hdiag : |‖b a a‖ ^ 2 - 1| ≤ 3 * δ + 36 / 100 * δ := by
      have h0 := hG a a
      rw [hsplit, Matrix.diagonal_apply_eq] at h0
      have hR0 := hR a le_rfl
      have hx : b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) - ((ε a : ℝ) : ℂ)
          = ((ε a : ℝ) : ℂ) * (((‖b a a‖ ^ 2 - 1 : ℝ)) : ℂ) := by
        rw [mul_right_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      have hn : ‖b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) - ((ε a : ℝ) : ℂ)‖
          = |‖b a a‖ ^ 2 - 1| := by
        rw [hx, norm_mul, hD, one_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [← hn]
      set R := ∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j a)
      have : b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) - ((ε a : ℝ) : ℂ)
          = (b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a a) + R - ((ε a : ℝ) : ℂ)) - R := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add h0 hR0)
    refine ⟨by linarith, fun c hac => ?_⟩
    have h0 := hG a c
    rw [hsplit, Matrix.diagonal_apply_ne _ (ne_of_lt hac), sub_zero] at h0
    have hR0 := hR c hac.le
    have hprod : ‖b a a‖ * ‖b a c‖ ≤ 3 * δ + 36 / 100 * δ := by
      have e : ‖b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c)‖ = ‖b a a‖ * ‖b a c‖ := by
        rw [norm_mul, norm_mul, hD, Complex.norm_conj, mul_one]
      rw [← e]
      set R := ∑ j ∈ Finset.univ.erase a, b j a * ((ε j : ℝ) : ℂ) * starRingEnd ℂ (b j c)
      have : b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c)
          = (b a a * ((ε a : ℝ) : ℂ) * starRingEnd ℂ (b a c) + R) - R := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add h0 hR0)
    have hsq : 9 / 10 ≤ ‖b a a‖ := by
      have h1 := (abs_le.mp hdiag).1
      nlinarith [norm_nonneg (b a a)]
    have hy := norm_nonneg (b a c)
    nlinarith
  exact ⟨fun a => (key a).1, fun a c h => (key a).2 c h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeExpNegCardInertiaOfInertiaFixed
section
open IsDedekindDomain

namespace GlobalTheory.InertiaFixedVal

theorem valuation_le_exp_neg_card_inertia (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (y : L) :
    (∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) → P.valuation L y < 1 →
      P.valuation L y ≤ WithZero.exp (-(Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) : ℤ)) := by
  intro hy hv
  classical
  let H : Subgroup (L ≃ₐ[K] L) := P.asIdeal.inertia (L ≃ₐ[K] L)
  let E : IntermediateField K L := FixedPoints.intermediateField H
  haveI : IsGaloisGroup H E L := IsGaloisGroup.subgroup (L ≃ₐ[K] L) K L H
  haveI : IsScalarTower R E L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K E]; rfl
  let OE := integralClosure R E
  haveI : IsFractionRing OE E := integralClosure.isFractionRing_of_finite_extension K E
  haveI : IsDedekindDomain OE := integralClosure.isDedekindDomain R K E
  let f : OE →ₐ[R] integralClosure R L := ((IsScalarTower.toAlgHom R E L).comp OE.val).codRestrict _
    (fun x => x.2.map (IsScalarTower.toAlgHom R E L))
  letI : Algebra OE (integralClosure R L) := f.toRingHom.toAlgebra
  haveI : IsScalarTower OE (integralClosure R L) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R OE (integralClosure R L) := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  haveI : Algebra.IsIntegral OE (integralClosure R L) := Algebra.IsIntegral.tower_top R
  haveI : FaithfulSMul OE (integralClosure R L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have := congrArg (fun x : integralClosure R L => (x : L)) hab
    exact Subtype.ext (FaithfulSMul.algebraMap_injective E L this)
  haveI : Module.IsTorsionFree OE (integralClosure R L) := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L (integralClosure R L)
  haveI : Module.Finite OE (integralClosure R L) := Module.Finite.of_restrictScalars_finite R OE _
  haveI : Module.Flat OE (integralClosure R L) := inferInstance
  haveI : SMulDistribClass H (integralClosure R L) L := inferInstance
  haveI : IsGaloisGroup H OE (integralClosure R L) := IsGaloisGroup.of_isFractionRing H OE (integralClosure R L) E L

  let Q : Ideal OE := P.asIdeal.under OE
  have hPne : P.asIdeal ≠ ⊥ := P.ne_bot
  have hQne : Q ≠ ⊥ := by
    exact Ideal.under_ne_bot OE hPne
  haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQne
  have hQR : (Q.under R).IsMaximal := Ideal.IsMaximal.under R Q
  haveI : Q.LiesOver (IsLocalRing.maximalIdeal R) := ⟨(IsLocalRing.eq_maximalIdeal hQR).symm⟩
  letI : Field (OE ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  haveI : Algebra.IsIntegral R OE := ⟨fun x => integralClosure.isIntegral x⟩
  haveI : Algebra.IsIntegral (R ⧸ IsLocalRing.maximalIdeal R) (OE ⧸ Q) := inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ IsLocalRing.maximalIdeal R) (OE ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : PerfectField (OE ⧸ Q) := by
    haveI : PerfectField (R ⧸ IsLocalRing.maximalIdeal R) := ‹PerfectField (IsLocalRing.ResidueField R)›
    exact Algebra.IsAlgebraic.perfectField (R ⧸ IsLocalRing.maximalIdeal R)
  haveI : PerfectField Q.ResidueField :=
    PerfectField.of_ringEquiv (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField Q))
  have htop : P.asIdeal.inertia H = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro σ
    exact AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp σ.2 x
  have hcard : Nat.card H = P.asIdeal.ramificationIdx OE := by
    have h := Ideal.card_inertia_eq_ramificationIdxIn (G := H) Q P.asIdeal
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q P.asIdeal H, htop, Subgroup.card_top] at h
    exact h

  have hyE : y ∈ E := fun σ => hy σ σ.2
  let z : E := ⟨y, hyE⟩
  let w : HeightOneSpectrum OE := ⟨Q, inferInstance, hQne⟩
  haveI : P.asIdeal.LiesOver w.asIdeal := inferInstance
  have hval := HeightOneSpectrum.valuation_liesOver L w P z
  rw [← hcard] at hval
  change w.valuation E z ^ Nat.card H = P.valuation L y at hval
  have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hz : w.valuation E z < 1 := by
    by_contra h
    rw [not_lt] at h
    have := one_le_pow₀ (n := Nat.card H) h
    rw [hval] at this
    exact absurd hv (not_lt.mpr this)
  have hz1 : w.valuation E z ≤ WithZero.exp (-1) := by
    by_cases h0 : w.valuation E z = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0] at hz ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
      rw [WithZero.exp_le_exp]
      omega
  rw [← hval]
  calc w.valuation E z ^ Nat.card H ≤ WithZero.exp (-1) ^ Nat.card H := pow_le_pow_left₀ zero_le hz1 _
    _ = WithZero.exp (-(Nat.card H : ℤ)) := by
      rw [← WithZero.exp_nsmul]; congr 1; simp
end GlobalTheory.InertiaFixedVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprime
section
namespace GlobalTheory.CMModel

theorem valuation_natCast_eq_one_of_coprime (V : ValuationSubring ℂ) (a b : ℕ)
    (h : Nat.Coprime a b) :
    V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  have hint : ∀ z : ℤ, V.valuation (z : ℂ) ≤ 1 := fun z =>
    (V.valuation_le_one_iff _).2 (intCast_mem V z)
  have hnat : ∀ n : ℕ, V.valuation (n : ℂ) ≤ 1 := fun n =>
    (V.valuation_le_one_iff _).2 (natCast_mem V n)
  by_contra hcon
  rw [not_or] at hcon
  have ha : V.valuation (a : ℂ) < 1 := lt_of_le_of_ne (hnat a) hcon.1
  have hb : V.valuation (b : ℂ) < 1 := lt_of_le_of_ne (hnat b) hcon.2
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 h
  have hC : (x : ℂ) * (a : ℂ) + (y : ℂ) * (b : ℂ) = 1 := by exact_mod_cast hxy
  have h1 : V.valuation ((x : ℂ) * (a : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint x)) ha
  have h2 : V.valuation ((y : ℂ) * (b : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint y)) hb
  have h3 := V.valuation.map_add_lt h1 h2
  rw [hC, map_one] at h3
  exact lt_irrefl _ h3

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingRootOfUnityLiftReduce
section
open NumberField

namespace GlobalTheory

theorem isPrimitiveRoot_map_of_isUnit_order' {o K : Type} [CommRing o] [IsDomain o] [CommRing K] [IsDomain K]
    (φ : o →+* K) {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) :
    IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem valuationRing_rootOfUnity_lift_reduce : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω]
    [Algebra U Ω] [IsFractionRing U Ω] [Field k] (h : U →+* k) (n : ℕ), IsUnit (n : U) → ∀ ζ : Ωˣ, ζ ^ n = 1 →
    ∃! z : Uˣ, algebraMap U Ω z = ζ ∧ (IsPrimitiveRoot ζ n → IsPrimitiveRoot (Units.map (h : U →* k) z) n) := by
  intro U Ω k _ _ _ _ _ _ _ h n hn ζ hζ
  have hinj : Function.Injective (algebraMap U Ω) := IsFractionRing.injective U Ω
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hn
    · exact h0

  have unitOf : ∀ a : U, (algebraMap U Ω a) ^ n = 1 → IsUnit a := by
    intro a ha
    have : a ^ n = 1 := hinj (by rw [map_pow, ha, map_one])
    exact IsUnit.of_mul_eq_one (a ^ (n - 1)) (by rw [← pow_succ', Nat.sub_add_cancel hn0, this])
  have hex : ∃ z : Uˣ, algebraMap U Ω z = ζ := by
    rcases (ValuationRing.iff_isInteger_or_isInteger U Ω).1 inferInstance (ζ : Ω) with ⟨a, ha⟩ | ⟨b, hb⟩
    · have hu := unitOf a (by rw [ha, ← Units.val_pow_eq_pow_val, hζ, Units.val_one])
      exact ⟨hu.unit, by simpa using ha⟩
    · have hb' : (algebraMap U Ω b) ^ n = 1 := by
        rw [hb, ← Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_pow, hζ, inv_one, Units.val_one]
      have hu := unitOf b hb'
      refine ⟨hu.unit⁻¹, ?_⟩
      have : algebraMap U Ω (hu.unit : U) = (ζ : Ω)⁻¹ := by simpa using hb
      have key : algebraMap U Ω (hu.unit : U) * algebraMap U Ω ((hu.unit⁻¹ : Uˣ) : U) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [this, inv_mul_eq_one₀ ζ.ne_zero] at key
      exact key.symm
  obtain ⟨z, hz⟩ := hex
  refine ⟨z, ⟨hz, fun hp => ?_⟩, fun w ⟨hw, _⟩ => Units.ext (hinj (by rw [hw, hz]))⟩
  have hpz : IsPrimitiveRoot (z : U) n := by
    rw [← IsPrimitiveRoot.map_iff_of_injective hinj, hz]
    exact IsPrimitiveRoot.coe_units_iff.2 hp
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact isPrimitiveRoot_map_of_isUnit_order' h hn0 hpz hn

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationUniformizerIntegralClosureEqExpNegRamif
section
open IsDedekindDomain

namespace GlobalTheory

theorem valuation_uniformizer_integralClosure (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra R L] [IsScalarTower R K L] [IsDedekindDomain (integralClosure R L)]
    [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L))
    (π : R) (hπ : Irreducible π) :
    P.valuation L (algebraMap K L (algebraMap R K π)) = WithZero.exp (-(P.asIdeal.ramificationIdx R : ℤ)) := by
  let v : HeightOneSpectrum R := IsDiscreteValuationRing.maximalIdeal R
  have hinj : Function.Injective (algebraMap R (integralClosure R L)) := by
    have h : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    rw [IsScalarTower.algebraMap_eq R (integralClosure R L) L] at h
    rw [RingHom.coe_comp] at h
    exact Function.Injective.of_comp h
  have : FaithfulSMul R (integralClosure R L) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.IsTorsionFree R (integralClosure R L) := inferInstance
  have hlo : P.asIdeal.LiesOver v.asIdeal := by
    constructor
    have hP := P.isPrime
    have hne : P.asIdeal.under R ≠ ⊥ := Ideal.under_ne_bot R P.ne_bot
    exact ((IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne))).symm
  have h1 := HeightOneSpectrum.valuation_liesOver L v P (algebraMap R K π)
  rw [← h1, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton v hπ.ne_zero hπ.maximalIdeal_eq, ← WithZero.exp_nsmul]
  congr 1
  simp

end GlobalTheory
end

