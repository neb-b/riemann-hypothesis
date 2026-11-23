module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldHermitianFormBaseChangeRealEqSum
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

private noncomputable def R {K : Type} [Fintype K] (c u v : K → ℂ) : ℝ :=
  ∑ k, 2 * (c k * u k * (starRingEnd ℂ) (v k)).re

private theorem R_add_l {K : Type} [Fintype K] (c u u' v : K → ℂ) :
    R c (u + u') v = R c u v + R c u' v := by
  unfold R
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, mul_add, add_mul, Complex.add_re]

private theorem R_add_r {K : Type} [Fintype K] (c u v v' : K → ℂ) :
    R c u (v + v') = R c u v + R c u v' := by
  unfold R
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, map_add (f := _), mul_add, add_mul, Complex.add_re]

private theorem R_smul_l {K : Type} [Fintype K] (c u v : K → ℂ) (r : ℝ) :
    R c (r • u) v = r * R c u v := by
  simp only [R, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : c k * (r • u) k * (starRingEnd ℂ) (v k) = (r : ℂ) * (c k * u k * (starRingEnd ℂ) (v k)) := by
    simp only [Pi.smul_apply, Complex.real_smul]; ring
  rw [h, Complex.re_ofReal_mul]; ring

private theorem R_smul_r {K : Type} [Fintype K] (c u v : K → ℂ) (r : ℝ) :
    R c u (r • v) = r * R c u v := by
  simp only [R, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : c k * u k * (starRingEnd ℂ) ((r • v) k) = (r : ℂ) * (c k * u k * (starRingEnd ℂ) (v k)) := by
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring
  rw [h, Complex.re_ofReal_mul]; ring

private theorem core0 (hT : TraceType) {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (a b : Fin n → 𝓞 E) :
    ((A.EF n a b : ℤ) : ℝ) = ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
      (starRingEnd ℂ) (k.1.1 (b k.2 : E))).re := by
  rw [Arith.EF_apply, ← Rat.cast_intCast, Arith.trd_spec, (hT E A).1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum, ← Complex.re_sum]
  congr 2
  push_cast
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Arith.bar_eq, Finset.mul_sum, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem e1 {E : Type} [Field E] [NumberField E] {n : ℕ} (q : ℚ) (a : Fin n → 𝓞 E) :
    (1 : ℝ) ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] a) = (q : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] a)) := by
  rw [show (q ⊗ₜ[ℤ] a : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) = q • ((1 : ℚ) ⊗ₜ[ℤ] a) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Rat.smul_one_eq_cast]

private theorem core1 (hT : TraceType) {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] (Fin n → E)) (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (w w' : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    (((A.EF n).baseChange ℚ w w' : ℚ) : ℝ) =
      R (fun k : Phi A × Fin n => k.1.1 A.δ * k.1.1 (A.hd n k.2 : E))
        (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ w)) (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ w')) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [R]
  | add a b ha hb =>
    rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), LinearMap.add_apply, Rat.cast_add, ha, hb, R_add_l]
  | tmul q a =>
    induction w' using TensorProduct.induction_on with
    | zero => simp [R]
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), Rat.cast_add, ha, hb, R_add_r]
    | tmul t b =>
      rw [LinearMap.BilinForm.baseChange_tmul, e1 q a, e1 t b, map_smul, map_smul, R_smul_l, R_smul_r]
      have h : R (fun k : Phi A × Fin n => k.1.1 A.δ * k.1.1 (A.hd n k.2 : E))
          (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ ((1 : ℚ) ⊗ₜ a)))
          (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ ((1 : ℚ) ⊗ₜ b))) = ((A.EF n a b : ℤ) : ℝ) := by
        rw [core0 hT A n a b]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Th_tmul, one_smul, hβ]
      rw [h]
      simp [Rat.smul_def, zsmul_eq_mul]
      ring

theorem UpperTheory.cmField_hermitianForm_baseChange_real_eq_sum :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] (Fin n → E)), (∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) → ∀ x y : ℝ ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)), ((A.EF n).baseChange ℚ).baseChange ℝ x y = ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Th (fun τ : Phi A => τ.1) β x k * (starRingEnd ℂ) (Th (fun τ : Phi A => τ.1) β y k)).re := by
  intro hT E _ _ _ A n β hβ x y
  change _ = R (fun k : Phi A × Fin n => k.1.1 A.δ * k.1.1 (A.hd n k.2 : E))
    (Th (fun τ : Phi A => τ.1) β x) (Th (fun τ : Phi A => τ.1) β y)
  induction x using TensorProduct.induction_on with
  | zero => simp [R]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, ha, hb, R_add_l]
  | tmul r w =>
    induction y using TensorProduct.induction_on with
    | zero => simp [R]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, R_add_r]
    | tmul s w' =>
      have e : ∀ (r : ℝ) (w : ℚ ⊗[ℤ] (Fin n → 𝓞 E)), r ⊗ₜ[ℚ] w = r • ((1 : ℝ) ⊗ₜ[ℚ] w) := by
        intro r w
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.BilinForm.baseChange_tmul, e r w, e s w', map_smul, map_smul, R_smul_l, R_smul_r, ← core1 hT A n β hβ w w',
        Rat.smul_def]
      simp only [mul_comm, mul_left_comm, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldRealTensorBijectiveCmType
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

private theorem func_repr {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℂ) →ₗ[ℝ] ℝ) :
    ∃ a : ι → ℂ, ∀ z, f z = ∑ τ, (a τ * z τ).re := by
  refine ⟨fun τ => (f (Pi.single τ 1) : ℂ) - Complex.I * (f (Pi.single τ Complex.I) : ℂ), fun z => ?_⟩
  have h1 : z = ∑ τ, ((z τ).re • (Pi.single τ 1 : ι → ℂ) + (z τ).im • (Pi.single τ Complex.I : ι → ℂ)) := by
    ext k
    have hk : ∀ τ, ((z τ).re • (Pi.single τ 1 : ι → ℂ) + (z τ).im • (Pi.single τ Complex.I : ι → ℂ)) k =
        if k = τ then z k else 0 := by
      intro τ
      by_cases h : k = τ
      · subst h
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, if_true]
        apply Complex.ext <;> simp
      · simp [Pi.single_apply, h]
    rw [Finset.sum_apply]
    simp only [hk]
    simp
  conv_lhs => rw [h1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_add (f := _), map_smul, map_smul]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

private theorem family_inj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E)
    (him : (A.τ₀ (A.ω : E)).im ≠ 0) :
    Function.Injective (Sum.elim (fun τ : Phi A => (τ.1 : E →* ℂ))
      (fun τ : Phi A => ((ComplexEmbedding.conjugate τ.1 : E →+* ℂ) : E →* ℂ))) := by
  have hval : ∀ (τ τ' : Phi A), (∀ x, τ.1 x = (starRingEnd ℂ) (τ'.1 x)) → False := by
    intro τ τ' h
    have h1 := h (A.ω : E)
    rw [τ.2, τ'.2] at h1
    exact him (Complex.conj_eq_iff_im.1 h1.symm)
  rintro (τ | τ) (τ' | τ') h
  · congr 1
    apply Subtype.ext
    ext x
    exact congrArg (fun g : E →* ℂ => g x) h
  · exfalso
    refine hval τ τ' fun x => ?_
    exact congrArg (fun g : E →* ℂ => g x) h
  · exfalso
    refine hval τ' τ fun x => ?_
    exact (congrArg (fun g : E →* ℂ => g x) h).symm
  · congr 1
    apply Subtype.ext
    ext x
    have h1 : (starRingEnd ℂ) (τ.1 x) = (starRingEnd ℂ) (τ'.1 x) := congrArg (fun g : E →* ℂ => g x) h
    exact (starRingEnd ℂ).injective h1

theorem UpperTheory.cmField_real_tensor_bijective_cmType :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E), Function.Bijective (fun (z : ℝ ⊗[ℚ] E) (τ : Phi A) => ev1 τ.1 z) := by
  intro hT E _ _ _ A
  classical
  obtain ⟨-, -, h3, him⟩ := hT E A
  haveI : Fintype (Phi A) := Fintype.ofFinite _
  let L : ℝ ⊗[ℚ] E →ₗ[ℝ] (Phi A → ℂ) := LinearMap.pi (fun τ => (ev1 τ.1).toLinearMap)
  have hL : ∀ z τ, L z τ = ev1 τ.1 z := fun _ _ => rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := (LinearMap.range L).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
    obtain ⟨a, ha⟩ := func_repr f
    have hzero : ∀ x : E, ∑ τ : Phi A, (a τ * τ.1 x).re = 0 := by
      intro x
      have h1 : f (L ((1 : ℝ) ⊗ₜ x)) = 0 := LinearMap.mem_ker.1 (hf ⟨_, rfl⟩)
      rw [ha] at h1
      simpa [hL, realTensorEvalAlgHom_tmul] using h1
    have hli := (linearIndependent_monoidHom E ℂ).comp _ (family_inj A him)
    have hc := Fintype.linearIndependent_iff.1 hli
      (Sum.elim a (fun τ => (starRingEnd ℂ) (a τ))) (by
        ext x
        rw [Finset.sum_apply, Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Function.comp, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have h2 : ∀ τ : Phi A, a τ * τ.1 x + (starRingEnd ℂ) (a τ) * (starRingEnd ℂ) (τ.1 x) =
            ((2 * (a τ * τ.1 x).re : ℝ) : ℂ) := by
          intro τ
          rw [← map_mul, Complex.add_conj]
        have h3 : ∑ τ : Phi A, (a τ * τ.1 x + (starRingEnd ℂ) (a τ) * (starRingEnd ℂ) (τ.1 x)) = 0 := by
          simp only [h2]
          rw [← Complex.ofReal_sum, ← Finset.mul_sum, hzero]
          simp
        rw [← h3, Finset.sum_add_distrib]
        rfl)
    apply hf0
    refine LinearMap.ext fun z => ?_
    rw [ha]
    have h0 : ∀ τ, a τ = 0 := fun τ => hc (Sum.inl τ)
    simp [h0]
  have hcard : Fintype.card (Phi A) = Fintype.card (InfinitePlace E) :=
    Fintype.card_congr (Equiv.ofBijective (fun τ : Phi A => InfinitePlace.mk τ.1)
      ⟨fun τ τ' h => (h3 _).unique rfl h.symm, fun v => (h3 v).exists⟩)
  have hdim : Module.finrank ℝ (ℝ ⊗[ℚ] E) = Module.finrank ℝ (Phi A → ℂ) := by
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hcard, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      ← InfinitePlace.card_add_two_mul_card_eq_rank, IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩
end

