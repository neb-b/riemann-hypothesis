module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDomSt
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private noncomputable def UpperTheory.Gal.W2.Seed.pDomSt_dL {I : Type} (a : I → ℂ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) where
  toFun z k := a k * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' r z := by funext k; simp [mul_left_comm]

private theorem UpperTheory.Gal.W2.Seed.pDomSt_theta_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) {n : ℕ}
    (Θ : ℝ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℝ] (Phi A × Fin n → ℂ))
    (hΘ : ∀ (x : Fin n → 𝓞 E) τ i, Θ (1 ⊗ₜ x) (τ, i) = τ.1 (x i : E))
    (b : 𝓞 E) (M : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] ℝ ⊗[ℤ] (Fin n → 𝓞 E))
    (hM : ∀ x : Fin n → 𝓞 E, M (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) (x : ℝ ⊗[ℤ] (Fin n → 𝓞 E)) (k : Phi A × Fin n) :
    Θ (M x) k = k.1.1 (b : E) * Θ x k := by
  obtain ⟨τ, i⟩ := k
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    have h : r ⊗ₜ[ℤ] y = r • ((1 : ℝ) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, LinearMap.map_smul, hM, LinearEquiv.map_smul, LinearEquiv.map_smul, Pi.smul_apply, Pi.smul_apply,
      hΘ, hΘ, Complex.real_smul, Complex.real_smul]
    simp [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb, mul_add]

private theorem UpperTheory.Gal.W2.Seed.pDomSt_term (D H z : ℂ) (e : ℝ) (hD : D.re = 0) (hH : H.im = 0) :
    (D * H * ((e : ℂ) * Complex.I * z) * (starRingEnd ℂ) z).re = -D.im * H.re * e * Complex.normSq z := by
  have hD' : D = (D.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hD]
  have hH' : H = (H.re : ℂ) := by
    apply Complex.ext <;> simp [hH]
  have h1 : D * H * ((e : ℂ) * Complex.I * z) * (starRingEnd ℂ) z
      = D * H * e * Complex.I * (z * (starRingEnd ℂ) z) := by ring
  rw [h1, Complex.mul_conj, hD', hH']
  have h2 : (D.im : ℂ) * Complex.I * (H.re : ℂ) * (e : ℂ) * Complex.I * (Complex.normSq z : ℂ)
      = ((-D.im * H.re * e * Complex.normSq z : ℝ) : ℂ) := by
    push_cast
    linear_combination ((D.im : ℂ) * H.re * e * Complex.normSq z) * Complex.I_sq
  rw [h2, Complex.ofReal_re]
  simp

private theorem UpperTheory.Gal.W2.Seed.pDomSt_sum {I : Type} [Fintype I] [DecidableEq I] (k0 : I) (y : I → ℝ) :
    ∑ k, (if k = k0 then (1 : ℝ) else -1) * y k = 2 * y k0 - ∑ k, y k := by
  have h : ∀ k, (if k = k0 then (1 : ℝ) else -1) * y k = 2 * (if k = k0 then y k else 0) - y k := by
    intro k
    split_ifs <;> ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem UpperTheory.Gal.W2.Seed.pDomSt :
    TraceType → RealIso → FormCoord → HdSign → DiagTrace → DomSt := by
  intro hT hR hF hS hD E _ _ _ A n hn
  classical
  obtain ⟨Θ, hΘ⟩ := hR E A n
  obtain ⟨-, hsum, -, him⟩ := hT E A
  let k0 : Phi A × Fin n := (⟨A.τ₀, rfl⟩, ⟨0, hn⟩)
  have hk0 : ∀ k : Phi A × Fin n,
      (InfinitePlace.mk k.1.1 = InfinitePlace.mk A.τ₀ ∧ (k.2 : ℕ) = 0) ↔ k = k0 := by
    rintro ⟨⟨τ, hτ⟩, i⟩
    constructor
    · rintro ⟨h1, h2⟩
      rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
      · exact Prod.ext (Subtype.ext h) (Fin.ext h2)
      · exfalso
        apply him
        have h3 : A.τ₀ (A.ω : E) = (starRingEnd ℂ) (τ (A.ω : E)) := by
          rw [← h, ComplexEmbedding.conjugate_coe_eq]
        rw [hτ] at h3
        exact Complex.conj_eq_iff_im.mp h3.symm
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
  let ε : Phi A × Fin n → ℝ := fun k => if k = k0 then 1 else -1
  let a : Phi A × Fin n → ℂ := fun k => (ε k : ℂ) * Complex.I
  have ha2 : ∀ k, a k * a k = -1 := by
    intro k
    have h' : (ε k : ℂ) * (ε k) = 1 := by
      simp only [ε]
      split_ifs <;> norm_num
    simp only [a]
    linear_combination Complex.I ^ 2 * h' + Complex.I_sq
  have hca : ∀ k, (starRingEnd ℂ) (a k) = -a k := by
    intro k
    simp only [a, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  let J := Θ.symm.toLinearMap ∘ₗ pDomSt_dL a ∘ₗ Θ.toLinearMap
  have hJ : ∀ x k, Θ (J x) k = a k * Θ x k := by
    intro x k
    simp [J, pDomSt_dL]
  have hpos : ∀ k : Phi A × Fin n, 0 < -(k.1.1 A.δ).im * ((k.1.1 (A.hd n k.2 : E)).re * ε k) := by
    intro k
    have h1 := A.δ_sign k.1.1 k.1.2
    obtain ⟨-, -, hp, hm⟩ := hS E A n k.1.1 k.2
    have h2 : 0 < (k.1.1 (A.hd n k.2 : E)).re * ε k := by
      by_cases hk : k = k0
      · have := hp ((hk0 k).mpr hk)
        rw [show ε k = 1 from if_pos hk, mul_one]
        exact this
      · have := hm (fun h => hk ((hk0 k).mp h))
        rw [show ε k = -1 from if_neg hk, mul_neg_one]
        linarith
    exact mul_pos (by linarith) h2
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Θ.injective
    funext k
    rw [hJ, hJ, map_neg, Pi.neg_apply, ← mul_assoc, ha2]
    ring
  · intro x y
    rw [hF E A n Θ hΘ, hF E A n Θ hΘ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hJ, hJ, map_mul, hca]
    congr 2
    linear_combination (-(k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ x k * (starRingEnd ℂ) (Θ y k))) * ha2 k
  · intro x hx
    rw [hF E A n Θ hΘ]
    have hx' : Θ x ≠ 0 := by simpa using hx
    obtain ⟨k1, hk1⟩ : ∃ k, Θ x k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx' (funext h)
    have hterm : ∀ k : Phi A × Fin n,
        2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ (J x) k * (starRingEnd ℂ) (Θ x k)).re
          = 2 * ((-(k.1.1 A.δ).im * ((k.1.1 (A.hd n k.2 : E)).re * ε k)) * Complex.normSq (Θ x k)) := by
      intro k
      obtain ⟨hH, hD0, -, -⟩ := hS E A n k.1.1 k.2
      rw [hJ]
      simp only [a]
      rw [pDomSt_term _ _ _ _ hD0 hH]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (by norm_num) (mul_nonneg (hpos k).le (Complex.normSq_nonneg _))
    · exact ⟨k1, Finset.mem_univ _, mul_pos (by norm_num) (mul_pos (hpos k1) (Complex.normSq_pos.mpr hk1))⟩
  · intro b M hM
    apply LinearMap.ext
    intro x
    apply Θ.injective
    funext k
    simp only [LinearMap.comp_apply]
    rw [hJ, pDomSt_theta_mul A Θ hΘ b M hM, pDomSt_theta_mul A Θ hΘ b M hM, hJ]
    ring
  · intro c M hM
    dsimp only
    have htrM : LinearMap.trace ℝ _ M = 2 * (∑ k : Phi A × Fin n, k.1.1 (c : E)).re := by
      rw [← LinearMap.trace_conj' M Θ]
      refine hD _ (fun k : Phi A × Fin n => k.1.1 (c : E)) _ (fun z k => ?_)
      rw [LinearEquiv.conj_apply_apply, pDomSt_theta_mul A Θ hΘ c M hM, LinearEquiv.apply_symm_apply]
    have htrJM : LinearMap.trace ℝ _ (J ∘ₗ M) = 2 * (∑ k : Phi A × Fin n, a k * k.1.1 (c : E)).re := by
      rw [← LinearMap.trace_conj' (J ∘ₗ M) Θ]
      refine hD _ (fun k : Phi A × Fin n => a k * k.1.1 (c : E)) _ (fun z k => ?_)
      rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, hJ, pDomSt_theta_mul A Θ hΘ c M hM,
        LinearEquiv.apply_symm_apply]
      ring
    have hre : (∑ k : Phi A × Fin n, a k * k.1.1 (c : E)).re = -∑ k, ε k * (k.1.1 (c : E)).im := by
      rw [Complex.re_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [a, Complex.mul_re]
    rw [hsum (fun τ => (n : ℂ) * τ (c : E))]
    constructor
    · rw [htrM]
      simp [ComplexEmbedding.conjugate_coe_eq, Fintype.sum_prod_type, Complex.re_sum, Finset.mul_sum]
    · rw [htrJM, hre, pDomSt_sum k0 (fun k => (k.1.1 (c : E)).im)]
      simp [k0, ComplexEmbedding.conjugate_coe_eq, Fintype.sum_prod_type, Complex.im_sum, Finset.mul_sum]
      ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormOKSt
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem trace_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

private theorem hd_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    A.bar (A.hd n i) = A.hd n i := by
  unfold Arith.hd Arith.dg
  split_ifs <;> simp [A.c_real]

private theorem hd_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.hd n i : 𝓞 E) : E) ≠ 0 := by
  have := A.c_ne
  unfold Arith.hd Arith.dg
  split_ifs <;> simp [this]

private theorem delta_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) : A.δ ≠ 0 := by
  intro h
  have := A.δ_sign A.τ₀ rfl
  simp [h] at this

private theorem alternatingMap_sub_base_eq_alternating_sum_removeNth {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (x : Fin n → 𝓞 E) : A.EF n x x = 0 := by
  rw [Arith.EF_apply]
  set s : 𝓞 E := ∑ i, A.hd n i * x i * A.bar (x i) with hs
  have hbs : A.bar s = s := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, hd_bar, A.bar_bar]
    ring
  have hc : IsCMField.complexConj E ((s : 𝓞 E) : E) = (s : E) := by
    rw [← A.bar_eq, hbs]
  have h1 : Algebra.trace ℚ E (A.δ * (s : E)) = - Algebra.trace ℚ E (A.δ * (s : E)) := by
    conv_lhs => rw [← trace_cj, map_mul, A.δ_im, hc, neg_mul, map_neg]
  have h2 : ((A.trd s : ℤ) : ℚ) = 0 := by
    rw [A.trd_spec]
    linarith
  exact_mod_cast h2

private theorem laurent_adjoin_eq_of_image_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    Function.Injective (A.EF n) := by
  refine (injective_iff_map_eq_zero (A.EF n)).2 fun x hx => ?_
  funext i
  by_contra hne
  have hxi : ((x i : 𝓞 E) : E) ≠ 0 := by
    intro h
    exact hne (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hw : A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (delta_ne A) (hd_ne A n i)) hxi
  have hint : ∀ b : 𝓞 E, Algebra.trace ℚ E (A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) * (b : E)) = 0 := by
    intro b
    have h0 : A.EF n x (Pi.single i (A.bar b)) = 0 := by rw [hx]; rfl
    rw [Arith.EF_apply] at h0
    have h1 : (∑ j, A.hd n j * x j * A.bar ((Pi.single i (A.bar b) : Fin n → 𝓞 E) j)) =
        A.hd n i * x i * b := by
      rw [Finset.sum_eq_single i]
      · simp [A.bar_bar]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [h1] at h0
    have h2 := A.trd_spec (A.hd n i * x i * b)
    rw [h0] at h2
    simp only [Int.cast_zero] at h2
    rw [h2]
    congr 1
    push_cast
    ring
  obtain ⟨b, hb⟩ : ∃ b : E, Algebra.trace ℚ E (A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) * b) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hw ((traceForm_nondegenerate ℚ E).1 _ fun b => by simpa [Algebra.traceForm_apply] using hall b)
  obtain ⟨m, hm, hy⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic b))
  obtain ⟨c, hc⟩ : ∃ c : 𝓞 E, (c : E) = (m : ℚ) • b := by
    refine ⟨⟨m • b, hy⟩, ?_⟩
    show m • b = (m : ℚ) • b
    rw [zsmul_eq_mul, Algebra.smul_def]
    simp
  have h3 := hint c
  rw [hc, mul_smul_comm, map_smul, smul_eq_mul] at h3
  rcases mul_eq_zero.1 h3 with h5 | h5
  · exact hm (by exact_mod_cast h5)
  · exact hb h5

theorem UpperTheory.Gal.W2.Seed.pFormOKSt :
    FormOKSt := by
  intro E _ _ _ A n
  refine ⟨alternatingMap_sub_base_eq_alternating_sum_removeNth A n, laurent_adjoin_eq_of_image_eq A n, fun b x y => ?_⟩
  rw [Arith.EF_apply, Arith.EF_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, A.bar_bar]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormPerfSt
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pFormPerfSt :
    FormPerfSt := by
  intro E _ _ _ A n q hP
  obtain ⟨e, he, hx, c', hc⟩ := hP
  refine ⟨e ^ 3, Nat.Coprime.pow_left 3 he, fun f => ?_⟩
  choose x hxf using fun i : Fin n =>
    hx (((f.toAddMonoidHom.comp (AddMonoidHom.single _ i)).comp A.bar.toAddMonoidHom).toIntLinearMap)
  refine ⟨fun i => -((if (i : ℕ) = 0 then c' * (e : 𝓞 E) else c' ^ 2) * x i), ?_⟩
  refine LinearMap.ext fun y => ?_
  rw [Arith.EF_apply]
  have key : ∀ i, A.hd n i * -((if (i : ℕ) = 0 then c' * (e : 𝓞 E) else c' ^ 2) * x i) * A.bar (y i)
      = ((e ^ 2 : ℕ) : 𝓞 E) * (x i * A.bar (y i)) := by
    intro i
    simp only [Arith.hd, Arith.dg]
    push_cast
    split_ifs
    · linear_combination ((e : 𝓞 E) * x i * A.bar (y i)) * hc
    · linear_combination (c' * A.c + (e : 𝓞 E)) * x i * A.bar (y i) * hc
  have hs : ∀ i, A.trd (x i * A.bar (y i)) = (e : ℤ) * f (Pi.single i (y i)) := by
    intro i
    rw [hxf i]
    simp [Arith.bar_bar]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, ← nsmul_eq_mul, map_nsmul, map_sum]
  simp_rw [hs]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.mul_sum, ← map_sum, Finset.univ_sum_single]
  simp only [LinearMap.smul_apply, nsmul_eq_mul]
  push_cast
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHdSign
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pHdSign :
    HdSign := by
  intro E _ _ _ A n τ i
  have hcim : ∀ σ : E →+* ℂ, (σ (A.c : E)).im = 0 := by
    intro σ
    have h1 : σ ((A.bar A.c : 𝓞 E) : E) = (starRingEnd ℂ) (σ (A.c : E)) := by
      rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]
    rw [A.c_real] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm
  have hre : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ → (τ (A.c : E)).re < 0 := by
    intro h
    rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
    · rw [h']
      exact A.c_neg
    · have h2 := A.c_neg
      rw [← h', NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
      simpa using h2
  have hδ : (τ A.δ).re = 0 := by
    have h1 : τ ((IsCMField.complexConj E) A.δ) = (starRingEnd ℂ) (τ A.δ) :=
      IsCMField.complexEmbedding_complexConj E τ A.δ
    rw [A.δ_im, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hc := hcim τ
  refine ⟨?_, hδ, ?_, ?_⟩
  · simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [Complex.mul_im, hc]
  · rintro ⟨h, hi0⟩
    have hr := hre h
    simp only [Arith.hd, Arith.dg, if_pos hi0]
    simp
    linarith
  · intro hn
    by_cases hp : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀
    · have hi : (i : ℕ) ≠ 0 := fun hi0 => hn ⟨hp, hi0⟩
      have hr := hre hp
      simp only [Arith.hd, Arith.dg, if_neg hi]
      simp [Complex.mul_re, hc]
      nlinarith
    · have hr : 0 < (τ (A.c : E)).re := A.c_pos τ hp
      simp only [Arith.hd, Arith.dg]
      split_ifs
      · simp
        linarith
      · simp [Complex.mul_re, hc]
        nlinarith
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma crtPrimes (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (f : ℕ → ℤ) :
    ∃ R : ℤ, ∀ q ∈ T, (q : ℤ) ∣ R - f q := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a T ha ih =>
    obtain ⟨R₀, hR₀⟩ := ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    have hap : a.Prime := hT a (Finset.mem_insert_self a T)
    have hcop : IsCoprime (a : ℤ) (∏ q ∈ T, (q : ℤ)) := by
      refine IsCoprime.prod_right (fun q hq => ?_)
      have hqp : q.Prime := hT q (Finset.mem_insert_of_mem hq)
      have hne : a ≠ q := fun h => ha (h ▸ hq)
      exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hap hqp).mpr hne)
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨R₀ + v * (∏ q ∈ T, (q : ℤ)) * (f a - R₀), fun q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · refine ⟨-u * (f q - R₀), ?_⟩
      linear_combination (f q - R₀) * huv
    · have h1 : (q : ℤ) ∣ ∏ q ∈ T, (q : ℤ) := Finset.dvd_prod_of_mem (fun q : ℕ => (q : ℤ)) hq'
      obtain ⟨k, hk⟩ := h1
      obtain ⟨l, hl⟩ := hR₀ q hq'
      refine ⟨l + v * k * (f a - R₀), ?_⟩
      rw [hk]
      linear_combination hl

private lemma primeDvdOfMem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (M : ℕ) (hM : 0 < M)
    (h : (M : A) ∈ P) : ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ (q : A) ∈ P := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases h1 : M = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h)) hP.ne_top
    · have hq : M.minFac.Prime := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd M
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hm; omega
        · exact h0
      have hlt : m < M := by
        have := hq.two_le
        rw [hm]
        nlinarith
      have hmem : ((M.minFac : A)) * (m : A) ∈ P := by
        have : (M : A) = ((M.minFac : A)) * (m : A) := by
          conv_lhs => rw [hm]
          push_cast
          rfl
        rwa [this] at h
      rcases hP.mem_or_mem hmem with h2 | h2
      · exact ⟨M.minFac, hq, Nat.minFac_dvd M, h2⟩
      · obtain ⟨q, hq', hqm, hqP⟩ := ih m hlt hm0 h2
        exact ⟨q, hq', hqm.trans ⟨M.minFac, by rw [mul_comm]; exact hm⟩, hqP⟩

private lemma localInv (q : ℕ) (hq : q.Prime) (tr nm r : ℤ) (hD : ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm)
    (hr : (q : ℤ) ∣ r ^ 2 - tr * r + nm) : ∃ s : ℤ, (q : ℤ) ∣ s * (tr - 2 * r) - 1 := by
  have hpr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hnd : ¬ (q : ℤ) ∣ tr - 2 * r := by
    intro h
    apply hD
    have h2 : (q : ℤ) ∣ (tr - 2 * r) ^ 2 - 4 * (r ^ 2 - tr * r + nm) :=
      dvd_sub (dvd_pow h two_ne_zero) (Dvd.dvd.mul_left hr 4)
    have h3 : (tr - 2 * r) ^ 2 - 4 * (r ^ 2 - tr * r + nm) = tr ^ 2 - 4 * nm := by ring
    rwa [h3] at h2
  have hco : IsCoprime (q : ℤ) (tr - 2 * r) := (Prime.coprime_iff_not_dvd hpr).mpr hnd
  obtain ⟨a, b, hab⟩ := hco
  refine ⟨b, -a, ?_⟩
  linear_combination hab

theorem UpperTheory.Gal.W2.Seed.pIdemEx :
    IdemEx := by
  intro E _ _ bar ω tr nm _ hsum hprod M hM hloc
  have hex : ∀ q : ℕ, q.Prime → q ∣ M → ∃ r s : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm ∧
      (q : ℤ) ∣ s * (tr - 2 * r) - 1 := by
    intro q hq hqM
    obtain ⟨hD, r, hr⟩ := hloc q hq hqM
    obtain ⟨s, hs⟩ := localInv q hq tr nm r hD hr
    exact ⟨r, s, hr, hs⟩
  choose! r s hr hs using hex
  have hT : ∀ q ∈ M.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  obtain ⟨R, hR⟩ := crtPrimes M.primeFactors hT r
  obtain ⟨S, hS⟩ := crtPrimes M.primeFactors hT s
  have hbar : bar ω = (tr : 𝓞 E) - ω := by rw [← hsum]; ring
  refine ⟨(S : 𝓞 E) * (ω - (R : 𝓞 E)), fun P hP hMP => ?_⟩
  obtain ⟨q, hq, hqM, hqP⟩ := primeDvdOfMem P hP.isPrime M hM hMP
  have hqf : q ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqM, hM.ne'⟩
  have castMem : ∀ z : ℤ, (q : ℤ) ∣ z → (z : 𝓞 E) ∈ P := by
    rintro z ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hqP
  obtain ⟨a, ha⟩ := hR q hqf
  obtain ⟨b, hb⟩ := hS q hqf
  obtain ⟨c, hc⟩ := hr q hq hqM
  obtain ⟨e, he⟩ := hs q hq hqM
  have h1 : (q : ℤ) ∣ S * (tr - 2 * R) - 1 := by
    refine ⟨b * (tr - 2 * R) + e - 2 * s q * a, ?_⟩
    linear_combination (tr - 2 * R) * hb + he - 2 * s q * ha
  have h2 : (q : ℤ) ∣ R ^ 2 - tr * R + nm := by
    refine ⟨a * (R + r q - tr) + c, ?_⟩
    linear_combination (R + r q - tr) * ha + hc
  have hbe : bar ((S : 𝓞 E) * (ω - (R : 𝓞 E))) = (S : 𝓞 E) * ((tr : 𝓞 E) - ω - (R : 𝓞 E)) := by
    rw [map_mul, map_sub, map_intCast, map_intCast, hbar]
  rw [hbe]
  constructor
  · have := castMem _ h1
    push_cast at this
    convert this using 1
    ring
  · have := Ideal.mul_mem_left P ((S : 𝓞 E) ^ 2) (castMem _ h2)
    push_cast at this
    convert this using 1
    have hp : ω * ((tr : 𝓞 E) - ω) = (nm : 𝓞 E) := by rw [← hbar]; exact hprod
    linear_combination (S : 𝓞 E) ^ 2 * hp
end

