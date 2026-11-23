module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairBaseOfLag
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.SelMain

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.CmpPair
section
noncomputable section
open Matrix

namespace PI.SqPair.LocCartanPairW

variable {R : Type*} [CommRing R] (σ : R ≃+* R)

theorem cmp_map_mulVec {ι : Type*} [Fintype ι] (h : Matrix ι ι R) (v : ι → R) :
    (fun i => σ ((h *ᵥ v) i)) = h.map σ *ᵥ (fun i => σ (v i)) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem cmp_gram_pull {ι : Type*} [Fintype ι] (A h : Matrix ι ι R) (v w : ι → R) :
    (fun i => σ ((h *ᵥ v) i)) ⬝ᵥ (A *ᵥ (h *ᵥ w)) =
      (fun i => σ (v i)) ⬝ᵥ (((h.map σ)ᵀ * A * h) *ᵥ w) := by
  rw [cmp_map_mulVec σ h v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec _ (h.map σ)ᵀ, Matrix.vecMul_transpose]

theorem cmp_gram_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι R) (a b : R) (v w : ι → R) :
    (fun i => σ ((a • v) i)) ⬝ᵥ (A *ᵥ (b • w)) = σ a * b * ((fun i => σ (v i)) ⬝ᵥ (A *ᵥ w)) := by
  have h1 : (fun i => σ ((a • v) i)) = σ a • fun i => σ (v i) := by
    funext i; simp [map_mul]
  rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : (fun i => σ a * σ (v i)) ⬝ᵥ (A *ᵥ w) = σ a * ((fun i => σ (v i)) ⬝ᵥ (A *ᵥ w)) := by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  have h3 : (σ a • fun i => σ (v i)) = fun i => σ a * σ (v i) := by
    funext i; simp
  rw [h3, h2]; ring

private lemma smulMulVec_lemma {ι : Type*} [Fintype ι] (a : R) (M : Matrix ι ι R) (v : ι → R) :
    (a • M) *ᵥ v = a • (M *ᵥ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem cmp_gram_pre [IsDomain R] {ι : Type*} [Fintype ι] (A A' h : Matrix ι ι R) (s : R)
    (hs : s ≠ 0) (hh : (h.map σ)ᵀ * A * h = s • A') (v w x y : ι → R) (c d t : R)
    (hv : h *ᵥ v = c • x) (hw : h *ᵥ w = d • y)
    (hxy : (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) * (σ c * d) = s * t) :
    (fun i => σ (v i)) ⬝ᵥ (A' *ᵥ w) = t := by
  have key : s • ((fun i => σ (v i)) ⬝ᵥ (A' *ᵥ w)) =
      (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) * (σ c * d) := by
    rw [← dotProduct_smul, ← smulMulVec_lemma, ← hh, ← cmp_gram_pull σ A h v w, hv, hw,
      cmp_gram_smul σ A c d x y]
    ring
  rw [hxy, smul_eq_mul] at key
  exact mul_left_cancel₀ hs key

theorem cmp_hyp [IsDomain R] {ι : Type*} [Fintype ι] (A A' h : Matrix ι ι R) (s : R) (hs : s ≠ 0)
    (hh : (h.map σ)ᵀ * A * h = s • A') (c₁ c₂ : R) (hc : σ c₁ * c₂ = s)
    (x₁ y₁ v₁ w₁ : ι → R) (hv : h *ᵥ v₁ = c₁ • x₁) (hw : h *ᵥ w₁ = c₂ • y₁)
    (hxx : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ x₁) = 0) (hyy : (fun i => σ (y₁ i)) ⬝ᵥ (A *ᵥ y₁) = 0)
    (hxy : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ y₁) = 1) :
    (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ v₁) = 0 ∧ (fun i => σ (w₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 0 ∧
      (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 1 := by
  refine ⟨cmp_gram_pre σ A A' h s hs hh v₁ v₁ x₁ x₁ c₁ c₁ 0 hv hv (by rw [hxx]; ring),
    cmp_gram_pre σ A A' h s hs hh w₁ w₁ y₁ y₁ c₂ c₂ 0 hw hw (by rw [hyy]; ring),
    cmp_gram_pre σ A A' h s hs hh v₁ w₁ x₁ y₁ c₁ c₂ 1 hv hw (by rw [hxy, hc]; ring)⟩

private lemma mapMul_lemma_2 {α β γ : Type*} [Fintype β] (X : Matrix α β R) (Y : Matrix β γ R) :
    (X * Y).map σ = X.map σ * Y.map σ := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum, map_mul]

theorem cmp_split [IsDomain R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A A' h : Matrix ι ι R) (s : R) (hh : (h.map σ)ᵀ * A * h = s • A')
    (c₁ c₂ : R) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (x y v₁ w₁ : ι → R)
    (hv : h *ᵥ v₁ = c₁ • x) (hw : h *ᵥ w₁ = c₂ • y)
    (u u' : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ A₁' : Matrix κ κ R)
    (huv : u * v = 1) (hvu : v * u = 1)
    (hu0 : ∀ i, u i (.inl 0) = x i) (hu1 : ∀ i, u i (.inl 1) = y i)
    (hu0' : ∀ i, u' i (.inl 0) = v₁ i) (hu1' : ∀ i, u' i (.inl 1) = w₁ i)
    (hG : (u.map σ)ᵀ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁)
    (hG' : (u'.map σ)ᵀ * A' * u' = fromBlocks !![0, 1; 1, 0] 0 0 A₁') :
    ∃ h₂ : Matrix κ κ R, v * h * u' = fromBlocks (diagonal ![c₁, c₂]) 0 0 h₂ ∧
      (h₂.map σ)ᵀ * A₁ * h₂ = s • A₁' := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = v * h * u' := ⟨_, rfl⟩
  have hcol : ∀ b : Fin 2, ∀ i, (h * u') i (.inl b) = ![c₁, c₂] b * u i (.inl b) := by
    rw [Fin.forall_fin_two]
    constructor
    · intro i
      have e := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
      simp [Matrix.mul_apply, hu0', hu0, e]
    · intro i
      have e := congrFun hw i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
      simp [Matrix.mul_apply, hu1', hu1, e]
  have hM1 : ∀ a (b : Fin 2), M a (.inl b) =
      ![c₁, c₂] b * (1 : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) a (.inl b) := by
    intro a b
    rw [hMdef, Matrix.mul_assoc, Matrix.mul_apply, ← hvu, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcol b i]
    ring
  have hUM : u * M = h * u' := by
    rw [hMdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]
  have hGram : (M.map σ)ᵀ * fromBlocks !![0, 1; 1, 0] 0 0 A₁ * M =
      s • fromBlocks !![0, 1; 1, 0] 0 0 A₁' := by
    rw [← hG, ← hG']
    calc (M.map σ)ᵀ * ((u.map σ)ᵀ * A * u) * M = ((u * M).map σ)ᵀ * A * (u * M) := by
          rw [mapMul_lemma_2 σ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = ((h * u').map σ)ᵀ * A * (h * u') := by rw [hUM]
      _ = (u'.map σ)ᵀ * ((h.map σ)ᵀ * A * h) * u' := by
          rw [mapMul_lemma_2 σ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = s • ((u'.map σ)ᵀ * A' * u') := by
          rw [hh, Matrix.mul_smul, Matrix.smul_mul]
  have hMb : M = fromBlocks (diagonal ![c₁, c₂]) M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rw [hM1 (.inl a) b]
      by_cases hab : a = b
      · subst hab
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      · simp [Matrix.one_apply, Matrix.diagonal_apply, hab]
    · simp [Matrix.toBlocks₁₂]
    · rw [hM1 (.inr a) b]
      simp [Matrix.one_apply]
    · simp [Matrix.toBlocks₂₂]
  rw [hMb] at hGram
  simp only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul, Matrix.map_zero, map_zero, Matrix.transpose_zero, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, smul_zero] at hGram
  obtain ⟨-, hQ, -, hS⟩ := Matrix.fromBlocks_inj.mp hGram
  have hc₁' : σ c₁ ≠ 0 := by simpa using hc₁
  have hc₂' : σ c₂ ≠ 0 := by simpa using hc₂
  have hB : M.toBlocks₁₂ = 0 := by
    ext a l
    have e0 := congrFun (congrFun hQ 0) l
    have e1 := congrFun (congrFun hQ 1) l
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hc₁', hc₂'] at e0 e1
    fin_cases a
    · simpa using e1
    · simpa using e0
  refine ⟨M.toBlocks₂₂, ?_, ?_⟩
  · rw [← hMdef]
    nth_rewrite 1 [hMb]
    rw [hB]
  · rw [hB] at hS
    simpa using hS

end PI.SqPair.LocCartanPairW

namespace PI.SqPair.LCP

open PI.SqPair.LocCartanPairW

theorem inert_isLocalRing {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R} {ϖ : R}
    (hI : Inert R₀ ϖ) : IsLocalRing R := by
  haveI := hI.dom
  have key : ∀ x : R, ¬ IsUnit x → ϖ ∣ x := by
    intro x hx
    by_cases h0 : x = 0
    · exact ⟨0, by rw [h0, mul_zero]⟩
    · obtain ⟨m, u, hu, rfl⟩ := hI.val x h0
      cases m with
      | zero => exact absurd (by simpa using hu) hx
      | succ k => exact ⟨ϖ ^ k * u, by ring⟩
  have back : ∀ x : R, ϖ ∣ x → ¬ IsUnit x := by
    rintro x ⟨c, rfl⟩ hu
    exact hI.pi_nonunit (isUnit_of_mul_isUnit_left hu)
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  exact back _ (dvd_add (key a ha) (key b hb))

theorem split_of (hS : SplitOff) : Split := by
  intro R _ _ R₀ ϖ hI κ _ _ A A' h k a hP hak x y v w hxx hyy hxy hv hw
  have := hI.dom
  have : IsLocalRing R := inert_isLocalRing hI
  obtain ⟨⟨hAh, -⟩, ⟨hAh', -⟩, hh⟩ := hP
  have hϖ : star ϖ = ϖ := (hI.fix ϖ).mp hI.pi_mem
  have hcard : Fintype.card κ + 2 = Fintype.card (Fin 2 ⊕ κ) := by
    simp [Fintype.card_sum, add_comm]
  obtain ⟨u, ui, A₁, huv, hvu, hu0, hu1, hG⟩ := hS R (Fin 2 ⊕ κ) κ hcard A hAh x y hxx hyy hxy
  have hs : ϖ ^ (2 * k) ≠ 0 := pow_ne_zero _ hI.pi_ne
  have hc : (starRingAut : R ≃+* R) (ϖ ^ (k - a)) * ϖ ^ (k + a) = ϖ ^ (2 * k) := by
    rw [map_pow, starRingAut_apply, hϖ, ← pow_add]
    congr 1
    omega
  obtain ⟨h1, h2, h3⟩ := cmp_hyp (starRingAut : R ≃+* R) A A' h _ hs hh (ϖ ^ (k - a)) (ϖ ^ (k + a))
    hc x y v w hv hw hxx hyy hxy
  obtain ⟨u', ui', A₁', huv', -, hu0', hu1', hG'⟩ :=
    hS R (Fin 2 ⊕ κ) κ hcard A' hAh' v w h1 h2 h3
  obtain ⟨h₂, hM, -⟩ := cmp_split (starRingAut : R ≃+* R) A A' h _ hh (ϖ ^ (k - a)) (ϖ ^ (k + a))
    (pow_ne_zero _ hI.pi_ne) (pow_ne_zero _ hI.pi_ne) x y v w hv hw u u' ui A₁ A₁' huv hvu hu0 hu1
    hu0' hu1' hG hG'
  refine ⟨u, u', A₁, A₁', h₂, ![ϖ ^ (k - a), ϖ ^ (k + a)], isUnit_det_of_right_inverse huv,
    isUnit_det_of_right_inverse huv', hG, hG', ?_⟩
  rw [← hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]

end PI.SqPair.LCP
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.FiniteAdeleIdempotentOfFMulSelf
section
noncomputable section
open Matrix

namespace PI.SqPair.LCP

section Alg
variable {R : Type} [CommRing R] [StarRing R]

def e0 : Matrix (Fin 2) (Fin 2) R := diagonal ![1, 0]

theorem finiteAdeleIdempotentOfF_mul_self : (e0 : Matrix (Fin 2) (Fin 2) R) * e0 = e0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e0]

theorem elementary_hyperbolic : (e0 : Matrix (Fin 2) (Fin 2) R)ᴴ * hyp = hyp - hyp * e0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e0, hyp, Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct, diagonal_apply]

theorem elementary_commutes_diagonal (d : Fin 2 → R) :
    (e0 : Matrix (Fin 2) (Fin 2) R) * diagonal d = diagonal d * e0 := by
  rw [e0, diagonal_mul_diagonal, diagonal_mul_diagonal]; congr 1; ext i; ring

theorem isUnit_ct {ι : Type} [Fintype ι] [DecidableEq ι] {u : Matrix ι ι R} (hu : IsUnit u.det) :
    IsUnit uᴴ := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_conjTranspose]; exact hu.star)

theorem cancel_conj {ι : Type} [Fintype ι] [DecidableEq ι] {u X Y : Matrix ι ι R}
    (hu : IsUnit u.det) (h : uᴴ * X * u = uᴴ * Y * u) : X = Y := by
  have hU : IsUnit u := (Matrix.isUnit_iff_isUnit_det _).2 hu
  have h2 : uᴴ * X = uᴴ * Y := hU.mul_right_cancel h
  exact (isUnit_ct hu).mul_left_cancel h2

theorem assemble {κ : Type} [Fintype κ] [DecidableEq κ]
    (A h u u' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (A₁ h₂ : Matrix κ κ R) (d : Fin 2 → R)
    (hu : IsUnit u.det) (hu' : IsUnit u'.det)
    (hA : uᴴ * A * u = fromBlocks hyp 0 0 A₁)
    (hh : h * u' = u * fromBlocks (diagonal d) 0 0 h₂)
    (e₂ f₂ : Matrix κ κ R) (he : e₂ * e₂ = e₂) (heA : e₂ᴴ * A₁ = A₁ * (1 - e₂))
    (hef : e₂ * h₂ = h₂ * f₂) : PConcl A h := by
  set E : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks e0 0 0 e₂ with hEdef
  set F : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks e0 0 0 f₂ with hFdef
  set D : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks (diagonal d) 0 0 h₂ with hDdef
  set B : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks hyp 0 0 A₁ with hBdef
  have hi : u⁻¹ * u = 1 := nonsing_inv_mul u hu
  have hi' : u'⁻¹ * u' = 1 := nonsing_inv_mul u' hu'
  have hE : E * E = E := by simp [hEdef, fromBlocks_multiply, finiteAdeleIdempotentOfF_mul_self, he]
  have hED : E * D = D * F := by simp [hEdef, hDdef, hFdef, fromBlocks_multiply, elementary_commutes_diagonal, hef]
  have heA' : e₂ᴴ * A₁ = A₁ - A₁ * e₂ := by rw [heA, Matrix.mul_sub, Matrix.mul_one]
  have hEB : Eᴴ * B = B - B * E := by
    rw [hEdef, hBdef, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    ext (i | i) (j | j) <;>
      simp [elementary_hyperbolic, heA', Matrix.sub_apply]
  refine ⟨u * E * u⁻¹, u' * F * u'⁻¹, ?_, ?_, ?_⟩
  · calc u * E * u⁻¹ * (u * E * u⁻¹) = u * (E * (u⁻¹ * u) * E) * u⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = u * E * u⁻¹ := by rw [hi, Matrix.mul_one, hE]
  · apply cancel_conj hu
    have hct : uᴴ * (u⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
    calc uᴴ * ((u * E * u⁻¹)ᴴ * A) * u = (uᴴ * (u⁻¹)ᴴ) * Eᴴ * (uᴴ * A * u) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Eᴴ * B := by rw [hct, Matrix.one_mul, hA]
      _ = B - B * E * (u⁻¹ * u) := by rw [hi, Matrix.mul_one, hEB]
      _ = uᴴ * (A * (1 - u * E * u⁻¹)) * u := by
          rw [← hA]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  · have hh' : h = u * D * u'⁻¹ := by
      rw [← hh, Matrix.mul_assoc, mul_nonsing_inv u' hu', Matrix.mul_one]
    rw [hh']
    calc u * E * u⁻¹ * (u * D * u'⁻¹) = u * (E * (u⁻¹ * u) * D) * u'⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = u * (D * (u'⁻¹ * u') * F) * u'⁻¹ := by rw [hi, hi', Matrix.mul_one, Matrix.mul_one, hED]
      _ = u * D * u'⁻¹ * (u' * F * u'⁻¹) := by simp only [Matrix.mul_assoc]

theorem blk_unimod {κ : Type} [Fintype κ] [DecidableEq κ]
    {A u : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R} {A₁ : Matrix κ κ R} (hu : IsUnit u.det)
    (hA : Unimod A) (h : uᴴ * A * u = fromBlocks hyp 0 0 A₁) : Unimod A₁ := by
  constructor
  · have h1 : (uᴴ * A * u)ᴴ = uᴴ * A * u := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA.1, Matrix.mul_assoc]
    rw [h, fromBlocks_conjTranspose] at h1
    exact (fromBlocks_inj.1 h1).2.2.2
  · have h1 : IsUnit (uᴴ * A * u).det := by
      rw [det_mul, det_mul, det_conjTranspose]; exact (hu.star.mul hA.2).mul hu
    rw [h, det_fromBlocks_zero₂₁] at h1
    exact isUnit_of_mul_isUnit_right h1

theorem blk_rel {κ : Type} [Fintype κ] [DecidableEq κ] (ϖ : R) (k : ℕ)
    (A A' h u u' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (A₁ A₁' h₂ : Matrix κ κ R) (d : Fin 2 → R)
    (hrel : hᴴ * A * h = (ϖ ^ (2 * k)) • A')
    (hA : uᴴ * A * u = fromBlocks hyp 0 0 A₁) (hA' : u'ᴴ * A' * u' = fromBlocks hyp 0 0 A₁')
    (hh : h * u' = u * fromBlocks (diagonal d) 0 0 h₂) :
    h₂ᴴ * A₁ * h₂ = (ϖ ^ (2 * k)) • A₁' := by
  have e1 : (h * u')ᴴ * A * (h * u') = (ϖ ^ (2 * k)) • fromBlocks hyp 0 0 A₁' := by
    rw [← hA', conjTranspose_mul]
    calc u'ᴴ * hᴴ * A * (h * u') = u'ᴴ * (hᴴ * A * h) * u' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hrel, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : (h * u')ᴴ * A * (h * u') = (fromBlocks (diagonal d) 0 0 h₂)ᴴ *
      (uᴴ * A * u) * fromBlocks (diagonal d) 0 0 h₂ := by
    rw [hh, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e2, hA, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_smul] at e1
  have := (fromBlocks_inj.1 e1).2.2.2
  simpa using this

theorem phyp_reindex {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (s : κ ≃ ι) {ϖ : R} {A A' h : Matrix ι ι R} {k : ℕ} (hP : PHyp ϖ A A' h k) :
    PHyp ϖ (A.submatrix s s) (A'.submatrix s s) (h.submatrix s s) k := by
  obtain ⟨⟨hA, hAd⟩, ⟨hA', hA'd⟩, hr⟩ := hP
  refine ⟨⟨by rw [conjTranspose_submatrix, hA], by rw [det_submatrix_equiv_self]; exact hAd⟩,
    ⟨by rw [conjTranspose_submatrix, hA'], by rw [det_submatrix_equiv_self]; exact hA'd⟩, ?_⟩
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hr, submatrix_smul]; rfl

theorem isBase_reindex {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (s : κ ≃ ι) {ϖ : R} {h : Matrix ι ι R} {k : ℕ} (hb : IsBase ϖ (h.submatrix s s) k) :
    IsBase ϖ h k := by
  obtain ⟨h₁, hu, he⟩ := hb
  refine ⟨h₁.submatrix s.symm s.symm, by rw [det_submatrix_equiv_self]; exact hu, ?_⟩
  have : h = (h.submatrix s s).submatrix s.symm s.symm := by simp
  rw [this, he, submatrix_smul]; rfl

theorem pconcl_reindex {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (s : κ ≃ ι) {A h : Matrix ι ι R} (hc : PConcl (A.submatrix s s) (h.submatrix s s)) :
    PConcl A h := by
  obtain ⟨e, f, he, heA, hef⟩ := hc
  have hA : A = (A.submatrix s s).submatrix s.symm s.symm := by simp
  have hh : h = (h.submatrix s s).submatrix s.symm s.symm := by simp
  refine ⟨e.submatrix s.symm s.symm, f.submatrix s.symm s.symm, ?_, ?_, ?_⟩
  · rw [submatrix_mul_equiv, he]
  · rw [hA, conjTranspose_submatrix, submatrix_mul_equiv, heA, ← submatrix_one_equiv s.symm]
    rw [show ((1 : Matrix κ κ R).submatrix s.symm s.symm) - e.submatrix s.symm s.symm
      = (1 - e).submatrix s.symm s.symm from rfl, submatrix_mul_equiv]
  · rw [hh, submatrix_mul_equiv, submatrix_mul_equiv, hef]

end Alg

theorem pgen_main (hB : BaseLag) (hS : Step) {R : Type} [CommRing R] [StarRing R]
    (R₀ : Subring R) [HenselianLocalRing R₀] [Finite (IsLocalRing.ResidueField R₀)] (ϖ : R)
    (hI : Inert R₀ ϖ) (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι = n → Even n → PGen ϖ ι := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hc hev A A' h k hP
  by_cases hb : IsBase ϖ h k
  · obtain ⟨h₁, hh₁, rfl⟩ := hb
    obtain ⟨e, he, heA⟩ := hB R R₀ ϖ hI ι (hc ▸ hev) A hP.1
    refine ⟨e, h₁⁻¹ * e * h₁, he, heA, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [← Matrix.mul_assoc, mul_nonsing_inv h₁ hh₁, Matrix.one_mul]
  · match n, ih, hc, hev with
    | 0, _, hc, _ =>
      have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
      exact absurd ⟨1, by simp, by ext i; exact isEmptyElim i⟩ hb
    | 1, _, _, hev => exact absurd hev (by decide)
    | m + 2, ih, hc, hev =>
      let s : Fin 2 ⊕ Fin m ≃ ι := Fintype.equivOfCardEq (by simp [hc]; omega)
      apply pconcl_reindex s
      have hP' := phyp_reindex s hP
      have hb' : ¬ IsBase ϖ (h.submatrix s s) k := fun hb' => hb (isBase_reindex s hb')
      obtain ⟨u, u', A₁, A₁', h₂, d, hu, hu', hA, hA', hh⟩ := hS R R₀ ϖ hI (Fin m) _ _ _ k hP' hb'
      have hU₁ := blk_unimod hu hP'.1 hA
      have hU₁' := blk_unimod hu' hP'.2.1 hA'
      have hr := blk_rel ϖ k _ _ _ u u' A₁ A₁' h₂ d hP'.2.2 hA hA' hh
      have hevm : Even m := by
        obtain ⟨r, hr⟩ := hev; exact ⟨r - 1, by omega⟩
      obtain ⟨e₂, f₂, he, heA, hef⟩ :=
        ih m (by omega) (Fin m) (Fintype.card_fin m) hevm A₁ A₁' h₂ k ⟨hU₁, hU₁', hr⟩
      exact assemble _ _ u u' A₁ h₂ d hu hu' hA hh e₂ f₂ he heA hef

theorem locCartanPair_of (h1 : Dichotomy) (hB : BaseLag) (hS : Step) :
    PI.SqPair.LocCartanPair := by
  intro R _ σ hσ R₀ hR₀ _ _ _ _ hθ ϖ hϖ N hN k h hh
  let _ : StarRing R :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add σ a b }
  have hR₀' : ∀ x, x ∈ R₀ ↔ star x = x := hR₀
  have hθ' : ∃ θ : R, IsUnit (θ - star θ) := hθ
  have hh' : hᴴ * 1 * h = ((ϖ : R) ^ (2 * k)) • (1 : Matrix (Fin N) (Fin N) R) := by
    rw [Matrix.mul_one]; exact hh
  rcases h1 R R₀ hR₀' hθ' ϖ hϖ with ⟨ε, hε, hεs⟩ | hI
  · refine ⟨ε • 1, ε • 1, ?_, ?_, ?_⟩
    · simp [smul_smul, hε]
    · change (ε • (1 : Matrix (Fin N) (Fin N) R))ᴴ = _
      rw [conjTranspose_smul, conjTranspose_one, hεs, sub_smul, one_smul]
    · simp
  · obtain ⟨e, f, he, heA, hef⟩ := pgen_main hB hS R₀ (ϖ : R) hI N (Fin N) (Fintype.card_fin N) hN
      1 1 h k ⟨⟨conjTranspose_one, by simp⟩, ⟨conjTranspose_one, by simp⟩, hh'⟩
    refine ⟨e, f, he, ?_, hef⟩
    rw [Matrix.mul_one, Matrix.one_mul] at heA
    exact heA

end PI.SqPair.LCP
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.HyperbolicPlane
section
noncomputable section
open Matrix

namespace PI.SqPair.LCP

theorem base_lagrangian : BaseLag := by
  intro R _ _ R₀ _ _ ϖ hI κ _ _ hev A hA
  obtain ⟨θ, hθ⟩ := hI.unr
  exact PI.LocCartanPair.lag_exists hI.fix hθ hev A hA.1 hA.2

theorem hyperbolic_plane : Plane := by
  intro R _ _ R₀ _ ϖ hI α β hα
  obtain ⟨θ, hθ⟩ := hI.unr
  have hσ : ∀ x : R, (starRingAut : R ≃+* R) ((starRingAut : R ≃+* R) x) = x := fun x => by
    simp [starRingAut_apply]
  have hR₀ : ∀ x, x ∈ R₀ ↔ (starRingAut : R ≃+* R) x = x := fun x => by
    rw [starRingAut_apply]
    exact hI.fix x
  have hθ' : IsUnit (θ - (starRingAut : R ≃+* R) θ) := by
    rw [starRingAut_apply]
    exact hθ
  obtain ⟨τ, hτ⟩ := tau_of_theta (starRingAut : R ≃+* R) hσ θ hθ'
  obtain ⟨w, hw1, hw2, hw3⟩ := plane_w (starRingAut : R ≃+* R) hσ R₀ hR₀ τ hτ α β hα
  refine ⟨w, hw1, ?_, hw3⟩
  have hct : wᴴ = (w.map (starRingAut : R ≃+* R))ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, starRingAut_apply]
  rw [hct, hw2]
  rfl

end PI.SqPair.LCP
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairSelection
section
noncomputable section
open Matrix

namespace PI.SqPair.LCP

theorem pair_selection : Select := by
  intro R _ _ R₀ ϖ hI ι _ _ A A' h k hP hNB
  have := hI.dom
  obtain ⟨⟨_, hA⟩, ⟨_, hA'⟩, hrel⟩ := hP
  have hne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hNB ⟨1, by simp, by ext i; exact (IsEmpty.false i).elim⟩
  let σ : R ≃+* R := starRingAut
  have hct : ∀ M : Matrix ι ι R, (M.map σ)ᵀ = Mᴴ := by
    intro M; ext i j; simp [σ, Matrix.conjTranspose_apply]
  have hs : ∀ x : ι → R, star x = fun l => σ (x l) := by
    intro x; ext l; simp [σ]
  have hσϖ : σ ϖ = ϖ := by simpa [σ] using (hI.fix ϖ).mp hI.pi_mem
  have hrel' : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A' := by rw [hct]; exact hrel
  obtain ⟨m, h₁, rfl, hle, _, hcase⟩ :=
    sel_main σ ϖ hI.pi_ne hI.pi_nonunit hσϖ hI.val A A' h hA hA' k hrel'
  rcases hcase with ⟨hmk, hu⟩ | ⟨hlt, g₁, j, y, _, _, _, hxy, hxx, hy⟩
  · exact absurd ⟨h₁, hu, by rw [hmk]⟩ hNB
  · refine ⟨k - m, h₁ *ᵥ Pi.single j 1, y, by omega, by omega, ?_, ⟨A' j j, ?_⟩,
      ⟨Pi.single j 1, ?_⟩, ⟨g₁ *ᵥ y, ?_⟩⟩
    · unfold hf; rw [hs]; exact hxy
    · unfold hf; rw [hs]; exact hxx
    · rw [Matrix.smul_mulVec, show k - (k - m) = m by omega]
    · rw [Matrix.smul_mulVec, ← hy, smul_smul, ← pow_add]
      congr 2
      omega

end PI.SqPair.LCP
end
end

