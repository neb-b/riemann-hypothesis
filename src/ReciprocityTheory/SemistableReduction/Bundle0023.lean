module

public import ReciprocityTheory.SemistableReduction.Bundle0020
public import ReciprocityTheory.SemistableReduction.Bundle0019

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegD
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

private theorem posDef_diagonal_ofReal_of_pos {r : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) :
    (diagonal fun l => (d l : ℂ)).PosDef := by
  first
  | exact Matrix.posDef_diagonal_iff.mpr fun l => Complex.zero_lt_real.mpr (hd l)
  | exact Matrix.posDef_diagonal_iff.mpr fun l => by exact_mod_cast hd l

theorem sdd_gram_step {K : Type} [Field K] [NumberField K] {r e k₀ k₁ : ℕ} (σ : K →+* ℂ)
    (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    Real.log (gramC (diagonal fun l => (d l : ℂ)) σ b₁).det.re ≤
      Real.log (quotGramC (diagonal fun l => (d l : ℂ)) σ b₀ c).det.re := by

  have hcutz : ∀ i (l : Fin r), e ≤ (l : ℕ) → b₀ i l = 0 := by
    intro i l hl
    have h := hb₀cut i
    simp only [cutSub, UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub] at h
    exact h l hl
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun l => (d l : ℂ) with hDdef
  have hDpd : D.PosDef := posDef_diagonal_ofReal_of_pos d hd
  have hG0 : ((embM σ b₀)ᴴ * D * embM σ b₀).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₀ hb₀li)
  have hG1 : ((embM σ b₁)ᴴ * D * embM σ b₁).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₁ hb₁li)
  have hu : IsUnit ((embM σ b₀)ᴴ * D * embM σ b₀).det := by
    first
    | exact (Matrix.isUnit_iff_isUnit_det _).mp hG0.isUnit
    | exact hG0.det_pos.ne'.isUnit
  set E : Matrix (Fin r) (Fin k₁) ℂ := embM σ c - embM σ b₀ *
    (((embM σ b₀)ᴴ * D * embM σ b₀)⁻¹ * ((embM σ b₀)ᴴ * D * embM σ c)) with hE

  have hq : quotGramC D σ b₀ c = Eᴴ * D * E := by
    simp only [quotGramC, sdd_gramC_eq, sdd_gramX_eq]
    exact sdd_schur _ _ _ hDpd.1 hG0.1 hu

  have hB1 : ∀ (l : Fin r) (j : Fin k₁),
      embM σ b₁ l j = if e ≤ (l : ℕ) then E l j else 0 := by
    intro l j
    have hb1 : b₁ j l = if e ≤ (l : ℕ) then c j l else 0 := by
      rw [← hcb j]; rfl
    by_cases hl : e ≤ (l : ℕ)
    · have hz : ∀ i, b₀ i l = 0 := fun i => hcutz i l hl
      rw [if_pos hl, hE]
      simp [embM, Matrix.mul_apply, hb1, hl, hz]
    · rw [if_neg hl]
      simp [embM, hb1, hl]
  have hquad : ∀ v : Fin k₁ → ℂ, (star v ⬝ᵥ (((embM σ b₁)ᴴ * D * embM σ b₁) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * D * E) *ᵥ v)).re :=
    sdd_cut_quad d (fun l => (hd l).le) e E (embM σ b₁) hB1
  obtain ⟨hpos, hle⟩ := sdd_det_mono _ _ hG1 (Matrix.isHermitian_conjTranspose_mul_mul E hDpd.1) hquad
  rw [sdd_gramC_eq, hq]
  exact Real.log_le_log hpos hle

theorem gradedExt_holds (hB : LatDegBasisStatement) (hD : DegAddStatement) :
    GradedExtStatement := by
  unfold GradedExtStatement
  unfold LatDegBasisStatement at hB
  unfold DegAddStatement at hD
  intro K _ _ r e k k₀ k₁ δ B b b₀ b₁ hδ hFG hb hb₀ hb₁

  have hlift : ∀ j, ∃ y ∈ B, projGe K r e y = b₁ j := fun j => Submodule.mem_map.mp (hb₁.1 j)
  choose c hcB hcb using hlift
  have hb₀B : ∀ i, b₀ i ∈ B := fun i => (hb₀.1 i).1
  have hb₀cut : ∀ i, b₀ i ∈ cutSub K r e := fun i => (hb₀.1 i).2
  have hli : LinearIndependent K (Fin.append b₀ c) :=
    sdd_append_li b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
  have hsp : ∀ x ∈ B, x ∈ Submodule.span K (Set.range (Fin.append b₀ c)) :=
    sdd_append_span B b₀ c b₁ hb₀ hcB hcb hb₁
  have hmem : ∀ i, Fin.append b₀ c i ∈ B := by
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hb₀B, hcB]
  have hk : k = k₀ + k₁ := sdd_card_eq B b (Fin.append b₀ c) hb hmem hli hsp
  subst hk
  have hpd : ∀ σ, (diagMet δ σ).PosDef := fun σ => by
    simp only [diagMet]
    exact posDef_diagonal_ofReal_of_pos (δ σ) (hδ σ)
  have h1 : latDeg (diagMet δ) B b = latDeg (diagMet δ) B (Fin.append b₀ c) :=
    hB K r (k₀ + k₁) (diagMet δ) B b (Fin.append b₀ c) hpd hFG hb ⟨hmem, hli, hsp⟩
  have h2 := hD K r k₀ k₁ (diagMet δ) B b₀ c hpd hFG hb₀B hcB hli hsp
  have hsat : satSub B b₀ = B ⊓ cutSub K r e := sdd_satSub_eq B b₀ hb₀
  rw [hsat] at h2
  have h3 : quotDeg (diagMet δ) B b₀ c ≤ latDeg (diagMet δ) (B.map (projGe K r e)) b₁ := by
    unfold quotDeg latDeg
    rw [sdd_index B b₀ c b₁ hsat hcB hcb]
    have hs : ∑ σ : K →+* ℂ, Real.log (gramC (diagMet δ σ) σ b₁).det.re ≤
        ∑ σ : K →+* ℂ, Real.log (quotGramC (diagMet δ σ) σ b₀ c).det.re :=
      Finset.sum_le_sum fun σ _ =>
        sdd_gram_step σ (δ σ) (hδ σ) b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
    linarith
  linarith [h1, h2, h3]

theorem absDet_holds : AbsDetStatement := by
  intro n A C hA hC h
  exact sdd_absDet A C hA hC h

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegF
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def wPart (r m : ℕ) (i : Fin r) : Fin r :=
  if (i : ℕ) < m ∨ r ≤ (i : ℕ) + m then Fin.rev i else i

def wVal {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r) : K :=
  if (i : ℕ) < m ∨ r ≤ (i : ℕ) + m then 1 else g i

theorem wPart_wPart (r m : ℕ) (i : Fin r) : wPart r m (wPart r m i) = i := by
  have hi := i.isLt
  unfold wPart
  by_cases h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m
  · rw [if_pos h, if_pos (by simp only [Fin.val_rev]; omega), Fin.rev_rev]
  · rw [if_neg h, if_neg h]

theorem wPart_outer (r m : ℕ) (i : Fin r) (h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m) :
    wPart r m i = Fin.rev i := by
  unfold wPart
  rw [if_pos h]

theorem wPart_mid (r m : ℕ) (i : Fin r) (h : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m)) :
    wPart r m i = i := by
  unfold wPart
  rw [if_neg h]

theorem wVal_outer {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r)
    (h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m) : wVal r m g i = 1 := by
  unfold wVal
  rw [if_pos h]

theorem wVal_mid {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r)
    (h : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m)) : wVal r m g i = g i := by
  unfold wVal
  rw [if_neg h]

theorem wittMat_eq {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) :
    wittMat r m g = Matrix.of fun i j => if j = wPart r m i then wVal r m g i else 0 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [wittMat, Matrix.of_apply]
  by_cases h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m
  · rw [wPart_outer r m i h, wVal_outer r m g i h]
    by_cases hj' : j = Fin.rev i
    · subst hj'
      rw [if_pos rfl, if_pos (by simp only [Fin.val_rev]; omega)]
    · rw [if_neg hj']
      rw [if_neg (by rintro ⟨h1, -⟩; apply hj'; ext; simp only [Fin.val_rev]; omega),
        if_neg (by rintro ⟨rfl, h2, h3⟩; omega)]
  · rw [wPart_mid r m i h, wVal_mid r m g i h]
    by_cases hij : j = i
    · subst hij
      rw [if_pos rfl, if_neg (by rintro ⟨h1, h2⟩; omega), if_pos ⟨rfl, by omega, by omega⟩]
    · rw [if_neg hij, if_neg (by rintro ⟨h1, h2⟩; omega), if_neg (by rintro ⟨h1, -⟩; exact hij h1.symm)]

theorem wittMat_map_mul {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (σ : K →+* ℂ)
    (v : Fin r → ℂ) :
    (wittMat r m g).map σ * diagonal v * (wittMat r m g).map σ =
      diagonal fun i => σ (wVal r m g i) * v (wPart r m i) * σ (wVal r m g (wPart r m i)) := by
  rw [wittMat_eq]
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (wPart r m i)]
  · simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply, if_pos rfl, wPart_wPart,
      Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [if_neg (Ne.symm hik), if_neg hik, map_zero, mul_zero]
  · intro j _ hj
    simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply, if_neg hj, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

def adMet {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K) (dd : Fin r → ℝ) :
    (K →+* ℂ) → Fin r → ℝ :=
  fun σ i => if (i : ℕ) < m then dd i else if r ≤ (i : ℕ) + m then (dd (Fin.rev i))⁻¹
    else ‖σ (g i)‖

theorem adMet_pos {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (hdd : ∀ i, 0 < dd i)
    (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) (σ : K →+* ℂ) (i : Fin r) :
    0 < adMet r m g dd σ i := by
  have hi := i.isLt
  unfold adMet
  split_ifs with h1 h2
  · exact hdd i
  · exact inv_pos.mpr (hdd _)
  · exact norm_pos_iff.mpr ((map_ne_zero σ).mpr (hg i (by omega) (by omega)))

theorem adMet_conj {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (σ : K →+* ℂ) :
    adMet r m g dd ((starRingEnd ℂ).comp σ) = adMet r m g dd σ := by
  funext i
  unfold adMet
  simp only [RingHom.comp_apply, Complex.norm_conj]

theorem wVal_adMet {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (h2m : 2 * m ≤ r)
    (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) (σ : K →+* ℂ)
    (hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i))
    (i : Fin r) :
    σ (wVal r m g i) * (((adMet r m g dd σ (wPart r m i) : ℝ) : ℂ))⁻¹ *
      σ (wVal r m g (wPart r m i)) = ((adMet r m g dd σ i : ℝ) : ℂ) := by
  have hi := i.isLt
  by_cases h1 : (i : ℕ) < m
  · have ho : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m := Or.inl h1
    rw [wPart_outer r m i ho, wVal_outer r m g i ho,
      wVal_outer r m g (Fin.rev i) (by simp only [Fin.val_rev]; omega)]
    unfold adMet
    simp only [Fin.val_rev, Fin.rev_rev]
    rw [if_neg (show ¬ (r - ((i : ℕ) + 1) < m) by omega), if_pos (show r ≤ r - ((i : ℕ) + 1) + m by omega),
      if_pos h1]
    simp
  · by_cases h2 : r ≤ (i : ℕ) + m
    · have ho : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m := Or.inr h2
      rw [wPart_outer r m i ho, wVal_outer r m g i ho,
        wVal_outer r m g (Fin.rev i) (by simp only [Fin.val_rev]; omega)]
      unfold adMet
      simp only [Fin.val_rev]
      rw [if_pos (show r - ((i : ℕ) + 1) < m by omega), if_neg h1, if_pos h2]
      simp
    · have hm : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m) := by omega
      rw [wPart_mid r m i hm, wVal_mid r m g i hm]
      unfold adMet
      rw [if_neg h1, if_neg h2]
      have hr := hreal i (by omega) (by omega)
      have hne : σ (g i) ≠ 0 := (map_ne_zero σ).mpr (hg i (by omega) (by omega))
      have hz : ((σ (g i)).re : ℂ) = σ (g i) := Complex.conj_eq_iff_re.mp hr
      rw [← hz, Complex.norm_real, Real.norm_eq_abs]
      have hx : (σ (g i)).re ≠ 0 := by
        intro h0
        apply hne
        rw [← hz, h0, Complex.ofReal_zero]
      have habs : ((|(σ (g i)).re| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hx
      have hsq : ((σ (g i)).re : ℂ) * (σ (g i)).re = ((|(σ (g i)).re| : ℝ) : ℂ) * |(σ (g i)).re| := by
        exact_mod_cast (abs_mul_abs_self (σ (g i)).re).symm
      calc ((σ (g i)).re : ℂ) * (↑|(σ (g i)).re|)⁻¹ * ((σ (g i)).re : ℂ)
          = (((σ (g i)).re : ℂ) * (σ (g i)).re) * (↑|(σ (g i)).re|)⁻¹ := by ring
        _ = (((|(σ (g i)).re| : ℝ) : ℂ) * |(σ (g i)).re|) * (↑|(σ (g i)).re|)⁻¹ := by rw [hsq]
        _ = ((|(σ (g i)).re| : ℝ) : ℂ) := by field_simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

