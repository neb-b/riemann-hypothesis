module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMemModelUnipotentAtPlace
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

theorem map_cT_of_conj {E : Type} [Field E] (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x))
    {a b : Type} (M : Matrix a b E) : (cT σ M).map τ = (M.map τ)ᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply, hτ]

theorem gM_mem_Nset (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ w, gM A γ w ∈ Nset k r := by
  intro hV γ hγ w
  obtain ⟨hCM, -, hJ, -, -, hD, -, hM, hs, hAd⟩ := hV
  obtain ⟨⟨hU, ⟨ν, hν, hγe⟩, hX⟩, -⟩ := hγ
  set τ := w.embedding with hτdef
  have hτ : ∀ x, τ ((σ : E →+* E) x) = star (τ x) := fun x => hCM.2.2.2 τ x
  set B := A w with hBdef
  set G := γ.map τ with hGdef
  set H := Hpk k r with hHdef
  set Ew := (eOf P).map τ with hEwdef
  have hJw : Bᴴ * H * B = J.map τ := hM w

  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hJw
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    have h2 : τ J.det = (J.map τ).det := by rw [RingHom.map_det]; rfl
    exact hJ.2 ((map_eq_zero τ).1 (h2.trans h1.symm))
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hBiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu

  have hGU : Gᴴ * J.map τ * G = J.map τ := by
    have h1 := congrArg (fun M => M.map τ) hU
    simp only [IsUn, Matrix.map_mul, map_cT_of_conj _ τ hτ] at h1
    exact h1

  set S : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i a => (s a : ℂ) * bvec (eI k r a) i with hSdef
  have hAE : B * Ew = S := by
    ext i a
    have h1 := congrFun (hAd w a).1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Ew, eOf, S] using h1
  have hgM : gM A γ w = B * G * B⁻¹ := rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    show (gM A γ w)ᴴ * H * gM A γ w = H
    rw [hgM]
    calc (B * G * B⁻¹)ᴴ * H * (B * G * B⁻¹) = (B⁻¹)ᴴ * (Gᴴ * (Bᴴ * H * B) * G) * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * H * B) * B⁻¹ := by rw [hJw, hGU]
      _ = (B * B⁻¹)ᴴ * H * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hBB]; simp
  ·
    have hGE : G * Ew = Ew * ν.map τ := by
      show γ.map τ * (eOf P).map τ = (eOf P).map τ * ν.map τ
      rw [← Matrix.map_mul, ← Matrix.map_mul, hγe]
      rfl
    have hgS : gM A γ w * S = S * ν.map τ := by
      rw [hgM, ← hAE]
      calc B * G * B⁻¹ * (B * Ew) = B * G * (B⁻¹ * B) * Ew := by simp only [Matrix.mul_assoc]
        _ = B * (G * Ew) := by rw [hBiB, Matrix.mul_one, Matrix.mul_assoc]
        _ = B * Ew * ν.map τ := by rw [hGE, Matrix.mul_assoc]
    intro b i hbi
    have h1 := congrFun (congrFun hgS i) b
    have hl : (gM A γ w * S) i b = gM A γ w i (eI k r b) * (s b : ℂ) := by
      simp [S, Matrix.mul_apply, bvec, Pi.single_apply]
    have hr : (S * ν.map τ) i b = (s b : ℂ) * (if i = eI k r b then 1 else 0) := by
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · simp [S, bvec, Pi.single_apply, (hν b b).2 rfl]
      · intro a _ hab
        by_cases hia : i = eI k r a
        · have hba : b < a := by
            have : b.val ≤ a.val := by rw [hia] at hbi; exact hbi
            exact lt_of_le_of_ne this (fun h => hab h.symm)
          simp [(hν a b).1 hba]
        · simp [S, bvec, Pi.single_apply, hia]
      · simp
    rw [hl, hr] at h1
    have hs0 : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have h2 := mul_right_cancel₀ hs0 (h1.trans (mul_comm _ _))
    exact h2
  ·
    have hH : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)), r ≤ j.val → j.val ≤ r + k → H (eI k r a) j = 0 := by
      intro a j h1 h2
      have ha := a.isLt
      have hv : (eI k r a).val = a.val := rfl
      show Hpk k r (eI k r a) j = 0
      unfold Hpk
      rw [if_neg (by rw [hv]; omega), if_neg (by omega), if_neg (fun h => absurd h.1 (by rw [hv]; omega))]
    set K := cT (σ : E →+* E) (eOf P) * J with hKdef
    have hKf : K * f = 1 := by
      ext a b
      have h1 := congrFun (congrFun hD.1 a.castSucc) b
      simp only [pairM, K, cT, eOf, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
        Matrix.submatrix_apply, id, Matrix.of_apply, Matrix.one_apply] at h1 ⊢
      rw [h1]
      simp [Fin.castSucc_inj]
    set Q := 1 - f * K with hQdef
    have hKQ : K * Q = 0 := by
      rw [hQdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hKf, Matrix.one_mul, sub_self]
    have hcol : ∀ j, ∃ c, γ *ᵥ (Q *ᵥ Pi.single j 1) - Q *ᵥ Pi.single j 1 = eOf P *ᵥ c := by
      intro j
      apply hX
      rw [Matrix.mulVec_mulVec, hKQ, Matrix.zero_mulVec]
    choose c hc using hcol
    set C : Matrix (Fin r) (Fin (2 * r + k + 1)) E := Matrix.of fun a j => c j a with hCdef
    have hsj : ∀ (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) i j, (M *ᵥ Pi.single j 1) i = M i j := by
      intro M i j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hQC : (γ - 1) * Q = eOf P * C := by
      ext i j
      have h1 := congrFun (hc j) i
      rw [Matrix.mulVec_mulVec, ← Matrix.sub_mulVec] at h1
      have e1 : γ * Q - Q = (γ - 1) * Q := by rw [Matrix.sub_mul, Matrix.one_mul]
      rw [e1, hsj] at h1
      rw [h1, Matrix.mul_apply]
      simp [Matrix.mulVec, dotProduct, C]
    set fw := f.map τ with hfwdef
    set Kw := Ewᴴ * J.map τ with hKwdef
    have hQw : (G - 1) * (1 - fw * Kw) = Ew * C.map τ := by
      have h1 := congrArg τ.mapMatrix hQC
      rw [map_mul, map_sub, map_one, hQdef, map_sub, map_one] at h1
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul, hKdef, map_cT_of_conj _ τ hτ] at h1
      exact h1
    have hKB : Kw * B⁻¹ = Sᴴ * H := by
      show Ewᴴ * J.map τ * B⁻¹ = Sᴴ * H
      rw [← hJw, ← hAE]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hBB, Matrix.mul_one]
    have hdecomp : gM A γ w - 1 = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H) := by
      have e1 : gM A γ w - 1 = B * (G - 1) * B⁻¹ := by
        rw [hgM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBB]
      rw [e1]
      calc B * (G - 1) * B⁻¹ = B * (G - 1) * ((1 - fw * Kw) + fw * Kw) * B⁻¹ := by
            rw [sub_add_cancel, Matrix.mul_one]
        _ = B * ((G - 1) * (1 - fw * Kw)) * B⁻¹ + B * (G - 1) * fw * (Kw * B⁻¹) := by
            rw [Matrix.mul_add, Matrix.add_mul]; simp only [Matrix.mul_assoc]
        _ = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H) := by
            rw [hQw, hKB, ← hAE]; simp only [Matrix.mul_assoc]
    intro i j hj1 hj2 hi
    have h1 := congrFun (congrFun hdecomp i) j
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply] at h1
    have z1 : (S * (C.map τ * B⁻¹)) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have hia : i ≠ eI k r a := fun h => by
        have ha := a.isLt
        rw [h] at hi
        exact absurd hi (show ¬ r ≤ a.val by omega)
      simp [S, bvec, Pi.single_apply, hia]
    have z2 : (B * (G - 1) * fw * (Sᴴ * H) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have h3 : (Sᴴ * H : Matrix (Fin r) (Fin (2 * r + k + 1)) ℂ) a j = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : l = eI k r a
        · subst hl
          rw [hH a j hj1 hj2, mul_zero]
        · simp [S, bvec, Pi.single_apply, hl, Matrix.conjTranspose_apply]
      rw [h3, mul_zero]
    rw [z1, z2, add_zero] at h1
    exact sub_eq_zero.1 h1

end GlobalTheory.SnMass.VolN

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentRadicalFormsUnitSubgroup
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.GNGroup

variable {E : Type} [Field E]

theorem cT_mul (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_mul' (σ : E →+* E) {n a : ℕ} (A : Matrix (Fin n) (Fin n) E) (B : Matrix (Fin n) (Fin a) E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_mul'' (σ : E →+* E) {n a : ℕ} (A : Matrix (Fin n) (Fin a) E) (B : Matrix (Fin a) (Fin a) E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : E →+* E) {n : ℕ} : cT σ (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp [cT]

theorem isUp_iff_bt {m : ℕ} (u : Matrix (Fin m) (Fin m) E) :
    IsUp u ↔ u.BlockTriangular id ∧ ∀ i, u i i = 1 := by
  constructor
  · intro h
    exact ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩
  · rintro ⟨h1, h2⟩ i j
    exact ⟨fun hij => h1 hij, fun hij => hij ▸ h2 i⟩

theorem diag_mul_of_bt {m : ℕ} {A B : Matrix (Fin m) (Fin m) E} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin m) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [hA hl, zero_mul]
    · rw [hB hl, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem isUp_mul {m : ℕ} {u u' : Matrix (Fin m) (Fin m) E} (h : IsUp u) (h' : IsUp u') : IsUp (u * u') := by
  rw [isUp_iff_bt] at h h' ⊢
  refine ⟨h.1.mul h'.1, fun i => ?_⟩
  rw [diag_mul_of_bt h.1 h'.1, h.2, h'.2, one_mul]

theorem isUp_inv {m : ℕ} {u : Matrix (Fin m) (Fin m) E} (h : IsUp u) : IsUp u⁻¹ ∧ u * u⁻¹ = 1 := by
  rw [isUp_iff_bt] at h
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular h.1]
    exact Finset.prod_eq_one fun i _ => h.2 i
  letI : Invertible u.det := { invOf := 1, invOf_mul_self := by simp [hdet], mul_invOf_self := by simp [hdet] }
  letI : Invertible u := Matrix.invertibleOfDetInvertible u
  have hbt : u⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h.1
  have hui : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u (by rw [hdet]; exact isUnit_one)
  refine ⟨(isUp_iff_bt _).2 ⟨hbt, fun i => ?_⟩, Matrix.mul_nonsing_inv u (by rw [hdet]; exact isUnit_one)⟩
  have := congrFun (congrFun hui i) i
  rw [diag_mul_of_bt hbt h.1, h.2, mul_one] at this
  simpa using this

variable [NumberField E]

theorem latMap_mul {n : ℕ} (g g' : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    latMap (g * g') Λ = latMap g (latMap g' Λ) := by
  ext x
  simp only [latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g' *ᵥ y, ⟨y, hy, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by rw [Matrix.mulVec_mulVec]⟩

theorem latMap_one {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) : latMap 1 Λ = Λ := by
  ext x
  simp [latMap, Submodule.mem_map]

omit [NumberField E] in
theorem isUnit_of_isUn (σ : E →+* E) {n : ℕ} {J g : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0)
    (h : IsUn σ J g) : IsUnit g := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have := congrArg Matrix.det h
  rw [cT, Matrix.det_mul, Matrix.det_mul] at this
  refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
  rw [h0, mul_zero] at this
  exact this.symm

omit [NumberField E] in
theorem isUn_mul (σ : E →+* E) {n : ℕ} {J g g' : Matrix (Fin n) (Fin n) E} (h : IsUn σ J g)
    (h' : IsUn σ J g') : IsUn σ J (g * g') := by
  unfold IsUn at *
  calc cT σ (g * g') * J * (g * g') = cT σ g' * (cT σ g * J * g) * g' := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [h, h']

omit [NumberField E] in
theorem isUn_inv (σ : E →+* E) {n : ℕ} {J a b : Matrix (Fin n) (Fin n) E} (h : IsUn σ J a)
    (hab : a * b = 1) : IsUn σ J b := by
  unfold IsUn at *
  calc cT σ b * J * b = cT σ b * (cT σ a * J * a) * b := by rw [h]
    _ = cT σ (a * b) * J * (a * b) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]

omit [NumberField E] in
theorem inN_one (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) :
    InN σ J P 1 := by
  refine ⟨by simp [IsUn, cT_one], ⟨1, ?_, ?_⟩, fun v _ => ⟨0, by simp⟩⟩
  · intro i j
    exact ⟨fun h => Matrix.one_apply_ne (ne_of_lt h).symm, fun h => by subst h; exact Matrix.one_apply_eq i⟩
  · have key : (1 : Matrix (Fin n) (Fin n) E) * eOf P = eOf P * (1 : Matrix (Fin r) (Fin r) E) := by
      rw [Matrix.one_mul, Matrix.mul_one]
    exact key

omit [NumberField E] in
theorem inN_mul (σ : E →+* E) {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E}
    {g g' : Matrix (Fin n) (Fin n) E} (h : InN σ J P g) (h' : InN σ J P g') : InN σ J P (g * g') := by
  obtain ⟨hu, ⟨ν, hν, he⟩, hp⟩ := h
  obtain ⟨hu', ⟨ν', hν', he'⟩, hp'⟩ := h'
  replace he : g * eOf P = eOf P * ν := he
  replace he' : g' * eOf P = eOf P * ν' := he'
  refine ⟨isUn_mul σ hu hu', ⟨ν * ν', isUp_mul hν hν', ?_⟩, fun v hv => ?_⟩
  · have key : (g * g') * eOf P = eOf P * (ν * ν') := by
      rw [Matrix.mul_assoc, he', ← Matrix.mul_assoc, he, Matrix.mul_assoc]
    exact key
  · obtain ⟨c, hc⟩ := hp v hv
    obtain ⟨c', hc'⟩ := hp' v hv
    refine ⟨ν *ᵥ c' + c, ?_⟩
    have e1 : (g * g') *ᵥ v - v = g *ᵥ (g' *ᵥ v - v) + (g *ᵥ v - v) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub]; abel
    rw [e1, hc', hc, Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, Matrix.mulVec_add]

omit [NumberField E] in
theorem inN_inv (σ : E →+* E) {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E}
    {a b : Matrix (Fin n) (Fin n) E} (h : InN σ J P a) (hab : a * b = 1) (hba : b * a = 1) :
    InN σ J P b := by
  obtain ⟨hu, ⟨ν, hν, he⟩, hp⟩ := h
  replace he : a * eOf P = eOf P * ν := he
  obtain ⟨hνi, hνν⟩ := isUp_inv hν
  have hJ : cT σ a * J = J * b := by
    calc cT σ a * J = cT σ a * J * (a * b) := by rw [hab, Matrix.mul_one]
      _ = J * b := by rw [← Matrix.mul_assoc, hu]
  refine ⟨isUn_inv σ hu hab, ⟨ν⁻¹, hνi, ?_⟩, fun v hv => ?_⟩
  · have key : b * eOf P = eOf P * ν⁻¹ := by
      calc b * eOf P = (b * (eOf P * ν)) * ν⁻¹ := by
            rw [Matrix.mul_assoc b, Matrix.mul_assoc, hνν, Matrix.mul_one]
        _ = (b * (a * eOf P)) * ν⁻¹ := by rw [he]
        _ = eOf P * ν⁻¹ := by rw [← Matrix.mul_assoc b, hba, Matrix.one_mul]
    exact key
  · have e2 : cT σ (eOf P) * J * b = cT σ ν * (cT σ (eOf P) * J) := by
      rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, ← cT_mul', he, cT_mul'', Matrix.mul_assoc]
    have hw : (cT σ (eOf P) * J) *ᵥ (b *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec]
      have hv' : (cT σ (eOf P) * J) *ᵥ v = 0 := hv
      rw [hv', Matrix.mulVec_zero]
    obtain ⟨c, hc⟩ := hp _ hw
    refine ⟨-c, ?_⟩
    rw [Matrix.mulVec_mulVec, hab, Matrix.one_mulVec] at hc
    rw [Matrix.mulVec_neg, ← hc]
    abel

end GlobalTheory.SnMass.VolN.GNGroup

namespace GlobalTheory.SnMass.VolN

variable {E : Type} [Field E] [NumberField E]

def gNUnits (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Subgroup (Matrix (Fin n) (Fin n) E)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P}
  one_mem' := by
    show ((1 : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P
    rw [Units.val_one]
    exact ⟨GNGroup.inN_one _ J P, GNGroup.latMap_one Λ⟩
  mul_mem' := by
    intro a b ha hb
    show ((a * b : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P
    rw [Units.val_mul]
    exact ⟨GNGroup.inN_mul _ ha.1 hb.1, by rw [GNGroup.latMap_mul, hb.2, ha.2]⟩
  inv_mem' := by
    intro a ha
    show ((a⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P
    refine ⟨GNGroup.inN_inv _ ha.1 a.mul_inv a.inv_mul, ?_⟩
    calc latMap ((a⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) Λ
        = latMap ((a⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E)
            (latMap (a : Matrix (Fin n) (Fin n) E) Λ) := by rw [ha.2]
      _ = Λ := by rw [← GNGroup.latMap_mul, a.inv_mul, GNGroup.latMap_one]

theorem gN_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → (∃ G : Subgroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, ∀ u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, u ∈ G ↔ (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) ∈ GN (σ : E →+* E) J Λ P) ∧ ∀ γ ∈ GN (σ : E →+* E) J Λ P, IsUnit γ := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV
  have hJ : J.det ≠ 0 := hV.2.2.1.2
  exact ⟨⟨gNUnits (σ : E →+* E) J Λ P, fun u => Iff.rfl⟩,
    fun γ hγ => GNGroup.isUnit_of_isUn (σ : E →+* E) hJ hγ.1.1⟩

end GlobalTheory.SnMass.VolN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite
section
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.SnMass.ProdQuot

theorem isHaarMeasure_of_sigmaFinite {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] (ν : Measure H)
    [SigmaFinite ν] [ν.IsMulLeftInvariant] (hν : ν ≠ 0) : ν.IsHaarMeasure := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have e := Measure.haarMeasure_unique ν K
  rw [e]
  refine Measure.IsHaarMeasure.smul _ (fun hc => hν (by rw [e, hc, zero_smul])) fun hc => hν ?_
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
  refine measure_iUnion_null fun n => ?_
  have h1 := measure_spanningSets_lt_top ν n
  have h2 : ν (spanningSets ν n) = ⊤ * Measure.haarMeasure K (spanningSets ν n) := by
    have := congrArg (fun ρ : Measure H => ρ (spanningSets ν n)) e
    simpa [hc] using this
  by_cases h3 : Measure.haarMeasure K (spanningSets ν n) = 0
  · rw [h2, h3, mul_zero]
  · rw [h2, ENNReal.top_mul h3] at h1
    exact absurd h1 (lt_irrefl _)

theorem exists_cutoff {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (R : Subgroup G) (μ : Measure G)
    [SigmaFinite μ] (hR : IsClosed (R : Set G)) (h0 : μ ≠ 0) (hc : μ (R : Set G)ᶜ = 0)
    (hi : ∀ s ∈ R, μ.map (fun x => s * x) = μ ∧ μ.map (fun x => x * s) = μ) :
    ∃ b : G → ℝ≥0, Measurable b ∧ ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1 := by
  have hce : Topology.IsClosedEmbedding R.subtype := hR.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding R.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : SecondCountableTopology R := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap R.subtype).map R.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range R.subtype = (R : Set G) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure R := μ.comap R.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => (g : G) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← (hi g g.2).1, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsMulRightInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => x * (g : G) := measurable_mul_const _
    rw [Measure.map_map hφ.measurable (measurable_mul_const g), h2]
    conv_rhs => rw [← (hi g g.2).2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsHaarMeasure := isHaarMeasure_of_sigmaFinite ν fun h => h0 (by rw [← h2, h, Measure.map_zero])
  obtain ⟨b, hb, h1⟩ := GlobalTheory.exists_measurable_lintegral_coset_eq_one G R ν R.subtype hce
  refine ⟨fun x => (b x).toNNReal, hb.ennreal_toNNReal, fun g => ?_⟩
  have hm : Measurable fun s => b (s * g) := hb.comp (measurable_mul_const g)
  have h3 : ∫⁻ s, b (s * g) ∂μ = 1 := by
    rw [← h2, hφ.lintegral_map]
    exact h1 g
  rw [← h3]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_lt_top hm (by rw [h3]; exact ENNReal.one_ne_top)] with s hs
  exact ENNReal.coe_toNNReal hs.ne

theorem map_eq {G : Type} [Group G] [MeasurableSpace G] (μG μ ν : Measure G) {b : G → ℝ≥0} (hb : Measurable b)
    (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {F : G → ℂ} (hF : Measurable F) (hi : ∀ᵐ s ∂μ, ∀ x, F (s * x) = F x) :
    ν.map F = (μG.withDensity fun x => b x).map F := by
  have hb' : Measurable fun x => (b x : ℝ≥0∞) := hb.coe_nnreal_ennreal
  ext A hA
  rw [Measure.map_apply hF hA, Measure.map_apply hF hA, withDensity_apply _ (hF hA),
    ← lintegral_indicator (hF hA), hν _ (hb'.indicator (hF hA)), ← lintegral_indicator_one (hF hA)]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ F ⁻¹' A
  · rw [Set.indicator_of_mem hx, Pi.one_apply, ← h1 x]
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [Set.indicator_of_mem (by simpa [hs] using hx)]
  · rw [Set.indicator_of_notMem hx, ← lintegral_zero (μ := μ)]
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [Set.indicator_of_notMem (by simpa [hs] using hx)]

theorem integral_eq {G : Type} [Group G] [MeasurableSpace G] (μG μ ν : Measure G) {b : G → ℝ≥0} (hb : Measurable b)
    (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {F : G → ℂ} (hF : Measurable F) (hi : ∀ᵐ s ∂μ, ∀ x, F (s * x) = F x) :
    ∫ x, F x ∂ν = ∫ x, (b x : ℂ) * F x ∂μG ∧ (Integrable F ν ↔ Integrable (fun x => (b x : ℂ) * F x) μG) := by
  have h := map_eq μG μ ν hb h1 hν hF hi
  have e : (fun x => (b x : ℂ) * F x) = fun x => b x • F x := by
    ext x
    simp [NNReal.smul_def]
  have hid : ∀ ρ : Measure ℂ, AEStronglyMeasurable (fun z : ℂ => z) ρ := fun ρ => continuous_id.aestronglyMeasurable
  rw [e]
  constructor
  · rw [← integral_withDensity_eq_integral_smul hb, ← integral_map hF.aemeasurable (hid _),
      ← integral_map hF.aemeasurable (hid _), h]
  · rw [← integrable_withDensity_iff_integrable_smul hb]
    have h2 := integrable_map_measure (μ := ν) (hid _) hF.aemeasurable
    have h3 := integrable_map_measure (μ := μG.withDensity fun x => b x) (hid _) hF.aemeasurable
    rw [h] at h2
    exact h2.symm.trans h3

end GlobalTheory.SnMass.ProdQuot
end
end

