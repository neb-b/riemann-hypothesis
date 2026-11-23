module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroup
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.RowIso

section Alg
variable {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, Matrix.mulVec_add, dotProduct_add]

theorem form_sub_left (x x' y : Fin n → E) : form σ J (x - x') y = form σ J x y - form σ J x' y := by
  simp [form, Matrix.mulVec_sub, dotProduct_sub]

theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  simp [form, dotProduct, add_mul, Finset.sum_add_distrib]

theorem form_sub_right (x y y' : Fin n → E) : form σ J x (y - y') = form σ J x y - form σ J x y' := by
  simp [form, dotProduct, sub_mul, Finset.sum_sub_distrib]

theorem form_neg_right (x y : Fin n → E) : form σ J x (-y) = -form σ J x y := by
  simp [form, dotProduct]

theorem form_neg_left (x y : Fin n → E) : form σ J (-x) y = -form σ J x y := by
  simp [form, Matrix.mulVec_neg]

theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

theorem form_herm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    form σ J x y = σ (form σ J y x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rowE_mulVec (e y : Fin n → E) (t : E) (x : Fin n → E) :
    rowE σ J e y t *ᵥ x = x + form σ J x e • (y + t • e) - form σ J x y • e := by
  ext i
  simp only [rowE, mulVec, dotProduct, form, vecMul, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm (f := fun (a b : Fin n) => y i * (σ (e b) * (J b a * x a))),
    Finset.sum_comm (f := fun (a b : Fin n) => t * (e i * (σ (e b) * (J b a * x a)))),
    Finset.sum_comm (f := fun (a b : Fin n) => e i * (σ (y b) * (J b a * x a))), ← Finset.sum_add_distrib]
  congr 2
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · funext a
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

theorem isUn_of_form (g : Matrix (Fin n) (Fin n) E)
    (h : ∀ x x', form σ J (g *ᵥ x) (g *ᵥ x') = form σ J x x') : IsUn σ J g := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [form, dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, apply_ite σ, map_one, map_zero, ite_mul, one_mul, zero_mul] at this
  rw [← this]
  simp only [IsUn, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Alg
end GlobalTheory.SnMass.VolN.RowIso

namespace GlobalTheory.SnMass.VolN.RowIso

section Iso
variable {E : Type} [Field E] {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
  (hJ : ∀ i j, σ (J j i) = J i j) {e y : Fin n → E} {t : E} (he : form σ J e e = 0)
  (hye : form σ J y e = 0) (ht : form σ J y y + t + σ t = 0)
include hσ hJ he hye ht

theorem form_rowE (x x' : Fin n → E) :
    form σ J (rowE σ J e y t *ᵥ x) (rowE σ J e y t *ᵥ x') = form σ J x x' := by
  have hey : form σ J e y = 0 := by rw [form_herm σ J hσ hJ, hye, map_zero]
  have h1 : form σ J y x' = σ (form σ J x' y) := form_herm σ J hσ hJ _ _
  have h2 : form σ J e x' = σ (form σ J x' e) := form_herm σ J hσ hJ _ _
  simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_add_right, form_sub_right,
    form_smul_right, map_add, map_sub, map_mul, hσ, he, hye, hey, h1, h2]
  linear_combination (form σ J x e * σ (form σ J x' e)) * ht

theorem rowE_inv (x : Fin n → E) :
    rowE σ J e y t *ᵥ (rowE σ J e (-y) (σ t) *ᵥ x) = x := by
  have hey : form σ J e y = 0 := by rw [form_herm σ J hσ hJ, hye, map_zero]
  have hα : form σ J (rowE σ J e (-y) (σ t) *ᵥ x) e = form σ J x e := by
    simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_neg_left, he, hye]
    ring
  have hβ : form σ J (rowE σ J e (-y) (σ t) *ᵥ x) y = form σ J x y - form σ J x e * form σ J y y := by
    simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_neg_left, form_neg_right, hey]
    ring
  rw [rowE_mulVec σ J e y t, hα, hβ, rowE_mulVec σ J e (-y) (σ t) x]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, form_neg_right]
  linear_combination (form σ J x e * e i) * ht

end Iso

section Lat
variable {E : Type} [Field E] [NumberField E]


open GlobalTheory.SnMass.FrameDual in
theorem rowE_mem {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : GlobalTheory.SgGlob.SelfDual σ J Λ) {𝔞 : FractionalIdeal (𝓞 E)⁰ E}
    (h0 : 𝔞 ≠ 0) (hs : Stab σ 𝔞) {e y : Fin n → E} {t : E} (he : ∀ c ∈ 𝔞, c • e ∈ Λ)
    (hy : ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ) (ht : t ∈ 𝔞 * 𝔞) {v : Fin n → E} (hv : v ∈ Λ) :
    rowE σ J e y t *ᵥ v ∈ Λ := by
  have hO : ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range := (hΛ.2 v).1 hv
  have hα : form σ J v e ∈ 𝔞⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff h0]
    intro z hz
    have := hO _ (he _ (hs z hz))
    rw [form_smul_right, hσ, mul_comm] at this
    obtain ⟨d, hd⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨d, hd⟩
  have hβ : form σ J v y ∈ 𝔞 := by
    have h0' : 𝔞⁻¹ ≠ 0 := inv_ne_zero h0
    rw [← inv_inv 𝔞, FractionalIdeal.mem_inv_iff h0']
    intro z hz
    have := hO _ (hy _ (Stab.inv hσ hs h0 z hz))
    rw [form_smul_right, hσ, mul_comm] at this
    obtain ⟨d, hd⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨d, hd⟩
  have hγ : t * form σ J v e ∈ 𝔞 := by
    have := FractionalIdeal.mul_mem_mul ht hα
    rwa [mul_assoc, mul_inv_cancel₀ h0, mul_one] at this
  have hvec : rowE σ J e y t *ᵥ v =
      v + form σ J v e • y + (t * form σ J v e) • e - form σ J v y • e := by
    rw [rowE_mulVec, smul_add, smul_smul, mul_comm (form σ J v e) t, add_assoc]
  rw [hvec]
  exact Λ.sub_mem (Λ.add_mem (Λ.add_mem hv (hy _ hα)) (he _ hγ)) (he _ hβ)

end Lat

end GlobalTheory.SnMass.VolN.RowIso

namespace GlobalTheory.SnMass.VolN.RowIso

theorem form_col_col {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (b c : Fin m) :
    form σ J (fun i => P i b) (fun i => P i c) = pairM σ J P P c b := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  ring


open GlobalTheory.SnMass.FrameDual in
theorem rowE_mem_GN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E), (∀ c : Fin r, c ≤ a → form (σ : E →+* E) J y (fun i => P i c.castSucc) = 0) → form (σ : E →+* E) J y y + t + σ t = 0 → (∀ c ∈ (dInv E (r - a.val))⁻¹, c • y ∈ Λ) → t ∈ dInv E (2 * (r - a.val)) → rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t ∈ GN (σ : E →+* E) J Λ P := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a y t hyc hyt hyΛ htI
  obtain ⟨hcm, -, hJ, hΛ, hP, -, htup, -⟩ := hV
  set σ' : E →+* E := (σ : E →+* E) with hσ'
  have hσ : ∀ x, σ' (σ' x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h := hcm.2.2.2 τ
    simp only [hσ', AlgHom.coe_toRingHom, h, star_star]
  have hJ' : ∀ i j, σ' (J j i) = J i j := hJ.1
  have hyt' : form σ' J y y + t + σ' t = 0 := hyt
  set e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc with he_def
  set 𝔞 : FractionalIdeal (𝓞 E)⁰ E := dInv E (r - a.val) with h𝔞
  have heb : ∀ b c : Fin r, form σ' J (fun i => P i b.castSucc) (fun i => P i c.castSucc) = 0 := by
    intro b c
    rw [form_col_col, hP.2, TF, Matrix.diagonal_apply]
    split_ifs with h1 h2 <;> first | rfl | exact absurd h2 (Fin.castSucc_ne_last c)
  have hee : form σ' J e e = 0 := heb a a
  have hye : form σ' J y e = 0 := hyc a le_rfl
  have hyb : ∀ b : Fin r, b ≤ a → form σ' J (fun i => P i b.castSucc) y = 0 := by
    intro b hb
    rw [form_herm σ' J hσ hJ', hyc b hb, map_zero]
  have h0 : 𝔞 ≠ 0 := dInv_ne_zero _
  have hs : Stab σ' 𝔞 := stab_dInv hσ _
  have he𝔞 : ∀ c ∈ 𝔞, c • e ∈ Λ := by
    intro c hc
    refine htup (Submodule.subset_span ⟨Fin.castAdd r a.castSucc, c, ?_, ?_⟩)
    · rw [frameDualTupleIdeals_castAdd]; exact hc
    · funext i
      simp [sideM, he_def]
  have ht2 : t ∈ 𝔞 * 𝔞 := by
    rw [h𝔞, GlobalTheory.SgGlob.dInv, ← pow_add, ← two_mul]
    exact htI
  refine ⟨⟨isUn_of_form σ' J _ (form_rowE hσ hJ' hee hye hyt'), ?_, ?_⟩, ?_⟩
  · refine ⟨Matrix.of fun i j => (if i = j then 1 else 0) -
        (if i = a then form σ' J (fun l => P l j.castSucc) y else 0), ?_, ?_⟩
    · intro i j
      refine ⟨fun hji => ?_, fun hij => ?_⟩
      · have hne : i ≠ j := (ne_of_lt hji).symm
        by_cases hia : i = a
        · subst hia
          simp [hne, hyb j (le_of_lt hji)]
        · simp [hne, hia]
      · subst hij
        by_cases hia : i = a
        · subst hia
          simp [hyb i le_rfl]
        · simp [hia]
    · ext l j
      change (rowE σ' J e y t *ᵥ fun m => P m j.castSucc) l = ∑ i : Fin r, P l i.castSucc *
        ((if i = j then 1 else 0) - (if i = a then form σ' J (fun l => P l j.castSucc) y else 0))
      rw [rowE_mulVec, heb j a]
      simp only [Matrix.of_apply, eOf, Matrix.submatrix_apply, id, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, he_def]
      ring
  · intro v hv
    have hve : form σ' J v e = 0 := by
      have := congrFun hv a
      rw [← Matrix.mulVec_mulVec] at this
      simpa [form, cT, mulVec, dotProduct, eOf, he_def] using this
    refine ⟨Pi.single a (-form σ' J v y), ?_⟩
    rw [rowE_mulVec, hve, Matrix.mulVec_single]
    ext l
    simp [eOf, he_def] <;> ring
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact rowE_mem hσ hΛ h0 hs he𝔞 hyΛ ht2 hv
    · intro v hv
      have hy' : ∀ c ∈ 𝔞⁻¹, c • (-y) ∈ Λ := fun c hc => by
        rw [smul_neg]; exact Λ.neg_mem (hyΛ c hc)
      refine ⟨rowE σ' J e (-y) (σ' t) *ᵥ v, rowE_mem hσ hΛ h0 hs he𝔞 hy' (hs.mul hs t ht2) hv, ?_⟩
      exact rowE_inv hσ hJ' hee hye hyt' v

end GlobalTheory.SnMass.VolN.RowIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinates
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

end GlobalTheory.SnMass.VolN

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
private lemma mul_vecMulVec_mul_flag_measures {n : Type} [Fintype n] (M N : Matrix n n ℂ) (u v : n → ℂ) :
    M * vecMulVec u v * N = vecMulVec (M *ᵥ u) (v ᵥ* N) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
private lemma single_vecMul_Hpk_eI (k r : ℕ) (a : Fin r) :
    Pi.single (_root_.Formalism.QuantumDeterminants.eI k r a) 1 ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r = Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) (1 : ℂ) := by
  funext j
  rw [single_one_vecMul]
  change _root_.Formalism.QuantumDeterminants.Hpk k r (_root_.Formalism.QuantumDeterminants.eI k r a) j = (Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) (1 : ℂ) : _ → ℂ) j
  unfold _root_.Formalism.QuantumDeterminants.Hpk _root_.Formalism.QuantumDeterminants.eI _root_.Formalism.QuantumDeterminants.esI
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  have ha := a.isLt
  split_ifs <;> first | rfl | (exfalso; omega)


open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
theorem _root_.GlobalTheory.SnMass.VolN.rowE_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), _root_.GlobalTheory.SnMass.VolN.IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E) (w : InfinitePlace E) (i j : Fin (2 * r + k + 1)), _root_.GlobalTheory.SnMass.VolN.gM A (_root_.GlobalTheory.SnMass.VolN.rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t) w i j = (if i = j then 1 else 0) + (if j = _root_.Formalism.QuantumDeterminants.esI k r a then (s a : ℂ) * (((A w).mulVec fun l => w.embedding (y l)) i + (if i = _root_.Formalism.QuantumDeterminants.eI k r a then (s a : ℂ) * w.embedding t else 0)) else 0) - (if i = _root_.Formalism.QuantumDeterminants.eI k r a then (s a : ℂ) * _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.bvec j) ((A w).mulVec fun l => w.embedding (y l)) else 0) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD a y t w i j
  obtain ⟨hσ, -, hJ, -, -, -, -, hA, -, hAd⟩ := hD
  set x : Fin (2 * r + k + 1) → ℂ := fun l => w.embedding (P l a.castSucc) with hx_def
  set v : Fin (2 * r + k + 1) → ℂ := fun l => w.embedding (y l) with hv_def
  have hconj : ∀ z : E, w.embedding (σ z) = star (w.embedding z) := fun z => hσ.2.2.2 w.embedding z
  have hiso : (A w)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * A w = J.map w.embedding := hA w
  have hAx : A w *ᵥ x = (s a : ℂ) • _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a) := (hAd w a).1
  have hdet : IsUnit (A w).det := by
    have h1 : (J.map w.embedding).det ≠ 0 := by
      rw [show (J.map w.embedding).det = w.embedding J.det from (RingHom.map_det _ _).symm]
      exact (map_ne_zero _).2 hJ.2
    rw [← hiso, det_mul, det_mul] at h1
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h1)
  have hinv : A w * (A w)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hrow : ∀ u : Fin (2 * r + k + 1) → ℂ,
      star u ᵥ* J.map w.embedding ᵥ* (A w)⁻¹ = star (A w *ᵥ u) ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r := by
    intro u
    rw [← hiso, vecMul_vecMul, Matrix.mul_assoc, hinv, Matrix.mul_one, ← vecMul_vecMul,
      ← star_mulVec]
  have hmap : (_root_.GlobalTheory.SnMass.VolN.rowE (σ : E →+* E) J (fun l => P l a.castSucc) y t).map
      w.embedding = 1 + vecMulVec (v + w.embedding t • x) (star x ᵥ* J.map w.embedding) -
        vecMulVec x (star v ᵥ* J.map w.embedding) := by
    ext p q
    set_option synthInstance.maxHeartbeats 100000 in
      simp [_root_.GlobalTheory.SnMass.VolN.rowE, vecMulVec_apply, vecMul, dotProduct, map_sum, hconj,
      one_apply, x, v]
      exact Matrix.one_apply.symm
  unfold _root_.GlobalTheory.SnMass.VolN.gM
  rw [hmap, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_one, hinv,
    mul_vecMulVec_mul_flag_measures, mul_vecMulVec_mul_flag_measures, hrow, hrow, mulVec_add, mulVec_smul, hAx]
  have hstar : star ((s a : ℂ) • _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a)) ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r =
      (s a : ℂ) • Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) 1 := by
    unfold _root_.Formalism.QuantumDeterminants.bvec
    rw [star_smul, ← Pi.single_star, star_one, smul_vecMul, single_vecMul_Hpk_eI, Complex.star_def,
      Complex.conj_ofReal]
  rw [hstar]
  unfold _root_.Formalism.QuantumDeterminants.herm _root_.Formalism.QuantumDeterminants.bvec
  rw [dotProduct_mulVec, dotProduct_single_one]
  simp only [Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, Matrix.one_apply]
  split_ifs <;> ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentBlockEntriesMulOfHasFlagDepthAtLeast
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LeftMul

theorem pos_eI (k r : ℕ) (a : Fin r) : pos k r (eI k r a) = a.val := by
  have := a.isLt
  unfold pos eI
  dsimp only
  split_ifs <;> omega

theorem pos_wI (k r : ℕ) (j : Fin (k + 1)) : pos k r (wI k r j) = r := by
  have := j.isLt
  unfold pos wI
  dsimp only
  split_ifs <;> omega

theorem pos_esI (k r : ℕ) (a : Fin r) : pos k r (esI k r a) = 2 * r - a.val := by
  have := a.isLt
  unfold pos esI
  dsimp only
  split_ifs <;> omega

theorem mul_apply_of_dep (k r d : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : Dep k r d (g - 1)) (hx : Dep k r 1 (x - 1)) (i j : Fin (2 * r + k + 1)) (hij : i ≠ j)
    (hp : pos k r j ≤ pos k r i + d) : (g * x) i j = g i j + x i j := by
  have h1 : g * x = (g - 1) * (x - 1) + (g - 1) + (x - 1) + 1 := by noncomm_ring
  have h2 : ((g - 1) * (x - 1)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : pos k r l < pos k r i + d
    · rw [hg i l hl, zero_mul]
    · rw [hx l j (by omega), mul_zero]
  rw [h1, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h2, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.one_apply_ne hij]
  ring

end GlobalTheory.SnMass.VolN.LeftMul

namespace GlobalTheory.SnMass.VolN


open GlobalTheory.SnMass.VolN.LeftMul in
theorem cM_mul_of_dep : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ),
    Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d →
      cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  intro k r g x d hg hx β hβ
  rcases β with p | a | p | a
  · have hlt : p.1.1.val < p.1.2.val := p.2
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (eI k r p.1.2) = x (eI k r p.1.1) (eI k r p.1.2) + g (eI k r p.1.1) (eI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI] at this; omega
    · rw [pos_eI, pos_eI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show (fun j => (g * x) (eI k r a) (wI k r j)) = (fun j => x (eI k r a) (wI k r j)) + (fun j => g (eI k r a) (wI k r j))
    funext l
    rw [Pi.add_apply, mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, wI] at this; omega
    · rw [pos_eI, pos_wI]; omega
  · have hlt : p.1.1.val < p.1.2.val := p.2
    have hb := p.1.2.isLt
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (esI k r p.1.2) = x (eI k r p.1.1) (esI k r p.1.2) + g (eI k r p.1.1) (esI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show ((g * x) (eI k r a) (esI k r a)).im = (x (eI k r a) (esI k r a)).im + (g (eI k r a) (esI k r a)).im
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, Complex.add_im, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega

end GlobalTheory.SnMass.VolN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelActionIsActionAndFaithful
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem det_embed_ne_zero {E : Type} [Field E] [NumberField E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (w : InfinitePlace E) : (J.map w.embedding).det ≠ 0 := by
  rw [show J.map w.embedding = w.embedding.mapMatrix J from rfl, ← RingHom.map_det]
  exact (map_ne_zero _).mpr hJ

theorem A_isUnit_det {E : Type} [Field E] [NumberField E] {k r : ℕ}
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hJ : J.det ≠ 0) (hA : IsModelAt J A) (w : InfinitePlace E) : IsUnit (A w).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h : ((A w)ᴴ * Hpk k r * A w).det = (J.map w.embedding).det := congrArg Matrix.det (hA w)
  rw [det_mul, det_mul, h0, mul_zero] at h
  exact det_embed_ne_zero J hJ w h.symm

theorem actLaws (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    IsVolData σ J Λ P f T A s → (∀ x, actM A 1 x = x) ∧ (∀ γ γ' x, actM A (γ * γ') x = actM A γ (actM A γ' x)) ∧ ∀ γ, (∀ w, gM A γ w = 1) → γ = 1 := by
  intro h
  have hJ : J.det ≠ 0 := h.2.2.1.2
  have hA : IsModelAt J A := h.2.2.2.2.2.2.2.1
  have hu : ∀ w, IsUnit (A w).det := fun w => A_isUnit_det J A hJ hA w
  refine ⟨?_, ?_, ?_⟩
  · intro x
    funext w
    have e : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E).map w.embedding = 1 :=
      map_one w.embedding.mapMatrix
    simp only [actM, e, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mul]
    rfl
  · intro γ γ' x
    funext w
    have e : (γ * γ').map w.embedding = γ.map w.embedding * γ'.map w.embedding :=
      map_mul w.embedding.mapMatrix γ γ'
    have m : A w * (γ.map w.embedding * γ'.map w.embedding) * (A w)⁻¹ * Matrix.of (x w) =
        A w * γ.map w.embedding * (A w)⁻¹ * (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w)) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
    show Matrix.of.symm (A w * (γ * γ').map w.embedding * (A w)⁻¹ * Matrix.of (x w)) =
      Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ *
        Matrix.of (Matrix.of.symm (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w))))
    rw [Equiv.apply_symm_apply, e, m]
  · intro γ hγ
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hi : (A w)⁻¹ * A w = 1 := Matrix.nonsing_inv_mul _ (hu w)
    have h1 : γ.map w.embedding = 1 := by
      have e : A w * γ.map w.embedding * (A w)⁻¹ = 1 := hγ w
      calc γ.map w.embedding = (A w)⁻¹ * (A w * γ.map w.embedding * (A w)⁻¹) * A w := by
            simp only [Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
        _ = 1 := by rw [e, Matrix.mul_one, hi]
    ext i j
    apply w.embedding.injective
    have := congrArg (fun M => M i j) h1
    simpa [Matrix.one_apply, apply_ite] using this

end GlobalTheory.SnMass.VolN
end
end

