module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousHPart
section
noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Real

variable {n r : ℕ} (ε : Fin n → Bool)

def RFrame (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Prop :=
  (∀ a b, hJ ε (e a) (e b) = 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
  (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) ∧ hJ ε z z ≠ 0

theorem rFrame_of {I : Formalism.MainNotions.S.AutInst} {r : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E}
    (hF : IsFrame I e f z) (v : NumberField.InfinitePlace I.F) :
    RFrame (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [rv_hJ, h1, map_zero]
  · rw [rv_hJ, h2, map_zero]
  · rw [rv_hJ, h3]; split_ifs <;> simp
  · rw [rv_hJ, (h4 a).1, map_zero]
  · rw [rv_hJ, (h4 a).2, map_zero]
  · rw [rv_hJ]
    exact fun h => h5 ((map_eq_zero_iff _ (I.φ v).injective).mp h)

def hJL (u : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun := hJ ε u
  map_add' x y := by simp [hJ, Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

theorem hJL_apply (u x : Fin n → ℂ) : hJL ε u x = hJ ε u x := rfl

def piW (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.id - ∑ a, (hJL ε (f a)).smulRight (e a) - ∑ a, (hJL ε (e a)).smulRight (f a) -
    ((hJ ε z z)⁻¹ • hJL ε z).smulRight z

theorem piW_apply (e f : Fin r → Fin n → ℂ) (z x : Fin n → ℂ) :
    piW ε e f z x = x - ∑ a, hJ ε (f a) x • e a - ∑ a, hJ ε (e a) x • f a -
      ((hJ ε z z)⁻¹ * hJ ε z x) • z := by
  simp [piW, hJL_apply, smul_eq_mul, mul_comm]

variable {ε}

theorem hJ_sub_right (u x y : Fin n → ℂ) : hJ ε u (x - y) = hJ ε u x - hJ ε u y := by
  simp [hJ, Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_sum_right {ι : Type*} (s : Finset ι) (u : Fin n → ℂ) (g : ι → Fin n → ℂ) :
    hJ ε u (∑ i ∈ s, g i) = ∑ i ∈ s, hJ ε u (g i) := by
  exact map_sum (hJL ε u) g s

theorem hJ_smul_right (u x : Fin n → ℂ) (c : ℂ) : hJ ε u (c • x) = c * hJ ε u x := by
  simp [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

variable {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}

theorem hJ_e_piW (hF : RFrame ε e f z) (b : Fin r) (x : Fin n → ℂ) : hJ ε (e b) (piW ε e f z x) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  rw [piW_apply]
  simp only [hJ_sub_right, hJ_sum_right, hJ_smul_right, hee, hef, (hz b).1]
  simp

private theorem hJ_conj_lemma (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  unfold hJ
  simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem hJ_f_piW (hF : RFrame ε e f z) (b : Fin r) (x : Fin n → ℂ) : hJ ε (f b) (piW ε e f z x) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  have h1 : ∀ a, hJ ε (f b) (e a) = if a = b then 1 else 0 := fun a => by
    rw [hJ_conj_lemma, hef a b]
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  rw [piW_apply]
  simp only [hJ_sub_right, hJ_sum_right, hJ_smul_right, hff, h1, (hz b).2]
  simp

theorem hJ_z_piW (hF : RFrame ε e f z) (x : Fin n → ℂ) : hJ ε z (piW ε e f z x) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  have h1 : ∀ a, hJ ε z (e a) = 0 := fun a => by rw [hJ_conj_lemma, (hz a).1, star_zero]
  have h2 : ∀ a, hJ ε z (f a) = 0 := fun a => by rw [hJ_conj_lemma, (hz a).2, star_zero]
  rw [piW_apply]
  simp only [hJ_sub_right, hJ_sum_right, hJ_smul_right, h1, h2, mul_zero, Finset.sum_const_zero, sub_zero]
  field_simp
  ring

theorem piW_of_perp {y : Fin n → ℂ} (he : ∀ a, hJ ε (e a) y = 0) (hf : ∀ a, hJ ε (f a) y = 0)
    (hz : hJ ε z y = 0) : piW ε e f z y = y := by
  rw [piW_apply]
  simp [he, hf, hz]

theorem piW_e (hF : RFrame ε e f z) (b : Fin r) : piW ε e f z (e b) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  have h1 : ∀ a, hJ ε (f a) (e b) = if a = b then 1 else 0 := fun a => by
    rw [hJ_conj_lemma, hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have h2 : hJ ε z (e b) = 0 := by rw [hJ_conj_lemma, (hz b).1, star_zero]
  rw [piW_apply]
  simp [h1, hee, h2]

theorem piW_spanLt (hF : RFrame ε e f z) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) :
    piW ε e f z x = 0 := by
  have hle : spanLt e a ≤ LinearMap.ker (piW ε e f z) := by
    rw [spanLt, Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact LinearMap.mem_ker.mpr (piW_e hF b)
  exact LinearMap.mem_ker.mp (hle hx)

theorem fix_sub_piW {h : Matrix (Fin n) (Fin n) ℂ} (he : ∀ a, h *ᵥ e a = e a)
    (hf : ∀ a, h *ᵥ f a = f a) (hz : h *ᵥ z = z) (x : Fin n → ℂ) :
    h *ᵥ (x - piW ε e f z x) = x - piW ε e f z x := by
  have hx : x - piW ε e f z x = ∑ a, hJ ε (f a) x • e a + ∑ a, hJ ε (e a) x • f a +
      ((hJ ε z z)⁻¹ * hJ ε z x) • z := by
    rw [piW_apply]; abel
  rw [hx]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, he, hf, hz]

def PwM (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (piW ε e f z)

def hPart (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 - PwM ε e f z + PwM ε e f z * g * PwM ε e f z

theorem continuous_hPart (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    Continuous (hPart ε e f z) := by
  unfold hPart
  fun_prop

theorem hPart_mulVec (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    hPart ε e f z g *ᵥ x = x - piW ε e f z x + piW ε e f z (g *ᵥ piW ε e f z x) := by
  have hP : ∀ y, PwM ε e f z *ᵥ y = piW ε e f z y := fun y => by
    rw [PwM, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  simp only [hPart, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hP]

private theorem hJ_mulVec_of_inUJ' {h : Matrix (Fin n) (Fin n) ℂ} (hU : Formalism.REAL.inUJ ε h) (u v : Fin n → ℂ) :
    hJ ε (h *ᵥ u) (h *ᵥ v) = hJ ε u v := by
  unfold Formalism.REAL.inUJ at hU
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

theorem hPart_mul (hF : RFrame ε e f z) {nm h : Matrix (Fin n) (Fin n) ℂ} (hn : InN ε e z nm)
    (hU : Formalism.REAL.inUJ ε h) (he : ∀ a, h *ᵥ e a = e a) (hf : ∀ a, h *ᵥ f a = f a) (hz : h *ᵥ z = z) :
    hPart ε e f z (nm * h) = h := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hPart_mulVec]
  have hey : ∀ a, hJ ε (e a) (h *ᵥ piW ε e f z x) = 0 := fun a => by
    have := hJ_mulVec_of_inUJ' hU (e a) (piW ε e f z x)
    rw [he a] at this
    rw [this]; exact hJ_e_piW hF a x
  have hfy : ∀ a, hJ ε (f a) (h *ᵥ piW ε e f z x) = 0 := fun a => by
    have := hJ_mulVec_of_inUJ' hU (f a) (piW ε e f z x)
    rw [hf a] at this
    rw [this]; exact hJ_f_piW hF a x
  have hzy : hJ ε z (h *ᵥ piW ε e f z x) = 0 := by
    have := hJ_mulVec_of_inUJ' hU z (piW ε e f z x)
    rw [hz] at this
    rw [this]; exact hJ_z_piW hF x
  have h0 : piW ε e f z ((nm - 1) *ᵥ (h *ᵥ piW ε e f z x)) = 0 :=
    piW_spanLt hF r (hn.2 _ hey)
  have hpy : piW ε e f z (h *ᵥ piW ε e f z x) = h *ᵥ piW ε e f z x := piW_of_perp hey hfy hzy
  have hsplit : (nm * h) *ᵥ piW ε e f z x =
      h *ᵥ piW ε e f z x + (nm - 1) *ᵥ (h *ᵥ piW ε e f z x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hx : h *ᵥ x = (x - piW ε e f z x) + h *ᵥ piW ε e f z x := by
    rw [← fix_sub_piW he hf hz x, ← Matrix.mulVec_add, sub_add_cancel]
  rw [hsplit, map_add (f := _), hpy, h0, add_zero, hx]

end Real

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.FrameGramInstance
section
noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem gram_entry (I : Formalism.MainNotions.S.AutInst) (v : NumberField.InfinitePlace I.F) {r : ℕ}
    (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (j k : Fin r ⊕ Fin r ⊕ Unit) :
    ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z) j k =
      hJ (I.ε v) (rv I v (instFvec e f z j)) (rv I v (instFvec e f z k)) := by
  unfold instBmat hJ
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum]

theorem frame_gram_instance : InstFrameGram := by
  intro I r e f z hF v
  obtain ⟨hee, hff, hef, hz, hzz⟩ := rv_frame (I := I) hF v
  have hJH : (Formalism.REAL.Jm (I.ε v))ᴴ = Formalism.REAL.Jm (I.ε v) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : I.ε v a <;> simp [h]
  have hH : ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z)ᴴ =
      (instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH, Matrix.mul_assoc]
  have hent := gram_entry I v e f z
  generalize (instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z = G at hH hent ⊢
  have hS : ∀ j k, G j k = star (G k j) := by
    intro j k
    have hjk := congrFun (congrFun hH j) k
    rw [Matrix.conjTranspose_apply] at hjk
    exact hjk.symm
  have h1 : ∀ a b, G (Sum.inl a) (Sum.inl b) = 0 := fun a b => by rw [hent]; exact hee a b
  have h3 : ∀ a b, G (Sum.inl a) (Sum.inr (Sum.inl b)) = if a = b then 1 else 0 :=
    fun a b => by rw [hent]; exact hef a b
  have h4 : ∀ a (u : Unit), G (Sum.inl a) (Sum.inr (Sum.inr u)) = 0 :=
    fun a u => by rw [hent]; exact (hz a).1
  have h5 : ∀ a (u : Unit), G (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr u)) = 0 :=
    fun a u => by rw [hent]; exact (hz a).2
  have h3' : ∀ a b, G (Sum.inr (Sum.inl a)) (Sum.inl b) = if b = a then 1 else 0 := by
    intro a b
    rw [hS, h3]
    split_ifs <;> simp
  have h4' : ∀ a (u : Unit), G (Sum.inr (Sum.inr u)) (Sum.inl a) = 0 := by
    intro a u
    rw [hS, h4, star_zero]
  have h5' : ∀ a (u : Unit), G (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inl a)) = 0 := by
    intro a u
    rw [hS, h5, star_zero]
  have h6 : ∀ u u' : Unit, G (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inr u')) ≠ 0 := by
    intro u u'
    rw [hent]
    exact hzz
  have hker : ∀ w, G *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hf : ∀ a, w (Sum.inr (Sum.inl a)) = 0 := by
      intro a
      have := congrFun hw (Sum.inl a)
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h1, h3, h4] using this
    have he : ∀ a, w (Sum.inl a) = 0 := by
      intro a
      have := congrFun hw (Sum.inr (Sum.inl a))
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h3', h5, hf] using this
    have hzw : ∀ u : Unit, w (Sum.inr (Sum.inr u)) = 0 := by
      intro u
      have := congrFun hw (Sum.inr (Sum.inr u))
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h4', h5', zero_mul,
        Finset.sum_const_zero, zero_add, Pi.zero_apply] at this
      rw [Fintype.sum_unique] at this
      rcases (mul_eq_zero.mp this) with h | h
      · exact absurd h (h6 _ _)
      · cases u
        exact h
    funext j
    rcases j with a | a | u
    · exact he a
    · exact hf a
    · exact hzw u
  refine Matrix.mulVec_injective_iff_isUnit.mp ?_
  intro w₁ w₂ h
  have h0 : G *ᵥ (w₁ - w₂) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (hker _ h0)

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAdapt
section
noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem inst_gram_entry {n : ℕ} (X J Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Xᴴ * J * Y) a b = ∑ s, ∑ r, star (X r a) * J r s * Y s b := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]

theorem inst_sign_real (l : ℝ) (hl : l ≠ 0) :
    (Real.sqrt |l|)⁻¹ * l * (Real.sqrt |l|)⁻¹ = if 0 < l then 1 else -1 := by
  have hpos : 0 < |l| := abs_pos.mpr hl
  have hs : Real.sqrt |l| * Real.sqrt |l| = |l| := Real.mul_self_sqrt hpos.le
  have h1 : (Real.sqrt |l|)⁻¹ * l * (Real.sqrt |l|)⁻¹ = l / |l| := by
    calc (Real.sqrt |l|)⁻¹ * l * (Real.sqrt |l|)⁻¹ = l * (Real.sqrt |l| * Real.sqrt |l|)⁻¹ := by
          rw [mul_inv]; ring
      _ = l / |l| := by rw [hs, div_eq_mul_inv]
  rw [h1]
  split_ifs with h
  · rw [abs_of_pos h, div_self hl]
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hl), div_neg, div_self hl]

theorem inst_rank_add_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) : (X + Y).rank ≤ X.rank + Y.rank := by
  first
    | exact Matrix.rank_add_le X Y
    | (unfold Matrix.rank
       rw [Matrix.mulVecLin_add]
       exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
         (Submodule.finrank_add_le_finrank_add_finrank _ _))

private theorem exists_unitary_diagonal_of_isHermitian {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), star U * U = 1 ∧ U * star U = 1 ∧
      X = U * diagonal (fun i => (d i : ℂ)) * star U := by
  have h1 : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.1
      | exact (Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2)
      | exact Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have h2 : (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.2
      | exact (Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2)
      | exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  refine ⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_⟩
  first
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def]
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def, Unitary.conjStarAlgAut_apply]
    | (have h3 := hX.star_mul_self_mul_eq_diagonal
       calc X = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              (star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * X *
                (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) *
              star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
             simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
             rw [Matrix.mul_assoc, h2, Matrix.mul_one]
         _ = _ := by rw [h3]; simp [Function.comp_def])

theorem inst_qfamily {n : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ) (hQQ : Q * Q = Q)
    (hQJ : Qᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Q) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ),
      Wᴴ * Formalism.REAL.Jm ε * W =
        diagonal (fun i => if lam i = 0 then (0 : ℂ) else if 0 < lam i then 1 else -1) ∧
      Q * W = W ∧
      (∀ x : Fin n → ℂ, Q *ᵥ x = x → ∃ y : Fin n → ℂ, (∀ i, lam i = 0 → y i = 0) ∧ x = W *ᵥ y) ∧
      Fintype.card {i // lam i ≠ 0} = Q.rank ∧
      ∃ (U : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℂ), W = Q * U * diagonal s := by
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJs : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  set J := Formalism.REAL.Jm ε with hJdef
  have hQJQ : Qᴴ * J * Q = J * Q := by rw [hQJ, Matrix.mul_assoc, hQQ]
  have hMh : (Qᴴ * J * Q).IsHermitian := by
    show (Qᴴ * J * Q)ᴴ = Qᴴ * J * Q
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJs,
      Matrix.mul_assoc]
  obtain ⟨V, μ, hVV, hVV', hM⟩ := exists_unitary_diagonal_of_isHermitian (Qᴴ * J * Q) hMh
  rw [hQJQ] at hM
  set s : Fin n → ℂ := fun i => if μ i = 0 then 0 else (((Real.sqrt |μ i|)⁻¹ : ℝ) : ℂ) with hsdef
  refine ⟨Q * V * diagonal s, μ, ?_, ?_, ?_, ?_, V, s, rfl⟩
  · have hD : star V * (J * Q) * V = diagonal (fun i => (μ i : ℂ)) := by
      rw [hM]
      calc star V * (V * diagonal (fun i => (μ i : ℂ)) * star V) * V
          = (star V * V) * diagonal (fun i => (μ i : ℂ)) * (star V * V) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hVV, Matrix.one_mul, Matrix.mul_one]
    have h1 : (Q * V * diagonal s)ᴴ * J * (Q * V * diagonal s) =
        (diagonal s)ᴴ * (star V * (Qᴴ * J * Q) * V) * diagonal s := by
      simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [h1, hQJQ, hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hμ : μ i = 0
    · simp [hsdef, hμ]
    · have hsr := inst_sign_real (μ i) hμ
      have hc : star (s i) * (μ i : ℂ) * s i =
          (((Real.sqrt |μ i|)⁻¹ * μ i * (Real.sqrt |μ i|)⁻¹ : ℝ) : ℂ) := by
        simp only [hsdef, hμ, if_false, Complex.star_def, Complex.conj_ofReal]
        first
          | (push_cast; ring)
          | push_cast
      simp only [Pi.star_apply]
      rw [hc, hsr, if_neg hμ]
      split_ifs <;> simp
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ]
  · intro x hx
    obtain ⟨z, hz⟩ : ∃ z : Fin n → ℂ, z = star V *ᵥ x := ⟨_, rfl⟩
    obtain ⟨w2, hw2⟩ : ∃ w2 : Fin n → ℂ, w2 = fun i => if μ i = 0 then z i else 0 := ⟨_, rfl⟩
    refine ⟨fun i => if μ i = 0 then 0 else (Real.sqrt |μ i| : ℂ) * z i, fun i hi => by simp [hi], ?_⟩
    have hVz : V *ᵥ z = x := by rw [hz, Matrix.mulVec_mulVec, hVV', Matrix.one_mulVec]
    have h1 : (J * Q) *ᵥ (V *ᵥ w2) = 0 := by
      rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec w2 (star V) V, hVV,
        Matrix.one_mulVec]
      have h2 : diagonal (fun i => (μ i : ℂ)) *ᵥ w2 = 0 := by
        funext i
        rw [Matrix.mulVec_diagonal, hw2]
        by_cases hμ : μ i = 0 <;> simp [hμ]
      rw [h2, Matrix.mulVec_zero]
    have hkill : Q *ᵥ (V *ᵥ w2) = 0 := by
      calc Q *ᵥ (V *ᵥ w2) = (J * J * Q) *ᵥ (V *ᵥ w2) := by rw [hJJ, Matrix.one_mul]
        _ = J *ᵥ ((J * Q) *ᵥ (V *ᵥ w2)) := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = 0 := by rw [h1, Matrix.mulVec_zero]
    have hSy : diagonal s *ᵥ (fun i => if μ i = 0 then 0 else (Real.sqrt |μ i| : ℂ) * z i) =
        fun i => if μ i = 0 then 0 else z i := by
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hμ : μ i = 0
      · simp [hμ]
      · have hpos : 0 < Real.sqrt |μ i| := Real.sqrt_pos.mpr (abs_pos.mpr hμ)
        simp only [hsdef, hμ, if_false]
        rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
    have hsplit : z = (fun i => if μ i = 0 then 0 else z i) + w2 := by
      funext i
      rw [hw2]
      simp only [Pi.add_apply]
      split_ifs <;> simp
    calc x = Q *ᵥ x := hx.symm
      _ = Q *ᵥ (V *ᵥ z) := by rw [hVz]
      _ = Q *ᵥ (V *ᵥ (fun i => if μ i = 0 then 0 else z i)) + Q *ᵥ (V *ᵥ w2) := by
          conv_lhs => rw [hsplit]
          rw [Matrix.mulVec_add, Matrix.mulVec_add]
      _ = Q *ᵥ (V *ᵥ (fun i => if μ i = 0 then 0 else z i)) := by rw [hkill, add_zero]
      _ = (Q * V * diagonal s) *ᵥ
            (fun i => if μ i = 0 then 0 else (Real.sqrt |μ i| : ℂ) * z i) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSy]
  · have hrk1 : (J * Q).rank = Q.rank :=
      Matrix.rank_mul_eq_right_of_isUnit_det J Q (Matrix.isUnit_det_of_left_inverse hJJ)
    have hVunit : IsUnit V.det := Matrix.isUnit_det_of_left_inverse hVV
    have hsVunit : IsUnit (star V).det := Matrix.isUnit_det_of_left_inverse hVV'
    rw [← hrk1, hM, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hsVunit,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVunit, Matrix.rank_diagonal]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => Complex.ofReal_ne_zero.symm)

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

