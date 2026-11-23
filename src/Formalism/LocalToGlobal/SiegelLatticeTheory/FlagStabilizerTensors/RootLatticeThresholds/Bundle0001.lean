module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsGA
section
noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsGA

variable {G : Type} [Group G] [Fintype G]

theorem coeff_mul_fin (a b : MonoidAlgebra ℂ G) (g : G) :
    (a * b).coeff g = ∑ h : G, a.coeff h * b.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]

theorem central_of_class (a : MonoidAlgebra ℂ G) (h : ∀ g P : G, a.coeff (P⁻¹ * g * P) = a.coeff g)
    (y : MonoidAlgebra ℂ G) : a * y = y * a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [coeff_mul_fin, coeff_mul_fin]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight g)) _ _ fun k => ?_
  have e1 : (k⁻¹ * g)⁻¹ * g = g⁻¹ * k * g := by group
  show a.coeff k * y.coeff (k⁻¹ * g) = y.coeff (k⁻¹ * g) * a.coeff ((k⁻¹ * g)⁻¹ * g)
  rw [e1, h k g]
  exact mul_comm _ _

def conjA (a : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => star (a.coeff g⁻¹))

theorem conjA_coeff (a : MonoidAlgebra ℂ G) (g : G) : (conjA a).coeff g = star (a.coeff g⁻¹) := by
  simp [conjA, MonoidAlgebra.coeff_ofCoeff]

theorem conjA_conjA (a : MonoidAlgebra ℂ G) : conjA (conjA a) = a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [conjA_coeff, conjA_coeff, inv_inv, star_star]

theorem conjA_mul (a b : MonoidAlgebra ℂ G) : conjA (a * b) = conjA b * conjA a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [conjA_coeff, coeff_mul_fin, coeff_mul_fin, star_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  have e1 : ((g * h)⁻¹ * g)⁻¹ = h := by group
  have e2 : (g * h)⁻¹ = h⁻¹ * g⁻¹ := mul_inv_rev g h
  show star (a.coeff h * b.coeff (h⁻¹ * g⁻¹)) =
    (conjA b).coeff (g * h) * (conjA a).coeff ((g * h)⁻¹ * g)
  rw [conjA_coeff, conjA_coeff, e1, e2, star_mul']
  exact mul_comm _ _

theorem conjA_sub (a b : MonoidAlgebra ℂ G) : conjA (a - b) = conjA a - conjA b := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  simp [conjA_coeff, MonoidAlgebra.coeff_sub, star_sub]

private theorem eq_zero_of_conjA_mul_self_eq_zero (x : MonoidAlgebra ℂ G) (hx : conjA x * x = 0) :
    x = 0 := by
  have h1 := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff 1) hx
  simp only [coeff_mul_fin, conjA_coeff, mul_one, MonoidAlgebra.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply] at h1
  have h2 : ∑ h : G, ((Complex.normSq (x.coeff h⁻¹) : ℝ) : ℂ) = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h2
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun h _ => Complex.normSq_nonneg (x.coeff h⁻¹))).mp h2
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  have h4 := h3 g⁻¹ (Finset.mem_univ _)
  rw [inv_inv, Complex.normSq_eq_zero] at h4
  simpa using h4

private theorem eq_mul_of_commuting_idempotents_conjA_swap (e f : MonoidAlgebra ℂ G) (hef : conjA e = f)
    (hfe : conjA f = e) (he : e * e = e) (hf : f * f = f) (hc : f * e = e * f) :
    e = e * f := by
  have hx : conjA (e - e * f) * (e - e * f) = 0 := by
    rw [conjA_sub, conjA_mul, hef, hfe]
    have h1 : f * (e * f) = e * f := by rw [← mul_assoc, hc, mul_assoc, hf]
    have h2 : e * f * e = e * f := by rw [mul_assoc, hc, ← mul_assoc, he]
    have h3 : e * f * (e * f) = e * f := by rw [← mul_assoc, h2, mul_assoc, hf]
    rw [sub_mul, mul_sub, mul_sub, h1, h3, h2, hc]
    simp
  exact sub_eq_zero.mp (eq_zero_of_conjA_mul_self_eq_zero _ hx)

theorem selfadj_of_central_idem (e : MonoidAlgebra ℂ G) (hid : e * e = e) (hc : ∀ y, e * y = y * e) :
    conjA e = e := by
  have hff : conjA e * conjA e = conjA e := by rw [← conjA_mul, hid]
  have h1 := eq_mul_of_commuting_idempotents_conjA_swap e (conjA e) rfl (conjA_conjA e) hid hff
    (hc (conjA e)).symm
  have h2 := eq_mul_of_commuting_idempotents_conjA_swap (conjA e) e (conjA_conjA e) rfl hff hid
    (hc (conjA e))
  calc conjA e = conjA e * e := h2
    _ = e * conjA e := (hc _).symm
    _ = e := h1.symm

end Formalism.L2.SG.Pf.AllRowsGA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PiMeasureScaling
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.PiMeasureScaling

theorem sf_smul (c : ℝ≥0∞) (hc : c ≠ ⊤) : SigmaFinite (c • (volume : Measure ℂ)) := by
  lift c to NNReal using hc
  first
  | exact (inferInstance : SigmaFinite (c • (volume : Measure ℂ)))
  | (rw [← ENNReal.smul_def]; infer_instance)

theorem pi_smul_vol {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • (volume : Measure ℂ)) = (∏ i, c i) • (volume : Measure (ι → ℂ)) := by
  haveI : ∀ i, SigmaFinite (c i • (volume : Measure ℂ)) := fun i => sf_smul (c i) (hc i)
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, volume_pi_pi, ← Finset.prod_mul_distrib]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem map_scale (s : ℂ) (hs : s ≠ 0) :
    (volume : Measure ℂ).map (fun z => s * z) = ENNReal.ofReal (Complex.normSq s)⁻¹ • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ s) = Complex.normSq s := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hpos : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ s) (by rw [hdet]; exact hpos.ne')
  rw [hdet, abs_of_pos (inv_pos.mpr hpos)] at h
  exact h

theorem reindex_mp {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    MeasurePreserving (fun (y : κ → ℂ) (i : ι) => y (e i)) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : ι => ℂ) e.symm
  have hf : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) e.symm)) =
      fun (y : κ → ℂ) (i : ι) => y (e i) := by
    funext y i
    have h1 := MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => ℂ) y (e i)
    simpa using h1
  rw [hf] at h
  exact h

theorem pi_reindex_scale {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (a : ℝ≥0∞) (ha : a ≠ ⊤) (s : ι → ℂ) (hs : ∀ i, s i ≠ 0) :
    (Measure.pi (fun _ : κ => a • (volume : Measure ℂ))).map (fun y i => s i * y (e i)) =
      (∏ i, a * ENNReal.ofReal (Complex.normSq (s i))⁻¹) • (volume : Measure (ι → ℂ)) := by
  classical
  have hk : Measure.pi (fun _ : κ => a • (volume : Measure ℂ)) =
      (∏ _k : κ, a) • (volume : Measure (κ → ℂ)) := pi_smul_vol (fun _ => a) (fun _ => ha)
  have hsc : (volume : Measure (ι → ℂ)).map (fun x i => s i * x i) =
      (∏ i, ENNReal.ofReal (Complex.normSq (s i))⁻¹) • (volume : Measure (ι → ℂ)) := by
    haveI : ∀ i, SigmaFinite (Measure.map (fun x => s i * x) (volume : Measure ℂ)) := fun i => by
      rw [map_scale _ (hs i)]
      exact sf_smul _ ENNReal.ofReal_ne_top
    rw [volume_pi, Measure.pi_map_pi (fun i => (measurable_const_mul (s i)).aemeasurable)]
    simp_rw [map_scale _ (hs _)]
    rw [pi_smul_vol _ (fun i => ENNReal.ofReal_ne_top), volume_pi]
  have hscale : Measurable (fun (x : ι → ℂ) (i : ι) => s i * x i) :=
    Measurable.of_eval fun i => by fun_prop
  have htotal : AEMeasurable (fun (y : κ → ℂ) (i : ι) => s i * y (e i)) volume := by
    exact (hscale.comp (reindex_mp e).measurable).aemeasurable
  have hcomp : (fun (y : κ → ℂ) (i : ι) => s i * y (e i)) =
      (fun (x : ι → ℂ) i => s i * x i) ∘ (fun (y : κ → ℂ) (i : ι) => y (e i)) := rfl
  rw [hk, Measure.map_smul _ htotal, hcomp,
    ← Measure.map_map (Measurable.of_eval fun i => (measurable_pi_apply i).const_mul (s i))
      (reindex_mp e).measurable, (reindex_mp e).map_eq, hsc, smul_smul]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_congr e]

end Formalism.L2.SG.PiMeasureScaling

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RConvFExistsPfAbs
section
noncomputable section

namespace Formalism.L2.SG.Pf.RConvFExistsPf

open MeasureTheory
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem wk_integrable {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ)
    (x y : E) : Integrable (fun g => f g * ⟪x, U g y⟫_ℂ) μ := by
  refine (hf.norm.mul_const (‖x‖ * ‖y‖)).mono' (hf.aestronglyMeasurable.mul (hm x y))
    (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_inner_le_norm x (U g y)).trans (mul_le_mul_of_nonneg_left (hU g y) (norm_nonneg x))) (norm_nonneg _)

theorem wk_bound {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖) {f : α → ℂ} (hf : Integrable f μ)
    (x y : E) : ‖∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖x‖ * ‖y‖ := by
  calc ‖∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ‖ ≤ ∫ g, ‖f g‖ * (‖x‖ * ‖y‖) ∂μ := by
        refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          ((norm_inner_le_norm x (U g y)).trans (mul_le_mul_of_nonneg_left (hU g y) (norm_nonneg x)))
          (norm_nonneg _)
    _ = (∫ g, ‖f g‖ ∂μ) * ‖x‖ * ‖y‖ := by rw [integral_mul_const, mul_assoc]

def wkForm {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ) :
    E →L⋆[ℂ] E →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ)
      (fun x₁ x₂ y => by
        simp only [inner_add_left, mul_add]
        exact integral_add (wk_integrable hU hm hf x₁ y) (wk_integrable hU hm hf x₂ y))
      (fun c x y => by
        simp only [inner_smul_left, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; funext g; ring)
      (fun x y₁ y₂ => by
        simp only [map_add (f := _), inner_add_right, mul_add]
        exact integral_add (wk_integrable hU hm hf x y₁) (wk_integrable hU hm hf x y₂))
      (fun c x y => by
        simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring))
    (∫ g, ‖f g‖ ∂μ) (fun x y => wk_bound hU hf x y)

theorem wk_exists {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ) :
    ∃ T : E →L[ℂ] E, ∀ x y : E, ⟪x, T y⟫_ℂ = ∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ := by
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin (wkForm hU hm hf)),
    fun x y => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

end Formalism.L2.SG.Pf.RConvFExistsPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RankUpdateMul
section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]

def Ymat (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) : Matrix n n ℂ :=
  1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J

theorem rankUpdate_mul (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (hΓ : IsUnit (Wᴴ * J * W).det) :
    Ymat J W M * W = W * (1 + M) := by
  have hinv : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  unfold Ymat
  calc (1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J) * W
        = W + W * M * ((Wᴴ * J * W)⁻¹ * (Wᴴ * J * W)) := by
          simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = W * (1 + M) := by rw [hinv, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one]

theorem Ymat_sub (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (x : n → ℂ) :
    Ymat J W M *ᵥ x - x = W *ᵥ (M *ᵥ ((Wᴴ * J * W)⁻¹ *ᵥ ((Wᴴ * J) *ᵥ x))) := by
  unfold Ymat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem Ymat_unitary (J : Matrix n n ℂ) (hJ : Jᴴ = J) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ)
    (hΓ : IsUnit (Wᴴ * J * W).det) (hM : (1 + M)ᴴ * (Wᴴ * J * W) * (1 + M) = Wᴴ * J * W) :
    (Ymat J W M)ᴴ * J * Ymat J W M = J := by
  have hGh : (Wᴴ * J * W)ᴴ = Wᴴ * J * W := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
      Matrix.mul_assoc]
  have hGi1 : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  have hGi2 : (Wᴴ * J * W) * (Wᴴ * J * W)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΓ
  have hGih : ((Wᴴ * J * W)⁻¹)ᴴ = (Wᴴ * J * W)⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  unfold Ymat
  set G := Wᴴ * J * W with hG
  set Gi := G⁻¹ with hGi

  have hK : G * M + Mᴴ * G + Mᴴ * G * M = 0 := by
    have h' := hM
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one] at h'
    have e : (1 + Mᴴ) * G * (1 + M) = G + (G * M + Mᴴ * G + Mᴴ * G * M) := by noncomm_ring
    rw [e] at h'
    exact add_eq_left.1 h'
  have hbr : M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi = 0 := by
    calc M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi
        = Gi * G * M * Gi + Gi * Mᴴ * (G * Gi) + Gi * Mᴴ * G * M * Gi := by
          rw [hGi1, hGi2]
          noncomm_ring
      _ = Gi * (G * M + Mᴴ * G + Mᴴ * G * M) * Gi := by noncomm_ring
      _ = 0 := by rw [hK]; noncomm_ring
  have key : J * W * (M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi) * Wᴴ * J = 0 := by
    rw [hbr]
    simp
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJ, hGih]
  refine Eq.trans ?_ (add_zero J)
  rw [← key]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hG]
  abel

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TensInt
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.WuDec

section Tens

variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vπ : Type} [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ] {tens : (∀ v, V v) → Vπ}

theorem norm_tens (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) :
    ‖tens x‖ = ∏ v, ‖x v‖ := by
  have h := hi x x
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖tens x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
    rw [← Finset.prod_pow]
    exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (tens x)), h2,
    Real.sqrt_sq (Finset.prod_nonneg fun v _ => norm_nonneg (x v))]

theorem norm_sub_tens_sq (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x y : ∀ v, V v) :
    ‖tens x - tens y‖ ^ 2 = RCLike.re ((∏ v, ⟪x v, x v⟫_ℂ) - (∏ v, ⟪x v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) +
      (∏ v, ⟪y v, y v⟫_ℂ)) := by
  have e := inner_self_eq_norm_sq (𝕜 := ℂ) (tens x - tens y)
  rw [← e, inner_sub_left, inner_sub_right, inner_sub_right, hi, hi, hi, hi]
  congr 1
  ring

theorem continuous_tens [∀ v, FiniteDimensional ℂ (V v)] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) :
    Continuous tens := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have p : ∀ v, Continuous fun y : (∀ v, V v) => y v := fun v => _root_.continuous_apply v
  have hF : Continuous fun y : (∀ v, V v) => RCLike.re ((∏ v, ⟪y v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) -
      (∏ v, ⟪x v, y v⟫_ℂ) + (∏ v, ⟪x v, x v⟫_ℂ)) := by
    refine RCLike.continuous_re.comp
      (Continuous.add (Continuous.sub (Continuous.sub ?_ ?_) ?_) continuous_const)
    · exact continuous_finsetProd _ fun v _ => (p v).inner (p v)
    · exact continuous_finsetProd _ fun v _ => (p v).inner continuous_const
    · exact continuous_finsetProd _ fun v _ => continuous_const.inner (p v)
  have h2 : Filter.Tendsto (fun y => ‖tens y - tens x‖ ^ 2) (nhds x) (nhds 0) := by
    have e : (fun y => ‖tens y - tens x‖ ^ 2) = fun y : (∀ v, V v) =>
        RCLike.re ((∏ v, ⟪y v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) - (∏ v, ⟪x v, y v⟫_ℂ) +
          (∏ v, ⟪x v, x v⟫_ℂ)) :=
      funext fun y => norm_sub_tens_sq hi y x
    rw [e]
    convert hF.tendsto x using 2
    simp
  have h3 := h2.sqrt
  simp only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at h3
  exact h3

theorem tens_smul (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (c : ι → ℂ) (x : ∀ v, V v) :
    tens (fun v => c v • x v) = (∏ v, c v) • tens x := by
  have key : ⟪tens (fun v => c v • x v) - (∏ v, c v) • tens x,
      tens (fun v => c v • x v) - (∏ v, c v) • tens x⟫_ℂ = 0 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hi,
      Finset.prod_mul_distrib, map_prod]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp key)

theorem inner_tens_update [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (ξ : ∀ v, V v)
    (v : ι) (a b : V v) :
    ⟪tens (Function.update ξ v a), tens (Function.update ξ v b)⟫_ℂ =
      ⟪a, b⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ := by
  rw [hi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw), Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem tens_update_inj [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (ξ : ∀ v, V v)
    (v : ι) (hne : ∀ w, w ≠ v → ξ w ≠ 0) (a b : V v)
    (h : tens (Function.update ξ v a) = tens (Function.update ξ v b)) : a = b := by
  have hP : ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro w hw
    exact inner_self_ne_zero.mpr (hne w (Finset.ne_of_mem_erase hw))
  have e : ∀ p q : V v, ⟪tens (Function.update ξ v p), tens (Function.update ξ v q)⟫_ℂ =
      ⟪p, q⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ :=
    fun p q => inner_tens_update hi ξ v p q
  have h0 : ⟪tens (Function.update ξ v a) - tens (Function.update ξ v b),
      tens (Function.update ξ v a) - tens (Function.update ξ v b)⟫_ℂ = 0 := by
    rw [h, sub_self, inner_zero_left]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, e, e, e, e] at h0
  have key : ⟪a - b, a - b⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    linear_combination h0
  exact sub_eq_zero.mp (inner_self_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hP))

end Tens

theorem integrable_and_integral_pi_apply :
  ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ v, MeasurableSpace (X v)] (μ : ∀ v, Measure (X v))
    [∀ v, SigmaFinite (μ v)] (V : ι → Type) [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
    [∀ v, FiniteDimensional ℂ (V v)] (Vπ : Type) [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ]
    [FiniteDimensional ℂ Vπ] (tens : (∀ v, V v) → Vπ),
    (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ →
    ∀ G : ∀ v, X v → V v, (∀ v, Integrable (G v) (μ v)) →
      Integrable (fun y : ∀ v, X v => tens (fun v => G v (y v))) (Measure.pi μ) ∧
        ∫ y, tens (fun v => G v (y v)) ∂(Measure.pi μ) = tens (fun v => ∫ t, G v t ∂(μ v)) := by
  intro ι _ X _ μ _ V _ _ _ Vπ _ _ _ tens hi hspan G hG
  have hcoord : ∀ w : Vπ, Integrable (fun y : ∀ v, X v => ⟪w, tens fun v => G v (y v)⟫_ℂ)
      (Measure.pi μ) := by
    intro w
    have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      simp_rw [hi]
      exact Integrable.fintype_prod_dep (fun v => (hG v).const_inner (z v))
    | zero =>
      simp only [inner_zero_left]
      exact integrable_zero _ _ _
    | add x y _ _ hx hy =>
      simp only [inner_add_left]
      exact hx.add hy
    | smul a x _ hx =>
      simp only [inner_smul_left]
      exact hx.const_mul _
  have hFint : Integrable (fun y : ∀ v, X v => tens fun v => G v (y v)) (Measure.pi μ) := by
    have e : (fun y : ∀ v, X v => tens fun v => G v (y v)) = fun y =>
        ∑ i, ⟪stdOrthonormalBasis ℂ Vπ i, tens fun v => G v (y v)⟫_ℂ • stdOrthonormalBasis ℂ Vπ i :=
      funext fun y => ((stdOrthonormalBasis ℂ Vπ).sum_repr' _).symm
    rw [e]
    exact MeasureTheory.integrable_finsetSum _ fun i _ => (hcoord _).smul_const _
  refine ⟨hFint, ?_⟩
  refine ext_inner_left ℂ fun w => ?_
  have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [← integral_inner hFint]
    simp_rw [hi]
    refine (integral_fintype_prod_eq_prod (fun v t => ⟪z v, G v t⟫_ℂ)).trans ?_
    exact Finset.prod_congr rfl fun v _ => integral_inner (hG v) (z v)
  | zero => simp only [inner_zero_left]
  | add x y _ _ hx hy => rw [inner_add_left, inner_add_left, hx, hy]
  | smul a x _ hx => rw [inner_smul_left, inner_smul_left, hx]

end Formalism.L2.SG.Pf.WuDec
end
end

