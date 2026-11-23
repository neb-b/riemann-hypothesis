module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0020

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusModulus
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem TorusModulus.commute (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v) (a : InfinitePlace E → ℂ)
    (hgx : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      a w • vecAt v x₀ w)
    (hgw : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w)
    (hgY : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (k : archUnitary h v) (hk : k ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) : g * k = k * g := by
  obtain ⟨hkx, hkw⟩ := Subgroup.mem_inf.1 hk
  apply Subtype.ext
  funext w
  apply Units.ext
  simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
  refine matrix_ext_mulVec fun z => ?_
  have hH := (h2 w).1
  have hAA : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.1, map_zero]
  have hBB : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.2.1, map_zero]
  have hAB : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 := by
    rw [hForm, ← h1 w, hp.2.2, map_one]
  have hBA : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hAB, map_one]
  have hKu : (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))ᴴ * gramAt h v w *
      ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w :=
    mem_archUnitary.1 k.2 w
  set H := gramAt h v w
  set A := vecAt v x₀ w
  set B := vecAt v w₀ w
  set G := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  set K := ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  have hKA : K *ᵥ A = A := hkx w
  have hKB : K *ᵥ B = B := hkw w
  set y := z - hForm H B z • A - hForm H A z • B with hy
  have hyA : hForm H A y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hAA, hAB]
    ring
  have hyB : hForm H B y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hBA, hBB]
    ring
  have hKyA : hForm H A (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu A y
    rw [hKA] at e
    rw [e, hyA]
  have hKyB : hForm H B (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu B y
    rw [hKB] at e
    rw [e, hyB]
  have hGy : G *ᵥ y = y := hgY w y hyA hyB
  have hGKy : G *ᵥ (K *ᵥ y) = K *ᵥ y := hgY w _ hKyA hKyB
  have hGA : G *ᵥ A = a w • A := hgx w
  have hGB : G *ᵥ B = (starRingEnd ℂ (a w))⁻¹ • B := hgw w
  have hz : z = y + hForm H B z • A + hForm H A z • B := by rw [hy]; abel
  rw [← mulVec_mulVec, ← mulVec_mulVec, hz]
  simp only [mulVec_add, mulVec_smul, hKA, hKB, hGy, hGKy, hGA, hGB]

theorem TorusModulus.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v)
    (h3 : ComplementForm.Statement h) (h4 : StabilizerLevi.Statement h v)
    (h5 : UnipotentModulus.Statement h v) (h6 : RadicalTorusModulus.Statement h v)
    (h7 : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectHaar.Statement (archUnitary h v) (archUnitary h' v')) :
    TorusModulus.Statement h v := by
  classical
  intro x₀ w₀ hp g a hgx hgw hgY ν _ f hf
  have : FiniteDimensional E W := Module.Finite.of_basis v
  obtain ⟨h', hh'⟩ := h3 x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  obtain ⟨i, q, hic, hqc, hqi, hker, hiw, -⟩ := h4 x₀ w₀ hp h' hh' _ v'
  let τ : archUnitary h' v' →* archUnitary h v := (vecFixGroup h v x₀).subtype.comp i
  have hτc : Continuous τ := continuous_subtype_val.comp hic
  have hτmem : ∀ t, τ t ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀ :=
    fun t => Subgroup.mem_inf.2 ⟨(i t).2, hiw t⟩
  have hnorm : ∀ t, ∀ x ∈ unipRadical h v x₀, τ t * x * (τ t)⁻¹ ∈ unipRadical h v x₀ := by
    intro t x hx
    have hxP : x ∈ vecFixGroup h v x₀ := unipRadical_le_vecFixGroup h v x₀ hx
    have e := (hker (i t * ⟨x, hxP⟩ * (i t)⁻¹)).1 (by
      rw [map_mul, map_mul, map_inv, hqi, (hker ⟨x, hxP⟩).2 hx, mul_one, mul_inv_cancel])
    simpa [τ] using e
  have hinj : ∀ t, τ t ∈ unipRadical h v x₀ → t = 1 := by
    intro t ht
    rw [← hqi t]
    exact (hker (i t)).2 ht
  have hdec : ∀ p : vecFixGroup h v x₀, (p : archUnitary h v) * (τ (q p))⁻¹ ∈ unipRadical h v x₀ := by
    intro p
    have e := (hker (p * (i (q p))⁻¹)).1 (by rw [map_mul, map_inv, hqi, mul_inv_cancel])
    simpa [τ] using e
  let νN : Measure (unipRadical h v x₀) := Measure.haar
  let ρ : Measure (archUnitary h' v') := Measure.haar
  have hδ : ∀ (t : archUnitary h' v') (f : archUnitary h v → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂νN = ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, f x ∂νN := by
    intro t f hf
    have e := h5 x₀ w₀ hp νN (τ t) (hτmem t)
    have hm : Measurable fun n : unipRadical h v x₀ => τ t * (n : archUnitary h v) * (τ t)⁻¹ :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    rw [ENNReal.coe_one, one_mul, ← lintegral_map hf hm, e, lintegral_map hf measurable_subtype_coe]
  obtain ⟨c, -, hc⟩ := h7 x₀ w₀ h' _ v' (vecFixGroup h v x₀) (unipRadical h v x₀)
    (isClosed_vecFixGroup h v x₀) (isClosed_unipRadical h v x₀) (unipRadical_le_vecFixGroup h v x₀)
    τ q (fun _ => 1) hτc hqc continuous_const (fun t => (i t).2) hnorm hinj hdec ν νN ρ hδ
  have hconj : ∀ t (n : archUnitary h v), g * (n * τ t) * g⁻¹ = g * n * g⁻¹ * τ t := by
    intro t n
    have e : τ t * g⁻¹ = g⁻¹ * τ t := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, TorusModulus.commute h v h1 h2 hp g a hgx hgw hgY _
        (hτmem t), mul_inv_cancel_right]
    calc g * (n * τ t) * g⁻¹ = g * n * (τ t * g⁻¹) := by group
      _ = g * n * (g⁻¹ * τ t) := by rw [e]
      _ = g * n * g⁻¹ * τ t := by group
  set K := ∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))
  have hφ : Measurable fun y : archUnitary h v => f (g * y * g⁻¹) :=
    hf.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have step : ∀ t, ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN =
      K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN := by
    intro t
    simp_rw [hconj t]
    exact h6 x₀ w₀ hp g a hgx hgw hgY νN (fun y => f (y * τ t))
      (hf.comp (continuous_id.mul continuous_const).measurable)
  have hmeas : Measurable fun t => ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN :=
    Measurable.lintegral_prod_right' (f := fun p : archUnitary h' v' × unipRadical h v x₀ =>
      f (p.2 * τ p.1)) (hf.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hτc.comp continuous_fst)).measurable)
  calc ∫⁻ x, f (g * x * g⁻¹) ∂ν
      = c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN ∂ρ := hc _ hφ
    _ = c * ∫⁻ t, K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ := by
        simp_rw [ENNReal.coe_one, one_mul, step]
    _ = K * (c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ) := by
        rw [lintegral_const_mul _ hmeas]
        simp only [ENNReal.coe_one, one_mul]
        ring
    _ = K * ∫⁻ x, f x ∂ν := by rw [hc f hf]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHomeo
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem continuous_hForm_self (H : Matrix ι ι ℂ) {X : Type*} [TopologicalSpace X] {y : X → ι → ℂ}
    (hy : Continuous y) : Continuous fun x => hForm H (y x) (y x) :=
  (continuous_star.comp hy).dotProduct (continuous_const.matrix_mulVec hy)

omit [DecidableEq ι] in
theorem continuous_hForm_right (H : Matrix ι ι ℂ) (u : ι → ℂ) {X : Type*} [TopologicalSpace X]
    {y : X → ι → ℂ} (hy : Continuous y) : Continuous fun x => hForm H u (y x) :=
  continuous_const.dotProduct (continuous_const.matrix_mulVec hy)

omit [DecidableEq ι] in
theorem heisS_eq (H : Matrix ι ι ℂ) (y : ι → ℂ) (t : ℝ) :
    heisS H y t = ((-(hForm H y y).re / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [heisS]

theorem continuous_heisMat_heisS (H : Matrix ι ι ℂ) (a : ι → ℂ) {X : Type*} [TopologicalSpace X]
    {y : X → ι → ℂ} {t : X → ℝ} (hy : Continuous y) (ht : Continuous t) :
    Continuous fun x => heisMat H a (y x) (heisS H (y x) (t x)) := by
  have hs : Continuous fun x => heisS H (y x) (t x) := by
    simp only [heisS_eq]
    exact (Complex.continuous_ofReal.comp
      ((Complex.continuous_re.comp (continuous_hForm_self H hy)).neg.div_const 2)).add
      ((Complex.continuous_ofReal.comp ht).mul continuous_const)
  unfold heisMat
  exact (continuous_const.add ((hy.add (hs.smul continuous_const)).matrix_vecMulVec
    continuous_const)).sub (continuous_const.matrix_vecMulVec
      ((continuous_star.comp hy).matrix_vecMul continuous_const))

section Homeo

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_unipRadical_at (w : InfinitePlace E) :
    Continuous fun n : unipRadical h v x₀ =>
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
  Units.continuous_val.comp ((continuous_apply w).comp
    (continuous_subtype_val.comp continuous_subtype_val))

theorem heisU_heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    heisU (w₀ := w₀) (heisPoint hp p) w = (p.1 : InfinitePlace E → ι → ℂ) w +
      heisS (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w) (p.2 w) • vecAt v x₀ w := by
  obtain ⟨hH, -, -, -, hab⟩ := hyperbolic_at_place h v hp w
  have hyb : hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w) (vecAt v w₀ w) = 0 := by
    rw [← hForm_conj hH, (p.1.2 w).2, map_zero]
  rw [heisU, heisPoint_val, heisMatAt, heisMat_mulVec, hab, hyb]
  simp only [one_smul, zero_smul, sub_zero, add_sub_cancel_left]

theorem hForm_heisU_heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) (heisPoint hp p) w) =
      heisS (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w) (p.2 w) := by
  obtain ⟨hH, -, -, -, hab⟩ := hyperbolic_at_place h v hp w
  have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hab, map_one]
  rw [heisU_heisPoint, hForm_add_right, hForm_smul_right, (p.1.2 w).2, hba]
  ring

theorem heisCoordOf_heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) :
    heisCoordOf hp (heisPoint hp p) = p := by
  refine Prod.ext (Subtype.ext (funext fun w => ?_)) (funext fun w => ?_)
  · change heisYOf (w₀ := w₀) (heisPoint hp p) w = (p.1 : InfinitePlace E → ι → ℂ) w
    rw [heisYOf, hForm_heisU_heisPoint, heisU_heisPoint, add_sub_cancel_right]
  · change (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) (heisPoint hp p) w)).im = p.2 w
    rw [hForm_heisU_heisPoint, heisS_im]

theorem heisPoint_heisCoordOf (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀) :
    heisPoint hp (heisCoordOf hp n) = n := by
  apply Subtype.ext
  apply Subtype.ext
  funext w
  apply Units.ext
  obtain ⟨-, -, h3, h4⟩ := heisYOf_spec hp n w
  rw [heisPoint_val]
  conv_rhs => rw [h4]
  exact congrArg (heisMat (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w))
    (eq_heisS h3).symm

def heisHomeo (hp : IsHyperbolicPair h x₀ w₀) : HeisCoord h v x₀ w₀ ≃ₜ unipRadical h v x₀ where
  toFun := heisPoint hp
  invFun := heisCoordOf hp
  left_inv := heisCoordOf_heisPoint hp
  right_inv := heisPoint_heisCoordOf hp
  continuous_toFun := by
    have hy : Continuous fun p : HeisCoord h v x₀ w₀ => (p.1 : InfinitePlace E → ι → ℂ) :=
      continuous_subtype_val.comp continuous_fst
    have ht : Continuous fun p : HeisCoord h v x₀ w₀ => p.2 := continuous_snd
    refine continuous_induced_rng.2 (continuous_induced_rng.2 (continuous_pi fun w => ?_))
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_heisMat_heisS _ _ ((continuous_apply w).comp hy)
        ((continuous_apply w).comp ht)
    · exact continuous_heisMat_heisS _ _ ((continuous_apply w).comp hy.neg)
        ((continuous_apply w).comp ht.neg)
  continuous_invFun := by
    have hu : ∀ w, Continuous fun n : unipRadical h v x₀ => heisU (w₀ := w₀) n w := fun w =>
      ((continuous_unipRadical_at w).matrix_mulVec continuous_const).sub continuous_const
    have hs : ∀ w, Continuous fun n : unipRadical h v x₀ =>
        hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) := fun w =>
      continuous_hForm_right _ _ (hu w)
    refine Continuous.prodMk (f := fun n => (heisCoordOf hp n).1)
      (g := fun n => (heisCoordOf hp n).2) ?_ ?_
    · refine continuous_induced_rng.2 (continuous_pi fun w => ?_)
      exact (hu w).sub ((hs w).smul continuous_const)
    · exact continuous_pi fun w => Complex.continuous_im.comp (hs w)

theorem heisHomeo_apply (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) :
    heisHomeo hp p = heisPoint hp p := rfl

theorem heisPoint_mul (hp : IsHyperbolicPair h x₀ w₀) (p q : HeisCoord h v x₀ w₀) :
    heisPoint hp p * heisPoint hp q = heisPoint hp (p.1 + q.1, p.2 + q.2 - fun w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((q.1 : InfinitePlace E → ι → ℂ) w)).im) := by
  apply Subtype.ext
  apply Subtype.ext
  funext w
  apply Units.ext
  simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
  rw [heisPoint_val, heisPoint_val, heisPoint_val, heisMatAt_mul hp p.1.2 q.1.2]
  rfl

def heisConjLin (g : archUnitary h v) (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) :
    heisY h v x₀ w₀ →ₗ[ℝ] heisY h v x₀ w₀ where
  toFun y := ⟨fun w => ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
      (y : InfinitePlace E → ι → ℂ) w, fun w => by
    have ha := (Subgroup.mem_inf.1 hg).1 w
    have hb := (Subgroup.mem_inf.1 hg).2 w
    constructor
    · conv_lhs => rw [← ha]
      rw [hForm_mulVec_of_unitary _ (archUnitary_at_place g w), (y.2 w).1]
    · conv_lhs => rw [← hb]
      rw [hForm_mulVec_of_unitary _ (archUnitary_at_place g w), (y.2 w).2]⟩
  map_add' y z := by
    apply Subtype.ext
    funext w
    simp [mulVec_add]
  map_smul' c y := by
    apply Subtype.ext
    funext w
    change _ *ᵥ (c • (y : InfinitePlace E → ι → ℂ) w) =
      c • (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ (y : InfinitePlace E → ι → ℂ) w)
    rw [real_smul_vec, real_smul_vec, mulVec_smul]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem heisConjLin_apply (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y : heisY h v x₀ w₀) (w : InfinitePlace E) :
    ((heisConjLin g hg y : heisY h v x₀ w₀) : InfinitePlace E → ι → ℂ) w =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ (y : InfinitePlace E → ι → ℂ) w := rfl

theorem heisPoint_conj (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (p : HeisCoord h v x₀ w₀) :
    g * ((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) * g⁻¹ =
      heisPoint hp (heisConjLin g hg p.1, p.2) := by
  apply Subtype.ext
  funext w
  apply Units.ext
  have ha := (Subgroup.mem_inf.1 hg).1 w
  have hu := archUnitary_at_place g w
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  rw [heisPoint_val, heisPoint_val, heisMatAt, heisMatAt, heisMat_conj hu ha, mul_assoc,
    Units.mul_inv, mul_one, heisConjLin_apply]
  congr 1
  simp only [heisS, hForm_mulVec_of_unitary _ hu]

end Homeo

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

