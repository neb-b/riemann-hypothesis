module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.IdeleRoots.ClassicalIdeles.ExistsPosBoundsOfIsCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbLower
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem ab_lower {F : Type} [Field F] [NumberField F] {Ω : Set (G1 F)} (hΩ : IsCompact Ω) :
    ∃ lo : ℝ, 0 < lo ∧ ∀ p ∈ Ω, ∀ x : (A F)ˣ, (x : A F) = p 0 0 → ((x⁻¹ : (A F)ˣ) : A F) = p 1 1 → lo ≤ ab x := by
  let f : G1 F → A F × (A F)ᵐᵒᵖ := fun p => (p 0 0, MulOpposite.op (p 1 1))
  have hf : Continuous f :=
    (M.continuous_entry 0 0).prodMk (MulOpposite.continuous_op.comp (M.continuous_entry 1 1))
  have hS : IsCompact ((Units.embedProduct (A F)) ⁻¹' (f '' Ω)) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hΩ.image hf)
  obtain ⟨lo, _, hlo, _, hb⟩ := GroundTheory.BlockD.exists_pos_bounds_of_isCompact hS M.continuous_ab M.ab_pos
  refine ⟨lo, hlo, fun p hp x h0 h1 => (hb x ?_).1⟩
  refine ⟨p, hp, ?_⟩
  simp [f, Units.embedProduct, h0, h1]

private theorem parts_eq {F : Type} [Field F] [NumberField F] {t : ℝ} (ht : 0 < t) (a : InfiniteAdeleRing F)
    (h : ∀ w, InfinitePlace.Completion.extensionEmbedding w (a w) = (t : ℂ)) :
    Formalism.D.adeleOfParts F a 1 = ((GroundTheory.Automorphic.Reduction.posIdele t ht : IdeleGroup F) : AdeleRing (𝓞 F) F) := by
  rw [← GroundTheory.BlockD.adeleOfParts_posIdele t ht]
  congr 1
  funext w
  exact (InfinitePlace.Completion.extensionEmbedding w).injective
    ((h w).trans (GroundTheory.BlockD.extensionEmbedding_posIdele t ht w).symm)

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.redE :
    RedE := by
  intro E _ _
  obtain ⟨Ω, K, t₀, hΩ, h10, hK, ht₀, H⟩ := GroundTheory.BlockD.siegelSetsSL2Adelic_holds E
  obtain ⟨lo, hlo, hb⟩ := ab_lower hΩ
  set d : ℕ := Module.finrank ℚ E with hd
  refine ⟨lo * t₀ ^ d, K, by positivity, hK, fun h => ?_⟩
  obtain ⟨_, ⟨γ, rfl⟩, p, hp, t, ht, a, a', ha, k, hk, heq⟩ := H h
  have htpos : 0 < t := ht₀.trans_le ht
  set z : (A E)ˣ := GroundTheory.Automorphic.Reduction.posIdele t htpos with hz
  have ea : Formalism.D.adeleOfParts E a 1 = (z : A E) := parts_eq htpos a fun w => (ha w).2
  have eaa : Formalism.D.adeleOfParts E a 1 * Formalism.D.adeleOfParts E a' 1 = 1 := by
    refine Prod.ext (funext fun w => (ha w).1) ?_
    show (1 : FiniteAdeleRing (𝓞 E) E) * 1 = 1
    simp
  have ea' : Formalism.D.adeleOfParts E a' 1 = ((z⁻¹ : (A E)ˣ) : A E) := by
    rw [ea] at eaa
    exact (Units.inv_eq_of_mul_eq_one_right eaa).symm
  have hp10 : p 1 0 = 0 := h10 p hp
  have hdet : p 0 0 * p 1 1 = 1 := by
    have := p.det_coe
    rw [Matrix.det_fin_two] at this
    simpa [hp10] using this
  let x : (A E)ˣ := ⟨p 0 0, p 1 1, hdet, by rw [mul_comm]; exact hdet⟩
  have hx := hb p hp x rfl rfl
  refine ⟨γ, p 0 1 * p 0 0, x * z, k, hk, ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [M.val_mul, M.val_mul, M.val_mul]
    refine heq.trans ?_
    rw [ea, ea']
    congr 1
    ext i j
    fin_cases i <;> fin_cases j
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-(p.1 0 1 * ((z⁻¹ : (A E)ˣ) : A E))) * hdet
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two, hp10]
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two, hp10, mul_comm]
  · rw [M.ab_mul]
    have hz' : ab z = t ^ d := by
      simp [ab, hz, GroundTheory.Automorphic.Reduction.ideleModule_posIdele, hd]
    rw [hz']
    have : t₀ ^ d ≤ t ^ d := pow_le_pow_left₀ ht₀.le ht d
    exact mul_le_mul hx this (by positivity) (M.ab_pos x).le
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DiagInvVal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal

private theorem cd_meas {E : Type} [Field E] [NumberField E] (N : MeasE E) (t : (A E)ˣ) :
    MeasurePreserving (cD t) N.μ N.μ := by
  haveI := N.haar
  haveI := N.right
  have hm : ∀ s : (A E)ˣ, Measurable (cD s : G1 E → G1 E) := fun s => (M.continuous_cD s).measurable
  let e : G1 E ≃ₜ* G1 E :=
    { toFun := cD t
      invFun := cD t⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      map_mul' := M.cD_mul t
      continuous_toFun := M.continuous_cD t
      continuous_invFun := M.continuous_cD t⁻¹ }
  haveI : (N.μ.map (cD t)).IsHaarMeasure := e.isHaarMeasure_map N.μ
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, N.μ.map (cD t) = c • N.μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (N.μ.map (cD t)) N.μ⟩
  have h2 : N.μ.map (cD (t * t)) = N.μ := by
    have : (cD (t * t) : G1 E → G1 E) = (fun g => g * mD t) ∘ (fun g => (mD t)⁻¹ * g) := by
      funext g; exact M.cD_sq t g
    rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _),
      map_mul_left_eq_self, map_mul_right_eq_self]
  have h3 : N.μ.map (cD (t * t)) = (c * c) • N.μ := by
    have : (cD (t * t) : G1 E → G1 E) = cD t ∘ cD t := by
      funext g; exact (M.cD_cD t t g).symm
    rw [this, ← Measure.map_map (hm t) (hm t), hc, Measure.map_smul, hc, smul_smul]
    exact (hm t).aemeasurable
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G1 E)
  have hpos : N.μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds N.μ hK1).ne'
  have hfin : N.μ K ≠ ∞ := hK.measure_lt_top.ne
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) * N.μ K = N.μ K := by
    have := congrArg (fun m : Measure (G1 E) => m K) (h3.symm.trans h2)
    simpa [ENNReal.smul_def] using this
  have h5 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := by
    have h6 : ((c * c : ℝ≥0) : ℝ≥0∞) * N.μ K = 1 * N.μ K := by rw [h4, one_mul]
    exact (ENNReal.mul_left_inj hpos hfin).1 h6
  have h7 : c * c = 1 := by exact_mod_cast h5
  have h8 : c = 1 := by
    have := (mul_self_eq_one_iff (a := (c : ℝ))).1 (by exact_mod_cast h7)
    rcases this with h | h
    · exact_mod_cast h
    · have := c.coe_nonneg; linarith
  refine ⟨hm t, ?_⟩
  rw [hc, h8, one_smul]

private theorem right_tr {E : Type} [Field E] [NumberField E] (N : MeasE E) (u : G1 E → ℂ)
    (hu : ∀ γ g, u (ratS E γ * g) = u g) (k : G1 E) :
    ∫ g in N.D, u (g * k) ∂N.μ = ∫ g in N.D, u g ∂N.μ := by
  haveI := N.haar
  haveI := N.right
  have hmp : MeasurePreserving (· * k) N.μ N.μ := measurePreserving_mul_right N.μ k
  have hemb : MeasurableEmbedding (· * k : G1 E → G1 E) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam E) ((Equiv.mulRight k) '' N.D) N.μ := by
    refine N.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right N.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam E) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 E → G1 E) ⁻¹' ((Equiv.mulRight k) '' N.D) = N.D := by
    ext x; simp
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' N.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq N.fund hinv

private theorem diag_val (E : Type) [Field E] [NumberField E] (t : Eˣ) :
    ((IdeleGroup.diagonal E t : (A E)ˣ) : A E) = rt (t : E) := rfl

private theorem diag_inv_val (E : Type) [Field E] [NumberField E] (t : Eˣ) :
    (((IdeleGroup.diagonal E t : (A E)ˣ)⁻¹ : (A E)ˣ) : A E) = rt ((t : E)⁻¹) := by
  rw [← map_inv, ← Units.val_inv_eq_inv_val]
  rfl

private def cR {E : Type} [Field E] (t : Eˣ) (g : Matrix.SpecialLinearGroup (Fin 2) E) :
    Matrix.SpecialLinearGroup (Fin 2) E :=
  ⟨!![g 0 0, g 0 1 * (t : E)⁻¹; (t : E) * g 1 0, g 1 1], by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    have ht : (t : E) ≠ 0 := t.ne_zero
    have : g 0 1 * (t : E)⁻¹ * ((t : E) * g 1 0) = g 0 1 * g 1 0 := by field_simp
    rw [this]
    exact h⟩

private theorem cD_ratS {E : Type} [Field E] [NumberField E] (t : Eˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) E) :
    cD (IdeleGroup.diagonal E t) (ratS E g) = ratS E (cR t g) := by
  refine Subtype.ext ?_
  rw [M.val_ratS]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cD, cR, M.val_ratS, diag_inv_val, diag_val, UpperTheory.ConvolutionTheory.R2.rt, map_mul]

private theorem cD_mem {E : Type} [Field E] [NumberField E] (t : Eˣ) {x : G1 E} (hx : x ∈ Gam E) :
    cD (IdeleGroup.diagonal E t) x ∈ Gam E := by
  obtain ⟨g, rfl⟩ := hx
  exact ⟨cR t g, (cD_ratS t g).symm⟩

private theorem conj_int {E : Type} [Field E] [NumberField E] (N : MeasE E) (u : G1 E → ℂ)
    (hu : ∀ γ g, u (ratS E γ * g) = u g) (t : Eˣ) :
    ∫ g in N.D, u (cD (IdeleGroup.diagonal E t) g) ∂N.μ = ∫ g in N.D, u g ∂N.μ := by
  haveI := N.haar
  set T : (A E)ˣ := IdeleGroup.diagonal E t with hT
  have hTi : T⁻¹ = IdeleGroup.diagonal E t⁻¹ := by rw [hT, map_inv]
  let e : G1 E ≃ₜ G1 E :=
    { toFun := cD T
      invFun := cD T⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      continuous_toFun := M.continuous_cD T
      continuous_invFun := M.continuous_cD T⁻¹ }
  let eG : Gam E ≃ Gam E :=
    { toFun := fun γ => ⟨cD T⁻¹ γ.1, by rw [hTi]; exact cD_mem t⁻¹ γ.2⟩
      invFun := fun γ => ⟨cD T γ.1, cD_mem t γ.2⟩
      left_inv := fun γ => Subtype.ext (by
        show cD T (cD T⁻¹ γ.1) = γ.1
        rw [M.cD_cD, mul_inv_cancel, M.cD_one])
      right_inv := fun γ => Subtype.ext (by
        show cD T⁻¹ (cD T γ.1) = γ.1
        rw [M.cD_cD, inv_mul_cancel, M.cD_one]) }
  have hmp : MeasurePreserving (cD T) N.μ N.μ := cd_meas N T
  have hmpi : MeasurePreserving (cD T⁻¹) N.μ N.μ := cd_meas N T⁻¹
  have hemb : MeasurableEmbedding (cD T : G1 E → G1 E) := e.measurableEmbedding
  have hD' : IsFundamentalDomain (Gam E) (cD T '' N.D) N.μ :=
    N.fund.image_of_equiv e.toEquiv hmpi.quasiMeasurePreserving eG (fun γ x => by
      show cD T (cD T⁻¹ γ.1 * x) = γ.1 * cD T x
      rw [M.cD_mul, M.cD_cD, mul_inv_cancel, M.cD_one])
  have hpre : cD T ⁻¹' (cD T '' N.D) = N.D := Set.preimage_image_eq _ e.injective
  have hinv : ∀ (γ : Gam E) (x : G1 E), u (γ • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    exact hu γ x
  have h1 := hmp.setIntegral_preimage_emb hemb u (cD T '' N.D)
  rw [hpre] at h1
  exact h1.trans (hD'.setIntegral_eq N.fund hinv)

private theorem glRat {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) E) :
    gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := Units.ext rfl

private theorem linv {E : Type} [Field E] [NumberField E] {Ψ : GL (Fin 2) (A E) → ℂ} (hΨ : LRat Ψ)
    (y : GL (Fin 2) (A E)) (γ : Matrix.SpecialLinearGroup (Fin 2) E) (g : G1 E) :
    Ψ (gl (ratS E γ * g) * y) = Ψ (gl g * y) := by
  have hm : gl (ratS E γ * g) = gl (ratS E γ) * gl g := map_mul _ _ _
  rw [hm, glRat, mul_assoc]
  exact hΨ _ _

private def dR {E : Type} [Field E] (r : Eˣ) : GL (Fin 2) E :=
  ⟨!![1, 0; 0, (r : E)], !![1, 0; 0, ((r⁻¹ : Eˣ) : E)], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

private theorem ratGL_dR {E : Type} [Field E] [NumberField E] (r : Eˣ) :
    ratGL E 2 (dR r) = dM (IdeleGroup.diagonal E r) := by
  refine Units.ext ?_
  show (dR r).val.map (algebraMap E (A E)) = (dM (IdeleGroup.diagonal E r)).val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dR, dM, diag_val, UpperTheory.ConvolutionTheory.R2.rt]

private theorem rat_decomp {E : Type} [Field E] [NumberField E] (γ : GL (Fin 2) E) :
    ∃ (r : Eˣ) (s : Matrix.SpecialLinearGroup (Fin 2) E),
      ratGL E 2 γ = dM (IdeleGroup.diagonal E r) * gl (ratS E s) := by
  set r : Eˣ := Matrix.GeneralLinearGroup.det γ with hr
  have hd : Matrix.GeneralLinearGroup.det (dR r) = r := by
    refine Units.ext ?_
    simp [dR, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdet : Matrix.GeneralLinearGroup.det ((dR r)⁻¹ * γ) = 1 := by
    rw [map_mul, map_inv, hd, ← hr, inv_mul_cancel]
  let s : Matrix.SpecialLinearGroup (Fin 2) E := ⟨((dR r)⁻¹ * γ).val, by
    have h1 := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1⟩
  have hs : Matrix.SpecialLinearGroup.toGL s = (dR r)⁻¹ * γ := Units.ext rfl
  refine ⟨r, s, ?_⟩
  rw [glRat, hs, map_mul, ← ratGL_dR, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.invE :
    InvE := by
  intro E _ _ N
  refine ⟨cd_meas N, fun Ψ hΨ => ?_⟩
  have hright : ∀ h : G1 E, (mean N fun x => Ψ (x * gl h)) = mean N Ψ := by
    intro h
    unfold mean
    have e : ∀ x : G1 E, Ψ (gl x * gl h) = Ψ (gl (x * h)) := fun x => by
      have hm : gl (x * h) = gl x * gl h := map_mul _ _ _
      rw [hm]
    simp only [e]
    refine right_tr N (fun x => Ψ (gl x)) (fun γ g => ?_) h
    simpa using linv hΨ 1 γ g
  refine ⟨hright, fun γ => ?_⟩
  obtain ⟨r, s, hγ⟩ := rat_decomp γ
  set S : GL (Fin 2) (A E) := gl (ratS E s) with hS
  set T : (A E)ˣ := IdeleGroup.diagonal E r with hT
  have hTi : T⁻¹ = IdeleGroup.diagonal E r⁻¹ := by rw [hT, map_inv]
  have e : ∀ x : G1 E, Ψ (gl x * ratGL E 2 γ) = Ψ (gl (cD (IdeleGroup.diagonal E r⁻¹) x) * S) := by
    intro x
    have h1 : gl x * dM T = dM T * gl (cD T⁻¹ x) := by
      have := M.gl_cD T (cD T⁻¹ x)
      rwa [M.cD_cD, mul_inv_cancel, M.cD_one] at this
    rw [hγ, ← mul_assoc, h1, mul_assoc, hT, ← ratGL_dR, hΨ, ← hT, hTi]
  have h2 : (mean N fun x => Ψ (x * ratGL E 2 γ)) =
      ∫ x in N.D, Ψ (gl x * S) ∂N.μ := by
    unfold mean
    simp only [e]
    exact conj_int N (fun x => Ψ (gl x * S)) (fun γ' g => linv hΨ S γ' g) r⁻¹
  rw [h2]
  exact hright (ratS E s)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianMatrixBasisOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

section
variable {E : Type} [Field E] [NumberField E]

private noncomputable def mm (D : Dat ℚ E) (u t : ℚ) : E := algebraMap ℚ E u + algebraMap ℚ E t * D.θ

private noncomputable def hm (D : Dat ℚ E) (ξ : Fin 4 → ℚ) : Matrix (Fin 2) (Fin 2) E :=
  !![mm D (ξ 1) 0, mm D (ξ 2) (ξ 3); mm D (ξ 2) (-ξ 3), mm D (ξ 0) 0]

private theorem mm_base (D : Dat ℚ E) (u : ℚ) : mm D u 0 = algebraMap ℚ E u := by simp [mm]

private theorem σ_alg (D : Dat ℚ E) (u : ℚ) : D.σ (algebraMap ℚ E u) = algebraMap ℚ E u := D.σ.commutes u

private theorem σ_mm (D : Dat ℚ E) (u t : ℚ) : D.σ (mm D u t) = mm D u (-t) := by
  simp only [mm, map_add (f := _), map_mul, σ_alg, D.conj, map_neg]; ring

private theorem mm_mul (D : Dat ℚ E) (u t : ℚ) :
    mm D u t * mm D u (-t) = algebraMap ℚ E (u ^ 2 - D.δ * t ^ 2) := by
  have h := D.sq
  simp only [mm, map_sub, map_mul, map_pow, map_neg, ← h]; ring

private theorem herm_rp (D : Dat ℚ E) (ξ : Fin 4 → ℚ) :
    D.herm (rp ξ) = (hm D ξ).map (algebraMap E (A E)) := by
  have h0 : (0 : A ℚ) = rt (0 : ℚ) := (map_zero _).symm
  have hn : -(rt (ξ 3) : A ℚ) = rt (-ξ 3) := (map_neg _ _).symm
  ext i j
  fin_cases i <;> fin_cases j
  · change D.mkE (rt (ξ 1)) 0 = rt (mm D (ξ 1) 0)
    rw [h0, D.mkE_rt]; rfl
  · exact D.mkE_rt _ _
  · change D.mkE (rt (ξ 2)) (-rt (ξ 3)) = rt (mm D (ξ 2) (-ξ 3))
    rw [hn, D.mkE_rt]; rfl
  · change D.mkE (rt (ξ 0)) 0 = rt (mm D (ξ 0) 0)
    rw [h0, D.mkE_rt]; rfl

private theorem act_iff (D : Dat ℚ E) (γ : SpecialLinearGroup (Fin 2) E) (ξ η : Fin 4 → ℚ) :
    D.act (gl (ratS E γ)) (rp ξ) = rp η ↔ γ.1 * hm D ξ * (γ.1.map D.σ)ᵀ = hm D η := by
  haveI := AdeleBaseChange.nontrivial_adeleRing E
  have inj : Function.Injective fun X : Matrix (Fin 2) (Fin 2) E => X.map (algebraMap E (A E)) :=
    Matrix.map_injective (algebraMap E (A E)).injective
  have hγ : ((gl (ratS E γ)) : Matrix (Fin 2) (Fin 2) (A E)) = γ.1.map (algebraMap E (A E)) := by
    ext i j; exact ratS_apply γ i j
  have hs : D.star2 ((gl (ratS E γ)) : Matrix (Fin 2) (Fin 2) (A E)) =
      ((γ.1.map D.σ)ᵀ).map (algebraMap E (A E)) := by
    ext i j
    rw [D.conjTransposeGal_apply, hγ]
    exact D.bar_rt _
  have hact : D.herm (D.act (gl (ratS E γ)) (rp ξ)) =
      (γ.1 * hm D ξ * (γ.1.map D.σ)ᵀ).map (algebraMap E (A E)) := by
    rw [D.herm_act, hs, herm_rp, hγ, Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro h
    apply inj
    change (γ.1 * hm D ξ * (γ.1.map D.σ)ᵀ).map (algebraMap E (A E)) = (hm D η).map (algebraMap E (A E))
    rw [← hact, h, herm_rp]
  · intro h
    apply D.herm_injective
    rw [hact, h, herm_rp]

private theorem hermitianMatrix_basisOne (D : Dat ℚ E) (r : ℚ) : hm D ![0, r, 0, 0] = !![algebraMap ℚ E r, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hm, mm]

private theorem prod_pow_unitVector_val (D : Dat ℚ E) (g : Matrix (Fin 2) (Fin 2) E) (R : E) :
    g * !![R, 0; 0, 0] * (g.map D.σ)ᵀ =
      !![g 0 0 * R * D.σ (g 0 0), g 0 0 * R * D.σ (g 1 0); g 1 0 * R * D.σ (g 0 0), g 1 0 * R * D.σ (g 1 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem prod_low (D : Dat ℚ E) (w R : E) :
    (!![1, 0; w, 1] : Matrix (Fin 2) (Fin 2) E) * !![R, 0; 0, 0] * ((!![1, 0; w, 1] : Matrix (Fin 2) (Fin 2) E).map D.σ)ᵀ =
      !![R, R * D.σ w; w * R, w * R * D.σ w] := by
  rw [prod_pow_unitVector_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem δ_neg (D : Dat ℚ E) : D.δ < 0 := by
  have h := D.neg (algebraMap ℚ ℝ)
  simpa using h

private theorem rank_one (D : Dat ℚ E) (ξ : Fin 4 → ℚ) (h0 : ξ ≠ 0) (hq : qr D.δ ξ = 0) :
    ∃ (γ : SpecialLinearGroup (Fin 2) E) (r : ℚ), r ≠ 0 ∧ rp ξ = D.act (gl (ratS E γ)) (rp ![0, r, 0, 0]) := by
  have hq' : ξ 2 ^ 2 - D.δ * ξ 3 ^ 2 = ξ 1 * ξ 0 := by
    have : ξ 2 ^ 2 - D.δ * ξ 3 ^ 2 - ξ 1 * ξ 0 = 0 := hq
    linarith
  by_cases hx : ξ 1 = 0
  · have hδ := δ_neg D
    rw [hx, zero_mul] at hq'
    have h3 : ξ 3 = 0 := by
      by_contra h
      have : 0 < ξ 3 ^ 2 := by positivity
      nlinarith [sq_nonneg (ξ 2)]
    have h2 : ξ 2 = 0 := by
      rw [h3] at hq'
      simpa using hq'
    have hy : ξ 0 ≠ 0 := fun hy => h0 (by
      ext i; fin_cases i <;> simp [hy, hx, h2, h3])
    refine ⟨⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩, ξ 0, hy, ((act_iff D _ _ _).2 ?_).symm⟩
    rw [hermitianMatrix_basisOne, prod_pow_unitVector_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm, mm, hx, h2, h3]
  · have hx' : algebraMap ℚ E (ξ 1) ≠ 0 := by simpa using hx
    obtain ⟨w, hw, hσ⟩ : ∃ w : E, w * algebraMap ℚ E (ξ 1) = mm D (ξ 2) (-ξ 3) ∧
        D.σ w * algebraMap ℚ E (ξ 1) = mm D (ξ 2) (ξ 3) :=
      ⟨mm D (ξ 2) (-ξ 3) / algebraMap ℚ E (ξ 1), div_mul_cancel₀ _ hx', by
        rw [map_div₀, σ_mm, σ_alg, neg_neg, div_mul_cancel₀ _ hx']⟩
    refine ⟨⟨!![1, 0; w, 1], by simp [Matrix.det_fin_two]⟩, ξ 1, hx, ((act_iff D _ _ _).2 ?_).symm⟩
    have hmul := mm_mul D (ξ 2) (ξ 3)
    rw [hq', map_mul] at hmul
    change !![1, 0; w, 1] * _ * _ = _
    rw [hermitianMatrix_basisOne, prod_low, hm, mm_base, mm_base]
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · change algebraMap ℚ E (ξ 1) * D.σ w = mm D (ξ 2) (ξ 3)
      rw [mul_comm]; exact hσ
    · exact hw
    · change w * algebraMap ℚ E (ξ 1) * D.σ w = algebraMap ℚ E (ξ 0)
      rw [hw]
      apply mul_left_cancel₀ hx'
      linear_combination mm D (ξ 2) (-ξ 3) * hσ + hmul
end

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.orb1 :
    Orb1 := by
  intro E _ _ _ D
  refine ⟨fun γ => ?_, fun ξ h0 hq => rank_one D ξ h0 hq, fun γ r r' hr h => ?_, fun γ hγ => ?_, fun u r => ?_⟩
  · obtain ⟨N, -, hN⟩ := actRat ℚ E D (Matrix.SpecialLinearGroup.toGL γ)
    refine ⟨Matrix.toLin'OfInv (M := (N⁻¹ : GL (Fin 4) ℚ).val) (M' := N.val) (by simp) (by simp), fun ξ => ?_⟩
    rw [gl_ratS, hN]
    rfl
  · rw [act_iff, hermitianMatrix_basisOne, hermitianMatrix_basisOne, prod_pow_unitVector_val] at h
    have h11 := congrFun (congrFun h 1) 1
    simpa [hr] using h11
  · set a := D.b.repr (γ.1 0 0) 0
    set t := D.b.repr (γ.1 0 0) 1
    have ha : γ.1 0 0 = mm D a t := by
      have h := D.b.sum_repr (γ.1 0 0)
      rw [Fin.sum_univ_two, D.b0, D.b1] at h
      rw [mm, ← h]
      simp [a, t, Algebra.smul_def]
    have hdet : γ.1 0 0 * γ.1 1 1 = 1 := by
      have h := γ.2
      rw [Matrix.det_fin_two] at h
      have h10 : γ.1 1 0 = 0 := hγ
      simpa [h10] using h
    have hne : γ.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hnorm : γ.1 0 0 * D.σ (γ.1 0 0) = algebraMap ℚ E (a ^ 2 - D.δ * t ^ 2) := by
      rw [ha, σ_mm, mm_mul]
    refine ⟨a ^ 2 - D.δ * t ^ 2, fun hc => ?_, fun r => ?_⟩
    · rw [hc, map_zero] at hnorm
      exact (mul_ne_zero hne (by simpa using hne)) hnorm
    · refine (act_iff D _ _ _).2 ?_
      have h10 : γ.1 1 0 = 0 := hγ
      have h00 : γ.1 0 0 * algebraMap ℚ E r * D.σ (γ.1 0 0) = algebraMap ℚ E ((a ^ 2 - D.δ * t ^ 2) * r) := by
        rw [map_mul, ← hnorm]; ring
      rw [hermitianMatrix_basisOne, hermitianMatrix_basisOne, prod_pow_unitVector_val, h10, h00]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · obtain ⟨a, b, rfl⟩ := D.exists_mkE u
    rw [D.act_nU]
    ext i
    fin_cases i <;> simp [rp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeasEEx
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.measEEx :
    MeasEEx := by
  intro E _ _
  let μ : Measure (G1 E) := Measure.haar
  obtain ⟨D, hD, -, hf⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Gam E)
  exact ⟨⟨μ, D, inferInstance, M.unimod E μ, hD, hf μ⟩⟩
end

