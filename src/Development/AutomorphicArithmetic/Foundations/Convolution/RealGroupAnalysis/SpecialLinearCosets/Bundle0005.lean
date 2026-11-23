module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IntegrableSB
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical NNReal

namespace UpperTheory.ConvolutionTheory.R2.I.CentralConjugation

section

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

private def cjE (x : GL (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃ₜ* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun m := ⟨(x⁻¹).val * m.1 * x.val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one]⟩
  invFun m := ⟨x.val * m.1 * (x⁻¹).val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one]⟩
  left_inv m := by
    apply Subtype.ext
    show x.val * ((x⁻¹).val * m.1 * x.val) * (x⁻¹).val = m.1
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  right_inv m := by
    apply Subtype.ext
    show (x⁻¹).val * (x.val * m.1 * (x⁻¹).val) * x.val = m.1
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
  map_mul' m n := by
    apply Subtype.ext
    show (x⁻¹).val * (m.1 * n.1) * x.val = ((x⁻¹).val * m.1 * x.val) * ((x⁻¹).val * n.1 * x.val)
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const

variable [LocallyCompactSpace (Matrix.SpecialLinearGroup (Fin 2) K)]
  [MeasurableSpace (Matrix.SpecialLinearGroup (Fin 2) K)]
  [BorelSpace (Matrix.SpecialLinearGroup (Fin 2) K)]

private noncomputable def cc (x : GL (Fin 2) K) : ℝ≥0 := mulEquivHaarChar (cjE x)

private theorem cc_ne (x : GL (Fin 2) K) : cc x ≠ 0 := (mulEquivHaarChar_pos (cjE x)).ne'

private theorem cc_mul (x y : GL (Fin 2) K) : cc (x * y) = cc x * cc y := by
  have h : cjE (x * y) = (cjE x).trans (cjE y) := by
    ext1 m
    apply Subtype.ext
    show ((x * y)⁻¹).val * m.1 * (x * y).val = (y⁻¹).val * ((x⁻¹).val * m.1 * x.val) * y.val
    simp only [_root_.mul_inv_rev, Units.val_mul, mul_assoc]
  unfold cc
  rw [h, mulEquivHaarChar_trans]

private theorem cc_central (z : GL (Fin 2) K) (hz : ∀ m : Matrix (Fin 2) (Fin 2) K, z.val * m = m * z.val) :
    cc z = 1 := by
  have h : cjE z = ContinuousMulEquiv.refl _ := by
    ext1 m
    apply Subtype.ext
    show (z⁻¹).val * m.1 * z.val = m.1
    rw [mul_assoc, ← hz, Units.inv_mul_cancel_left]
  unfold cc
  rw [h, mulEquivHaarChar_refl]

private theorem cc_of_sq (d t : GL (Fin 2) K) (h : d * t = t * t * d) : cc t = 1 := by
  have e := congrArg cc h
  rw [cc_mul, cc_mul, cc_mul] at e
  apply mul_left_cancel₀ (mul_ne_zero (cc_ne t) (cc_ne d))
  rw [mul_one, show cc t * cc d * cc t = cc t * cc t * cc d by ring, ← e]
  ring


variable (K) in
private noncomputable def ccS : Matrix.SpecialLinearGroup (Fin 2) K →* ℝ≥0 where
  toFun g := cc (Matrix.SpecialLinearGroup.toGL g)
  map_one' := by
    rw [map_one]
    exact cc_central 1 (by simp)
  map_mul' g h := by rw [map_mul, cc_mul]

private theorem cc_SL (h2 : (2 : K) ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    cc (Matrix.SpecialLinearGroup.toGL g) = 1 := by
  let d₁ : GL (Fin 2) K := ⟨!![2, 0; 0, 1], !![2⁻¹, 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2]⟩
  let d₂ : GL (Fin 2) K := ⟨!![1, 0; 0, 2], !![1, 0; 0, 2⁻¹],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2]⟩
  have hT := UpperTheory.ConvolutionTheory.R2.I.genSL K (ccS K).ker
    (fun g b hg => by
      rw [MonoidHom.mem_ker]
      refine cc_of_sq d₁ _ (Units.ext ?_)
      show d₁.val * g.1 = g.1 * g.1 * d₁.val
      rw [hg]
      ext i j; fin_cases i <;> fin_cases j <;> simp [d₁, Matrix.mul_apply, Fin.sum_univ_two] <;> ring)
    (fun g c hg => by
      rw [MonoidHom.mem_ker]
      refine cc_of_sq d₂ _ (Units.ext ?_)
      show d₂.val * g.1 = g.1 * g.1 * d₂.val
      rw [hg]
      ext i j; fin_cases i <;> fin_cases j <;> simp [d₂, Matrix.mul_apply, Fin.sum_univ_two] <;> ring)
  have : g ∈ (ccS K).ker := by rw [hT]; trivial
  exact this

private theorem cc_eq_one (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K) : cc x = 1 := by
  have hd : x.val.det ≠ 0 := by
    intro h0
    have h1 : x.val.det * (x⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  set t := x.val.det with ht
  let s : Matrix.SpecialLinearGroup (Fin 2) K := ⟨t⁻¹ • (x.val * x.val), by
    rw [Matrix.det_smul, Matrix.det_mul, ← ht]
    simp only [Fintype.card_fin]
    field_simp⟩
  let z : GL (Fin 2) K := ⟨t • 1, t⁻¹ • 1, by simp [smul_smul, hd], by simp [smul_smul, hd]⟩
  have hx : x * x = z * Matrix.SpecialLinearGroup.toGL s := by
    apply Units.ext
    show x.val * x.val = (t • (1 : Matrix (Fin 2) (Fin 2) K)) * (t⁻¹ • (x.val * x.val))
    simp [smul_smul, hd]
  have hz : cc z = 1 := cc_central z (fun m => by
    show (t • (1 : Matrix (Fin 2) (Fin 2) K)) * m = m * (t • (1 : Matrix (Fin 2) (Fin 2) K))
    simp)
  have e := congrArg cc hx
  rw [cc_mul, cc_mul, hz, cc_SL h2, one_mul] at e
  have e' : ((cc x : ℝ≥0) : ℝ) * (cc x : ℝ≥0) = 1 := by exact_mod_cast e
  rcases mul_self_eq_one_iff.1 e' with h | h
  · exact_mod_cast h
  · have := (cc x).coe_nonneg
    linarith

private theorem mp_cjE (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K) :
    MeasurePreserving (cjE x) (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) Measure.haar := by
  refine ⟨(map_continuous (cjE x)).measurable, ?_⟩
  have h := mulEquivHaarChar_smul_map (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) (cjE x)
  have h1 : mulEquivHaarChar (cjE x) = 1 := cc_eq_one h2 x
  rwa [h1, one_smul] at h

private theorem integral_cjE (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K)
    (f : Matrix.SpecialLinearGroup (Fin 2) K → ℂ) :
    ∫ m, f (cjE x m) ∂(Measure.haar) = ∫ m, f m ∂(Measure.haar) :=
  (mp_cjE h2 x).integral_comp (cjE x).toHomeomorph.measurableEmbedding f

private theorem integrable_SB (a : SB (Matrix.SpecialLinearGroup (Fin 2) K)) :
    Integrable a.1 (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) :=
  a.2.1.continuous.integrable_of_hasCompactSupport a.2.2

private theorem exists_I (h2 : (2 : K) ≠ 0) :
    ∃ I : SB (Matrix.SpecialLinearGroup (Fin 2) K) →ₗ[ℂ] ℂ,
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (a a' : SB (Matrix.SpecialLinearGroup (Fin 2) K)),
        (∀ m, a'.1 m = a.1 (m * g)) → I a' = I a) ∧
      (∀ (x : GL (Fin 2) K) (a a' : SB (Matrix.SpecialLinearGroup (Fin 2) K)),
        (∀ m m' : Matrix.SpecialLinearGroup (Fin 2) K, m'.1 = (x⁻¹).val * m.1 * x.val → a'.1 m = a.1 m') →
          I a' = I a) ∧
      (∀ (U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (a : SB (Matrix.SpecialLinearGroup (Fin 2) K)),
        IsOpen (U : Set (Matrix.SpecialLinearGroup (Fin 2) K)) → a.1 = ind U → I a ≠ 0) := by
  let I : SB (Matrix.SpecialLinearGroup (Fin 2) K) →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ m, a.1 m ∂(Measure.haar)
      map_add' := fun a b => integral_add (integrable_SB a) (integrable_SB b)
      map_smul' := fun c a => integral_smul c a.1 }
  have hI : ∀ a, I a = ∫ m, a.1 m ∂(Measure.haar) := fun _ => rfl
  refine ⟨I, ?_, ?_, ?_⟩
  · intro g a a' h
    have hm : ∀ m, m * g = g * cjE (Matrix.SpecialLinearGroup.toGL g) m := by
      intro m
      apply Subtype.ext
      show m.1 * g.1 = g.1 * (((Matrix.SpecialLinearGroup.toGL g)⁻¹).val * m.1 * (Matrix.SpecialLinearGroup.toGL g).val)
      have e : g.1 * ((Matrix.SpecialLinearGroup.toGL g)⁻¹).val = 1 :=
        Units.mul_inv (Matrix.SpecialLinearGroup.toGL g)
      rw [← mul_assoc, ← mul_assoc, e, one_mul]
      rfl
    rw [hI, hI]
    simp_rw [h, hm]
    rw [integral_cjE h2 _ (fun y => a.1 (g * y))]
    exact integral_mul_left_eq_self a.1 g
  · intro x a a' h
    rw [hI, hI]
    simp_rw [fun m => h m (cjE x m) rfl]
    exact integral_cjE h2 x a.1
  · intro U a hU ha
    have hs : Function.support a.1 = (U : Set _) := by
      rw [ha]
      ext m
      by_cases hm : m ∈ (U : Set _) <;> simp [ind, hm]
    have hfin : (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) (U : Set _) ≠ ⊤ := by
      have hc : IsCompact (tsupport a.1) := a.2.2
      exact ((measure_mono (hs ▸ subset_tsupport a.1)).trans_lt hc.measure_lt_top).ne
    have hpos : (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) (U : Set _) ≠ 0 :=
      (hU.measure_pos _ ⟨1, U.one_mem⟩).ne'
    rw [hI, ha]
    unfold ind
    rw [integral_indicator_const _ hU.measurableSet]
    simp only [Measure.real, smul_eq_mul, Complex.real_smul, mul_one]
    exact_mod_cast (ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩)

end

end UpperTheory.ConvolutionTheory.R2.I.CentralConjugation

theorem UpperTheory.ConvolutionTheory.R2.I.invI :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∃ I : SB (SL v) →ₗ[ℂ] ℂ, InvI I := by
  intro F _ _ v
  letI : MeasurableSpace (SL v) := borel _
  haveI : BorelSpace (SL v) := ⟨rfl⟩
  haveI : LocallyCompactSpace (M2 v) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → Kv v))
  haveI : LocallyCompactSpace (SL v) :=
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := Kv v)).locallyCompactSpace
  have h2 : (2 : Kv v) ≠ 0 := by
    haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
    exact two_ne_zero
  obtain ⟨I, h₁, h₂, h₃⟩ := UpperTheory.ConvolutionTheory.R2.I.CentralConjugation.exists_I (K := Kv v) h2
  exact ⟨I, ⟨h₁, h₂, h₃⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PtL
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.ptL :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : M2 v → ℂ) (x : GLv v) (X : M2 v),
      Pt a ((x⁻¹).val * X) = ((ab (idl v (Matrix.GeneralLinearGroup.det x)) : ℝ) : ℂ) * Pt (fun m => a ((x⁻¹).val * m * (dd x).val)) X := by
  intro F _ _ v a x X
  set t : (Kv v)ˣ := Matrix.GeneralLinearGroup.det x with ht
  have htv : (t : Kv v) = (x.val).det := by
    rw [ht, Matrix.GeneralLinearGroup.val_det_apply]
  have hxx : x.val * (x⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hxx' : (x⁻¹).val * x.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : (t : Kv v) * ((x⁻¹).val).det = 1 := by
    rw [htv, ← Matrix.det_mul, hxx, Matrix.det_one]
  have htt : ((t⁻¹ : (Kv v)ˣ) : Kv v) * (t : Kv v) = 1 := Units.inv_mul t
  have htt' : (t : Kv v) * ((t⁻¹ : (Kv v)ˣ) : Kv v) = 1 := Units.mul_inv t
  let A : M2 v := (t : Kv v) • (x⁻¹).val
  let B : M2 v := ((t⁻¹ : (Kv v)ˣ) : Kv v) • x.val
  have hAB : A * B = 1 := by
    simp only [A, B, Matrix.smul_mul, Matrix.mul_smul, hxx', smul_smul, htt, one_smul]
  have hBA : B * A = 1 := by
    simp only [A, B, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul, htt', one_smul]
  let L : (Fin 2 → Kv v) ≃ₗ[Kv v] (Fin 2 → Kv v) := Matrix.toLin'OfInv hBA hAB
  have hL : ∀ y, L y = A *ᵥ y := fun y => rfl
  have hLdet : ((LinearEquiv.det L : (Kv v)ˣ) : Kv v) = t := by
    have h1 : ((LinearEquiv.det L : (Kv v)ˣ) : Kv v) = A.det := by
      rw [LinearEquiv.coe_det]
      exact LinearMap.det_toLin' A
    rw [h1, Matrix.det_smul, Fintype.card_fin, pow_two, mul_assoc, hdet, mul_one]
  have hLu : LinearEquiv.det L = t := Units.ext hLdet
  have hmod : (((distribHaarChar (Kv v) t : NNReal) : ℝ) : ℂ) = ((ab (idl v t) : ℝ) : ℂ) := by
    rw [(UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.2.2.2.2 t, GroundTheory.LocalField.distribHaarChar_eq_modulus]
  have hne : ((ab (idl v t) : ℝ) : ℂ) ≠ 0 := by
    rw [← hmod]
    exact_mod_cast (distribHaarChar_pos (A := Kv v) (g := t)).ne'
  haveI : (μ2 v).IsAddHaarMeasure := by
    unfold μ2
    infer_instance
  have key := GlobalTheory.DetScale.integral_comp_linearEquiv (k := Kv v) (μ2 v) L
    (fun c' => a (cols (fun i => ((x⁻¹).val * X) i 1) c') *
      ψl v (((x⁻¹).val * X) 0 0 * c' 1 - ((x⁻¹).val * X) 1 0 * c' 0))
  rw [hLu, hmod] at key
  have hpt : ∀ y : Fin 2 → Kv v,
      a ((x⁻¹).val * cols (fun i => X i 1) y * (dd x).val) * ψl v (X 0 0 * y 1 - X 1 0 * y 0) =
      a (cols (fun i => ((x⁻¹).val * X) i 1) (L y)) *
        ψl v (((x⁻¹).val * X) 0 0 * (L y) 1 - ((x⁻¹).val * X) 1 0 * (L y) 0) := by
    intro y
    have hd2 := hdet
    rw [Matrix.det_fin_two] at hd2
    have e1 : (x⁻¹).val * cols (fun i => X i 1) y * (dd x).val =
        cols (fun i => ((x⁻¹).val * X) i 1) (L y) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hL, A, cols, dd, dL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, ← ht] <;> ring
    have e2 : X 0 0 * y 1 - X 1 0 * y 0 =
        ((x⁻¹).val * X) 0 0 * (L y) 1 - ((x⁻¹).val * X) 1 0 * (L y) 0 := by
      simp only [hL, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
      linear_combination (-(X 0 0 * y 1 - X 1 0 * y 0)) * hd2
    rw [e1, e2]
  unfold Pt
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [show (fun a_1 => a (cols (fun i => ((x⁻¹).val * X) i 1) (L a_1)) * ψl v (((x⁻¹).val * X) 0 0 * (L a_1) 1 - ((x⁻¹).val * X) 1 0 * (L a_1) 0)) = _ from rfl]
  rw [key, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.TranslateMemSB
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem ind_mem_SB (U : Subgroup G) (ho : IsOpen (U : Set G)) (hc : IsCompact (U : Set G)) :
    ind U ∈ SB G := by
  have hcl : IsClopen (U : Set G) := ⟨U.isClosed_of_isOpen ho, ho⟩
  refine GroundTheory.LocalField.mem_schwartzBruhat.mpr ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ U
    · refine ⟨U, ho, hx, fun y hy => ?_⟩
      simp [ind, Set.indicator, hx, show y ∈ U from hy]
    · refine ⟨(U : Set G)ᶜ, hcl.compl.isOpen, hx, fun y hy => ?_⟩
      simp [ind, Set.indicator, hx, show y ∉ U from hy]
  · refine HasCompactSupport.intro hc fun x hx => ?_
    simp [ind, Set.indicator, show x ∉ U from hx]

private theorem translate_mem_SB (a : SB G) (g : G) : (fun m => a.1 (m * g)) ∈ SB G := by
  obtain ⟨h1, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.mp a.2
  exact GroundTheory.LocalField.mem_schwartzBruhat.mpr
    ⟨h1.comp_continuous (continuous_mul_const g), h2.comp_homeomorph (Homeomorph.mulRight g)⟩

private theorem scale (B : SB G →ₗ[ℂ] ℂ) (U U' : Subgroup G) (s : Finset G) (hs : ∀ g ∈ s, g ∈ U)
    (hsum : ∀ x, ind U x = ∑ g ∈ s, ind U' (x * g⁻¹)) (a a' : SB G) (ha : a.1 = ind U)
    (ha' : a'.1 = ind U')
    (hB : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → B b' = B b) :
    B a = (s.card : ℂ) * B a' := by
  let t : G → SB G := fun g => ⟨fun m => a'.1 (m * g⁻¹), translate_mem_SB a' g⁻¹⟩
  have hat : a = ∑ g ∈ s, t g := by
    apply Subtype.ext
    funext x
    rw [ha, hsum x, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    change ind U' (x * g⁻¹) = a'.1 (x * g⁻¹)
    rw [ha']
  have ht : ∀ g ∈ s, B (t g) = B a' := fun g hg =>
    hB g⁻¹ (U.inv_mem (hs g hg)) a' (t g) fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hat, map_sum, Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]

variable [T2Space G]

private theorem cross_le (B C : SB G →ₗ[ℂ] ℂ) (U U' : Subgroup G) (hle : U' ≤ U)
    (hc : IsCompact (U : Set G)) (ho : IsOpen (U' : Set G)) (a a' : SB G) (ha : a.1 = ind U)
    (ha' : a'.1 = ind U')
    (hB : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → B b' = B b)
    (hC : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → C b' = C b) :
    B a * C a' = B a' * C a := by
  obtain ⟨s, -, hs, hsum⟩ := cosetSum G U U' hle hc ho
  rw [scale B U U' s hs hsum a a' ha ha' hB, scale C U U' s hs hsum a a' ha ha' hC]
  ring

private theorem core {V : Type} [AddCommGroup V] [Module ℂ V] (hL : Lgrp G) (act : G → V →ₗ[ℂ] V)
    (hact : ∀ f, {g | act g f = f} ∈ 𝓝 (1 : G)) (I : SB G →ₗ[ℂ] ℂ)
    (hI : ∀ (g : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * g)) → I a' = I a)
    (hne : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U → I a ≠ 0)
    (β : V →ₗ[ℂ] SB G →ₗ[ℂ] ℂ)
    (hβ : ∀ (g : G) f (a a' : SB G), (∀ m, a'.1 m = a.1 (m * g)) → β (act g f) a' = β f a) :
    ∃ Λ : V →ₗ[ℂ] ℂ, ∀ f (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      (∀ g ∈ U, act g f = f) → β f a = I a * Λ f := by

  have hinv : ∀ (f : V) (U : Subgroup G), (∀ g ∈ U, act g f = f) →
      ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → β f b' = β f b := by
    intro f U hf g hg b b' hb
    have := hβ g f b b' hb
    rwa [hf g hg] at this

  have hex : ∀ f f' : V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧
      (∀ g ∈ U, act g f = f) ∧ (∀ g ∈ U, act g f' = f') := by
    intro f f'
    obtain ⟨U, ho, hc, hsub⟩ := hL _ (Filter.inter_mem (hact f) (hact f'))
    exact ⟨U, ho, hc, fun g hg => (hsub hg).1, fun g hg => (hsub hg).2⟩

  have hcpt : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      IsCompact (U : Set G) := by
    intro U a ho ha
    obtain ⟨-, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.mp a.2
    refine IsCompact.of_isClosed_subset h2 (U.isClosed_of_isOpen ho) fun x hx => ?_
    refine subset_tsupport _ ?_
    rw [Function.mem_support, ha]
    simp [ind, Set.indicator, show x ∈ U from hx]

  have hcross : ∀ (f : V) (U₁ U₂ : Subgroup G) (a₁ a₂ : SB G), IsOpen (U₁ : Set G) →
      IsOpen (U₂ : Set G) → a₁.1 = ind U₁ → a₂.1 = ind U₂ → (∀ g ∈ U₁, act g f = f) →
      (∀ g ∈ U₂, act g f = f) → β f a₁ * I a₂ = β f a₂ * I a₁ := by
    intro f U₁ U₂ a₁ a₂ ho₁ ho₂ h₁ h₂ hf₁ hf₂
    have hc₁ := hcpt U₁ a₁ ho₁ h₁
    have hc₂ := hcpt U₂ a₂ ho₂ h₂
    have ho₃ : IsOpen ((U₁ ⊓ U₂ : Subgroup G) : Set G) := by
      rw [Subgroup.coe_inf]
      exact ho₁.inter ho₂
    have hc₃ : IsCompact ((U₁ ⊓ U₂ : Subgroup G) : Set G) :=
      IsCompact.of_isClosed_subset hc₁ ((U₁ ⊓ U₂).isClosed_of_isOpen ho₃) fun x hx => hx.1
    let a₃ : SB G := ⟨ind (U₁ ⊓ U₂), ind_mem_SB _ ho₃ hc₃⟩
    have e₁ := cross_le (β f) I U₁ (U₁ ⊓ U₂) inf_le_left hc₁ ho₃ a₁ a₃ h₁ rfl
      (hinv f U₁ hf₁) fun g _ => hI g
    have e₂ := cross_le (β f) I U₂ (U₁ ⊓ U₂) inf_le_right hc₂ ho₃ a₂ a₃ h₂ rfl
      (hinv f U₂ hf₂) fun g _ => hI g
    have h₃ : I a₃ ≠ 0 := hne _ a₃ ho₃ rfl
    apply mul_right_cancel₀ h₃
    linear_combination I a₂ * e₁ - I a₁ * e₂
  choose W hWo hWc hWf _ using fun f : V => hex f f
  let A : V → SB G := fun f => ⟨ind (W f), ind_mem_SB _ (hWo f) (hWc f)⟩
  let Λ₀ : V → ℂ := fun f => β f (A f) / I (A f)
  have key : ∀ f (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      (∀ g ∈ U, act g f = f) → β f a = I a * Λ₀ f := by
    intro f U a ho ha hf
    have h := hcross f U (W f) a (A f) ho (hWo f) ha rfl hf (hWf f)
    have hA : I (A f) ≠ 0 := hne _ (A f) (hWo f) rfl
    change β f a = I a * (β f (A f) / I (A f))
    field_simp
    linear_combination h
  have hadd : ∀ f f', Λ₀ (f + f') = Λ₀ f + Λ₀ f' := by
    intro f f'
    obtain ⟨U, ho, hc, h₁, h₂⟩ := hex f f'
    let a : SB G := ⟨ind U, ind_mem_SB _ ho hc⟩
    have hIa : I a ≠ 0 := hne U a ho rfl
    apply mul_left_cancel₀ hIa
    have hf : ∀ g ∈ U, act g (f + f') = f + f' := fun g hg => by
      rw [map_add (f := _), h₁ g hg, h₂ g hg]
    rw [mul_add, ← key f U a ho rfl h₁, ← key f' U a ho rfl h₂, ← key (f + f') U a ho rfl hf,
      map_add, LinearMap.add_apply]
  have hsmul : ∀ (c : ℂ) f, Λ₀ (c • f) = c * Λ₀ f := by
    intro c f
    obtain ⟨U, ho, hc, h₁, -⟩ := hex f f
    let a : SB G := ⟨ind U, ind_mem_SB _ ho hc⟩
    have hIa : I a ≠ 0 := hne U a ho rfl
    apply mul_left_cancel₀ hIa
    have hf : ∀ g ∈ U, act g (c • f) = c • f := fun g hg => by
      rw [map_smul, h₁ g hg]
    rw [mul_left_comm, ← key f U a ho rfl h₁, ← key (c • f) U a ho rfl hf, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
  exact ⟨⟨⟨Λ₀, hadd⟩, fun c f => by simpa using hsmul c f⟩, key⟩

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.lamEx :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ (I : SB (SL v) →ₗ[ℂ] ℂ), InvI I → ∀ β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      ∃ Λ : V →ₗ[ℂ] ℂ, ∀ f (U : Subgroup (SL v)) (a : SB (SL v)), IsOpen (U : Set (SL v)) → a.1 = ind U →
        (∀ g ∈ U, ρ (Matrix.SpecialLinearGroup.toGL g) f = f) → β f a = I a * Λ f := by
  intro F _ _ v V _ _ ρ hρ I hI β hβ
  refine core (lgrp F v).1 (fun g => ρ (Matrix.SpecialLinearGroup.toGL g)) (fun f => ?_) I
    hI.right hI.ne β hβ
  have ho : IsOpen {g : SL v | ρ (Matrix.SpecialLinearGroup.toGL g) f = f} :=
    (hρ f).preimage Matrix.SpecialLinearGroup.continuous_toGL
  exact ho.mem_nhds (by simp)
end

