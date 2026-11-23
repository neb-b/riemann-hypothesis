module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import GroundTheory.AutomorphicForms.FourierWhittaker

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.InfDec
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

private theorem real_dec {ι : Type} (X : GL (Fin 2) (ι → ℝ)) :
    ∃ (s : (ι → ℝ)ˣ) (g : GL (Fin 2) (ι → ℝ)) (k : Matrix.unitaryGroup (Fin 2) (ι → ℝ)),
      Matrix.GeneralLinearGroup.det g = 1 ∧
        X = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (g * Unitary.toUnits k) := by
  classical
  set D : (ι → ℝ)ˣ := Matrix.GeneralLinearGroup.det X with hD
  have hw : ∀ w, (D : ι → ℝ) w ≠ 0 := fun w => ((Pi.isUnit_iff.1 D.isUnit) w).ne_zero
  have hpos : ∀ w, 0 < Real.sqrt |(D : ι → ℝ) w| := fun w => Real.sqrt_pos.2 (abs_pos.2 (hw w))
  let s : (ι → ℝ)ˣ :=
    ⟨fun w => Real.sqrt |(D : ι → ℝ) w|, fun w => (Real.sqrt |(D : ι → ℝ) w|)⁻¹,
      funext fun w => mul_inv_cancel₀ (hpos w).ne', funext fun w => inv_mul_cancel₀ (hpos w).ne'⟩
  let e : ι → ℝ := fun w => if 0 < (D : ι → ℝ) w then 1 else -1
  have hee : e * e = 1 := by
    funext w
    by_cases h : 0 < (D : ι → ℝ) w <;> simp [e, h]
  have hse : (s : ι → ℝ) * s * e = D := by
    funext w
    have h2 : Real.sqrt |(D : ι → ℝ) w| * Real.sqrt |(D : ι → ℝ) w| = |(D : ι → ℝ) w| :=
      Real.mul_self_sqrt (abs_nonneg _)
    change Real.sqrt |(D : ι → ℝ) w| * Real.sqrt |(D : ι → ℝ) w| * e w = _
    rw [h2]
    by_cases h : 0 < (D : ι → ℝ) w
    · simp [e, h, abs_of_pos h]
    · have h' : (D : ι → ℝ) w < 0 := lt_of_le_of_ne (not_lt.1 h) (hw w)
      simp [e, h, abs_of_neg h']
  have hstar : star e = e := by
    funext w
    simp
  let K : Matrix (Fin 2) (Fin 2) (ι → ℝ) := !![1, 0; 0, e]
  have hKK : K * K = 1 := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [K, Matrix.mul_apply, Fin.sum_univ_two, hee]
  have hKs : star K = K := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [K, Matrix.star_eq_conjTranspose, hstar]
  have hKmem : K ∈ Matrix.unitaryGroup (Fin 2) (ι → ℝ) := by
    rw [Matrix.mem_unitaryGroup_iff, hKs]
    exact hKK
  let k : Matrix.unitaryGroup (Fin 2) (ι → ℝ) := ⟨K, hKmem⟩
  have hk : (Unitary.toUnits k) * (Unitary.toUnits k) = 1 := Units.ext hKK
  have hdetk : (Matrix.GeneralLinearGroup.det (Unitary.toUnits k) : ι → ℝ) = e := by
    change K.det = e
    simp [K, Matrix.det_fin_two]
  have hdets : ∀ t : (ι → ℝ)ˣ,
      (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) t) : ι → ℝ) = t * t := by
    intro t
    change (Matrix.GeneralLinearGroup.scalar (Fin 2) t).val.det = _
    simp [Matrix.det_fin_two, sq]
  refine ⟨s, Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹ * X * Unitary.toUnits k, k, ?_, ?_⟩
  · refine Units.ext ?_
    rw [map_mul, map_mul]
    simp only [Units.val_mul, hdetk, hdets, Units.val_one]
    rw [← hD, ← hse]
    funext w
    have h1 := congrFun hee w
    have h2 : (s : ι → ℝ) w * ((s⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) w = 1 := congrFun s.mul_inv w
    simp only [Pi.mul_apply, Pi.one_apply] at h1 ⊢
    calc _ = (((s : ι → ℝ) w * ((s⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) w) ^ 2) * (e w * e w) := by ring
      _ = 1 := by rw [h2, h1]; simp
  · have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) s * Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹ = 1 := by
      rw [← map_mul]; simp
    rw [mul_assoc _ _ (Unitary.toUnits k), hk, mul_one, ← mul_assoc, hsc, one_mul]

theorem UpperTheory.ConvolutionTheory.R2.Pp.infDec :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.InfDec F := by
  intro F _ _ _ x
  obtain ⟨s, g, k, hg, hx⟩ := real_dec (GeneralLinearGroup.map (TR.pInf F) x)
  have hdet : GeneralLinearGroup.det (TR.infGL F 2 g) = 1 := by
    rw [TR.det_infGL, hg, map_one]
  have hdet' : (TR.infGL F 2 g).val.det = 1 := congrArg Units.val hdet
  let G : G1 F := ⟨(TR.infGL F 2 g).val, hdet'⟩
  have hG : gl G = TR.infGL F 2 g := Units.ext rfl
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F s) =
      TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) s) := by
    have hs : ∀ y, TR.pInf F (TR.sInf F y) = y := fun y => (TR.infEq F).symm_apply_apply y
    have hi : TR.pInf F (TR.infId F s).val = s.val := by
      change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
      simp [hs]
    have hf : pFin F (TR.infId F s).val = 1 := by
      change (1 : Af F) - 0 + 0 = 1
      simp
    refine TR.ga_ext ?_ ?_
    · rw [TR.pInf_infGL]
      ext i j
      by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, hi]
    · rw [TR.pFin_infGL]
      ext i j
      by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, hf]
  refine ⟨G, TR.infId F s, k, GeneralLinearGroup.map (pFin F) x, ?_, ?_⟩
  · intro i j
    have h := congrArg (fun h : GL (Fin 2) (Af F) => h.val i j) (TR.pFin_infGL (E := F) g)
    have h1 : ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 = (1 : GL (Fin 2) (Af F)).val i j := by
      by_cases e : i = j
      · simp only [Matrix.one_apply, e, if_true, Units.val_one]
        rfl
      · simp [Matrix.one_apply, e]
    rw [h1]
    exact h
  · rw [hsc, hG]
    conv_lhs => rw [← TR.infGL_mul_finGL x, hx]
    simp only [map_mul, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

namespace UpperTheory.ConvolutionTheory.R2.Pp

variable {F : Type} [Field F] [NumberField F]

theorem vn (q : A F) : (nU q).val = !![1, q; 0, 1] := rfl

theorem n_add (x y : A F) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem n_zero : gl (nU (0 : A F)) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn]

theorem cont_n : Continuous fun q : A F => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A F, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

theorem rat_n (k : F) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

theorem rat_a (t : Fˣ) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = aE (IdeleGroup.diagonal F t) := by
  refine ⟨⟨!![(t : F), 0; 0, 1], !![((t⁻¹ : Fˣ) : F), 0; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![(t : F), 0; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE]

theorem a_n (t : (A F)ˣ) (b : A F) : aE t * gl (nU b) = gl (nU ((t : A F) * b)) * aE t := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, aE, Matrix.mul_apply, Fin.sum_univ_two]

theorem ψ_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

theorem ψ_rt (k : F) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

theorem norm_ψ (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _

theorem cont_ψ : Continuous (ψ (F := F)) := continuous_subtype_val.comp continuous_adelicChar

theorem exists_cpt : ∃ C : Set (A F), IsCompact C ∧ fundamentalSet F ⊆ C :=
  ⟨_, (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F),
    fun _ hx => ⟨subset_closure hx.1, hx.2⟩⟩

theorem int_one {ι : Type} [Fintype ι] [Unique ι] (h : A F → ℂ) :
    ∫ x in vecDomain F ι, h (x default) ∂(vecMeasure F ι) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  have hp := measurePreserving_funUnique (adeleMeasure F) ι
  have e : vecDomain F ι = MeasurableEquiv.funUnique ι (A F) ⁻¹' fundamentalSet F := by
    ext x
    exact ⟨fun hx => hx default trivial, fun hx i _ => by rw [Unique.eq_default i]; exact hx⟩
  rw [e]
  convert hp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) h (fundamentalSet F) using 2
  all_goals first | rfl | congr!

theorem int_add {h : A F → ℂ} (hh : ∀ k x, h (rt k + x) = h x) (a : A F) :
    ∫ b in fundamentalSet F, h (b + a) ∂(adeleMeasure F) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  rw [← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h]
  refine setIntegral_comp_add (fun _ => a) (h := fun x => h (x default)) fun ξ hξ x => ?_
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
  exact hh _ _

theorem int_mul {h : A F → ℂ} (hh : ∀ k x, h (rt k + x) = h x) (t : Fˣ) :
    ∫ b in fundamentalSet F, h (rt (t : F) * b) ∂(adeleMeasure F) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  rw [← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h,
    ← setIntegral_comp_matVec (Matrix.GeneralLinearGroup.scalar (Fin 1) t) (f := fun x => h (x default)) fun ξ hξ x => by
      obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      exact hh _ _]
  simp [matVec_apply]

theorem Lf.per {f : GL (Fin 2) (A F) → ℂ} (hf : Lf f) (k : F) (x : A F) (g : GL (Fin 2) (A F)) :
    f (gl (nU (rt k + x)) * g) = f (gl (nU x) * g) := by
  obtain ⟨γ, hγ⟩ := rat_n k
  rw [n_add, ← hγ, mul_assoc, hf.2]

theorem intOn {h : A F → ℂ} (hc : Continuous h) : IntegrableOn h (fundamentalSet F) (adeleMeasure F) := by
  obtain ⟨C, hC, hs⟩ := exists_cpt (F := F)
  exact (hc.continuousOn.integrableOn_compact hC).mono_set hs

theorem norm_Wf_le {f : GL (Fin 2) (A F) → ℂ} {g : GL (Fin 2) (A F)} {B : ℝ} (h : ∀ b, ‖f (gl (nU b) * g)‖ ≤ B) :
    ‖Wf f g‖ ≤ B := by
  have := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasure F) (s := fundamentalSet F)
    (f := fun b => f (gl (nU b) * g) * ψ b) (C := B) (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top)
    fun b _ => by rw [norm_mul, norm_ψ, mul_one]; exact h b
  rwa [measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one, mul_one] at this

end UpperTheory.ConvolutionTheory.R2.Pp
end

