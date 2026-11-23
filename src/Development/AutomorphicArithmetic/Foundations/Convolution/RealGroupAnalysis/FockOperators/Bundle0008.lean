module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FW
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w, O.f D.δ w * W.Om (wW F) = -(W.Om (wW F) * O.e D.δ w) := by
  intro F E _ _ _ _ _ _ _ D W O w
  have hc : cw w (rt D.δ) ≠ 0 := (coordMk F E D).2.2.1 w
  have hcc : cc ≠ 0 := by
    simp [cc, Real.pi_ne_zero]
  have h2 : ∀ i j, O.d w i * O.d w j * W.Om (wW F) =
      W.Om (wW F) * (O.p D.δ w i * O.p D.δ w j) := fun i j => by
    calc
      _ = O.d w i * (W.Om (wW F) * O.p D.δ w j) := by rw [mul_assoc, dW F E D W O w j]
      _ = (O.d w i * W.Om (wW F)) * O.p D.δ w j := by rw [mul_assoc]
      _ = _ := by rw [dW F E D W O w i, mul_assoc]
  have comm : O.x w 0 * O.x w 1 = O.x w 1 * O.x w 0 := (weyl F O w w 0 1).1
  have p0 : O.p D.δ w 0 = (-cc) • O.x w 1 := rfl
  have p1 : O.p D.δ w 1 = (-cc) • O.x w 0 := rfl
  have p2 : O.p D.δ w 2 = (2 * cc) • O.x w 2 := rfl
  have p3 : O.p D.δ w 3 = (-2 * cw w (rt D.δ) * cc) • O.x w 3 := rfl
  have key : (4 : ℂ)⁻¹ • (O.p D.δ w 2 * O.p D.δ w 2) -
      (4 * cw w (rt D.δ))⁻¹ • (O.p D.δ w 3 * O.p D.δ w 3) -
      O.p D.δ w 1 * O.p D.δ w 0 = cc • O.e D.δ w := by
    rw [p0, p1, p2, p3, Ops.e]
    simp only [smul_mul_smul_comm, comm]
    match_scalars <;> field_simp <;> ring
  have move : ((4 : ℂ)⁻¹ • (O.d w 2 * O.d w 2) - (4 * cw w (rt D.δ))⁻¹ • (O.d w 3 * O.d w 3) -
      O.d w 1 * O.d w 0) * W.Om (wW F) =
      W.Om (wW F) * ((4 : ℂ)⁻¹ • (O.p D.δ w 2 * O.p D.δ w 2) -
        (4 * cw w (rt D.δ))⁻¹ • (O.p D.δ w 3 * O.p D.δ w 3) - O.p D.δ w 1 * O.p D.δ w 0) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, h2]
  rw [Ops.f, smul_mul_assoc, move, key, mul_smul_comm, smul_smul,
    neg_mul, inv_mul_cancel₀ hcc, neg_smul, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkD
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkD :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (N : Submodule ℂ (S4 F)), N ≤ Vac δ → ∀ m w i, ∀ φ ∈ O.Fk N m, O.d w i φ ∈ O.Fk N (m + 1) := by
  intro F _ _ _ δ O N hN m
  obtain ⟨hmono, hx, -⟩ := UpperTheory.ConvolutionTheory.R2.Fo.fkBasic F O
  induction m with
  | zero =>
    intro w i φ hφ
    have hφ' : φ ∈ N := hφ
    rw [UpperTheory.ConvolutionTheory.R2.Fo.vacAnn F δ O φ (hN hφ') w i]
    exact Submodule.smul_mem _ _ (hx N 0 w i φ hφ)
  | succ m ih =>
    intro w i
    have hle : O.Fk N (m + 1) ≤ (O.Fk N (m + 1 + 1)).comap (O.d w i) := by
      change O.Fk N m ⊔ ⨆ w', ⨆ j, (O.Fk N m).map (O.x w' j) ≤ _
      refine sup_le ?_ (iSup_le fun w' => iSup_le fun j => ?_)
      · intro ψ hψ
        exact hmono N N le_rfl (m + 1) (m + 1 + 1) (Nat.le_succ _) (ih w i ψ hψ)
      · rw [Submodule.map_le_iff_le_comap]
        intro ψ hψ
        change O.d w i (O.x w' j ψ) ∈ O.Fk N (m + 1 + 1)
        have hc := congrArg (fun T : Module.End ℂ (S4 F) => T ψ) (UpperTheory.ConvolutionTheory.R2.Fo.weyl F O w w' i j).2
        have hc' : O.d w i (O.x w' j ψ) = O.x w' j (O.d w i ψ) + (if w = w' ∧ i = j then (1 : Module.End ℂ (S4 F)) else 0) ψ := hc
        rw [hc']
        refine Submodule.add_mem _ (hx N (m + 1) w' j _ (ih w i ψ hψ)) ?_
        split_ifs
        · exact hmono N N le_rfl m (m + 1 + 1) (by omega) hψ
        · exact Submodule.zero_mem _
    exact fun φ hφ => hle hφ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PForm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma p_form {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F) (δ : F)
    (w : InfinitePlace F) (i : Fin 4) : ∃ (c : ℂ) (k : Fin 4), O.p δ w i = c • O.x w k := by
  fin_cases i
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

private lemma p_comm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F) (δ : F)
    (w w' : InfinitePlace F) (i j : Fin 4) :
    O.p δ w i * O.p δ w' j = O.p δ w' j * O.p δ w i := by
  obtain ⟨c, k, h⟩ := p_form O δ w i
  obtain ⟨c', k', h'⟩ := p_form O δ w' j
  have hx : O.x w k * O.x w' k' = O.x w' k' * O.x w k := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    change (O.x w k (O.x w' k' φ)).1 v = (O.x w' k' (O.x w k φ)).1 v
    rw [O.x_apply, O.x_apply, O.x_apply, O.x_apply, mul_left_comm]
  rw [h, h']
  simp only [smul_mul_smul, hx, mul_comm c c']

theorem UpperTheory.ConvolutionTheory.R2.Fo.dComm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w w' i j, O.d w i * O.d w' j = O.d w' j * O.d w i := by
  intro F E _ _ _ _ _ _ _ D W O w w' i j
  have hinv : W.Om (wW F) * W.Om (wW F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have key : O.d w i * O.d w' j * W.Om (wW F) = O.d w' j * O.d w i * W.Om (wW F) := by
    calc O.d w i * O.d w' j * W.Om (wW F)
        = O.d w i * (O.d w' j * W.Om (wW F)) := mul_assoc _ _ _
      _ = O.d w i * (W.Om (wW F) * O.p D.δ w' j) := congrArg (O.d w i * ·) (dW F E D W O w' j)
      _ = (O.d w i * W.Om (wW F)) * O.p D.δ w' j := (mul_assoc _ _ _).symm
      _ = (W.Om (wW F) * O.p D.δ w i) * O.p D.δ w' j := congrArg (· * O.p D.δ w' j) (dW F E D W O w i)
      _ = W.Om (wW F) * (O.p D.δ w i * O.p D.δ w' j) := mul_assoc _ _ _
      _ = W.Om (wW F) * (O.p D.δ w' j * O.p D.δ w i) := by rw [p_comm O D.δ w w' i j]
      _ = (W.Om (wW F) * O.p D.δ w' j) * O.p D.δ w i := (mul_assoc _ _ _).symm
      _ = (O.d w' j * W.Om (wW F)) * O.p D.δ w i := congrArg (· * O.p D.δ w i) (dW F E D W O w' j).symm
      _ = O.d w' j * (W.Om (wW F) * O.p D.δ w i) := mul_assoc _ _ _
      _ = O.d w' j * (O.d w i * W.Om (wW F)) := congrArg (O.d w' j * ·) (dW F E D W O w i).symm
      _ = O.d w' j * O.d w i * W.Om (wW F) := (mul_assoc _ _ _).symm
  calc O.d w i * O.d w' j
      = O.d w i * O.d w' j * (W.Om (wW F) * W.Om (wW F)⁻¹) := by rw [hinv, mul_one]
    _ = O.d w i * O.d w' j * W.Om (wW F) * W.Om (wW F)⁻¹ := (mul_assoc _ _ _).symm
    _ = O.d w' j * O.d w i * W.Om (wW F) * W.Om (wW F)⁻¹ := by rw [key]
    _ = O.d w' j * O.d w i * (W.Om (wW F) * W.Om (wW F)⁻¹) := mul_assoc _ _ _
    _ = O.d w' j * O.d w i := by rw [hinv, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.WeilSignAnticommuteOperator
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem wW_sq (F : Type) [Field F] [NumberField F] : wW F * wW F = mD (-1 : (A F)ˣ) := by
  apply Subtype.ext
  change (wW F).1 * (wW F).1 = (mD (-1 : (A F)ˣ)).1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wW, mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem cw_neg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (a : A F) :
    cw w (-a) = -cw w a := by
  simp [cw, map_neg]

private theorem weilSign_anticommute_operator {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) (O : Ops F) (w : InfinitePlace F) (j : Fin 4) :
    W.Om (mD (-1 : (A F)ˣ)) * O.x w j = -(O.x w j * W.Om (mD (-1 : (A F)ˣ))) := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext v
  have h1 := W.Om_m (-1 : (A F)ˣ) (O.x w j φ) v
  have h2 := O.x_apply w j (W.Om (mD (-1 : (A F)ˣ)) φ) v
  have h3 := W.Om_m (-1 : (A F)ˣ) φ v
  have h4 := O.x_apply w j φ (fun i => (((-1 : (A F)ˣ) : A F)) * v i)
  change (W.Om (mD (-1 : (A F)ˣ)) (O.x w j φ)).1 v = -((O.x w j (W.Om (mD (-1 : (A F)ˣ)) φ)).1 v)
  rw [h1, h2, h3, h4]
  have h5 : cw w ((((-1 : (A F)ˣ) : A F)) * v j) = -cw w (v j) := by
    rw [Units.val_neg, Units.val_one, neg_one_mul, cw_neg]
  rw [h5]
  ring

private theorem R_p {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) (O : Ops F) (w : InfinitePlace F) (i : Fin 4) :
    W.Om (mD (-1 : (A F)ˣ)) * O.p D.δ w i = -(O.p D.δ w i * W.Om (mD (-1 : (A F)ˣ))) := by
  fin_cases i <;> simp [Ops.p, mul_smul_comm, smul_mul_assoc, weilSign_anticommute_operator W O w]

theorem UpperTheory.ConvolutionTheory.R2.Fo.pW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w i, O.p D.δ w i * W.Om (wW F) = -(W.Om (wW F) * O.d w i) := by
  intro F E _ _ _ _ _ _ _ D W O w i
  have hd := UpperTheory.ConvolutionTheory.R2.Fo.dW F E D W O w i
  have hR : W.Om (wW F) * W.Om (wW F) = W.Om (mD (-1 : (A F)ˣ)) := by
    rw [← map_mul, wW_sq]
  have hinv : W.Om (wW F) * W.Om (wW F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have key : (W.Om (wW F) * O.d w i) * W.Om (wW F) = (-(O.p D.δ w i * W.Om (wW F))) * W.Om (wW F) := by
    calc (W.Om (wW F) * O.d w i) * W.Om (wW F)
        = W.Om (wW F) * (O.d w i * W.Om (wW F)) := mul_assoc _ _ _
      _ = (W.Om (wW F) * W.Om (wW F)) * O.p D.δ w i := by rw [hd, mul_assoc]
      _ = -(O.p D.δ w i * (W.Om (wW F) * W.Om (wW F))) := by rw [hR, R_p W O w i]
      _ = (-(O.p D.δ w i * W.Om (wW F))) * W.Om (wW F) := by rw [neg_mul, mul_assoc]
  have key2 : W.Om (wW F) * O.d w i = -(O.p D.δ w i * W.Om (wW F)) := by
    have := congrArg (· * W.Om (wW F)⁻¹) key
    simpa only [mul_assoc, hinv, mul_one] using this
  rw [key2, neg_neg]
end

