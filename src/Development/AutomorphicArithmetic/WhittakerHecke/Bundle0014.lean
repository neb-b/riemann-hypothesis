module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0288
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ThetaSeriesPoissonFunctionalEquation
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private noncomputable abbrev rv (ξ : Fin 2 → ℚ) : Fin 2 → A ℚ := fun i => rt (ξ i)

private noncomputable abbrev sc (a : (A ℚ)ˣ) : GL (Fin 2) (A ℚ) := Matrix.GeneralLinearGroup.scalar (Fin 2) a

private theorem tInv_tInv (x : GL (Fin 2) (A ℚ)) : PositivityTheory.RgEis.tInv (PositivityTheory.RgEis.tInv x) = x := by
  apply Units.ext
  show ((x : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ)ᵀ = x
  rw [Matrix.transpose_transpose]

private theorem tInv_sc (a : (A ℚ)ˣ) : PositivityTheory.RgEis.tInv (sc a) = sc a⁻¹ := by
  apply Units.ext
  show (((sc a)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
  rw [← map_inv]
  have e : ((sc a⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = Matrix.diagonal fun _ => ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    rfl
  rw [e, Matrix.diagonal_transpose]

private theorem sc_mulVec (a : (A ℚ)ˣ) (x : GL (Fin 2) (A ℚ)) (v : Fin 2 → A ℚ) :
    ((sc a * x : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ v =
      fun j => (a : A ℚ) * ((x : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ v) j := by
  funext j
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem det_sc (a : (A ℚ)ˣ) : Matrix.GeneralLinearGroup.det (sc a) = a * a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [Matrix.det_fin_two, sq]

private theorem det_tInv (x : GL (Fin 2) (A ℚ)) :
    Matrix.GeneralLinearGroup.det (PositivityTheory.RgEis.tInv x) = (Matrix.GeneralLinearGroup.det x)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transpose _

private theorem iy_inv (y : ℝ) (h : y ≠ 0) : iy y⁻¹ = (iy y)⁻¹ := by
  unfold iy
  rw [dite_eq_right h, dite_eq_right (inv_ne_zero h), ← map_inv]
  congr 1
  apply Units.ext
  funext _
  rfl

private theorem ab_iy (y : ℝ) (h : y ≠ 0) : ab (iy y) = |y| := by
  unfold ab iy
  rw [dite_eq_right h]
  have := GlobalTheory.HenQ.DetSplit.ideleModule_infId (K := ℚ) ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩
  rw [this]
  simp

private theorem tsum_split {f : (Fin 2 → ℚ) → ℂ} (hf : Summable f) :
    ∑' ξ, f ξ = f 0 + ∑' ξ : Rw ℚ, f ξ.1 := by
  rw [← hf.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton]
  rfl

private theorem poisson_row {Φ : (Fin 2 → A ℚ) → ℂ} (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) (a : (A ℚ)ˣ)
    (h : GL (Fin 2) (A ℚ)) :
    Summable (fun ξ : Fin 2 → ℚ => Φ fun j => (a : A ℚ) * (rv ξ ᵥ* h.val) j) ∧
    Summable (fun ξ : Fin 2 → ℚ => adelicFourierPi ℚ Φ fun j =>
      ((a⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ ᵥ* (PositivityTheory.RgEis.tInv h).val) j) ∧
    ∑' ξ : Fin 2 → ℚ, Φ (fun j => (a : A ℚ) * (rv ξ ᵥ* h.val) j) =
      ((ab (a * a * Matrix.GeneralLinearGroup.det h) : ℝ) : ℂ)⁻¹ * ∑' ξ : Fin 2 → ℚ, adelicFourierPi ℚ Φ fun j =>
        ((a⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ ᵥ* (PositivityTheory.RgEis.tInv h).val) j := by
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 2) (A ℚ), B = sc a * PositivityTheory.RgEis.tInv h⁻¹ := ⟨_, rfl⟩
  have hl := GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem hΦ B
  obtain ⟨h1, h2, h3⟩ := poisson_of_mem_schwartzBruhatPi hl
  have hf := GlobalTheory.CompanionTheory.LtrFourier.adelicFourierPi_ltr B Φ
  have hdet : Matrix.GeneralLinearGroup.det B = a * a * Matrix.GeneralLinearGroup.det h := by
    rw [hB, map_mul, det_sc, det_tInv, map_inv, inv_inv]
  have e1 : ∀ ξ : Fin 2 → ℚ, PositivityTheory.He2M1.ltr B Φ (fun i => algebraMap ℚ (A ℚ) (ξ i)) =
      Φ fun j => (a : A ℚ) * (rv ξ ᵥ* h.val) j := by
    intro ξ
    show Φ ((B : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ _) = _
    congr 1
    rw [hB, sc_mulVec]
    funext j
    have e : ((PositivityTheory.RgEis.tInv h⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = (h.val)ᵀ := by
      show (((h⁻¹)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
      rw [inv_inv]
    rw [e, Matrix.mulVec_transpose]
  have hBi : PositivityTheory.RgEis.tInv B = sc a⁻¹ * h⁻¹ := by
    rw [hB, map_mul, tInv_sc, tInv_tInv]
  have e2 : ∀ ξ : Fin 2 → ℚ, PositivityTheory.He2M1.ltr (PositivityTheory.RgEis.tInv B) (adelicFourierPi ℚ Φ) (fun i => algebraMap ℚ (A ℚ) (ξ i)) =
      adelicFourierPi ℚ Φ fun j => ((a⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ ᵥ* (PositivityTheory.RgEis.tInv h).val) j := by
    intro ξ
    show adelicFourierPi ℚ Φ (((PositivityTheory.RgEis.tInv B : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ _) = _
    congr 1
    rw [hBi, sc_mulVec]
    funext j
    have e : ((PositivityTheory.RgEis.tInv h : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) =
        ((h⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ := rfl
    rw [e, Matrix.vecMul_transpose]
  have hc : ((ab (Matrix.GeneralLinearGroup.det B) : ℝ) : ℂ)⁻¹ ≠ 0 := by
    have : (0 : ℝ) < ab (Matrix.GeneralLinearGroup.det B) := (IdeleGroup.ideleModule ℚ _).2
    exact inv_ne_zero (Complex.ofReal_ne_zero.2 this.ne')
  rw [hf] at h2 h3
  simp only [Pi.smul_apply, smul_eq_mul, e1, e2] at h1 h2 h3
  rw [← hdet]
  refine ⟨h1.of_norm, (summable_mul_left_iff hc).1 h2.of_norm, ?_⟩
  rw [h3, tsum_mul_left]
  rfl

private theorem tInv_dM (u : (A ℚ)ˣ) : PositivityTheory.RgEis.tInv (dM u) = dM u⁻¹ := by
  apply Units.ext
  show (((dM u)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
  have e : (((dM u)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![1, 0; 0, ((u⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

private theorem tInv_gl (g : G1 ℚ) : PositivityTheory.RgEis.tInv (gl g) = gl (wW ℚ) * (gl g * (gl (wW ℚ))⁻¹) := by
  have e1 : (gl g)⁻¹ = gl g⁻¹ := (map_inv Matrix.SpecialLinearGroup.toGL g).symm
  have e2 : (gl (wW ℚ))⁻¹ = gl (wW ℚ)⁻¹ := (map_inv Matrix.SpecialLinearGroup.toGL (wW ℚ)).symm
  apply Units.ext
  show (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
  have hw : ((gl (wW ℚ) : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![0, 1; -1, 0] := rfl
  have hwi : (((gl (wW ℚ))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![0, -1; 1, 0] := by
    rw [e2]
    show Matrix.adjugate (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (A ℚ)) = _
    rw [Matrix.adjugate_fin_two]
    simp
  have hgi : (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
    rw [e1]
    show Matrix.adjugate g.1 = _
    rw [Matrix.adjugate_fin_two]
  have hg : ((gl g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![g 0 0, g 0 1; g 1 0, g 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Units.val_mul, Units.val_mul, hw, hwi, hgi, hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem tInv_h (g : G1 ℚ) (u : (A ℚ)ˣ) :
    PositivityTheory.RgEis.tInv (gl g * dM u) = gl (wW ℚ) * (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) := by
  rw [map_mul, tInv_gl, tInv_dM]
  simp only [mul_assoc]

private theorem det_h (g : G1 ℚ) (u : (A ℚ)ˣ) : Matrix.GeneralLinearGroup.det (gl g * dM u) = u := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul]
  have : ((gl g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)).det = 1 := g.det_coe
  rw [this, one_mul]
  simp [dM, Matrix.det_fin_two]

private def eW : Rw ℚ ≃ Rw ℚ where
  toFun r := ⟨![-(r.1 1), r.1 0], fun h => r.2 (by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    ext i
    fin_cases i <;> simp [h0, h1])⟩
  invFun r := ⟨![r.1 1, -(r.1 0)], fun h => r.2 (by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    ext i
    fin_cases i <;> simp [h0, h1])⟩
  left_inv r := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv r := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp

private theorem rv_w (ξ : Fin 2 → ℚ) :
    rv ξ ᵥ* ((gl (wW ℚ) : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = rv ![-(ξ 1), ξ 0] := by
  have hw : ((gl (wW ℚ) : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![0, 1; -1, 0] := rfl
  rw [hw]
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, UpperTheory.ConvolutionTheory.R2.rt]
  · exact (map_neg (algebraMap ℚ (A ℚ)) (ξ 1)).symm
  · rfl

theorem UpperTheory.thetaSeries_poisson_functional_equation :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∃ Ψ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ (t : ℝ) (g : G1 ℚ) (u : (A ℚ)ˣ), ab u = 1 →
        ThR Φ t (gl g * dM u) = -Φ 0 + (Real.exp (-(2 * t)) : ℂ) * Ψ 0 + (Real.exp (-(2 * t)) : ℂ) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) := by
  intro Φ hΦ
  refine ⟨adelicFourierPi ℚ Φ, adelicFourierPi_mem_schwartzBruhatPi hΦ, ?_⟩
  intro t g u hu
  have hne : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  obtain ⟨s1, s2, s3⟩ := poisson_row hΦ (iy (Real.exp t)) (gl g * dM u)
  rw [tsum_split s1, tsum_split s2] at s3
  have hz : rv 0 = 0 := by
    funext i
    show UpperTheory.ConvolutionTheory.R2.rt ((0 : Fin 2 → ℚ) i) = 0
    simp [UpperTheory.ConvolutionTheory.R2.rt]
  have z1 : (fun j => ((iy (Real.exp t) : (A ℚ)ˣ) : A ℚ) * (rv 0 ᵥ* (gl g * dM u).val) j) = 0 := by
    funext j
    simp [hz]
  have z2 : (fun j => (((iy (Real.exp t))⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv 0 ᵥ* (PositivityTheory.RgEis.tInv (gl g * dM u)).val) j) = 0 := by
    funext j
    simp [hz]
  have hd : ab (iy (Real.exp t) * iy (Real.exp t) * Matrix.GeneralLinearGroup.det (gl g * dM u)) = Real.exp (2 * t) := by
    rw [det_h, UpperTheory.ConvolutionTheory.R2.ab_mul, UpperTheory.ConvolutionTheory.R2.ab_mul, hu, ab_iy _ hne, abs_of_pos (Real.exp_pos t), mul_one, ← Real.exp_add, two_mul]
  have hR : ∑' ξ : Rw ℚ, adelicFourierPi ℚ Φ (fun j =>
      (((iy (Real.exp t))⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ.1 ᵥ* (PositivityTheory.RgEis.tInv (gl g * dM u)).val) j) =
      ThR (adelicFourierPi ℚ Φ) (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) := by
    unfold ThR
    refine Eq.trans ?_ (eW.tsum_eq _)
    refine tsum_congr fun ξ => ?_
    congr 1
    funext j
    rw [tInv_h, Units.val_mul, ← Matrix.vecMul_vecMul, rv_w, Real.exp_neg, iy_inv _ hne]
    rfl
  have hL : ∑' ξ : Rw ℚ, Φ (fun j => ((iy (Real.exp t) : (A ℚ)ˣ) : A ℚ) * (rv ξ.1 ᵥ* (gl g * dM u).val) j) =
      ThR Φ t (gl g * dM u) := rfl
  simp only [z1, z2, hR, hL, hd] at s3
  have hexp : ((Real.exp (-(2 * t)) : ℝ) : ℂ) = ((Real.exp (2 * t) : ℝ) : ℂ)⁻¹ := by
    rw [Real.exp_neg, Complex.ofReal_inv]
  rw [hexp]
  linear_combination s3
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ThetaSeriesRatSL2MulInvariant
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem vm_mul_inv (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (x ᵥ* γ.1) ᵥ* (γ⁻¹).1 = x := by
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

private theorem vm_inv_mul (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (x ᵥ* (γ⁻¹).1) ᵥ* γ.1 = x := by
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

private def rowE (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) : Rw ℚ ≃ Rw ℚ where
  toFun ξ := ⟨ξ.1 ᵥ* γ.1, fun h => ξ.2 (by
    have := vm_mul_inv γ ξ.1
    rw [h, Matrix.zero_vecMul] at this
    exact this.symm)⟩
  invFun ξ := ⟨ξ.1 ᵥ* (γ⁻¹).1, fun h => ξ.2 (by
    have := vm_inv_mul γ ξ.1
    rw [h, Matrix.zero_vecMul] at this
    exact this.symm)⟩
  left_inv ξ := Subtype.ext (vm_mul_inv γ ξ.1)
  right_inv ξ := Subtype.ext (vm_inv_mul γ ξ.1)

private theorem row_rat (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (fun i => rt (x i)) ᵥ* (ratS ℚ γ).1 = fun i => rt ((x ᵥ* γ.1) i) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ratS, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_add, map_mul]

theorem UpperTheory.thetaSeries_ratSL2_mul_invariant :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (g : G1 ℚ) (h : GL (Fin 2) (A ℚ)),
        ThR Φ t (gl (ratS ℚ γ * g) * h) = ThR Φ t (gl g * h) := by
  intro Φ t γ g h
  unfold ThR
  rw [← (rowE γ).tsum_eq (fun ξ : Rw ℚ => Φ fun j => (iy (Real.exp t) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (gl g * h).val) j)]
  refine tsum_congr fun ξ => ?_
  have key : (fun i => rt (ξ.1 i)) ᵥ* (gl (ratS ℚ γ * g) * h).val
      = (fun i => rt ((rowE γ ξ).1 i)) ᵥ* (gl g * h).val := by
    have e : (gl (ratS ℚ γ * g) * h).val = (ratS ℚ γ).1 * (gl g * h).val := by
      simp [gl, Matrix.SpecialLinearGroup.toGL, Matrix.mul_assoc]
    rw [e, ← Matrix.vecMul_vecMul, row_rat]
    rfl
  rw [key]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ZCSuccEqAndEnvelopingActionCompatible
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem UpperTheory.polynomial_identity_coefficients_zero {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (v : Fin n → M)
    (h : ∀ u : ℂ, ∑ i : Fin n, u ^ (n - (i + 1)) • v i = 0) (i : Fin n) : v i = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have hp : (∑ j : Fin n, Polynomial.monomial (n - (j + 1)) (f (v j)) : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro u
    have := congrArg f (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (n - (i + 1))) hp
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg]
    intro e
    apply hj
    have := j.2
    have := i.2
    exact Fin.ext (by omega)
  · simp

private theorem UpperTheory.polynomial_coefficients_compare {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (a : ℕ → M) (b : Fin n → M)
    (h : ∀ u : ℂ, ∑ i ∈ Finset.range (n + 1), u ^ (n - i) • a i = u ^ n • a 0 + ∑ i : Fin n, u ^ (n - (i + 1)) • b i)
    (i : Fin n) : a (i + 1) = b i := by
  rw [← sub_eq_zero]
  refine UpperTheory.polynomial_identity_coefficients_zero (fun i : Fin n => a (i + 1) - b i) (fun u => ?_) i
  have := h u
  rw [Finset.sum_range_succ', add_comm, Nat.sub_zero, add_right_inj,
    ← Fin.sum_univ_eq_sum_range (fun i => u ^ (n - (i + 1)) • a (i + 1)) n] at this
  simp only [smul_sub, Finset.sum_sub_distrib, this, sub_self]

theorem UpperTheory.zC_succ_eq_and_envelopingAction_compatible :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
          (∀ (τ : E →+* ℂ) (i : Fin n), UpperTheory.ConvolutionTheory.BW.zC E n τ (i + 1) = zc τ i) ∧
          ∀ (u : UC E n) (φ : GlobalTheory.CuspRep.Sm E n), (UpperTheory.V.Cm.uC E n u φ).1 = (uAct u (UpperTheory.V.Cm.smEq E n φ)).1 := by
  intro E _ _ _ n
  refine ⟨fun τ i => ?_, fun u φ => ?_⟩
  · obtain ⟨h0, h1⟩ := UpperTheory.ConvolutionTheory.BW.zSpec E n τ
    refine UpperTheory.polynomial_coefficients_compare (M := UC E n) (UpperTheory.ConvolutionTheory.BW.zC E n τ) (zc τ) (fun u => ?_) i
    rw [h0]
    exact (h1 u).symm.trans ((UpperTheory.ConvolutionTheory.Dp.capZc E n τ).2 u)
  · induction u using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; rfl
    | tmul c x =>
      have e : uAct (TensorProduct.tmul ℝ c x : UC E n) = c • uAction x :=
        (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (uAction x)).symm
      rw [UpperTheory.V.Cm.uC_tmul, e]
      rfl
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, ha, hb]
end

