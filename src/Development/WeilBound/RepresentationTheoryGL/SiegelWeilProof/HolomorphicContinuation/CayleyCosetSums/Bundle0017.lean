module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveHasDerivAt
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem cd_det_lemma {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x.det) := by
  have he : ∀ i j : ι, ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x i j) := fun i j =>
    contDiff_apply_apply ℂ i j
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum (fun σ _ => contDiff_const.mul (contDiff_prod (fun i _ => he _ _)))

theorem cd_det : ContDiff ℂ ∞ (fun x : M2 n => x.det) := by
  exact cd_det_lemma

theorem cd_detu1 : ContDiff ℂ ∞ (fun x : M2 n => (u1 x).det) := by
  exact cd_det_lemma.comp contDiff_first_cayley_block

theorem curve_hasDerivAt (X x : M2 n) : HasDerivAt (fun s : ℝ => x * cE X s) (x * X) 0 := by
  have h := (mulL x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (cE_hasDerivAt0 X)
  simp only [Function.comp_def, mulL_apply] at h
  exact h

theorem curve_deriv (Ψ : M2 n → ℂ) (hΨ : ContDiff ℂ ∞ Ψ) (X x : M2 n) :
    HasDerivAt (fun s : ℝ => Ψ (x * cE X s)) (fderiv ℂ Ψ x (x * X)) 0 := by
  have hd : HasFDerivAt Ψ (fderiv ℂ Ψ x) (x * cE X 0) := by
    rw [cE_zero, Matrix.mul_one]
    exact (hΨ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := (hd.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt X x)
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] at h
  exact h

theorem continuous_mR' : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem det_mR_ne' (g : GR n) : (mR g).det ≠ 0 := by
  show ((g : GL (Fin n ⊕ Fin n) ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ).det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n ⊕ Fin n) ℂ).isUnit).ne_zero

def rD (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => x.det) x (x * X) / x.det

def rA (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => (u1 x).det) x (x * X) / (u1 x).det

private theorem rD_mul_left_eq_of_det_ne_zero (P A X : M2 n) (hP : P.det ≠ 0) : rD X (P * A) = rD X A := by
  unfold rD
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => x.det) (fderiv ℂ (fun x : M2 n => x.det) B) B :=
    fun B => ((cd_det (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (P * y).det)
      ((fderiv ℂ (fun x : M2 n => x.det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (P * y).det)
      (P.det • fderiv ℂ (fun x : M2 n => x.det) A) A := by
    simp_rw [Matrix.det_mul]
    exact (hdet A).const_mul P.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, Matrix.det_mul, mul_div_mul_left _ _ hP]

theorem rD_up (X : M2 n) (p k : GR n) : rD X (mR p * mR k) = rD X (mR k) := by
  exact rD_mul_left_eq_of_det_ne_zero _ _ X (det_mR_ne' p)

private theorem rA_mul_left_eq_of_u1_mul (D : Matrix (Fin n) (Fin n) ℂ) (P A X : M2 n) (hD : D.det ≠ 0)
    (hu : ∀ y, u1 (P * y) = D * u1 y) : rA X (P * A) = rA X A := by
  unfold rA
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => (u1 x).det) (fderiv ℂ (fun x : M2 n => (u1 x).det) B) B :=
    fun B => ((cd_detu1 (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      ((fderiv ℂ (fun x : M2 n => (u1 x).det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      (D.det • fderiv ℂ (fun x : M2 n => (u1 x).det) A) A := by
    simp_rw [hu, Matrix.det_mul]
    exact (hdet A).const_mul D.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, hu, Matrix.det_mul, mul_div_mul_left _ _ hD]

theorem rA_up (X : M2 n) (p k : GR n) (hp : IsUp p) : rA X (mR p * mR k) = rA X (mR k) := by
  have hD : (toBlocks₂₂ (mR p)).det ≠ 0 := by
    rw [← first_block_of_upper p hp]
    exact det_first_cayley_block_ne_zero p.2
  exact rA_mul_left_eq_of_u1_mul _ _ _ X hD (fun y => first_block_upper_mul p y hp)

theorem continuous_rD (X : M2 n) : Continuous fun k : GR n => rD X (mR k) := by
  unfold rD
  refine Continuous.div ?_ (cd_det.continuous.comp continuous_mR') (fun k => det_mR_ne' k)
  exact ((cd_det.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

theorem continuous_rA (X : M2 n) : Continuous fun k : GR n => rA X (mR k) := by
  unfold rA
  refine Continuous.div ?_ (cd_detu1.continuous.comp continuous_mR')
    (fun k => (det_u_ne (x := mR k) k.2).1)
  exact ((cd_detu1.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

end PositivityTheory.Rg.Sw.HSt.FL
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetNeZeroOfInG
section
noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inG_mul {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  unfold InG at *
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx, hy]

theorem det_ne_zero_of_inG {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, h, mul_zero] at h1
  have h2 : (JJ n).det ≠ 0 := by
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [Matrix.det_mul, Matrix.det_neg] at this
    intro h3
    rw [h3, zero_mul] at this
    simp at this
  exact h2 h1.symm

def toGR (x : M2 n) (hx : InG x) : GR n := ⟨(Matrix.isUnit_iff_isUnit_det _ |>.2 (isUnit_iff_ne_zero.2
  (det_ne_zero_of_inG hx))).unit, hx⟩

theorem mR_toGR (x : M2 n) (hx : InG x) : mR (toGR x hx) = x := rfl

end PositivityTheory.Rg.Sw.HSt.CR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DifferentiableAtFirstCayleyBlock
section
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_function_eq_weighted (m : ℕ) (e : ℤ) (y : GR n) : F0 m 0 e y = holomorphicScalarSection m e (mR y) := by
  simp [F0, f0, holomorphicScalarSection]

def Nm (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂

def Nm' (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := -(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂

private theorem Cm_mul_Cmi_eq_one : Cm n * Cmi n = 1 := by
  simp only [Cm, Cmi, Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

private theorem Cm_inv_eq_Cmi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv Cm_mul_Cmi_eq_one

private theorem Cmi_mul_Cm_eq_one : Cmi n * Cm n = 1 := by
  rw [← Cm_inv_eq_Cmi]
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse Cm_mul_Cmi_eq_one)

private theorem u1_eq_mul_Cm_toBlocks₂₁ (g : M2 n) : u1 g = (g * Cm n).toBlocks₂₁ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [u1, Cm, Matrix.fromBlocks_multiply]

private theorem u2_eq_mul_Cm_toBlocks₂₂ (g : M2 n) : u2 g = (g * Cm n).toBlocks₂₂ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [u2, Cm, Matrix.fromBlocks_multiply]

private theorem Nm_eq_mul_Cm_toBlocks₁₁ (g : M2 n) : Nm g = (g * Cm n).toBlocks₁₁ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [Nm, Cm, Matrix.fromBlocks_multiply]

private theorem Nm'_eq_mul_Cm_toBlocks₁₂ (g : M2 n) : Nm' g = (g * Cm n).toBlocks₁₂ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [Nm', Cm, Matrix.fromBlocks_multiply]

private theorem toBlocks11_mul_fromBlocks (A : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    (A * fromBlocks P Q R S).toBlocks₁₁ = A.toBlocks₁₁ * P + A.toBlocks₁₂ * R := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [Matrix.fromBlocks_multiply]

private theorem mul_fromBlocks_toBlocks₂₁ (A : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    (A * fromBlocks P Q R S).toBlocks₂₁ = A.toBlocks₂₁ * P + A.toBlocks₂₂ * R := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [Matrix.fromBlocks_multiply]

private theorem mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    x * mX P Q R S * Cm n = x * Cm n * fromBlocks P Q R S := by
  simp only [mX, Cm_inv_eq_Cmi, Matrix.mul_assoc, Cmi_mul_Cm_eq_one, Matrix.mul_one]

theorem zOfE_eq (x : M2 n) : zOfE x = Nm x * (u1 x)⁻¹ := rfl

theorem first_cayley_block_mul_block (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    u1 (x * mX P Q R S) = u1 x * P + u2 x * R := by
  rw [u1_eq_mul_Cm_toBlocks₂₁, u1_eq_mul_Cm_toBlocks₂₁, u2_eq_mul_Cm_toBlocks₂₂, mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks, mul_fromBlocks_toBlocks₂₁]

theorem Nm_mX (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    Nm (x * mX P Q R S) = Nm x * P + Nm' x * R := by
  rw [Nm_eq_mul_Cm_toBlocks₁₁, Nm_eq_mul_Cm_toBlocks₁₁, Nm'_eq_mul_Cm_toBlocks₁₂, mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks, toBlocks11_mul_fromBlocks]

theorem da_entry (i j : Fin n ⊕ Fin n) (x : M2 n) : DifferentiableAt ℂ (fun y : M2 n => y i j) x := by
  exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_id (x := x)) i) j

theorem da_matrix {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n}
    (h : ∀ i j, DifferentiableAt ℂ (fun y => f y i j) x) : DifferentiableAt ℂ f x := by
  have h1 : DifferentiableAt ℂ (fun y => (f y : Fin n → Fin n → ℂ)) x :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => h i j
  exact h1

theorem da_apply {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (h : DifferentiableAt ℂ f x) (i j : Fin n) :
    DifferentiableAt ℂ (fun y => f y i j) x := by
  have h1 : DifferentiableAt ℂ (fun y => (f y : Fin n → Fin n → ℂ)) x := h
  exact differentiableAt_pi.1 (differentiableAt_pi.1 h1 i) j

theorem da_mul {f g : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x)
    (hg : DifferentiableAt ℂ g x) : DifferentiableAt ℂ (fun y => f y * g y) x := by
  refine da_matrix fun i j => ?_
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (da_apply hf i k).mul (da_apply hg k j)

theorem differentiableAt_first_cayley_block (x : M2 n) : DifferentiableAt ℂ u1 x := by
  refine da_matrix fun i j => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact ((da_entry _ _ x).const_mul _).add (da_entry _ _ x)

theorem da_Nm (x : M2 n) : DifferentiableAt ℂ Nm x := by
  refine da_matrix fun i j => ?_
  simp only [Nm, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, smul_eq_mul]
  exact ((da_entry _ _ x).const_mul _).add (da_entry _ _ x)

private theorem differentiableAt_det_of_differentiableAt_entries {ι : Type} [Fintype ι] [DecidableEq ι] {f : M2 n → Matrix ι ι ℂ}
    {x : M2 n} (hf : ∀ a b, DifferentiableAt ℂ (fun y => f y a b) x) :
    DifferentiableAt ℂ (fun y => (f y).det) x := by
  have hp : ∀ (s : Finset ι) (σ : Equiv.Perm ι),
      DifferentiableAt ℂ (fun y => ∏ i ∈ s, f y (σ i) i) x := by
    intro s σ
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact (hf _ _).mul ih
  have e : (fun y => (f y).det) =
      fun y => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e]
  exact DifferentiableAt.fun_sum fun σ _ => (hp _ σ).const_mul _

theorem da_det {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun y => (f y).det) x := by
  exact differentiableAt_det_of_differentiableAt_entries (da_apply hf)

theorem da_inv {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x) (h : (f x).det ≠ 0) :
    DifferentiableAt ℂ (fun y => (f y)⁻¹) x := by
  have hadj : ∀ i j, DifferentiableAt ℂ (fun y => (f y).adjugate i j) x := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine differentiableAt_det_of_differentiableAt_entries fun a b => ?_
    simp only [Matrix.updateRow_apply]
    by_cases hab : a = j
    · simp only [hab, if_true]
      exact differentiableAt_const _
    · simp only [hab, if_false]
      exact da_apply hf a b
  have hd : DifferentiableAt ℂ (fun y => ((f y).det)⁻¹) x := (differentiableAt_det_of_differentiableAt_entries (da_apply hf)).inv h
  refine da_matrix fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.mul (hadj i j)

theorem da_zOfE (x : M2 n) (h : (u1 x).det ≠ 0) : DifferentiableAt ℂ zOfE x := by
  have e : zOfE = fun y : M2 n => Nm y * (u1 y)⁻¹ := funext zOfE_eq
  rw [e]
  exact da_mul (da_Nm x) (da_inv (differentiableAt_first_cayley_block x) h)

theorem da_F0E (m : ℕ) (e : ℤ) (x : M2 n) (h0 : x.det ≠ 0) (h : (u1 x).det ≠ 0) : DifferentiableAt ℂ (holomorphicScalarSection m e) x := by
  show DifferentiableAt ℂ (fun y : M2 n => y.det ^ e * (u1 y).det ^ (-(m : ℤ))) x
  exact ((differentiableAt_det_of_differentiableAt_entries (f := fun y => y) fun a b => da_entry a b x).zpow (Or.inl h0)).mul
    ((da_det (differentiableAt_first_cayley_block x)).zpow (Or.inl h))

theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Cm n * fromBlocks 0 Q 0 0 * Cmi n := by
  have h1 : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) Q 0 1 : M2 n) = 1 + fromBlocks 0 Q 0 0 := by
    rw [← fromBlocks_one, fromBlocks_add]; simp
  rw [lowQ, mX, h1, cm_inv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, add_sub_cancel_left]

theorem lowQ_smul (c : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ (c • Q) = c • lowQ Q := by
  rw [lowQ_eq, lowQ_eq, show (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • Q) 0 0 : M2 n) = c • fromBlocks 0 Q 0 0 by
    rw [fromBlocks_smul]; simp]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem mX_low (Q : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q 0 1 = 1 + lowQ Q := by
  rw [lowQ]; abel

theorem det_mX_low (Q : Matrix (Fin n) (Fin n) ℂ) : (mX 1 Q 0 1 : M2 n).det = 1 := by
  simp only [mX, Cm_inv_eq_Cmi]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_one, mul_one]
  rw [← Matrix.det_mul, Cm_mul_Cmi_eq_one, Matrix.det_one]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DirSeries
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem dirSeries (hC : CurveGR) (hF : FzDer) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) {z : ℂ} (hz : t < z.re)
    (Z : M2 n) (b : Bool) (g : G) (y : GR n) (y₀ : GlobalTheory.Eis.Cosets Pp Γ → GR n) (C : GlobalTheory.Eis.Cosets Pp Γ → ℂ)
    (hyC : ∀ q y', trm Ht f s₀ z (((q.out : Γ) : G) * g * ι y') = C q * fz m e (z - s₀) (mR (y₀ q * y'))) :
    Summable (fun q => C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0) ∧
    deriv (fun s : ℝ => resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 =
      d.eval z * ∑' q, C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 := by
  obtain ⟨γ, hγc, hγ0, hγadd, hγe⟩ := hC n Z b
  obtain ⟨Cd, hCd0, hR⟩ := hF n m e (z - s₀) Z b
  choose Rf hRf using hR
  have hfzγ : ∀ (y₁ : GR n) (s : ℝ), fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
      fz m e (z - s₀) (mR (y₁ * γ s)) := by
    intro y₁ s
    rw [mR_mul, hγe]
  have hderiv : ∀ (y₁ : GR n) (s : ℝ), HasDerivAt (fun u : ℝ => fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) (Rf (y₁ * γ s)) s := by
    intro y₁ s
    have h1 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact (hRf (y₁ * γ s)).1)
    have hfe : (fun u : ℝ => fz m e (z - s₀)
        (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) =
        fun x : ℝ => fz m e (z - s₀)
          (mR (y₁ * γ s) * NormedSpace.exp (((x - s : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z))) := by
      funext u
      rw [hfzγ, ← hγe, ← mR_mul, mul_assoc, ← hγadd, add_sub_cancel]
    rw [hfe]
    exact h1
  have hK : IsCompact ((fun s : ℝ => g * ι (y * γ s)) '' Icc (-1) 1) :=
    isCompact_Icc.image (continuous_const.mul (h.ιc.comp (continuous_const.mul hγc)))
  obtain ⟨u, hu, hbound⟩ := (h.far z hz).1 _ hK
  have hterm : ∀ q (s : ℝ), s ∈ Icc (-1 : ℝ) 1 →
      ‖C q * fz m e (z - s₀) (mR (y₀ q * y * γ s))‖ ≤ u q := by
    intro q s hs
    have hb := hbound (g * ι (y * γ s)) ⟨s, hs, rfl⟩ q
    rw [mul_assoc (y₀ q), ← hyC q (y * γ s)]
    simpa only [GlobalTheory.Eis.term, trm, mul_assoc] using hb
  have hbd : ∀ q, ∀ s ∈ Ioo (-1 : ℝ) 1, ‖C q * Rf (y₀ q * y * γ s)‖ ≤ Cd * u q := by
    intro q s hs
    have h1 := (hRf (y₀ q * y * γ s)).2
    have h2 := hterm q s (Ioo_subset_Icc_self hs)
    rw [norm_mul] at h2 ⊢
    calc ‖C q‖ * ‖Rf (y₀ q * y * γ s)‖
        ≤ ‖C q‖ * (Cd * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = Cd * (‖C q‖ * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) := by ring
      _ ≤ Cd * u q := mul_le_mul_of_nonneg_left h2 hCd0
  have h0mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hg0 : Summable (fun q => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp (((0 : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z)))) :=
    hu.of_norm_bounded fun q => by
      simpa only [hfzγ] using hterm q 0 ⟨by norm_num, by norm_num⟩
  have hsum := hasDerivAt_tsum_of_isPreconnected (hu.mul_left Cd) isOpen_Ioo isPreconnected_Ioo
    (g := fun q (s : ℝ) => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))))
    (g' := fun q s => C q * Rf (y₀ q * y * γ s))
    (fun q s _ => (hderiv (y₀ q * y) s).const_mul (C q)) hbd h0mem hg0 h0mem
  rw [hγ0] at hsum
  simp only [mul_one] at hsum
  have hRfd : ∀ q, deriv (fun s : ℝ => fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 = Rf (y₀ q * y) :=
    fun q => (hRf (y₀ q * y)).1.deriv
  have hfun : (fun s : ℝ => resG ι (Ê z) g
      (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) =
      fun s : ℝ => d.eval z * ∑' q, C q * fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) := by
    funext s
    have hl : resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
        Ê z (g * ι (y * γ s)) := by
      rw [← hγe, ← mR_mul, resG_mR]
    rw [hl, (h.far z hz).2]
    simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
    congr 1
    refine tsum_congr fun q => ?_
    rw [hfzγ, mul_assoc (y₀ q), ← hyC q (y * γ s), trm, mul_assoc]
  simp only [hRfd]
  refine ⟨(hu.mul_left Cd).of_norm_bounded fun q => ?_, ?_⟩
  · simpa only [hγ0, mul_one] using hbd q 0 h0mem
  · rw [hfun, (hsum.const_mul (d.eval z)).deriv]

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

