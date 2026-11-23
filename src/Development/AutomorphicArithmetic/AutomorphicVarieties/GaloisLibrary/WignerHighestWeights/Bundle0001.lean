module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ActOpApply
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private noncomputable def actAlg (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private noncomputable def actOp (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (actAlg V d Nᵀ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.transpose_add]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

private theorem actOp_apply (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (N : Matrix (Fin d) (Fin d) ℂ) :
    actOp V d N = MulOpposite.op (actAlg V d Nᵀ) := rfl

set_option synthInstance.maxHeartbeats 100000 in
theorem UpperTheory.V.AlgRepEndIrreducible.tensB :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), IsLieHom (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) ∧
      (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), tensorK π Ξ k * lieB π Ξ (toL X) = lieB π Ξ (toL (k.1 * X * star k.1)) * tensorK π Ξ k) ∧
      ∀ (τ : E →+* ℂ) (m : Multiset ℂ), GlobalTheory.WignerGL.HasDualInfChar Ξ τ m → ∀ u : ℂ,
        Formalism.REAL.qdet (fun i j => -MulOpposite.op (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) τ i j)) (u + ((a : ℂ) - 1) / 2) =
          MulOpposite.op ((m.map (u + ·)).prod • (1 : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))) := by
  intro E _ _ _ a π Ξ
  have hB : ∀ X, lieB π Ξ X = actAlg π.V Ξ.d (Ξ.dmat X) := fun _ => rfl
  refine ⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩
  · rw [hB, hB, hB, ← GlobalTheory.AlgInfChar.dmat_bracket, map_sub, map_mul, map_mul]
  · refine TensorProduct.ext' fun φ v => ?_
    have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X) =
        Ξ.dmat (toL (k.1 * X * star k.1)) * Ξ.mat (Unitary.toUnits k) :=
      Ξ.mat_mul_dmat (Unitary.toUnits k) X
    simp only [mul_apply_eq_comp, tensorK, lieB_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
  · have h0 := map_qdet (A := Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (B := (Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))ᵐᵒᵖ)
      (actOp π.V Ξ.d) (GlobalTheory.WignerGL.dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)
    have h := h0.symm.trans (congrArg (actOp π.V Ξ.d) (hm.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, actOp π.V Ξ.d (GlobalTheory.WignerGL.dualE Ξ τ i j) =
        -MulOpposite.op (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg, actOp_apply, Matrix.transpose_transpose]
      simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h
    rw [h, MulOpposite.op_smul, MulOpposite.op_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.CohTransport
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.cohTransport :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ Ξ' : AlgRep E a) (T : (Fin Ξ.d → ℂ) ≃ₗ[ℂ] (Fin Ξ'.d → ℂ)),
      IsAlgIso Ξ Ξ' T → IsCohFor π Ξ → IsCohFor π Ξ' := by
  rintro E _ _ _ a π Ξ Ξ' T ⟨h1, h2⟩ H
  refine GlobalTheory.ConjCoh.hasCohomology_transport (σ := LinearMap.id) (s := id)
    (LinearEquiv.lTensor π.V T) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun k m => ?_) (fun X m => ?_) H
  · induction m using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v =>
      change π.op (.cpt k) φ ⊗ₜ[ℂ] T (Ξ.mat (Unitary.toUnits k) *ᵥ v) =
        π.op (.cpt k) φ ⊗ₜ[ℂ] (Ξ'.mat (Unitary.toUnits k) *ᵥ T v)
      rw [h1]
  · induction m using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v =>
      rw [GlobalTheory.GKCoh.tensorLie_tmul, map_add (f := _)]
      change π.op (.lie (toL X.1)) φ ⊗ₜ[ℂ] T v + φ ⊗ₜ[ℂ] T (Ξ.dmat (toL X.1) *ᵥ v) =
        π.op (.lie (toL X.1)) φ ⊗ₜ[ℂ] T v + φ ⊗ₜ[ℂ] (Ξ'.dmat (toL X.1) *ᵥ T v)
      rw [h2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.EpsDer
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem update_swap_mul_eq_update {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : Fin n} (hab : a ≠ b) :
    Function.update (⇑(Equiv.swap a b * σ)) ((Equiv.swap a b * σ).symm b) a
      = Function.update (⇑σ) (σ.symm b) a := by
  have e : (Equiv.swap a b * σ).symm b = σ.symm a := by
    simp [Equiv.Perm.mul_def, Equiv.swap_apply_right]
  rw [e]
  funext j
  simp only [Function.update_apply, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.eq_symm_apply]
  by_cases h1 : σ j = a
  · have h2 : σ j ≠ b := h1 ▸ hab
    simp [h1, hab]
  · by_cases h2 : σ j = b
    · simp [h1, h2, Equiv.swap_apply_right]
    · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem sum_sign_smul_update_eq_ite {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (h : (Fin n → Fin n) → M) (a b : Fin n) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a)
      = if a = b then ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h ⇑σ else 0 := by
  split_ifs with hab
  · subst hab
    refine Finset.sum_congr rfl fun σ _ => ?_
    have := Function.update_eq_self (σ.symm a) (⇑σ)
    simp only [Equiv.apply_symm_apply] at this
    rw [this]
  · have key : ∀ σ : Equiv.Perm (Fin n),
        (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a)
          = -((Equiv.Perm.sign (Equiv.mulLeft (Equiv.swap a b) σ) : ℤ) •
              h (Function.update (⇑(Equiv.mulLeft (Equiv.swap a b) σ))
                ((Equiv.mulLeft (Equiv.swap a b) σ).symm b) a)) := by
      intro σ
      simp only [Equiv.coe_mulLeft]
      rw [update_swap_mul_eq_update σ hab, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      simp
    set S := ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a) with hSdef
    have hS : S = -S := by
      conv_lhs => rw [hSdef, Finset.sum_congr rfl fun σ _ => key σ, Finset.sum_neg_distrib,
        Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))
          (fun τ => (Equiv.Perm.sign τ : ℤ) • h (Function.update (⇑τ) (τ.symm b) a))]
    have h2 : (2:ℂ) • S = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hS]
      exact add_neg_cancel S
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
private theorem update_single_first_index_eq {n : ℕ} (r c : Fin n → Fin n) (k a : Fin n) :
    Function.update (fun j => Matrix.single (r j) (c j) (1:ℂ)) k (Matrix.single a (c k) 1)
      = fun j => Matrix.single (Function.update r k a j) (c j) (1:ℂ) := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp
  · simp [hj]

private theorem update_single_col_eq {n : ℕ} (r c : Fin n → Fin n) (k a : Fin n) :
    Function.update (fun j => Matrix.single (r j) (c j) (1:ℂ)) k (Matrix.single (r k) a 1)
      = fun j => Matrix.single (r j) (Function.update c k a j) (1:ℂ) := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp
  · simp [hj]

private theorem mul_single_eq_sum_smul_single {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    y * Matrix.single p q (1:ℂ) = ∑ a, y a p • Matrix.single a q (1:ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

private theorem single_mul_eq_sum_smul_single {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    Matrix.single p q (1:ℂ) * y = ∑ c, y q c • Matrix.single p c (1:ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

private theorem sum_sign_left_mul_update_eq_trace_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M)
    (y : Matrix (Fin n) (Fin n) ℂ) (τ : Equiv.Perm (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k))
      = Matrix.trace y • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • μ (units σ τ) := by
  set h : (Fin n → Fin n) → M := fun r => μ (fun j => Matrix.single (r j) (τ j) (1:ℂ)) with hh
  have inner : ∀ σ : Equiv.Perm (Fin n),
      ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k))
        = ∑ b, ∑ a, y a b • h (Function.update (⇑σ) (σ.symm b) a) := by
    intro σ
    have hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1:ℂ) := rfl
    rw [hu]
    simp_rw [mul_single_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul,
      update_single_first_index_eq]
    rw [← Equiv.sum_comp σ.symm]
    simp [hh]
  simp_rw [inner, Finset.smul_sum]
  rw [Finset.sum_comm]
  have step : ∀ b : Fin n, ∑ σ : Equiv.Perm (Fin n), ∑ a, (Equiv.Perm.sign σ : ℤ) •
      y a b • h (Function.update (⇑σ) (σ.symm b) a)
        = y b b • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h ⇑σ := by
    intro b
    rw [Finset.sum_comm]
    simp_rw [smul_comm ((Equiv.Perm.sign _ : ℤ)) (y _ b), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]
    simp
  rw [Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]
  rfl

private theorem sum_sign_right_mul_update_eq_trace_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M)
    (y : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) •
        ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y))
      = Matrix.trace y • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • μ (units σ τ) := by
  set h : (Fin n → Fin n) → M := fun c => μ (fun j => Matrix.single (σ j) (c j) (1:ℂ)) with hh
  have inner : ∀ τ : Equiv.Perm (Fin n),
      ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y))
        = ∑ b, ∑ c, y b c • h (Function.update (⇑τ) (τ.symm b) c) := by
    intro τ
    have hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1:ℂ) := rfl
    rw [hu]
    simp_rw [single_mul_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul,
      update_single_col_eq]
    rw [← Equiv.sum_comp τ.symm]
    simp [hh]
  simp_rw [inner, Finset.smul_sum]
  rw [Finset.sum_comm]
  have step : ∀ b : Fin n, ∑ τ : Equiv.Perm (Fin n), ∑ c, (Equiv.Perm.sign τ : ℤ) •
      y b c • h (Function.update (⇑τ) (τ.symm b) c)
        = y b b • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • h ⇑τ := by
    intro b
    rw [Finset.sum_comm]
    simp_rw [smul_comm ((Equiv.Perm.sign _ : ℤ)) (y b _), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]
    simp
  rw [Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]
  rfl

theorem UpperTheory.V.AlgRepEndIrreducible.epsDer :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ)
      (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M) (y : Matrix (Fin n) (Fin n) ℂ),
      eps (fun x => ∑ k, μ (Function.update x k (y * x k - x k * y))) = 0 := by
  intro M _ _ n μ y
  show ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k - units σ τ k * y)) = 0
  simp_rw [MultilinearMap.map_update_sub, Finset.sum_sub_distrib, smul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have L : ∀ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k))
      = (Equiv.Perm.sign τ : ℤ) • (Matrix.trace y •
          ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • μ (units σ τ)) := by
    intro τ
    rw [← sum_sign_left_mul_update_eq_trace_smul, Finset.smul_sum]
    simp_rw [mul_smul]
  have R : ∀ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y))
      = (Equiv.Perm.sign σ : ℤ) • (Matrix.trace y •
          ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • μ (units σ τ)) := by
    intro σ
    rw [← sum_sign_right_mul_update_eq_trace_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_comm, mul_smul]
  rw [Finset.sum_congr rfl fun τ _ => L τ, Finset.sum_comm,
    Finset.sum_congr rfl fun σ _ => R σ]
  simp_rw [smul_comm _ (Matrix.trace y), ← Finset.smul_sum]
  congr 1
  simp_rw [Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.EpsGrp
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private def outL {n : ℕ} (w : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun u := vecMulVec u w
  map_add' u u' := by ext; simp [vecMulVec_apply, add_mul]
  map_smul' c u := by ext; simp [vecMulVec_apply, mul_assoc]

private theorem eps_left_mul_eq_det_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : (Π _ : Fin n, Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M) (g : Matrix (Fin n) (Fin n) ℂ) :
    eps (fun x => μ fun i => g * x i) = g.det • eps μ := by
  have hs : ∀ a b : Fin n, g * single a b (1 : ℂ) = ∑ c, g c a • single c b (1 : ℂ) := by
    intro a b
    ext i j
    by_cases hbj : b = j <;> simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, hbj]
  have hdet : ∀ c : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, g (c k) (σ k) = (g.submatrix c id).det := by
    intro c
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  have hsum : ∀ w : (Fin n → Fin n) → M, ∑ c, (g.submatrix c id).det • w c =
      ∑ α : Equiv.Perm (Fin n), (((Equiv.Perm.sign α : ℤ) : ℂ) * g.det) • w α := by
    intro w
    rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.univ.image (fun α : Equiv.Perm (Fin n) => (⇑α : Fin n → Fin n))))]
    · rw [Finset.sum_image (fun α _ β _ h => Equiv.coe_fn_injective h)]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Matrix.det_permute]
    · intro c _ hc
      have hni : ¬ Function.Injective c := by
        intro hinj
        apply hc
        exact Finset.mem_image.mpr
          ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
      simp only [Function.Injective, not_forall] at hni
      obtain ⟨i, j, hij, hne⟩ := hni
      rw [Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]), zero_smul]
  simp only [eps, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hμ : ∀ σ : Equiv.Perm (Fin n), μ (fun i => g * units σ τ i) =
      ∑ c : Fin n → Fin n, (∏ k, g (c k) (σ k)) • μ (fun k => single (c k) (τ k) (1 : ℂ)) := by
    intro σ
    simp only [units, hs]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply]
  have hc : ∀ c : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) • (∏ k, g (c k) (σ k)) •
        μ (fun k => single (c k) (τ k) (1 : ℂ)) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) • ((g.submatrix c id).det • μ (fun k => single (c k) (τ k) (1 : ℂ))) := by
    intro c
    simp only [← Int.cast_smul_eq_zsmul ℂ, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [← hdet c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    push_cast
    ring
  simp only [hμ, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun c _ => hc c, ← Finset.smul_sum, hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring

theorem UpperTheory.V.AlgRepEndIrreducible.epsGrp :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (μ : (Π _ : Fin n, Matrix (Fin n) (Fin n) ℂ) →ₘₗ[ℂ] M) (g g' : Matrix (Fin n) (Fin n) ℂ), g' * g = 1 →
      eps (fun x => μ fun i => g * x i * g') = eps μ := by
  intro M _ _ n μ g g' h
  have hT : ∀ ν : (Fin n → Matrix (Fin n) (Fin n) ℂ) → M, eps (fun x => ν fun i => (x i)ᵀ) = eps ν := by
    intro ν
    simp only [eps, units, Matrix.transpose_single]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_comm]
    rfl
  have e1 : eps (fun x => μ fun i => g * x i * g') = g.det • eps (fun x => μ fun i => x i * g') :=
    eps_left_mul_eq_det_smul (μ.compLinearMap (fun _ => LinearMap.mulRight ℂ g')) g
  have e2 : eps (fun x => μ fun i => (g'ᵀ * x i)ᵀ) = g'ᵀ.det • eps (fun x => μ fun i => (x i)ᵀ) :=
    eps_left_mul_eq_det_smul (μ.compLinearMap
      (fun _ => (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap)) g'ᵀ
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.det_transpose, hT] at e2
  have e3 : eps (fun x => μ fun i => x i * g') = g'.det • eps μ := by
    rw [← hT (fun x => μ fun i => x i * g')]
    exact e2
  rw [e1, e3, smul_smul, mul_comm, ← Matrix.det_mul, h, Matrix.det_one, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGenC
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem expSq {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (h : N * N = 0) :
    NormedSpace.exp N = 1 + N :=
  _root_.UpperTheory.Reformulated.B.Qf11.expSq N h

theorem UpperTheory.V.AlgRepEndIrreducible.expGenC :
    ∀ (n : ℕ) (H : Submonoid (Matrix (Fin n) (Fin n) ℂ)), (∀ X : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp X ∈ H) →
      ∀ g : Matrix (Fin n) (Fin n) ℂ, g.det ≠ 0 → g ∈ H := by
  intro n H hH g hg
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => M ∈ H) g hg ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := by
      rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
      exact fun i => hD i (Finset.mem_univ i)
    have := hH (Matrix.diagonal fun i => Complex.log (D i))
    rw [Matrix.exp_diagonal] at this
    convert this using 2
    funext i
    rw [Pi.exp_def]
    simp only [← Complex.exp_eq_exp_ℂ]
    exact (Complex.exp_log (hD' i)).symm
  · intro t
    have := hH (Matrix.single t.i t.j t.c)
    rw [expSq _ (Matrix.single_mul_single_of_ne _ _ _ _ t.hij.symm _)] at this
    exact this
  · intro A B _ _ hA hB
    exact H.mul_mem hA hB
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpMat
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct


open scoped Matrix.Norms.Operator in
private theorem oneParam_eq_exp {n : ℕ} (F : ℝ → Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (h0 : F 0 = 1) (hadd : ∀ s t, F (s + t) = F s * F t) (hD : HasDerivAt F D 0) :
    F 1 = NormedSpace.exp D := by
  have h1 : ∀ t, HasDerivAt F (F t * D) t := by
    intro t
    have h2 : HasDerivAt (fun s => F (s - t)) D t := by
      have h := HasDerivAt.comp_sub_const (f := F) (f' := D) t t (by rw [sub_self]; exact hD)
      exact h
    have h3 := h2.const_mul (F t)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    change F s = F t * F (s - t)
    rw [← hadd, add_sub_cancel]
  have h4 : ∀ t, HasDerivAt (fun t : ℝ => F t * NormedSpace.exp (t • -D)) 0 t := by
    intro t
    have h := (h1 t).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-D) t)
    have e : F t * D * NormedSpace.exp (t • -D) + F t * (-D * NormedSpace.exp (t • -D)) = 0 := by
      rw [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
    exact h.congr_deriv e
  have h5 := is_const_of_deriv_eq_zero (fun t => (h4 t).differentiableAt) (fun t => (h4 t).deriv) 1 0
  simp only [one_smul, zero_smul, NormedSpace.exp_zero, h0, mul_one] at h5
  have h6 : NormedSpace.exp (-D) * NormedSpace.exp D = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl D).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  rw [← mul_one (F 1), ← h6, ← mul_assoc, h5, one_mul]

open scoped Matrix.Norms.Operator in
private theorem representation_exp_eq_exp_derivative {E : Type} [Field E] [NumberField E] {a : ℕ} (Ξ : AlgRep E a)
    (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    Ξ.mat (Matrix.isUnit_exp X).unit = NormedSpace.exp (Ξ.dmat (toL X)) := by
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • X)).unit
  have hc : ∀ t, (c t).val = NormedSpace.exp (t • X) := fun t => rfl
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hadd : ∀ s t, c (s + t) = c s * c t := fun s t => Units.ext (by
    rw [Units.val_mul, hc, hc, hc, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
  have h1 : HasDerivAt (fun t => (c t).val) X 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  have h2 := GlobalTheory.AlgInfChar.hasDerivAt_mat Ξ c (toL X) h0 h1
  have h3 := oneParam_eq_exp (fun t => Ξ.mat (c t)) _ (by simp only [h0, map_one])
    (fun s t => by simp only [hadd, map_mul]) h2
  have e : (Matrix.isUnit_exp X).unit = c 1 := Units.ext (by rw [hc, one_smul]; rfl)
  rw [e]
  exact h3

theorem UpperTheory.V.AlgRepEndIrreducible.expMat :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (X : Matrix (Fin a) (Fin a) (Cinf E)) (y : GL (Fin a) (Cinf E)),
      y.val = NormedSpace.exp X → Ξ.mat y = NormedSpace.exp (Ξ.dmat (toL X)) := by
  intro E _ _ _ a Ξ X y hy
  have e : y = (Matrix.isUnit_exp X).unit := Units.ext hy
  rw [e]
  exact representation_exp_eq_exp_derivative Ξ X
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpSub
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.expSub :
    ∀ (d d' : ℕ) (S : Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ))
      (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d') (Fin d') ℂ), (A, B) ∈ S → (NormedSpace.exp A, NormedSpace.exp B) ∈ S := by
  intro d d' S A B h
  have hc : IsClosed (S : Set (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule S)
  have hA : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • A ^ n) (NormedSpace.exp A) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hB : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) (NormedSpace.exp B) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B
  refine hc.mem_of_tendsto (hA.prodMk hB) (Filter.Eventually.of_forall fun s => ?_)
  refine S.sum_mem fun n _ => ?_
  exact S.smul_mem (S.pow_mem h n) ((n.factorial : ℂ)⁻¹)
end

