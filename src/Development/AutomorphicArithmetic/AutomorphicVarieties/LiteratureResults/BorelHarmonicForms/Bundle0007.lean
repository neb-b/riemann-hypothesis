module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasTens
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cas_inter {E : Type} [Field E] [NumberField E] {a n : ℕ} (e : Fin n → Herm E a)
    {M N : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
    (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (L' : Lie E a →ₗ[ℝ] Module.End ℂ N) (f : M →ₗ[ℂ] N) (r : ℝ)
    (h : ∀ X m, f (L X m) = L' X (f m)) (m : M) :
    f (cas (shift L r) e m) = cas (shift L' r) e (f m) := by
  have h' : ∀ X m, f (shift L r X m) = shift L' r X (f m) := fun X m => by
    simp only [shift_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), h,
      LinearMap.map_smul_of_tower]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cas, LinearMap.sum_apply, LinearMap.sub_apply, Module.End.mul_apply, map_sum, map_sub, h']

private theorem cas_alg {E : Type} [Field E] [NumberField E] {a n : ℕ} (e : Fin n → Herm E a)
    {A B : Type} [Ring A] [Algebra ℂ A] [Module ℝ A]
    [Ring B] [Algebra ℂ B] [Module ℝ B]
    (L : Lie E a →ₗ[ℝ] A) (L' : Lie E a →ₗ[ℝ] B) (f : A →ₐ[ℂ] B) (h : ∀ X, f (L X) = L' X) :
    f (cas L e) = cas L' e := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cas, map_sum, map_sub, map_mul, h]

theorem UpperTheory.V.Lit.Bor.casTens :
    UpperTheory.V.Lit.Bor.CasTens := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ a n e he π Ξ r
    obtain ⟨c₁, h₁⟩ := casPi E a n e he π r
    obtain ⟨c₂, h₂⟩ := casXi E a n e he Ξ (-r)
    have hB := cas_alg (B := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) e (shift Ξ.dmat (-r)) (shift (lieB π Ξ) (-r))
      ((Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) π.V).comp
        (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom)
      fun X => by
        rw [shift_apply, shift_apply, map_add (f := _), ← algebraMap_smul ℂ _ (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), map_smul, map_one]
        rfl
    rw [h₂, map_smul, map_one] at hB
    have hπ : ∀ φ : π.V, cas (A := Module.End ℂ π.V) (shift (lieOp π) r) e φ = c₁ • φ := fun φ =>
      Subtype.ext ((cas_inter e (lieOp π) (lie E a) π.V.subtype r (fun _ _ => rfl) φ).trans (h₁ φ.1 φ.2))
    have hA : ∀ m, cas (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (shift (lieA π Ξ) r) e m = c₁ • m := fun m => by
      induction m using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
      | tmul φ v =>
        have h := cas_inter e (lieOp π) (lieA π Ξ) ((TensorProduct.mk ℂ π.V (Fin Ξ.d → ℂ)).flip v) r
          (fun _ _ => rfl) φ
        rw [hπ, map_smul] at h
        exact h.symm
    refine ⟨c₂ - c₁, fun m => ?_⟩
    rw [LinearMap.sub_apply, hA, ← hB]
    exact (sub_smul c₂ c₁ m).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IsOpenUnits
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem isOpen_units (T : Type) [Fintype T] (a : ℕ) :
    IsOpen {x : Fin a → Fin a → T → ℂ | IsUnit (Matrix.of x)} := by
  have e : {x : Fin a → Fin a → T → ℂ | IsUnit (Matrix.of x)} = ⋂ t, {x : Fin a → Fin a → T → ℂ | (Matrix.of x).det t ≠ 0} := by
    ext x
    simp [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
  rw [e]
  refine isOpen_iInter_of_finite fun t => isOpen_ne_fun ?_ continuous_const
  have h : Continuous fun x : Fin a → Fin a → T → ℂ => (Matrix.of x).det := Continuous.matrix_det continuous_id
  exact (continuous_apply t).comp h

theorem UpperTheory.V.Lit.Bor.cxExt :
    UpperTheory.V.Lit.Bor.CxExt := by
  intro E _ _ _ a Ξ
  classical
  obtain ⟨R, Φ, hΦ, hR, hm⟩ := UpperTheory.V.Lit.Bor.cxGrp E a Ξ
  have ho := isOpen_units (E →+* ℂ) a
  let o : Fin a → Fin a → (E →+* ℂ) → ℂ := fun i j => (1 : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ)) i j
  have hd : ∀ k l (g : GL (Fin a) ((E →+* ℂ) → ℂ)), DifferentiableAt ℂ (Φ k l) (fun i j => g.val i j) := fun k l g =>
    (hΦ k l).differentiableAt (ho.mem_nhds g.isUnit)
  have hd1 : ∀ k l, HasFDerivAt (Φ k l) ((fderiv ℂ (Φ k l) o).restrictScalars ℝ) o := fun k l =>
    (hd k l 1).hasFDerivAt.restrictScalars ℝ
  let D : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ) →ₗ[ℂ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
    { toFun := fun Z => Matrix.of fun k l => fderiv ℂ (Φ k l) o (fun i j => Z i j)
      map_add' := fun X Y => by
        ext k l
        exact map_add (fderiv ℂ (Φ k l) o) (fun i j => X i j) (fun i j => Y i j)
      map_smul' := fun c X => by
        ext k l
        exact map_smul (fderiv ℂ (Φ k l) o) c (fun i j => X i j) }
  refine ⟨R, D, ⟨fun k l => ?_, fun c Z h0 hc k l => ?_⟩, fun X => ?_⟩
  · simp only [hR]
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hv : Continuous fun g : GL (Fin a) ((E →+* ℂ) → ℂ) => (fun i j => g.val i j : Fin a → Fin a → (E →+* ℂ) → ℂ) :=
      Units.continuous_val (M := Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ))
    exact ContinuousAt.comp (f := fun g : GL (Fin a) ((E →+* ℂ) → ℂ) => (fun i j => g.val i j : Fin a → Fin a → (E →+* ℂ) → ℂ))
      (hd k l g).continuousAt hv.continuousAt
  · simp only [hR]
    have h1 : HasDerivAt (fun s => (fun i j => (c s).val i j : Fin a → Fin a → (E →+* ℂ) → ℂ)) (fun i j => Z i j) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun t => hc i j t
    exact (hd1 k l).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [h0]; rfl)
  · ext k l
    let L : Lie E a →L[ℝ] (Fin a → Fin a → (E →+* ℂ) → ℂ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun τ =>
        (coordL τ).comp ((ContinuousLinearMap.proj j).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) i))
    have hL : L (oneL E a) = o := by
      funext i j
      exact congrFun (congrFun (Matrix.map_one (emb E) (map_zero _) (map_one _)) i) j
    have h := extGL_eventuallyEq (f := fun y => Ξ.mat y k l) (F := fun x => Φ k l (L x))
      (fun y => by rw [← hm, hR]; rfl) (x := oneL E a) isUnit_one
    have h1 : HasFDerivAt (Φ k l) ((fderiv ℂ (Φ k l) o).restrictScalars ℝ) (L (oneL E a)) := by
      rw [hL]; exact hd1 k l
    have h2 := HasFDerivAt.comp (oneL E a) h1 L.hasFDerivAt
    change _ = fderiv ℝ _ _ (toL X)
    rw [h.fderiv_eq]
    exact (congrArg (fun M : Lie E a →L[ℝ] ℂ => M (toL X)) h2.fderiv).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PetEx
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct


open MeasureTheory GlobalTheory.CuspRep.CuspidalL2GL in
theorem UpperTheory.V.Lit.Bor.petEx :
    UpperTheory.V.Lit.Bor.PetEx := by
  intro E _ _ _ a ha r
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  let μ : Measure (GA E a) := Measure.haar
  have hs := sqMem E a ha μ r χ hχ
  have hm : ∀ φ ∈ (sqSub E a r).map (mulChi a χ).toLinearMap,
      GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hs φ hφ).2
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (sqSub E a r).subtype (Submodule.ker_subtype _)
  obtain ⟨T, hT⟩ : ∃ T : Sm E a →ₗ[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ, ∀ φ ∈ sqSub E a r, ∀ (ψ : Sm E a)
      (h : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ.1), ψ = mulChi a χ φ → T φ = h.toL2 := by
    refine ⟨toL2ₗ μ _ hm ∘ₗ (mulChi a χ).toLinearMap.submoduleMap (sqSub E a r) ∘ₗ p, ?_⟩
    rintro φ hφ _ h rfl
    have e : p φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hp ⟨φ, hφ⟩
    simp only [LinearMap.comp_apply, e]
    rfl
  refine ⟨((innerₛₗ ℂ) ∘ₛₗ T).compl₂ T, ⟨fun x y => ?_, fun x _ => ?_, fun x hx h0 => ?_⟩, fun X φ hφ ψ hψ => ?_⟩
  · exact (inner_conj_symm (T y) (T x)).symm
  · exact inner_self_nonneg (𝕜 := ℂ) (x := T x)
  · have h1 : T x = 0 := inner_self_eq_zero.1 (show inner ℂ (T x) (T x) = 0 from h0)
    rw [hT x hx _ (hs x hx).2 rfl] at h1
    by_contra hne
    refine toL2_ne_zero (hs x hx).2 (ContAut.continuous_of_isOpen_stab E a _ (hs x hx).1) (fun e => hne ?_) h1
    exact (mulChi a χ).map_eq_zero_iff.1 (Subtype.ext e)
  · have hL := (sqLie E a r).2 X
    have hmem : ∀ f ∈ sqSub E a r, lie E a X f + ((r * ell E a X : ℝ) : ℂ) • f ∈ sqSub E a r := fun f hf =>
      add_mem (hL f hf) (Submodule.smul_mem _ _ hf)
    have hd : ∀ f ∈ sqSub E a r, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X (mulChi a χ f)).1 :=
      fun f hf => by
        rw [hχ.2]
        exact (hs _ (hmem f hf)).2
    have hk := skew_lie_action_L2 E a μ X _ _ (hs φ hφ).1 (hs ψ hψ).1 (hs φ hφ).2 (hs ψ hψ).2 (hd φ hφ) (hd ψ hψ)
    rw [← hT _ (hmem φ hφ) _ (hd φ hφ) (hχ.2 X φ), ← hT _ (hmem ψ hψ) _ (hd ψ hψ) (hχ.2 X ψ),
      ← hT φ hφ _ (hs φ hφ).2 rfl, ← hT ψ hψ _ (hs ψ hψ).2 rfl, map_add, map_add, map_smul, map_smul,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hk
    change inner ℂ (T (lie E a X φ)) (T ψ) + inner ℂ (T φ) (T (lie E a X ψ)) = _ * inner ℂ (T φ) (T ψ)
    push_cast at hk ⊢
    linear_combination hk
end

