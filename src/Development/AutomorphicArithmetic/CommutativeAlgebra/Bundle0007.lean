module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.InvertibleModuleEquivOfSameCocycle
section
open CategoryTheory TensorProduct UpperTheory.PicD

namespace UpperTheory.PicD

private theorem smul_eq_tmul_mul {A C : Type} [CommRing A] [CommRing C] [Algebra A C] (c : C) (x : C ⊗[A] C) :
    c • x = (c ⊗ₜ[A] (1 : C)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, mul_add, hx, hy]
  | tmul a b => simp [smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]

private theorem injective_and_range {A C M : Type} [CommRing A] [CommRing C] [Algebra A C]
    [Module.FaithfullyFlat A C] [AddCommGroup M] [Module A M]
    (g : C ⊗[A] C) (t : M →ₗ[A] C) (ht : ∀ m, t m • g = (1 : C) ⊗ₜ[A] t m)
    (bij : Function.Bijective (LinearMap.liftBaseChange C t)) :
    Function.Injective t ∧ LinearMap.range t = Mg g := by
  have hψ : ∀ m, LinearMap.liftBaseChange C t ((1 : C) ⊗ₜ[A] m) = t m := fun m => by simp
  refine ⟨fun a b hab => ?_, ?_⟩
  · apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := C) M
    apply bij.1
    simpa [hψ] using hab
  · ext b
    constructor
    · rintro ⟨m, rfl⟩
      exact GlobalTheory.FlatDescent.mem_invariants.2 (ht m)
    · intro hb
      have hb' : b • g = (1 : C) ⊗ₜ[A] b := GlobalTheory.FlatDescent.mem_invariants.1 hb
      obtain ⟨s, rfl⟩ := bij.2 b
      have hinj : Function.Injective
          (((LinearMap.liftBaseChange C t).restrictScalars A).lTensor C) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ bij.1
      have hcan : ∀ x : C ⊗[A] M,
          ((LinearMap.liftBaseChange C t).restrictScalars A).lTensor C (GlobalTheory.FlatDescent.canonical C M x) =
            (LinearMap.liftBaseChange C t x) • g := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add (f := _), hx, hy, add_smul]
        | tmul c m =>
          have h1 : c ⊗ₜ[A] t m = c • ((1 : C) ⊗ₜ[A] t m) := by simp [smul_tmul']
          simp [GlobalTheory.FlatDescent.canonical, h1, ← ht m, mul_smul]
      have hs : GlobalTheory.FlatDescent.canonical C M s = (1 : C) ⊗ₜ[A] s := by
        apply hinj
        rw [hcan, hb']
        simp
      have hd : GlobalTheory.FlatDescent.amitsurDiff C M s = 0 := by
        simp [GlobalTheory.FlatDescent.amitsurDiff, hs]
      obtain ⟨m, rfl⟩ := ((GlobalTheory.FlatDescent.amitsur_exact (A := A) C M).2 s).1 hd
      exact ⟨m, by simp⟩

end UpperTheory.PicD

theorem UpperTheory.invertibleModule_equiv_of_same_cocycle :
    ∀ (P : Data) (A : Type) [CommRing A] (z : P.S1.obj (CommRingCat.of A)) (M M' : Type) [AddCommGroup M] [Module A M]
        [AddCommGroup M'] [Module A M'], P.Rel z M → P.Rel z M' → Nonempty (M ≃ₗ[A] M') := by
  intro P A _ z M M' _ _ _ _ h h'
  obtain ⟨C, iC, iA, hff, het, w, g, t, w', g', t', T, T'⟩ := UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors P A z z M M' h h'
  have hd : P.dd C (w' - w) = 0 := by rw [map_sub, T.dw, T'.dw, sub_self]
  obtain ⟨u, hu⟩ := (P.dd_eq_zero _).1 hd
  have hg : g' * Units.map (i1 A C).toRingHom.toMonoidHom u =
      g * Units.map (i2 A C).toRingHom.toMonoidHom u := by
    apply P.un_injective
    rw [P.un_mul, P.un_mul, ← P.mapDegZero_ofUnit, ← P.mapDegZero_ofUnit, hu, T.hg, T'.hg, map_sub, map_sub]
    abel
  have hg' : (g' : C ⊗[A] C) * ((u : C) ⊗ₜ[A] (1 : C)) = (g : C ⊗[A] C) * ((1 : C) ⊗ₜ[A] (u : C)) := by
    simpa using congrArg Units.val hg
  let t₁ : M →ₗ[A] C := LinearMap.mulLeft A (u : C) ∘ₗ t
  have ht₁ : ∀ m, t₁ m • (g' : C ⊗[A] C) = (1 : C) ⊗ₜ[A] t₁ m := by
    intro m
    have h1 := T.ht m
    rw [smul_eq_tmul_mul] at h1 ⊢
    have h2 : ((u : C) * t m) ⊗ₜ[A] (1 : C) = ((u : C) ⊗ₜ[A] (1 : C)) * (t m ⊗ₜ[A] (1 : C)) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    have h3 : (1 : C) ⊗ₜ[A] ((u : C) * t m) = ((1 : C) ⊗ₜ[A] t m) * ((1 : C) ⊗ₜ[A] (u : C)) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    simp only [t₁, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [h2, h3, ← h1]
    linear_combination (t m ⊗ₜ[A] (1 : C)) * hg'
  have hψ : ∀ x : C ⊗[A] M, LinearMap.liftBaseChange C t₁ x = (u : C) * LinearMap.liftBaseChange C t x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]
    | tmul c m => simp [t₁, mul_left_comm]
  have hbij : Function.Bijective (LinearMap.liftBaseChange C t₁) := by
    have : (LinearMap.liftBaseChange C t₁ : C ⊗[A] M → C) =
        (fun x => (u : C) * x) ∘ (LinearMap.liftBaseChange C t) := funext hψ
    rw [this]
    exact (Units.mulLeft_bijective u).comp T.bij
  obtain ⟨i₁, r₁⟩ := injective_and_range (g' : C ⊗[A] C) t₁ ht₁ hbij
  obtain ⟨i₂, r₂⟩ := injective_and_range (g' : C ⊗[A] C) t' T'.ht T'.bij
  exact ⟨LinearEquiv.ofInjective t₁ i₁ ≪≫ₗ LinearEquiv.ofEq _ _ (r₁.trans r₂.symm) ≪≫ₗ
    (LinearEquiv.ofInjective t' i₂).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RelAddTensorProductOfRel
section
open CategoryTheory TensorProduct UpperTheory.PicD

private theorem cotangentAtUnit_tangentBijection {A C M M' : Type} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (t : M →ₗ[A] C) (t' : M' →ₗ[A] C)
    (h : Function.Bijective (LinearMap.liftBaseChange C t))
    (h' : Function.Bijective (LinearMap.liftBaseChange C t')) :
    Function.Bijective (LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t')) := by
  let e := LinearEquiv.ofBijective _ h
  let e' := LinearEquiv.ofBijective _ h'
  let F : C ⊗[A] (M ⊗[A] M') ≃ₗ[C] C :=
    TensorProduct.AlgebraTensorModule.distribBaseChange A C M M' ≪≫ₗ TensorProduct.congr e e' ≪≫ₗ
      TensorProduct.lid C C
  have hF : ∀ x, F x = LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t') x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y1 y2 h1 h2 => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), h1, h2]
      | tmul m m' =>
        simp [F, e, e', LinearMap.liftBaseChange_tmul, smul_eq_mul, mul_assoc]
  have : ⇑(LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t')) = F := by
    funext x
    exact (hF x).symm
  rw [this]
  exact F.bijective

theorem UpperTheory.rel_add_tensorProduct_of_rel :
    ∀ (P : Data) (A : Type) [CommRing A] (z z' : P.S1.obj (CommRingCat.of A)) (M M' : Type) [AddCommGroup M] [Module A M]
        [AddCommGroup M'] [Module A M'], P.Rel z M → P.Rel z' M' → P.Rel (z + z') (M ⊗[A] M') := by
  intro P A _ z z' M M' _ _ _ _ hz hz'
  obtain ⟨C, i1, i2, hff, het, w, g, t, w', g', t', T, T'⟩ := UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors P A z z' M M' hz hz'
  refine ⟨C, i1, i2, hff, het, w + w', g * g',
    (Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t', ?_⟩
  refine ⟨?_, ?_, ?_, cotangentAtUnit_tangentBijection t t' T.bij T'.bij⟩
  · rw [map_add (f := _), map_add (f := _), T.dw, T'.dw]
  · rw [P.un_mul, T.hg, T'.hg, map_add (f := _), map_add (f := _)]
    abel
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), add_smul, hx, hy, TensorProduct.tmul_add]
    | tmul m m' =>
      have h1 := T.ht m
      have h2 := T'.ht m'
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, Units.val_mul]
      rw [Algebra.smul_def] at h1 h2 ⊢
      rw [map_mul, show ∀ a b c d : C ⊗[A] C, a * b * (c * d) = (a * c) * (b * d) from
        fun a b c d => by ring, h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end

