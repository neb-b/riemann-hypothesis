module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0005
public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootSubsetProductEquationOfHenselianReduct
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEtaleTrivializationOfTwoInvertibleModuleTo
section
open CategoryTheory TensorProduct UpperTheory.PicD

private theorem UpperTheory.PicD.Data.Triv.mapAlg (P : Data) {A : Type} [CommRing A]
    {z : P.S1.obj (CommRingCat.of A)} {M : Type} [AddCommGroup M] [Module A M]
    {C E : Type} [CommRing C] [Algebra A C] [CommRing E] [Algebra A E]
    {w : P.S0.obj (CommRingCat.of C)} {g : (C ⊗[A] C)ˣ} {t : M →ₗ[A] C}
    (h : P.Triv z M C w g t) (f : C →ₐ[A] E) :
    P.Triv z M E (P.r0 f.toRingHom w)
      (Units.map (Algebra.TensorProduct.map f f).toRingHom.toMonoidHom g) (f.toLinearMap ∘ₗ t) := by
  have e0 : f.toRingHom.comp (algebraMap A C) = algebraMap A E := f.comp_algebraMap
  have e1 : (Algebra.TensorProduct.map f f).toRingHom.comp (i1 A C).toRingHom
      = (i1 A E).toRingHom.comp f.toRingHom := by
    ext x <;> simp
  have e2 : (Algebra.TensorProduct.map f f).toRingHom.comp (i2 A C).toRingHom
      = (i2 A E).toRingHom.comp f.toRingHom := by
    ext x <;> simp
  have key : ∀ (c : C) (x : C ⊗[A] C), Algebra.TensorProduct.map f f (c • x)
      = f c • Algebra.TensorProduct.map f f x := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.smul_tmul']
    | add a b ha hb => simp [smul_add, ha, hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P.diff_mapDegZero, h.dw, P.mapDegOne_comp, e0]
  · rw [← P.mapDegZero_ofUnit, h.hg, map_sub, P.mapDegZero_comp, P.mapDegZero_comp, P.mapDegZero_comp, P.mapDegZero_comp, e1, e2]
  · intro m
    have := congrArg (Algebra.TensorProduct.map f f) (h.ht m)
    rw [key] at this
    simpa using this
  · letI : Algebra C E := f.toRingHom.toAlgebra
    haveI : IsScalarTower A C E := IsScalarTower.of_algebraMap_eq' e0.symm
    have hb1 : IsBaseChange C t :=
      IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h.bij) (fun x => by simp)
    have hb2 := hb1.comp (IsBaseChange.linearMap C E)
    have : LinearMap.liftBaseChange E (f.toLinearMap ∘ₗ t) = hb2.equiv.toLinearMap := by
      ext m
      simp [IsBaseChange.equiv_tmul]
      rfl
    rw [this]
    exact hb2.equiv.bijective

theorem UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors :
    ∀ (P : Data) (A : Type) [CommRing A] (z z' : P.S1.obj (CommRingCat.of A)) (M M' : Type) [AddCommGroup M] [Module A M]
        [AddCommGroup M'] [Module A M'], P.Rel z M → P.Rel z' M' →
        ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
          ∃ (w : P.S0.obj (CommRingCat.of C)) (g : (C ⊗[A] C)ˣ) (t : M →ₗ[A] C)
            (w' : P.S0.obj (CommRingCat.of C)) (g' : (C ⊗[A] C)ˣ) (t' : M' →ₗ[A] C),
            P.Triv z M C w g t ∧ P.Triv z' M' C w' g' t' := by
  intro P A _ z z' M M' _ _ _ _ hM hM'
  obtain ⟨C, _, _, hf, he, w, g, t, h⟩ := hM
  obtain ⟨C', _, _, hf', he', w', g', t', h'⟩ := hM'
  exact ⟨C ⊗[A] C', inferInstance, inferInstance, Module.FaithfullyFlat.trans A C _,
    Algebra.Etale.comp A C _, _, _, _, _, _, _,
    UpperTheory.PicD.Data.Triv.mapAlg P h Algebra.TensorProduct.includeLeft,
    UpperTheory.PicD.Data.Triv.mapAlg P h' Algebra.TensorProduct.includeRight⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsInvertibleModuleOfLocallyTrivialCocycle
section
open CategoryTheory TensorProduct UpperTheory.PicD

namespace UpperTheory.PicD

section
variable {A C : Type} [CommRing A] [CommRing C] [Algebra A C]

private theorem smul_eq_left_inclusion (b : C) (x : C ⊗[A] C) : b • x = i1 A C b * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, mul_add, hx, hy]
  | tmul p q => simp [smul_tmul']

private theorem act_eq (x : C ⊗[A] C) :
    GlobalTheory.FlatDescent.act A C C x = Algebra.TensorProduct.lmul' A x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul p q => simp

private theorem lTensor_theta (g x : C ⊗[A] C) :
    ((theta g).restrictScalars A).lTensor C x = c12 A C x * c23 A C g := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), add_mul, hx, hy]
  | tmul p q =>
    simp [smul_eq_left_inclusion, Algebra.TensorProduct.tmul_mul_tmul]

private theorem lTensor_mk (x : C ⊗[A] C) :
    (TensorProduct.mk A C C 1).lTensor C x = c13 A C x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul p q => simp

private theorem isDescentDatum_theta (g : C ⊗[A] C)
    (hc : c12 A C g * c23 A C g = c13 A C g) (hu : Algebra.TensorProduct.lmul' A g = (1 : C)) :
    GlobalTheory.FlatDescent.IsDescentDatum (theta g) := by
  constructor
  · intro b
    rw [theta_apply, map_smul, act_eq, hu]
    simp
  · intro b
    rw [theta_apply, lTensor_theta, lTensor_mk, smul_eq_left_inclusion, map_mul, map_mul, mul_assoc, hc]
    congr 1

end

end UpperTheory.PicD

theorem UpperTheory.exists_invertibleModule_of_locallyTrivial_cocycle :
    ∀ (P : Data) (A : Type) [CommRing A] (z : P.S1.obj (CommRingCat.of A)), P.LocEx z →
        ∃ (M : Type) (_ : AddCommGroup M) (_ : Module A M), Module.Invertible A M ∧ P.Rel z M := by
  intro P A _ z hz
  obtain ⟨C, _, _, hff, het, w, hw⟩ := hz
  have hdx : P.dd _ (P.r0 (i2 A C).toRingHom w - P.r0 (i1 A C).toRingHom w) = 0 := by
    have hcomp : (i2 A C).toRingHom.comp (algebraMap A C) = (i1 A C).toRingHom.comp (algebraMap A C) :=
      RingHom.ext fun a => ((i2 A C).commutes a).trans ((i1 A C).commutes a).symm
    rw [map_sub, P.diff_mapDegZero, P.diff_mapDegZero, hw, P.mapDegOne_comp, P.mapDegOne_comp, hcomp, sub_self]
  obtain ⟨g, hg⟩ := (P.dd_eq_zero _).1 hdx
  have q1 : (c12 A C).toRingHom.comp (i1 A C).toRingHom = (c13 A C).toRingHom.comp (i1 A C).toRingHom := by
    ext b <;> simp
  have q2 : (c12 A C).toRingHom.comp (i2 A C).toRingHom = (c23 A C).toRingHom.comp (i1 A C).toRingHom := by
    ext b <;> simp
  have q3 : (c13 A C).toRingHom.comp (i2 A C).toRingHom = (c23 A C).toRingHom.comp (i2 A C).toRingHom := by
    ext b <;> simp
  have hcoc : Units.map (c12 A C).toRingHom.toMonoidHom g * Units.map (c23 A C).toRingHom.toMonoidHom g =
      Units.map (c13 A C).toRingHom.toMonoidHom g := by
    apply P.un_injective
    rw [P.un_mul, ← P.mapDegZero_ofUnit, ← P.mapDegZero_ofUnit, ← P.mapDegZero_ofUnit, hg]
    simp only [map_sub, P.mapDegZero_comp]
    rw [q1, q2, q3]
    abel
  have hcount : Units.map (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.toMonoidHom g = 1 := by
    apply P.un_injective
    have hcomp : (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.comp (i2 A C).toRingHom =
        (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.comp (i1 A C).toRingHom := by
      ext b <;> simp
    rw [← P.mapDegZero_ofUnit, hg, P.un_one]
    simp only [map_sub, P.mapDegZero_comp]
    rw [hcomp, sub_self]
  have hdd : GlobalTheory.FlatDescent.IsDescentDatum (theta (g : C ⊗[A] C)) := by
    refine isDescentDatum_theta _ ?_ ?_
    · simpa using congrArg Units.val hcoc
    · simpa using congrArg Units.val hcount
  refine ⟨↥(Mg (g : C ⊗[A] C)), inferInstance, inferInstance, hdd.invertible_invariants, ?_⟩
  exact ⟨C, _, _, hff, het, w, g, (Mg (g : C ⊗[A] C)).subtype,
    ⟨hw, hg, fun m => GlobalTheory.FlatDescent.mem_invariants.1 m.2, hdd.bijective_extend⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicFactorLiftOfPowMulSubOnePow
section
noncomputable section
open Polynomial

theorem UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (g : A[X]), g.Monic → ∀ n m : ℕ, g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
      ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧ P.map (Ideal.Quotient.mk I) = X ^ n ∧ Q.map (Ideal.Quotient.mk I) = (X - 1) ^ m := by
  intro A _ I _ g hg n m hgm
  by_cases hR : Nontrivial (A ⧸ I)
  swap
  · rw [not_nontrivial_iff_subsingleton] at hR
    exact ⟨g, 1, hg, monic_one, (mul_one g).symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI := hR
  haveI hA : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  have h1 : ((X : (A ⧸ I)[X]) - 1) = X - C 1 := by simp
  have hdeg : g.natDegree = n + m := by
    have h := congrArg natDegree hgm
    rw [hg.natDegree_map, h1, (monic_X_pow n).natDegree_mul ((monic_X_sub_C 1).pow m),
      natDegree_X_pow, (monic_X_sub_C (1 : A ⧸ I)).natDegree_pow, natDegree_X_sub_C, mul_one] at h
    exact h
  obtain ⟨α, c, hα, hc⟩ := UpperTheory.exists_root_subset_product_equation_of_henselian_reduction A I g n m (n + m) rfl hg hdeg hgm
  obtain ⟨P, Q, hP, hQ, hPQ, hQd, hQm, hQ0⟩ := UpperTheory.exists_monic_factor_of_root_subset_product_equation A g n m (n + m) rfl hg hdeg α c hc
  have hQdeg : Q.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hQd (by rw [hQm]; exact one_ne_zero)
  have hPdeg : P.natDegree = n := by
    have h := hP.natDegree_mul hQ
    rw [← hPQ, hdeg, hQdeg] at h
    omega
  set φ := Ideal.Quotient.mk I
  have hPb : (P.map φ).Monic := hP.map φ
  have hprod : P.map φ * Q.map φ = X ^ n * (X - 1) ^ m := by
    rw [← Polynomial.map_mul, ← hPQ, hgm]
  have hQ0b : (Q.map φ).eval 0 = (-1) ^ m := by
    rw [eval_zero_map, hQ0, map_mul, map_pow, map_neg, map_one, Ideal.Quotient.eq.mpr hα, map_one, mul_one]
  have hcop : IsCoprime (X : (A ⧸ I)[X]) (Q.map φ) := by
    have hd : X ∣ Q.map φ - C ((Q.map φ).coeff 0) := X_dvd_sub_C
    obtain ⟨r, hr⟩ := hd
    rw [coeff_zero_eq_eval_zero, hQ0b] at hr
    refine ⟨-(C ((-1) ^ m) * r), C ((-1) ^ m), ?_⟩
    have hu : ((-1 : A ⧸ I) ^ m) * (-1) ^ m = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    calc -(C ((-1) ^ m) * r) * X + C ((-1) ^ m) * Q.map φ
        = C ((-1) ^ m) * (Q.map φ - X * r) := by ring
      _ = 1 := by rw [← hr, sub_sub_cancel, ← C_mul, hu, C_1]
  obtain ⟨s, hs⟩ := hcop.pow_left.dvd_of_dvd_mul_right ⟨(X - 1) ^ m, hprod⟩
  have hsm : s.Monic := (monic_X_pow n).of_mul_monic_left (by rw [← hs]; exact hPb)
  have hsdeg : s.natDegree = 0 := by
    have h := congrArg natDegree hs
    rw [hP.natDegree_map φ, (monic_X_pow n).natDegree_mul hsm, natDegree_X_pow, hPdeg] at h
    omega
  have hs1 : s = 1 := eq_one_of_monic_natDegree_zero hsm hsdeg
  have hPmap : P.map φ = X ^ n := by rw [hs, hs1, mul_one]
  have hQmap : Q.map φ = (X - 1) ^ m := by
    rw [hPmap] at hprod
    have h : X ^ n * (Q.map φ - (X - 1) ^ m) = 0 := by rw [mul_sub, hprod, sub_self]
    exact sub_eq_zero.mp ((monic_X_pow n).mul_right_eq_zero_iff.mp h)
  exact ⟨P, Q, hP, hQ, hPQ, hPmap, hQmap⟩

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsZeroOfLinearFormJacobianHenselian
section
noncomputable section
open IsLocalRing UpperTheory.Et

private lemma UpperTheory.eval_zero_pderiv {R : Type} [CommRing R] {n : ℕ} (j : Fin n)
    (P : MvPolynomial (Fin n) R) :
    MvPolynomial.eval 0 (MvPolynomial.pderiv j P) = AddMonoidAlgebra.coeff P (Finsupp.single j 1) := by
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hs : s = Finsupp.single j 1
    · subst hs
      simp
    · rw [if_neg hs]
      split_ifs with h
      · by_cases hsj : s j = 0
        · simp [hsj]
        · exfalso
          apply hs
          ext k
          have hk := DFunLike.congr_fun h k
          by_cases hkj : k = j
          · subst hkj
            simp at hk ⊢
            omega
          · simp [Finsupp.single_apply, hkj, Ne.symm hkj] at hk ⊢
            exact hk
      · rfl
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]

theorem UpperTheory.exists_zero_of_linear_form_jacobian_henselian :
    ∀ (A E : Type) [CommRing A] [HenselianLocalRing A] [CommRing E] [Algebra A E] (n : ℕ) (Φ : MvPolynomial (Fin n) E) (L : E →ₗ[A] (Fin n → A)),
      (∀ i, L (MvPolynomial.eval 0 Φ) i ∈ maximalIdeal A) →
      (∀ i j, L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i - (if i = j then 1 else 0) ∈ maximalIdeal A) →
      ∃ x : Fin n → A, (∀ j, x j ∈ maximalIdeal A) ∧ L (MvPolynomial.eval (fun j => algebraMap A E (x j)) Φ) = 0 := by
  intro A E _ _ _ _ n Φ L h0 h1
  let G : Fin n → MvPolynomial (Fin n) E → MvPolynomial (Fin n) A := fun i P =>
    ∑ d ∈ P.support, MvPolynomial.monomial d (L (AddMonoidAlgebra.coeff P d) i)
  have hG : ∀ i d P, AddMonoidAlgebra.coeff (G i P) d = L (AddMonoidAlgebra.coeff P d) i := by
    intro i d P
    simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [MvPolynomial.mem_support_iff, not_not] at h
      simp [h]
  have hGadd : ∀ i p q, G i (p + q) = G i p + G i q := by
    intro i p q
    ext d
    rw [MvPolynomial.coeff_add, hG, hG, hG, MvPolynomial.coeff_add, map_add (f := _), Pi.add_apply]
  have key : ∀ i (x : Fin n → A) (P : MvPolynomial (Fin n) E),
      MvPolynomial.eval x (G i P) = L (MvPolynomial.eval (fun j => algebraMap A E (x j)) P) i := by
    intro i x P
    induction P using MvPolynomial.induction_on' with
    | monomial d c =>
      have hm : G i (MvPolynomial.monomial d c) = MvPolynomial.monomial d (L c i) := by
        ext d'
        rw [hG, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
        split_ifs <;> simp
      rw [hm, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      have hp : (d.prod fun k e => (algebraMap A E (x k)) ^ e) = algebraMap A E (d.prod fun k e => x k ^ e) := by
        simp [Finsupp.prod, map_prod, map_pow]
      rw [hp, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
      simp [mul_comm]
    | add p q hp hq =>
      rw [hGadd, map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, hp, hq]
  let F : Fin n → MvPolynomial (Fin n) A := fun i => G i Φ
  have hF0 : ∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A := by
    intro i
    have h := key i 0 Φ
    have e : (fun j => algebraMap A E ((0 : Fin n → A) j)) = 0 := by
      ext
      simp
    rw [e] at h
    show MvPolynomial.eval 0 (G i Φ) ∈ maximalIdeal A
    rw [h]
    exact h0 i
  have hF1 : ∀ i j, MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)) =
      L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i := by
    intro i j
    rw [UpperTheory.eval_zero_pderiv, UpperTheory.eval_zero_pderiv]
    exact hG i _ Φ
  have hdet : IsUnit (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det := by
    have hM : (residue A).mapMatrix (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))) = 1 := by
      ext i j
      have h := (residue_eq_zero_iff _).mpr (h1 i j)
      rw [map_sub, sub_eq_zero] at h
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hF1, h, Matrix.one_apply]
      split_ifs <;> simp
    by_contra hu
    have hm := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
    have h := (residue_eq_zero_iff _).mpr hm
    rw [RingHom.map_det, hM, Matrix.det_one] at h
    exact one_ne_zero h
  obtain ⟨x, hx, hxm⟩ := UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian A n F hF0 hdet
  refine ⟨x, hxm, ?_⟩
  funext i
  rw [← key i x Φ]
  exact hx i

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TorsorRelSelfIffExistsCoboundary
section
open CategoryTheory TensorProduct UpperTheory.PicD

private theorem unit_of_surj {A C : Type} [CommRing A] [CommRing C] [Algebra A C] (t : A →ₗ[A] C)
    (hs : Function.Surjective (LinearMap.liftBaseChange C t)) : ∃ c : C, c * t 1 = 1 := by
  have key : ∀ x : C ⊗[A] A, ∃ c : C, LinearMap.liftBaseChange C t x = c * t 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c a =>
      refine ⟨c * algebraMap A C a, ?_⟩
      rw [LinearMap.liftBaseChange_tmul]
      have e : t a = a • t 1 := by rw [← map_smul, smul_eq_mul, mul_one]
      rw [e]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def, smul_eq_mul]
      ring
    | add x y hx hy =>
      obtain ⟨c1, h1⟩ := hx
      obtain ⟨c2, h2⟩ := hy
      exact ⟨c1 + c2, by rw [map_add (f := _), h1, h2, add_mul]⟩
  obtain ⟨x, hx⟩ := hs 1
  obtain ⟨c, hc⟩ := key x
  exact ⟨c, by rw [← hc, hx]⟩

private theorem tensor_inclusions_eq (A : Type) [CommRing A] : (i1 A A).toRingHom = (i2 A A).toRingHom := by
  ext a
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]
  calc a ⊗ₜ[A] (1 : A) = (a • (1 : A)) ⊗ₜ[A] (1 : A) := by rw [smul_eq_mul, mul_one]
    _ = (1 : A) ⊗ₜ[A] (a • (1 : A)) := TensorProduct.smul_tmul _ _ _
    _ = (1 : A) ⊗ₜ[A] a := by rw [smul_eq_mul, mul_one]

theorem UpperTheory.torsorRel_self_iff_exists_coboundary :
    ∀ (P : Data) (A : Type) [CommRing A] (z : P.S1.obj (CommRingCat.of A)),
        P.Rel z A ↔ ∃ y : P.S0.obj (CommRingCat.of A), P.dd A y = z := by
  intro P A _ z
  constructor
  · rintro ⟨C, _, _, _, _, w, g, t, hT⟩
    obtain ⟨c', hc'⟩ := unit_of_surj t hT.bij.2
    let u : Cˣ := ⟨t 1, c', by rw [mul_comm, hc'], hc'⟩
    have hgu : Units.map ((i1 A C).toRingHom : C →* C ⊗[A] C) u * g
        = Units.map ((i2 A C).toRingHom : C →* C ⊗[A] C) u := by
      ext
      have h := hT.ht 1
      rw [Algebra.smul_def] at h
      simpa using h
    have hun : P.un g = P.r0 (i2 A C).toRingHom (P.un u) - P.r0 (i1 A C).toRingHom (P.un u) := by
      rw [Data.mapDegZero_ofUnit, Data.mapDegZero_ofUnit, eq_sub_iff_add_eq, add_comm, ← Data.un_mul]
      congr 1
    have hg := hT.hg
    rw [hun] at hg
    obtain ⟨y, hy⟩ := P.glue A C (w - P.un u) (by
      change P.r0 (i1 A C).toRingHom (w - P.un u) = P.r0 (i2 A C).toRingHom (w - P.un u)
      rw [map_sub, map_sub, sub_eq_sub_iff_sub_eq_sub,
        ← neg_sub (P.r0 (i2 A C).toRingHom w), ← hg, neg_sub])
    have hy' : P.r0 (algebraMap A C) y = w - P.un u := hy
    refine ⟨y, P.sep A C ?_⟩
    change P.r1 (algebraMap A C) (P.dd A y) = P.r1 (algebraMap A C) z
    rw [← Data.diff_mapDegZero, hy', map_sub, hT.dw]
    have e : P.dd C (P.un u) = 0 := (Data.dd_eq_zero P _).mpr ⟨u, rfl⟩
    rw [e, sub_zero]
  · rintro ⟨y, rfl⟩
    refine ⟨A, inferInstance, Algebra.id A, inferInstance, inferInstance,
      P.r0 (algebraMap A A) y, 1, LinearMap.id, ?_⟩
    refine ⟨Data.diff_mapDegZero P _ y, ?_, ?_, ?_⟩
    · rw [Data.un_one, tensor_inclusions_eq, sub_self]
    · intro m
      have e := congrArg (fun f => f m) (tensor_inclusions_eq A)
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply] at e
      rw [LinearMap.id_apply, Units.val_one, Algebra.smul_def, mul_one]
      exact e
    · have e : ⇑(LinearMap.liftBaseChange A (LinearMap.id : A →ₗ[A] A)) = ⇑(TensorProduct.lid A A) := by
        funext x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      rw [e]
      exact (TensorProduct.lid A A).bijective
end

