module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GramBasic
section
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem exists_diag {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (hG : G.charpoly.Separable) :
    ∃ (l : Fin n → K) (x : GL (Fin n) K), Function.Injective l ∧ G * x.val = x.val * diagonal l := by
  classical
  have hsp : G.charpoly.Splits := IsAlgClosed.splits _
  have hcard : G.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hG), ← hsp.natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := G.charpoly.roots.toFinset.equivFinOfCardEq hcard
  obtain ⟨x, hx⟩ := (conjSep K K n G hG).1 (diagonal fun i => (e.symm i : K)) (by
    rw [Matrix.charpoly_diagonal, e.symm.prod_comp (fun a => (X - C (a : K))),
      Finset.prod_coe_sort _ (fun a : K => X - C a)]
    conv_rhs => rw [hsp.eq_prod_roots_of_monic G.charpoly_monic]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (nodup_roots hG).dedup])
  exact ⟨_, x, Subtype.val_injective.comp e.symm.injective, hx⟩

private theorem unit_of_closed {R : Type} [CommRing R] (r : R)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : R →+* K), φ r ≠ 0) : IsUnit r := by
  by_contra hr
  obtain ⟨m, hm, hrm⟩ := exists_max_ideal_of_mem_nonunits hr
  letI := Ideal.Quotient.field m
  refine h (AlgebraicClosure (R ⧸ m)) ((algebraMap (R ⧸ m) _).comp (Ideal.Quotient.mk m)) ?_
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hrm, map_zero]

section

variable {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {n : ℕ} (B : Module.Basis (Fin n) R L)

private theorem units_of_sep (g : L) (hg : (Algebra.leftMulMatrix B g).charpoly.Separable) :
    IsUnit (Matrix.of fun i j => Algebra.trace R L (B i * B j)).det ∧
      IsUnit (Matrix.of fun i j : Fin n => B.repr (g ^ (j : ℕ)) i).det := by
  suffices H : ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : R →+* K),
      φ (Matrix.of fun i j => Algebra.trace R L (B i * B j)).det ≠ 0 ∧
      φ (Matrix.of fun i j : Fin n => B.repr (g ^ (j : ℕ)) i).det ≠ 0 from
    ⟨unit_of_closed _ fun K _ _ φ => (H K φ).1, unit_of_closed _ fun K _ _ φ => (H K φ).2⟩
  intro K _ _ φ
  let ρ : L →+* Matrix (Fin n) (Fin n) K := φ.mapMatrix.comp (Algebra.leftMulMatrix B).toRingHom
  have hρ : ∀ z, ρ z = (Algebra.leftMulMatrix B z).map φ := fun _ => rfl
  obtain ⟨l, x, hl, hx⟩ := exists_diag (ρ g) (by rw [hρ, Matrix.charpoly_map]; exact hg.map)
  let τ : L → Matrix (Fin n) (Fin n) K := fun z => (x⁻¹).val * ρ z * x.val
  have hτmul : ∀ z w, τ (z * w) = τ z * τ w := fun z w => by
    simp only [τ, map_mul, mul_assoc, Units.mul_inv_cancel_left]
  have hτg : τ g = diagonal l := by
    simp only [τ, mul_assoc, hx, Units.inv_mul_cancel_left]
  have hd : ∀ z, τ z = diagonal fun i => τ z i i := fun z => by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · have h := congrFun (congrFun (show τ z * diagonal l = diagonal l * τ z by
        rw [← hτg, ← hτmul, ← hτmul, mul_comm]) i) j
      rw [mul_diagonal, diagonal_mul, mul_comm (l i)] at h
      rw [diagonal_apply_ne _ hij]
      by_contra h0
      exact hij (hl (mul_left_cancel₀ h0 h)).symm
  have hpow : ∀ j : ℕ, τ (g ^ j) = diagonal fun i => l i ^ j := fun j => by
    induction j with
    | zero => simp [τ]
    | succ j ih => rw [pow_succ, hτmul, ih, hτg, diagonal_mul_diagonal]; simp [pow_succ]
  let w : Fin n → K := (x⁻¹).val *ᵥ fun i => φ (B.repr 1 i)
  have hw : ∀ z i, ((x⁻¹).val *ᵥ fun i => φ (B.repr z i)) i = w i * τ z i i := fun z i => by
    have h1 : (fun i => φ (B.repr z i)) = ρ z *ᵥ fun i => φ (B.repr 1 i) := by
      funext i
      have := congrFun (Algebra.leftMulMatrix_mulVec_repr B z 1) i
      rw [mul_one] at this
      rw [← this, hρ, RingHom.map_mulVec]; rfl
    have h2 : (x⁻¹).val * ρ z = τ z * (x⁻¹).val := by
      simp only [τ, Units.mul_inv_cancel_right]
    rw [h1, mulVec_mulVec, h2, ← mulVec_mulVec, hd z, mulVec_diagonal, mul_comm]
    simp [w]
  have hxd : (x⁻¹).val.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (x⁻¹).isUnit).ne_zero
  have hE : (x⁻¹).val = diagonal w * Matrix.of fun i j => τ (B j) i i := by
    ext i j
    rw [diagonal_mul, of_apply, ← hw]
    simp [mulVec, dotProduct, Finsupp.single_apply, apply_ite φ]
  rw [hE, det_mul] at hxd
  constructor
  · have : (Matrix.of fun i j => Algebra.trace R L (B i * B j)).map φ =
        (Matrix.of fun i j => τ (B j) i i)ᵀ * Matrix.of fun i j => τ (B j) i i := by
      ext i j
      have h1 : (τ (B i * B j)).trace = (ρ (B i * B j)).trace := by
        simp only [τ]
        rw [trace_mul_comm, Units.mul_inv_cancel_left]
      rw [map_apply, of_apply, Algebra.trace_eq_matrix_trace B, AddMonoidHom.map_trace, ← hρ, ← h1,
        hτmul, hd (B i), hd (B j), diagonal_mul_diagonal, trace_diagonal]
      simp [Matrix.mul_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, this, det_mul, det_transpose]
    exact mul_ne_zero (right_ne_zero_of_mul hxd) (right_ne_zero_of_mul hxd)
  · have : (x⁻¹).val * (Matrix.of fun i j : Fin n => B.repr (g ^ (j : ℕ)) i).map φ =
        diagonal w * vandermonde l := by
      ext i j
      rw [diagonal_mul, vandermonde_apply]
      have := hw (g ^ (j : ℕ)) i
      rw [hpow, diagonal_apply_eq] at this
      rw [← this]; rfl
    have h2 := congrArg det this
    rw [det_mul, det_mul] at h2
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact right_ne_zero_of_mul (h2 ▸ mul_ne_zero (left_ne_zero_of_mul hxd)
      (det_vandermonde_ne_zero_iff.2 hl))

private theorem comm_of_sep (g : L) (hg : (Algebra.leftMulMatrix B g).charpoly.Separable)
    (y : Matrix (Fin n) (Fin n) R) (hy : y * Algebra.leftMulMatrix B g = Algebra.leftMulMatrix B g * y) :
    ∃ z, y = Algebra.leftMulMatrix B z := by
  refine ⟨B.equivFun.symm (y *ᵥ B.repr 1), ?_⟩
  refine ((isUnit_iff_isUnit_det _).2 (units_of_sep B g hg).2).mul_right_cancel ?_
  ext i j
  have h1 : ∀ M : Matrix (Fin n) (Fin n) R,
      (M * Matrix.of fun i j : Fin n => B.repr (g ^ (j : ℕ)) i) i j = (M *ᵥ B.repr (g ^ (j : ℕ))) i :=
    fun M => rfl
  have h2 : y * Algebra.leftMulMatrix B (g ^ (j : ℕ)) = Algebra.leftMulMatrix B (g ^ (j : ℕ)) * y := by
    rw [map_pow]; exact (Commute.pow_right hy _).eq
  rw [h1, h1, Algebra.leftMulMatrix_mulVec_repr, mul_comm, ← Algebra.leftMulMatrix_mulVec_repr,
    ← mul_one (g ^ (j : ℕ)), ← Algebra.leftMulMatrix_mulVec_repr, mul_one, mulVec_mulVec, h2,
    ← mulVec_mulVec]
  congr 1
  exact (B.equivFun.apply_symm_apply _).symm

end

section

variable {k R A : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing A] [Algebra k A] {n : ℕ}
  (b : Module.Basis (Fin n) k A)

private theorem gramL_apply (s : R ⊗[k] A) (i j : Fin n) : gramL b s i j =
    Algebra.trace R _ (s * (Algebra.TensorProduct.basis R b i * Algebra.TensorProduct.basis R b j)) := by
  simp [gramL, Algebra.TensorProduct.basis_apply]

private theorem gramL_mul (s z : R ⊗[k] A) : gramL b s * mat b z = gramL b (s * z) := by
  ext i j
  rw [Matrix.mul_apply, gramL_apply, mul_assoc, mul_left_comm z,
    ← (Algebra.TensorProduct.basis R b).sum_repr (z * _)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, gramL_apply, mat,
    Algebra.leftMulMatrix_eq_repr_mul, smul_eq_mul, mul_comm]

private theorem gramL_tr (s : R ⊗[k] A) : (gramL b s)ᵀ = gramL b s := by
  ext i j
  rw [transpose_apply, gramL_apply, gramL_apply, mul_comm (Algebra.TensorProduct.basis R b i)]

private theorem mat_io (c : R ≃ₐ[k] R) (z : R ⊗[k] A) : mat b (io c A z) = (mat b z).map c := by
  have h1 : ∀ y i, (Algebra.TensorProduct.basis R b).repr (io c A y) i =
      c ((Algebra.TensorProduct.basis R b).repr y i) := fun y i => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp [io, Algebra.TensorProduct.basis_repr_tmul]
    | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
  ext i j
  rw [map_apply, mat, mat, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, ← h1,
    map_mul (io c A)]
  simp [io, Algebra.TensorProduct.basis_apply]

private theorem mat_one_tmul (x : A) :
    mat b ((1 : R) ⊗ₜ[k] x) = (Algebra.leftMulMatrix b x).map (algebraMap k R) := by
  ext i j
  simp [mat, Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_repr_tmul]

private theorem gramL_eq (s : R ⊗[k] A) : gramL b s = gram R b 1 * mat b s := by
  rw [gram, gramL_mul, ← Algebra.TensorProduct.one_def, one_mul]

end

theorem gramBasic : GramBasic := by
  intro k R _ _ _ A _ _ n b c _
  have hdet : ∀ s, (gramL b s).det = Algebra.norm R s * (gram R b 1).det := fun s => by
    rw [gramL_eq, det_mul, mul_comm, Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis R b)]
    rfl
  refine ⟨fun s z => ⟨?_, gramL_mul b s z, ?_, hdet s⟩, fun x => ⟨?_, ?_⟩, fun g hg => ?_⟩
  · rw [ct, ← mat_io, ← gramL_tr b s, ← transpose_mul, gramL_mul, gramL_tr, mul_comm]
  · rw [ct, ← gramL_tr b (io c A s)]
    congr 1
    ext i j
    simp only [map_apply, gramL, of_apply,
      Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b)]
    rw [AddMonoidHom.map_trace]
    refine (congrArg trace (mat_io b c _).symm).trans ?_
    rw [map_mul]
    simp [io, mat]
  · ext i j
    simp only [gram, map_apply, gramL, of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b), Algebra.trace_eq_matrix_trace b]
    rw [AddMonoidHom.map_trace]
    exact congrArg trace (mat_one_tmul b _)
  · rw [gram, gramL_eq, det_mul, mul_comm, mat_one_tmul, Algebra.norm_eq_matrix_det b, RingHom.map_det]
    rfl
  · have hu : IsUnit (gram R b (1 : A)).det := by
      convert (units_of_sep (Algebra.TensorProduct.basis R b) g.val hg.2).1 using 2
      ext i j
      rw [gram, gramL_apply, ← Algebra.TensorProduct.one_def, one_mul, of_apply]
    refine ⟨hu, fun s t hst => ?_, comm_of_sep _ g.val hg.2⟩
    rw [gramL_eq b s, gramL_eq b t] at hst
    exact Algebra.leftMulMatrix_injective _ (((isUnit_iff_isUnit_det _).2 hu).mul_left_cancel hst)

end UpperTheory.ConvolutionTheory.D
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ModelEx
section
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem desc_alg {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hG : IsGal c 2)
    (L : Type) [CommRing L] [Algebra k L] [Algebra R L] [IsScalarTower k R L] (s : L →ₐ[k] L)
    (hs : ∀ r, s (algebraMap R L r) = algebraMap R L (c r)) (hss : ∀ z, s (s z) = z) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (e : R ⊗[k] A ≃ₐ[R] L), ∀ z, e (io c A z) = s (e z) := by
  let A : Subalgebra k L := AlgHom.equalizer s (AlgHom.id k L)
  let f : R ⊗[k] A →ₐ[R] L := Algebra.TensorProduct.lift (Algebra.ofId R L) A.val fun _ _ => Commute.all _ _
  have hf : ∀ (r : R) (a : A), f (r ⊗ₜ a) = algebraMap R L r * a := fun r a => rfl
  have hb := descent k R c 2 hG L s.toLinearMap
    (fun r m => by simp [Algebra.smul_def, hs]) (LinearMap.ext fun z => by simp [pow_two, hss])
  let j : A ≃ₗ[k] LinearMap.eqLocus s.toLinearMap LinearMap.id :=
    { toFun := fun a => ⟨a.1, a.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hbij : Function.Bijective f := by
    have h2 := hb.comp (j.lTensor R).bijective
    convert h2 using 1
    funext z
    induction z with
    | add a b ha hb => simp only [Function.comp_apply, map_add (f := _)] at ha hb ⊢; rw [ha, hb]
    | tmul r a => rw [hf, ← Algebra.smul_def]; rfl
  refine ⟨A, inferInstance, inferInstance, AlgEquiv.ofBijective f hbij, fun z => ?_⟩
  change f _ = s (f z)
  induction z with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul r a =>
    have h1 : io c A (r ⊗ₜ a) = c r ⊗ₜ a := by simp [io]
    have h2 : s a = a := a.2
    rw [h1, hf, hf, map_mul, hs, h2]

private theorem inv_ex {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hc : c ^ 2 = 1)
    {n : ℕ} {P : R[X]} (hP : IsCsr c n P) :
    ∃ s : AdjoinRoot P →ₐ[k] AdjoinRoot P, (∀ r, s (algebraMap R _ r) = algebraMap R _ (c r)) ∧ (∀ z, s (s z) = z) ∧
      AdjoinRoot.root P * s (AdjoinRoot.root P) = 1 := by
  obtain ⟨hm, hn, hu, hr⟩ := hP
  have hcc : ∀ r, c (c r) = r := fun r => by
    rw [← AlgEquiv.mul_apply, ← pow_two, hc]; rfl
  have hx : IsUnit (AdjoinRoot.root P) := by
    have h1 : AdjoinRoot.mk P (X * P.divX + C (P.coeff 0)) = 0 := by
      rw [X_mul_divX_add, AdjoinRoot.mk_self]
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h1
    have h2 := (hu.map (AdjoinRoot.of P)).neg
    rw [← eq_neg_of_add_eq_zero_left h1] at h2
    exact isUnit_of_mul_isUnit_left h2
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  letI : Invertible y := ⟨AdjoinRoot.root P, hy, by rw [mul_comm, hy]⟩
  have h0 : P.eval₂ ((AdjoinRoot.of P).comp (c : R →+* R)) y = 0 := by
    rw [← eval₂_map, ← eval₂_reflect_eq_zero_iff _ y n _ (natDegree_map_le.trans hn.le), hr, eval₂_mul]
    exact mul_eq_zero_of_right _ (AdjoinRoot.eval₂_root P)
  let s0 : AdjoinRoot P →+* AdjoinRoot P := AdjoinRoot.lift _ y h0
  have h1 : ∀ r, s0 (AdjoinRoot.of P r) = AdjoinRoot.of P (c r) := fun r => AdjoinRoot.lift_of h0
  have h2 : s0 (AdjoinRoot.root P) = y := AdjoinRoot.lift_root h0
  have h3 : s0 y = AdjoinRoot.root P := by
    have := congrArg s0 hy
    rw [map_mul, map_one, h2] at this
    calc s0 y = (AdjoinRoot.root P * y) * s0 y := by rw [hy, one_mul]
      _ = _ := by rw [mul_assoc, this, mul_one]
  refine ⟨⟨s0, fun a => ?_⟩, h1, fun z => ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply k R (AdjoinRoot P)]
    exact (h1 _).trans (by rw [c.commutes]; rfl)
  · change s0 (s0 z) = z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    induction p using Polynomial.induction_on with
    | C a => rw [AdjoinRoot.mk_C, h1, h1, hcc]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | monomial m a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul, ih, AdjoinRoot.mk_X, h2, h3]
  · change _ * s0 _ = 1
    rw [h2, hy]

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.modelEx :
    UpperTheory.ConvolutionTheory.D.ModelEx := by
  intro k R _ _ _ _ c hG n P hP hsep
  obtain ⟨s, hs, hss, hx⟩ := inv_ex c hG.pow hP
  obtain ⟨A, _, _, e, he⟩ := desc_alg c hG (AdjoinRoot P) s hs hss
  obtain ⟨-, -, hff, -⟩ := galBase k R k c 2 hG
  obtain ⟨hm, hn, -, -⟩ := hP
  haveI : Nontrivial R := hG.inj.nontrivial
  let B := (AdjoinRoot.powerBasis' hm).basis.map e.symm.toLinearEquiv
  haveI : Module.Finite R (R ⊗[k] A) := Module.Finite.of_basis B
  haveI : Module.Free R (R ⊗[k] A) := Module.Free.of_basis B
  haveI : Module.Finite k A := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat R
  haveI : Module.Flat k A := Module.Flat.of_flat_tensorProduct k A R
  haveI : Module.Free k A := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank k A = n := by
    rw [← Module.finrank_baseChange (R := R), Module.finrank_eq_card_basis B, Fintype.card_fin, ← hn]
    rfl
  let b := Module.finBasisOfFinrankEq k A hr
  have h1 : e.symm (AdjoinRoot.root P) * io c A (e.symm (AdjoinRoot.root P)) = 1 := by
    apply e.injective
    rw [map_mul, he, e.apply_symm_apply, hx, map_one]
  let g : (R ⊗[k] A)ˣ := Units.mkOfMulEqOne _ _ h1
  have h2 : cp (matU b g) = P := by
    set M := Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b) (e.symm (AdjoinRoot.root P)) with hM
    change M.charpoly = P
    have h3 : aeval (AdjoinRoot.root P) M.charpoly = 0 := by
      have h4 := Matrix.aeval_self_charpoly M
      rw [hM, aeval_algHom_apply, ← hM, map_eq_zero_iff _ (Algebra.leftMulMatrix_injective _),
        aeval_algHom_apply] at h4
      exact (map_eq_zero_iff _ e.symm.injective).1 h4
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h3
    exact eq_of_monic_of_dvd_of_natDegree_le hm M.charpoly_monic h3
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hn])
  exact ⟨A, _, _, b, g, ⟨h1, h2 ▸ hsep⟩, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ReflectCpInv
section
noncomputable section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.D

private lemma reflect_cp_inv {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (g : GL (Fin n) R) :
    reflect n (cp g⁻¹) = C ((cp g⁻¹).coeff 0) * cp g := by
  have h1 : reflect n (cp g⁻¹) = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpolyRev := by
    rw [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, cp]
  have h2 := Matrix.charpoly_inv ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) (Units.isUnit _)
  have h3 := Matrix.det_eq_sign_charpoly_coeff ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  rw [← Matrix.coe_units_inv, inv_inv] at h2
  have h4 : IsUnit ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have h5 := Ring.mul_inverse_cancel _ h4
  rw [h1, cp, cp, h2]
  nth_rewrite 1 [h3] at h5
  have h6 := congrArg (C : R → R[X]) h5
  simp only [map_mul, map_pow, map_neg, map_one] at h6
  linear_combination (-((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpolyRev) * h6

private lemma ct_mul {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) : ct c (A * B) = ct c B * ct c A := by
  rw [ct, ct, ct, ← Matrix.transpose_mul, Matrix.map_mul]

private lemma ct_ct {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hc : c ^ 2 = 1) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : ct c (ct c A) = A := by
  ext i j
  have := congrArg (fun f : R ≃ₐ[k] R => f (A i j)) hc
  simpa [ct, pow_two] using this

private lemma csr_of_cong {k R : Type} [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R] (c : R ≃ₐ[k] R) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (g : GL (Fin n) R) (hJ : IsUnit J.det) (h : cong c g J = J) :
    IsCsr c n (cp g) := by
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  have h1 : ct c (g : Matrix (Fin n) (Fin n) R) =
      u.val * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (u⁻¹).val := by
    rw [cong] at h
    nth_rewrite 1 [← h]
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  have h2 : (cp g).map (c : R →+* R) = cp g⁻¹ := by
    have h3 := congrArg Matrix.charpoly h1
    rw [Matrix.coe_units_inv u, Matrix.charpoly_units_conj, ct, Matrix.charpoly_transpose] at h3
    rw [cp, cp, ← h3, ← Matrix.charpoly_map]
    rfl
  refine ⟨Matrix.charpoly_monic _, ?_, ?_, ?_⟩
  · rw [cp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · have h4 : IsUnit (g : Matrix (Fin n) (Fin n) R).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    rw [Matrix.det_eq_sign_charpoly_coeff] at h4
    exact isUnit_of_mul_isUnit_right h4
  · have h5 : c ((cp g).coeff 0) = (cp g⁻¹).coeff 0 := by
      rw [← h2, Polynomial.coeff_map]
      rfl
    rw [h2, h5, reflect_cp_inv]

theorem csrOf : CsrOf := by
  intro k R _ _ _ _ c hc n
  refine ⟨fun J g hJ h => csr_of_cong c J g hJ h, fun d => ?_⟩
  refine csr_of_cong c ((d⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) _
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)) ?_
  have h1 : (th c d).val = ct c (d⁻¹ : GL (Fin n) R).val := rfl
  have h2 : ct c d.val * (th c d).val = 1 := (th c d).inv_val
  rw [cong, Units.val_mul, ct_mul]
  nth_rewrite 1 [h1]
  rw [ct_ct c hc]
  simp only [mul_assoc, Units.inv_mul_cancel_left, h2, mul_one]

end UpperTheory.ConvolutionTheory.D
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.TBase
section
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.D.tBase :
    UpperTheory.ConvolutionTheory.D.TBase := by
  intro k R _ _ _ _ A _ _ n b c hc g hg
  haveI : Module.Finite k A := Module.Finite.of_basis b
  let e : A ⊗[k] R ≃ₐ[k] R ⊗[k] A := Algebra.TensorProduct.comm k A R
  let τ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R := Algebra.TensorProduct.congr AlgEquiv.refl c
  have hτ : UpperTheory.ConvolutionTheory.D.IsGal τ 2 := (UpperTheory.ConvolutionTheory.D.galBase k R A c 2 hc).2.2.2
  have he : ∀ z, e (τ z) = UpperTheory.ConvolutionTheory.D.io c A (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [e, τ, UpperTheory.ConvolutionTheory.D.io]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 : ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) *
      UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1 := by
    have h2 : UpperTheory.ConvolutionTheory.D.io c A (g : R ⊗[k] A) *
        UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [Units.inv_eq_of_mul_eq_one_right hg.1] at h2 ⊢
    exact h2
  let a : (A ⊗[k] R)ˣ := Units.map (e.symm : R ⊗[k] A →* A ⊗[k] R) g⁻¹
  have ha : e (a : A ⊗[k] R) = ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) := e.apply_symm_apply _
  obtain ⟨z, hz⟩ := UpperTheory.ConvolutionTheory.D.h90 k k A (A ⊗[k] R) τ 2 hτ a (by
    apply e.injective
    rw [Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one, AlgEquiv.one_apply,
      map_mul, he, ha, h1, map_one])
  refine ⟨Units.map (e : A ⊗[k] R →* R ⊗[k] A) z, ?_⟩
  have h3 := congrArg e hz
  rw [map_mul, he, ha] at h3
  change UpperTheory.ConvolutionTheory.D.io c A (e z) = g * e z
  calc UpperTheory.ConvolutionTheory.D.io c A (e z)
      = g * (((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) * UpperTheory.ConvolutionTheory.D.io c A (e z)) := by
        rw [Units.mul_inv_cancel_left]
    _ = g * e z := by rw [h3]
end

