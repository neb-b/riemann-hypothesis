module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
section
noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.SchwartzFstOp

variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasTemperateGrowth_prodMk_const (x' : V') : Function.HasTemperateGrowth (fun x : V => (x, x')) := by
  have h := (ContinuousLinearMap.inl ℝ V V').hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const ((0 : V), x'))
  convert h using 1
  funext x
  change (x, x') = (x, 0) + (0, x')
  simp

theorem antilipschitz_prodMk_const (x' : V') : AntilipschitzWith 1 (fun x : V => (x, x')) :=
  AntilipschitzWith.of_le_mul_dist fun x y => by
    simp only [NNReal.coe_one, one_mul, Prod.dist_eq, dist_self]
    exact le_max_left _ _

def sliceCLM (x' : V') : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (hasTemperateGrowth_prodMk_const x') (antilipschitz_prodMk_const x')

@[simp] theorem sliceCLM_apply (x' : V') (f : 𝓢(V × V', ℂ)) (x : V) : sliceCLM x' f x = f (x, x') := rfl

def lineSnd (v' : V') : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V × V', ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢(V × V', ℂ) ((0 : V), v')

theorem lineSnd_apply (v' : V') (f : 𝓢(V × V', ℂ)) (p : V × V') :
    lineSnd v' f p = fderiv ℝ f p ((0 : V), v') := by
  rw [lineSnd, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem lineSnd_add (v₁ v₂ : V') (f : 𝓢(V × V', ℂ)) :
    lineSnd (v₁ + v₂) f = lineSnd v₁ f + lineSnd v₂ f := by
  ext p
  simp only [lineSnd_apply, SchwartzMap.add_apply]
  rw [← map_add (f := _)]
  simp

theorem lineSnd_smul (c : ℝ) (v : V') (f : 𝓢(V × V', ℂ)) :
    lineSnd (c • v) f = (c : ℂ) • lineSnd v f := by
  ext p
  simp only [lineSnd_apply, SchwartzMap.smul_apply]
  rw [show ((0 : V), c • v) = c • ((0 : V), v) by simp, map_smul]
  simp [Complex.real_smul]

def opFst (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V') : E :=
  T (sliceCLM p.2 f) p.1

theorem opFst_apply (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V') :
    opFst T f (y, x') = T (sliceCLM x' f) y := rfl

def dSndCLM [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V') :
    V' →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v' => opFst T (lineSnd v' f) p
      map_add' := fun v₁ v₂ => by simp [opFst, lineSnd_add]
      map_smul' := fun c v => by
        simp only [opFst, lineSnd_smul, map_smul, SchwartzMap.smul_apply, RingHom.id_apply]
        rw [Complex.coe_smul] }

theorem dSndCLM_apply [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V')
    (v' : V') : dSndCLM T f p v' = opFst T (lineSnd v' f) p := rfl

end GlobalTheory.SchwartzFstOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianEndoMatrixRationalInLatticeBasis
section
open Matrix

namespace GlobalTheory

def imFormRight {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun w := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [star_add, mulVec_add, dotProduct_add]
  map_smul' r w := by
    simp [star_smul, mulVec_smul, dotProduct_smul, Complex.smul_im]

def imFormLeft {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun z := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [add_dotProduct]
  map_smul' r z := by
    simp [smul_dotProduct, Complex.smul_im]

theorem herm_endo_matrix_rat : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₁.mulVec (star (e l))).im) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₂.mulVec (star (e l))).im) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    ∃ Tq : Matrix (Fin n) (Fin n) ℚ,
      Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) := by
  intro g n e H₁ H₂ hpos h1 h2 γ hγ
  classical
  set T := LinearMap.toMatrix e e (γ.restrictScalars ℝ) with hT
  let A₁ : Matrix (Fin n) (Fin n) ℝ := fun k l => (e k ⬝ᵥ H₁ *ᵥ star (e l)).im
  let A₂ : Matrix (Fin n) (Fin n) ℝ := fun k l => (e k ⬝ᵥ H₂ *ᵥ star (e l)).im

  have hγe : ∀ l, γ (e l) = ∑ m, T m l • e m := by
    intro l
    have := e.sum_repr (γ (e l))
    rw [← this]
    simp [hT, LinearMap.toMatrix_apply]

  have key : A₁ * T = A₂ := by
    ext k l
    rw [Matrix.mul_apply]
    show _ = (e k ⬝ᵥ H₂ *ᵥ star (e l)).im
    rw [hγ, hγe l]
    have := map_sum (imFormRight H₁ (e k)) (fun m : Fin n => T m l • e m) (Finset.univ : Finset (Fin n))
    simp only [map_smul, smul_eq_mul] at this
    change _ = imFormRight H₁ (e k) _
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]; rfl

  have hdet : A₁.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    set v := ∑ l, x l • e l with hv
    have hk : ∀ k, imFormRight H₁ (e k) v = 0 := by
      intro k
      have := congrFun hx k
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hv, map_sum]
      simp only [map_smul, smul_eq_mul]
      simp only [mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]; rfl
    have hu : ∀ u, imFormLeft H₁ v u = 0 := by
      intro u
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← e.sum_repr u, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [map_smul]
      have := hk k
      simp only [imFormRight, imFormLeft, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
      rw [this, smul_zero]
    have hre : (v ⬝ᵥ H₁ *ᵥ star v).re = 0 := by
      have := hu (Complex.I • v)
      simp only [imFormLeft, LinearMap.coe_mk, AddHom.coe_mk, smul_dotProduct, smul_eq_mul,
        Complex.mul_im, Complex.I_re, Complex.I_im] at this
      simpa using this
    have hv0 : v = 0 := by
      by_contra hne
      have := hpos v hne
      linarith
    apply hx0
    have : e.equivFun.symm x = 0 := by rw [Module.Basis.equivFun_symm_apply]; exact hv0
    exact e.equivFun.symm.injective (by rw [this, map_zero])

  choose m₁ hm₁ using h1
  choose m₂ hm₂ using h2
  let A₁q : Matrix (Fin n) (Fin n) ℚ := fun k l => (m₁ k l : ℚ)
  let A₂q : Matrix (Fin n) (Fin n) ℚ := fun k l => (m₂ k l : ℚ)
  have hA₁ : A₁q.map (Rat.castHom ℝ) = A₁ := by
    ext k l
    show ((m₁ k l : ℚ) : ℝ) = _
    rw [Rat.cast_intCast, hm₁]
  have hA₂ : A₂q.map (Rat.castHom ℝ) = A₂ := by
    ext k l
    show ((m₂ k l : ℚ) : ℝ) = _
    rw [Rat.cast_intCast, hm₂]
  have hdetq : IsUnit A₁q.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdet
    have := (Rat.castHom ℝ).map_det A₁q
    rw [h0, map_zero] at this
    rw [← hA₁]
    exact this.symm
  have hdetR : IsUnit A₁.det := isUnit_iff_ne_zero.2 hdet
  refine ⟨A₁q⁻¹ * A₂q, ?_⟩
  have h3 : A₁ * (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = A₂ := by
    have := congrArg (fun M => M.map (Rat.castHom ℝ)) (Matrix.mul_nonsing_inv_cancel_left A₁q A₂q hdetq)
    rw [Matrix.map_mul, hA₁, hA₂] at this
    exact this
  have h4 : (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = T := by
    calc (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ)
        = A₁⁻¹ * (A₁ * (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ)) :=
          (Matrix.nonsing_inv_mul_cancel_left A₁ _ hdetR).symm
      _ = A₁⁻¹ * (A₁ * T) := by rw [h3, key]
      _ = T := Matrix.nonsing_inv_mul_cancel_left A₁ T hdetR
  simpa using h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFlagComplementPosDefFactorization
section
open scoped ComplexOrder

namespace GlobalTheory

open Matrix

theorem schur_complement_step_cpx : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  intro n r J θ hJ hpos X Y hXY l d h u₁ A X₁ Xb X₂ Yb Y₂ hθ h0

  let K : Matrix (Fin (l + d)) (Fin d) ℂ := fun i j =>
    Fin.addCases (motive := fun _ => ℂ) (fun i => A i j)
      (fun i => (1 : Matrix (Fin d) (Fin d) ℂ) i j) i
  have hK : X₂ * K = Xb + X₁ * A := by
    ext a c
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp only [K, Fin.addCases_left, Fin.addCases_right, Matrix.add_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Matrix.mul_apply]
    rw [add_comm]
    rfl
  have hP : ∀ {m : ℕ} (f : Fin m → Fin (l + d)),
      (X₂.submatrix id f)ᴴ * (J * θ) * (Xb + X₁ * A)
        = (X₂ᴴ * (J * θ) * (Xb + X₁ * A)).submatrix f id := fun _ => rfl
  have hrow1 : (X₂ᴴ * (J * θ) * (Xb + X₁ * A)).submatrix (Fin.castAdd d) id = 0 :=
    (hP (Fin.castAdd d)).symm.trans h0
  have key : ∀ P : Matrix (Fin (l + d)) (Fin d) ℂ, P.submatrix (Fin.castAdd d) id = 0 →
      Y₂ * P = Yb * P.submatrix (Fin.natAdd l) id := by
    intro P hP0
    ext a c
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
    have h00 : ∀ i, P (Fin.castAdd d i) c = 0 := fun i => by
      simpa using congrFun (congrFun hP0 i) c
    simp only [h00, mul_zero, Finset.sum_const_zero, zero_add]
    rfl
  have hmain : θ * (Xb + X₁ * A) = u₁ * Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A)) := by
    calc θ * (Xb + X₁ * A) = θ * X₂ * K := by rw [← hK, Matrix.mul_assoc]
      _ = u₁ * Y₂ * (X₂ᴴ * (J * θ) * X₂) * K := by rw [hθ]
      _ = u₁ * (Y₂ * (X₂ᴴ * (J * θ) * (X₂ * K))) := by simp only [Matrix.mul_assoc]
      _ = u₁ * (Y₂ * (X₂ᴴ * (J * θ) * (Xb + X₁ * A))) := by rw [hK]
      _ = u₁ * (Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A))) := by rw [key _ hrow1]; rfl
      _ = u₁ * Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A)) := (Matrix.mul_assoc u₁ Yb _).symm
  have hzero : (X₁ * A)ᴴ * (J * θ) * (Xb + X₁ * A) = 0 := by
    have h0' := h0
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc] at h0' ⊢
    rw [h0', Matrix.mul_zero]
  have hsame : Xbᴴ * (J * θ) * (Xb + X₁ * A)
      = (Xb + X₁ * A)ᴴ * (J * θ) * (Xb + X₁ * A) := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.add_mul, hzero, add_zero]
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg Matrix.conjTranspose hXY
    simpa [Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hL : (Ybᴴ * J) * (Xb + X₁ * A) = 1 := by
    have e1 : Ybᴴ * J * Xb = 1 := by
      have : Ybᴴ * J * Xb = (Yᴴ * J * X).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
          (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := rfl
      rw [this, hYX]
      ext i j
      simp [Matrix.one_apply, Fin.ext_iff]
    have e2 : Ybᴴ * J * X₁ = 0 := by
      have : Ybᴴ * J * X₁ = (Yᴴ * J * X).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
          (fun j : Fin l => (⟨j.val, by omega⟩ : Fin r)) := rfl
      rw [this, hYX]
      ext i j
      have := j.isLt
      simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.ext_iff, Matrix.zero_apply]
      rw [if_neg (by omega)]
    rw [Matrix.mul_add, e1, ← Matrix.mul_assoc, e2, Matrix.zero_mul, add_zero]
  have hinj : Function.Injective (Xb + X₁ * A).mulVec := by
    intro v w hvw
    have := congrArg (Ybᴴ * J).mulVec hvw
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec, Matrix.one_mulVec] at this
    exact this
  refine ⟨hmain, ?_⟩
  rw [hsame]
  exact hpos.conjTranspose_mul_mul_same hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFlagUnipotentMatrixExistsSparse
section
open scoped ComplexOrder

namespace GlobalTheory

theorem isotropic_unipotent_column_relations : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      u * X₁ = X₁ → u * Xb = Xb + X₁ * A →
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a) →
      ∃ N : Matrix (Fin r) (Fin r) ℂ, u * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u v - v = Matrix.mulVec X w) := by
  intro n r J X hX l d h u A X₁ Xb X₂ h1 hb hperp
  classical

  have hext : ∀ (m : ℕ) (hm : m ≤ r) (a : Fin m → ℂ),
      Matrix.mulVec X (fun i : Fin r => if hi : i.val < m then a ⟨i.val, hi⟩ else 0) =
        Matrix.mulVec (X.submatrix id fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) a := by
    intro m hm a
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
    symm
    refine Fintype.sum_of_injective (fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) ?_ _ _ ?_ ?_
    · intro x y hxy
      exact Fin.ext (by simpa using congrArg Fin.val hxy)
    · intro i hi
      have : ¬ i.val < m := by
        intro hlt
        exact hi ⟨⟨i.val, hlt⟩, rfl⟩
      simp [this]
    · intro j
      simp
  have he1 : ∀ a : Fin l → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0) =
      Matrix.mulVec X₁ a := fun a => hext l (by omega) a
  have he2 : ∀ a : Fin (l + d) → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l + d then a ⟨i.val, hi⟩ else 0) =
      Matrix.mulVec X₂ a := fun a => hext (l + d) h a
  have hcol : ∀ (v : Fin n → ℂ) (i : Fin (l + d)),
      Matrix.mulVec (X₂.conjTranspose * J) v i =
        Matrix.mulVec (X.conjTranspose * J) v ⟨i.val, by omega⟩ := by
    intro v i
    rfl
  have hXc : ∀ (i j : Fin r), Matrix.mulVec (X.conjTranspose * J) (fun k => X k j) i = 0 := by
    intro i j
    exact congrFun (congrFun hX i) j
  have key : ∀ j : Fin r, ∃ c : Fin r → ℂ,
      (∀ i, c i ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
      Matrix.mulVec u (fun k => X k j) = (fun k => X k j) + Matrix.mulVec X c := by
    intro j
    by_cases hj1 : j.val < l
    · refine ⟨0, fun i hi => absurd rfl hi, ?_⟩
      funext k
      have := congrFun (congrFun h1 k) ⟨j.val, hj1⟩
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, X₁] using this
    by_cases hj2 : j.val < l + d
    · refine ⟨fun i => if hi : i.val < l then A ⟨i.val, hi⟩ ⟨j.val - l, by omega⟩ else 0, ?_, ?_⟩
      · intro i hi
        left
        by_cases hil : i.val < l
        · exact ⟨hil, by omega⟩
        · exact absurd (by simp [hil]) hi
      · have he1' := he1 (fun i => A i ⟨j.val - l, by omega⟩)
        beta_reduce at he1'
        rw [he1']
        funext k
        have := congrFun (congrFun hb k) ⟨j.val - l, by omega⟩
        have hjj : (⟨l + (j.val - l), by omega⟩ : Fin r) = j := Fin.ext (by simp; omega)
        simp only [Matrix.mul_apply, Matrix.add_apply, Xb, X₁, Matrix.submatrix_apply, id, hjj] at this
        simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, X₁] using this
    · have hz : Matrix.mulVec (X₂.conjTranspose * J) (fun k => X k j) = 0 := by
        funext i
        rw [hcol]
        exact hXc _ _
      obtain ⟨w, a, hwa⟩ := hperp _ hz
      refine ⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) +
          (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩
      · intro i hi
        right
        refine ⟨?_, by omega⟩
        by_contra hc
        have hc' : ¬ i.val < l := by omega
        exact hi (by simp [hc, hc'])
      · rw [Matrix.mulVec_add, he1, he2, ← hwa]
        abel
  choose c hc hc' using key
  refine ⟨Matrix.of fun i j => c j i, ?_, ?_, ?_⟩
  · ext k j
    have := congrFun (hc' j) k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · intro i j hij
    exact hc j i (by simpa using hij)
  · intro v hv
    have hz : Matrix.mulVec (X₂.conjTranspose * J) v = 0 := by
      funext i
      rw [hcol]
      exact hv _ (by simp)
    obtain ⟨w, a, hwa⟩ := hperp v hz
    refine ⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) +
        (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩
    · intro i hi
      by_contra hc
      have hc' : ¬ i.val < l := by omega
      exact hi (by simp [hc, hc'])
    · rw [hwa, Matrix.mulVec_add, he1, he2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormEqCombinationOfSelfAdjointIdentity
section
open Matrix

namespace GlobalTheory

theorem herm_form_identity (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h1 : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w)))
    (h2 : ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ))
    (z w : Fin g → ℂ) :
    z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by
  have hadd : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z u v : Fin g → ℂ),
      z ⬝ᵥ H.mulVec (star (u + v)) = z ⬝ᵥ H.mulVec (star u) + z ⬝ᵥ H.mulVec (star v) := by
    intro H z u v; rw [star_add, mulVec_add, dotProduct_add]
  have hsmul : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      z ⬝ᵥ H.mulVec (star (a • v)) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, star_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]
    simp
  have hsmulL : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      (a • z) ⬝ᵥ H.mulVec (star v) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, smul_dotProduct, smul_eq_mul]
  have hsum : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (f : Fin r → (Fin g → ℂ)),
      z ⬝ᵥ H.mulVec (star (∑ i, f i)) = ∑ i, z ⬝ᵥ H.mulVec (star (f i)) := by
    intro H z f
    rw [star_sum, mulVec_sum, dotProduct_sum]
  have hsa : ∀ (q : Polynomial ℚ) (z w : Fin g → ℂ),
      z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ q w)) =
        Polynomial.aeval γ q z ⬝ᵥ H₂.mulVec (star w) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro z w
      simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
      rw [hsmul, hsmulL]
    | add p q hp hq =>
      intro z w
      simp only [map_add (f := _), LinearMap.add_apply]
      rw [hadd, hp, hq, add_dotProduct]
    | monomial n a ih =>
      intro z w
      have e : Polynomial.C a * Polynomial.X ^ (n+1) =
          (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      have e' : Polynomial.C a * Polynomial.X ^ (n+1) =
          Polynomial.X * (Polynomial.C a * Polynomial.X ^ n) := by ring
      calc z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ (n+1)) w))
          = z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) (γ w))) := by
            rw [e, map_mul (Polynomial.aeval γ) (Polynomial.C a * Polynomial.X ^ n) Polynomial.X,
              Polynomial.aeval_X, Module.End.mul_apply]
        _ = Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z ⬝ᵥ H₂.mulVec (star (γ w)) :=
            ih _ _
        _ = γ (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z) ⬝ᵥ H₂.mulVec (star w) :=
            h2 _ _
        _ = _ := by
            rw [e', map_mul (Polynomial.aeval γ) Polynomial.X (Polynomial.C a * Polynomial.X ^ n),
              Polynomial.aeval_X, Module.End.mul_apply]
  have comm : ∀ q : Polynomial ℚ, (Polynomial.aeval γ q) ^ 2 * γ =
      γ * (Polynomial.aeval γ q * Polynomial.aeval γ q) := by
    intro q
    rw [show (Polynomial.aeval γ q) ^ 2 * γ = Polynomial.aeval γ (q ^ 2 * Polynomial.X) by
          simp [map_mul, map_pow],
      show q ^ 2 * Polynomial.X = Polynomial.X * (q * q) by ring]
    simp [map_mul]
  have hw : w = c₀ • γ w + ∑ i, c i • (γ (Polynomial.aeval γ (p i) (Polynomial.aeval γ (p i) w))) := by
    have := congrArg (fun f : Module.End ℂ (Fin g → ℂ) => f w) hid
    simp only [Module.End.one_apply, LinearMap.add_apply, LinearMap.smul_apply,
      comm] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
    exact this
  conv_lhs => rw [hw]
  rw [hadd, hsmul, hsum, ← h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsmul, ← h1, hsa]

end GlobalTheory
end

