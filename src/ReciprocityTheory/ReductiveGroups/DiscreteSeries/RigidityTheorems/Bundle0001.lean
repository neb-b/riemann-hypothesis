module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IsInLieAlgebraISmulAddConjTranspose
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rq_JJ (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem rq_JH (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem rq_actM_add {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem rq_actM_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp [actM, Finset.smul_sum, mul_smul]

theorem rq_K_unit {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ * k = 1 ∧ k * kᴴ = 1 := by
  obtain ⟨hu, -⟩ := hk
  exact ⟨Matrix.mem_unitaryGroup_iff'.mp hu, Matrix.mem_unitaryGroup_iff.mp hu⟩

theorem rq_K_JH {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ * Jm ε = Jm ε * kᴴ := by
  obtain ⟨h1, h2⟩ := rq_K_unit hk
  have hc : k * Jm ε = Jm ε * k := hk.2
  calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, mul_one]
    _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [mul_assoc]
    _ = kᴴ * (k * Jm ε) * kᴴ := by rw [hc]
    _ = kᴴ * k * Jm ε * kᴴ := by simp only [mul_assoc]
    _ = Jm ε * kᴴ := by rw [h1, one_mul]

theorem rq_K_UJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  have hc : k * Jm ε = Jm ε * k := hk.2
  show kᴴ * Jm ε * k = Jm ε
  rw [mul_assoc, ← hc, ← mul_assoc, (rq_K_unit hk).1, one_mul]

theorem rq_KH {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  refine ⟨?_, rq_K_JH hk⟩
  rw [Matrix.mem_unitaryGroup_iff]
  show kᴴ * kᴴᴴ = 1
  rw [Matrix.conjTranspose_conjTranspose]
  exact (rq_K_unit hk).1

theorem rq_UJ_mul {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have ha' : aᴴ * Jm ε * a = Jm ε := ha
  have hb' : bᴴ * Jm ε * b = Jm ε := hb
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [mul_assoc]
    _ = Jm ε := by rw [ha', hb']

theorem rq_inG_conj {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : inG ε (k * X * kᴴ) := by
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hc : k * Jm ε = Jm ε * k := hk.2
  have hc' := rq_K_JH hk
  show (k * X * kᴴ)ᴴ * Jm ε + Jm ε * (k * X * kᴴ) = 0
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc _ = k * (Xᴴ * Jm ε + Jm ε * X) * kᴴ := by
        rw [mul_add, add_mul]
        simp only [mul_assoc]
        rw [hc', ← mul_assoc (Jm ε) k, ← hc, mul_assoc]
    _ = 0 := by rw [hX', mul_zero, zero_mul]

theorem rq_exp_mem (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
  have hJJ := rq_JJ ε
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hXH : Xᴴ = -(Jm ε * X * Jm ε) := by
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [eq_neg_of_add_eq_zero_left hX', neg_mul]
  have hAH : ((t : ℂ) • X)ᴴ = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [hJinv, Matrix.conjTranspose_smul, hXH]
    simp only [Complex.star_def, Complex.conj_ofReal, mul_neg, neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_neg]
  have hEu : IsUnit (NormedSpace.exp ((t : ℂ) • X)) := Matrix.isUnit_exp _
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  rw [← Matrix.exp_conjTranspose, hAH, Matrix.exp_conj _ _ hJu, hJinv, Matrix.exp_neg]
  simp only [mul_assoc]
  rw [← mul_assoc (Jm ε) (Jm ε), hJJ, one_mul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hEu), mul_one]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rq_main_G {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : D) :
    σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
  have hkU := rq_K_unit hk
  have hkUJ := rq_K_UJ hk
  have hkHUJ := rq_K_UJ (rq_KH hk)
  have hkinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkU.1
  have hku : IsUnit k := ⟨⟨k, kᴴ, hkU.2, hkU.1⟩, rfl⟩
  have h2 := hD.deriv (k * X * kᴴ) (rq_inG_conj hk hX) ⟨σ k (v : H), hD.kStable k hk v v.2⟩
  have h1 : HasDerivAt (fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (σ k ((actM E X v : D) : H)) 0 := by
    have := ((σ k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hD.deriv X hX v)
    simpa [Function.comp_def] using this
  have hfun : (fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (k * X * kᴴ))) (σ k (v : H)) := by
    funext t
    have heUJ := rq_exp_mem ε X hX t
    have hexp : NormedSpace.exp ((t : ℂ) • (k * X * kᴴ)) = k * NormedSpace.exp ((t : ℂ) • X) * kᴴ := by
      rw [← hkinv, ← Matrix.exp_conj _ _ hku, Matrix.mul_smul, Matrix.smul_mul]
    rw [hexp]
    have e1 : σ (k * NormedSpace.exp ((t : ℂ) • X) * kᴴ * k) =
        (σ (k * NormedSpace.exp ((t : ℂ) • X) * kᴴ)).comp (σ k) :=
      hσ.1.2 _ (rq_UJ_mul (rq_UJ_mul hkUJ heUJ) hkHUJ) k hkUJ
    rw [mul_assoc (k * NormedSpace.exp ((t : ℂ) • X)), hkU.1, mul_one, hσ.1.2 k hkUJ _ heUJ] at e1
    exact congrArg (fun L : H →L[ℂ] H => L (v : H)) e1
  rw [hfun] at h1
  exact h1.unique h2

end Rep

theorem rq_inG_S (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (X - Jm ε * Xᴴ * Jm ε) := by
  have hJJ := rq_JJ ε
  have hJH := rq_JH ε
  show (X - Jm ε * Xᴴ * Jm ε)ᴴ * Jm ε + Jm ε * (X - Jm ε * Xᴴ * Jm ε) = 0
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJH, Matrix.conjTranspose_conjTranspose,
    sub_mul, mul_sub, mul_assoc, hJJ, mul_one]
  rw [← mul_assoc (Jm ε) (Jm ε), hJJ, one_mul]
  abel

theorem isInLieAlgebra_I_smul_add_conjTranspose (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (Complex.I • (X + Jm ε * Xᴴ * Jm ε)) := by
  have hJJ := rq_JJ ε
  have hJH := rq_JH ε
  show (Complex.I • (X + Jm ε * Xᴴ * Jm ε))ᴴ * Jm ε + Jm ε * (Complex.I • (X + Jm ε * Xᴴ * Jm ε)) = 0
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_I, Matrix.smul_mul, Matrix.mul_smul,
    add_mul, mul_add, mul_assoc, hJJ, mul_one]
  rw [← mul_assoc (Jm ε) (Jm ε), hJJ, one_mul, neg_smul, add_comm (Jm ε * X) (Xᴴ * Jm ε), neg_add_cancel]

theorem rq_decomp (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    (1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε) + (-(Complex.I / 2)) • (Complex.I • (X + Jm ε * Xᴴ * Jm ε))
      = X := by
  have h : -(Complex.I / 2) * Complex.I = 1 / 2 := by
    rw [neg_mul, div_mul_eq_mul_div, Complex.I_mul_I]
    ring
  rw [smul_smul, h, ← smul_add, sub_add_add_cancel, ← two_smul ℂ X, smul_smul]
  norm_num

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rq_lin {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : D) (a b : ℂ)
    {S T : Matrix (Fin n) (Fin n) ℂ}
    (hS : σ k ((actM E S v : D) : H) =
      ((actM E (k * S * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H))
    (hT : σ k ((actM E T v : D) : H) =
      ((actM E (k * T * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H)) :
    σ k ((actM E (a • S + b • T) v : D) : H) =
      ((actM E (k * (a • S + b • T) * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
  have e1 : k * (a • S + b • T) * kᴴ = a • (k * S * kᴴ) + b • (k * T * kᴴ) := by
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, rq_actM_add, rq_actM_add, rq_actM_smul, rq_actM_smul, rq_actM_smul, rq_actM_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add (f := _), map_smul,
    hS, hT]

end Rep

theorem derived_adK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (X : Matrix (Fin n) (Fin n) ℂ) (v : D) :
    σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
  have hS := rq_main_G hσ hD hk (rq_inG_S ε X) v
  have hT := rq_main_G hσ hD hk (isInLieAlgebra_I_smul_add_conjTranspose ε X) v
  have := rq_lin hD hk v (1 / 2 : ℂ) (-(Complex.I / 2)) hS hT
  rwa [rq_decomp] at this

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.SopNegComm
section
noncomputable section

open Finset Matrix WithLp

namespace ReciprocityTheory.ChartRestriction.DS

namespace USum

variable {n : ℕ}

section Ops

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

def sop (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) : WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).symm.toContinuousLinearMap ∘L
    ((A.prodMap B) ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).toContinuousLinearMap)

theorem sop_apply (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (x : WithLp 2 (H₁ × H₂)) :
    sop A B x = toLp 2 (A (ofLp x).1, B (ofLp x).2) := rfl

theorem norm_sop {A : H₁ →L[ℂ] H₁} {B : H₂ →L[ℂ] H₂} (hA : ∀ v, ‖A v‖ = ‖v‖)
    (hB : ∀ v, ‖B v‖ = ‖v‖) (x : WithLp 2 (H₁ × H₂)) : ‖sop A B x‖ = ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  show √(‖A (ofLp x).1‖ ^ 2 + ‖B (ofLp x).2‖ ^ 2) = √(‖(ofLp x).1‖ ^ 2 + ‖(ofLp x).2‖ ^ 2)
  rw [hA, hB]

theorem sop_one : sop (1 : H₁ →L[ℂ] H₁) (1 : H₂ →L[ℂ] H₂) = 1 := by
  ext x; rfl

theorem sop_comp (A A' : H₁ →L[ℂ] H₁) (B B' : H₂ →L[ℂ] H₂) :
    sop (A.comp A') (B.comp B') = (sop A B).comp (sop A' B') := by
  ext x; rfl

theorem sop_neg_comm (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (x : WithLp 2 (H₁ × H₂)) :
    sop 1 (-1) (sop A B x) = sop A B (sop 1 (-1) x) := by
  simp only [sop_apply, WithLp.ofLp_toLp]
  simp

theorem inner_sum (x y : WithLp 2 (H₁ × H₂)) :
    inner ℂ x y = inner ℂ (ofLp x).1 (ofLp y).1 + inner ℂ (ofLp x).2 (ofLp y).2 := rfl

def sD (D₁ : Submodule ℂ H₁) (D₂ : Submodule ℂ H₂) : Submodule ℂ (WithLp 2 (H₁ × H₂)) :=
  (D₁.prod D₂).comap (WithLp.linearEquiv 2 ℂ (H₁ × H₂)).toLinearMap

variable {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}

def toP : sD D₁ D₂ →ₗ[ℂ] D₁ × D₂ where
  toFun x := (⟨(ofLp (x : WithLp 2 (H₁ × H₂))).1, x.2.1⟩, ⟨(ofLp (x : WithLp 2 (H₁ × H₂))).2, x.2.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ofP : D₁ × D₂ →ₗ[ℂ] sD D₁ D₂ where
  toFun p := ⟨toLp 2 ((p.1 : H₁), (p.2 : H₂)), p.1.2, p.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toPrimitive_ofPrimitive (p : D₁ × D₂) : toP (ofP p) = p := rfl

def lift (F₁ : Module.End ℂ D₁) (F₂ : Module.End ℂ D₂) : Module.End ℂ (sD D₁ D₂) :=
  ofP ∘ₗ (F₁.prodMap F₂) ∘ₗ toP

theorem lift_ofP (F₁ : Module.End ℂ D₁) (F₂ : Module.End ℂ D₂) (p : D₁ × D₂) :
    lift F₁ F₂ (ofP p) = ofP (F₁ p.1, F₂ p.2) := rfl

theorem lift_mul (F₁ G₁ : Module.End ℂ D₁) (F₂ G₂ : Module.End ℂ D₂) :
    lift (F₁ * G₁) (F₂ * G₂) = lift F₁ F₂ * lift G₁ G₂ := LinearMap.ext fun _ => rfl

theorem lift_sub (F₁ G₁ : Module.End ℂ D₁) (F₂ G₂ : Module.End ℂ D₂) :
    lift (F₁ - G₁) (F₂ - G₂) = lift F₁ F₂ - lift G₁ G₂ := LinearMap.ext fun _ => rfl

theorem lift_zero : lift (0 : Module.End ℂ D₁) (0 : Module.End ℂ D₂) = 0 :=
  LinearMap.ext fun _ => rfl

def liftL : (Module.End ℂ D₁ × Module.End ℂ D₂) →ₗ[ℂ] Module.End ℂ (sD D₁ D₂) where
  toFun p := lift p.1 p.2
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_smul' _ _ := LinearMap.ext fun _ => rfl

theorem liftL_apply (p : Module.End ℂ D₁ × Module.End ℂ D₂) : liftL p = lift p.1 p.2 := rfl

def sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂) :
    Fin n → Fin n → Module.End ℂ (sD D₁ D₂) :=
  fun a b => lift (E₁ a b) (E₂ a b)

theorem actM_sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM (sE E₁ E₂) X = lift (actM E₁ X) (actM E₂ X) := by
  have h : ∀ a b, X a b • sE E₁ E₂ a b = liftL (X a b • (E₁ a b, E₂ a b)) := by
    intro a b; rw [map_smul]; rfl
  unfold actM
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, ← map_sum]
  rw [liftL_apply]
  congr 1
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

theorem casimir_sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂) :
    casimir (sE E₁ E₂) = lift (casimir E₁) (casimir E₂) := by
  have h : ∀ a b, sE E₁ E₂ a b * sE E₁ E₂ b a = liftL (E₁ a b * E₁ b a, E₂ a b * E₂ b a) := by
    intro a b; rw [liftL_apply]; exact (lift_mul _ _ _ _).symm
  unfold casimir
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, ← map_sum]
  rw [liftL_apply]
  congr 1
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

section Rep

variable {ε : Fin n → Bool}
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

def sσ (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)) (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)) :
    Matrix (Fin n) (Fin n) ℂ → (WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂)) :=
  fun g => sop (σ₁ g) (σ₂ g)

theorem isURepOn_sσ {G : Set (Matrix (Fin n) (Fin n) ℂ)} (h₁ : IsURepOn G σ₁) (h₂ : IsURepOn G σ₂) :
    IsURepOn G (sσ σ₁ σ₂) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show sop (σ₁ 1) (σ₂ 1) = 1
    rw [h₁.1.1, h₂.1.1]; exact sop_one
  · intro a ha b hb
    show sop (σ₁ (a * b)) (σ₂ (a * b)) = (sop (σ₁ a) (σ₂ a)).comp (sop (σ₁ b) (σ₂ b))
    rw [h₁.1.2 a ha b hb, h₂.1.2 a ha b hb, sop_comp]
  · intro g hg v
    exact norm_sop (h₁.2.1 g hg) (h₂.2.1 g hg) v
  · intro v
    have hc := ((h₁.2.2 (ofLp v).1).prodMk (h₂.2.2 (ofLp v).2))
    exact (WithLp.prod_continuous_toLp 2 H₁ H₂).comp_continuousOn hc

theorem isDerivedOn_sσ {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
    {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
    (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) :
    IsDerivedOn ε (sσ σ₁ σ₂) (sD D₁ D₂) (sE E₁ E₂) where
  glRep := by
    intro a b c d
    have e1 := hD₁.glRep a b c d
    have e2 := hD₂.glRep a b c d
    show lift (E₁ a b) (E₂ a b) * lift (E₁ c d) (E₂ c d) - lift (E₁ c d) (E₂ c d) * lift (E₁ a b) (E₂ a b) =
      (if b = c then lift (E₁ a d) (E₂ a d) else 0) - (if d = a then lift (E₁ c b) (E₂ c b) else 0)
    rw [← lift_mul, ← lift_mul, ← lift_sub, e1, e2]
    split_ifs <;> rw [lift_sub] <;> simp only [lift_zero]
  kStable := by
    intro k hk v hv
    exact ⟨hD₁.kStable k hk _ hv.1, hD₂.kStable k hk _ hv.2⟩
  deriv := by
    intro X hX v
    have h1 := hD₁.deriv X hX (toP v).1
    have h2 := hD₂.deriv X hX (toP v).2
    have h3 := (WithLp.prodContinuousLinearEquiv 2 ℝ H₁ H₂).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (h1.prodMk h2)
    rw [actM_sE]
    exact h3

end Rep

end Ops

end USum

end ReciprocityTheory.ChartRestriction.DS
end
end

