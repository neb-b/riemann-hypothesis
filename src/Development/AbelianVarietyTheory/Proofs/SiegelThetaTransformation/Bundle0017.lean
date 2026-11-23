module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TracePairingGeDetImPowHermitianHalfSpace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DerivDerivConstMulCexpBilinearAtZero
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HeatTerm

noncomputable section

theorem diffAt_det {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {N : ℕ}
    (A : X → Matrix (Fin N) (Fin N) ℂ) (x : X)
    (h : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x) :
    DifferentiableAt ℂ (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_mul ?_ _
  exact (HasFDerivAt.finsetProd (fun i _ => (h (σ i) i).hasFDerivAt)).differentiableAt

theorem diffAt_inv {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {N : ℕ}
    (A : X → Matrix (Fin N) (Fin N) ℂ) (x : X)
    (h : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x) (h0 : (A x).det ≠ 0) (i j : Fin N) :
    DifferentiableAt ℂ (fun y => (A y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((diffAt_det A x h).fun_inv h0).fun_mul (diffAt_det _ x fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact h a b

def loc {n N : ℕ} (C D Z : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ) : ℂ :=
  ((C * Z + D).det ^ n * cexp (2 * Real.pi * I * ∑ k, z' k ⬝ᵥ ((C * Z + D)⁻¹ * C) *ᵥ z k))⁻¹

theorem det_one_add {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (s : ℂ) :
    (1 + S * Matrix.single a b s).det = 1 + s * S b a := by
  have : S * Matrix.single a b s =
      replicateCol Unit (fun i => S i a * s) * replicateRow Unit (Pi.single b (1 : ℂ)) := by
    ext i j
    by_cases hj : j = b
    · subst hj; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, Matrix.single_apply, hj, Ne.symm hj]
  rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [mul_comm]

theorem inv_one_add {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (s : ℂ)
    (h : 1 + s * S b a ≠ 0) :
    (1 + S * Matrix.single a b s)⁻¹ = 1 - (s / (1 + s * S b a)) • (S * Matrix.single a b 1) := by
  apply Matrix.inv_eq_right_inv
  have h1 : Matrix.single a b s = s • Matrix.single a b (1 : ℂ) := by simp
  have h2 : S * Matrix.single a b (1 : ℂ) * (S * Matrix.single a b 1) =
      S b a • (S * Matrix.single a b 1) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single a b 1),
      Matrix.single_mul_mul_single, ← Matrix.mul_smul]
    simp
  rw [h1, Matrix.mul_smul]
  generalize S * Matrix.single a b (1 : ℂ) = P at h2
  rw [add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h2]
  have : s / (1 + s * S b a) + s * (s / (1 + s * S b a) * S b a) = s := by field_simp
  rw [smul_smul, smul_smul, sub_add_sub_comm, ← add_smul, mul_assoc, this]
  simp

theorem quad_single {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (u v : Fin N → ℂ) :
    u ⬝ᵥ (S * Matrix.single a b 1 * S) *ᵥ v = (u ᵥ* S) a * (S *ᵥ v) b := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.single_mulVec]
  simp [dotProduct, Function.update_apply]

theorem loc_Z {n N : ℕ} (C D Z : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (h : (C * Z + D).det ≠ 0) (a b : Fin N) :
    HasDerivAt (fun s : ℂ => loc C D (Z + Matrix.single a b s) z z')
      ((-(n : ℂ) * ((C * Z + D)⁻¹ * C) b a + 2 * Real.pi * I *
        ∑ k, (z' k ᵥ* ((C * Z + D)⁻¹ * C)) a * (((C * Z + D)⁻¹ * C) *ᵥ z k) b) *
        loc C D Z z z') 0 := by
  set M := C * Z + D with hM
  set S := M⁻¹ * C with hS
  have hu : IsUnit M.det := Ne.isUnit h
  have hfac : ∀ s, C * (Z + Matrix.single a b s) + D = M * (1 + S * Matrix.single a b s) := by
    intro s
    rw [Matrix.mul_add M, mul_one, hS, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, one_mul, hM, Matrix.mul_add]
    abel
  set q := ∑ k, z' k ⬝ᵥ S *ᵥ z k with hq
  set r := ∑ k, (z' k ᵥ* S) a * (S *ᵥ z k) b with hr
  set c := S b a with hc
  have hl : HasDerivAt (fun s : ℂ => 1 + s * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const c).const_add 1
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), 1 + s * c ≠ 0 :=
    hl.continuousAt.eventually_ne (by simp)
  have heq : (fun s : ℂ => loc C D (Z + Matrix.single a b s) z z') =ᶠ[𝓝 0]
      fun s => ((M.det * (1 + s * c)) ^ n *
        cexp (2 * Real.pi * I * (q - s / (1 + s * c) * r)))⁻¹ := by
    filter_upwards [hev] with s hs
    rw [loc, hfac, Matrix.det_mul, det_one_add, Matrix.mul_inv_rev, inv_one_add _ _ _ _ hs,
      Matrix.mul_assoc, ← hS, sub_mul, one_mul, Matrix.smul_mul]
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      quad_single, Finset.sum_sub_distrib, smul_eq_mul, ← Finset.mul_sum]
    rfl
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h1 := (hl.const_mul M.det).fun_pow n
  have h2 := (((((hasDerivAt_id (0 : ℂ)).fun_div hl (by simp)).mul_const r).const_sub q).const_mul
    (2 * Real.pi * I)).cexp
  have h3 := (h1.fun_mul h2).fun_inv (by simp [h])
  refine HasDerivAt.congr_deriv h3 ?_
  have he := Complex.exp_ne_zero (2 * Real.pi * I * q)
  rw [loc, ← hM, ← hS, ← hq]
  simp only [id, zero_mul, add_zero, mul_one, zero_div, sub_zero, one_mul, one_pow, div_one]
  rcases n with _ | n
  · simp
    field_simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

theorem quad_add {n N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (k : Fin n) (a b : Fin N) (s t : ℂ) :
    ∑ j, (z' + Matrix.single k b t) j ⬝ᵥ S *ᵥ (z + Matrix.single k a s) j =
      ∑ j, z' j ⬝ᵥ S *ᵥ z j + s * (z' k ᵥ* S) a + t * ((S *ᵥ z k) b + s * S b a) := by
  have h : ∀ (j : Fin n) (a : Fin N) (s : ℂ) (w : Matrix (Fin n) (Fin N) ℂ),
      (w + Matrix.single k a s) j = w j + if j = k then Pi.single a s else 0 := by
    intro j a s w
    ext i
    by_cases hj : j = k
    · subst hj; simp [Matrix.single_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.single_apply, hj, Ne.symm hj]
  have h2 : ∀ j, (z' + Matrix.single k b t) j ⬝ᵥ S *ᵥ (z + Matrix.single k a s) j =
      z' j ⬝ᵥ S *ᵥ z j +
        if j = k then s * (z' k ᵥ* S) a + t * ((S *ᵥ z k) b + s * S b a) else 0 := by
    intro j
    rw [h, h]
    by_cases hj : j = k
    · subst hj
      simp only [if_true, Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct]
      rw [Matrix.dotProduct_mulVec _ _ (Pi.single a s), dotProduct_single]
      simp [Matrix.mulVec_single]
      ring
    · simp [hj]
  simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem deriv_deriv_const_mul_cexp_bilinear_at_zero (K w q u v c : ℂ) :
    deriv (fun s : ℂ => deriv (fun t : ℂ =>
      K * cexp (w * (q + s * u + t * (v + s * c)))) 0) 0 =
      (w * c + w * w * (u * v)) * (K * cexp (w * q)) := by
  have h1 : ∀ s : ℂ, deriv (fun t : ℂ => K * cexp (w * (q + s * u + t * (v + s * c)))) 0 =
      K * (cexp (w * (q + s * u)) * (w * (v + s * c))) := by
    intro s
    have := ((((((hasDerivAt_id (0 : ℂ)).mul_const (v + s * c)).const_add (q + s * u)).const_mul
      w).cexp).const_mul K).deriv
    simpa using this
  simp only [h1]
  have h2 := (((((hasDerivAt_id (0 : ℂ)).mul_const u).const_add q).const_mul w).cexp)
  have h3 := (((hasDerivAt_id (0 : ℂ)).mul_const c).const_add v).const_mul w
  have := ((h2.fun_mul h3).const_mul K).deriv
  simp only [id] at this
  rw [this]
  simp
  ring

theorem loc_heat {n N : ℕ} (C D Z : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (h : (C * Z + D).det ≠ 0) (a b : Fin N) (K : ℂ) :
    2 * Real.pi * I * deriv (fun s : ℂ => K * loc C D (Z + Matrix.single a b s) z z') 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ =>
        K * loc C D Z (z + Matrix.single k a s) (z' + Matrix.single k b t)) 0) 0 := by
  rw [((loc_Z C D Z z z' h a b).const_mul K).deriv]
  have h1 : ∀ (w w' : Matrix (Fin n) (Fin N) ℂ), K * loc C D Z w w' =
      (K * ((C * Z + D).det ^ n)⁻¹) *
        cexp (-(2 * Real.pi * I) * ∑ k, w' k ⬝ᵥ ((C * Z + D)⁻¹ * C) *ᵥ w k) := by
    intro w w'
    rw [loc, mul_inv, ← Complex.exp_neg, neg_mul, ← mul_assoc K]
  simp only [h1, quad_add, deriv_deriv_const_mul_cexp_bilinear_at_zero]
  rw [← h1, ← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  generalize (∑ k, (z' k ᵥ* ((C * Z + D)⁻¹ * C)) a * (((C * Z + D)⁻¹ * C) *ᵥ z k) b) = r
  simp
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

omit [NumberField E] [IsCMField E] in
theorem hFac_inv (γ : M2 E N) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    (hFac Ψ γ Z z z')⁻¹ = ∏ τ : Ψ,
      loc (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) (Z τ) (z τ) (z' τ) := by
  rw [hFac, ← Finset.prod_inv_distrib]
  rfl

open Classical in
omit [NumberField E] [IsCMField E] in
theorem hFac_inv_at (γ : M2 E N) (Z : CM Ψ N N) (z z' : CM Ψ n N) (τ : Ψ)
    (W : Matrix (Fin N) (Fin N) ℂ) (w w' : Matrix (Fin n) (Fin N) ℂ) :
    (hFac Ψ γ (fun σ => Z σ + if σ = τ then W else 0) (fun σ => z σ + if σ = τ then w else 0)
      (fun σ => z' σ + if σ = τ then w' else 0))⁻¹ =
    (∏ σ ∈ Finset.univ.erase τ,
      loc (γ.toBlocks₂₁.map σ.1) (γ.toBlocks₂₂.map σ.1) (Z σ) (z σ) (z' σ)) *
      loc (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) (Z τ + W) (z τ + w) (z' τ + w') := by
  rw [hFac_inv, ← Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
  congr 1
  · refine Finset.prod_congr rfl fun σ hσ => ?_
    simp [(Finset.mem_erase.1 hσ).1]
  · simp

omit [NumberField E] [IsCMField E] in
theorem isHeat_of_det (γ : M2 E N) (h : ∀ Z ∈ Hn Ψ N, ∀ τ, (hDen Ψ γ Z τ).det ≠ 0) :
    IsHeat Ψ (fun Z (z z' : CM Ψ n N) => (hFac Ψ γ Z z z')⁻¹) := by
  classical
  refine ⟨fun p hp => DifferentiableAt.differentiableWithinAt ?_, fun Z hZ z z' τ a b => ?_⟩
  · suffices hs : ∀ τ : Ψ, DifferentiableAt ℂ (fun y : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
        loc (n := n) (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) (y.1 τ) (y.2.1 τ) (y.2.2 τ)) p by
      refine ((HasFDerivAt.finsetProd (u := Finset.univ)
        (fun τ _ => (hs τ).hasFDerivAt)).differentiableAt).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun y => hFac_inv Ψ γ _ _ _
    intro τ
    have hd := h _ hp τ
    have hM : ∀ i j, DifferentiableAt ℂ (fun y : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
        hDen Ψ γ y.1 τ i j) p := by
      intro i j
      show DifferentiableAt ℂ (fun y : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
        ∑ l, γ.toBlocks₂₁.map τ.1 i l * y.1 τ l j + γ.toBlocks₂₂.map τ.1 i j) p
      fun_prop
    have h1 := diffAt_det _ p hM
    have h2 := diffAt_inv _ p hM hd
    refine DifferentiableAt.fun_inv ((h1.fun_pow n).fun_mul (DifferentiableAt.cexp ?_))
      (mul_ne_zero (pow_ne_zero _ hd) (Complex.exp_ne_zero _))
    refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun k _ => ?_) _
    simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply]
    refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_mul (by fun_prop) ?_
    refine DifferentiableAt.fun_sum fun j _ => DifferentiableAt.fun_mul ?_ (by fun_prop)
    exact DifferentiableAt.fun_sum fun l _ => (h2 i l).mul_const _
  · have e1 := fun s : ℂ => hFac_inv_at Ψ γ Z z z' τ (Matrix.single a b s) 0 0
    have e2 := fun (k : Fin n) (s t : ℂ) =>
      hFac_inv_at Ψ γ Z z z' τ 0 (Matrix.single k a s) (Matrix.single k b t)
    simp only [ite_self, add_zero] at e1 e2
    simp only [e1, e2]
    exact loc_heat _ _ _ _ _ (h Z hZ τ) a b _

end

end GlobalTheory.SW.HeatTerm

theorem GlobalTheory.SW.isHeat_hFac_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ), ∀ γ ∈ UU E N, IsHeat Ψ (fun Z (z z' : CM Ψ n N) => (hFac Ψ γ Z z z')⁻¹) :=
  fun E _ _ _ Ψ _ N γ hγ => GlobalTheory.SW.HeatTerm.isHeat_of_det Ψ γ
    fun Z hZ τ => (((GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalMatrixMoveAdmissibleUniformLevel
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TwistMove

open GlobalTheory.SW.TwistAdm

variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

def imL (b : Matrix (Fin N) (Fin N) E) : AddSubgroup (Fin N → E) :=
  (stdL E N).toAddSubgroup.map (Matrix.toLin' b).toAddMonoidHom

theorem mem_imL {b : Matrix (Fin N) (Fin N) E} {x : Fin N → E} :
    x ∈ imL b ↔ ∃ v ∈ stdL E N, b *ᵥ v = x := by
  simp [imL]

theorem std_eq_closure : (stdL E N).toAddSubgroup =
    AddSubgroup.closure (Set.range (Pi.basis fun _ : Fin N => integralBasis E)) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  ext x
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, Base.mem_stdL,
    Module.Basis.mem_span_iff_repr_mem, Sigma.forall]
  refine forall_congr' fun a => ?_
  simp only [Pi.basis_repr]
  rw [← Module.Basis.mem_span_iff_repr_mem, mem_span_integralBasis]
  exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe⟩

theorem relIndex_imL {b₁ b₂ : Matrix (Fin N) (Fin N) E} (h₁ : b₁.det ≠ 0) (h₂ : b₂.det ≠ 0)
    (hle : imL b₁ ≤ imL b₂) :
    ((imL b₁).relIndex (imL b₂) : ℚ) * |Algebra.norm ℚ b₂.det| = |Algebra.norm ℚ b₁.det| := by
  let B := Pi.basis fun _ : Fin N => integralBasis E
  have key : ∀ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 → ∃ B' : Module.Basis _ ℚ (Fin N → E),
      imL b = AddSubgroup.closure (Set.range B') ∧ B.det B' = Algebra.norm ℚ b.det := by
    intro b hb
    have hd : LinearMap.det (Matrix.toLin' b) ≠ 0 := by rwa [LinearMap.det_toLin']
    refine ⟨B.map (((Matrix.toLin' b).equivOfDetNeZero hd).restrictScalars ℚ), ?_, ?_⟩
    · rw [imL, std_eq_closure, AddMonoidHom.map_closure, ← Set.range_comp]
      rfl
    · rw [← LinearMap.det_toLin', ← LinearMap.det_restrictScalars]
      have := B.det_comp ((Matrix.toLin' b).restrictScalars ℚ) B
      rw [B.det_self, mul_one] at this
      exact this
  obtain ⟨B₁, e₁, d₁⟩ := key b₁ h₁
  obtain ⟨B₂, e₂, d₂⟩ := key b₂ h₂
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hle B₁ B₂ e₁ e₂, ← d₁, ← d₂, ← abs_mul, mul_comm,
    Module.Basis.det_mul_det]

theorem gidx_mul_le {𝔛 : Lt E N} {t : ℕ} (ht : 0 < t) (h : ∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛)
    {b : Matrix (Fin N) (Fin N) E} (hb : b.det ≠ 0) (hX : 𝔛.toAddSubgroup ≤ imL b) :
    gidx 𝔛 * |(Algebra.norm ℚ b.det : ℝ)| ≤ 1 := by
  have hs : ((t : E) • (1 : Matrix (Fin N) (Fin N) E)).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 ht.ne')
  set s := (t : E) • (1 : Matrix (Fin N) (Fin N) E) with hsd
  have h1 : imL (1 : Matrix (Fin N) (Fin N) E) = (stdL E N).toAddSubgroup := by
    ext x; simp [mem_imL]
  have hKX : imL s ≤ 𝔛.toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using h v hv
  have hKL : imL s ≤ (stdL E N).toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using nat_smul_mem _ t hv
  have e1 := relIndex_imL hs hb (hKX.trans hX)
  have e2 := relIndex_imL hs (b₂ := 1) (by simp) (h1 ▸ hKL)
  rw [h1, Matrix.det_one, map_one, abs_one, mul_one] at e2
  have hn : 0 < |Algebra.norm ℚ s.det| := abs_pos.2 (Algebra.norm_ne_zero_iff.2 hs)
  have n1 : (imL s).relIndex (imL b) ≠ 0 := fun h0 => by
    rw [h0] at e1; simp at e1; exact hn.ne' (by simpa using e1.symm)
  have l1 := AddSubgroup.relIndex_le_of_le_right (H := imL s) hX n1
  have m1 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_right : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  have m2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_left : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  rw [AddSubgroup.inf_relIndex_right] at m1
  rw [AddSubgroup.inf_relIndex_left] at m2
  rw [← m1] at l1
  rw [← m2] at e2
  unfold gidx
  generalize (imL s).relIndex ((stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup) = k at *
  generalize (stdL E N).toAddSubgroup.relIndex 𝔛.toAddSubgroup = p at *
  generalize 𝔛.toAddSubgroup.relIndex (stdL E N).toAddSubgroup = q at *
  have hkq : (0 : ℚ) < (k * q : ℕ) := e2 ▸ hn
  have hk : 0 < k := Nat.pos_of_mul_pos_right (by exact_mod_cast hkq)
  have hq : 0 < q := Nat.pos_of_mul_pos_left (by exact_mod_cast hkq)
  have l2 : ((k * p : ℕ) : ℚ) * |Algebra.norm ℚ b.det| ≤ (k * q : ℕ) := by
    rw [e2, ← e1]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast l1) (abs_nonneg _)
  have l3 : (p : ℚ) * |Algebra.norm ℚ b.det| ≤ q := by
    push_cast at l2
    rw [mul_assoc] at l2
    exact le_of_mul_le_mul_left l2 (by exact_mod_cast hk)
  rw [div_mul_eq_mul_div, div_le_one (by exact_mod_cast hq)]
  exact_mod_cast l3

theorem exists_frame (E : Type) [Field E] [NumberField E] (N : ℕ) : ∃ c : ℕ, 0 < c ∧
    ∀ (𝔛 : Lt E N) (t : ℕ), 0 < t → (∀ v ∈ 𝔛, (t : E) • v ∈ stdL E N) →
      (∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛) → ∃ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 ∧
        (∀ v ∈ stdL E N, b *ᵥ v ∈ 𝔛) ∧ ∀ u, b *ᵥ u ∈ 𝔛 → (c : E) • u ∈ stdL E N := by
  obtain ⟨C, hC⟩ := NearPrim.exists_reduce E
  obtain ⟨M, hM⟩ := NearPrim.exists_approx E
  refine ⟨M.factorial ^ N, pow_pos M.factorial_pos _, fun 𝔛 t ht h1 h2 => ?_⟩
  have ht0 : (t : E) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  let L : AddSubgroup (Fin N → E) :=
    { carrier := {s | (t : E) • s ∈ 𝔛}
      add_mem' := fun {s t} hs ht => by
        rw [Set.mem_setOf_eq, smul_add]; exact add_mem hs ht
      zero_mem' := by simp
      neg_mem' := fun {s} hs => by rw [Set.mem_setOf_eq, smul_neg]; exact neg_mem hs }
  have hO : ∀ s : Fin N → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L := fun s hs =>
    h2 s ((Base.mem_stdL s).2 hs)
  have hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L := fun y hy s hs => by
    change (t : E) • y • s ∈ 𝔛
    rw [smul_comm]
    exact 𝔛.smul_mem (⟨y, hy⟩ : 𝓞 E) hs
  have hden : ∀ s ∈ L, ∀ i, IsIntegral ℤ (((t * t : ℤ) : E) * s i) := fun s hs i => by
    have := (Base.mem_stdL _).1 (h1 _ hs) i
    simpa [mul_assoc] using this
  choose a haL ha0 hai haC hmin using NearPrim.exists_rows L hO (t * t)
    (by positivity) hden C hC
  refine ⟨(t : E) • (Matrix.of a)ᵀ, ?_, fun v hv => ?_, fun u hu => ?_⟩
  · rw [Matrix.det_smul, Matrix.det_transpose,
      Matrix.det_of_lowerTriangular (Matrix.of a) (fun i j h => ha0 i j h)]
    exact mul_ne_zero (pow_ne_zero _ ht0) (Finset.prod_ne_zero_iff.2 fun i _ => hai i)
  · exact colsIn_mulVec (fun j => haL j) hv
  · rw [Matrix.smul_mulVec, Matrix.mulVec_transpose] at hu
    exact (Base.mem_stdL _).2 (NearPrim.integral_coord L hsm M hM (Matrix.of a) haL ha0 hai hmin N
      le_rfl u (fun j hj => absurd j.2 (not_lt.2 hj)) hu)

variable [IsCMField E]

theorem admissibleLatticeFamily_moved_by_rational_matrix {M R : ℕ} {φ : Fam E n N} {𝔛 : Lt E N} (hφ : admitted M R φ)
    (hA : Agree (R * M) 𝔛 (stdL E N)) (a : Matrix (Fin N) (Fin N) E) {c : ℕ} (hc0 : 0 < c)
    (h1 : ∀ v ∈ stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v)
    (h2 : ∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ stdL E N) :
    admitted M (R * c) (fun Λ (x : Matrix (Fin n) (Fin N) E) => twist R 𝔛 φ Λ
      (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) x a)) := by
  have hex := exists_mult hφ.pos.2 hA
  refine ⟨⟨hφ.pos.1, Nat.mul_pos hφ.pos.2 hc0⟩, ?_,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).1,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).2, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' hm x
    obtain ⟨R', hR'⟩ := twist_adm hφ hA
    have := hR'.equiv h hh Λ hΛ Λ' hΛ' hm (x * a)
    rwa [← Matrix.mul_assoc] at this
  · intro Λ hΛ Λ' hΛ' ⟨u, hu, hc, h3, h4⟩ x hx hx'
    have hct : u.Coprime (c * c) := by
      have : u.Coprime c := hc.coprime_dvd_right ⟨R * M, by ring⟩
      exact this.mul_right this
    have key : ∀ A B : Lt E n, (∀ v ∈ A, (u : E) • v ∈ B) → ColsIn B (((R * c : ℕ) : E) • x) →
        (∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ A) → ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ B := by
      intro A B hAB hB h ξ hξ
      refine mem_of_coprime B hct (hAB _ (h ξ hξ)) ?_
      have := colsIn_mulVec hB (h2 ξ hξ)
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec] at this
      rw [smul_smul]
      convert this using 2
      push_cast; ring
    simp only [twist_eq φ hex]
    by_cases h : ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ
    · have h' := key Λ Λ' h3 hx' h
      rw [if_pos h, if_pos h']
      exact hφ.loc Λ hΛ Λ' hΛ' ⟨u, hu, hc.coprime_dvd_right ⟨c, by ring⟩, h3, h4⟩ _
        (cols_of_cond hex.choose_spec.2 h) (cols_of_cond hex.choose_spec.2 h')
    · rw [if_neg h, if_neg (fun h' => h (key Λ' Λ h4 hx h'))]

end GlobalTheory.SW.TwistMove


open GlobalTheory.SW.TwistMove in
theorem GlobalTheory.SW.twist_move_adm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (n M R : ℕ) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∃ a : Matrix (Fin N) (Fin N) E, a.det ≠ 0 ∧ gidx 𝔛 ≤ C * |(Algebra.norm ℚ a.det : ℝ)| ∧ admitted M (R * c) (fun Λ x => twist R 𝔛 φ Λ (x * a)) := by
  intro E _ _ _ N
  obtain ⟨c, hc, H⟩ := exists_frame E N
  have hc0 : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  refine ⟨c, |(Algebra.norm ℚ ((c : E) ^ N) : ℝ)|, hc, fun n M R φ 𝔛 hφ _ hA => ?_⟩
  obtain ⟨t, ht, -, h1, h2⟩ := id hA
  obtain ⟨b, hb, hb1, hb2⟩ := H 𝔛 t ht h1 h2
  have hu : IsUnit b.det := hb.isUnit
  have ha : b⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det b hu).ne_zero
  have k2 : ∀ ξ ∈ 𝔛, (c : E) • (b⁻¹ *ᵥ ξ) ∈ stdL E N := fun ξ hξ => hb2 _ (by
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec])
  refine ⟨b⁻¹, ha, ?_, admissibleLatticeFamily_moved_by_rational_matrix hφ hA b⁻¹ hc (fun v hv => ⟨b *ᵥ ((c : E) • v),
    hb1 _ (TwistAdm.nat_smul_mem _ c hv), by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]⟩) k2⟩
  have hd : ((c : E)⁻¹ • b).det * ((c : E) ^ N * b⁻¹.det) = 1 := by
    rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin, inv_pow]
    field_simp
  have hle := gidx_mul_le ht h2 (left_ne_zero_of_mul_eq_one hd) (fun ξ hξ => mem_imL.2
    ⟨_, k2 ξ hξ, by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]⟩)
  have hn := congrArg (fun z : E => |((Algebra.norm ℚ z : ℚ) : ℝ)|) hd
  simp only [map_mul, Rat.cast_mul, abs_mul, map_one, Rat.cast_one, abs_one] at hn
  have := mul_le_mul_of_nonneg_right hle (mul_nonneg
    (abs_nonneg (Algebra.norm ℚ ((c : E) ^ N) : ℝ)) (abs_nonneg (Algebra.norm ℚ b⁻¹.det : ℝ)))
  rwa [mul_assoc, hn, mul_one, one_mul] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TracePairingGeDetImPowHermitianHalfSpaceStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_ge_detIm_pow_hermitianHalfSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N c : ℕ, 0 < N → 0 < c → ∃ k : ℝ, 0 < k ∧ ∀ T : Matrix (Fin N) (Fin N) E, ccT T = T → Den c T → (∀ τ : Ψ, (T.map τ.1).PosDef) → ∀ Z ∈ Hn Ψ N, k * detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) ≤ ∑ τ : Ψ, (T.map τ.1 * imH (Z τ)).trace.re := by
  first | exact @GlobalTheory.SW.TracePair.trace_ge | exact GlobalTheory.SW.TracePair.trace_ge | (intros; apply GlobalTheory.SW.TracePair.trace_ge <;> assumption)
end

