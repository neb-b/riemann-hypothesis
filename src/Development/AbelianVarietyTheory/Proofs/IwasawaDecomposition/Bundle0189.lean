module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
section
open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.DualWeyl GlobalTheory.CompactDS
open Formalism.GradedWeylDivisibility (rowAct rowDeg)
open scoped Matrix

noncomputable section

namespace GlobalTheory.NablaType

variable {n : ℕ}

theorem cdom_of_partial_sums (μ ν : Fin n → ℕ)
    (h : ∀ k : ℕ, (∑ a : Fin n with a.val < k, μ a) ≤ ∑ a : Fin n with a.val < k, ν a)
    (he : ∑ a, μ a = ∑ a, ν a) : CDom (allPos n) (fun a => (μ a : ℝ)) (fun a => (ν a : ℝ)) := by
  classical
  let D : ℕ → ℕ := fun k => (∑ a : Fin n with a.val < k, ν a) - ∑ a : Fin n with a.val < k, μ a
  have hD : ∀ k, (D k : ℝ) = ∑ a : Fin n, if a.val < k then ((ν a : ℝ) - μ a) else 0 := by
    intro k
    simp only [D]
    rw [Nat.cast_sub (h k), ← Finset.sum_filter, Finset.sum_sub_distrib]
    push_cast
    rfl
  have hstep : ∀ i : Fin n, (D (i.val + 1) : ℝ) - D i.val = (ν i : ℝ) - μ i := by
    intro i
    rw [hD, hD, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : b.val ≠ i.val := fun e => hb (Fin.ext e)
      by_cases h1 : b.val < i.val
      · rw [if_pos h1, if_pos (by omega), sub_self]
      · rw [if_neg h1, if_neg (by omega), sub_self]
    · simp
  have h0 : D 0 = 0 := by simp [D]
  have hn : D n = 0 := by simp [D, he]
  refine ⟨fun a b => if b.val = a.val + 1 then D b.val else 0, fun a b hab => ?_, ?_⟩
  · have : b.val = a.val + 1 := by by_contra h'; exact hab (if_neg h')
    exact ⟨Fin.lt_def.2 (by omega), rfl⟩
  · funext i
    have e1 : ∑ b : Fin n, ((if b.val = i.val + 1 then D b.val else 0 : ℕ) : ℝ) = D (i.val + 1) := by
      by_cases hi : i.val + 1 < n
      · rw [Finset.sum_eq_single ⟨i.val + 1, hi⟩]
        · simp
        · intro b _ hb
          rw [if_neg (fun e => hb (Fin.ext e)), Nat.cast_zero]
        · simp
      · rw [Finset.sum_eq_zero, show i.val + 1 = n by omega, hn, Nat.cast_zero]
        intro b _
        rw [if_neg (by omega), Nat.cast_zero]
    have e2 : ∑ a : Fin n, ((if i.val = a.val + 1 then D i.val else 0 : ℕ) : ℝ) = D i.val := by
      by_cases hi : 0 < i.val
      · rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
        · rw [if_pos (by simp only; omega)]
        · intro b _ hb
          rw [if_neg (fun e => hb (Fin.ext (by simp only; omega))), Nat.cast_zero]
        · simp
      · rw [Finset.sum_eq_zero, show i.val = 0 by omega, h0, Nat.cast_zero]
        intro b _
        rw [if_neg (by omega), Nat.cast_zero]
    rw [Pi.sub_apply, ← hstep, ← e1, ← e2]
    simp only [Finset.sum_apply, Pi.smul_apply, Formalism.REAL.root, Pi.sub_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero]
    congr 1
    · rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem cdom_of_coeff_ne_zero {la : Fin n → ℕ} {f : Pol n ℂ} (hf : f ∈ nabla la ℂ) (m : Fin n × Fin n →₀ ℕ)
    (hm : AddMonoidAlgebra.coeff f m ≠ 0) : CDom (allPos n) (fun a => (rowDeg m a : ℝ)) (fun a => (la a : ℝ)) := by
  unfold nabla at hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ n n la] at hf
  by_contra hc
  apply hm
  clear hm
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, rfl, rfl⟩ := hx
    by_contra h0
    obtain ⟨h1, h2⟩ := Formalism.GradedWeylDivisibility.bidetDominance ℂ n n K sz hsz I m (mem_support_iff.2 h0)
    exact hc (cdom_of_partial_sums _ _ h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [MvPolynomial.coeff_add, hx, hy, add_zero]
  | smul c x _ hx => rw [coeff_smul, hx, smul_zero]

def act (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) : Space lam.natW →L[ℂ] Space lam.natW :=
  LinearMap.toContinuousLinearMap
    ((g.det ^ lam.detShift) • ((toSpace lam.natW).conj (rho lam.natW ℂ g)))

def incl (lam : DomWeight n) : Space lam.natW →ₗ[ℂ] Pol n ℂ :=
  (nabla lam.natW ℂ).subtype ∘ₗ (toSpace lam.natW).symm.toLinearMap

theorem incl_injective (lam : DomWeight n) : Function.Injective (incl lam) :=
  (nabla lam.natW ℂ).injective_subtype.comp (toSpace lam.natW).symm.injective

theorem incl_mem (lam : DomWeight n) (x : Space lam.natW) : incl lam x ∈ nabla lam.natW ℂ :=
  ((toSpace lam.natW).symm x).2

theorem incl_act (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) (x : Space lam.natW) :
    incl lam (act lam g x) = (g.det ^ lam.detShift) • rowAct ℂ gᵀ (incl lam x) := rfl

theorem act_unitary (lam : DomWeight n) (u : UN n) (x : Space lam.natW) :
    act lam u.1 x = (u.1.det ^ lam.detShift) • rhoSpace lam.natW u x := rfl

theorem det_ne_zero {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ) : g.det ≠ 0 :=
  (Matrix.UnitaryGroup.det_isUnit ⟨g, hg⟩).ne_zero

theorem isURepOn_act (lam : DomWeight n) : IsURepOn (UJset (allPos n)) (act lam) := by
  rw [ujset_eq]
  refine ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · ext x
    apply incl_injective
    rw [incl_act, Matrix.transpose_one, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
    simp
  · ext x
    apply incl_injective
    rw [ContinuousLinearMap.comp_apply, incl_act, incl_act, incl_act, Matrix.transpose_mul,
      ← Formalism.GradedWeylDivisibility.rowActMul ℂ n n, Matrix.det_mul, mul_zpow, map_smul, smul_smul]
    rfl
  · have h1 : ‖g.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hg)
    rw [act_unitary lam ⟨g, hg⟩, norm_smul, norm_zpow, h1, one_zpow, one_mul, norm_rhoSpace]
  · rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun u : UN n => u.1.det ^ lam.detShift :=
      (continuous_subtype_val.matrix_det).zpow₀ _ fun u => Or.inl (det_ne_zero u.2)
    exact h1.smul (continuous_rhoSpace v)

theorem coeff_torus (lam : DomWeight n) (θ : Fin n → ℝ) (x : Space lam.natW) (m : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (incl lam (act lam (torus θ) x)) m =
      chr (fun a => (rowDeg m a : ℝ) + lam.detShift) θ * AddMonoidAlgebra.coeff (incl lam x) m := by
  rw [incl_act, torus, Matrix.diagonal_transpose, coeff_smul, Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, Matrix.det_diagonal,
    smul_eq_mul, mul_left_comm, mul_comm]
  congr 1
  simp only [← Complex.exp_nat_mul]
  rw [chr, ← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem natW_add (lam : DomWeight n) (a : Fin n) : (lam.natW a : ℝ) + lam.detShift = lam.w a := by
  exact_mod_cast (factNatW n lam).2.1 a

theorem isKTypeOf_act (lam : DomWeight n) : IsKTypeOf (allPos n) (act lam) (fun a => (lam.w a : ℝ)) ⊤ := by
  have ha := (factNatW n lam).1
  refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => ?_, ?_, fun μ v _ hv hw => ?_⟩
  · by_cases h0 : S = ⊥
    · exact Or.inl h0
    right
    have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ S.map (incl lam), rowAct ℂ u f ∈ S.map (incl lam) := by
      rintro u hu _ ⟨f, hf, rfl⟩
      have hu' := transpose_mem_unitaryGroup hu
      have h1 : incl lam (act lam uᵀ f) ∈ S.map (incl lam) := ⟨_, hS _ (by rw [kset_eq]; exact hu') f hf, rfl⟩
      rw [incl_act, Matrix.transpose_transpose] at h1
      exact (Submodule.smul_mem_iff _ (zpow_ne_zero _ (det_ne_zero hu'))).1 h1
    have hcl := GlobalTheory.Branching.rowDivClosed_of_rowAct_stable _ (GlobalTheory.Branching.rowAct_mem_of_unitary_stable _ hU)
    have hne : S.map (incl lam) ≠ ⊥ := fun e => h0 (Submodule.map_injective_of_injective (incl_injective lam)
      (e.trans (Submodule.map_bot _).symm))
    have hle := GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl lam.natW ha _
      (by rintro _ ⟨f, -, rfl⟩; exact incl_mem lam f) hcl hne
    refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨g, hg, e⟩ := hle (incl_mem lam f)
    rwa [← incl_injective lam e]
  · refine ⟨toSpace _ ⟨_, extremal_mem ha⟩, trivial, fun h => ?_, fun θ _ => ?_⟩
    · exact extremal_ne_zero (congrArg (incl lam) h)
    · apply incl_injective
      ext m
      have h1 := coeff_torus lam θ (toSpace _ ⟨_, extremal_mem ha⟩) m
      refine h1.trans ?_
      rw [map_smul, coeff_smul, smul_eq_mul]
      by_cases hm : AddMonoidAlgebra.coeff (incl lam (toSpace _ ⟨_, extremal_mem ha⟩)) m = 0
      · rw [hm, mul_zero, mul_zero]
      have h2 := Formalism.GradedWeylDivisibility.hwRowWeight ℂ n n le_rfl lam.natW ha hm
      have h3 : (fun a => (rowDeg m a : ℝ) + lam.detShift) = fun a => (lam.w a : ℝ) := by
        funext a
        rw [← natW_add, ← Formalism.GradedWeylDivisibility.ldrow_weight_rowW, h2]
        simp [Formalism.GradedWeylDivisibility.rowNu]
      rw [h3]
      rfl
  · have h0 : incl lam v ≠ 0 := fun e => hv (incl_injective lam (e.trans (map_zero _).symm))
    obtain ⟨m, hm⟩ := ne_zero_iff.1 h0
    have h1 : μ = fun a => (rowDeg m a : ℝ) + lam.detShift := by
      refine chr_inj fun θ => ?_
      have h2 := coeff_torus lam θ v m
      have h3 : act lam (torus θ) v = chr μ θ • v := hw θ (by rw [kset_eq]; exact torus_mem θ)
      rw [h3, map_smul, coeff_smul, smul_eq_mul] at h2
      exact mul_right_cancel₀ hm h2
    have h4 := cdom_add (cdom_of_coeff_ne_zero (incl_mem lam v) m hm)
      (cdom_refl (allPos n) fun _ => (lam.detShift : ℝ))
    rw [h1]
    have h5 : (fun a => (lam.w a : ℝ)) = (fun a => (lam.natW a : ℝ)) + fun _ => (lam.detShift : ℝ) :=
      funext fun a => (natW_add lam a).symm
    rw [h5]
    exact h4

theorem exists_isHCTypeU_nablaSq : ∀ (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n), ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (e : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), Formalism.MainNotions.S.IsHCTypeU n (fun i => (lam.w i : ℝ) + ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ)) π ∧ Function.Injective e ∧ (∀ x, e x ∈ Formalism.BasicNotions.nablaSq ℂ n lam) ∧ ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ x, e (π (g : Matrix (Fin n) (Fin n) ℂ) x) = Formalism.BasicNotions.sqAct ℂ n lam g (e x) := by
  intro n lam
  have hK := isKTypeOf_act lam
  refine ⟨Space lam.natW, inferInstance, inferInstance, act lam, incl lam,
    ⟨?_, inferInstance, isURepOn_act lam, ?_⟩, incl_injective lam, incl_mem lam, fun g _ x => ?_⟩
  · obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
    exact ⟨v, 0, hv⟩
  · convert hK using 1
    funext a
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.lowK_const]
    simp [rhoVec]
  · rw [incl_act]
    simp [sqAct, detPow]

end GlobalTheory.NablaType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerIrreducibleUnitaryHighestWeight
section
open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.HighestWeightMap

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_line {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

end

theorem raising_eq_zero {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} (E : Fin k → Fin k → Module.End ℂ W) (Δ : W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z →
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) Δ) (∑ a, ∑ b, Z a b • E a b Δ) 0)
    (hd : DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) Δ)
      (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j))
    {a b : Fin k} (hab : ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) : E a b Δ = 0 := by
  obtain ⟨D, hD⟩ := hd
  let Φ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W :=
    { toFun := fun Z => ∑ a, ∑ b, Z a b • E a b Δ
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, mul_smul] }
  let Ψ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W :=
    { toFun := fun Z => D fun i j => Z i j
      map_add' := fun x y => D.map_add x y
      map_smul' := fun c x => D.map_smul c x }
  have hskew : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → Φ Z = Ψ Z := by
    intro Z hZ
    have h1 : HasDerivAt (fun t : ℝ => fun i j => NormedSpace.exp ((t : ℂ) • Z) i j) (fun i j => Z i j) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_exp_line Z i j
    have h2 := (hD.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 h1 (by simp)
    exact (hE Z hZ).unique h2
  have hall : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Φ Z = Ψ Z := by
    intro Z
    have e : Z = (1 / 2 : ℂ) • (Z - Zᴴ) + (-Complex.I / 2) • (Complex.I • (Z + Zᴴ)) := by
      have : -Complex.I / 2 * Complex.I = 1 / 2 := by
        linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      rw [smul_smul, this]
      module
    have s1 := hskew (Z - Zᴴ) (by simp)
    have s2 := hskew (Complex.I • (Z + Zᴴ)) (by simp [conjTranspose_smul, add_comm])
    rw [e, map_add (f := _), map_add (f := _), map_smul, map_smul (Ψ), s1, map_smul Φ (-Complex.I / 2), map_smul Ψ (-Complex.I / 2), s2]
  have h3 : Φ (Matrix.single a b 1) = E a b Δ := by
    show ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • E c d Δ = _
    simp [Matrix.single_apply, ite_and, ite_smul]
  have h4 : HasDerivAt (fun s : ℂ => fun i j => (1 + Matrix.single a b s : Matrix (Fin k) (Fin k) ℂ) i j)
      (fun i j => Matrix.single a b (1 : ℂ) i j) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [Matrix.add_apply, Matrix.single_apply]
    split_ifs
    · exact (hasDerivAt_id' _).const_add _
    · exact hasDerivAt_const _ _
  have h5 : HasDerivAt (fun s : ℂ => π (1 + Matrix.single a b s) Δ) (Ψ (Matrix.single a b 1)) 0 :=
    hD.comp_hasDerivAt_of_eq 0 h4 (by
      funext i j
      show _ = (1 : Matrix (Fin k) (Fin k) ℂ) i j + Matrix.single a b (0 : ℂ) i j
      simp)
  simp only [hab] at h5
  rw [← h3, hall, h5.unique (hasDerivAt_const _ _)]


open Formalism.REAL in
theorem exists_lie_map {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [NormedAddCommGroup V₂]
    [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] {n : ℕ}
    (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ)
    (v₁ : V₁) (v₂ : V₂) (hE₁ : GlRel E₁) (hE₂ : GlRel E₂)
    (hU : ∀ a b x y, ⟪E₂ a b x, y⟫_ℂ = ⟪x, E₂ b a y⟫_ℂ)
    (h₁ : ∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hw₁ : IsHW E₁ ν v₁) (hw₂ : IsHW E₂ ν v₂) (hv₁ : v₁ ≠ 0) :
    ∃ L : V₁ →ₗ[ℂ] V₂, (∀ a b x, L (E₁ a b x) = E₂ a b (L x)) ∧ L v₁ = v₂ := by
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  let K : Submodule ℂ V₂ := S.comap (LinearMap.inr ℂ V₁ V₂)
  have hK : ∀ a b, ∀ x ∈ K, E₂ a b x ∈ K := fun a b x hx => by
    have := hS a b _ hx
    simpa [hEap, K] using this
  have hK' : ∀ a b, ∀ x ∈ Kᗮ, E₂ a b x ∈ Kᗮ := fun a b x hx =>
    (Submodule.mem_orthogonal _ _).2 fun u hu => by
      rw [← hU]
      exact (Submodule.mem_orthogonal _ _).1 hx _ (hK _ _ _ hu)
  have hv₂ : v₂ ∈ Kᗮ := by
    obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal v₂
    have hyw : ∀ a, E₂ a a y = ν a • y := fun a => by
      have e := hw₂.1 a
      rw [hyz, map_add (f := _), smul_add] at e
      have e' : E₂ a a y - ν a • y = -(E₂ a a z - ν a • z) := by
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, e, add_comm]
      rw [← sub_eq_zero]
      refine Submodule.disjoint_def.1 K.orthogonal_disjoint _ (K.sub_mem (hK _ _ _ hy) (K.smul_mem _ hy)) ?_
      rw [e']
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (hK' _ _ _ hz) (Submodule.smul_mem _ _ hz))
    obtain ⟨c, hc⟩ := htop (0, y) hy fun a => by simp [hEap, hyw]
    have hc1 : (0 : V₁) = c • v₁ := congrArg Prod.fst hc
    have hc2 : y = c • v₂ := congrArg Prod.snd hc
    rw [(smul_eq_zero.1 hc1.symm).resolve_right hv₁, zero_smul] at hc2
    rw [hyz, hc2, zero_add]
    exact hz
  let T : Submodule ℂ (V₁ × V₂) := S ⊓ Kᗮ.comap (LinearMap.snd ℂ V₁ V₂)
  have hT : ∀ a b, ∀ x ∈ T, E a b x ∈ T := fun a b x hx => ⟨hS a b x hx.1, hK' a b _ hx.2⟩
  have hvT : (v₁, v₂) ∈ T := ⟨hvS, hv₂⟩
  have hb : Function.Bijective ((LinearMap.fst ℂ V₁ V₂).comp T.subtype) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨⟨x, y⟩, hx⟩ h0
      obtain rfl : x = 0 := h0
      obtain rfl : y = 0 := Submodule.disjoint_def.1 K.orthogonal_disjoint y hx.1 hx.2
      rfl
    · rcases h₁ (T.map (LinearMap.fst ℂ V₁ V₂)) (by
        rintro a b _ ⟨x, hx, rfl⟩
        exact ⟨E a b x, hT a b x hx, rfl⟩) with h | h
      · have hm : v₁ ∈ T.map (LinearMap.fst ℂ V₁ V₂) := ⟨_, hvT, rfl⟩
        rw [h] at hm
        exact absurd hm hv₁
      · intro y
        have hm : y ∈ T.map (LinearMap.fst ℂ V₁ V₂) := by rw [h]; trivial
        obtain ⟨x, hx, rfl⟩ := hm
        exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨((LinearMap.snd ℂ V₁ V₂).comp T.subtype).comp (LinearEquiv.ofBijective _ hb).symm.toLinearMap, ?_, ?_⟩
  · intro a b x
    obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ hb).surjective x
    have h : E₁ a b (LinearEquiv.ofBijective _ hb y)
        = LinearEquiv.ofBijective _ hb ⟨E a b y, hT a b y y.2⟩ := rfl
    rw [h]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  · have h : v₁ = LinearEquiv.ofBijective _ hb ⟨(v₁, v₂), hvT⟩ := rfl
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, (LinearEquiv.symm_apply_eq _).2 h]
    rfl


open Formalism.MainNotions.S in
theorem exists_intertwiner : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (Δ : E), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ Λ ⊤ → IsURepOn (UJset (allPos k)) π → (∀ w : E, DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w) (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j)) → Δ ≠ 0 → (∀ a b : Fin k, a < b → ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) → IsWtOn (Formalism.REAL.Kset (allPos k)) π Λ Δ → ∃ L : H →ₗ[ℂ] E, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = π g (L u)) ∧ ∃ v, L v = Δ := by
  intro k Λ H _ _ _ τ E _ _ _ π Δ hτ hK hπ hd _ hup hwt
  have : Nontrivial H := by
    obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
    exact nontrivial_of_ne v 0 hv
  have hτ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) τ := hτ
  have hπ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π := hπ
  obtain ⟨E₁, g₁, d₁, i₁, x₁, hx₁, w₁⟩ :=
    GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest (Λ := Λ) hτ' hK
  obtain ⟨E₂, g₂, u₂, d₂⟩ := GlobalTheory.UnitaryDerived.exists_derived_action k E π hπ'
  have w₂ : Formalism.REAL.IsHW E₂ (fun a => (Λ a : ℂ)) Δ :=
    ⟨GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E₂ d₂ Λ Δ hwt,
      fun a b hab => raising_eq_zero E₂ Δ (fun Z hZ => d₂ Z hZ Δ) (hd Δ) (hup a b hab)⟩
  obtain ⟨L, hL, hLx⟩ := exists_lie_map E₁ E₂ _ x₁ Δ g₁ g₂
    (fun a b x y => by simpa [Formalism.REAL.sgn, PI.UpqRep.allPos] using u₂ a b x y) i₁ w₁ w₂ hx₁
  refine ⟨L, fun g hg x => ?_, x₁, hLx⟩
  obtain ⟨Y, hY, hg', -⟩ := Formalism.REAL.compact_exponential_surjective k (PI.UpqRep.allPos k) g
    ((GlobalTheory.UnitaryHighestWeight.mem_K_iff g).2 hg)
  have hZ : Yᴴ = -Y := by
    have h : Yᴴ * PI.UpqRep.Jm (PI.UpqRep.allPos k) + PI.UpqRep.Jm (PI.UpqRep.allPos k) * Y = 0 := hY.1
    rw [GlobalTheory.UnitaryHighestWeight.Jm_allPos, Matrix.mul_one, Matrix.one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  have h := GlobalTheory.UnitaryHighestWeightUnique.intertwine_group
    (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E₁ a b)
    (GlobalTheory.UnitaryHighestWeight.group_zero hτ' _) (GlobalTheory.UnitaryHighestWeight.group_add hτ' hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using d₁ _ hZ w)
    (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E₂ a b)
    (GlobalTheory.UnitaryHighestWeight.group_zero hπ' _) (GlobalTheory.UnitaryHighestWeight.group_add hπ' hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using d₂ _ hZ w)
    L (fun w => by simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hL]) x 1
  simpa [hg'] using h

end GlobalTheory.HighestWeightMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerStepsOfStepsOK
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.InnerLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def InnerSteps : Prop :=
  ∀ t (k : Fin D.R.m), (k : ℕ) + 1 < D.R.m → IsStepWeil k R.ψ (Yc D k) (Yc D (k + 1)) (R.ωY t k) ∧
    IsVacVec R.ψ R.θ (R.MY k) (R.MY (k + 1)) (R.vY t k)

def InnerLaws : Prop :=
  ∀ t k, k + 1 < D.R.m → ∀ κ ∈ levS _ (R.βY k) (R.datYt t k R.triv), κ ∈ GfC (Yc D k) ∧
    R.ωY t k (κ, 1) (R.vY t k) = levChi _ (R.βY k) (R.datYt t k R.triv) κ • R.vY t k

theorem haar_fund (hν : R.models_νY) (hν' : R.models_νY') (t : T) (j : ℕ) (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · exact ⟨(hν t j h).1.1, (hν t j h).2⟩
  · have e : j = D.R.m - 1 := by omega
    subst e
    exact ⟨(hν' t).1.1, (hν' t).2⟩

theorem ioYSt_of_inner (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : InnerSteps R)
    (hL : InnerLaws R) (hν : R.models_νY) (hν' : R.models_νY') (hI : R.chain_ItY) : IoYSt R := by
  intro t k hk
  have hk0 : k < D.R.m := by omega
  obtain ⟨hW, hV⟩ := hS t ⟨k, hk0⟩ hk
  exact hP.of_index_eq ⟨k, hk0⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hk0.le) (min_eq_left hk.le)
    (Yc D k) (Yc D (k + 1)) (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY t k) (R.vY t k) hW hV
    (R.ItY k) (hI t k hk) _ _ (hL t k hk) _ _ (haar_fund R hν hν' t _ hk).1 (haar_fund R hν hν' t _ hk).2
    _ _ (R.CC t (k + 1)) le_rfl

theorem exists_ioY_of_ioYSt (h : IoYSt R) : ∃ io, ({ R with ioY := io } : RealDat D A Ks).chain_ioY := by
  classical
  have key : ∀ t k, ∃ io : R.CC t (k + 1) →ₗ[ℂ] R.CC t k, k + 1 < D.R.m →
      Lift.IsIo (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k)
        (R.CC t (k + 1)) (R.CC t k) io := by
    intro t k
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨io, hio⟩ := h t k hk
      exact ⟨io, fun _ => hio⟩
    · exact ⟨0, fun h' => absurd h' hk⟩
  choose io hio using key
  exact ⟨io, fun t k hk => hio t k (by omega)⟩

theorem exists_ioY_of_pair (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hS : InnerSteps R) (hL : InnerLaws R)
    (hM : R.IsModels) (hI : R.chain_ItY) : ∃ io, ({ R with ioY := io } : RealDat D A Ks).chain_ioY :=
  exists_ioY_of_ioYSt R (ioYSt_of_inner R hP hC hM.inf hS hL hM.νY hM.νY' hI)

end GlobalTheory.Chain.InnerLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevelStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → (pc P v c').act (glE γ) = pc P v c → mov K (A.eV v).1 c γ c' ∈ K.lev.Uloc (A.eV v).1 := by
  first | exact @GlobalTheory.LevelHecke.PairToLevel.main | exact GlobalTheory.LevelHecke.PairToLevel.main | (intros; apply GlobalTheory.LevelHecke.PairToLevel.main <;> assumption)
end

