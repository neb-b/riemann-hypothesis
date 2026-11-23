module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeMulNormFlatOfSelfDual
section
namespace GlobalTheory.TensorLat

open NumberField ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}

theorem norm_sq_contr_apply_le (γ : Fin n → Vsp dim) (w : Fin n → E) (i : Idx dim) :
    ‖contr γ w i‖ ^ 2 ≤ (∑ k, ‖i.1 (w k)‖ ^ 2) * ∑ k, ‖γ k i‖ ^ 2 := by
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖i.1 (w k)‖)
    fun k => ‖γ k i‖)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [contr_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

theorem norm_sq_contr_le (γ : Fin n → Vsp dim) (w : Fin n → E) {R : ℝ}
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ R) :
    ‖contr γ w‖ ^ 2 ≤ R * ‖flat γ‖ ^ 2 := by
  rw [norm_sq_flat, EuclideanSpace.norm_sq_eq]
  simp only [EuclideanSpace.norm_sq_eq (γ _)]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => (norm_sq_contr_apply_le γ w i).trans ?_
  exact mul_le_mul_of_nonneg_right (hw i.1) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem norm_contr_le (γ : Fin n → Vsp dim) (w : Fin n → E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ ρ ^ 2) :
    ‖contr γ w‖ ≤ ρ * ‖flat γ‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow]
  exact norm_sq_contr_le γ w hw

theorem exists_contr_ne_zero {ι : Type*} (v : ι → Fin n → E)
    (hspan : Submodule.span E (Set.range v) = ⊤) {γ : Fin n → Vsp dim} (hγ : γ ≠ 0) :
    ∃ i, contr γ (v i) ≠ 0 := by
  by_contra h
  push Not at h
  exact hγ (eq_zero_of_contr_span hspan (by rintro _ ⟨i, rfl⟩; exact h i))

theorem le_mul_norm_flat (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) {ι : Type*}
    (v : ι → Fin n → E) (hv : ∀ i, v i ∈ Λ') (hspan : Submodule.span E (Set.range v) = ⊤)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hlen : ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2)
    {lam : ℝ} (hlam : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (h0 : γ ≠ 0) :
    lam ≤ ρ * ‖flat γ‖ := by
  obtain ⟨i, hi⟩ := exists_contr_ne_zero v hspan h0
  exact (hlam _ (hγ _ (hv i)) hi).trans (norm_contr_le γ (v i) hρ (hlen i))


omit [IsCMField E] in
theorem span_eq_top_of_rat {S : Set (Fin n → E)} (h : Submodule.span ℚ S = ⊤) :
    Submodule.span E S = ⊤ :=
  eq_top_iff.2 fun x _ => Submodule.span_le_restrictScalars ℚ E S (h ▸ Submodule.mem_top (x := x))

theorem le_mul_norm_flat_of_selfDual (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {lam : ℝ} (hlam : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (h0 : γ ≠ 0) :
    lam ≤ 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E * ‖flat γ‖ := by
  obtain ⟨v, hv, -, hspan, hlen⟩ := exists_short_vectors Λ' hfg hint hdual
  have hr : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
  exact le_mul_norm_flat X Λ' v hv (span_eq_top_of_rat hspan) (by positivity) hlen hlam hγ h0

end GlobalTheory.TensorLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NsmulApplyMemOfMemTensorLat
section
namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}

theorem eq_sum_tens_contr {ι : Type*} [Fintype ι] {v w : ι → Fin n → E}
    (h : ∀ u : Fin n → E, u = ∑ i, herm 1 u (w i) • v i) (γ : Fin n → Vsp dim) :
    γ = ∑ i, tens (contr γ (w i)) (v i) := by
  have hs : ∀ j, ∑ i, cc (w i j) • v i = (Pi.single j (1 : E) : Fin n → E) := by
    intro j
    rw [h (Pi.single j 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [DualFamily.herm_one_eq]
    simp [Pi.single_apply]
  calc γ = ∑ j, tens (γ j) (Pi.single j (1 : E)) := (sum_tens_single γ).symm
    _ = ∑ j, ∑ i, tens (actE (cc (w i j)) (γ j)) (v i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hs j, tens_sum_right]
        simp_rw [tens_smul_right]
    _ = ∑ i, ∑ j, tens (actE (cc (w i j)) (γ j)) (v i) := Finset.sum_comm
    _ = ∑ i, tens (contr γ (w i)) (v i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [contr, tens_sum_left]

variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}

theorem tens_mem_of_integral (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    {x : Vsp X.dim} (hx : x ∈ X.L) {v : Fin n → E} (hv : v ∈ Λ') : tens x v ∈ tensorLat X Λ' :=
  tens_mem_tensorLat hx fun w hw => hint v hv w hw

theorem tensorLat_eq_span (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    tensorLat X Λ' = Submodule.span ℤ {γ | ∃ x ∈ X.L, ∃ v ∈ Λ', γ = tens x v} := by
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  apply le_antisymm
  · intro γ hγ
    rw [eq_sum_tens_contr hexp γ]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨_, mem_tensorLat.1 hγ (w i) (hw i), v i, hv i, rfl⟩
  · rw [Submodule.span_le]
    rintro γ ⟨x, hx, u, hu, rfl⟩
    exact tens_mem_of_integral hint hx hu

theorem im_HC_int (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {γ γ' : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (hγ' : γ' ∈ tensorLat X Λ') :
    ∃ k : ℤ, (HC γ γ').im = k := by
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  have hc := mem_tensorLat.1 hγ'
  choose k hk using fun i => im_HC_tens_int hγ (hc (w i) (hw i)) (hv i)
  refine ⟨∑ i, k i, ?_⟩
  rw [eq_sum_tens_contr hexp γ', HC_sum_right, Complex.im_sum]
  push_cast
  exact Finset.sum_congr rfl fun i _ => hk i

theorem exists_im_HC_eq (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (φ : tensorLat X Λ' →+ ℤ) :
    ∃ γ ∈ tensorLat X Λ', ∀ γ' : tensorLat X Λ',
      (φ γ' : ℝ) = (HC γ (γ' : Fin n → Vsp X.dim)).im := by
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  let ψ : Fin m → (X.L →+ ℤ) := fun i => φ.comp
    { toFun := fun x => ⟨tens (x : Vsp X.dim) (v i), tens_mem_of_integral hint x.2 (hv i)⟩
      map_zero' := Subtype.ext (tens_zero_left _)
      map_add' := fun a b => Subtype.ext (tens_add_left _ _ _) }
  choose y hyL hy using fun i => X.perfect (ψ i)
  refine ⟨∑ i, tens (y i) (w i),
    Submodule.sum_mem _ fun i _ => tens_mem_of_integral hint (hyL i) (hw i), fun γ' => ?_⟩
  have hc : ∀ i, contr (γ' : Fin n → Vsp X.dim) (w i) ∈ X.L :=
    fun i => mem_tensorLat.1 γ'.2 (w i) (hw i)
  have hsplit : γ' = ∑ i, (⟨tens (contr (γ' : Fin n → Vsp X.dim) (w i)) (v i),
      tens_mem_of_integral hint (hc i) (hv i)⟩ : tensorLat X Λ') := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact eq_sum_tens_contr hexp _
  rw [HC_sum_left, Complex.im_sum]
  conv_lhs => rw [hsplit]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HC_tens_left]
  exact hy i ⟨_, hc i⟩

private lemma tens_nsmul (x : Vsp dim) (v : Fin n → E) (N : ℕ) :
    tens x (N • v) = N • tens x v := by
  rw [← Nat.cast_smul_eq_nsmul E N v, tens_smul_right, actE_natCast]
  funext k
  simp only [tens_apply, Pi.smul_apply]
  rw [← actL_apply, map_nsmul, actL_apply]

theorem nsmul_mem_tensorLat (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {N : ℕ}
    (hN : ∀ u ∈ stdLat E n, N • u ∈ Λ') {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) :
    N • γ ∈ tensorLat X Λ' := by
  have hs : ∀ k, N • (Pi.single k (1 : E) : Fin n → E) ∈ Λ' := fun k =>
    hN _ (mem_stdLat.2 fun j => by
      by_cases hjk : j = k <;> simp [hjk, isIntegral_one, isIntegral_zero])
  have heq : N • γ = ∑ k, tens (γ k) (N • (Pi.single k (1 : E) : Fin n → E)) := by
    conv_lhs => rw [← sum_tens_single γ]
    rw [Finset.smul_sum]
    simp_rw [tens_nsmul]
  rw [heq]
  exact Submodule.sum_mem _ fun k _ => tens_mem_of_integral hint (hγ k) (hs k)

theorem nsmul_apply_mem_of_mem_tensorLat {N : ℕ} (hN : ∀ u ∈ stdLat E n, N • u ∈ Λ')
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (k : Fin n) : (N • γ) k ∈ X.L := by
  have h1 : N • (Pi.single k (1 : E) : Fin n → E) ∈ Λ' :=
    hN _ (mem_stdLat.2 fun j => by
      by_cases hjk : j = k <;> simp [hjk, isIntegral_one, isIntegral_zero])
  have h2 := mem_tensorLat.1 hγ _ h1
  rw [← Nat.cast_smul_eq_nsmul E N (Pi.single k (1 : E) : Fin n → E), contr_smul_right,
    contr_single] at h2
  have hcc : cc (N : E) = N := by
    unfold cc
    exact map_natCast _ N
  rw [hcc, actE_natCast] at h2
  exact h2

theorem exists_nsmul_stdLat_le (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ stdLat E n, N • u ∈ Λ' := by
  classical
  have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image fun p : Fin m × Fin n => cc (w p.1 p.2))
  have hN : ((y.natAbs : ℕ) : E) = (y : E) ∨ ((y.natAbs : ℕ) : E) = -(y : E) := by
    rcases Int.natAbs_eq y with hq | hq
    · left
      conv_rhs => rw [hq]
      simp
    · right
      conv_rhs => rw [hq]
      simp
  have hyz : ∀ i a, IsIntegral ℤ ((y.natAbs : E) * cc (w i a)) := by
    intro i a
    have h := hy _ (Finset.mem_image.2 ⟨(i, a), Finset.mem_univ _, rfl⟩)
    rw [zsmul_eq_mul] at h
    rcases hN with e | e
    · rw [e]
      exact h
    · rw [e, neg_mul]
      exact h.neg
  refine ⟨y.natAbs, Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hy0), fun u hu => ?_⟩
  have hc : ∀ i, IsIntegral ℤ ((y.natAbs : E) * herm 1 u (w i)) := by
    intro i
    rw [DualFamily.herm_one_eq, Finset.mul_sum]
    refine IsIntegral.sum _ fun a _ => ?_
    rw [mul_left_comm]
    exact (mem_stdLat.1 hu a).mul (hyz i a)
  have hmem : ∑ i, (⟨_, hc i⟩ : 𝓞 E) • v i ∈ Λ' :=
    Λ'.sum_mem fun i _ => Λ'.smul_mem _ (hv i)
  convert hmem using 1
  conv_lhs => rw [hexp u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  rw [Algebra.smul_def, ← mul_assoc]
  rfl

theorem exists_nsmul_commensurable (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    ∃ M : ℕ, 1 ≤ M ∧
      (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → M • γ ∈ tensorLat X Λ') ∧
      (∀ γ ∈ tensorLat X Λ', ∀ k, (M • γ) k ∈ X.L) := by
  obtain ⟨N, hN1, hN⟩ := exists_nsmul_stdLat_le hfg hint hdual
  exact ⟨N, hN1, fun γ hγ => nsmul_mem_tensorLat hint hN hγ,
    fun γ hγ k => nsmul_apply_mem_of_mem_tensorLat hN hγ k⟩

theorem tensorLat_span_integral_perfect (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ'.FG) (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    (∃ (m : ℕ) (v w : Fin m → Fin n → E), (∀ i, v i ∈ Λ') ∧ (∀ i, w i ∈ Λ') ∧
      (∀ u : Fin n → E, u = ∑ i, herm 1 u (w i) • v i) ∧
      ∀ γ : Fin n → Vsp X.dim, γ = ∑ i, tens (contr γ (w i)) (v i)) ∧
    (∀ (m : ℕ) (v w : Fin m → Fin n → E), (∀ u : Fin n → E, u = ∑ i, herm 1 u (w i) • v i) →
      ∀ γ : Fin n → Vsp X.dim, γ = ∑ i, tens (contr γ (w i)) (v i)) ∧
    tensorLat X Λ' = Submodule.span ℤ {γ | ∃ x ∈ X.L, ∃ v ∈ Λ', γ = tens x v} ∧
    (∀ (α : 𝓞 E), ∀ γ ∈ tensorLat X Λ', (fun k => act α (γ k)) ∈ tensorLat X Λ') ∧
    (∀ γ ∈ tensorLat X Λ', ∀ γ' ∈ tensorLat X Λ', ∃ k : ℤ, (HC γ γ').im = k) ∧
    (∀ φ : tensorLat X Λ' →+ ℤ, ∃ γ ∈ tensorLat X Λ', ∀ γ' : tensorLat X Λ',
      (φ γ' : ℝ) = (HC γ (γ' : Fin n → Vsp X.dim)).im) ∧
    (∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ stdLat E n, N • u ∈ Λ') ∧
    (∀ N : ℕ, (∀ u ∈ stdLat E n, N • u ∈ Λ') →
      (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → N • γ ∈ tensorLat X Λ') ∧
      (∀ γ ∈ tensorLat X Λ', ∀ k, (N • γ) k ∈ X.L)) ∧
    (∃ M : ℕ, 1 ≤ M ∧
      (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → M • γ ∈ tensorLat X Λ') ∧
      (∀ γ ∈ tensorLat X Λ', ∀ k, (M • γ) k ∈ X.L)) := by
  refine ⟨?_, fun m v w h γ => eq_sum_tens_contr h γ, tensorLat_eq_span hfg hint hdual,
    fun α γ hγ => act_mem_tensorLat α hγ, fun γ hγ γ' hγ' => im_HC_int hfg hint hdual hγ hγ',
    exists_im_HC_eq hfg hint hdual, exists_nsmul_stdLat_le hfg hint hdual,
    fun N hN => ⟨fun γ hγ => nsmul_mem_tensorLat hint hN hγ,
      fun γ hγ k => nsmul_apply_mem_of_mem_tensorLat hN hγ k⟩,
    exists_nsmul_commensurable hfg hint hdual⟩
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  exact ⟨m, v, w, hv, hw, hexp, fun γ => eq_sum_tens_contr hexp γ⟩

end GlobalTheory.TensorLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormSqPullbackTensorEqProd
section
open Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

namespace ThetaBound

section General

variable {ι : Type} [Fintype ι]

theorem l2NormSq_nonneg_gaussianTorus (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : 0 ≤ Y.l2 q F := by
  unfold GT.l2
  rw [MeasureTheory.average_eq]
  refine MeasureTheory.integral_nonneg_of_ae ?_ |> smul_nonneg (by positivity)
  refine Filter.Eventually.of_forall fun v => ?_
  unfold GT.ptN2
  positivity

theorem le_firstMinimum_of_period_lower_bound (Y : GT ι) (hι : Fintype.card ι ≠ 0) {lam : ℝ}
    (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖) : lam ≤ Y.la1 := by
  refine le_csInf ⟨‖Y.b ⟨0, by omega⟩‖, Y.b ⟨0, by omega⟩,
    Submodule.subset_span ⟨_, rfl⟩, Y.b.ne_zero _, rfl⟩ ?_
  rintro t ⟨x, hx, hx0, rfl⟩
  exact hmin x hx hx0

theorem pointwiseNormSq_le_l2_of_firstMinimum (hsup : GSupStatement) (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    (v : EuclideanSpace ℂ ι) :
    Y.ptN2 1 F v ≤ (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
      (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) ^ 2 * Y.l2 1 F := by
  refine (hsup ι Y 1 le_rfl F hF v).trans (mul_le_mul_of_nonneg_right ?_ (l2NormSq_nonneg_gaussianTorus Y 1 F))
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← pow_mul, mul_comm (Fintype.card ι) 2]
  simp only [Nat.cast_one, one_pow, mul_one, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  by_cases hι : Fintype.card ι = 0
  · simp [hι]
  have h1 := le_firstMinimum_of_period_lower_bound Y hι hmin
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : 0 < Y.la1 := hlam.trans_le h1
  gcongr


end General

section Columns

open TensorLat

variable {E : Type} [Field E] [NumberField E]

theorem col_mem_Sec (X : PT E) {q : ℕ} {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1) :
    (fun z => s fun _ => z) ∈ (gtOf X q).Sec q := by
  refine ⟨hs.1.comp (differentiable_pi.2 fun _ => differentiable_id), fun γ hγ v => ?_⟩
  have e : (fun _ : Fin 1 => v + γ) = (fun _ => v) + (fun _ => γ) := by funext j; simp
  simp only [e]
  rw [hs.2 (fun _ => γ) (fun _ => hγ) (fun _ => v)]
  simp [HC, gtOf]

theorem oneColumn_pointwiseNorm_eq_torus (X : PT E) (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) (x : Vsp X.dim) :
    (gtOf X q).ptN2 q (fun z => s fun _ => z) x = X.ptN2 q s fun _ => x := by
  simp [GT.ptN2, PT.ptN2, HC, jof_Hf_self_re]

theorem oneColumn_l2Norm_eq_torus (X : PT E) (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    (gtOf X q).l2 q (fun z => s fun _ => z) = X.l2 q s := by
  rw [l2_norm_fundamental_domain, GT.l2]
  simp only [oneColumn_pointwiseNorm_eq_torus]
  rfl

theorem l2_pos_of_mem_sec_of_ne_zero (X : PT E) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1)
    (hne : s ≠ 0) : 0 < X.l2 q s := by
  refine lt_of_le_of_ne ?_ fun h => hne (eq_zero_of_l2_eq_zero X packingCount hq hs h.symm)
  rw [← oneColumn_l2Norm_eq_torus]
  exact l2NormSq_nonneg_gaussianTorus _ _ _

end Columns

end ThetaBound


open scoped Classical in
open Classical in
theorem theta_value_bound (hsup : GSupStatement) {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (Y : GT ι) (F : EuclideanSpace ℂ ι → ℂ) (hF : F ∈ Y.Sec 1) (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    {κ : Type} (s : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ s, ‖c j‖ ≤ 1) (y : κ → EuclideanSpace ℂ ι)
    (P : MvPolynomial ι ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    ‖∑ j ∈ s, c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
      s.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) / (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) * Real.sqrt (Y.l2 1 F) := by
  set C : ℝ := Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
    (Real.sqrt Real.pi * lam)) ^ Fintype.card ι with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ j ∈ s,
      ‖c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
        (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) * C *
          Real.sqrt (Y.l2 1 F) := by
    intro j hj
    have h := translate_jet_bound U hU 1 le_rfl F hF.1 (C ^ 2 * Y.l2 1 F)
      (ThetaBound.pointwiseNormSq_le_l2_of_firstMinimum hsup Y hF hlam hmin) P a hP (y j)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC0, Nat.cast_one, one_mul] at h
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hc j hj)).trans (h.trans_eq ?_)
    ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ key).trans_eq ?_)
  rw [nsmul_eq_mul]
  ring

end GlobalTheory
end

