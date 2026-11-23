module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0018

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianPsiBounds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace HermitianPsiBounds

open Matrix NumberField Complex QuadraticLatticeForms
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

noncomputable def Cinv : ℝ := ∑ τ : X.Ψ, 1 / X.c τ

theorem inv_c_le (τ : X.Ψ) : 1 / X.c τ ≤ Cinv X := by
  unfold Cinv
  exact Finset.single_le_sum (f := fun τ => 1 / X.c τ)
    (fun τ' _ => by unfold Data.c; positivity) (Finset.mem_univ τ)

theorem Cinv_nonneg : 0 ≤ Cinv X := by
  unfold Cinv
  exact Finset.sum_nonneg fun τ _ => by unfold Data.c; positivity

theorem sum_sq_le (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) (p : Fin r → E) :
    ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 ≤ Qy X y p * Cinv X := by
  have hc : 0 < X.c τ := by
    have h1 : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).mpr X.ξ0_ne
    have := norm_pos_iff.mpr h1
    unfold Data.c
    linarith
  have key : ∀ s : ℝ, 0 ≤ s → X.c τ * s ≤ Qy X y p → s ≤ Qy X y p * Cinv X := by
    intro s hs h1
    have h2 := inv_c_le X τ
    have hQ : 0 ≤ Qy X y p := le_trans (mul_nonneg hc.le hs) h1
    calc s = (X.c τ * s) * (1 / X.c τ) := by
          rw [mul_comm (X.c τ), mul_assoc, mul_one_div_cancel hc.ne', mul_one]
      _ ≤ Qy X y p * Cinv X := mul_le_mul h1 h2 (by positivity) hQ
  apply key _ (Finset.sum_nonneg fun _ _ => by positivity)
  unfold Qy
  exact Finset.single_le_sum
    (f := fun τ' => X.c τ' * ∑ a, ‖((y τ')⁻¹ *ᵥ Data.emb τ'.1 p) a‖ ^ 2)
    (fun τ' _ => mul_nonneg (by unfold Data.c; positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)) (Finset.mem_univ τ)

private lemma hermC_sum_left_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : Fin r → ℂ)
    (y : Fin r → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ b, c b • y b) w = ∑ b, c b * hermC τ G (y b) w := by
  obtain ⟨g, hg⟩ : ∃ g : Fin r → ℂ, ∀ u, hermC τ G u w = ∑ i, u i * g i :=
    ⟨fun i => ∑ k, τ (G i k) * conj (w k), fun u => by simp only [hermC, Finset.mul_sum, mul_assoc]⟩
  simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

private lemma hermC_sum_right_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ)
    (c : Fin r → ℂ) (y : Fin r → Fin r → ℂ) :
    hermC τ G u (∑ b, c b • y b) = ∑ b, conj (c b) * hermC τ G u (y b) := by
  obtain ⟨g, hg⟩ : ∃ g : Fin r → ℂ, ∀ w, hermC τ G u w = ∑ k, g k * conj (w k) :=
    ⟨fun k => ∑ i, u i * τ (G i k), fun w => by simp only [hermC, Finset.sum_mul]; exact Finset.sum_comm⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

theorem herm_bound_psi {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IntegralBasisReduction.IsNormal X y) (τ : X.Ψ)
    (p q : Fin r → E) : ‖τ.1 (herm X.Gm p q)‖ ≤ (Qy X y p + Qy X y q) * Cinv X := by
  obtain ⟨hdet, hg⟩ := hy τ
  have hu : IsUnit (y τ).det := isUnit_iff_ne_zero.mpr hdet
  have hyinv : ∀ u : Fin r → ℂ, y τ *ᵥ ((y τ)⁻¹ *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hcols : ∀ γ : Fin r → ℂ, y τ *ᵥ γ = ∑ k, γ k • col (y τ) k := fun γ => by
    ext i
    simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]
  have hgl : ∀ k l, hermC τ.1 X.Gm (col (y τ) k) (col (y τ) l) =
      if k = l then ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) else 0 := fun k l => by
    have h := congrFun (congrFun hg k) l
    simpa [gram, Matrix.diagonal_apply] using h
  have hSp := sum_sq_le X y τ p
  have hSq := sum_sq_le X y τ q
  rw [← hermC_emb, ← hyinv (Data.emb τ.1 p), ← hyinv (Data.emb τ.1 q), hcols, hcols,
    hermC_sum_left_lemma]
  simp only [hermC_sum_right_lemma_2, hgl, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  set A := (y τ)⁻¹ *ᵥ Data.emb τ.1 p with hA
  set B := (y τ)⁻¹ *ᵥ Data.emb τ.1 q with hB
  have hterm : ∀ k, ‖A k * (conj (B k) * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ))‖ ≤ ‖A k‖ ^ 2 + ‖B k‖ ^ 2 := by
    intro k
    have hε : ‖((sgn X.p0 (k : ℕ) : ℝ) : ℂ)‖ = 1 := by
      unfold sgn
      split_ifs <;> simp
    rw [norm_mul, norm_mul, Complex.norm_conj, hε, mul_one]
    nlinarith [sq_nonneg (‖A k‖ - ‖B k‖), norm_nonneg (A k), norm_nonneg (B k)]
  calc ‖∑ k, A k * (conj (B k) * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ))‖
      ≤ ∑ k, ‖A k * (conj (B k) * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ k, (‖A k‖ ^ 2 + ‖B k‖ ^ 2) := Finset.sum_le_sum fun k _ => hterm k
    _ = ∑ k, ‖A k‖ ^ 2 + ∑ k, ‖B k‖ ^ 2 := Finset.sum_add_distrib
    _ ≤ (Qy X y p + Qy X y q) * Cinv X := by nlinarith [hSp, hSq]

theorem herm_bound {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IntegralBasisReduction.IsNormal X y) (σ : E →+* ℂ)
    (p q : Fin r → E) : ‖σ (herm X.Gm p q)‖ ≤ (Qy X y p + Qy X y q) * Cinv X := by
  by_cases hσ : σ ∈ X.Ψ
  · exact herm_bound_psi X hy ⟨σ, hσ⟩ p q
  · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      rw [X.cmType]
      first
      | (rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]
         exact hσ)
      | simpa using hσ
    have h := herm_bound_psi X hy ⟨_, hc⟩ p q
    first
    | simpa [ComplexEmbedding.conjugate_coe_eq] using h
    | (simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h; exact h)

theorem Qy_smul (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (α : E) (p : Fin r → E) :
    Qy X y (α • p) ≤ (∑ τ : X.Ψ, ‖τ.1 α‖ ^ 2) * Qy X y p := by
  unfold Qy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have e : Data.emb τ.1 (α • p) = τ.1 α • Data.emb τ.1 p := by
    funext a; simp [Data.emb]
  have e2 : ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (α • p)) a‖ ^ 2 =
      ‖τ.1 α‖ ^ 2 * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 := by
    rw [e, Matrix.mulVec_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [e2]
  have h1 : ‖τ.1 α‖ ^ 2 ≤ ∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2 :=
    Finset.single_le_sum (f := fun σ : X.Ψ => ‖σ.1 α‖ ^ 2) (fun σ _ => by positivity)
      (Finset.mem_univ τ)
  have h2 : 0 ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 :=
    mul_nonneg (c_pos X τ).le (Finset.sum_nonneg fun a _ => by positivity)
  calc X.c τ * (‖τ.1 α‖ ^ 2 * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2)
      = ‖τ.1 α‖ ^ 2 * (X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) := by ring
    _ ≤ (∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2) * (X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h1 h2

theorem sq_le_Qy_of_le_firstMinimum {x : Frame X.Ψ r} {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hm : ∀ τ u, X.maj x τ u = ∑ a, ‖((y τ)⁻¹ *ᵥ u) a‖ ^ 2) {ε : ℝ} (hε : 0 < ε) (hl : ε ≤ X.la1 x)
    {v : Fin r → E} (hv : v ∈ X.Λ) (hv0 : v ≠ 0) : ε ^ 2 ≤ Qy X y v := by
  have hQ : ∀ w : Fin r → E, ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 w) = Qy X y w := by
    intro w
    unfold Qy
    simp only [hm]
  have hnn : ∀ t ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}, 0 ≤ t := by
    rintro t ⟨w, -, -, rfl⟩
    rw [hQ]
    unfold Qy
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (by unfold Data.c; positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)
  have hmem : Qy X y v ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)} :=
    ⟨v, hv, hv0, (hQ v).symm⟩
  have h1 : X.firstMinimumSq x ≤ Qy X y v := csInf_le ⟨0, hnn⟩ hmem
  have h0 : 0 ≤ X.firstMinimumSq x := Real.sInf_nonneg hnn
  have h2 : ε ^ 2 ≤ X.la1 x ^ 2 := by nlinarith
  rw [Data.la1, Real.sq_sqrt h0] at h2
  linarith

end HermitianPsiBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LowBlock
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma sum_split (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) +
      ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ := by
  set g : ℕ → ℂ := fun i => if h : i < r then f ⟨i, h⟩ else 0 with hg
  have e1 : ∑ j, f j = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hg, dif_pos j.isLt]
  have e2 : ∑ i ∈ Finset.range r, g i = ∑ i ∈ Finset.range (X.p0 + (r - X.p0)), g i := by
    rw [Nat.add_sub_cancel' X.p0_le]
  rw [e1, e2, Finset.sum_range_add, Finset.sum_range, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha : (a : ℕ) < r := lt_of_lt_of_le a.isLt X.p0_le
    simp only [hg, dif_pos ha]
    rfl
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hm : X.p0 + (m : ℕ) < r := by have := m.isLt; have := X.p0_le; omega
    simp only [hg, dif_pos hm]

def nI (m : Fin (r - X.p0)) : Fin r := ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩

private lemma nI_val_eq_p0_add (m : Fin (r - X.p0)) : ((nI X m : Fin r) : ℕ) = X.p0 + m := rfl

lemma L_pp (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    X.lowBlock Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) = if a = c then 1 else 0 := by
  have ha := a.isLt
  have h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0) := by
    simp only [Fin.val_castLE]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : a = c
  · subst h
    simp
  · rw [if_neg h, if_neg (fun e => h (Fin.castLE_injective X.p0_le e))]

lemma L_pn (Z : X.Coord) (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    X.lowBlock Z τ (Fin.castLE X.p0_le a) (nI X m) = 0 := by
  have ha := a.isLt
  have h1 : (Fin.castLE X.p0_le a : Fin r) ≠ nI X m := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castLE, nI_val_eq_p0_add] at h'
    omega
  have h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((nI X m : Fin r) : ℕ) < X.p0) := by
    rw [Fin.val_castLE, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_neg h2, add_zero]

lemma L_np (Z : X.Coord) (τ : X.Ψ) (m : Fin (r - X.p0)) (c : Fin X.p0) :
    X.lowBlock Z τ (nI X m) (Fin.castLE X.p0_le c) = Z τ m c := by
  have hc := c.isLt
  have h1 : nI X m ≠ (Fin.castLE X.p0_le c : Fin r) := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castLE, nI_val_eq_p0_add] at h'
    omega
  have h2 : X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 := by
    rw [Fin.val_castLE, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_pos h2, zero_add]
  exact congrArg₂ (Z τ) (Fin.ext (by simp [nI_val_eq_p0_add])) (Fin.ext (by simp))

lemma L_nn (Z : X.Coord) (τ : X.Ψ) (m m' : Fin (r - X.p0)) :
    X.lowBlock Z τ (nI X m) (nI X m') = if m = m' then 1 else 0 := by
  have h2 : ¬ (X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((nI X m' : Fin r) : ℕ) < X.p0) := by
    rw [nI_val_eq_p0_add, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : m = m'
  · subst h
    simp
  · have h1 : nI X m ≠ nI X m' := by
      intro e
      have h' := congrArg Fin.val e
      rw [nI_val_eq_p0_add, nI_val_eq_p0_add] at h'
      exact h (Fin.ext (by omega))
    rw [if_neg h, if_neg h1]

lemma sgn_p (a : Fin X.p0) : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.sgn, a.isLt]

lemma sgn_n (m : Fin (r - X.p0)) : sgn X.p0 ((nI X m : Fin r) : ℕ) = -1 := by
  rw [nI_val_eq_p0_add]
  simp [ReciprocityTheory.ChartRestriction.G.FD.sgn]

def Gp (Z : X.Coord) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (X.lowBlock Z τ)ᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
    (X.lowBlock Z τ).map (starRingEnd ℂ)

private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma gram_xZ {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (X.xZ x Z) τ) = Gp X Z τ := by
  have h := ho τ
  rw [gram_eq_upper_bounds] at h
  have hm : mat (X.xZ x Z) τ = mat x τ * X.lowBlock Z τ := rfl
  rw [gram_eq_upper_bounds, hm, Gp, ← h, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

lemma Gp_apply (Z : X.Coord) (τ : X.Ψ) (a c : Fin r) :
    Gp X Z τ a c = ∑ j, X.lowBlock Z τ j a * ((sgn X.p0 (j : ℕ) : ℝ) : ℂ) * conj (X.lowBlock Z τ j c) := by
  rw [Gp, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

private lemma sum_eq_sum_castLE_add_sum_nI (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) + ∑ m : Fin (r - X.p0), f (nI X m) :=
  sum_split X f

lemma Gp_pp (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    Gp X Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) =
      (if a = c then 1 else 0) - ∑ m, Z τ m a * conj (Z τ m c) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pp X, L_np X, sgn_p X, sgn_n X]
  by_cases hac : a = c
  · subst hac
    simp [sub_eq_add_neg]
  · simp [hac, Ne.symm hac, sub_eq_add_neg]

lemma Gp_np (Z : X.Coord) (τ : X.Ψ) (m : Fin (r - X.p0)) (c : Fin X.p0) :
    Gp X Z τ (nI X m) (Fin.castLE X.p0_le c) = -conj (Z τ m c) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]
  simp

lemma Gp_pn (Z : X.Coord) (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    Gp X Z τ (Fin.castLE X.p0_le a) (nI X m) = -Z τ m a := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pp X, L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]
  simp

lemma Gp_nn (Z : X.Coord) (τ : X.Ψ) (m m' : Fin (r - X.p0)) :
    Gp X Z τ (nI X m) (nI X m') = -(if m = m' then 1 else 0) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pn X, L_nn X, sgn_p X, sgn_n X]
  by_cases h : m = m'
  · subst h
    simp
  · simp [h, Ne.symm h]

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
section
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quad2 (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) (a : Fin 2 → ℂ) :
    M.det.re * Complex.normSq (a 1) ≤ (M 0 0).re * (∑ i, ∑ k, M i k * a i * conj (a k)).re := by
  have h00 : (M 0 0).im = 0 := by
    have := hM.apply 0 0
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h11 : (M 1 1).im = 0 := by
    have := hM.apply 1 1
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h10 : M 1 0 = conj (M 0 1) := by
    have := hM.apply 1 0
    rw [Complex.star_def] at this
    exact this.symm
  simp only [Matrix.det_fin_two, Fin.sum_univ_two, h10, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, h00, h11]
  nlinarith [sq_nonneg ((M 0 0).re * (a 0).re + (M 0 1).re * (a 1).re + (M 0 1).im * (a 1).im),
    sq_nonneg ((M 0 0).re * (a 0).im + (M 0 1).re * (a 1).im - (M 0 1).im * (a 1).re)]

theorem coef_zero {r : ℕ} {ξ x : Fin r → E} (hξ0 : ξ ≠ 0) (hne : ∀ e : E, x ≠ e • ξ)
    (τ : E →+* ℂ) (p q : ℂ) (h : p • Data.emb τ ξ + q • Data.emb τ x = 0) : q = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hξ0 (funext h0)
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ (x a / ξ a) * ξ b := by
    by_contra h0
    push_neg at h0
    exact hne (x a / ξ a) (funext fun b => by rw [Pi.smul_apply, smul_eq_mul, h0 b])
  have hm : ξ a * x b - ξ b * x a ≠ 0 := by
    intro h0
    apply hb
    rw [div_mul_eq_mul_div, eq_div_iff ha]
    linear_combination h0
  have h1 := congrFun h a
  have h2 := congrFun h b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Data.emb] at h1 h2
  have hτ : τ (ξ a * x b - ξ b * x a) ≠ 0 := (map_ne_zero τ).2 hm
  rw [map_sub, map_mul, map_mul] at hτ
  have h3 : q * (τ (ξ a) * τ (x b) - τ (ξ b) * τ (x a)) = 0 := by
    linear_combination τ (ξ a) * h2 - τ (ξ b) * h1
  exact (mul_eq_zero.1 h3).resolve_right hτ

variable {r : ℕ} (X : Data E r)

def toCP (τ : X.Ψ) : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩

theorem toCP_bij : Function.Bijective (toCP X) := by
  constructor
  · rintro ⟨τ, hτ⟩ ⟨τ', hτ'⟩ h
    have h' : InfinitePlace.mk τ = InfinitePlace.mk τ' := congrArg Subtype.val h
    rcases InfinitePlace.mk_eq_iff.1 h' with e | e
    · exact Subtype.ext e
    · exfalso
      rw [← e] at hτ'
      exact (X.cmType τ).1 hτ hτ'
  · rintro ⟨w, hw⟩
    by_cases hφ : w.embedding ∈ X.Ψ
    · exact ⟨⟨_, hφ⟩, Subtype.ext (InfinitePlace.mk_embedding w)⟩
    · have hc : ComplexEmbedding.conjugate w.embedding ∈ X.Ψ := by
        by_contra hc
        exact hφ ((X.cmType _).2 hc)
      exact ⟨⟨_, hc⟩, Subtype.ext ((InfinitePlace.mk_conjugate_eq _).trans (InfinitePlace.mk_embedding w))⟩

theorem card_Psi : Fintype.card X.Ψ = fdeg E := by
  rw [Fintype.card_of_bijective (toCP_bij X)]
  unfold fdeg
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
  have h0 : NumberField.InfinitePlace.nrRealPlaces E = 0 := by
    first
    | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero
    | exact NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance
    | simp
  rw [h0, zero_add] at h
  rw [← h]
  unfold NumberField.InfinitePlace.nrComplexPlaces
  have h3 : Fintype.card (TraceIntegralBasis.CP E) = Fintype.card {w : InfinitePlace E // w.IsComplex} :=
    Fintype.card_congr (Equiv.refl _)
  omega

theorem card_Psi_pos : 0 < Fintype.card X.Ψ := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(Classical.arbitrary (InfinitePlace E)).embedding⟩
  rw [Fintype.card_pos_iff]
  by_cases h : φ ∈ X.Ψ
  · exact ⟨⟨φ, h⟩⟩
  · exact ⟨⟨ComplexEmbedding.conjugate φ, by
      by_contra hc
      exact h ((X.cmType φ).2 hc)⟩⟩

theorem one_le_prod_norm (γ : E) (hint : IsIntegral ℤ γ) (hγ : γ ≠ 0) :
    1 ≤ ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 := by
  have hall : ∀ w : InfinitePlace E, w.IsComplex := fun w => IsTotallyComplex.isComplex w
  have h1 : ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 = ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 :=
    Fintype.prod_bijective (toCP X) (toCP_bij X) _ _ fun τ => by
      show _ = (InfinitePlace.mk τ.1 γ) ^ 2
      rw [InfinitePlace.apply]
  have h2 : ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 = ∏ w : InfinitePlace E, w γ ^ w.mult := by
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv hall) _ _ fun w => ?_
    show w.1 γ ^ 2 = w.1 γ ^ InfinitePlace.mult w.1
    rw [InfinitePlace.mult_isComplex w]
  rw [h1, h2, InfinitePlace.prod_eq_abs_norm]
  have hI : IsIntegral ℤ (Algebra.norm ℚ γ) := by
    first
    | exact Algebra.isIntegral_norm ℚ hint
    | exact Algebra.isIntegral_norm hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have hN : Algebra.norm ℚ γ ≠ 0 := Algebra.norm_ne_zero_iff.2 hγ
  rw [← hn] at hN ⊢
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hN (map_zero _)
  have h3 := Int.one_le_abs hn0
  simp only [algebraMap_int_eq, eq_intCast]
  push_cast
  exact_mod_cast h3

end

end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
end

