module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveMinorUnits

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.AdmissibleHermitianColumns
section
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section gram

variable (X : Data E r)

def hv (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Fin r → ℂ :=
  fun a => hermC τ.1 X.Gm (col M a) (Data.emb τ.1 ξ)

def rk1 (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  vecMulVec (hv X ξ τ M) (fun b => conj (hv X ξ τ M b))

lemma col_mul (A M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * M) a = A *ᵥ col M a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

private lemma hermC_add_smul_add_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u e v : Fin r → ℂ)
    (β γ : ℂ) :
    hermC τ G (u + β • e) (v + γ • e) = hermC τ G u v + conj γ * hermC τ G u e +
      β * hermC τ G e v + β * conj γ * hermC τ G e e := by
  simp only [hermC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma hermC_swap_of_conj_symm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc', hG]
  ring

lemma hermC_pair (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (e u v : Fin r → ℂ) (he : hermC τ G e e = 0) (α : ℂ) :
    hermC τ G (u + (α * hermC τ G u e) • e) (v + (α * hermC τ G v e) • e) =
      hermC τ G u v + (α + conj α) * hermC τ G u e * conj (hermC τ G v e) := by
  rw [hermC_add_smul_add_smul, hermC_swap_of_conj_symm τ G hG v e, he]
  simp only [map_mul]
  ring

lemma alpha_conj (c : ℝ) (s : ℂ) :
    (-(I * (c : ℂ) * s)) + conj (-(I * (c : ℂ) * s)) = ((2 * c * s.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private lemma hermC_emb_emb_eq_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hermC, herm, Data.emb, map_sum, map_mul, emb_cc']

lemma gram_flowMat {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.flowMat ξ τ s * M) =
      gram τ.1 X.Gm M + ((2 * X.c τ * s.im : ℝ) : ℂ) • rk1 X ξ τ M := by
  have he : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb_emb_eq_herm, hξ, map_zero]
  ext a b
  simp only [gram, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rk1, hv,
    vecMulVec_apply]
  rw [col_mul, col_mul, flowMat_mulVec (X := X), flowMat_mulVec (X := X),
    hermC_pair τ.1 X.Gm X.Gm_herm _ _ _ he, alpha_conj]
  ring

lemma mat_flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl

def admissibleImaginary (ξ : Fin r → E) (x : Frame X.Ψ r) : Set (X.Ψ → ℝ) :=
  {y | ∀ τ : X.Ψ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i *
    (lminor (gram τ.1 X.Gm (mat x τ) + ((2 * X.c τ * y τ : ℝ) : ℂ) • rk1 X ξ τ (mat x τ)) i).re}

lemma flow_mem_dom_iff {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (x : Frame X.Ψ r)
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) :
    X.flow ξ s x ∈ X.dom ↔ (fun τ => (s τ).im) ∈ admissibleImaginary X ξ x := by
  simp only [Data.dom, GG, Set.mem_setOf_eq, admissibleImaginary, dmin, mat_flow, gram_flowMat X hξ, det_mul,
    det_flowMat (X := X) hξ, one_mul]
  constructor
  · intro h τ i
    exact (h τ).2 i
  · intro h τ
    exact ⟨(hx τ).1, h τ⟩

end gram

section affine

lemma leadingMinor_add_rankOne (A : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) (i : Fin (r + 1))
    (hA : lminor A i ≠ 0) : ∃ κ : ℂ, ∀ t : ℂ, lminor (A + t • vecMulVec u v) i = lminor A i * (1 + t * κ) := by
  unfold lminor at hA ⊢
  set e := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  set B := A.submatrix e e with hB
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨(v ∘ e) ⬝ᵥ (B⁻¹ *ᵥ (u ∘ e)), fun t => ?_⟩
  have hz : B *ᵥ (B⁻¹ *ᵥ (u ∘ e)) = u ∘ e := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hB', one_mulVec]
  have key : B * (1 + vecMulVec (B⁻¹ *ᵥ (u ∘ e)) (t • (v ∘ e))) =
      (A + t • vecMulVec u v).submatrix e e := by
    rw [mul_add, mul_one]
    ext a b
    have hza : ∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k = u (e a) := congrFun hz a
    simp only [Matrix.add_apply, Matrix.mul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Function.comp_apply, Matrix.submatrix_apply, Matrix.smul_apply]
    rw [show ∑ k, B a k * ((B⁻¹ *ᵥ (u ∘ e)) k * (t * v (e b))) =
        (∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k) * (t * v (e b)) by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring, hza]
    simp only [hB, Matrix.submatrix_apply]
    ring
  rw [← key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, smul_dotProduct,
    smul_eq_mul]

lemma open_convex_aff {ι κ : Type*} [Fintype ι] [Finite κ] (a b : ι → κ → ℝ) :
    IsOpen {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} ∧
      Convex ℝ {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  constructor
  · have hs : {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} =
        ⋂ τ, ⋂ i, {y : ι → ℝ | 0 < a τ i + y τ * b τ i} := by
      ext y
      simp
    rw [hs]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_const.add ((continuous_apply τ).mul continuous_const))
  · intro y hy z hz s t hs ht hst
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy hz ⊢
    intro τ i
    have h1 := hy τ i
    have h2 := hz τ i
    have key : a τ i + (s * y τ + t * z τ) * b τ i =
        s * (a τ i + y τ * b τ i) + t * (a τ i + z τ * b τ i) := by
      linear_combination (-(a τ i)) * hst
    rw [key]
    rcases hs.lt_or_eq with hs' | hs'
    · exact add_pos_of_pos_of_nonneg (mul_pos hs' h1) (mul_nonneg ht h2.le)
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simpa using h2

end affine

section adm

variable (X : Data E r)

lemma admissibleImaginary_eq_halfspaces {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    ∃ a b : X.Ψ → Fin (r + 1) → ℝ, admissibleImaginary X ξ x = {y | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  have hL : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), lminor (gram τ.1 X.Gm (mat x τ)) i ≠ 0 := by
    intro τ i h
    have h1 := (hx τ).2 i
    simp only [dmin, h, Complex.zero_re, mul_zero, lt_irrefl] at h1
  have hk : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), ∃ κ : ℂ, ∀ t : ℂ,
      lminor (gram τ.1 X.Gm (mat x τ) + t • rk1 X ξ τ (mat x τ)) i =
        lminor (gram τ.1 X.Gm (mat x τ)) i * (1 + t * κ) :=
    fun τ i => leadingMinor_add_rankOne _ _ _ i (hL τ i)
  choose κ hκ using hk
  have hre : ∀ (L k : ℂ) (t : ℝ), (L * (1 + (t : ℂ) * k)).re = L.re + t * (L * k).re := by
    intro L k t
    rw [show L * (1 + (t : ℂ) * k) = L + (t : ℂ) * (L * k) by ring, Complex.add_re,
      Complex.re_ofReal_mul]
  refine ⟨fun τ i => psgn X.p0 i * (lminor (gram τ.1 X.Gm (mat x τ)) i).re,
    fun τ i => psgn X.p0 i * (2 * X.c τ) * (lminor (gram τ.1 X.Gm (mat x τ)) i * κ τ i).re, ?_⟩
  ext y
  simp only [admissibleImaginary, Set.mem_setOf_eq, hκ, hre]
  refine forall_congr' fun τ => forall_congr' fun i => ?_
  apply iff_of_eq
  congr 1
  ring

lemma admissibleImaginary_open_convex {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    IsOpen (admissibleImaginary X ξ x) ∧ Convex ℝ (admissibleImaginary X ξ x) := by
  obtain ⟨a, b, h⟩ := admissibleImaginary_eq_halfspaces X (ξ := ξ) x hx
  rw [h]
  exact open_convex_aff a b

end adm

end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def epStar (M f w k0 : ℝ) : ℝ := min 1 (Real.pi / (M * (f * w + 2) * k0 * Real.log 2))

def CuspFormGapCondition : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    ∃ c' : ℝ, 0 < c' ∧ P ∈ X.SSgt la c'

def CuspidalExponentialDecay : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (c : ℝ), 0 ≤ c → P ∈ X.SSgt la c →
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ C * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x)

def MahlerCompactnessCriterion : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ K : Set (Frame X.Ψ r), IsCompact K ∧ K ⊆ X.dom ∧
    ∀ x ∈ X.dom, ε ≤ X.la1 x → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ K

def MaxBoundStatement : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (M w : ℝ), P ∈ X.SS la →
    0 < M → (∑ τ, X.spread la τ) ≤ w → 0 < w →
    (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧
        ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) →
    ∀ z0 ∈ X.dom, (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    ∀ v ∈ X.L', v ≠ 0 → ∃ τ : X.Ψ, epStar M (fdeg E) w X.k0 ≤ X.maj z0 τ (Data.emb τ.1 v)

end

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section herm

variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

lemma hC_add_left (u u' v : Fin r → ℂ) : hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma hC_sub_left (u u' v : Fin r → ℂ) : hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma hC_smul_left (c : ℂ) (u v : Fin r → ℂ) : hermC τ G (c • u) v = c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_add_right (u v v' : Fin r → ℂ) : hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

lemma hC_smul_right (c : ℂ) (u v : Fin r → ℂ) : hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) v = ∑ i ∈ s, hermC τ G (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hC_add_left, ih]

lemma hC_symm (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc, hG]
  ring

lemma emb_herm (x y : Fin r → E) : τ (herm G x y) = hermC τ G (Data.emb τ x) (Data.emb τ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, hermC, Data.emb, map_sum, map_mul, emb_cc]

end herm

namespace Data

variable {r : ℕ} (X : Data E r)

lemma col_mul (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * B) a = Matrix.mulVec A (col B a) := by
  funext k; simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  funext a
  simp only [flowMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, emb, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma mat_flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl

lemma ppos_eq_of (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (β : Fin X.p0 → ℂ)
    (horth : ∀ b : Fin X.p0, hermC τ.1 X.Gm (u - ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) :
    X.ppos x τ u = ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a) := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have hc : cf = Matrix.vecMul β A := by
    funext b
    have h := horth b
    rw [hC_sub_left, sub_eq_zero, hC_sum_left] at h
    simp only [cf, h, hC_smul_left, Matrix.vecMul, dotProduct, hAdef, gramPos, gram,
      Matrix.submatrix_apply, Matrix.of_apply]
  have hα : (fun a => ∑ b, cf b * A⁻¹ b a) = β := by
    have : Matrix.vecMul cf A⁻¹ = β := by
      rw [hc, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hA), Matrix.vecMul_one]
    rw [← this]; rfl
  unfold ppos
  rw [← hα]

lemma ppos_orth (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (b : Fin X.p0) : hermC τ.1 X.Gm (u - X.ppos x τ u) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have key : Matrix.vecMul (Matrix.vecMul cf A⁻¹) A = cf := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hA), Matrix.vecMul_one]
  have h2 := congrFun key b
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [hC_sub_left, sub_eq_zero]
  unfold ppos
  rw [hC_sum_left]
  simp only [hC_smul_left]
  rw [show hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) = cf b from rfl, ← h2]
  rfl

lemma gramPos_det_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : (X.gramPos x τ).det ≠ 0 := by
  have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
  intro h0
  have : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0 := h0
  rw [this] at h
  simp at h

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramFlowTransform
section
namespace ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}

def flw (α : ℂ) (e : Fin r → ℂ) (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (f : Fin n → Fin r → ℂ) : Fin n → Fin r → ℂ :=
  fun a => f a + (α * hermC τ G (f a) e) • e

theorem cv_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    cv τ G (flw α e τ G f) e = cv τ G f e := by
  funext a
  show hermC τ G e (f a + (α * hermC τ G (f a) e) • e) = hermC τ G e (f a)
  rw [GramDeterminantReal.hC_add_right, GramDeterminantReal.hermC_smul_right, he, mul_zero, add_zero]
  all_goals exact hG

theorem gramF_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    gramF τ G (flw α e τ G f) = gramF τ G f +
      replicateCol Unit (fun a => (α + conj α) * conj (cv τ G f e a)) *
        replicateRow Unit (cv τ G f e) := by
  ext a b
  have hc := GramDeterminantReal.hC_conj hG
  simp only [Matrix.add_apply, Matrix.mul_apply, replicateCol, replicateRow, Matrix.of_apply,
    Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.gramF, flw]
  rw [GramDeterminantReal.hC_add_left, GramDeterminantReal.hC_add_right, GramDeterminantReal.hC_add_right,
    GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_left, GramDeterminantReal.hermC_smul_right,
    GramDeterminantReal.hermC_smul_right, he, hc e (f a)]
  all_goals try exact hG
  simp only [GramDeterminantReal.cv, map_mul]
  rw [← hc (f b) e]
  ring

theorem mt_y {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ) :
    GramDeterminantReal.mt τ G f e = ∑ b, yv τ G f e b * conj (cv τ G f e b) := by
  simp only [GramDeterminantReal.mt, GramDeterminantReal.yv, Matrix.vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) : (gramF τ G (flw α e τ G f)).det =
      (gramF τ G f).det * (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  rw [gramF_flw hG e he α f, Matrix.det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateCol, replicateRow,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, GramDeterminantReal.mt, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mt_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) (h1 : 1 + (α + conj α) * GramDeterminantReal.mt τ G f e ≠ 0) :
    GramDeterminantReal.mt τ G (flw α e τ G f) e =
      GramDeterminantReal.mt τ G f e / (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by
  set s := α + conj α with hs
  set m := GramDeterminantReal.mt τ G f e with hm
  have hA' : IsUnit (gramF τ G (flw α e τ G f)).det := by
    rw [det_flw hG e he α f hA]
    exact hA.mul (isUnit_iff_ne_zero.mpr h1)
  have hyA : Matrix.vecMul (yv τ G f e) (gramF τ G f) = cv τ G f e := by
    simp only [GramDeterminantReal.yv, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  have hyB : Matrix.vecMul (yv τ G f e)
      (replicateCol Unit (fun a => s * conj (cv τ G f e a)) * replicateRow Unit (cv τ G f e)) =
      (s * m) • cv τ G f e := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, replicateCol, replicateRow,
      Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul]
    rw [hm, mt_y, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have key : Matrix.vecMul (yv τ G f e) (gramF τ G (flw α e τ G f)) =
      (1 + s * m) • cv τ G f e := by
    rw [gramF_flw hG e he α f, Matrix.vecMul_add, hyA, hyB, add_smul, one_smul]
  have hy : yv τ G (flw α e τ G f) e = (1 + s * m)⁻¹ • yv τ G f e := by
    have h2 : yv τ G f e = (1 + s * m) • yv τ G (flw α e τ G f) e := by
      conv_rhs => rw [GramDeterminantReal.yv, cv_flw hG e he α f, ← Matrix.smul_vecMul, ← key,
        Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA', Matrix.vecMul_one]
    rw [h2, smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [mt_y (flw α e τ G f) e, hy, cv_flw hG e he α f, div_eq_inv_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  congr 1
  exact (mt_y f e).symm

end

end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
end

