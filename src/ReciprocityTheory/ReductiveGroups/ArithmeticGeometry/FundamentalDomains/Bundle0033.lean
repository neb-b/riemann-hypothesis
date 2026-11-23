module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MmatUnitary
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BlockIdentityExpansion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0032

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramSchmidtEigenframe
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private theorem hermC_sub_left_eq_sub {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u u' v : Fin r → ℂ) : hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v :=
  map_sub (AddMonoidHom.mk' (fun x => hermC τ G x v) (fun a b => hermC_add_left τ G a b v)) u u'

private theorem hermC_finset_sum_left' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {ι : Type} (s : Finset ι) (u : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, u i) v = ∑ i ∈ s, hermC τ G (u i) v :=
  map_sum (AddMonoidHom.mk' (fun x => hermC τ G x v) (fun a b => hermC_add_left τ G a b v)) u s

private theorem hermC_finset_sum_right_of_conj_symm {r : ℕ} (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) {ι : Type} (s : Finset ι) (u : Fin r → ℂ)
    (v : ι → Fin r → ℂ) : hermC τ G u (∑ i ∈ s, v i) = ∑ i ∈ s, hermC τ G u (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hermC_conj τ hG _ u, hermC_finset_sum_left', map_sum]
  exact Finset.sum_congr rfl (fun i _ => hermC_conj τ hG _ _)

private theorem hermC_sub_right_of_conj_symm {r : ℕ} (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  rw [← hermC_conj τ hG _ u, hermC_sub_left_eq_sub, map_sub, hermC_conj τ hG, hermC_conj τ hG]

private theorem ppos_self_adjoint_hermC {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (w v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ w) v = hermC τ.1 X.Gm w (X.ppos x τ v) := by
  have hH : (X.gramPos x τ).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Data.gramPos, Matrix.submatrix_apply, gram,
      Matrix.of_apply]
    rw [← starRingEnd_apply]
    exact hermC_conj _ X.Gm_herm _ _
  have hM := hH.inv
  simp only [Data.ppos]
  rw [hermC_finset_sum_left', hermC_finset_sum_right_of_conj_symm _ X.Gm_herm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC_smul_left, hermC_smul_right, Finset.sum_mul, map_sum, map_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [hermC_conj _ X.Gm_herm, starRingEnd_apply, hM.apply]
  ring

private theorem hermC_ppos_eq_zero_of_hermC_eq_zero_of_Jt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (w v : Fin r → ℂ) (h0 : hermC τ.1 X.Gm w v = 0) (hJ : hermC τ.1 X.Gm w (X.Jt x τ v) = 0) :
    hermC τ.1 X.Gm w (X.ppos x τ v) = 0 := by
  simp only [Data.Jt] at hJ
  rw [hermC_smul_right, hermC_sub_right_of_conj_symm _ X.Gm_herm, hermC_smul_right, h0] at hJ
  simpa using hJ

theorem gramSchmidt_eigenframe (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f Y : X.Ψ → Fin (r - 2) → Fin r → ℂ) (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (hYind : ∀ τ, LinearIndependent ℂ (Y τ))
    (hYU : ∀ τ j, Y τ j ∈ Submodule.span ℂ (Set.range (f τ)))
    (hYorth : ∀ τ (j k : Fin (r - 2)), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
      hermC τ.1 X.Gm (Y τ j) (Y τ k) = 0)
    (hYpos : ∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
      0 < (hermC τ.1 X.Gm (∑ j, w j • Y τ j) (∑ j, w j • Y τ j)).re)
    (hYneg : ∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → w j = 0) → w ≠ 0 →
      (hermC τ.1 X.Gm (∑ j, w j • Y τ j) (∑ j, w j • Y τ j)).re < 0) :
    ∃ h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ, X.IsUnitaryC h1 ∧
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) ∧
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) ∧
      (∀ τ (v : Fin r → ℂ), v ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) →
        (h1 τ) *ᵥ v ∈ Submodule.span ℂ (Y τ '' {j | (j : ℕ) < X.p0 - 1})) ∧
      (∀ τ (j : Fin (r - 2)), ∃ u : Fin r → ℂ,
        u ∈ Submodule.span ℂ (f τ '' {k | ((k : ℕ) < X.p0 - 1 ↔ (j : ℕ) < X.p0 - 1)}) ∧ (h1 τ) *ᵥ u = Y τ j) := by
  have hgs := fun τ : X.Ψ => GramSchmidtSelfImaginary.gs_exists (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (Y := Y τ)
    (hind := hYind τ) (horth := hYorth τ) (hpos := hYpos τ) (hneg := hYneg τ) X.Gm_herm
  choose g hg1 hg2 hg3 hg4 using hgs
  have hgf : ∀ τ k, g τ k ∈ Submodule.span ℂ (Set.range (f τ)) := by
    intro τ k
    have hsub : Submodule.span ℂ (Set.range (Y τ)) ≤ Submodule.span ℂ (Set.range (f τ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hYU τ j
    exact hsub (hg3 τ k)
  have e0 : ∀ τ : X.Ψ, ∀ k, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (f τ k) = 0 := fun τ k => by
    rw [← hermC_conj τ.1 X.Gm_herm, ((hf τ).1 k).1, map_zero]
  have eP : ∀ τ : X.Ψ, ∀ k, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (X.ppos z0 τ (f τ k)) = 0 := fun τ k => by
    refine hermC_ppos_eq_zero_of_hermC_eq_zero_of_Jt X.toData z0 τ _ _ (e0 τ k) ?_
    rw [(hf τ).2.1 k, hermC_smul_right, e0 τ k, mul_zero]
  have hspan : ∀ τ : X.Ψ, ∀ y ∈ Submodule.span ℂ (Set.range (f τ)),
      hermC τ.1 X.Gm y (Data.emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm y (X.ppos z0 τ (Data.emb τ.1 ξ)) = 0 := by
    intro τ y hy
    refine ⟨GramSchmidtSelfImaginary.perp_span (τ := τ.1) (G := X.Gm) ?_ y hy,
      GramSchmidtSelfImaginary.perp_span (τ := τ.1) (G := X.Gm) ?_ y hy⟩
    · rintro _ ⟨k, rfl⟩
      exact ((hf τ).1 k).1
    · rintro _ ⟨k, rfl⟩
      rw [← ppos_self_adjoint_hermC, ← hermC_conj τ.1 X.Gm_herm, eP τ k, map_zero]
  have hJspan : ∀ τ : X.Ψ, ∀ y ∈ Submodule.span ℂ (Set.range (f τ)),
      hermC τ.1 X.Gm (I • ((2 : ℂ) • X.ppos z0 τ y - y)) (Data.emb τ.1 ξ) = 0 := by
    intro τ y hy
    rw [hermC_smul_left, hermC_sub_left_eq_sub, hermC_smul_left, ppos_self_adjoint_hermC, (hspan τ y hy).1,
      (hspan τ y hy).2]
    simp
  refine ⟨fun τ => EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro τ u w
    exact EigenframeMatrices.Mmat_unitary (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1)
      (hgf τ) (hg1 τ) u w
  · intro s t
    funext τ
    simp only [Data.applyV]
    refine EigenframeMatrices.Mmat_fix (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1) _
      (fun k => ?_)
    simp only [Pi.add_apply, Data.lineV, Data.Jz]
    simp only [hermC_add_left, hermC_smul_left, hermC_sub_left_eq_sub, ppos_self_adjoint_hermC, e0, eP,
      mul_zero, sub_zero, add_zero, zero_add]
  · intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hmem : ∀ τ : X.Ψ, EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ)
        (g := g τ) *ᵥ u τ ∈ Submodule.span ℂ (Set.range (f τ)) := fun τ =>
      EigenframeMatrices.Mmat_span (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1) (hgf τ)
        (u τ) ((hf τ).2.2.2.2 (u τ) (hu1 τ) (hu2 τ))
    exact And.intro (fun τ => (hspan τ _ (hmem τ)).1) (fun τ => hJspan τ _ (hmem τ))
  · intro τ v hv
    have hle : Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) ≤
        (Submodule.span ℂ (Y τ '' {j | (j : ℕ) < X.p0 - 1})).comap
          (Matrix.mulVecLin (EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ)
            (g := g τ))) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply,
        EigenframeMatrices.Mmat_f (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1)]
      exact hg2 τ k hk
    have hv' := hle hv
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv'
  · intro τ j
    obtain ⟨β, hβ, hYj⟩ := hg4 τ j
    refine ⟨∑ c, β c • f τ c, GramSchmidtSelfImaginary.sum_mem_of (f τ) _ β hβ, ?_⟩
    show EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) *ᵥ
      (∑ c, β c • f τ c) = Y τ j
    rw [EigenframeMatrices.Mmat_comb (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1), hYj]

end

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LowerBlockMatrices
section
namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Amat (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  Matrix.of fun b' b => hermC τ.1 X.Gm (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b))
    (col (mat x0 τ) (Fin.castLE X.p0_le b'))

def Bmat (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  Matrix.of fun a b => -hermC τ.1 X.Gm (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b))
    (col (mat x0 τ) (kap X.p0_le a))

lemma col_mul' (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * B) a = A *ᵥ col B a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma mulVec_eq_sum_col (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) : M *ᵥ w = ∑ c, w c • col M c := by
  funext k
  simp only [Matrix.mulVec, dotProduct, col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ ↦ mul_comm _ _

lemma yvec_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    ∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) =
      h1 τ *ᵥ ∑ b, u b • col (mat z0 τ) (Fin.castLE X.p0_le b) := by
  simp only [col_mul', Matrix.mulVec_sum, Matrix.mulVec_smul]

private lemma hermC_sum_smul_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ}
    (c : Fin m → ℂ) (y : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ b, c b • y b) v = ∑ b, c b * hermC τ G (y b) v := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b' _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

lemma Pos_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    Pos X x0 τ (∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) =
      ∑ b', ‖(Amat X h1 z0 x0 τ *ᵥ u) b'‖ ^ 2 := by
  unfold Pos
  refine Finset.sum_congr rfl fun b' _ ↦ ?_
  have h : (Amat X h1 z0 x0 τ *ᵥ u) b' = ∑ b, u b * hermC τ.1 X.Gm
      (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) (col (mat x0 τ) (Fin.castLE X.p0_le b')) := by
    simp only [Matrix.mulVec, dotProduct, Amat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  rw [hermC_sum_smul_left', h]

lemma Neg_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    Neg X x0 τ (∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) =
      ∑ a, ‖(Bmat X h1 z0 x0 τ *ᵥ u) a‖ ^ 2 := by
  unfold PositiveSpanMatrices.Neg
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have h : (Bmat X h1 z0 x0 τ *ᵥ u) a = -∑ b, u b * hermC τ.1 X.Gm
      (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) (col (mat x0 τ) (kap X.p0_le a)) := by
    simp only [Matrix.mulVec, dotProduct, Bmat, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  rw [hermC_sum_smul_left', h, norm_neg]

lemma colW_expand (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 : Frame X.Ψ r) {x0 : Frame X.Ψ r}
    (hortho : X.IsOrtho x0) (τ : X.Ψ) (hdet0 : (mat x0 τ).det ≠ 0) (b : Fin X.p0) :
    col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) =
      ∑ b', Amat X h1 z0 x0 τ b' b • col (mat x0 τ) (Fin.castLE X.p0_le b') +
        ∑ a, Bmat X h1 z0 x0 τ a b • col (mat x0 τ) (kap X.p0_le a) := by
  classical
  set y := col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) with hy
  set α := (mat x0 τ)⁻¹ *ᵥ y with hα
  have hyα : y = ∑ c, α c • col (mat x0 τ) c := by
    rw [← mulVec_eq_sum_col, hα, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet0), Matrix.one_mulVec]
  have hcd : ∀ c d, hermC τ.1 X.Gm (col (mat x0 τ) c) (col (mat x0 τ) d) =
      if c = d then ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) else 0 := by
    intro c d
    have := congrFun (congrFun (hortho τ) c) d
    simpa [gram, Matrix.diagonal_apply] using this
  have hh : ∀ d, hermC τ.1 X.Gm y (col (mat x0 τ) d) = α d * ((sgn X.p0 (d : ℕ) : ℝ) : ℂ) := by
    intro d
    rw [hyα, hermC_sum_smul_left']
    simp only [hcd, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  rw [hyα, sum_split X.p0_le]
  congr 1
  · refine Finset.sum_congr rfl fun b' _ ↦ ?_
    congr 1
    simp only [Amat, Matrix.of_apply]
    rw [← hy, hh]
    have hb' := b'.isLt
    simp [sgn, hb']
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    congr 1
    simp only [Bmat, Matrix.of_apply]
    rw [← hy, hh, show sgn X.p0 (kap X.p0_le a : ℕ) = -1 by simp [sgn, kap]]
    push_cast
    ring

lemma lowBlock_castLE (Z : X.Coord) (τ : X.Ψ) (b' b : Fin X.p0) :
    X.lowBlock Z τ (Fin.castLE X.p0_le b') (Fin.castLE X.p0_le b) = if b' = b then 1 else 0 := by
  have hb' := b'.isLt
  simp only [Data.lowBlock, Matrix.of_apply, Fin.castLE_inj, Fin.coe_castLE]
  rw [dite_eq_right (by omega)]
  simp

lemma lowBlock_kap (Z : X.Coord) (τ : X.Ψ) (a : Fin (r - X.p0)) (b : Fin X.p0) :
    X.lowBlock Z τ (kap X.p0_le a) (Fin.castLE X.p0_le b) = Z τ a b := by
  simp only [Data.lowBlock, Matrix.of_apply, if_neg (kap_ne_castLE X.p0_le a b), zero_add]
  rw [dite_eq_left ⟨by simp [kap], by simp [b.isLt]⟩]
  exact congrArg₂ (Z τ) (Fin.ext (by simp [kap])) (Fin.ext (by simp))

lemma colZ (x0 : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (b : Fin X.p0) :
    col (mat (X.xZ x0 Z) τ) (Fin.castLE X.p0_le b) =
      col (mat x0 τ) (Fin.castLE X.p0_le b) + ∑ a, Z τ a b • col (mat x0 τ) (kap X.p0_le a) := by
  classical
  have hm : mat (X.xZ x0 Z) τ = mat x0 τ * X.lowBlock Z τ := rfl
  have hc : ∀ c k, col (X.lowBlock Z τ) c k = X.lowBlock Z τ k c := fun _ _ ↦ rfl
  rw [hm, col_mul', mulVec_eq_sum_col, sum_split X.p0_le]
  simp only [hc, lowBlock_castLE, lowBlock_kap, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

end

end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma sum_castLE_lemma {r k : ℕ} (hk : k ≤ r) (f : Fin r → ℂ)
    (hf : ∀ j : Fin r, k ≤ (j : ℕ) → f j = 0) : ∑ j, f j = ∑ j : Fin k, f (Fin.castLE hk j) := by
  have hr : r = k + (r - k) := (Nat.add_sub_cancel' hk).symm
  rw [← Equiv.sum_comp (finCongr hr.symm), Fin.sum_univ_add]
  have h2 : ∑ a : Fin (r - k), f (finCongr hr.symm (Fin.natAdd k a)) = 0 :=
    Finset.sum_eq_zero fun a _ => hf _ (by simp)
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun j _ => congrArg f (Fin.ext (by simp))

lemma rmul_mem_dom {z b : Frame X.Ψ r} (hz : z ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul z b ∈ X.dom := by
  intro τ
  obtain ⟨hz1, hz2⟩ := hz τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hmat : mat (rmul z b) τ = mat z τ * mat b τ := rfl
  have hgram : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      gram τ.1 X.Gm M = Mᵀ * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    intro M
    ext a c
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hprod : gram τ.1 X.Gm (mat z τ * mat b τ) =
      (mat b τ)ᵀ * gram τ.1 X.Gm (mat z τ) * (mat b τ).map (starRingEnd ℂ) := by
    rw [hgram, hgram, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have htri : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), (∀ a c : Fin n, c < a → M a c = 0) →
      M.det = ∏ a, M a a :=
    fun n M h => Matrix.det_of_upperTriangular (fun a c hca => h a c hca)
  have hdiag : ∀ a, mat b τ a a ≠ 0 := by
    have h0 := hb1
    rw [htri r (mat b τ) hb2] at h0
    exact fun a => Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)
  refine ⟨by rw [hmat, Matrix.det_mul]; exact mul_ne_zero hz1 hb1, fun i => ?_⟩
  have hk : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hsub : ((mat b τ)ᵀ * gram τ.1 X.Gm (mat z τ) * (mat b τ).map (starRingEnd ℂ)).submatrix
        (Fin.castLE hk) (Fin.castLE hk) =
      ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk))ᵀ *
        (gram τ.1 X.Gm (mat z τ)).submatrix (Fin.castLE hk) (Fin.castLE hk) *
        ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).map (starRingEnd ℂ) := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine (sum_castLE_lemma hk _ ?_).trans (Finset.sum_congr rfl fun l _ => ?_)
    · intro l hl
      have hc := c.isLt
      have h0 : mat b τ l (Fin.castLE hk c) = 0 :=
        hb2 l (Fin.castLE hk c) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      exact mul_eq_zero_of_right _ ((map_eq_zero _).mpr h0)
    · refine congrArg (fun s => s * _) (sum_castLE_lemma hk _ ?_)
      intro j hj
      have ha := a.isLt
      have h0 : mat b τ j (Fin.castLE hk a) = 0 :=
        hb2 j (Fin.castLE hk a) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      exact mul_eq_zero_of_left h0 _
  set d := ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det with hd
  have hdne : d ≠ 0 := by
    rw [hd, htri (i : ℕ) ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk))
      (fun a c h => hb2 _ _ (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]; exact h))]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hdiag (Fin.castLE hk a)
  have hdetmap : (((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).map (starRingEnd ℂ)).det =
      starRingEnd ℂ d := by
    rw [hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hclaim : dmin X.Gm (rmul z b) τ i = ((Complex.normSq d : ℝ) : ℂ) * dmin X.Gm z τ i := by
    unfold dmin lminor
    rw [hmat, hprod, hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetmap, ← hd,
      mul_right_comm, Complex.mul_conj]
  rw [hclaim, Complex.re_ofReal_mul]
  have hpos : 0 < Complex.normSq d := Complex.normSq_pos.mpr hdne
  calc (0 : ℝ) < Complex.normSq d * (psgn X.p0 i * (dmin X.Gm z τ i).re) := mul_pos hpos (hz2 i)
    _ = _ := by ring

lemma opN_smul_le {m n : ℕ} (t : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Data.opN (t • A) ≤ ‖t‖ * Data.opN A := by
  unfold Data.opN
  have key : ∀ v : Fin n → ℂ,
      Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2) =
        ‖t‖ * (Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)) := by
    intro v
    have h1 : ∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2 = ‖t‖ ^ 2 * ∑ i, ‖Matrix.mulVec A v i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmv : Matrix.mulVec (t • A) v i = t * Matrix.mulVec A v i := by
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [hmv, norm_mul, mul_pow]
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg t), mul_div_assoc]
  open scoped Pointwise in
  have hS : {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} =
      ‖t‖ • {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
    ext s
    simp only [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨_, ⟨v, hv, rfl⟩, ?_⟩
      rw [smul_eq_mul, key v]
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by rw [smul_eq_mul, key v]⟩
  refine le_of_eq ?_
  rw [hS, Real.sSup_smul_of_nonneg (norm_nonneg t), smul_eq_mul]

private lemma opN_nonneg' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ Data.opN A := by
  unfold Data.opN
  apply Real.sSup_nonneg
  rintro s ⟨v, _, rfl⟩
  positivity

lemma zN_nonneg (Z : X.Coord) : 0 ≤ X.zN Z := by
  unfold Data.zN
  exact Real.iSup_nonneg fun τ => opN_nonneg' _

lemma zN_smul_le (t : ℂ) (Z : X.Coord) : X.zN (t • Z) ≤ ‖t‖ * X.zN Z := by
  unfold Data.zN
  refine Real.iSup_le (fun τ => ?_) (mul_nonneg (norm_nonneg t) (zN_nonneg X Z))
  have h1 : Data.opN (Matrix.of ((t • Z) τ)) ≤ ‖t‖ * Data.opN (Matrix.of (Z τ)) :=
    opN_smul_le t (Matrix.of (Z τ))
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg t))
  exact le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ

lemma xZ_diff (x : Frame X.Ψ r) : Differentiable ℂ fun Z : X.Coord => X.xZ x Z := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hL : ∀ j, Differentiable ℂ fun Z : X.Coord => X.lowBlock Z τ j b := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  show Differentiable ℂ fun Z : X.Coord => ∑ j, mat x τ a j * X.lowBlock Z τ j b
  first
    | exact Differentiable.fun_sum (fun j _ => (hL j).const_mul _)
    | exact Differentiable.sum (fun j _ => (hL j).const_mul _)

lemma xZ_zero (x : Frame X.Ψ r) : X.xZ x 0 = x := by
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  show mat x τ * X.lowBlock 0 τ = x τ
  rw [h1, Matrix.mul_one]
  rfl

lemma exp_small : Real.exp (1 / 25) < 3 / 2 := by
  by_contra hcon
  push_neg at hcon
  have h25 : Real.exp 1 = Real.exp (1 / 25) ^ 25 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (3 / 2 : ℝ) ^ 25 ≤ Real.exp (1 / 25) ^ 25 := pow_le_pow_left₀ (by norm_num) hcon 25
  have he := Real.exp_one_lt_d9
  norm_num at hpow
  linarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
end

