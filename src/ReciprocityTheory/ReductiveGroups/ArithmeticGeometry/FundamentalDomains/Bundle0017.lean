module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientLattice

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CompactEntryBounds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace CompactEntryBounds

open Matrix NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  have hcc : ∀ x : E, τ (cc x) = conj (τ x) := fun x =>
    NumberField.IsCMField.complexEmbedding_complexConj E τ x
  have hL : ∀ a b, ((P.map τ) *ᵥ u) a * τ (X.Gm a b) * conj (((P.map τ) *ᵥ w) b) =
      ∑ k, ∑ l, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := by
    intro a b
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    ring
  have hR : ∀ k l, u k * conj (w l) *
      τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) = ∑ a, ∑ b, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := by
    intro k l
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, Matrix.mulVec_single_one, Matrix.transpose_apply, map_sum, map_mul, hcc,
      Finset.mul_sum]
    rfl
  simp only [hermC, hL, hR]
  calc _ = ∑ a, ∑ k, ∑ b, ∑ l, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, ∑ l, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ l, ∑ b, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w := by
  rw [hermC_expand X τ γ u w]
  have h1 := hermC_expand X τ 1 u w
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.one_mulVec, Matrix.one_mulVec] at h1
  rw [h1]
  simp only [hγ, Matrix.one_mulVec]

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : gram τ X.Gm (γ.map τ * Y) = gram τ X.Gm Y := by
  have hc : ∀ a, col (γ.map τ * Y) a = (γ.map τ) *ᵥ col Y a := fun a => by
    funext k
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext a b
  simp only [gram, Matrix.of_apply, hc, hermC_stab X hγ τ]

theorem inv_lact (γ : GL (Fin r) E) (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ * Y)⁻¹ *ᵥ Data.emb τ v =
      Y⁻¹ *ᵥ Data.emb τ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  have hinv : ((γ : Matrix (Fin r) (Fin r) E).map τ)⁻¹ =
      ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero τ) (map_one τ)]
  rw [Matrix.mul_inv_rev, hinv, ← Matrix.mulVec_mulVec]
  congr 1
  funext a
  exact (RingHom.map_mulVec τ _ v a).symm

private theorem gram_eq_transpose_mul_map_mul_fundamental_domains (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm Y = Yᵀ * X.Gm.map τ * (Yᴴ)ᵀ := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, Complex.star_def]
  exact Finset.sum_comm

theorem entry_bound {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0)
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (l b : Fin r) :
    ‖Y l b‖ ≤ ∑ k, ‖(X.Gm.map τ)⁻¹ k l‖ * ‖Y⁻¹ b k‖ := by
  set d : Fin r → ℂ := fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hd_def
  have hA : (X.Gm.map τ).det ≠ 0 := by
    have h := RingHom.map_det τ X.Gm
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (map_ne_zero τ).2 X.Gm_det
  have e1 : Yᵀ * X.Gm.map τ * (Yᴴ)ᵀ = diagonal d := by
    rw [← gram_eq_transpose_mul_map_mul_fundamental_domains, hg]
  have e2 := congrArg Matrix.transpose e1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    ← Matrix.mul_assoc] at e2
  have hYH : IsUnit (Yᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.2 (star_ne_zero.2 hY)
  have hAT : IsUnit (X.Gm.map τ)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 hA
  have e3 : Y = ((X.Gm.map τ)ᵀ)⁻¹ * (Yᴴ)⁻¹ * diagonal d := by
    rw [← e2]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc ((X.Gm.map τ)ᵀ)⁻¹ (Yᴴ)⁻¹ Yᴴ, Matrix.nonsing_inv_mul _ hYH, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hAT, Matrix.one_mul]
  have e4 : Y l b = (∑ k, (X.Gm.map τ)⁻¹ k l * star (Y⁻¹ b k)) * d b := by
    conv_lhs => rw [e3]
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply, ← Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_apply]
  have hdb : ‖d b‖ = 1 := by
    rw [hd_def, Complex.norm_real]
    unfold sgn
    split_ifs <;> norm_num
  rw [e4, norm_mul, hdb, mul_one]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_star]

theorem comp_le_Qy (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) (p : Fin r → E) (b : Fin r) :
    X.c τ * ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) b‖ ^ 2 ≤ QuadraticLatticeForms.Qy X y p := by
  unfold QuadraticLatticeForms.Qy
  have hc : ∀ τ' : X.Ψ, 0 ≤ X.c τ' := fun τ' => by unfold Data.c; positivity
  calc X.c τ * ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) b‖ ^ 2
      ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum
          (f := fun a => ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) (fun a _ => by positivity)
          (Finset.mem_univ b)) (hc τ)
    _ ≤ _ := Finset.single_le_sum
          (f := fun τ' => X.c τ' * ∑ a, ‖((y τ')⁻¹ *ᵥ Data.emb τ'.1 p) a‖ ^ 2)
          (fun τ' _ => mul_nonneg (hc τ') (by positivity)) (Finset.mem_univ τ)

theorem comb_bound (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) {ι : Type} [Fintype ι]
    (q : ι → ℚ) (f : ι → Fin r → E) (b : Fin r) :
    ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (∑ i, q i • f i)) b‖ ≤
      ∑ i, ‖(q i : ℂ)‖ * (1 + QuadraticLatticeForms.Qy X y (f i) / X.c τ) := by
  have hcpos : 0 < X.c τ := by
    unfold Data.c
    have := (map_ne_zero τ.1).2 X.ξ0_ne
    positivity
  have hemb : Data.emb τ.1 (∑ i, q i • f i) = ∑ i, (q i : ℂ) • Data.emb τ.1 (f i) := by
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Data.emb, map_sum, Finset.sum_apply, Rat.smul_def, map_mul, map_ratCast]
  have hlin : ((y τ)⁻¹ *ᵥ Data.emb τ.1 (∑ i, q i • f i)) b =
      ∑ i, (q i : ℂ) * ((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b := by
    rw [hemb, Matrix.mulVec_sum, Finset.sum_apply]
    simp [Matrix.mulVec_smul]
  rw [hlin]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := comp_le_Qy X y τ (f i) b
  have h2 : ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b‖ ^ 2 ≤ QuadraticLatticeForms.Qy X y (f i) / X.c τ := by
    rw [le_div_iff₀ hcpos]
    linarith
  nlinarith [sq_nonneg (‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b‖ - 1)]

def Kset (R : ℝ) : Set (Frame X.Ψ r) :=
  {w | ∀ τ : X.Ψ, gram τ.1 X.Gm (mat w τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ a c, ‖w τ a c‖ ≤ R}

theorem cont_gram' (τ : X.Ψ) : Continuous fun w : Frame X.Ψ r => gram τ.1 X.Gm (mat w τ) := by
  apply continuous_matrix
  intro a b
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

theorem Kset_compact (R : ℝ) : IsCompact (Kset X R) := by
  have hcl : IsClosed (Kset X R) := by
    have : Kset X R = ⋂ τ : X.Ψ, ({w : Frame X.Ψ r | gram τ.1 X.Gm (mat w τ) =
        diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))} ∩
        ⋂ a, ⋂ c, {w : Frame X.Ψ r | ‖w τ a c‖ ≤ R}) := by
      ext w
      simp only [Kset, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [this]
    refine isClosed_iInter fun τ => (isClosed_eq (cont_gram' X τ) continuous_const).inter
      (isClosed_iInter fun a => isClosed_iInter fun c => isClosed_le (by fun_prop) continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := max R 0)).subset ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a =>
      (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun c =>
        ((hw τ).2 a c).trans (le_max_left _ _)

theorem det_ne_of_gram {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} {p0 : ℕ}
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det hg
  rw [gram_eq_transpose_mul_map_mul_fundamental_domains, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul,
    zero_mul, Matrix.det_diagonal] at h
  refine absurd h.symm (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
  rw [ne_eq, Complex.ofReal_eq_zero]
  unfold sgn
  split_ifs <;> norm_num

theorem Kset_sub (R : ℝ) : Kset X R ⊆ X.dom := by
  intro w hw
  refine (X.mem_dom_iff w).2 fun τ => ?_
  have hg := (hw τ).1
  refine ⟨det_ne_of_gram X hg, fun i => ?_⟩
  have hd : dmin X.Gm w τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    rw [dmin, hg, lminor, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
      Matrix.det_diagonal, psgn, Complex.ofReal_prod]
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 := by
    unfold psgn
    exact Finset.prod_ne_zero_iff.2 fun a _ => by unfold sgn; split_ifs <;> norm_num
  exact mul_self_pos.2 hne

end CompactEntryBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FixedPointImaginarySpan
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
  ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)

lemma cc_mul'' (x y : E) : cc (x * y) = cc x * cc y := map_mul (IsCMField.complexConj E) x y

lemma im_of_fixed {a : E} (ha : cc a = a) (τ : E →+* ℂ) : (τ a).im = 0 := by
  have h : conj (τ a) = τ a := by
    rw [← NumberField.IsCMField.complexEmbedding_complexConj E τ a]
    exact congrArg τ ha
  exact Complex.conj_eq_iff_im.mp h

lemma span_Lc (hg : 0 < g) :
    Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) = ⊤ := by
  set Sp := Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) with hSp
  have hsub : ∀ b ∈ X.LZ g, kap b ∈ Sp := fun b hb =>
    Submodule.subset_span ((mem_Lc X g).2 ⟨b, hb, rfl⟩)
  have hcr := cr_pos (E := E) g hg
  have hposition : ∀ (i0 k0 : Fin 2), (∀ a : E, cc a = a → IsIntegral ℤ a →
      intersection_update_fsHerm_neg_one i0 k0 (cr (E := E) g • fun τ : X.Ψ => (τ.1 a).re) ∈ Sp) → ∀ p, intersection_update_fsHerm_neg_one i0 k0 p ∈ Sp := by
    intro i0 k0 h p
    have := span_gen X g ((intersection_update_fsHerm_neg_one i0 k0).comp (cr (E := E) g • LinearMap.id)) (fun a ha hai => by
      simpa using h a ha hai) ((cr (E := E) g)⁻¹ • p)
    simpa [smul_smul, inv_mul_cancel₀ hcr.ne'] using this
  have h00 : ∀ p, intersection_update_fsHerm_neg_one 0 0 p ∈ Sp := hposition 0 0 fun a ha hai => by
    have hm := mem_LZ_of X g !![a, 0; 0, 0]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]
  have h11 : ∀ p, intersection_update_fsHerm_neg_one 1 1 p ∈ Sp := hposition 1 1 fun a ha hai => by
    have hm := mem_LZ_of X g !![0, 0; 0, a]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]
  have h01 : ∀ p, intersection_update_fsHerm_neg_one 0 1 p ∈ Sp := hposition 0 1 fun a ha hai => by
    have hm := mem_LZ_of X g !![0, a; a, 0]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE, im_of_fixed ha]
  obtain ⟨η, hηcc, hηi, hηne⟩ : ∃ η : E, cc η = -η ∧ IsIntegral ℤ η ∧ η ≠ 0 := by
    have halg : IsAlgebraic ℤ X.ξ0 :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic X.ξ0)
    obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
    refine ⟨k • X.ξ0, ?_, hki, smul_ne_zero hk X.ξ0_ne⟩
    rw [show cc (k • X.ξ0) = k • cc X.ξ0 from map_zsmul _ k _, X.ξ0_im, smul_neg]
  have hre : ∀ τ : E →+* ℂ, (τ η).re = 0 := fun τ => by
    have h := emb_cc' τ η
    rw [hηcc, map_neg] at h
    have := congrArg Complex.re h
    simp at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ η).im ≠ 0 := fun τ h => by
    have : τ η = 0 := Complex.ext (hre τ) h
    exact hηne ((map_eq_zero τ).1 this)
  have h10 : ∀ p, intersection_update_fsHerm_neg_one 1 0 p ∈ Sp := by
    set D : (X.Ψ → ℝ) →ₗ[ℝ] (X.Ψ → ℝ) :=
      LinearMap.pi fun τ : X.Ψ => (cr (E := E) g * (τ.1 η).im) • LinearMap.proj τ with hD
    have hDapp : ∀ q τ, D q τ = cr (E := E) g * (τ.1 η).im * q τ := fun q τ => by simp [hD]
    have key : ∀ q, (intersection_update_fsHerm_neg_one 1 0).comp D q ∈ Sp := span_gen X g _ fun a ha hai => by
      have hm := mem_LZ_of X g !![0, η * a; -(η * a), 0]
        (fun i k => by
          fin_cases i <;> fin_cases k <;>
            simp [ha, RealEmbeddingCharacters.cc_zero', cc_mul'', hηcc, RealEmbeddingCharacters.cc_neg'])
        (fun i k => by fin_cases i <;> fin_cases k <;> simp [(hηi.mul hai), (hηi.mul hai).neg, isIntegral_zero])
      convert hsub _ hm using 1
      funext τ i k
      rw [LinearMap.comp_apply]
      fin_cases i <;> fin_cases k <;>
        simp [kap, position_apply, Data.embH, emb_cE, hDapp, Complex.mul_re, Complex.mul_im, hre,
          im_of_fixed ha]
      ring
    intro p
    have e : D (fun τ => p τ / (cr (E := E) g * (τ.1 η).im)) = p := by
      funext τ
      rw [hDapp]
      have : cr (E := E) g * (τ.1 η).im ≠ 0 := mul_ne_zero hcr.ne' (him τ.1)
      field_simp [him τ.1]
    have := key (fun τ => p τ / (cr (E := E) g * (τ.1 η).im))
    rwa [LinearMap.comp_apply, e] at this
  refine eq_top_iff.2 fun y _ => ?_
  rw [sum_position y]
  refine Submodule.sum_mem _ fun i0 _ => Submodule.sum_mem _ fun k0 _ => ?_
  fin_cases i0 <;> fin_cases k0
  exacts [h00 _, h01 _, h10 _, h11 _]

theorem exists_basis (hg : 0 < g) : ∃ ω, X.IsLZBasis g ω := by
  have : Fact (0 < g) := ⟨hg⟩
  have : IsZLattice ℝ (Lc X g) := ⟨span_Lc X g hg⟩
  have := ZLattice.module_free ℝ (Lc X g)
  have := ZLattice.module_finite ℝ (Lc X g)
  have hrank : Module.finrank ℤ (Lc X g) = 4 * Fintype.card X.Ψ := by
    rw [ZLattice.rank ℝ (Lc X g), finrank_rfam]
  set bZ := Module.finBasisOfFinrankEq ℤ (Lc X g) hrank
  set eR := bZ.ofZLatticeBasis ℝ (Lc X g)
  have heR : ∀ j, eR j = (bZ j : X.Ψ → Fin 2 → Fin 2 → ℝ) := fun j =>
    bZ.ofZLatticeBasis_apply ℝ (Lc X g) j
  have hthinj : LinearMap.ker (thL : (X.Ψ → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] _) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro z z' h
    rw [← kap_th z, ← kap_th z']
    exact congrArg kap h
  have hli : LinearIndependent ℝ (fun j => th (eR j)) := eR.linearIndependent.map' thL hthinj
  have hc : ∀ (m : ℤ) (v : X.Ψ → Fin 2 → Fin 2 → ℂ), (m : ℂ) • v = (m : ℝ) • v := fun m v => by
    rw [← Complex.ofReal_intCast, Complex.coe_smul]
  refine ⟨fun j => th (eR j), fun j => ?_, fun b hb => ?_, hli⟩
  · obtain ⟨b, hb, hkb⟩ := (mem_Lc X g).1 (show eR j ∈ Lc X g by rw [heR]; exact (bZ j).2)
    show th (eR j) ∈ X.LZ g
    rw [← hkb, th_kap (herm_of_LZ X g hb)]
    exact hb
  · have hmem : kap b ∈ Lc X g := (mem_Lc X g).2 ⟨b, hb, rfl⟩
    set n := bZ.repr ⟨kap b, hmem⟩
    have h1 := congrArg Subtype.val (bZ.sum_repr ⟨kap b, hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h1
    have hb' : b = ∑ j, (n j : ℂ) • th (eR j) := by
      calc b = thL (kap b) := (th_kap (herm_of_LZ X g hb)).symm
        _ = thL (∑ j, ((n j : ℝ)) • eR j) := by
            congr 1
            rw [← h1]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [heR, Int.cast_smul_eq_zsmul]
        _ = ∑ j, (n j : ℂ) • th (eR j) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, hc]
            rfl
    refine ⟨n, hb', fun n' hn' => ?_⟩
    have e : ∑ j, (n' j : ℝ) • th (eR j) = ∑ j, (n j : ℝ) • th (eR j) := by
      have := hn'.symm.trans hb'
      simpa only [hc] using this
    have hz := Fintype.linearIndependent_iff.1 hli (fun j => (n' j : ℝ) - n j) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [e, sub_self])
    funext j
    have := sub_eq_zero.1 (hz j)
    exact_mod_cast this

end

end ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan
end

