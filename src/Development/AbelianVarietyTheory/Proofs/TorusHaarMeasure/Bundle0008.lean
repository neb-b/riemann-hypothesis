module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.AbsNormEqProdCmTypeSq
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem abs_norm_eq_prod_cmType_sq :
    (∀ (r : ℕ) (X : Data E r) (z : E), ((|Algebra.norm ℚ z| : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2) := by
  classical
  intro r X z

  have hall : ((Algebra.norm ℚ z : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ z := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), Algebra.norm_eq_prod_embeddings ℚ ℂ z]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl)

  have hcompl : ∏ σ ∈ X.Ψᶜ, σ z = ∏ τ ∈ X.Ψ, (starRingEnd ℂ) (τ z) := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      have h := X.cmType (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at h
      exact h.mpr (Finset.mem_compl.mp hσ)
    · intro τ hτ
      exact Finset.mem_compl.mpr ((X.cmType τ).mp hτ)
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro τ _
      exact ComplexEmbedding.involutive_conjugate E τ
    · intro σ _
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  have hC : ((Algebra.norm ℚ z : ℚ) : ℂ) = ((∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hall, ← Finset.prod_mul_prod_compl X.Ψ, hcompl, ← Finset.prod_mul_distrib,
      Finset.prod_coe_sort X.Ψ (fun τ => ‖τ z‖ ^ 2), Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    rw [RCLike.mul_conj]
    push_cast
    rfl
  have hR : ((Algebra.norm ℚ z : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_ratCast]
    exact hC
  have hnn : (0 : ℚ) ≤ Algebra.norm ℚ z := by
    have h0 : (0 : ℝ) ≤ ((Algebra.norm ℚ z : ℚ) : ℝ) := by
      rw [hR]
      positivity
    exact_mod_cast h0
  rw [abs_of_nonneg hnn, hR]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetMulStrictLowerEqOne
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem det_mul_strictLower_eq_one (r : ℕ) (N : Matrix (Fin r) (Fin r) ℂ)
    (h0 : ∀ a c : Fin r, a < c → N a c = 0) (h1 : ∀ a, N a a = 1) :
    (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} =>
      if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0).det = 1 := by
  letI L : LinearOrder {p : Fin r × Fin r // p.2 < p.1} :=
    LinearOrder.lift' (fun p => toLex p.1) (fun p q h => Subtype.ext (toLex.injective h))
  have key := @Matrix.det_of_lowerTriangular {p : Fin r × Fin r // p.2 < p.1} ℂ _ _ _ L
    (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} =>
      if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0) (by
      intro p q hpq
      have hlt : toLex p.1 < toLex q.1 := hpq
      rw [Matrix.of_apply]
      split_ifs with h
      · rcases Prod.Lex.toLex_lt_toLex.1 hlt with h2 | ⟨_, h3⟩
        · exact h0 _ _ h2
        · exact absurd h (ne_of_lt h3)
      · rfl)
  rw [key]
  simp [h1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate

namespace GlobalTheory.UnitaryFrames

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
lemma hermC_eq_dot {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ star w) := by
  simp only [hermC, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply,
    mul_assoc, RCLike.star_def]

omit [NumberField E] [IsCMField E] in
lemma gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * (G.map τ * P.map (starRingEnd ℂ)) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc]

omit [NumberField E] [IsCMField E] in
lemma hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    hermC τ G (P *ᵥ u) (P *ᵥ w) = u ⬝ᵥ (gram τ G P *ᵥ star w) := by
  have h : star (P *ᵥ w) = P.map (starRingEnd ℂ) *ᵥ star w := by
    ext a
    simp [Matrix.mulVec, dotProduct]
  rw [hermC_eq_dot, gram_eq_mul, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

omit [NumberField E] [IsCMField E] in
lemma col_mul' {r : ℕ} (g P : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (g * P) a = g *ᵥ col P a := by
  ext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma det_ne_zero_of_isOrth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x)
    (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_diagonal] at h
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
  unfold sgn
  split_ifs <;> simp

def unitarySubgroup {r : ℕ} (X : Data E r) : Subgroup (X.Ψ → GL (Fin r) ℂ) where
  carrier := {g | X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)}
  one_mem' := by
    intro τ u w
    simp
  mul_mem' := by
    intro a b ha hb τ u w
    have h1 := ha τ ((b τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((b τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
    have h2 := hb τ u w
    simp only [Matrix.mulVec_mulVec] at h1
    simp only [Pi.mul_apply, Units.val_mul]
    exact h1.trans h2
  inv_mem' := by
    intro a ha τ u w
    have h1 := ha τ ((((a τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
      ((((a τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
    exact h1.symm

lemma isClosed_unitary {r : ℕ} (X : Data E r) :
    IsClosed {g : X.Ψ → GL (Fin r) ℂ | X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)} := by
  simp only [Data.IsUnitaryC, Set.setOf_forall]
  refine isClosed_iInter fun τ => isClosed_iInter fun u => isClosed_iInter fun w => ?_
  refine isClosed_eq ?_ continuous_const
  have hc : Continuous fun g : X.Ψ → GL (Fin r) ℂ => (g τ : Matrix (Fin r) (Fin r) ℂ) :=
    Units.continuous_val.comp (continuous_apply τ)
  simp only [hermC_eq_dot]
  exact (hc.matrix_mulVec continuous_const).dotProduct
    (continuous_const.matrix_mulVec (hc.matrix_mulVec continuous_const).star)

lemma locallyCompact_GL (r : ℕ) : LocallyCompactSpace (GL (Fin r) ℂ) := by
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

lemma secondCountable_GL (r : ℕ) : SecondCountableTopology (GL (Fin r) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

lemma isOrth_lmulC {r : ℕ} (X : Data E r) {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hn : X.IsUnitaryC n) {x : Frame X.Ψ r} (hx : IsOrth X x) : IsOrth X (X.lmulC n x) := by
  intro τ
  rw [← hx τ, show mat (X.lmulC n x) τ = n τ * mat x τ from rfl]
  ext a b
  simp only [gram, Matrix.of_apply, col_mul', hn τ]

noncomputable def toGL {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    X.Ψ → GL (Fin r) ℂ :=
  fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (mat x τ) (det_ne_zero_of_isOrth X hx τ)

lemma val_toGL {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    (toGL X hx τ : Matrix (Fin r) (Fin r) ℂ) = mat x τ := rfl

lemma quotient_unitary {r : ℕ} (X : Data E r) {x y : Frame X.Ψ r} (hx : IsOrth X x)
    (hy : IsOrth X y) :
    X.IsUnitaryC fun τ => ((toGL X hx * (toGL X hy)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  intro τ u w
  have key : ∀ u w, hermC τ.1 X.Gm (mat x τ *ᵥ u) (mat x τ *ᵥ w) =
      hermC τ.1 X.Gm (mat y τ *ᵥ u) (mat y τ *ᵥ w) := by
    intro u w
    rw [hermC_mulVec, hermC_mulVec, hx τ, hy τ]
  have h := key ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
    ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
  rw [← val_toGL X hx, ← val_toGL X hy] at h
  simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
  simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  exact h

lemma continuous_toGL {r : ℕ} (X : Data E r) :
    Continuous fun x : {x : Frame X.Ψ r | IsOrth X x} => toGL X x.2 := by
  refine continuous_pi fun τ => ?_
  have hc : Continuous fun x : {x : Frame X.Ψ r | IsOrth X x} => mat x.1 τ :=
    (continuous_apply τ).comp continuous_subtype_val
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  have h : (fun x : {x : Frame X.Ψ r | IsOrth X x} =>
      (((toGL X x.2 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) =
      fun x => ((mat x.1 τ).det)⁻¹ • (mat x.1 τ).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, val_toGL, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hc.matrix_det.inv₀ fun x => det_ne_zero_of_isOrth X x.2 τ).smul hc.matrix_adjugate

theorem unitary_group_frames :
    ((∀ (r : ℕ) (X : Data E r), ∃ H : Subgroup (X.Ψ → GL (Fin r) ℂ), ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) ∧ (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → LocallyCompactSpace H ∧ SecondCountableTopology H ∧ ∀ x0, IsOrth X x0 → (∀ g : H, IsOrth X (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) ∧ ∃ ι : Frame X.Ψ r → H, ContinuousOn ι {x | IsOrth X x} ∧ (∀ x, IsOrth X x → X.lmulC (fun τ => ((ι x : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 = x) ∧ ∀ g : H, ι (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = g)) := by
  classical
  refine ⟨fun r X => ⟨unitarySubgroup X, fun g => Iff.rfl⟩, fun r X H hH => ?_⟩
  haveI := locallyCompact_GL r
  haveI := secondCountable_GL r
  have hcl : IsClosed (H : Set (X.Ψ → GL (Fin r) ℂ)) := by
    convert isClosed_unitary X using 1
    ext g
    exact hH g
  refine ⟨hcl.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, fun x0 hx0 => ?_⟩
  have horth : ∀ g : H, IsOrth X (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) :=
    fun g => isOrth_lmulC X ((hH _).1 g.2) hx0
  refine ⟨horth, fun x => if hx : IsOrth X x then
    ⟨toGL X hx * (toGL X hx0)⁻¹, (hH _).2 (quotient_unitary X hx hx0)⟩ else 1, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    refine continuous_induced_rng.2 ?_
    refine ((continuous_toGL X).mul (continuous_const (y := (toGL X hx0)⁻¹))).congr fun x => ?_
    have hx : IsOrth X x.1 := x.2
    simp only [Function.comp_apply, Set.restrict_apply, dif_pos hx]
    rfl
  · intro x hx
    simp only [dif_pos hx]
    funext τ
    change (((toGL X hx τ * (toGL X hx0 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (toGL X hx0 τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Units.val_mul, inv_mul_cancel_right, val_toGL]
  · intro g
    simp only [dif_pos (horth g)]
    apply Subtype.ext
    change toGL X (horth g) * (toGL X hx0)⁻¹ = g
    rw [mul_inv_eq_iff_eq_mul]
    funext τ
    exact Units.ext rfl

end GlobalTheory.UnitaryFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetOfBlockTriangularInjective
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem det_of_blockTriangular_injective {m α R : Type} [Fintype m] [DecidableEq m]
    [LinearOrder α] [CommRing R] (M : Matrix m m R) (f : m → α) (hf : Function.Injective f)
    (h : M.BlockTriangular f) : M.det = ∏ i, M i i := by
  letI : LinearOrder m := LinearOrder.lift' f hf
  exact Matrix.det_of_upperTriangular (M := M) (fun i j hij => h hij)

theorem prod_lowerPairs_fst {r : ℕ} (d : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, d p.1.1 = ∏ a, d a ^ (a : ℕ) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1)
    (by simp) (fun p => d p.1), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [← Fin.card_Iio a]
  congr 1
  ext c; simp

theorem prod_lowerPairs_snd {r : ℕ} (d : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, d p.1.2 = ∏ a, d a ^ (r - 1 - (a : ℕ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1)
    (by simp) (fun p => d p.2), Finset.prod_filter, Fintype.prod_prod_type_right]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [← Fin.card_Ioi a]
  congr 1
  ext c; simp

theorem det_conj_strictLower : (∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℂ), B.det ≠ 0 → (∀ a c : Fin r, c < a → B a c = 0) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2).det = ∏ a : Fin r, B a a ^ (2 * (a : ℤ) - ((r : ℤ) - 1))) := by
  intro r B hdet htri
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hu
  have hB : B.BlockTriangular id := fun a c h => htri a c h
  have hBi : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  have hdiag : ∀ a, B a a * B⁻¹ a a = 1 := by
    intro a
    have h1 : (B * B⁻¹) a a = 1 := by rw [Matrix.mul_nonsing_inv B hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · exact h1
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [htri a c h, zero_mul]
      · rw [hBi (i := c) (j := a) h, mul_zero]
    · simp
  have hne : ∀ a, B a a ≠ 0 := fun a => left_ne_zero_of_mul_eq_one (hdiag a)
  have hinv : ∀ a, B⁻¹ a a = (B a a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (hdiag a)
  rw [det_of_blockTriangular_injective _
    (fun p : {p : Fin r × Fin r // p.2 < p.1} => toLex (p.1.1, OrderDual.toDual p.1.2))]
  · simp only [Matrix.of_apply, hinv]
    rw [Finset.prod_mul_distrib, prod_lowerPairs_fst (fun a => B a a),
      prod_lowerPairs_snd (fun a => (B a a)⁻¹), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hne a)]
    congr 1
    have := a.2
    omega
  · intro p q h
    have h' := toLex.injective h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h'
    exact Subtype.ext (Prod.ext h'.1 h'.2)
  · intro p q h
    simp only [Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] at h
    rcases h with h | ⟨_, h⟩
    · simp [htri _ _ h]
    · simp [hBi (i := q.1.2) (j := p.1.2) h]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfHermOne
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix

namespace GlobalTheory.TwoLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E]




theorem two_mul_card_cmType {r : ℕ} (X : Data E r) : 2 * X.Ψ.card = Module.finrank ℚ E := by
  classical
  have hinv : Function.Involutive (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    ComplexEmbedding.involutive_conjugate E
  have hdisj : Disjoint X.Ψ (X.Ψ.image ComplexEmbedding.conjugate) := by
    rw [Finset.disjoint_left]
    intro τ hτ hτ'
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ'
    exact ((X.cmType σ).mp hσ) hτ
  have hunion : X.Ψ ∪ X.Ψ.image ComplexEmbedding.conjugate = Finset.univ := by
    ext τ
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
    by_cases hτ : τ ∈ X.Ψ
    · exact Or.inl hτ
    · refine Or.inr ⟨ComplexEmbedding.conjugate τ, ?_, hinv τ⟩
      rw [X.cmType, hinv τ]
      exact hτ
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinv.injective,
    Finset.card_univ, NumberField.Embeddings.card] at hcard
  omega

end GlobalTheory.TwoLines
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GramSchmidtCont

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

theorem continuousOn_inv_apply {T : Type} [TopologicalSpace T] {n : ℕ} {s : Set T}
    {M : T → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M) (hd : ∀ t ∈ s, (M t).det ≠ 0)
    (i j : Fin n) : ContinuousOn (fun t => (M t)⁻¹ i j) s := by
  have hdet : Continuous fun t => (M t).det := hM.matrix_det
  have hadj : Continuous fun t => (M t).adjugate i j := hM.matrix_adjugate.matrix_elem i j
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hdet.continuousOn.inv₀ hd).mul hadj.continuousOn

theorem continuousOn_uMat_apply {T : Type} [TopologicalSpace T] {n : ℕ} {s : Set T}
    {M : T → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M)
    (hd : ∀ t ∈ s, ∀ c : Fin n, (blk (M t) c).det ≠ 0) (j c : Fin n) :
    ContinuousOn (fun t => uMat (M t) j c) s := by
  by_cases hjc : j = c
  · simp only [uMat, Matrix.of_apply, if_pos hjc]
    exact continuousOn_const
  by_cases h : j < c
  · have hB : Continuous fun t => blk (M t) c := by
      unfold blk
      exact hM.matrix_submatrix _ _
    have hinv := fun m k => continuousOn_inv_apply hB (fun t ht => hd t ht c) m k
    simp only [uMat, Matrix.of_apply, if_neg hjc, dif_pos h, Matrix.vecMul, dotProduct, rowc]
    refine ContinuousOn.neg (continuousOn_finsetSum _ fun m _ => ContinuousOn.mul ?_ (hinv m _))
    exact (hM.matrix_elem c _).continuousOn
  · simp only [uMat, Matrix.of_apply, if_neg hjc, dif_neg h]
    exact continuousOn_const

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem continuous_gram {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) :
    Continuous (gram τ G) := by
  refine continuous_matrix fun a b => ?_
  simp only [gram, hermC, col, Matrix.of_apply]
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    ((continuous_id.matrix_elem k a).mul continuous_const).mul
      (Complex.continuous_conj.comp (continuous_id.matrix_elem l b))

theorem continuous_mat {r : ℕ} (X : Data E r) (τ : X.Ψ) :
    Continuous (fun x : Frame X.Ψ r => mat x τ) := by
  refine continuous_matrix fun a b => ?_
  simp only [mat, Matrix.of_apply]
  exact (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))

theorem continuousOn_uOf {r : ℕ} (X : Data E r) (τ : X.Ψ) :
    ContinuousOn (fun x : Frame X.Ψ r => uOf X x τ) X.dom := by
  refine continuousOn_pi.2 fun j => continuousOn_pi.2 fun c => ?_
  exact continuousOn_uMat_apply ((continuous_gram τ.1 X.Gm).comp (continuous_mat X τ))
    (fun x hx c => blk_det X hx τ c) j c

theorem continuousOn_dOf {r : ℕ} (X : Data E r) (τ : X.Ψ) (k : Fin r) :
    ContinuousOn (fun x : Frame X.Ψ r => dOf X x τ k) X.dom := by
  show ContinuousOn (fun x => gram τ.1 X.Gm (mat x τ * uOf X x τ) k k) X.dom
  exact ((continuous_id.matrix_elem k k).comp (continuous_gram τ.1 X.Gm)).comp_continuousOn
    ((continuous_mat X τ).continuousOn.mul (continuousOn_uOf X τ))

theorem continuousOn_sOf {r : ℕ} (X : Data E r) (τ : X.Ψ) (k : Fin r) :
    ContinuousOn (fun x : Frame X.Ψ r => sOf X x τ k) X.dom := by
  show ContinuousOn (fun x => (((Real.sqrt |(dOf X x τ k).re|)⁻¹ : ℝ) : ℂ)) X.dom
  refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.inv₀ ?_ ?_)
  · exact Real.continuous_sqrt.comp_continuousOn (continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (continuousOn_dOf X τ k)))
  · intro x hx
    exact (Real.sqrt_pos.2 (abs_re_pos X hx τ k)).ne'

theorem continuousOn_bOf {r : ℕ} (X : Data E r) : ContinuousOn (bOf X) X.dom := by
  refine continuousOn_pi.2 fun τ => ?_
  show ContinuousOn (fun x => (uOf X x τ * Matrix.diagonal (sOf X x τ) : Matrix (Fin r) (Fin r) ℂ)) X.dom
  exact (continuousOn_uOf X τ).mul (continuous_id.matrix_diagonal.comp_continuousOn
    (continuousOn_pi.2 fun k => continuousOn_sOf X τ k))

theorem exists_continuous_gramSchmidt :
    (∀ (r : ℕ) (X : Data E r), ∃ β : Frame X.Ψ r → Frame X.Ψ r, ContinuousOn β X.dom ∧
      ∀ x ∈ X.dom, β x ∈ Bor X.Ψ r ∧ IsOrth X (rmul x (β x))) := by
  intro r X
  exact ⟨bOf X, continuousOn_bOf X, fun x hx => ⟨bOf_mem X hx, ortho_bOf X hx⟩⟩

end GlobalTheory.GramSchmidtCont
end

