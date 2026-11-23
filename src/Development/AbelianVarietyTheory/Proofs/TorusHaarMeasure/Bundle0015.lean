module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightAtFrame
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightLower

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_pos_le_height : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∃ m : ℝ, 0 < m ∧ ∀ W, m ≤ d x W) := by
  intro r X d hd x hx
  obtain ⟨C, hC, hCle⟩ := GlobalTheory.relIndex_span_le_norm_minor r X
  have hω : ∀ τ : X.Ψ, ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (M : Matrix (Fin r) ι ℂ), ((mat x τ * M)ᴴ * (mat x τ * M)).det.re ≤ ω * (Mᴴ * M).det.re :=
    fun τ => GlobalTheory.gram_det_mul_le GlobalTheory.det_re_mono_of_posSemidef r (mat x τ)
  choose ω hω1 hωle using hω
  have hΩ : 0 < ∏ τ, ω τ := Finset.prod_pos fun τ _ => lt_of_lt_of_le one_pos (hω1 τ)
  refine ⟨1 / (C * ∏ τ, ω τ), by positivity, fun W => ?_⟩
  obtain ⟨w, hwi, hwΛ, hspan⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  obtain ⟨e, he, hδ⟩ := GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent E r _ w hwi
  have hdW := hd x hx _ w hwi hwΛ
  rw [hspan] at hdW
  rw [hdW]
  have hI0 := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X _ w hwi hwΛ
  have hIle := hCle _ w hwi hwΛ e he hδ
  rw [hspan] at hI0 hIle
  set I := ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex
    (X.Λ.toAddSubgroup ⊓ W.toAddSubgroup)) with hIdef
  have hIpos : (0 : ℝ) < (I : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hI0

  have key : ∀ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2 ≤
      ω τ * (((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    intro τ
    have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hx τ)
    have h1 := hωle τ _ ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h1
    have h2 := GlobalTheory.norm_det_submatrix_sq_le_det_gram (Fin r) _
      (Matrix.of fun k a => τ.1 (w a k)) e he
    have h3 : ((Matrix.of fun k a => τ.1 (w a k)).submatrix e id).det =
        τ.1 (Matrix.of fun k a => w a (e k)).det := by
      rw [RingHom.map_det]
      congr 1
    rw [h3] at h2
    exact h2.trans h1
  have hprod : ∏ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2 ≤
      (∏ τ, ω τ) * ∏ τ : X.Ψ, (((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun τ _ => by positivity) (fun τ _ => key τ)
  rw [div_le_div_iff₀ (by positivity) hIpos, one_mul]
  calc (I : ℝ) ≤ C * _ := hIle
    _ ≤ C * ((∏ τ, ω τ) * _) := mul_le_mul_of_nonneg_left hprod hC.le
    _ = _ := by ring

end GlobalTheory.HeightLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightBotTop
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightEnds

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * (xᴴ)ᵀ := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem norm_det_orth {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (τ : X.Ψ) :
    ‖(mat x τ).det‖ ^ 2 * ‖τ.1 X.Gm.det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (hx τ)
  simp only [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_conjTranspose,
    Matrix.det_diagonal, norm_mul, norm_star, norm_prod] at h
  have h1 : ∀ a : Fin r, ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ)‖ = 1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  simp only [h1, Finset.prod_const_one] at h
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← h]
  ring

theorem gramDet_square {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) :
    (Nᴴ * N).det.re = ‖N.det‖ ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem exists_pos_le_bot_top : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∃ m : ℝ, 0 < m ∧ ∀ x, IsOrth X x → m ≤ d x ⊥ ∧ m ≤ d x ⊤) := by
  intro r X d hd
  obtain ⟨w0, hw0, hΛ0, hsp0⟩ := GlobalTheory.LatBasis.exists_basis_mem r X ⊤
  have hr : r = Module.finrank E (⊤ : Submodule E (Fin r → E)) := by simp
  let w : Fin r → Fin r → E := w0 ∘ finCongr hr
  have hw : LinearIndependent E w := hw0.comp _ (finCongr hr).injective
  have hΛ : ∀ a, w a ∈ X.Λ := fun a => hΛ0 _
  have hsp : Submodule.span E (Set.range w) = ⊤ := by
    rw [(finCongr hr).surjective.range_comp]; exact hsp0
  have hdet : (Matrix.of w).det ≠ 0 := by
    have : IsUnit (Matrix.of w) := Matrix.linearIndependent_rows_iff_isUnit.1 hw
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hind := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X (Fin r) w hw hΛ
  set n : ℕ := (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup) with hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hind)
  let c : ℝ := (∏ τ : X.Ψ, ‖τ.1 X.Gm.det‖ * ‖τ.1 (Matrix.of w).det‖ ^ 2) / n
  have hc : 0 < c := by
    refine div_pos (Finset.prod_pos fun τ _ => mul_pos ?_ (pow_pos ?_ 2)) hnpos
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 X.Gm_det)
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 hdet)
  refine ⟨min 1 c, lt_min one_pos hc, fun x hx => ?_⟩
  have hxd : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := by
    intro τ h0
    have := norm_det_orth X x hx τ
    simp [h0] at this
  constructor
  · have h := hd x hxd Empty (fun a => a.elim) linearIndependent_empty_type (fun a => a.elim)
    have hre : Set.range (fun a : Empty => (a.elim : Fin r → E)) = ∅ := Set.range_eq_empty _
    rw [hre] at h
    simp only [Submodule.span_empty, Matrix.det_isEmpty, Complex.one_re, Finset.prod_const_one,
      Submodule.bot_toAddSubgroup, inf_bot_eq, AddSubgroup.relIndex_self, Nat.cast_one,
      div_one] at h
    rw [h]
    exact min_le_left _ _
  · have h := hd x hxd (Fin r) w hw hΛ
    rw [← hn, hsp] at h
    rw [h]
    refine (min_le_right _ _).trans (le_of_eq ?_)
    refine congrArg (· / (n : ℝ)) (Finset.prod_congr rfl fun τ _ => ?_)
    have h1 : (Matrix.of fun k a => τ.1 (w a k)).det = τ.1 (Matrix.of w).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
      rfl
    have h2 := norm_det_orth X x hx τ
    have h3 : ‖(mat x τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hxd τ)
    rw [gramDet_square, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h1, norm_mul,
      norm_inv, mul_pow, inv_pow]
    congr 1
    exact eq_inv_of_mul_eq_one_right h2

end GlobalTheory.HeightEnds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumLowerOfLineHeights
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LineHeight

theorem gramDet_column {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (((A * (Matrix.of fun k (_ : Unit) => u k))ᴴ * (A * (Matrix.of fun k (_ : Unit) => u k))).det.re)
      = ∑ a, ‖(A.mulVec u) a‖ ^ 2 := by
  rw [Matrix.det_unique, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : (A * Matrix.of fun k (_ : Unit) => u k) a default = A.mulVec u a := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [Matrix.conjTranspose_apply, h, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem exists_min_le_of_le_prod {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (m : ℝ) (hm : m ≤ ∏ i, f i) : ∃ i, min 1 m ≤ f i := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i0⟩ := ‹Nonempty ι›
  by_cases hm0 : m ≤ 0
  · exact absurd ((min_le_right _ _).trans (hm0.trans (hf i0))) (not_le.mpr (hcon i0))
  · have h1 : ∀ i, f i ≤ 1 := fun i => ((hcon i).trans_le (min_le_left _ _)).le
    have hp : ∏ i, f i ≤ f i0 := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i0)]
      exact mul_le_of_le_one_right (hf i0) (Finset.prod_le_one₀ (fun i _ => hf i) fun i _ => h1 i)
    have h2 : f i0 < m := (hcon i0).trans_le (min_le_right _ _)
    linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nonempty_cmType {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨_, not_not.mp (mt (X.cmType τ).2 h)⟩⟩

theorem c_pos {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ :=
  mul_pos two_pos (norm_pos_iff.mpr ((map_ne_zero τ.1).mpr X.ξ0_ne))

theorem exists_la1_lower_bound_of_line_heights : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → 0 < r → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → ε ≤ X.la1 x) := by
  intro r X d hd hr m hm
  have := nonempty_cmType X
  obtain ⟨τ0, -, hτ0⟩ := (Finset.univ : Finset X.Ψ).exists_min_image X.c Finset.univ_nonempty
  have hmin : 0 < min 1 m := lt_min one_pos hm
  have hδ : 0 < X.c τ0 * min 1 m := mul_pos (c_pos X τ0) hmin
  refine ⟨Real.sqrt (X.c τ0 * min 1 m), Real.sqrt_pos.2 hδ, fun x hx hW => ?_⟩
  obtain ⟨hdet, hmaj⟩ := GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame r X x hx
  have key : ∀ v ∈ X.Λ, v ≠ 0 →
      X.c τ0 * min 1 m ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    have hli : LinearIndependent E (fun _ : Unit => v) := linearIndependent_unique_iff.mpr hv0
    have hfin : Module.finrank E (Submodule.span E (Set.range fun _ : Unit => v)) = 1 := by
      rw [Set.range_const]
      exact finrank_span_singleton hv0
    have hg : ∀ τ : X.Ψ, (((mat x τ)⁻¹ * Matrix.of fun k (_ : Unit) => τ.1 (v k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k (_ : Unit) => τ.1 (v k))).det.re =
          X.maj x τ (Data.emb τ.1 v) :=
      fun τ => (gramDet_column _ _).trans (hmaj τ _).symm
    have hmaj0 : ∀ τ, 0 ≤ X.maj x τ (Data.emb τ.1 v) := fun τ => by
      rw [hmaj]
      positivity
    have hidx := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X Unit (fun _ => v) hli fun _ => hv
    have h1 := hW _ hfin
    rw [hd x hdet Unit (fun _ => v) hli (fun _ => hv)] at h1
    simp only [hg] at h1
    have h2 : m ≤ ∏ τ, X.maj x τ (Data.emb τ.1 v) :=
      h1.trans (div_le_self (Finset.prod_nonneg fun τ _ => hmaj0 τ)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hidx))
    obtain ⟨τ, hτ⟩ := exists_min_le_of_le_prod _ hmaj0 m h2
    calc X.c τ0 * min 1 m ≤ X.c τ * X.maj x τ (Data.emb τ.1 v) :=
          mul_le_mul (hτ0 τ (Finset.mem_univ _)) hτ hmin.le (c_pos X τ).le
      _ ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) :=
          Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (Data.emb τ.1 v))
            (fun τ _ => mul_nonneg (c_pos X τ).le (hmaj0 τ)) (Finset.mem_univ τ)
  have hne : ∃ v ∈ X.Λ, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ :=
      Submodule.span_eq_bot.mpr fun v hv => hcon v hv
    rw [X.Λ_span] at hbot
    have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact top_ne_bot hbot
  obtain ⟨v0, hv0, hv00⟩ := hne
  unfold Data.la1
  refine Real.sqrt_le_sqrt ?_
  unfold Data.firstMinimumSq
  refine le_csInf ⟨_, v0, hv0, hv00, rfl⟩ ?_
  rintro t ⟨v, hv, hv0', rfl⟩
  exact key v hv hv0'

end GlobalTheory.LineHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetDivIndexEqOfSpanEqStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.gramDet_div_index_eq_of_span_eq : (∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ι : Type) [Fintype ι] [DecidableEq ι] (w w' : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → LinearIndependent E w' → (∀ a, w' a ∈ X.Λ) → Submodule.span E (Set.range w) = Submodule.span E (Set.range w') → ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w')).toAddSubgroup)) : ℝ))) := by
  first | exact @GlobalTheory.gram_div_index_eq_of_span_eq | exact GlobalTheory.gram_div_index_eq_of_span_eq | (intros; apply GlobalTheory.gram_div_index_eq_of_span_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetReNonneg
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.HeightSubmodular

theorem gram_det_re_nonneg {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq ι]
    (N : Matrix m ι ℂ) : 0 ≤ (Nᴴ * N).det.re := by
  have h : (0 : ℂ) ≤ (Nᴴ * N).det := (Matrix.posSemidef_conjTranspose_mul_self N).det_nonneg
  exact (Complex.nonneg_iff.mp h).1

theorem div_mul_div_le {p q p' q' : ℝ} {i j i' j' : ℕ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : p * q ≤ p' * q') (hi : i' ≠ 0) (hj : j' ≠ 0) (hij : i' * j' ≤ i * j) :
    p / i * (q / j) ≤ p' / i' * (q' / j') := by
  have hnum : 0 ≤ p' * q' := (mul_nonneg hp hq).trans h
  have hden : (0 : ℝ) < (i' : ℝ) * j' :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (by exact_mod_cast Nat.pos_of_ne_zero hj)
  rw [div_mul_div_comm, div_mul_div_comm]
  rcases Nat.eq_zero_or_pos (i * j) with h0 | h0
  · have hz : (i : ℝ) * j = 0 := by exact_mod_cast h0
    rw [hz, div_zero]
    exact div_nonneg hnum hden.le
  · exact div_le_div₀ hnum h hden (by exact_mod_cast hij)

theorem height_submodular : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ W₁ W₂, d x (W₁ ⊓ W₂) * d x (W₁ ⊔ W₂) ≤ d x W₁ * d x W₂) := by
  intro r X d hd x hx W₁ W₂
  obtain ⟨a, b, c, w, hli, hmem, h0, h1, h2, h3⟩ :=
    GlobalTheory.LatBasisAdapted.exists_basis_adapted_mem r X W₁ W₂
  have hsub : ∀ {κ : Type} (f : κ → Fin a ⊕ Fin b ⊕ Fin c) (τ : X.Ψ),
      (mat x τ)⁻¹ * (Matrix.of fun k l => τ.1 ((w ∘ f) l k)) =
        ((mat x τ)⁻¹ * Matrix.of fun k l => τ.1 (w l k)).submatrix id f := by
    intro κ f τ
    ext k l
    simp [Matrix.mul_apply]
  have key := fun {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Fin a ⊕ Fin b ⊕ Fin c)
      (hf : Function.Injective f) =>
    hd x hx κ (w ∘ f) (hli.comp f hf) (fun l => hmem (f l))
  have hI := fun {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Fin a ⊕ Fin b ⊕ Fin c)
      (hf : Function.Injective f) =>
    GlobalTheory.SpanIndex.relIndex_span_ne_zero r X κ (w ∘ f) (hli.comp f hf) (fun l => hmem (f l))
  have i1 : Function.Injective (Sum.map id Sum.inl : Fin a ⊕ Fin b → Fin a ⊕ Fin b ⊕ Fin c) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩
  have i2 : Function.Injective (Sum.map id Sum.inr : Fin a ⊕ Fin c → Fin a ⊕ Fin b ⊕ Fin c) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩
  rw [← h0, ← h3, ← h1, ← h2, key _ Sum.inl_injective, key _ i1, key _ i2,
    hd x hx _ w hli hmem]
  apply div_mul_div_le
  · exact Finset.prod_nonneg fun τ _ => gram_det_re_nonneg _
  · exact Finset.prod_nonneg fun τ _ => gram_det_re_nonneg _
  · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro τ _
      exact mul_nonneg (gram_det_re_nonneg _) (gram_det_re_nonneg _)
    · intro τ _
      simp only [hsub]
      exact (_root_.GlobalTheory.gramDet_closed_forms).1 (Fin r) (Fin a) (Fin b) (Fin c) _
  · exact hI _ i1
  · exact hI _ i2
  · exact (GlobalTheory.T.relIndex_integralSpan_supermultiplicative) r X (Fin a) (Fin b) (Fin c) w hli hmem

end GlobalTheory.HeightSubmodular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightContinuousOnFrames
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightCont

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem height_continuousOn : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ W, ContinuousOn (fun x => d x W) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  intro r X d hd W
  obtain ⟨w, hw, hΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  suffices H : ContinuousOn (fun x => d x (Submodule.span E (Set.range w)))
      {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)} by rwa [hsp] at H
  refine ContinuousOn.congr ?_ (fun x hx => hd x hx _ w hw hΛ)
  refine ContinuousOn.div_const ?_ _
  refine continuousOn_finsetProd _ fun τ _ x hx => ContinuousAt.continuousWithinAt ?_
  have hm : Continuous (fun x : Frame X.Ψ r => mat x τ) := continuous_apply τ
  have hr : ContinuousAt (Ring.inverse : ℂ → ℂ) (mat x τ).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hx τ)
  have hi : ContinuousAt (fun x : Frame X.Ψ r => (mat x τ)⁻¹) x :=
    ContinuousAt.comp (f := fun x : Frame X.Ψ r => mat x τ) (continuousAt_matrix_inv _ hr)
      hm.continuousAt
  have hg : Continuous (fun A : Matrix (Fin r) (Fin r) ℂ =>
      ((A * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * (A * (Matrix.of fun k a => τ.1 (w a k)))).det.re) :=
    Complex.continuous_re.comp
      (((continuous_id.matrix_mul continuous_const).matrix_conjTranspose.matrix_mul
        (continuous_id.matrix_mul continuous_const)).matrix_det)
  exact ContinuousAt.comp (f := fun x : Frame X.Ψ r => (mat x τ)⁻¹) hg.continuousAt hi

end GlobalTheory.HeightCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightUpdateFrameComponent
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightStep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.HeightStep.height_update : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (d : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (τ0 : X.Ψ) (W : Submodule E (Fin r → E)), ∃ M : Matrix (Fin r) (Fin (Module.finrank E W)) ℂ, 0 < (((M)ᴴ * (M)).det.re) ∧ ∀ a : Matrix (Fin r) (Fin r) ℂ, a.det ≠ 0 → d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W = d x W * ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  classical
  intro r X d hd x hx τ0 W
  obtain ⟨w, hli, hmem, hspan⟩ := _root_.GlobalTheory.LatBasis.exists_basis_mem r X W
  obtain ⟨e, -, hdet⟩ := _root_.GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent E r _ w hli
  set N : X.Ψ → Matrix (Fin r) (Fin (Module.finrank E W)) ℂ :=
    fun τ => Matrix.of fun k a => τ.1 (w a k) with hN
  set M := (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0)⁻¹ * N τ0 with hM
  have hA : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0).det := isUnit_iff_ne_zero.mpr (hx τ0)
  have hminor : (Matrix.of fun k a => N τ0 (e k) a).det ≠ 0 := by
    have hmap : (Matrix.of fun k a => N τ0 (e k) a) =
        τ0.1.mapMatrix (Matrix.of fun k a => w a (e k)) := by
      ext k a
      rfl
    rw [hmap, ← RingHom.map_det]
    exact (map_ne_zero τ0.1).mpr hdet
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    rw [← sub_eq_zero]
    have h0 : M *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have h1 : N τ0 *ᵥ (u - v) = 0 := by
      have : N τ0 = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * M := by
        rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]
      rw [this, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    apply Matrix.eq_zero_of_mulVec_eq_zero hminor
    funext k
    have := congrFun h1 (e k)
    simpa [Matrix.mulVec, dotProduct] using this
  have hpos : 0 < ((Mᴴ * M).det.re) := by
    have := (Matrix.PosDef.conjTranspose_mul_self M hinj).det_pos
    exact (Complex.pos_iff.mp this).1
  refine ⟨M, hpos, fun a ha => ?_⟩
  set x' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := @Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _)
    x τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ) with hx'
  have haU : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hupd : ∀ τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ = if τ = τ0 then _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ else _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ := by
    intro τ
    by_cases h : τ = τ0
    · subst h
      rw [if_pos rfl, hx']
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
      exact @Function.update_self _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ _
    · rw [if_neg h, hx']
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
      exact @Function.update_of_ne _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ h _ _
  have hx'det : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ).det ≠ 0 := by
    intro τ
    rw [hupd]
    split_ifs
    · rw [Matrix.det_mul]
      exact mul_ne_zero (hx τ0) (Matrix.isUnit_nonsing_inv_det a haU).ne_zero
    · exact hx τ
  set F : X.Ψ → ℝ := fun τ => (((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * N τ)ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * N τ)).det.re with hF
  have h1 := hd x' hx'det _ w hli hmem
  have h2 := hd x hx _ w hli hmem
  rw [hspan] at h1 h2
  rw [h1, h2]
  have hprod' : ∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re) =
      (((a * M)ᴴ * (a * M)).det.re) * ∏ τ ∈ Finset.univ \ {τ0}, F τ := by
    rw [← Finset.prod_update_of_mem (Finset.mem_univ τ0)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Function.update_apply, hupd]
    split_ifs with h
    · subst h
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv a haU, Matrix.mul_assoc]
    · rfl
  have hprod : ∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re) =
      ((Mᴴ * M).det.re) * ∏ τ ∈ Finset.univ \ {τ0}, F τ := by
    rw [← Finset.prod_update_of_mem (Finset.mem_univ τ0), Function.update_eq_self]
  rw [hprod', hprod]
  have hne : (Mᴴ * M).det.re ≠ 0 := hpos.ne'
  field_simp

end GlobalTheory.HeightStep
end

