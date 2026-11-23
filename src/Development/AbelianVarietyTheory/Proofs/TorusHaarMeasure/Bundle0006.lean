module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsAlgebraicIndependentRatiosOfGenericZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory

theorem mem_matroid_closure_of_mem_adjoin {k κ : Type} [Field k] [Field κ] [Algebra k κ]
    {S : Set κ} {x : κ} (hx : x ∈ Algebra.adjoin k S) :
    x ∈ (AlgebraicIndependent.matroid k κ).closure S := by
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact isAlgebraic_algebraMap (⟨x, hx⟩ : Algebra.adjoin k S)

theorem exists_algebraicIndependent_ratios_of_generic_zero :
    ∀ (k κ : Type) [Field k] [Field κ] [Algebra k κ] (m N : ℕ) (t : Fin m × Fin (N + 1) → κ)
    (ζ : Fin (N + 1) → κ) (j0 : Fin (N + 1)), AlgebraicIndependent k t → ζ j0 ≠ 0 →
    (∀ i, ∑ j, t (i, j) * ζ j = 0) →
    ∃ J : Fin m → Fin (N + 1), AlgebraicIndependent k (fun a => ζ (J a) / ζ j0) := by
  intro k κ _ _ _ m N t ζ j0 ht h0 hz
  classical
  set M := AlgebraicIndependent.matroid k κ with hM
  set η : Fin (N + 1) → κ := fun j => ζ j / ζ j0 with hη
  set t' : Fin m × Fin N → κ := fun p => t (p.1, j0.succAbove p.2) with ht'
  have hsub : Set.range t ⊆ M.closure (Set.range η ∪ Set.range t') := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    apply mem_matroid_closure_of_mem_adjoin
    have hmem : ∀ l : Fin N, t (i, j0.succAbove l) ∈
        Algebra.adjoin k (Set.range η ∪ Set.range t') := fun l =>
      Algebra.subset_adjoin (Or.inr ⟨(i, l), rfl⟩)
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨l, rfl⟩
    · have h1 := hz i
      rw [Fin.sum_univ_succAbove _ j] at h1
      have h2 : t (i, j) = -∑ l : Fin N, t (i, j.succAbove l) * η (j.succAbove l) := by
        simp only [hη, ← mul_div_assoc, ← Finset.sum_div]
        field_simp
        linear_combination h1
      rw [h2]
      exact neg_mem (sum_mem fun l _ =>
        mul_mem (hmem l) (Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)))
    · exact hmem l
  have hind : M.Indep (Set.range t) := ht.to_subtype_range
  have h1 : M.eRk (Set.range t) = ((m * (N + 1) : ℕ) : ℕ∞) := by
    rw [hind.eRk_eq_encard, ← Set.image_univ, ht.injective.encard_image]
    simp
  have h2 : (Set.range t').encard ≤ ((m * N : ℕ) : ℕ∞) := by
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    simp
  have h3 : ((m * (N + 1) : ℕ) : ℕ∞) ≤ M.eRk (Set.range η) + ((m * N : ℕ) : ℕ∞) := by
    rw [← h1]
    refine (M.eRk_mono hsub).trans ?_
    rw [M.eRk_closure_eq]
    exact (M.eRk_union_le_eRk_add_encard _ _).trans (by gcongr)
  have h4 : (m : ℕ∞) ≤ M.eRk (Set.range η) := by
    have : ((m * (N + 1) : ℕ) : ℕ∞) = (m : ℕ∞) + ((m * N : ℕ) : ℕ∞) := by
      push_cast; ring
    rw [this] at h3
    exact (WithTop.add_le_add_iff_right (ENat.coe_ne_top _)).mp h3
  obtain ⟨I, hIη, hI, hc⟩ := Matroid.le_eRk_iff.mp h4
  have hfin : I.Finite := Set.finite_of_encard_eq_coe hc
  have : Finite I := hfin
  have hcard : Nat.card I = m := by
    rw [Nat.card_coe_set_eq, Set.ncard, hc]; simp
  let e : Fin m ≃ I := (Finite.equivFinOfCardEq hcard).symm
  choose g hg using fun x : I => hIη x.2
  refine ⟨fun a => g (e a), ?_⟩
  have hI' : AlgebraicIndependent k (fun x : I => (x : κ)) := hI
  have := hI'.comp e e.injective
  convert this using 1
  funext a
  exact hg (e a)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetInequalitiesClosedForms
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem gramDet_closed_forms :
    (∀ (m α β γ : Type) [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (M : Matrix m (α ⊕ β ⊕ γ) ℂ), (((M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))).det.re) * (((M)ᴴ * (M)).det.re) ≤ (((M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))).det.re) * (((M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))).det.re)) ∧ (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) ∧ (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ ω ∧ ∀ (i : ℕ) (M : Matrix (Fin r) (Fin i) ℂ), 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re) ∧ (((M)ᴴ * (M)).det.re) ≤ ω * (((a * M)ᴴ * (a * M)).det.re)) ∧ (0 < i → i < r → ∑ a ∈ S, ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) ^ (-δ) ≤ S.card * c)) ∧ (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by
  have hmono := det_re_mono_of_posSemidef
  have hcs := gram_det_cauchy_schwarz_of_det_mono hmono
  have hdist := gram_det_mul_le hmono
  have hexp := uniform_log_expansion_of_pointwise (sum_log_gramDet_ratio_pos hcs)
  refine ⟨gram_det_submodular hmono, hdist, ?_, ?_⟩
  · exact gramDet_contraction hdist hexp exists_rpow_neg_sum_le_of_sum_log
  · exact exists_finite_symmetric_irreducible_rotations offDiagonal_matrixUnits_irreducible

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.InjectiveOfInjectiveCompAevalOfTrdegLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory

open MvPolynomial

theorem injective_of_injective_comp_aeval_of_trdeg_le {k A κ ι : Type} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [CommRing κ] [Finite ι] (b : ι → A)
    (hA : Algebra.trdeg k A ≤ Cardinal.mk ι) (χ : A →+* κ)
    (hχ : Function.Injective (fun q : MvPolynomial ι k => χ (aeval b q))) :
    Function.Injective χ := by
  have hb : AlgebraicIndependent k b := by
    rw [algebraicIndependent_iff_injective_aeval]
    exact Function.Injective.of_comp (f := χ) hχ
  have hT := hb.isTranscendenceBasis_of_trdeg_le_of_finite hA
  have := hT.isAlgebraic
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  have hmem : a ∈ RingHom.ker χ := ha
  refine Ideal.comap_ne_bot_of_algebraic_mem hne hmem
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin k (Set.range b)) a) (eq_bot_iff.2 fun y hy => ?_)
  rw [Ideal.mem_comap, RingHom.mem_ker] at hy
  rw [Ideal.mem_bot]
  obtain ⟨y, hy'⟩ := y
  have hr := hy'
  rw [Algebra.adjoin_range_eq_range_aeval] at hr
  obtain ⟨q, rfl⟩ := hr
  have h0 : χ (aeval b q) = 0 := hy
  have hq : q = 0 := hχ (show χ (aeval b q) = χ (aeval b 0) by rw [map_zero, map_zero]; exact h0)
  subst hq
  apply Subtype.ext
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormDetSubmatrixSqLeDetGram
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem norm_det_submatrix_sq_le_det_gram :
    ∀ (m : Type) [Fintype m] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix m ι ℂ)
      (e : ι → m), Function.Injective e →
        ‖(M.submatrix e id).det‖ ^ 2 ≤ (Mᴴ * M).det.re := by
  classical
  intro m _ ι _ _ M e he
  set N : Matrix ι ι ℂ := M.submatrix e id with hN
  set s : Finset m := Finset.univ.map ⟨e, he⟩ with hs
  let B : Matrix (sᶜ : Finset m) ι ℂ := fun i j => M i j
  have hsplit : Mᴴ * M = Nᴴ * N + Bᴴ * B := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply]
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · rw [hs, Finset.sum_map]
      rfl
    · rw [← Finset.sum_coe_sort sᶜ]
  have hN1 : (Nᴴ * N).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self N
  have hB1 : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have key := (det_re_mono_of_posSemidef ι (Nᴴ * N) (Bᴴ * B) hN1 hB1).2.1
  rw [hsplit]
  refine le_trans (le_of_eq ?_) key
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
  norm_cast

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PolyImgSuccAbove
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial

namespace GlobalTheory.GenericSection

variable {F : Type} [Field F] {D N : ℕ}

noncomputable def polyImg (j0 : Fin (N + 1)) (x : Fin N → F) (p : TVar D N) :
    MvPolynomial (SVar D N) F :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) F) j0
    (if p.1 = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (p.1, k)) * C (x k))
    (fun k => X (Sum.inr (p.1, k))) p.2

def freeVar (j0 : Fin (N + 1)) : SVar D N → TVar D N :=
  Sum.elim (fun _ => (0, j0)) (fun q => (q.1, j0.succAbove q.2))

open NumberField MvPolynomial in
variable {F : Type} [Field F] {D N : ℕ} in
theorem _root_.GlobalTheory.GenericSection.polyImg_same (j0 : Fin (N + 1)) (x : Fin N → F)
    (i : Fin (D + 1)) :
    _root_.GlobalTheory.GenericSection.polyImg j0 x (i, j0) =
      (if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k)) := by
  simp [_root_.GlobalTheory.GenericSection.polyImg]

open NumberField MvPolynomial in
variable {F : Type} [Field F] {D N : ℕ} in
theorem _root_.GlobalTheory.GenericSection.polyImg_succAbove (j0 : Fin (N + 1)) (x : Fin N → F)
    (i : Fin (D + 1)) (k : Fin N) :
    _root_.GlobalTheory.GenericSection.polyImg j0 x (i, j0.succAbove k) = X (Sum.inr (i, k)) := by
  simp [_root_.GlobalTheory.GenericSection.polyImg]

end GlobalTheory.GenericSection
end

