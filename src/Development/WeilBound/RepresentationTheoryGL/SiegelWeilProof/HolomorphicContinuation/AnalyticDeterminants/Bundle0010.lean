module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0008
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0009

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetColumnPerturbation
section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

def phiF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Fin.cons 0 X

def piF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ := fun k l => X k l.succ

def colQ (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (c : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun k l => if l = c then X k 0 else 0

@[simp] theorem phiF_zero_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (j : Fin (N + 1)) : phiF X 0 j = 0 := rfl

@[simp] theorem phiF_succ_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (k : Fin N) (j : Fin (N + 1)) :
    phiF X k.succ j = X k j := rfl

def phiL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := phiF
      map_add' := fun X Y => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp
      map_smul' := fun a X => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp }

def piL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := piF
      map_add' := fun X Y => by ext k l; simp [piF]
      map_smul' := fun a X => by ext k l; simp [piF] }

@[simp] theorem piL_apply (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : piL N X = piF X := rfl

theorem phiF_single (k : Fin N) (j : Fin (N + 1)) :
    phiF (Matrix.single k j (1 : ℂ)) = Matrix.single k.succ j 1 := by
  ext i l
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [Matrix.single_apply, (Fin.succ_ne_zero k).symm]
  · simp [Matrix.single_apply, Fin.succ_inj]

theorem piF_single_succ (k : Fin N) (j : Fin N) :
    piF (Matrix.single k j.succ (1 : ℂ)) = Matrix.single k j 1 := by
  ext a b; simp [piF, Matrix.single_apply, Fin.succ_inj]

theorem piF_single_zero (k : Fin N) : piF (Matrix.single k (0 : Fin (N + 1)) (1 : ℂ)) = 0 := by
  ext a b; simp only [piF, Matrix.single_apply, Matrix.zero_apply]
  rw [if_neg]; rintro ⟨_, h⟩; exact Fin.succ_ne_zero b h.symm

theorem det_first_row_expansion (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (a : ℂ) (h : ∀ j, A 0 j = if j = 0 then a else 0) :
    A.det = a * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · simp [h]
  · intro j _ hj; simp [h, hj]
  · simp

theorem det_corner_perturbation (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    (1 + phiF X + s • Matrix.single 0 0 1).det = (1 + s) * (1 + piF X).det := by
  have hsub : (1 + phiF X + s • Matrix.single 0 0 1).submatrix Fin.succ Fin.succ = 1 + piF X := by
    ext k l
    simp [piF, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj, Fin.succ_ne_zero]
    intro h; exact absurd h.symm (Fin.succ_ne_zero k)
  rw [det_first_row_expansion _ (1 + s), hsub]
  intro j
  refine Fin.cases ?_ (fun m => ?_) j
  · simp [Matrix.one_apply, Matrix.single_apply]
  · simp [Matrix.one_apply, Matrix.single_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero m).symm]

theorem det_column_perturbation (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) (c : Fin N) :
    (1 + phiF X + s • Matrix.single 0 c.succ 1).det = (1 + piF X - s • colQ X c).det := by
  set A := 1 + phiF X + s • Matrix.single 0 c.succ (1 : ℂ) with hA
  have hne : c.succ ≠ (0 : Fin (N + 1)) := Fin.succ_ne_zero c
  have hz : ∀ k : Fin N, ((0 : Fin (N + 1)) = k.succ) ↔ False :=
    fun k => ⟨fun h => Fin.succ_ne_zero k h.symm, False.elim⟩
  rw [← Matrix.det_updateCol_add_smul_self A hne (-s)]
  rw [det_first_row_expansion _ 1]
  · rw [one_mul]
    congr 1
    ext k l
    by_cases hl : l = c
    · subst hl
      simp [A, Matrix.updateCol_apply, piF, colQ, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj,
        Fin.succ_ne_zero, hz]
      ring
    · have hl' : l.succ ≠ c.succ := fun h => hl (Fin.succ_inj.mp h)
      simp [A, Matrix.updateCol_apply, piF, colQ, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj,
        hl, hl', Fin.succ_ne_zero, hz]
  · intro j
    by_cases hj : j = c.succ
    · subst hj
      simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, Fin.succ_ne_zero, hz]
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨m, rfl⟩
      · simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, hne.symm, hz]
      · have hm : m ≠ c := fun h => hj (by rw [h])
        simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, hm, Fin.succ_ne_zero, hz,
          Fin.succ_inj, Ne.symm hm]

end PositivityTheory.Rg.Sw.LVs.CK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IteratedFderivRightTranslation
section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulR (c : M2 n) : M2 n →L[ℂ] M2 n := (LinearMap.mulRight ℂ c).toContinuousLinearMap

theorem mulR_apply (c y : M2 n) : mulR c y = y * c := rfl

def mulL (c : M2 n) : M2 n →L[ℂ] M2 n := (LinearMap.mulLeft ℂ c).toContinuousLinearMap

theorem mulL_apply (c y : M2 n) : mulL c y = c * y := rfl

theorem iterated_fderiv_right_translation {N : ℕ} (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (W : Fin (N + 1) → M2 n) (hW : ∀ a b, W a * W b = 0) (x : M2 n) (hx : x ∈ U) :
    fderiv ℂ (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) x (x * W 0) =
      iteratedFDeriv ℂ (N + 1) F x (fun i => x * W i) := by
  classical
  have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ N F) x :=
    hFx.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top N)
  have hg : ∀ i : Fin N, HasFDerivAt (fun y : M2 n => y * W i.succ) (mulR (W i.succ)) x :=
    fun i => (mulR (W i.succ)).hasFDerivAt
  have h := hd.hasFDerivAt.continuousMultilinearMap_apply (g := fun i y => y * W i.succ) hg
  have hz : ∀ i : Fin N, mulR (W i.succ) (x * W 0) = 0 := fun i => by
    rw [mulR_apply, mul_assoc, hW, mul_zero]
  refine (congrArg (fun L => L (x * W 0)) h.fderiv).trans ?_
  have hs : ∀ L : Fin N → (M2 n →L[ℂ] ℂ), (∀ i, L i (x * W 0) = 0) → (∑ i, L i) (x * W 0) = 0 := by
    intro L hL
    rw [ContinuousLinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hL i
  rw [ContinuousLinearMap.add_apply, hs _ (fun i => by rw [ContinuousLinearMap.comp_apply, hz, map_zero]), add_zero,
    ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_succ_apply_left]
  rfl

def rit (F : M2 n → ℂ) : (N : ℕ) → (Fin N → M2 n) → M2 n → ℂ
  | 0, _ => F
  | N + 1, W => fun y => fderiv ℂ (rit F N (fun i => W i.succ)) y (y * W 0)

theorem rit_zero (F : M2 n → ℂ) (W : Fin 0 → M2 n) : rit F 0 W = F := rfl

theorem rit_succ (F : M2 n → ℂ) (N : ℕ) (W : Fin (N + 1) → M2 n) :
    rit F (N + 1) W = fun y => fderiv ℂ (rit F N (fun i => W i.succ)) y (y * W 0) := rfl

theorem rit_contDiffOn (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) :
    ∀ (N : ℕ) (W : Fin N → M2 n), ContDiffOn ℂ ∞ (rit F N W) U := by
  intro N
  induction N with
  | zero => intro W; exact hF
  | succ N ih =>
    intro W
    rw [rit_succ]
    exact ((ih _).fderiv_of_isOpen hU (by simp)).clm_apply ((mulR (W 0)).contDiff.contDiffOn)

theorem rit_eq (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) :
    ∀ (N : ℕ) (W : Fin N → M2 n), (∀ a b, W a * W b = 0) → ∀ x ∈ U,
      rit F N W x = iteratedFDeriv ℂ N F x (fun i => x * W i) := by
  intro N
  induction N with
  | zero =>
    intro W _ x _
    simp [rit_zero, iteratedFDeriv_zero_apply]
  | succ N ih =>
    intro W hW x hx
    rw [rit_succ]
    have hev : rit F N (fun i => W i.succ) =ᶠ[nhds x]
        (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih _ (fun a b => hW _ _) y hy
    simp only
    rw [hev.fderiv_eq]
    exact iterated_fderiv_right_translation F U hU hF W hW x hx

theorem rit_law (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (χ : M2 n → ℂ)
    (hUP : ∀ P x, InP P → x ∈ U → P * x ∈ U) (hl : ∀ P x, InP P → x ∈ U → F (P * x) = χ P * F x) :
    ∀ (N : ℕ) (W : Fin N → M2 n) (P x : M2 n), InP P → x ∈ U → rit F N W (P * x) = χ P * rit F N W x := by
  intro N
  induction N with
  | zero => intro W P x hP hx; exact hl P x hP hx
  | succ N ih =>
    intro W P x hP hx
    rw [rit_succ]
    simp only
    set H := rit F N (fun i => W i.succ) with hH
    have hHs : ContDiffOn ℂ ∞ H U := rit_contDiffOn F U hU hF N _
    have hPx : P * x ∈ U := hUP P x hP hx
    have hdH : DifferentiableAt ℂ H (P * x) :=
      (hHs.contDiffAt (hU.mem_nhds hPx)).differentiableAt (by simp)
    have hev : (fun y => H (P * y)) =ᶠ[nhds x] (fun y => χ P * H y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih _ P y hP hy
    have hc : fderiv ℂ (fun y => H (P * y)) x = (fderiv ℂ H (P * x)).comp (mulL P) := by
      have := (hdH.hasFDerivAt.comp x (mulL P).hasFDerivAt)
      exact this.fderiv
    have hdHx : DifferentiableAt ℂ H x :=
      (hHs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have e1 : fderiv ℂ H (P * x) (P * x * W 0) = fderiv ℂ (fun y => H (P * y)) x (x * W 0) := by
      rw [hc]; simp [mulL_apply, mul_assoc]
    rw [e1]
    refine (congrArg (fun L : M2 n →L[ℂ] ℂ => L (x * W 0)) hev.fderiv_eq).trans ?_
    have hcm : fderiv ℂ (fun y => χ P * H y) x = χ P • fderiv ℂ H x := fderiv_const_mul hdHx (χ P)
    refine (congrArg (fun L : M2 n →L[ℂ] ℂ => L (x * W 0)) hcm).trans ?_
    simp

theorem snoc_rev {N : ℕ} (W : Fin (N + 1) → M2 n) :
    (Fin.snoc (fun i : Fin N => W (Fin.rev i).succ) (W 0) : Fin (N + 1) → M2 n) = fun i => W (Fin.rev i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Fin.snoc_last]
  · simp [Fin.snoc_castSucc, Fin.rev_castSucc]

theorem rit_snoc (G : M2 n → ℂ) (c : M2 n) :
    ∀ (N : ℕ) (V : Fin N → M2 n), rit (fun y => fderiv ℂ G y (y * c)) N V = rit G (N + 1) (Fin.snoc V c) := by
  intro N
  induction N with
  | zero =>
    intro V
    funext y
    simp only [rit_zero, rit_succ]
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]
  | succ N ih =>
    intro V
    rw [rit_succ, rit_succ, ih]
    have h1 : (fun i : Fin (N + 1) => (Fin.snoc V c : Fin (N + 2) → M2 n) i.succ) =
        Fin.snoc (fun i : Fin N => V i.succ) c := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_last]
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    have h0 : (Fin.snoc V c : Fin (N + 2) → M2 n) 0 = V 0 := by
      simpa using (Fin.snoc_castSucc (α := fun _ => M2 n) (p := V) (x := c) (i := 0))
    rw [h1, h0]

theorem cont_on_K (H : M2 n → ℂ) (hH : ContDiffOn ℂ ∞ H (Dom n)) (Kg : Type) [TopologicalSpace Kg]
    (ι : Kg → M2 n) (hι : Continuous ι) (hdom : ∀ k, ι k ∈ Dom n) : Continuous (fun k => H (ι k)) :=
  hH.continuousOn.comp_continuous hι hdom

theorem rit_transpose (hI : InfInv) (F1 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) :
    ∀ (N : ℕ) (F2 : M2 n → ℂ), ContDiffOn ℂ ∞ F2 (Dom n) →
      (∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x) → ∀ (W : Fin N → M2 n), (∀ a b, W a * W b = 0) →
      ∫ k, rit F1 N W (ι k) * F2 (ι k) ∂μ = (-1) ^ N * ∫ k, F1 (ι k) * rit F2 N (fun i => W (Fin.rev i)) (ι k) ∂μ := by
  have hdom : ∀ k, ι k ∈ Dom n := fun k => gset_sub_dom ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hint : ∀ g : Kg → ℂ, Continuous g → Integrable g μ := fun g hg => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun k => hC k trivial)
  have hUP : ∀ P x, InP P → x ∈ Dom n → P * x ∈ Dom n := fun P x hP hx => mul_mem_dom hP hx
  intro N
  induction N with
  | zero => intro F2 _ _ W _; simp [rit_zero]
  | succ N ih =>
    intro F2 hF2 h2 W hW
    set G := rit F1 N (fun i => W i.succ) with hGdef
    set F2' : M2 n → ℂ := fun y => fderiv ℂ F2 y (y * W 0) with hF2'def
    have hG : ContDiffOn ℂ ∞ G (Dom n) := rit_contDiffOn F1 _ isOpen_dom hF1 N _
    have hGlaw : ∀ P x, InP P → x ∈ Dom n → G (P * x) = χ1 P * G x :=
      rit_law F1 (Dom n) isOpen_dom hF1 χ1 hUP h1 N _
    have hF2'e : F2' = rit F2 1 (fun _ => W 0) := rfl
    have hF2' : ContDiffOn ℂ ∞ F2' (Dom n) := by rw [hF2'e]; exact rit_contDiffOn F2 _ isOpen_dom hF2 1 _
    have hF2'law : ∀ P x, InP P → x ∈ Dom n → F2' (P * x) = χ2 P * F2' x := by
      rw [hF2'e]; exact rit_law F2 (Dom n) isOpen_dom hF2 χ2 hUP h2 1 _
    have hlaw : ∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x →
        G (p * x) * F2 (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * (G x * F2 x) := by
      intro p x hp hp0 hx
      have hP : InP p := ⟨hp, hp0⟩
      rw [hGlaw p x hP (gset_sub_dom hx), h2 p x hP (gset_sub_dom hx), ← h12 p hP]
      ring
    have hInf := hI n G F2 (Dom n) isOpen_dom gset_sub_dom hG hF2 hlaw Kg μ ι hι hK (W 0)
    have hA : Continuous (fun k => rit F1 (N + 1) W (ι k) * F2 (ι k)) :=
      (cont_on_K _ (rit_contDiffOn F1 _ isOpen_dom hF1 (N + 1) W) Kg ι hι hdom).mul
        (cont_on_K _ hF2 Kg ι hι hdom)
    have hB : Continuous (fun k => G (ι k) * F2' (ι k)) :=
      (cont_on_K _ hG Kg ι hι hdom).mul (cont_on_K _ hF2' Kg ι hι hdom)
    have hsplit : (∫ k, rit F1 (N + 1) W (ι k) * F2 (ι k) ∂μ) + ∫ k, G (ι k) * F2' (ι k) ∂μ = 0 := by
      rw [← integral_add (hint _ hA) (hint _ hB)]
      exact hInf
    have hIH := ih F2' hF2' hF2'law (fun i => W i.succ) (fun a b => hW _ _)
    have hr : rit F2' N (fun i => W (Fin.rev i).succ) = rit F2 (N + 1) (fun i => W (Fin.rev i)) := by
      rw [hF2'def, rit_snoc F2 (W 0) N, snoc_rev]
    rw [hr] at hIH
    rw [pow_succ]
    linear_combination hsplit - hIH

end PositivityTheory.Rg.Sw.LVs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatC
section
noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem diag_single_diag (u v : Fin n → ℂ) (r s : Fin n) (c : ℂ) :
    diagonal u * single r s c * diagonal v = single r s (u r * c * v s) := by
  ext i k
  rw [mul_diagonal, diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · simp

theorem inG_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, star (d1 a) * d1 a = 1) (h2 : ∀ a, star (d2 a) * d2 a = 1) :
    InG (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n) := by
  unfold InG
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  have hK : Dᴴ * fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1) * D =
      fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1) := by
    rw [hD, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [diagonal_conjTranspose]
    exact ⟨funext fun a => h1 a, funext fun a => h2 a⟩
  calc (Cm n * D * CmI n)ᴴ * JJ n * (Cm n * D * CmI n)
      = (CmI n)ᴴ * (Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D) * CmI n := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (CmI n)ᴴ * ((Cm n)ᴴ * JJ n * Cm n) * CmI n := by rw [cmH_JJ_cm, hK]
    _ = (Cm n * CmI n)ᴴ * JJ n * (Cm n * CmI n) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [cm_mul_cmI, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem prod_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n *
      (Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n) = 1 := by
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'
  have hDD : D * D' = 1 := by
    rw [hD, hD', fromBlocks_multiply, ← fromBlocks_one]
    simp [diagonal_mul_diagonal, h1, h2]
    done
  calc Cm n * D * CmI n * (Cm n * D' * CmI n) = Cm n * D * (CmI n * Cm n) * D' * CmI n := by
        simp only [Matrix.mul_assoc]
    _ = Cm n * (D * D') * CmI n := by
        rw [cmI_mul_cm, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hDD, Matrix.mul_one, cm_mul_cmI]

theorem inv_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n)⁻¹ =
      Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n := by
  exact Matrix.inv_eq_right_inv (prod_conjDiag d1 d2 h1 h2)

theorem cmI_N_cm (E : Matrix (Fin n) (Fin n) ℂ) :
    CmI n * fromBlocks 0 E 0 0 * Cm n = ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks E E (-E) (-E) := by
  rw [CmI, Cm, Matrix.smul_mul, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_multiply]
  congr 1
  simp
  done

theorem conj_nU (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) (r s : Fin n) :
    Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n * nU (single r s 1) *
        (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n)⁻¹ - 1 =
      Cm n * (((2 * Complex.I)⁻¹ : ℂ) • fromBlocks (single r s (d1 r * (d1 s)⁻¹)) (single r s (d1 r * (d2 s)⁻¹))
        (-single r s (d2 r * (d1 s)⁻¹)) (-single r s (d2 r * (d2 s)⁻¹))) * CmI n := by
  rw [inv_conjDiag d1 d2 h1 h2]
  have hn : nU (single r s (1 : ℂ)) = 1 + fromBlocks 0 (single r s 1) 0 0 := by
    rw [nU, ← fromBlocks_one, fromBlocks_add]
    simp
  rw [hn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, prod_conjDiag d1 d2 h1 h2, add_sub_cancel_left]
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'
  calc Cm n * D * CmI n * fromBlocks 0 (single r s 1) 0 0 * (Cm n * D' * CmI n)
      = Cm n * (D * (CmI n * fromBlocks 0 (single r s 1) 0 0 * Cm n) * D') * CmI n := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [cmI_N_cm]
        congr 2
        rw [Matrix.mul_smul, Matrix.smul_mul, hD, hD', fromBlocks_multiply, fromBlocks_multiply]
        simp [diag_single_diag]
        done

end PositivityTheory.Rg.Sw.LVs.TC
end
end

