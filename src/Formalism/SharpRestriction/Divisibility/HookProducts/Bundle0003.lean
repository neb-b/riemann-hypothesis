module

public import Formalism.LocalToGlobal.Divisibility.Numbers
public import Mathlib
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.SharpRestriction.Divisibility.HookProducts.Bundle0002
public import Formalism.SharpRestriction.Divisibility.HookProducts.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.HookProducts.HookProd
section
namespace Formalism.MainNotions.DIV.HookProducts

namespace HookLengthProduct

open Finset

def K (n : ℕ) (a : ℕ → ℕ) (c : ℕ) : ℕ := ((range n).filter (fun l => c < a l)).card

def E (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ c ∈ range (a i), ((a i - c) + (K n a c - i) - 1)

def D (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ l ∈ Ioo i n, (a i + l - a l - i)

def F (n : ℕ) (a : ℕ → ℕ) : ℕ := ∏ i ∈ range n, (a i + n - 1 - i).factorial

theorem K_succ_of_zero (m : ℕ) (a : ℕ → ℕ) (h : a m = 0) (c : ℕ) : K (m + 1) a c = K m a c := by
  simp [K, Finset.range_add_one, Finset.filter_insert, h]

theorem K_zero (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) : K n a 0 = n := by
  unfold K
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro l hl
  have := h1 l (Finset.mem_range.mp hl)
  omega

theorem K_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) (c : ℕ) :
    K n a (c + 1) = K n (fun i => a i - 1) c := by
  unfold K
  congr 1
  apply Finset.filter_congr
  intro l hl
  have := h1 l (Finset.mem_range.mp hl)
  show c + 1 < a l ↔ c < a l - 1
  omega

theorem prod_range_pos (m : ℕ) (hm : 1 ≤ m) (f : ℕ → ℕ) :
    ∏ c ∈ range m, f c = f 0 * ∏ c ∈ range (m - 1), f (c + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.prod_range_succ', mul_comm, Nat.add_sub_cancel]

theorem E_succ_zero (m : ℕ) (a : ℕ → ℕ) (h : a m = 0) : E (m + 1) a = E m a := by
  unfold E
  rw [Finset.prod_range_succ, h, Finset.range_zero, Finset.prod_empty, mul_one]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun c _ => ?_))
  rw [K_succ_of_zero m a h c]

theorem D_succ (m : ℕ) (a : ℕ → ℕ) :
    D (m + 1) a = (∏ i ∈ range m, (a i + m - a m - i)) * D m a := by
  unfold D
  rw [Finset.prod_range_succ]
  have h0 : Ioo m (m + 1) = ∅ := by
    ext x
    simp only [Finset.mem_Ioo]
    simp
    try omega
  rw [h0, Finset.prod_empty, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < m := Finset.mem_range.mp hi
  have h1 : Ioo i (m + 1) = insert m (Ioo i m) := by
    ext x
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  rw [h1, Finset.prod_insert (by simp)]

theorem F_succ_zero (m : ℕ) (a : ℕ → ℕ) (h : a m = 0) :
    F (m + 1) a = (∏ i ∈ range m, (a i + m - a m - i)) * F m a := by
  unfold F
  rw [Finset.prod_range_succ, ← Finset.prod_mul_distrib]
  have hl : a m + (m + 1) - 1 - m = 0 := by omega
  rw [hl, Nat.factorial_zero, mul_one]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < m := Finset.mem_range.mp hi
  have e1 : a i + (m + 1) - 1 - i = (a i + m - 1 - i) + 1 := by omega
  have e2 : a i + m - a m - i = (a i + m - 1 - i) + 1 := by omega
  rw [e1, e2, Nat.factorial_succ]

theorem E_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) :
    E n a = (∏ i ∈ range n, (a i + n - 1 - i)) * E n (fun i => a i - 1) := by
  simp only [E]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  have hai := h1 i hi'
  rw [prod_range_pos (a i) hai]
  congr 1
  · rw [K_zero n a h1]
    omega
  · refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [K_shift n a h1 c]
    omega

theorem D_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) :
    D n a = D n (fun i => a i - 1) := by
  simp only [D]
  refine Finset.prod_congr rfl (fun i hi => Finset.prod_congr rfl (fun l hl => ?_))
  have hi' : i < n := Finset.mem_range.mp hi
  have hl' : l < n := (Finset.mem_Ioo.mp hl).2
  have := h1 i hi'
  have := h1 l hl'
  omega

theorem F_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) :
    F n a = (∏ i ∈ range n, (a i + n - 1 - i)) * F n (fun i => a i - 1) := by
  simp only [F]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  have := h1 i hi'
  have e : a i + n - 1 - i = (a i - 1 + n - 1 - i) + 1 := by omega
  rw [e, Nat.factorial_succ]

theorem E_mul_D (n : ℕ) :
    ∀ a : ℕ → ℕ, (∀ i l, i < l → l < n → a l ≤ a i) → E n a * D n a = F n a := by
  induction n with
  | zero => intro a _; simp [E, D, F]
  | succ m ih =>
    suffices H : ∀ k (a : ℕ → ℕ), a m = k → (∀ i l, i < l → l < m + 1 → a l ≤ a i) →
        E (m + 1) a * D (m + 1) a = F (m + 1) a from fun a h => H _ a rfl h
    intro k
    induction k with
    | zero =>
      intro a ha hmono
      rw [E_succ_zero m a ha, D_succ, F_succ_zero m a ha,
        ← ih a (fun i l hil hl => hmono i l hil (by omega))]
      ring
    | succ k ihk =>
      intro a ha hmono
      have h1 : ∀ i < m + 1, 1 ≤ a i := by
        intro i hi
        rcases Nat.lt_or_ge i m with h | h
        · have := hmono i m h (by omega)
          omega
        · have e : i = m := by omega
          rw [e, ha]
          omega
      rw [E_shift (m + 1) a h1, D_shift (m + 1) a h1, F_shift (m + 1) a h1,
        ← ihk (fun i => a i - 1) (by show a m - 1 = k; omega)
          (fun i l hil hl => by
            have := hmono i l hil hl
            show a l - 1 ≤ a i - 1
            omega)]
      ring

theorem hookProd_eq_E (n : ℕ) (a : ℕ → ℕ) (w : List ℕ) (hw : w.SortedGE)
    (hwe : w = (List.range n).map a) : Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens w hw) = E n a := by
  subst hwe
  set μ := YoungDiagram.ofRowLens ((List.range n).map a) hw with hμ
  have hmem : ∀ i j, (i, j) ∈ μ ↔ i < n ∧ j < a i := by
    intro i j
    rw [hμ, YoungDiagram.mem_ofRowLens]
    simp
  have hrow : ∀ i < n, μ.rowLen i = a i := by
    intro i hi
    apply eq_of_forall_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, hmem]
    simp [hi]
  have hcol : ∀ c, μ.colLen c = K n a c := by
    intro c
    have e : (range n).filter (fun l => c < a l) = range (μ.colLen c) := by
      ext i
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen,
        hmem]
    unfold K
    rw [e, Finset.card_range]
  unfold Formalism.LatticeIndexTer.hookProd E
  rw [Finset.prod_finset_product μ.cells (range n) (fun i => range (a i))]
  · refine Finset.prod_congr rfl (fun i hi => Finset.prod_congr rfl (fun c _ => ?_))
    rw [hrow i (Finset.mem_range.mp hi), hcol c]
  · rintro ⟨i, j⟩
    rw [YoungDiagram.mem_cells, hmem]
    simp

end HookLengthProduct

open HookLengthProduct in
theorem hookProd_mul_prod (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i)
    (hmono : ∀ i l, i < l → l < n → a l ≤ a i) :
    Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens (((List.range n).map a).insertionSort (· ≥ ·))
              List.sortedGE_insertionSort) *
              (∏ i ∈ Finset.range n, ∏ l ∈ Finset.Ioo i n, (a i + l - a l - i)) =
      ∏ i ∈ Finset.range n, (a i + n - 1 - i).factorial := by
  have hsorted : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a := by
    apply List.Pairwise.insertionSort_eq
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_map, List.length_range] at hi hj
    simp only [List.getElem_map, List.getElem_range]
    exact hmono i j hij hj
  rw [hookProd_eq_E n a _ List.sortedGE_insertionSort hsorted]
  exact E_mul_D n a hmono

end Formalism.MainNotions.DIV.HookProducts
end

-- bundled from Formalism.SharpRestriction.Divisibility.HookProducts.RBTieMu
section
open Matrix NumberField Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

section Mu

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mem_dualLat_iff {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (A : Submodule (𝓞 K) V) (f : Module.Dual K V) :
    f ∈ Formalism.HN.dualLat A ↔ ∀ x ∈ A, f x ∈ Set.range (algebraMap (𝓞 K) K) := Iff.rfl

theorem cnorm_isom {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (W : Matrix m n ℂ)
    (hW : Wᴴ * W = 1) (c : n → ℂ) : Formalism.HermitianLatticesTheory.cnorm (W *ᵥ c) = Formalism.HermitianLatticesTheory.cnorm c := by
  have key : ∀ {ι : Type} [Fintype ι] (u : ι → ℂ), ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
    intro ι _ u
    push_cast
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  have h : ((∑ i, ‖(W *ᵥ c) i‖ ^ 2 : ℝ) : ℂ) = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [key, key, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hW,
      Matrix.one_mulVec]
  exact_mod_cast h

theorem muDual_tie (A : Formalism.BasicNotions.HLat K) {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K))
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (e : (Fin n → K) ≃ₗ[K] A.V)
    (hlat : A.L = L.map ((e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K)))
    (hmet : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXA : ∀ v, IsUnit (A.X v).det) (hXE : ∀ v, IsUnit (XE v).det) :
    Formalism.HN.muDef (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat L) = A.muDual := by
  set ψ : Module.Dual K (Fin n → K) →ₗ[K] Module.Dual K A.V := Module.Dual.transpose e.symm.toLinearMap with hψ
  have hψx : ∀ f x, ψ f x = f (e.symm x) := fun f x => by simp [hψ, Module.Dual.transpose_apply]

  have hnA : ∀ v f, Formalism.HermitianLatticesTheory.normAt A.b.dualBasis (Formalism.HN.dualFrame A.X) v (ψ f) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) v f := by
    intro v f
    have hv := vecAt_map (Pi.basisFun K (Fin n)).dualBasis A.b.dualBasis v ψ f
    have hT : LinearMap.toMatrix (Pi.basisFun K (Fin n)).dualBasis A.b.dualBasis ψ =
        (LinearMap.toMatrix A.b (Pi.basisFun K (Fin n)) e.symm.toLinearMap)ᵀ := by
      rw [hψ, LinearMap.toMatrix_transpose]
    have hW : ((A.X v)ᵀ * (cQ A.b e v)ᵀ) = ((cU A.b A.X XE e v)ᴴ)ᵀ * (XE v)ᵀ := by
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, cQ_mul_XA A.b A.X XE e v hmet (hXA v) (hXE v)]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
    rw [hv, hT, dualFrame_inv A.X v (hXA v), dualFrame_inv XE v (hXE v), Matrix.mulVec_mulVec]
    have hQ : (LinearMap.toMatrix A.b (Pi.basisFun K (Fin n)) e.symm.toLinearMap)ᵀ.map v.embedding = (cQ A.b e v)ᵀ := rfl
    rw [hQ, hW, ← Matrix.mulVec_mulVec, cnorm_isom]
    rw [conjT_transpose_isom, cU_conj_mul A.b A.X XE e v hmet (hXE v), Matrix.transpose_one]
  have hn : ∀ f, ‖((Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)).comp ψ.toAddMonoidHom) f‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) f‖ := by
    intro f
    have h2 : ‖((Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)).comp ψ.toAddMonoidHom) f‖ ^ 2 =
        ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) f‖ ^ 2 := by
      rw [AddMonoidHom.comp_apply, Formalism.HN.PlaceOperatorNorms.norm_sq_realize, Formalism.HN.PlaceOperatorNorms.norm_sq_realize]
      simp only [LinearMap.toAddMonoidHom_coe, hnA]
    rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_sq (norm_nonneg _)]

  have hzl : Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)) (Formalism.HN.dualLat A.L) =
      Formalism.HN.zl ((Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)).comp ψ.toAddMonoidHom) (Formalism.HN.dualLat L) := by
    ext y
    rw [Formalism.HN.satR_mem_zl, Formalism.HN.satR_mem_zl]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨Module.Dual.transpose e.toLinearMap g, ?_, ?_⟩
      · rw [mem_dualLat_iff] at hg ⊢
        intro x hx
        simp only [Module.Dual.transpose_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
        exact hg (e x) (by rw [hlat]; exact ⟨x, hx, rfl⟩)
      · congr 1
        exact LinearMap.ext fun x => by simp [hψx, Module.Dual.transpose_apply]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨ψ f, ?_, rfl⟩
      rw [mem_dualLat_iff] at hf ⊢
      intro z hz
      rw [hlat] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      rw [hψx]
      simpa using hf x hx
  have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)) (Formalism.HN.dualLat A.L) =
      Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE)) (Formalism.HN.dualLat L) := by
    rw [← slope_eq_of_norm_eq _ _ hn (Formalism.HN.dualLat L)]
    unfold Formalism.HN.slope
    rw [hzl]
  unfold Formalism.BasicNotions.HLat.muDual Formalism.BasicNotions.HLat.dualB Formalism.BasicNotions.HLat.dualX Formalism.BasicNotions.HLat.dualL Formalism.HN.muDef
  rw [hs]

end Mu

end Formalism.MainNotions.DIV.HookProducts.RBTie
end
end

