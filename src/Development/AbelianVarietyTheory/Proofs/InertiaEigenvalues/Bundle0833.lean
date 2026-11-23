module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
section
open NumberField IsDedekindDomain GlobalTheory.JSW
open scoped ENNReal

noncomputable section
namespace GlobalTheory.RSPole.EulerPole

open Filter Topology GlobalTheory.RSPole

theorem schurAt_const_zero {n : ℕ} (a : Fin n → ℂ) : GlobalTheory.JSW.schurAt (fun _ => 0) a = 1 := by
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

theorem one_le_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) : 1 ≤ schurDir q a x := by
  unfold schurDir
  refine le_trans ?_ (ENNReal.le_tsum ⟨fun _ => 0, antitone_const⟩)
  simp [schurAt_const_zero]

theorem hasProd_of_one_le {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) :
    HasProd f (⨆ s : Finset I, ∏ i ∈ s, f i) :=
  tendsto_atTop_iSup fun _ _ hst => Finset.prod_le_prod_of_subset_of_one_le' hst fun i _ _ => hf i

theorem finset_prod_le_tprod {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (s : Finset I) :
    ∏ i ∈ s, f i ≤ ∏' i, f i := by
  rw [(hasProd_of_one_le f hf).tprod_eq]; exact le_iSup (fun s : Finset I => ∏ i ∈ s, f i) s

theorem le_tprod_of_one_le {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (i : I) : f i ≤ ∏' i, f i := by
  simpa using finset_prod_le_tprod f hf {i}

theorem hasProd_toReal {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (hfin : ∏' i, f i ≠ ⊤) :
    HasProd (fun i => (f i).toReal) (∏' i, f i).toReal := by
  have h := hasProd_of_one_le f hf
  rw [← h.tprod_eq] at h
  have := (ENNReal.tendsto_toReal hfin).comp h
  simpa [HasProd, Function.comp_def, ENNReal.toReal_prod] using this

theorem schurAt_conj {n : ℕ} (l : Fin n → ℕ) (a : Fin n → ℂ) :
    GlobalTheory.JSW.schurAt l (fun i => starRingEnd ℂ (a i)) = starRingEnd ℂ (GlobalTheory.JSW.schurAt l a) := by
  rw [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schurAt, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Filter Topology GlobalTheory.RSPole

def schurTerm (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) : ℝ :=
  ‖GlobalTheory.JSW.schurAt l.1 a‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x))

theorem schurTerm_nonneg (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (l) : 0 ≤ schurTerm q a x l := by
  unfold schurTerm; positivity

theorem schurDir_eq (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) :
    schurDir q a x = ∑' l, ENNReal.ofReal (schurTerm q a x l) := rfl

theorem summable_schurTerm (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (hfin : schurDir q a x ≠ ⊤) :
    Summable (schurTerm q a x) := by
  rw [schurDir_eq] at hfin
  exact (ENNReal.summable_toReal hfin).congr fun l => ENNReal.toReal_ofReal (schurTerm_nonneg q a x l)

theorem toReal_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) :
    (schurDir q a x).toReal = ∑' l, schurTerm q a x l := by
  rw [schurDir_eq, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun l => ENNReal.toReal_ofReal (schurTerm_nonneg q a x l)

theorem term_eq (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo le_rfl l.1) (fun i => (α i : ℂ)) *
      GlobalTheory.JSW.schurAt l.1 (fun j => (((Units.map (starRingEnd ℂ).toMonoidHom ∘ α) j : ℂˣ) : ℂ)) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) = ((schurTerm q (fun i => (α i : ℂ)) x l : ℝ) : ℂ) := by
  rw [GlobalTheory.JSW.padTo_self]
  have h1 : (fun j => (((Units.map (starRingEnd ℂ).toMonoidHom ∘ α) j : ℂˣ) : ℂ)) =
      fun j => starRingEnd ℂ (α j : ℂ) := by
    funext j; simp
  rw [h1, schurAt_conj, Complex.mul_conj']
  have h2 : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]; push_cast; rfl
  have h3 : (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)) = ((q : ℝ) ^ (-x)) ^ (∑ i, l.1 i) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]; ring_nf
  rw [h2, schurTerm, h3]
  push_cast
  ring

theorem locL_eq (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) (x : ℝ) (hfin : schurDir q (fun i => (α i : ℂ)) x ≠ ⊤) :
    locL q (Finset.univ.val.map α) ((Finset.univ.val.map α).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) =
      (((schurDir q (fun i => (α i : ℂ)) x).toReal : ℝ) : ℂ) := by
  have hs := summable_schurTerm q _ x hfin
  rw [Multiset.map_map]
  have key := cauchy_locL le_rfl α (Units.map (starRingEnd ℂ).toMonoidHom ∘ α) q (x : ℂ) (hs.congr fun l => by
    rw [← norm_pow, ← norm_mul, term_eq, Complex.norm_real, Real.norm_of_nonneg (schurTerm_nonneg _ _ _ _)])
  have h2 : HasSum (fun l => ((schurTerm q (fun i => (α i : ℂ)) x l : ℝ) : ℂ))
      (((schurDir q (fun i => (α i : ℂ)) x).toReal : ℝ) : ℂ) := by
    rw [toReal_schurDir]; exact Complex.hasSum_ofReal.mpr hs.hasSum
  simp only [term_eq] at key
  exact key.unique h2

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Filter Topology GlobalTheory.RSPole Set

theorem schurTerm_anti (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) {x y : ℝ} (hxy : x ≤ y) (l) :
    schurTerm q a y l ≤ schurTerm q a x l := by
  unfold schurTerm
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) ?_) (by positivity)
  have : (0 : ℝ) ≤ ((∑ i, l.1 i : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem schurDir_anti (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) {x y : ℝ} (hxy : x ≤ y) :
    schurDir q a y ≤ schurDir q a x := by
  rw [schurDir_eq, schurDir_eq]
  exact ENNReal.tsum_le_tsum fun l => ENNReal.ofReal_le_ofReal (schurTerm_anti q hq a hxy l)

theorem continuousOn_toReal_schurDir (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) (x₀ : ℝ)
    (hfin : schurDir q a x₀ ≠ ⊤) : ContinuousOn (fun x => (schurDir q a x).toReal) (Ici x₀) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : ContinuousOn (fun x => ∑' l, schurTerm q a x l) (Ici x₀) := by
    refine continuousOn_tsum (u := schurTerm q a x₀) (fun l => ?_) (summable_schurTerm q a x₀ hfin) ?_
    · unfold schurTerm
      exact (continuous_const.mul (continuous_const.rpow (by fun_prop) fun _ => Or.inl hqpos.ne')).continuousOn
    · intro l x hx
      rw [Real.norm_of_nonneg (schurTerm_nonneg _ _ _ _)]
      exact schurTerm_anti q hq a hx l
  exact hc.congr fun x _ => toReal_schurDir q a x

theorem one_le_toReal_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (hfin : schurDir q a x ≠ ⊤) :
    1 ≤ (schurDir q a x).toReal := by
  have := ENNReal.toReal_mono hfin (one_le_schurDir q a x)
  simpa using this

section
variable {I : Type} (q : I → ℕ) {n : ℕ} (a : I → Fin n → ℂ)

theorem schurDir_ne_top (x : ℝ) (h : eulD q a x ≠ ⊤) (w : I) : schurDir (q w) (a w) x ≠ ⊤ :=
  ne_top_of_le_ne_top h (le_tprod_of_one_le (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) w)

theorem hasProd_eulD (x : ℝ) (h : eulD q a x ≠ ⊤) :
    HasProd (fun w => (schurDir (q w) (a w) x).toReal) (eulD q a x).toReal :=
  hasProd_toReal (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) h

theorem summable_log (x : ℝ) (h : eulD q a x ≠ ⊤) :
    Summable fun w => Real.log (schurDir (q w) (a w) x).toReal := by
  have h1 : ∀ w, 1 ≤ (schurDir (q w) (a w) x).toReal :=
    fun w => one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x h w)
  refine summable_of_sum_le (c := Real.log (eulD q a x).toReal) (fun w => Real.log_nonneg (h1 w)) fun s => ?_
  rw [← Real.log_prod (fun w _ => (zero_lt_one.trans_le (h1 w)).ne')]
  refine Real.log_le_log (Finset.prod_pos fun w _ => zero_lt_one.trans_le (h1 w)) ?_
  rw [← ENNReal.toReal_prod]
  exact ENNReal.toReal_mono h (finset_prod_le_tprod (fun w => schurDir (q w) (a w) x)
    (fun w => one_le_schurDir _ _ _) s)

theorem toReal_eulD_eq_exp (x : ℝ) (h : eulD q a x ≠ ⊤) :
    (eulD q a x).toReal = Real.exp (∑' w, Real.log (schurDir (q w) (a w) x).toReal) := by
  have h1 : ∀ w, 0 < (schurDir (q w) (a w) x).toReal :=
    fun w => zero_lt_one.trans_le (one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x h w))
  exact (hasProd_eulD q a x h).unique (Real.hasProd_of_hasSum_log h1 (summable_log q a x h).hasSum)

theorem continuousOn_toReal_eulD (hq : ∀ w, 1 ≤ q w) (x₀ : ℝ) (hall : ∀ x, x₀ ≤ x → eulD q a x ≠ ⊤) :
    ContinuousOn (fun x => (eulD q a x).toReal) (Ici x₀) := by
  have hx₀ := hall x₀ le_rfl
  have hF : ∀ w x, x₀ ≤ x → 1 ≤ (schurDir (q w) (a w) x).toReal :=
    fun w x hx => one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x (hall x hx) w)
  have hc : ContinuousOn (fun x => ∑' w, Real.log (schurDir (q w) (a w) x).toReal) (Ici x₀) := by
    refine continuousOn_tsum (u := fun w => Real.log (schurDir (q w) (a w) x₀).toReal) (fun w => ?_)
      (summable_log q a x₀ hx₀) ?_
    · exact (continuousOn_toReal_schurDir (q w) (hq w) (a w) x₀ (schurDir_ne_top q a x₀ hx₀ w)).log
        fun x hx => (zero_lt_one.trans_le (hF w x hx)).ne'
    · intro w x hx
      rw [Real.norm_of_nonneg (Real.log_nonneg (hF w x hx))]
      refine Real.log_le_log (zero_lt_one.trans_le (hF w x hx)) ?_
      exact ENNReal.toReal_mono (schurDir_ne_top q a x₀ hx₀ w) (schurDir_anti (q w) (hq w) (a w) hx)
  exact (Real.continuous_exp.comp_continuousOn hc).congr fun x hx => toReal_eulD_eq_exp q a x (hall x hx)
end

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Set

theorem eulD_hasProd_locL : ∀ (I : Type) (q : I → ℕ) (n : ℕ) (α : I → Fin n → ℂˣ), (∀ w, 2 ≤ q w) →
    (∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤) →
    (∀ x : ℝ, 1 < x →
      HasProd (fun w => locL (q w) (Finset.univ.val.map (α w))
          ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ))
        (((GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) ∧
      1 ≤ (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) ∧
    ContinuousOn (fun x => (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) (Set.Ioi 1) := by
  intro I q n α hq hfin
  set a : I → Fin n → ℂ := fun w i => ((α w i : ℂˣ) : ℂ) with ha
  have hq1 : ∀ w, 1 ≤ q w := fun w => le_trans (by norm_num) (hq w)
  refine ⟨fun x hx => ⟨?_, ?_⟩, ?_⟩
  · have h := (hasProd_eulD q a x (hfin x hx)).map Complex.ofRealHom Complex.continuous_ofReal
    have he : (fun w => locL (q w) (Finset.univ.val.map (α w))
        ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) =
        Complex.ofRealHom ∘ fun w => (schurDir (q w) (a w) x).toReal := by
      funext w
      exact locL_eq (q w) (α w) x (schurDir_ne_top q a x (hfin x hx) w)
    rw [he]; exact h
  · have h1 : (1 : ℝ≥0∞) ≤ eulD q a x := by
      simpa [eulD] using finset_prod_le_tprod (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) ∅
    simpa using ENNReal.toReal_mono (hfin x hx) h1
  · intro x hx
    have hx' : (1 + x) / 2 < x := by simp only [mem_Ioi] at hx; linarith
    have h := continuousOn_toReal_eulD q a hq1 ((1 + x) / 2) fun y hy => hfin y (by simp only [mem_Ioi] at hx; linarith)
    exact (h.continuousAt (Ici_mem_nhds hx')).continuousWithinAt

end GlobalTheory.RSPole.EulerPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProduct
section
open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.ZEul

open GlobalTheory.JSW

def partVec {n : ℕ} (l : {l : Fin n → ℕ // Antitone l}) : Fin n → ℤ := fun j => (l.1 j : ℤ)

theorem partVec_injective {n : ℕ} : Function.Injective (partVec (n := n)) := by
  intro a b h
  apply Subtype.ext; funext j
  have := congrFun h j
  simpa [partVec] using this

theorem partVec_valid {n : ℕ} (l : {l : Fin n → ℕ // Antitone l}) :
    (∀ i, 0 ≤ partVec l i) ∧ Antitone (partVec l) :=
  ⟨fun i => Int.natCast_nonneg _, fun a b h => Int.ofNat_le.2 (l.2 h)⟩

theorem mem_range_partVec {n : ℕ} {v : Fin n → ℤ} (hv : (∀ i, 0 ≤ v i) ∧ Antitone v) :
    v ∈ Set.range (partVec (n := n)) :=
  ⟨⟨fun i => (v i).toNat, fun a b h => Int.toNat_le_toNat (hv.2 h)⟩, by
    funext j; simp [partVec, Int.toNat_of_nonneg (hv.1 j)]⟩

theorem rsTerm_partVec (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    rsTerm q α β x (partVec l) =
      schurAt l.1 α * conj (schurAt l.1 β) * ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) := by
  rw [rsTerm, if_pos (partVec_valid l)]
  simp [partVec]


open Classical in
def sqTerm (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : ℝ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    ‖schurAt (fun i => (v i).toNat) α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))
  else 0

theorem sqTerm_nonneg (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : 0 ≤ sqTerm q α x v := by
  unfold sqTerm
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact le_rfl

theorem sqTerm_zero (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : sqTerm q α x 0 = 1 := by
  have hs : schurAt (fun _ : Fin n => 0) α = 1 := by rw [schurAt, schur_zero]; simp
  rw [sqTerm, if_pos ⟨fun i => le_rfl, antitone_const⟩]
  simp [hs]

theorem sqTerm_partVec (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    sqTerm q α x (partVec l) = ‖schurAt l.1 α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)) := by
  rw [sqTerm, if_pos (partVec_valid l)]
  simp [partVec]

theorem norm_cpow_pow (q : ℕ) (hq : 0 < q) (x : ℝ) (k : ℕ) :
    ‖((q : ℂ) ^ (-(x : ℂ))) ^ k‖ = (q : ℝ) ^ (-((k : ℝ) * x)) := by
  rw [norm_pow, Complex.norm_natCast_cpow_of_pos hq]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1; ring

theorem norm_rsTerm_le (q : ℕ) (hq : 0 < q) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) :
    ‖rsTerm q α β x v‖ ≤ (sqTerm q α x v + sqTerm q β x v) / 2 := by
  by_cases hv : (∀ i, 0 ≤ v i) ∧ Antitone v
  · rw [rsTerm, if_pos hv, sqTerm, if_pos hv, sqTerm, if_pos hv, norm_mul, norm_mul, Complex.norm_conj,
      norm_cpow_pow q hq]
    have hw : 0 ≤ (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_nonneg (sq_nonneg (‖schurAt (fun i => (v i).toNat) α‖ - ‖schurAt (fun i => (v i).toNat) β‖)) hw]
  · rw [rsTerm, if_neg hv, sqTerm, if_neg hv, sqTerm, if_neg hv]; simp

end GlobalTheory.ZEul

namespace GlobalTheory.ZEul

open GlobalTheory.JSW

theorem summable_sqTerm {I : Type} (q : I → ℕ) {n : ℕ} (α : I → Fin n → ℂ) (x : ℝ)
    (h : GlobalTheory.RSPole.eulD q α x ≠ ⊤) :
    Summable fun p : I × {v : Fin n → ℤ // v ≠ 0} => sqTerm (q p.1) (α p.1) x p.2 := by
  set f : I → (Fin n → ℤ) → ℝ≥0∞ := fun i v => ENNReal.ofReal (sqTerm (q i) (α i) x v) with hf
  have hf0 : ∀ i, f i 0 = 1 := fun i => by simp [hf, sqTerm_zero]
  have hloc : ∀ i, ∑' v, f i v = GlobalTheory.RSPole.schurDir (q i) (α i) x := by
    intro i
    rw [← (partVec_injective (n := n)).tsum_eq]
    · rw [GlobalTheory.RSPole.schurDir]
      refine tsum_congr fun l => ?_
      simp only [hf, sqTerm_partVec]
    · intro v hv
      by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
      · exact mem_range_partVec hval
      · exact absurd (by simp [hf, sqTerm, if_neg hval]) hv
  have hE : ∑' l : I →₀ (Fin n → ℤ), l.prod f = GlobalTheory.RSPole.eulD q α x := by
    rw [(GlobalTheory.EulerSum.euler_product_intVec_ennreal n f hf0).2, GlobalTheory.RSPole.eulD]
    exact tprod_congr hloc
  have hinj : Function.Injective fun p : I × {v : Fin n → ℤ // v ≠ 0} => Finsupp.single p.1 p.2.1 := by
    intro p p' hp
    rcases (Finsupp.single_eq_single_iff _ _ _ _).1 hp with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Prod.ext h1 (Subtype.ext h2)
    · exact absurd h1 p.2.2
  have hle : ∑' p : I × {v : Fin n → ℤ // v ≠ 0}, f p.1 p.2 ≤ ∑' l : I →₀ (Fin n → ℤ), l.prod f := by
    have hc : (fun p : I × {v : Fin n → ℤ // v ≠ 0} => f p.1 p.2) =
        fun p => (fun l : I →₀ (Fin n → ℤ) => l.prod f) (Finsupp.single p.1 p.2.1) := by
      funext p; simp only; rw [Finsupp.prod_single_index (hf0 p.1)]
    rw [hc]
    exact (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective hinj _); exact _root_.le_rfl)
  have hfin : ∑' p : I × {v : Fin n → ℤ // v ≠ 0}, f p.1 p.2 ≠ ⊤ := ne_top_of_le_ne_top (hE ▸ h) hle
  refine (ENNReal.summable_toReal hfin).congr fun p => ?_
  simp only [hf]
  exact ENNReal.toReal_ofReal (sqTerm_nonneg _ _ _ _)

theorem hasSum_rsTerm_local (q : ℕ) {n : ℕ} (α β : Fin n → ℂˣ) (x : ℝ)
    (hs : Summable fun v : Fin n → ℤ => ‖rsTerm q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v‖) :
    HasSum (fun v => rsTerm q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v)
      (locL q (Finset.univ.val.map α) ((Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom))
        (x : ℂ)) := by
  set β' : Fin n → ℂˣ := fun j => Units.map (starRingEnd ℂ).toMonoidHom (β j) with hβ'
  have hconj : ∀ l : Fin n → ℕ, schurAt l (fun j => (β' j : ℂ)) = conj (schurAt l fun j => (β j : ℂ)) := by
    intro l
    rw [schurAt, schurAt, MvPolynomial.eval₂_comp_left, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
      (Int.castRingHom ℂ)]
    rfl
  have hm : (Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom) = Finset.univ.val.map β' :=
    Multiset.map_map _ _ _
  rw [hm]
  have hs' : Summable fun l : {l : Fin n → ℕ // Antitone l} =>
      ‖schurAt (padTo le_rfl l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β' j : ℂ))‖ *
        ‖(q : ℂ) ^ (-(x : ℂ))‖ ^ (∑ i, l.1 i) := by
    refine (hs.comp_injective partVec_injective).congr fun l => ?_
    simp only [Function.comp, rsTerm_partVec, padTo_self, hconj, norm_mul, norm_pow, Complex.norm_conj]
  have hc := cauchy_locL le_rfl α β' q (x : ℂ) hs'
  rw [← (partVec_injective (n := n)).hasSum_iff]
  · convert hc using 1
    funext l
    simp only [Function.comp, rsTerm_partVec, padTo_self, hconj]
  · intro v hv
    by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
    · exact absurd (mem_range_partVec hval) hv
    · rw [rsTerm, if_neg hval]

theorem hasSum_rsTerm_finsupp : ∀ {I : Type} (q : I → ℕ) {n : ℕ} (α β : I → Fin n → ℂˣ) (x : ℝ), 1 < x → (∀ i, 2 ≤ q i) →
    GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    HasSum (fun l : I →₀ (Fin n → ℤ) => l.prod fun i v => GlobalTheory.ZEul.rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v)
      (∏' i, GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i)) ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) := by
  intro I q n α β x _ hq hα hβ
  set f : I → (Fin n → ℤ) → ℂ := fun i v => rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v with hfdef
  have hf0 : ∀ i, f i 0 = 1 := fun i => rsTerm_zero _ _ _ _
  have hA := summable_sqTerm q (fun i j => (α i j : ℂ)) x hα
  have hB := summable_sqTerm q (fun i j => (β i j : ℂ)) x hβ
  have hsum : Summable fun p : I × {v : Fin n → ℤ // v ≠ 0} => ‖f p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by
        simpa only [hfdef] using norm_rsTerm_le (q p.1) (by have := hq p.1; omega) (fun j => (α p.1 j : ℂ)) (fun j => (β p.1 j : ℂ)) x p.2.1) ((hA.add hB).div_const 2)
  obtain ⟨hN, -, hE⟩ := GlobalTheory.EulerSum.euler_product_intVec n f hf0 hsum
  have hloc : ∀ i, ∑' v, f i v = locL (q i) (Finset.univ.val.map (α i))
      ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) :=
    fun i => (hasSum_rsTerm_local (q i) (α i) (β i) x (GlobalTheory.EulerSum.summable_norm_local f hsum i)).tsum_eq
  rw [← hE.trans (tprod_congr hloc)]
  exact hN.of_norm.hasSum

end GlobalTheory.ZEul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomain
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open GlobalTheory.UnitaryBC GlobalTheory.ShortVecDecay
open scoped ComplexConjugate nonZeroDivisors ContDiff ENNReal

namespace GlobalTheory.RSThetaLow

theorem exists_tsum_zpow_le_low {T s : ℝ} (hT : 1 < T) (hs : 0 < s) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ u : ℝ, 0 < u →
    ∑' n : ℤ, (if T ^ n * u ≤ 1 then ENNReal.ofReal ((T ^ n * u) ^ s) else 0) ≤ B := by
  obtain ⟨B, hB, h⟩ := GlobalTheory.RSTheta.exists_tsum_zpow_le hT hs
  refine ⟨B, hB, fun u hu => ?_⟩
  have hT0 : 0 < T := one_pos.trans hT
  refine le_of_eq_of_le ?_ (h u⁻¹ (inv_pos.2 hu))
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply]
  have hp : 0 < T ^ n * u⁻¹ := by positivity
  have e : T ^ (-n) * u = (T ^ n * u⁻¹)⁻¹ := by
    rw [_root_.zpow_neg, mul_inv, inv_inv]
  rw [e, Real.inv_rpow hp.le, Real.rpow_neg hp.le]
  simp only [inv_le_one₀ hp]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem integrableOn_absDet_rpow (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ s)
      (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hm : MeasurableSet {g | δ g ≤ 1} := (isClosed_le hδc continuous_const).measurableSet
  have hc : Continuous fun g => δ g ^ s := hδc.rpow_const fun g => Or.inl (hδ0 g).ne'
  refine ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (.of_forall fun g => Real.rpow_nonneg (hδ0 g).le _)).2 ?_⟩
  rw [Set.inter_comm, ← Measure.restrict_restrict hm, ← lintegral_indicator hm]
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * splitCentre E a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * splitCentre E a 1 ^ n = ratGL E a γ' * splitCentre E a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hd := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hd]; exact measure_ne_top _ _
  rw [← GlobalTheory.ThetaUnfold.lintegral_unfold μ (latticeGL E a) (ratGL E a).range (fun n : ℤ => splitCentre E a 1 ^ n)
    (Equiv.ofBijective φ hφ) (fun _ => rfl) hd h𝓕 _
    (by rintro _ ⟨γ, rfl⟩ g; simp only [Set.indicator_apply, Set.mem_setOf_eq]; rw [show δ (ratGL E a γ * g) = δ g from hδr γ g])
    ((hc.measurable.ennreal_ofReal.indicator hm).aemeasurable)]
  obtain ⟨B, hB, h⟩ := exists_tsum_zpow_le_low hT1 hs
  refine (lintegral_mono (g := fun _ => B) fun g => ?_).trans_lt ?_
  · refine le_of_eq_of_le (tsum_congr fun n => ?_) (h _ (hδ0 g))
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [hδz]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hB.lt_top h1.lt_top

theorem integrableOn_absDet_rpow_low : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
    ∀ s : ℝ, 0 < s → IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ s)
      (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ :=
  fun _ _ _ _ _ ha μ _ _ h𝓕 _ hs => integrableOn_absDet_rpow ha μ h𝓕 hs

end GlobalTheory.RSThetaLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariantStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  first | exact @GlobalTheory.ZUnfWt.wt_measurable_invariant | exact GlobalTheory.ZUnfWt.wt_measurable_invariant | (intros; apply GlobalTheory.ZUnfWt.wt_measurable_invariant; all_goals assumption)
end

