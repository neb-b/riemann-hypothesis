module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormProdSignMulDetSubmatrixSubOneLe
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PeriodTorusConstantEqBase
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFirstMinimumLowerBoundNearMax
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD Topology

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace CuspNet

theorem exists_finset_rmul_near_one {r : ℕ} (X : Data E r) {K : Set (Frame X.Ψ r)}
    (hK : IsCompact K) (hKd : K ⊆ X.dom) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : Finset (Frame X.Ψ r), (∀ y ∈ N, y ∈ K) ∧ ∀ x ∈ K, ∃ A : Frame X.Ψ r,
      (∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ δ) ∧ rmul x A ∈ N := by
  obtain ⟨N, hN, hcov⟩ := hK.elim_nhdsWithin_subcover
    (fun y => {x | ∀ τ a b, ‖((mat x τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖ ≤ δ})
    (fun y hy => by
      simp only [Set.ofPred_forall]
      refine Filter.iInter_mem.2 fun τ => Filter.iInter_mem.2 fun a =>
        Filter.iInter_mem.2 fun b => ?_
      have hc : ContinuousOn (fun x : Frame X.Ψ r =>
          ‖((mat x τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖) K := by
        refine (ContinuousOn.sub ?_ continuousOn_const).norm
        simp only [Matrix.mul_apply]
        refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul ?_ continuousOn_const
        exact GramSchmidtCont.continuousOn_inv_apply (GramSchmidtCont.continuous_mat X τ)
          (fun x hx => (hKd hx τ).1) a k
      have h0 : ‖((mat y τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖ < δ := by
        rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hKd hy τ).1), Matrix.one_apply,
          sub_self, norm_zero]
        exact hδ
      exact (hc y hy).eventually (eventually_le_nhds h0))
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
  refine ⟨fun τ => ((mat x τ)⁻¹ * mat y τ : Matrix (Fin r) (Fin r) ℂ), hxy, ?_⟩
  convert hy using 1
  funext τ
  show mat x τ * ((mat x τ)⁻¹ * mat y τ) = mat y τ
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hKd hx τ).1)]

end CuspNet

namespace CuspNet

end CuspNet

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HermFormDiagonalEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem hermForm_diagonal_eq (d z w : Fin g → ℂ) :
    hermForm (Matrix.diagonal d) z w = ∑ j, d j * z j * conj (w j) := by
  simp only [hermForm, dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  ring

theorem selfD_of_isSympl (hs : IsSympl X bas) : SelfD X X.Λ := by
  refine ⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, ha⟩ : ∃ a, (bas a : Fin r → E) = x := ⟨bas.symm ⟨x, hx⟩, by simp⟩
    obtain ⟨b, hb⟩ : ∃ b, (bas b : Fin r → E) = y := ⟨bas.symm ⟨y, hy⟩, by simp⟩
    refine ⟨-omegaStd a b, ?_⟩
    rw [← ha, ← hb, hs a b]
    push_cast
    rfl
  · have hint : ∀ c, ∃ n : ℤ, GlobalTheory.SW.crd X bas x c = n := by
      intro c
      cases c with
      | inl j =>
        obtain ⟨k, hk⟩ := h _ (bas (Pi.single (Sum.inr j) 1)).2
        have e := GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x)
          (fun c => (((Pi.single (Sum.inr j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))
        rw [GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk] at e
        simp [Pi.single_apply] at e
        exact ⟨-k, by push_cast; linarith⟩
      | inr j =>
        obtain ⟨k, hk⟩ := h _ (bas (Pi.single (Sum.inl j) 1)).2
        have e := GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x)
          (fun c => (((Pi.single (Sum.inl j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))
        rw [GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk] at e
        simp [Pi.single_apply] at e
        exact ⟨k, by linarith⟩
    choose n hn using hint
    have hx : x = (bas n : Fin r → E) := by
      rw [← GlobalTheory.SW.vecQ_crd X bas x, ← GlobalTheory.SW.vecQ_intCast]
      congr 1
      funext c
      exact hn c
    rw [hx]
    exact (bas n).2

theorem hx_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ x ∈ X.dom, X.IsOrtho x → (∀ z z', hx X bas idx x z z' = ∑ j, ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z' j)) ∧ (∀ u, (hx X bas idx x (pv X idx x u) (pv X idx x u)).re = ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 u)) ∧ (∀ u ∈ X.Λ, u ≠ 0 → X.firstMinimumSq x ≤ (hx X bas idx x (pv X idx x u) (pv X idx x u)).re) ∧ IsUnitFr X x ∧ SelfD X X.Λ := by
  intro E _ _ _ r X g bas idx hs x hxd ho
  have hHm := GlobalTheory.ThFr.Hm_of_isOrtho idx hs ho
  have h1 : ∀ z z', hx X bas idx x z z' = ∑ j, ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z' j) := by
    intro z z'
    rw [hx_eq_hermForm idx x z z', hHm, hermForm_diagonal_eq]
  have h2 : ∀ u, (hx X bas idx x (pv X idx x u) (pv X idx x u)).re =
      ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 u) := by
    intro u
    rw [hx_eq_hermForm idx x, hHm]
    exact (congrArg Complex.re (GlobalTheory.ThFr.hermForm_diagonal_c_self idx hxd ho u)).trans
      (Complex.ofReal_re _)
  have h0 : ∀ z, 0 ≤ (hx X bas idx x z z).re := by
    intro z
    rw [h1, Complex.re_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    have e : ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z j) =
        ((X.c (idx j).1 * Complex.normSq (z j) : ℝ) : ℂ) := by
      rw [_root_.mul_assoc, Complex.mul_conj]
      push_cast
      ring
    rw [e, Complex.ofReal_re]
    exact mul_nonneg (GlobalTheory.ThFr.c_pos X _).le (Complex.normSq_nonneg _)
  refine ⟨h1, h2, ?_, ?_, selfD_of_isSympl hs⟩
  · intro u hu hne
    rw [h2]
    unfold Data.firstMinimumSq
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro t ⟨v, -, -, rfl⟩
      rw [← h2]
      exact h0 _
    · exact ⟨u, hu, hne, rfl⟩
  · unfold IsUnitFr
    intro τ i
    unfold dmin lminor
    rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp_apply, Complex.norm_real]
    unfold sgn
    split_ifs <;> simp

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NetSizeCubic
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.NetSize

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_two_lt_d9; linarith

lemma eps_pos {M f w k : ℝ} (hM : 1 ≤ M) (hf : 1 ≤ f) (hw : 0 < w) (hk : 0 < k) :
    0 < epStar M f w k := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := Real.pi_pos
  unfold epStar
  exact lt_min one_pos (by positivity)

lemma neg_log_eps_le {M f w k L : ℝ} (hM : 1 ≤ M) (hf : 1 ≤ f) (hw : 0 < w) (hk : 0 < k)
    (hL : 1 ≤ L) (h1 : Real.log f ≤ 2 * L) (h2 : Real.log M ≤ 30 * L)
    (h3 : Real.log w ≤ 3 * L) (h4 : Real.log k ≤ 4 * L) :
    -Real.log (epStar M f w k) ≤ 41 * L := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi := Real.pi_gt_three
  have hl1 := log_two_le_one
  unfold epStar
  rcases le_total 1 (Real.pi / (M * (f * w + 2) * k * Real.log 2)) with h | h
  · rw [min_eq_left h, Real.log_one]; linarith
  · rw [min_eq_right h]
    have hf0 : 0 < f := by linarith
    have hM0 : 0 < M := by linarith
    have hfw : f * w ≤ Real.exp (5 * L) := by
      rw [← Real.log_le_iff_le_exp (by positivity), Real.log_mul hf0.ne' hw.ne']
      linarith
    have he : 1 ≤ Real.exp (5 * L) := Real.one_le_exp (by linarith)
    have hA : Real.log (f * w + 2) ≤ 7 * L := by
      have h5 : f * w + 2 ≤ 2 ^ 2 * Real.exp (5 * L) := by linarith
      have h6 := Real.log_le_log (by positivity) h5
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp] at h6
      push_cast at h6
      linarith
    have hB : Real.log (Real.log 2) ≤ Real.log Real.pi :=
      Real.log_le_log hl2 (by linarith)
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hl2.ne',
      Real.log_mul (by positivity) hk.ne', Real.log_mul hM0.ne' (by positivity)]
    linarith

theorem net_size_cubic : ∀ (f r L M w k0 dE s NA NC g : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ L → 1 ≤ M → 0 < w → 0 < k0 → 1 ≤ dE → 0 ≤ s → 1 ≤ NA → 1 ≤ NC → 1 ≤ g → Real.log f ≤ 2 * L → Real.log r ≤ L → Real.log M ≤ 30 * L → Real.log w ≤ 3 * L → Real.log k0 ≤ 4 * L → Real.log dE ≤ 4 * f * L → Real.log (1 + s) ≤ 3 * L → Real.log NA ≤ 30 * f * L → Real.log NC ≤ 30 * f * L → Real.log g ≤ 30 * f * L → 2 * f * r ^ 2 * Real.log (3 * NA * NC * g * r * (max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * epStar M f w k0))) ^ 2) + (2 * f * r ^ 2 * Real.log (6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s)))) + 2 * f * r ^ 3 * Real.log (r * max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * epStar M f w k0)))) + Real.log 16 ≤ 1000 * (f * r * L) ^ 3 := by
  intro f r L M w k0 dE s NA NC g hf hr hL hM hw hk hd hs hNA hNC hg lf lr lM lw lk ld ls lA lC lg
  have he := eps_pos hM hf hw hk
  have hle := neg_log_eps_le hM hf hw hk hL lf lM lw lk
  have hl1 := log_two_le_one
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ε := epStar M f w k0
  have hf0 : 0 < f := by linarith
  have hr0 : 0 < r := by linarith
  have hL0 : 0 < L := by linarith
  have hd0 : 0 < dE := by linarith
  have hNA0 : 0 < NA := by linarith
  have hNC0 : 0 < NC := by linarith
  have hg0 : 0 < g := by linarith
  have hfL : L ≤ f * L := le_mul_of_one_le_left hL0.le hf
  set B := max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * ε)) with hBdef
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := by linarith
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB : Real.log B ≤ 65 * (f * L) := by
    rcases le_total 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * ε)) with h | h
    · rw [hBdef, max_eq_right h, Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      push_cast
      linarith
    · rw [hBdef, max_eq_left h, Real.log_one]; positivity
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  have T1 : Real.log (3 * NA * NC * g * r * B ^ 2) ≤ 223 * (f * L) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    linarith
  have h6 : Real.log 6000 ≤ 13 := by
    have h := Real.log_le_log (show (0:ℝ) < 6000 by norm_num) (show (6000:ℝ) ≤ 2 ^ 13 by norm_num)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have T2 : Real.log (6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s)))) ≤ 20 * (f * L) := by
    have e : 6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s))) = 6000 * r ^ 4 * (1 + s) := by
      field_simp; ring
    rw [e, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    linarith
  have T3 : Real.log (r * B) ≤ 66 * (f * L) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    linarith
  have T4 : Real.log 16 ≤ 4 := by
    have : (16:ℝ) = 2 ^ 4 := by norm_num
    rw [this, Real.log_pow]; push_cast; linarith
  have hr23 : r ^ 2 ≤ r ^ 3 := pow_le_pow_right₀ hr (by norm_num)
  have hP : f * r ^ 3 * (f * L) ≤ (f * r * L) ^ 3 := by
    have h1 : 1 ≤ f * L ^ 2 := one_le_mul_of_one_le_of_one_le hf (one_le_pow₀ hL)
    calc f * r ^ 3 * (f * L) ≤ f * r ^ 3 * (f * L) * (f * L ^ 2) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = (f * r * L) ^ 3 := by ring
  have hQ : f * r ^ 2 * (f * L) ≤ f * r ^ 3 * (f * L) := by gcongr
  have hone : 1 ≤ (f * r * L) ^ 3 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) hL)
  have U1 := mul_le_mul_of_nonneg_left T1 (show 0 ≤ 2 * f * r ^ 2 by positivity)
  have U2 := mul_le_mul_of_nonneg_left T2 (show 0 ≤ 2 * f * r ^ 2 by positivity)
  have U3 := mul_le_mul_of_nonneg_left T3 (show 0 ≤ 2 * f * r ^ 3 by positivity)
  linarith

end GlobalTheory.NetSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ProjAEqSumReps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VacMean

open GlobalTheory.SW.TensVac GlobalTheory.SW.TensLat

theorem projA_eq_sum_reps {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E}
    {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)} (hA : Good X w A) (hA' : Good X w A')
    {v : TF n g} (hv : IsVac X bas w A' v) {R : Finset (Matrix (Fin n) (Fin r) E)}
    (hR : ∀ y ∈ R, y ∈ A) (hR' : ∀ y ∈ A, ∃! y' ∈ R, y - y' ∈ A') :
    projA X bas w A v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v := by
  have hfix : ∀ y, epsW X w y • heisG X bas y v = v ↔ y ∈ A' := by
    refine fun y => ⟨fun h => ?_, hv.2.2 y⟩
    by_contra hy
    have := hA'.ip_eq_zero idx hs hn hv hy
    rw [h, hv.2.1] at this
    exact one_ne_zero this
  have hiff : ∀ a ∈ A, ∀ b ∈ A, epsW X w a • heisG X bas a v = epsW X w b • heisG X bas b v ↔
      b - a ∈ A' := by
    intro a ha b hb
    rw [← neg_add_eq_sub, ← hfix, ← hA.rho_rho idx hs hn (A.neg_mem ha) hb hv.1]
    constructor
    · intro h
      rw [← h, hA.rho_rho idx hs hn (A.neg_mem ha) ha hv.1, neg_add_cancel,
        rho_zero idx hs hn hv.1]
    · intro h
      conv_lhs => rw [← h]
      rw [hA.rho_rho idx hs hn ha (A.neg_mem ha) (rho_sb idx hs hn b hv.1), add_neg_cancel,
        rho_zero idx hs hn (rho_sb idx hs hn b hv.1)]
  have hinj : Set.InjOn (fun y => epsW X w y • heisG X bas y v) R := fun a ha b hb h =>
    (hR' b (hR b hb)).unique ⟨ha, (hiff a (hR a ha) b (hR b hb)).1 h⟩
      ⟨hb, by rw [sub_self]; exact A'.zero_mem⟩
  have himg : (fun y => epsW X w y • heisG X bas y v) '' A =
      (fun y => epsW X w y • heisG X bas y v) '' R := by
    refine Set.Subset.antisymm ?_ (Set.image_mono fun y hy => hR y hy)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', ⟨h1, h2⟩, -⟩ := hR' y hy
    exact ⟨y', h1, (hiff y' (hR y' h1) y hy).2 h2⟩
  rw [projA, himg, finsum_mem_image hinj, finsum_mem_coe_finset, hinj.ncard_image,
    Set.ncard_coe_finset]

theorem vac_proj_mean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∃ R : Finset (Matrix (Fin n) (Fin r) E), (∀ y ∈ R, y ∈ tens Λ L) ∧ (∀ y ∈ tens Λ L, ∃! y', y' ∈ R ∧ ∀ b, y b - y' b ∈ L) ∧ R.card = ((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup) ^ r ∧ 0 < R.card ∧ projA X bas (w : E) (tens Λ L) v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X (w : E) y • heisG X bas y v := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn w hw L hL Λ hΛ v hv
  have good (Λ) (hΛ : Λ ∈ Vset E n 1) : Good X (w : E) (tens Λ L) :=
    ⟨tens_fg hΛ hL.1, tens_selfDual hΛ hL, fun y hy => epsW_semichar hΛ hL w.isIntegral_coe hw hy⟩
  have hS := GlobalTheory.SW.Base.stdL_mem_Vset (E := E) n 1
  have hidx := (tens_selfDual_semichar_index E r X g bas idx n hs hn w w.isIntegral_coe hw L hL 1
    Λ hΛ).2.2.2.2.2 _ hS
  obtain ⟨v', hv', -⟩ := (good Λ hΛ).vac hs
  have hne : (tens (stdL E n) L).relIndex (tens Λ L) ≠ 0 := by
    intro h
    have := (good Λ hΛ).overlap idx hs hn (good _ hS) hv' hv
    rw [h] at this
    simp at this
  obtain ⟨R, hR, hR'⟩ := TensorLat.exists_reps_of_relIndex_ne_zero hne
  have hc := TensorLat.card_eq_relIndex_of_reps hR hR'
  refine ⟨R, hR, fun y hy => ?_, hc.trans hidx, hc ▸ Nat.pos_of_ne_zero hne,
    projA_eq_sum_reps idx hs hn (good Λ hΛ) (good _ hS) hv hR hR'⟩
  have := hR' y hy
  simp only [mem_tens_stdL] at this
  exact this

end GlobalTheory.Dict.VacMean
end

