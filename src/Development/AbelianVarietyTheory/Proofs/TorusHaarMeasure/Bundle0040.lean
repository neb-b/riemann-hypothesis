module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CurvatureMarginsDefiniteCase
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem margins_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X), X.p0 = 0 → Nonempty X.Ψ → (∀ x, Xa.ps0 x = 0) → IsStrictDom X Xa.L → (∀ τ (a b : Fin r), a ≤ b → (Xa.Fp - kapW X - nd X • Xa.L) τ b ≤ (Xa.Fp - kapW X - nd X • Xa.L) τ a) → Margins X Xa := by
  intro E _ _ _ r X Xa h0 _ hps _ hgap
  have hA : ∀ (m : ℝ) x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ := fun m x0 ho z hz ξ => by
    rw [← IW.leviM_comb X x0 ho hz]
    exact (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ m
      (fun τ i j a _ => hgap τ i j a) (fun τ i j _ b => hgap τ i j b)
      (fun τ i j a _ => absurd a (by omega)) x0 ho z hz ξ
  have hB : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ leviO X x0 (phla X Xa.L) z ξ := fun x0 ho z hz ξ => by
    by_cases hξ : ξ = 0
    · subst hξ; simp [leviO, leviM, leviV]
    · exact (Xa.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le
  have hP : ∀ x0 z ξ, leviO X x0 Xa.ps0 z ξ = 0 := fun x0 z ξ => by
    simp only [leviO, leviM, hps]
    rw [RgC.leviV_const, Complex.zero_re]
  refine ⟨⟨_, _, lt_add_one _, lt_add_one _, fun t _ x0 ho z hz ξ => ?_⟩,
    ⟨_, _, lt_add_one _, lt_add_one _, fun x0 ho z hz ξ => ?_⟩, hB, ⟨0, fun x _ => (hps x).le⟩,
    fun k P hP => ⟨hP, fun ξ hξ =>
      (GlobalTheory.PoincareSeriesCompare.not_isIso_of_definite X (Or.inl h0) ξ hξ).elim⟩⟩
  · rw [hP, mul_zero, add_zero]
    exact hA _ x0 ho z hz ξ
  · exact (hA _ x0 ho z hz ξ).trans
      (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (hB x0 ho z hz ξ)))

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExpLeOfNegLogSqrtLe
section
noncomputable section

namespace GlobalTheory.BigRec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem pnorm_pos_of_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (P : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have := (hx τ).2 i
    rw [h0] at this
    simp at this
  refine mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_)
  exact Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _

theorem exp_le_of_neg_log_sqrt_le {S a b : ℝ} (hS : 0 < S) (h : -Real.log (Real.sqrt S) ≤ a + b) :
    Real.exp (-(2 * b)) ≤ Real.exp (2 * a) * S := by
  rw [Real.log_sqrt hS.le] at h
  calc Real.exp (-(2 * b)) ≤ Real.exp (2 * a + Real.log S) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (2 * a) * S := by rw [Real.exp_add, Real.exp_log hS]

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_rdU_ne_zero {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) {N : ℕ} (w : Fin N → Rul Xo c)
    (hw : NoCommonZero Xo c w) (k : U.Comp) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ∃ m, rdU U (w m) k x ≠ 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨m, hm⟩ := hw (CAt σ) (U.un k ⟨x, hx⟩)
  refine ⟨m, ?_⟩
  have e : rdU U (w m) k x = toC (evR Xo c (w m) (U.un k ⟨x, hx⟩)) := dif_pos hx
  rw [e]
  exact hm

theorem model_ineq_of_log_bound {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (σ : c.F →+* ℂ)
    {N N' : ℕ} (i : ℕ) (w : Fin N → Rul Xo c) (e : Fin (N' + 1) ≃ Fin N) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (th tableLineDegreeFive DF tableLineDegreeTwo cc : ℝ) (hσ : GoodEmb c σ)
    (hI : I2AtFramePoints U xR (fun m => w (e m)) (a, n) th tableLineDegreeFive DF cc) (hw : NoCommonZero Xo c w)
    (k : (U σ).Comp) (eW : ReciprocityTheory.ChartRestriction.G.FD.Wt ((U σ).X k).Ψ r)
    (et : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r → ℂ)
    (het : ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm eW et x ≤
      Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x - tableLineDegreeTwo))) :
    ReciprocityTheory.ChartRestriction.G.AR.Up.InterpolationModelInequalities ((U σ).X k) (laU (U σ) a n k) eW (fun m => rdU (U σ) (w m) k) et cc i
      (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th) := by
  refine ⟨⟨Real.exp (2 * (tableLineDegreeFive * DF)) * lieFac Dw xR a ^ 2, fun x hx => ?_⟩,
    Real.exp (2 * (i * tableLineDegreeTwo)), fun x hx => ?_⟩
  · have h1 := hI σ hσ k x hx
    have hs : ∑ m, recNrm (U σ) xR a n (w (e m)) k x ^ 2 =
        lieFac Dw xR a ^ 2 * ∑ m, ((U σ).X k).pnorm (laU (U σ) a n k) (rdU (U σ) (w m) k) x ^ 2 := by
      rw [Finset.mul_sum, ← e.sum_comp]
      exact Finset.sum_congr rfl fun m _ => by rw [recNrm, mul_pow]
    have hpos : 0 < ∑ m, ((U σ).X k).pnorm (laU (U σ) a n k) (rdU (U σ) (w m) k) x ^ 2 := by
      obtain ⟨m, hm⟩ := exists_rdU_ne_zero (U σ) w hw k hx
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨m, Finset.mem_univ _, pow_pos (pnorm_pos_of_ne_zero _ _ _ hx hm) 2⟩
    simp only [hs] at h1
    have h2 := exp_le_of_neg_log_sqrt_le (mul_pos (pow_pos (lieFac_pos Dw xR a) 2) hpos) h1
    rw [← mul_assoc, ← mul_assoc] at h2
    exact h2
  · have h0 : 0 ≤ ((U σ).X k).pnorm eW et x :=
      mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
        Real.rpow_nonneg (norm_nonneg _) _)
    refine (pow_le_pow_left₀ h0 (het x hx) 2).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring

end Gen

theorem firstMin_fn_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (th : ℝ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    0 ≤ ReciprocityTheory.ChartRestriction.G.I2.phiFD X th x := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD
  split_ifs <;> positivity

theorem firstMin_fn_lower {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {th : ℝ} (hth : 0 < th) :
    ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 →
      ca / X.la1 x ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.phiFD X th x := by
  have hf : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    have h1 := IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hrd : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.rd
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))) _
  refine ⟨2 * ReciprocityTheory.ChartRestriction.G.I2.PT.f E / ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2, th, by positivity, hth,
    fun x _ hlt => ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD
  rw [if_pos hlt, div_div]


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem phRec_of_firstMin : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (wL : WeightFamilies.Wt D j) (N N' i : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (e : Fin (N' + 1) ≃ Fin N) (et : (recB h.toLawsCore).Cusp j (etWt D j i)) (th tableLineDegreeFive DF tableLineDegreeTwo c : ℝ), GoodEmb T.Q.c σ → 0 < th → I2AtFramePoints (T.U j) (xiR D) (fun m => (w (e m)).1) (wtA wL, wL.n) th tableLineDegreeFive DF c → NoCommonZero (T.Q.Xo j) T.Q.c (fun m => (w m).1) → (∀ k : (T.U j σ).Comp, ∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (etWt D j i)) ((etWt D j i)).n k) (rdU (T.U j σ) et.1 k) x ≤ Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x - tableLineDegreeTwo))) → PhRec h j σ w i et c := by
  intro D T h j hj σ wL N N' i w e et th tableLineDegreeFive DF tableLineDegreeTwo c hσ hth hI hw het k
  exact ⟨ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th, fun x _ => firstMin_fn_nonneg _ th x,
    firstMin_fn_lower _ hth,
    model_ineq_of_log_bound (T.U j) (xiR D) σ i (fun m => (w m).1) e (wtA wL) wL.n th tableLineDegreeFive DF tableLineDegreeTwo c hσ hI hw k _ _
      (het k)⟩

end GlobalTheory.BigRec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExtendByZeroStrictAntiOfPositiveGaps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

namespace GlobalTheory.RunWts


open ReciprocityTheory.ChartRestriction.G.AR.Inst in
theorem nd_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    {f p q : ℕ} (hf : Module.finrank ℚ E = 2 * f) (hr : p + q = r) :
    nd X = f * (p * q + p * (p - 1) / 2 + q * (q - 1) / 2) := by
  classical
  have h1 := GlobalTheory.TwoLines.two_mul_card_cmType X
  have h2 : X.Ψ.card = f := by omega
  have h3 : Fintype.card {x : Fin r × Fin r // x.2 < x.1} = r.choose 2 := by
    rw [Nat.choose_two_right, ← GlobalTheory.FlagDim.card_pairs_lt, Nat.card_eq_fintype_card]
    exact Fintype.card_congr ((Equiv.prodComm _ _).subtypeEquiv fun _ => Iff.rfl)
  unfold nd
  rw [Fintype.card_prod, Fintype.card_coe, h2, h3, ← hr, ← Nat.choose_two_right, ← Nat.choose_two_right,
    Nat.add_choose_eq]
  simp [Finset.Nat.antidiagonal_succ]
  left
  ring

theorem extendByZero_strictAnti_of_positive_gaps {p : ℕ} (l : Fin p → ℕ) (hl : Antitone l) (hg : ∀ i : Fin p, i.1 + 1 < p → 0 < gapZ l i)
    {a b : ℕ} (hab : a < b) (hb : b < p) : ext0 l b < ext0 l a := by
  have h1 := hg ⟨a, by omega⟩ (by show a + 1 < p; omega)
  have h2 : a + 1 < p := by omega
  unfold gapZ at h1
  rw [dite_eq_left h2] at h1
  have h3 : l ⟨b, hb⟩ ≤ l ⟨a + 1, h2⟩ := hl (show a + 1 ≤ b by omega)
  unfold ext0
  rw [dite_eq_left hb, dite_eq_left (by omega : a < p)]
  simp only at h1
  omega

theorem fdiv_pos {c : ℤ} {t s : ℕ} (ht : 0 < t) (h : ((t * (t + s) : ℕ) : ℤ) ≤ c) : 0 < Int.fdiv c t := by
  have ht' : (0 : ℤ) < t := by exact_mod_cast ht
  rw [Int.fdiv_eq_ediv_of_nonneg _ ht'.le]
  have : (1 : ℤ) ≤ c / t := by
    refine Int.le_ediv_of_mul_le ht' ?_
    push_cast at h
    nlinarith [Int.natCast_nonneg s]
  omega

theorem wtA_lt_upper {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) {a b : ℕ} (hab : a < b)
    (h : ext0 (w.aP t) b < ext0 (w.aP t) a) : wtA w (DV.tauEmb D t, b) < wtA w (DV.tauEmb D t, a) := by
  classical
  simp only [wtA]
  refine Finset.sum_lt_sum (fun s _ => add_le_add ?_ ?_) ⟨t, Finset.mem_univ _, add_lt_add_of_lt_of_le ?_ ?_⟩
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone s) hab.le
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti s) hab.le
    · exact le_rfl
  · simpa using h
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti t) hab.le
    · exact le_rfl

theorem wtA_lt_lower {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) {a b : ℕ} (hab : a < b)
    (h : ext0 (w.aM t) b < ext0 (w.aM t) a) :
    wtA w (conjEmb (DV.tauEmb D t), b) < wtA w (conjEmb (DV.tauEmb D t), a) := by
  classical
  simp only [wtA]
  refine Finset.sum_lt_sum (fun s _ => add_le_add ?_ ?_) ⟨t, Finset.mem_univ _, add_lt_add_of_le_of_lt ?_ ?_⟩
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone s) hab.le
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti s) hab.le
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone t) hab.le
    · exact le_rfl
  · simpa using h

theorem strictDom_smul_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (a z : (E →+* ℂ) × ℕ → ℕ) (hz : ∀ x, z x = 0) (n m s : ℕ) (k : U.Comp) (hs : 0 < s) (hm : m / 2 < s * (n / 2))
    (hu : ∀ τ : (U.X k).Ψ, ∀ x y, x < y → (U.X k).p0 + y < r →
      a (Function.invFun (relab c σ) τ.1, y) < a (Function.invFun (relab c σ) τ.1, x))
    (hl : ∀ τ : (U.X k).Ψ, ∀ x y, x < y → y < (U.X k).p0 →
      a (Function.invFun (relab c σ) (conjEmb τ.1), y) < a (Function.invFun (relab c σ) (conjEmb τ.1), x)) :
    ReciprocityTheory.ChartRestriction.G.AR.Inst.IsStrictDom (U.X k) (s • laU U a n k - laU U z m k) := by
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have hm' : ((m / 2 : ℕ) : ℤ) < s * ((n / 2 : ℕ) : ℤ) := by exact_mod_cast hm
  intro τ
  refine ⟨fun i j hij hj => ?_, fun i j hi hij => ?_, fun i j hi hj => ?_⟩
  · have hij' : (i : ℕ) < j := hij
    have h1 : ¬ (U.X k).p0 ≤ (j : ℕ) := by omega
    have h2 : ¬ (U.X k).p0 ≤ (i : ℕ) := by omega
    have h3 := hl τ ((U.X k).p0 - 1 - j) ((U.X k).p0 - 1 - i) (by omega) (by omega)
    have h4 := mul_lt_mul_of_pos_left (Int.ofNat_lt.2 h3) hs'
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [laU, h1, h2, if_false, hz, nsmul_eq_mul]
    linarith
  · have hij' : (i : ℕ) < j := hij
    have h1 : (U.X k).p0 ≤ (j : ℕ) := by omega
    have h3 := hu τ (i - (U.X k).p0) (j - (U.X k).p0) (by omega) (by omega)
    have h4 := mul_lt_mul_of_pos_left (Int.ofNat_lt.2 h3) hs'
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [laU, h1, hi, if_true, hz, nsmul_eq_mul]
    linarith
  · have h1 : ¬ (U.X k).p0 ≤ (i : ℕ) := by omega
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [laU, h1, hj, if_true, if_false, hz, nsmul_eq_mul]
    have h3 := mul_nonneg hs'.le (Int.natCast_nonneg
      (a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (i : ℕ))))
    have h4 := mul_nonneg hs'.le (Int.natCast_nonneg
      (a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0)))
    push_cast at hm' ⊢
    linarith


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem weights_of_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (ka wL wF : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((T.U j σ).X k) = WeightFamilies.dimY D j ∧ ReciprocityTheory.ChartRestriction.G.AR.Inst.IsStrictDom ((T.U j σ).X k) (laU (T.U j σ) (wtA wL) (wL).n k) ∧ (∀ i : ℕ, 0 < i → ReciprocityTheory.ChartRestriction.G.AR.Inst.IsStrictDom ((T.U j σ).X k) ((i * g0 D) • (laU (T.U j σ) (wtA wL) (wL).n k) - (laU (T.U j σ) (wtA (etWt D j i)) ((etWt D j i)).n k))) ∧ (j = D.R.m → ((T.U j σ).X k).p0 = 0 ∨ D.R.r ≤ ((T.U j σ).X k).p0) := by
  intro D T h j hj ka wL wF large₂ CK C1 A1 h0 Tn nP nW hS σ hσ k
  obtain ⟨-, hgP, hgM, -, -, -, -, -, -, -, -, -, -, -, ⟨hn, hLP, hLM⟩, -, -, -, -, -, -, h40, -⟩ := hS
  obtain ⟨-, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr1, -⟩ := hnum j hj
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨-, hk, -⟩ := h.unf j hj σ hσ
  obtain ⟨hp0, hΨ⟩ := hk k
  obtain ⟨hbij, hrt, hcj, -⟩ := GlobalTheory.Relab.relab_good _ T.Q.H T.Q.l T.Q.c σ hσ
  replace hbij : Function.Bijective (relab T.Q.c σ) := hbij
  replace hrt : ∀ τ, relab T.Q.c σ τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 ↔ τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hrt
  replace hcj : ∀ τ, relab T.Q.c σ (conjEmb τ) = conjEmb (relab T.Q.c σ τ) := hcj
  rw [hp, hq] at hpq
  rw [hq] at hp0
  have hT : 0 < Tp D j Tn := by unfold Tp; omega
  have key : ∀ τ : ((T.U j σ).X k).Ψ, ∃ t, Function.invFun (relab T.Q.c σ) τ.1 = DV.tauEmb D t ∧
      Function.invFun (relab T.Q.c σ) (conjEmb τ.1) = conjEmb (DV.tauEmb D t) := by
    rintro ⟨τ, hτ⟩
    obtain ⟨ρ, rfl⟩ := hbij.2 τ
    obtain ⟨t, rfl⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q h.pins.1 ρ ((hrt ρ).1 ((hΨ _).1 hτ))
    refine ⟨t, Function.leftInverse_invFun hbij.1 _, ?_⟩
    show Function.invFun (relab T.Q.c σ) (conjEmb (relab T.Q.c σ (DV.tauEmb D t))) = _
    rw [← hcj]
    exact Function.leftInverse_invFun hbij.1 _
  have hu : ∀ τ : ((T.U j σ).X k).Ψ, ∀ x y, x < y → ((T.U j σ).X k).p0 + y < D.R.r →
      wtA wL (Function.invFun (relab T.Q.c σ) τ.1, y) < wtA wL (Function.invFun (relab T.Q.c σ) τ.1, x) := by
    intro τ x y hxy hy
    obtain ⟨t, ht, -⟩ := key τ
    rw [ht]
    refine wtA_lt_upper wL t hxy (extendByZero_strictAnti_of_positive_gaps _ (wL.aPlus_antitone t) (fun i hi => ?_) hxy (by omega))
    rw [hLP t i, if_pos hi]
    exact fdiv_pos hT (hgP t i hi)
  have hl : ∀ τ : ((T.U j σ).X k).Ψ, ∀ x y, x < y → y < ((T.U j σ).X k).p0 →
      wtA wL (Function.invFun (relab T.Q.c σ) (conjEmb τ.1), y) <
        wtA wL (Function.invFun (relab T.Q.c σ) (conjEmb τ.1), x) := by
    intro τ x y hxy hy
    obtain ⟨t, -, ht⟩ := key τ
    rw [ht]
    refine wtA_lt_lower wL t hxy (extendByZero_strictAnti_of_positive_gaps _ (wL.aM_anti t) (fun i hi => ?_) hxy (by omega))
    rw [hLM t i, if_pos hi]
    exact fdiv_pos hT (hgM t i hi)
  have h20 : 20 ≤ wL.n / 2 := by omega
  refine ⟨nd_eq _ hf hpq, ?_, fun i hi => ?_, fun hm => Or.inl ?_⟩
  · have h1 := strictDom_smul_sub (T.U j σ) (wtA wL) (fun _ => 0) (fun _ => rfl) wL.n 0 1 k one_pos (by omega) hu hl
    have h2 : laU (T.U j σ) (fun _ => 0) 0 k = 0 := by
      funext τ x
      simp [laU]
    rwa [h2, one_smul, sub_zero] at h1
  · have hg : 0 < i * g0 D := Nat.mul_pos hi (by unfold g0; omega)
    refine strictDom_smul_sub (T.U j σ) (wtA wL) _ (fun x => ?_) wL.n _ _ k hg ?_ hu hl
    · simp [wtA, etWt, wscalar, ext0]
    · show g0 D * i / 2 < i * g0 D * (wL.n / 2)
      have := Nat.mul_le_mul_left (i * g0 D) h20
      rw [mul_comm (g0 D) i]
      omega
  · rw [hp0, hm]
    simp [Ranks.sigW]

end GlobalTheory.RunWts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndependentDifferentialsRatiosOfTrdegValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

namespace GlobalTheory.BigRec

theorem adjoin_div_le {K F κ : Type} [Field K] [Field F] [Algebra K F] (a : κ → F) (p q : κ) (hq : a q ≠ 0) :
    IntermediateField.adjoin K (Set.range fun k => a k / a p) ≤
      IntermediateField.adjoin K (Set.range fun k => a k / a q) := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨k, rfl⟩
  have hk : a k / a q ∈ IntermediateField.adjoin K (Set.range fun k => a k / a q) :=
    IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
  have hp : a p / a q ∈ IntermediateField.adjoin K (Set.range fun k => a k / a q) :=
    IntermediateField.subset_adjoin K _ ⟨p, rfl⟩
  have hkp := div_mem hk hp
  rwa [div_div_div_cancel_right₀ hq] at hkp

theorem ratio_single {F Γ : Type} [Field F] [AddCommGroup Γ] (g : Γ) (a b : F) (hb : b ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := F) (AddMonoidAlgebra.single g a : AddMonoidAlgebra F Γ)
      (AddMonoidAlgebra.single g b) = a / b := by
  have hex : ∃ c : F, (AddMonoidAlgebra.single g a : AddMonoidAlgebra F Γ) = c • AddMonoidAlgebra.single g b :=
    ⟨a / b, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ a hb]⟩
  rw [ReciprocityTheory.ChartRestriction.G.T0.ratio, dite_eq_left hex]
  have hc := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at hc
  have hv : a = hex.choose * b := by
    first
    | exact AddMonoidAlgebra.single_injective g hc
    | simpa using hc
  exact eq_div_of_mul_eq hb hv.symm

theorem independent_differentials_ratios_of_trdeg_values {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)] (hG : GenFrEx Xo c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))
    {κ : Type} (w : κ → Rul Xo c) (e : κ ≃ Fin (d.N + 1)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (htr : FnTrdeg Xo c d.D) (hw : ∀ k, d.w (e k) = valC hG a n (w k)) (hb : ∀ Z, d.w (d.jc Z) Z ≠ 0)
    (hbig : ∀ Z : Comp Xo c, ∃ k₀, evC hG Z (w k₀) ≠ 0 ∧ Algebra.trdeg c.F
      (IntermediateField.adjoin c.F (Set.range fun k => evC hG Z (w k) / evC hG Z (w k₀))) = d.D) :
    A1Bigness d := by
  unfold A1Bigness
  intro Z
  have hfull : Algebra.trdeg c.F (Om Z) = d.D := by
    unfold FnTrdeg at htr
    exact htr Z
  refine (GlobalTheory.trdegD_iff_exists_linearIndependent_D d Z hfull (hb Z)).mp ?_
  unfold ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD
  obtain ⟨k₀, hk₀, htk⟩ := hbig Z
  have hwZ : ∀ k, d.w (e k) Z = AddMonoidAlgebra.single (wtZ a n) (evC hG Z (w k)) := by
    intro k
    rw [hw k]
    rfl
  set kc := e.symm (d.jc Z) with hkc
  have hjc : d.jc Z = e kc := (e.apply_symm_apply _).symm
  have hc0 : evC hG Z (w kc) ≠ 0 := by
    intro h0
    apply hb Z
    rw [hjc, hwZ, h0, AddMonoidAlgebra.single_zero]
  have hrange : (Set.range fun j => ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (d.w j Z) (d.w (d.jc Z) Z)) =
      Set.range fun k => evC hG Z (w k) / evC hG Z (w kc) := by
    rw [← e.surjective.range_comp]
    congr 1
    funext k
    change ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w (e k) Z) (d.w (d.jc Z) Z) = _
    rw [hjc, hwZ, hwZ]
    exact ratio_single _ _ _ hc0
  rw [hrange]
  have hsame : IntermediateField.adjoin c.F (Set.range fun k => evC hG Z (w k) / evC hG Z (w kc)) =
      IntermediateField.adjoin c.F (Set.range fun k => evC hG Z (w k) / evC hG Z (w k₀)) :=
    le_antisymm (adjoin_div_le (fun k => evC hG Z (w k)) kc k₀ hk₀)
      (adjoin_div_le (fun k => evC hG Z (w k)) k₀ kc hc0)
  rw [hsame]
  exact htk


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem independent_differentials_ratios_cusp_forms_trdeg : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (e : Fin G.N ≃ Fin (d.N + 1)), d.D = WeightFamilies.dimY D j → (∀ k, d.w (e k) = valC hG (wtA wL) wL.n (G.w k).1) → (∀ Z, d.w (d.jc Z) Z ≠ 0) → (∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z (G.w k₀).1 ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z (G.w k).1 / evC hG Z (G.w k₀).1)) = WeightFamilies.dimY D j) → A1Bigness d := by
  intro D T h j hj hG ka wL wF G _ d e hD hw hb hbig
  have hpin : T.Q.PinDat := by
    have hp := h.toLawsCore.pins
    unfold Par.Pins at hp
    exact hp.2.2.2
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q hpin j hj).2
  rw [← hD] at htr hbig
  exact independent_differentials_ratios_of_trdeg_values hG d (fun k => (G.w k).1) e (wtA wL) wL.n htr hw hb hbig

end GlobalTheory.BigRec
end

