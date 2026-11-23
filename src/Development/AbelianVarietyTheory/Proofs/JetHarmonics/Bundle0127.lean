module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegral
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfGe
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.KappaRowsEntriesLeSizes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.WeightRows

theorem kappa_entries_le : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ τ : D.what₂.Tau, (∀ i, i.1 < D.R.k - 1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ wj D j τ + L.Sc) ∧ (∀ i, D.R.k - 1 ≤ i.1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ L.etaSz) ∧ ∀ i, ((kaR Tp hK j).aM τ i : ℝ) ≤ L.etaSz := by
  intro D L Pm Tp hK j hj τ
  have h1 := hj.1
  have h2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have a9 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have big : ∀ i : Fin (D.R.sigW j).1, ((kaR Tp hK j).aP τ i : ℝ) ≤
      ((DV.sigPar D τ i : ℚ) : ℝ) + (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
    intro i
    have hi : i.1 < D.R.k + j - 1 := i.2
    have hi' : i.1 + 2 ≤ D.R.k + j := by omega
    have hr : (i.1 : ℝ) + 2 ≤ D.R.k + j := by exact_mod_cast hi'
    have e1 := kaWt_big D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).1 i
    rw [← e1, DV.aPlusQ_eq] at e2
    unfold DV.eQ at e2
    rw [dite_eq_left ⟨h1, h2⟩] at e2
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at e3
    unfold kaR
    linarith
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i => ?_⟩
  · have b := big i
    unfold DV.sigPar at b
    rw [dite_eq_left hi] at b
    have a1 := (L.cloud_v τ ⟨i.1, hi⟩).2
    unfold wj
    rw [dite_eq_left (by omega : j - 1 < D.R.m)]
    linarith
  · have b := big i
    have hi2 : i.1 < D.R.k + j - 1 := i.2
    have hb : i.1 - (D.R.k - 1) < D.R.m := by omega
    unfold DV.sigPar at b
    rw [dite_eq_right (by omega), dite_eq_left hb] at b
    have a2 := (abs_le.1 (L.be_close τ ⟨i.1 - (D.R.k - 1), hb⟩ ⟨j - 1, by omega⟩)).1
    push_cast at a2 b
    linarith
  · have hs : (D.R.sigW j).2 = D.R.m - j := rfl
    have e1 := kaWt_small D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).2 (Fin.rev i)
    have hi := (Fin.rev i).2
    unfold DV.aMinusQ DV.eQ at e2
    rw [dite_eq_left (by omega), dite_eq_left ⟨h1, h2⟩] at e2
    have a2 := (abs_le.1 (L.be_close τ ⟨j + (Fin.rev i).1, by omega⟩ ⟨j - 1, by omega⟩)).2
    have a8 : (0 : ℝ) ≤ (Fin.rev i).1 := Nat.cast_nonneg _
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) e2
    have e4 := congrArg (fun q : ℤ => (q : ℝ)) e1
    push_cast at e3 e4 a2
    unfold kaR
    linarith

end GlobalTheory.WeightRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulRowsScaledWeightLeKappaRows
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem mul_toNat_fdiv_le (T d : ℕ) (c x : ℤ) (hc : 0 ≤ c) (hx : x ≤ c + 2) :
    (T : ℤ) * ((Int.fdiv x ((T + d + 2 : ℕ) : ℤ)).toNat : ℤ) ≤ c := by
  have hpos : (0 : ℤ) < ((T + d + 2 : ℕ) : ℤ) := by positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hpos.le]
  have h1 := Int.ediv_mul_le x hpos.ne'
  generalize x / ((T + d + 2 : ℕ) : ℤ) = q at h1
  rcases le_or_gt q 0 with hq | hq
  · rw [Int.toNat_eq_zero.2 hq]; simpa using hc
  · rw [Int.toNat_of_nonneg hq.le]
    push_cast at h1
    have hd : (0 : ℤ) ≤ d := by positivity
    nlinarith [mul_nonneg hq.le hd]

theorem gapZ_nonneg_of_antitone {p : ℕ} {a : Fin p → ℕ} (ha : Antitone a) (i : Fin p) :
    0 ≤ WeightAlgebra.gapZ a i := by
  unfold WeightAlgebra.gapZ
  split_ifs with h
  · have : a ⟨i.1 + 1, h⟩ ≤ a i := ha (by simp [Fin.le_def])
    omega
  · positivity

theorem mul_ofGaps_le {p : ℕ} (T : ℕ) (g a : Fin p → ℕ)
    (h : ∀ i, (T : ℤ) * (g i : ℤ) ≤ WeightAlgebra.gapZ a i) (i : Fin p) : T * ofGaps g i ≤ a i := by
  have key : ∀ n : ℕ, ∀ i : Fin p, i.1 + n + 1 = p → T * ofGaps g i ≤ a i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hn : ¬ i.1 + 1 < p := by omega
      have h1 := h i
      rw [ofGaps_last g i hn]
      unfold WeightAlgebra.gapZ at h1
      rw [dite_eq_right hn] at h1
      exact_mod_cast h1
    | succ n ih =>
      intro i hi
      have hn : i.1 + 1 < p := by omega
      have h1 := h i
      have h2 := ih ⟨i.1 + 1, hn⟩ (by simp only; omega)
      rw [ofGaps_succ g i hn, Nat.mul_add]
      unfold WeightAlgebra.gapZ at h1
      rw [dite_eq_left hn] at h1
      have h3 : ((T * g i : ℕ) : ℤ) ≤ (a i : ℤ) - a ⟨i.1 + 1, hn⟩ := by push_cast; exact h1
      omega
  exact key (p - 1 - i.1) i (by have := i.2; omega)

theorem mul_lWt_aP_le (D : D7) {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) : T * (lWt D ka T nW hW).aP τ i ≤ ka.aP τ i := by
  refine mul_ofGaps_le T (lGapP D ka T nW τ) (ka.aP τ) (fun i => ?_) i
  have h0 := gapZ_nonneg_of_antitone (ka.aPlus_antitone τ) i
  unfold lGapP WeightAlgebra.Tp
  split_ifs with h
  · exact mul_toNat_fdiv_le _ _ _ _ h0 le_rfl
  · refine mul_toNat_fdiv_le _ _ _ _ h0 ?_
    unfold WeightAlgebra.gapZ
    rw [dite_eq_right h]
    have : (0 : ℤ) ≤ ((WeightFamilies.dimY D j : ℤ) + 2) * nW := by positivity
    have : (0 : ℤ) ≤ (D.R.r : ℤ) := by positivity
    linarith

theorem mul_lWt_aM_le (D : D7) {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).2) : T * (lWt D ka T nW hW).aM τ i ≤ ka.aM τ i := by
  refine mul_ofGaps_le T (lGapM D ka T τ) (ka.aM τ) (fun i => ?_) i
  have h0 := gapZ_nonneg_of_antitone (ka.aM_anti τ) i
  unfold lGapM WeightAlgebra.Tp
  split_ifs with h
  · exact mul_toNat_fdiv_le _ _ _ _ h0 le_rfl
  · refine mul_toNat_fdiv_le _ _ _ _ h0 ?_
    unfold WeightAlgebra.gapZ
    rw [dite_eq_right h]
    linarith

theorem mul_DF_lWt_le (D : D7) {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW) :
    T * WeightAlgebra.DF (lWt D ka T nW hW) ≤ WeightAlgebra.DF ka := by
  unfold WeightAlgebra.DF WeightAlgebra.degP
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Nat.mul_add, Finset.mul_sum, Finset.mul_sum]
  exact Nat.add_le_add (Finset.sum_le_sum fun i _ => mul_lWt_aP_le D ka T nW hW τ i)
    (Finset.sum_le_sum fun i _ => mul_lWt_aM_le D ka T nW hW τ i)

theorem mul_rows_lR_le_kaR : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ) (τ : D.what₂.Tau), (∀ i, Tp.TO * (lR Tp hK j).aP τ i ≤ (kaR Tp hK j).aP τ i) ∧ (∀ i, Tp.TO * (lR Tp hK j).aM τ i ≤ (kaR Tp hK j).aM τ i) ∧ Tp.TO * WeightAlgebra.DF (lR Tp hK j) ≤ WeightAlgebra.DF (kaR Tp hK j) := by
  intro D L Pm Tp hK j τ
  exact ⟨fun i => mul_lWt_aP_le D _ _ _ _ τ i, fun i => mul_lWt_aM_le D _ _ _ _ τ i,
    mul_DF_lWt_le D _ _ _ _⟩

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvExpLinearPartIntegralCharMemIntegralGerm
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.CharGerm

open MvPowerSeries GlobalTheory.RowLaw.GermRing GlobalTheory.FormalInv

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {Y : RawChart C d I κ} {V : VF C}

theorem const_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (F : MvPowerSeries σ C) : constantCoeff (subst a F) = constantCoeff F := by
  have hs := hasSubst_of_constantCoeff_zero ha
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [e, subst_add hs, map_add (f := _), constantCoeff_subst_zero ha (by simp), subst_C]
  simp

theorem coeff_single_subst_lg (hY : RLaw Y V) (F : MvPowerSeries κ C) (i : κ) :
    coeff (Finsupp.single i 1) (subst Y.lg F) = coeff (Finsupp.single i 1) F := by
  have hs := hasSubst_of_constantCoeff_zero (lg_const hY)
  have h := subst_sub_subst_mem_degGe (a := Y.lg) (b := (X : κ → MvPowerSeries κ C)) (k := 1) (m := 1)
    (fun s => mem_degGe_one.2 (lg_const hY s)) (fun s => mem_degGe_one.2 (constantCoeff_X s))
    (fun s => mem_degGe.2 fun μ hμ => by rw [map_sub, hY.lin s μ (by omega), sub_self])
    (f := F - MvPowerSeries.C (constantCoeff F)) (mem_degGe_one.2 (by simp))
  have h2 := mem_degGe.1 h (Finsupp.single i 1) (by simp)
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [map_sub, sub_eq_zero, congrFun subst_self] at h2
  conv_lhs => rw [e, subst_add hs, map_add (f := _), h2, subst_C]
  rw [← map_add (f := _)]
  exact congrArg _ e.symm

theorem subst_ex_eq_mvExp (hY : RLaw Y V) (χ : MvPowerSeries κ C) (h0 : constantCoeff χ = 1)
    (hχ : subst (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1)) χ =
      subst (gp C κ (0 : Fin 2)) χ * subst (gp C κ (1 : Fin 2)) χ) :
    subst Y.ex χ = mvExp (∑ i : κ, coeff (Finsupp.single i 1) χ • (X i : MvPowerSeries κ C)) := by
  haveI := hY.charZero
  have hex := hasSubst_of_constantCoeff_zero hY.exc
  have hlg := hasSubst_of_constantCoeff_zero (lg_const hY)
  have hlin : ∀ i, coeff (Finsupp.single i 1) χ = coeff (Finsupp.single i 1) (subst Y.ex χ) := by
    intro i
    rw [← coeff_single_subst_lg hY (subst Y.ex χ), subst_comp_subst_apply hex hlg]
    simp only [hY.exlg]
    exact congrArg _ (congrFun subst_self χ).symm
  simp only [hlin]
  refine GlobalTheory.AddChar.eq_mvExp_of_additive C κ _ (by rw [const_subst hY.exc, h0]) ?_
  have hg : ∀ (j : Fin 2) x, constantCoeff (gp C κ j x) = 0 := fun j x => constantCoeff_X _
  have hgs : ∀ j : Fin 2, HasSubst (gp C κ j) := fun j => hasSubst_of_constantCoeff_zero (hg j)
  let e : Fin 2 × κ → MvPowerSeries (Fin 2 × κ) C := fun p => subst (gp C κ p.1) (Y.ex p.2)
  have he0 : ∀ p, constantCoeff (e p) = 0 := fun p => constantCoeff_subst_zero (hg _) (hY.exc _)
  have hes := hasSubst_of_constantCoeff_zero he0
  have hadd : ∀ i, constantCoeff (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1) i) = 0 := fun i =>
    constantCoeff_subst_zero (log_add_const hY (hg 0) (hg 1)) (hY.exc i)
  have hA : HasSubst (fun i : κ => (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have k1 : ∀ (j : Fin 2) (F : MvPowerSeries κ C),
      subst e (subst (gp C κ j) F) = subst (fun x => subst (gp C κ j) (Y.ex x)) F := by
    intro j F
    rw [subst_comp_subst_apply (hgs j) hes]
    congr 1
    funext x
    rw [gp, subst_X hes]
  have h1 := congrArg (subst e) hχ
  rw [subst_mul hes, k1, k1, ← subst_comp_subst_apply hex (hgs 0), ← subst_comp_subst_apply hex (hgs 1),
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hadd) hes] at h1
  refine Eq.trans ?_ h1
  rw [subst_comp_subst_apply hex hA]
  congr 1
  funext i
  unfold addP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (log_add_const hY (hg 0) (hg 1))) hes]
  congr 1
  funext x
  rw [subst_add hes, k1, k1, lg_ex hY (hg 0), lg_ex hY (hg 1)]
  rfl

end GlobalTheory.RowLaw.CharGerm

namespace GlobalTheory.RowLaw


open MvPowerSeries GlobalTheory.RowLaw.GermRing GlobalTheory.RowLaw.CharGerm in
theorem upG_mvExp_char_mem_intGerm : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (χ : MvPowerSeries κ C), IntS V χ → MvPowerSeries.constantCoeff χ = 1 → MvPowerSeries.subst (addP X (gp C κ (0 : Fin 2)) (gp C κ 1)) χ = MvPowerSeries.subst (gp C κ (0 : Fin 2)) χ * MvPowerSeries.subst (gp C κ (1 : Fin 2)) χ → ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → upG g (mvExp (∑ x : I g, (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) χ * X.u g x i) • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t := by
  intro C _ V d _ I _ κ _ Y hY H χ hi h0 hχ g S t ht
  haveI := hY.charZero
  rw [intGerm_eq_expInt C V d I κ Y hY H S t ht]
  have hg : ∀ x, constantCoeff (gp C κ g x) = 0 := fun x => constantCoeff_X _
  refine ⟨subst (gp C κ g) χ, intS_subst hg (fun _ => intS_X _) hi, ?_⟩
  have hL : ∀ (g : Fin 2) (i : κ), constantCoeff (∑ c : I g, Y.u g c i •
      (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) = 0 := fun g i => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have hLs := hasSubst_of_constantCoeff_zero (hL g)
  have hes : HasSubst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => constantCoeff_subst_zero (hL _) (hY.exc _)
  have hU0 : ∀ x : I g, constantCoeff (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C) = 0 :=
    fun _ => constantCoeff_X _
  have hUs := hasSubst_of_constantCoeff_zero hU0
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hg) hes]
  have e : (fun s => subst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) (gp C κ g s)) = fun s =>
      subst (fun i : κ => ∑ c : I g, Y.u g c i • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C))
        (Y.ex s) := by
    funext s
    rw [gp, subst_X hes]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hY.exc) hLs, subst_ex_eq_mvExp hY χ h0 hχ,
    (GlobalTheory.mvExp_add_subst_linear C κ).2.2.1 _ _ _ (hL g) (by simp [map_sum])]
  unfold upG
  set_option synthInstance.maxHeartbeats 100000 in
    rw [(GlobalTheory.mvExp_add_subst_linear C (I g)).2.2.1 _ _ _ hU0 (by simp [map_sum])]
  congr 1
  rw [subst_sum_smul hLs, subst_sum_smul hUs]
  simp only [subst_X hLs, subst_X hUs, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

end GlobalTheory.RowLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesLthPowerOfPderivVanishModMaximal
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeriesFrobRoot

theorem eq_pow_of_pderiv {k σ : Type} [CommRing k] [IsDomain k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (b c : MvPowerSeries σ k) (hb : ∀ i, MvPowerSeries.pderiv (R := k) i b = 0)
    (hc : ∀ ν, MvPowerSeries.coeff ν c ^ p = MvPowerSeries.coeff (p • ν) b) : b = c ^ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← MvPowerSeries.map_frobenius_expand p hp]
  ext μ
  rw [MvPowerSeries.coeff_map]
  by_cases h : ∀ i, p ∣ μ i
  · obtain ⟨m, hm⟩ : ∃ m, p • m = μ := ⟨μ.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm, MvPowerSeries.coeff_expand_smul, frobenius_def, hc]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [MvPowerSeries.coeff_expand_of_not_dvd p hp _ hi, map_zero]
    have h0 : μ i ≠ 0 := fun h => hi (h ▸ dvd_zero p)
    have hle : Finsupp.single i 1 ≤ μ := by
      rw [Finsupp.single_le_iff]; omega
    have h1 := congrArg (MvPowerSeries.coeff (μ - Finsupp.single i 1)) (hb i)
    rw [MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle, map_zero] at h1
    refine (mul_eq_zero.1 h1).resolve_right fun h2 => hi ?_
    rw [← CharP.cast_eq_zero_iff k p]
    have h3 : μ i = ((μ - Finsupp.single i 1 : σ →₀ ℕ) i) + 1 := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    rw [h3]; push_cast; exact h2

variable {C : Type} [Field C] {V : VF C} {σ : Type}

open TeichPair

theorem exists_lift {f : MvPowerSeries σ C} (hf : IntS V f) :
    ∃ F : MvPowerSeries σ (intRing V), MvPowerSeries.map (intRing V).subtype F = f :=
  ⟨fun μ => ⟨MvPowerSeries.coeff μ f, hf μ⟩, by ext μ; rfl⟩

theorem mm_iff (F : MvPowerSeries σ (intRing V)) :
    (∀ μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.map (intRing V).subtype F))) ↔
      MvPowerSeries.map (Ideal.Quotient.mk (maxId V)) F = 0 := by
  rw [MvPowerSeries.ext_iff]
  refine forall_congr' fun μ => ?_
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem charP_res (V : VF C) : CharP (intRing V ⧸ maxId V) V.l := by
  refine (CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_
  rw [← map_natCast (Ideal.Quotient.mk (maxId V)), Ideal.Quotient.eq_zero_iff_mem]
  show 0 < V.v (((V.l : ℕ) : intRing V) : C)
  rw [show (((V.l : ℕ) : intRing V) : C) = (V.l : C) by simp, V.v_l]
  exact zero_lt_one

theorem pderiv_map' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ) (F : MvPowerSeries σ R) :
    MvPowerSeries.pderiv (R := S) i (MvPowerSeries.map φ F) = MvPowerSeries.map φ (MvPowerSeries.pderiv (R := R) i F) := by
  ext μ
  simp [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map]

theorem ge_of_pow {x : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (x ^ n)) : V.Ge 0 x := by
  unfold VF.Ge at h ⊢
  rw [V.v.map_pow] at h
  by_contra hx
  rw [not_le] at hx
  induction hv : V.v x using WithTop.recTopCoe with
  | top => rw [hv] at hx; exact not_top_lt hx
  | coe t =>
    rw [hv] at hx h
    rw [← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul] at h
    rw [WithTop.coe_lt_coe] at hx
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    nlinarith

theorem main : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) [Fintype σ], (∀ b : MvPowerSeries σ C, IntS V b → (∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i b))) → ∃ b' : MvPowerSeries σ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (b - b' ^ V.l))) ∧ (∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → (∀ μ, V.MM (MvPowerSeries.coeff μ (f ^ V.l - g ^ V.l))) → ∀ μ, V.MM (MvPowerSeries.coeff μ (f - g))) ∧ ∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → ∀ μ, V.MM (MvPowerSeries.coeff μ ((f + g) ^ V.l - f ^ V.l - g ^ V.l)) ∧ V.MM (MvPowerSeries.coeff μ ((f - g) ^ V.l - (f ^ V.l - g ^ V.l))) := by
  intro C _ _ V σ _
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  have := charP_res V
  have : CharP (MvPowerSeries σ (intRing V ⧸ maxId V)) V.l :=
    charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := σ)) V.l
  have : IsDomain (MvPowerSeries σ (intRing V ⧸ maxId V)) := NoZeroDivisors.to_isDomain _
  refine ⟨fun b hb hd => ?_, fun f g hf hg h => ?_, fun f g hf hg => ?_⟩
  · choose r hr using fun ν : σ →₀ ℕ =>
      IsAlgClosed.exists_pow_nat_eq (MvPowerSeries.coeff (V.l • ν) b) V.l_prime.pos
    have hri : ∀ ν, V.Ge 0 (r ν) := fun ν => ge_of_pow V.l_prime.ne_zero (by rw [hr]; exact hb _)
    obtain ⟨B, rfl⟩ := exists_lift hb
    let B' : MvPowerSeries σ (intRing V) := fun ν => ⟨r ν, hri ν⟩
    refine ⟨MvPowerSeries.map (intRing V).subtype B', hri, ?_⟩
    rw [← map_pow, ← map_sub, mm_iff, map_sub, map_pow, sub_eq_zero]
    refine eq_pow_of_pderiv V.l _ _ (fun i => ?_) fun ν => ?_
    · rw [pderiv_map', ← mm_iff, ← pderiv_map']
      exact hd i
    · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, ← map_pow]
      congr 1
      exact Subtype.ext (hr ν)
  · obtain ⟨F, rfl⟩ := exists_lift hf
    obtain ⟨G, rfl⟩ := exists_lift hg
    rw [← map_pow, ← map_pow, ← map_sub, mm_iff, map_sub, map_pow, map_pow, ← sub_pow_char] at h
    rw [← map_sub, mm_iff, map_sub]
    exact (pow_eq_zero_iff V.l_prime.ne_zero).1 h
  · obtain ⟨F, rfl⟩ := exists_lift hf
    obtain ⟨G, rfl⟩ := exists_lift hg
    rw [forall_and]
    constructor
    · rw [← map_add (f := _), ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]
      simp only [map_sub, map_pow, map_add (f := _), add_pow_char]
      ring
    · rw [← map_sub, ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]
      simp only [map_sub, map_pow, sub_pow_char]
      ring

end GlobalTheory.SeriesFrobRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem not_dvd_discr_host : ∀ (Rk : Ranks) (H : Formalism.BasicNotions.Host Rk) (p : ℕ), p.Prime → p ∉ H.small →
    p ≠ H.q → p ≠ H.d → ¬ (p : ℤ) ∣ NumberField.discr H.E := by
  intro Rk H p hp hs hq hd hdvd
  have hc : p ∣ H.QS * H.q * H.d := H.der.discr_primes.1 p hp hdvd
  rcases (hp.dvd_mul).1 hc with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · exact hs (Nat.mem_primeFactors.2 ⟨hp, h, H.QS_pos.ne'⟩)
    · exact hq ((Nat.prime_dvd_prime_iff_eq hp H.hyp.1).1 h)
  · exact hd ((Nat.prime_dvd_prime_iff_eq hp H.hyp.2.1).1 h)

end GlobalTheory.GoodDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabelBijectiveCardEqF
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem plOf_bijective_card (D : D7) :
    Function.Bijective (plOf D) ∧ Fintype.card D.what₂.Tau = D.R.f := by
  refine ⟨?_, D.what₂.card_Tau⟩
  have hb := D.R.toFrame.iota_bijective
  refine D.eTau.symm.bijective.comp (f := fun z : RPl D.R =>
    (if z.1 then ⟨D.R.tau2 z.2, rfl⟩ else ⟨D.R.tau1 z.2, rfl⟩ : D.R.Psi)) ⟨?_, ?_⟩
  · rintro ⟨a, s⟩ ⟨b, t⟩ h
    have h' := congrArg Subtype.val h
    cases a <;> cases b <;>
      simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, Bool.false_eq_true, if_true, if_false, Prod.mk.injEq] at h'
    · exact Prod.ext rfl (hb.1 h'.2)
    · exact absurd h'.1.1 (by decide)
    · exact absurd h'.1.1 (by decide)
    · exact Prod.ext rfl (hb.1 h'.2)
  · rintro ⟨⟨⟨a, b⟩, h⟩, hg⟩
    obtain ⟨t, rfl⟩ := hb.2 h
    have hb1 : b = 1 := hg
    subst hb1
    rcases Int.units_eq_one_or a with rfl | rfl
    · exact ⟨(false, t), rfl⟩
    · exact ⟨(true, t), rfl⟩

end GlobalTheory.RunDepth
end

