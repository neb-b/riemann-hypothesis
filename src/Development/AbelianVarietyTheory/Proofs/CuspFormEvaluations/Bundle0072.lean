module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InBasisIffPointValuesLinearIndependentSpan
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InContainMROfAnFacts
section
noncomputable section

namespace GlobalTheory.Shares.Contain

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem addL_zero (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  unfold addL wadd wsmul
  cases u
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i; simp
  · funext τ i; simp
  · simp

def secP (X : PJ D B P j) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (i : Fin (WeightFamilies.dimY D j + 1)) :
    MvPolynomial (Idx D j N) X.Forms :=
  ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))

section Weights

variable {X : PJ D B P j} {N : ℕ} {wL : WeightFamilies.Wt D j} {w : Fin N → B.Cusp j wL}

theorem ofWt_pow_mul (hs : ∀ i, OfWt X wL (secP X w i))
    (hm : ∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q))
    (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {p : MvPolynomial (Idx D j N) X.Forms}
    (hp : OfWt X (addL u wL n) p) : OfWt X (addL u wL (n + m)) (secP X w i ^ m * p) := by
  induction m with
  | zero => simpa using hp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ← add_assoc, ← wadd_addL]
    exact hm _ _ _ _ (hs i) ih

theorem ofWt_prod_mul (hs : ∀ i, OfWt X wL (secP X w i))
    (hm : ∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q))
    (α : Fin (WeightFamilies.dimY D j) → ℕ) (u : WeightFamilies.Wt D j) (n : ℕ) {p : MvPolynomial (Idx D j N) X.Forms}
    (hp : OfWt X (addL u wL n) p) (s : Finset (Fin (WeightFamilies.dimY D j))) :
    OfWt X (addL u wL (n + ∑ i ∈ s, α i)) ((∏ i ∈ s, secP X w i.succ ^ α i) * p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc, add_comm (α a), ← add_assoc]
    exact ofWt_pow_mul hs hm _ u _ _ ih

end Weights

theorem inContainMR_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (CR c : ℝ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T (WeightFamilies.MggK B CR T c j ka) xs → addL wF wL T = ka → WeightFamilies.dimY D j ≤ T → ∀ S : Scal B, Submodule.span B.KO ((X.Thc S.s0 (X.wF0 wL wF) : Submodule (𝓞 B.KO) _) : Set (B.Cusp j (X.wF0 wL wF))) = ⊤ → ∀ la, InBasis G la → InContainMR G la S CR T c := by
  intro D B P j X ka wL wF G R t T CR c δ xs hgen hA hka hDT S hTh la hB
  obtain ⟨hsec, hC, hCw, hmul, -, -, hsp, -⟩ := _root_.GlobalTheory.Shares.polyDictionary D B P j X R la G.N wL G.w t
  obtain ⟨hli, hdel⟩ := (_root_.GlobalTheory.Shares.inBasis_iff_vals D B P j X ka wL wF G R t T _ δ xs hgen hA hka la).1 hB
  have hs1 : ∀ i, toRp X la G.N (secP X G.w i) = sec X la G.w i := fun i => (hsec i).1
  have hs2 : ∀ i, R.toFn t (secP X G.w i) = R.s G.w t i := fun i => (hsec i).2.1
  have hs3 : ∀ i, OfWt X wL (secP X G.w i) := fun i => (hsec i).2.2
  have hspan : Submodule.span ℂ (Set.range (vals xs fun i => R.ev (X.inc wF (G.th' i)))) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hdel])
  have hcon := hA.contain G.del (fun i => R.ev (X.inc wF (G.th' i)))
    (fun i => Submodule.subset_span ⟨G.th' i, Set.mem_univ _, rfl⟩) hspan

  set Gen : Set (Rp X la G.N) := ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
          v = Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
       zAll G la S T) with hGen
  let Sp : Set (MvPolynomial (Idx D j G.N) X.Forms) := {p | OfWt X ka p ∧ toRp X la G.N p ∈ Gen}
  have hle : Submodule.span ℂ (Set.range (R.lead G.w t T (a0 D j T) fun i => R.ev (X.inc wF (G.th' i)))) ⊔
      R.deep G.w t (X.wF0 wL wF) (a0 D j T) ≤ Submodule.span ℂ (R.toFn t '' Sp) := by
    refine sup_le (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨⟨⟨al, hal⟩, i⟩, rfl⟩
      refine ⟨(∏ k, secP X G.w k.succ ^ al k) * (secP X G.w 0 ^ (T - ∑ k, al k) *
        MvPolynomial.C (X.inc wF (G.th' i))), ⟨?_, Or.inl ⟨al, i, hal, ?_⟩⟩, ?_⟩
      · have h0 : OfWt X (addL wF wL 0) (MvPolynomial.C (X.inc wF (G.th' i)) : MvPolynomial (Idx D j G.N) X.Forms) := by
          rw [addL_zero]; exact hCw _ _
        have h1 := ofWt_prod_mul hs3 hmul al wF _ (ofWt_pow_mul hs3 hmul 0 wF 0 (T - ∑ k, al k) h0) Finset.univ
        have he : 0 + (T - ∑ k, al k) + ∑ k, al k = T := by
          unfold a0 at hal; omega
        rwa [he, hka] at h1
      · simp only [map_mul, map_prod, map_pow, hs1, (hC _).1, Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow, mul_assoc]
      · simp only [map_mul, map_prod, map_pow, hs2, (hC _).2, Rdg.lead, Rdg.mon, mul_assoc]
    · rintro _ ⟨al, f, hal, hf, rfl⟩
      have hf' : f ∈ R.sp (X.wF0 wL wF)
          ((X.Thc S.s0 (X.wF0 wL wF) : Submodule (𝓞 B.KO) _) : Set (B.Cusp j (X.wF0 wL wF))) := by
        rw [← hsp, hTh]; exact hf
      clear hf
      unfold Rdg.sp at hf'
      induction hf' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨θ, hθ, rfl⟩ := hx
        refine Submodule.subset_span ⟨(∏ k, secP X G.w k.succ ^ al k) * MvPolynomial.C (X.inc _ θ),
          ⟨?_, Or.inr ⟨al, θ, hal, hθ, ?_⟩⟩, ?_⟩
        · have h0 : OfWt X (addL wF wL (WeightFamilies.dimY D j))
              (MvPolynomial.C (X.inc _ θ) : MvPolynomial (Idx D j G.N) X.Forms) := hCw _ θ
          have h1 := ofWt_prod_mul hs3 hmul al wF _ h0 Finset.univ
          have he : WeightFamilies.dimY D j + ∑ k, al k = T := by
            unfold a0 at hal; omega
          rwa [he, hka] at h1
        · simp only [map_mul, map_prod, map_pow, hs1, (hC _).1, Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow]
        · simp only [map_mul, map_prod, map_pow, hs2, (hC _).2, Rdg.mon]
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  have hmem : R.ev (X.inc ka F) ∈ Submodule.span ℂ (R.toFn t '' Sp) :=
    hle (hcon (Submodule.subset_span ⟨F, hF, rfl⟩))
  obtain ⟨n, a, g, hsum⟩ := Submodule.mem_span_set'.1 hmem
  choose p hp hpg using fun i => (g i).2
  have htr := (_root_.GlobalTheory.reading_transfer D B P j X R la G.N t hgen ka (Fin n) p (fun i => (hp i).1)).2.1
    (MvPolynomial.C (X.inc ka F)) (hCw _ _)
  rw [(hC _).1, (hC _).2] at htr
  have h2 : R.ev (X.inc ka F) ∈ Submodule.span ℂ (Set.range fun i => R.toFn t (p i)) := by
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hpg i⟩)
  refine Submodule.span_mono ?_ (htr.2 h2)
  rintro _ ⟨i, rfl⟩
  exact (hp i).2

end GlobalTheory.Shares.Contain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PhiFDEqZeroAtLastIndex
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem phiFD_eq_zero_at_last_index : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), j = D.R.m → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp), ∀ x ∈ ((T.U j σ).X k).dom, I2.phiFD ((T.U j σ).X k) (I2.th (E := D.host.E) q R0) x = 0 := by
  intro D T h j hj hjm DF q R0 hrun σ hσ k x hx
  have hu := h.unf j hj σ hσ
  have hq0 : (T.Q.Dw j).q = 0 := by
    rw [(h.pins.2.2.2 j hj).2.1, hjm]
    exact Nat.sub_self _
  have hp0 : ((T.U j σ).X k).p0 = 0 := ((hu.2.1 k).1).trans hq0
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hu k ⟨x, hx⟩
  have hint : ∀ u ∈ ((T.U j σ).X k).Λ, ∀ v ∈ ((T.U j σ).X k).Λ, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (((T.U j σ).X k).ξ0 * FD.herm ((T.U j σ).X k).Gm u v) = z := by
    intro u hu' v hv'
    have hEF := W.isom k ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)
    simp only [LinearEquiv.apply_symm_apply] at hEF
    refine ⟨-((W.F.Di (W.ik k)).EF ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)), ?_⟩
    rw [Int.cast_neg, hEF, neg_mul, map_neg, neg_neg]
  obtain ⟨A, -⟩ := _root_.GlobalTheory.TorusSign.exists_torusAt_w0_eq _ _ _ _ _ _ _ _ (T.U j σ) k ⟨x, hx⟩ W
  obtain ⟨τ0⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ ((T.U j σ).X k).Ψ := by
    by_cases h1 : τ0 ∈ ((T.U j σ).X k).Ψ
    · exact ⟨τ0, h1⟩
    · refine ⟨NumberField.ComplexEmbedding.conjugate τ0, ?_⟩
      rw [((T.U j σ).X k).cmType]
      simpa using h1
  have hpos := A.dim_pos ⟨τ, hτ⟩
  have hneg := A.dim_neg ⟨τ, hτ⟩
  have hsum := A.T.dim_conj τ
  have hr : A.T.r = D.R.r := by
    simp only at hpos hneg
    omega
  obtain ⟨P, hPq, hPR, -⟩ := hrun A.T hr ⟨τ, by simp only at hpos; omega⟩
  have hr0 : 0 < D.R.r := by
    have h2m := D.R.two_le_m
    show 0 < D.R.k + D.R.m - 1
    omega
  refine (GlobalTheory.T.la1sq_ge_two_f_div_rd_of_p0_eq_zero D.host.E D.R.r ((T.U j σ).X k) hr0 hp0 hint x hx).2 q R0
    ?_ ?_ ?_
  · have h16 := P.hrd
    linarith
  · have h1q := P.hq
    omega
  · have hb := P.C2
    rwa [hPq, hPR] at hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNeZeroAndLogBounded
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn.ScalSize

variable {D : D7} {j : ℕ}

theorem one_le_f (D : D7) : (1 : ℝ) ≤ D.R.f := by
  have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  exact_mod_cast this

theorem one_le_r (D : D7) : (1 : ℝ) ≤ D.R.r := by
  have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact_mod_cast this

theorem size_eq (w : WeightFamilies.Wt D j) :
    w.size = (WeightAlgebra.DF w : ℝ) + (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  push_cast
  ring

theorem size_ge (w : WeightFamilies.Wt D j) : (WeightAlgebra.DF w : ℝ) + (D.R.f : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 ≤ w.size := by
  rw [size_eq]
  have h1 : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h2 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

theorem n_le_size (w : WeightFamilies.Wt D j) : (w.n : ℝ) ≤ w.size := by
  have h := size_ge w
  have h1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le (one_le_f D) (one_le_r D)
  have h2 : (0 : ℝ) ≤ w.n := by positivity
  have h3 : (0 : ℝ) ≤ WeightAlgebra.DF w := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem size_comb (T : ℕ) (wL wF : WeightFamilies.Wt D j) :
    (wadd wF (wsmul T wL)).size + T = T * wL.size + wF.size := by
  unfold WeightFamilies.Wt.size
  simp only [wadd, wsmul]
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  ring

theorem log_zOwn_le (p : ℕ) (hp : 0 < p) (w : WeightFamilies.Wt D j) :
    Real.log (zOwnP D p w : ℝ) ≤ 2 * Real.log p * w.size := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h := size_ge w
  have h3 : (0 : ℝ) ≤ WeightAlgebra.DF w := by positivity
  unfold zOwnP
  push_cast
  rw [Real.log_pow]
  push_cast
  have : (WeightAlgebra.DF w : ℝ) + 2 * D.R.f * D.R.r * w.n ≤ 2 * w.size := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hl]

theorem lamStar_nonneg (w : WeightFamilies.Wt D j) : 0 ≤ lamStar D := by
  obtain ⟨-, -, h1, h2, -⟩ := GlobalTheory.RunIn.pPow_size D j w
  unfold lamStar
  linarith

noncomputable def comb (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) : 𝓞 B.KO :=
  (zOwnP D p G : 𝓞 B.KO) * sOf B hinj EX wL ^ T * sOf B hinj EX wF

theorem comb_eq (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (zOwnP D p G : 𝓞 B.KO) * nnW B hinj EX wL ^ T * nnW B hinj EX wF *
      (pPow D (T * c2 D wL + c2 D wF) (T * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
        (T * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) : 𝓞 B.KO) = comb B hinj EX p G wL wF T := by
  unfold comb sOf pPow
  push_cast
  ring

theorem comb_ne_zero (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) : comb B hinj EX p G wL wF T ≠ 0 := by
  unfold comb
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (_root_.GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D B hinj EX j wL).1)) (_root_.GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D B hinj EX j wF).1
  exact Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')

theorem log_comb_le (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (comb B hinj EX p G wL wF T : B.KO)‖ ≤
      2 * Real.log p * G.size + lamStar D * (T * wL.size + wF.size) := by
  obtain ⟨hL0, hL⟩ := _root_.GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D B hinj EX j wL
  obtain ⟨hF0, hF⟩ := _root_.GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D B hinj EX j wF
  have hL1 := (hL σ).2.2.2
  have hF1 := (hF σ).2.2.2
  have nz : ∀ x : 𝓞 B.KO, x ≠ 0 → ‖σ (x : B.KO)‖ ≠ 0 := fun x hx => by
    rw [norm_ne_zero_iff, map_ne_zero]
    exact_mod_cast hx
  have hz : (zOwnP D p G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')
  have e : ‖σ (comb B hinj EX p G wL wF T : B.KO)‖ =
      (zOwnP D p G : ℝ) * ‖σ (sOf B hinj EX wL : B.KO)‖ ^ T * ‖σ (sOf B hinj EX wF : B.KO)‖ := by
    unfold comb
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, norm_mul, norm_pow,
      Complex.norm_natCast]
  rw [e, Real.log_mul (mul_ne_zero hz (pow_ne_zero _ (nz _ hL0))) (nz _ hF0),
    Real.log_mul hz (pow_ne_zero _ (nz _ hL0)), Real.log_pow]
  have h1 := log_zOwn_le p hp G
  have hT : (0 : ℝ) ≤ T := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hL1 hT]

theorem log_comb_le' (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (wL wF : WeightFamilies.Wt D j) (hn : 1 ≤ wL.n) (T : ℕ) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (comb B hinj EX p (wadd wF (wsmul T wL)) wL wF T : B.KO)‖ ≤
      2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul T wL)).size := by
  have h := log_comb_le B hinj EX p hp (wadd wF (wsmul T wL)) wL wF T σ
  rw [← size_comb] at h
  have h1 := n_le_size (wadd wF (wsmul T wL))
  have h2 : T ≤ (wadd wF (wsmul T wL)).n := by
    simp only [wadd, wsmul]
    nlinarith
  have h3 : (T : ℝ) ≤ (wadd wF (wsmul T wL)).size := le_trans (by exact_mod_cast h2) h1
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hΛ := lamStar_nonneg wL
  have hs := (wadd wF (wsmul T wL)).one_le_size
  nlinarith [mul_le_mul_of_nonneg_left h3 hΛ, mul_nonneg hl (le_trans zero_le_one hs)]

theorem wt_eq {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} (hF : IsF' ka wL wF T nP) (hL : wL.n = nW)
    (hn : ka.n = nP + T * nW) : ka = wadd wF (wsmul T wL) := by
  obtain ⟨h1, h2, h3⟩ := hF
  obtain ⟨a, b, _, _, n, _⟩ := ka
  have e1 : a = (wadd wF (wsmul T wL)).aP := funext fun τ => funext fun i => by
    have := h2 τ i
    simp only [wadd, wsmul] at this ⊢
    zify
    linarith
  have e2 : b = (wadd wF (wsmul T wL)).aM := funext fun τ => funext fun i => by
    have := h3 τ i
    simp only [wadd, wsmul] at this ⊢
    zify
    linarith
  have e3 : n = (wadd wF (wsmul T wL)).n := by
    simp only [wadd, wsmul] at hn ⊢
    rw [h1, hL, hn]
  subst e1 e2 e3
  rfl

end GlobalTheory.RunIn.ScalSize


open GlobalTheory.RunIn.ScalSize in
theorem GlobalTheory.RunIn.scalOfP_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ), 0 < p → 1 ≤ nW → wL.n = nW → IsF' ka wL wF Tn nP → ka.n = nP + Tn * nW → (scalOfP B hinj EX p ka wL wF Tn).sF ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).s0 ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).sK ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, (Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sW : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wL.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sF : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).s0 : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul (WeightFamilies.dimY D j) wL)).size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sK : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * ka.size) := by
  intro D B hinj EX j p ka wL wF Tn nP nW hp hW hL hF hn
  have eF : (scalOfP B hinj EX p ka wL wF Tn).sF = comb B hinj EX p wF wL wF 0 := by
    unfold comb sOf
    simp only [scalOfP, pow_zero, mul_one, mul_assoc]
  have e0 : (scalOfP B hinj EX p ka wL wF Tn).s0 =
      comb B hinj EX p (wadd wF (wsmul (WeightFamilies.dimY D j) wL)) wL wF (WeightFamilies.dimY D j) := comb_eq ..
  have eK : (scalOfP B hinj EX p ka wL wF Tn).sK = comb B hinj EX p ka wL wF Tn := comb_eq ..
  have hn1 : 1 ≤ wL.n := hL ▸ hW
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [eF, e0, eK, sW_eq_sOf]
  refine ⟨comb_ne_zero B hinj EX p hp _ _ _ _, comb_ne_zero B hinj EX p hp _ _ _ _,
    comb_ne_zero B hinj EX p hp _ _ _ _, fun σ => ⟨?_, ?_, log_comb_le' B hinj EX p hp wL wF hn1 _ σ, ?_⟩⟩
  · have h := ((_root_.GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D B hinj EX j wL).2 σ).2.2.2
    nlinarith [mul_nonneg hl (le_trans zero_le_one wL.one_le_size)]
  · have h := log_comb_le B hinj EX p hp wF wL wF 0 σ
    push_cast at h
    linarith
  · rw [wt_eq hF hL hn]
    exact log_comb_le' B hinj EX p hp wL wF hn1 _ σ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRdOfInBasis
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem addL_zero_wt (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  cases u
  simp [addL, wadd, wsmul]

theorem rk_Mlat_eq_finrank (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (h : LatAt B j ka) :
    X.rk ka (B.Mlat j ka) = Module.finrank B.KO (⊤ : Submodule B.KO (B.Cusp j ka)) := by
  letI : Submodule.IsFullLattice B.KO (B.Mlat j ka) := h
  unfold PJ.rk
  rw [Submodule.IsFullLattice.span_eq_top]

private lemma s_mem_sp_univ (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) : R.s w t i ∈ R.sp wL Set.univ := by
  unfold Rdg.s Rdg.sp
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨w k, Set.mem_univ _, rfl⟩

theorem Rdg.s_pow_mul_mem (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)
    (hmul : ∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ)
    (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {v : R.Y → ℂ}
    (hv : v ∈ R.sp (addL u wL n) Set.univ) : R.s w t i ^ m * v ∈ R.sp (addL u wL (n + m)) Set.univ := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>

    rw [pow_succ', mul_assoc, ← Nat.add_assoc, ← wadd_addL]
    exact hmul _ _ _ (s_mem_sp_univ R w t i) _ ih

theorem Rdg.prod_pow_mul_mem (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)
    (hmul : ∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ)
    (α : Fin (WeightFamilies.dimY D j) → ℕ) (s : Finset (Fin (WeightFamilies.dimY D j))) (u : WeightFamilies.Wt D j) (n : ℕ) {v : R.Y → ℂ}
    (hv : v ∈ R.sp (addL u wL n) Set.univ) :
    (∏ i ∈ s, R.s w t i.succ ^ α i) * v ∈ R.sp (addL u wL (n + ∑ i ∈ s, α i)) Set.univ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    have h := R.s_pow_mul_mem w t hmul a.succ u (n + ∑ i ∈ s, α i) (α a) ih
    have e : n + (α a + ∑ i ∈ s, α i) = n + ∑ i ∈ s, α i + α a := by ring
    rw [e]
    exact h

theorem shareRd_of_inBasis : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T Mg xs → addL wF wL T = ka → WeightFamilies.dimY D j < T → 0 < WeightFamilies.dimY D j → LatAt B j ka → (∃ la, InBasis G la) → ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka hDT _ hlat hex
  obtain ⟨la, hla⟩ := hex

  have hI := (_root_.GlobalTheory.Shares.inBasis_iff_vals D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka la).1 hla
  obtain ⟨-, -, -, -, -, hmul, -, hfin⟩ := _root_.GlobalTheory.Shares.polyDictionary D B P j X R la G.N wL G.w t
  have hθ : ∀ i, R.ev (X.inc wF (G.th' i)) ∈ R.sp wF Set.univ := fun i =>
    Submodule.subset_span ⟨G.th' i, Set.mem_univ _, rfl⟩

  have hLI := (hfac.indep G.del (fun i => R.ev (X.inc wF (G.th' i))) hθ hI.1).1

  have hmem : ∀ p, R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p ∈
      R.sp ka Set.univ := by
    rintro ⟨⟨α, hα⟩, i⟩
    have h0 : R.ev (X.inc wF (G.th' i)) ∈ R.sp (addL wF wL 0) Set.univ := by
      rw [addL_zero_wt]
      exact hθ i
    have h1 := R.s_pow_mul_mem G.w t hmul 0 wF 0 (T - ∑ k, α k) h0
    have h2 := R.prod_pow_mul_mem G.w t hmul α Finset.univ wF (0 + (T - ∑ k, α k)) h1
    have hle : ∑ k, α k ≤ T := by
      unfold a0 at hα
      omega
    have e : 0 + (T - ∑ k, α k) + ∑ k ∈ Finset.univ, α k = T := by omega
    rw [e, hka] at h2
    show R.mon G.w t α * R.s G.w t 0 ^ (T - ∑ k, α k) * R.ev (X.inc wF (G.th' i)) ∈ R.sp ka Set.univ
    rw [mul_assoc]
    exact h2

  obtain ⟨hfd, hfr⟩ := hfin ka ⊤
  rw [Submodule.top_coe] at hfd hfr
  have hcard : Nat.card ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del) ≤
      Module.finrank B.KO (⊤ : Submodule B.KO (B.Cusp j ka)) := by
    rw [← hfr]
    haveI : FiniteDimensional ℂ (R.sp ka Set.univ) := hfd
    have hLI' : LinearIndependent ℂ (fun p =>
        (⟨R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p, hmem p⟩ :
          R.sp ka Set.univ)) :=
      LinearIndependent.of_comp (R.sp ka Set.univ).subtype hLI
    haveI := hLI'.finite
    haveI := Fintype.ofFinite ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del)
    rw [Nat.card_eq_fintype_card]
    exact hLI'.fintype_card_le_finrank
  have hcnt : Nat.card {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} =
      (T - 1).choose (WeightFamilies.dimY D j) :=
    GlobalTheory.card_exponents_sum_lt_sub _ _ hDT
  rw [Nat.card_prod, Nat.card_fin, hcnt] at hcard
  unfold ShareRd
  rw [rk_Mlat_eq_finrank X ka hlat]
  exact_mod_cast hcard

end GlobalTheory.Shares
end

