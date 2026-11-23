module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortFiniteGeneratorsThetaLattice
section
noncomputable section

namespace GlobalTheory.ThetaFamily

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem span_eq_spanIn {D : D7} {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)]
    [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]
    (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j)) (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) {ι : Type}
    (g : ι → cutR C j w) (hg : ∀ i, (g i : R j) ∈ s)
    (hs : ∀ f ∈ s, f ∈ AddSubgroup.closure (Set.range fun i => (g i : R j))) :
    Submodule.span (𝓞 K) (Set.range g) = spanIn C j w s := by
  unfold spanIn
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hg i)
  · intro x hx
    have hx' : (x : R j) ∈ Submodule.span (𝓞 K) s := hx
    let F : cutR C j w →ₗ[𝓞 K] R j := (cutR C j w).subtype.restrictScalars (𝓞 K)
    have hsub : Submodule.span (𝓞 K) s ≤ (Submodule.span (𝓞 K) (Set.range g)).map F := by
      rw [Submodule.span_le]
      intro f hf
      have hcl : AddSubgroup.closure (Set.range fun i => (g i : R j)) ≤
          ((Submodule.span (𝓞 K) (Set.range g)).map F).toAddSubgroup := by
        rw [AddSubgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        exact ⟨g i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
      exact hcl (hs f hf)
    obtain ⟨y, hy, hyx⟩ := hsub hx'
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']

theorem exists_family (hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab : NabV Xo c) (hn : IsNab Xo c nab) (ht : ThValTot Xo c nab) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {R : ℕ}
    (b : Fin R → MvPolynomial (LtN Dw n) c.F) (hb : ∀ i, b i ∈ harmA (Dw := Dw) c a n)
    (hgen : ∀ P ∈ harmA (Dw := Dw) c a n, ∃ z : Fin R → ℤ, P = ∑ i, (z i : c.F) • b i) :
    ∃ g : (Fin n → LevQ Dw l) × Fin R → Rul Xo c,
      (∀ p, IsThRule Xo c nab (fun k => levRep (p.1 k)) (b p.2) (g p)) ∧
      ∀ f ∈ thGen Xo c nab a n, f ∈ AddSubgroup.closure (Set.range g) := by
  have hex : ∀ p : (Fin n → LevQ Dw l) × Fin R,
      ∃ f : Rul Xo c, IsThRule Xo c nab (fun k => levRep (p.1 k)) (b p.2) f := fun p =>
    (existsUnique_thRule Xo c nab ht (fun k => levRep (p.1 k)) (hb p.2)).exists
  choose g hg using hex
  refine ⟨g, hg, ?_⟩
  rintro f ⟨x, P, hP, hf⟩
  obtain ⟨hlin, hmod⟩ := _root_.GlobalTheory.ThetaRule.isThRule_linear_and_congr hci E H Dw l Xo c nab hn a n
  set q : Fin n → LevQ Dw l := fun k => Submodule.Quotient.mk (x k) with hq
  have hrep : ∀ k, x k - levRep (q k) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro k
    have h1 : Submodule.Quotient.mk (levRep (q k)) = q k := by
      unfold levRep
      exact Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q k))
    rw [← Submodule.Quotient.eq, h1]
  have hf' : IsThRule Xo c nab (fun k => levRep (q k)) P f := hmod x _ P f hrep hf
  obtain ⟨z, hz⟩ := hgen P hP
  have hsum : f = ∑ i, ((z i : ℤ) : c.F) • g (q, i) := by
    refine hlin (fun k => levRep (q k)) R (fun i => ((z i : ℤ) : c.F)) b f (fun i => g (q, i)) hb ?_ ?_ ?_
    · rw [← hz]; exact hP
    · rw [← hz]; exact hf'
    · intro i; exact hg (q, i)
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (q, i))) _

theorem log_rdE (D : D7) : Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) = lrd D := by
  have hf : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by
    first
    | exact_mod_cast Formalism.MainNotions.Gaps.LevGap.finrank_hostE_eq D.host
    | exact_mod_cast Formalism.MainNotions.StandardLattice.finrank_host D
  have hd : (NumberField.discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  unfold lrd ReciprocityTheory.ChartRestriction.G.FD.rdE ReciprocityTheory.ChartRestriction.G.FD.dE
  rw [Real.log_rpow (abs_pos.mpr hd), hf]
  ring

theorem absA_eq {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : absA w = (WeightAlgebra.DF w : ℝ) := by
  unfold absA WeightAlgebra.DF WeightAlgebra.degP
  push_cast
  rfl

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem theta_family : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → (fun (B : WeightFamilies.Prov D) (X : PJ D B T.G.P j) => ∃ (N : ℕ) (w0 : Fin N → B.Cusp j w), Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll w ∧ N ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n)) ∧ ∀ k σ, Real.log (B.supN j w σ (w0 k)) ≤ 400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) (recB h.toLawsCore) (recPJ h j hj) := by
  intro hci D T h hG large₂ j hj w hpg hL hr hlast
  beta_reduce

  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    first
    | exact Formalism.MainNotions.Gaps.LevGap.finrank_hostE_eq D.host
    | exact Formalism.MainNotions.StandardLattice.finrank_host D
  have hfd : ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.fdeg
    omega
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.toLawsCore.toLawsM.pins.2.1.1
  have hk := D.R.m_add_three_le_k
  obtain ⟨hj1, hj2⟩ := id hj
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    have h4 := h.toLawsCore.toLawsM.pins.2.2.2 j hj
    unfold IsDatW at h4
    rw [h4.1, h4.2.1]
    simp only [Formalism.BasicNotions.Ranks.sigW, Formalism.BasicNotions.Ranks.r]
    omega
  have hr1 : 1 ≤ D.R.r := by
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  have hnpos : 0 < w.n := by omega
  have hDF : Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ WeightAlgebra.DF w := ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
  have hLP : Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlast
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hnabex, -, htot, hcusp, -, -⟩ := id h
  obtain ⟨inst, hn⟩ := hnabex j hj
  obtain ⟨-, hlrd, -, -, hlf, -, -, hlDF, hln⟩ := id hpg

  have hrd : Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) ≤ 2 * large₂.sc.L := by
    rw [log_rdE]; exact hlrd
  have hfd' : Real.log (ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E) ≤ 2 * large₂.sc.L := by
    rw [hfd]; exact hlf
  have hDFr : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ WeightAlgebra.DF w := by exact_mod_cast hDF
  have hDF' : Real.log (1 + Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w)) ≤ 2 * large₂.sc.L := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hlDF
    linarith
  obtain ⟨R, b, hb, hgen, hR, hl1⟩ := GlobalTheory.T.exists_reduced_integral_basis_harmonicPolynomials D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n
    (by rw [hpq]; exact hr) (wtA w) large₂.sc.L hL hrd hfd' hDF' hln

  obtain ⟨g, hgr, hgcl⟩ := exists_family hci (T.Q.Xo j) T.Q.c (T.nab j) hn (htot j hj) (wtA w) w.n b hb hgen
  have hmem : ∀ f, f ∈ T.th j w ↔ ∃ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
      P ∈ harmA T.Q.c (wtA w) w.n ∧ IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f := fun f => Iff.rfl
  have hth : ∀ p, g p ∈ T.th j w := fun p => (hmem _).2 ⟨fun k => levRep (p.1 k), b p.2, hb p.2, hgr p⟩
  have hcut : ∀ p, g p ∈ cutR T.C j w := by
    intro p
    unfold cutR
    rw [Submodule.mem_inf, Submodule.mem_iInf]
    exact ⟨hcusp j hj (wtA w) w.n (dom_wtA w) hLP (g p) (hth p), fun hn' => absurd hj hn'⟩
  have : Finite (LevQ (T.Q.Dw j) T.Q.l) := (_root_.GlobalTheory.card_levQ D.host.E T.Q.H (T.Q.Dw j) T.Q.l).1
  let e := Finite.equivFin ((Fin w.n → LevQ (T.Q.Dw j) T.Q.l) × Fin R)
  let w0 : Fin (Nat.card ((Fin w.n → LevQ (T.Q.Dw j) T.Q.l) × Fin R)) → ↥(cutR T.C j w) :=
    fun k => ⟨g (e.symm k), hcut (e.symm k)⟩
  refine ⟨_, (w0 : Fin _ → (recB h.toLawsCore).Cusp j w), ?_, ?_, ?_⟩
  ·
    have h2 : Set.range (fun k => ((w0 k : cutR T.C j w) : T.R j)) = Set.range g :=
      e.symm.surjective.range_comp g
    have hsp := span_eq_spanIn T.C j w (T.th j w) w0 (fun k => hth (e.symm k))
      (fun f hf => by rw [h2]; exact hgcl f ((hmem f).1 hf))
    exact hsp
  ·
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_fin,
      (_root_.GlobalTheory.card_levQ D.host.E T.Q.H (T.Q.Dw j) T.Q.l).2, hM, hfd, hpq, ← pow_mul]
    rw [hfd, hpq] at hR
    refine Nat.mul_le_mul le_rfl (le_trans hR (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (by omega) _)))
  ·
    intro k σ
    have hs : (recB h.toLawsCore).supN j w σ (w0 k) = T.Ns j w σ (g (e.symm k)) := by
      dsimp only [recB, mkB]
      unfold cutN
      rw [if_pos hj]
    rw [hs]
    have hexp := hl1 (e.symm k).2 σ
    simp only [hfd, hpq] at hexp
    have hlg : 0 ≤ Real.log (Module.finrank ℚ T.Q.c.F) := Real.log_natCast_nonneg _
    have hld : 0 ≤ Real.log |((NumberField.discr T.Q.c.F : ℤ) : ℝ)| / Module.finrank ℚ T.Q.c.F := by
      apply div_nonneg _ (Nat.cast_nonneg _)
      apply Real.log_nonneg
      have : (1 : ℤ) ≤ |NumberField.discr T.Q.c.F| := Int.one_le_abs (NumberField.discr_ne_zero _)
      exact_mod_cast this
    have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
    have hA : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ absA w := by rw [absA_eq]; exact hDFr
    have hrL : (0 : ℝ) ≤ 140 * (D.R.r : ℝ) * large₂.sc.L := by positivity
    have hAm := mul_le_mul_of_nonneg_left hA hrL
    have hfrnL : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n * large₂.sc.L := by positivity
    have hDF0 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) := Nat.cast_nonneg _
    have hℓ : (0 : ℝ) ≤ 140 * ((D.R.r : ℕ) : ℝ) * large₂.sc.L * (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) +
        2 * (D.R.f : ℝ) * ((D.R.r : ℕ) : ℝ) * (w.n : ℝ) * large₂.sc.L + 4 * Real.log (Module.finrank ℚ T.Q.c.F) +
        Real.log |((NumberField.discr T.Q.c.F : ℤ) : ℝ)| / Module.finrank ℚ T.Q.c.F := by
      have : (0 : ℝ) ≤ 140 * ((D.R.r : ℕ) : ℝ) * large₂.sc.L * (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) := by positivity
      linarith
    have key := _root_.GlobalTheory.RunIn.log_sup_theta_generator_le hci D T h hG large₂ j hj w hpg hL hr hLP (fun i => levRep ((e.symm k).1 i)) (b (e.symm k).2)
      (hb _) (g (e.symm k)) (hgr _) σ _ hℓ hexp
    have h30 := (_root_.GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j w 0 hL hnpos).1
    show Real.log (T.Ns j w σ (g (e.symm k))) ≤ 400 * Zb D large₂ * w.size + 3 * (D.R.f : ℝ) * D.R.r * w.n * large₂.sc.L +
      5 * Real.log (Module.finrank ℚ T.Q.c.F) + Real.log |((NumberField.discr T.Q.c.F : ℤ) : ℝ)| / Module.finrank ℚ T.Q.c.F + 2
    nlinarith [key, h30, hAm, hfrnL, hlg, hld]

end GlobalTheory.ThetaFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn


set_option maxHeartbeats 800000 in
theorem log_sup_short_generator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ g) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  intro hCh D T hT hG large₂ j hj w hRows hL hr hLast hSh hA Λ N x0 P g hU hTb hTM hLev hX hP hS hg σ ℓ hℓ hl1
  obtain ⟨hfd, hrd, hrd1, hf1, hr1, hxi, hDF, habs, hc, hlie, hlA, hpde, hpde', hl1g⟩ := _root_.GlobalTheory.SupDict.record_dictionary D T hT j hj w
  have hRw := hRows
  obtain ⟨-, hlrd, -, -, hlf, hlp, hlp', hlDF, hln⟩ := hRows
  set σ' := goodOf T.Q.c σ with hσ'
  have hgood : GoodEmb T.Q.c σ' := goodEmb_goodOf _ σ
  have hgC : g ∈ T.C j w :=
    hSh.8 j hj (wtA w) w.n (dom_wtA w) hLast (dom_wtA w) hLast ⟨hg, Λ, N, x0, P, hU, hTb, hTM, hLev, hX, hP, hS⟩
  obtain ⟨Cls, _, _, δ, gdet, hcmp⟩ := hSh.6 j hj w.n
  have hUC : GlobalTheory.Dict.UnitC (T.dδ j w.n) := FiniteOrderRule.unitC_of_cmp _ _ _ _ _ _ _ _ Cls δ gdet hcmp
  obtain ⟨p, hp, hpd⟩ := hSh.4
  have hpdw : (T.dδ j w.n).pd = p := hpd j hj w.n
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> assumption
  have hlogp : Real.log p ≤ large₂.sc.L := by rcases hp with rfl | rfl <;> assumption
  obtain ⟨ph, ψ, xψ, -, hpin, -⟩ := hSh.5 j hj w.n hr
  have hunf : IsUnf (T.U j σ') := hT.unf j hj σ' hgood
  have hNs : T.Ns j w σ g = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) := rfl
  rw [hNs, hlie]
  set S := supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; unfold supN; exact ENNReal.toReal_nonneg
  have hL0 : (0:ℝ) ≤ large₂.sc.L := by linarith
  have ha0 : (0:ℝ) ≤ absA w := by rw [habs]; positivity
  rcases hS0.eq_or_lt with hS00 | hSpos
  · rw [← hS00, mul_zero, Real.log_zero]
    positivity
  obtain ⟨k, xf, -, hortho, hSle, hla, hlog⟩ :=
    _root_.GlobalTheory.RunIn.half_sup_at_ortho_frame D T hT hG large₂ j hj w hRw hL hr hLast σ' hgood g hgC hSpos
  set lam := Real.sqrt (((T.U j σ').X k).firstMinimumSq xf.1) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hla
  have hlam2 : lam ^ 2 = ((T.U j σ').X k).firstMinimumSq xf.1 := Real.sq_sqrt hla.le
  have hv := GlobalTheory.T.norm_short_generator_eval_le_orthonormal_frame hCh D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ' D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ')) ((Formalism.L2.PjFree.goodEmb_iff σ').mpr hgood)
    ((Formalism.L2.PjFree.isUnf_ofPj _).mpr hunf) hr1 (2 * xiR D) (by linarith) (hc σ' hgood) (wtA w) w.n
    (dom_wtA w) hr (T.dδ j w.n) (hSh.2 j hj w.n) (by rw [hpdw]; exact hp0) hlA hA (hSh.3 j hj w.n)
    ⟨ph, ψ, xψ, hpin⟩ hUC Λ N x0 P g hU hTM hLev (hSh.1 j hj w.n (hT.kPsi j hj) Λ hU hTb) hP hS
    k xf hortho lam hlam0 hlam2.le
  have hp1eq : (∑ m ∈ P.support, ‖σ' (P.coeff m)‖) = l1At σ P := hl1g _ σ P
  rw [hfd, hp1eq] at hv
  have hcle : ((T.dδ j w.n).pd : ℝ) ^ (D.R.f * D.R.r * w.n) ≤
      Real.exp (D.R.f * D.R.r * w.n * large₂.sc.L) := by
    rw [hpdw]
    have hp' : (0:ℝ) < p := by exact_mod_cast hp0
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hp']
    apply Real.exp_le_exp.mpr
    push_cast
    have hfrn : (0:ℝ) ≤ D.R.f * D.R.r * w.n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogp hfrn]
  have hp1 : 0 ≤ l1At σ P := by unfold l1At; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact GlobalTheory.log_exp_mul_le_of_generator_sup_bound D.R.f D.R.r w.n (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))
    large₂.sc.L ℓ (absA w) (rdE D.host.E) lam (2 * xiR D) _ S _ (l1At σ P) hL hf1 hr1 hr
    (by rw [habs]; exact_mod_cast hDF) (by rw [habs]; exact hlDF) hln hlf hrd1 (by rw [hrd]; exact hlrd)
    hlam0 (by rw [hlam2]; exact hlog) (by linarith) hℓ hp1 hl1 (by positivity) hcle hS0 hSle hv

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoBaseComponentShortPolynomialGenerator
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NoBase

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem rank_of_pins {D : D7} {Q : Par D} (h : Q.Pins) {j : ℕ} (hj : InR D j) :
    (Q.Dw j).p + (Q.Dw j).q = D.R.r := by
  obtain ⟨hp, hq, -⟩ := h.2.2.2 j hj
  obtain ⟨h1, h2⟩ := hj
  rw [hp, hq]
  have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos
  simp only [Ranks.sigW, Ranks.r, Ranks.k]
  omega

theorem log_rdE (D : D7) : Real.log (FD.rdE D.host.E) = lrd D := by
  have hpos : 0 < dE D.host.E := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  unfold FD.rdE lrd
  rw [Real.log_rpow hpos, hostSize_finrank D]
  unfold dE
  push_cast
  ring

theorem mem_span_short (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j)
    (w : WeightFamilies.Wt D j) (hrows : PullbackSections.SupBoundPageRows D large₂ w) (hL : 2 ≤ large₂.sc.L) (hr : D.R.r ≤ w.n)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (hP : P ∈ harmA T.Q.c (wtA w) w.n) :
    P ∈ Submodule.span T.Q.c.F {Q | Q ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n ∧
      ∀ σ' : T.Q.c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * D.R.r * large₂.sc.L * absA w} := by
  have hrk := rank_of_pins h.pins hj
  have h2 := PfTies1.DF_wtA_le (T.Q.Dw j) w
  have h3 : (((∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) : ℕ)) : ℝ) = absA w := by simp [absA]
  have hDF : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ absA w := by rw [← h3]; exact_mod_cast h2
  have hDF' : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := by exact_mod_cast h2
  have hfd : FD.fdeg D.host.E = D.R.f := by unfold FD.fdeg; rw [hostSize_finrank D]; omega
  obtain ⟨-, r1, -, -, r4, -, -, r7, r8⟩ := hrows
  have key := (GlobalTheory.StdHarm.harmA_mem_span_short D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n).2
    (hrk ▸ hr) (wtA w) large₂.sc.L hL (by rw [log_rdE]; exact r1) (by rw [hfd]; exact r4)
    (le_trans (Real.log_le_log (by positivity) (by linarith)) r7) r8 P hP
  refine Submodule.span_mono ?_ key
  intro Q hQ
  refine ⟨hQ.1, fun σ' => (hQ.2 σ').trans ?_⟩
  rw [hrk]
  have : (0 : ℝ) ≤ large₂.sc.L := by linarith
  gcongr

theorem noBase : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ReciprocityTheory.ChartRestriction.G.PullbackSections.NoBaseSt := by
  intro hC D T h large₂ j hj w hrows hL hr hlast hDF hα σ hσ k
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  letI := inst
  have hT := h.thTot j hj
  obtain ⟨x0, hx0⟩ := dom_nonempty ((T.U j σ).X k)
  have hM : 4 * WeightAlgebra.DF w + 4 ≤ T.Q.l.M := by
    rw [h.pins.2.1.1]
    have e0 : WeightAlgebra.DF w + 2 ≤ D.host.g 0 := le_trans hDF (min_le_left _ _)
    have e1 : WeightAlgebra.DF w + 2 ≤ D.host.g 1 := le_trans hDF (min_le_right _ _)
    nlinarith [Nat.mul_le_mul e0 e1]
  obtain ⟨f, ⟨x, P, hP, hfP⟩, hf0⟩ := _root_.GlobalTheory.noCommonZero_of_chartIndep hC D T h j hj w hr hlast hM hα σ hσ k x0 hx0
  by_contra hno
  push_neg at hno
  obtain ⟨N, cf, g, hsum⟩ := Submodule.mem_span_set'.1 (mem_span_short D T h large₂ j hj w hrows hL hr P hP)
  choose gi hgi using fun i => (existsUnique_thRule _ _ _ hT x (g i).2.1).exists
  have hlin := (_root_.GlobalTheory.ThetaRule.isThRule_linear_and_congr hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (wtA w) w.n).1
    x N cf (fun i => (g i : _)) f gi (fun i => (g i).2.1) (by rw [hsum]; exact hP) (by rw [hsum]; exact hfP) hgi
  apply hf0
  have hz : ∀ i, rdU (T.U j σ) (gi i) k x0 = 0 := fun i =>
    hno x (g i) (gi i) (g i).2.1 (g i).2.2 (hgi i) x0 hx0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hlin, map_sum]
  simp only [LinearMap.map_smulₛₗ, Finset.sum_apply, Pi.smul_apply, hz, smul_zero, Finset.sum_const_zero]

end GlobalTheory.NoBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledThetaLatticeGeneratorsNoCommonZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem semilinear_eq_zero_of_span_smul {O K L M ι : Type} [CommRing O] [Field K] [Field L] [Algebra O K]
    [AddCommGroup M] [Module K M] [Module O M] [IsScalarTower O K M] (σ : K →+* L) (φ : M →ₛₗ[σ] L)
    (w : ι → M) (hw : ∀ i, φ (w i) = 0) (s : O) (hs : algebraMap O K s ≠ 0) (f : M)
    (hf : s • f ∈ Submodule.span O (Set.range w)) : φ f = 0 := by
  have h1 : ∀ g ∈ Submodule.span O (Set.range w), φ g = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hw i
    | zero => exact map_zero φ
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul a x _ hx => rw [← algebraMap_smul K a x, map_smulₛₗ, hx, smul_zero]
  have h2 := h1 _ hf
  rw [← algebraMap_smul K s f, map_smulₛₗ, smul_eq_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left ((map_ne_zero σ).2 hs)

theorem eq_zero_of_span_eq_WWc {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (w : WeightFamilies.Wt D j)
    {ι : Type} (g : ι → B.Cusp j w) (s : 𝓞 B.KO) (hs : s ≠ 0)
    (hg : Submodule.span (𝓞 B.KO) (Set.range g) = X.WWc s w) (σ : B.KO →+* ℂ) (φ : B.Cusp j w → ℂ)
    (hadd : ∀ F F', φ (F + F') = φ F + φ F') (hsmul : ∀ (a : B.KO) F, φ (a • F) = σ a * φ F)
    (h0 : ∀ i, φ (g i) = 0) (F : B.Cusp j w) (hF : F ∈ X.thAll w) : φ F = 0 := by
  have hW : s • F ∈ X.WWc s w := ⟨F, hF, rfl⟩
  rw [← hg] at hW
  exact semilinear_eq_zero_of_span_smul σ ⟨⟨φ, hadd⟩, hsmul⟩ g h0 s
    (fun h' => hs (RingOfIntegers.coe_eq_zero_iff.1 h')) F hW


set_option synthInstance.maxHeartbeats 400000 in
theorem noCommonZero_of_tiedW : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → S.sW ≠ 0 → ∀ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW S Gc Prw → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) := by
  intro hC D T h EX j hj S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hP hs G hG
  obtain ⟨hDF, -, hr, hl⟩ := (GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0
    hj.1 hP).1 wL (Set.mem_insert _ _)
  have hlp := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj wL hl
  have hg : ∀ i, 2 * WeightAlgebra.DF ka + 2 < D.host.g i := hP.2.2.2.1.2.2.2.2.2
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hdeg : 4 * WeightAlgebra.DF wL + 4 ≤ T.Q.l.M := by
    have h1 : (2 * WeightAlgebra.DF ka + 3) * 3 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (hg 0) (by have := hg 1; omega)
    omega
  refine GlobalTheory.FrameZero.noCommonZero_of_readings D T h j hj (wtA wL) wL.n G.N _
    (fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j wL (G.w i).2)) fun k x hx => ?_
  obtain ⟨f, hf, hf0⟩ := GlobalTheory.noCommonZero_of_chartIndep hC D T h j hj wL hr hlp hdeg (half_level_generator_norm D T h EX) T.σ₀ T.good_σ₀ k x hx
  have hc : f ∈ cutR T.C j wL := by
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA wL) hlp f hf
  have hF : (⟨f, hc⟩ : (recB h.toLawsCore).Cusp j wL) ∈ (recPJ h j hj).thAll wL := Submodule.subset_span hf
  by_contra hno
  have hno' : ∀ i, rdU (T.U j T.σ₀) (G.w i).1 k x = 0 := fun i => by
    by_contra h'
    exact hno ⟨i, h'⟩
  have hadd : ∀ F F' : T.R j, rdU (T.U j T.σ₀) (F + F') k x = rdU (T.U j T.σ₀) F k x + rdU (T.U j T.σ₀) F' k x :=
    fun F F' => by rw [map_add (f := _)]; rfl
  have hsmul : ∀ (a : T.Q.c.F) (F : T.R j), rdU (T.U j T.σ₀) (a • F) k x = T.σ₀ a * rdU (T.U j T.σ₀) F k x :=
    fun a F => by rw [map_smulₛₗ]; rfl
  exact hf0 (eq_zero_of_span_eq_WWc (recPJ h j hj) wL G.w S.sW hs hG.1 T.σ₀
    (fun F => rdU (T.U j T.σ₀) F.1 k x) (fun F F' => hadd F.1 F'.1) (fun a F => hsmul a F.1) hno' ⟨f, hc⟩ hF)

end GlobalTheory.RunIn
end

