module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeCoefficientsCommonZerosSimple
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormQuotientThetaFlatAttainsSupOffCommonZeros
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsNotSmallWhereCombinationsVanish

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeCoefficientsCommonZerosSimpleStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_coefficients_common_zeros_simple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) , ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∀ x ∈ X.dom, sf 0 x ≠ 0 → (∀ k : Fin (nd X), sf k.succ x = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => sf k.succ (cpt X x z) / sf 0 (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
  first | exact @GlobalTheory.ParamSard.main | exact GlobalTheory.ParamSard.main | (intros; apply GlobalTheory.ParamSard.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoverMulShortThetaSeriesIndepOfFramedLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortLiftInvariance

theorem shortValAt_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) {n : ℕ}
    (w w' : (Fin n → LevQ Dw l) → c.F) (t : c.F) (hw : ∀ q, w' q = t * w q)
    (Λ : GenLat E n) (β : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S)
    (h : ShortValAt Xo c nab w Λ β N P y v) :
    ShortValAt Xo c nab w' Λ β N P y (algebraMap c.F S t * v) := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [map_mul, AlgHom.commutes, h7]
  simp only [hw, map_mul, _root_.mul_assoc]
  by_cases hf : Finite (Fin n → LevQ Dw l)
  · have := Fintype.ofFinite (Fin n → LevQ Dw l)
    simp only [finsum_eq_sum_of_fintype]
    rw [← Finset.mul_sum]
    ring
  · have := not_finite_iff_infinite.mp hf
    simp [Nat.card_eq_zero_of_infinite]

theorem cover_product_indep_of_lift : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), @ToroidalLevelCompatibility E _ _ _ H Dw → d.IsLev → d.l₂.A = l.A → ∀ [StarRing (𝓞 E)], IsNab d.Xo₂ d.c₂ d.nab₂ → (∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (x0 : Fin n → Dw.La) (β : d.c₂.F), ∀ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), DeltaDat.EtaOK { d with r := r', m := m' } → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y : FrPt Xo c k) (y₂ y₂' : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → FrOver { d with r := r', m := m' } y₂' y → ∀ v v', ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂ v → ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂' v' → evR d.Xo₂ d.c₂ d.cδ y₂ * v = evR d.Xo₂ d.c₂ d.cδ y₂' * v' := by
  intro hL hC E _ _ _ H Dw l Xo c n d hN1 hLev hA _ hNab hex Λ N hU hT hO a P hP x0 β r' m' hE k _ _ _ _ hk y y₂ y₂' hF hF' v v' hv hv'
  obtain ⟨ph, ψ, x₀, hph, hpsi⟩ := hex
  obtain ⟨hDvd, hM, hcop, hMb, hI, hEta, -, -, -⟩ := hLev
  obtain ⟨g, ρ, ν, hg, hρ, hmv, hfm⟩ :=
    GlobalTheory.exists_levMove_of_frOver hL E H Dw l Xo c n d hN1 hDvd hM hEta r' m' hE k hk y y₂ y₂' hF hF'
  obtain ⟨kI, σq, hk1, hk2, hk3⟩ :=
    GlobalTheory.DatumInverseCharacter.datum_inv_char E H Dw l Xo c n d hM hcop hMb hI hDvd ph ψ x₀ hph g hg
  have hx : y₂'.x = y₂.x ≫ ρ.hom := by
    unfold FrMove at hfm
    exact hfm.1
  have hmod : ∀ a : Dw.La, Dw.ModN d.l₂.A ((g.f d.l₂.A) a - a) := by
    intro a
    rw [hA]
    unfold Sim.InGam at hg
    exact hg.2.2 a
  unfold DeltaDat.PsiTie at hpsi
  have hev := hpsi kI g ρ hg hmod hρ hk1 k y₂ y₂' hx
  have h1 := _root_.GlobalTheory.ShortValMove.shortValAt_move hL hC E H Dw d.l₂ d.Xo₂ d.c₂ _ hNab k ρ.hom ν (g.f d.l₂.M) (g.f d.l₂.A)
    y₂ y₂' hmv hfm σq hk2 n a P hP (d.w x0) Λ β N v' hv'
  have hw : ∀ q, d.w x0 q = d.eF ↑(ψ kI) * d.w x0 (fun b => σq.symm (q b)) := by
    intro q
    rw [hk3, ← _root_.mul_assoc, ← map_mul, Units.mul_inv, map_one, _root_.one_mul]
  have h2 := shortValAt_smul d.Xo₂ d.c₂ _ _ (d.w x0) (d.eF ↑(ψ kI)) hw Λ β N P y₂ v' h1
  have hu := (_root_.GlobalTheory.shortThetaValue_existsUnique_natural hL hC E H Dw d.l₂ d.Xo₂ d.c₂ _ hNab n Λ N hU hT hO a P hP (d.w x0) β).1 k y₂
  rw [hu.unique hv h2, hev]
  ring

end GlobalTheory.ShortLiftInvariance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRankOneCuspDataLogBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.CuspDataBounds

theorem exists_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (X : Data E r)
    (hX : Xx.toData = X) (S : Set E)
    (hΛ : Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ Xx.L', v = a • u})
    (NA NC : ℕ) (hA : 0 < NA) (hC : 0 < NC) (hAi : ∀ a ∈ S, IsIntegral ℤ ((NA : E) * a)) (hCS : (NC : E) ∈ S) :
    ∃ e : XExt X, e.NA = NA ∧ e.NC = NC ∧ e.g = Xx.g ∧ e.k0 = Xx.k0 := by
  subst hX
  refine ⟨⟨Xx.k0, Xx.minWeight_pos, Xx.k0_le, Xx.ξ0_abs, Xx.EF_int, Xx.EF_perf, Xx.L', Xx.L'_fg, Xx.L'_int,
      Xx.L'_dual, NA, NC, hA, hC, ?_, ?_, Xx.g, Xx.g_pos, Xx.cong⟩, rfl, rfl, rfl, rfl⟩
  ·
    intro x hx
    rw [hΛ] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hy
      rw [smul_smul]
      have h1 : ((NA : E) * a) • u = (⟨(NA : E) * a, hAi a ha⟩ : 𝓞 E) • u := by
        rw [← algebraMap_smul E (⟨(NA : E) * a, hAi a ha⟩ : 𝓞 E) u]
        rfl
      rw [h1]
      exact Xx.L'.smul_mem _ hu
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact Xx.L'.add_mem hy hz
    | smul c y _ hy =>
      rw [smul_comm]
      exact Xx.L'.smul_mem c hy
  ·
    intro x hx
    rw [hΛ]
    exact Submodule.subset_span ⟨(NC : E), hCS, x, hx, rfl⟩

theorem weight_bounds (L f r n d : ℝ) (hL : 2 ≤ L) (hf : 1 ≤ f) (hfr : f ≤ r) (hrn : r ≤ n) (hd : 0 ≤ d)
    (hn : Real.log n ≤ L) (hD : Real.log (1 + d) ≤ 2 * L) :
    Real.log (d + f * n + 1) ≤ 3 * L ∧ Real.log (f * (d + f * n + 1) + 2) ≤ 5 * L ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ d + f * r * n / 2 → Real.log (1 + s) ≤ 3 * L := by
  have hx3 : 3 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have e2 : Real.exp (2 * L) = Real.exp L ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp (3 * L) = Real.exp L ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have e5 : Real.exp (5 * L) = Real.exp L ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  set x := Real.exp L with hx
  have hn0 : 0 < n := by linarith
  have hnx : n ≤ x := (Real.log_le_iff_le_exp hn0).1 hn
  have hdx : 1 + d ≤ x ^ 2 := by rw [← e2]; exact (Real.log_le_iff_le_exp (by linarith)).1 hD
  have hfx : f ≤ x := by linarith
  have hrx : r ≤ x := by linarith
  have hfn : f * n ≤ x ^ 2 := by nlinarith
  have hfn0 : 0 ≤ f * n := by nlinarith
  have hx2 : 9 ≤ x ^ 2 := by nlinarith
  have hx23 : 3 * x ^ 2 ≤ x ^ 3 := by nlinarith
  have hx35 : 9 * x ^ 3 ≤ x ^ 5 := by nlinarith
  have hA : d + f * n + 1 ≤ 2 * x ^ 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.log_le_iff_le_exp (by linarith), e3]
    linarith
  · have hB : f * (d + f * n + 1) ≤ x * (2 * x ^ 2) := mul_le_mul hfx hA (by linarith) (by linarith)
    rw [Real.log_le_iff_le_exp (by nlinarith), e5]
    nlinarith
  · intro s hs0 hs
    have hfr0 : 0 ≤ f * r := by nlinarith
    have hC : f * r * n ≤ x ^ 3 := by
      have h1 : f * r ≤ x * x := mul_le_mul hfx hrx (by linarith) (by linarith)
      have h2 : f * r * n ≤ x * x * x := mul_le_mul h1 hnx hn0.le (by positivity)
      nlinarith
    rw [Real.log_le_iff_le_exp (by linarith), e3]
    nlinarith

private theorem level_M_eq_g_zero_mul_g_one_of_lawsM {D : D7} (T : Core D) (h : Formalism.L2.Pj.LawsM T) :
    T.Q.l.M = D.host.g 0 * D.host.g 1 := by
  have p := h.pins.2.1
  unfold Formalism.L2.Pj.Par.PinLevel at p
  exact p.1

theorem cusp_data_bounds : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (e : ∀ k : (T.U j σ).Comp, XExt ((T.U j σ).X k)) (M wg : ℝ), 1 ≤ M ∧ Real.log M ≤ 30 * large₂.sc.L ∧ 0 < wg ∧ Real.log wg ≤ 3 * large₂.sc.L ∧ Real.log ((fdeg D.host.E : ℝ) * wg + 2) ≤ 5 * large₂.sc.L ∧ ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ wg ∧ (∀ v ∈ (e k).L', herm ((T.U j σ).X k).Gm v v = 0 → ∀ b : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j σ).X k).Γ, ((T.U j σ).X k).χ (laU (T.U j σ) (wtA w) w.n k) γ = 1 ∧ ∀ τ : ((T.U j σ).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j σ).X k).flowMat v τ ((M : ℂ) * τ.1 b)) ∧ Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L ∧ Real.log (e k).NA ≤ 4 * large₂.sc.L ∧ Real.log (e k).NC ≤ 2 * large₂.sc.L ∧ Real.log (e k).g ≤ 19 * large₂.sc.L ∧ Real.log (1 / (e k).k0) ≤ 3 * large₂.sc.L := by
  intro D T h hGam large₂ j hj w hP hL hrn σ hσ
  obtain ⟨hgi, hlrd, hdd, hcc, -, -, -, hDF, hn⟩ := hP
  obtain ⟨⟨NA, hNA0, hNAi, hNAL⟩, hccA, hcc0, ⟨m, hm0, hmi, hmL⟩, hk0L, hfdeg, -, -, hfr, hf1, hxicc, -,
    hxiabs⟩ := _root_.GlobalTheory.HostClear.host_clear D large₂.sc.L hL hlrd hdd hcc
  have h10 := _root_.GlobalTheory.RunIn.WtSize.laU_wtA_size D T h j hj w σ hσ
  obtain ⟨hW1, hW2, hW3⟩ := weight_bounds large₂.sc.L (D.R.f : ℝ) (D.R.r : ℝ) (w.n : ℝ) (WeightAlgebra.DF w : ℝ) hL
    (by exact_mod_cast hf1) (by exact_mod_cast hfr) (by exact_mod_cast hrn) (by positivity) hn hDF
  have hwg0 : 0 < (WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1 := by positivity
  have hwgF : Real.log ((fdeg D.host.E : ℝ) * ((WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1) + 2) ≤ 5 * large₂.sc.L := by
    rw [hfdeg]; exact hW2
  have hspread : ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤
      (WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1 := fun k => by linarith [(h10 k).1]
  have hla : ∀ k, Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L :=
    fun k => hW3 _ (by positivity) (h10 k).2
  rcases isEmpty_or_nonempty (T.U j σ).Comp with hE | ⟨⟨k₁⟩⟩
  · exact ⟨fun k => isEmptyElim k, 1, _, le_rfl, by simp; positivity, hwg0, hW1, hwgF, fun k => isEmptyElim k⟩
  have hPr : GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M :=
    fun k γ h1 h2 => hGam j hj σ hσ k γ h1 h2
  choose Xx hXx hXg hXΛ hXk0 hXNA hXNC using _root_.GlobalTheory.LatticeData.exists_dataX_of_hasPrinc D T.toCore h.toLawsCore j hj σ hσ hPr
  choose e heNA heNC heg hek0 using fun k => exists_ext (Xx k) _ (hXx k) _ (hXΛ k) NA
    (Ideal.absNorm D.host.ccK) hNA0 hcc0 hNAi hccA
  have hMpos : 0 < T.Q.l.M := by rw [← hXg k₁]; exact (Xx k₁).g_pos
  have hlev : T.Q.l.M = D.host.g 0 * D.host.g 1 := level_M_eq_g_zero_mul_g_one_of_lawsM T.toCore h.toLawsCore.toLawsM

  have hgL : Real.log (T.Q.l.M : ℝ) ≤ 19 * large₂.sc.L := by
    have h0 : D.host.g 0 ≠ 0 := fun h0 => by simp [hlev, h0] at hMpos
    have h1 : D.host.g 1 ≠ 0 := fun h1 => by simp [hlev, h1] at hMpos
    rw [hlev, Nat.cast_mul, Real.log_mul (by exact_mod_cast h0) (by exact_mod_cast h1)]
    linarith [hgi 0, hgi 1]

  have hmX : ∀ k, IsIntegral ℤ ((m : D.host.E) * (2 * ((T.U j σ).X k).ξ0)) := by
    intro k
    rcases GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq D.host.E D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
      hxicc ((T.U j σ).X k).ξ0_im (by rw [hxiabs, h.xiAbs j hj σ hσ k]) with h1 | h1
    · rw [h1]; exact hmi
    · rw [h1]; convert hmi.neg using 1; ring
  have hMk : ∀ k, ((e k).toX.g * (e k).toX.NA * (e k).toX.NC * m : ℕ) =
      T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m := by
    intro k
    show (e k).g * (e k).NA * (e k).NC * m = _
    rw [heg, heNA, heNC, hXg]
  have hM1 : 1 ≤ T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hMpos hNA0) hcc0) hm0
  refine ⟨e, ((T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m : ℕ) : ℝ), _, by exact_mod_cast hM1, ?_, hwg0, hW1,
    hwgF, fun k => ⟨hspread k, ?_, hla k, ?_, ?_, ?_, ?_⟩⟩
  · push_cast
    have hN : (0 : ℝ) < NA := by exact_mod_cast hNA0
    have hC : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hcc0
    have hm : (0 : ℝ) < m := by exact_mod_cast hm0
    have hg : (0 : ℝ) < T.Q.l.M := by exact_mod_cast hMpos
    rw [Real.log_mul (by positivity) hm.ne', Real.log_mul (by positivity) hC.ne',
      Real.log_mul hg.ne' hN.ne']
    linarith
  · intro v hv hv0 b hb hbi
    obtain ⟨γ, hγ, hγf⟩ := GlobalTheory.TransvLevel.transv_mem D.host.E D.R.r (e k).toX m (hmX k) v hv hv0 b hb hbi
    refine ⟨γ, hγ, h.chiTriv j hj σ hσ _ _ (Formalism.L2.Pj.dom_wtA w) k γ hγ, fun τ => ?_⟩
    have := hγf τ
    rw [hMk k] at this
    exact this
  · rw [heNA]; exact hNAL
  · rw [heNC]; exact hcc
  · rw [heg, hXg]; exact hgL
  · rw [hek0, hXk0]; exact hk0L

end GlobalTheory.CuspDataBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSmallCoeffEtaValAtNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaForm

private theorem frMap_id_self {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have eid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 (Sp S) := Spec.map_id _
  have did : spMap (dualMap (AlgHom.id c.F S).toRingHom) = 𝟙 _ := by
    have : dualMap (AlgHom.id c.F S).toRingHom = RingHom.id _ :=
      RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [this]
    exact Spec.map_id _
  refine ⟨by rw [eid, Category.id_comp], fun τ i => by rw [did, Category.id_comp], 𝟙 _, by simp,
    by rw [eid]; simp, ?_⟩
  intro i h
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx y.x).presheaf.map_id]
    rfl
  rw [e, CommRingCat.hom_id, RingHom.id_apply]

theorem exists_small_coeff_etaValAt_ne_zero : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → 1 < R → ∀ [Fintype (LatMod Dw R)] (n : ℕ) (x₀ : Fin n → Dw.La) (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (Nc : ℕ) (y : Fin Nc → FrPt Xo c K), ∃ cf : (Fin n → LatMod Dw R) → ℕ, (∀ j, cf j ≤ Nc * Nat.card (LevGrp Dw (R ^ 4))) ∧ ∀ k v, EtaValAt Xo c R (fun j => (cf j : ℤ)) (shiftFam R x₀) (y k) v → v ≠ 0 := by
  intro hL E _ _ _ H Dw l Xo c R hodd hR _ n x₀ K _ _ _ Nc y
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  haveI : Finite (LevGrp Dw (R ^ 4)) := (GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R hR).1
  letI : Fintype (LevGrp Dw (R ^ 4)) := Fintype.ofFinite _
  have hlev := GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (by positivity)
  choose ev hev using fun k => hlev.2.2.2 K (y k).x
  have hpow : ∀ k q, ev k q ^ ((R ^ 2) ^ 2) = 1 := by
    intro k q
    have h := (hlev.2.1 K K (RingHom.id K) (y k).x (y k).x (𝟙 _)
      (by rw [Over.id_left]; exact (Spec.map_id _).symm) (ev k) (hev k)).2 q
    rwa [← pow_mul]
  choose w hw using fun k q =>
    ((GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hodd.pow).1 K (y k) (ev k q) (hpow k q)).exists
  obtain ⟨cf, hcf, hne⟩ := exists_sum_natCast_smul_apply_ne_zero (K := K)
    (V := Fin Nc × LevGrp Dw (R ^ 4) → K) (W := fun _ : Fin Nc × LevGrp Dw (R ^ 4) => K)
    (fun a => LinearMap.proj a)
    (fun (j : Fin n → LatMod Dw R) a => ∏ b, w a.1 (a.2 (shiftFam R x₀ j b)))
    (fun a => by
      obtain ⟨u, hu⟩ := GlobalTheory.exists_shift_nullVal_ne_zero hL E H Dw l Xo c R hodd hR K (y a.1) (ev a.1) (w a.1) (hev a.1) (hw a.1)
        n x₀ a.2
      refine ⟨u, ?_⟩
      rw [LinearMap.proj_apply]
      exact Finset.prod_ne_zero_iff.2 fun b _ => hu b)
  refine ⟨cf, fun j => ?_, fun k v hv => ?_⟩
  · have := hcf j
    rwa [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card] at this
  · have h0 : EtaValAt Xo c R (fun j => (cf j : ℤ)) (shiftFam R x₀) (y k)
        (etaExpr (R ^ 4) (fun j => (cf j : ℤ)) (shiftFam R x₀) (w k)) :=
      ⟨K, inferInstance, inferInstance, AlgHom.id c.F K, y k, ev k, w k,
        RingHom.FaithfullyFlat.of_bijective Function.bijective_id, frMap_id_self (y k), hev k, hw k, rfl⟩
    have hu := ((GlobalTheory.EtaForm.etaValAt_existsUnique_natural hL E H Dw l Xo c R hodd _ n (fun j => (cf j : ℤ)) (shiftFam R x₀)).1 K (y k)).unique
      hv h0
    rw [hu, etaExpr, finprod_eq_prod_of_fintype]
    refine Finset.prod_ne_zero_iff.2 fun g _ => ?_
    have := hne (k, g)
    simpa [Finset.sum_apply] using this

end GlobalTheory.EtaForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueCanonicalConnectionEqPolyDeriv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem sum_support_natCast_smul {σ K : Type} [Field K] [Algebra K ℂ] (N : ℕ) (P : MvPolynomial σ K)
    (hs : ((N : K) • P).support = P.support) (v : (σ →₀ ℕ) → ℂ) :
    ∑ m ∈ ((N : K) • P).support, algebraMap K ℂ (((N : K) • P).coeff m) * v m =
      (N : ℂ) * ∑ m ∈ P.support, algebraMap K ℂ (P.coeff m) * v m := by
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, map_natCast, _root_.mul_assoc]

theorem harm_nab_eq_polyDeriv : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : Fin n → (Fin g → ℂ) → ℂ), (∀ b, Φ.toAnFr.Rd k (F b) (θ b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, θ b (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ _ y g ty el Φ nab hnab k n F θ hθ a P hP
  classical
  obtain ⟨N, hN, hNP, hs⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  obtain ⟨C₁, hex₁, hpin₁⟩ := hnab.2 ℂ y
  choose f₁ hf₁ using fun b => hex₁ k (F b)
  obtain ⟨C, hd, hh, hF, hu, hgerm⟩ := GlobalTheory.T.exists_analytic_biextension_chart_complex_point E H Dw l Xo c y g ty el Φ hnab.1
  subst hd
  have hdiff : ∀ b, Differentiable ℂ (θ b) := fun b =>
    ((_root_.GlobalTheory.AnVal.reading_existsUnique_isTh _ _ _ _ _ Φ.toAnFr k (F b)).2.1 (θ b) (hθ b)).1
  have hg : ∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (tay (θ b) 0) := fun b => by
    have h := hgerm k (F b) (θ b) (hθ b)
    have e : (fun p : Fin 1 × Fin C.d => (p.1, Fin.cast (rfl : C.d = C.d).symm p.2)) = id := rfl
    simp only [e, MvPowerSeries.rename_id, AlgHom.id_apply] at h
    exact h
  have h := hC E H Dw l Xo c hnab.1 ℂ y C₁ C k n F f₁ (fun b => tay (θ b) 0) hf₁ hg a _ hNP
  unfold chartVal at h
  rw [sum_support_natCast_smul N P hs, sum_support_natCast_smul N P hs] at h
  have h' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hN.ne' : (N : ℂ) ≠ 0) h
  have e₁ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C₁.B.nabVal ℂ C₁.h H.w0 k (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₁ k (F b) (f₁ b) (hf₁ b) (colOf m b)
  simp only [e₁]
  rw [h']
  have huu : C.uvec = fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ) := by
    funext ℓ i
    rw [hu ℓ i, Pi.single_apply]
    rfl
  have hpd := _root_.GlobalTheory.AnVal.polyDeriv_prod_cols (Fin C.d → ℂ) (E →+* ℂ) Dw.mult n
    (fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ)) θ hdiff
    (MvPolynomial.map (algebraMap c.F ℂ) P)
  refine Eq.trans ?_ hpd.symm
  rw [MvPolynomial.support_map_of_injective P (algebraMap c.F ℂ).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [hh, huu]
  exact nabVal_additive C.B hF H.w0 k ((GlobalTheory.SCV.contDiff_of_differentiable (hdiff b) _).contDiffAt) _ _

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormQuotientThetaFlatAttainsSupOffCommonZerosStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normQuotientThetaFlat_attains_sup_off_common_zeros : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (f : Frame X.Ψ r → ℂ), X.IsBddSec (Xa.Fp + Xa.T • Xa.L) f → (∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (Xa.T + nd X + 7)) → let Φ : Frame X.Ψ r → ℝ := fun x => X.pnorm (Xa.Fp + Xa.T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 * X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 * (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) / (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2); (∃ x ∈ X.dom, 0 < Φ x) → ∃ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) ∧ 0 < Φ x0 ∧ ∀ x ∈ X.dom, Φ x ≤ Φ x0 := by
  first | exact @GlobalTheory.QuotientMax.main | exact GlobalTheory.QuotientMax.main | (intros; apply GlobalTheory.QuotientMax.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.OneDivisionUpstairsFreeWeightStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_division_upstairs_free_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ bb : ℝ, (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) → ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) bb F → ∃ H : Fin (nd X) → V (nd X) → ℂ, (∀ k, DifferentiableOn ℂ (H k) (OmF X x0) ∧ InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X : ℕ) : ℝ) - 1 / 2)) else 0) bb (H k)) ∧ ∀ z ∈ OmF X x0, F z = ∑ k, Fl.s k (cpt X x0 z) * H k z := by
  first | exact @GlobalTheory.Shares.DivOne.divOne_up | exact GlobalTheory.Shares.DivOne.divOne_up | (intros; apply GlobalTheory.Shares.DivOne.divOne_up <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsBoundedByGenericCombinationsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_forms_bounded_by_generic_combinations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖sf i x‖ ^ 2 := by
  first | exact @GlobalTheory.Shares.forms_le_generic_comb | exact GlobalTheory.Shares.forms_le_generic_comb | (intros; apply GlobalTheory.Shares.forms_le_generic_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsNotSmallWhereCombinationsVanishStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_forms_not_small_where_combinations_vanish : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < ε * ‖sf 0 x‖ ^ 2 → c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  first | exact @GlobalTheory.Shares.Low.forms_not_small | exact GlobalTheory.Shares.Low.forms_not_small | (intros; apply GlobalTheory.Shares.Low.forms_not_small <;> assumption)
end

