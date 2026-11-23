module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSelfDualPairGaloisConjugateHomLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumSize.TopInt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def primeUnder (w : PlL D) : ℕ := ringChar (𝓞 D.what₂.LL ⧸ w.asIdeal)

theorem primeUnder_mem (w : PlL D) : ((primeUnder w : ℕ) : 𝓞 D.what₂.LL) ∈ w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem primeUnder_prime (w : PlL D) : (primeUnder w).Prime := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (𝓞 D.what₂.LL ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  exact CharP.char_is_prime (𝓞 D.what₂.LL ⧸ w.asIdeal) (ringChar (𝓞 D.what₂.LL ⧸ w.asIdeal))

def kerLoss (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (X Y : Node) (l n : ℕ) : ℝ :=
  (((∑ τ, ∑ a, (wt G Y τ).natW a : ℕ) : ℝ) + (D.R.f : ℝ) * (G.V X).rank * (G.V Y).rank) *
      (δ l + (if l = D.host.d then 1 else 0) + n) +
    (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (if (l : ℝ) ≤ C1 * b then Real.logb l (C1 * b) else 0)

def topDl (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (w : PlL D) : ℝ :=
  (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 *
    ∑ j ∈ Finset.range D.R.m, kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) (depL G (primeUnder w))

theorem vw_natCast_nonneg (w : PlL D) (n : ℕ) : 0 ≤ vw w ((n : ℕ) : D.what₂.LL) := by
  have e : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) ((n : ℕ) : D.what₂.LL) =
      ((Ideal.span {((n : ℕ) : 𝓞 D.what₂.LL)} : Ideal (𝓞 D.what₂.LL)) : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      map_natCast (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)]
  unfold vw
  rw [e]
  exact FractionalIdeal.count_coe_nonneg _ _ _

theorem kerLoss_nonneg (G : GridData L sc) {δ : ℕ → ℝ} (hδ : ∀ l, 0 ≤ δ l) (C1 b : ℝ) (X Y : Node) {l : ℕ} (hl : l.Prime)
    (n : ℕ) : 0 ≤ kerLoss G δ C1 b X Y l n := by
  unfold kerLoss
  have h1 : 0 ≤ (if l = D.host.d then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have h2 : 0 ≤ (if (l : ℝ) ≤ C1 * b then Real.logb l (C1 * b) else 0) := by
    split_ifs with h
    · exact Real.logb_nonneg (by exact_mod_cast hl.one_lt) (le_trans (by exact_mod_cast hl.one_lt.le) h)
    · exact le_rfl
  have := hδ l
  positivity

theorem kerLoss_mono (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (X Y : Node) (l : ℕ) {n n' : ℕ} (h : n ≤ n') :
    kerLoss G δ C1 b X Y l n ≤ kerLoss G δ C1 b X Y l n' := by
  unfold kerLoss
  have : (n : ℝ) ≤ n' := by exact_mod_cast h
  gcongr

theorem le_topDl (G : GridData L sc) {δ : ℕ → ℝ} (hδ : ∀ l, 0 ≤ δ l) {C1 : ℝ} (hC1 : 0 ≤ C1) (b : ℝ) (w : PlL D) {j : ℕ}
    (hj : j < D.R.m) {n : ℕ} (hn : n ≤ depL G (primeUnder w)) :
    (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 * kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) n ≤
      topDl G δ C1 b w := by
  unfold topDl
  have h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 :=
    mul_nonneg (by exact_mod_cast vw_natCast_nonneg w _) hC1
  refine mul_le_mul_of_nonneg_left ?_ h0
  refine le_trans (kerLoss_mono G δ C1 b _ _ _ hn) ?_
  exact Finset.single_le_sum (f := fun j => kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) (depL G (primeUnder w)))
    (fun j _ => kerLoss_nonneg G hδ C1 b _ _ (primeUnder_prime w) _) (Finset.mem_range.2 hj)

theorem inLat_mono {n : ℕ} {lam : D.what₂.Tau → DomWeight n} {w : PlL D} {a a' : ℝ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {v : VV ℂ lam} (h : InLat lam w a Λ v) (ha : a ≤ a') : InLat lam w a' Λ v := by
  obtain ⟨u, s, h1, h2, h3, h4⟩ := h
  exact ⟨u, s, h1, h2, h3.trans ha, h4⟩

end GlobalTheory.SumSize.TopInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositive
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SupModel

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_nonneg₀ {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    0 ≤ X.pnorm la P y := by
  unfold Data.pnorm; positivity

theorem pnorm_lact_eq {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    X.pnorm la P (lact γ y) = X.pnorm la P y := by
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  unfold Data.pnorm dmin
  simp only [GlobalTheory.MajInv.gram_lact X (X.Γ_stab γ hγ)]
  rw [hP.2.2 γ hγ _ hy, norm_mul, hχ, one_mul]

theorem pnorm_piecewise_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r}
    (hy : y ∈ X.dom) : X.pnorm la (X.dom.piecewise P 0) y = X.pnorm la P y := by
  unfold Data.pnorm
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

theorem epStar_eq_epsLev (d M : ℕ) (w M' k0 : ℝ) (hk : M' * k0 = 2 * (M : ℝ) * Real.sqrt d) :
    epStar M' (fdeg E) w k0 = epsLev E d M w := by
  unfold epsLev epStar
  congr 2
  rw [show M' * ((fdeg E : ℝ) * w + 2) * k0 * Real.log 2 = (M' * k0) * ((fdeg E : ℝ) * w + 2) * Real.log 2 by ring, hk]
  ring

theorem comp_bound {r : ℕ} (hr : 0 < r) (X : Data E r) (Xx : DataX E r) (hX : Xx.toData = X) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (hP : P ∈ X.SS la) (w : ℝ) (hw0 : 0 < w) (hw : (∑ τ, X.spread la τ) ≤ w)
    (hχ : ∀ γ ∈ X.Γ, X.χ la γ = 1) (d M : ℕ)
    (hL : ∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ Xx.L') (M' : ℝ) (hM' : 0 < M')
    (hk : M' * Xx.k0 = 2 * (M : ℝ) * Real.sqrt d)
    (hT : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ,
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M' : ℂ) * τ.1 b))
    (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))) (ho : IsOrth X x0) (hF : IsFundSet X x0 FF) :
    ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epsLev E d M w)) *
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (X.dom.piecewise P 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(muF X x0) := by
  subst hX
  intro y hy
  have h := _root_.GlobalTheory.supLoc_component E r Xx la P M' w x0 FF hr hP hM' hw hw0 hL
    (fun v hv hiso b hb hbi => by
      obtain ⟨γ, hγ, he⟩ := hT v hv hiso b hb hbi
      exact ⟨γ, hγ, hχ γ hγ, he⟩) ho hF y hy
  rw [epStar_eq_epsLev d M w M' Xx.k0 hk] at h
  refine h.trans (mul_le_mul' le_rfl ?_)
  have hae : ∀ᵐ z ∂(muF Xx.toData x0), z ∈ OmF Xx.toData x0 := by
    have h1 : ∀ᵐ z ∂(volume.restrict (OmF Xx.toData x0)), z ∈ OmF Xx.toData x0 :=
      ae_restrict_mem (ExF.isOpen_OmF Xx.toData x0).measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le h1
  refine lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [hae] with z hz
  rw [pnorm_piecewise_eq Xx.toData la P hz]

end GlobalTheory.SupModel


open GlobalTheory.SupModel in
theorem GlobalTheory.supPet_principal : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) → ∀ P ∈ holSub (U σ).X la, supE (U σ).X la P ^ 2 ≤ ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
  classical
  intro hMB hTB D j H Dw l Xo c U dict hLw σ hσ la w hw0 hspread hχ P hP
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hcusp := abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ).X la hP
  have hdat := fun k => _root_.GlobalTheory.LevGeo.exists_dataX_transv D j H Dw l Xo c U dict hLw σ hσ k
  choose Xx hXx hg hΛ hL' M' hM' hk hT using hdat
  have hfs : ∀ k, ∃ x0, IsOrth ((U σ).X k) x0 ∧ ∃ FF, IsFundSet ((U σ).X k) x0 FF := fun k => by
    obtain ⟨x0, ho, FF, hF, -⟩ := GlobalTheory.DriftCovolume.finMu_unconditional D.R.r ((U σ).X k)
    exact ⟨x0, ho, FF, hF⟩
  choose x0 ho FF hF using hfs

  set Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞ := fun k u =>
    ENNReal.ofReal (((U σ).X k).pnorm (la k) (((U σ).X k).dom.piecewise (P k) 0) u ^ 2) with hΦdef
  have hsec : ∀ k, ((U σ).X k).IsSec (la k) (P k) := fun k => (hcusp k).1.1
  have hΦm : ∀ k, Measurable (Φ k) := fun k => by
    have hm := GlobalTheory.PeterssonCompare.measurable_pnorm ((U σ).X k) (la k)
      (P := ((U σ).X k).dom.piecewise (P k) 0)
      ((hsec k).1.continuousOn.congr fun u hu => Set.piecewise_eq_of_mem _ _ _ hu)
      (fun u hu => by rw [Set.piecewise_eq_of_notMem _ _ _ hu]; rfl)
    exact ENNReal.measurable_ofReal.comp (hm.pow_const 2)
  have hΦΓ : ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x := by
    intro k γ hγ u hu
    have hu' := GlobalTheory.MajInv.lact_mem_dom ((U σ).X k) (((U σ).X k).Γ_stab γ hγ) hu
    simp only [hΦdef]
    rw [pnorm_piecewise_eq _ _ _ hu, pnorm_piecewise_eq _ _ _ hu', pnorm_lact_eq _ (hsec k) hγ hu]
  have hΦB : ∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x := by
    intro k b hb u hu
    have hu' := OrthogonalFrameDomain.rmul_mem_dom ((U σ).X k) hu hb
    simp only [hΦdef]
    rw [pnorm_piecewise_eq _ _ _ hu, pnorm_piecewise_eq _ _ _ hu',
      FrameDegreeData.pnorm_rmul ((U σ).X k) (la k) (P k) (hsec k).2.1 u hu b hb]
  obtain ⟨hS0, hStop, hΦeq⟩ := _root_.GlobalTheory.LevGeo.adelicProb_mul_volFund D j H Dw l Xo c U dict hLw σ hσ x0 FF (fun k => ⟨ho k, hF k⟩)
  have heq := hΦeq Φ hΦm hΦΓ hΦB
  have hms := _root_.GlobalTheory.LevGeo.MassLev.mass_components_le hMB hTB D j H Dw l Xo c U dict hLw σ hσ x0 FF (fun k => ⟨ho k, hF k⟩)

  obtain ⟨Kf, th, hr', -, -, hU, -⟩ := hLw.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := hU.2.2.2.1

  have hpet : (∫⁻ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j))) =
      petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
    rw [petE, eLpNorm'_eq_lintegral_eNorm, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
    refine lintegral_congr fun q => ?_
    simp only [hΦdef, ptN]
    rw [pnorm_piecewise_eq _ _ _ (hdom _), Real.enorm_eq_ofReal (pnorm_nonneg₀ _ _ _ _), ← ENNReal.ofReal_pow (pnorm_nonneg₀ _ _ _ _)]
  set S := ∑ k, muF ((U σ).X k) (x0 k) (FF k) with hSdef

  have hpt : ∀ p : Formalism.L2.Pj.FPt (U σ).X, ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P p.1) p.2) ^ 2 ≤
      ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
    rintro ⟨k, y, hy⟩
    rw [← ENNReal.ofReal_pow (pnorm_nonneg₀ _ _ _ _)]
    have h1 := GlobalTheory.SupModel.comp_bound hr ((U σ).X k) (Xx k) (hXx k) (la k) (P k) (hcusp k) w hw0 (hspread k) (hχ k)
      D.host.d l.M (hL' k) (M' k) (hM' k) (hk k) (hT k) (x0 k) (FF k) (ho k) (hF k) y hy
    have h2 : (∫⁻ z in FF k, Φ k (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k))) ≤
        petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
      calc _ ≤ ∑ k', ∫⁻ z in FF k', Φ k' (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k') (x0 k') z) ∂(muF ((U σ).X k') (x0 k')) :=
            Finset.single_le_sum (f := fun k' => ∫⁻ z in FF k', Φ k' (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k') (x0 k') z)
              ∂(muF ((U σ).X k') (x0 k'))) (fun _ _ => bot_le) (Finset.mem_univ k)
        _ = petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * S := by rw [← heq, hpet]
        _ ≤ _ := mul_le_mul' le_rfl hms
    by_cases hLc : 0 ≤ locConst D.host.E D.R.r w (epsLev D.host.E D.host.d l.M w)
    · calc _ ≤ ENNReal.ofReal (locConst D.host.E D.R.r w (epsLev D.host.E D.host.d l.M w)) * (petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * ENNReal.ofReal (massLev D.host.E D.R.r l.M)) :=
            h1.trans (mul_le_mul' le_rfl h2)
        _ = _ := by
          rw [supConst, ENNReal.ofReal_mul hLc]
          ring
    · rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hLc)), zero_mul] at h1
      exact (le_antisymm h1 bot_le) ▸ bot_le

  show (⨆ p : Formalism.L2.Pj.FPt (U σ).X, ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P p.1) p.2)) ^ 2 ≤ _
  rcases isEmpty_or_nonempty (Formalism.L2.Pj.FPt (U σ).X) with hE | hN
  · rw [iSup_of_empty]; simp
  · rw [ENNReal.iSup_pow]
    exact iSup_le hpt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorFixedPrincipalCongruence
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

open GlobalTheory.FunObj.StdDatum

namespace GlobalTheory.BotPairSmall.CvFix

theorem om_cvec_of_congOne : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ k ∈ intG D a, CongOne D (D.host.conj • 𝔪) k → W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho k hk hkc
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    rw [smul_smul, GlobalTheory.GaloisTwist.conj_mul_conj, one_smul]
  have h := _root_.GlobalTheory.FunObj.FixKey.om_cosetV_of_congOne D δ t0 hc e0 hv W (D.host.conj • 𝔪) (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm) ?_ ?_ o (by omega) k hk hkc
  · exact h
  · rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  · intro u hu hu1
    apply hcond u hu
    rwa [hcc, mul_comm] at hu1

end GlobalTheory.BotPairSmall.CvFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.CosetFix

variable {D : D7}

theorem zeroAt_zero (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left _, 0, zero_mem _, by simp⟩

theorem trivAt_one {N : ℕ} (q : ℕ) : TrivAt D q ((1 : GA D N) : GL (Fin N) (AE D)) := fun i j => by
  simpa using zeroAt_zero (D := D) q


set_option maxHeartbeats 1000000 in
theorem fix_of_prop {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hT : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d) {g' : GA D P.d}
    {H : VC D P.a P.d → ℂ} {c : ℂ} (hc' : P.W.Om 1 g' P.e0 = c • H) :
    H ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧ ∀ k : GA D P.a, P.W.Om k 1 P.e0 = P.e0 → P.W.Om k 1 H = H := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply P.W.nz
    have h0 : P.W.Om 1 g' P.e0 = 0 := by rw [hc', zero_smul]
    have e := P.W.mul 1 1 g'⁻¹ g' P.e0 hT
    have e1 : (1 : GA D P.a) * 1 = 1 := mul_one 1
    have e2 : g'⁻¹ * g' = 1 := inv_mul_cancel g'
    rw [e1, e2, P.W.one _ hT, h0] at e
    have z := P.W.smul 1 g'⁻¹ (0 : ℂ) (0 : VC D P.a P.d → ℂ) (NormUniq.tt_zero _)
    have z0 : (0 : ℂ) • (0 : VC D P.a P.d → ℂ) = 0 := zero_smul ℂ _
    rw [z0] at z
    rw [e, z]
    exact zero_smul ℂ _
  have hHT : H ∈ TT D (tor0 D ⊤ δ) P.a P.d := by
    have e : H = c⁻¹ • P.W.Om 1 g' P.e0 := by rw [hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hm : P.W.Om 1 g' P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := P.W.maps 1 g' P.e0 hT
    rw [e]
    exact NormUniq.tt_smul hm c⁻¹
  refine ⟨hHT, fun k he => ?_⟩
  have e1 := P.W.mul k 1 1 g' P.e0 hT
  have e2 := P.W.mul 1 k g' 1 P.e0 hT
  have f1 : k * (1 : GA D P.a) = k := mul_one k
  have f2 : (1 : GA D P.d) * g' = g' := one_mul g'
  have f3 : (1 : GA D P.a) * k = k := one_mul k
  have f4 : g' * (1 : GA D P.d) = g' := mul_one g'
  rw [f1, f2] at e1
  rw [f3, f4] at e2
  have e3 : P.W.Om k 1 (P.W.Om 1 g' P.e0) = P.W.Om 1 g' P.e0 := by rw [← e1, e2, he]
  rw [hc', P.W.smul _ _ _ _ hHT] at e3
  exact smul_right_injective _ hc0 e3

theorem iop_facts (hI : Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 ∈
      TT D (tor0 D ⊤ δ) P.a P.d ∧
    ∀ k : GA D P.a, P.W.Om k 1 P.e0 = P.e0 →
      P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 := by
  obtain ⟨g', hg'⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D P.d _ (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d)
  obtain ⟨c, hc⟩ := VacMove.exists_scalar hI P.crv P.vac.1 P.W 1 g' (VacMove.moves_one D P.a) hg'
  exact fix_of_prop P (VacMove.vac_TT hI.g1 P.crv P.vac.1) (c := c) (by rw [hc]; funext z; rfl)

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem vac_fix_split (G : GridData L sc) (i j : Fin D.R.m) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) (hs : SuppSplit D (k : GL (Fin P.a) (AE D))) : P.W.Om k 1 P.e0 = P.e0 := by
  obtain ⟨x, hxu, hxi, hx, h1, h2⟩ := GlobalTheory.FunObj.NormUniq.SplitDet.exists_splitComp_det hk hk' hs
  have hm : Moves D (k : GL (Fin P.a) (AE D)) (stdL D P.a) := by
    simpa using VacMove.moves_mul_int hk (VacMove.moves_one D P.a)
  have e := P.W.split k 1 x 1 (stdL D P.a) (stdL D P.d) hs (fun q _ _ => trivAt_one q)
    (fun q hq hi => ⟨hxi q hq hi, by simpa using zeroAt_zero (D := D) q⟩) hx (by simp) hm (VacMove.moves_one D P.d)
  have hc : P.W.chV'.f x ^ P.W.ep' = 1 := by
    rw [h.chars.2 x]
    show ((nuH G μ₀ i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x))⁻¹ = 1
    rw [GlobalTheory.NuTrivSq.nuH_finIdl_eq_one G i j hL x hxu h1 h2, inv_one]
  rw [e, map_one, one_zpow, hc, one_mul,
    show La D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d) = La0 D (tor0 D ⊤ δ) P.a P.d from rfl,
    VacMove.iop_self D _ (La0 D (tor0 D ⊤ δ) P.a P.d) P.vac.1]
  funext z
  simp

theorem vac_fix (G : GridData L sc) (i j : Fin D.R.m) (hI : Inp D) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) : P.W.Om k 1 P.e0 = P.e0 := by
  obtain ⟨ks, ki, rfl, hs, hi, hs', hss, hii⟩ := GlobalTheory.CongSplitFactor.exists_split_inert_factor hk hk'
  have hT := VacMove.vac_TT hI.g1 P.crv P.vac.1
  have h1 : P.W.Om ki 1 P.e0 = P.e0 :=
    P.W.inert ki 1 ((mem_intG ki).1 hi) ((mem_intG 1).1 (one_mem _)) hii (fun q _ _ => trivAt_one q)
  have e := P.W.mul ks ki 1 1 P.e0 hT
  rw [mul_one] at e
  rw [e, h1, vac_fix_split G i j hL h hs hs' hss]

theorem cosetVec_fix (G : GridData L sc) (i j : Fin D.R.m) (hI : Inp D) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) : P.W.Om k 1 (cosetVec P (condE G.pl) 0) = cosetVec P (condE G.pl) 0 := by
  obtain ⟨hHT, hfix⟩ := iop_facts hI P (condE_ne_bot G.pl)
  have hH := hfix k (vac_fix G i j hI hL h hk hk')
  have hW := GlobalTheory.HeisFix.heis_fix hI P (condE_ne_bot G.pl) 0 hk hk' hHT hH
  have hWT := GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT P.crv one_pos (by rw [one_smul]; exact pt_unitBlock_mem δ 0 P.a P.d) hHT
  unfold cosetVec
  rw [P.W.smul _ _ _ _ hWT, hW]

end GlobalTheory.FunObj.CosetFix
end
end

