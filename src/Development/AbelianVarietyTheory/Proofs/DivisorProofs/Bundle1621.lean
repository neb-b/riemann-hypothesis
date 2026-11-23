module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSkewIdealLatticeUnitVectorUnimodularEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
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
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorBlockLevelUnimodularEigen
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall

theorem cvec_eig : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = c • W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho j hj
  have hn : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  have hF := _root_.GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hmove : ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∀ y y' : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i l, (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) *
        (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) - y'.map (inc D)) i l ∈ hatId D (D.host.conj • 𝔪)) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om g g' (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0)) =
        c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
    intro g hg g' hg' y y' hy
    obtain ⟨m, hm0, hl⟩ := W.lift g g' y _ hF
    obtain ⟨z, hz1, hz2⟩ := _root_.GlobalTheory.BotPairSmall.CongApprox.approx_two_moduli D _ hn a d (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) *
        (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) m hm0
    rw [hl z hz1]
    obtain ⟨c1, hc1, e1⟩ := _root_.GlobalTheory.BotPairSmall.CvEig.om_unitVec_eig D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho g hg g' hg'
    obtain ⟨c2, hc2, e2⟩ := _root_.GlobalTheory.HeisTranslate.wd_unitVec_congr D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho z y' (fun i l => by
      have := sub_mem (hy i l) (hz2 i l)
      convert this using 1
      simp [Matrix.sub_apply, Matrix.map_apply, map_sub])
    refine ⟨c1 * c2, by rw [norm_mul, hc1, hc2, one_mul], ?_⟩
    rw [e1]
    have : ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
      intro x F c; funext w; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, e2, smul_smul]

  obtain ⟨k, hk, hjk⟩ := _root_.GlobalTheory.BotPairSmall.BlockK.blockJ_unitBlock D 𝔪 hm hcop o a d ho j hj
  obtain ⟨y', -, hy'⟩ := _root_.GlobalTheory.BotPairSmall.CongApprox.approx_two_moduli D _ hn a d ((unitBlock D o a d).map (inc D) *
    (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) 1 one_pos
  have hjJ : j ∈ intG D d := GlobalTheory.BotPairSmall.blockJ_le D 𝔪 o d hj
  obtain ⟨c1, hc1, e1⟩ := hmove 1 (one_mem _) j hjJ (unitBlock D o a d) y' (fun i l => by
    have := add_mem (hjk i l) (hy' i l)
    convert this using 1
    simp [Matrix.sub_apply])
  obtain ⟨c2, hc2, e2⟩ := hmove k hk 1 (one_mem _) (unitBlock D o a d) y' (fun i l => by
    convert hy' i l using 1
    simp [Matrix.sub_apply])
  have hwd : ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
    intro x F c; funext w; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
  set s : ℂ := ((Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d)) : ℂ)) with hs_def
  have hs : s ≠ 0 := by
    have h0 : (Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hn)
    have : 0 < Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d)) :=
      Real.sqrt_pos.2 (pow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)) _)
    exact Complex.ofReal_ne_zero.2 this.ne'
  have hcv := _root_.GlobalTheory.BotPairSmall.cvec_conj_mem_TT D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hV : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) =
      s • GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
    rw [GlobalTheory.BotPairSmall.cvec, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have hVT : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d := by
    rw [hV]
    obtain ⟨h1, m, hm0, h2⟩ := hcv
    exact ⟨h1.const_smul s, m, hm0, fun x hx => by rw [hwd, h2 x hx]⟩
  have hc2' : c2 ≠ 0 := by intro h; rw [h, norm_zero] at hc2; exact zero_ne_one hc2
  refine ⟨k, hk, c1 / c2, by rw [norm_div, hc1, hc2, div_one], ?_⟩
  show W.Om 1 j (s⁻¹ • _) = (c1 / c2) • W.Om k 1 (s⁻¹ • _)
  rw [W.smul _ _ _ _ hVT, W.smul _ _ _ _ hVT, e1, e2, smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory.BotPairSmall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsFiniteDimensional
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevGeo.RankBd

theorem supConst_nonneg (E : Type) [Field E] [NumberField E] (r d M : ℕ) (w : ℝ) : 0 ≤ supConst E r d M w := by
  unfold supConst locConst massLev GlobalTheory.UCls.massBd multBd
  have h1 : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
  have h2 : Even (2 * fdeg E * r ^ 2) := by rw [mul_assoc]; exact even_two_mul _
  refine mul_nonneg (mul_nonneg (div_nonneg (by positivity) (pow_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) _))
    (h2.pow_nonneg _)) ?_
  have := Real.rpow_nonneg h1 ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2)
  positivity

variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}

theorem pnorm_fac_pos (Y : Data D.host.E r) (la : Wt Y.Ψ r) {x : Frame Y.Ψ r} (hx : x ∈ Y.dom) :
    0 < ∏ τ, ∏ i : Fin r, ‖dmin Y.Gm x τ i.succ / dmin Y.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  have hne : ∀ τ i, dmin Y.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))

theorem eLpNorm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hm : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ x, f x ≤ B) :
    eLpNorm f 2 μ ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
  have hint : Integrable (fun x => f x ^ 2) μ :=
    Integrable.of_bound (hm.pow 2) (B ^ 2) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (hf0 x) (hB x) 2)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity),
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hm, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_two, ← lintegral_rpow_eNorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 2)]
  refine lintegral_congr fun x => ?_
  rw [Real.eNorm_eq_ofReal (hf0 x), ENNReal.rpow_two, ← ENNReal.ofReal_pow (hf0 x)]

open scoped TensorProduct

open scoped TensorProduct

variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}

theorem finrank_le_of_sup (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r) (la : ∀ k, Wt (X k).Ψ r)
    {Kf : Subgroup (GA D V)} {th : ∀ k, (X k).Ψ → (GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} {N : ℕ} (hN : 0 < N) (hth : ∀ k τ, StandardLattice.IsInfEmb τ.1 (th k τ))
    (hd : DictIsUnif V dict Kf th hr) (hK : IsLevelK V N Kf)
    (hu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (S : Submodule ℂ (FDSec X))
    (hS : ∀ P ∈ S, P ∈ holSub X la ∧ (∀ k, ContinuousOn (P k) (X k).dom) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) ∧ (∀ k x, x ∉ (X k).dom → P k x = 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ P ∈ S, supE X la P ^ 2 ≤ ENNReal.ofReal C * petE V dict (muQ1 V) la P ^ 2) :
    FiniteDimensional ℂ S ∧ (Module.finrank ℂ S : ℝ) ≤ C := by

  have hpt : ∀ (P : FDSec X) (g : GA D V), ptN la P (dict g) = ‖P (dict g).1 (dict g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  have hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom := hd.2.2.2.1
  have hle : ∀ (P : FDSec X) (g : GA D V), ENNReal.ofReal ‖P (dict g).1 (dict g).2‖ ≤ supE X la P := fun P g => by
    rw [← hpt]
    exact le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) ⟨(dict g).1, ⟨_, hdom g⟩⟩
  have hmeas : ∀ P ∈ S, AEStronglyMeasurable (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) (muQ1 V) := by
    intro P hP
    obtain ⟨-, hc, hΓ, -⟩ := hS P hP
    have hmu : MuUnit V dict (fun _ => 1) := ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hu⟩
    have h := GlobalTheory.PeterssonCompare.measurable_onQ_adel V hN hth hd hK hmu continuous_const P hc hΓ
    have e : (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) = fun q => ‖onQ V (adel V dict (fun _ => 1) P) q‖ := by
      funext q
      simp [onQ, adel]
    rw [e]
    exact h.norm.aestronglyMeasurable
  have hpet : ∀ P ∈ S, petE V dict (muQ1 V) la P ^ 2 =
      ENNReal.ofReal (∫ q, ‖P (dict q.out).1 (dict q.out).2‖ ^ 2 ∂(muQ1 V)) := by
    intro P hP
    have hfin := supE_ne_top X la (hS P hP).1
    have e : petE V dict (muQ1 V) la P = eLpNorm (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) 2 (muQ1 V) := by
      rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top (hmeas P hP), ENNReal.toReal_ofNat]
      simp only [petE, hpt]
    rw [e]
    exact eLpNorm_sq_eq (fun _ => norm_nonneg _) (hmeas P hP) (B := (supE X la P).toReal) fun q =>
      (ENNReal.ofReal_le_iff_le_toReal hfin).1 (hle P _)
  refine GlobalTheory.Bergman.finite_and_finrank_le_of_pointwise (μ := muQ1 V)
    (fun q (P : S) => ‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖)
    (fun q => ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : Frame (X (dict q.out).1).Ψ r => ℂ) (dict q.out).2 ∘ₗ
      LinearMap.proj (R := ℂ) (φ := fun k => Frame (X k).Ψ r → ℂ) (dict q.out).1) ∘ₗ S.subtype, fun P => rfl⟩)
    (fun P => hmeas P P.2) ?_ hC ?_
  · intro P hP0
    have h0 : petE V dict (muQ1 V) la (P : FDSec X) = 0 := by
      have e : (fun q : AutQ V => ptN la (P : FDSec X) (dict q.out)) = fun _ => 0 := by
        funext q
        rw [hpt]
        exact hP0 q
      unfold petE
      rw [e]
      exact eLpNorm'_zero (by norm_num)
    have hs := hsup P P.2
    rw [h0] at hs
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, nonpos_iff_eq_zero,
      pow_eq_zero_iff] at hs
    obtain ⟨-, -, -, hoff⟩ := hS P P.2
    refine Subtype.ext (funext fun k => funext fun x => ?_)
    by_cases hx : x ∈ (X k).dom
    · have h1 : ENNReal.ofReal ((X k).pnorm (la k) ((P : FDSec X) k) x) ≤ supE X la P :=
        le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) ((P : FDSec X) p.1) p.2)) ⟨k, ⟨x, hx⟩⟩
      rw [hs, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
      have h2 : ‖(P : FDSec X) k x‖ * _ ≤ 0 := h1
      have h3 := pnorm_fac_pos (X k) (la k) hx
      have h4 : ‖(P : FDSec X) k x‖ ≤ 0 := nonpos_of_mul_nonpos_left h2 h3
      simpa using h4
    · simpa using hoff k x hx
  · intro P q
    have h1 := hle (P : FDSec X) q.out
    have h2 := hsup P P.2
    rw [hpet P P.2] at h2
    have h3 : ENNReal.ofReal (‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖ ^ 2) ≤
        ENNReal.ofReal (C * ∫ q, ‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖ ^ 2 ∂(muQ1 V)) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul hC]
      exact (pow_le_pow_left' h1 2).trans h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg fun _ => by positivity))).1 h3

open Module


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem finrank_cuspW_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cuspW Xo c U (wtZ a n)) ∧ (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) ≤ supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) := by
  intro hM hT D j H Dw l Xo c U dict hL a n hDom
  obtain ⟨σ, hσ⟩ : ∃ σ : c.F →+* ℂ, GoodEmb c σ := ⟨_, goodEmb_goodOf c c.F.val.toRingHom⟩
  obtain ⟨Kf, th, hr, hK, hth, hd, hu⟩ := hL.dictU σ hσ
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ, w = ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hw_def]
  have hw : 0 < w := by rw [hw_def]; positivity
  have hspread : ∀ k, (∑ τ, ((U σ).X k).spread (laU (U σ) a n k) τ) ≤ w := fun k =>
    (_root_.GlobalTheory.LamSpread.sum_spread_laU_le D j H Dw l Xo c U dict hL σ hσ a n k).trans (by rw [hw_def]; linarith)
  have hχ := hL.chiTriv σ hσ a n hDom
  have hsup := _root_.GlobalTheory.supPet_principal hM hT D j H Dw l Xo c U dict hL σ hσ (laU (U σ) a n) w hw hspread hχ
  obtain ⟨Cw, hCw⟩ : ∃ Cw, Cw = cuspW Xo c U (wtZ a n) := ⟨_, rfl⟩
  rw [← hCw]
  have hsecOf : ∀ f ∈ Cw, f ∈ sec Xo c a n := fun f hf => by
    rw [hCw, cuspW_wtZ] at hf
    exact cusp_le_sec Xo c U a n hf

  have hgen : ∀ f ∈ Cw, rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) ∧
      (∀ k, ContinuousOn (rdU (U σ) f k) ((U σ).X k).dom) ∧
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, rdU (U σ) f k (lact γ x) = rdU (U σ) f k x) ∧
      (∀ k x, x ∉ ((U σ).X k).dom → rdU (U σ) f k x = 0) := by
    intro f hf
    have hs := hU.2.2.2.2.1 a n hDom f (hsecOf f hf)
    refine ⟨?_, fun k => (hs k).1.continuousOn, fun k γ hγ x hx => ?_, fun k x hx => ?_⟩
    · rw [hCw] at hf
      have := (mem_cuspW.1 hf).2 σ hσ
      rwa [modelWt_wtZ] at this
    · rw [(hs k).2.2 γ hγ x hx, hχ k γ hγ, one_mul]
    · classical
      show (if h : x ∈ ((U σ).X k).dom then _ else 0) = 0
      rw [dite_eq_right hx]
  obtain ⟨S, hS_def⟩ : ∃ S : Submodule ℂ (FDSec (U σ).X), S = Submodule.span ℂ (rdU (U σ) '' (Cw : Set (Rul Xo c))) :=
    ⟨_, rfl⟩
  have hS : ∀ P ∈ S, P ∈ holSub (U σ).X (laU (U σ) a n) ∧ (∀ k, ContinuousOn (P k) ((U σ).X k).dom) ∧
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, P k (lact γ x) = P k x) ∧
      (∀ k x, x ∉ ((U σ).X k).dom → P k x = 0) := by
    intro P hP
    rw [hS_def] at hP
    induction hP using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨f, hf, rfl⟩ := hP
      exact hgen f hf
    | zero => exact ⟨Submodule.zero_mem _, fun k => continuousOn_const, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
    | add P Q _ _ hP hQ =>
      refine ⟨Submodule.add_mem _ hP.1 hQ.1, fun k => (hP.2.1 k).add (hQ.2.1 k), fun k γ hγ x hx => ?_,
        fun k x hx => ?_⟩
      · simp only [Pi.add_apply]
        rw [hP.2.2.1 k γ hγ x hx, hQ.2.2.1 k γ hγ x hx]
      · simp only [Pi.add_apply]
        rw [hP.2.2.2 k x hx, hQ.2.2.2 k x hx, add_zero]
    | smul z P _ hP =>
      refine ⟨Submodule.smul_mem _ z hP.1, fun k => (hP.2.1 k).const_smul z, fun k γ hγ x hx => ?_,
        fun k x hx => ?_⟩
      · simp only [Pi.smul_apply]
        rw [hP.2.2.1 k γ hγ x hx]
      · simp only [Pi.smul_apply]
        rw [hP.2.2.2 k x hx, smul_zero]
  obtain ⟨hSfin, hSle⟩ := finrank_le_of_sup (D.sp.W j) (dict σ) (laU (U σ) a n) (Nat.pos_of_ne_zero (by
      have := l.three_le; omega)) hth hd hK hu S hS (supConst_nonneg _ _ _ _ _) fun P hP => hsup P (hS P hP).1

  have hind : ∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ Cw) → LinearIndependent c.F b →
      LinearIndependent ℂ (fun i => rdU (U σ) (b i)) := fun m b hb hli =>
    (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ H Dw l Xo c σ _
      (Formalism.L2.PjFree.Unf.ofPj (U σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) a n).1 m b (fun i => hsecOf _ (hb i)) hli
  have hcard : ∀ s : Finset Cw, LinearIndependent c.F (fun i : s => (i : Cw)) → s.card ≤ finrank ℂ S := by
    intro s hs
    let e : Fin s.card ≃ s := s.equivFin.symm
    let b : Fin s.card → Rul Xo c := fun i => ((e i : Cw) : Rul Xo c)
    have hb : LinearIndependent c.F b :=
      ((hs.comp e e.injective).map' Cw.subtype (Submodule.ker_subtype _))
    have hrd := hind s.card b (fun i => (e i : Cw).2) hb
    let v : Fin s.card → S := fun i => ⟨rdU (U σ) (b i), hS_def ▸ Submodule.subset_span ⟨b i, (e i : Cw).2, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp S.subtype hrd
    simpa using hv.fintype_card_le_finrank
  have : Module.Free c.F Cw := Module.Free.of_divisionRing c.F Cw
  have hrank : Module.rank c.F Cw ≤ ((finrank ℂ S : ℕ) : Cardinal) := rank_le hcard
  have hfin : FiniteDimensional c.F Cw :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  have h2 : finrank c.F Cw ≤ finrank ℂ S := finrank_le_of_rank_le hrank
  refine ⟨hfin, le_trans ?_ hSle⟩
  exact Nat.cast_le.2 h2

end GlobalTheory.LevGeo.RankBd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeData
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.SumCount.DataCount

section General

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [FiniteDimensional K V]

theorem finrank_le_dim (M : Submodule (𝓞 K) V) : Module.finrank (𝓞 K) M ≤ Module.finrank K V := by
  have h1 : Module.rank (𝓞 K) M ≤ Module.rank (𝓞 K) V := Submodule.rank_le M
  have h2 : Module.rank (𝓞 K) V = Module.rank K V := (IsFractionRing.rank_right_eq (𝓞 K) K V).symm
  rw [h2, ← Module.finrank_eq_rank K V] at h1
  exact Module.finrank_le_of_rank_le h1

theorem card_quot_le_of_fg (M : Submodule (𝓞 K) V) [Module.Finite (𝓞 K) M] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Finite (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ∧
      Nat.card (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ≤ Ideal.absNorm I ^ Module.finrank K V := by
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Module.Flat (𝓞 K) M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have h1 : (a : K) • (x : V) = 0 := by
      have h0 : a • (x : V) = 0 := congrArg Subtype.val hx
      rwa [← algebraMap_smul K a] at h0
    have h2 : (a : K) ≠ 0 := by
      have := nonZeroDivisors.ne_zero ha
      exact_mod_cast this
    exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left h2)
  have e := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (N := M) I
  have hN : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hI)
  rw [hN] at e
  refine ⟨Nat.finite_of_card_ne_zero (by rw [e]; exact (pow_pos hpos _).ne'), ?_⟩
  rw [e]
  exact Nat.pow_le_pow_right hpos (finrank_le_dim M)

theorem card_quot_le (M : Submodule (𝓞 K) V) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Nat.card (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ≤ Ideal.absNorm I ^ Module.finrank K V := by
  by_cases hf : Finite (M ⧸ (I • ⊤ : Submodule (𝓞 K) M))
  swap
  · haveI := not_finite_iff_infinite.1 hf
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _
  choose s hs using Submodule.Quotient.mk_surjective (I • ⊤ : Submodule (𝓞 K) M)
  let M' : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range fun q => (s q : V))
  have hle : M' ≤ M := Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact (s q).2)
  haveI : Module.Finite (𝓞 K) M' := Module.Finite.span_of_finite _ (Set.finite_range _)
  obtain ⟨hfin, hc⟩ := card_quot_le_of_fg M' hI
  let φ : (M' ⧸ (I • ⊤ : Submodule (𝓞 K) M')) →ₗ[𝓞 K] (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top)
  have hφ : Function.Surjective φ := fun q =>
    ⟨Submodule.Quotient.mk ⟨s q, Submodule.subset_span ⟨q, rfl⟩⟩, hs q⟩
  exact (Nat.card_le_card_of_surjective φ hφ).trans hc

end General

theorem absNorm_le_sq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm w.asIdeal ≤ Ideal.absNorm (w.under (𝓞 F)).asIdeal ^ 2 := by
  have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← h2]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  have h1 := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) (w.under (𝓞 F)).asIdeal
  rw [hr] at h1
  rw [← h1]
  refine Nat.le_of_dvd ?_ (Ideal.absNorm_dvd_absNorm_of_le Ideal.map_comap_le)
  rw [h1]
  exact pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (w.under (𝓞 F)).ne_bot)) _

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.SumSize GlobalTheory.RowTest

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem sig_nonneg : 0 ≤ sig G :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem absNorm_modul_le : (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  unfold sig
  rw [Finset.mul_sum, Real.exp_sum]
  show ((Ideal.absNorm (∏ v ∈ G.pl.S0, (G.pl.w v).asIdeal ^ G.pl.depth sc v) : ℕ) : ℝ) ≤ _
  rw [map_prod, Nat.cast_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun v hv => ?_
  have h1 := absNorm_le_sq D.sp.cm.deg2 (G.pl.w v)
  rw [G.pl.under_w hv] at h1
  have hpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  have e : Real.exp (2 * ((G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ 2) ^ G.pl.depth sc v := by
    rw [← pow_mul, ← mul_assoc, ← Nat.cast_ofNat, ← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hpos]
  rw [e, map_pow, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h1) _

theorem rank_row_le {i : ℕ} (hi : i ≤ D.R.m) : (G.V (.grid i 0)).rank ≤ bigN D := by
  have hr : (G.V (.grid i 0)).rank = rankV D i 0 := by
    cases i with
    | zero =>
      refine (D.sp.Y_rank _ (min_le_right _ _)).trans ?_
      rw [min_eq_left (Nat.zero_le _)]
      simp [rankV, Ranks.rankY]
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).rank
  have h1 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have hk : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr]
  simp only [rankV, bigN]
  have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
  rw [e]
  omega

theorem card_cosAt_le {i : ℕ} (hi : i < D.R.m) :
    (Nat.card (G.CosAt i) : ℝ) ≤ Real.exp ((bigN D : ℝ) ^ 2 * (2 * sig G)) := by
  have h1 := card_quot_le (homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) (G.pl.modul_ne_bot sc)
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin, Fintype.card_fin] at h1
  have hpos : 0 < Ideal.absNorm G.modul := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (G.pl.modul_ne_bot sc))
  have h2 : (G.V (.grid i 0)).rank * (G.V (.grid (i + 1) 0)).rank ≤ bigN D ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (rank_row_le G hi.le) (rank_row_le G hi)
  have h3 : Nat.card (G.CosAt i) ≤ Ideal.absNorm G.modul ^ (bigN D ^ 2) := h1.trans (Nat.pow_le_pow_right hpos h2)
  calc (Nat.card (G.CosAt i) : ℝ) ≤ (Ideal.absNorm G.modul : ℝ) ^ (bigN D ^ 2) := by exact_mod_cast h3
    _ ≤ Real.exp (2 * sig G) ^ (bigN D ^ 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) (absNorm_modul_le G) _
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; rfl

theorem card_datum_le : (Nat.card G.Datum : ℝ) ≤ Real.exp (D.R.m * ((bigN D : ℝ) ^ 2 * (2 * sig G))) := by
  rw [Nat.card_pi, Nat.cast_prod, Real.exp_nat_mul]
  refine (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun i _ => card_cosAt_le G i.2).trans (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_datum_le_aOne {C b : ℝ} (hC : 2 ≤ C) (hb : 1 ≤ b) : (Nat.card G.Datum : ℝ) ≤ Real.exp (D.R.m * aOne G C b) := by
  refine (card_datum_le G).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)))
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hl := Real.log_nonneg hb
  have hs : 0 ≤ (bigN D : ℝ) ^ 2 * sig G := mul_nonneg (by positivity) (sig_nonneg G)
  have h1 : 0 ≤ C * D.R.f * bigN D * b * Real.log b := by
    have : 0 ≤ C := by linarith
    have : 0 ≤ b := by linarith
    positivity
  have h2 : 2 ≤ C * D.R.m := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 hs
  unfold aOne
  nlinarith

theorem dataK : GlobalTheory.SumCount.DataK := by
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ _ => ?_⟩⟩⟩
  have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  exact card_datum_le_aOne ch.G hC (Real.one_le_exp (by linarith))

end GlobalTheory.SumCount.DataCount

end
end

