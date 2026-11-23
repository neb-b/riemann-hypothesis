module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharZeroEigenformSurvivingCompositionFacto
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpanned
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option synthInstance.maxHeartbeats 100000 in
theorem cuspOn_fd_and_span_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → FiniteDimensional c.F (cuspOn U Z (wtZ a n)) ∧ ∀ P ∈ holSub (U σ).X (modelWt (U σ) (wtZ a n)), (∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z → P k y = 0) → P ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x h Z σ hσ a n hD hpos hn
  refine ⟨?_, fun P hP hoffZ => ?_⟩
  · haveI := GlobalTheory.cuspForms_finiteDimensional_of_goodEmb E H Dw l Xo c r U σ hσ (h.unf σ hσ) a n hD
    have hle : cuspOn U Z (wtZ a n) ≤ cusp Xo c U a n := by
      rw [← cuspW_wtZ]; exact cuspOn_le U Z (wtZ a n)
    exact Submodule.finiteDimensional_of_le hle
  · have hpts : HasPts U Z := GlobalTheory.FlatLine.hasPts U h.pos h.good h.unf Z
    have e : goodOf c σ = σ := if_pos hσ
    have htest := (hpts.1 σ).2
    rw [e] at htest
    have hoff : P ∈ offZero (U σ).X := fun k y hy => hoffZ k y fun hz => hy hz.1
    have hP0 : P ∈ holSub0 (U σ).X (laU (U σ) a n) := ⟨by rwa [← modelWt_wtZ], hoff⟩
    have hsp := h.onto σ hσ a n hD hpos hn hP0
    have hfix : rdU (U σ) (idem Z) * P = P := by
      funext k y
      show rdU (U σ) (idem Z) k y * P k y = P k y
      by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨hd, hl⟩ := hz
        have h1 : rdU (U σ) (idem Z) k y = 1 := by
          simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_pos]
          rw [evR_idem hl (htest _ ⟨hd, hl⟩ hd)]
          rfl
        rw [h1, one_mul]
      · rw [hoffZ k y hz, mul_zero]
    let g : FDSec (U σ).X →ₗ[ℂ] FDSec (U σ).X := LinearMap.mulLeft ℂ (rdU (U σ) (idem Z))
    have hmap := Submodule.mem_map_of_mem (f := g) hsp
    rw [Submodule.map_span] at hmap
    have hg : g P = P := hfix
    rw [hg] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨idem Z * f, ⟨?_, ?_⟩, ?_⟩
    · rw [← cuspW_wtZ] at hf
      exact GlobalTheory.CompRestr.idem_mul_mem_cuspW h.unf Z hf
    · rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
    · show rdU (U σ) (idem Z * f) = rdU (U σ) (idem Z) * rdU (U σ) f
      exact AllWt.rdU_mul (U σ) _ _

end GlobalTheory.FlatCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCuspFormsFiniteRegularRepresentation
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn.Definite

theorem free_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E → ∀ (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → LevelHyp M → ∀ (u : U) (c : C), u • c = c → u = 1 := by
  intro E _ _ _ hbal hsmall r U C _ _ M hdef hlev u c huc
  obtain ⟨g, hsplit, hg, hunip⟩ := hlev
  obtain ⟨Γo, hst, hun, hmem⟩ := GlobalTheory.T.exists_upperArithmeticGroup_unipotentUnitary E r U C M c g hunip
  obtain ⟨x, hx, hnc, -⟩ := hbal r (M.comp c)
  have h1 : M.tr u c = 1 :=
    hsmall r (M.comp c) g (_root_.GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely E g hsplit) hg Γo hst hun x hx hnc (M.tr u c) (hmem u huc)
      (fun τ => _root_.GlobalTheory.DefiniteOpNorm.opNormLe_definite E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) x hx _
        (hst _ (hmem u huc)).1 τ)
  exact M.tr_faithful u c huc (by rw [h1]; exact (M.comp c).Γ.one_mem)

theorem share_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → Module.Finite ℂ (M.cusp ka) ∧ ∀ H : Subgroup U, LevelHyp (sub M H) → (∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H = finrank ℂ (M.cusp ka)) ∧ ∀ lam : H →* ℂˣ, Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank ℂ (M.cusp ka) := by
  intro E _ _ _ r U C _ _ _ _ M hdef ka ρ hρ
  classical
  haveI : Fintype C := Fintype.ofFinite C
  have hfin : Module.Finite ℂ (M.cusp ka) :=
    _root_.GlobalTheory.cusp_finite_of_comp E r U C M ka (fun c =>
      _root_.GlobalTheory.DefiniteFin.finiteDimensional_cusp_definite E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) _)
  refine ⟨hfin, fun H hH => ?_⟩
  haveI : FiniteDimensional ℂ (M.cusp ka) := hfin
  have hfree : ∀ (h : H) (c : C), h • c = c → h = 1 :=
    free_of_definite E (_root_.GlobalTheory.BalancedPointPf.balancedPoint E) (_root_.GlobalTheory.SmallElement.smallElement E) r H C (sub M H) hdef hH
  obtain ⟨A, hA, hAρ⟩ := _root_.GlobalTheory.ShareOn.cusp_decomp E r U C M ka ρ hρ
  have hAρH : ∀ (h : H) (x : C), ∀ v ∈ A x, ρ h v ∈ A (h • x) := fun h x v hv => hAρ h x v hv
  exact ⟨_root_.GlobalTheory.BadCount.embReg_of_free_permuted_summands ℂ U (M.cusp ka) C ρ H hfree A hA hAρH,
    fun lam => _root_.GlobalTheory.BadCount.card_mul_finrank_eig_of_free ℂ U (M.cusp ka) C ρ H hfree A hA hAρH H le_rfl lam⟩

end GlobalTheory.ShareOn.Definite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt
open scoped ENNReal Classical

theorem eLpNorm_sq_le_add {α : Type} [MeasurableSpace α] {μ : Measure α} (hμ : μ Set.univ ≤ 1) {f g : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ a, f a ^ 2 ≤ g a ^ 2 + C) : eLpNorm' f 2 μ ^ 2 ≤ eLpNorm' g 2 μ ^ 2 + ENNReal.ofReal C := by
  have key : ∀ u : α → ℝ, eLpNorm' u 2 μ ^ 2 = ∫⁻ a, ENNReal.ofReal (u a ^ 2) ∂μ := fun u => by
    have e := (lintegral_rpow_eNorm_eq_rpow_eLpNorm' (f := u) (μ := μ) (q := 2) (by norm_num)).symm
    simp only [ENNReal.rpow_ofNat] at e
    rw [e]
    refine lintegral_congr fun a => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [key, key]
  calc ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ ≤ ∫⁻ a, ENNReal.ofReal (g a ^ 2) + ENNReal.ofReal C ∂μ :=
        lintegral_mono fun a => by
          rw [← ENNReal.ofReal_add (sq_nonneg _) hC]
          exact ENNReal.ofReal_le_ofReal (h a)
    _ = ∫⁻ a, ENNReal.ofReal (g a ^ 2) ∂μ + ENNReal.ofReal C * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hμ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem denseRange_of_goodEmb {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) : DenseRange σ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h
  · exfalso
    have h1 : H.rt0 ∈ σ.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨_, hσ⟩
    rw [h] at h1
    obtain ⟨t, ht⟩ := h1
    have h2 := H.sqrt_neg_disc_sq
    rw [← ht] at h2
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h3 : t ^ 2 = -(H.d : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact h2
    nlinarith [sq_nonneg t]
  · rw [denseRange_iff_closure_range]
    exact congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h

section Model

variable {r : ℕ} {Cp : Type} [Fintype Cp] {X : Cp → FD.Data E r} {la : ∀ k, FD.Wt (X k).Ψ r}

theorem exists_ptN_le {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : FPt X, ptN la P ⟨p.1, p.2.1⟩ ≤ M :=
  ⟨(supE X la P).toReal, ENNReal.toReal_nonneg, fun p => (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top X la hP)).1
    (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p)⟩


omit [Fintype Cp] in
theorem ptN_add_le (P Q : FDSec X) (z : Σ k, FD.Frame (X k).Ψ r) : ptN la (P + Q) z ≤ ptN la P z + ptN la Q z :=
  pnorm_add_le _ _ _ _ _


omit [Fintype Cp] in
theorem ptN_smul (a : ℂ) (P : FDSec X) (z : Σ k, FD.Frame (X k).Ψ r) : ptN la (a • P) z = ‖a‖ * ptN la P z :=
  pnorm_smul _ _ _ _ _

theorem exists_ptN_sub_le {K W : Type} [Field K] [AddCommGroup W] [Module K W] {σ : K →+* ℂ} (hσ : DenseRange σ)
    (rd : W →ₛₗ[σ] FDSec X) (C : Submodule K W) (hC : ∀ f ∈ C, rd f ∈ holSub X la) {Q : FDSec X}
    (hQ : Q ∈ Submodule.span ℂ (rd '' C)) :
    ∀ ε : ℝ, 0 < ε → ∃ f ∈ C, ∀ p : FPt X, ptN la (Q - rd f) ⟨p.1, p.2.1⟩ ≤ ε := by
  have h0 : ∀ z, ptN la (0 : FDSec X) z = 0 := fun z => pnorm_zero _ _ _
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact fun ε hε => ⟨f, hf, fun p => by rw [sub_self, h0]; exact hε.le⟩
  | zero => exact fun ε hε => ⟨0, zero_mem _, fun p => by rw [map_zero, sub_self, h0]; exact hε.le⟩
  | add P Q _ _ hP hQ =>
    intro ε hε
    obtain ⟨f, hf, h₁⟩ := hP (ε / 2) (half_pos hε)
    obtain ⟨g, hg, h₂⟩ := hQ (ε / 2) (half_pos hε)
    refine ⟨f + g, add_mem hf hg, fun p => ?_⟩
    rw [map_add (f := _), show P + Q - (rd f + rd g) = (P - rd f) + (Q - rd g) by abel]
    exact (ptN_add_le _ _ _).trans (by linarith [h₁ p, h₂ p])
  | smul a P _ hP =>
    intro ε hε
    have ha : 0 < ‖a‖ + 1 := by positivity
    obtain ⟨f, hf, h₁⟩ := hP (ε / 2 / (‖a‖ + 1)) (by positivity)
    obtain ⟨M, hM, h₂⟩ := exists_ptN_le (hC f hf)
    obtain ⟨b, hb⟩ := hσ.exists_dist_lt a (show 0 < ε / 2 / (M + 1) by positivity)
    rw [dist_eq_norm, lt_div_iff₀ (by positivity)] at hb
    refine ⟨b • f, C.smul_mem b hf, fun p => ?_⟩
    rw [map_smulₛₗ, show a • P - σ b • rd f = a • (P - rd f) + (a - σ b) • rd f by
      rw [smul_sub, sub_smul]; abel]
    refine (ptN_add_le _ _ _).trans ?_
    rw [ptN_smul, ptN_smul]
    have e₁ := (le_div_iff₀ ha).1 (h₁ p)
    have e₂ := mul_le_mul_of_nonneg_left (h₂ p) (norm_nonneg (a - σ b))
    nlinarith [ptN_nonneg la (P - rd f) ⟨p.1, p.2.1⟩, norm_nonneg (a - σ b)]

variable {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (dict : Formalism.L2.Theta.GA D V → Σ k, FD.Frame (X k).Ψ r)
  (μ : Measure (AutQ V))

theorem ptN_sq_le_of_mem_span (hμ : μ Set.univ ≤ 1) (hd : ∀ g, (dict g).2 ∈ (X (dict g).1).dom)
    {K W : Type} [Field K] [AddCommGroup W] [Module K W] {σ : K →+* ℂ} (hσ : DenseRange σ)
    (rd : W →ₛₗ[σ] FDSec X) (C : Submodule K W) (hC : ∀ f ∈ C, rd f ∈ holSub X la) (z : FPt X) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ f ∈ C, ptN la (rd f) ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (petE V dict μ la (rd f)).toReal ^ 2) {Q : FDSec X}
    (hQ : Q ∈ Submodule.span ℂ (rd '' C)) :
    ptN la Q ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (petE V dict μ la Q).toReal ^ 2 := by
  have hQ' : Q ∈ holSub X la := (Submodule.span_le.2 (by rintro _ ⟨f, hf, rfl⟩; exact hC f hf)) hQ
  obtain ⟨M, hM, h₂⟩ := exists_ptN_le hQ'
  have hfin := petE_ne_top V dict μ hμ hd hQ'
  set A := (petE V dict μ la Q).toReal with hA
  have step : ∀ ε : ℝ, 0 < ε →
      ptN la Q ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2) := fun ε hε => by
    obtain ⟨f, hf, h₁⟩ := exists_ptN_sub_le hσ rd C hC hQ ε hε
    have up : ∀ p : FPt X, ptN la (rd f) ⟨p.1, p.2.1⟩ ≤ ptN la Q ⟨p.1, p.2.1⟩ + ε := fun p => by
      have e := ptN_add_le (la := la) Q ((-1 : ℂ) • (Q - rd f)) ⟨p.1, p.2.1⟩
      rw [ptN_smul, show Q + (-1 : ℂ) • (Q - rd f) = rd f by rw [neg_one_smul]; abel, norm_neg, norm_one,
        one_mul] at e
      linarith [h₁ p]
    have dn : ptN la Q ⟨z.1, z.2.1⟩ ≤ ptN la (rd f) ⟨z.1, z.2.1⟩ + ε := by
      have e := ptN_add_le (la := la) (rd f) (Q - rd f) ⟨z.1, z.2.1⟩
      rw [add_sub_cancel] at e
      linarith [h₁ z]
    have hC0 : 0 ≤ 2 * M * ε + ε ^ 2 := by positivity
    have e₁ : petE V dict μ la (rd f) ^ 2 ≤ petE V dict μ la Q ^ 2 + ENNReal.ofReal (2 * M * ε + ε ^ 2) :=
      eLpNorm_sq_le_add hμ hC0 fun q => by
        have a₁ : ptN la (rd f) (dict q.out) ≤ ptN la Q (dict q.out) + ε := up ⟨_, _, hd q.out⟩
        have a₂ : ptN la Q (dict q.out) ≤ M := h₂ ⟨_, _, hd q.out⟩
        have a₃ := pow_le_pow_left₀ (ptN_nonneg _ _ _) a₁ 2
        nlinarith
    have e₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top hfin, ENNReal.ofReal_ne_top⟩) e₁
    rw [ENNReal.toReal_add (ENNReal.pow_ne_top hfin) ENNReal.ofReal_ne_top, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hC0] at e₂
    have e₃ := (h f hf).trans (mul_le_mul_of_nonneg_left e₂ hB)
    have e₄ := pow_le_pow_left₀ (ptN_nonneg _ _ _) dn 2
    have e₅ : ptN la (rd f) ⟨z.1, z.2.1⟩ ≤ M + ε := by linarith [up z, h₂ z]
    nlinarith
  have lim : Filter.Tendsto (fun ε : ℝ => B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (B * A ^ 2)) := by
    refine Filter.Tendsto.mono_left (Continuous.tendsto' (by fun_prop) _ _ (by simp)) nhdsWithin_le_nhds
  exact ge_of_tendsto lim (eventually_nhdsWithin_of_forall step)

end Model

section Berg

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : Formalism.BasicNotions.D7}
  {V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D}
  {dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r} {Z : Comp Xo c}

theorem eq_zero_of_mem_span_cuspOn {G : WTZ E} {σ : c.F →+* ℂ} {Q : FDSec (U σ).X}
    (hQ : Q ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z G : Set (Rul Xo c))))
    {z : Σ k, FD.Frame ((U σ).X k).Ψ r} (hz : z ∉ framesOn (U σ) Z) : Q z.1 z.2 = 0 := by
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact rdU_eq_zero _ hf.2 hz
  | zero => rfl
  | add P Q _ _ hP hQ => rw [Pi.add_apply, Pi.add_apply, hP, hQ, add_zero]
  | smul a P _ hP => rw [Pi.smul_apply, Pi.smul_apply, hP, smul_zero]

theorem bergOn_le_bergCusp {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    (z : FPt (U (goodOf c σ)).X)
    (hz : (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) ∈ framesOn (U (goodOf c σ)) Z) :
    bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z ≤ bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ := by
  by_cases h : bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ = ⊤
  · exact h ▸ le_top
  have hB := (bergCusp_le_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal h).ge
  rw [← ENNReal.ofReal_toReal h]
  set B := (bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩).toReal
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  set μ := muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z
  have hμ : μ Set.univ ≤ 1 := muPart_univ_le _ _ _
  have hfin := fun P (hP : P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G)) =>
    petE_ne_top (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd hP
  refine (bergE_le_iff _ _ μ hfin z ENNReal.ofReal_ne_top).2 fun P hP => ?_
  obtain ⟨Q, hQ, hPQ⟩ := hspan P hP
  have key := ptN_sq_le_of_mem_span (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd
    (denseRange_of_goodEmb (goodEmb_goodOf c σ)) (rdU (U (goodOf c σ))) (cuspOn U Z G)
    (fun f hf => (mem_cuspW.1 hf.1).2 _ (goodEmb_goodOf c σ)) z hB0 (fun f hf => by
      have e := hB f hf
      have hl := lieFacZ_pos (Dw := Dw) x G
      simp only [homN, petOn, petAt, mul_pow] at e
      exact le_of_mul_le_mul_left (e.trans_eq (by ring)) (pow_pos hl 2)) hQ
  have hle : ∀ w, ptN (modelWt (U (goodOf c σ)) G) Q w ≤ ptN (modelWt (U (goodOf c σ)) G) P w := fun w => by
    by_cases hw : w ∈ framesOn (U (goodOf c σ)) Z
    · simp only [ptN, FD.Data.pnorm, hPQ w hw, le_refl]
    · refine le_trans (le_of_eq ?_) (ptN_nonneg _ P w)
      simp only [ptN, FD.Data.pnorm, eq_zero_of_mem_span_cuspOn hQ hw, norm_zero, zero_mul]
  have hpet : petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) Q ≤
      petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) P :=
    eLpNorm'_mono_ae (by norm_num) (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (ptN_nonneg _ _ _), Real.norm_of_nonneg (ptN_nonneg _ _ _)]
      exact hle _)
  have hz' : ptN (modelWt (U (goodOf c σ)) G) P ⟨z.1, z.2.1⟩ = ptN (modelWt (U (goodOf c σ)) G) Q ⟨z.1, z.2.1⟩ := by
    have := hPQ _ hz
    simp only [ptN, FD.Data.pnorm] at this ⊢
    rw [this]
  have e := key.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono (hfin P hP) hpet) 2) hB0)
  rw [hz', ← ENNReal.ofReal_toReal (hfin P hP), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _),
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hB0]
  exact ENNReal.ofReal_le_ofReal e

theorem bergCusp_eq_bergOn {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    (z : FPt (U (goodOf c σ)).X)
    (hz : (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) ∈ framesOn (U (goodOf c σ)) Z) :
    bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ = bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z :=
  le_antisymm (bergCusp_le_bergOn hd z) (bergOn_le_bergCusp hd hspan z hz)

end Berg

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharZeroEigenformSurvivingCompositionFactoStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charZero_eigenform_surviving_compositionFactor : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (ϖ : F.O), F.Ok → F.IsJ lam jK → Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)], F.IsHecke lam jK Gm → Embeds F.O N lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal], ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)) → ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  first | exact @GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving | exact GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving | (intros; apply GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientLatticeSpan
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.Exp


open GlobalTheory.TraceIncl in
theorem clSum_equiv_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (g : G) (f : (A.MtCSD i t).Forms) :
    clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g f) = actS R i g (clSum (presV R i t) (kern R i t) f) := by
  refine clSum_act (presV R i t) (kernelLaws hS.models hS.thP hS.typ) (R.B.L i t).act_tie (envV R i t).J_le (actS R i)
    (fun q y w => funext fun v => ?_) g f
  exact (_root_.GlobalTheory.TraceIncl.kern_laws R i t hS.models.inf hS.models.cV hS.thP.ωP hS.thP.pt_theta hS.thP.ioP hS.typ).2.2.2 _ q (hS.red i t q)
    (hl _) y w v


open GlobalTheory.TraceIncl in
theorem clSum_trU_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (f : (A.MtCSD i t).Forms)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    clSum (presV R i t) (kern R i t) (trU (A.leftGroupActionLift i t) U ψ f) v =
      levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
  unfold levelTrace gaL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [trU_apply, map_sum, Finset.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smulₛₗ, clSum_equiv_of_lift hS hl, LinearMap.smul_apply, invChar, apply_dite D.what₂.embLL, map_zero]
  rfl


open GlobalTheory.TraceIncl in
set_option maxHeartbeats 4000000 in
theorem exists_adForm_levelTrace {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : ∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (hχ : ∀ k, ∃ a : D.what₂.LL, D.what₂.embLL a = (((envV R i t).χ k : ℂˣ) : ℂ))
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {θ : (Fin (srcDim A i t U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : IsClassSum R i t U ψ 1 θ) {h : GA D (Vc D i)} (hh : h ∈ GfC (Vc D i)) {w : (R.cV i).W} (hw : InCoefLat R i h w) :
    ∃ y ∈ LinearMap.range θ, ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
      adForm R i y (fun ρ => v ρ) = levelTrace R i U ψ (singleSeries R i (R.ωP i t) (R.vP i t) h w v) := by
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  obtain ⟨e, r, h1, hL⟩ := exists_latSys (i := i) (t := t) hS.lev hT
  obtain ⟨f, hf, j, hj⟩ := hL.exists_trace (GlobalTheory.LevelCharOrder.levEnv_chi_isOfFinOrder _ _ _)
    (kernelLaws hS.models hS.thP hS.typ) (h := fin _ h) (x := e.symm P)
    (Submodule.mem_comap.2 ((e.apply_symm_apply P).symm ▸ hP : e (e.symm P) ∈ nabAtr (labLL D) (lamV D i) _))
  obtain ⟨y, -, ey⟩ := exists_src_trU i t U ψ hS.act hf
  have hcw : (presV R i t).coef (e.symm P) = c0L i P := (h1 _).trans (congrArg (c0L i) (e.apply_symm_apply P))
  obtain ⟨a, ha⟩ := hχ j
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  refine ⟨θ (a⁻¹ • y), LinearMap.mem_range_self _ _, fun v => ?_⟩
  have e1 : singleSeries R i (R.ωP i t) (R.vP i t) h (c0L i P) v =
      ((((envV R i t).χ j)⁻¹ : ℂˣ) : ℂ) • clSum (presV R i t) (kern R i t) f v :=
    (hS.kern_fin hh _ v).symm.trans ((congrArg (fun w' => kern R i t (fin _ h) w' v) hcw.symm).trans (congrFun hj v))
  have e2 : adForm R i (θ y) (fun ρ => v ρ) = (1 : ℂ) • levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
    rw [hS.adForm_theta hθ y v, ey, clSum_trU_of_lift hS hl]
  have e3 : adForm R i (θ (a⁻¹ • y)) (fun ρ => v ρ) = D.what₂.embLL a⁻¹ • adForm R i (θ y) (fun ρ => v ρ) := by
    rw [map_smul, adForm_smul]
    rfl
  rw [e3, e2, one_smul, e1, (levelTrace R i U ψ).map_smul, map_inv₀, ha, Units.val_inv_eq_inv_val]

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrbitFamilyAdaptedLatticeSplitSupportStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (U : Subgroup G) (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), IsOrbitFamily (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (badN D) (wtA (κ i)) (T.dδ ((i : ℕ) + 1) (κ i).n) (fun u : U => ℓ u) (fun u => ((f u).1 : T.R ((i : ℕ) + 1))) → ∃ (a : 𝓞 T.Q.c.F) (s : ℕ) (f' : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ (∀ u, (s : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (a : T.Q.c.F) • ((f' u).1 : T.R ((i : ℕ) + 1))) ∧ SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧ (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧ Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ AdmX (l := T.Q.l) true x₀ ∧ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) ∧ ∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f' u).1 : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.OrbitAdapt.exists_adapted | exact GlobalTheory.OrbitAdapt.exists_adapted | (intros; apply GlobalTheory.OrbitAdapt.exists_adapted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMemberLieActionFockPlusTraceStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMember_lieAction_fock_plus_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → (∀ x : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = d.e x) → IsUSplitting (adeleClass F) ψ d' (actB (cA σ)) om → ∃ c, ActsByD τ A om Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c := by
  exact @GlobalTheory.HoweD.LieFirstD.lieFirstD
end

