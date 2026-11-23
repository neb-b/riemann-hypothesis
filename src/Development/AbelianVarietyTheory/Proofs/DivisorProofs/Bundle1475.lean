module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLIteratedDecayModerateGrowth
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem iterated_decay : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (m : ℕ) (ψ : Sm E a), IsCuspForm ψ → (∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod ψ).1 (infGL E a y)‖ ≤ C * height y ^ N) → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N := by
  intro hfin E _ _ _ a N t ht i j hij m
  induction m with
  | zero =>
    intro ψ _ htame Ω hΩ
    obtain ⟨C0, hC0⟩ := htame []
    obtain ⟨B, hB1, hB⟩ := _root_.GlobalTheory.AutGrowth.height_mul_le_of_isCompact E a Ω hΩ
    refine ⟨|C0| * B ^ N, by positivity, ?_⟩
    intro r d _ _ _ c hc
    have h1 := hC0 (d * c)
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at h1
    have hh0 : 0 ≤ height (d * c) := le_trans zero_le_one (one_le_height _)
    have hh : height (d * c) ^ N ≤ (B * height d) ^ N := pow_le_pow_left₀ hh0 (hB c hc d) N
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C0 * height (d * c) ^ N := h1
      _ ≤ |C0| * height (d * c) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C0) (pow_nonneg hh0 N)
      _ ≤ |C0| * (B * height d) ^ N := mul_le_mul_of_nonneg_left hh (abs_nonneg C0)
      _ = |C0| * B ^ N * (r j / r i) ^ 0 * height d ^ N := by rw [mul_pow]; ring
  | succ m ih =>
    intro ψ hψ htame Ω hΩ
    obtain ⟨Ω', B, C, hΩ', hC, hstep⟩ := _root_.GlobalTheory.cuspForm_decay_step E a ψ hψ t ht i j hij Ω hΩ
    have hY : ∀ Y ∈ B, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) →
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
        ∀ c ∈ Ω', ‖(lie E a Y ψ).1 (infGL E a (d * c))‖ ≤ C' * (r j / r i) ^ m * height d ^ N := by
      intro Y _
      have hcusp : IsCuspForm (lie E a Y ψ) := GlobalTheory.T.isCuspForm_operator_act hfin E a (.lie Y) ψ hψ
      refine ih (lie E a Y ψ) hcusp ?_ Ω' hΩ'
      intro l
      obtain ⟨C1, hC1⟩ := htame (l ++ [Y])
      refine ⟨C1, fun y => ?_⟩
      have e : (l.map (lie E a)).prod (lie E a Y ψ) = ((l ++ [Y]).map (lie E a)).prod ψ := by
        simp [List.map_append, List.prod_append, Module.End.mul_apply]
      rw [e]
      exact hC1 y
    choose! CY hCY0 hCY using hY
    refine ⟨C * ∑ Y ∈ B, CY Y, mul_nonneg hC (Finset.sum_nonneg hCY0), ?_⟩
    intro r d hr hrt hd c hc
    have hq : 0 ≤ (r j / r i) ^ m * height d ^ N :=
      mul_nonneg (pow_nonneg (div_nonneg (hr j).le (hr i).le) m)
        (pow_nonneg (le_trans zero_le_one (one_le_height d)) N)
    have hM0 : 0 ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
      mul_nonneg (Finset.sum_nonneg hCY0) hq
    have h := hstep r d hr hrt hd _ hM0 (fun Y hYB c' hc' => by
      have h2 : lieD Y ψ.1 = (lie E a Y ψ).1 := rfl
      rw [h2]
      calc ‖(lie E a Y ψ).1 (infGL E a (d * c'))‖ ≤ CY Y * (r j / r i) ^ m * height d ^ N := hCY Y hYB r d hr hrt hd c' hc'
        _ = CY Y * ((r j / r i) ^ m * height d ^ N) := by ring
        _ ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun Y hY => hCY0 Y hY) hYB) hq) c hc
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * ((∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N)) := h
      _ = (C * ∑ Y ∈ B, CY Y) * (r j / r i) ^ (m + 1) * height d ^ N := by ring

end GlobalTheory.CuspRapid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupNormLePeterssonIntegralComponent
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SupLoc

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem fdeg_pos' : 0 < fdeg E := by
  unfold fdeg
  have h2 := IsTotallyComplex.finrank (K := E)
  have hp : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

theorem pnorm_nonneg' {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    0 ≤ X.pnorm la P y := by
  unfold Data.pnorm; positivity

theorem pnorm_lact' {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
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

theorem pnorm_piecewise {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r}
    (hy : y ∈ X.dom) : X.pnorm la (X.dom.piecewise P 0) y = X.pnorm la P y := by
  classical
  unfold Data.pnorm
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

theorem pnorm_piecewise_le {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    X.pnorm la (X.dom.piecewise P 0) y ^ 2 ≤ X.pnorm la P y ^ 2 := by
  classical
  by_cases hy : y ∈ X.dom
  · rw [pnorm_piecewise X la P hy]
  · have : X.pnorm la (X.dom.piecewise P 0) y = 0 := by
      unfold Data.pnorm
      rw [Set.piecewise_eq_of_notMem _ _ _ hy]; simp
    rw [this, sq, zero_mul]; positivity

end GlobalTheory.SupLoc


open GlobalTheory.SupLoc in
theorem GlobalTheory.supLoc_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (M w : ℝ) (x0 : Frame X.Ψ r) (FF : Set (V (nd X.toData))), 0 < r → P ∈ X.SS la → 0 < M → (∑ τ, X.spread la τ) ≤ w → 0 < w → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧ ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) → IsOrth X.toData x0 → IsFundSet X.toData x0 FF → ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epStar M (fdeg E) w X.k0)) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0) := by
  classical
  intro E _ _ _ r X la P M w x0 FF hr hP hM hw hw0 hΓL hTr hx0 hFF y hy
  have hsec : X.IsSec la P := hP.1.1
  obtain ⟨C, hC⟩ := hP.1.2
  by_cases hy0 : X.pnorm la P y = 0
  · rw [hy0]; simp
  have hypos : 0 < X.pnorm la P y := lt_of_le_of_ne (pnorm_nonneg' _ _ _ _) (Ne.symm hy0)

  set S := sSup (X.pnorm la P '' X.dom) with hSdef
  have hbdd : BddAbove (X.pnorm la P '' X.dom) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hC x hx
  have hle : ∀ x ∈ X.dom, X.pnorm la P x ≤ S := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hSpos : 0 < S := lt_of_lt_of_le hypos (hle y hy)
  obtain ⟨_, ⟨z0, hz0, rfl⟩, hz0S⟩ := exists_lt_of_lt_csSup ((show X.dom.Nonempty from ⟨y, hy⟩).image (X.pnorm la P)) (half_lt_self hSpos)
  have hhalf : ∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0 := fun x hx => by
    linarith [hle x hx]
  have hz0pos : 0 < X.pnorm la P z0 := by linarith
  have hmax := maxBound_holds (E := E) r X la P M w hP hM hw hw0 hTr z0 hz0 hhalf hz0pos

  obtain ⟨b, hb, hxo, hmaj⟩ := ModeHalfC.orthonormalize X.toData hz0
  set x := rmul z0 b with hxdef
  have hpx : X.pnorm la P x = X.pnorm la P z0 := FrameDegreeData.pnorm_rmul X.toData la P hsec.2.1 z0 hz0 b hb
  set ε := epStar M (fdeg E) w X.k0 with hεdef
  have hf1 : (1 : ℝ) ≤ fdeg E := by exact_mod_cast (fdeg_pos' (E := E))
  have hε : 0 < ε := by
    rw [hεdef]; unfold epStar
    have hk := X.minWeight_pos
    have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    refine lt_min one_pos (div_pos Real.pi_pos ?_)
    have : 0 < (fdeg E : ℝ) * w + 2 := by positivity
    positivity
  have hshort : ∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    obtain ⟨τ, hτ⟩ := hmax v hv hv0
    rw [← hmaj τ] at hτ
    exact hτ.trans (Finset.single_le_sum (f := fun τ => X.maj x τ (Data.emb τ.1 v))
      (fun τ _ => ModeHalfC.maj_nonneg_orth X.toData hxo τ _) (Finset.mem_univ τ))
  set ρ := chartRad E r w with hρdef
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hρ : (r : ℝ) ^ 2 * ρ ≤ 1 / 100 := by
    rw [hρdef]; unfold chartRad
    have h1 : 0 < (r : ℝ) := by linarith
    have h2 : 0 < w + fdeg E := by linarith
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hr1 (show (1:ℝ) ≤ w + fdeg E by linarith) zero_le_one h1.le]
  have hmult := _root_.GlobalTheory.chart_mult_le E r X x ε ρ hr hxo hε hρ hΓL hshort
  have hsub := _root_.GlobalTheory.SubmeanChart.submean_chart E r X.toData la w x P hr hxo hw hsec.1

  set P' : Frame X.Ψ r → ℂ := X.dom.piecewise P 0 with hP'def
  set Φ : Frame X.Ψ r → ℝ≥0∞ := fun u => ENNReal.ofReal (X.pnorm la P' u ^ 2) with hΦdef
  have hdomO := FourierCoefficientDomain.isOpen_dom X.toData
  have hΦm : Measurable Φ := by
    have hm := GlobalTheory.PeterssonCompare.measurable_pnorm X.toData la (P := P')
      (hsec.1.continuousOn.congr fun u hu => Set.piecewise_eq_of_mem _ _ _ hu)
      (fun u hu => by rw [hP'def, Set.piecewise_eq_of_notMem _ _ _ hu]; rfl)
    exact ENNReal.measurable_ofReal.comp (hm.pow_const 2)
  have hΦΓ : ∀ γ ∈ X.Γ, ∀ u ∈ X.dom, Φ (lact γ u) = Φ u := by
    intro γ hγ u hu
    have hu' := GlobalTheory.MajInv.lact_mem_dom X.toData (X.Γ_stab γ hγ) hu
    show ENNReal.ofReal (X.pnorm la P' (lact γ u) ^ 2) = ENNReal.ofReal (X.pnorm la P' u ^ 2)
    rw [hP'def, pnorm_piecewise X.toData la P hu, pnorm_piecewise X.toData la P hu',
      pnorm_lact' X.toData hsec hγ hu]
  have hΦB : ∀ c ∈ Bor X.Ψ r, ∀ u ∈ X.dom, Φ (rmul u c) = Φ u := by
    intro c hc u hu
    have hu' := OrthogonalFrameDomain.rmul_mem_dom X.toData hu hc
    show ENNReal.ofReal (X.pnorm la P' (rmul u c) ^ 2) = ENNReal.ofReal (X.pnorm la P' u ^ 2)
    rw [hP'def, pnorm_piecewise X.toData la P hu, pnorm_piecewise X.toData la P hu',
      FrameDegreeData.pnorm_rmul X.toData la P hsec.2.1 u hu c hc]
  set A := Metric.ball (0 : V (nd X.toData)) ρ ∩ OmF X.toData x with hAdef
  have hOm := ExF.isOpen_OmF X.toData x
  have hA : MeasurableSet A := measurableSet_ball.inter hOm.measurableSet
  have hAsub : A ⊆ OmF X.toData x := Set.inter_subset_right
  have hmA : (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ c ∈ Bor X.Ψ r,
      lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') c}.encard : ℝ≥0∞)) ≤
      ENNReal.ofReal (multBd E r ε) := by
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) hmult
    rintro γ ⟨hγ, z, hz, z', hz', c, hc, he⟩
    exact ⟨hγ, z, z', (mem_ball_zero_iff.1 hz.1).le, (mem_ball_zero_iff.1 hz'.1).le, c, hc, he⟩
  have hunf := _root_.GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet E r X.toData x0 x FF A _ Φ hx0 hxo hFF hA hAsub hΦm hΦΓ hΦB hmA

  have hae : ∀ᵐ z ∂(muF X.toData x), z ∈ OmF X.toData x := by
    have h1 : ∀ᵐ z ∂(volume.restrict (OmF X.toData x)), z ∈ OmF X.toData x :=
      ae_restrict_mem hOm.measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le h1
  have hball : ∫⁻ z in Metric.ball (0 : V (nd X.toData)) ρ,
      ENNReal.ofReal (X.pnorm la P (cpt X.toData x z) ^ 2) ∂(muF X.toData x) =
      ∫⁻ z in A, Φ (cpt X.toData x z) ∂(muF X.toData x) := by
    have hset : A =ᵐ[muF X.toData x] Metric.ball (0 : V (nd X.toData)) ρ := by
      filter_upwards [hae] with z hz
      simp [hAdef, hz]
    rw [Measure.restrict_congr_set hset]
    refine setLIntegral_congr_fun_ae measurableSet_ball ?_
    filter_upwards [hae] with z hz
    try intro _
    show ENNReal.ofReal (X.pnorm la P (cpt X.toData x z) ^ 2) = ENNReal.ofReal (X.pnorm la P' (cpt X.toData x z) ^ 2)
    rw [hP'def, pnorm_piecewise X.toData la P hz]
  have hFFle : ∫⁻ z in FF, Φ (cpt X.toData x0 z) ∂(muF X.toData x0) ≤
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0) :=
    lintegral_mono fun z => ENNReal.ofReal_le_ofReal (pnorm_piecewise_le X.toData la P _)

  set C2 : ℝ := 2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r with hC2
  have hC2n : 0 ≤ C2 := by positivity
  have hyx : X.pnorm la P y ^ 2 ≤ 4 * X.pnorm la P x ^ 2 := by
    have h := hhalf y hy
    rw [← hpx] at h
    have := pnorm_nonneg' X.toData la P y
    nlinarith
  have hconst : ENNReal.ofReal (locConst E r w ε) =
      ENNReal.ofReal 4 * (ENNReal.ofReal C2 * ENNReal.ofReal (multBd E r ε)) := by
    rw [← ENNReal.ofReal_mul hC2n, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hC2]; unfold locConst; ring
  calc ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (4 * X.pnorm la P x ^ 2) :=
        ENNReal.ofReal_le_ofReal hyx
    _ = ENNReal.ofReal 4 * ENNReal.ofReal (X.pnorm la P x ^ 2) := ENNReal.ofReal_mul (by norm_num)
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal C2 * ∫⁻ z in A, Φ (cpt X.toData x z) ∂(muF X.toData x)) := by
        rw [← hball]; gcongr
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal C2 * (ENNReal.ofReal (multBd E r ε) *
          ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0))) := by
        gcongr
        exact hunf.trans (by gcongr)
    _ = _ := by rw [hconst]; ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransferHaarFundamentalDomainCm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.RatDarbouxTransferF

theorem finDim (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem finrank_AEF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Module.Free (AF F) (AF F ⊗[F] E) ∧ Module.Finite (AF F) (AF F ⊗[F] E) ∧
    Module.finrank (AF F) (AF F ⊗[F] E) = Module.finrank F E := by
  haveI := finDim F E
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  let bA := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  exact ⟨Module.Free.of_basis bA, Module.Finite.of_basis bA, by
    rw [Module.finrank_eq_card_basis bA, Fintype.card_fin]⟩

theorem card_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (nS nT : ℕ) (κ : Type) [Fintype κ]
    (e : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) :
    2 * Fintype.card κ = nT * nS * Module.finrank F E := by
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AEF F E
  have h := e.finrank_eq
  have ha : Module.finrank (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) = nT * nS * Module.finrank F E := by
    show Module.finrank (AF F) (Fin nT → Fin nS → AF F ⊗[F] E) = _
    simp [Module.finrank_pi_fintype, hAE, mul_assoc]
  have hb : Module.finrank (AF F) ((κ → AF F) × (κ → AF F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    ring
  rw [← hb, ← h, ha]

set_option maxHeartbeats 1000000 in
theorem onto (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (nS nT : ℕ) (κ : Type) [Fintype κ]
    (e : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, e.symm p ∈ ratLF F E nS nT := by
  have hκ := card_eq F E nS nT κ e
  haveI := finDim F E
  let J1 : (κ → F) →ₗ[F] (κ → AF F) := LinearMap.compLeft (Algebra.linearMap F (AF F)) κ
  let J : ((κ → F) × (κ → F)) →ₗ[F] (κ → AF F) × (κ → AF F) := J1.prodMap J1
  let I : Matrix (Fin nT) (Fin nS) E →ₗ[F] Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) :=
    (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
  let L := (e.toLinearMap.restrictScalars F).comp I
  have hJinj : Function.Injective J := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    have hi := AdeleRing.algebraMap_injective (𝓞 F) F
    simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
    refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have hLinj : Function.Injective L := by
    haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    have hr : Function.Injective (inclR (F := F) (E := E) (AF F)) := RingHom.injective _
    intro x x' h
    have := e.injective h
    exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
  have hle : LinearMap.range L ≤ LinearMap.range J := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨(y, z), by rw [show L x = e (incM F x) from rfl, h]; rfl⟩
  have heq : LinearMap.range L = LinearMap.range J := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
    have hm : Module.finrank F (Matrix (Fin nT) (Fin nS) E) = nT * nS * Module.finrank F E := by
      show Module.finrank F (Fin nT → Fin nS → E) = _
      simp [Module.finrank_pi_fintype, mul_assoc]
    have hp : Module.finrank F ((κ → F) × (κ → F)) = 2 * Fintype.card κ := by
      rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
      ring
    rw [hm, hp, hκ]
  intro p hp
  obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
  have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, ?_⟩
  have hx' : e (incM F x) = J (y, z) := hx
  show incM F x = e.symm (J (y, z))
  rw [← hx']
  exact (e.symm_apply_apply _).symm

open scoped Pointwise


set_option maxHeartbeats 1000000 in
theorem haar_fundDomain_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
            IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
            ∃ (ν' : @Measure ((κ → AF F) × (κ → AF F)) (borel _)) (𝓕' : Set ((κ → AF F) × (κ → AF F))),
              @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
              @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕' ν' ∧
              ∀ f : (κ → AF F) × (κ → AF F) → ℂ,
                ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  obtain ⟨hfr, hfin, -⟩ := finrank_AEF F E
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI hMT : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  letI mP : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
  haveI : BorelSpace ((κ → AF F) × (κ → AF F)) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let ce : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃L[AF F] (κ → AF F) × (κ → AF F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : WOF F E nS nT ≃ₜ+ (κ → AF F) × (κ → AF F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me : WOF F E nS nT ≃ᵐ (κ → AF F) × (κ → AF F) := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratLF F E nS nT, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, co.e.symm p ∈ ratLF F E nS nT :=
    onto F E nS nT κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : WOF F E nS nT) + x) = co.e g + co.e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS nT := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratLF F E nS nT := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS nT => co.e (t : WOF F E nS nT)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F κ) (k : ratLF F E nS nT),
          (k : WOF F E nS nT) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF F) × (κ → AF F)) + co.e w = co.e ((k : WOF F E nS nT) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl

end GlobalTheory.RatDarbouxTransferF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefiStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ᶠ w in cofinite, ∀ x : UA E n, x ∈ locU n w → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ h : x ∈ finU (E := E) (n := n), (⟨x, h⟩ : finU (E := E) (n := n)) ∈ L := by
  first | exact @GlobalTheory.BCT.GlobLev.eventually_locU_mem | exact GlobalTheory.BCT.GlobLev.eventually_locU_mem | (intros; apply GlobalTheory.BCT.GlobLev.eventually_locU_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFramesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fock_vacuum_gaussian_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → Framed τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix P Q) (b : Ix R S) (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  first | exact @GlobalTheory.FockVacuum.exists_vacuum | exact GlobalTheory.FockVacuum.exists_vacuum | (intros; apply GlobalTheory.FockVacuum.exists_vacuum <;> assumption)
end

