module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PHalfTerm
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem test_trM (D : Dom E n 0) {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ) :
    IsTestH (trM Φ M) := by
  have h := (kerLin (ctx ratProper_holds D) (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1)
    (fun p => hΦ p.1 p.2)).1
  have e : trM Φ M = fun z => ∑ p : ι × ι, Φ p.1 p.2 z * M p.2 p.1 := by
    funext z
    simp only [trM, Fintype.sum_prod_type]
  rw [e]
  exact h

private theorem measurable_cnt (D : Dom E n 0) {Ω : Set (H E n 0)} (hΩ : IsCompact Ω) :
    Measurable (cnt (ratH E n 0) Ω) := by
  haveI : T2Space (H E n 0) := (ctx ratProper_holds D).t2
  haveI : IsTopologicalGroup (H E n 0) := (ctx ratProper_holds D).tg
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : Countable (ratH E n 0) := Dcy.countable_ratH'
  unfold cnt
  refine Measurable.tsum fun γ => ?_
  have hc : Continuous fun x : H E n 0 => x⁻¹ * (γ : H E n 0) * x :=
    (continuous_inv.mul continuous_const).mul continuous_id
  exact (measurable_one.indicator hΩ.isClosed.measurableSet).comp hc.measurable

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.halfTerm_pf :
    Basic → GBound → Supp → Rep → Flip → DomInt → HalfTerm := by
  intro hB hGB hSu hRep hFl hDI E _ _ _ n ι _ s m ψ hψ x₀ hx₀
  classical
  haveI : T2Space (H E n 0) := (ctx ratProper_holds s.D).t2
  haveI : SecondCountableTopology (H E n 0) := (ctx ratProper_holds s.D).sc
  haveI : IsTopologicalGroup (H E n 0) := (ctx ratProper_holds s.D).tg
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : IsLocallyFiniteMeasure s.D.μ := s.D.haar.2.2.2
  haveI : SFinite s.D.ν := by unfold Dom.ν; infer_instance
  obtain ⟨hlac, hlmul, -, -, -, hacc, -, -, -, -, hlc, hthc⟩ := hB E n s.pos
  have hφ : IsTestH m.φ := test_trM s.D m.t s.M
  have hψc : Continuous ψ.1 := continuous_of_mem s.π hψ
  obtain ⟨R₀, hR₀⟩ := (hφ.2.isCompact).exists_bound_of_continuousOn hlc.continuousOn
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ z, m.φ z ≠ 0 → |ldet z| ≤ R := fun z hz =>
    (hR₀ z (subset_tsupport _ hz)).trans (le_max_left _ _)
  obtain ⟨Ω, hΩ, hG⟩ := hGB E n ι s
  obtain ⟨C, hC0, hCb⟩ := hG x₀
  obtain ⟨N, hN⟩ := hDI E n s.pos s.D s.π s.fix ψ hψ Ω hΩ
  obtain ⟨C', hC', hb⟩ := hN 0 le_rfl
  have hb' := hb (R + 1) 0 (by positivity)
  have hcf : ∀ x, cnt (ratH E n 0) Ω x ≠ ⊤ := (cntBasic (ctx ratProper_holds s.D)).1 Ω hΩ
  have hcm := measurable_cnt s.D hΩ
  have hA : 0 ≤ C * ‖m.U‖ := mul_nonneg hC0 (norm_nonneg _)
  set S : Set (H E n 0) := {x | |ldet x| ≤ R + 1} with hS
  have hSm : MeasurableSet S := (isClosed_le (continuous_abs.comp hlc) continuous_const).measurableSet
  let F : ℝ → H E n 0 → ℂ := fun t x => ψ.1 x.1 * m.G (ac E n t * x₀) x
  let mm : H E n 0 → ℂ := fun z => m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1))
  let d : H E n 0 → ℝ := S.indicator fun x => ‖ψ.1 x.1‖ * (C * ‖m.U‖) * (cnt (ratH E n 0) Ω x).toReal
  have hlm : Measurable (ldet : H E n 0 → ℝ) := hlc.measurable

  have hFj : Continuous (Function.uncurry F) := by
    refine (hψc.comp (continuous_fst.comp continuous_snd)).mul ?_
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.inner ?_ ?_
    · exact (s.vecs.cont i).1.comp ((hacc.comp continuous_fst).mul continuous_const)
    · exact m.Uπ.continuous.comp ((s.vecs.cont i).2.comp continuous_snd)
  have hFs : ∀ x, Continuous fun t => F t x := fun x =>
    hFj.comp (continuous_id.prodMk continuous_const)

  have hmm : Integrable mm s.D.μ := by
    haveI : IsFiniteMeasureOnCompacts s.D.μ :=
      ⟨fun K hK => hK.measure_lt_top_of_nhdsWithin fun x _ => s.D.μ.finiteAt_nhdsWithin x K⟩
    refine Continuous.integrable_of_hasCompactSupport ?_ hφ.2.mul_right
    refine hφ.1.mul (hψc.comp ?_)
    have : Continuous fun z : H E n 0 => (th (x₀ * z)).1 :=
      continuous_fst.comp (hthc.comp (continuous_const.mul continuous_id))
    exact this

  have hdm : Measurable d := by
    refine Measurable.indicator ?_ hSm
    refine Measurable.mul ?_ hcm.ennreal_toReal
    exact ((hψc.comp continuous_fst).norm.mul continuous_const).measurable
  have hdI : Integrable d s.D.ν := by
    refine ⟨hdm.aestronglyMeasurable, ?_⟩
    set f : H E n 0 → ℝ≥0∞ := {x | |ldet x| ≤ R + 1 ∧ (0 : ℝ) ≤ r0 x}.indicator
      (fun x => ‖ψ.1 x.1‖ₑ * cnt (ratH E n 0) Ω x) with hf
    have hpt : ∀ x, ‖d x‖ₑ ≤ ENNReal.ofReal (C * ‖m.U‖) * f x := by
      intro x
      by_cases hx : x ∈ S
      · have hx' : x ∈ {x | |ldet x| ≤ R + 1 ∧ (0 : ℝ) ≤ r0 x} := ⟨hx, Dcy.redSize_nonneg _⟩
        have e1 : d x = ‖ψ.1 x.1‖ * (C * ‖m.U‖) * (cnt (ratH E n 0) Ω x).toReal :=
          Set.indicator_of_mem hx _
        rw [e1, hf, Set.indicator_of_mem hx', Real.enorm_eq_ofReal (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
          ENNReal.ofReal_toReal (hcf x)]
        exact le_of_eq (by ring)
      · have e1 : d x = 0 := Set.indicator_of_notMem hx _
        simp [e1]
    calc ∫⁻ x, ‖d x‖ₑ ∂s.D.ν ≤ ∫⁻ x, ENNReal.ofReal (C * ‖m.U‖) * f x ∂s.D.ν := lintegral_mono hpt
      _ = ENNReal.ofReal (C * ‖m.U‖) * ∫⁻ x, f x ∂s.D.ν := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hb' ENNReal.ofReal_lt_top)

  have hlx : ∀ t, ldet (ac E n t * x₀) = t := fun t => by rw [hlmul, hlac, hx₀, add_zero]
  have hbd : ∀ t x, |t - ldet x| ≤ 1 → ‖F t x‖ ≤ d x := by
    intro t x htx
    by_cases hx : x ∈ S
    · have e1 : d x = ‖ψ.1 x.1‖ * (C * ‖m.U‖) * (cnt (ratH E n 0) Ω x).toReal :=
        Set.indicator_of_mem hx _
      rw [e1, mul_assoc]
      show ‖ψ.1 x.1 * m.G (ac E n t * x₀) x‖ ≤ _
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcf x)) (hCb m t x)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] at h1
      simpa using h1
    · have e1 : d x = 0 := Set.indicator_of_notMem hx _
      have hx2 : R + 1 < |ldet x| := not_le.1 hx
      have hg : m.G (ac E n t * x₀) x = 0 := by
        refine hSu E n ι s m R hR _ _ ?_
        rw [hlx]
        by_contra hc
        have h1 := abs_le.1 (not_lt.1 hc)
        have h2 := abs_le.1 htx
        have h3 : |ldet x| ≤ R + 1 := abs_le.2 ⟨by linarith [h1.1, h1.2, h2.1, h2.2, hR0], by linarith [h1.1, h1.2, h2.1, h2.2, hR0]⟩
        exact hx h3
      rw [e1]
      show ‖ψ.1 x.1 * m.G (ac E n t * x₀) x‖ ≤ 0
      simp [hg]

  obtain ⟨ψ', hψ', hθ⟩ := s.fix.2 ψ hψ
  have hrep : ∀ (t : ℝ) (u : ℝ → ℂ), Continuous u → HasCompactSupport u →
      ∫ x, F t x * u (ldet x) ∂s.D.ν = ∫ z, mm z * u (-(t + ldet z)) ∂s.D.μ := by
    intro t u hu hu'
    have h := (hRep E n ι s m ψ hψ u hu hu' (ac E n t * x₀)).2
    refine h.trans (integral_congr_ae (Eventually.of_forall fun z => ?_))
    show m.φ z * ψ.1 (thetaA E n ((ac E n t * x₀).1 * z.1)) * u (-(ldet (ac E n t * x₀) + ldet z)) =
      m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) * u (-(t + ldet z))
    have e : (ac E n t * x₀).1 * z.1 = splitCentre E n (t / (n * Module.finrank ℚ E)) * (x₀.1 * z.1) := by
      simp only [ac, Prod.fst_mul, mul_assoc]
    rw [hlx, e, ← hθ, ← hθ, s.fix.1 ψ' hψ']
  exact hFl (H E n 0) (H E n 0) s.D.ν s.D.μ ldet ldet F mm d hlm hlm hFj.measurable hFs hmm hdI hbd hrep
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PInCut
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem deg_finrank_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (x : GA E n)
    (W : Submodule E (Fin n → E)) (hW : Module.finrank E W = 0) : deg x W = 0 := by
  have key : ∀ (k : ℕ) (M : Matrix (Fin n) (Fin k) E), k = 0 → degM x M = 0 := by
    rintro k M rfl
    exact degM_zero x M
  exact key _ _ hW

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem logSize_inv' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (h : GA E n) :
    logSize (h⁻¹ : GA E n) = logSize h := by
  simp only [logSize, inv_inv]
  exact add_comm _ _

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem tau_le_prof {n k : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (h1 : 1 ≤ k) (hk : k ≤ n) : τ ≤ prof n τ k := by
  have a : (1 : ℝ) ≤ k := by exact_mod_cast h1
  have b : (k : ℝ) ≤ n := by exact_mod_cast hk
  have c : (1 : ℝ) ≤ 2 * n + 1 - k := by linarith
  have d : (1 : ℝ) ≤ (k : ℝ) * (2 * n + 1 - k) := by nlinarith
  have e : τ * 1 ≤ τ * ((k : ℝ) * (2 * n + 1 - k)) := mul_le_mul_of_nonneg_left d hτ
  simp only [prof]
  nlinarith

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.inCut_pf :
    InCut := by
  intro E _ _ _ n
  obtain ⟨C, hC0, hC⟩ := E1.degRight E n
  obtain ⟨B, hB⟩ := (D1.degBdd E n).1 (1 : GA E n)
  have hB' : ∀ W, deg (1 : GA E n) W ≤ B := fun W => hB ⟨W, rfl⟩
  set A : ℝ := deg (1 : GA E n) ⊤ with hA
  refine ⟨|B| + |A| + 2 * C + 1, by positivity, fun τ g hτ => ?_⟩
  have hr : 0 ≤ redSize g := ((E1.redBasic E n).2.1 g).1
  have hcr : C * redSize g ≤ (|B| + |A| + 2 * C + 1) * redSize g := by
    apply mul_le_mul_of_nonneg_right _ hr
    have := abs_nonneg B
    have := abs_nonneg A
    linarith
  have hexp : (|B| + |A| + 2 * C + 1) * (1 + redSize g) =
      (|B| + |A| + 2 * C + 1) + (|B| + |A| + 2 * C + 1) * redSize g := by ring
  have hBa := le_abs_self B
  have hAa := neg_abs_le A
  have hBn := abs_nonneg B
  have hAn := abs_nonneg A
  have hτ0 : 0 ≤ τ := by
    have : 0 ≤ (|B| + |A| + 2 * C + 1) * redSize g := mul_nonneg (by positivity) hr
    linarith
  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin n) E, logSize (ratGL E n γ * g) < redSize g + 1 :=
    exists_lt_of_ciInf_lt (lt_add_one (redSize g))
  have hinv := ((E1.mahler_holds E n τ).2.1 γ g)
  refine hinv.1 ?_
  set h : GA E n := ratGL E n γ * g with hh
  have hup : ∀ W, deg h W ≤ B + C * (2 + redSize g) := by
    intro W
    have s := hC 1 h W
    rw [one_mul] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith [hB' W]
  refine ⟨fun W => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank E W) with h0 | h1
    · rw [deg_finrank_zero h W h0, h0]
      simp [prof]
    · have hk : Module.finrank E W ≤ n := by
        have := Submodule.finrank_le W
        simpa using this
      refine le_trans (hup W) (le_trans ?_ (tau_le_prof hτ0 h1 hk))
      linarith
  · have s := hC h (h⁻¹ : GA E n) ⊤
    rw [mul_inv_cancel, logSize_inv'] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPComm
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem op_unique {D : Dom E n 0} {Φ : Matrix ι ι (H E n 0 → ℂ)}
    {T T' : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D} (h : IsROp D Φ T) (h' : IsROp D Φ T') : T = T' := by
  refine ContinuousLinearMap.ext fun f => PiLp.ext fun i => ?_
  exact Lp.ext ((h f i).trans (h' f i).symm)

private theorem isTestM_adjM {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) : IsTestM (adjM Φ) := by
  intro i j
  refine ⟨Complex.continuous_conj.comp ((hΦ j i).1.comp continuous_inv), ?_⟩
  have h := (hΦ j i).2.comp_homeomorph (Homeomorph.inv (H E n 0))
  exact h.comp_left (g := starRingEnd ℂ) (map_zero _)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pComm_pf :
    PComm := by
  intro E _ _ _ n hn D π hfix ι _ Φ T hΦ hT f
  obtain ⟨T₀, h₀, hadj, -⟩ := PositivityTheory.Rg.BcB.E1.kernel_operator_exists_holds E n 0 D ι Φ hΦ
  obtain rfl : T₀ = T := op_unique h₀ hT
  have hS : ∀ g ∈ piSp D π ι, T₀ g ∈ piSp D π ι := piInv E n hn D π hfix ι Φ T₀ hΦ hT
  have hS' : ∀ g ∈ piSp D π ι, ContinuousLinearMap.adjoint T₀ g ∈ piSp D π ι :=
    piInv E n hn D π hfix ι (adjM Φ) _ (isTestM_adjM hΦ) hadj
  have hO : ∀ g ∈ (piSp D π ι)ᗮ, T₀ g ∈ (piSp D π ι)ᗮ := by
    intro g hg
    rw [Submodule.mem_orthogonal] at hg ⊢
    intro u hu
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact hg _ (hS' u hu)
  refine Submodule.eq_starProjection_of_mem_orthogonal (hS _ (Submodule.starProjection_apply_mem _ _)) ?_
  rw [← map_sub]
  exact hO _ (Submodule.sub_starProjection_mem_orthogonal _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPDiag
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {D : Dom E n 0} {ι : Type}

private lemma vecM_apply (v : Lp ℂ 2 D.ν) (c : ι → ℂ) (l : ι) : vecM v c l = c l • v := rfl

private lemma vecM_zero (c : ι → ℂ) : vecM (0 : Lp ℂ 2 D.ν) c = 0 := by
  ext1 l
  simp [vecM_apply]

private lemma vecM_add (a b : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (a + b) c = vecM a c + vecM b c := by
  ext1 l
  simp [vecM_apply, smul_add]

private lemma vecM_sub (a b : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (a - b) c = vecM a c - vecM b c := by
  ext1 l
  simp [vecM_apply, smul_sub]

private lemma vecM_smul (r : ℂ) (a : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (r • a) c = r • vecM a c := by
  ext1 l
  simp [vecM_apply, smul_comm r]

private lemma vecM_unit (f : Hs (ι := Unit) D) : vecM (f ()) (fun _ : Unit => 1) = f := by
  ext1 l
  simp [vecM_apply]

private lemma continuous_vecM [Fintype ι] (c : ι → ℂ) :
    Continuous fun f : Hs (ι := Unit) D => (vecM (f ()) c : Hs (ι := ι) D) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun l => (continuous_const_smul (c l)).comp (PiLp.continuous_apply 2 _ ()))

private lemma isPiVec_vecM (π : CuspSub E n) {f : Hs (ι := Unit) D} (hf : IsPiVec D π f) (c : ι → ℂ) :
    IsPiVec D π (vecM (f ()) c : Hs (ι := ι) D) := by
  intro l
  obtain ⟨ψ, hψ, u, hu, hc, he⟩ := hf ()
  refine ⟨c l • ψ, π.V.smul_mem _ hψ, u, hu, hc, ?_⟩
  have h1 := Lp.coeFn_smul (c l) (f ())
  filter_upwards [h1, he] with x h1 h2
  rw [vecM_apply, h1, Pi.smul_apply, h2]
  simp [mul_assoc]

private lemma isPiVec_comp (π : CuspSub E n) {g : Hs (ι := ι) D} (hg : IsPiVec D π g) (l : ι) :
    IsPiVec D π (vecM (g l) (fun _ : Unit => 1) : Hs (ι := Unit) D) := by
  intro _
  obtain ⟨ψ, hψ, u, hu, hc, he⟩ := hg l
  refine ⟨ψ, hψ, u, hu, hc, ?_⟩
  simpa [vecM_apply] using he

private lemma vecM_mem [Fintype ι] (π : CuspSub E n) (c : ι → ℂ) {f : Hs (ι := Unit) D}
    (hf : f ∈ piSp D π Unit) : (vecM (f ()) c : Hs (ι := ι) D) ∈ piSp D π ι := by
  have hspan : ∀ f ∈ Submodule.span ℂ {f : Hs (ι := Unit) D | IsPiVec D π f},
      (vecM (f ()) c : Hs (ι := ι) D) ∈ Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (isPiVec_vecM π hx c)
    | zero => simpa [vecM_zero] using Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (x + y) () = x () + y () := rfl
      rw [this, vecM_add]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have : (r • x) () = r • x () := rfl
      rw [this, vecM_smul]
      exact Submodule.smul_mem _ _ hx
  have hf' : f ∈ closure (Submodule.span ℂ {f : Hs (ι := Unit) D | IsPiVec D π f} : Set (Hs (ι := Unit) D)) := hf
  have : (vecM (f ()) c : Hs (ι := ι) D) ∈
      closure (Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} : Set (Hs (ι := ι) D)) :=
    map_mem_closure (f := fun f : Hs (ι := Unit) D => (vecM (f ()) c : Hs (ι := ι) D))
      (continuous_vecM c) hf' hspan
  exact this

private lemma vecM_orth [Fintype ι] (π : CuspSub E n) (c : ι → ℂ) {w : Lp ℂ 2 D.ν}
    (hw : (vecM w fun _ : Unit => 1 : Hs (ι := Unit) D) ∈ (piSp D π Unit)ᗮ) :
    (vecM w c : Hs (ι := ι) D) ∈ (piSp D π ι)ᗮ := by
  rw [piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h := (Submodule.mem_orthogonal _ _).1 hw _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (isPiVec_comp π hg l)))
    rw [PiLp.inner_apply] at h
    simp only [vecM_apply, one_smul, Finset.univ_unique, Finset.sum_singleton] at h
    rw [vecM_apply, inner_smul_right, h, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pDiag_pf :
    PDiag := by
  intro E _ _ _ n D π ι _ v c
  show _ = vecM ((piSp D π Unit).starProjection (vecM v fun _ : Unit => 1) ()) c
  have hmem := (piSp D π Unit).starProjection_apply_mem (vecM v fun _ : Unit => 1)
  have horth := (piSp D π Unit).sub_starProjection_mem_orthogonal (vecM v fun _ : Unit => 1)
  refine Submodule.eq_starProjection_of_mem_orthogonal (vecM_mem π c hmem) ?_
  rw [← vecM_sub]
  refine vecM_orth π c ?_
  rw [vecM_sub, vecM_unit]
  exact horth

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPointRep
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem kerH_left {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (φ : H E n 0 → ℂ) (γ : ratH E n 0) (x y : H E n 0) :
    kerH φ ((γ : H E n 0) * x) y = kerH φ x y := by
  unfold kerH
  rw [← finsum_comp_equiv (Equiv.mulLeft γ)]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, _root_.mul_inv_rev]
  group

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pointRep_pf :
    AeEq → KInv → PointRep := by
  intro hA hK E _ _ _ n ι _ s Φ T hΦ hT h g hg x i
  obtain ⟨k, k', hk⟩ := vecsEx E n 0 s.D ι Φ Φ T T 0 hΦ hΦ hT hT
  have hF : Continuous fun x => inner ℂ (s.k₁ x i) h :=
    ((s.vecs.cont i).1).inner continuous_const
  have hG : Continuous fun x => inner ℂ (k x i) g := ((hk.cont i).1).inner continuous_const
  have hIF : Inv fun x => inner ℂ (s.k₁ x i) h := fun γ x => by
    simp only [(hK E n ι s).1 γ x]
  have hIG : Inv fun x => inner ℂ (k x i) g := fun γ x => by
    simp only [hk.rep₁, kerH_left]
  have hae : ∀ᵐ x ∂s.D.ν, ldet x ∈ (Set.univ : Set ℝ) →
      inner ℂ (s.k₁ x i) h = inner ℂ (k x i) g := by
    have h1 := s.o₁ h i
    have h2 := hT g i
    rw [hg] at h1
    filter_upwards [h1, h2] with y a1 a2 _
    rw [s.vecs.rep₁, hk.rep₁, ← a1, a2]
  have := hA E n s.D _ _ Set.univ hF hG hIF hIG isOpen_univ hae x (Set.mem_univ _)
  rw [this, hk.rep₁]
end

