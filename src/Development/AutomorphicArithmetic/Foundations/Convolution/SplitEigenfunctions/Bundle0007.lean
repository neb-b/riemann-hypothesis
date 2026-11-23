module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import GroundTheory.AutomorphicForms.CompactFormulaCountable
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPartAlt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem tsum_split (δ : ℚ) (f : (Fin 4 → ℚ) → ℂ) (hf : Summable f) :
    ∑' ξ, f ξ = f 0 + (∑' ξ : ({ξ | ξ ≠ 0 ∧ qr δ ξ = 0} : Set (Fin 4 → ℚ)), f ξ) +
      ∑' ξ : ({ξ | qr δ ξ ≠ 0} : Set (Fin 4 → ℚ)), f ξ := by
  set R : Set (Fin 4 → ℚ) := {ξ | ξ ≠ 0 ∧ qr δ ξ = 0}
  set Q : Set (Fin 4 → ℚ) := {ξ | qr δ ξ ≠ 0}
  have h0 : qr δ 0 = 0 := by simp [qr]
  have hpt : ∀ ξ, f ξ = (({0} : Set (Fin 4 → ℚ)).indicator f ξ + R.indicator f ξ) + Q.indicator f ξ := by
    intro ξ
    by_cases hq : qr δ ξ = 0
    · by_cases hξ : ξ = 0
      · subst hξ
        simp [R, Q, h0]
      · simp [R, Q, hξ, hq]
    · have hξ : ξ ≠ 0 := fun e => hq (e ▸ h0)
      simp [R, Q, hξ, hq]
  have s0 := hf.indicator ({0} : Set (Fin 4 → ℚ))
  have sR := hf.indicator R
  have sQ := hf.indicator Q
  rw [tsum_subtype R f, tsum_subtype Q f]
  have e0 : ∑' ξ, ({0} : Set (Fin 4 → ℚ)).indicator f ξ = f 0 := by
    rw [← tsum_subtype]; simp
  rw [← e0, ← (s0.tsum_add sR), ← ((s0.add sR).tsum_add sQ)]
  exact tsum_congr hpt

private theorem cD_one (g : G1 ℚ) : cD 1 g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem ab_one' : ab (1 : (A ℚ)ˣ) = 1 := by
  simp [ab]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E}

private theorem act_zero (h : GL (Fin 2) (A E)) : D.act h (0 : V4 ℚ) = 0 := by
  have e : D.herm (0 : V4 ℚ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE]
  have e2 : D.unherm (0 : Matrix (Fin 2) (Fin 2) (A E)) = 0 := by
    funext i
    fin_cases i <;> simp [Dat.unherm, Dat.co]
  simp [Dat.act, e, e2]

private theorem om_zero (W : Weil D) (g : G1 ℚ) (ph : S4 ℚ) (x : GL (Fin 2) (A E)) (hx : nu ℚ x = 1) :
    (W.Om g (W.L x ph)).1 (rp 0) = (W.Om g ph).1 (rp 0) := by
  have h1 := W.comm x g
  rw [hx, cD_one] at h1
  have h2 : W.Om g (W.L x ph) = W.L x (W.Om g ph) := by
    have := congrArg (fun T : Module.End ℂ (S4 ℚ) => T ph) h1
    simpa [Module.End.mul_apply] using this.symm
  have hz : rp (0 : Fin 4 → ℚ) = (0 : V4 ℚ) := by
    funext i; simp [rp]
  rw [h2, W.L_apply, hx, ab_one', hz, act_zero]
  simp

private theorem core (hMaj : Maj) (hTh : ThCont) (hMean : MeanZero) (hR1 : Rank1)
    (W : Weil D) (M : Meas ℚ) (N : MeasE E) (P : CuspSub E 2) (hV : N.μ N.D < ⊤)
    (ph : S4 ℚ) (hph : ph ∈ Fock D.δ) (φ : Sm E 2) (hφ : φ ∈ P.V) (g : G1 ℚ)
    (y : GL (Fin 2) (A E)) (hy : nu ℚ y = 1) (hgl : ∀ h : G1 E, nu ℚ (gl h) = 1) :
    (mean N fun x => Th (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y)) =
      mean N fun x => ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y) := by
  obtain ⟨b, a, k', hk', hg⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g
  have hapos : 0 < ab a := (IdeleGroup.ideleModule ℚ a).2
  obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ {y} isCompact_singleton
    (by rintro k rfl; exact hy) (ab a) hapos 0
  have hB' : ∀ h : G1 E, (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) ∧
      (∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * y)‖ ≤ B * ab a ^ 2 := by
    intro h
    have := hB b a k' hk' le_rfl h y rfl
    rw [← hg] at this
    exact ⟨this.1, this.2.1⟩
  have hnu : ∀ h : G1 E, nu ℚ (gl h * y) = 1 := fun h => by rw [nu_mul, hgl, hy, one_mul]
  have hcφ : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E 2 φ (P.cusp φ hφ).1
  have hcg : Continuous fun h : G1 E => gl h := by fun_prop
  have hcx : Continuous fun h : G1 E => gl h * y := hcg.mul continuous_const
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using hV⟩
  have hint : ∀ S : Set (Fin 4 → ℚ), IntegrableOn
      (fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := by
    intro S
    have hc1 : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 :=
      (hTh E D W M N P ph hph S).comp_continuous (f := fun h : G1 E => (g, gl h * y))
        (continuous_const.prodMk hcx) (fun h => hnu h)
    have hc : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) :=
      hc1.mul (hcφ.comp hcx)
    refine Integrable.of_bound hc.aestronglyMeasurable (B * ab a ^ 2) (Eventually.of_forall fun h => ?_)
    obtain ⟨hs, hb⟩ := hB' h
    have hle : ‖ThOn S (W.Om g (W.L (gl h * y) ph)).1‖ ≤
        ∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖ := by
      have hsS := hs.subtype (fun x => x ∈ S)
      refine (norm_tsum_le_tsum_norm hsS).trans ?_
      exact tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) Subtype.val_injective
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb
  set c : ℂ := (W.Om g ph).1 (rp 0)
  have hz : ∀ h : G1 E, ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = c := by
    intro h
    have e : ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = (W.Om g (W.L (gl h * y) ph)).1 (rp 0) := by
      simp [ThOn]
    rw [e]
    exact om_zero W g ph _ (hnu h)
  have hφi : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y)) N.D N.μ := by
    refine (hint {0}).congr (Eventually.of_forall fun h => ?_)
    simp only [hz]
  have hpt : ∀ h : G1 E, Th (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) =
      c * φ.1 (gl h * y) +
        ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) := by
    intro h
    have hsp := tsum_split D.δ (fun ξ => (W.Om g (W.L (gl h * y) ph)).1 (rp ξ)) (hB' h).1.of_norm
    have e0 : (W.Om g (W.L (gl h * y) ph)).1 (rp 0) = c := om_zero W g ph _ (hnu h)
    have : Th (W.Om g (W.L (gl h * y) ph)).1 = c + ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 := by
      rw [← e0]
      exact hsp
    rw [this]
    ring
  have z1 : ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0 := hMean E D W M N P φ hφ y
  have z2 : ∫ h in N.D, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) ∂N.μ = 0 :=
    hR1 E D W M N P ph hph φ hφ g y hy
  simp only [mean]
  simp only [hpt]
  have i1 : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y) +
      ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := hφi.add (hint _)
  rw [integral_add i1 (hint _), integral_add hφi (hint _), integral_const_mul, z1, z2]
  simp

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.f0Eq :
    Maj → ThCont → MeanZero → Rank1 → ThetaLiftEqAnisotropicPart := by
  intro hMaj hTh hMean hR1 E _ _ _ D W M N P ph hph φ hφ
  funext g
  have hS := szLaws E D
  simp only [f0, fOn, J1]
  refine congrArg (UI (E := E)) (funext fun z => ?_)
  exact core hMaj hTh hMean hR1 W M N P (UpperTheory.ConvolutionTheory.RankTwoDescent.volE E N) ph hph φ hφ g (sZ D z) (hS.2.2.1 z) hS.2.2.2.1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftIsBoundedCuspidal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity

private theorem cont_nested {X Z Y : Type} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Z) (ν : Measure Y) (S : Set Z) (Dm : Set Y) (hS : MeasurableSet S) (hμ : μ S < ⊤) (hν : ν Dm < ⊤)
    (f : X → Z → Y → ℂ) (x₀ : X) (U : Set X) (hU : U ∈ 𝓝 x₀) (B : ℝ)
    (hb : ∀ x ∈ U, ∀ z ∈ closure S, ∀ y, ‖f x z y‖ ≤ B)
    (hc : ∀ y, Continuous fun p : X × Z => f p.1 p.2 y)
    (hy : ∀ x z, Continuous (f x z)) :
    ContinuousAt (fun x => ∫ z in S, ∫ y in Dm, f x z y ∂ν ∂μ) x₀ := by
  have hint : Integrable (fun _ : Y => B) (ν.restrict Dm) := integrableOn_const hν.ne
  have hG : ∀ x ∈ U, ContinuousOn (fun z => ∫ y in Dm, f x z y ∂ν) (closure S) := by
    intro x hx z₀ hz₀
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun z => (hy x z).aestronglyMeasurable
    · exact eventually_nhdsWithin_of_forall fun z hz => Eventually.of_forall fun y => hb x hx z hz y
    · refine Eventually.of_forall fun y => ?_
      have h1 : Continuous fun z => f x z y := (hc y).comp (Continuous.prodMk_right x)
      exact h1.continuousWithinAt
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B * ν.real Dm) ?_ ?_ (integrableOn_const hμ.ne) ?_
  · filter_upwards [hU] with x hx
    exact ((hG x hx).aestronglyMeasurable isClosed_closure.measurableSet).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  · filter_upwards [hU] with x hx
    refine ae_restrict_of_forall_mem hS fun z hz => ?_
    exact norm_setIntegral_le_of_norm_le_const hν fun y _ => hb x hx z (subset_closure hz) y
  · refine ae_restrict_of_forall_mem hS fun z hz => ?_
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun x => (hy x z).aestronglyMeasurable
    · filter_upwards [hU] with x hx
      exact Eventually.of_forall fun y => hb x hx z (subset_closure hz) y
    · refine Eventually.of_forall fun y => ?_
      have h1 : Continuous fun x => f x z y := (hc y).comp (Continuous.prodMk_left z)
      exact h1.continuousAt

variable {E : Type} [Field E] [NumberField E]

private theorem norm_liftIntegral_le (D : Dat ℚ E) (N : MeasE E) (hV : N.μ N.D < ⊤) (Ψ : GL (Fin 2) (A E) → ℂ) (B : ℝ)
    (hB : ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E, ‖Ψ (gl h * sZ D (z : IdeleGroup E))‖ ≤ B) :
    ‖J1 D N Ψ‖ ≤ B * N.μ.real N.D * (normOneMeasure E).real (normOneFundamentalDomain E) := by
  unfold J1 UI
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top E) fun z hz => ?_
  unfold mean
  exact norm_setIntegral_le_of_norm_le_const hV fun h _ => hB z hz h

end UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity

open UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.thetaPairing_constantTerm_cuspidal :
    Maj → ThCont → ThetaLiftEqAnisotropicPart → Coef → ThetaLiftIsBoundedCuspidal := by
  intro hMaj hTh hF0 hCoef E _ _ _ D W M N P ph hph φ hφ
  obtain ⟨-, hsC, hsN, hgN, -, -, -, -, -, -, -⟩ := szLaws E D
  have hφc : Continuous φ.1 := IsAutForm.continuous (P.cusp φ hφ).1
  have hV : N.μ N.D < ⊤ := volE E N
  set Zc : Set ↥(IdeleGroup.normOneSubgroup E) := closure (normOneFundamentalDomain E) with hZc
  have hZcpt : IsCompact Zc := isCompact_closure_normOneFundamentalDomain E
  have hsz : Continuous fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E) :=
    hsC.comp continuous_subtype_val
  set C : Set (GL (Fin 2) (A E)) := (fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E)) '' Zc with hCdef
  have hC : IsCompact C := hZcpt.image hsz
  have hCn : ∀ k ∈ C, nu ℚ k = 1 := by
    rintro k ⟨z, -, rfl⟩
    exact hsN _
  have hzC : ∀ z ∈ Zc, sZ D (z : IdeleGroup E) ∈ C := fun z hz => ⟨z, hz, rfl⟩
  have hleft : LInv (f0 W N ph φ.1) := by
    intro γ g
    simp only [f0, map_mul, Module.End.mul_apply, W.th_Om]
  have hth := hTh E D W M N P ph hph Set.univ
  have eTh : ∀ u : V4 ℚ → ℂ, ThOn Set.univ u = Th u := fun u => tsum_univ (fun ξ : Fin 4 → ℚ => u (rp ξ))
  have hnu : ∀ (h : G1 E) (z : (A E)ˣ), (gl h * sZ D z) ∈ {x : GL (Fin 2) (A E) | nu ℚ x = 1} := by
    intro h z
    have a1 : ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (gl h)) = 1 := hgN h
    have a2 : ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (sZ D z)) = 1 := hsN z
    change ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (gl h * sZ D z)) = 1
    rw [map_mul, map_mul, a1, a2, one_mul]
  refine ⟨?_, hleft, ?_, ?_⟩
  ·
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds g₀
    obtain ⟨-, hIw⟩ := UpperTheory.ConvolutionTheory.R2.Ff.iwa ℚ
    obtain ⟨V, hVc, hVU⟩ := hIw U hUc
    have hab : Continuous (ab : (A ℚ)ˣ → ℝ) := UpperTheory.ConvolutionTheory.R2.continuous_ab
    have hpos : ∀ a : (A ℚ)ˣ, 0 < ab a := fun a => (IdeleGroup.ideleModule ℚ a).2
    obtain ⟨T, hT⟩ := hVc.exists_bound_of_continuousOn hab.continuousOn
    obtain ⟨T', hT'⟩ := hVc.exists_bound_of_continuousOn
      (f := fun a => (ab a)⁻¹) (hab.inv₀ fun a => (hpos a).ne').continuousOn
    have hc0 : 0 < (|T'| + 1)⁻¹ := inv_pos.2 (by positivity)
    obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ C hC hCn _ hc0 0
    refine cont_nested (normOneMeasure E) N.μ (normOneFundamentalDomain E) N.D
      (measurableSet_normOneFundamentalDomain E) (normOneMeasure_normOneFundamentalDomain_lt_top E) hV
      (fun g z h => Th (W.Om g (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 * φ.1 (gl h * sZ D (z : IdeleGroup E)))
      g₀ U hU (|B| * T ^ 2) ?_ ?_ ?_
    · intro x hx z hz h
      obtain ⟨b, a, ha, k, hk, rfl⟩ := hVU x hx
      have hle : (|T'| + 1)⁻¹ ≤ ab a := by
        have h1 : (ab a)⁻¹ ≤ |T'| + 1 := by
          have := hT' a ha
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos a))] at this
          linarith [le_abs_self T']
        exact (inv_le_comm₀ (hpos a) (by positivity)).1 h1
      obtain ⟨h1, h2, -⟩ := hB b a k hk hle h _ (hzC z hz)
      have h3 : ab a ≤ T := by
        have := hT a ha
        rwa [Real.norm_eq_abs, abs_of_pos (hpos a)] at this
      rw [norm_mul]
      calc _ ≤ _ := mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm h1) (norm_nonneg _)
        _ ≤ _ := h2
        _ ≤ |B| * T ^ 2 := mul_le_mul (le_abs_self B)
          (pow_le_pow_left₀ (hpos a).le h3 2) (by have := hpos a; positivity) (abs_nonneg B)
    · intro y
      have hA : Continuous fun p : G1 ℚ × ↥(IdeleGroup.normOneSubgroup E) => (p.1, gl y * sZ D (p.2 : IdeleGroup E)) :=
        continuous_fst.prodMk (continuous_const.mul (hsz.comp continuous_snd))
      have h1 := hth.comp_continuous hA (fun p => hnu y _)
      simp only [eTh] at h1
      exact h1.mul (hφc.comp (continuous_const.mul (hsz.comp continuous_snd)))
    · intro x z
      have hA : Continuous fun h : G1 E => (x, gl h * sZ D (z : IdeleGroup E)) :=
        continuous_const.prodMk (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const)
      have h1 := hth.comp_continuous hA (fun h => hnu h _)
      simp only [eTh] at h1
      exact h1.mul (hφc.comp (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const))
  ·
    obtain ⟨c, hc, hred⟩ := red ℚ
    obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ C hC hCn c hc 0
    refine ⟨B * N.μ.real N.D * (normOneMeasure E).real (normOneFundamentalDomain E), fun g => ?_⟩
    obtain ⟨γ, b, a, k, hk, he, hle⟩ := hred g
    rw [← hleft γ g, he, hF0 E D W M N P ph hph φ hφ]
    refine norm_liftIntegral_le D N hV _ B fun z hz h => ?_
    obtain ⟨h1, -, h3⟩ := hB b a k hk hle h _ (hzC z (subset_closure hz))
    have h4 : ‖ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om (nU b * mD a * k) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1‖ ≤
        ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0},
          ‖(W.Om (nU b * mD a * k) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 (rp ξ.1)‖ :=
      norm_tsum_le_tsum_norm (h1.subtype _)
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)).trans ?_
    simpa using h3
  ·
    intro g
    have h := hCoef E D W M N P ph hph φ hφ 0 g
    have e0 : fOn W N {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = 0} ph φ.1 g = 0 := by
      have e : {ξ : Fin 4 → ℚ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = 0} = ∅ := by
        ext ξ
        simp
      rw [e]
      simp [fOn, J1, UI, mean, ThOn]
    have e1 : ∀ b : A ℚ, ψ (-(b * UpperTheory.ConvolutionTheory.R2.rt (0 : ℚ))) = 1 := fun b => by simp [ψ, UpperTheory.ConvolutionTheory.R2.rt]
    rw [e0, mul_zero] at h
    simp only [e1, mul_one] at h
    rw [hF0 E D W M N P ph hph φ hφ]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UILaws
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.uiLaws :
    UILaws := by
  intro E _ _ β hc hinv
  have hf : Continuous fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E) :=
    hc.comp continuous_subtype_val
  have hcl := isCompact_closure_normOneFundamentalDomain E
  have hinv' : ∀ (k : Eˣ) (u : IdeleGroup.normOneSubgroup E),
      β ((u * diagonalToNormOne E k : IdeleGroup.normOneSubgroup E) : IdeleGroup E) = β (u : IdeleGroup E) := by
    intro k u
    have h := hinv k (u : IdeleGroup E)
    rw [mul_comm] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · exact (hf.continuousOn.integrableOn_compact hcl).mono_set subset_closure
  · obtain ⟨B, hB⟩ := hcl.exists_bound_of_continuousOn hf.continuousOn
    refine ⟨B, fun t ht => ?_⟩
    have hm : t ∈ IdeleGroup.normOneSubgroup E := by
      refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
      exact ht
    obtain ⟨k, hk, -⟩ := existsUnique_mul_mem_normOneFundamentalDomain E ⟨t, hm⟩
    have h := hB _ (subset_closure hk)
    rwa [hinv' k ⟨t, hm⟩] at h
  · intro d hd
    have hm : d ∈ IdeleGroup.normOneSubgroup E := by
      refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
      exact hd
    set b : IdeleGroup.normOneSubgroup E := ⟨d, hm⟩ with hb
    set g : IdeleGroup.normOneSubgroup E → ℂ := fun z => β (z : IdeleGroup E) with hg
    have hD := isFundamentalDomain_normOneFundamentalDomain E (normOneMeasure E)
    have hD' := hD.smul_of_comm b
    have hI : ∀ (γ : (diagonalNormOne E).op) (x : IdeleGroup.normOneSubgroup E), g (γ • x) = g x := by
      rintro ⟨γ, hγ⟩ x
      obtain ⟨k, hk⟩ := Subgroup.mem_op.1 hγ
      have e : γ.unop = diagonalToNormOne E k := Subtype.ext hk.symm
      change g (x * γ.unop) = g x
      rw [e]
      exact hinv' k x
    have h1 := hD.setIntegral_eq hD' hI
    have h2 := (measurePreserving_mul_left (normOneMeasure E) b).setIntegral_image_emb
      (MeasurableEquiv.mulLeft b).measurableEmbedding g (normOneFundamentalDomain E)
    unfold UI
    change ∫ z in normOneFundamentalDomain E, g (z * b) ∂normOneMeasure E = ∫ z in normOneFundamentalDomain E, g z ∂normOneMeasure E
    rw [h1]
    simp_rw [mul_comm _ b]
    exact h2.symm
end

