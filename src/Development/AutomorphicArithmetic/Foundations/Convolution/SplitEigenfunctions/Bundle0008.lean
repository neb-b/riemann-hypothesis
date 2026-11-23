module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
public import Development.AutomorphicArithmetic.UnipotentInvariants.IntegralTsumRowSectionEqZeroOfConstantTermEqZero
public import Development.AutomorphicArithmetic.UnipotentInvariants.ExistsEquivRowSelectionUnitsIsotropicVectors
public import Development.AutomorphicArithmetic.UnipotentInvariants.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.IILaws
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

private noncomputable def mm (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ) (y : GL (Fin 2) (A E)) : ℂ :=
  mean N fun x => Ψ (x * y)

private theorem beta_cont {N : MeasE E} {Ψ : GL (Fin 2) (A E) → ℂ}
    (h : Continuous fun y => mean N fun x => Ψ (x * y)) : Continuous fun t : (A E)ˣ => mm N Ψ (aE t) :=
  h.comp continuous_aE

private theorem beta_inv {N : MeasE E} {Ψ : GL (Fin 2) (A E) → ℂ}
    (h : ∀ γ y, (mean N fun x => Ψ (x * (ratGL E 2 γ * y))) = mean N fun x => Ψ (x * y))
    (e : Eˣ) (t : (A E)ˣ) : mm N Ψ (aE (IdeleGroup.diagonal E e * t)) = mm N Ψ (aE t) := by
  obtain ⟨γ, hγ⟩ := exists_ratGL_aE (F := E) e
  rw [aE_mul, ← hγ]
  exact h γ _

private theorem mm_det {N : MeasE E} {Ψ : GL (Fin 2) (A E) → ℂ}
    (h : ∀ (h : G1 E) y, (mean N fun x => Ψ (x * (gl h * y))) = mean N fun x => Ψ (x * y))
    (y : GL (Fin 2) (A E)) : mm N Ψ y = mm N Ψ (aE (Matrix.GeneralLinearGroup.det y)) := by
  obtain ⟨g, hg⟩ := exists_gl_mul_aE y
  conv_lhs => rw [hg]
  exact h g _

private theorem mm_central {N : MeasE E} {Ψ : GL (Fin 2) (A E) → ℂ} (hP : PosC Ψ)
    (h : ∀ (h : G1 E) y, (mean N fun x => Ψ (x * (gl h * y))) = mean N fun x => Ψ (x * y))
    (s : {r : ℝ // 0 < r}) (t : (A E)ˣ) :
    mm N Ψ (aE (t * Matrix.GeneralLinearGroup.det
      (GroundTheory.Automorphic.Reduction.centralSection E 2 s : GL (Fin 2) (A E)))) = mm N Ψ (aE t) := by
  set c : GL (Fin 2) (A E) := GroundTheory.Automorphic.Reduction.centralSection E 2 s with hc
  have e1 : mm N Ψ (c * aE t) = mm N Ψ (aE t) := by
    unfold mm
    congr 1
    funext x
    have : x * (c * aE t) = c * (x * aE t) := by
      rw [← mul_assoc, ← mul_assoc]
      congr 1
      exact (GroundTheory.Automorphic.Reduction.centralSection_mul_comm s x).symm
    rw [this]
    exact hP s _
  rw [← e1, mm_det h (c * aE t), map_mul, det_aE, mul_comm]

private theorem ui_add {β β' : (A E)ˣ → ℂ} (c : ℂ)
    (h : IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E)) (normOneFundamentalDomain E) (normOneMeasure E))
    (h' : IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => β' (z : IdeleGroup E)) (normOneFundamentalDomain E) (normOneMeasure E)) :
    (UI fun t => β t + c * β' t) = UI β + c * UI β' := by
  unfold UI
  rw [integral_add h (h'.const_mul c), integral_const_mul]

private theorem mean_add {N : MeasE E} {f f' : GL (Fin 2) (A E) → ℂ} (c : ℂ)
    (h : IntegrableOn (fun x => f (gl x)) N.D N.μ) (h' : IntegrableOn (fun x => f' (gl x)) N.D N.μ) :
    (mean N fun x => f x + c * f' x) = mean N f + c * mean N f' := by
  unfold mean
  rw [integral_add h (h'.const_mul c), integral_const_mul]

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.iiLaws :
    IILaws := by
  intro E _ _ N Ψ hΨ
  obtain ⟨i1, c1, s1, r1⟩ := meanLaws E N Ψ hΨ
  have hβ := uiLaws E (fun t => mm N Ψ (aE t)) (beta_cont c1) (beta_inv r1)
  refine ⟨fun Ψ' hΨ' c => ?_, fun hP g => ?_⟩
  · obtain ⟨i2, c2, s2, r2⟩ := meanLaws E N Ψ' hΨ'
    have hβ' := uiLaws E (fun t => mm N Ψ' (aE t)) (beta_cont c2) (beta_inv r2)
    have e : (fun t : (A E)ˣ => mean N fun x => Ψ (x * aE t) + c * Ψ' (x * aE t)) =
        fun t => mm N Ψ (aE t) + c * mm N Ψ' (aE t) := by
      funext t
      exact mean_add (f := fun x => Ψ (x * aE t)) (f' := fun x => Ψ' (x * aE t)) c (i1 _) (i2 _)
    unfold II
    rw [e]
    exact ui_add c hβ.1 hβ'.1
  · set d₀ : (A E)ˣ := Matrix.GeneralLinearGroup.det g with hd₀
    set s : {r : ℝ // 0 < r} := (IdeleGroup.ideleModule E d₀)⁻¹ with hs
    set d₁ : (A E)ˣ := Matrix.GeneralLinearGroup.det
      (GroundTheory.Automorphic.Reduction.centralSection E 2 s : GL (Fin 2) (A E)) with hd₁
    have hm : IdeleGroup.ideleModule E d₁ = s :=
      GroundTheory.Automorphic.Reduction.detModule_centralSection (K := E) (n := 2) (by norm_num) s
    have hab : ab (d₀ * d₁) = 1 := by
      have : IdeleGroup.ideleModule E (d₀ * d₁) = 1 := by rw [map_mul, hm, hs, mul_inv_cancel]
      exact congrArg Subtype.val this
    have e : (fun t : (A E)ˣ => mean N fun x => Ψ (x * aE t * g)) = fun t => mm N Ψ (aE (t * (d₀ * d₁))) := by
      funext t
      have e1 : (mean N fun x => Ψ (x * aE t * g)) = mm N Ψ (aE t * g) := by
        unfold mm
        simp only [mul_assoc]
      rw [e1, mm_det s1, map_mul, det_aE, ← mul_assoc]
      exact (mm_central hP s1 s _).symm
    unfold II
    rw [e]
    exact hβ.2.2 _ hab
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.RatGl
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem om_L {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D) (g : G1 ℚ) (ph : S4 ℚ)
    {h : GL (Fin 2) (A E)} (hn : nu ℚ h = 1) (v : V4 ℚ) :
    (W.Om g (W.L h ph)).1 v = (W.Om g ph).1 (D.act h⁻¹ v) := by
  have hc := W.comm h g
  rw [hn, M.cD_one] at hc
  have h1 : W.Om g (W.L h ph) = W.L h (W.Om g ph) := (congrArg (fun T => T ph) hc).symm
  rw [h1, W.L_apply, hn, M.ab_one]
  simp

private theorem rat_gl {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) E) :
    gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := by
  apply Units.ext; rfl

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.rank1 :
    DecE → Maj → Orb1 → Rank1 := by
  intro hD hM hO E _ _ _ D W M₀ N P ph hph φ hφ g y hy
  obtain ⟨hLf, hcus, -⟩ := hD E P φ hφ
  obtain ⟨b0, a0, k0, hk0, hg⟩ := M.iwa ℚ g
  obtain ⟨B, hB⟩ := hM E D W M₀ N P ph hph φ hφ {y} isCompact_singleton (by simpa using hy) (ab a0) (M.ab_pos a0) 0
  have hb : ∀ h : G1 E, Summable (fun ξ : Fin 4 → ℚ => ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) ∧
      (∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * y)‖ ≤ B * ab a0 ^ 2 := by
    intro h
    obtain ⟨h1, h2, -⟩ := hB b0 a0 k0 hk0 le_rfl h y rfl
    rw [hg]
    exact ⟨h1, h2⟩
  obtain ⟨⟨σ, hσ⟩, -⟩ := M.rowCosets E
  obtain ⟨T, hTm, hTn, hTs⟩ := UpperTheory.exists_unipotentInvariant_set_unique_row_scaling torCo E
  have glm : ∀ a b : G1 E, gl (a * b) = gl a * gl b := fun a b => map_mul Matrix.SpecialLinearGroup.toGL a b
  have hnu : ∀ x : G1 E, nu ℚ (gl x * y) = 1 := fun x => by rw [nu_mul, nu_gl, hy, one_mul]
  set F : G1 E → (Fin 4 → ℚ) → ℂ := fun x ξ => (W.Om g (W.L (gl x * y) ph)).1 (rp ξ) with hF
  have hFe : ∀ x ξ, F x ξ = (W.Om g ph).1 (D.act (gl x * y)⁻¹ (rp ξ)) := fun x ξ => om_L W g ph (hnu x) _
  have hFc : ∀ ξ, Continuous fun x => F x ξ := by
    intro ξ
    simp only [hFe]
    have h1 : Continuous fun x : G1 E => (gl x * y)⁻¹ := (M.continuous_gl.mul continuous_const).inv
    have h2 := D.continuous_act' h1 (continuous_const (y := rp ξ))
    exact ((W.cont (ph)).comp (continuous_const (y := g) |>.prodMk h2))
  have hinj : Function.Injective fun s : ℚˣ => (![0, (s : ℚ), 0, 0] : Fin 4 → ℚ) := by
    intro s s' h
    exact Units.ext (by simpa using congrFun h 1)
  have hsu : ∀ x, Summable fun s : ℚˣ => F x ![0, (s : ℚ), 0, 0] := fun x =>
    ((hb x).1.comp_injective hinj).of_norm
  set u : G1 E → ℂ := fun x => ∑' s : ℚˣ, F x ![0, (s : ℚ), 0, 0] with hu
  have hum : Measurable u := by
    refine measurable_of_tendsto_metrizable' (u := atTop) (f := fun (S : Finset ℚˣ) x => ∑ s ∈ S, F x ![0, (s : ℚ), 0, 0])
      (fun S => Finset.measurable_sum _ fun s _ => (hFc _).measurable) (tendsto_pi_nhds.2 fun x => (hsu x).hasSum)
  have hun : ∀ b x, u (nU b * x) = u x := by
    intro b x
    refine tsum_congr fun s => ?_
    have h5 := (hO E D).2.2.2.2 (-b) s
    have h6 : (gl (nU b))⁻¹ = gl (nU (-b)) := by rw [M.nU_neg]; exact (map_inv Matrix.SpecialLinearGroup.toGL (nU b)).symm
    rw [hFe, hFe, glm, mul_assoc, _root_.mul_inv_rev, Dat.act_mul, h6, h5]
  set Aa : G1 E → ℂ := T.indicator u with hA
  set c : G1 E → ℂ := fun x => φ.1 (gl x * y) with hc
  have hAm : Measurable Aa := hum.indicator hTm
  have hcm : Measurable c := (hLf.1.comp (M.continuous_gl.mul continuous_const)).measurable
  have hAn : ∀ b x, Aa (nU b * x) = Aa x := by
    intro b x
    by_cases hx : x ∈ T
    · rw [hA, Set.indicator_of_mem hx, Set.indicator_of_mem ((hTn b x).2 hx), hun]
    · rw [hA, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hTn b x).1 h))]
  have hcl : ∀ γ x, c (ratS E γ * x) = c x := by
    intro γ x
    change φ.1 (gl (ratS E γ * x) * y) = φ.1 (gl x * y)
    rw [glm, rat_gl, mul_assoc]
    exact hLf.2 _ _
  have h0 : ∀ x, ∫ b in fundamentalSet E, c (nU b * x) ∂(adeleMeasure E) = 0 := by
    intro x
    have := hcus (gl x * y)
    simpa only [hc, glm, mul_assoc] using this
  have hact : ∀ (x : G1 E) (γ : Matrix.SpecialLinearGroup (Fin 2) E) (ξ ξ' : Fin 4 → ℚ),
      rp ξ' = D.act (gl (ratS E γ))⁻¹ (rp ξ) → F (ratS E γ * x) ξ = F x ξ' := by
    intro x γ ξ ξ' h
    rw [hFe, hFe, h, glm, mul_assoc, _root_.mul_inv_rev, Dat.act_mul]
  have hSel : ∀ x, ∃ e : ↥{r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} × ℚˣ ≃ ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0},
      ∀ r s, rp (e (r, s)).1 = D.act (gl (ratS E (σ r.1)))⁻¹ (rp ![0, (s : ℚ), 0, 0]) :=
    fun x => UpperTheory.exists_equiv_rowSelection_units_isotropicVectors D σ _ hO hσ (hTs σ hσ x)
  have hind : ∀ x r, Aa (ratS E (σ r) * x) =
      Set.indicator {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} (fun r => u (ratS E (σ r) * x)) r := by
    intro x r
    by_cases h : ratS E (σ r) * x ∈ T
    · rw [hA, Set.indicator_of_mem h, Set.indicator_of_mem (show r ∈ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} from h)]
    · rw [hA, Set.indicator_of_notMem h, Set.indicator_of_notMem (show r ∉ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} from h)]
  have hTh : ∀ x, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl x * y) ph)).1 = ∑' r, Aa (ratS E (σ r) * x) := by
    intro x
    obtain ⟨e, he⟩ := hSel x
    have hs0 : Summable fun ξ : ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0} => F x ξ.1 :=
      ((hb x).1.comp_injective Subtype.val_injective).of_norm
    have hs : Summable fun p => F x (e p).1 := e.summable_iff.2 hs0
    change ∑' ξ : ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, F x ξ.1 = _
    rw [← e.tsum_eq (fun ξ => F x ξ.1), hs.tsum_prod]
    simp_rw [hind]
    rw [← tsum_subtype]
    refine tsum_congr fun r => tsum_congr fun s => ?_
    exact (hact x (σ r.1) _ _ (he r s)).symm
  have hbd : ∀ x, ∑' r, ‖Aa (ratS E (σ r) * x) * c x‖ₑ ≤ ENNReal.ofReal (B * ab a0 ^ 2) := by
    intro x
    obtain ⟨e, he⟩ := hSel x
    have h1 : ∑' r, ‖Aa (ratS E (σ r) * x)‖ₑ ≤ ∑' ξ : Fin 4 → ℚ, ‖F x ξ‖ₑ := by
      calc ∑' r, ‖Aa (ratS E (σ r) * x)‖ₑ
          = ∑' r, Set.indicator {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} (fun r => ‖u (ratS E (σ r) * x)‖ₑ) r := by
            refine tsum_congr fun r => ?_
            rw [hind]
            by_cases h : r ∈ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
            · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero]
        _ = ∑' r : ↥{r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}, ‖u (ratS E (σ r.1) * x)‖ₑ :=
            (tsum_subtype _ (fun r => ‖u (ratS E (σ r) * x)‖ₑ)).symm
        _ ≤ ∑' r : ↥{r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}, ∑' s : ℚˣ, ‖F x (e (r, s)).1‖ₑ := by
            refine ENNReal.tsum_le_tsum fun r => enorm_tsum_le_tsum_enorm.trans_eq (tsum_congr fun s => ?_)
            rw [hact x (σ r.1) _ _ (he r s)]
        _ = ∑' p, ‖F x (e p).1‖ₑ := ENNReal.tsum_prod.symm
        _ = ∑' ξ : ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, ‖F x ξ.1‖ₑ := e.tsum_eq fun ξ => ‖F x ξ.1‖ₑ
        _ ≤ ∑' ξ : Fin 4 → ℚ, ‖F x ξ‖ₑ := (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
    have h2 : ∑' ξ : Fin 4 → ℚ, ‖F x ξ‖ₑ = ENNReal.ofReal (∑' ξ : Fin 4 → ℚ, ‖F x ξ‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb x).1]
      exact tsum_congr fun ξ => (ofReal_norm_eq_enorm _).symm
    calc ∑' r, ‖Aa (ratS E (σ r) * x) * c x‖ₑ = (∑' r, ‖Aa (ratS E (σ r) * x)‖ₑ) * ‖c x‖ₑ := by
          simp only [enorm_mul]; exact ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal (∑' ξ : Fin 4 → ℚ, ‖F x ξ‖) * ‖c x‖ₑ := by rw [← h2]; gcongr
      _ = ENNReal.ofReal ((∑' ξ : Fin 4 → ℚ, ‖F x ξ‖) * ‖c x‖) := by
          rw [ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _), ofReal_norm_eq_enorm]
      _ ≤ ENNReal.ofReal (B * ab a0 ^ 2) := ENNReal.ofReal_le_ofReal (hb x).2
  have hfin : (∫⁻ x in N.D, ∑' r, ‖Aa (ratS E (σ r) * x) * c x‖ₑ ∂N.μ) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hbd) ?_)
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (volE E N)
  have hz := UpperTheory.integral_tsum_rowSection_eq_zero_of_constantTerm_eq_zero N σ Aa c hσ hAm hcm hAn hcl h0 hfin
  change ∫ h in N.D, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) ∂N.μ = 0
  rw [← hz]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl x * y) ph)).1 * c x = ∑' r, Aa (ratS E (σ r) * x) * c x
  rw [hTh, tsum_mul_right]
end

