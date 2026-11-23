module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0049
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetricPositionLevelShapeOnParabolic
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.SymShape

theorem block_mul_embX {F : Type} [Field F] {κ l p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p)
    (γ : GL (Fin κ) F) : (u * embX l γ).val.toBlocks₁₁ = γ.val := by
  rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val, ← Matrix.fromBlocks_toBlocks u.val,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu]
  simp

theorem simpleSum_embX {F : Type} [Field F] {κ l : ℕ} (γ : GL (Fin κ) F) : simpleSum (embX l γ) = 0 := by
  apply GlobalTheory.RootEx.Radical.simpleSum_eq_zero
  intro i j
  rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.fromBlocks_apply₂₂]

theorem sym_shape :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ)
      (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)),
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P →
        (∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J →
          ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
        (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb →
          IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J,
          (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
        ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J,
          (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u) := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP
  refine ⟨?_, ?_, ?_⟩
  · intro u hu γ hm
    obtain ⟨u', hu', γ', hγ', g₀, hg₀, hr₀⟩ := (hP.1 _).1 hm
    have key : ∀ {F : Type} [Field F] (f : 𝒪[k] →+* F) (x : GL (Fin κ ⊕ Fin l) F) (y : GL (Fin κ) F),
        Matrix.GeneralLinearGroup.map f g₀ = x → x.val.toBlocks₁₁ = y.val →
          (g₀.val.toBlocks₁₁).map f = y.val := by
      intro F _ f x y h1 h2
      rw [← h2, ← h1]
      rfl
    have hBk := key (algebraMap 𝒪[k] k) _ γ hg₀ (block_mul_embX hu γ)
    have hBr := key (IsLocalRing.residue 𝒪[k]) _ γ' hr₀ (block_mul_embX hu' γ')
    have hdet : IsUnit (g₀.val.toBlocks₁₁).det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      change ((g₀.val.toBlocks₁₁).map (IsLocalRing.residue 𝒪[k])).det ≠ 0
      rw [hBr]
      exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨γ', ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_, ?_⟩, hγ'⟩
    · exact Units.ext (by rw [← hBk]; rfl)
    · exact Units.ext (by rw [← hBr]; rfl)
  · intro γ gb hred hgb
    obtain ⟨γ₀, h1, h2⟩ := hred
    let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
      ⟨Matrix.fromBlocks γ₀.val 0 0 1, Matrix.fromBlocks (γ₀⁻¹).val 0 0 1,
        by rw [Matrix.fromBlocks_multiply]; simp, by rw [Matrix.fromBlocks_multiply]; simp⟩
    have hemb : ∀ {F : Type} [Field F] (f : 𝒪[k] →+* F),
        Matrix.GeneralLinearGroup.map f g₀ = embX l (Matrix.GeneralLinearGroup.map f γ₀) := by
      intro F _ f
      refine Units.ext ?_
      rw [GlobalTheory.RootEx.Radical.embX_val]
      change (Matrix.fromBlocks γ₀.val 0 0 1).map f = _
      rw [Matrix.fromBlocks_map]
      simp
    have hm : embX l γ ∈ P.J := (hP.1 _).2 ⟨1, one_mem _, gb, hgb, g₀, by rw [hemb, h1], by rw [hemb, h2, one_mul]⟩
    refine ⟨hm, ?_⟩
    have hblk : (embX l γ).val.toBlocks₁₁ = γ.val := by
      rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.toBlocks_fromBlocks₁₁]
    rw [hP.2 ⟨_, hm⟩]
    simp only [simpleSum_embX, hblk, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  · intro u hu hm
    rw [hP.2 ⟨u, hm⟩]
    simp only [GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu, GlobalTheory.GenericShape.superSum_one, mul_zero,
      AddChar.map_zero_eq_one, Circle.coe_one, mul_one]

end GlobalTheory.SymShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicQuotient
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.QuotIntFJ

theorem integral_rotate_three {B X U : Type} [MeasurableSpace X] [MeasurableSpace B] [MeasurableSpace U]
    (β : Measure B) (μ : Measure X) (ρ : Measure U) [SFinite μ] [SFinite β] [SFinite ρ]
    (Φ : B → X → U → ℂ) (hΦ : Integrable (fun z : B × (X × U) => Φ z.1 z.2.1 z.2.2) (β.prod (μ.prod ρ))) :
    Integrable (fun b => ∫ x, ∫ u, Φ b x u ∂ρ ∂μ) β ∧
      ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ := by
  have hsec : ∀ᵐ b ∂β, Integrable (fun y : X × U => Φ b y.1 y.2) (μ.prod ρ) := hΦ.prod_right_ae
  have hin : ∀ᵐ b ∂β, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ = ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) := by
    filter_upwards [hsec] with b hb
    exact (integral_prod (fun y : X × U => Φ b y.1 y.2) hb).symm
  have hsw : Integrable (fun w : (X × U) × B => Φ w.2 w.1.1 w.1.2) ((μ.prod ρ).prod β) := hΦ.swap
  refine ⟨hΦ.integral_prod_left.congr (hin.mono fun b hb => hb.symm), ?_⟩
  calc ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β
      = ∫ b, ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) ∂β := integral_congr_ae hin
    _ = ∫ w : B × (X × U), Φ w.1 w.2.1 w.2.2 ∂(β.prod (μ.prod ρ)) := (integral_prod _ hΦ).symm
    _ = ∫ w : (X × U) × B, Φ w.2 w.1.1 w.1.2 ∂((μ.prod ρ).prod β) :=
        (integral_prod_swap (fun w : B × (X × U) => Φ w.1 w.2.1 w.2.2)).symm
    _ = ∫ y : X × U, ∫ b, Φ b y.1 y.2 ∂β ∂(μ.prod ρ) := integral_prod _ hsw
    _ = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ :=
        integral_prod (fun y : X × U => ∫ b, Φ b y.1 y.2 ∂β) hsw.integral_prod_left

theorem weil_formula_FJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) f z → (∀ h, Integrable (fun β : n → k => f (colE c (ρ + 1) β * h)) (Measure.pi fun _ => ν)) ∧ IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k, f (colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν)) z := by
  intro k _ _ _ _ _ _ n _ _ c ρ hρ hρc ν _ μX _ μG f z hq
  obtain ⟨F, hF, hfF, hz⟩ := hq
  have hF' : IsLocallyConstant F ∧ HasCompactSupport F := hF
  obtain ⟨hsck, ht2k⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have := hsck
  have := ht2k
  obtain ⟨hB1, hL1, hS1, -⟩ := volGL_haar k n ν
  obtain ⟨hB2, hL2, hS2, -⟩ := volGL_haar k (n ⊕ Fin c) ν
  have := hB1
  have := hL1
  have := hS1
  have := hB2
  have := hL2
  have := hS2

  have hV : volN ν n c (ρ + 1) =
      (Measure.pi fun _ => ν).map (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)) :=
    GlobalTheory.RootEx.VolN.volN_eq (n := n) (c := c) ν (ρ + 1)
  have : SigmaFinite (volN ν n c (ρ + 1)) := by
    rw [hV]
    exact (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)).sigmaFinite_map
  have : IsFiniteMeasureOnCompacts (volN ν n c (ρ + 1)) := by
    rw [hV]
    refine ⟨fun K hK => ?_⟩
    rw [MeasurableEquiv.map_apply]
    have hpre : (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)) ⁻¹' K =
        GlobalTheory.RootEx.VolN.co (ρ + 1) '' K := by
      ext e
      constructor
      · intro he
        exact ⟨_, he, GlobalTheory.RootEx.VolN.co_mkNel _ e⟩
      · rintro ⟨g, hg, rfl⟩
        show GlobalTheory.RootEx.Model.mkNel _ (GlobalTheory.RootEx.VolN.co _ g) ∈ K
        rw [GlobalTheory.RootEx.VolN.mkNel_co]
        exact hg
    rw [hpre]
    exact (hK.image (GlobalTheory.RootEx.VolN.continuous_co _)).measure_lt_top

  have hint : ∀ h : GL (n ⊕ Fin c) k, Integrable
      (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h))
      ((Measure.pi fun _ => ν).prod (μX.prod (volN ν n c (ρ + 1)))) := by
    intro h
    have hcont : Continuous (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine hF'.1.continuous.comp (Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) continuous_const)
      · exact GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_fst.comp continuous_snd)
      · exact continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
      · exact (GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp continuous_fst
    obtain ⟨D, hD, hDC⟩ := _root_.GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hρ hρc ((fun g => g * h⁻¹) '' tsupport F)
      (hF'.2.image (continuous_mul_const h⁻¹))
    have hsupp : HasCompactSupport (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine HasCompactSupport.intro
        (hD.image (f := fun t : GL n k × N k n c (ρ + 1) × (n → k) => (t.2.2, (t.1, t.2.1)))
          (by fun_prop)) ?_
      intro w hw
      by_contra hne
      apply hw
      refine ⟨(w.2.1, w.2.2, w.1), hDC _ ⟨_, subset_tsupport _ hne, ?_⟩, rfl⟩
      simp [mul_assoc]
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hfeq : ∀ (h : GL (n ⊕ Fin c) k) (b : n → k), f (colE c (ρ + 1) b * h) =
      ∫ x, ∫ u : N k n c (ρ + 1), F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
        ∂(volN ν n c (ρ + 1)) ∂μX := by
    intro h b
    rw [hfF]
    simp only [mul_assoc]
  have key := fun h : GL (n ⊕ Fin c) k => integral_rotate_three (Measure.pi fun _ : n => ν) μX
    (volN ν n c (ρ + 1))
    (fun b x (u : N k n c (ρ + 1)) => F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h))
    (hint h)
  refine ⟨fun h => (key h).1.congr (Filter.Eventually.of_forall fun b => (hfeq h b).symm), ?_⟩
  unfold IsQuotIntFJ
  refine ⟨F, hF, fun h => ?_, hz⟩
  calc ∫ b : n → k, f (colE c (ρ + 1) b * h) ∂(Measure.pi fun _ => ν)
      = ∫ b : n → k, ∫ x, ∫ u : N k n c (ρ + 1),
          F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
            ∂(volN ν n c (ρ + 1)) ∂μX ∂(Measure.pi fun _ => ν) :=
        integral_congr_ae (Filter.Eventually.of_forall (hfeq h))
    _ = _ := (key h).2

end GlobalTheory.QuotIntFJ
end

