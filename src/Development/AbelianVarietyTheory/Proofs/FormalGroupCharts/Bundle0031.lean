module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGoodConst
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.EvalStandardPointsThree
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RelatedMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosatiCubicalAdditive
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp

theorem inPsi_or_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : E →+* ℂ) :
    InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  unfold InPsi
  have hb : ∀ σ : E →+* ℂ, σ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    intro σ
    have h1 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]; simp
  have h0 : H.rt0.re = 0 := by
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hre := congrArg Complex.re H.sqrt_neg_disc_sq
    have him := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [pow_two] at hre him
    by_contra hne
    have : H.rt0.im = 0 := by
      have h2 : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hb τ) with h | h
  · exact Or.inl h
  · right
    rw [ComplexEmbedding.conjugate_coe_eq, h]
    apply Complex.ext <;> simp [h0]

theorem nuAlg_le_of_jrel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (d : ℕ) (B B' : FB T.V d (𝓞 E)) (φ φi : Pt T.V 1 d) (h h' : PS T.Fr 2 d) (u u' : Lt1 Dw → Fin d → T.Fr), (∀ m, ∃ ε : PS T.V 2 d, JRel m B B' φ φi ε) → B.IsCanonGauge T.Fr h → B'.IsCanonGauge T.Fr h' → (∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct T.Fr B' a).mulVec (u' ℓ) = io (embK c ℓ.1 a) • u' ℓ) → (∀ ℓ, u ℓ = ((dLin φ).map (algebraMap T.V T.Fr)).mulVec (u' ℓ)) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuAlg Dw T B h u e k a n ≤ nuAlg Dw T B' h' u' e k a n := by
  intro E _ _ _ H Dw l Xo c _ hstar T io d B B' φ φi h h' u u' hrel hB hB' heig hu e k a n
  unfold nuAlg
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun f' => ?_
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.ChartVal.exists_nabValN_eq T.V d (𝓞 E) T.Fr B B' φ φi hrel h h' hB hB' (E →+* ℂ) Dw.mult
    ComplexEmbedding.conjugate (InPsi H) (fun τ => io.comp (embK c τ)) (fun τ => by ext x; simp)
    (inPsi_or_conjugate H)
    (fun τ a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hstar]
      congr 1
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])
    (fun σ τ hne => by
      have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))
      obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_⟩
      have h0 : embK c σ a - embK c τ a ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        apply ha
        rw [← embK_coe c, ← embK_coe c, h1]
      rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub]
      exact (Ne.isUnit h0).map _)
    u u' (fun ℓ a => heig a ℓ) hu n P hP.1.1 H.w0 k f'
  refine iInf_le_of_le P (iInf_le_of_le hP (iInf_le_of_le f ?_))
  exact le_of_eq (congrArg (nval T.V e) hf)

end GlobalTheory.ChartCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosIdSt
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer

namespace GlobalTheory.JetRoad

theorem rosIdSt : RosIdSt := by
  intro S G _ _ h2 h3 Lr c O _ _ act u hu T z J hJ
  have a := GlobalTheory.RosatiCube.rosati_cubical_additive S G h2 h3 Lr c O act u hu T z J hJ
  have b := GlobalTheory.rosatiGen_one_mul_star S G h2 h3 Lr c O act u hu T z J hJ
  exact ⟨a.1, a.2.1, b.1, b.2.1, a.2.2, b.2.2⟩

theorem jetRoad : JetAlgSt ∧ RepSt ∧ LawSt ∧ MapSt ∧ DLinSt ∧ ActSt ∧ TwoChartSt ∧ SerSt ∧
    SerExSt ∧ FBOfSt ∧ HMulSt ∧ GermExSt ∧ IntTransSt ∧ ChartBCSt := by
  have hJ : JetAlgSt := jetAlg
  have hR : RepSt := repSt_of_jetAlgSt hJ
  have hL : LawSt := lawSt_of hJ hR
  have hM : MapSt := (GlobalTheory.JetMap.mapSt_and_dLinSt hJ hR).1
  have hD : DLinSt := (GlobalTheory.JetMap.mapSt_and_dLinSt hJ hR).2
  have hA : ActSt := GlobalTheory.ChartAction.actSt_of hJ hR hM
  have hT : TwoChartSt := twoChart_of_rep_map hJ hR hM
  have hS : SerSt := serSt_of_jetAlgSt hJ
  have hE : SerExSt := serEx hJ hR hS
  exact ⟨hJ, hR, hL, hM, hD, hA, hT, hS, hE,
    FBOf.fbOf hJ hR hL hM hA hS hE valSer rosIdSt,
    FrameChange.hMul hJ hR hT hS hE,
    GlobalTheory.GermExist.germ_exists_unique hJ hR hS hE,
    IntTrans.intTrans GlobalTheory.canonGauge_independence_all.2.2.2 GlobalTheory.exists_formalBiext_map,
    GlobalTheory.ChartBaseChange.chartBaseChange hJ hS⟩

end GlobalTheory.JetRoad
end

