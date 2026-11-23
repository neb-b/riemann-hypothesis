module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0686
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0086
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0077
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FirstRowInvariantUnderTwist
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FirstRowLaw
section Gen
variable {Gg Γg : Type} [Group Gg] [Group Γg] {Wg : Type} [NormedAddCommGroup Wg] [InnerProductSpace ℂ Wg]
end Gen
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} {W : G.Weil} {U : Set T}
theorem first_row_invariant_under_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (u : (R.HX t).H) (v : VV ℂ (wt ch.G (.top 0))) (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m))
      (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v (ch.S.formC t u (y 0 * k)) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v (ch.S.formC t u (y 0)) := by
  intro hP hS
  obtain ⟨a, h1⟩ := _root_.GlobalTheory.FirstRowLevel.levRow_zero_le
  obtain ⟨b, h2⟩ := _root_.GlobalTheory.T.vertex_pair_points_transformation_law hP hS
  refine ⟨max a b, fun ε CF hC => ?_⟩
  obtain ⟨x₁, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x₂, h2⟩ := h2 ε CF (le_of_max_le_right hC)
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ u v x y k hk0
  have hk := h1 D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t k hk0
  have hC := h2 D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ x y k hk0 hk v
  rw [formC_mul ch.S s.core.models.HX t u (y 0) k hk]
  exact hC _
end GlobalTheory.FirstRowLaw
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NormBigOfNonvanishing
section
section
open Finset
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open GlobalTheory.NormSum (Pair)
open GlobalTheory.CMVal (IsHeckeL)
namespace GlobalTheory.NormBigProof
theorem normBig_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → NormBig := by
  intro hP hI hL
  obtain ⟨a1, k1⟩ := hL
  obtain ⟨a2, k2⟩ := _root_.GlobalTheory.T.theta_lift_petersson_norm_ratio_formula hP hI ⟨a1, k1⟩
  obtain ⟨a3, k3⟩ := _root_.GlobalTheory.T.big_theta_lift_ne_zero_of_petersson_norm hP hI ⟨a1, k1⟩
  refine ⟨max a1 (max a2 a3), fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, l1⟩ := k1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, l2⟩ := k2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨c3, x3, l3⟩ := k3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max c1 (max c2 c3), max x1 (max x2 x3), fun C hC D large₂ he hx hRec T Lc μ₀ hμ G => ?_⟩
  have hl := l1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hRec T Lc μ₀ hμ G
  have hr := l2 C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hRec T Lc μ₀ hμ G
  have hz := l3 C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hRec T Lc μ₀ hμ G
  intro δ t0 i j
  by_cases hex : ∃ (t : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G t i j (modT G t) P P'
  · obtain ⟨t₀, Q₀, P₀, P₀', hb₀⟩ := hex
    obtain ⟨Λ₀, hΛ₀, hne⟩ := (hl i j).1 t₀
    have hprod : ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ₀ s ≠ 0 :=
      prod_ne_zero_iff.2 fun s hs => hne s (mem_Icc.1 hs).1
        (le_trans (mem_Icc.1 hs).2 (by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j))
    have hn₀ : (P₀.norm : ℂ) ≠ 0 := by exact_mod_cast hz δ t0 i j t₀ Q₀ P₀ P₀' hb₀
    refine ⟨(P₀.norm : ℂ) / ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ₀ s, div_ne_zero hn₀ hprod,
      fun t Q P P' Λ hb hΛ => ?_⟩
    have e := hr δ t0 i j t t₀ Q Q₀ P P' P₀ P₀' Λ Λ₀ hb hb₀ hΛ hΛ₀
    rw [div_mul_eq_mul_div, eq_div_iff hprod, e]
  · exact ⟨1, one_ne_zero, fun t Q P P' Λ hb _ => absurd ⟨t, Q, P, P', hb⟩ hex⟩
end GlobalTheory.NormBigProof
end

section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normBig_of_lNe : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → NormBig := by
  first | exact @_root_.GlobalTheory.NormBigProof.normBig_alt | exact _root_.GlobalTheory.NormBigProof.normBig_alt | (intros; apply _root_.GlobalTheory.NormBigProof.normBig_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaLargeRank
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotFormula
end GlobalTheory.BotFormula
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.BotFormula.rallis_bottom_formula_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T, starRingEnd ℂ (P.coord h T) = Ω * u * X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g := by
  intro hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := _root_.GlobalTheory.T.bottomTheta_kernel_finiteDimensional hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := _root_.GlobalTheory.T.bottom_thetaIntegral_classSum_formula hPr hK hM hI hB
  refine ⟨max cA cB, fun ε CF hCF => ?_⟩
  obtain ⟨CA, xA, hA⟩ := hA ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max CA CB, max xA xB, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have hA := hA C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have hB' := hB' C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω₀, hΩ₀, HK⟩ := hA W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨v, hv, HC⟩ := hB' W hψ i j A A' WW X δ t0 hX
  refine ⟨(v * Ω₀)⁻¹, inv_ne_zero (mul_ne_zero hv hΩ₀), fun s Q P P' hP => ?_⟩
  obtain ⟨u, hu, huQ, huU, HK⟩ := HK s Q P P' hP
  have huQ' : u⁻¹ ∈ Qbar := inv_mem huQ
  refine ⟨u⁻¹, inv_ne_zero hu, huQ', fun p _ hp lam => ?_, fun ea ed h g hg T => ?_⟩
  · have h1 := GlobalTheory.BotFormula.lamC_mul lam huQ huQ'
    rw [mul_inv_cancel₀ hu] at h1
    have h2 : lamC lam (1 : ℂ) = 1 := by
      unfold lamC
      rw [dite_eq_left (one_mem Qbar)]
      exact (congrArg lam (Subtype.ext rfl : (⟨1, one_mem Qbar⟩ : Qbar) = 1)).trans (map_one lam)
    rw [h2] at h1
    have h3 := congrArg norm h1
    rw [norm_mul, huU p hp lam, one_mul, norm_one] at h3
    exact h3.symm
  have pts : ∀ x : GA D P.a, ∃ y : GA D A, GlobalTheory.BotFormula.IsFinPt A y x := fun x =>
    _root_.GlobalTheory.BotFormula.exists_isFinPt_of_gram_one A hX.std.1 x ea.symm
  choose pt hpt using pts
  rw [HC s Q P P' hP ea ed g pt hpt T]
  simp_rw [HK ea ed h g _ (pt _) hg (hpt _) T]
  rw [GlobalTheory.NormSum.Pair.coord, GlobalTheory.BotFormula.conj_finsum]
  have e1 : ∀ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * (Ω₀ * u * starRingEnd ℂ (P.term x.out h T)) =
      (Ω₀ * u) * starRingEnd ℂ (((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * P.term x.out h T) := by
    intro x
    rw [map_mul, map_inv₀, map_natCast]; ring
  simp_rw [e1, ← mul_finsum]
  field_simp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bottom_formula_large : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T, starRingEnd ℂ (P.coord h T) = Ω * u * X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g := by
  first | exact @_root_.GlobalTheory.BotFormula.rallis_bottom_formula_large_rank | exact _root_.GlobalTheory.BotFormula.rallis_bottom_formula_large_rank | (intros; apply _root_.GlobalTheory.BotFormula.rallis_bottom_formula_large_rank <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmallConvolutionExistsIntegrableTranslates
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.SmallConv
theorem small_convolution_exists_integrable_translates : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence →
    GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t (M : Vol ch.G), M.Is t → ∀ Θ Θ',
      IsMatched ch.S.B t ch.rm i j Θ Θ' → ∀ g g₁,
    ∃ z, zdeg z ≠ 0 ∧ IntegrableOn (translates z (kerSmall ch.W Θ' g g₁)) (M.fd _) (M.ν _) := by
  intro _ hK _ _ _
  obtain ⟨CF0, hH⟩ := standing
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  have hst := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  intro i j t M hM Θ Θ' hΘ g g₁
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  obtain ⟨e, Bs, Γ', X, om, om', h, hTr, hv⟩ := GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL ch.W t i j (hst t) M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid⟩ :=
    _root_.GlobalTheory.ZConvIdent.translates_kerSmall_le_theta hL ch.W ch.S.B ch.rm t i j M hM Θ Θ' hΘ g₁ e Bs Γ' X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ' X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ u, ‖translates z (kerSmall ch.W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall ch.W Θ' g g₁) u = translates z (kerSmall ch.W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.ZConvLeft.kerSmall_rat_left hL ch.W ch.S.B ch.rm t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.BlockHeight.ht_blkU_le _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))
  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  have hcont := GlobalTheory.SmallRoute.continuous_translates_kerSmall hL ch.W ch.S.B ch.rm t i j Θ Θ' hΘ g₁ z
  exact ⟨z, hz, Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
    (.of_forall hbd)⟩
end GlobalTheory.SmallConv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrable_translates_small_convolution : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t (M : Vol ch.G), M.Is t → ∀ Θ Θ', IsMatched ch.S.B t ch.rm i j Θ Θ' → ∀ g g₁,
    ∃ z, zdeg z ≠ 0 ∧ IntegrableOn (translates z (kerSmall ch.W Θ' g g₁)) (M.fd _) (M.ν _) := by
  first | exact @_root_.GlobalTheory.SmallConv.small_convolution_exists_integrable_translates | exact _root_.GlobalTheory.SmallConv.small_convolution_exists_integrable_translates | (intros; apply _root_.GlobalTheory.SmallConv.small_convolution_exists_integrable_translates <;> assumption)
end
end

