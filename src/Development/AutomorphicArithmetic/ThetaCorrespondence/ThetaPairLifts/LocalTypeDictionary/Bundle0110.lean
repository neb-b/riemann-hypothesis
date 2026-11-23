module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.PolarizationScalarImPos
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0088
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0085
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomMinorMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0082
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsGeoOfSignatureRankBounds
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0106

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaNeZeroOfInnerProductFormula
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTop.BotNeFormula
set_option maxHeartbeats 4000000 in
theorem bottomTheta_ne_zero_of_innerProduct_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  intro hPr hK hM hI hL hB hN hT
  have hA := _root_.GlobalTheory.T.theta_bottom_formula_large hPr hK hM hI hB
  have hB' := _root_.GlobalTheory.T.theta_bottom_formula_small hPr hK hM hI hB
  have hC := _root_.GlobalTheory.T.rallis_bottom_minor_matching hPr hK hM hI hB
  have hR := _root_.GlobalTheory.T.exists_bottom_basis_change hPr
  refine GlobalTheory.SqTop.BotConstPf.gBig_imp (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and hL hB)
    (GlobalTheory.SqTop.Model.gBig_and hN hT)) (GlobalTheory.SqTop.Model.gBig_and hA (GlobalTheory.SqTop.Model.gBig_and hB' (GlobalTheory.SqTop.Model.gBig_and hC hR)))) ?_
  intro D T Lc sc G μ₀ C x b hLc ⟨⟨⟨l1, l2⟩, l3, l5⟩, a1, a2, a3, a4⟩
  intro δ t0 Q P P' i j hbot
  have hmod : modT G μ₀ = SqNum.condE G.pl := by simp [modT, l2.2.1]
  rw [← hmod] at hbot
  obtain ⟨Λ, hΛ, hnz⟩ := (l1 i j).1 μ₀
  have hh : (h0 D i j : ℤ) ≤ halfRank D i j := by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j
  obtain ⟨Aa, hAa, hAn⟩ := l3 δ t0 i j
  have hP : P.norm ≠ 0 := by
    intro h0'
    have e := hAn μ₀ Q P P' Λ hbot hΛ
    rw [h0', Complex.ofReal_zero] at e
    refine mul_ne_zero hAa (Finset.prod_ne_zero_iff.2 fun s hs => ?_) e.symm
    rw [Finset.mem_Icc] at hs
    exact hnz s hs.1 (hs.2.trans hh)
  obtain ⟨h, Tt, hne⟩ := exists_coord_ne_of_norm_ne P hP
  refine ⟨⟨h, Tt, hne⟩, ?_⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Ker.Model.exists_stdChar D
  obtain ⟨W, hWψ⟩ := GlobalTheory.GridWeil.exists_weil hPr.weilRepresentationUnitaryPair D T Lc μ₀ hLc sc G ψ hψ
  have hψW : IsStdChar D W.ψ (-1) := hWψ ▸ hψ
  obtain ⟨A, A', WW, X₀, c₀, hX₀, hc₀⟩ := l5 W hψW i j
  obtain ⟨X, ζ, hX, hβ, -, hc⟩ := a4 W hψW i j A A' WW X₀ c₀ hX₀ hc₀
  obtain ⟨Ω, -, HA⟩ := a1 W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', -, HB⟩ := a2 W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, -, HC⟩ := a3 W hψW i j A A' WW X _ hX hc
  obtain ⟨uA, -, -, -, HA⟩ := HA μ₀ Q P P' hbot
  obtain ⟨uB, -, -, -, HB⟩ := HB μ₀ Q P P' hbot
  have ea : P.a = A.rank := hbot.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hbot.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hbot.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have hd : P'.d = P.d := hbot.rank.2.2.2
  have ed' : P'.d = WW.rank := hd.trans ed
  obtain ⟨M, -, -, HC⟩ := HC μ₀ Q δ t0 P P' hbot ea ea' ed ed'
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.BotFormula.exists_isFinPt_of_gram_one WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  by_contra hz
  push Not at hz
  apply hne
  have e := HA ea ed h g hg Tt
  rw [HC g Tt] at e
  have hs : ∑ T', (M Tt T' : ℂ) * X.I' W.ψ W.θ μ₀ (GlobalTheory.BotFormula.minorF ea' ed' T') g = 0 := by
    refine Finset.sum_eq_zero fun T' _ => ?_
    rw [HB ea' ed' (hd ▸ h) g hg' T', hz, mul_zero, mul_zero]
  rw [hs, mul_zero, mul_zero] at e
  simpa using e
end GlobalTheory.SqTop.BotNeFormula
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomTheta_nonvanishing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  first | exact @_root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula | exact _root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula | (intros; apply _root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FirstOccurrenceThetaLiftNeZero
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.NonVanBottom
theorem bottom_theta_lift_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
      IsBottomTri W i j X → ∀ t : T, (∃ P h, X.I W.ψ W.θ t P h ≠ 0) ∧ ∃ P' h, X.I' W.ψ W.θ t P' h ≠ 0 := by
  intro hP hK hM hL
  obtain ⟨a1, h1⟩ := _root_.GlobalTheory.T.rallis_inner_product_big_theta_lift hP
  obtain ⟨a2, h2⟩ := _root_.GlobalTheory.T.bottom_theta_norm_eq_prod_local_factors hP.howeDualityReal hP hK hM hL
  obtain ⟨a3, h3⟩ := hL
  refine ⟨max (max a1 a2) a3, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCF)
  obtain ⟨C3, x3, k3⟩ := h3 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max (max C1 C2) C3, max (max x1 x2) x3, fun C hC D large₂ he hx hr T Lc μ₀ hμ G W i j A A' WW X hX t => ?_⟩
  have n1 := k1 C (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX t
  have n2 := k2 C (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Λ, hΛ, hne⟩ := ((k3 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G) i j).1 t
  have hh : ((h0 D i j : ℕ) : ℤ) ≤ (halfRank D i j : ℤ) := by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j
  obtain ⟨P, ν, 𝓕, c, hc, -, -, hf⟩ := n1
  obtain ⟨Pi, p, p', J, -, ⟨P', hP'⟩, hJ, hI, hI'⟩ := n2
  obtain ⟨y, hy⟩ := exists_ne_zero_of_norm_formula hc (fun s hs hs' => hne s hs (hs'.trans hh)) (hf Λ hΛ)
  refine ⟨⟨P, y, hy⟩, P', ?_⟩
  obtain ⟨lam, hlam⟩ := hI t
  have hinj : Function.Injective (J t) := by
    refine (hJ t).resolve_left fun h0 => hy ?_
    rw [hlam P, h0]
    simp
  by_contra hc'
  push_neg at hc'
  apply hP'
  apply hinj
  rw [← hI' t P', map_zero]
  exact funext hc'
end GlobalTheory.NonVanBottom
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_occurrence_theta_lift_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ t : T, (∃ P h, X.I W.ψ W.θ t P h ≠ 0) ∧ ∃ P' h, X.I' W.ψ W.θ t P' h ≠ 0 := by
  first | exact @_root_.GlobalTheory.NonVanBottom.bottom_theta_lift_ne_zero | exact _root_.GlobalTheory.NonVanBottom.bottom_theta_lift_ne_zero | (intros; apply _root_.GlobalTheory.NonVanBottom.bottom_theta_lift_ne_zero <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.QuadraticTowerLargeStepStageDictionary
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepBig
theorem quadratic_tower_large_step_stage_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank, GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf c →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ c₀ →
          ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))ˣ, c * lam μ₀ =
            (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * (c₀ * lam t) := by
  intro hP hK hM
  refine GlobalTheory.SqStepBig.gbig_two (_root_.GlobalTheory.T.exists_good_geometry_over_carried_frames hP) (_root_.GlobalTheory.T.pivot_reduction_divisibility hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b q1 q2 W hψ i j p q A A' WW X lam t Bs hX hF hB
  obtain ⟨FA, FA', FW, Γ, hO, hp, hq, hg, hs⟩ := q1 W hψ i j p q A A' WW X lam t Bs hX hF hB
  refine ⟨Γ, hO, hp, hq, hg, ?_⟩
  intro R om om' Rf om₀ om₀' Rf₀ c c₀ m1 m0 k1 k0
  obtain ⟨h0, Pim, pp, pp', J, hsurj, hJ, hi, hI, hI', P', hP'0, hi'⟩ := id hF
  obtain ⟨P, k, H⟩ := q2 W hψ i j p q A A' WW X lam t Bs hX hF hB FA FA' FW Γ hO hp hq hg hs R P'
    (fun s _ h => hi' s h)
  have key : ∀ s, (s = t ∨ s = μ₀) → ∀ om om' Rf (c : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c →
      ((((GlobalTheory.SqStep.chs G i j s).ν k : ℂ) * lam s) • pp P) = c • pp' P' := by
    intro s hs' om om' Rf c m kc
    apply hJ s
    rw [map_smul, map_smul, mul_smul, ← hI, ← hI' s P' (hi' s)]
    funext h
    simp only [Pi.smul_apply, smul_eq_mul]
    exact H s hs' om om' Rf c m kc h
  have e1 := key t (Or.inl rfl) om om' Rf c m1 k1
  have e0 := key μ₀ (Or.inr rfl) om₀ om₀' Rf₀ c₀ m0 k0
  have e2 : ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) * c) • pp' P' =
      ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) * c₀) • pp' P' := by
    calc ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) * c) • pp' P'
        = (((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • (c • pp' P') := mul_smul _ _ _
      _ = (((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • pp P) := by
          rw [e1]
      _ = (((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • pp P) :=
          smul_comm _ _ _
      _ = (((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • (c₀ • pp' P') := by rw [e0]
      _ = ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) * c₀) • pp' P' := (mul_smul _ _ _).symm
  have e3 := sub_eq_zero.2 e2
  rw [← sub_smul] at e3
  have hz := (smul_eq_zero.1 e3).resolve_right hP'0
  have hn : (((GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  refine ⟨k, ?_⟩
  rw [Circle.coe_div, div_mul_eq_mul_div, eq_div_iff hn]
  linear_combination hz
end GlobalTheory.SqStepBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.tower_stage_fit_factor_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank, GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf c →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ c₀ →
          ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))ˣ, c * lam μ₀ =
            (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * (c₀ * lam t) := by
  first | exact @_root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary | exact _root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary | (intros; apply _root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisInnerProductFormulaFirstOccurrence
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ) (δ t0 : ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ (u : ℂ) (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          u ≠ 0 ∧ u ∈ Qbar ∧
          (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (hd : P'.d = P.d) (h : GA D P.d),
            (∀ T, starRingEnd ℂ (P.coord h T) = κ * u * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T') ∧
            ∀ T', P'.coord (hd ▸ h) T' * (κ * u * c0 s) = ∑ T, (M' T' T : ℂ) * starRingEnd ℂ (P.coord h T) := by
  intro hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := _root_.GlobalTheory.T.theta_bottom_formula_large hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := _root_.GlobalTheory.T.theta_bottom_formula_small hPr hK hM hI hB
  obtain ⟨cC, hC⟩ := _root_.GlobalTheory.T.rallis_bottom_minor_matching hPr hK hM hI hB
  obtain ⟨cD, hD⟩ := _root_.GlobalTheory.T.exists_bottom_basis_change hPr
  refine ⟨max (max (max cA cB) cC) cD, fun ε CF hCF => ?_⟩
  simp only [max_le_iff] at hCF
  obtain ⟨CA, xA, hA⟩ := hA ε CF hCF.1.1.1
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF hCF.1.1.2
  obtain ⟨CC, xC, hC⟩ := hC ε CF hCF.1.2
  obtain ⟨CD, xD, hD⟩ := hD ε CF hCF.2
  refine ⟨max (max (max CA CB) CC) CD, max (max (max xA xB) xC) xD, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  simp only [max_le_iff] at hC0 hx
  have hA := hA C hC0.1.1.1 D large₂ he hx.1.1.1 hR T Lc μ₀ hL G
  have hB' := hB' C hC0.1.1.2 D large₂ he hx.1.1.2 hR T Lc μ₀ hL G
  have hC := hC C hC0.1.2 D large₂ he hx.1.2 hR T Lc μ₀ hL G
  have hD := hD C hC0.2 D large₂ he hx.2 hR T Lc μ₀ hL G
  intro W S hψ _ i j A A' WW X₀ c0 δ t0 hX₀ hc₀
  obtain ⟨X, ζ, hX, hβ, hζ, hc⟩ := hD W hψ i j A A' WW X₀ c0 hX₀ hc₀
  obtain ⟨Ω, hΩ, HA⟩ := hA W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', hΩ', HB⟩ := hB' W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, hκ₀, HC⟩ := hC W hψ i j A A' WW X _ hX hc
  refine ⟨Ω * κ₀ * Ω', mul_ne_zero (mul_ne_zero hΩ hκ₀) hΩ', fun s Q P P' hP => ?_⟩
  obtain ⟨uA, huA, huAQ, huAu, HA⟩ := HA s Q P P' hP
  obtain ⟨uB, huB, huBQ, huBu, HB⟩ := HB s Q P P' hP
  obtain ⟨n, hn, hζn⟩ := hζ s
  obtain ⟨hz0, hzQ, hzu⟩ := GlobalTheory.BotFormula.root_unit hn hζn
  have ea : P.a = A.rank := hP.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hP.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hP.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have ed' : P'.d = WW.rank := hP.rank.2.2.2.trans ed
  obtain ⟨M, M', hMM, HC⟩ := HC s Q δ t0 P P' hP ea ea' ed ed'
  refine ⟨uA * uB * ζ s, M, M', mul_ne_zero (mul_ne_zero huA huB) hz0, Qbar.mul_mem (Qbar.mul_mem huAQ huBQ) hzQ, fun p _ hp lam => ?_, fun hd h => ?_⟩
  · rw [GlobalTheory.BotFormula.lamC_mul lam (Qbar.mul_mem huAQ huBQ) hzQ, GlobalTheory.BotFormula.lamC_mul lam huAQ huBQ, norm_mul, norm_mul,
      huAu p hp lam, huBu p hp lam, hzu p lam, one_mul, one_mul]
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.BotFormula.exists_isFinPt_of_gram_one WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  have key : ∀ T, starRingEnd ℂ (P.coord h T) =
      Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T' := by
    intro T
    rw [HA ea ed h g hg T, HC g T]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T' _ => ?_
    rw [HB ea' ed' (hd ▸ h) g hg' T']
    ring
  refine ⟨key, fun T' => ?_⟩
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e1 : ∀ T'' T, (M' T' T : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ((M T T'' : ℂ) * P'.coord (hd ▸ h) T'')) =
      ((M' T' T * M T T'' : ℤ) : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * P'.coord (hd ▸ h) T'') := by
    intro T'' T; push_cast; ring
  simp_rw [e1, ← Finset.sum_mul, ← Int.cast_sum, hMM]
  simp [mul_comm]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallis_inner_product_formula_first_occurrence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ) (δ t0 : ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ (u : ℂ) (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          u ≠ 0 ∧ u ∈ Qbar ∧
          (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (hd : P'.d = P.d) (h : GA D P.d),
            (∀ T, starRingEnd ℂ (P.coord h T) = κ * u * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T') ∧
            ∀ T', P'.coord (hd ▸ h) T' * (κ * u * c0 s) = ∑ T, (M' T' T : ℂ) * starRingEnd ℂ (P.coord h T) := by
  first | exact @_root_.GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula | exact _root_.GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula | (intros; apply _root_.GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSmallRankStageHolds
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StageSmall
theorem theta_stage_of_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (_root_.GlobalTheory.T.smallStage_thetaIntegral_nonzero_case hP hK hL) (_root_.GlobalTheory.T.smallStage_thetaIntegral_large_rank_case hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨h1, h2⟩ := h C hC D large₂ a b r T Lc μ hL G
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hi := _root_.GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero G W i j p A A' WW X hX
    obtain ⟨P', hP'⟩ := h1 W S hW hN i j p A A' WW X hX hi
    exact ⟨P', fun t h => hi t P' h, hP'⟩
  · exact h2 W S hW hN i j p q A A' WW X hX hq
end GlobalTheory.StageSmall
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_small_rank_stage_holds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageSmall.theta_stage_of_small_rank | exact _root_.GlobalTheory.StageSmall.theta_stage_of_small_rank | (intros; apply _root_.GlobalTheory.StageSmall.theta_stage_of_small_rank <;> assumption)
end
end

