module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SettingNormaliser
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalInvariantIntegralsSymmetricHaarSubgroups
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.HaarR
open scoped ENNReal NNReal

theorem eq_of_mass_one {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (κ μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts κ] [κ.IsMulLeftInvariant] (S : Set G) (hS : μ S = 1) (hκ : κ S = 1) : κ = μ := by
  have h := Measure.isMulLeftInvariant_eq_smul κ μ
  set a := Measure.haarScalarFactor κ μ
  have h1 : (a : ℝ≥0∞) = 1 := by
    rw [h, Measure.smul_apply, hS, ENNReal.smul_def, smul_eq_mul, mul_one] at hκ
    exact hκ
  have : a = 1 := by exact_mod_cast h1
  rw [h, this, one_smul]

theorem quot_int_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (m : Measure (GL n k)) (G : Measure (GL (n ⊕ Fin c) k)), m.IsHaarMeasure → G.IsHaarMeasure → m (KO k n) = 1 → (c + 1 = 2 * ρ → ∀ μR : Measure (R k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotInt ν m G ρ f z → IsQuotIntL1 μR G f z) ∧ (1 ≤ ρ → c = 2 * ρ → ∀ μR : Measure (RFJ k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotIntFJ ν m G ρ f z → IsQuotIntL1 μR G f z) := by
  intro k _ _ _ _ _ _ ν hν n _ _ c ρ m G hm hG hmK
  haveI := hν.1
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  have hKO : ∀ (S : Subgroup (GL (n ⊕ Fin c) k)), MeasurableSet {x : S | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} :=
    fun S => (GlobalTheory.SplitFlip.isOpen_KO.preimage continuous_subtype_val).measurableSet
  have hFint : ∀ F ∈ SB (GL (n ⊕ Fin c) k), Integrable F G := fun F hF => hF.1.continuous.integrable_of_hasCompactSupport hF.2
  have hFS : ∀ (S : Subgroup (GL (n ⊕ Fin c) k)), IsClosed (S : Set (GL (n ⊕ Fin c) k)) → ∀ (μS : Measure S),
      μS.IsHaarMeasure → ∀ F ∈ SB (GL (n ⊕ Fin c) k), ∀ h, Integrable (fun r : S => F (r * h)) μS := by
    intro S hS μS _ F hF h
    exact (hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
      ((hF.2.comp_homeomorph (Homeomorph.mulRight h)).comp_isClosedEmbedding hS.isClosedEmbedding_subtypeVal)
  refine ⟨fun hc μR hR hRK => ?_, fun h1 hc μR hR hRK => ?_⟩
  · have h1 : 1 ≤ ρ := by omega
    have h2 : ρ ≤ c := by omega
    obtain ⟨hNc, hcl, hNH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c ρ h1 h2 ν
    haveI : LocallyCompactSpace (N k n c ρ) := hNc.locallyCompactSpace
    haveI := hNH
    haveI : LocallyCompactSpace (R k n c ρ) := hcl.locallyCompactSpace
    haveI := hR
    haveI := hm
    haveI := _root_.GlobalTheory.HaarR.map_prodR_isMulLeftInvariant k n c ρ h1 h2 ν hν.1 m hm
    haveI := _root_.GlobalTheory.HaarR.finite_r k n c ρ h1 h2 ν hν.1 m hm
    have hmeas : Measurable (prodR (k := k) (n := n) (c := c) ρ) :=
      (Continuous.subtype_mk ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)) _).measurable
    have hκ : (m.prod (volN ν n c ρ)).map (prodR ρ) = μR := by
      refine eq_of_mass_one _ μR _ hRK ((Measure.map_apply hmeas (hKO (R k n c ρ))).trans ?_)
      rw [GlobalTheory.T.levyProductMap_preimage_integralGL, Measure.prod_prod, hmK, _root_.GlobalTheory.HaarR.volN_KO_eq_one k n c ρ h1 h2 ν hν, one_mul]
    haveI : μR.IsMulRightInvariant := GlobalTheory.LevelUnimod.unimodular k n c ρ (fun i => i.val + 1)
      (fun i => by simp [Fin.rev]; omega) (R k n c ρ)
      (GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).1 μR hR
    refine ⟨GlobalTheory.SemiHaar.invInv_of_rightInv μR, ?_⟩
    rintro f z ⟨F, hF, hf, hz⟩
    have hi := hFS _ hcl μR hR F hF
    refine ⟨F, hFint F hF, hi, fun h => ?_, hz⟩
    have hc' : Continuous fun r : R k n c ρ => F (r * h) :=
      hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hp : Integrable (fun q => F ((prodR (k := k) (n := n) (c := c) ρ q : GL (n ⊕ Fin c) k) * h)) (m.prod (volN ν n c ρ)) := by
      have := hi h
      rw [← hκ] at this
      exact (integrable_map_measure hc'.aestronglyMeasurable hmeas.aemeasurable).1 this
    rw [hf h, ← hκ, integral_map hmeas.aemeasurable hc'.aestronglyMeasurable, integral_prod _ hp]
    rfl
  · have h2 : ρ < c := by omega
    obtain ⟨hNc, -, hNH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c (ρ + 1) (by omega) (by omega) ν
    haveI : LocallyCompactSpace (N k n c (ρ + 1)) := hNc.locallyCompactSpace
    haveI := hNH
    haveI := hm
    haveI := hR
    have hmem := (GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).2 h1 h2
    have hcl : IsClosed (RFJ k n c ρ : Set (GL (n ⊕ Fin c) k)) := by
      have e : (RFJ k n c ρ : Set (GL (n ⊕ Fin c) k)) = ⋂ r : n ⊕ Fin c, ⋂ s : n ⊕ Fin c,
          {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
        ext g; simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_setOf_eq]
      rw [e]
      refine isClosed_iInter fun r => isClosed_iInter fun s => ?_
      by_cases hrs : (r.isRight ∨ s.isRight) ∧ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
          Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r
      · have : {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} =
            {g : GL (n ⊕ Fin c) k | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
          ext g; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hrs.1 hrs.2, fun h _ _ => h⟩
        rw [this]
        exact isClosed_eq (GlobalTheory.RootEx.VolN.continuous_entry r s) continuous_const
      · have : {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} = Set.univ := by
          ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact fun a b => absurd ⟨a, b⟩ hrs
        rw [this]; exact isClosed_univ
    haveI : LocallyCompactSpace (RFJ k n c ρ) := hcl.locallyCompactSpace
    haveI := _root_.GlobalTheory.HaarR.LeftFJ.isMulLeftInvariant_map_prodRFJ k n c ρ h1 h2 ν hν.1 m hm
    haveI := _root_.GlobalTheory.HaarR.finite_on_compacts_prodRFJ k n c ρ h1 h2 ν hν.1 m hm
    have hmeas : Measurable (prodRFJ (k := k) (n := n) (c := c) ρ) :=
      (Continuous.subtype_mk (((GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_fst.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul
        ((GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp continuous_snd)) _).measurable
    have hκ : ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ) = μR := by
      refine eq_of_mass_one _ μR _ hRK ((Measure.map_apply hmeas (hKO (RFJ k n c ρ))).trans ?_)
      have hpi : {β : n → k | ∀ i, β i ∈ 𝒪[k]} = Set.univ.pi fun _ : n => (𝒪[k] : Set k) := by
        ext β; simp
      rw [GlobalTheory.T.levyProductMapToFourierJacobi_preimage_integralGL k n c ρ h2, Measure.prod_prod, Measure.prod_prod, hmK, _root_.GlobalTheory.HaarR.volN_KO_eq_one k n c (ρ + 1) (by omega) (by omega) ν hν, hpi,
        Measure.pi_pi, hν.2]
      simp
    haveI : μR.IsMulRightInvariant := GlobalTheory.LevelUnimod.unimodular k n c (2 * ρ + 1) (fun i => 2 * (i.val + 1))
      (fun i => by simp [Fin.rev]; omega) (RFJ k n c ρ) hmem μR hR
    refine ⟨GlobalTheory.SemiHaar.invInv_of_rightInv μR, ?_⟩
    rintro f z ⟨F, hF, hf, hz⟩
    have hi := hFS _ hcl μR hR F hF
    refine ⟨F, hFint F hF, hi, fun h => ?_, hz⟩
    have hc' : Continuous fun r : RFJ k n c ρ => F (r * h) :=
      hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hp : Integrable (fun q => F ((prodRFJ (k := k) (n := n) (c := c) ρ q : GL (n ⊕ Fin c) k) * h))
        ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)) := by
      have := hi h
      rw [← hκ] at this
      exact (integrable_map_measure hc'.aestronglyMeasurable hmeas.aemeasurable).1 this
    rw [hf h, ← hκ, integral_map hmeas.aemeasurable hc'.aestronglyMeasurable, integral_prod _ hp,
      integral_prod _ hp.integral_prod_left]
    rfl

end GlobalTheory.HaarR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottom
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LevNorm

open Formalism.BasicNotions.TH

theorem embA_injective {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) :
    Function.Injective (embA d o) := fun _ _ h =>
  congrArg Prod.fst (o.emb_injective (d.wittDecomp_anisotropicEmbedding_injective h))

theorem finf_sand {D : D7} {k n : ℕ} (p : Mx D k n) (m : Mx D n n) (j : Mx D n k) (hm : m.map (CenAct.finf D) = 1)
    (h : p ⬝ j = 1) : (p ⬝ (m ⬝ j)).map (CenAct.finf D) = 1 := by
  rw [← Matrix.mul_assoc, CenAct.map_sand p m j hm, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_GfC_of_embA {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {a : GA D A}
    (h : embA d o a ∈ GfC S) : a ∈ GfC A := by
  rw [embA_apply, CenAct.mem_GfC_iff] at h
  have h1 := finf_sand d.p0 _ d.j0 h d.p0_j0
  rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul] at h1
  have h2 := finf_sand o.pA _ o.jA h1 o.pA_jA
  rw [o.emb_jA, cancel₂ o.pA_jA, Matrix.one_mul] at h2
  exact (CenAct.mem_GfC_iff _ _).2 h2

theorem matches_differ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hρ : 1 ≤ D.R.rS)
    (u : D.what₂.Word) {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)
    {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {t t' : GA D (D.sp.Y 0)} (ht : Matches X h J χ t) (ht' : Matches X h J χ t') :
    ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ k ∈ J,
      t = ((iotaX X h).symm (1, X.xu u))⁻¹ * embA B.d B.o a * (iotaX X h).symm (1, X.xu u) * z * t' * k := by
  let j : X.B.I.Gf →* GA D (D.sp.Y 0) := ((iotaX X h).symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : ∀ x, iotaX X h (j x) = (1, x) := fun x => (iotaX X h).apply_symm_apply _
  have hjG : ∀ x, j x ∈ GfC (D.sp.Y 0) := fun x => (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h _).1 (by rw [hj])
  have hjJ : ∀ x, j x ∈ rowJ X h ↔ x ∈ X.K2 := fun x => by
    show (iotaX X h (j x)).1 = 1 ∧ (iotaX X h (j x)).2 ∈ X.K2 ↔ _
    rw [hj]
    exact and_iff_right rfl
  have hjχ : ∀ x, rowChi X h (j x) = star (X.chi2 x) := fun x => by
    show star (X.chi2 (iotaX X h (j x)).2) = _
    rw [hj]
  obtain ⟨y, hy⟩ : ∃ y, j y = t * t'⁻¹ := ⟨_, GlobalTheory.SeeConjRead.eq_symm_one X h _
    ((GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h _).2 (mul_mem ht.1 (inv_mem ht'.1)))⟩
  have e1 : ∀ x, t'⁻¹⁻¹ * (t'⁻¹ * j x * t') * t'⁻¹ = j x := fun x => by group
  have e2 : ∀ x, t⁻¹⁻¹ * (t'⁻¹ * j x * t') * t⁻¹ = j (y * x * y⁻¹) := fun x => by
    rw [map_mul, map_mul, map_inv, hy]; group
  have hJ : ∀ x, t'⁻¹ * j x * t' ∈ J ↔ x ∈ X.K2 := fun x => by rw [(ht'.2 _).1, e1, hjJ]
  obtain ⟨z, hz, w, hw, hw', k, hk, e⟩ := setting_normaliser X h hρ u y fun x =>
    ⟨by rw [← hJ, (ht.2 _).1, e2, hjJ], fun hx => by
      rw [← hjχ, ← hjχ, ← e2, (ht.2 _).2 ((hJ x).2 hx), ← (ht'.2 _).2 ((hJ x).2 hx), e1]⟩
  obtain ⟨a, ha⟩ := (B.tieH (j w)).2 (by rw [hj]; exact ⟨one_mem _, hw⟩)
  refine ⟨j z, hjG z, Subgroup.mem_center_iff.2 fun g => (iotaX X h).injective ?_, a,
    mem_GfC_of_embA B.d B.o (ha ▸ hjG w), Subgroup.mem_center_iff.2 fun b => embA_injective B.d B.o ((iotaX X h).injective ?_),
    t'⁻¹ * j k * t', (hJ k).2 hk, ?_⟩
  · rw [map_mul, map_mul, hj]
    exact Prod.ext (by simp) (Subgroup.mem_center_iff.1 hz _)
  · rw [map_mul, map_mul, map_mul, map_mul, ha, hj]
    exact Prod.ext (by simp) (hw' _ ((B.tieH _).1 ⟨b, rfl⟩).2).symm
  · show t = (j (X.xu u))⁻¹ * embA B.d B.o a * j (X.xu u) * j z * t' * (t'⁻¹ * j k * t')
    rw [ha]
    have e3 := congrArg j e
    rw [hy, map_mul, map_mul, map_mul, map_mul, map_inv] at e3
    calc t = t * t'⁻¹ * t' := by group
      _ = _ := by rw [e3]; group

end GlobalTheory.LevNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntLocIffValBar
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LineUnit

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped NNReal

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {k : ℕ}

theorem exists_lt_nnnorm (v : HeightOneSpectrum (𝓞 F)) (C : ℝ≥0) : ∃ t : Fv F v, C < ‖t‖₊ := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm (Fv F v) (C : ℝ)
  exact ⟨t, by exact_mod_cast ht⟩

theorem valBar_smul (τ : E →ₐ[F] FvBar F v) (t : Fv F v) (y : Fv F v ⊗[F] E) :
    valBar F v (finEmb F v τ (t • y)) = ‖t‖₊ * valBar F v (finEmb F v τ y) := by
  rw [map_smul, Algebra.smul_def, map_mul]
  congr 1
  exact absBar_algebraMap F v t

theorem mem_intLoc_iff_valBar {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ ∀ τ : E →ₐ[F] FvBar F v, valBar F v (finEmb F v τ y) ≤ 1 :=
  mem_intLoc_iff_absFin_le_one.trans (absFin_le_iff F v)

theorem exists_valBar_ne_zero {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) (τ : E →ₐ[F] FvBar F v) :
    ∃ j, valBar F v (finEmb F v τ (u j)) ≠ 0 := by
  by_contra hc
  push Not at hc
  have := congrArg (finEmb F v τ) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one, Finset.sum_eq_zero fun j _ => by
    rw [map_mul, (Valuation.zero_iff _).1 (hc j), mul_zero]] at this
  exact zero_ne_one this

theorem mem_intLoc_of_stable {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, a * u j ∈ intLoc F E v) → ∀ j, c * a * u j ∈ intLoc F E v) : c ∈ intLoc F E v := by
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (Finset.univ.sup fun j => absFin F v (u j))
  have ht0 : ‖t‖₊ ≠ 0 := (lt_of_le_of_lt zero_le ht).ne'
  have h0 : ∀ j, (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun j => by
    rw [smul_mul_assoc, one_mul, mem_intLoc_iff_valBar]
    intro τ
    rw [valBar_smul, nnnorm_inv, inv_mul_le_iff₀ (pos_iff_ne_zero.2 ht0), mul_one]
    exact (le_absFin F v τ (u j)).trans
      ((Finset.le_sup (f := fun j => absFin F v (u j)) (Finset.mem_univ j)).trans ht.le)
  have hk : ∀ m : ℕ, ∀ j, c ^ m * (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun m => by
    induction m with
    | zero => simpa only [pow_zero, one_mul] using h0
    | succ m ih =>
      intro j
      have := hc _ ih j
      rwa [← mul_assoc, ← pow_succ'] at this
  rw [mem_intLoc_iff_valBar]
  intro τ
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)) :=
    mul_pos (inv_pos.2 (pos_iff_ne_zero.2 ht0)) (pos_iff_ne_zero.2 hj)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)))⁻¹ hlt
  have h1 := mem_intLoc_iff_valBar.1 (hk m j) τ
  rw [mul_assoc, smul_mul_assoc, one_mul, map_mul, map_mul, map_pow, map_pow, valBar_smul, nnnorm_inv,
    ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 hm)

theorem isUnit_of_reflect {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, c * a * u j ∈ intLoc F E v) → ∀ j, a * u j ∈ intLoc F E v) : IsUnit c := by
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_left.2 fun a ha => ?_)
  refine absFin_eq_zero_iff.1 (le_antisymm ((absFin_le_iff F v).2 fun τ => ?_) zero_le)
  by_contra hne
  have hpa : 0 < valBar F v (finEmb F v τ a) := not_le.1 hne
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  have hpos : 0 < valBar F v (finEmb F v τ (a * u j)) := by
    rw [map_mul, map_mul]; exact mul_pos hpa (pos_iff_ne_zero.2 hj)
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (valBar F v (finEmb F v τ (a * u j)))⁻¹
  have h1 := mem_intLoc_iff_valBar.1
    (hc (t • a) (fun j => by rw [mul_smul_comm, ha, smul_zero, zero_mul]; exact zero_mem _) j) τ
  rw [smul_mul_assoc, valBar_smul, ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 ht)

theorem smul_mem_latLoc_iff {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    {w l : Fin n → Fv F v ⊗[F] E} (h : l ⬝ᵥ w = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a : Fv F v ⊗[F] E, (c * a) • w ∈ latLoc F L v ↔ a • w ∈ latLoc F L v) (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ c • y ∈ latLoc F L v := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  have h2 := SelfDual.map_mul_eq_one (F := F) (Fv F v) h1
  set u := Φ.map (inclR (F := F) (Fv F v)) *ᵥ w with hu
  have hl : ∑ j, (l ᵥ* S.map (inclR (F := F) (Fv F v))) j * u j = 1 := by
    change (l ᵥ* _) ⬝ᵥ u = 1
    rw [← Matrix.dotProduct_mulVec, hu, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, h]
  have key : ∀ a : Fv F v ⊗[F] E, a • w ∈ latLoc F L v ↔ ∀ j, a * u j ∈ intLoc F E v := fun a => by
    rw [SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v, Matrix.mulVec_smul]
    rfl
  simp only [key] at hc
  have hc1 := mem_intLoc_of_stable hl fun a => (hc a).2
  obtain ⟨c, rfl⟩ := isUnit_of_reflect hl fun a => (hc a).1
  have hc2 : ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v :=
    mem_intLoc_of_stable hl fun a ha => (hc _).1 fun j => by rw [Units.mul_inv_cancel_left]; exact ha j
  refine ⟨fun hy => (latLoc F L v).smul_mem ⟨_, hc1⟩ hy, fun hy => ?_⟩
  have := (latLoc F L v).smul_mem ⟨_, hc2⟩ hy
  change ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • (c : Fv F v ⊗[F] E) • y ∈ _ at this
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end Local


set_option maxHeartbeats 1600000 in
theorem smul_mem_latV_iff : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Λ : GlobalTheory.FinPl.Lat V), Submodule.IsFullLattice D.host.E Λ → ∀ (v : GlobalTheory.FinPl.Pl D) (ε : Fin V.rank → D.host.E), ε ≠ 0 → ∀ (c : AE D) (s : Matrix (Fin V.rank) (Fin V.rank) (AE D)), IsUnit s → (∀ a ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (s) (fun i => c * (a * Formalism.L2.Theta.incA D (ε i))) ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ Matrix.mulVec (s) (fun i => a * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V Λ (· = v))) → ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = v)) → (y ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ c • y ∈ GlobalTheory.FinPl.latV V Λ (· = v)) := by
  intro D V Λ hΛ v ε hε c s hs h y hy
  have hfg : Λ.FG := by
    letI := hΛ
    exact Submodule.IsLattice.fg D.host.E Λ
  let π : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E := (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v).comp (finPart D)
  have hπ : ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ GlobalTheory.FinPl.idAt D (· = v)) →
      (z ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ (fun i => π (z i)) ∈ latLoc D.host.F Λ v) := fun z hz =>
    GlobalTheory.StMoves.mem_latV_iff_latLoc V Λ hfg v z hz
  let w : Fin V.rank → AE D := s *ᵥ fun i => Formalism.L2.Theta.incA D (ε i)
  have hw : ∀ a : AE D, (s *ᵥ fun i => a * Formalism.L2.Theta.incA D (ε i)) = a • w := fun a =>
    Matrix.mulVec_smul s a _
  obtain ⟨l, hl⟩ : ∃ l : Fin V.rank → AE D, l ⬝ᵥ w = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hε
    obtain ⟨s', rfl⟩ := hs
    refine ⟨(Pi.single i (Formalism.L2.Theta.incA D (ε i)⁻¹)) ᵥ* (s'⁻¹).1, ?_⟩
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, single_dotProduct,
      ← map_mul, inv_mul_cancel₀ hi, map_one]
  have hl' : (fun i => π (l i)) ⬝ᵥ (fun i => π (w i)) = 1 := by
    rw [← map_one π, ← hl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
  have hsm : ∀ (a : AE D) (z : Fin V.rank → AE D), (fun i => π ((a • z) i)) = π a • fun i => π (z i) :=
    fun a z => funext fun i => map_mul π a (z i)
  rw [hπ y hy, hπ (c • y) fun i => Ideal.mul_mem_left _ _ (hy i), hsm]
  refine smul_mem_latLoc_iff Λ hΛ hl' (fun b => ?_) _
  obtain ⟨a, ha, hab⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (D := D) (n := 1) v fun _ => b
  have hab' : π (a 0) = b := congrFun hab 0
  have h1 := h (a 0) (ha 0)
  simp only [← mul_assoc] at h1
  rw [hw, hw, hπ ((c * a 0) • w) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (ha 0)),
    hπ (a 0 • w) fun i => Ideal.mul_mem_right _ _ (ha 0), hsm, hsm, map_mul, hab'] at h1
  exact h1

end GlobalTheory.LineUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLastValuationNeOfRankZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.MiStar.normLast_valuation : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (S A L : HSp D) (o : OrthDec S A L), 0 < S.rank → S.gram = 1 → ∀ (ζ : Fin L.rank → D.host.E) (π : D.host.E), (∀ r : Fin S.rank, vecB o ζ r = if r.1 + 1 = S.rank then π else 0) → valuation k (p.pr (incA D π)) = valuation k ((q.1 : 𝒪[k]) : k) → valuation k (p.pr (incA D (star π))) = 1 → valuation k (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ))) = valuation k ((q.1 : 𝒪[k]) : k) := by
  intro D k _ _ _ _ p q S A L o hpos hS ζ π hv h1 h2
  have key : star ζ ⬝ᵥ L.gram *ᵥ ζ = star π * π := by
    have hB := o.isoB
    rw [hS, Matrix.mul_one] at hB
    rw [← hB, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hfun : o.iB *ᵥ ζ = fun r : Fin S.rank => if r.1 + 1 = S.rank then π else 0 := by
      funext r; exact hv r
    rw [hfun]
    let r0 : Fin S.rank := ⟨S.rank - 1, by omega⟩
    have hr : ∀ r : Fin S.rank, (r.1 + 1 = S.rank) ↔ r = r0 := by
      intro r; constructor
      · intro h; ext; simp [r0]; omega
      · intro h; subst h; simp [r0]; omega
    simp only [dotProduct, Pi.star_apply, hr]
    simp [apply_ite star]
  rw [key, map_mul, map_mul, map_mul, h2, h1, one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadingVectorFixedByClassStabiliserCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readingVector_fixed_by_class_stabiliser_character : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∀ (c : (I.stX a).Cl) (w : Formalism.L2.DIV.Pol ℂ (I.rec7 l Z).what₂.Tau (B.R.N B.R.m - 1)), w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT → (∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w) → ∀ s : (I.stX a).Stab c, w = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ • Formalism.L2.DIV.rhoP (I.perIn u a).sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) ((I.stX a).gam c.1 s.1)) w := by
  first | exact @GlobalTheory.AdForm.StabInv.reading_stab_inv | exact GlobalTheory.AdForm.StabInv.reading_stab_inv | (intros; apply GlobalTheory.AdForm.StabInv.reading_stab_inv <;> assumption)
end

