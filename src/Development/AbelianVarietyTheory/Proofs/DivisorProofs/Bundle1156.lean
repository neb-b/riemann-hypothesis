module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import ReciprocityTheory.Hypotheses.GalCoh
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.Bundle0003
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0962
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlobalSectionsDimNefPowTensorAmpleIsBi
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.NefGrowth

section SlopeTestRemainingChoices

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

theorem isLocallyNoetherian_of_isProjOver (hp : IsProjOver (strHom k (X := X))) :
    IsLocallyNoetherian X := by
  obtain ⟨N, ι, _, h⟩ := hp
  have : LocallyOfFiniteType (strHom k (X := X)) := h ▸ inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (strHom k X)

theorem lineBundleGlobalSectionsDim_eq_zero_of_isEmpty [IsEmpty X] (L : LB X) : lbH0 k L = 0 := by
  have : Subsingleton (coh (twist (structureModule X) L) 0) := by
    refine ⟨fun x y => ?_⟩
    have h : ∀ z : coh (twist (structureModule X) L) 0, z = 0 := fun z => by
      rw [← one_smul Γ(X, ⊤) z, Subsingleton.elim (1 : Γ(X, ⊤)) 0, zero_smul]
    rw [h x, h y]
  exact hdim_eq_zero_of_subsingleton k 0

theorem lineBundleGlobalSectionsDim_le_of_injective_section_mul [IsLocallyNoetherian X] {N A B : LB X} (hN : N.IsLB)
    (hA : A.IsLB) (hB : B.IsLB) (e : cls N hN = cls A hA + cls B hB) (s : B.Sec)
    (hs : Mono (cutHom (structureModule X) hB s))
    (hfin : Module.Finite k (coh (twist (structureModule X) N) 0)) : lbH0 k A ≤ lbH0 k N := by
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule X) hA hB hN e
  have := Twist.isQuasicoherent_twist (F := structureModule X) hA
  have : Mono (Twist.secHom (twist (structureModule X) A) s) := by
    rw [mono_secHom_iff _ hB, Twist.assPoints_twist hA, ← mono_cutHom_iff _ hB]
    exact hs
  exact LinearMap.finrank_le_finrank_of_injective
    (cohOn.map_zero_injective_of_mono k ⊤ (Twist.secHom (twist (structureModule X) A) s ≫ i.hom))

end SlopeTestRemainingChoices

open GlobalTheory.Published

theorem lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0})
    [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F (X := Z)) → topologicalKrullDim Z ≤ d →
    ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  intro hNum F _ Z _ d hp hd L A hL hA
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact ⟨0, .of_forall fun m => by rw [lineBundleGlobalSectionsDim_eq_zero_of_isEmpty]; simp⟩
  have := isLocallyNoetherian_of_isProjOver hp
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim Z = e := by
    have h0 : topologicalKrullDim Z ≠ ⊥ := topologicalKrullDim_eq_bot_iff.not.2 (not_isEmpty_of_nonempty Z)
    revert h0 hd
    generalize topologicalKrullDim Z = D
    intro hd h0
    induction D using WithBot.recBotCoe with
    | bot => exact absurd rfl h0
    | coe D =>
      induction D using ENat.recTopCoe with
      | top =>
        have h' : (⊤ : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast hd
        exact absurd (top_le_iff.1 h') (ENat.coe_ne_top d)
      | coe n => exact ⟨n, rfl⟩
  have hed : e ≤ d := by
    rw [he] at hd
    exact_mod_cast hd
  have hLA : IsNef F (tens L A) := hL.tens hA.isNef hA
  have ht := hNum.2.2.tendsto hp he hLA
  set c : ℝ := (topSelfIntersection F (tens L A) e : ℝ) / e.factorial
  have hb := ht.eventually (gt_mem_nhds (lt_add_one c))
  have hcut : ∀ᶠ m : ℕ in atTop,
      ∃ t : (lbPow A (m - 1)).Sec, Mono (cutHom (structureModule Z) (isLB_lbPow hA.isLB (m - 1)) t) :=
    (tendsto_sub_atTop_nat 1).eventually (hA.eventually_exists_mono_cutHom_pow (structureModule Z))
  refine ⟨|c| + 1, ?_⟩
  filter_upwards [hcut, hb, eventually_ge_atTop 1] with m ⟨t, hts⟩ hm hm1
  have hcls : cls _ (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m) =
      cls _ (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) + cls _ (isLB_lbPow hA.isLB (m - 1)) := by
    rw [cls_lbPow (isLB_tens hL.isLB hA.isLB), cls_tens hL.isLB hA.isLB,
      cls_tens (isLB_lbPow hL.isLB m) hA.isLB, cls_lbPow hL.isLB, cls_lbPow hA.isLB]
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, add_smul, one_smul, smul_add]
    abel
  have h1 := lineBundleGlobalSectionsDim_le_of_injective_section_mul (k := F) (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m)
    (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) (isLB_lbPow hA.isLB (m - 1)) hcls t hts
    (finite_coh_zero_twist_of_isProjOver (algebraMap_eq_strHom F Z) hp
      (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m))
  have hmpos : (0 : ℝ) < (m : ℝ) ^ e := by positivity
  have h2 : (lbH0 F (lbPow (tens L A) m) : ℝ) ≤ (c + 1) * (m : ℝ) ^ e :=
    ((div_lt_iff₀ hmpos).1 hm).le
  have h3 : (m : ℝ) ^ e ≤ (m : ℝ) ^ d := pow_le_pow_right₀ (by exact_mod_cast hm1) hed
  calc (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ lbH0 F (lbPow (tens L A) m) := by exact_mod_cast h1
    _ ≤ (c + 1) * (m : ℝ) ^ e := h2
    _ ≤ (|c| + 1) * (m : ℝ) ^ e := by gcongr; exact le_abs_self c
    _ ≤ (|c| + 1) * (m : ℝ) ^ d := by gcongr

end GlobalTheory.NefGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberNonnegOfAmple
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_nonneg_of_isAmpleLB_of_isProjOver :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)],
      IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) →
        ∀ P : Fin d → LB X, (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F P := by
  intro k _ _ X _ hp d
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hd P _
    rw [interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k hd]
    exact Nat.cast_nonneg _
  | succ d ih =>
    intro F _ hd P hP
    obtain ⟨n, hn, s, hs, -⟩ := (hP 0).exists_mono_cutHom F
    have hL := isLB_lbPow (hP 0).isLB n
    have h1 := ih (cut F hL s) (suppDim_cut_le F hL s hd) (Fin.tail P) fun i => hP i.succ
    rw [← interNum_cons_eq_interNum_cut hL s (P := Fin.tail P) (fun i => (hP i.succ).isLB)
      (finiteCohTwists_of_isProjOver hf F hp)] at h1
    have h2 := (diffVanish_chiPic_of_isProjOver hf F hp hd).interNum_update_of_cls_eq_zsmul
      (L := P) (by simp) (fun i => (hP i).isLB) 0 hL (hP 0).isLB (n : ℤ)
      (by rw [cls_lbPow (hP 0).isLB, natCast_zsmul])
    have e : Function.update P 0 (lbPow (P 0) n) =
        (Fin.cons (lbPow (P 0) n) (Fin.tail P) : Fin (d + 1) → LB X) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Fin.tail]
    rw [Function.update_eq_self, e] at h2
    rw [h2] at h1
    exact nonneg_of_mul_nonneg_right h1 (Nat.cast_pos.2 hn)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvPowAddNormSqComplexSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory.ComplexSpaceIntegral

theorem lintegral_inv_pow_add_sum_norm_sq :
    ∀ (n m : ℕ) (a : ℝ), 0 < a → ∫⁻ v : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖v i‖ ^ 2) ^ (n + m + 1))⁻¹)
      = ENNReal.ofReal (Real.pi ^ n * m.factorial / ((n + m).factorial * a ^ (m + 1))) := by
  intro n
  induction n with
  | zero =>
    intro m a ha
    rw [lintegral_unique]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add, pow_zero, one_mul]
    have : (volume : Measure (Fin 0 → ℂ)) univ = 1 := by
      rw [MeasureTheory.volume_pi, Measure.pi_univ]; simp
    rw [this, mul_one]
    congr 1
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  | succ n ih =>
    intro m a ha
    have e := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0
    rw [← (e.symm).lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm.measurableEmbedding]
    rw [MeasureTheory.Measure.volume_eq_prod]
    rw [lintegral_prod]
    swap
    · apply Measurable.aemeasurable
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.inv
      apply Measurable.pow_const
      apply Measurable.add measurable_const
      apply Finset.measurable_sum
      intro i _
      apply Measurable.pow_const
      apply Measurable.norm
      exact (measurable_pi_apply i).comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm.measurable
    have inner : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm (z, w) i‖ ^ 2) ^ (n + 1 + m + 1))⁻¹)
        = ENNReal.ofReal (Real.pi ^ n * (m+1).factorial / (n + (m+1)).factorial) * ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹) := by
      intro z
      have hz : 0 < a + ‖z‖ ^ 2 := by positivity
      have key := ih (m+1) (a + ‖z‖ ^ 2) hz
      have hsum : ∀ w : Fin n → ℂ, a + ∑ i, ‖(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm (z, w) i‖ ^ 2
          = a + ‖z‖ ^ 2 + ∑ i, ‖w i‖ ^ 2 := by
        intro w
        rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.sum_univ_succ]
        simp [Fin.insertNthEquiv, add_assoc]
      simp_rw [hsum]
      have hexp : n + 1 + m + 1 = n + (m + 1) + 1 := by ring
      rw [hexp, key, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show m + 1 + 1 = m + 2 by ring]
      have hf : ((n + (m+1)).factorial : ℝ) ≠ 0 := by positivity
      have hp : (a + ‖z‖ ^ 2) ^ (m + 2) ≠ 0 := by positivity
      field_simp
    simp_rw [inner]
    rw [lintegral_const_mul _ (by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.inv
      apply Measurable.pow_const
      exact measurable_const.add (measurable_norm.pow_const 2))]
    rw [GlobalTheory.T.lintegral_complex_inv_pow_add_norm_sq m a ha, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : ((n + (m+1)).factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((n + 1 + m).factorial : ℝ) ≠ 0 := by positivity
    have h3 : (n + (m+1)) = n + 1 + m := by ring
    rw [h3, Nat.factorial_succ m]
    push_cast
    have ha' : a ^ (m+1) ≠ 0 := by positivity
    field_simp
    ring

end GlobalTheory.ComplexSpaceIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSiegelTorusConeModulusLtTop
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelSet

theorem lintegral_cone_modulus_lt_top_of_witt : ∀ (F : Type) [Field F] [NumberField F] (m r n : ℕ) (c : ℝ), 0 < c → (r = 0 ∨ n + r < m) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * (2 * n))) * ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F m t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ m r n c hc h
  rcases h with h | h
  · subst h
    simp only [GlobalTheory.SiegelSet.modulus, Finset.univ_eq_empty, Finset.prod_empty, mul_one, inv_one, ENNReal.ofReal_one,
      lintegral_const, one_mul]
    rw [Measure.restrict_apply MeasurableSet.univ]
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) _ < ⊤
    rw [Measure.pi_of_empty]
    exact measure_lt_top _ _
  · exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top F m r (2 * n) hc (by omega)

end GlobalTheory.SiegelSet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocfinHolds
section
namespace GlobalTheory.Laid

theorem locfin_holds : ReciprocityTheory.Gal.LocalFiniteness := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness

end GlobalTheory.Laid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem lcAt_iff_of_isLogEqn : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ : X → ℚ) (η : RatForms p n) (x : X) (m : ℕ) (g : X.functionFieldˣ), η ≠ 0 → 0 < m → IsLogEqn p Γ η x m g → (LcAt p n Γ x ↔ ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g) := by
  intro X _ _ _ p n hp hn Γ η x m g hη hm h
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  exact ⟨fun ⟨_, _, _, h₁, h₂, h₃, h₄⟩ E hE => discrep_eq hn h₁ hη h₂ hm h₃ h hE ▸ h₄ E hE,
    fun h' => ⟨η, m, g, hη, hm, h, h'⟩⟩

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeSpaceHolomorphicKModuleKilled
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.LowKType

theorem lowKSub_mem_of_forall {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {lam : Fin n → ℝ} {D : Submodule ℂ H} (Q : Submodule ℂ D)
    (hD : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → S ≤ D)
    (hQ : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → ∀ y : D, (y : H) ∈ S → y ∈ Q) :
    ∀ y : D, (y : H) ∈ lowKSub ε lam σ → y ∈ Q := by
  have hle : lowKSub ε lam σ ≤ Q.map D.subtype := by
    unfold lowKSub
    refine sSup_le fun S hS x hx => ?_
    exact ⟨⟨x, hD S hS hx⟩, hQ S hS ⟨x, hD S hS hx⟩ hx, rfl⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hle hy
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

end GlobalTheory.LowKType

open GlobalTheory.LowKType in
theorem GlobalTheory.HolDS.lowKSub_kMod : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → lowKSub ε lam σ ≤ D ∧ KStab ε E ((lowKSub ε lam σ).comap D.subtype) ∧ (lowKSub ε lam σ).comap D.subtype ≠ ⊥ ∧ ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ (lowKSub ε lam σ).comap D.subtype, E b a x = 0 := by
  intro n ε H _ _ σ D E lam hHC hch hDS hK
  obtain ⟨hC, _, hU, hI, _, hEx, hmin⟩ := hDS
  have hT := fun μ S hS => _root_.GlobalTheory.kTypeInKFinite n ε H σ D E hC hU hI hK μ S hS
  have hD : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → S ≤ D := fun S hS => (hT _ S hS).1
  have hM : IsMin ε E lam := fun μ x hx0 hx => by
    obtain ⟨T, hT'⟩ := hK.ty μ x hx0 hx
    exact hmin μ T hT'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lowKSub
    exact sSup_le fun S hS => hD S hS
  · intro a b hab v hv
    exact lowKSub_mem_of_forall ((lowKSub ε lam σ).comap D.subtype |>.comap (E a b)) hD
      (fun S hS y hy => by
        have h3 := (hT _ S hS).2.2.1 a b hab y hy
        show ((E a b y : D) : H) ∈ lowKSub ε lam σ
        exact (le_sSup hS : S ≤ lowKSub ε lam σ) h3) v hv
  · obtain ⟨S, hS⟩ := hEx
    obtain ⟨v, hv0, hvS, _⟩ := hK.hw _ S hS
    intro hbot
    have hv : v ∈ (lowKSub ε lam σ).comap D.subtype := (le_sSup hS : S ≤ lowKSub ε lam σ) hvS
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  · intro a b ha hb x hx
    exact (lowKSub_mem_of_forall (LinearMap.ker (E b a)) hD
      (fun S hS y hy => by
        have h := hT _ S hS
        haveI := h.2.1
        exact _root_.GlobalTheory.HolDS.pMinus_kills_lowest n ε D E lam hK.gl hK.unit hHC.1 hch hM (S.comap D.subtype) h.2.1 h.2.2.1 h.2.2.2
          a b ha hb y hy) x hx : x ∈ LinearMap.ker (E b a))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LpDimLocParT
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep
  GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT

theorem lpDim_locParT (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (π : CG E a) (h : IsPlaceOver A w) : (locParT hT π h).lpDim = a := by
  obtain ⟨_, _, H⟩ := isRecT_locRecT hT h
  exact H.dim _

end GlobalTheory.CuspRep.ParLawsT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFixesLowRankProjectorOfFixesRationalKernelStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_fixes_lowRankProjector_of_fixes_rationalKernel : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E), B₀ * A₀ = 1 → ∀ G : Matrix (Fin M) (Fin M) (R ⊗[F] E), (∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) → G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) := by
  first | exact @GlobalTheory.RatFix.ratfix | exact GlobalTheory.RatFix.ratfix | (intros; apply GlobalTheory.RatFix.ratfix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerRestrictedProductIff
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerAbs

theorem mem_twCent_iff_forall_comp : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → ∀ (δ x : X), x ∈ twCent θ δ ↔ ∀ v, pf v x ∈ twCent (θv v) (pf v δ) := by
  intro X V Y _ _ _ _ pf K hX θ θv hθ δ x
  simp only [twCent, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h v
    have := congrArg (pf v) h
    simpa [map_mul, hθ] using this
  · intro h
    apply hX.ext
    · intro w; exact isEmptyElim w
    · intro v
      simpa [map_mul, hθ] using h v

end GlobalTheory.EulerAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingKernelEqOneAddLowRankOfUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fixing_kernel_eq_oneAddLowRank_of_unitary : ∀ (R : Type) [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) R), IsUnit J.det → ∀ (A : Matrix (Fin M) (Fin 2) R) (B : Matrix (Fin 2) (Fin M) R) (H : Matrix (Fin 2) (Fin 2) R), B * A = 1 → Formalism.UG.cT c A * J = H * B → J * A = Formalism.UG.cT c B * H → ∀ G : Matrix (Fin M) (Fin M) R, Formalism.UG.cT c G * J * G = J → G * (1 - A * B) = 1 - A * B → G = emb A B (B * G * A) ∧ Formalism.UG.cT c (B * G * A) * H * (B * G * A) = H := by
  first | exact @GlobalTheory.PlaneSU.eq_emb_of_fix | exact GlobalTheory.PlaneSU.eq_emb_of_fix | (intros; apply GlobalTheory.PlaneSU.eq_emb_of_fix <;> assumption)
end

