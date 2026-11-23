module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjReferenceFrameOnFlagBasisModLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RefProjFlag

open Formalism.L2.SG.PoincareInHH.Cut.GU

variable {D : D7} (X : HidaSetting D)

theorem hA_zero_right' (u : VA X.B.I) : hA X.B.I u 0 = 0 := by
  have h := Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right X.B.I u 0 0
  rwa [zero_smul, zero_mul] at h

theorem intsmul_Lf' {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {y : VA X.B.I}
    (hy : y ∈ X.B.I.Lf) : t • y ∈ X.B.I.Lf :=
  X.B.I.Lf.smul_mem ⟨t, ht⟩ hy

theorem orthProjReferenceFrame_mem_finiteAdelicLattice {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf := by
  have he : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hf : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  refine sub_mem (add_mem (Submodule.sum_mem _ fun a _ => ?_) (Submodule.sum_mem _ fun a _ => ?_)) ?_
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (hf a) hy) (he a)
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (he a) hy) (hf a)
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I hz hy) hz

theorem orthProjReferenceFrame_mem_levelMultiple_of_coeff_congr {y : VA X.B.I} (hf : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) y))
    (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) y)) (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 y)) :
    GlobalTheory.ScalW.prj0 X y ∈ mL X.B.I X.B.g :=
  sub_mem (add_mem (sum_mL X _ _ hf fun a => (X.vectorsInLattice.1 a).1) (sum_mL X _ _ he fun a => (X.vectorsInLattice.1 a).2))
    (smul_mL X hz X.vectorsInLattice.2.1)

theorem sub_orthProjReferenceFrame_mem_levelMultiple_of_congr (b : VA X.B.I) (α β : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (γ : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hb : b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0) ∈ mL X.B.I X.B.g)
    (hα : ∀ a, ZMod' X.B.I X.B.g (α a - hA X.B.I (X.f0 a) b))
    (hβ : ∀ a, ZMod' X.B.I X.B.g (β a - hA X.B.I (X.e0 a) b))
    (hγ : ZMod' X.B.I X.B.g (γ - hA X.B.I X.z0 b)) : GlobalTheory.ScalW.prj0 X b - b ∈ mL X.B.I X.B.g := by
  have e : GlobalTheory.ScalW.prj0 X b - b = (γ - hA X.B.I X.z0 b) • X.z0
      - (b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0))
      - ∑ a, (α a - hA X.B.I (X.f0 a) b) • X.e0 a - ∑ a, (β a - hA X.B.I (X.e0 a) b) • X.f0 a := by
    simp only [GlobalTheory.ScalW.prj0, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [e]
  exact sub_mem (sub_mem (sub_mem (smul_mL X hγ X.vectorsInLattice.2.1) hb) (sum_mL X _ _ hα fun a => (X.vectorsInLattice.1 a).1))
    (sum_mL X _ _ hβ fun a => (X.vectorsInLattice.1 a).2)

theorem orthProjReferenceFrame_flagE_sub_mem_levelMultiple (c : Fin D.R.rS) : GlobalTheory.ScalW.prj0 X (X.e0 c) - X.e0 c ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ (fun a => if a = c then sigA X.B.I 1 else 0) 0 0 ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Zsw_ite X 1 (X.gramIntegral c a).2.2
  · intro a; exact Z0 X (X.gramIntegral a c).1
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).1)

theorem orthProjReferenceFrame_flagF_sub_mem_levelMultiple (c : Fin D.R.rS) : GlobalTheory.ScalW.prj0 X (X.f0 c) - X.f0 c ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ 0 (fun a => if a = c then 1 else 0) 0 ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.gramIntegral a c).2.1
  · intro a; exact Zswap X (X.gramIntegral a c).2.2
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).2)

theorem orthProjReferenceFrame_flagZ_sub_mem_levelMultiple : GlobalTheory.ScalW.prj0 X X.z0 - X.z0 ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ 0 0 (-1) ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.formsAtZero.2 a).2
  · intro a; exact Z0 X (X.formsAtZero.2 a).1
  · have := Zneg X X.formsAtZero.1
    rw [neg_add, add_comm] at this
    rwa [sub_eq_add_neg]

theorem orthProjReferenceFrame_middle_mem_levelMultiple (c c' : Fin D.R.k) : GlobalTheory.ScalW.prj0 X (X.bw c + X.bwd c') ∈ mL X.B.I X.B.g := by
  refine orthProjReferenceFrame_mem_levelMultiple_of_coeff_congr X (fun a => ?_) (fun a => ?_) ?_
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g ((X.weightVectorsIntegral c).2.2 a).2.1 ((X.weightVectorsIntegral c').2.2 a).2.2.2
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g ((X.weightVectorsIntegral c).2.2 a).1 ((X.weightVectorsIntegral c').2.2 a).2.2.1
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g (X.weightVectorsIntegral c).1 (X.weightVectorsIntegral c').2.1

theorem flagVec_Lf (j : ℕ) : flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf := by
  unfold flagVec
  split_ifs
  · exact (X.vectorsInLattice.1 _).1
  · exact add_mem (X.vectorsInLattice.2.2 _).1 (X.vectorsInLattice.2.2 _).2
  · exact X.vectorsInLattice.2.1
  · exact (X.vectorsInLattice.1 _).2
  · exact zero_mem _

theorem prj0_flagVec_mem_mL_or_sub_mem_mL : ∀ (D : D7) (X : HidaSetting D), (∀ y ∈ X.B.I.Lf, GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf) ∧
    ∀ j : ℕ, flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf ∧
      (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) ∈ mL X.B.I X.B.g) ∧
      (¬ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k) →
        GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ mL X.B.I X.B.g) := by
  intro D X
  refine ⟨fun y hy => orthProjReferenceFrame_mem_finiteAdelicLattice X hy, fun j => ⟨flagVec_Lf X j, ?_, ?_⟩⟩
  · rintro ⟨h1, h2⟩
    have h3 : ¬ j < D.R.rS := by omega
    have h4 : j - D.R.rS < D.R.k := by omega
    rw [flagVec, dite_eq_right h3, dite_eq_left h4]
    exact orthProjReferenceFrame_middle_mem_levelMultiple X _ _
  · intro h
    unfold flagVec
    split_ifs with h1 h2 h3 h4
    · exact orthProjReferenceFrame_flagE_sub_mem_levelMultiple X _
    · exact absurd ⟨by omega, by omega⟩ h
    · exact orthProjReferenceFrame_flagZ_sub_mem_levelMultiple X
    · exact orthProjReferenceFrame_flagF_sub_mem_levelMultiple X _
    · simp only [GlobalTheory.ScalW.prj0, hA_zero_right', zero_smul, Finset.sum_const_zero, add_zero, sub_zero]
      exact zero_mem _

end GlobalTheory.RefProjFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvd
section
open NumberField IsDedekindDomain Formalism.BasicNotions
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormPlaces

theorem places_dvd_iff (D : Formalism.BasicNotions.D7) (π π' : 𝓞 D.host.E) (T : ℕ)
    (hc : (π' : D.host.E) = star (π : D.host.E)) (hT : π * π' = (T : 𝓞 D.host.E)) (hπ : π ≠ 0)
    (x : HeightOneSpectrum (𝓞 D.host.F)) :
    (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x := by
  have hmap : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (T : 𝓞 D.host.F) = (T : 𝓞 D.host.E) := map_natCast _ _
  constructor
  · intro hx
    have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) :=
      FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E)
    have hker : RingHom.ker (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ x.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le
    haveI := x.isPrime
    obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal (𝓞 D.host.E))
      (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]; exact hker)
    have hQb : Q ≠ ⊥ := by
      rintro rfl
      apply x.ne_bot
      rw [← hQ, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
    let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQp, hQb⟩
    have hw : w.under (𝓞 D.host.F) = x := HeightOneSpectrum.ext hQ
    have hTw : π * π' ∈ w.asIdeal := by
      rw [hT, ← hmap]
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (T : 𝓞 D.host.F) ∈ Q
      rw [← Ideal.mem_comap]
      change (T : 𝓞 D.host.F) ∈ Ideal.under (𝓞 D.host.F) Q
      rw [hQ]; exact hx
    rcases w.isPrime.mem_or_mem hTw with h | h
    · exact ⟨w, (Formalism.L2.Col.mem_divs hπ w).2 h, hw⟩
    · refine ⟨GlobalTheory.IdemSupport.cP w, (Formalism.L2.Col.mem_divs hπ _).2 ?_, (GlobalTheory.IdemSupport.under_cP w).trans hw⟩
      rw [GlobalTheory.IdemSupport.mem_cP]
      have : GlobalTheory.IdemSupport.cO D π = π' := by
        apply RingOfIntegers.ext
        rw [GlobalTheory.IdemSupport.cO_coe, hc]
      rw [this]; exact h
  · rintro ⟨w, hw, rfl⟩
    have h1 : π ∈ w.asIdeal := (Formalism.L2.Col.mem_divs hπ w).1 hw
    have h2 : (T : 𝓞 D.host.E) ∈ w.asIdeal := hT ▸ w.asIdeal.mul_mem_right π' h1
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (T : 𝓞 D.host.F) ∈ w.asIdeal
    rw [hmap]; exact h2

end GlobalTheory.NormPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalLevelFock

theorem levW_fix_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, ∀ k ∈ levW R i, ω (1, k) (ptAt R i σ BW f Q) = ptAt R i σ BW f Q := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h Q k hk
  have hr : Formalism.L2.DIV.rTup (R.βW i) (R.datWp i P) (finE (Wc D i) k) = 1 := by
    have h2 := hk.2.2
    have e : (R.datWp i R.triv).P.H = ⊥ := rfl
    rw [e] at h2
    exact Subgroup.mem_bot.1 h2
  have hk' : k ∈ levG (Wc D i) (R.βW i) (R.datWp i P) := by
    refine ⟨hk.1, hk.2.1, ?_⟩
    show Formalism.L2.DIV.rTup (R.βW i) (R.datWp i P) (finE (Wc D i) k) ∈ (R.datWp i P).P.H
    rw [hr]; exact Subgroup.one_mem _
  have hchi : levChi (Wc D i) (R.βW i) (R.datWp i P) k = 1 := by
    unfold levChi Formalism.L2.DIV.levFn
    rw [hr, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one]
    have hs : (R.datWp i P).s = 0 := rfl
    have hq : (R.datWp i P).Q = ∅ := rfl
    rw [hs, hq]
    simp
  have hz := GlobalTheory.ZetaLaw.zeta_law R F i t σ s P cμ cη m ω BW f₀ f c io h k hk'
  rw [hchi] at hz
  have hθ : IsInfFam R.θ := h.1.models.inf
  exact (GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ ω hθ h.2.2.2.2.2.1 _ _ _ _ f
    h.2.2.2.2.2.2.2.2.1 1 (Subgroup.one_mem _) k hk.1 1 hz Q).trans (one_smul ℂ _)

end GlobalTheory.PrincipalLevelFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdLocalParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section

namespace GlobalTheory.LevelCut

open GlobalTheory.SplitCut

variable {D : D7}

theorem entry_idAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2


open GlobalTheory.LocWeil.PlaceIdem in
theorem sum_act {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v)
    (y : AE D) (hy : y ∈ idAt D (fun u => u ∈ Set.range v)) :
    (1 - ∑ w, algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w))) * y = 0 := by
  unfold idAt at hy
  obtain ⟨h1, h2⟩ := hy
  have h1' : infPart D y = 0 := h1
  have h2' : ∀ u, u ∉ Set.range v → compAt D u y = 0 := fun u hu => by
    have := (Ideal.mem_iInf.1 h2) ⟨u, hu⟩
    exact (RingHom.mem_ker).mp this
  have h3 := key v hv y h2'
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)) = 0 := by
    rw [finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  have h4 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 :=
    GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h1', mul_zero, RingHom.map_zero])
      (by rw [RingHom.map_mul, h0, zero_mul, RingHom.map_zero])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sub, map_one, map_sum] at h3
  linear_combination h3 + h4

theorem pr_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) :
    q.pr (q.e + cA D q.e) = 1 := by
  have h2 := q.split.2.1
  have ho : q.sec 1 = q.e := by rw [← q.pr.map_one, q.sec_pr, mul_one]
  have p1 : q.pr q.e = 1 := by rw [← ho, q.pr_sec]
  have p2 : q.pr (cA D q.e) = 0 := by rw [← one_mul (q.pr _), ← p1, ← RingHom.map_mul, h2, RingHom.map_zero]
  rw [RingHom.map_add (f := _), p1, p2, add_zero]

theorem exists_coord {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y)
    (A B : Matrix (Fin N) (Fin N) k) (h1 : A * B = 1) (h2 : B * A = 1) : ∃ x : GL Y k, A = F.β * x.val * F.γ := by
  have key : ∀ A B : Matrix (Fin N) (Fin N) k, A * B = 1 → (F.γ * A * F.β) * (F.γ * B * F.β) = 1 := fun A B h => by
    calc (F.γ * A * F.β) * (F.γ * B * F.β) = F.γ * (A * (F.β * F.γ) * B) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h, Matrix.mul_one, F.γβ]
  refine ⟨⟨F.γ * A * F.β, F.γ * B * F.β, key A B h1, key B A h2⟩, ?_⟩
  calc A = (F.β * F.γ) * A * (F.β * F.γ) := by rw [F.βγ, Matrix.mul_one, Matrix.one_mul]
    _ = F.β * (F.γ * A * F.β) * F.γ := by simp only [Matrix.mul_assoc]


open GlobalTheory.LocWeil.PlaceIdem in
theorem exists_parts (V : HSp D) {n : ℕ} (v : Fin n → Pl D) (e : Fin n → AE D) (hv : Function.Injective v)
    (he : ∀ w, ∃ ε, IsPlaceIdem D (v w) ε ∧ e w + cA D (e w) = algebraMap (AF D.host.F) (AE D) ε)
    (g : GA D V) (hg : g ∈ grpAt V (fun u => u ∈ Set.range v)) :
    ∃ h : Fin n → GA D V, (∀ w, SuppAt (e w) V (h w)) ∧
      (∀ w, mt V (h w) = (e w + cA D (e w)) • mt V g + (1 - (e w + cA D (e w))) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      g = ((List.finRange n).map h).prod := by
  set E : Fin n → AE D := fun w => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w)) with hEdef
  have hE : ∀ w, e w + cA D (e w) = E w := fun w => by
    obtain ⟨ε, hε, h⟩ := he w
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ w, E w * E w = E w := fun w => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ w, cA D (E w) = E w := fun w => cA_algebraMap _
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hww (hv h)), map_zero]
  choose h hh using fun w => cut_exists V g (E w) (hEE w) (hEc w)
  refine ⟨h, fun w i j => ?_, fun w => ?_, ?_⟩
  · rw [hE w, hh w]
    exact idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j
  · rw [hE w, hh w]
  · apply GlobalTheory.SplitCut.mt_injective
    rw [mt_list_prod V h E _ hh hEo _ (List.nodup_finRange n), ← Fin.sum_univ_def]
    exact exists_widePullback_of_iteratedLine _ _ fun i j => sum_act v hv _ (entry_idAt V _ g hg i j)

theorem prod_local_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G →
    ∀ (j : ℕ) (k : GA D (c.V j)), k ∈ grpAt (c.V j) (· ∈ v.gP) → ∃ h : Fin n → GA D (c.V j),
      (∀ i b hb, ∃ x, (G i).Mat j b hb k x ∧ (ofSplit (G i).q).IsLoc ((G i).FY j b hb) (h i) x) ∧
        k = ((List.finRange n).map h).prod := by
  intro D c v n G hG j g hg
  have hP : (fun u => u ∈ v.gP) = fun u => u ∈ Set.range (fun i => (G i).q.v) := by
    funext u
    rw [hG.places u]
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  rw [hP] at hg
  obtain ⟨h, h1, h2, h3⟩ := exists_parts (c.V j) (fun i => (G i).q.v) (fun i => (G i).q.e) hG.inj
    (fun i => (G i).q.above) g hg
  refine ⟨h, fun i b hb => ?_, h3⟩
  have hm : ∀ a a' : GA D (c.V j), a * a' = 1 →
      (mt (c.V j) a).map (G i).q.pr * (mt (c.V j) a').map (G i).q.pr = 1 := fun a a' ha => by
    rw [← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, ha, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  obtain ⟨x, hx⟩ := exists_coord ((G i).FY j b hb) _ _ (hm g g⁻¹ (mul_inv_cancel g)) (hm g⁻¹ g (inv_mul_cancel g))
  refine ⟨x, hx, h1 i, ?_⟩
  change (mt (c.V j) (h i)).map (G i).q.pr = _
  rw [h2 i, GlobalTheory.GfCut.map_idem, pr_sum, one_smul, sub_self, zero_smul, add_zero]
  exact hx

end GlobalTheory.LevelCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOfSupportedAtOrthogonalSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffPlaceRed

theorem pr_add_conj_eq_zero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (a : Formalism.L2.Theta.AE D)
    (h : a * (q.e + cA D q.e) = 0) : q.pr a = 0 := by
  have h1 : q.pr q.e = 1 := by
    have h2 := q.pr_sec 1
    have h3 := q.sec_pr 1
    rw [map_one, mul_one] at h3
    rwa [h3] at h2
  have h4 : q.pr (cA D q.e) = 0 := by
    have := congrArg q.pr q.split.2.1
    rwa [map_mul, h1, one_mul, map_zero] at this
  have := congrArg q.pr h
  rwa [map_mul, map_add, h1, h4, add_zero, mul_one, map_zero] at this

theorem bc_eq_one_of_isRed {S κ k : Type} [CommRing S] [CommRing κ] [Field k] [ValuativeRel k] {φ : S →+* κ}
    {ψ : S →+* k} (hred : GlobalTheory.FunObj.Comparison₂.IsRed φ ψ) {n : ℕ} (m : GL (Fin n) S) (h : Formalism.UG.bc ψ m = 1) :
    Formalism.UG.bc φ m = 1 := by
  apply Units.ext
  ext i j
  have h6 : ψ (m.val i j) = (1 : Matrix (Fin n) (Fin n) k) i j :=
    congrArg (fun x : GL (Fin n) k => x.val i j) h
  show φ (m.val i j) = (1 : Matrix (Fin n) (Fin n) κ) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq] at h6 ⊢
    have h7 := (hred.ker (m.val i i - 1)).2 (by
      rw [map_sub, map_one, h6, sub_self, map_zero]; exact zero_lt_one)
    rwa [map_sub, map_one, sub_eq_zero] at h7
  · rw [Matrix.one_apply_ne hij] at h6 ⊢
    refine (hred.ker (m.val i j)).2 ?_
    rw [h6, map_zero]; exact zero_lt_one

theorem bc_comp_eq_one {S A k : Type} [CommRing S] [CommRing A] [CommRing k] (ι : S →+* A) (π : A →+* k) {n : ℕ}
    (m : GL (Fin n) S) (β x : GL (Fin n) A) (hx : β * Formalism.UG.bc ι m * β⁻¹ = x) (h : Formalism.UG.bc π x = 1) :
    Formalism.UG.bc (π.comp ι) m = 1 := by
  rw [← hx, map_mul, map_mul, map_inv, mul_inv_eq_one, mul_eq_left] at h
  exact h

theorem redFn_eq_one_of_suppAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (e : Formalism.L2.Theta.AE D), (e + cA D e) * (q.e + cA D q.e) = 0 → ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (g : GA D V), Formalism.L2.Theta.SuppAt e V g → finE V g ∈ St β → redFn β PP (finE V g) = 1 := by
  intro D k _ _ _ _ q PP hq e he V β g hg hst
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hq
  obtain ⟨m, hm⟩ := hst
  have h0 : q.pr (e + cA D e) = 0 := pr_add_conj_eq_zero q _ he
  have h1 : (finE V g).val.map π' = 1 := by
    ext i j
    have h2 : q.pr ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
      rw [← hg i j, map_mul, h0, zero_mul]
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h2
    show π' (toEAf D (Formalism.L2.Theta.mt V g i j)) = _
    rw [hπ, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : Formalism.UG.bc π' (finE V g) = 1 := Units.ext h1
  rw [← hm, redFn_frGL]
  exact bc_eq_one_of_isRed hred m (bc_comp_eq_one _ π' m β _ hm h3)

end GlobalTheory.OffPlaceRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarBlendProjectionMemStabilizerAndCommutes
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalW

theorem hMat_mem_hfin_comm : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (h : X.B.I.Gf), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) → GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u → X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c → h ∈ Hfin X u ∧ ∀ h' ∈ Hfin X u, h * h' = h' * h := by
  intro D X u c h hef hz hh
  have hfixV : ∀ v ∈ fixSet X u, GlobalTheory.ScalW.prj X u (incl X.B.I v) = incl X.B.I v := by
    rintro v ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hv)
    · exact (hef a).1
    · exact (hef a).2
    · rw [Set.mem_singleton_iff.1 hv]; exact hz
  have hmem : h ∈ Hfin X u := by
    intro v hv
    show X.B.I.fmat h *ᵥ incl X.B.I v = incl X.B.I v
    rw [hh, hMat_mulVec, hfixV v hv, ← add_smul, add_sub_cancel, one_smul]
  refine ⟨hmem, fun h' hh' => ?_⟩
  have hg : ∀ v ∈ fixSet X u, X.B.I.fmat h' *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u ⟨h', hh'⟩
  have hgi : ∀ v ∈ fixSet X u, X.B.I.fmat h'⁻¹ *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix_inv X u ⟨h', hh'⟩
  have hE := Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix X u
  have hF := Formalism.L2.SG.PoincareInHH.Cut.fR_mem_fix X u
  have hZ := Formalism.L2.SG.PoincareInHH.Cut.zR_mem_fix X u
  have hmv : ∀ v, v ∈ fixSet X u → ∀ y, hA X.B.I (incl X.B.I v) (X.B.I.fmat h' *ᵥ y) = hA X.B.I (incl X.B.I v) y := by
    intro v hv y
    rw [GlobalTheory.St.G.FrameClose.hA_move, hgi v hv]
  have hprj : ∀ y, prj X u (X.B.I.fmat h' *ᵥ y) = prj X u y := by
    intro y
    simp only [prj, eV, fV, zV, hmv _ (hE _), hmv _ (hF _), hmv _ hZ]
  have hprj2 : ∀ y, X.B.I.fmat h' *ᵥ prj X u y = prj X u y := by
    intro y
    simp only [prj, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, eV, fV, zV,
      hg _ (hE _), hg _ (hF _), hg _ hZ]
  have hM : X.B.I.fmat (h * h') = X.B.I.fmat (h' * h) := by
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, hh]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMat_mulVec, hMat_mulVec, hprj, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hprj2]
  exact Subtype.ext (Units.ext hM)

end GlobalTheory.ScalW
end

