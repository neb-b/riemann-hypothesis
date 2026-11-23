module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOfContinuousRepresentative
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.CuspRep

theorem isCuspFun_of_mem_L2cusp : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ F ∈ GlobalTheory.Cusp.L2cusp V μ, ∀ ψ : GA D V → ℂ, Continuous ψ → LeftInv (GQ V) ψ → lift (GQ V) F =ᵐ[μ] ψ → IsCuspFun V ψ := by
  intro D V μ _ _ F hF ψ hψc hψl hFψ
  refine (GlobalTheory.Cusp.isCuspFun_iff hψl).2 fun W hW => ?_
  have hc := GlobalTheory.Cusp.cocompact_single (D := D) hW
  have := hc.isProbabilityMeasure
  have hm : StronglyMeasurable (lift (GQ V) F) := (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  have h1 : GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) (lift (GQ V) F) =ᵐ[μ] 0 := by
    refine GlobalTheory.CuspAE.constTermOn_ae_eq_zero hc (closure_mono ?_ hF)
    rintro F' ⟨φ, hφ, e⟩
    exact ⟨φ, hφ.1, hφ.2.1, (GlobalTheory.Cusp.isCuspFun_iff hφ.2.1).1 hφ.2.2 W hW, e⟩
  have hcont := hc.continuous_constTermOn hψl hψc
  have h2 : GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) ψ =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hcont.locallyIntegrable fun S hS => ?_
    rw [GlobalTheory.CuspAE.setIntegral_constTermOn hc hψl hψc.stronglyMeasurable hψc.locallyIntegrable hS]
    calc _ = ∫ q, ∫ y in S, lift (GQ V) F (((q.out : GlobalTheory.Cusp.NA (.single hW)) : GA D V) * y) ∂μ
            ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA (.single hW)) :=
          integral_congr_ae (.of_forall fun q => integral_congr_ae (ae_restrict_of_ae
            ((measurePreserving_mul_left μ ((q.out : GlobalTheory.Cusp.NA (.single hW)) : GA D V)).quasiMeasurePreserving.ae
              hFψ.symm)))
      _ = ∫ y in S, GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) (lift (GQ V) F) y ∂μ :=
          (GlobalTheory.CuspAE.setIntegral_constTermOn hc (leftInv_lift F) hm (GlobalTheory.CuspAE.locallyIntegrable_lift F) hS).symm
      _ = 0 := by rw [integral_congr_ae (ae_restrict_of_ae h1)]; simp
  exact (hcont.ae_eq_iff_eq μ continuous_const).1 h2

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesMultiplicity
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TestFnCusp

theorem hypH_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (h : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ := by
  intro a ha har
  obtain ⟨v, hv⟩ := h.2 a ha har
  refine ⟨v, fun y hy => hv y fun g hg => hy g ?_⟩
  intro i j hij
  by_contra hc
  exact hij (hg i j hc)

theorem isCuspidalOp_tensor : (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ (tensor D.sp.cm.sig V.gram fa ff) := by
  intro hCO hPC D V lam S M T U μa μf μ _ _ fa ff hTD
  obtain ⟨hodd, -, -, hnf, hμ, ha, hb⟩ := hTD
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hμ.haar_loc
  have hT : IsTestFnG M T U μa μf (tensor D.sp.cm.sig V.gram fa ff) := ⟨fa, ff, ha, hb, rfl⟩
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V := hT.isPureTensor.2
  have hU := hPC.2 D V hodd S M T (hypH_of_noFixed T hnf) U μa μf _ hT
  refine hCO D V μ _ hf ?_ ?_
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).1 ν x y).2
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).2 ν x y).2

end GlobalTheory.TestFnCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestFunctionTrace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.ArchTrace

open Formalism.MainNotions.S (IsURepOn UJset IsIrredOn)
open GlobalTheory.Orb (ujMat ujRep frameEquiv)
open GlobalTheory.RealInd (IsIrrAdm groupRep)

section Pull

variable {m : ℕ} (ε : Fin m → Bool) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

theorem ujMat_injective : Function.Injective (ujMat ε) := fun _ _ h => Subtype.ext (Units.ext h)

def matRep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (x : Matrix (Fin m) (Fin m) ℂ) : X →L[ℂ] X := by
  classical exact if h : ∃ g, ujMat ε g = x then π h.choose else 1

theorem matRep_ujMat (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (g : Formalism.REAL.UJ ε) : matRep ε π (ujMat ε g) = π g := by
  have h : ∃ g', ujMat ε g' = ujMat ε g := ⟨g, rfl⟩
  rw [matRep, dite_eq_left h, ujMat_injective ε h.choose_spec]

theorem ujMat_mem_UJset (g : Formalism.REAL.UJ ε) : ujMat ε g ∈ UJset ε := g.2

variable {ε}

theorem matRep_isURepOn (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (hπ : GlobalTheory.OpTrace.IsUnitaryRep π)
    (hs : ∀ x ∈ UJset ε, ∃ g, ujMat ε g = x) : IsURepOn (UJset ε) (matRep ε π) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩
  · rw [← map_one (ujMat ε), matRep_ujMat, map_one]
  · obtain ⟨g, rfl⟩ := hs a ha
    obtain ⟨h, rfl⟩ := hs b hb
    rw [← map_mul, matRep_ujMat, matRep_ujMat, matRep_ujMat, map_mul]
    rfl
  · obtain ⟨g, rfl⟩ := hs a ha
    rw [matRep_ujMat]
    exact hπ.norm_apply g v
  · have hr : UJset ε = Set.range (ujMat ε) :=
      Set.ext fun x => ⟨fun hx => hs x hx, by rintro ⟨g, rfl⟩; exact ujMat_mem_UJset ε g⟩
    rw [hr, continuousOn_iff_continuous_domRestrict]
    let E := (GlobalTheory.Orb.isEmbedding_ujMat ε).toHomeomorph
    have hE : ∀ y, (fun g => π g v) (E.symm y) = matRep ε π (y : Matrix (Fin m) (Fin m) ℂ) v := by
      intro y
      obtain ⟨g, rfl⟩ := E.surjective y
      show π (E.symm (E g)) v = matRep ε π (ujMat ε g) v
      rw [E.symm_apply_apply, matRep_ujMat]
    exact ((hπ.continuous_apply v).comp E.symm.continuous).congr hE

theorem matRep_isIrredOn (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (hπ : GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π) :
    IsIrredOn (UJset ε) (matRep ε π) := fun S hS hinv =>
  hπ.2 S ⟨hS, fun g v hv => by simpa [matRep_ujMat] using hinv _ (ujMat_mem_UJset ε g) v hv⟩

theorem groupRep_matRep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (h : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) (matRep ε π)) :
    groupRep ε h = π := MonoidHom.ext fun g => matRep_ujMat ε π g

end Pull

theorem hasWideGaps_of_gap {r : ℕ} (hr : 0 < r) {lam : Fin r → ℤ} (h : Gap lam) :
    GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.HasWideGaps lam := by
  refine ⟨?_, h⟩
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
  have := h i.castSucc i.succ (by simp)
  push_cast at this
  omega

theorem isHCParam_of_gap {r : ℕ} (hr : Odd r) {lam : Fin r → ℤ} (h : Gap lam) :
    Formalism.QuantumDeterminants.IsHCParam (fun i => (lam i : ℝ)) := by
  refine ⟨Int.cast_strictMono.comp_strictAnti (hasWideGaps_of_gap hr.pos h).1, fun a => ?_⟩
  obtain ⟨k, hk⟩ := hr
  subst hk
  refine ⟨lam a - k, ?_⟩
  push_cast
  ring

end GlobalTheory.ArchTrace

namespace GlobalTheory.ArchTrace

open Formalism.MainNotions.S (IsURepOn UJset IsIrredOn)
open GlobalTheory.Orb (ujMat ujRep frameEquiv IsPseudoCoeff isPseudoCoeff_dsRep_iff exists_frameMat_eq repOp_map)
open GlobalTheory.RealInd (IsIrrAdm groupRep)

theorem trace_pseudoCoeff_arch : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (ρ : D.what₂.Tau) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* (X →L[ℂ] X)), IsIrrUnitary δ → ∃ c, HasTrace (repOp δ (μa (placeOf D ρ)) (fa (placeOf D ρ))) c ∧ (c ≠ 0 → IsUnitEquiv δ (dsRep M ρ)) := by
  intro hDS hHC hSep D V lam S M T U μa μf μ _ _ fa ff hT ρ X _ _ _ δ hδ
  obtain ⟨hodd, hgap, hlam, -, hprod, harch, -⟩ := hT
  haveI : (μa (placeOf D ρ)).IsHaarMeasure := hprod.1 (placeOf D ρ)
  haveI := (M.ds ρ).1
  haveI : Nontrivial X := hδ.irred.1
  have hs : ∀ x ∈ UJset (M.ε ρ), ∃ g, ujMat (M.ε ρ) g = x := fun x hx => by
    obtain ⟨g, hg⟩ := exists_frameMat_eq M ρ hx
    exact ⟨frameEquiv M ρ g, hg⟩
  haveI : ((μa (placeOf D ρ)).map (frameEquiv M ρ)).IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map _ (frameEquiv M ρ)
  have hfe : (fa (placeOf D ρ) ∘ (frameEquiv M ρ).symm) ∘ frameEquiv M ρ = fa (placeOf D ρ) :=
    funext fun g => by simp
  have hpc : IsPseudoCoeff (ujMat (M.ε ρ)) ((μa (placeOf D ρ)).map (frameEquiv M ρ)) (ujRep (M.ds ρ).2.2.1)
      (fa (placeOf D ρ) ∘ (frameEquiv M ρ).symm) :=
    (isPseudoCoeff_dsRep_iff M ρ _ _).2 (by rw [hfe]; exact harch ρ)
  let π := δ.comp ((frameEquiv M ρ).symm : Formalism.REAL.UJ (M.ε ρ) →* _)
  have hπu : GlobalTheory.OpTrace.IsUnitaryRep π :=
    ⟨fun g v => hδ.unitary.norm_apply _ v,
      fun v => (hδ.unitary.continuous_apply v).comp (frameEquiv M ρ).symm.continuous⟩
  have hπi : GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π :=
    ⟨hδ.irred.1, fun W hW => hδ.irred.2 W ⟨hW.1, fun h v hv => by simpa [π] using hW.2 (frameEquiv M ρ h) v hv⟩⟩
  have hU := matRep_isURepOn π hπu hs
  have hadm : IsIrrAdm (M.ε ρ) (matRep (M.ε ρ) π) := _root_.GlobalTheory.IrrAdm.isIrrAdm_of_irred _ _ X _ hU (matRep_isIrredOn π hπi)
  obtain ⟨Θ, hΘ⟩ := hHC.1 V.rank (M.ε ρ) ((μa (placeOf D ρ)).map (frameEquiv M ρ)) X (matRep (M.ε ρ) π) hadm
  obtain ⟨c, htr⟩ : ∃ c, HasTrace (repOp (groupRep (M.ε ρ) hadm.2.1.1) ((μa (placeOf D ρ)).map (frameEquiv M ρ))
      (fa (placeOf D ρ) ∘ (frameEquiv M ρ).symm)) c := ⟨_, hΘ.1.2.2 _ hpc.mem⟩
  have hδe : π.comp ((frameEquiv M ρ) : _ →* Formalism.REAL.UJ (M.ε ρ)) = δ := MonoidHom.ext fun g => by simp [π]
  refine ⟨c, ?_, fun hc => ?_⟩
  · have h2 := htr
    rw [groupRep_matRep, repOp_map, hδe, hfe] at h2
    exact h2
  · have hML : M.lam ρ = fun i => (lam ρ i : ℝ) := funext (hlam ρ)
    have hHCp : Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) := by
      rw [hML]
      exact isHCParam_of_gap hodd (hgap ρ)
    have hinf := (GlobalTheory.DiscreteSeriesConsequences.of_classification hDS).2.1 V.rank (M.ε ρ) (M.lam ρ) (M.H ρ) (M.σ ρ) hHCp (M.ds ρ)
    simp only [hlam ρ, Complex.ofReal_intCast] at hinf
    have hD : GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.IsDiscreteWithInfChar (M.ε ρ) (lam ρ) (M.σ ρ) :=
      ⟨⟨(M.ds ρ).1, (M.ds ρ).2.1, (M.ds ρ).2.2.1, (M.ds ρ).2.2.2.1, (M.ds ρ).2.2.2.2.1⟩, hinf⟩
    obtain ⟨-, hb⟩ := hSep V.rank hodd (M.ε ρ) (lam ρ) (hasWideGaps_of_gap hodd.pos (hgap ρ)) (M.H ρ) (M.σ ρ) hD
      ((μa (placeOf D ρ)).map (frameEquiv M ρ)) _ hpc X (matRep (M.ε ρ) π) hadm _ htr hc
    obtain ⟨⟨A, hA⟩, -⟩ := hb hU
    refine ⟨A, fun g v => ?_⟩
    have h3 := hA (ujMat (M.ε ρ) (frameEquiv M ρ g)) (ujMat_mem_UJset _ _) v
    rw [matRep_ujMat] at h3
    simp only [π, MonoidHom.comp_apply, MonoidHom.coe_coe, ContinuousMulEquiv.symm_apply_apply] at h3
    exact h3

end GlobalTheory.ArchTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNormInj

open GlobalTheory.MixModel

theorem phase_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y' : Mx D r W.rank) (u : Mx D W.rank r) :
    GlobalTheory.LeviNorm.phase ψ W (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W)))) u =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y' : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) := by
  rw [GlobalTheory.LeviNorm.phase_apply, adj_adj]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc]
  have h : giA W * gA W = 1 := by
    change (W.gram⁻¹).map (incA D) * W.gram.map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne W)),
      Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))]
  rw [← Matrix.mul_assoc (giA W), h, Matrix.one_mul]

theorem eq_of_phase_integral_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ N₁ N₂ : Mx D W.rank r → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ μ → Integrable N₂ μ → (∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₁ u ∂μ = ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₂ u ∂μ) → N₁ = N₂ := by
  intro D ψ hψ W r μ hμ N₁ N₂ hc₁ hc₂ hi₁ hi₂ h
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D W.rank r
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hcont : ∀ y : Mx D r W.rank, Continuous fun u : Mx D W.rank r =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) :=
    fun y => hψ.1.1.comp (ht.comp (continuous_finsetSum _ fun i _ =>
      ((continuous_const.matrix_mul continuous_id).matrix_elem i i)))
  have hint : ∀ (y : Mx D r W.rank) (N : Mx D W.rank r → ℂ), Integrable N μ → Integrable (fun u =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) * N u) μ := by
    intro y N hN
    have := hN.mul_bdd (hcont y).aestronglyMeasurable (c := 1) (Filter.Eventually.of_forall fun u => (hψ.1.2.1 _).le)
    simpa only [mul_comm] using this
  rw [← sub_eq_zero]
  refine GlobalTheory.AdelicMatFourier.eq_zero_of_fourier_eq_zero D ψ hψ W.rank r μ hμ (N₁ - N₂) (hc₁.sub hc₂) (hi₁.sub hi₂) fun y' => ?_
  have e := h (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W))))
  simp only [phase_eq] at e
  simp only [Pi.sub_apply, mul_sub]
  rw [integral_sub (hint y' N₁ hi₁) (hint y' N₂ hi₂), e, sub_self]

end GlobalTheory.LeviNormInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseFrameSelfDualHermitianFrameLattice
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.SelfDualBaseFrame

theorem exists_baseFrame_frameLat : ∀ (D : D7) (V : HSp D), ∃ β₀ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D), IsSDFrame V β₀ (frameLat V) 1 ∧ IsBaseFrame V β₀ (frameLat V) 1 := by
  intro D V
  have hl : frameLat V = GlobalTheory.Member.latC V :=
    SetLike.coe_injective ((GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice V).symm.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  have hd : Formalism.L2.Herm.dualL D.sp.cm V (frameLat V) = frameLat V := by
    rw [hl]; exact Formalism.L2.Herm.coordinate_lattice_self_dual D.sp.cm V
  obtain ⟨β, c, hc⟩ := GlobalTheory.AdelicFrame.exists_isSDFrame D V (frameLat V) (GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice V).symm hd
  rw [one_pow] at hc
  exact ⟨β, ⟨0, by rwa [pow_zero]⟩, hc⟩

end GlobalTheory.SelfDualBaseFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteGroupActionPrincipalLevelFixedVector
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PrinFixedRep

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
  {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W}

theorem mem_fixed_iff {x : W} :
    x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) ↔
      ∀ h : GfC V, (h : GA D V) ∈ levG V β (flag1L L) → σ h x = x := by
  unfold GlobalTheory.PRep.fixed GlobalTheory.PRep.eig
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro H h hh
    exact H ⟨h, (Subgroup.mem_subgroupOf).2 hh⟩
  · intro H h
    exact H h ((Subgroup.mem_subgroupOf).1 h.2)

theorem act_eq_of_lifts {g0 : G0 L.Pg L.r} {κ κ' : GfC V} (hκ : IsLevelLift V β L g0 κ)
    (hκ' : IsLevelLift V β L g0 κ') {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) : σ κ' x = σ κ x := by
  have hm : ((κ⁻¹ * κ' : GfC V) : GA D V) ∈ levG V β (flag1L L) := by
    simpa using lift_div_mem hκ hκ'
  have e : κ' = κ * (κ⁻¹ * κ') := by group
  rw [e, map_mul, Module.End.mul_apply, (mem_fixed_iff.1 hx) _ hm]

theorem act_mem_fixed {g0 : G0 L.Pg L.r} {κ : GfC V} (hκ : IsLevelLift V β L g0 κ) {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) :
    σ κ x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) := by
  rw [mem_fixed_iff] at hx ⊢
  intro h hh
  have hc := (GlobalTheory.FlagAction.conj_mem_flag1 hκ hh).1
  have hc' : ((κ⁻¹ * (h * κ) : GfC V) : GA D V) ∈ levG V β (flag1L L) := by simpa using hc
  have e : h * κ = κ * (κ⁻¹ * (h * κ)) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hx _ hc']

theorem main : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W),
    ∃ ρ : Representation ℂ (G0 L.Pg L.r) (GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))),
      ∀ (g0 : G0 L.Pg L.r) (κ : GfC V), IsLevelLift V β L g0 κ → ∀ x, (ρ g0 x : W) = σ κ x := by
  intro D V β L hl W _ _ σ
  let lift : G0 L.Pg L.r → GfC V := fun g0 => ⟨(hl g0).choose, (hl g0).choose_spec.1⟩
  have hlift : ∀ g0, IsLevelLift V β L g0 (lift g0) := fun g0 => (hl g0).choose_spec
  let F := GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))
  have hs : ∀ g0, ∀ x ∈ F, σ (lift g0) x ∈ F := fun g0 x hx => act_mem_fixed (hlift g0) hx
  let ρ : Representation ℂ (G0 L.Pg L.r) F :=
    { toFun := fun g0 => (σ (lift g0)).restrict (hs g0)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show σ (lift 1) x = x
        have h1 : IsLevelLift V β L 1 ((1 : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_one_of_mem (Subgroup.one_mem _)
        rw [act_eq_of_lifts h1 (hlift 1) x.2, map_one, Module.End.one_apply])
      map_mul' := fun g g' => LinearMap.ext fun x => Subtype.ext (by
        show σ (lift (g * g')) x = σ (lift g) (σ (lift g') x)
        have hm : IsLevelLift V β L (g * g') ((lift g * lift g' : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_mul (hlift g) (hlift g')
        rw [act_eq_of_lifts hm (hlift (g * g')) x.2, map_mul, Module.End.mul_apply]) }
  refine ⟨ρ, fun g0 κ hκ x => ?_⟩
  show σ (lift g0) x = σ κ x
  exact act_eq_of_lifts hκ (hlift g0) x.2

end GlobalTheory.PrinFixedRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsL2AdelicQuotientModelEquivalence
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrModel

theorem exists_model : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∃ (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕))) (e : DividedPowerChartLift V μ ≃ₗᵢ[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕)), GlobalTheory.HolDict.FinPair V μ 𝓕 ∧ GlobalTheory.HolDict.IsReg V μ 𝓕 ρ ∧ (∀ g F, e (RG V μ g F) = ρ g (e F)) ∧ ∀ F ψ, GlobalTheory.HolDict.Repr V μ 𝓕 (e F) ψ ↔ lift (GQ V) F =ᵐ[μ] ψ := by
  intro D V μ _ _
  refine ⟨GlobalTheory.AutomorphicL2Unitary.stdDom (GQ V), RG V μ, LinearIsometryEquiv.refl ℂ _, ?_, ?_, fun g F => rfl, fun F ψ => Iff.rfl⟩
  · exact ⟨inferInstance, inferInstance, GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ,
      (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ _ inferInstance
        (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ)).ne⟩
  · exact ⟨fun g F => GlobalTheory.AutomorphicL2Unitary.lift_R g F, fun g F => GlobalTheory.AutomorphicL2Unitary.norm_R g F,
      fun F => (isUnitaryRep_RG (V := V) (μ := μ)).continuous_apply F⟩

end GlobalTheory.TrModel
end

