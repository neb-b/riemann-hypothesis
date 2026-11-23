module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0051
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicTraceCharDifferentGenConjIdealCompletionAl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

theorem conj_mem_AA_mul_AAbar {a : D.host.E} (ha : a ∈ D.host.AA * D.host.AAbar) :
    D.host.conj a ∈ D.host.AA * D.host.AAbar := by
  refine FractionalIdeal.mul_induction_on (C := fun a => D.host.conj a ∈ D.host.AA * D.host.AAbar) ha ?_ ?_
  · intro x hx y hy
    rw [map_mul, mul_comm (D.host.conj x)]
    exact FractionalIdeal.mul_mem_mul (Formalism.L2.Pj.conj_mem_AA D hy) (Formalism.L2.Pj.conj_mem_AAbar D hx)
  · intro x y hx hy
    rw [map_add (f := _)]
    exact Submodule.add_mem (p := ((D.host.AA * D.host.AAbar : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E)) hx hy

theorem hostDifferentGenerator_mul_mem_inverseDifferent {a : D.host.E} (ha : a ∈ D.host.AA * D.host.AAbar) :
    D.host.xi0 * a ∈ GlobalTheory.IdeleAA.Dual D := by
  change _ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
  rw [← Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D]
  have h := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0) ha
  rwa [← mul_assoc] at h

theorem psiE_add' (ψ : AddChar (AF D.host.F) ℂ) (x y : AE D) : psiE ψ (x + y) = psiE ψ x * psiE ψ y := by
  unfold psiE
  rw [map_add (f := _), AddChar.map_add_eq_mul]

theorem psiE_zero' (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  unfold psiE
  rw [map_zero, AddChar.map_zero_eq_one]

theorem cA_tmul' (p : AF D.host.F) (e : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] e) = p ⊗ₜ[D.host.F] D.host.conj e := by
  rw [GlobalTheory.IdeleAA.tmul_eq, map_mul, GlobalTheory.SelfDualAt.cA_alg, GlobalTheory.IdeleAA.cA_incA, ← GlobalTheory.IdeleAA.tmul_eq]

theorem adelicTraceChar_differentGen_conj_integral_tmul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {α : Af D.host.F}
    (hα : α ∈ intAf D.host.F) {a : D.host.E} (ha : a ∈ D.host.AA * D.host.AAbar) :
    psiE ψ (incA D D.host.xi0 * cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a)) = 1 := by
  have e : incA D D.host.xi0 * cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (D.host.xi0 * D.host.conj a) := by
    rw [cA_tmul', GlobalTheory.IdeleAA.tmul_eq, GlobalTheory.IdeleAA.tmul_eq, map_mul]
    ring
  rw [e, GlobalTheory.FinPl.Conductor.psiE_eq_chi ψ (by exact TensorProduct.zero_tmul _ _)]
  exact GlobalTheory.IdeleAA.chi_tmul_dual hψ hα (hostDifferentGenerator_mul_mem_inverseDifferent (conj_mem_AA_mul_AAbar ha))

theorem adelicTraceChar_differentGen_conj_idealCompletion : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) →
    ∀ s ∈ complId (D.host.AA * D.host.AAbar), psiE ψ (incA D D.host.xi0 * cA D s) = 1 := by
  intro D ψ hψ s hs
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨α, hα, a, ha, rfl⟩ := hs
    exact adelicTraceChar_differentGen_conj_integral_tmul hψ hα ha
  | zero => rw [map_zero, mul_zero]; exact psiE_zero' ψ
  | add x y _ _ hx hy => rw [map_add (f := _), mul_add, psiE_add', hx, hy, one_mul]
  | neg x _ hx =>
    have h := psiE_add' ψ (incA D D.host.xi0 * cA D x) (incA D D.host.xi0 * cA D (-x))
    rw [← mul_add, ← map_add (f := _), add_neg_cancel, map_zero, mul_zero, psiE_zero', hx, one_mul] at h
    exact h.symm

end GlobalTheory.XCharBF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjInstanceCharacterEqProdResidueFieldAddChars
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjProd
open Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis Formalism.L2.SG.HidaSetting
open scoped TensorProduct
variable {D : D7}

theorem sigInt_oToS (a : 𝓞 D.host.E) :
    sigInt (instOf D) (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (GlobalTheory.IdemSupport.cO D a) :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE (instOf D) (a : D.host.E))

theorem conjRes_mk (PP : Pl D.host.E) (x : 𝓞 D.host.E) :
    GlobalTheory.SeeConjChar.conjRes PP (Ideal.Quotient.mk PP.asIdeal x) =
      Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal (GlobalTheory.IdemSupport.cO D x) := rfl

theorem conj_res_oToS (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) (oToS D.host.F D.host.E a))) =
      Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal a := by
  rw [sigInt_oToS, resS_oToS, conjRes_mk, GlobalTheory.IdemSupport.cO_cO]

theorem resS_cP (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F (GlobalTheory.IdemSupport.cP PP) s =
      GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) s)) := by
  set f1 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
    (GlobalTheory.SeeConjChar.conjRes PP).toRingHom.comp ((resS D.host.F PP).comp (sigInt (instOf D))) with hf
  have hf0 : ∀ x, f1 x = GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) x)) := fun x => rfl
  have hf1 : ∀ a, f1 (oToS D.host.F D.host.E a) = Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal a :=
    fun a => (hf0 _).trans (conj_res_oToS PP a)
  have hker : idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal ≤ RingHom.ker f1 := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hf1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hc
  obtain ⟨a, ha⟩ := (cmpS_bij (F := D.host.F) (GlobalTheory.IdemSupport.cP PP).asIdeal (GlobalTheory.IdemSupport.cP PP).ne_bot).2
    (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have e : Ideal.Quotient.mk (idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal) s =
      Ideal.Quotient.mk _ (oToS D.host.F D.host.E a) := ha.symm
  have hd : s - oToS D.host.F D.host.E a ∈ idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal := Ideal.Quotient.eq.1 e
  have hker2 : idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal ≤ RingHom.ker (resS D.host.F (GlobalTheory.IdemSupport.cP PP)) := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, resS_oToS]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hc
  have h2 : resS D.host.F (GlobalTheory.IdemSupport.cP PP) s = resS D.host.F (GlobalTheory.IdemSupport.cP PP) (oToS D.host.F D.host.E a) := by
    have := hker2 hd
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  have h1 : f1 s = f1 (oToS D.host.F D.host.E a) := by
    have := hker hd
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  exact h2.trans ((resS_oToS _ a).trans ((hf1 a).symm.trans (h1.symm.trans (hf0 s))))

theorem exists_addChar_ne_one (k : Type) [Field k] [Finite k] : ∃ ψ : AddChar k ℂ, ψ ≠ 1 := by
  have h1 : Multiplicative.ofAdd (1 : k) ≠ 1 := by
    intro h
    exact one_ne_zero (congrArg Multiplicative.toAdd h)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative k) ℂ h1
  let ψ : AddChar k ℂ :=
    { toFun := fun x => ((φ (Multiplicative.ofAdd x) : ℂˣ) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y => by simp [ofAdd_add] }
  refine ⟨ψ, fun h => hφ (Units.ext ?_)⟩
  have := congrArg (fun χ : AddChar k ℂ => χ 1) h
  simpa [ψ] using this

theorem addChar_comp_ne_one {k k' : Type} [Field k] [Field k'] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : k) (ha : a ≠ 0)
    (e : k' ≃+* k) : ψ.compAddMonoidHom ((AddMonoidHom.mulLeft a).comp e.toAddMonoidHom) ≠ 1 := by
  intro h
  apply hψ
  ext t
  have := congrArg (fun χ : AddChar k' ℂ => χ (e.symm (a⁻¹ * t))) h
  change ψ (a * e (e.symm (a⁻¹ * t))) = (1 : AddChar k' ℂ) (e.symm (a⁻¹ * t)) at this
  rw [RingEquiv.apply_symm_apply, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, AddChar.one_apply] at this
  rw [this, AddChar.one_apply]

theorem cP_cP (P : Pl D.host.E) : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem sigInt_sigInt (s : Formalism.L2.Herm.intAf D.host.F D.host.E) : sigInt (instOf D) (sigInt (instOf D) s) = s :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA (instOf D) s.1)

theorem conjRes_cP (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s) =
      resS D.host.F (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) (sigInt (instOf D) s) := by
  rw [resS_cP (GlobalTheory.IdemSupport.cP PP) (sigInt (instOf D) s), sigInt_sigInt]


open Classical in
theorem core (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1)
    (hrat : ∀ x : (instOf D).E,
      psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1)
    (Pg : Finset (Pl D.host.E)) (hdiv : ∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hcov : ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') :
    ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧
      ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
        psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) =
          ∏ PP ∈ Pg, ψ PP (resS D.host.F PP s) *
            ψ (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s) := by
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) →
      ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1 := by
    intro s hs
    refine _root_.GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero (instOf D) _ hg (_root_.GlobalTheory.TypePrimeUnif.prod_not_mem_sq D) s fun Q hQ => ?_
    obtain ⟨PP, hPP, rfl | rfl⟩ := hcov Q hQ
    · exact (hs _ hPP).1
    · exact (resS_cP PP s).trans (by rw [(hs _ hPP).2]; exact map_zero _)
  choose ψ0 hψ0 using fun P : Pl D.host.E => exists_addChar_ne_one (kP P)
  obtain ⟨a₁, a₂, ha, hχ⟩ := _root_.GlobalTheory.LeviBlockCharacter.char_eq_prod_shift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP)
    (fun PP => (resS D.host.F PP).comp (sigInt (instOf D)))
    (fun s => psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ψ0 (fun PP _ => hψ0 PP)
    (fun s t => (congrArg psiEf (Formalism.L2.SG.Pf.unitaryCongruence.divN_add (instOf D) (D.host.g 0 * D.host.g 1) s.1 t.1)).trans
      (hadd _ _))
    (fun s hs => by
      obtain ⟨t, ht, e⟩ := hN s hs
      have : divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t :=
        (congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)
      show psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) = 1
      rw [this, hint t ht])
    (GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)
    (GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hdiv hnc (fun s => psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1)
      fun Q hQ => GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ)
  have hout : ∀ PP ∈ Pg, GlobalTheory.IdemSupport.cP PP ∉ Pg := fun PP hPP h =>
    hnc PP hPP _ h ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)
  let ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ := fun P =>
    if P ∈ Pg then (ψ0 P).compAddMonoidHom ((AddMonoidHom.mulLeft (a₁ P)).comp (RingEquiv.refl (kP P)).toAddMonoidHom)
    else if GlobalTheory.IdemSupport.cP P ∈ Pg then (ψ0 (GlobalTheory.IdemSupport.cP P)).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₂ (GlobalTheory.IdemSupport.cP P))).comp (GlobalTheory.SeeConjChar.conjRes P).toAddMonoidHom)
    else 1
  have hψ1 : ∀ PP ∈ Pg, ψ PP = (ψ0 PP).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₁ PP)).comp (RingEquiv.refl (kP PP)).toAddMonoidHom) := fun PP hPP => if_pos hPP
  have hψ2 : ∀ PP ∈ Pg, ψ (GlobalTheory.IdemSupport.cP PP) = (ψ0 (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP))).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₂ (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)))).comp
        (GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP)).toAddMonoidHom) := fun PP hPP => by
    have h2 : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP) ∈ Pg := by rw [cP_cP]; exact hPP
    exact (if_neg (hout PP hPP)).trans (if_pos h2)
  refine ⟨ψ, fun PP hPP => ⟨?_, ?_⟩, fun s => ?_⟩
  · rw [hψ1 PP hPP]
    exact addChar_comp_ne_one _ (hψ0 PP) _ (ha PP hPP).1 _
  · rw [hψ2 PP hPP]
    refine addChar_comp_ne_one _ (hψ0 _) _ ?_ _
    rw [cP_cP]
    exact (ha PP hPP).2
  · refine (hχ s).trans (Finset.prod_congr rfl fun PP hPP => ?_)
    refine (AddChar.map_add_eq_mul (ψ0 PP) _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · rw [hψ1 PP hPP]
      rfl
    rw [hψ2 PP hPP]
    show _ = ψ0 (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) (a₂ (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) *
      GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s))
    rw [conjRes_cP]
    have key : ∀ Q : Pl D.host.E, Q = PP → ψ0 Q (a₂ Q * resS D.host.F Q (sigInt (instOf D) s)) =
        ψ0 PP (a₂ PP * resS D.host.F PP (sigInt (instOf D) s)) := by
      rintro Q rfl
      rfl
    exact (key _ (cP_cP PP)).symm

theorem chiS_eq_prod : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, GlobalTheory.SeeConjChar.chiS X h c = ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
  intro D X h Pg hdiv hcov hnc
  have key : ∀ (I : AutInst) (hI : I = instOf D) (g : ℕ) (_ : g = D.host.g 0 * D.host.g 1)
      (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ) (_ : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
      (_ : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
      (_ : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1),
      ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧
        ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
          psiEf (divN I g (cast (congrArg (fun I : AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) hI).symm c)) =
            ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) *
              ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
    intro I hI g hg psiEf hadd hint hrat
    subst hI hg
    obtain ⟨ψ, hψ, hprod⟩ := core psiEf hadd hint hrat Pg hdiv hcov hnc
    refine ⟨ψ, hψ, fun c hc => ?_⟩
    have e1 : ∀ P : Pl D.host.E, GlobalTheory.SeeConjChar.resT P c = resS D.host.F P ⟨c, hc⟩ := fun P => dif_pos hc
    simp only [e1, cast_eq]
    exact hprod ⟨c, hc⟩
  exact key X.B.I h X.B.g X.g_eq X.psiEf X.psiEf_add X.psiEf_int X.psiEf_rat

end GlobalTheory.SeeConjProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPrimeSmulLatticeHeckeElementLe
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeConjPart

open Formalism.L2.NTheta GlobalTheory.SplitPlace IsDedekindDomain

variable {D : D7}

theorem le_unif {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
  rw [WithZero.coe_le_coe]
  rw [← Multiplicative.toAdd_lt, toAdd_one] at h
  rw [← Multiplicative.toAdd_le, toAdd_ofAdd]
  omega

theorem ratio_int {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {y : 𝓞 D.host.E} (hy : y ∈ P.asIdeal) :
    ∃ t ∈ intAE D, finPart D e * finPart D (incA D (y : D.host.E)) =
      t * (finPart D e * finPart D (incA D (ϖ : D.host.E))) := by
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  have hu := isUnif he h4 h5 ϖ hP hP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0
    apply hP2
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _
  set φ : D.host.E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v := (π.comp (finPart D)).comp (incA D) with hφ
  set q : D.host.E := (y : D.host.E) / (ϖ : D.host.E)
  refine ⟨finPart D e * finPart D (incA D q), ?_, ?_⟩
  · rw [h4]
    change Valued.v (φ q) ≤ 1
    rw [map_div₀, map_div₀]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have hn := (he.2 y hy0).1 hy
    rw [map_mul, h4] at hn
    change ¬ Valued.v (φ ((y : D.host.E)⁻¹)) ≤ 1 at hn
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 fun h0 => hy0 (RingOfIntegers.coe_eq_zero_iff.1 h0))))] at hn
    have hϖv : Valued.v (φ ϖ) = _ := hu
    have h6 := le_unif hn
    rw [← hϖv] at h6
    rw [div_le_one₀ (by rw [hϖv]; exact zero_lt_iff.2 WithZero.coe_ne_zero)]
    exact h6
  · have hee : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
    have hq : q * (ϖ : D.host.E) = y := div_mul_cancel₀ _ hϖ0
    calc finPart D e * finPart D (incA D (y : D.host.E))
        = (finPart D e * finPart D e) * (finPart D (incA D q) * finPart D (incA D (ϖ : D.host.E))) := by
          rw [hee, ← map_mul (finPart D) (incA D q), ← map_mul (incA D) q, hq]
      _ = _ := mul_mul_mul_comm _ _ _ _

open scoped Matrix


set_option maxHeartbeats 1000000 in
theorem keeps {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ z ∈ LamHat V, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z ∈ LamHat V := by
  intro z hz
  have hee : e * e = e := he.1.1
  have hint : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩
  have hc := hecke_conj hee ha
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have h4 := (lower_iff hce V _ a₀⁻¹).1 hc.2.2.2.1
  rw [inv_inv] at h4
  obtain ⟨t, ht, hteq⟩ := ratio_int he hP hP2 ((Formalism.L2.Col.mem_conjP P x).1 hx)
  have hteq' := congrArg (cf D) hteq
  rw [map_mul, map_mul, map_mul, ← fin_cA, ← fin_cA, ← fin_cA, cA_incA, cA_incA] at hteq'
  have hsx : star ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := by
    change star (star (x : D.host.E)) = _
    exact star_star _
  rw [hsx] at hteq'
  have h6 := mulVec_parts (finPart D) ((suppAt_iff e V a₀).1 ha.2.1) z
  rw [← fm_eq V a₀] at h6
  rw [h6, RingHom.map_add (f := _), add_smul, smul_sub, smul_add, smul_add]
  have hi1 := idem_mem hee
  have hi2 := idem_mem hce
  refine sub_mem (add_mem (add_mem ?_ ?_) (smul_mem V hint hz))
    (smul_mem V hint (smul_mem V (add_mem hi1 hi2) hz))
  · exact smul_mem V hint (ha.2.2.1 z hz)
  · rw [smul_smul, mul_comm, hteq', mul_smul]
    exact smul_mem V (cf_mem ht) (h4 z hz)

theorem finHom_eq {V : HSp D} (g : GA D V) : (finHom V g).1 = fm V g := rfl

theorem finPart_incA (c : D.host.E) :
    finPart D (incA D c) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c := rfl

theorem keeps_one {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ y ∈ latGHat V 1, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y ∈ latGHat V 1 := by
  intro y hy
  rw [GlobalTheory.LevelActionPinned.latGHat_one] at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c, hc, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z, ?_, ?_⟩
    · rw [GlobalTheory.StdFrameCong.pj_latHat_eq] at hz ⊢
      exact keeps he hP hP2 ha hx z hz
    · rw [Matrix.mulVec_smul, smul_comm]
  | zero => rw [Matrix.mulVec_zero, smul_zero]; exact zero_mem _
  | add a b _ _ ha' hb' => rw [Matrix.mulVec_add, smul_add]; exact add_mem ha' hb'
  | neg a _ ha' => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem ha'

end GlobalTheory.HeckeConjPart

open scoped Matrix


open GlobalTheory.SplitPlace in
theorem GlobalTheory.HeckeConjPart.conj_part : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E)
    (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  intro D V P e ϖ k g a₀ he hP hP2 ha
  rw [Submodule.smul_le]
  intro x hx v hv
  have spec := GlobalTheory.MarkCoset.latG_spec D V
  rw [(spec (g * a₀)).1, (spec (g * a₀)).2] at hv
  obtain ⟨y, hy, hyv⟩ := hv
  rw [(spec g).1, (spec g).2]
  refine ⟨finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y, GlobalTheory.HeckeConjPart.keeps_one he hP hP2 ha hx y hy, ?_⟩
  rw [GlobalTheory.HeckeConjPart.finHom_eq] at hyv ⊢
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← fm_mul, hyv]
  funext i
  simp only [finVec, Pi.smul_apply, smul_eq_mul, GlobalTheory.HeckeConjPart.finPart_incA,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_selfDual_primitive_meet : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧ capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  first
  | exact @GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap
  | intro D u Y X ι z h L₀ x₀ hL hg
    exact GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap D u Y X ι z h L₀ x₀ hL.toIsLattice hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioLeTraceTerms
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

namespace GlobalTheory.HeckeEx

theorem cabs_gen_le_of_hkPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) ≤ (Ideal.absNorm P : ℝ) ^ i := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hz hb hx hx'
  obtain ⟨g, Λ, Λ', Fd, Fd', h, u, u', v, c1, c2, f1, f2, hh, u0, u0', up, up', m1, m1', hpt⟩ :=
    _root_.GlobalTheory.HeckeGenBound.exists_pointwise_bound E H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hz hb hx hx'
  exact_mod_cast _root_.GlobalTheory.PeriodicMean.mean_factor_le g Λ Λ' Fd Fd' h u u' p _ v _ c1 c2 f1 f2 hA.2.2.1.pos hh u0 u0' up up' m1 m1' hpt

end GlobalTheory.HeckeEx
end

