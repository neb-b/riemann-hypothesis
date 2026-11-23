module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPlaceIntegerMem
section
namespace ConjugatePlaceIntegrality
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.ConjPlaceInt

variable {D : D7}

theorem sg_mem_OA {x : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D} (hx : x ∈ OA D) : sg D x ∈ OA D :=
  Formalism.UG.P.csDual_sig_mem D.sp.cm.sig hx

theorem cpt_sg_mem_integers : ∀ {D : D7} (Q : Pl D.host.E) (z : Lev.EAf D),
    cpt Q z ∈ Q.adicCompletionIntegers D.host.E →
      cpt (GlobalTheory.IdemSupport.cP Q) (sg D z) ∈ (GlobalTheory.IdemSupport.cP Q).adicCompletionIntegers D.host.E := by
  intro D Q z hz
  obtain ⟨e, -, -, h1, h0⟩ := GlobalTheory.StdFrames.exists_idem (D := D) ({Q} : Set (Pl D.host.E))
  have he1 : cpt Q e = 1 := h1 Q rfl
  have hez : e * z ∈ OA D := (mem_OA_iff _).2 fun P => by
    by_cases hP : P = Q
    · subst hP
      rw [map_mul, he1, one_mul]
      exact hz
    · rw [map_mul, h0 P hP, zero_mul]
      exact zero_mem _
  have hs : cpt (GlobalTheory.IdemSupport.cP Q) (sg D e) = 1 := by
    have h2 : cpt (GlobalTheory.IdemSupport.cP Q) (sg D (1 - e)) = 0 :=
      cpt_sg_eq_zero (by rw [cP_cP, map_sub, map_one, he1, sub_self])
    rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h2
    exact h2.symm
  have h3 := (mem_OA_iff _).1 (sg_mem_OA hez) (GlobalTheory.IdemSupport.cP Q)
  rwa [map_mul, map_mul, hs, one_mul] at h3

end GlobalTheory.CompanionTheory.ConjPlaceInt

end
end

end ConjugatePlaceIntegrality
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjTypeOverReal

theorem exists_tau_of_val {D : D7} (ψ : D.host.E →+* ℂ)
    (h : ψ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)) :
    ∃ τ : D.what₂.Tau, tauE D τ = ψ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 ψ
  refine ⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 h⟩, ?_⟩
  simp [tauE]

theorem sqrt_sq' {D : D7} : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
  have h0 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  apply D.host.φ₀.injective
  rw [map_pow, h3, h0]
  simp

theorem exists_conj_tauE_over (D : D7) (w : InfinitePlace D.host.F) : ∃ τ : D.what₂.Tau,
    ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding := by
  letI : Algebra D.host.F ℂ := w.embedding.toAlgebra
  haveI : Algebra.IsAlgebraic D.host.F D.host.E := inferInstance
  haveI : Module.IsTorsionFree D.host.F ℂ := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  let ψ : D.host.E →ₐ[D.host.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hψ : (ψ : D.host.E →+* ℂ).comp (algebraMap D.host.F D.host.E) = w.embedding := by
    ext x
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    rfl
  have hreal : (starRingEnd ℂ).comp w.embedding = w.embedding := by
    have hw : w.IsReal := IsTotallyReal.isReal w
    have := (InfinitePlace.isReal_iff.1 hw)
    exact this
  have h0 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h1 : (ψ : D.host.E →+* ℂ) D.host.sqrtMinusD ^ 2 =
      (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
    rw [← map_pow, sqrt_sq', h0]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · obtain ⟨τ, hτ⟩ := exists_tau_of_val (ψ : D.host.E →+* ℂ) h2
    refine ⟨τ, ?_⟩
    rw [hτ, RingHom.comp_assoc, hψ, hreal]
  · obtain ⟨τ, hτ⟩ := exists_tau_of_val ((starRingEnd ℂ).comp (ψ : D.host.E →+* ℂ))
      (by rw [RingHom.comp_apply, h2]; simp)
    refine ⟨τ, ?_⟩
    rw [hτ, ← RingHom.comp_assoc]
    have hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
      ext z; simp
    rw [hcc, RingHom.id_comp, hψ]

theorem conj_tauE_over_realPlace : ∀ {D : D7} (w : InfinitePlace D.host.F), ∃ τ : D.what₂.Tau,
    ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding :=
  fun {D} w => exists_conj_tauE_over D w

end GlobalTheory.ConjTypeOverReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjUTransport

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (UB incM incM_smul mt_gram continuous_conj continuous_conjU)

variable {D : D7}

theorem mem_inv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) :
    (GeneralLinearGroup.map (cA D) (show GL (Fin V.rank) (AE D) from x.1) : GL (Fin V.rank) (AE D)) ∈
      HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have e : ((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)).map (cA D) =
      (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
  have hx : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))ᵀ * incM J *
      (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = incM J := x.2
  show (((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)).map (cA D))ᵀ * incM V.gram *
    (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = incM V.gram
  rw [e]
  generalize (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = X at hx ⊢
  rw [h, incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hx
  have hx' := congrArg (fun y => incA D c⁻¹ • y) hx
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul] at hx'
  exact hx'

def conjUInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) : GA D V :=
  show HR (AF D.host.F) D.sp.cm.sig V.gram from ⟨_, mem_inv V c hc h x⟩

def conjEquiv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GA D V ≃* UB J where
  toFun := conjU V c h
  invFun := conjUInv V c hc h
  left_inv g := by
    apply Subtype.ext; apply Units.ext; ext i j; exact Formalism.L2.Theta.cA_cA _
  right_inv x := by
    apply Subtype.ext; apply Units.ext; ext i j; exact Formalism.L2.Theta.cA_cA _
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    show (mt V (a * b)).map (cA D) = (mt V a).map (cA D) * (mt V b).map (cA D)
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt, map_mul]

theorem continuous_conjUInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : Continuous (conjUInv V c hc h) := by
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (continuous_conj D)
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (continuous_conj D)

theorem cA_inclR (a : D.host.E) :
    cA D (inclR (F := D.host.F) (AF D.host.F) a) = inclR (F := D.host.F) (AF D.host.F) (D.sp.cm.sig a) := rfl

theorem rat_fwd (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram)
    (γ : GA D V) (hγ : γ ∈ GQ V) : conjU V c h γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J := by
  obtain ⟨y, -, e⟩ := hγ
  refine ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) y, Units.ext ?_⟩
  have e' : mt V γ = (y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val e).symm
  show _ = (mt V γ).map (cA D)
  rw [e']
  ext i j
  exact (cA_inclR _).symm

theorem inclR_injective : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem rat_inv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) : conjUInv V c hc h x ∈ GQ V := by
  obtain ⟨z, hz⟩ := hx
  have hz' : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) =
      (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val hz).symm
  set Z := (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (D.sp.cm.sig : D.host.E →+* D.host.E) with hZ
  have hY : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) =
      Z.map (inclR (F := D.host.F) (AF D.host.F)) := by
    rw [hz']; ext i j; exact cA_inclR _
  refine ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) z, ?_, Units.ext ?_⟩
  · have hm := mem_inv V c hc h x
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)) *
      JR (AF D.host.F) V.gram * (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = JR (AF D.host.F) V.gram at hm
    rw [hY] at hm
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Z.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; exact cA_inclR _
    rw [hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram * Z = V.gram
    apply Matrix.map_injective inclR_injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · show Z.map (inclR (F := D.host.F) (AF D.host.F)) = (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)
    exact hY.symm

def ratEquiv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J ≃ GQ V where
  toFun γ := ⟨conjUInv V c hc h γ.1, rat_inv V c hc h γ.1 γ.2⟩
  invFun γ := ⟨conjU V c h γ.1, rat_fwd V c h γ.1 γ.2⟩
  left_inv γ := Subtype.ext ((conjEquiv V c hc h).right_inv γ.1)
  right_inv γ := Subtype.ext ((conjEquiv V c hc h).left_inv γ.1)

theorem map_isHaar_isFundamentalDomain : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure →
    IsFundamentalDomain (GQ V) fd ν →
    (ν.map (conjU V c h)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (conjU V c h '' fd) (ν.map (conjU V c h)) := by
  intro D V J c hc h ν fd hν hfd
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have : BorelSpace (UB J) := ⟨rfl⟩
  let φ := conjEquiv V c hc h
  have c1 : Continuous φ := continuous_conjU V c h
  have c2 : Continuous φ.symm := continuous_conjUInv V c hc h
  have hH : (ν.map φ).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν φ c1 c2
  refine ⟨hH, ?_⟩
  let H : GA D V ≃ₜ UB J := ⟨φ.toEquiv, c1, c2⟩
  let M := H.toMeasurableEquiv
  have hq : Measure.QuasiMeasurePreserving M.symm (ν.map M) ν :=
    (M.measurePreserving_symm ν).quasiMeasurePreserving
  refine hfd.image_of_equiv M.toEquiv hq (ratEquiv V c hc h) fun γ x => ?_
  show φ (φ.symm γ.1 * x) = γ.1 * φ x
  rw [map_mul, MulEquiv.apply_symm_apply]

end GlobalTheory.ConjUTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAddCharSymplecticSelfPairingPlaceCoord
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ContSymp

theorem continuous_psi_symp_atPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (o : E) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {M : Type} [Fintype M] (g : M → Matrix (Fin n) (Fin d) E),
    Continuous (fun a : M → v.adicCompletionIntegers F => ψ (⅟(2 : AF F) *
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) o) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB)
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)))) := by
  intro F E _ _ _ _ _ σ ψ hψ n d JA JB o v M _ g
  set B := GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) o) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) with hB
  have hadd1 : ∀ x x' y, B (x + x') y = B x y + B x' y := by
    intro x x' y
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, ← map_add (f := _), ← mul_add, ← Finset.sum_add_distrib, Matrix.add_apply, add_mul]
  have hadd2 : ∀ x y y', B x (y + y') = B x y + B x y' := by
    intro x y y'
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have hsm1 : ∀ (r : AF F) x y, B (r • x) y = r * B x y := by
    intro r x y
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm,
      LinearMap.map_smul, smul_eq_mul]
  have hsm2 : ∀ (r : AF F) x y, B x (r • y) = r * B x y := by
    intro r x y
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.smul_apply, map_smul, mul_smul_comm, ← Finset.smul_sum,
      smul_eq_mul]
  let Bl : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →ₗ[AF F] Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →ₗ[AF F] AF F :=
    LinearMap.mk₂ (AF F) B hadd1 (fun r x y => by rw [hsm1, smul_eq_mul]) hadd2 (fun r x y => by rw [hsm2, smul_eq_mul])
  have hexp : ∀ a : M → v.adicCompletionIntegers F,
      B (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * ∑ m', GlobalTheory.EmbChart.atPlace v (a m' : Fv F v) *
        B (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) := by
    intro a
    change Bl _ _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rfl
  simp_rw [hexp]
  have hc : ∀ m, Continuous fun a : M → v.adicCompletionIntegers F => GlobalTheory.EmbChart.atPlace v (a m : Fv F v) :=
    fun m => (GlobalTheory.VacAny.continuous_atPlace v).comp (continuous_subtype_val.comp (continuous_apply m))
  refine hψ.comp (continuous_const.mul (continuous_finsetSum _ fun m _ => (hc m).mul (continuous_finsetSum _ fun m' _ =>
    (hc m').mul continuous_const)))

end GlobalTheory.ContSymp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRectangularAdelicMatricesShrunkCompact
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem cover_rect_adMat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j m : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (m * μ i) ∧ ∀ x : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), ∃ x₀ : Matrix (Fin j) (Fin m) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω) := by
  intro F E _ _ _ _ _ σ hσ j m
  classical
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.GodementSectionReduction.cover_adele F E σ hσ
  choose Y hY h using h
  refine ⟨Ω, (C ^ m) ^ j, hΩ, fun μ =>
    ⟨Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i), ?_, fun x => ?_⟩⟩
  · have h1 : (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i)).card = ∏ i, (Y (μ i)).card ^ m := by
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (Nat.cast_le.2 h1.le).trans ?_
    push_cast
    refine (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ =>
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY (μ i)) m).trans (le_of_eq ?_)
    simp only [bse, mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul _ (μ _), mul_comm m]
  · choose x₀ y hy ω hω e using fun i k => h (μ i) (x i k)
    refine ⟨Matrix.of x₀, Matrix.of y, Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 (hy i), Matrix.of ω,
      fun i k => hω i k, ?_⟩
    ext i k
    rw [Matrix.add_apply, Matrix.add_apply, ← add_assoc]
    simp only [tor, GlobalTheory.Eis.Conv.dg, Matrix.diagonal_mul, adMat, Matrix.map_apply, Matrix.of_apply, zpow_natCast,
      Units.val_pow_eq_pow_val]
    exact e i k

end GlobalTheory.SphEis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem covolume_ne_top_of_continuousMulEquiv : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (Γ : Subgroup G) (Λ : Subgroup H) [Countable Γ], (∀ g, g ∈ Γ ↔ e g ∈ Λ) → (∀ μ : Measure G, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤) → ∀ (π : Measure H) (𝓜 : Set H), π.IsHaarMeasure → IsFundamentalDomain Λ 𝓜 π → π 𝓜 ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ e Γ Λ _ hmem hfin π 𝓜 hπ h𝓜
  let E : G ≃ᵐ H := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun _ => rfl
  set μ : Measure G := π.map E.symm with hμdef
  have hμ : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map π e.symm
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving E μ π := by
    refine ⟨E.measurable.aemeasurable, ?_⟩
    rw [hμdef, Measure.map_map E.measurable E.symm.measurable]
    simp only [MeasurableEquiv.self_comp_symm, Measure.map_id]
    exact Measure.AbsolutelyContinuous.rfl
  let φ : Λ → Γ := fun l => ⟨e.symm l, (hmem _).2 (by simpa using l.2)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have := congrArg (fun x : Γ => e (x : G)) hab
      simpa [φ] using this
    · intro g
      refine ⟨⟨e g, (hmem g).1 g.2⟩, ?_⟩
      apply Subtype.ext; simp [φ]
  have hsemi : ∀ l : Λ, Function.Semiconj E (φ l • ·) (l • ·) := by
    intro l x
    show e ((e.symm l : G) * x) = (l : H) * e x
    simp [map_mul]
  have hF := h𝓜.preimage_of_equiv hqmp hφ hsemi
  have hlt := hfin μ hμ _ hF
  have : μ (E ⁻¹' 𝓜) = π 𝓜 := by
    rw [hμdef, MeasurableEquiv.map_apply]
    congr 1
    ext x; simp
  rw [this] at hlt
  exact hlt.ne

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFrameCols
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem eq_of_frame_cols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g g' : GAd σ J, (matHom _ σ J g).1 * adMat F C = (matHom _ σ J g').1 * adMat F C → (matHom _ σ J g).1 * adMat F Z = (matHom _ σ J g').1 * adMat F Z → (matHom _ σ J g).1 * adMat F D = (matHom _ σ J g').1 * adMat F D → g = g' := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g g' hC hZ hD
  have key : ∀ h : GAd σ J, (matHom _ σ J h).1 =
      (matHom _ σ J h).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J) +
      (matHom _ σ J h).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (matHom _ σ J h).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
    intro h
    have e : (matHom _ σ J h).1 = (matHom _ σ J h).1 * adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) := by
      rw [hF.sum, adMat, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    conv_lhs => rw [e]
    simp only [adMat, Matrix.map_add (inclR (F := F) (E := E) (AF F)) (map_add _), Matrix.map_mul, Matrix.mul_add, Matrix.mul_assoc]
  apply matHom_injective _ σ J
  apply Units.ext
  rw [key g, key g', hC, hZ, hD]

end GlobalTheory.SphEis
end

