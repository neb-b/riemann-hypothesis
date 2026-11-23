module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestTypePositiveAndDecays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceFockDsUniqueness
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPos
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSpaceContainsDiscreteSeriesTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.SignedRename

open MvPolynomial

section General

variable {ι κ : Type} (σ : ι ≃ κ) (s : ι → ℂ)

def ren : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ := aeval fun v => s v • (X (σ v) : MvPolynomial κ ℂ)

theorem ren_monomial (k : ι →₀ ℕ) (c : ℂ) :
    ren σ s (monomial k c) = monomial (k.mapDomain σ) ((k.prod fun v n => s v ^ n) * c) := by
  classical
  have h1 : ∀ (v : ι) (n : ℕ), (s v • (X (σ v) : MvPolynomial κ ℂ)) ^ n =
      C (s v ^ n) * monomial (Finsupp.single (σ v) n) 1 := by
    intro v n
    rw [smul_pow, X_pow_eq_monomial, smul_eq_C_mul]
  rw [ren, aeval_monomial, Finsupp.mapDomain, monomial_finsupp_sum_index]
  simp only [Finsupp.prod, h1, Finset.prod_mul_distrib, algebraMap_eq]
  rw [← map_prod, C_mul]
  ring

theorem coeff_ren (k : ι →₀ ℕ) (P : MvPolynomial ι ℂ) :
    AddMonoidAlgebra.coeff (ren σ s P) (k.mapDomain σ) = (k.prod fun v n => s v ^ n) * AddMonoidAlgebra.coeff P k := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [ren_monomial, coeff_monomial, coeff_monomial]
    by_cases hm : m = k
    · subst hm
      simp
    · rw [if_neg hm, if_neg (fun h => hm (Finsupp.mapDomain_injective σ.injective h)), mul_zero]
  | add P Q hP hQ => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hP, hQ, mul_add]

theorem isHomogeneous_ren {ι κ : Type} (f : ι → κ) (s : ι → ℂ) (d : ℕ) (P : MvPolynomial ι ℂ) (h : P.IsHomogeneous d) :
    (aeval (fun v => s v • (X (f v) : MvPolynomial κ ℂ)) P).IsHomogeneous d := by
  have hg : ∀ v, (s v • (X (f v) : MvPolynomial κ ℂ)).IsHomogeneous 1 := by
    intro v
    rw [smul_eq_C_mul]
    exact isHomogeneous_C_mul_X _ _
  have h0 : ∀ r : ℂ, (algebraMap ℂ (MvPolynomial κ ℂ) r).IsHomogeneous 0 := fun r => isHomogeneous_C κ r
  rw [aeval_def]
  simpa only [one_mul] using h.eval₂ (algebraMap ℂ (MvPolynomial κ ℂ)) _ h0 hg

theorem fockIp_ren (hs : ∀ v, s v * conj (s v) = 1) (P Q : MvPolynomial ι ℂ) :
    fockIp (ren σ s P) (ren σ s Q) = fockIp P Q := by
  classical
  have hs0 : ∀ v, s v ≠ 0 := fun v h0 => by simpa [h0] using hs v
  have hp : ∀ k : ι →₀ ℕ, (k.prod fun v n => s v ^ n) ≠ 0 := by
    intro k
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hs0 v)
  have hpc : ∀ k : ι →₀ ℕ, (k.prod fun v n => s v ^ n) * conj (k.prod fun v n => s v ^ n) = 1 := by
    intro k
    rw [Finsupp.prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [map_pow, ← mul_pow, hs v, one_pow]
  have hback : ∀ k' : κ →₀ ℕ, (k'.mapDomain σ.symm).mapDomain σ = k' := by
    intro k'
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hfwd : ∀ k : ι →₀ ℕ, (k.mapDomain σ).mapDomain σ.symm = k := by
    intro k
    rw [← Finsupp.mapDomain_comp, Equiv.symm_comp_self, Finsupp.mapDomain_id]
  have hc : ∀ (R : MvPolynomial ι ℂ) (k' : κ →₀ ℕ), AddMonoidAlgebra.coeff (ren σ s R) k' =
      ((k'.mapDomain σ.symm).prod fun v n => s v ^ n) * AddMonoidAlgebra.coeff R (k'.mapDomain σ.symm) := by
    intro R k'
    conv_lhs => rw [← hback k']
    exact coeff_ren σ s _ R
  unfold fockIp
  refine Finset.sum_nbij' (fun k' => k'.mapDomain σ.symm) (fun k => k.mapDomain σ) ?_ ?_ ?_ ?_ ?_
  · intro k' hk'
    rw [mem_support_iff] at hk' ⊢
    rw [hc] at hk'
    exact right_ne_zero_of_mul hk'
  · intro k hk
    rw [mem_support_iff] at hk ⊢
    rw [coeff_ren]
    exact mul_ne_zero (hp k) hk
  · intro k' _
    exact hback k'
  · intro k _
    exact hfwd k
  · intro k' _
    have hF : ((k'.prod fun _ e => e.factorial : ℕ) : ℂ) =
        (((k'.mapDomain σ.symm).prod fun _ e => e.factorial : ℕ) : ℂ) := by
      have := Finsupp.prod_mapDomain_index_inj (h := fun (_ : κ) (e : ℕ) => e.factorial) σ.injective
        (s := k'.mapDomain σ.symm)
      rw [hback] at this
      rw [this]
    rw [hc P, hc Q, hF, map_mul]
    have := hpc (k'.mapDomain σ.symm)
    calc _ = (((k'.mapDomain σ.symm).prod fun v n => s v ^ n) *
          conj ((k'.mapDomain σ.symm).prod fun v n => s v ^ n)) *
          (AddMonoidAlgebra.coeff P (k'.mapDomain σ.symm) * conj (AddMonoidAlgebra.coeff Q (k'.mapDomain σ.symm)) *
          (((k'.mapDomain σ.symm).prod fun _ e => e.factorial : ℕ) : ℂ)) := by ring
      _ = _ := by rw [this, one_mul]

end General


open GlobalTheory.Chain.RealIt.PolyIso in
theorem exists_isPolyIso_graded_isometry : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), SignCompat ε e → SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ ∧ Graded κ ∧ ∀ P Q, fockIp (κ P) (κ Q) = fockIp P Q := by
  intro p q r s a b ε ε' e e' h h'
  refine ⟨(kap ε e e').toLinearEquiv, ⟨fun Z P => fwd_locS h h' Z P, fun Z P => fwd_locT h h' Z P⟩, ?_, ?_⟩
  · intro d P
    constructor
    · intro hP
      have hb : bwd ε e e' ((kap ε e e').toLinearEquiv P) = P := (kap ε e e').symm_apply_apply P
      rw [← hb]
      exact isHomogeneous_ren (fun l : Ix p q × Ix r s => (e' l.2, e l.1))
        (fun l => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε (e l.1))) d _ hP
    · intro hP
      exact isHomogeneous_ren (fun v : Fin b × Fin a => (e.symm v.2, e'.symm v.1))
        (fun v => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) d P hP
  · intro P Q
    let τ : Fin b × Fin a ≃ Ix p q × Ix r s := (Equiv.prodComm _ _).trans (Equiv.prodCongr e.symm e'.symm)
    have hs : ∀ v : Fin b × Fin a, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2) * conj (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) = 1 := by
      intro v
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn
      split <;> simp
    exact fockIp_ren τ (fun v => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) hs P Q

end GlobalTheory.ArchRec.SignedRename

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameChangeWeakWeilRepresentation
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem isThetaFunO_reF (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ (reS S b) T (reF S T b f) := {
  quasi γ w := by
    show f (reW S T b (ratW T (reS S b) γ + w)) = ψ (-(symplOH (reS S b) T (ratW T (reS S b) γ) w)) * f (reW S T b w)
    rw [reW_add, ← symplOH_reW, reW_ratW S T b γ]
    exact hf.quasi _ _
  level := by
    obtain ⟨U, hU, hfU⟩ := hf.level
    refine ⟨U.comap (reWAdd S T b), hU.preimage (reW_continuous S T b), fun u hu hu0 => ?_⟩
    rw [heisO_reF]
    exact congrArg (reF S T b) (hfU _ hu ((reW_map_eq_zero S T b _ u).2 hu0))
  cont := hf.cont.comp (reW_continuous S T b)
  smooth k L hL hL0 w := by
    have := hf.smooth k ((reWAdd S T b).comp L) ((reW_continuous S T b).comp hL)
      (fun t => (reW_map_eq_zero S T b _ (L t)).2 (hL0 t)) (reW S T b w)
    have e : (fun t => reF S T b f (w + L t)) = fun t => f (reW S T b w + (reWAdd S T b).comp L t) :=
      funext fun t => by rw [reF_apply, reW_add]; rfl
    rw [e]; exact this }

theorem isThetaFunO_of_reF (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ (reS S b) T (reF S T b f)) : IsThetaFunO ψ S T f := by
  have h := isThetaFunO_reF (reS S b) T S.frame ψ _ hf
  have e : reF (reS S b) T S.frame (reF S T b f) = f := by
    funext x
    exact congrArg f (reW_reWinv S T b x)
  rw [e] at h
  exact h

section Meas

theorem reW_fd (μ : Measure (WO (reS S b) T)) (𝓕 : Set (WO (reS S b) T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T (reS S b)) 𝓕 μ) :
    (μ.map (reW S T b)).IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratL T S) (reWinv S T b ⁻¹' 𝓕) (μ.map (reW S T b)) := by
  have hTR : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : BorelSpace (WO (reS S b) T) := ⟨rfl⟩
  let eA : WO (reS S b) T ≃+ WO S T :=
    { toFun := reW S T b
      invFun := reWinv S T b
      left_inv := reWinv_reW S T b
      right_inv := reW_reWinv S T b
      map_add' := reW_add S T b }
  let eM : WO (reS S b) T ≃ᵐ WO S T := (reWHomeo S T b).toMeasurableEquiv
  refine ⟨AddEquiv.isAddHaarMeasure_map μ eA (reW_continuous S T b) (reWinv_continuous S T b), ?_⟩
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL T (reS S b) → ratL T S := fun g => ⟨reW S T b g, (mem_ratL_reW S T b _).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨reWinv S T b g, (mem_ratL_reW S T b _).1 (by rw [reW_reWinv]; exact g.2)⟩, ?_⟩⟩
    · have e := congrArg (fun x : ratL T S => reWinv S T b (x : WO S T)) hg
      simp only [eG, reWinv_reW] at e
      exact Subtype.ext e
    · exact Subtype.ext (reW_reWinv S T b _)
  refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
  show reWinv S T b (reW S T b g + x) = (g : WO (reS S b) T) + reWinv S T b x
  rw [reWinv_add, reWinv_reW]

theorem setLIntegral_reW (μ : Measure (WO (reS S b) T)) (𝓕 : Set (WO (reS S b) T))
    (F : WO S T → ENNReal) :
    ∫⁻ w in 𝓕, F (reW S T b w) ∂μ = ∫⁻ x in reWinv S T b ⁻¹' 𝓕, F x ∂(μ.map (reW S T b)) := by
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : BorelSpace (WO (reS S b) T) := ⟨rfl⟩
  let eM : WO (reS S b) T ≃ᵐ WO S T := (reWHomeo S T b).toMeasurableEquiv
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have e1 := hmp.setLIntegral_comp_preimage_emb eM.measurableEmbedding F (reWinv S T b ⁻¹' 𝓕)
  have hpre : eM ⁻¹' (reWinv S T b ⁻¹' 𝓕) = 𝓕 := by
    ext w
    show reWinv S T b (reW S T b w) ∈ 𝓕 ↔ w ∈ 𝓕
    rw [reWinv_reW]
  rw [hpre] at e1
  exact e1

end Meas

section Weil

def omRe (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D (reS S b) × GA D T →* Module.End ℂ (WO (reS S b) T → ℂ) where
  toFun p := (reFEquiv S T b).toLinearMap ∘ₗ om (reGrp S b p.1, p.2) ∘ₗ (reFEquiv S T b).symm.toLinearMap
  map_one' := by
    ext f x
    show (reFEquiv S T b) ((om (reGrp S b 1, 1)) ((reFEquiv S T b).symm f)) x = f x
    rw [map_one, Prod.mk_one_one, map_one, one_apply_eq_self, LinearEquiv.apply_symm_apply]
  map_mul' p q := by
    ext f x
    simp [Prod.fst_mul, Prod.snd_mul, ← Prod.mk_mul_mk, map_mul]

theorem omRe_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D (reS S b)) (g : GA D T)
    (f' : WO (reS S b) T → ℂ) :
    omRe S T b om (h, g) f' = reF S T b (om (reGrp S b h, g) ((reFEquiv S T b).symm f')) := rfl

theorem omRe_reF (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D (reS S b)) (g : GA D T)
    (f : WO S T → ℂ) : omRe S T b om (h, g) (reF S T b f) = reF S T b (om (reGrp S b h, g) f) := by
  have e : (reFEquiv S T b).symm (reF S T b f) = f := (reFEquiv S T b).symm_apply_apply f
  rw [omRe_apply, e]

theorem reF_symm (f' : WO (reS S b) T → ℂ) : reF S T b ((reFEquiv S T b).symm f') = f' :=
  (reFEquiv S T b).apply_symm_apply f'

theorem isWeak_omRe (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (hom : IsWeak ψ S T om) : IsWeak ψ (reS S b) T (omRe S T b om) := by
  constructor
  · intro p f' hf'
    obtain ⟨h, g⟩ := p
    rw [omRe_apply]
    refine isThetaFunO_reF S T b ψ _ (hom.om_pres _ _ (isThetaFunO_of_reF S T b ψ _ ?_))
    rw [reF_symm]; exact hf'
  · intro h g w₀ f' hf'
    set f := (reFEquiv S T b).symm f' with hf
    have hf1 : f' = reF S T b f := (reF_symm S T b f').symm
    have hth : IsThetaFunO ψ S T f := isThetaFunO_of_reF S T b ψ _ (by rw [← hf1]; exact hf')
    rw [hf1, heisO_reF, omRe_reF, omRe_reF, hom.om_heis _ _ _ _ hth, ← reW_actO, heisO_reF]
  · intro γ hγ γ' hγ' f' hf'
    have hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f') :=
      isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')
    rw [omRe_apply, reF_apply, reW_zero, hom.om_aut _ (reGrp_mem_GQ S b γ hγ) _ hγ' _ hth]
    conv_rhs => rw [← reF_symm S T b f']
    exact (reF_zero b _).symm
  · intro μ 𝓕 hμ h𝓕 p f' hf'
    obtain ⟨h, g⟩ := p
    have hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f') :=
      isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')
    obtain ⟨hν, h𝓕'⟩ := reW_fd S T b μ 𝓕 hμ h𝓕
    have e1 := setLIntegral_reW S T b μ 𝓕 fun x => ‖om (reGrp S b h, g) ((reFEquiv S T b).symm f') x‖ₑ ^ 2
    have e2 := setLIntegral_reW S T b μ 𝓕 fun x => ‖(reFEquiv S T b).symm f' x‖ₑ ^ 2
    have e3 := hom.om_unit _ _ hν h𝓕' (reGrp S b h, g) _ hth
    have e4 : (fun w => ‖f' w‖ₑ ^ 2) = fun w => ‖(reFEquiv S T b).symm f' (reW S T b w)‖ₑ ^ 2 := by
      funext w
      conv_lhs => rw [← reF_symm S T b f']
      rfl
    rw [e4]
    exact e1.trans (e3.trans e2.symm)

theorem contT_omRe (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (hc : ContT ψ om) : ContT ψ (omRe S T b om) := by
  intro f' hf' w
  have hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f') :=
    isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')
  have e : (fun g : GA D T => omRe S T b om (1, g) f' w) =
      fun g => om (1, g) ((reFEquiv S T b).symm f') (reW S T b w) := by
    funext g
    rw [omRe_apply, reF_apply, map_one]
  rw [e]
  exact hc _ hth _

end Weil

theorem reframe_weil : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V),
    ∃ e : GA D (reS S b) ≃* GA D S, (∀ h, e h ∈ GinfC S ↔ h ∈ GinfC (reS S b)) ∧
      ∀ (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
        IsWeak ψ S T om → ContT ψ om →
        ∃ om' : GA D (reS S b) × GA D T →* Module.End ℂ (WO (reS S b) T → ℂ),
          IsWeak ψ (reS S b) T om' ∧ ContT ψ om' ∧
            ∀ h g f, om' (h, g) (reF S T b f) = reF S T b (om (e h, g) f) := by
  intro D S T b
  exact ⟨reGrp S b, reGrp_mem_GinfC S b, fun ψ om hom hc =>
    ⟨omRe S T b om, isWeak_omRe S T b ψ om hom, contT_omRe S T b ψ om hc, fun h g f => omRe_reF S T b om h g f⟩⟩

end GlobalTheory.AdSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GfCut

variable {R : Type} [CommRing R] {n : ℕ}

theorem idem_mul (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {T : Type} [CommRing T] (ψ : R →+* T) (f : R) (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add (f := _),
    map_mul, map_sub, map_one]
  split_ifs <;> simp

theorem idem_unitary (σ : R →+* R) (ε : R) (hε : σ ε = ε) (hεε : ε * ε = ε) (J M : Matrix (Fin n) (Fin n) R)
    (h : Formalism.UG.cT σ M * J * M = J) :
    Formalism.UG.cT σ (ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * J * (ε • M + (1 - ε) • 1) = J :=
  _root_.GlobalTheory.TruncationIsometry.cut_isometry σ ε hε hεε J M h

end GlobalTheory.GfCut

open GlobalTheory.GfCut in
theorem GlobalTheory.GfCut.exists_cut : ∀ {D : D7} (T : HSp D) (g : GA D T) (ε : AE D), g ∈ GfC T → ε * ε = ε → cA D ε = ε → ∃ k : GA D T, k ∈ GfC T ∧ Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
  intro D T g ε hg hεε hε
  set M := Formalism.L2.Theta.mt T g with hM
  have hinv : M * ((matHom T g)⁻¹).1 = 1 := (matHom T g).mul_inv
  have hinv' : ((matHom T g)⁻¹).1 * M = 1 := (matHom T g).inv_mul
  let K : GL (Fin T.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom T g)⁻¹).1 + (1 - ε) • 1,
    idem_mul ε hεε _ _ hinv, idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * T.gram.map (incA D) * M = T.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig T.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig T.gram :=
    idem_unitary (cA D) ε hε hεε _ M hgU
  let k : GA D T := (⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig T.gram)
  refine ⟨k, ?_, rfl⟩
  have hg1 : infHom T g = 1 := hg
  show infHom T k = 1
  have hg2 := congrArg Units.val hg1
  apply Units.ext
  change (ε • M + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))).map _ = 1
  rw [map_idem]
  change M.map _ = 1 at hg2
  rw [hg2, ← add_smul, add_sub_cancel, one_smul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARParts
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta

namespace GlobalTheory.RealPlaceTheta

theorem exists_record_theta :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    ∃ X : ProvA, (∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam) ∧
      DiscreteSeriesBlattner X ∧ admQ5 X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X ∧ ArchimedeanRallisUpDownLine X ∧ ArchimedeanRallisFifth X := by
  intro hDS hHC

  obtain ⟨X, hX⟩ := GlobalTheory.exists_provA_of_forall_exists_hasParam fun p q T lam hl =>
    GlobalTheory.CoverDS.exists_hasParam hDS p q T lam hl
  have hH1 : admH1 X := GlobalTheory.FockDeg.degrees_and_adjoints X
  have hH2 : admH2 X := GlobalTheory.FockAlg.fock_structure X
  have hD1 : DiscreteSeriesBlattner X := GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hDS X hX
  have hQ5 : admQ5 X := GlobalTheory.Published.HarishChandraModules.admQ5_of_harishChandraModules hHC X
  have hQ6 : CoverHaarIntegration X := _root_.GlobalTheory.PolarU.polar_coordinates X
  have hQ7 : admQ7 := TensorHW.highestWeight_tensor
  have hQ8 : admQ8 := GlobalTheory.InducedPBW.pbw_induced
  have hD2 : DiscreteSeriesPositivity X := GlobalTheory.SphJet.lowest_type_positive_and_decays X hD1 hQ5 hQ7 hQ8
  have hA1 : ArchimedeanRallisFirst X := _root_.GlobalTheory.DoublingPos.doubling_pos X hH1 hH2 hD1 hD2 hQ5 hQ6 hQ7 hQ8
  have hA2 : ArchimedeanRallisSecond X := _root_.GlobalTheory.FockTensor.fock_contains_tensor X hH1 hH2 hD1 hD2 hQ5 hQ6 hQ7 hQ8 hA1
  have hA3 : ArchimedeanRallisUpDownLine X := _root_.GlobalTheory.ThetaUnique.theta_unique X hH1 hH2 hD1 hQ5 hQ7 hQ8 hA1 hA2
  have hA5 : ArchimedeanRallisFifth X := _root_.GlobalTheory.SmallerSource.no_map_smaller_source X hH1 hH2 hD1 hQ5
  exact ⟨X, hX, hD1, hQ5, hA1, hA2, hA3, hA5⟩

end GlobalTheory.RealPlaceTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicMemFrameStabilizerOfLatticeTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevMov

theorem finE_mem_St_of_isMov : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, IsMov (fmt V k) L L → Lev.finE V k ∈ Formalism.L2.DIV.St β := by
  intro D V L β hβ k hk
  have h1 := GlobalTheory.LevSplit.mem_St_iff β L hβ (Lev.finE V k)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff L) (finHom V k)
  refine h1.2 (h2.1 ?_)
  have hk' : ∀ u, u ∈ hatV L ↔ ∃ u₀ ∈ hatV L, u = (finHom V k).1 *ᵥ u₀ := hk
  intro y
  constructor
  · intro hy
    exact (hk' _).2 ⟨y, hy, rfl⟩
  · intro hy
    obtain ⟨u₀, hu₀, e⟩ := (hk' _).1 hy
    have e2 : y = u₀ := by
      have := congrArg (fun z => ((finHom V k)⁻¹).1 *ᵥ z) e
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
      exact this
    rw [e2]; exact hu₀

end GlobalTheory.LevMov
end

