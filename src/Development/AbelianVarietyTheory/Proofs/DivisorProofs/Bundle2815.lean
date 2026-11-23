module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCF
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotSameRig

open GlobalTheory.Grid

variable {D : D7}

theorem heisO_smul {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaAt_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    {f₀ Φ f f' : WO S T → ℂ} (ζ : ℂ) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h' : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) Φ f') : f' = ζ • f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) (ζ • Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul]
      vac := by rw [LinearMap.smul_apply, hT.vac] }
  rw [h'.2 _ hT', hall Tm hT, LinearMap.smul_apply]

theorem isVacO_fixSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) :
    IsVacO ψ θ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T) sS sT LS LT f :=
  ⟨h.1, h.2.inf, ⟨h.2.theta.quasi, h.2.theta.level, h.2.theta.cont, h.2.theta.smooth⟩, h.2.lat, h.2.fock, h.2.norm⟩

theorem setIntegral_eq_mul {V : HSp D} (ν₁ ν₂ : Measure (GA D V)) (fd₁ fd₂ : Set (GA D V)) (h₁ : ν₁.IsHaarMeasure)
    (h₂ : ν₂.IsHaarMeasure) (hfd₁ : IsFundamentalDomain (GQ V) fd₁ ν₁) (hfd₂ : IsFundamentalDomain (GQ V) fd₂ ν₂) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) →
      (IntegrableOn f fd₁ ν₁ ↔ IntegrableOn f fd₂ ν₂) ∧ ∫ g in fd₁, f g ∂ν₁ = c * ∫ g in fd₂, f g ∂ν₂ := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hc := Measure.isMulLeftInvariant_eq_smul ν₁ ν₂
  set c₀ : NNReal := Measure.haarScalarFactor ν₁ ν₂ with hc₀
  have hpos : 0 < c₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν₁ ν₂
  have hc0 : (c₀ : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hctop : (c₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsm : (c₀ • ν₂ : Measure (GA D V)) = (c₀ : ENNReal) • ν₂ := rfl
  have hfd₂' : IsFundamentalDomain (GQ V) fd₂ ν₁ := hfd₂.mono (by rw [hc, hsm]; exact Measure.smul_absolutelyContinuous)
  refine ⟨(c₀ : ℂ), by exact_mod_cast hpos.ne', fun f hf => ?_⟩
  have hf' : ∀ (g : GQ V) (x : GA D V), f (g • x) = f x := fun g x => hf g g.2 x
  constructor
  · rw [hfd₁.integrableOn_iff hfd₂' hf', hc, hsm, IntegrableOn, Measure.restrict_smul, integrable_smul_measure hc0 hctop]
    rfl
  · rw [hfd₁.setIntegral_eq hfd₂' hf', hc, hsm, Measure.restrict_smul, integral_smul_measure]
    simp [Complex.real_smul]


set_option maxHeartbeats 1000000 in
theorem const_of_sameRig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  intro D T L sc G W i j A A' WW X Y hX hY hA hA' hW c hc

  have hvX := hX.is.isVac
  have hvY := hY.is.isVac
  rw [← hA, ← hW] at hvY
  have hvX' := hX.is.isVac'
  have hvY' := hY.is.isVac'
  rw [← hA', ← hW] at hvY'
  have hψ : IsStdChar D W.ψ (-1) := hvX.1
  have hθ : IsInfFam W.θ := hvX.2.inf
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hcS' : ∀ τ, IsCartanInv (gramAt D A' τ) (X.rA'.s τ) := fun τ => (hX.is.rigA'.2.2 τ).1
  obtain ⟨ζ, hζ1, hζ⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig (neg A))
    (Formalism.L2.Fam.ThC.fixSig WW) (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS hcT X.rA.Λ X.rW.Λ (GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1) hX.is.rigW.1 X.vac Y.vac (isVacO_fixSig hvX)
    (isVacO_fixSig hvY)
  obtain ⟨ζ', hζ1', hζ'⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig A')
    (Formalism.L2.Fam.ThC.fixSig WW) X.rA'.s X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS' hcT X.rA'.Λ X.rW.Λ hX.is.rigA'.1 hX.is.rigW.1 X.vac' Y.vac' (isVacO_fixSig hvX') (isVacO_fixSig hvY')
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
  have hζ0' : ζ' ≠ 0 := fun h => by rw [h, norm_zero] at hζ1'; exact zero_ne_one hζ1'

  have he : ∀ t, Y.e t = X.e t := fun t => GlobalTheory.BaseKernelUniq.idemSum_unique A (hY.is.idem t) (hX.is.idem t)
  have hid : ∀ t, Y.ideal (locPl G) t = X.ideal (locPl G) t := fun t => by
    unfold Tri.ideal
    exact Finset.prod_congr rfl fun w hw => by rw [(hY.is.expo t w hw).unique (hX.is.expo t w hw)]

  have hf : ∀ t, Y.f t = ζ • X.f t := fun t => by
    have h2 := hY.is.fst t
    rw [← hA, ← hW, he t, hid t, hζ] at h2
    exact thetaAt_smul (S := neg A) ζ (hX.is.fst t) h2
  have hf' : ∀ t, Y.f' t = ζ' • X.f' t := fun t => by
    have h2 := hY.is.snd t
    rw [← hA', ← hW, he t, hid t, hζ'] at h2
    exact thetaAt_smul ζ' (hX.is.snd t) h2

  have thX : ∀ t, IsThetaFunO W.ψ (neg A) WW (X.f t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.fst t) hvX.2.theta
  have thX' : ∀ t, IsThetaFunO W.ψ A' WW (X.f' t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.snd t) hvX'.2.theta

  have hk : ∀ t P h g, Y.ker W.ψ W.θ t P h g = ζ * X.ker W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have hWY : IsWeilDatumO W.ψ (neg A) WW _ _ ((Y.ω t).toSgn true) := hY.is.weil t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ (neg A) WW _ _ _ _ hWY hWX ((ofSgn true A).symm g, h) _ hF
    unfold Tri.ker
    rw [← hA, ← hW, hf t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show ((Y.ω t).toSgn true) ((ofSgn true A).symm g, h) (ζ • _) 0 =
      ζ * ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]
  have hk' : ∀ t P h g, Y.ker' W.ψ W.θ t P h g = ζ' * X.ker' W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have hWY : IsWeilDatumO W.ψ A' WW _ _ (Y.ω' t) := hY.is.weil' t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ A' WW _ _ _ _ hWY hWX (g, h) _ hF
    unfold Tri.ker'
    rw [← hA', ← hW, hf' t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show (Y.ω' t) (g, h) (ζ' • _) 0 = ζ' * (X.ω' t) (g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]

  have inv : ∀ t P h, ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t P h (γ * g) = X.ker W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have e1 : (((ofSgn true A).symm (γ * g), h) : GA D (neg A) × GA D WW) =
        ((ofSgn true A).symm γ, 1) * ((ofSgn true A).symm g, h) := by simp
    show ((X.ω t).toSgn true) ((ofSgn true A).symm (γ * g), h) _ 0 = ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hWX.om_pres _ _ hF)
  have inv' : ∀ t P h, ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t P h (γ * g) = X.ker' W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have e1 : ((γ * g, h) : GA D A' × GA D WW) = (γ, 1) * (g, h) := by simp
    show (X.ω' t) (γ * g, h) _ 0 = (X.ω' t) (g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ hγ 1 (one_mem _) _ (hWX.om_pres _ _ hF)

  obtain ⟨r, hr0, hr⟩ := setIntegral_eq_mul X.m Y.m X.fd Y.fd hX.is.meas.1 hY.is.meas.1 hX.is.meas.2 hY.is.meas.2
  obtain ⟨r', hr0', hr'⟩ := setIntegral_eq_mul X.m' Y.m' X.fd' Y.fd' hX.is.meas'.1 hY.is.meas'.1 hX.is.meas'.2
    hY.is.meas'.2
  have hYk : ∀ t P h, Y.ker W.ψ W.θ t P h = fun g => ζ * X.ker W.ψ W.θ t P h g := fun t P h => funext (hk t P h)
  have hYk' : ∀ t P h, Y.ker' W.ψ W.θ t P h = fun g => ζ' * X.ker' W.ψ W.θ t P h g := fun t P h => funext (hk' t P h)
  have hI : ∀ t P h, X.I W.ψ W.θ t P h = r * ζ⁻¹ * Y.I W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I, Tri.I, hYk, integral_const_mul, (hr _ (inv t P h)).2]
    field_simp
  have hI' : ∀ t P h, X.I' W.ψ W.θ t P h = r' * ζ'⁻¹ * Y.I' W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I', Tri.I', hYk', integral_const_mul, (hr' _ (inv' t P h)).2]
    field_simp
  have hint : ∀ t P h, IntegrableOn (Y.ker W.ψ W.θ t P h) Y.fd Y.m → IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m :=
    fun t P h hi => by
      rw [hYk, IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0)] at hi
      exact (hr _ (inv t P h)).1.2 hi
  have hint' : ∀ t P h, IntegrableOn (Y.ker' W.ψ W.θ t P h) Y.fd' Y.m' →
      IntegrableOn (X.ker' W.ψ W.θ t P h) X.fd' X.m' := fun t P h hi => by
    rw [hYk', IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0')] at hi
    exact (hr' _ (inv' t P h)).1.2 hi

  set κ : ℂ := r * ζ⁻¹ * (r' * ζ'⁻¹)⁻¹ with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact mul_ne_zero (mul_ne_zero hr0 (inv_ne_zero hζ0)) (inv_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')))
  obtain ⟨⟨t₁, h₁⟩, P, P', H⟩ := hc
  have hX1 : X.IsConst W.ψ W.θ fun t => κ * c t := by
    refine ⟨⟨t₁, mul_ne_zero hκ0 h₁⟩, P, P', fun t => ⟨fun h => ⟨hint t P h ((H t).1 h).1, hint' t P' h ((H t).1 h).2⟩,
      ?_, fun h => ?_⟩⟩
    · obtain ⟨h, hh⟩ := (H t).2.1
      refine ⟨h, ?_⟩
      rw [hI']
      exact mul_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')) hh
    · have e := (H t).2.2 h
      have e' : Y.I' W.ψ W.θ t P' h = (r' * ζ'⁻¹)⁻¹ * X.I' W.ψ W.θ t P' h := by
        rw [hI', ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hr0' (inv_ne_zero hζ0')), one_mul]
      rw [hI, e, e', hκ]
      ring
  have := GlobalTheory.BotTransfer.isConst_smul hX1 (inv_ne_zero hκ0)
  simpa only [← mul_assoc, inv_mul_cancel₀ hκ0, one_mul] using this

end GlobalTheory.BotSameRig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfNondeg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilBridge
open GlobalTheory.WeilSchrodinger

theorem det_ne_zero_of_nondeg (D : D7) {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E)
    (h : (sesq D G).Nondegenerate) : G.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  apply h.2 v
  intro x
  have e : ∀ i, ∑ j, G i j * v j = 0 := fun i => by
    have := congrFun hGv i
    simpa [Matrix.mulVec, dotProduct] using this
  simp only [sesq, Matrix.toLinearMapₛₗ₂'_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j _ => mul_comm (v j) (G i j), e i, mul_zero]

theorem exists_isTransport (D : D7) (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig)
    (S T : HSp D) (X : Spc D.host.F D.host.E T.rank) (Y : Spc D.host.F D.host.E S.rank) (r s r' s' : ℕ)
    (hX : X.IsHerm D.sp.cm.sig B r s) (hY : Y.IsSkew D.sp.cm.sig B r' s')
    (eA : X.J = T.gramᵀ)
    (eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Mo : Model D.sp.cm.sig X Y) (hMo : Mo.IsGood B.ψ) (χX χW : Chr D.host.F D.host.E)
    (hcX : GlobalTheory.LFun.IsHecke D.host.F D.host.E χX) (hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E χW)
    (rX : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX T.rank)
    (rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW S.rank)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig X Y) (hom : Mo.IsWeil B.ψ χX χW om) :
    ∃ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO B.ψ S T χW χX ω ∧ IsTransport B.ψ Mo.co ω om := by
  have hψ : IsStdChar D B.ψ (-1) := _root_.GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D B.ψ hB.std
  have rS := _root_.GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow D χW S.rank rW
  have rT := _root_.GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow D χX T.rank rX
  obtain ⟨ω, hω⟩ := GlobalTheory.weilRepresentationUnitaryPair D B.ψ S T χW χX hψ hcW hcX rS rT
  obtain ⟨om₀, hom₀⟩ := _root_.GlobalTheory.ThetaTransform.exists_isTransport D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB
    (Fin T.rank × Fin S.rank) Mo.co hMo.rat ω hω
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h3 := _root_.GlobalTheory.WeilAdm.transport_adm D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h4 := _root_.GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h5 := _root_.GlobalTheory.WeilCont.continuous_transport D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h6 := _root_.GlobalTheory.DblSchr.doubledModel D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h7 := _root_.GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) B.ψ Mo.co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om₀ := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hw₀ : Mo.IsWeil B.ψ χX χW om₀ :=
    ⟨⟨isUSplitting_inr hsp, h6⟩, ⟨transD _ Mo.co, transD_e Mo.co, isUSplitting_inl hsp, h7⟩, h5⟩
  obtain ⟨h1X, h2X, -⟩ := _root_.GlobalTheory.WeilSchrodingerHerm.main D B hB T.rank X r s hX
  obtain ⟨hdY, -⟩ := _root_.GlobalTheory.WeilSchrodingerSkew.main D B hB S.rank Y r' s' hY
  have hdX : X.J.det ≠ 0 := by
    have := det_ne_zero_of_nondeg D X.Jᵀ h2X
    rwa [Matrix.det_transpose] at this
  have huniq := GlobalTheory.T.adelicWeilRep_schrodingerModel_unique D.host.F D.host.E D.sp.cm.sig hB.cm T.rank S.rank X Y Mo B.ψ χX χW hB.std hX.herm hdX
    hY.skew hdY.ne_zero om om₀ hom hw₀
  refine ⟨ω, hω, fun a b g h ha hb Φ hΦ => ?_⟩
  rw [huniq (a, b) Φ hΦ]
  exact hom₀ a b g h ha hb Φ hΦ

theorem thetaTr_zero (D : D7) {W : Type} [AddCommGroup W] [Module (AF D.host.F) W] {Bf : W → W → AF D.host.F}
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux Bf κ) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (κ → AF D.host.F) → ℂ) :
    thetaTr D.host.F d ψ Φ 0 = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  have : GlobalTheory.WeilM.schr ψ (0 : (κ → AF D.host.F) × (κ → AF D.host.F)) Φ = Φ := by
    funext x
    simp [GlobalTheory.WeilM.schr]
  simp [thetaTr, GlobalTheory.WeilM.Darboux.rho, this]

theorem exists_theta_eq (D : D7) (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig)
    (S T : HSp D) (X : Spc D.host.F D.host.E T.rank) (Y : Spc D.host.F D.host.E S.rank) (r s r' s' : ℕ)
    (hX : X.IsHerm D.sp.cm.sig B r s) (hY : Y.IsSkew D.sp.cm.sig B r' s')
    (eA : X.J = T.gramᵀ)
    (eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Mo : Model D.sp.cm.sig X Y) (hMo : Mo.IsGood B.ψ) (χX χW : Chr D.host.F D.host.E)
    (hcX : GlobalTheory.LFun.IsHecke D.host.F D.host.E χX) (hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E χW)
    (rX : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX T.rank)
    (rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW S.rank)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig X Y) (hom : Mo.IsWeil B.ψ χX χW om) :
    ∃ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO B.ψ S T χW χX ω ∧ IsTransport B.ψ Mo.co ω om ∧
      ∀ (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig X.J) (b : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Y.J) (g : GA D S) (h : GA D T),
        mt T h = a.1.1 → mt S g = (b⁻¹).1.1ᵀ → ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin T.rank × Fin S.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ a b = ω (g, h) (thetaTr D.host.F Mo.co B.ψ Φ) 0 := by
  obtain ⟨ω, hω, htr⟩ := exists_isTransport D B hB S T X Y r s r' s' hX hY eA eB Mo hMo χX χW hcX hcW rX rW om hom
  refine ⟨ω, hω, htr, fun a b g h ha hb Φ hΦ => ?_⟩
  rw [← (htr a b g h ha hb Φ hΦ).2, thetaTr_zero]
  rfl

end GlobalTheory.WeilBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Theory

theorem frobProj_omega_surjective {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (G : PDivGroup p k) : Function.Surjective (frobProj (p_eq_zero p k) G).omega := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  intro t
  obtain ⟨x, rfl⟩ := (omega_baseChange_bijective G k (p_eq_zero p k)).2 t
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ x y).symm)⟩
  | tmul r w =>
    refine ⟨(frobeniusEquiv k p).symm r • w, ?_⟩
    rw [liftSemi_tmul, map_smulₛₗ]
    congr 1
    show frobRing (p_eq_zero p k) _ = r
    rw [frobRing_apply, frobeniusEquiv_symm_pow_p]

theorem hodge_filtration : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), (∀ x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧ (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ m, G.rigToLie (p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧ Function.Injective G.rigOfOmega := by
  intro p _ T k _ _ _ G
  obtain ⟨-, hVinj, hVsm, -, -⟩ := _root_.GlobalTheory.Dieu.theory_V_verschiebung p T k G
  obtain ⟨hbij, -, -⟩ := _root_.GlobalTheory.Dieu.frobTwist_module p T.base k G
  obtain ⟨-, -, -, hver, -, -, -⟩ := rigExt_field_of_charP p k (p_eq_zero p k) G
  have key : ∀ m, SemiHom.rig (frobProj (p_eq_zero p k) G) (T.red G (T.V G m)) =
      rigExtMap (verschiebung (p_eq_zero p k) G) (T.red G m) := by
    intro m
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), hVsm]
    rw [← SemiHom.ofHom_rig]
    exact T.base.red_smap trivial trivial (SemiHom.ofHom _) m
  have rinj : Function.Injective (frobProj (p_eq_zero p k) G).rig := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial x
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G)] at hx
    have hx' := (T.base.red_eq_zero (frobTwist (p_eq_zero p k) G) trivial _).1 hx
    clear hx
    obtain ⟨n, hn⟩ := hx'
    obtain ⟨n', rfl⟩ := hbij.2 n
    have hm : m = p • n' := hbij.1 (by rw [hn, map_nsmul])
    exact (T.base.red_eq_zero G trivial m).2 ⟨n', hm⟩
  have osurj := frobProj_omega_surjective G
  have h1 : ∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega := by
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      have hm : SemiHom.rig (frobProj (p_eq_zero p k) G) (T.red G (T.V G m)) ∈
          LinearMap.range (frobTwist (p_eq_zero p k) G).rigOfOmega := by
        rw [key, ← hver]; exact ⟨_, rfl⟩
      obtain ⟨w', hw'⟩ := hm
      obtain ⟨w, rfl⟩ := osurj w'
      exact ⟨w, rinj ((SemiHom.rig_rigOfOmega _ w).trans hw')⟩
    · rintro ⟨w, rfl⟩
      have hw : (frobTwist (p_eq_zero p k) G).rigOfOmega (SemiHom.omega (frobProj (p_eq_zero p k) G) w) ∈
          LinearMap.range (rigExtMap (verschiebung (p_eq_zero p k) G)) := by
        rw [hver]; exact ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := hw
      obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial y
      exact ⟨m, rinj ((key m).trans (hy.trans (SemiHom.rig_rigOfOmega _ w).symm))⟩
  have h2 : ∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n := by
    intro m
    refine (T.base.red_eq_zero G trivial _).trans ⟨fun ⟨n, hn⟩ => ⟨n, hVinj ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
    · rw [hn]; exact (T.V_F G n).symm
    · rw [hn]; exact T.V_F G n
  refine ⟨h1, h2, fun m => ?_, G.rigOfOmega_injective_of_eq_zero (p_eq_zero p k)⟩
  rw [G.exact_rigOfOmega_rigToLie (p_eq_zero p k) (T.red G m)]
  constructor
  · intro hm
    obtain ⟨m', hm'⟩ := (h1 _).2 hm
    have h0 : T.red G (m - T.V G m') = 0 := by rw [map_sub, hm', sub_self]
    obtain ⟨n, hn⟩ := (T.base.red_eq_zero G trivial _).1 h0
    refine ⟨m' + T.F G n, ?_⟩
    rw [map_add (f := _), T.V_F G n, ← hn, add_sub_cancel]
  · rintro ⟨n, rfl⟩
    obtain ⟨w, hw⟩ := (h1 (T.red G (T.V G n))).1 ⟨n, rfl⟩
    exact ⟨w, hw⟩

end GlobalTheory.Dieu.Theory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSectionRatioEqNearThickeningPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem eq_of_secRatioEq_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k), w ∈ N ∧ ∀ (W : Scheme.{0}) (a b : W ⟶ (thickObj R (maximalIdeal R) e G).left), a ≫ (thickObj R (maximalIdeal R) e G).hom = b ≫ (thickObj R (maximalIdeal R) e G).hom → (∀ x, a x ∈ N) → (∀ x, b x ∈ N) → (∀ l, SecRatioEq U.LG.L (a ≫ (fstG (maximalIdeal R) e G).left) (b ≫ (fstG (maximalIdeal R) e G).left) (σ l) s₀ (σ l) s₀) → a = b := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₀, hk₀, H⟩ := GlobalTheory.T.exists_section_ratios_generate_mod_maximal R hB D A G hG U
  refine ⟨k₀, hk₀, fun e k hk s₀ i w hw hu => ?_⟩
  obtain ⟨N, m, σ, r, hwN, hNaff, hNi, hgerm, hgen⟩ := H e k hk s₀ i w hw hu
  have hw' : (fstG (maximalIdeal R) e G).left ≫ G.hom = (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e :=
    (fstG (maximalIdeal R) e G).w
  have hz : ∀ x ∈ maximalIdeal R ^ (e + 1), (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) x = 0 := by
    intro x hx
    have h0 : (thick R (maximalIdeal R) e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = 0 := by
      have := congrArg (fun φ => φ.hom x)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      rw [← this, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, hw', Scheme.Hom.comp_appTop, CommRingCat.hom_comp, h0, map_zero]
  have hgen' := _root_.GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent R _ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) (e + 1) hz m r hgen
  refine ⟨N, m, σ, hwN, fun W a b hab ha hb hrat => ?_⟩
  have ha' : ⊤ ≤ a ⁻¹ᵁ N := fun x _ => ha x
  have hb' : ⊤ ≤ b ⁻¹ᵁ N := fun x _ => hb x
  have hst : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (f : Γ((thickObj R (maximalIdeal R) e G).left, N)), c x ∈ N →
      (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) = gs c x N f := by
    intro c x f h
    have e1 : gs (c ≫ 𝟙 _) x N f = (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) := by
      rw [gs_eq (𝟙 _) (c x) _ h, ← gs_pull c (𝟙 _) x _ h, gs_eq c x _ (show c x ∈ (𝟙 (thickObj R (maximalIdeal R) e G).left : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) ⁻¹ᵁ N from h)]
      exact (Scheme.Hom.germ_stalkMap_apply c _ x h _).symm
    rw [← e1, Category.comp_id]
  have hsg : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (s : H0 U.LG.L k), c x ∈ N →
      secGerm (c ≫ (fstG (maximalIdeal R) e G).left) x s i = (c.stalkMap x).hom (secGerm (fstG (maximalIdeal R) e G).left (c x) s i) :=
    fun c x s h => secGerm_comp c _ x s (hNi h)
  refine GlobalTheory.T.eq_of_agree_on_affineOpen_generators R _ W ((fstG (maximalIdeal R) e G).left ≫ G.hom) N hNaff m r hgen' a b ?_ ha' hb' ?_
  · rw [hw', ← Category.assoc, hab, Category.assoc]
  · intro l
    apply fn_ext
    intro x _
    rw [gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_pull (𝟙 W) a x N (ha x), gs_pull (𝟙 W) b x N (hb x), Category.id_comp, Category.id_comp]
    have key := secRatioEq_iff_germ.1 (hrat l) x i i (hNi (ha x)) (hNi (hb x))
    rw [hsg a x _ (ha x), hsg a x _ (ha x), hsg b x _ (hb x), hsg b x _ (hb x),
      (hgerm _ (ha x)).2 l, (hgerm _ (hb x)).2 l, map_mul, map_mul, hst a x _ (ha x), hst b x _ (hb x)] at key
    have hA := ((hgerm _ (ha x)).1).map (a.stalkMap x).hom
    have hB := ((hgerm _ (hb x)).1).map (b.stalkMap x).hom
    refine (hA.mul hB).mul_left_inj.1 ?_
    linear_combination key

end GlobalTheory.Mum
end
end

