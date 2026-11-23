module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyCV
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyNF
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.Carrier.EnergyNF

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace Formalism.L2.SG.Pf.Carrier.EnergyFinal Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lintegral_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)] (F : ι → E → ℝ≥0∞) (hF : ∀ i, Measurable (F i)) :
    ∫⁻ x, ∏ i, F i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, F i y ∂(μ i) := by
  have hm : Measurable (fun x : ι → E => ∏ i, F i (x i)) :=
    Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i)
  have key : ∀ s : Finset ι, ∀ x : ι → E,
      (∫⋯∫⁻_s, (fun x : ι → E => ∏ i, F i (x i)) ∂μ) x = (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ i ∈ sᶜ, F i (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | insert i s hi ih =>
      intro x
      rw [lmarginal_insert _ hm hi]
      simp_rw [ih]
      have hsplit : ∀ y, ∏ j ∈ sᶜ, F j (Function.update x i y j) = F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j) := by
        intro y
        have hic : i ∈ sᶜ := Finset.mem_compl.2 hi
        rw [← Finset.mul_prod_erase _ _ hic, Function.update_self, Finset.compl_insert]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      simp_rw [hsplit]
      have h2 : ∀ y, (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * (F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j)) =
          ((∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ j ∈ (insert i s)ᶜ, F j (x j)) * F i y := fun y => by ring
      simp_rw [h2]
      rw [lintegral_const_mul _ (hF i), Finset.prod_insert hi]
      ring
  rw [lintegral_eq_lmarginal_univ (fun _ => Classical.arbitrary E), key, Finset.compl_univ, Finset.prod_empty,
    mul_one]

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

theorem intCe_eq_prodE (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (hL : LocRep X u u' L) :
    intCe X u u' 1 = ∏ v, ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) := by
  obtain ⟨hpos, hLc⟩ := hL
  have hG : MeasurableSet (Good X u u') := by
    rw [good_eq_pi]; exact MeasurableSet.univ_pi fun _ => goodV_meas u u'
  have hpt : ∀ c ∈ Good X u u', ENNReal.ofReal (Formalism.L2.SG.RealObj.wt X u u' c * hilbertSchmidtSqGram X u u' 1 c) =
      ∏ v, ENNReal.ofReal (wtV u u' (c v) * L v (c v)) := by
    intro c hc
    have hcv : ∀ v, c v ∈ GoodV u u' := fun v => hc v
    rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ =>
      mul_nonneg (wtV_nonneg u u' (hcv v)) ((hpos v).2 _))]
    congr 1
    have hO : hilbertSchmidtSqGram X u u' 1 c = ∏ v, L v (c v) := by
      unfold hilbertSchmidtSqGram
      rw [hilbert_schmidt_tensor_product_factor]
      exact Finset.prod_congr rfl fun v _ => hLc c hc v
    rw [hO, Finset.prod_mul_distrib]
    rfl
  unfold intCe
  rw [setLIntegral_congr_fun hG hpt, good_eq_pi]
  have h2s : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
    have h : ((2 : ℝ≥0∞) • (volume : Measure ℂ)) = ((2 : NNReal) • (volume : Measure ℂ)) := by
      rw [ENNReal.smul_def]; simp
    rw [h]; infer_instance
  unfold dcInf
  rw [Measure.restrict_pi_pi]
  have hdc : SigmaFinite ((dcV (D := D)).restrict (GoodV u u')) := by unfold dcV; infer_instance
  rw [show (Measure.pi fun _ : Fin (D.R.rS + 1) => (2 : ℝ≥0∞) • (volume : Measure ℂ)) = dcV (D := D) from rfl]
  exact lintegral_pi_prod _ (fun v cv => ENNReal.ofReal (wtV u u' cv * L v cv))
    (fun v => ENNReal.measurable_ofReal.comp ((wtV_cont u u').measurable.mul (hpos v).1))

def PlaceEnergyE (P : Parts X u u') (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  ∀ v, ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) =
    ENNReal.ofReal (K v) * Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))

theorem energyNorm_of_stepsE (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (K : InfinitePlace X.B.I.F → ℝ)
    (h1 : LocRep X u u' L) (h2 : PlaceEnergyE P L K) (h3 : ConstPin P ψ K) :
    P.EnergyNorm (IntNX X u u' ψ) := by
  set n : InfinitePlace X.B.I.F → ℝ :=
    fun v => (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal with hn
  have hC : IntC X u u' 1 = (∏ v, K v) * ∏ v, n v := by
    unfold IntC
    rw [intCe_eq_prodE L h1]
    rw [Finset.prod_congr rfl (fun v _ => h2 v)]
    rw [ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h3.1 v)]
  unfold Parts.EnergyNorm IntNX
  rw [hC]
  have hre : (∏ j, (Formalism.FourierDecayAlt.B.normSq (P.T j).base (P.f j)).toReal / P.Gam0) =
      (∏ v, n v) * (P.Gam0 ^ P.S.f)⁻¹ := by
    rw [← Equiv.prod_comp P.τ.symm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      ← Fintype.card_congr P.τ, Fintype.card_fin, div_eq_mul_inv]
  rw [hre, ← h3.2]
  ring

theorem placeEnergyE_of_steps (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (hPN : PlaceNorm P hr L) (hCV : ChangeVar P hr) :
    PlaceEnergyE P L (fun _ => EnergyConst.Kexp P) := by
  intro v
  rw [setLIntegral_congr_fun (goodV_meas u u') (fun cv hcv => by rw [hPN v cv hcv])]
  rw [hCV hk hT v (fun q => ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
      (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base q))‖ ^ 2) (fun q => by positivity)]
  rw [← Formalism.L2.SG.Pf.Carrier.EnergyKM.kMatch_holds P hg hrd hr hk hg0 hk1]
  rfl

theorem energyNorm_bookY_of_placeNormG_of_changeVar (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst.LemmaMS X u u' ψ)
    (hPN : PlaceNormG P hr) (hCV : ChangeVar P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN := by
  obtain ⟨L, hL⟩ := Formalism.L2.SG.Pf.Carrier.EnergyPfLoc.locRep_holds X u u'
  rw [intN_massDataY]
  exact energyNorm_of_stepsE P ψ L (fun _ => EnergyConst.Kexp P) hL
    (placeEnergyE_of_steps P hr hk hT hg hrd hg0 hk1 L (placeNorm_of_G P hr hPN L hL) hCV)
    (EnergyConst.constPin_of P ψ hC hMS hf)

theorem energy_norm_bound_second_form (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst.LemmaMS X u u' ψ)
    (hPN : PlaceNormG P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN :=
  energyNorm_bookY_of_placeNormG_of_changeVar hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC hMS hPN
    (Formalism.L2.SG.Pf.Carrier.EnergyCV.changeVar_of_pos P hr hg0)

theorem energy_norm_bound_third_form (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : Formalism.L2.SG.LocVol.IsStdChar ψ)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst2.LemmaMSStd X u u' ψ)
    (hPN : PlaceNormG P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN :=
  energy_norm_bound_second_form hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC (hMS hψ hstd hC) hPN

end Formalism.L2.SG.Pf.Carrier.EnergyNF
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPin
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.JointPin

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf
  Formalism.L2.SG.Pf.Carrier.JointQuot Formalism.L2.SG.Pf.Carrier.EnergyFinal Formalism.L2.SG.Pf.Carrier.EnergyPlace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def PinHyp (P : Parts X u u') (v : InfinitePlace X.B.I.F) (γ : Formalism.REAL.UJ (X.B.I.ε v))
    (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C6.IsRelevant (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ) ∧
  IsHaarLoc (StSet (NV X u v) (NV X u' v) γ) μRv ∧ IsQuotLoc μRv ν

def trMeas (P : Parts X u u') (v : InfinitePlace X.B.I.F) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Measure (Formalism.QuantumDeterminants.Mt P.S.G.k P.S.G.r) :=
  μRv.map (fun s => Matrix.of.symm (trG (P.Q v) (P.Qi v) s))

def PinCov (P : Parts X u u') : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (γ : Formalism.REAL.UJ (X.B.I.ε v)) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))),
    PinHyp P v γ μRv ν →
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) γ) =
      ((P.eP v).toContinuousLinearEquiv : _ →L[ℂ] X.Vloc u v).comp
        ((Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ) (trMeas P v μRv)
            (P.f (P.τ.symm v))).comp
          ((P.eQ v).symm.toContinuousLinearEquiv : X.Vloc u' v →L[ℂ] _))

def JointBridge (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  0 < sc → StRel X u u' → P.FromX → P.Base i0 i0' → (∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) →
  P.Built → ∀ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
  (∀ w, OkPt X u u' w → LocPin X u u' w νl) →
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' → ∀ v : InfinitePlace X.B.I.F,
    ∃ (γ' : Formalism.REAL.UJ (X.B.I.ε v)) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))), PinHyp P v γ' μRv ν ∧
      (∀ y : X.Vloc u' v,
        X.piLoc u v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v h⁻¹)
          ((haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
            Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))
            (X.piLoc u' v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v h') y)) =
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) γ') y) ∧
      Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ') (trMeas P v μRv) (P.f (P.τ.symm v)) =
        (((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
          Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
            (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))

def NormBridge (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  P.FromX → P.Built → 0 < P.S.g →
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    ∃ μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v)), PinHyp P v g μRv ν ∧
      JvX X u u' v g = (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) g) ∧
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) g) (trMeas P v μRv)
                (P.f (P.τ.symm v)))‖ =
        ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
          (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖

private theorem sum_norm_sq_apply_basis_indep {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (b : OrthonormalBasis ι ℂ Wq) (b' : OrthonormalBasis ι' ℂ Wq) (A : Wq →L[ℂ] Wp) :
    ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ‖A (b' i)‖ ^ 2 := by
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  have key : ∀ {κ : Type} [Fintype κ] (c : OrthonormalBasis κ ℂ Wq), ∑ i, ‖A (c i)‖ ^ 2 =
      (LinearMap.trace ℂ Wq (((ContinuousLinearMap.adjoint A).comp A : Wq →L[ℂ] Wq) : Wq →ₗ[ℂ] Wq)).re := by
    intro κ _ c
    rw [LinearMap.trace_eq_sum_inner _ c, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [key b, key b']

theorem hilbertSchmidt_conj_isometry {Wp Wq : Type} {V V' : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (e : Wp ≃ₗᵢ[ℂ] V) (e' : Wq ≃ₗᵢ[ℂ] V') (A : Wq →L[ℂ] Wp) :
    hs2 ((e.toContinuousLinearEquiv : Wp →L[ℂ] V).comp
      (A.comp (e'.symm.toContinuousLinearEquiv : V' →L[ℂ] Wq))) = ‖Formalism.FourierDecayAlt.B.hsVec A‖ ^ 2 := by
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  simp only [hs2, Formalism.FourierDecayAlt.B.hsVec, PiLp.norm_sq_eq_of_L2, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
  try simp only [PiLp.toLp_apply]
  have hb : ∀ i, e'.symm (stdOrthonormalBasis ℂ V' i) = ((stdOrthonormalBasis ℂ V').map e'.symm) i := fun i => by
    rw [OrthonormalBasis.map_apply]
  simp only [hb]
  exact sum_norm_sq_apply_basis_indep _ _ A

theorem placeJ_of_pin (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hpin : PinCov P) (hB : JointBridge P sc i0 i0') (hsc : 0 < sc) (hR : StRel X u u') (hFX : P.FromX)
    (hBase : P.Base i0 i0') (hEmb : ∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) (hBuilt : P.Built)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hνl : ∀ w, OkPt X u u' w → LocPin X u u' w νl) : PlaceJ P sc i0 i0' νl := by
  intro p w hp hrep hG h h' hD v y
  obtain ⟨γ', μRv, ν, hH, hJ, hO⟩ := hB hsc hR hFX hBase hEmb hBuilt νl hνl p w hp hrep hG h h' hD v
  rw [hJ y, hpin v γ' μRv ν hH, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hO]
  rfl

theorem placeNormG_of_pin (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hpin : PinCov P) (hB : NormBridge P hr)
    (hFX : P.FromX) (hBuilt : P.Built) (hg : 0 < P.S.g) : PlaceNormG P hr := by
  intro v g cv hc hZ
  obtain ⟨μRv, ν, hH, hJ, hn⟩ := hB hFX hBuilt hg v g cv hc hZ
  rw [hJ, hpin v g μRv ν hH, hilbertSchmidt_conj_isometry, hn]

theorem jointTensor_of_pin (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u') (hLU : LocUni X u u')
    (hGP : GlobProd X u u') (hpin : PinCov P) (hB : JointBridge P sc i0 i0') (hsc : 0 < sc) (hFX : P.FromX)
    (hBase : P.Base i0 i0') (hEmb : ∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) (hBuilt : P.Built) :
    P.JointTensor sc i0 i0' νq :=
  Formalism.L2.SG.Pf.Carrier.JointFinal.joint_tensor_factorization P sc i0 i0' νq hN hR hLU hGP
    (fun νl hνl => placeJ_of_pin P sc i0 i0' hpin hB hsc hR hFX hBase hEmb hBuilt νl hνl)

end Formalism.L2.SG.Pf.Carrier.JointPin
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGConstSmul
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.GoodS

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem v0_ne (C : Choice X θ) (τ : D.what₂.Tau) : v0Of C τ ≠ 0 := by
  intro h0
  have hy : (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    have hg := (C.isT τ).2.2.1
    have hyU : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
    calc (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ)
        = (C.Qi τ)ᴴ * ((C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.y τ) * C.Qi τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hyU, qiHqi _ (C.isT τ).2.1 hg]
  have hn := (X.ds (vOf X τ)).2.2.1.2.1 _ hy (X.B.w (vOf X τ))
  have h1 := (X.low (vOf X τ)).1
  unfold v0Of sigB at h0
  rw [h0, norm_zero] at hn
  rw [← hn] at h1
  exact zero_ne_one h1

theorem finrank_pos (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : 0 < Module.finrank ℂ (X.Vloc u v) := by
  have : Nontrivial (X.Vloc u v) := (X.piLoc_type u v).1
  exact Module.finrank_pos

theorem l2SG_const_smul {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (s : ℂ) (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) :
    l2SG ν (fun m => s • f m) = (‖s‖₊ : ℝ≥0∞) ^ 2 * l2SG ν f := by
  unfold l2SG
  simp only [nnnorm_smul, ENNReal.coe_mul, mul_pow]
  first
    | exact lintegral_const_mul' _ _ (by simp)
    | exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

theorem goodSRest_of {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hsm : v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ))
    (hLu : l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤)
    (hLu' : l2SG (C.nuS u' τ) (phiOf hB u' τ) ≠ 0 ∧ l2SG (C.nuS u' τ) (phiOf hB u' τ) < ⊤)
    (hT : Formalism.BasicNotions.dsigTie D) : GoodSRest hB u u' τ := by
  set v := vOf X τ
  have hd : (0 : ℝ) < Module.finrank ℂ (X.Vloc u v) := by exact_mod_cast finrank_pos u v
  have hd' : (0 : ℝ) < Module.finrank ℂ (X.Vloc u' v) := by exact_mod_cast finrank_pos u' v
  have hL : 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := ENNReal.toReal_pos hLu.1 hLu.2.ne
  have hL' : 0 < (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal := ENNReal.toReal_pos hLu'.1 hLu'.2.ne
  have hc : 0 < cOf hB u τ := div_pos hL hd
  refine ⟨Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, Formalism.L2.SG.Pf.dsTr C τ, hsm, v0_ne C τ, hc, ?_, ?_, ?_⟩
  · show l2SG (C.nuS u τ) (phiOf hB u τ) = _
    rw [cOf, div_mul_cancel₀ _ hd.ne', ENNReal.ofReal_toReal hLu.2.ne]
  · show l2SG (C.nuS u' τ) (fun m => sclOf hB u u' τ • phiOf hB u' τ m) = _
    rw [l2SG_const_smul, sclOf]
    set a := cOf hB u τ * (Module.finrank ℂ (X.Vloc u' v) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal
      with ha
    have ha0 : 0 ≤ a := div_nonneg (mul_nonneg hc.le hd'.le) hL'.le
    have hnorm : (‖((Real.sqrt a : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal a := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ha0]
    rw [hnorm, ← ENNReal.ofReal_toReal hLu'.2.ne, ← ENNReal.ofReal_mul ha0, ha, div_mul_cancel₀ _ hL'.ne']
  · obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
    refine ⟨P, hP.1, ?_⟩
    have hε : ∀ i, epsSH D.R i = X.B.I.ε v (Fin.cast (n_eq' X).symm i) := fun i => by
      rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl)
    have hF := fdegHpk_tr (n_eq' X) (X.B.I.ε v) (epsSH D.R) hε (X.B.σ v) (X.ds v).2.2.1
      (Formalism.L2.SG.Pf.RowDictPf.fdeg_of_schur X Formalism.L2.SG.Pf.RowDictPf.schur_orthogonality_discrete_series v)
      (C.Q τ) (C.Qi τ) (C.isT τ).2.1 (C.isT τ).2.2.1 P hP
    have hDS := dsHpk_tr (n_eq' X) (X.B.I.ε v) (epsSH D.R) hε (X.B.lam v) (lamSH D.R (D.hc τ))
      (fun i => by
        rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
        exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
      (X.B.σ v) (X.ds v) (C.Q τ) (C.Qi τ) (C.isT τ).2.1 (C.isT τ).2.2.1 P hP
    have hF2 := Formalism.L2.SG.Pf.RowDictPf.isFdeg_smul (D.s.cdScale_pos _ (epsSH D.R)) hF
    have htie := hT τ (X.B.H v) _ _ hDS hF2
    rw [← htie]
    exact hF2

end Formalism.L2.SG.Pf.GoodS
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowLast
section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ) (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1))
  (blk : Fin (r + 1) → ℕ)
  (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

include hFF hGG hπ hZ hgap in
theorem Yc_G {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (b : Fin (r + 1)) :
    Yc ε F G C *ᵥ G b = ∑ b', C b' b • G b' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hGcol : G b = Wfg F G *ᵥ Pi.single (Sum.inr b) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg, Function.swap]
  rw [hGcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

include hFF hGG hπ hZ hgap in
theorem Yc_F {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (a : Fin (r + 1)) :
    Yc ε F G C *ᵥ F a = ∑ a', Am ε F G C a' a • F a' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hFcol : F a = Wfg F G *ᵥ Pi.single (Sum.inl a) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg, Function.swap]
  rw [hFcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

theorem rowLast {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (k : Fin (r + 1)) :
    C (Fin.last r) k = if k = Fin.last r then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hk
  · rw [hk]
    exact hdiag _
  · by_contra h
    have h1 := (hup _ _ h).1
    exact hk (le_antisymm (Fin.le_last k) h1)

include hπ hblk hanti in
theorem colMin {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (b : Fin (r + 1)) :
    C b (π (Fin.last r)) = if b = π (Fin.last r) then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hb
  · rw [hb]
    exact hdiag _
  · by_contra h
    obtain ⟨hle, hbl⟩ := hup _ _ h
    have hlt : b < π (Fin.last r) := lt_of_le_of_ne hle hb
    have h2 := hanti b (π (Fin.last r)) hbl hlt
    rw [hπ] at h2
    exact absurd (Fin.le_last (π b)) (not_le.mpr h2)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

