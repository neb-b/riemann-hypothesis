module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0045

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaDictAllC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D))

theorem levi_split_iff {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) {u u' : D.what₂.Word}
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam') :
    (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
      AdTriv X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt * s₁.pt⁻¹).2 *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u))) := by
  obtain ⟨gδ, -, hs⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  rw [hb2, AdTriv, ← IotaDictPf.levi_one_iff Y.TR gδ, hs]
  constructor
  · intro h
    exact mul_right_cancel (h.symm.trans (one_mul _).symm)
  · intro h
    rw [h, one_mul]

theorem iotaDict_fwd {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) {u u' : D.what₂.Word}
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam')
    (h : iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂) :
    IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D) := by
  obtain ⟨gδ, nδ, -⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  have hRL : RatLink X (s₂.pt * s₁.pt⁻¹) (s₂.lin * s₁.lin⁻¹) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X s₂.rep.2.1 (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X s₁.rep.2.1)
  rw [Formalism.L2.SG.Pf.Act.ratIotaC' Y u u' s₁ s₂ hl hl']
  refine iotaBridgeARC_holds _ X Y u s₁.lam s₁.mem _ _ hRL (by rw [hb2]; exact gδ.1.1) (by rw [hb2]; exact nδ) ?_
  exact (levi_split_iff Y s₁ s₂ hl hl').1 h

theorem iotaDictAllC_of (h2 : IotaBridgeRAC) : IotaDictAllC := by
  intro D X Y u u' s₁ s₂ hl hl'
  refine ⟨iotaDict_fwd Y s₁ s₂ hl hl', fun h => ?_⟩
  obtain ⟨gδ, nδ, -⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  have hRL : RatLink X (s₂.pt * s₁.pt⁻¹) (s₂.lin * s₁.lin⁻¹) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X s₂.rep.2.1 (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X s₁.rep.2.1)
  rw [Formalism.L2.SG.Pf.Act.ratIotaC' Y u u' s₁ s₂ hl hl'] at h
  exact (levi_split_iff Y s₁ s₂ hl hl').2
    (h2 D X Y u s₁.lam s₁.mem _ _ hRL (by rw [hb2]; exact gδ.1.1) (by rw [hb2]; exact nδ) h)

theorem iotaDictC_holds_of (h2 : IotaBridgeRAC) : IotaDictC :=
  fun D X Y u u' s₁ s₂ _ _ _ _ hl hl' => iotaDictAllC_of h2 D X Y u u' s₁ s₂ hl hl'

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NHLocHolds
section
noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

theorem NHLoc_holds : JacobianCoordinates.NHLoc := by
  intro n r k ε e p z z' T T' F hep hpp hzp μN μH hN hH
  have hpz : ∀ a, hJ ε (p a) z = 0 := fun a => hJ_swap0 (hzp a)
  obtain ⟨w, hww, hew, hpw, hzw⟩ := UnitaryIsometries.RI.complement ε F.dim F.sig F.T_pos
    (⟨F.ee, hep, hpp, F.ez, hpz, F.zz⟩ : UnitaryIsometries.RI.Hyp ε e p z (T : ℂ))
  have Fw : Frm ε e p z w T := ⟨F.ee, hep, hpp, F.ez, hpz, F.zz, hew, hpw, hzw, hww, F.T_pos.ne'⟩
  have hdim := F.dim
  have hHc := HG_compact Fw hdim
  have hNH := hN
  obtain ⟨⟨hσN, hneN, hcN, hinvN⟩, hfinN⟩ := hN
  obtain ⟨⟨hσH, hneH, hcH, hinvH⟩, hfinH⟩ := hH
  haveI := hσN
  haveI := hσH
  haveI := hfinN
  haveI := hfinH
  have hmult : Measurable (fun q : UJ ε × UJ ε => q.1 * q.2) := measurable_fst.mul measurable_snd
  set NH : Set (UJ ε × UJ ε) := (NG ε e z : Set (UJ ε)) ×ˢ (HG ε e p z : Set (UJ ε)) with hNHdef
  have hPout : (μN.prod μH) NHᶜ = 0 := by
    rw [hNHdef, Set.compl_prod_eq_union]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod]
      have : μN (NG ε e z : Set (UJ ε))ᶜ = 0 := hcN
      rw [this, zero_mul]
    · rw [Measure.prod_prod]
      have : μH (HG ε e p z : Set (UJ ε))ᶜ = 0 := hcH
      rw [this, mul_zero]
  have hHfin : μH (HG ε e p z : Set (UJ ε)) < ⊤ := hHc.measure_lt_top
  have hfin : IsFiniteMeasureOnCompacts ((μN.prod μH).map (fun q : UJ ε × UJ ε => q.1 * q.2)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hmult hK.measurableSet]
    have hsub : (fun q : UJ ε × UJ ε => q.1 * q.2) ⁻¹' K ⊆
        ((K * (HG ε e p z : Set (UJ ε))⁻¹) ×ˢ (HG ε e p z : Set (UJ ε))) ∪ NHᶜ := by
      intro q hq
      by_cases hq' : q ∈ NH
      · left
        refine ⟨⟨q.1 * q.2, hq, q.2⁻¹, by simpa using hq'.2, by group⟩, hq'.2⟩
      · right; exact hq'
    refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
    rw [hPout, add_zero, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hK.mul hHc.inv).measure_lt_top hHfin
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, hfin⟩
  · haveI := hfin
    infer_instance
  · intro h0
    have := congrArg (fun m : Measure (UJ ε) => m Set.univ) h0
    simp only [Measure.map_apply hmult MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
      Pi.zero_apply, ← Set.univ_prod_univ, Measure.prod_prod] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hneN (Measure.measure_univ_eq_zero.1 h1)
    · exact hneH (Measure.measure_univ_eq_zero.1 h1)
  · rw [Measure.map_apply hmult (show MeasurableSet (SLoc ε e z)ᶜ from
      (UnitaryIsometries.RI.SG_closed ε e z).measurableSet.compl)]
    refine measure_mono_null (s := (fun q : UJ ε × UJ ε => q.1 * q.2) ⁻¹' (SLoc ε e z)ᶜ) (t := NHᶜ)
      (fun q hq hqNH => hq ?_) hPout
    exact (UnitaryIsometries.RI.SG ε e z).mul_mem (NG_le_SG ε e z hqNH.1) (HG_le_SG ε e p z hqNH.2)
  · obtain ⟨m0, hm0, h0, hh0, rfl⟩ := mem_NH Fw hdim hs
    have hf : μN.map (fun x => m0 * conjH h0 x) = μN := by
      have : (fun x => m0 * conjH h0 x) = (fun x => m0 * x) ∘ conjH h0 := rfl
      rw [this, ← Measure.map_map (measurable_const_mul m0) (conjH h0).continuous.measurable,
        conj_haar_eq Fw hdim hNH hh0, hinvN m0 hm0]
    have hg : μH.map (fun x => h0 * x) = μH := hinvH h0 hh0
    have hfm : Measurable (fun x => m0 * conjH h0 x) := (conjH h0).continuous.measurable.const_mul m0
    have hgm : Measurable (fun x : UJ ε => h0 * x) := measurable_const_mul h0
    haveI : SFinite (μN.map (fun x => m0 * conjH h0 x)) := by rw [hf]; infer_instance
    haveI : SFinite (μH.map (fun x => h0 * x)) := by rw [hg]; infer_instance
    have hfun : (fun x => m0 * h0 * x) ∘ (fun q : UJ ε × UJ ε => q.1 * q.2) =
        (fun q : UJ ε × UJ ε => q.1 * q.2) ∘ Prod.map (fun x => m0 * conjH h0 x) (fun x => h0 * x) := by
      funext q
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, conjH_apply]
      group
    rw [Measure.map_map (measurable_const_mul _) hmult, hfun,
      ← Measure.map_map hmult (hfm.prodMap hgm), ← Measure.map_prod_map μN μH hfm hgm, hf, hg]

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviGlue
section
namespace Formalism.L2.SG.Pf.SlabCount

theorem leviFinC_of_pos (hP : LeviPosC) : LeviFinC :=
  leviFinC_of (leviStabFinC_of (leviWFinC_of hP) rational_z_condition_holds)

theorem levi_finite_index : LeviFinC :=
  leviFinC_of_pos levi_totally_positive_definite

end Formalism.L2.SG.Pf.SlabCount
end

