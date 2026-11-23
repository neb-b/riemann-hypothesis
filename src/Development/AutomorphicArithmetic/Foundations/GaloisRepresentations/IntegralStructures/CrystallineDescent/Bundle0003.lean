module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0337

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.CsdLift
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.csdLift_holds :
    CsdLift := by
  intro hJ hG E M _ _ _ _ _ _ _ l a ha π P hL hS
  obtain ⟨hreg, hpol, -⟩ := hS
  have hreg' : (CG.mk P).IsRegAlg := (CG.isRegAlg_iff _).2 fun τ => by
    rw [hL.inf τ]
    exact (CG.isRegAlg_iff _).1 hreg (τ.comp (algebraMap E M))
  have hF := GlobalTheory.automorphicFormsFiniteGL
  refine ⟨hreg', ⟨fun v => by rw [locInf_pow, quadChar_locInf], ?_⟩, trivial⟩
  rw [GlobalTheory.CsdLift.compNorm_quadChar_pow]
  refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha P 1 ?_
  have hsd := _root_.GlobalTheory.PolarizedSat.hasSat_conjPlace hF E a π _ hpol
  have hun := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π
  filter_upwards [(GlobalTheory.LiftPolar.tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hs, B, hB⟩
  rw [GlobalTheory.CsdLift.compNorm_quadChar_pow] at hs
  have e1 := GlobalTheory.LiftPolar.cPl_under (E := E) w
  have e2 := GlobalTheory.LiftPolar.normV_cPl w
  have e3 := GlobalTheory.LiftPolar.normV_cPl (w.under (𝓞 E))
  have hf := GlobalTheory.LiftPolar.normV_under (K := E) w
  set f := w.asIdeal.inertiaDeg (𝓞 E)
  have hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B := (CG.hasSat_mk _ _ _).2 hB
  have h1 := hL.sat w f B hf hB0
  have h2 := hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)
  refine ⟨GlobalTheory.CsdLift.unrAt_one w, _, _, h1, h2, ?_⟩
  simp only [GlobalTheory.CsdLift.val_one, Multiset.map_map, Function.comp_def, mul_one, inv_one, inv_pow, inv_inv]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownPhi
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open GlobalTheory.GLq GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.AboveL
open UpperTheory.Gal.Int.Core
open GlobalTheory.RoadU GlobalTheory.RoadU.PhiDescent in
theorem UpperTheory.Gal.Int.Core.downPhi_holds : SphDown .phi := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP r w B hB hQdec hyp Pr AI hT A h O _ _ _ Bw hj g
  have hdec := hQdec A h
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A h hdec
  have hunder : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver h h'
    ext1
    exact this.over.symm
  obtain ⟨c, hc, hdegc, hq, -⟩ :=
    _root_.GlobalTheory.WeilTransport.weil_equiv E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  obtain ⟨S, hS, -, -, -, -, hTw, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hunder, hq]) (by rw [hunder]; exact hB)
    simpa using this
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  have hrel : WDRel (RingEquiv.refl Ω) (wdAt Pr ι Bw h hj (r.comp (Dec (F := E) A).subtype))
      (wdAt Pr ι Bw' h' hj' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype)) := by
    by_cases hp : IsPstAt Pr Bw (r.comp (Dec (F := E) A).subtype)
    · exact GlobalTheory.RealGal.wdRelRes_gen E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r hp ι w w' h h' hj hj' i hi
    · have hp' : ¬ IsPstAt Pr Bw' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype) :=
        fun H => hp (D.2.2.2.1 H)
      rw [wdAt_of_not_isPstAt _ _ _ _ hp, wdAt_of_not_isPstAt _ _ _ _ hp']
      exact wdRel_trivWD h h' _ a
  have hsat : WDRel (RingEquiv.refl Ω) (satWD h a B) (satWD h' a B) := by
    have h0 := GlobalTheory.RSGam.Transport.wdRel_lpUnr c hc hdegc (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))
    unfold satWD
    rw [hS, hTw, (hS _ _).mp h0]
  have hgc : WeilRel (RingEquiv.refl Ω) g (c g) := (hc g (c g)).2 rfl
  have hcl := hyp w' hunder hB' Pr AI hT A h' O Bw' hj' (c g)
  rw [charPol_eq hrel hgc, charPol_eq hsat hgc]
  exact hcl
end

