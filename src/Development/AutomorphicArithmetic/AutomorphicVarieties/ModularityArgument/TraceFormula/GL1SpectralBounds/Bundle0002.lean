module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MultiplicityOneRigidity.GelfandKazhdanDualOfRigidity
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepC
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PMultC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.SecondFromFirstStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CsdDisc
section
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

theorem UpperTheory.V.Z.Tf.GOne.csdDisc :
    CsdDisc := by
  intro E _ _ _ n _ π h
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired CuspFormAutomorphicBounds.automorphicFormsFiniteGL E n π
    (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n π) h
  have hn : IsNormalised π := GlobalTheory.BcSpehCompare.isNormalised_of_isCsd hc
  refine isDiscrete_of_cuspSub π fun φ hφ => ?_
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_invariant (π.cusp φ hφ) (hn φ hφ)
  exact GlobalTheory.DiscChar.isSqInt_of_bounded (hn φ hφ) (C := C) fun g => by simpa using hC g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CsdSat
section
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

private theorem conj_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {w u : HeightOneSpectrum (𝓞 E)}
    (h : ConjPl w u) : UpperTheory.V.Af.Bc.cPl u = w := by
  obtain ⟨h1, h2⟩ := h
  by_cases e : u = w
  · subst e
    exact (GlobalTheory.ConjAtPlace.conjSrc_eq_iff u).2 (h2.resolve_left fun h => h rfl)
  · rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w).1 h1.symm with h | h
    · exact absurd h.symm e
    · refine (eq_conjSrc ?_).symm
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at h ⊢
      intro x y hxy
      refine (h y x ?_).symm
      rw [hxy]
      exact (IsCMField.complexConj_apply_apply E _).symm

theorem UpperTheory.V.Z.Tf.GOne.csdSat :
    CsdSat := by
  intro E _ _ _ n _ π h
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired CuspFormAutomorphicBounds.automorphicFormsFiniteGL E n π
    (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n π) h
  filter_upwards [_root_.GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat π] with w hw
  obtain ⟨B, hB⟩ := hw
  exact ⟨B, hB, fun u hu => (UpperTheory.satake_parameters_complex_conjugate E u).1 n π hc B (conj_eq hu ▸ hB)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.NotTwo
section
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

private theorem satV_of_locComp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (Matrix.GeneralLinearGroup (Fin N) (w.adicCompletion E))} (hσ : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) {φ : Sm E N} (hφ : φ ∈ V) (h0 : φ ≠ 0)
    (hfix : ∀ k ∈ GlobalTheory.LFun.KGL w (n := N), finRep E N (locGL E N w k) φ = φ) : SatV V w B := by
  have hmem : ∀ ψ ∈ V, ψ ∈ ⨆ f : SatakeVectors.SatakeVectorEventually.MapsD V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [SatakeVectors.SatakeVectorEventually.iSup_range_eq hV w σ hσ]; exact hψ
  have key : ∀ ψ ∈ V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := N), finRep E N (locGL E N w k) ψ = ψ) → ψ ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) ψ B := fun ψ hψ hψK hψ0 =>
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hB (fun f : SatakeVectors.SatakeVectorEventually.MapsD V w σ => f.1) (fun f => f.2.2)
      (hmem ψ hψ) (GlobalTheory.LGrp.mem_fixed.2 hψK) hψ0
  exact ⟨⟨φ, hφ, key φ hφ hfix h0⟩, key⟩

theorem UpperTheory.V.Z.Tf.GOne.notTwo :
    NotTwo := by
  intro E _ _ _ N a d V P π ha hd hV hA h
  have hNa : d * a = N := by
    obtain ⟨e, -⟩ := hA
    simpa using e
  have hN : 1 ≤ N := by
    rw [← hNa]
    exact Nat.mul_pos (by omega) ha
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have hlev := GlobalTheory.CuspRep.LocSph.eventually_mem (E := E) ((hV.aut φ hφ).level.mem_nhds (by simp))
  have key : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ (B : Fin d → Multiset ℂˣ) (B' : Unit → Multiset ℂˣ),
        (∀ i, ((CG.mk P).twist (GlobalTheory.CuspRep.Model.absC E (spehExp d i : ℂ))).HasSat w (B i)) ∧
        (∀ _j : Unit, (CG.mk π).HasSat w (B' ())) ∧ ∑ i, B i = ∑ j, B' j := by
    filter_upwards [h, satAsc_holds E N a d V P hV hA, hlev] with w hw hs hl
    obtain ⟨σ, B, hσ, hB, hπ⟩ := hw
    obtain ⟨B₀, hB₀, hall⟩ := hs
    have hfix : ∀ k ∈ GlobalTheory.LFun.KGL w (n := N), finRep E N (locGL E N w k) φ = φ := fun k hk => by
      obtain ⟨g, rfl⟩ := hk
      exact hl g
    have e := hall B (satV_of_locComp hV hσ hB hφ h0 hfix)
    refine ⟨fun i => B₀.map (· * (GlobalTheory.CuspRep.Model.absC E (spehExp d i : ℂ)).val w), fun _ => B,
      fun i => StrStepB.hasSat_twist_absC P hB₀ _, fun _ => hπ, ?_⟩
    apply Multiset.map_injective (f := fun b : ℂˣ => (b : ℂ)) Units.val_injective
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [e, StrStepC.map_fsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SatakeVectors.satTw_eq]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [StrStepB.absC_val]
  obtain ⟨s, -⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E (Fin d) Unit (fun _ => a) (fun _ => N)
    (fun i => (CG.mk P).twist (GlobalTheory.CuspRep.Model.absC E (spehExp d i : ℂ))) (fun _ => CG.mk π)
    (fun _ => ha) (fun _ => hN) key
  have hc := Fintype.card_congr s
  simp at hc
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.ThetaFixOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem theta_eq (g : GA E n) :
    GlobalTheory.ThetaPull.thetaA E n g = PhiU n (Ad E) * PositivityTheory.Rg.BcB.thetaA E n g * (PhiU n (Ad E))⁻¹ := by
  have e : GlobalTheory.ThetaPull.thetaA E n g = PhiU n (Ad E) * invT n (Ad E) (GeneralLinearGroup.map (conjAd E) g) *
      (PhiU n (Ad E))⁻¹ := rfl
  rw [e]
  congr 2

private theorem phi_rat : PhiU n (Ad E) = ratGL E n (PhiU n E) :=
  (GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU (algebraMap E (Ad E)) n).symm

private theorem phi_split : PhiU n (Ad E) = GlobalTheory.CsdFromConj.phiG E n := by
  refine ga_ext ?_ ?_
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CsdFromConj.toUnits_PhiK, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]

private theorem rt_phi_mem (π : CuspSub E n) {φ : Sm E n} (hφ : φ ∈ π.V) : rt E n (PhiU n (Ad E)) φ ∈ π.V := by
  have h := (GlobalTheory.CsdFromConj.phiEquiv π ⟨φ, hφ⟩).2
  rw [phi_split, GlobalTheory.CsdFromConj.rt_phiG]
  exact h

private theorem iso_theta {P : CuspSub E n} (h : P.IsCsd) : (GlobalTheory.ThetaPull.thetaSub P).Iso P := by
  obtain ⟨T, hT⟩ := h
  let L := (GlobalTheory.ThetaPull.pull E n).submoduleMap P.V
  refine ⟨L.symm.trans T, fun o φ => ?_⟩
  obtain ⟨φ, rfl⟩ := L.surjective φ
  have e : (GlobalTheory.ThetaPull.thetaSub P).op o (L φ) = L (P.op (thetaOp o) φ) :=
    Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1)
  rw [e]
  exact (congrArg T (L.symm_apply_apply _)).trans
    ((hT o φ).trans (congrArg (P.op o) (congrArg T (L.symm_apply_apply φ)).symm))

private theorem pull_mem {P : CuspSub E n} (h : P.IsCsd) {φ : Sm E n} (hφ : φ ∈ P.V) :
    GlobalTheory.ThetaPull.pull E n φ ∈ P.V := by
  have e : (GlobalTheory.ThetaPull.thetaSub P).V = P.V :=
    UpperTheory.V.Af.cuspMultOneGL E n _ _ (Quotient.sound (iso_theta h))
  rw [← e]
  exact ⟨φ, hφ, rfl⟩

theorem UpperTheory.V.Z.Tf.GOne.thetaFixOf :
    PositivityTheory.Rg.BcB.Desc.ThetaFixOf := by
  intro E _ _ _ n _ π hd
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired CuspFormAutomorphicBounds.automorphicFormsFiniteGL E n π
    (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n π) hd
  refine ⟨fun ψ hψ t g => GlobalTheory.BcSpehCompare.isNormalised_of_isCsd hc ψ hψ t g, fun ψ hψ => ?_⟩
  refine ⟨GlobalTheory.ThetaPull.pull E n (rt E n (PhiU n (Ad E)) ψ), pull_mem hc (rt_phi_mem π hψ), fun g => ?_⟩
  have e : PositivityTheory.Rg.BcB.thetaA E n g =
      ratGL E n (PhiU n E)⁻¹ * (GlobalTheory.ThetaPull.thetaA E n g * PhiU n (Ad E)) := by
    rw [theta_eq, map_inv, ← phi_rat]
    group
  rw [e, (π.cusp ψ hψ).1.left, GlobalTheory.ThetaPull.pull_apply, rt_apply]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.UnitOf
section
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

theorem UpperTheory.V.Z.Tf.GOne.unitOf :
    UnitOf := by
  intro E _ _ _ n _ π h
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired UpperTheory.V.Af.formsFiniteGL E n π
    (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n π) h
  exact (CG.isUnitary_mk π).2
    (GlobalTheory.SpehPair.isUnitary_of_isNormalised (GlobalTheory.BcSpehCompare.isNormalised_of_isCsd hc))
end

