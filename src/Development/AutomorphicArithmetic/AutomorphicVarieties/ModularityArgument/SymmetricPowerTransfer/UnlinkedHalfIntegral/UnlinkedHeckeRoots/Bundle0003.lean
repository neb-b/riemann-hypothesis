module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Mathlib
public import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0220
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0225
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0623
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0613
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescription
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
public import GroundTheory.AutomorphicForms.HaarSK
public import GroundTheory.AutomorphicForms.GL2.IdeleModuleDetOfMemMaxCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
public import GroundTheory.LocalFields.LocalZetaEpsilon
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0609
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0626
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0618
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvalues
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecay
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficients
public import GroundTheory.AutomorphicForms.Bundle0008
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.BadAbs
section
private theorem norm_sq_of_scaled (k p : ℕ) (hk : 3 ≤ k) (hp : 2 ≤ p) (x : ℂ)
    (h : ‖x * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 = (p : ℝ)) : ‖x‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  have hr : (0 : ℝ) < (p : ℝ) ^ (1 - (k : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow] at h
  have hr2 : ((p : ℝ) ^ (1 - (k : ℝ) / 2)) ^ 2 = (p : ℝ) ^ (2 - (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have he : (((k - 1 : ℕ) : ℝ)) + (2 - (k : ℝ)) = 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hkey : (p : ℝ) ^ (k - 1) * (p : ℝ) ^ (2 - (k : ℝ)) = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0, he, Real.rpow_one]
  have hne : (p : ℝ) ^ (2 - (k : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
  rw [hr2] at h
  exact mul_right_cancel₀ hne (h.trans hkey.symm)

theorem UpperTheory.V.Z.Sym.Unl.badAbs :
    UpperTheory.V.Z.Sym.Unl.BadAbs := by
  intro k N _ hk χ hχ g p hp hpN
  have b0 : Ad3.R.B0 := @_root_.GlobalTheory.CompanionTheory.RankinQ.b0
  have c0 : Ad3.R.C0 := @_root_.GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant
  have c1 : Ad3.R.C1 := @GlobalTheory.T.congruence_subgroup_coset_decomposition
  have u2 : Ad3.R.U2 := @_root_.GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char
  have g0 : Ad3.R.G0 := @_root_.GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain (@_root_.GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain)
  have g1 : Ad3.R.G1 := @_root_.GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing (@_root_.GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts)
  have f0 : Ad3.R.F0 := @_root_.GlobalTheory.CompanionTheory.RankinSelbergQ.f0 b0
  have f0b : Ad3.R.F0b := @_root_.GlobalTheory.CompanionTheory.NewformLiftConductor.f0b b0
  have f1 : Ad3.R.F1 := @GlobalTheory.T.newform_lift_level b0
  have f1b : Ad3.R.AutomorphicLevelEquivariance := @_root_.GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance b0
  have f2 : Ad3.R.F2 := @_root_.GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift
  have f3a : Ad3.R.HeckeSumLocalTranslates := @_root_.GlobalTheory.CompanionTheory.RSq.f3a b0
  have f3 : Ad3.R.F3 := @_root_.GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift b0 c0 c1 f0b f1 f1b f3a
  have f5 : Ad3.R.F5 := @_root_.GlobalTheory.CompanionTheory.NewformLiftDecay.main b0
  have f4 : Ad3.R.F4 := @_root_.GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq b0 c1 u2 g0 g1 f0b f1 f2 f3 f5
  obtain ⟨hform, heig⟩ := Ad3P.sEig k N hk χ g
  obtain ⟨ω, hω⟩ := f0 N χ
  obtain ⟨-, φ, hφ⟩ := f1 k N χ _ _ hform g.one ω hω
  obtain ⟨v, rfl⟩ := b0.2.2.1 p hp
  have h := f4 k N hk χ hχ _ _ hform heig ω φ hω hφ v hpN
  exact norm_sq_of_scaled k _ hk hp.two_le _ h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SelfAdj
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate
open Ad3 Ad3.R

namespace UpperTheory.V.Z.Sym.Unl

theorem selfAdj : SelfAdj := by
  intro k N _ hk χ hχ g p hp hpN
  have hB := _root_.GlobalTheory.CompanionTheory.RankinQ.b0
  have hE := Ad3P.sEig k N hk χ g
  obtain ⟨hF, hEig⟩ := hE
  obtain ⟨ω, hω⟩ := _root_.GlobalTheory.CompanionTheory.RankinSelbergQ.f0 hB N χ
  obtain ⟨hsign, φ, hL⟩ := GlobalTheory.T.newform_lift_level hB k N χ g.f g.a hF hEig.2.1 ω hω
  have hOmL := _root_.GlobalTheory.CompanionTheory.NewformLiftConductor.f0b hB k N χ hχ hsign ω hω
  have hHk := _root_.GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift hB _root_.GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant GlobalTheory.T.congruence_subgroup_coset_decomposition (_root_.GlobalTheory.CompanionTheory.NewformLiftConductor.f0b hB) (GlobalTheory.T.newform_lift_level hB)
    (_root_.GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance hB) (_root_.GlobalTheory.CompanionTheory.RSq.f3a hB) k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  have hW := _root_.GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  have hb := _root_.GlobalTheory.CompanionTheory.NewformLiftDecay.main hB k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  obtain ⟨μ, 𝓕, mK, 𝓓, hS⟩ := _root_.GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain _root_.GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain
  have hG1 := _root_.GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing _root_.GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts
  obtain ⟨v, hv⟩ := hB.2.2.1 p hp
  have hnd : ¬pOf v ∣ N := by rwa [hv]
  obtain ⟨C, hC⟩ := hb.1
  have hφ0 : φ ≠ 0 := by
    intro h0
    have h1 := hW.2.2.2 (-1)
    rw [h0, GlobalTheory.CompanionTheory.RSEigen.wh_zero] at h1
    exact GlobalTheory.CompanionTheory.RSEigen.wr_ne k h1.symm
  have hpr := GlobalTheory.CompanionTheory.RSEigen.pr_self_ne hS hG1 (ω := ω) hL.cont hb.1 hL.left hL.cen hφ0
  have hone : ∀ x : G2, cdet 1 x = 1 := by
    intro x
    simp [Ad3.R.cdet, GroundTheory.Global.HeckeCharacter.toIdele_apply]
  have hPr : GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Pr μ 𝓕 φ 1 1 1 ≠ 0 := by
    simpa [GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Pr, GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Fn, hone, GlobalTheory.CompanionTheory.RSEigen.pr] using hpr
  have hloc1 : ∀ u, localChar (1 : HeckeCharacter ℚ) v u = 1 := by
    intro u
    ext
    simp [GroundTheory.Automorphic.GodementSection.coe_localChar,
      GroundTheory.Global.HeckeCharacter.localComponent_apply, GroundTheory.Global.HeckeCharacter.toIdele_apply]
  have hunr1 : IsUnramifiedChar (localChar (1 : HeckeCharacter ℚ) v) :=
    isUnramifiedChar_iff.2 (fun u _ => hloc1 u)
  have hstd := (hB.1 v).1
  obtain ⟨ϖ, B, hR⟩ := (GlobalTheory.T.congruence_subgroup_coset_decomposition (Qv v) (localAdelicChar ℚ v) hstd).1
  have key := GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.eig_relation (φ := φ) (ω := ω) (c := 1) (μ := μ) (𝓕 := 𝓕) (C := C)
    hL.cont hC hL.left hL.cen (by simp)
    (fun F hF hFb hFL hFC h => (hG1 μ 𝓕 mK 𝓓 hS F hF hFb hFL).1 hFC h) hS.vol
    (v := v) (hB.1 v).2.2.2.2.2.1 hB.2.2.2.1 (hB.2.2.2.2.2.2.2 v) hunr1
    (lam := lamOf k g.a v) (fun g W hW' => hHk.good v hnd g W hW') hR (h := 1)
    (GroundTheory.Automorphic.Reduction.finAt_one v) hPr
  have hω1 : ((localChar ω v ϖ : ℂˣ) : ℂ) = χ p := by
    rw [quasiChar_apply_eq_of_isUnramified (hOmL.good v hnd).1 hR.1, (hOmL.good v hnd).2, hv]
  rw [hloc1, hω1] at key
  simp only [lamOf, hv, Units.val_one, one_mul, map_mul, Complex.conj_ofReal] at key
  have hr : (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).ne'
  have h : g.a p * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)
      = (χ p * (starRingEnd ℂ) (g.a p)) * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) :=
    key.trans (by ring)
  have h2 := mul_right_cancel₀ hr h
  linear_combination -h2

end UpperTheory.V.Z.Sym.Unl
end
end

