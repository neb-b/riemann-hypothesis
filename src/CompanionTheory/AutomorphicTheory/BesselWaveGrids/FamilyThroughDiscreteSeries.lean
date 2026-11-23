module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Formalism.HermitianCurvature.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0003
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.DiscreteSeriesUnitarySmoothBasicImports
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionInjectiveParameters
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselNormSqEqConstMulArchPairingImports
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ExistsRegularRepBesselBigCellVectorEqBesselImpor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.WaveGrid.Ball

section sup

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

structure Sup0 (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (q0 : ℕ)
    (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq)
    (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ)
    (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) : Prop where
  fam : IsFam lam q0 R
  left : haveI := FiniteDimensional.complete ℂ Wp
    SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg
  right : haveI := FiniteDimensional.complete ℂ Wq
    SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg
  coef : ∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) →
    IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν
  zero : ∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0
  tau_zero : ∀ ν I, J ν = 0 ∨ J (ν + eZ I) = 0 → tau ν I = 0
  tau_eq : ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 →
    ∃ io pr ep, TensH (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep ∧
      ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), J ν ≠ 0 → J (ν + eZ I.1) ≠ 0 → ∃ κ κ' : ℂ,
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) ∧
        tau ν I.1 = (ep I : ℂ) * κ' * star κ * s ν / s (ν + eZ I.1)

end sup

theorem family_through_discreteSeries : Hyps → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep k r) (ν₀ : Fin (2 * r + k + 1) → ℤ), Num k r lam u b bv ga h q0 →
    R0.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν₀ a : ℝ)) →
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFam lam q0 R ∧ R ν₀ = R0 := by
  intro hH k r lam u b bv ga h q0 R0 ν₀ hN hR0
  classical
  have hex : DSExist := hH.2.2.2.1
  have hfam := (_root_.GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN).2
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      ∑ a, (ν a).natAbs ≤ q0 → R.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := fun ν =>
    if hq : ∑ a, (ν a).natAbs ≤ q0 then (hex k r _ _ (hfam ν hq).1 (hR0.2.imp fun _ h => h.1)).imp fun _ h _ => h
    else ⟨R0, fun h => absurd h hq⟩
  choose R hR using key
  refine ⟨Function.update R ν₀ R0, fun ν hν => ?_, Function.update_self ..⟩
  rcases eq_or_ne ν ν₀ with rfl | hne
  · simpa using hR0
  · simpa [Function.update_of_ne hne] using hR ν hν

theorem exists_coef_family : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s₀ : ℂ) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν₀ ≤ q0 → IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → IsCoef (R ν₀) (l ν₀) (l' ν₀) f s₀ → s₀ ≠ 0 → ∃ (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (t : ℝ), 0 < t ∧ J ν₀ = (fun g => (t : ℂ) • f g) ∧ (NzOn (R ν₀) (l ν₀) ∧ NzOn (R ν₀) (l' ν₀)) ∧ (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) ∧ (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg f s₀ ν₀ h0 hfam hL hR hf hs₀
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hdg0 : 0 < dg ν₀ := (hL ν₀ h0).2.1
  have hsn : 0 < ‖s₀‖ := norm_pos_iff.mpr hs₀
  have hnz : NzOn (R ν₀) (l ν₀) ∧ NzOn (R ν₀) (l' ν₀) := by
    obtain ⟨m, x, y, X, hxy, -, hs⟩ := hf
    have hsm := (GlobalTheory.rep_basic_of_isDS hK _ _ _ _ (R ν₀) (hfam ν₀ h0)).2.2.2.2.1
    rw [hs] at hs₀
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs₀
    refine ⟨⟨x i, hsm _ (hxy i).1, fun h => hi ?_⟩, ⟨y i, hsm _ (hxy i).2, fun h => hi ?_⟩⟩
    · rw [h, inner_zero_left]
    · rw [h, map_zero, inner_zero_right]
  have hex : ∀ ν, ∃ (s : ℂ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (ν = ν₀ → F = fun g => ((dg ν₀ / ‖s₀‖ : ℝ) : ℂ) • f g) ∧
      (n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) F s ∧ ‖s‖ = dg ν) ∧
      (¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → F = 0) := by
    intro ν
    by_cases hν : ν = ν₀
    · subst ν
      refine ⟨((dg ν₀ / ‖s₀‖ : ℝ) : ℂ) * s₀, _, fun _ => rfl, fun _ _ _ => ⟨?_, ?_⟩, fun hn => ?_⟩
      · exact (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R ν₀) Wp Wq (l ν₀) (l' ν₀) (hfam ν₀ h0)).2.1 f s₀ _ hf
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hdg0 hsn).le]
        field_simp
      · exact absurd ⟨h0, hnz⟩ hn
    · by_cases hc : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
      · obtain ⟨h1, h2, h3⟩ := hc
        have e1 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wp _ _ (l ν) (hfam ν h1) (hL ν h1).1.1 h2
        have e2 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wq _ _ (l' ν) (hfam ν h1) (hR ν h1).1.1 h3
        obtain ⟨F, hF⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R ν) Wp Wq (l ν) (l' ν)
          (hfam ν h1)).2.2 e1 e2 (dg ν : ℂ)
        refine ⟨_, F, fun h => absurd h hν, fun _ _ _ => ⟨hF, ?_⟩, fun hn => absurd ⟨h1, h2, h3⟩ hn⟩
        rw [Complex.norm_real, Real.norm_of_nonneg (hL ν h1).2.1.le]
      · exact ⟨0, 0, fun h => absurd h hν, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc, fun _ => rfl⟩
  choose s J h1 h2 h3 using hex
  exact ⟨s, J, dg ν₀ / ‖s₀‖, div_pos hdg0 hsn, h1 ν₀ rfl, hnz, h2, h3⟩

theorem exists_tau : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) → (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) → ∃ tau, Sup0 p lam q0 R l l' dg s J tau := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J hNum hFam hL hR hco hz
  classical
  obtain ⟨-, hz1, hz2, -, -, ht1, ht2⟩ := p.hP
  obtain ⟨νq, νq', hS, hS'⟩ := _root_.GlobalTheory.exists_sideG_both_of_isType P.k P.r Wp Wq p.T.base P.u P.u' ht1 ht2
  have key : ∀ ν, ∃ t : Finset (Fin (2 * P.r + P.k + 1)) → ℂ,
      (∀ I, J ν = 0 ∨ J (ν + eZ I) = 0 → t I = 0) ∧
      (n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 →
    ∃ io pr ep, TensH (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep ∧
      ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), J ν ≠ 0 → J (ν + eZ I.1) ≠ 0 → ∃ κ κ' : ℂ,
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) ∧
        t I.1 = (ep I : ℂ) * κ' * star κ * s ν / s (ν + eZ I.1)) := by
    intro ν
    by_cases hν : n1 ν + (P.r + 1) * (P.r + 2) ≤ q0
    swap
    · exact ⟨fun _ => 0, fun _ _ => rfl, fun h => absurd h hν⟩
    have hν1 : n1 ν + (P.r + 1) ≤ q0 := by nlinarith
    have hν0 : n1 ν ≤ q0 := by omega
    obtain ⟨io, pr, ep, hT⟩ := (GlobalTheory.T.pieri_tensor_decomposition hH P.k P.r lam P.u b bv ga h q0 R hNum hFam ν).1 (P.r + 1) hν1
    have hI : ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), n1 (ν + eZ I.1) ≤ q0 := by
      intro I
      have h1 := GlobalTheory.SuppliedPieri.n1_add_eZ_le ν I.1
      rw [I.2] at h1
      omega
    have hk : ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), ∃ κ κ' : ℂ, J ν ≠ 0 →
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) := by
      intro I
      by_cases hJ : J ν = 0
      · exact ⟨0, 0, fun h => absurd hJ h⟩
      have hn : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := not_not.1 (mt (hz ν) hJ)
      obtain ⟨κ, hκ⟩ := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH P.k P.r _ _ _ _ (P.r + 1) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep _ _ _ Wp
        p.T.base.z p.T.base.π P.u p.T.base.μW p.T.base.μN p.T.base.μG νq
        (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) (l ν) (hFam ν hν0) (fun I => hFam _ (hI I))
        (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (P.r + 1)) hT hS
        (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ hz1 g hg).1) (hL ν hν0).1 hn.2.1 I
        (l (ν + eZ I.1)) (hL _ (hI I)).1).1
      obtain ⟨κ', hκ'⟩ := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH P.k P.r _ _ _ _ (P.r + 1) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep _ _ _ Wq
        p.T.base.z' p.T.base.π' P.u' p.T.base.μW' p.T.base.μN p.T.base.μG νq'
        (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) (l' ν) (hFam ν hν0) (fun I => hFam _ (hI I))
        (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (P.r + 1)) hT hS'
        (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ hz2 g hg).1) (hR ν hν0).1 hn.2.2 I
        (l' (ν + eZ I.1)) (hR _ (hI I)).1).1
      exact ⟨κ, κ', fun _ => ⟨hκ, hκ'⟩⟩
    choose κ κ' hκ using hk
    refine ⟨fun I => if hc : I.card = P.r + 1 ∧ J ν ≠ 0 ∧ J (ν + eZ I) ≠ 0 then
      (ep ⟨I, hc.1⟩ : ℂ) * κ' ⟨I, hc.1⟩ * star (κ ⟨I, hc.1⟩) * s ν / s (ν + eZ I) else 0, ?_, fun _ => ?_⟩
    · intro I hI0
      refine dif_neg ?_
      rintro ⟨-, h1, h2⟩
      exact hI0.elim h1 h2
    · refine ⟨io, pr, ep, hT, fun I h1 h2 => ⟨κ I, κ' I, (hκ I h1).1, (hκ I h1).2, ?_⟩⟩
      exact dif_pos (⟨I.2, h1, h2⟩ : I.1.card = P.r + 1 ∧ J ν ≠ 0 ∧ J (ν + eZ I.1) ≠ 0)
  choose tau h1 h2 using key
  exact ⟨tau, ⟨hFam, hL, hR, hco, hz, h1, h2⟩⟩

theorem sup_norm : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∃ c : ℝ, 0 < c ∧ ∀ ν, n1 ν ≤ q0 → (J ν = 0 ∧ TBB.jN2 p (J ν) = 0 ∧ ¬ (NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν))) ∨ (J ν ≠ 0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) ∧ s ν ≠ 0 ∧ TBB.jN2 p (J ν) = ENNReal.ofReal (c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)))) := by
  intro hy P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hS
  obtain ⟨c₁, hc₁, h1⟩ := GlobalTheory.T.bessel_setting_uniform_constant hy P.k P.r Wp Wq p.T.base
  have hH : PI.BesselPeriodGGP.IsHaarOn (GG P.k P.r) p.T.base.μG :=
    have : IsFiniteMeasureOnCompacts p.T.base.μG := ⟨p.T.base.haarG.finite_compact⟩
    ⟨inferInstance, p.T.base.haarG.ne_zero, p.T.base.haarG.conc, p.T.base.haarG.left⟩
  obtain ⟨c₂, hc₂, h2⟩ := GlobalTheory.BesselDegree.schur_fdeg hy P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) _ hH
  obtain ⟨⟨-, -, -, -, hgap⟩, hfam⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, fun ν hν => ?_⟩
  have hDS := hS.fam ν hν
  obtain ⟨hl, hdg, hfd⟩ := hS.left ν hν
  obtain ⟨hl', -, -⟩ := hS.right ν hν
  have hP := h1 _ _ (h / 2) (R ν) (l ν) (l' ν) (dg ν) hDS (hfam ν hν).2.2.1 hgap hl hl' hfd
  have h0 : TBB.jN2 p (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = 0 := by
    simpa [Pi.zero_def] using Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul p 0 0
  by_cases hnz : NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
  · right
    obtain ⟨hc, hs⟩ := hS.coef ν hν hnz.1 hnz.2
    have hj : TBB.jN2 p (J ν) = ENNReal.ofReal (c₁ * dg ν) := by
      rw [_root_.GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq, hP _ _ hc, hs]
      congr 1
      field_simp
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 P.k P.r _ _ (R ν) hDS).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    have hd : dg ν = c₂ * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := by
      rw [← hfd w hw0, (h2 _ (R ν) hDS).1 w hw0]
    refine ⟨?_, hnz.1, hnz.2, ?_, ?_⟩
    · exact fun hJ => (ENNReal.ofReal_pos.2 (mul_pos hc₁ hdg)).ne' (hj.symm.trans (by rw [hJ, h0]))
    · exact fun hs0 => hdg.ne' (by rw [← hs, hs0, norm_zero])
    · rw [hj, hd, mul_assoc]
  · left
    have hJ := hS.zero ν (fun hh => hnz hh.2)
    exact ⟨hJ, by rw [hJ, h0], hnz⟩

theorem sup_meas : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∀ ν, AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) (J ν) (P.r + 1) [] (TBB.bigPt P.r c)) := by
  intro _ P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau _ hS ν
  apply _root_.GlobalTheory.bigCell_density_aemeasurable
  by_cases hν : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
  · exact GlobalTheory.SupMeas.isCoef_continuousOn (hS.fam ν hν.1) (hS.coef ν hν.1 hν.2.1 hν.2.2).1
  · rw [hS.zero ν hν]
    exact continuousOn_const

theorem tau_bound : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ I : Finset (Fin (2 * P.r + P.k + 1)), I.card = P.r + 1 → ‖tau ν I‖ ≤ Real.sqrt (Hsq P.r P.T b * Hsq P.r P.T' b) ^ (P.r + 1) := by
  intro hyp P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hN' hS ν hν I hI
  classical
  by_cases hz : J ν = 0 ∨ J (ν + eZ I) = 0
  · rw [hS.tau_zero ν I hz, norm_zero]
    positivity
  rw [not_or] at hz
  have h1 : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := not_not.1 (mt (hS.zero ν) hz.1)
  have h2 : n1 (ν + eZ I) ≤ q0 ∧ NzOn (R (ν + eZ I)) (l (ν + eZ I)) ∧ NzOn (R (ν + eZ I)) (l' (ν + eZ I)) :=
    not_not.1 (mt (hS.zero _) hz.2)
  obtain ⟨-, -, -, hT, hT', hty, hty'⟩ := p.hP
  obtain ⟨νq, νq', hG, hG'⟩ := _root_.GlobalTheory.exists_sideG_both_of_isType P.k P.r Wp Wq p.T.base P.u P.u' hty hty'
  obtain ⟨io, pr, ep, hTens, hκ⟩ := hS.tau_eq ν hν
  obtain ⟨κ, κ', hk, hk', ht⟩ := hκ ⟨I, hI⟩ hz.1 hz.2
  have b1 := GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le hyp P.k P.r Wp lam P.u b bv ga h q0 _ _ _ _ _ νq R l dg
    ⟨hN, hS.fam, hG, hS.left⟩ ν hν io pr ep hTens h1.2.1 ⟨I, hI⟩ κ h2.2.1 hk
  have b2 := GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le hyp P.k P.r Wq lam P.u' b bv ga h q0 _ _ _ _ _ νq' R l' dg
    ⟨hN', hS.fam, hG', hS.right⟩ ν hν io pr ep hTens h1.2.2 ⟨I, hI⟩ κ' h2.2.2 hk'
  rw [hT] at b1
  rw [hT'] at b2
  have s1 := (hS.coef ν h1.1 h1.2.1 h1.2.2).2
  have s2 := (hS.coef _ h2.1 h2.2.1 h2.2.2).2
  have d1 := (hS.left ν h1.1).2.1
  have d2 := (hS.left _ h2.1).2.1
  have hep : ‖(ep ⟨I, hI⟩ : ℂ)‖ = 1 := by
    rcases hTens.ep_sq ⟨I, hI⟩ with h | h <;> simp [h]
  have ht' : tau ν I = (ep ⟨I, hI⟩ : ℂ) * κ' * star κ * s ν / s (ν + eZ I) := ht
  rw [ht', norm_div, norm_mul, norm_mul, norm_mul, hep, one_mul, norm_star, s1, s2]
  exact GlobalTheory.SupTau.arith _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) d1 d2 (GlobalTheory.SupTau.hsq_nonneg _ _ _) (GlobalTheory.SupTau.hsq_nonneg _ _ _) b1 b2

theorem supplied_pieri : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • p.V (J ν) (TBB.bigPt P.r c) = ∑ I ∈ powersetCard (P.r + 1) (univ : Finset (Fin (2 * P.r + P.k + 1))), tau ν I • p.V (J (ν + eZ I)) (TBB.bigPt P.r c) := by
  intro H P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hS ν hν c hc hG
  obtain ⟨γ, hγ, hZ, hV⟩ := _root_.GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel P Wp Wq p c hc hG
  simp only [hV]
  by_cases hJ : J ν = 0
  · rw [hJ, GlobalTheory.SuppliedPieri.JF_zero, smul_zero]
    symm
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [hS.tau_zero ν I (Or.inl hJ), zero_smul]
  obtain ⟨c0, -, hdich⟩ := sup_norm H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hS
  obtain ⟨⟨-, -, -, -, hGap⟩, hfam⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  have hν0 : n1 ν ≤ q0 := by omega
  have hνI : ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), n1 (ν + eZ I.1) ≤ q0 := by
    intro I
    have h1 := GlobalTheory.SuppliedPieri.n1_add_eZ_le ν I.1
    rw [I.2] at h1
    have h2 : P.r + 1 ≤ (P.r + 1) * (P.r + 2) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  obtain ⟨io, pr, ep, hT, htau⟩ := hS.tau_eq ν hν
  have hnz : NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := (not_not.1 (mt (hS.zero ν) hJ)).2
  have key := GlobalTheory.T.tensor_weighted_bessel_gap H P.k P.r (Sub (2 * P.r + P.k + 1) (P.r + 1)) (Sub (2 * P.r + P.k + 1) (P.r + 1))
    (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (P.r + 1) (R ν) (fun I => R (ν + eZ I.1)) io pr ep
    (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ))
    (fun I a => lam a + ((ν + eZ I.1) a : ℝ)) (h / 2) Wp Wq p.T.base
    (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z'))
    (l ν) (l' ν) (fun I => l (ν + eZ I.1)) (fun I => l' (ν + eZ I.1)) (J ν) (s ν)
    (fun I => J (ν + eZ I.1)) (fun I => s (ν + eZ I.1)) (fun I => tau ν I.1)
    (hS.fam ν hν0) (hfam ν hν0).2.2.1
    (fun I => ⟨hS.fam _ (hνI I), (hfam _ (hνI I)).2.2.1⟩) hGap
    (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (P.r + 1)) hT
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ p.T.base.z_mem g hg).1)
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ p.T.base.z'_mem g hg).1)
    (fun I => ⟨(hS.left _ (hνI I)).1, (hS.right _ (hνI I)).1⟩)
    (hS.coef ν hν0 hnz.1 hnz.2).1
    (fun I => by
      rcases hdich _ (hνI I) with ⟨h0, -, hn⟩ | ⟨h0, hn, hn', hs, -⟩
      · exact Or.inl ⟨not_and_or.mp hn, hS.tau_zero ν I.1 (Or.inr h0)⟩
      · exact Or.inr ⟨(hS.coef _ (hνI I) hn hn').1, hs, htau I hJ h0⟩)
    γ hγ
  rw [GlobalTheory.TopMinorWedge.herm_cmp_wedge_eq_det, hZ] at key
  rw [key]
  symm
  exact Finset.sum_subtype _ (fun I => by simp) (fun I => tau ν I • B.JF p.T.base (J (ν + eZ I)) γ)

end CompanionTheory.WaveGrid.Ball
