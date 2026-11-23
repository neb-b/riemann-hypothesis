module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
public import Formalism.HermitianCurvature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentEstimate
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KappaDual

theorem mul_mem_GG {k r : ℕ} {g h : Mx k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r := by
  simp only [GG, Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hg hh ⊢
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem ae_pair {k r : ℕ} {U V : Set (Mx k r)} {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : PI.BesselPeriodGGP.IsHaarOn V ν) :
    ∀ᵐ p ∂(μ.prod ν), Matrix.of p.1 ∈ U ∧ Matrix.of p.2 ∈ V := by
  haveI := hμ.1
  haveI := hν.1
  have h1 : ∀ᵐ x ∂μ, Matrix.of x ∈ U := ae_iff.2 hμ.2.2.1
  have h2 : ∀ᵐ x ∂ν, Matrix.of x ∈ V := ae_iff.2 hν.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)

theorem kappa_dual : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (l : R.H → Wp), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → IsBeL R z π μW μN l → NzOn R l → ∀ I lI, IsBeL (RI I) z π μW μN lI → (∃ κ₀ : ℂ, ∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ ∀ κ₀ : ℂ, (∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = ((ep I : ℂ) * star κ₀) • lI y := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ z π u μW μN μG νq om l hR hRI hF hT hS hom
    hl hnz I lI hlI
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hbes, hS_eq, hsm⟩ :=
    GlobalTheory.T.isBes_tensor_projection_and_ev_equivariant_smooth hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp z π om hR hRI hF hT.raw hom I
  refine ⟨_root_.GlobalTheory.BesselLine.bessel_line hH k r ε mu R Wp z π u μW μN μG νq l _ hR hS hl.1 hnz (hbes lI hlI.1), ?_⟩
  intro κ₀ hκ y hy
  obtain ⟨v, hvTK, hv0⟩ := GlobalTheory.T.exists_K_type_nonzero_bessel hH k r ε mu R Wp z π l hR hl.1 hnz
  obtain ⟨-, -, -, -, hTKsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε mu R hR
  obtain ⟨-, -, -, hIsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε (muI I) (RI I) (hRI I)
  obtain ⟨hadj, -, hev, -⟩ := GlobalTheory.T.frep_discrete_series_sum hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hprTK⟩ := GlobalTheory.T.tensor_raw_of_frep hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw
  have hvsm : v ∈ R.sm := hTKsm v hvTK
  have htmTK : ∀ c, tm R om v c ∈ R.TK := fun c => R.TK.smul_mem _ hvTK
  have hPTK : (∑ c, pr I c (tm R om v c)) ∈ (RI I).TK :=
    Submodule.sum_mem _ fun c _ => hprTK I c _ (htmTK c)
  have h1 := (hl.2 _ (hsm.mem y hy) v hvTK).2
  have h2 := (hlI.2 y hy _ hPTK).2
  have h3 : be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (ev Γ R om (fun c => io I c y)) v =
      (ep I : ℂ) • be z Formalism.QuantumDeterminants.cStd π (RI I).σ μW μN y (∑ c, pr I c (tm R om v c)) := by
    unfold be
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [ae_pair hS.2.2.2.2.1 hS.2.2.2.2.2.1] with p hp
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Sset k r z := ⟨_, hp.1, _, hp.2, rfl⟩
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := mul_mem_GG hp.1.1 hp.2.1
    unfold beInt
    rw [← hS_eq _ hs y hy, ← hev, hadj I _ (hIsm _ hg y hy) _ (fun c => hTKsm _ (htmTK c)), smul_smul, mul_assoc]
  rw [h1, h2, hκ v hvsm] at h3
  have h4 := congrArg (fun T : Wp →L[ℂ] Wp => T (l v)) h3
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_left] at h4
  have hne : ⟪l v, l v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  apply smul_right_injective Wp hne
  simp only
  rw [h4, smul_smul, smul_smul]
  congr 1
  simp only [starRingEnd_apply]
  ring

end GlobalTheory.KappaDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepLoweringUnitaryComplement
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WignerStepLower

open Formalism.FourierDecayAlt.P

theorem comp_adjoint_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {k : ℕ} (S : Submodule ℂ (PiLp 2 (fun _ : Fin k => V))) (c : Fin k) (a : S →L[ℂ] V)
    (ha : ∀ y : S, a y = (y : PiLp 2 (fun _ : Fin k => V)) c) (v : V) :
    a (ContinuousLinearMap.adjoint a v) = S.starProjection (PiLp.single 2 c v) c := by
  have h : ContinuousLinearMap.adjoint a v = S.orthogonalProjection (PiLp.single 2 c v) := by
    refine ext_inner_left ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left, ha,
      PiLp.inner_apply, Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [PiLp.single_apply, Pi.single_apply, hb]
    · simp
  rw [h, ha]
  rfl

theorem wigner_step_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l - 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wM L M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l hz hT hty hL hu hB hl
  obtain ⟨hH, hadj⟩ := GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hty hL hu hB
  have hR : IsRepW (n + 1) r z π := ⟨hty.2.1, hty.2.2.1⟩
  obtain ⟨πt, hRt, hnt, hft⟩ := GlobalTheory.tensor_dual_standard V (n + 1) r z π B hz hT hR hty.2.2.2.1 hB
  have hE := GlobalTheory.TensorDualDifferential.EB_tensor V (n + 1) r z π B πt hz hT hR hRt hB hft
  obtain ⟨S, hS, hS0, hirr, hcap, hw⟩ := _root_.GlobalTheory.WigSh.pieri_step_lowering V n (EB π B) (EB πt B) β L l hH hadj hE hl
  obtain ⟨π₂, hty₂, hπ₂⟩ := GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S
    (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - 1)) hz hT hRt hnt hB hS hS0 hirr (by
      intro w y hy
      rw [mem_CapSp.1 (hcap hy) w, FrameExtension.prod_Icc_fin]
      congr 1
      unfold cpol shf
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have h1 := hu j
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self, Function.update_self]
        push_cast at h1 ⊢
        linear_combination -h1
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
        linear_combination -h1)
  let a : Fin (n + 1) → (S →L[ℂ] V) := fun c =>
    (PiLp.proj 2 (fun _ : Fin (n + 1) => V) c).comp S.subtypeL
  have ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c := fun _ _ => rfl
  obtain ⟨hW, hA⟩ := GlobalTheory.ContractLinear.wigMap_contract V (n + 1) r z π B S π₂ a hz hT hB
    (fun y => by
      simp only [ha]
      rw [← PiLp.norm_sq_eq_of_L2]
      rfl)
    (fun h hh y c => by
      simp only [ha]
      rw [hπ₂ h hh y, hft h hh])
  refine ⟨S, inferInstance, inferInstance, inferInstance, π₂, _, hty₂, hW, fun M v hv => ?_⟩
  simp only [hA]
  rw [comp_adjoint_apply S (Fin.last n) (a (Fin.last n)) (ha _) v]
  exact hw M v hv

end GlobalTheory.WignerStepLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepRaisingUnitaryComplement
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem adjoint_eval_subspace {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {k : ℕ} (S : Submodule ℂ (PiLp 2 (fun _ : Fin k => V))) (c : Fin k) (v : V) :
    ContinuousLinearMap.adjoint
        ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin k => V) c).comp S.subtypeL) v
      = S.orthogonalProjectionOnto (PiLp.single 2 c v) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left,
    PiLp.inner_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [PiLp.single_eq_of_ne, hb]
  · simp

theorem wigner_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l + 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wP L M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l hz hT hπ hL hu hB hl
  obtain ⟨hH, hadj⟩ := GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB
  have hrep : IsRepW (n + 1) r z π := ⟨hπ.2.1, hπ.2.2.1⟩
  obtain ⟨πt, ht1, ht2, ht3⟩ :=
    GlobalTheory.exists_tensor_standard_rep V (n + 1) r z π B hz hT hrep hπ.2.2.2.1 hB
  have hE := GlobalTheory.TensorStd.EB_tensor_std V (n + 1) r z π B πt hz hT hrep ht1 hB ht3
  obtain ⟨S, hS1, hS2, hS3, hS4, hS5⟩ := _root_.GlobalTheory.WigSh.pieri_step_raise V n (EB π B) (EB πt B) β L l hH hadj hE hl
  have hq : ∀ (w : ℂ), ∀ y ∈ S, qdet (EB πt B) w y = (∏ i ∈ Finset.Icc 1 (n + 1),
      (w - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 +
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1) i : ℝ) : ℂ))) • y := by
    intro w y hy
    have h1 := hS4 hy
    unfold CapSp at h1
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply] at h2
    rw [h2, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj := hu j
    by_cases hjl : j = l
    · subst hjl
      simp only [Function.update_self]
      push_cast at hj ⊢
      linear_combination -hj
    · have hne : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hjl (Fin.ext (by omega))
      rw [Function.update_of_ne hjl, Function.update_of_ne hne]
      linear_combination -hj
  obtain ⟨πS, hπS, hπS2⟩ := GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S _ hz hT ht1 ht2 hB
    hS1 hS2 hS3 hq
  let a : Fin (n + 1) → (S →L[ℂ] V) := fun c =>
    (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (n + 1) => V) c).comp S.subtypeL
  have ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c := fun c y => rfl
  obtain ⟨hW, hA⟩ := GlobalTheory.WigSh.ContrPlus.contraction_wigMap V (n + 1) r z π B S πS a hz hT hB
    (by
      intro y
      simp only [ha]
      rw [← PiLp.norm_sq_eq_of_L2]
      rfl)
    (by
      intro h hh y c
      simp only [ha]
      rw [hπS2 h hh y, ht3 h hh])
  refine ⟨S, inferInstance, inferInstance, inferInstance, πS, _, hπS, hW, ?_⟩
  intro M v hv
  simp only [hA]
  rw [ha, ← hS5 M v hv]
  simp only [a]
  rw [adjoint_eval_subspace]
  rfl

end GlobalTheory.WigSh
end

