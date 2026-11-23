module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.HermitianCurvature.Bundle0008

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbPf
section
set_option linter.unusedVariables false

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.L2.SG.AmpOrbPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem lowest_K_type_unit {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (hA : GoodS D lam A) :
    PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) := by
  obtain ⟨-, -, -, -, -, hne, ⟨P, hP, hmem⟩, -⟩ := hA
  refine ⟨P, hP, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
  · exact Submodule.smul_mem _ _ hmem

theorem c_ne_zero (D : D7) :
    (((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
  have hrd : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  exact_mod_cast (div_pos (by linarith) (mul_pos hg0 hg1)).ne'

theorem kapN_ne_zero {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (hW : GoodW D τ w w' θ W) : kapN D θ ≠ 0 := by
  intro h0
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, hq, -⟩ := hW
  have hN0 : W.μN = 0 := by rw [hN, h0]; simp [haarLie]
  have hq1 := hq (fun _ => 1) measurable_const
  simp [muS, hN0] at hq1
  exact hG.2.1 hq1

theorem muN_haar {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') :
    IsHaarOn (Nset D.R.k D.R.rS) (toBessel D τ w w' θ W lam A hW hA hT hT').μN :=
  Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero hW) ENNReal.ofReal_ne_top

theorem side_pair {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) :
    Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam h A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) W.z
              (toBessel D τ w w' θ W lam A hW hA hT hT').c (toBessel D τ w w' θ W lam A hW hA hT hT').u W.π W.μW
              (toBessel D τ w w' θ W lam A hW hA hT hT').μN W.μG W.νS ∧
      Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam h A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) W.z'
        (toBessel D τ w w' θ W lam A hW hA hT hT').c (toBessel D τ w w' θ W lam A hW hA hT hT').u' W.π' W.μW'
        (toBessel D τ w w' θ W lam A hW hA hT hT').μN W.μG W.νS' := by
  set L := toBessel D τ w w' θ W lam A hW hA hT hT' with hL
  have hN := muN_haar hW hA hT hT'
  have hc : L.c ≠ 0 := c_ne_zero D
  have hw0 := lowest_K_type_unit hA
  have hW2 := hW
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hWN, hq0, hq0'⟩ := hW2
  have hμN : W.μN = L.μN := hWN
  have hq : PI.BesselPeriodGGP.IsQuotMeas W.μG (Formalism.FourierDecayAlt.ThreeDimData.muSof W.μW L.μN) W.νS := by
    rw [← hμN]; exact hq0
  have hq' : PI.BesselPeriodGGP.IsQuotMeas W.μG (Formalism.FourierDecayAlt.ThreeDimData.muSof W.μW' L.μN) W.νS' := by
    rw [← hμN]; exact hq0'
  exact ⟨⟨hA.1, hA.2.1, hg, hok, hw0, L.hz.1, L.hz.2, hc, L.hπ, L.hμW.1, hN, hG, hq⟩,
    ⟨hA.1, hA.2.1, hg, hok, hw0, L.hz'.1, L.hz'.2, hc, L.hπ', L.hμW'.1, hN, hG, hq'⟩⟩

theorem ls_pair (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hAt : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOne)
    {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) :
    ∃ (l : A.H → W.Wp) (l' : A.H → W.Wq),
      PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
        (psi D.R.k D.R.rS W.z (toBessel D τ w w' θ W lam A hW hA hT hT').c) A.σ W.π l ∧
      PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
        (psi D.R.k D.R.rS W.z' (toBessel D τ w w' θ W lam A hW hA hT hT').c) A.σ W.π' l' ∧
      Formalism.MainNotions.S.Pv.AmpDD.OnePlaceKF (toBessel D τ w w' θ W lam A hW hA hT hT') h W.μG
        (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) l l' := by
  set L := toBessel D τ w w' θ W lam A hW hA hT hT' with hL
  obtain ⟨h1, h2⟩ := side_pair hW hA hT hT' hg hok
  obtain ⟨l, hl, hla, -⟩ := hAt hI _ _ _ _ h _ A.σ _ W.Wp _ _ _ _ _ _ _ _ h1
  obtain ⟨l', hl', hla', -⟩ := hAt hI _ _ _ _ h _ A.σ _ W.Wq _ _ _ _ _ _ _ _ h2
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hw0 := lowest_K_type_unit hA
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0),
      x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  refine ⟨l, l', hl, hl', ⟨⟨hg, hok, c_ne_zero D, hw0, hG, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro x hx v hv
    exact (hla x (hDDs x hx) v (Or.inl hv)).2
  · intro x hx v hv
    exact (hla' x (hDDs x hx) v (Or.inl hv)).2
  · intro x hx v hv
    exact (hla x (hDDs x hx) v (Or.inr hv)).2
  · intro x hx v hv
    exact (hla' x (hDDs x hx) v (Or.inr hv)).2

theorem orbit_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {B l : H → V} (c0 : ℂ)
    (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = c0 • l v)
    (hlin : ∀ (a : ℂ), ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, l (a • v) = a • l v)
    {w0 : H} (hw0 : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (t : ℂ)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    B (σ g (t • w0)) = (c0 * t) • l (σ g w0) := by
  have hs : σ g w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hσ hw0 hg
  rw [map_smul, hB _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul t hs), hlin t _ hs, smul_smul]

theorem ampJ_mul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (νR : Measure (Mt k r)) (cN : ℝ)
    (Φ L1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp)
    (Φ' L1' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wq) (a a' : ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : γ ∈ UH (Hpk k r))
    (hΦ : ∀ g ∈ UH (Hpk k r), Φ g = a • L1 g) (hΦ' : ∀ g ∈ UH (Hpk k r), Φ' g = a' • L1' g)
    (hae : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r)) :
    ampJ νR cN Φ Φ' γ = (((cN : ℂ)⁻¹) * a * (starRingEnd ℂ) a') • ampJ νR 1 L1 L1' γ := by
  unfold ampJ
  have hcongr : (fun x : Mt k r => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) =ᵐ[νR]
      (fun x => (a * (starRingEnd ℂ) a') • (innerSL ℂ (L1' (Matrix.of x))).smulRight (L1 (γ * Matrix.of x))) := by
    filter_upwards [hae] with x hx
    have hγx : γ * Matrix.of x ∈ UH (Hpk k r) := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hγ hx
    rw [hΦ _ hγx, hΦ' _ hx]
    ext η
    simp [smul_smul, mul_comm]
    congr 1; ring
  rw [integral_congr_ae hcongr, integral_smul, smul_smul]
  simp only [Complex.ofReal_one, inv_one, one_smul]
  congr 1; ring

theorem psiGen_const {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    PI.BesselMapUniq.psiGen k r z (fun _ => c) = psi k r z c := by
  funext g
  unfold PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA psi ell
  rw [Finset.mul_sum]

theorem orbInt_smul {k r : ℕ} (L : LocBessel k r) (a : ℂ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) :
    OrbInt L (fun g => a • F g) γ ν = a • OrbInt L F γ ν := by
  unfold OrbInt
  rw [← integral_smul]
  congr 1
  funext p
  unfold besselIntg
  rw [smul_comm]
  congr 1
  ext η
  simp

theorem kfin_coef {k r : ℕ} (L : LocBessel k r) (a : ℂ) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v) (hv' : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v') :
    IsKFinCoefH L.σ (fun g => a • Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ' g) := by
  refine ⟨a • (innerSL ℂ v).smulRight ξ, (innerSL ℂ ξ').smulRight v', ?_, ?_, ?_⟩
  · intro η
    obtain ⟨S, hS, hvS, hSinv⟩ := hv'
    exact ⟨S, hS, S.smul_mem _ hvS, hSinv⟩
  · intro x
    have hadj : ContinuousLinearMap.adjoint (a • (innerSL ℂ v).smulRight ξ) x =
        ((starRingEnd ℂ) a * ⟪ξ, x⟫_ℂ) • v := by
      apply ext_inner_right ℂ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp [inner_smul_left, inner_smul_right]
      ring
    rw [hadj]
    obtain ⟨S, hS, hvS, hSinv⟩ := hv
    exact ⟨S, hS, S.smul_mem _ hvS, hSinv⟩
  · intro g
    ext η
    simp [Formalism.MainNotions.S.Pv.AmpDD.coefF, smul_smul]

theorem ae_UH_conj {k r : ℕ} {μG μR νR : Measure (Mt k r)}
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    (hG : IsHaarOn (UH (Hpk k r)) μG) (hR : IsHaarOn (RStab k r γ) μR)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
  have hc : Continuous (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j) := by
    have h1 : Continuous (fun x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => γ⁻¹ * x * γ) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h1
  have hf : Measurable (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j) := hc.measurable
  have hUm : MeasurableSet {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} :=
    Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet
  refine Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 ?_ ?_ hq
  · intro h0
    exact hR.2.1 ((Measure.map_eq_zero_iff hf.aemeasurable).1 h0)
  · rw [Measure.map_apply hf hUm]
    refine measure_mono_null (fun x hx => ?_) hR.2.2.1
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    intro hxR
    exact hx hxR.2.1

end Formalism.L2.SG.AmpOrbPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate Classical

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj

section HSForms

variable {Wq Wp : Type*} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem inner_hsEmb {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A A' : Wq →L[ℂ] Wp) :
    ⟪Formalism.L2.SG.PackageTie.hsEmb A, Formalism.L2.SG.PackageTie.hsEmb A'⟫_ℂ =
      ∑ j, ⟪A (stdOrthonormalBasis ℂ Wq j), A' (stdOrthonormalBasis ℂ Wq j)⟫_ℂ := by
  simp [Formalism.L2.SG.PackageTie.hsEmb, PiLp.inner_apply]

theorem inner_hsVec {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A A' : Wq →L[ℂ] Wp) :
    ⟪Formalism.FourierDecayAlt.B.hsVec A, Formalism.FourierDecayAlt.B.hsVec A'⟫_ℂ =
      ∑ j, ⟪A (stdOrthonormalBasis ℂ Wq j), A' (stdOrthonormalBasis ℂ Wq j)⟫_ℂ := by
  simp [Formalism.FourierDecayAlt.B.hsVec, PiLp.inner_apply]

private theorem sum_inner_basis_eq_trace_adjoint_comp {U Y : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [FiniteDimensional ℂ U] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ U) (N N' : U →L[ℂ] Y) :
    ∑ j, ⟪N (b j), N' (b j)⟫_ℂ =
      LinearMap.trace ℂ U ((ContinuousLinearMap.adjoint N ∘L N' : U →L[ℂ] U) : U →ₗ[ℂ] U) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem hsSum_conj {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] [FiniteDimensional ℂ Wp]
    (e : Wp ≃ₗᵢ[ℂ] V) (e' : Wq ≃ₗᵢ[ℂ] V') (M M' : Wq →L[ℂ] Wp) :
    ∑ j, ⟪((e.toContinuousLinearEquiv : Wp →L[ℂ] V).comp (M.comp (e'.symm.toContinuousLinearEquiv : V' →L[ℂ] Wq)))
        (stdOrthonormalBasis ℂ V' j),
      ((e.toContinuousLinearEquiv : Wp →L[ℂ] V).comp (M'.comp (e'.symm.toContinuousLinearEquiv : V' →L[ℂ] Wq)))
        (stdOrthonormalBasis ℂ V' j)⟫_ℂ =
    ∑ j, ⟪M (stdOrthonormalBasis ℂ Wq j), M' (stdOrthonormalBasis ℂ Wq j)⟫_ℂ := by
  have key := sum_inner_basis_eq_trace_adjoint_comp ((stdOrthonormalBasis ℂ V').map e'.symm) M M'
  simp only [OrthonormalBasis.map_apply] at key
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.inner_map_map]
  rw [key, sum_inner_basis_eq_trace_adjoint_comp]

end HSForms

section Joint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def locOp (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (v : InfinitePlace X.B.I.F) : X.Vloc u' v →L[ℂ] X.Vloc u v :=
  ((eP v).toContinuousLinearEquiv : Wp (S.pl (τ.symm v)) →L[ℂ] X.Vloc u v).comp
    (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
          (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
        Formalism.FourierDecayAlt.D.vecV (T (τ.symm v)).base (ν' (τ.symm v)) (m₀ (τ.symm v)) (f (τ.symm v))
          (Formalism.FourierDecayAlt.D.toStd S.G.r S.g 1 (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p))).comp
      ((eQ v).symm.toContinuousLinearEquiv : X.Vloc u' v →L[ℂ] Wq (S.pl (τ.symm v))))

theorem hsVec_smul {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    Formalism.FourierDecayAlt.B.hsVec (c • A) = c • Formalism.FourierDecayAlt.B.hsVec A := by
  unfold Formalism.FourierDecayAlt.B.hsVec
  ext i
  simp

theorem inner_V0Pt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (hVJ : VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ)
    (p q : Formalism.FourierDecayAlt.TB.Pt D.host.E) (wp wq : Point D.host.E (D.R.rS + 1))
    (hp : ptOfL (D := D) (D.R.rS + 1) p = some wp) (hq : ptOfL (D := D) (D.R.rS + 1) q = some wq)
    (hrp : ∃ γ, IsPtRep X u u' wp γ) (hrq : ∃ γ, IsPtRep X u u' wq γ)
    (hGp : ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' wp) v)
    (hGq : ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' wq) v) :
    ⟪Formalism.L2.SG.PackageTie.hsEmb (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wq),
              Formalism.L2.SG.PackageTie.hsEmb (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wp)⟫_ℂ =
      ∏ j : Fin S.f, ⟪Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) q),
        Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) p)⟫_ℂ := by
  rw [inner_hsEmb]
  rw [hsSum_tensor (X.tensU u') (X.tensU_inner u') (X.tensU_span u') (X.tensU u) (X.tensU_inner u)
    (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wq) (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wp)
    (locOp X S u u' T f ν' m₀ τ eP eQ q) (locOp X S u u' T f ν' m₀ τ eP eQ p)
    (fun x => by rw [hVJ q wq hq hrq hGq x]; rfl) (fun x => by rw [hVJ p wp hp hrp hGp x]; rfl)]
  rw [← Fintype.prod_equiv τ.symm (fun v => ⟪Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ (τ.symm v)
      (Formalism.FourierDecayAlt.C.loc (S.σ (τ.symm v)) q), Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ (τ.symm v)
      (Formalism.FourierDecayAlt.C.loc (S.σ (τ.symm v)) p)⟫_ℂ) _ (fun v => rfl)]
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold Formalism.FourierDecayAlt.JC.vecPlace
  rw [← hsVec_smul, ← hsVec_smul, inner_hsVec]
  unfold locOp
  have : FiniteDimensional ℂ (Wp (S.pl (τ.symm v))) := LinearEquiv.finiteDimensional (eP v).symm.toLinearEquiv
  exact hsSum_conj (eP v) (eQ v) _ _

end Joint

section Assembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def GoodPt (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  (∃ γ, IsPtRep X u u' w γ) ∧ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v

def PtSome (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) : Prop :=
  ∀ p : Formalism.FourierDecayAlt.TB.Pt D.host.E, Formalism.FourierDecayAlt.TB.IsPt p (S.G.r + 1) → ∃ w, ptOfL (D := D) (D.R.rS + 1) p = some w

def WtTie (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)), ptOfL (D := D) (D.R.rS + 1) p = some w →
    GoodPt X u u' w →
    Real.sqrt (nW X u u' w) =
      ∏ j, Real.sqrt (Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.σ j) p))

def LZero (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)), ptOfL (D := D) (D.R.rS + 1) p = some w →
    ¬ GoodPt X u u' w → VtPt X u u' sc i0 i0' FdN FdN' νq p = 0

def RZero (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)), ptOfL (D := D) (D.R.rS + 1) p = some w →
    ¬ GoodPt X u u' w → ∃ j,
      Real.sqrt (Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.σ j) p)) = 0 ∨
      Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) p) = 0

theorem alg_prod {ι : Type*} [Fintype ι] (a b : ι → ℝ) (c : ι → ℂ) :
    (starRingEnd ℂ) ((∏ j, b j : ℝ) : ℂ) * (((∏ j, a j : ℝ) : ℂ) * ∏ j, c j) = ∏ j, ((a j * b j : ℝ) : ℂ) * c j := by
  rw [Complex.conj_ofReal]
  simp only [Complex.ofReal_prod, Complex.ofReal_mul, Finset.prod_mul_distrib]
  ring

theorem inner_zero_of {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) (h : y = 0) :
    inner ℂ x y = 0 := by
  subst h
  simp

theorem inner_zero_of' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) (h : x = 0) :
    inner ℂ x y = 0 := by
  subst h
  simp

theorem rhs_zero (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (p q : Formalism.FourierDecayAlt.TB.Pt D.host.E)
    (h : (∃ j, Real.sqrt (Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.σ j) p)) = 0 ∨
      Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) p) = 0) ∨
      (∃ j, Real.sqrt (Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd j).G (Formalism.FourierDecayAlt.C.loc (S.σ j) q)) = 0 ∨
      Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ j (Formalism.FourierDecayAlt.C.loc (S.σ j) q) = 0)) :
    ∏ v, ((√(Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd v).G (Formalism.FourierDecayAlt.C.loc (S.σ v) p)) *
          √(Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd v).G (Formalism.FourierDecayAlt.C.loc (S.σ v) q)) : ℝ) : ℂ) *
        inner ℂ (Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v (Formalism.FourierDecayAlt.C.loc (S.σ v) q))
          (Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v (Formalism.FourierDecayAlt.C.loc (S.σ v) p)) = 0 := by
  rcases h with ⟨j, hj | hj⟩ | ⟨j, hj | hj⟩ <;>
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

theorem vt_good (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (hVJ : VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ) (hW : WtTie X S u u')
    (p q : Formalism.FourierDecayAlt.TB.Pt D.host.E) (wp wq : Point D.host.E (D.R.rS + 1))
    (hp : ptOfL (D := D) (D.R.rS + 1) p = some wp) (hq : ptOfL (D := D) (D.R.rS + 1) q = some wq)
    (gp : GoodPt X u u' wp) (gq : GoodPt X u u' wq) :
    inner ℂ (VtPt X u u' sc i0 i0' FdN FdN' νq q) (VtPt X u u' sc i0 i0' FdN FdN' νq p) = ∏ v,
      ((√(Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd v).G (Formalism.FourierDecayAlt.C.loc (S.σ v) p)) *
          √(Formalism.FourierDecayAlt.C.nLoc S.G.k S.G.r S.fr (S.pd v).G (Formalism.FourierDecayAlt.C.loc (S.σ v) q)) : ℝ) : ℂ) *
        inner ℂ (Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v (Formalism.FourierDecayAlt.C.loc (S.σ v) q))
          (Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v (Formalism.FourierDecayAlt.C.loc (S.σ v) p)) := by
  have ep : VtPt X u u' sc i0 i0' FdN FdN' νq p = ((Real.sqrt (nW X u u' wp) : ℝ) : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wp) := by
    unfold VtPt; rw [hp]
  have eq' : VtPt X u u' sc i0 i0' FdN FdN' νq q = ((Real.sqrt (nW X u u' wq) : ℝ) : ℂ) •
      Formalism.L2.SG.PackageTie.hsEmb (unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq wq) := by
    unfold VtPt; rw [hq]
  rw [ep, eq', inner_smul_left, inner_smul_right,
    inner_V0Pt X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ hVJ p q wp wq hp hq gp.1 gq.1 gp.2 gq.2,
    hW p wp hp gp, hW q wq hq gq]
  exact alg_prod _ _ _

theorem vtTensor_of_steps (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (hVJ : VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ) (hPt : PtSome S) (hW : WtTie X S u u')
    (hL : LZero X u u' sc i0 i0' FdN FdN' νq) (hR : RZero X S u u' T f ν' m₀) :
    Formalism.FourierDecayAlt.JCT.VtTensor S T f ν' m₀ (VtPt X u u' sc i0 i0' FdN FdN' νq) := by
  intro p q hpP hqP
  obtain ⟨wp, hp⟩ := hPt p hpP
  obtain ⟨wq, hq⟩ := hPt q hqP
  by_cases gp : GoodPt X u u' wp
  · by_cases gq : GoodPt X u u' wq
    · exact vt_good X S u u' sc i0 i0' FdN FdN' νq T f ν' m₀ τ eP eQ hVJ hW p q wp wq hp hq gp gq
    · rw [rhs_zero S T f ν' m₀ p q (Or.inr (hR q wq hq gq))]
      exact inner_zero_of' _ _ (hL q wq hq gq)
  · rw [rhs_zero S T f ν' m₀ p q (Or.inl (hR p wp hp gp))]
    exact inner_zero_of _ _ (hL p wp hp gp)

end Assembly

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

