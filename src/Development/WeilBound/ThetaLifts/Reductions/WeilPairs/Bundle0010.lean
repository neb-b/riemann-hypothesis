module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SpanInfRatF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0002
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0008
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutRealA
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF GlobalTheory.RealWeil

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

theorem ev_fderivF (hc : IsCharAF F ψ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (G : BBF σ JS JT ξ₀ ψ)
    (hG : Sm (rhoVF σ JS JT ξ₀ ψ hc ι) G) (z : IxF F nS nT → ℂ) (w : WOF F E nS nT) :
    (fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 z).1 w =
      deriv (fun t : ℝ => heisOF σ JS JT ξ₀ ψ (iotaVF ι (t • z)) G.1 w) 0 := by
  have hd : DifferentiableAt ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 :=
    (hG.differentiable (by simp)).differentiableAt
  let L : ↥(BBF σ JS JT ξ₀ ψ) →L[ℝ] ℂ :=
    ((BoundedContinuousFunction.evalCLM ℂ w).comp (BBF σ JS JT ξ₀ ψ).subtypeL).restrictScalars ℝ
  have hline : HasDerivAt (fun t : ℝ => t • z) z 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
  have h2 : HasDerivAt (fun t : ℝ => rhoVF σ JS JT ξ₀ ψ hc ι (t • z) G)
      (fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 z) 0 := by
    have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact h
  have h3 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  exact h3.deriv.symm

theorem fderiv_vacF (hc : IsCharAF F ψ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ)
    (G : BBF σ JS JT ξ₀ ψ) (hG : Sm (rhoVF σ JS JT ξ₀ ψ hc ι) G) (hv : IsVacF σ JS JT ξ₀ ψ ι s G.1)
    (z : IxF F nS nT → ℂ) :
    fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 z +
      Complex.I • fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 (Complex.I • s *ᵥ z) = 0 := by
  apply Subtype.ext
  ext w
  have h1 := ev_fderivF hc ι G hG z w
  have h2 := ev_fderivF hc ι G hG (Complex.I • s *ᵥ z) w
  have h3 := hv w z
  rw [PositivityTheory.ThKW.jV_apply] at h3
  simp only [Submodule.coe_add, Submodule.coe_smul, BoundedContinuousFunction.coe_add,
    BoundedContinuousFunction.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero,
    BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  rw [h1, h2]
  exact h3

variable {B : Base F E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}

theorem exists_inf_A (C : Ctx σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f := by
  obtain ⟨good, hS, hT, h0, hξ, hinf, hchart⟩ := C
  obtain ⟨hc, -⟩ := _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B good
  obtain ⟨hHh, hHd⟩ := _root_.GlobalTheory.RealWeilF.HMF_herm_det F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ
  have hheis : GlobalTheory.RealWeil.IsHeis
      (fun x y : IxF F nS nT → ℂ => (star y ⬝ᵥ (HMF JS JT ξ₀ (tauB B)).mulVec x).im)
      (rhoVF σ JS JT ξ₀ B.ψ hc ι) := by
    unfold GlobalTheory.RealWeil.IsHeis
    simp only [GlobalTheory.RealWeilF.rhoVF]
    refine ⟨fun f => ?_, fun u v f => ?_, fun u f => ?_, fun f => ?_⟩
    · rw [iotaVF_zero, rhoBF_zero]
    · rw [rhoBF_rhoBF, iotaVF_add,
        _root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart u v]
    · exact norm_rhoBF hc _ f
    · exact (_root_.GlobalTheory.RealWeilF.continuous_rhoBF F E σ nS nT JS JT ξ₀ B.ψ hc f).comp (continuous_iotaVF hchart)
  obtain ⟨Ω, hosc, hone1, hcont, hvac⟩ := _root_.GlobalTheory.RealWeil.UnitaryOsc.exists_osc (IxF F nS nT) (HMF JS JT ξ₀ (tauB B)) hHh hHd
    (↥(BBF σ JS JT ξ₀ B.ψ)) (rhoVF σ JS JT ξ₀ B.ψ hc ι) hheis (GAF σ JS × GAF σ JT) (mMF σ JS JT θ)
    (_root_.GlobalTheory.RealWeilF.mMF_unitary F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart)
  obtain ⟨hadd, hsmul, hsmp, hone, hmul, hequiv, hcomm7, hnorm⟩ := hosc
  have hSmθ : ∀ x : ↥(BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) →
      GlobalTheory.RealWeil.Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) x := fun x hx =>
    _root_.GlobalTheory.ThetaSmoothF.sm_of_thetaF F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart hc x hx
  have hcommA : ∀ u : WOF F E nS nT, Matrix.map u ⇑(infPartF F E) = 0 →
      ∀ (v : IxF F nS nT → ℂ) (z : ↥(BBF σ JS JT ξ₀ B.ψ)),
        rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v z) =
          rhoVF σ JS JT ξ₀ B.ψ hc ι v (rhoBF σ JS JT ξ₀ B.ψ hc u z) := by
    intro u hu v z
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀ u (iotaVF ι v) hu (real_iotaVF hchart v)
    simp only [GlobalTheory.RealWeilF.rhoVF]
    rw [rhoBF_rhoBF, rhoBF_rhoBF, h1, h2, add_comm u (iotaVF ι v)]
  have hfix : ∀ (u : WOF F E nS nT) (z : ↥(BBF σ JS JT ξ₀ B.ψ)),
      heisOF σ JS JT ξ₀ B.ψ u ⇑(z : BoundedContinuousFunction (WOF F E nS nT) ℂ) = ⇑(z : BoundedContinuousFunction (WOF F E nS nT) ℂ) → rhoBF σ JS JT ξ₀ B.ψ hc u z = z := by
    intro u z hz
    apply Subtype.ext
    apply DFunLike.coe_injective
    rw [coe_rhoBF, hz]
  have hth : ∀ p (x : ↥(BBF σ JS JT ξ₀ B.ψ)), IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) →
      IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑((Ω p x) : BoundedContinuousFunction (WOF F E nS nT) ℂ) := by
    intro p x hx
    have hsm := hSmθ x hx
    obtain ⟨-, ⟨U, hU, hUx⟩, -, -⟩ := hx
    refine _root_.GlobalTheory.ThetaOfSmF.theta_of_smF F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart hc (Ω p x) (hsmp p x hsm)
      ⟨U, hU, fun u hu hu0 => ?_⟩
    have hA : rhoBF σ JS JT ξ₀ B.ψ hc u x = x := hfix u x (hUx u hu hu0)
    have h7 := hcomm7 p (rhoBF σ JS JT ξ₀ B.ψ hc u) (fun v f => hcommA u hu0 v f) x hsm
    rw [hA] at h7
    rw [← coe_rhoBF hc u (Ω p x), ← h7]
  obtain ⟨om, hom⟩ := GlobalTheory.RealWeilF.exists_homF (_root_.GlobalTheory.TowerFD.thetaFunOF_bounded F E σ nS nT JS JT ξ₀ B.ψ hc) Ω hth
    (fun p x x' hx hx' => hadd p x x' (hSmθ x hx) (hSmθ x' hx'))
    (fun p a x hx => hsmul p a x (hSmθ x hx))
    (fun x hx => hone x (hSmθ x hx))
    (fun p p' x hx => hmul p p' x (hSmθ x hx))
  have hx : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ x : ↥(BBF σ JS JT ξ₀ B.ψ), ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) = f := by
    intro f hf
    have hb := _root_.GlobalTheory.TowerFD.thetaFunOF_bounded F E σ nS nT JS JT ξ₀ B.ψ hc f hf
    obtain ⟨hq, -, hcf, -⟩ := hf
    exact ⟨GlobalTheory.RealWeilF.toBF f hcf hb hq, rfl⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩,
    fun g hg h hh f hf => ?_, fun g hg h hh w₀ f hf => ?_⟩, fun s hss hpos p hsp f hf hv => ?_⟩
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [hom p x hf]
    exact hth p x hf
  · obtain ⟨x, rfl⟩ := hx f hf
    have e : (fun p => om p ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) w) = fun p => (↑(Ω p x) : BoundedContinuousFunction (WOF F E nS nT) ℂ) w :=
      funext fun p => by rw [hom p x hf]
    rw [e]
    exact (BoundedContinuousFunction.evalCLM ℂ w).continuous.comp
      (continuous_subtype_val.comp (hcont (_root_.GlobalTheory.RealWeilF.MCont.continuous_mMF F E σ B good nS nT JS JT θ hinf) x (hSmθ x hf)))
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [show om p ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) = ⇑((Ω p x) : BoundedContinuousFunction (WOF F E nS nT) ℂ) from hom p x hf]
    exact _root_.GlobalTheory.RealWeilF.lintegral_eq_of_normsF F E σ nS nT JS JT ξ₀ B.ψ hc μ 𝓕 hμ h𝓕 x (Ω p x)
      (fun Hs _ _ _ Φ hΦ => hnorm Hs Φ (fun v g => hΦ (iotaVF ι v) g) p x (hSmθ x hf))
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [hom (g, h) x hf, hone1 (g, h) (mMF_fin θ hg hh) x (hSmθ x hf)]
  · obtain ⟨x, rfl⟩ := hx f hf
    obtain ⟨u, v, hu, rfl⟩ := _root_.GlobalTheory.RealWeilF.exists_realZero_add_iotaVF F E nS nT θ ι hchart w₀
    have hθ0 := _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B good nS nT JS JT ξ₀ (u + iotaVF ι v) ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) hf
    obtain ⟨y, hy⟩ := hx _ hθ0
    have hyθ : IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑(y : BoundedContinuousFunction (WOF F E nS nT) ℂ) := by rw [hy]; exact hθ0
    have hsym := _root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀ u (iotaVF ι v) hu (real_iotaVF hchart v)
    have hyx : y = rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v x) := by
      apply Subtype.ext
      apply DFunLike.coe_injective
      show ⇑(y : BoundedContinuousFunction (WOF F E nS nT) ℂ) = ⇑((rhoBF σ JS JT ξ₀ B.ψ hc u (rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) x)) : BoundedContinuousFunction (WOF F E nS nT) ℂ)
      rw [hy, coe_rhoBF, coe_rhoBF, heisOF_heisOF, hsym.1, AddChar.map_zero_eq_one, one_smul]
    have hsmv : GlobalTheory.RealWeil.Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) (rhoVF σ JS JT ξ₀ B.ψ hc ι v x) := by
      apply hSmθ
      show IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑((rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) x) : BoundedContinuousFunction (WOF F E nS nT) ℂ)
      rw [coe_rhoBF]
      exact _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B good nS nT JS JT ξ₀ (iotaVF ι v) _ hf
    rw [← hy, hom (g, h) y hyθ, hyx, hcomm7 (g, h) _ (hcommA u hu) _ hsmv, hequiv (g, h) v x (hSmθ x hf),
      GlobalTheory.RealWeilF.actOF_add, _root_.GlobalTheory.RealWeilFinFix.actOF_fin F E σ nS nT JS JT g h hg hh u hu,
      _root_.GlobalTheory.RealWeilF.actOF_iotaVF F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart g h v, hom (g, h) x hf]
    have hsym2 := _root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀ u
      (iotaVF ι ((mMF σ JS JT θ (g, h)).mulVec v)) hu (real_iotaVF hchart _)
    show ⇑((rhoBF σ JS JT ξ₀ B.ψ hc u (rhoBF σ JS JT ξ₀ B.ψ hc
      (iotaVF ι ((mMF σ JS JT θ (g, h)).mulVec v)) (Ω (g, h) x))) : BoundedContinuousFunction (WOF F E nS nT) ℂ) = _
    rw [coe_rhoBF, coe_rhoBF, heisOF_heisOF, hsym2.1, AddChar.map_zero_eq_one, one_smul]
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [hom p x hf, hvac s p hss hpos hsp x (hSmθ x hf) (fun z => fderiv_vacF hc ι s x (hSmθ x hf) hv z)]
    rfl

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.FinIdemSmulOfReal
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem beta_iota_right (C : Ctx σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)) = Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWF θ x) v : ℝ)) :=
  TauSpanIdentities.beta_iota_right C x v

theorem beta_iota_left (C : Ctx σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι v) x) = Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) v (piWF θ x) : ℝ)) :=
  TauSpanIdentities.beta_iota_left C v x

theorem piWF_iotaVF (hι : IsChartF θ ι) (v : IxF F nS nT → ℂ) : piWF θ (iotaVF ι v) = v :=
  TauSpanIdentities.piWF_iotaVF hι v

theorem piWF_ratWF (C : Ctx σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    piWF θ (ratWF (F := F) y) = infRatF (tauB B) y :=
  TauSpanIdentities.piWF_ratWF C y

theorem finIdem_add_iota (hι : IsChartF θ ι) (x : WOF F E nS nT) : x = finIdem F E • x + iotaVF ι (piWF θ x) :=
  TauSpanIdentities.finIdem_add_iota hι x

theorem finIdem_smul_of_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : finIdem F E • u = u :=
  TauSpanIdentities.finIdem_smul_of_fin hu

theorem finIdem_smul_of_real {u : WOF F E nS nT} (hu : u.map (finPartF F E) = 0) : finIdem F E • u = 0 :=
  TauSpanIdentities.finIdem_smul_of_real hu

theorem continuous_piWF (C : Ctx σ B JS JT ξ₀ θ ι) : Continuous (piWF (nS := nS) (nT := nT) θ) :=
  TauSpanIdentities.continuous_piWF C

theorem piWF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    piWF θ (actOF σ JS JT g h x) = mMF σ JS JT θ (g, h) *ᵥ piWF θ x :=
  TauSpanIdentities.piWF_actOF C g h x

theorem symplOF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y :=
  TauSpanIdentities.symplOF_actOF C g h x y

theorem psi_rat (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y)) = 1 :=
  TauSpanIdentities.psi_rat C x y

theorem rhoFF_finRatF {g : GAF σ JS} {h : GAF σ JT} {a b} (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (y : Matrix (Fin nT) (Fin nS) E) : rhoFF σ JS JT (g⁻¹, h⁻¹) (finRatF F y) = finRatF F (b * y * a) :=
  TauSpanIdentities.rhoFF_finRatF ha hb y

theorem gamQF_eq_one_iff (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ z : ℤ, omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) = z :=
  TauSpanIdentities.gamQF_eq_one_iff C x y

theorem gamQF_eq_one_iff' (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y) = n :=
  TauSpanIdentities.gamQF_eq_one_iff' C x y

theorem infRatF_injective (B : Base F E) : Function.Injective (infRatF (nS := nS) (nT := nT) (tauB B)) :=
  TauSpanIdentities.infRatF_injective B

theorem span_infRatF (hB : B.IsGood σ) :
    Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B))) = ⊤ :=
  TauSpanIdentities.span_infRatF hB

theorem omV_laws {κ : Type} [Fintype κ] [DecidableEq κ] {H s : Matrix κ κ ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) :
    (∀ x y, omV H x y = -omV H y x) ∧ (∀ v, jV s (jV s v) = -v) ∧ (∀ x y, omV H x (jV s y) = omV H y (jV s x)) ∧
      ∀ v, v ≠ 0 → 0 < omV H v (jV s v) :=
  TauSpanIdentities.omV_laws hH hs hQ

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB
section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_integral_trace_one (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ w : 𝓞 E, w + sgOF σ w = 1 :=
  LatB.exists_w hB.cm hB.unram

theorem exists_good_norm_character (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam ∧
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  haveI := hB.galois
  exact LatB.exists_goodNorm hB.cm hB.unram

theorem lattice_stable_under_idempotents (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ := by
  intro e he a ha
  obtain ⟨hf, hfc, hcc⟩ := LatB.split_parts he
  exact ⟨LatB.idem_smul_mem he.1 hf ha, LatB.idem_smul_mem hcc hfc ha⟩

theorem lattice_index_prime_to_inert (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) :
    ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) :=
  LatB.idx_main hB.cm hfin

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ParsevalPol
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open scoped Pointwise in
theorem parseval_pol {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} (N : ℕ)
    (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N) (hec : Continuous e) (hes : Continuous e.symm)
    (hrat : ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z))
    (hrat' : ∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) :
    ∃ (μN : Measure (Fin N → AF F)) (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (c : ℝ),
      μN.IsAddHaarMeasure ∧ μW.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < c ∧
      ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
        ∫ w in 𝓕W, thV B.ψ Φ₁ (e w) * starRingEnd ℂ (thV B.ψ Φ₂ (e w)) ∂μW =
          (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μN := by
  obtain ⟨μW, 𝓕W, hμW, h𝓕W⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS (nT + nT)
  obtain ⟨i1, i2, -, -, -, -⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS (nT + nT)
  haveI := i1
  haveI := i2
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
  letI mP : MeasurableSpace (VA F N) := borel _
  haveI : BorelSpace (VA F N) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS (nT + nT)) := ⟨rfl⟩
  let ca : WOF F E nS (nT + nT) ≃ₜ+ VA F N :=
    { e.toAddEquiv with continuous_toFun := hec, continuous_invFun := hes }
  let me : WOF F E nS (nT + nT) ≃ᵐ VA F N := ca.toHomeomorph.toMeasurableEquiv
  have hme : ∀ w, me w = e w := fun _ => rfl
  have into : ∀ g ∈ ratLF F E nS (nT + nT), e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N), e.symm p ∈ ratLF F E nS (nT + nT) := by
    intro p hp
    obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    obtain ⟨x, hx⟩ := hrat' y z
    have : e.symm (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    rw [show ((fun i => algebraMap F (AF F) (y i)), fun i => algebraMap F (AF F) (z i)) =
      (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) from rfl, this]
    exact ⟨x, rfl⟩
  have hν : (μW.map me).IsAddHaarMeasure := ca.isAddHaarMeasure_map μW
  have h𝓕 : IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (me '' 𝓕W) (μW.map me) := by
    refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (μW.map me) μW :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕W = me.symm ⁻¹' 𝓕W :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕W.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕W.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show e ((g : WOF F E nS (nT + nT)) + x) = e g + e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS (nT + nT) := ⟨e.symm p, onto' p p.2⟩
      let h : ratLF F E nS (nT + nT) := ⟨e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro eq
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS (nT + nT) => e (t : WOF F E nS (nT + nT))) eq
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (k : ratLF F E nS (nT + nT)),
          (k : WOF F E nS (nT + nT)) = e.symm r → r +ᵥ me '' 𝓕W = me '' (k +ᵥ 𝓕W) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : VA F N) + e w = e ((k : WOF F E nS (nT + nT)) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (μW.map me) (p +ᵥ me '' 𝓕W) (q +ᵥ me '' 𝓕W)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕W.aedisjoint hgh
  have key : ∀ m : MeasurableSpace (Fin N → AF F), m = borel _ →
      ∃ (μ : @Measure _ m) (c : ℝ), @Measure.IsAddHaarMeasure _ _ _ m μ ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in me '' 𝓕W, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂(μW.map me) =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
    rintro m rfl
    exact PositivityTheory.ThKW.ParsevalPolarization.parseval_adelic_pair_fundamental hB N (μW.map me) hν (me '' 𝓕W) h𝓕
  obtain ⟨μN, c, hμN, hc, hK⟩ := key _ hb
  refine ⟨μN, μW, 𝓕W, c, hμN, hμW, h𝓕W, hc, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  rw [← hK Φ₁ hΦ₁ Φ₂ hΦ₂, MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, integral_map_equiv]
  rfl

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end

