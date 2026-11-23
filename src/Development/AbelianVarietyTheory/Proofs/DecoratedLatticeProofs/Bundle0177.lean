module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamAddSmulOfAgreeOffSet
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0006
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.ParClosed

variable {D : D7}

theorem chS_succ (c : Com D) (k : ℕ) : c.chS (k + 1) = c.μ (k + 1) * c.eps (k + 1) := by
  unfold Com.chS Com.eps Lift.chrStep
  split_ifs <;> simp

theorem chT_succ (c : Com D) (k : ℕ) : c.chT (k + 1) = c.μ (k + 1) * c.eps k := by
  unfold Com.chT Com.eps Lift.chrStep
  rcases Nat.even_or_odd k with hk | hk
  · have h1 : Odd (k + 1) := hk.add_one
    have h2 : ¬ Odd k := Nat.not_odd_iff_even.2 hk
    simp [h1, h2]
  · have h1 : ¬ Odd (k + 1) := Nat.not_odd_iff_even.2 hk.add_one
    simp [h1, hk]

theorem eps_succ (c : Com D) (k : ℕ) :
    c.chS (k + 1) * (c.chT (k + 1))⁻¹ * c.eps k = c.eps (k + 1) := by
  rw [chS_succ, chT_succ]
  exact by
    have h : ∀ a b e : (AE D)ˣ →* Circle, a * b * (a * e)⁻¹ * e = b := fun a b e => by
      rw [_root_.mul_inv_rev, mul_comm e⁻¹ a⁻¹, mul_comm a b]
      simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one]
    exact h _ _ _

abbrev vf (χ : (AE D)ˣ →* Circle) : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := GlobalTheory.LFun.val (F := D.host.F) χ

theorem vf_mul (χ ψ : (AE D)ˣ →* Circle) : vf (χ * ψ) = vf χ * vf ψ := by
  funext w; simp [vf]

theorem twist_sum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → GlobalTheory.LFun.Fam K)
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : GlobalTheory.LFun.twist (∑ i ∈ s, f i) z = ∑ i ∈ s, GlobalTheory.LFun.twist (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => funext w; simp [GlobalTheory.LFun.twist]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LFun.twist_add, ih]

theorem stepPar_eq (χS χT : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) :
    stepPar χS χT t B = GlobalTheory.LFun.twist B (vf (χS * χT⁻¹)) + GlobalTheory.LFun.segFam (vf χS) t := by
  funext w; simp [stepPar, GlobalTheory.LFun.twist, GlobalTheory.LFun.segFam, vf]

theorem chainPar_closed (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B k = GlobalTheory.LFun.twist (B + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i)) D.R.t) (vf (c.eps k)) := by
  induction k with
  | zero =>
    have h1 : vf (1 : (AE D)ˣ →* Circle) = 1 := funext fun w => GlobalTheory.LFun.val_one (F := D.host.F) w
    simp [chainPar, Com.eps, h1]
  | succ k ih =>
    rw [chainPar_succ, ih, stepPar_eq, GlobalTheory.LFun.twist_twist, ← vf_mul, eps_succ, Finset.sum_Icc_succ_top (by omega),
      ← add_assoc, GlobalTheory.LFun.twist_add (B + _), GlobalTheory.LFun.twist_segFam, ← vf_mul, chS_succ, mul_comm (c.eps (k + 1))]

theorem twist_vf (μ e : (AE D)ˣ →* Circle) : (vf (μ * e))⁻¹ * vf e = (vf μ)⁻¹ := by
  funext w; simp [vf, mul_comm]

theorem vf_quot (μ ν : (AE D)ˣ →* Circle) : (vf ν)⁻¹ * vf μ = vf (μ * ν⁻¹) := by
  funext w; simp [vf, mul_comm]

end GlobalTheory.ChainOnto.ParClosed


open GlobalTheory.ChainOnto.ParClosed in
theorem GlobalTheory.ChainOnto.chainPar_twist_chT : ∀ (D : D7) (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ),
    GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ =
      GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ +
        ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t := by
  intro D c B k
  change GlobalTheory.LFun.twist (chainPar c B k) (vf (c.chT (k + 1)))⁻¹ =
    GlobalTheory.LFun.twist B (vf (c.μ (k + 1)))⁻¹ + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t
  rw [chainPar_closed, GlobalTheory.LFun.twist_twist, chT_succ, twist_vf, GlobalTheory.LFun.twist_add, twist_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.LFun.twist_segFam, vf_quot]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSurjectiveOfAdjointNonvanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem ontoAll_of_chainUp : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ChainUp D → OntoAll D := by
  intro D hFin hMet hEig hInd hUp hGap c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨hs, hadj⟩ := hUp hGap c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨ipD₀, ip₀, hm₀⟩ := hMet c hc 0 (Nat.zero_le _) s₀ hs₀
  obtain ⟨ipD, ip, hm⟩ := hMet c hc k hk s hs
  haveI : FiniteDimensional ℂ (s₀.CC c) := hFin c hc 0 (Nat.zero_le _) s₀ hs₀
  let Sab := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  let R : GlobalTheory.LFun.Fam D.host.E → GlobalTheory.LFun.Fam D.host.E → Prop := fun B B' => ∀ w ∉ Sab, B w = B' w
  have hRe : Equivalence R :=
    ⟨fun _ _ _ => rfl, fun h w hw => (h w hw).symm, fun h h' w hw => (h w hw).trans (h' w hw)⟩
  have hlin₀ := _root_.GlobalTheory.ChainOnto.isPar_add_smul D c s₀
  refine _root_.GlobalTheory.ChainOnto.surjective_of_adjoint_separates (s₀.CC c) (s.CC c) (GlobalTheory.LFun.Fam D.host.E) (GlobalTheory.LFun.Fam D.host.E) ip₀ ip Θ
    (fun u B => IsPar u B) (fun x B => IsPar x B) R R (fun B => chainPar c B k)
    hm₀.herm hm₀.pos hm.pos hRe (hEig c hc 0 (Nat.zero_le _) s₀ hs₀) hlin₀.1 hlin₀.2 ?_ ?_ ?_
  · intro B B' h w hw
    exact _root_.GlobalTheory.ChainOnto.chainPar_inj D c k B B' w (h w hw)
  · intro ι x B hx hne
    refine hInd c hc k hk s hs ι x B hx ?_
    intro i i' hii'
    have := hne i i' hii'
    by_contra hcon
    push_neg at hcon
    exact this hcon
  · intro u B hu
    exact hadj ipD₀ ip₀ ipD ip hm₀ hm u B hu

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

variable {D : D7}

theorem rapidDec_val (hP : GlobalTheory.Published.CuspRapidDecay) {c : Com D} (hc : c.Is) {s : PiLocalization₂ D} (u : s.CC c)
    (v : SmT s.M) : GlobalTheory.Grow.RapidDec s.V (PiLocalization₂.val u v) := by
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 u.2)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r w =>
    have h1 := GlobalTheory.Grow.rapidDec_of_cuspForm hP hc.inf (hM.aut w) (hM.cusp w)
    have h2 : PiLocalization₂.val u (r • PiTensorProduct.tprod ℂ w) =
        r • PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w := by
      simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
    rw [h2]
    exact Grow.RapidDec.smul r h1
  | add x y hx hy =>
    have : PiLocalization₂.val u (x + y) = PiLocalization₂.val u x + PiLocalization₂.val u y := by simp [PiLocalization₂.val]
    rw [this]; exact hx.add hy

theorem upAdj_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  intro hP D _ c hc k _ s s' hs hs' p hp u y φ v _ w _
  have hF := _root_.GlobalTheory.ChainOnto.ThetaSwap.integral_swap D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hc.inf hp.weil (p.pt φ) (hp.theta φ)
    s.ν s.fd s'.ν s'.fd hs.haar hs.fund hs'.haar hs'.fund (PiLocalization₂.val u v) (PiLocalization₂.val y w)
    (rapidDec_val hP hc u v) (rapidDec_val hP hc y w)
  simp only [PiLocalization₂.pet, Lift.pet, Step.up]
  calc ∫ h in s'.fd, PiLocalization₂.val y w h * starRingEnd ℂ (∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * PiLocalization₂.val u v g ∂s.ν) ∂s'.ν
      = ∫ h in s'.fd, ∫ g in s.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s.ν ∂s'.ν := by
        congr 1; funext h
        rw [← integral_conj, ← integral_const_mul]
        congr 1; funext g
        simp only [map_mul, Complex.conj_conj]; ring
    _ = ∫ g in s.fd, ∫ h in s'.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s'.ν ∂s.ν := hF
    _ = ∫ g in s.fd, PiLocalization₂.val (p.io y) (p.It φ w) g * starRingEnd ℂ (PiLocalization₂.val u v g) ∂s.ν := by
        congr 1; funext g
        rw [integral_mul_const]
        congr 1
        exact hp.io.eq y φ w g

end GlobalTheory.ChainOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaOfHeisenbergIntertwinerBoundedAtZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.ThetaMap

variable {D : D7}

theorem heisO_apply_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (g : WO S T → ℂ) :
    heisO ψ S T w g 0 = g w := by
  have h0 : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h0]

theorem thetaMap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T S₀ T₀ : HSp D) (ι : WO S₀ T₀ →+ WO S T), Continuous ι → (∀ w, w.map (finPart D) = 0 → (ι w).map (finPart D) = 0) → (∀ w, w.map (infPart D) = 0 → (ι w).map (infPart D) = 0) → ∀ A : (WO S T → ℂ) → WO S₀ T₀ → ℂ, IsSobForm ψ θ S T (fun f => A f 0) → (∀ f w, IsThetaFunO ψ S T f → A (heisO ψ S T (ι w) f) = heisO ψ S₀ T₀ w (A f)) → (∀ f γ, IsThetaFunO ψ S T f → A f (ratW T₀ S₀ γ) = A f 0) → ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S₀ T₀ (A f) := by
  intro D ψ hψ θ hθ S T S₀ T₀ ι hιc hιf hιi A hA hint hrat f hf

  have key : ∀ w, A f w = A (heisO ψ S T (ι w) f) 0 := by
    intro w
    rw [hint f w hf, heisO_apply_zero]
  have hfun : A f = fun w => (fun g => A g 0) (heisO ψ S T (ι w) f) := funext key
  obtain ⟨hc, hs⟩ := _root_.GlobalTheory.Unf.MatCoef.matCoef_smooth D ψ hψ θ hθ S T (fun g => A g 0) hA f hf
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro γ w
    have h1 := hrat (heisO ψ S T (ι w) f) γ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (ι w))
    rw [hint f w hf, heisO_apply_zero] at h1
    simp only [heisO] at h1
    rw [← h1, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  ·
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap ι, hUo.preimage hιc, fun u hu hui => ?_⟩
    rw [← hint f u hf, hU (ι u) hu (hιi u hui)]
  ·
    rw [hfun]
    exact hc.comp hιc
  ·
    intro k L hL hLf w
    have h2 := hs k (ι.comp L) (hιc.comp hL) (fun t => hιf (L t) (hLf t)) (ι w)
    rw [hfun]
    simpa [map_add (f := _)] using h2

end GlobalTheory.ThetaMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedFrameGramOrth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem transported_frame_gram_orth : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (i j : Fin (D.sp.X 0).rank) (a : Fin D.R.rS), (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) = (D.sp.X 0).gram i j ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.eX a) = 0 ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.fY a) = 0 ∧ (VS D).hT (X.zu u) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) = 0 := by
  intro D X u F₀ tr i j a
  have key : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) (tr.wt.symm y) = (VS D).hT x y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have key2 : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) y = (VS D).hT x (tr.wt y) := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have key3 : ∀ (x y : (VS D).V), (VS D).hT x (tr.wt.symm y) = (VS D).hT (tr.wt x) y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key, Fin.cast_cast, Fin.cast_eq_self]
    exact D.sp.iXY_isom 0 hm _ _
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_e]
    exact (D.sp.hyp_orthX a _).1
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_f]
    exact (D.sp.hyp_orthX a _).2
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key3, tr.weight_z]
    exact Formalism.MainNotions.BridgeLemma₂.z_orth_embedding D u _

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnWeightSpreadLeTwoMulScale
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.SpreadBound

theorem spread_lamOf_le {R : Ranks} (p : HCParam R) (j : ℕ) (hj : j ≤ R.m) (hk : 0 < R.k) (hm : R.m - 1 < R.m) :
    (((Formalism.BasicNotions.Examples₂.lamOf p j).spread : ℤ) : ℚ) ≤ p.u ⟨0, hk⟩ + p.e ⟨R.m - 1, hm⟩ + R.N R.m := by
  have hN : 0 < R.N j := by unfold Ranks.N; omega
  have hNm := Formalism.BasicNotions.Examples₂.N_mono (R := R) hj
  have h2 := R.two_le_m
  unfold DomWeight.spread
  rw [dite_eq_left hN]
  push_cast
  rw [Formalism.BasicNotions.Examples₂.lamOf_eq p j hj, Formalism.BasicNotions.Examples₂.lamOf_eq p j hj, Formalism.BasicNotions.Examples₂.wtQ_eq_wtN, Formalism.BasicNotions.Examples₂.wtQ_eq_wtN]
  have a1 : Formalism.BasicNotions.Examples₂.wtN p (R.N R.m - 1) ≤ Formalism.BasicNotions.Examples₂.wtN p (R.N j - 1) :=
    Formalism.BasicNotions.Examples₂.wtN_anti p (by omega) (by omega)
  have hmul : R.m * (R.t + 1) = (R.m - 1) * (R.t + 1) + (R.t + 1) := by
    obtain ⟨n, hn⟩ : ∃ n, R.m = n + 1 := ⟨R.m - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]; ring
  have hb : Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) = R.m - 1 := by
    unfold Formalism.BasicNotions.Examples₂.blkN Ranks.N
    have : R.k + R.m * (R.t + 1) - 1 - R.k = R.t + (R.t + 1) * (R.m - 1) := by
      rw [hmul, mul_comm (R.t + 1)]; omega
    rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have a2 : -p.e ⟨R.m - 1, hm⟩ ≤ Formalism.BasicNotions.Examples₂.wtN p (R.N R.m - 1) := by
    have c1 : ¬ R.N R.m - 1 < R.k := by unfold Ranks.N; omega
    have c2 : Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) < R.m := by omega
    unfold Formalism.BasicNotions.Examples₂.wtN
    rw [dite_eq_right c1, dite_eq_left c2]
    have e : (⟨Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1), c2⟩ : Fin R.m) = ⟨R.m - 1, hm⟩ := Fin.ext hb
    rw [e]
    unfold wG
    push_cast
    have : (0 : ℚ) ≤ (2 * ((Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) + 1) - 1) * ((R.t : ℚ) + 1) / 2 := by
      have : (0 : ℚ) ≤ 2 * ((Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) + 1) - 1 := by
        have : (0 : ℚ) ≤ (Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) := by positivity
        linarith
      positivity
    have : (0 : ℚ) ≤ (R.k : ℚ) / 2 := by positivity
    linarith
  have a3 : Formalism.BasicNotions.Examples₂.wtN p 0 ≤ p.u ⟨0, hk⟩ := by
    unfold Formalism.BasicNotions.Examples₂.wtN
    rw [dite_eq_left hk]
    unfold hcToWeightQ rhoVec
    have : (1 : ℚ) ≤ R.k := by exact_mod_cast hk
    simp only [Nat.cast_zero]
    linarith
  have a4 : (R.N j : ℚ) ≤ R.N R.m := by exact_mod_cast hNm
  simp only
  linarith

end GlobalTheory.CoreHt.SpreadBound

namespace GlobalTheory.CoreHt.SpreadBound

theorem spread_lamTrue_le : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → ∀ (u : B.Word) (j : ℕ), j ≤ B.R.m → ∀ τ,
    ((B.wts.lamTrue u j τ).spread : ℝ) ≤ 2 * L.sc.a := by
  intro B X I _ l Z L CY hS hX hx u j hj τ
  obtain ⟨⟨P⟩, -, -, ⟨hN3, -, hmt, hkS, hbT⟩, -, hT⟩ := hS
  have hm := B.R.two_le_m
  have hk : 5 ≤ B.R.k := by have := B.R.m_add_three_le_k; omega
  have hk0 : 0 < B.R.k := by omega
  have hm1 : B.R.m - 1 < B.R.m := by omega
  have c1 := spread_lamOf_le (B.hcW u τ) j hj hk0 hm1
  have c2 : (((B.wts.lamTrue u j τ).spread : ℤ) : ℝ) ≤
      (((B.hcW u τ).u ⟨0, hk0⟩ : ℚ) : ℝ) + (((B.hcW u τ).e ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ) + B.R.N B.R.m := by
    unfold Wts.lamTrue
    rw [spread_shiftW]
    exact_mod_cast c1
  refine c2.trans ?_
  have hx1 := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have hb2 : 2 * L.sc.b ≤ L.sc.a := by rw [ha]; nlinarith
  have hX0 : 0 < L.sc.X' := by linarith
  have hb'a : L.sc.b' ≤ L.sc.a / 8 := by
    have : 0 < L.sc.a := by linarith
    exact div_le_div_of_nonneg_left this.le (by norm_num) hX
  have hb'0 : 0 < L.sc.b' := by
    have : 0 < L.sc.a := by linarith
    exact div_pos this hX0
  have hn1 : (1 : ℝ) ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.n := by
    have : 1 ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.n := by
      have h₁ := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.two_le_m
      have h₂ := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m_le_f
      unfold Ranks.n
      omega
    exact_mod_cast this
  have hw : L.sc.w'' (I.rec7 l Z).R.n ≤ L.sc.b' :=
    div_le_self hb'0.le (one_le_mul_of_one_le_of_one_le hx1.le hn1)
  have he := L.etaSz_pos
  have hS0 := L.Sc_pos
  have hm' : (2 : ℝ) ≤ B.R.m := by exact_mod_cast hm
  have hk' : (5 : ℝ) ≤ B.R.k := by exact_mod_cast hk
  have ht : (0 : ℝ) ≤ B.R.t := Nat.cast_nonneg _
  have heta : 2 * L.etaSz ≤ L.sc.b' := by
    have h1 : (2 : ℝ) ≤ B.R.m * ((B.R.t : ℝ) + 1) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 he.le
    have h3 : (B.R.m : ℝ) * ((B.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' (I.rec7 l Z).R.n := hmt
    linarith
  have hSc : 5 * L.Sc ≤ L.sc.b' := by
    have h3 : (B.R.k : ℝ) * L.Sc ≤ L.sc.w'' (I.rec7 l Z).R.n := hkS
    nlinarith
  have hN1 : (1 : ℝ) ≤ B.R.N B.R.m := by
    have : 1 ≤ B.R.N B.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hNeta : (B.R.N B.R.m : ℝ) ≤ L.etaSz := by
    have h3 : 4 * (B.R.N B.R.m : ℝ) ^ 3 ≤ L.etaSz := hN3
    have h4 : (B.R.N B.R.m : ℝ) ^ 1 ≤ (B.R.N B.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
    rw [pow_one] at h4
    linarith
  have hkN : (B.R.k : ℝ) ≤ B.R.N B.R.m := by
    have : B.R.k ≤ B.R.N B.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hu0 : (B.hcW u τ).u ⟨0, hk0⟩ = ((I.rec7 l Z).hc τ).u ⟨0, hk0⟩ := (I.rec7 l Z).hcW_first u τ hk0
  have he0 : (B.hcW u τ).e = ((I.rec7 l Z).hc τ).e := (I.rec7 l Z).hcW_e u τ
  have hwm : wj (I.rec7 l Z) B.R.m τ = (((B.hcW u τ).e ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (show B.R.m - 1 < (I.rec7 l Z).R.m from hm1)]
    exact (congrArg (fun f => ((f ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ)) he0).symm
  rw [← hwm, hu0]
  by_cases htop : ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) ∈ (I.rec7 l Z).host.topPlaces
  · obtain ⟨t, htt⟩ : ∃ t : (I.rec7 l Z).host.TT,
        ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) = (I.rec7 l Z).R.tau1 t := by
      unfold Host.topPlaces at htop
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
      exact ⟨⟨t, ht⟩, hte.symm⟩
    rw [(L.top_u τ t hk0 htt).1]
    show (L.aT t : ℝ) + ((B.R.k : ℝ) - 1) / 2 + wj (I.rec7 l Z) B.R.m τ + (B.R.N B.R.m : ℝ) ≤ 2 * L.sc.a
    have a1 : wj (I.rec7 l Z) B.R.m τ ≤ (L.bT t : ℝ) + L.sc.b' / L.sc.x + L.etaSz :=
      (L.win_top B.R.m (by omega) le_rfl τ t htt).2
    have a2 : (L.aT t : ℝ) ≤ L.sc.a + L.sc.a / ((B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) := (L.aT_win t).2
    have a3 : (5 : ℝ) ≤ (B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)))
    have a4 : L.sc.a / ((B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1.le
    have a6 := hbT t
    linarith
  · have h1 := P.cloud_place_bound τ (by show 0 < B.R.k - 1; omega) htop
    have h2 := (L.cloud_v τ ⟨0, by show 0 < B.R.k - 1; omega⟩).2
    push_cast at h1
    by_cases hc : ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) ∈ (I.rec7 l Z).host.thickPlaces
    · have a1 := hT B.R.m (by omega) le_rfl τ hc
      linarith
    · have a1 := (L.win_thin B.R.m (by omega) le_rfl τ ⟨((I.rec7 l Z).eTau τ).2, htop, hc⟩).2
      linarith

end GlobalTheory.CoreHt.SpreadBound
end

