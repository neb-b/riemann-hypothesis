module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0077
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalIffSecondModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.SBesFlagTie

open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

variable {D : D7}

theorem unip_joint {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂] (f : A →+* R₁) (g : A →+* R₂)
    (hinj : ∀ y, f y = 0 → g y = 0 → y = 0) (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ}
    (E : Matrix (Fin n) (Fin ρ) A) (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A) :
    Unip E K M ↔ Unip (E.map f) (K.map f) (M.map f) ∧ Unip (E.map g) (K.map g) (M.map g) :=
  _root_.GlobalTheory.BesselChar.JointSplit.unip_iff_of_joint f g hinj hsurj E K M

theorem unip_pi {ι S : Type} [Fintype ι] [DecidableEq ι] [CommRing S] {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) (ι → S))
    (K : Matrix (Fin ρ) (Fin n) (ι → S)) (M : Matrix (Fin n) (Fin n) (ι → S)) :
    Unip E K M ↔ ∀ i, Unip (E.map (Pi.evalRingHom (fun _ => S) i)) (K.map (Pi.evalRingHom (fun _ => S) i))
      (M.map (Pi.evalRingHom (fun _ => S) i)) :=
  _root_.GlobalTheory.BesselChar.unip_pi_iff E K M

theorem unip_real (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (z : Fin I.n → I.E) (hc : ∀ a, c a ≠ 0) (hz : ∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0)
    (N : Matrix (Fin I.n) (Fin I.n) ℂ) :
    Unip ((Matrix.of fun k a => c a * x a k).map (I.φ v))
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) N ↔
    InN (I.ε v) (fun a => rv I v (x a)) (rv I v z) ((I.P v)⁻¹ * N * I.P v) :=
  _root_.GlobalTheory.RealUnipFrame.unip_iff_inN I v x c z hc hz N

theorem unip_fin (I : Formalism.MainNotions.S.AutInst) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (z : Fin I.n → I.E) (hc : ∀ a, c a ≠ 0) (hz : ∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0)
    (N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    Unip ((Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)))
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) N ↔
    ((∀ a : Fin ρ, (N - 1) *ᵥ incl I (x a) ∈
        Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => incl I (x b)) '' {b | b.1 < a.1})) ∧
    (N - 1) *ᵥ incl I z ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (x b)) ∧
    ∀ y : VA I, (∀ a, hA I (incl I (x a)) y = 0) →
      (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (x b))) :=
  GlobalTheory.T.isFlagUnipotent_finiteAdeles_iff_frame_unipotentRadical I x c z hc hz N

theorem eM_linIndep (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E) (ht : t ≠ 0)
    (hl : lam ≠ 0) : LinearIndependent D.host.E (GlobalTheory.Core.SBesEx.eM X h t lam).transpose :=
  _root_.GlobalTheory.Core.SBesEx.eM_transpose_linearIndependent X h t lam ht hl

theorem unip_congr {R : Type} [CommRing R] {n ρ : ℕ} {E E' : Matrix (Fin n) (Fin ρ) R}
    {K K' : Matrix (Fin ρ) (Fin n) R} {M M' : Matrix (Fin n) (Fin n) R} (hE : E = E') (hK : K = K') (hM : M = M') :
    Unip E K M ↔ Unip E' K' M' := by
  subst hE hK hM; rfl

theorem castGA_self {I : Formalism.MainNotions.S.AutInst} (e : I = I) (x : I.GA) : castGA e x = x := rfl

theorem thetaV_incA (v : InfinitePlace (Formalism.L2.SG.InstExistsPf.instOf D).F) (y : D.host.E) :
    thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D y) = (Formalism.L2.SG.InstExistsPf.instOf D).φ v y := by
  have := thetaV_tmul (Formalism.L2.SG.InstExistsPf.instOf D) v 1 y
  rw [map_one, one_mul] at this
  exact this

theorem tauF_incA (y : D.host.E) :
    tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D y) = Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) y := by
  exact tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) 1 y

theorem core (D : D7) {ρ : ℕ} (x : Fin ρ → Fin (D.sp.Y 0).rank → D.host.E) (c : Fin ρ → D.host.E)
    (z : Fin (D.sp.Y 0).rank → D.host.E) (hc : ∀ a, c a ≠ 0)
    (hz : ∀ a, Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J (x a) z = 0)
    (hLI : LinearIndependent D.host.E (Matrix.of fun k a => c a * x a k).transpose) (g : GA D (D.sp.Y 0)) :
    g ∈ NFlag (D.sp.Y 0) (Matrix.of fun k a => c a * x a k) ↔
      (Formalism.IndefR.RationalEmbedding.iota D g).1 ∈ Ninf (Formalism.L2.SG.InstExistsPf.instOf D) x z ∧
        (Formalism.IndefR.RationalEmbedding.iota D g).2 ∈ Nfin (Formalism.L2.SG.InstExistsPf.instOf D) x z := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  have hb1 : ∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) = ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) g v :=
    fun v => (hb.1 v).trans (congrArg (fun q => ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) q v) key)
  have hb2 : (Formalism.IndefR.RationalEmbedding.inst D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) g :=
    hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)
  refine (GlobalTheory.BesselChar.mem_NFlag_iff _ _ hLI g).trans ?_
  refine (unip_joint (A := AF D.host.F ⊗[D.host.F] D.host.E) (Pi.ringHom fun v => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v)
      (tauF (Formalism.L2.SG.InstExistsPf.instOf D))
      (fun y h1 h2 => Formalism.L2.SG.Pf.TT_ext _ y (fun v => congr_fun h1 v) h2)
      (fun a b => by
        obtain ⟨y, h1, h2⟩ := Formalism.L2.SG.Pf.TT_surj (Formalism.L2.SG.InstExistsPf.instOf D) a b
        exact ⟨y, funext h1, h2⟩) _ _ _).trans ?_
  refine (and_congr_left' (unip_pi _ _ _)).trans ?_
  refine and_congr (forall_congr' fun v => ?_) ?_
  · have hR := unip_real (Formalism.L2.SG.InstExistsPf.instOf D) v x c z hc hz
      ((hmat (Formalism.IndefR.RationalEmbedding.inst D) g).map (thetaV (Formalism.IndefR.RationalEmbedding.inst D) v))
    refine (unip_congr (Matrix.ext fun k a => thetaV_incA v _) (Matrix.ext fun k a => thetaV_incA v _)
      (Matrix.ext fun k a => rfl)).trans (hR.trans ?_)
    show _ ↔ InN _ _ _ (uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v))
    rw [hb1 v]
    rfl
  · have hF := unip_fin (Formalism.L2.SG.InstExistsPf.instOf D) x c z hc hz
      ((hmat (Formalism.IndefR.RationalEmbedding.inst D) g).map (tauF (Formalism.IndefR.RationalEmbedding.inst D)))
    refine (unip_congr (Matrix.ext fun k a => tauF_incA _) (Matrix.ext fun k a => tauF_incA _)
      (Matrix.ext fun k a => rfl)).trans (hF.trans ?_)
    show _ ↔ (_ ∧ _ ∧ _)
    rw [hb2]
    rfl

theorem transport (D : D7) (I : Formalism.MainNotions.S.AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n) {ρ : ℕ} (eR : Fin ρ → Fin I.n → I.E)
    (zR : Fin I.n → I.E) (s : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    ((castGA hI.symm s).1 ∈ Ninf I eR zR ↔ s.1 ∈ Ninf (Formalism.L2.SG.InstExistsPf.instOf D)
      (fun a k => ιE (eR a (Fin.cast hr k))) (fun k => ιE (zR (Fin.cast hr k)))) ∧
    ((castGA hI.symm s).2 ∈ Nfin I eR zR ↔ s.2 ∈ Nfin (Formalism.L2.SG.InstExistsPf.instOf D)
      (fun a k => ιE (eR a (Fin.cast hr k))) (fun k => ιE (zR (Fin.cast hr k)))) ∧
    ∀ p q : Fin I.n → I.E, Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J
      (fun k => ιE (p (Fin.cast hr k))) (fun k => ιE (q (Fin.cast hr k))) =
        ιE (Formalism.UG.hform (starRingEnd I.E) I.J p q) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hv : ∀ p : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E,
      (fun k => ιE (p (Fin.cast hr k))) = p := fun p => funext fun k => by rw [hid]; rfl
  have hx : (fun a k => ιE (eR a (Fin.cast hr k))) = eR := funext fun a => hv (eR a)
  refine ⟨?_, ?_, fun p q => ?_⟩
  · rw [castGA_self]
    exact Iff.of_eq (congrArg₂ (fun A B => s.1 ∈ Ninf (Formalism.L2.SG.InstExistsPf.instOf D) A B) hx.symm (hv zR).symm)
  · rw [castGA_self]
    exact Iff.of_eq (congrArg₂ (fun A B => s.2 ∈ Nfin (Formalism.L2.SG.InstExistsPf.instOf D) A B) hx.symm (hv zR).symm)
  · exact (congrArg₂ (fun A B => Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J A B)
      (hv p) (hv q)).trans (hid _).symm

theorem mem_flagN_iff : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → IdE X → ∀ (V₀ : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS), d.e = GlobalTheory.Core.SBesEx.eM X h t lam → ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u := by
  intro D X h u t lam ht hl hId V₀ d hd n
  have hLI := eM_linIndep X h t lam ht hl
  have hsc : ∀ a, GlobalTheory.Core.SBesEx.scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have horth : ∀ a, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.zR u) = 0 := by
    intro a
    apply X.ιE.injective
    show X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd (X.eX a)) (X.crd (X.zu u))) = X.ιE 0
    rw [Formalism.L2.SG.PoincareInHH.Cut.hform_crd X, map_zero]
    exact (X.zu_orth u a).1
  have hT := transport D X.B.I X.ιE hId h (rank_eq X h) X.eR (X.zR u) (Formalism.IndefR.RationalEmbedding.iota D n)
  have hz : ∀ a, Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J
      (fun k => X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) (fun k => X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) = 0 :=
    fun a => by rw [hT.2.2, horth a, map_zero]
  have hcore := core D (fun a k => X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) (GlobalTheory.Core.SBesEx.scl t lam)
    (fun k => X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) hsc hz hLI n
  show n ∈ NFlag (D.sp.Y 0) d.e ↔ _
  rw [hd]
  exact hcore.trans (and_congr hT.1.symm hT.2.1.symm)

end GlobalTheory.Core.SBesFlagTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

theorem exists_finSection (D : D7) :
    ∃ s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D, Continuous s ∧ (∀ a, finPart D (s a) = a) ∧
      ∀ a, infPart D (s a) = 0 := by
  obtain ⟨e, he, -, hec⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inr _ _), hec.comp (continuous_const.prodMk continuous_id),
    fun a => ?_, fun a => ?_⟩
  · have := (he (e.symm (0, a))).2
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  · have := (he (e.symm (0, a))).1
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm

theorem isOpen_intAE (D : D7) : IsOpen (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
  have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
  have hs : (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) = {z | ∃ y ∈ intAE D, z = 1 • y} := by
    ext z
    constructor
    · intro h
      exact ⟨z, h, (one_nsmul z).symm⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hs]
  exact this

theorem isCompact_intAE (D : D7) : IsCompact (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨C, hC, hCd⟩ := GlobalTheory.SmoothForms.Cover.exists_compact_denom D 1 one_pos
  exact hC.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (isOpen_intAE D)) fun y hy => hCd y (by simpa using hy)

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

def chartM (σ : (D.what₂.Tau → ℂ) →+ AE D) (m n : ℕ) : (D.what₂.Tau → Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun c := Matrix.of fun i j => σ fun τ => c τ i j
  map_zero' := by
    funext i j
    show σ (fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ i j) = 0
    exact σ.map_zero
  map_add' c c' := by
    funext i j
    show σ (fun τ => (c + c') τ i j) = σ (fun τ => c τ i j) + σ (fun τ => c' τ i j)
    exact σ.map_add _ _

theorem continuous_chartM {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Continuous σ) (m n : ℕ) :
    Continuous (chartM σ m n) :=
  continuous_pi fun i => continuous_pi fun j => hσ.comp (continuous_pi fun τ =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ)))

theorem compAt_chartM {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n : ℕ}
    (c : D.what₂.Tau → Fin m → Fin n → ℂ) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    compAt θ τ (chartM σ m n c) i j = c τ i j :=
  hσ.comp (fun τ => c τ i j) τ

theorem finPart_chartM {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n : ℕ}
    (c : D.what₂.Tau → Fin m → Fin n → ℂ) : (chartM σ m n c).map (finPart D) = 0 := by
  funext i j
  exact hσ.fin _

theorem decomp {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D} (hsf : ∀ a, finPart D (s a) = a) (hsi : ∀ a, infPart D (s a) = 0)
    {m n : ℕ} (y : Mx D m n) :
    y = s.mapMatrix (y.map (finPart D)) + chartM σ m n (fun τ i j => compAt θ τ y i j) := by
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · show finPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j)) = 0
    rw [RingHom.map_sub, RingHom.map_add (f := _), hsf, hσ.fin, add_zero, sub_self]
  · show θ τ (infPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j))) = 0
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_add (f := _), hsi, hσ.comp, RingHom.map_zero, zero_add]
    exact sub_self _

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}


open Classical in
theorem coset_mem_SB {m n : ℕ} (W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)))
    (hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))))
    (hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))))
    (q : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) :
    (fun a : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E =>
      if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = q then (1 : ℂ) else 0) ∈
      GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hmk : IsLocallyConstant
      (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => (a : _ ⧸ W)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  have hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    AddSubgroup.isClosed_of_isOpen _ hWo
  let K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    (fun b : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => q.out + b) '' (W : Set _)
  have hKc : IsCompact K := hWc.image (continuous_const.add continuous_id)
  have hKcl : IsClosed K := (Homeomorph.addLeft q.out).isClosedMap _ hcl
  refine HasCompactSupport.intro' hKc hKcl fun x hx => ?_
  show (if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x) : _ ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  have h1 : (QuotientAddGroup.mk q.out : _ ⧸ W) = QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x) := by
    rw [hq, QuotientAddGroup.out_eq']
  exact ⟨-q.out + (show Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) from x), QuotientAddGroup.eq.1 h1,
    add_neg_cancel_left _ _⟩

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor


open Classical in
theorem mem_schwartzA_of_isSchwartzBruhat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  intro D θ hθ m n φ hφ
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, hsc, hsf, hsi⟩ := exists_finSection D
  obtain ⟨U, hUo, hU⟩ := hφ.level
  obtain ⟨K, hK, hKs⟩ := hφ.supp
  let S : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →+ Mx D m n := s.mapMatrix
  have hSc : Continuous S := continuous_id.matrix_map hsc
  have hSi : ∀ a, (S a).map (infPart D) = 0 := fun a => by
    funext i j
    exact hsi (a i j)
  let W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | S a ∈ U ∧ ∀ i j, a i j ∈ intAE D}
      add_mem' := fun {a b} ha hb => ⟨by rw [S.map_add]; exact U.add_mem ha.1 hb.1,
        fun i j => (intAE D).add_mem (ha.2 i j) (hb.2 i j)⟩
      zero_mem' := ⟨by rw [S.map_zero]; exact U.zero_mem, fun _ _ => (intAE D).zero_mem⟩
      neg_mem' := fun {a} ha => ⟨by rw [S.map_neg]; exact U.neg_mem ha.1, fun i j => (intAE D).neg_mem (ha.2 i j)⟩ }
  have hWe : (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      S ⁻¹' U ∩ ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact (hUo.preimage hSc).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i)))
  have hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    AddSubgroup.isClosed_of_isOpen _ hWo
  have hbig : IsCompact {a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) | ∀ i j, a i j ∈ intAE D} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_intAE D
  have hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    hbig.of_isClosed_subset hcl fun a ha => ha.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) := t.image QuotientAddGroup.mk
  let k := Module.finrank ℝ (D.what₂.Tau → Fin m → Fin n → ℂ)
  let eZ : (D.what₂.Tau → Fin m → Fin n → ℂ) ≃L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let L : (Fin k → ℝ) →+ Mx D m n := (chartM σ m n).comp eZ.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L :=
    ⟨(continuous_chartM hσ.cont m n).comp eZ.symm.continuous, fun t => finPart_chartM hσ _⟩
  have hLi : Function.Injective L := by
    intro t t' h
    apply eZ.symm.injective
    funext τ i j
    have e := congrArg (fun y => compAt θ τ y i j) h
    simp only [L, AddMonoidHom.coe_comp, Function.comp_apply] at e
    rw [compAt_chartM hσ, compAt_chartM hσ] at e
    exact e
  choose g hg using fun q : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W =>
    hφ.schwartz k L hL hLi (S q.out)
  let f : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) →
      SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ :=
    fun q => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eZ (g q)
  have hf : ∀ q c, f q c = φ (S q.out + chartM σ m n c) := fun q c => by
    show g q (eZ c) = _
    rw [hg q (eZ c)]
    congr 2
    show chartM σ m n (eZ.symm (eZ c)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  let gf : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) →
      (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun q a =>
    if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = q then (1 : ℂ) else 0
  have key : φ = ∑ q ∈ T, fun x : Mx D m n =>
      f q (fun τ i j => compAt θ τ x i j) * gf q (fun i j => finPart D (x i j)) := by
    funext y
    rw [Finset.sum_apply]
    let a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) := fun i j => finPart D (y i j)
    let c : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ y i j
    have hdec : y = S a + chartM σ m n c := decomp hσ hsf hsi y
    show φ y = ∑ q ∈ T, f q c * (if (QuotientAddGroup.mk a : _ ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hf]
      have hmem : -(QuotientAddGroup.mk a : _ ⧸ W).out + a ∈ W := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
      have e := hU (S (-(QuotientAddGroup.mk a : _ ⧸ W).out + a)) hmem.1 (hSi _)
        (S (QuotientAddGroup.mk a : _ ⧸ W).out + chartM σ m n c)
      rw [← e]
      conv_lhs => rw [hdec]
      congr 1
      rw [S.map_add, S.map_neg]
      abel
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      have hba : (QuotientAddGroup.mk b : _ ⧸ W) = QuotientAddGroup.mk a := QuotientAddGroup.eq.2 hab
      exact hT (Finset.mem_image.2 ⟨b, hb, hba⟩)
  rw [key]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨f q, gf q, coset_mem_SB W hWo hWc q, rfl⟩

end GlobalTheory.SchwartzBruhatTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeStringGivesSimplePoleHypothesesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_string_gives_simple_pole_hypotheses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t s, HasString R i t s → ∃ B c : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B ∧ GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))) D.R.r D.R.t c B (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
  first | exact @GlobalTheory.Core.Rk.StringPole.string_pole_hyp | exact GlobalTheory.Core.Rk.StringPole.string_pole_hyp | (intros; apply GlobalTheory.Core.Rk.StringPole.string_pole_hyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_vector_iff_inverse_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → B.card = n → (IsSatVecGL w ρ x B ↔ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x = satEig (qV E w) n (B.map (·⁻¹)) j • x) := by
  first | exact @GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | exact GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | (intros; apply GlobalTheory.ChainOnto.SatInv.satVec_iff_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernelsStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_fubini_two_lifts_moderate_growth_kernels : ∀ (D : D7) (A B : HSp D) (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ K₁ K₂ : GA D A → GA D B → ℂ, (∀ K ∈ ({K₁, K₂} : Set (GA D A → GA D B → ℂ)), Continuous (Function.uncurry K) ∧ (∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) ∧ (∀ g, MemL2Quotient (GQ B) mH (K g)) ∧ (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) ∧ ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) → ∀ u₁ u₂ : GA D A → ℂ, GlobalTheory.Grow.RapidDec A u₁ → GlobalTheory.Grow.RapidDec A u₂ → let θ₁ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₁ g h * u₁ g) q ∂autMeasure A m; let θ₂ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₂ g h * u₂ g) q ∂autMeasure A m; (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₁ g h * u₁ g) (autMeasure A m)) ∧ (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₂ g h * u₂ g) (autMeasure A m)) ∧ MemL2Quotient (GQ B) mH θ₁ ∧ MemL2Quotient (GQ B) mH θ₂ ∧ petersson B mH θ₁ θ₂ = ∫ q : AutQ A × AutQ A, petersson B mH (K₁ q.1.out) (K₂ q.2.out) * u₁ q.1.out * conj (u₂ q.2.out) ∂(autMeasure A m).prod (autMeasure A m) := by
  first | exact @GlobalTheory.Core.Rk.Seesaw.seesaw_fubini | exact GlobalTheory.Core.Rk.Seesaw.seesaw_fubini | (intros; apply GlobalTheory.Core.Rk.Seesaw.seesaw_fubini <;> assumption)
end

