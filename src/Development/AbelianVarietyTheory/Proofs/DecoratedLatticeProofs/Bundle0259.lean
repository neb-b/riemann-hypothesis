module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjugateWeilDatumHermitianSpaceNeg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilize
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section
namespace GlobalTheory.Core.Rk.IwAd

theorem exists_stab_proj_eq {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r)
    (x : ∀ v : FinPl D, Gv T v) (hx : ∀ v, emb D.sp.cm.sig T.gram v (x v) ∈ stab d)
    (S : Finset (FinPl D)) : ∃ p ∈ stab d,
      (∀ v ∈ S, proj D.sp.cm.sig T.gram v p = x v) ∧ (∀ v ∉ S, proj D.sp.cm.sig T.gram v p = 1) ∧
        ∀ w, projArch D.sp.cm.sig T.gram w p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, hp, h1, h2, h3⟩ := ih
    refine ⟨emb D.sp.cm.sig T.gram u (x u) * p, mul_mem (hx u) hp, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [proj_emb_self, h2 _ hu, mul_one]
      · rw [proj_emb_ne _ _ (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, proj_emb_ne _ _ hv.1, h2 v hv.2, mul_one]
    · rw [map_mul, projArch_emb, h3, mul_one]

theorem hasIw_Kmax : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → IsMaj T b → HasIw d (Kmax T b) := by
  intro D T T₀ r d b h2 hb h
  choose x k hx hk hxk using fun v => GlobalTheory.T.iwasawa_isotropic_stabiliser_finite_place D T T₀ r d h2 v (proj D.sp.cm.sig T.gram v h)
  have hS := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig T.gram (frameLat T) h)
  obtain ⟨p, hp, e1, e2, e3⟩ := exists_stab_proj_eq d x hx hS.toFinset
  set h' := p⁻¹ * h with hh'
  have hfin : ∀ v, proj D.sp.cm.sig T.gram v h' ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v := fun v => by
    by_cases hv : v ∈ hS.toFinset
    · rw [hh', map_mul, map_inv, e1 v hv, hxk v, inv_mul_cancel_left]
      exact hk v
    · rw [hh', map_mul, map_inv, e2 v hv, inv_one, one_mul]
      exact not_not.1 fun h => hv (hS.mem_toFinset.2 h)
  set y := ofInf D.sp.cm.sig T.gram (projInf D.sp.cm.sig T.gram h') with hy
  have hyC : y ∈ GinfC T := mem_infPts.2 (projFin_ofInf _ _ _)
  obtain ⟨q, hq, k₁, hk₁, -, hyq⟩ := _root_.GlobalTheory.Core.Rk.IwIso.iwasawa_stab_arch D T T₀ r d b hb y hyC
  have hz : y⁻¹ * h' ∈ Kmax T b := by
    refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [map_mul, map_inv, hy, proj_ofInf, inv_one, one_mul]
      exact hfin v
    · have : projArch D.sp.cm.sig T.gram w (y⁻¹ * h') = 1 := by
        rw [map_mul, map_inv, hy, projArch_ofInf, projInfArch_projInf, inv_mul_cancel]
      rw [this]
      exact one_mem _
  refine ⟨⟨p * q, mul_mem hp hq⟩, k₁ * (y⁻¹ * h'), mul_mem hk₁ hz, ?_⟩
  rw [Subgroup.coe_mk, hyq, hh']
  group

end GlobalTheory.Core.Rk.IwAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaPreservesSupportedMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LinkKapMx

theorem mxAt_linkKappa : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (w : WO S L'), MxAt P w → MxAt P (l.κ S w) := by
  intro D ρ B L' ζ' l S P w hw
  exact GlobalTheory.LastOpPf.mxAt_kap _ S hw

end GlobalTheory.LinkKapMx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaSurjectiveSupportedConjugateHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinkKapInv

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

theorem isHalf_mul_l {e : AE D} {l m n : ℕ} (A : Mx D l m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (A * x) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hx k j]

theorem isHalf_mul_r {e : AE D} {l m n : ℕ} {x : Mx D l m} (hx : IsHalf e x) (A : Mx D m n) : IsHalf e (x * A) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hx i k]

theorem isHalf_smul {e : AE D} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_adj {e : AE D} {m n : ℕ} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) :=
  fun i j => by
    show cA D e * cA D (x j i) = cA D (x j i)
    rw [← map_mul, hx j i]

def tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (_l : Link B L' ζ') :
    Matrix (Fin L'.rank) (Fin B.L.rank) D.host.E := fun i j => -(B.ζ j)⁻¹ * ζ' i

theorem mul_tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') :
    l.τ * tauPlus l = 1 := by
  obtain ⟨hr, hq⟩ := B.line
  have hsub : ∀ a b : Fin B.L.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  have hne : ∀ a, B.ζ a ≠ 0 := by
    intro a ha
    apply hq
    have h0 : B.ζ = 0 := funext fun b => by rw [hsub b a]; exact ha
    rw [h0]; simp
  funext a b
  rw [hsub b a, Matrix.one_apply_eq, Matrix.mul_apply]
  have hm := congrFun l.map a
  rw [Pi.neg_apply, Matrix.mulVec, dotProduct] at hm
  simp only [tauPlus]
  calc ∑ k, l.τ a k * (-(B.ζ a)⁻¹ * ζ' k) = -(B.ζ a)⁻¹ * ∑ k, l.τ a k * ζ' k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = 1 := by rw [hm, neg_mul_neg, inv_mul_cancel₀ (hne a)]

theorem kappa_inv : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ')
    (S : HSp D) (P : Pl D → Prop) (h : WO B.L S), ∃ x : WO S L', l.κ S x = h ∧ (MxAt P h → MxAt P x) ∧
      ∀ e : AE D, IsHalf e h → IsHalf (cA D e) x := by
  intro D ρ B L' ζ' l S P h
  refine ⟨(rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h, ?_, fun hh => ?_, fun e he => ?_⟩
  · show ofAdj B.L S ((rat l.τ : Mx D B.L.rank L'.rank) * ((rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h)) = h
    rw [← Matrix.mul_assoc, ← rat_mul, mul_tauPlus l, rat_one, Matrix.one_mul, GlobalTheory.LastOpPf.ofAdj_starAdj]
  · exact GlobalTheory.LastOpPf.mxAt_mul_l _ (GlobalTheory.LastOpPf.mxAt_smul _ (GlobalTheory.LastOpPf.mxAt_mul_l _
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LastOpPf.mxAt_adj hh) _)))
  · exact isHalf_mul_l _ (isHalf_smul _ (isHalf_mul_l _ (isHalf_mul_r (isHalf_adj he) _)))

end GlobalTheory.LinkKapInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionRepresentativeMemPreviousIndexSetStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_representative_mem_previous_index_set : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0 := by
  first | exact @GlobalTheory.RepsAtTwist.exists_rep_flat_ne | exact GlobalTheory.RepsAtTwist.exists_rep_flat_ne | (intros; apply GlobalTheory.RepsAtTwist.exists_rep_flat_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionRepresentativesNormalFormModUnipotentStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_representatives_normal_form_mod_unipotent : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → (∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0) → ∀ j c (h : j + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1)) k), IsGL ι (L.h j al P) g → ∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j c h (r * g) := by
  first | exact @GlobalTheory.TwNormalReps.exists_normal_rep | exact GlobalTheory.TwNormalReps.exists_normal_rep | (intros; apply GlobalTheory.TwNormalReps.exists_normal_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIteratedWeilActionBiTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiActCont

variable {D : D7} {X Y A S A' : HSp D} (d : OrthDec X S A) (e : OrthDec Y S A')

def four (C : WO A S → WO S A' → ℂ) (φ₁ : WO A A' → ℂ) (φ₂ : WO S S → ℂ) : WO X Y → ℂ := fun x =>
  C (sandwich e.pA d.jB x) (sandwich e.pB d.jA x) * (φ₁ (sandwich e.pB d.jB x) * φ₂ (sandwich e.pA d.jA x))

theorem four_eq (C : WO A S → WO S A' → ℂ) (φ₁ : WO A A' → ℂ) (φ₂ : WO S S → ℂ) (x : WO X Y) :
    four d e C φ₁ φ₂ x = C (e.resT A (d.resS Y x).2).1 (e.resT S (d.resS Y x).1).2 *
      (φ₁ (e.resT A (d.resS Y x).2).2 * φ₂ (e.resT S (d.resS Y x).1).1) := by
  simp only [four, sandwich_apply, OrthDec.resT_apply, OrthDec.resS_apply, Matrix.mul_assoc]

theorem four_symm (C : WO A S → WO S A' → ℂ) (φ₁ : WO A A' → ℂ) (φ₂ : WO S S → ℂ) (s₁ : WO S S) (s₂ : WO S A')
    (u₁ : WO A S) (u₂ : WO A A') :
    four d e C φ₁ φ₂ ((d.resS Y).symm ((e.resT S).symm (s₁, s₂), (e.resT A).symm (u₁, u₂))) =
      C u₁ s₂ * (φ₁ u₂ * φ₂ s₁) := by
  simp only [four_eq, AddEquiv.apply_symm_apply]

theorem symplOH_four (x y : WO X Y) : symplOH X Y x y =
    symplOH A S (sandwich e.pA d.jB x) (sandwich e.pA d.jB y) + symplOH S A' (sandwich e.pB d.jA x) (sandwich e.pB d.jA y) +
    (symplOH A A' (sandwich e.pB d.jB x) (sandwich e.pB d.jB y) +
      symplOH S S (sandwich e.pA d.jA x) (sandwich e.pA d.jA y)) := by
  rw [d.symplOH_resS, e.symplOH_resT, e.symplOH_resT]
  simp only [sandwich_apply, OrthDec.resT_apply, OrthDec.resS_apply, Matrix.mul_assoc]
  ring

variable {ψ : AddChar (AF D.host.F) ℂ} {C : WO A S → WO S A' → ℂ} {φ₁ : WO A A' → ℂ} {φ₂ : WO S S → ℂ}

theorem isThetaFunO_four (h : IsBiTheta ψ A S A' C) (h₁ : IsThetaFunO ψ A A' φ₁) (h₂ : IsThetaFunO ψ S S φ₂) :
    IsThetaFunO ψ X Y (four d e C φ₁ φ₂) := {
  quasi γ w := by
    have e₁ : sandwich e.pA d.jB (ratW Y X γ) = ratW S A (e.qA * γ * d.iB) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₂ : sandwich e.pB d.jA (ratW Y X γ) = ratW A' S (e.qB * γ * d.iA) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₃ : sandwich e.pB d.jB (ratW Y X γ) = ratW A' A (e.qB * γ * d.iB) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₄ : sandwich e.pA d.jA (ratW Y X γ) = ratW S S (e.qA * γ * d.iA) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    rw [symplOH_four d e]
    simp only [four, map_add (f := _)]
    rw [e₁, e₂, e₃, e₄, h.quasiL, h.quasiR, h₁.quasi, h₂.quasi]
    simp only [neg_add, AddChar.map_add_eq_mul]
    ring
  level := by
    obtain ⟨U₁, hU₁, k₁⟩ := h.levL
    obtain ⟨U₂, hU₂, k₂⟩ := h.levR
    obtain ⟨U₃, hU₃, k₃⟩ := h₁.level
    obtain ⟨U₄, hU₄, k₄⟩ := h₂.level
    refine ⟨(U₁.comap (sandwich e.pA d.jB) ⊓ U₂.comap (sandwich e.pB d.jA)) ⊓
      (U₃.comap (sandwich e.pB d.jB) ⊓ U₄.comap (sandwich e.pA d.jA)),
      ((hU₁.preimage (continuous_sandwich _ _)).inter (hU₂.preimage (continuous_sandwich _ _))).inter
      ((hU₃.preimage (continuous_sandwich _ _)).inter (hU₄.preimage (continuous_sandwich _ _))), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1.1 (map_sandwich _ _ _ h0) (sandwich e.pB d.jA w + sandwich e.pB d.jA u))
      (sandwich e.pA d.jB w)
    have e₂ := congrFun (k₂ _ hu.1.2 (map_sandwich _ _ _ h0) (sandwich e.pA d.jB w)) (sandwich e.pB d.jA w)
    have e₃ := congrFun (k₃ _ hu.2.1 (map_sandwich _ _ _ h0)) (sandwich e.pB d.jB w)
    have e₄ := congrFun (k₄ _ hu.2.2 (map_sandwich _ _ _ h0)) (sandwich e.pA d.jA w)
    simp only [heisO] at e₁ e₂ e₃ e₄ ⊢
    rw [symplOH_four d e]
    simp only [four, map_add (f := _), AddChar.map_add_eq_mul]
    rw [← e₂, ← e₁, ← e₃, ← e₄]
    ring
  cont := (h.cont.comp ((continuous_sandwich _ _).prodMk (continuous_sandwich _ _))).mul
    ((h₁.cont.comp (continuous_sandwich _ _)).mul (h₂.cont.comp (continuous_sandwich _ _)))
  smooth k L hL h0 w := by
    simp only [four, map_add (f := _)]
    exact (h.smooth k ((sandwich e.pA d.jB).comp L) ((sandwich e.pB d.jA).comp L) ((continuous_sandwich _ _).comp hL)
      ((continuous_sandwich _ _).comp hL) (fun t => map_sandwich _ _ _ (h0 t)) (fun t => map_sandwich _ _ _ (h0 t)) _ _).mul
      ((h₁.smooth k ((sandwich e.pB d.jB).comp L) ((continuous_sandwich _ _).comp hL)
        (fun t => map_sandwich _ _ _ (h0 t)) _).mul
      (h₂.smooth k ((sandwich e.pA d.jA).comp L) ((continuous_sandwich _ _).comp hL)
        (fun t => map_sandwich _ _ _ (h0 t)) _)) }

theorem end_const_mul {Z : Type} (L : Module.End ℂ (Z → ℂ)) (c : ℂ) (f : Z → ℂ) (z : Z) :
    L (fun y => c * f y) z = c * L f z :=
  congrFun (L.map_smul c f) z

theorem om_four {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'} {Ω : Om X Y} {ΩS : Om S Y}
    {ΩA : Om A Y} {ω₁ : Om A A'} {ω₂ : Om S S} (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb)
    (hΩ : IsWeilDatumO ψ X Y (χS' * χA) (χS * χA') Ω) (hS : IsWeilDatumO ψ S Y χS' (χS * χA') ΩS)
    (hA : IsWeilDatumO ψ A Y χA (χS * χA') ΩA) (hω₁ : IsWeilDatumO ψ A A' χA χA' ω₁) (hω₂ : IsWeilDatumO ψ S S χS' χS ω₂)
    (hΦ : IsThetaFunO ψ X Y (four d e C φ₁ φ₂)) (a : GA D A) (h h' : GA D S) (b : GA D A') (w : WO A S) (w' : WO S A') :
    Ω (d.emb (h', a), e.emb (h, b)) (four d e C φ₁ φ₂)
        ((d.resS Y).symm ((e.resT S).symm (0, w'), (e.resT A).symm (w, 0))) =
      (ω₁ (a, b) φ₁ 0 * ω₂ (h', h) φ₂ 0) * omb (h', b) (fun v => oma (a, h) (fun u => C u v) w) w' := by
  have hψ := ha.std
  have tS := _root_.GlobalTheory.TensorSrc.tensorSource D ψ hψ X S A d Y
  have tA := _root_.GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ Y S A' e A
  have tB := _root_.GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ Y S A' e S
  obtain ⟨th, ev⟩ := tS.om_slice χS' χA (χS * χA') Ω ΩS ΩA hΩ hS hA h' a (e.emb (h, b)) _ hΦ ((e.resT A).symm (w, 0))
  have inner : ∀ s₁ s₂, ΩA (a, e.emb (h, b))
      (fun v' => four d e C φ₁ φ₂ ((d.resS Y).symm ((e.resT S).symm (s₁, s₂), v'))) ((e.resT A).symm (w, 0)) =
      (ω₁ (a, b) φ₁ 0 * φ₂ s₁) * oma (a, h) (fun u => C u s₂) w := by
    intro s₁ s₂
    rw [(tA.om_slice χA χS χA' ΩA oma ω₁ hA ha hω₁ a h b _ ((tS.slice_theta _ hΦ).2 _) 0).2 w, ← end_const_mul]
    refine congrArg (fun f => oma (a, h) f w) (funext fun u => ?_)
    have : (fun v' => four d e C φ₁ φ₂ ((d.resS Y).symm ((e.resT S).symm (s₁, s₂), (e.resT A).symm (u, v')))) =
        fun v' => (C u s₂ * φ₂ s₁) * φ₁ v' := by
      funext v'; rw [four_symm]; ring
    rw [this, end_const_mul]; ring
  rw [ev, (tB.om_slice χS' χS χA' ΩS ω₂ omb hS hω₂ hb h' h b _ th w').2 0]
  simp only [inner, end_const_mul]
  have : (fun s₁ => ω₁ (a, b) φ₁ 0 * φ₂ s₁ * omb (h', b) (fun v => oma (a, h) (fun u => C u v) w) w') =
      fun s₁ => (ω₁ (a, b) φ₁ 0 * omb (h', b) (fun v => oma (a, h) (fun u => C u v) w) w') * φ₂ s₁ := by
    funext s₁; ring
  rw [this, end_const_mul]; ring

theorem exists_kernel_ne_zero {V W : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χ χ' om)
    (p : GA D V × GA D W) : ∃ f, IsThetaFunO ψ V W f ∧ om p f 0 ≠ 0 := by
  obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero h.std V W
  obtain ⟨w, hw⟩ := Function.ne_iff.1 f0
  refine ⟨om p⁻¹ (heisO ψ V W w f), h.om_pres _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all h.std hf w), ?_⟩
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, heisO, zero_add,
    symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]
  exact hw

theorem hecke_mul {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') : IsHeckeChar D (χ * χ') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2, h'.2, mul_one]⟩

theorem continuous_biAct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C → Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' => omb x.2.1 (fun v => oma x.1 (fun u => C u v) x.2.2.1) x.2.2.2 := by
  intro D ψ A S A' χA χS χS' χA' oma omb ha hb C hC
  have hψ := ha.std
  have ex := _root_.GlobalTheory.WeilDatumExistence.weilDatumExists D
  obtain ⟨X, ⟨d⟩⟩ : ∃ X, Nonempty (OrthDec X S A) := ⟨_, ⟨GlobalTheory.BiTransfer.sumDec S A⟩⟩
  obtain ⟨Y, ⟨e⟩⟩ : ∃ Y, Nonempty (OrthDec Y S A') := ⟨_, ⟨GlobalTheory.BiTransfer.sumDec S A'⟩⟩
  have hY := hecke_mul ha.hecT hb.hecT
  have rY : ResEta D (χS * χA') Y.rank := e.rank_add ▸ resEta_mul ha.resT hb.resT
  have rX : ResEta D (χS' * χA) X.rank := d.rank_add ▸ resEta_mul hb.resS ha.resS
  obtain ⟨Ω, hΩ⟩ := ex X Y ψ _ _ hψ (hecke_mul hb.hecS ha.hecS) hY rX rY
  obtain ⟨ΩS, hS⟩ := ex S Y ψ _ _ hψ hb.hecS hY hb.resS rY
  obtain ⟨ΩA, hA⟩ := ex A Y ψ _ _ hψ ha.hecS hY ha.resS rY
  obtain ⟨ω₁, hω₁⟩ := ex A A' ψ _ _ hψ ha.hecS hb.hecT ha.resS hb.resT
  obtain ⟨ω₂, hω₂⟩ := ex S S ψ _ _ hψ hb.hecS ha.hecT hb.resS ha.resT
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨φ₁, h₁, n₁⟩ := exists_kernel_ne_zero hω₁ (x₀.1.1, x₀.2.1.2)
  obtain ⟨φ₂, h₂, n₂⟩ := exists_kernel_ne_zero hω₂ (x₀.2.1.1, x₀.1.2)
  have hΦ := isThetaFunO_four d e hC h₁ h₂
  have cK : Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
      ω₁ (x.1.1, x.2.1.2) φ₁ 0 * ω₂ (x.2.1.1, x.1.2) φ₂ 0 :=
    ((hω₁.om_cont _ h₁ 0).comp (continuous_fst.fst.prodMk continuous_snd.fst.snd)).mul
      ((hω₂.om_cont _ h₂ 0).comp (continuous_snd.fst.fst.prodMk continuous_fst.snd))
  have cG : Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
      ((d.emb (x.2.1.1, x.1.1), e.emb (x.1.2, x.2.1.2)),
        (d.resS Y).symm ((e.resT S).symm (0, x.2.2.2), (e.resT A).symm (x.2.2.1, 0))) :=
    ((d.continuous_emb.comp (continuous_snd.fst.fst.prodMk continuous_fst.fst)).prodMk
      (e.continuous_emb.comp (continuous_fst.snd.prodMk continuous_snd.fst.snd))).prodMk
      ((d.continuous_resS_symm Y).comp
        (((e.continuous_resT_symm S).comp (continuous_const.prodMk continuous_snd.snd.snd)).prodMk
          ((e.continuous_resT_symm A).comp (continuous_snd.snd.fst.prodMk continuous_const))))
  have cN := (GlobalTheory.Unf.jointCont_all D ψ X Y _ _ Ω hΩ _ hΦ).comp cG
  have nK := mul_ne_zero n₁ n₂
  refine (cN.continuousAt.div cK.continuousAt nK).congr ?_
  filter_upwards [cK.continuousAt.eventually_ne nK] with x hx
  rw [Pi.div_apply, div_eq_iff hx, mul_comm]
  exact om_four d e ha hb hΩ hS hA hω₁ hω₂ hΦ _ _ _ _ _ _

end GlobalTheory.BiActCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapSpanDenseHeisenbergStable
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.DoubleSpan

variable {D : D7}

theorem span_delta_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A W : HSp D) :
    (Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂} :
      Submodule ℂ (WO (dblSp A) W → ℂ)) =
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan ((GlobalTheory.DoublingTheta.sumDec A (negSp A)).resS W) (IsThetaFunO ψ A W)
      (IsThetaFunO ψ (negSp A) W) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro φ ⟨f₁, f₂, h₁, h₂, rfl⟩
    refine Submodule.subset_span ⟨f₁, fun x => starRingEnd ℂ (f₂ (-x)), h₁,
      GlobalTheory.CjNeg.theta_negS hψ (GlobalTheory.NegWeil.theta_refl h₂), ?_⟩
    funext x
    exact (GlobalTheory.DoublingTheta.boxS_apply A W f₁ (fun x => starRingEnd ℂ (f₂ (-x))) x).symm
  · refine Submodule.span_le.2 ?_
    rintro φ ⟨g₁, g₂, h₁, h₂, rfl⟩
    refine Submodule.subset_span ⟨g₁, fun x => starRingEnd ℂ (g₂ (-x)), h₁,
      GlobalTheory.NegWeil.theta_refl (GlobalTheory.CjNeg.theta_negS' hψ h₂), ?_⟩
    funext x
    refine ((GlobalTheory.DoublingTheta.boxS_apply A W g₁ g₂ x).trans ?_)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, neg_neg, Complex.conj_conj]

theorem prodSpan_theta_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S A B : HSp D}
    (o : GlobalTheory.MixModel.OrthDec S A B) (W : HSp D) :
    (∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W), IsThetaFunO ψ S W g) ∧
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W), ∀ w,
      heisO ψ S W w g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W) := by
  refine ⟨fun g hg => ?_, fun g hg w => ?_⟩
  · induction hg using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hA, hB, rfl⟩ := hf
      exact o.isThetaFunO_boxS hA hB
    | zero => exact Formalism.IndefR.Fock.CCR.theta_zero ψ S W
    | add a b _ _ ha hb => exact Formalism.IndefR.Fock.CCR.theta_add ha hb
    | smul c a _ ha => exact Formalism.IndefR.Fock.CCR.theta_smul ha c
  · induction hg using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hA, hB, rfl⟩ := hf
      refine Submodule.subset_span ⟨_, _, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hA (o.resS W w).1,
        GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hB (o.resS W w).2, ?_⟩
      exact o.heisO_boxS ψ W fA fB w
    | zero =>
      have : heisO ψ S W w 0 = 0 := by funext x; simp [heisO]
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : heisO ψ S W w (a + b) = heisO ψ S W w a + heisO ψ S W w b := by
        funext x; simp only [heisO, Pi.add_apply]; ring
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : heisO ψ S W w (c • a) = c • heisO ψ S W w a := by
        funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact Submodule.smul_mem _ c ha

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A W : HSp D), IsStdChar D ψ (-1) → let M : Submodule ℂ (WO (dblSp A) W → ℂ) := Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂}; (∀ g ∈ M, IsThetaFunO ψ (dblSp A) W g) ∧ (∀ g ∈ M, ∀ w, heisO ψ (dblSp A) W w g ∈ M) ∧ ∀ f, IsThetaFunO ψ (dblSp A) W f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f := by
  intro D ψ A W hψ M
  have hM : M = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan ((GlobalTheory.DoublingTheta.sumDec A (negSp A)).resS W) (IsThetaFunO ψ A W)
      (IsThetaFunO ψ (negSp A) W) := span_delta_eq hψ A W
  obtain ⟨h1, h2⟩ := prodSpan_theta_heis hψ (GlobalTheory.DoublingTheta.sumDec A (negSp A)) W
  rw [hM]
  exact ⟨h1, h2, fun f hf =>
    GlobalTheory.DenseSum.unifLimit_prodSpan D ψ hψ _ A (negSp A) W (GlobalTheory.DoublingTheta.sumDec A (negSp A)) f hf⟩

end GlobalTheory.Core.Rk.DoubleSpan
end
end

