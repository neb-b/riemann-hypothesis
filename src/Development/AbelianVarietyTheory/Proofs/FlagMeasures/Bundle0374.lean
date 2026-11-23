module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpan
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0373

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
section
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev GlobalTheory.SmVec NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepSmooth

variable {D : D7} {θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {Φ : MMap M}

def IsEquiv (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (Φ : MMap M) : Prop :=
  ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (u : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ a (u τ) → Φ (Function.update u τ w) = rTr V (atTau θ V τ a) (Φ u)

def IsSob (Φ : MMap M) : Prop :=
  ∀ τ (u : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = Φ (Function.update u τ w) x

def der (u : M.Vec) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : M.sm τ :=
  ⟨dRep (trRep (M.σ τ) (M.fr τ)) X (u τ), (MultGelf.mem_sm M τ).2
    (dRep_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (MultGelf.isURep M τ) ((MultGelf.mem_sm M τ).1 (u τ).2) hX)⟩

theorem hasDerivAt_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (x : GA D V) :
    HasDerivAt (fun t : ℝ => Φ u (x * oneP θ V τ X t)) (Φ (Function.update u τ (der u τ hX)) x) 0 := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  obtain ⟨ℓ, hℓ, hℓT⟩ := hs τ u x
  obtain ⟨m, ls, a, hls, ha⟩ := _root_.GlobalTheory.SmVec.sobCont_repr _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (MultGelf.mem_sm M τ).1 (u τ).2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) (u τ) ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (MultGelf.isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => Φ u (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i)
        (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) (u τ))⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := he τ _ (exp_mem_UH hG hX t) u ⟨_, (MultGelf.mem_sm M τ).2 (hmem t)⟩ rfl
    have h3 := hℓT ⟨_, (MultGelf.mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  rw [h1, ← hℓT, show ((der u τ hX : M.sm τ) : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X (u τ) from rfl,
    ha _ (dRep_mem hG (MultGelf.isURep M τ) hu hX)]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
    (_root_.GlobalTheory.SmVecDeriv.hasDerivAt_word _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
  simpa using h5

theorem rder_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X (Φ u) = Φ (Function.update u τ (der u τ hX)) :=
  funext fun x => (hasDerivAt_apply he hs τ u hX x).deriv

theorem rderC_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (Φ (Function.update v τ u)) = Φ (Function.update v τ w) := by
  have hp := parts_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ)) Z
  have h1 := rder_apply he hs τ (Function.update v τ u) hp.1
  have h2 := rder_apply he hs τ (Function.update v τ u) hp.2
  rw [Function.update_idem] at h1 h2
  have h3 : w = der (Function.update v τ u) τ hp.1 + Complex.I • der (Function.update v τ u) τ hp.2 :=
    Subtype.ext (by rw [hw]; simp only [der, Function.update_self]; rfl)
  rw [h3, Φ.map_update_add, Φ.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (Φ (Function.update v τ u)) =
        Φ (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (MultGelf.mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (MultGelf.isURep M τ) Z ((MultGelf.mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply he hs τ v Z w _ rfl

theorem gelf_scalar (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (k : ℕ) :
    ∃ c : ℂ, ∀ v : M.Vec, gelf θ V τ k (Φ v) = c • Φ v := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨c, hc⟩ := GlobalTheory.SmVec.GelfScalar.gelfH_scalar _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    (M.ds τ).2.2.2.1 k
  refine ⟨c, fun v => ?_⟩
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply he hs τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : c • v τ = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, ← hc _ ((MultGelf.mem_sm M τ).1 (v τ).2), Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  have h2 : c • Φ v = Φ (Function.update v τ (c • v τ)) := by
    rw [Φ.map_update_smul, RingHom.id_apply, Function.update_eq_self]
  rw [h2, h1]
  refine Eq.trans ?_ (map_sum (Φ.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

theorem zfin (he : IsEquiv θ Φ) (hs : IsSob Φ) (u : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ Φ u ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨Submodule.span ℂ {Φ u}, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := gelf_scalar he hs τ k
  have h2 : a • Φ u = Φ (Function.update u τ (a • u τ)) := by
    rw [Φ.map_update_smul, RingHom.id_apply, Function.update_eq_self]
  rw [h2, hc, ← h2]
  exact Submodule.smul_mem _ _ hf

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem smooth (hθ : IsInfFam θ) (he : IsEquiv θ Φ) (hs : IsSob Φ) (hc : ∀ u, Continuous (Φ u)) (u : M.Vec)
    (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : ∀ i, Xs i ∈ lieAt V (τs i)) (g : GA D V) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => Φ u (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  refine GlobalTheory.T.derivative_along_lie_algebra_preserves_smooth_space D θ V hθ (Set.range Φ) ?_ _ ⟨u, rfl⟩ k τs Xs hX g
  rintro _ ⟨v, rfl⟩
  refine ⟨hc v, fun τ => ⟨fun X => Rder θ V τ X (Φ v), fun X hX => ?_, fun a X hX Y hY => ?_⟩⟩
  · simp only [rder_apply he hs τ v hX]
    exact ⟨⟨_, rfl⟩, hasDerivAt_apply he hs τ v hX⟩
  · haveI : CompleteSpace (M.H τ) := (M.ds τ).1
    obtain ⟨h1, h2⟩ := GlobalTheory.SmVecLinear.dRep_linear _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 _
      ((MultGelf.mem_sm M τ).1 (v τ).2)
    have haX : a • X ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).smul_mem' a hX
    have hXY : a • X + Y ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).add_mem' haX hY
    have h3 : der v τ hXY = (a : ℂ) • der v τ hX + der v τ hY :=
      Subtype.ext ((h1 _ haX _ hY).trans (by rw [h2 a X hX]; rfl))
    simp only [rder_apply he hs τ v hX, rder_apply he hs τ v hY, rder_apply he hs τ v hXY]
    rw [h3, Φ.map_update_add, Φ.map_update_smul, RingHom.id_apply]

theorem foldr_rder (he : IsEquiv θ Φ) (hs : IsSob Φ) (u : M.Vec)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    ∃ v, l.foldr (fun p f => Rder θ V p.1 p.2 f) (Φ u) = Φ v := by
  induction l with
  | nil => exact ⟨u, rfl⟩
  | cons p l ih =>
    obtain ⟨v, hv⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    exact ⟨_, by rw [List.foldr_cons, hv, rder_apply he hs p.1 v (hl p List.mem_cons_self)]⟩

section Inst

@[reducible] def bundle (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (H : InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] (hC : ∀ v, CompleteSpace (H v))
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (Hs : Type)
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) (hF : I.IsFundDom (I.muA μf) fund) (hR : I.IsRightReg μf fund R)
    (hH : I.IsHilbTensor σ σs tens) (g : ℕ) : RowsAut where
  I := I
  μf := μf
  fund := fund
  fund_spec := hF
  lam := fun _ _ => 0
  H := H
  hC := hC
  σ := σ
  w := fun _ => 0
  Hs := Hs
  σs := σs
  tens := tens
  tens_spec := hH
  R := R
  R_spec := hR
  g := g
  g₀ := 0
  e := fun _ => 0
  e_adm := ⟨IsLocallyConstant.const _, by funext x; simp [AutInst.convF], fun _ => by simp,
    fun _ _ _ => by simp, fun _ h => absurd rfl h, fun _ _ _ _ _ => rfl, fun _ h => absurd rfl h⟩
  Re := 0
  Re_spec := ⟨integrable_zero _ _ _, fun _ _ => by simp⟩

theorem isContRep_of_ae (B : RowsAut) {y : B.I.L2 B.μf B.fund} {f : B.I.GA → ℂ} (hc : Continuous f)
    (hl : ∀ γ ∈ B.I.GFset, ∀ x, f (γ * x) = f x) (h : ∀ᵐ x ∂(B.I.muA B.μf), f x = B.I.ext y x) :
    GlobalTheory.Dec.IsContRep B y f := by
  refine ⟨hc, hl, ?_⟩
  have h1 := B.R_spec 1 y
  rw [(GlobalTheory.RightRegFund.rightReg_unitary_continuous B).1] at h1
  filter_upwards [h1, ae_restrict_of_ae (s := B.fund) h] with x a b
  rw [b]
  simpa using a

theorem eq_of_ae (B : RowsAut) {f f' : B.I.GA → ℂ} (hc : Continuous f) (hc' : Continuous f')
    (h : f =ᵐ[B.I.muA B.μf] f') : f = f' := by
  obtain ⟨-, -, -, -, hop⟩ := _root_.GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf
  have : (B.I.muA B.μf).IsOpenPosMeasure := ⟨fun U hU hne => (hop U hU hne).ne'⟩
  exact (Continuous.ae_eq_iff_eq (B.I.muA B.μf) hc hc').1 h

theorem eq_onePar (B : RowsAut) (w : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε w)) (t : ℝ) {h : B.I.GA}
    (h2 : h.2 = 1) (hw : uMat (h.1 w) = NormedSpace.exp (t • E.1)) (hv : ∀ v, v ≠ w → uMat (h.1 v) = 1) :
    h = GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B w E) t := by
  refine Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) h2
  change uMat (h.1 v) = NormedSpace.exp (t • (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B w E v).1)
  by_cases c : v = w
  · subst c
    rw [hw, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace, Pi.single_eq_same]
  · rw [hv v c, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace, Pi.single_eq_of_ne c]
    simp

theorem hasDerivAt_switch (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) {G : Type} [Group G] (T : GA D V ≃* G) (c : ℝ → G)
    (hc : ∀ t, T (oneP θ V τ Y t) = c t) (y : G) :
    HasDerivAt (fun t : ℝ => Φ u (T.symm (y * c t))) (Φ (Function.update u τ (der u τ hY)) (T.symm y)) 0 := by
  simp only [← hc, map_mul, T.symm_apply_apply]
  exact hasDerivAt_apply he hs τ u hY (T.symm y)

end Inst

end GlobalTheory.RepSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeffChosenRedEqRedHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem coeff_goodAt_eq (D : D7) (X : HidaSetting D) (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ b, a * b = b * a)
    (x : X.B.I.Gf) (γ γ' : G0g D.nd) (h : GoodAt X x γ) (h' : GoodAt X x γ') : a.coeff γ' = a.coeff γ := by
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      γ' kv = P⁻¹ * γ kv * P := by
    intro kv
    exact Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2))
      (D.host.g kv.1) (D.host.g_prime kv.1)
      (by rw [Formalism.L2.SG.Pf.RowDictPf.card_wB, Formalism.L2.SG.Pf.RowDictPf.card_res_host]) D.R.r X.n_eq.symm x (γ kv) (γ' kv)
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h kv))
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h' kv))
  choose P hP using hP
  have e : γ' = (P : G0g D.nd)⁻¹ * γ * P := funext fun kv => hP kv
  rw [e]
  exact Formalism.L2.SG.Pf.RowDictPf.coeff_conj_of_central ha γ P

theorem coeff_chosenRed_eq_redHom : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd), IsRedHom X red →
    ∀ a : MonoidAlgebra ℂ (G0g D.nd), (∀ b, a * b = b * a) → ∀ x : X.B.I.Gf,
    (if h : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ then
      a.coeff (Classical.choose h.2) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0) =
    if x ∈ X.B.I.Kset then a.coeff (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 := by
  intro D X red hred a ha x
  by_cases hx : x ∈ X.B.I.Kset
  · have hc : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ := ⟨hx, red x, hred.1 x hx⟩
    rw [dite_eq_left hc, if_pos hx,
      coeff_goodAt_eq D X a ha x (red x) (Classical.choose hc.2) (hred.1 x hx) (Classical.choose_spec hc.2)]
  · rw [dite_eq_right (fun h => hx h.1), if_neg hx]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalLatticeOverLocalInnerData
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.GlueOver

theorem exists_locOver : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : Dat Z FP), (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ Λ : LV D, LocOver Λ d0 := by
  intro D Z FP d0 hT hΛ
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hΛ
  have hc : ∀ p, ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ ∧
      ((∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀) →
        τ.abelian₂ = lattice₂ D Z.M p Λ₀) := by
    intro p
    by_cases h : ∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀
    · obtain ⟨τ', h1, h2⟩ := h
      exact ⟨τ', h1, fun _ => h2⟩
    · obtain ⟨τ', h1⟩ := hT p
      exact ⟨τ', h1, fun h' => absurd h' h⟩
  choose τ hτ hτ' using hc
  haveI : Infinite (PlF D) := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.F
  obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset hfin.toFinset
  have hp' : ∃ t, LocNG.IsTermOver (FP p) (d0 p) t ∧ t.abelian₂ = lattice₂ D Z.M p Λ₀ := by
    by_contra h
    exact hp (hfin.mem_toFinset.mpr h)
  obtain ⟨t, ht, heq⟩ := hp'
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ₀ : Set (Vp D p)) = ⊤ := by
    rw [← heq]
    exact (_root_.GlobalTheory.GenMass.Fibre.termLat D Z FP p (d0 p) t ht).2
  have hfull : Submodule.IsFullLattice D.host.E Λ₀ := by
    let U := Submodule.span D.host.E (Λ₀ : Set (VS D).V)
    let b := Module.finBasis D.host.E U
    let W := Submodule.span (D.s.atP p).Ep
      (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
    have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
      have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
      change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
      rw [map_sum, map_sum] at hx
      rw [← hx]
      exact W.sum_mem fun i _ => by
        rw [map_smul, baseChange_smul₂]
        exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    have htop : W = ⊤ := by
      apply top_le_iff.mp
      rw [← hspan, lattice₂, Submodule.span_span_of_tower]
      refine Submodule.span_le.2 ?_
      rintro y ⟨x, hx, heq⟩
      rw [← heq]
      exact hW ⟨x, Submodule.subset_span hx⟩
    refine { toIsLattice := hΛ₀, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
    rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
    simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
      finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
  obtain ⟨Λ, hΛ, heq⟩ := (GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).2 Λ₀ hfull (fun p => (τ p).abelian₂)
    (fun p => _root_.GlobalTheory.GenMass.Fibre.termLat D Z FP p (d0 p) (τ p) (hτ p))
    (hfin.subset (fun p hp h => hp (hτ' p h)))
  exact ⟨Λ, hΛ, fun p => ⟨τ p, hτ p, (heq p).symm⟩⟩

end GlobalTheory.Unfold.GlueOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.SplitPlaceOfFixed

theorem exists_splitPlace_plGw : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = D.naut.plGw kv.1 kv.2 := by
  intro D kv
  obtain ⟨s, -, h, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D kv.1 kv.2)
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  have hm : x ∈ (GlobalTheory.SplitConjPlace.conjSP s).w.asIdeal ↔
      IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal := by
    show Valued.v ((GlobalTheory.SplitConjPlace.conjSP s).i (x : D.host.E)) < 1 ↔
      Valued.v (s.i ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E)) < 1
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    rfl
  rw [hm]
  refine (h x _ ?_).symm
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

end GlobalTheory.SplitPlaceOfFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedTypePrimePlacesChoiceOnePerConjugatePair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open Formalism.MainNotions.BridgeLemma IsDedekindDomain

namespace GlobalTheory.RowLev.FixedChoice

theorem isChoice_wB_plGw : ∀ (D : D7) (X : HidaSetting D), GlobalTheory.RowLev.IsChoice X.B.I D.host.g D.nd.PlG (fun k v => Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v)) := by
  intro D X
  let e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE
  have he : ∀ a : 𝓞 X.B.I.E, ((e a : 𝓞 D.host.E) : D.host.E) = X.ιE (a : X.B.I.E) := fun a => rfl
  have hnat : ∀ m : ℕ, e (m : 𝓞 X.B.I.E) = (m : 𝓞 D.host.E) := fun m => map_natCast e m
  have hmemB : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E),
      a ∈ (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal ↔ e a ∈ w.asIdeal := fun w a => Iff.rfl

  have hspl : ∀ k, SplitsCompl D.host.E (D.host.g k) := by
    intro k
    have hp := D.host.g_prime k
    have := span_isMaximal hp
    apply splitsCompl_of_ncard _ _ hp
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k
  have hsp : ∀ k (P : Ideal (𝓞 X.B.I.E)), P.IsMaximal → ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P →
      Ideal.absNorm P = D.host.g k ∧ ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∉ P ^ 2 := by
    intro k P hP hg
    have hQ : (P.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hgQ : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.map e := by
      rw [← hnat]; exact Ideal.mem_map_of_mem _ hg
    obtain ⟨h1, h2⟩ := hspl k _ hQ hgQ
    refine ⟨?_, fun h => h2 ?_⟩
    · rw [← h1, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
      exact Nat.card_congr (Ideal.quotientEquiv P (P.map e) e rfl).toEquiv
    · rw [← hnat, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ h
  have hf : X.B.I.f = D.R.f := Formalism.L2.SG.Pf.RowDictPf.f_eq X
  refine (GlobalTheory.SplitChoice.exists_isChoice_and_isChoice_of_card X.B.I D.host.g D.host.g_prime D.host.g_ne hsp).2
    D.nd.PlG _ (fun k => by rw [hf]; convert D.nd.card_PlG k) (fun k v => ?_) (fun k => ?_) (fun k v v' hc => ?_)
  · rw [hmemB, hnat]; exact D.naut.plGw_over k v
  · intro v v' h
    simp only at h
    apply D.naut.plGw_inj k
    apply HeightOneSpectrum.ext
    have h1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal.map e = w.asIdeal :=
      fun w => Ideal.map_comap_of_surjective _ e.surjective w.asIdeal
    rw [← h1, ← h1 (D.naut.plGw k v'), h]
  · apply D.naut.plGw_nconj k v v'
    intro x y hxy
    have hst : ((e.symm y : 𝓞 X.B.I.E) : X.B.I.E) = star ((e.symm x : 𝓞 X.B.I.E) : X.B.I.E) := by
      apply X.ιE.injective
      rw [X.ιE_conj, ← he, ← he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hxy]
    have := hc (e.symm x) (e.symm y) hst
    rwa [hmemB, hmemB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at this

end GlobalTheory.RowLev.FixedChoice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedFrameCongruentUnitriangularAtPrimesStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedFrame_congruent_unitriangular_at_primes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ)) := by
  first | exact @GlobalTheory.Unfold.GluedCong.glued_loc_cong | exact GlobalTheory.Unfold.GluedCong.glued_loc_cong | (intros; apply GlobalTheory.Unfold.GluedCong.glued_loc_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFamilyUnitriangularChangeOfMemFrameUnipotentStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (Fr : FrameD H r), ∀ n ∈ Fr.N, Tri E Fr.f (fun b => n (Fr.f b)) := by
  first | exact @GlobalTheory.NFrameTri.tri_of_mem_N | exact GlobalTheory.NFrameTri.tri_of_mem_N | (intros; apply GlobalTheory.NFrameTri.tri_of_mem_N <;> assumption)
end

