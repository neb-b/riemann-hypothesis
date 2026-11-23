module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowRep

open GlobalTheory.SmoothMultilinear

theorem act_list {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : (∀ τ, M.H τ) → K)
    (h : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      F (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (F y))
    (y : ∀ τ, M.H τ) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V p.1)) :
    ρ (l.map fun p => atTau θ V p.1 p.2).prod (F y) =
      F fun τ => M.rep τ (l.map fun p => if p.1 = τ then p.2 else 1).prod (y τ) := by
  induction l with
  | nil => simp [rep_one]
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V q.1) := fun q hq => hl q (by simp [hq])
    rw [List.map_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply, ih hl',
      ← h p.1 p.2 (hl p (by simp))]
    congr 1
    funext τ
    rw [List.map_cons, List.prod_cons]
    by_cases e : p.1 = τ
    · subst e
      rw [Function.update_self, if_pos rfl, rep_mul M _ (hl p (by simp)), ContinuousLinearMap.mul_apply]
      apply GlobalTheory.SmoothMultilinear.prod_mem
      intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
      split_ifs with e
      · exact e ▸ hl' q hq
      · exact GlobalTheory.SmoothMultilinear.prod_mem _ [] (by simp)
    · rw [Function.update_of_ne (Ne.symm e), if_neg e, one_mul]

theorem smooth_of_contDiff {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : (∀ τ, M.H τ) → K) (hF : ContDiff ℝ ∞ F)
    (h : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      F (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (F y)) (v : M.Vec) :
    GlobalTheory.HolDict.IsSmoothVector' θ V ρ (F fun τ => (v τ : M.H τ)) := by
  have hs : ∀ τ, SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) := fun τ => smooth_of_span _ _ _ (v τ).2
  intro k τs Xs hX
  have e : (fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod (F fun τ => (v τ : M.H τ))) =
      fun t : Fin k → ℝ => F fun τ => M.rep τ
        (List.ofFn fun i => NormedSpace.exp (t i • (if τs i = τ then Xs i else 0))).prod (v τ : M.H τ) := by
    funext t
    have := act_list θ M ρ F h (fun τ => (v τ : M.H τ))
      (List.ofFn fun i => (τs i, NormedSpace.exp (t i • Xs i))) (by
        intro p hp
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
        exact exp_mem _ _ (hX i) _)
    simp only [List.map_ofFn] at this
    refine this.trans ?_
    congr 1
    funext τ
    congr 4
    funext i
    dsimp only [Function.comp_apply, Prod.fst, Prod.snd]
    split_ifs <;> simp
  rw [e]
  refine hF.comp (contDiff_pi.2 fun τ => ?_)
  refine hs τ k _ fun i => ?_
  split_ifs with e
  · exact e ▸ hX i
  · simp [lieAt]

theorem contDiff_anti {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] (c : A ≃ₗᵢ⋆[ℂ] B) : ContDiff ℝ ∞ c := by
  let L : A →L[ℝ] B :=
    { toFun := c
      map_add' := c.map_add
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, c.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]; rfl
      cont := c.continuous }
  exact L.contDiff


set_option maxHeartbeats 1000000 in
theorem exists_contRep : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) := by
  intro _ D X h θ S M J χ t c _ hθ _ hE _ hc Φ hΦ u
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, M.H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCd : ContDiff ℝ ∞ C := by
    refine contDiff_pi.2 fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (contDiff_anti (c τ)).comp (contDiff_pi.1 contDiff_id τ)
  let F : (∀ τ, M.H τ) → L2X X := fun y => Φ (X.B.tens (C y))
  have hF : ContDiff ℝ ∞ F := by
    have e : F = fun y => (Φ.compContinuousMultilinearMap m) (C y) := by
      funext y
      show Φ (X.B.tens (C y)) = Φ (m (C y))
      rw [hm]
    rw [e]
    exact (((Φ.compContinuousMultilinearMap m).contDiff (n := ∞)).restrict_scalars ℝ).comp hCd
  have hsm := smooth_of_contDiff θ M ρ F hF (fun τ a ha y => by
    obtain ⟨q1, q2, -⟩ := hat τ a ha
    rw [h3]
    refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
    obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
    rw [hC, hC]
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact hc _ a ha _
    · rw [Function.update_of_ne e]
      have q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
      rw [q]
      have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
      show _ = X.B.σ (X.pl.symm τ') 1 _
      rw [this]
      rfl) u
  obtain ⟨R, L, -, hR, -⟩ := GlobalTheory.TensRep.exists_adelic_rep (ι := fun v x => X.B.I.ext v (T x)) hθ h1 h2 h5 h6 h7
    h8 h9 hU
  obtain ⟨p1, p2⟩ := hR _ hsm (fun k hk hk' => by
    rw [h3]
    have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
    rw [e]
    exact hlev _ (hUg k hk) _)
  refine ⟨fun x => R (F fun τ => (u τ : M.H τ)) (T.symm x),
    GlobalTheory.RepSmooth.isContRep_of_ae X.B (p1.comp hT') (fun γ hγ x => ?_) ?_⟩
  · have e : (fun x => R (F fun τ => (u τ : M.H τ)) (T.symm γ * x)) = R (F fun τ => (u τ : M.H τ)) :=
      ((p1.comp (continuous_const_mul _)).ae_eq_iff_eq μ p1).1
        (Filter.EventuallyEq.trans
          (((measurePreserving_mul_left μ _).quasiMeasurePreserving.ae p2).mono fun _ hy => hy.symm)
          ((h10 (T.symm γ) (by rw [T.apply_symm_apply]; exact hγ) _).trans p2))
    rw [map_mul]
    exact congrFun e _
  · filter_upwards [h4 _ p2] with x hx
    rw [← hx, T.apply_symm_apply]
    rfl

end GlobalTheory.ConjRowRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlaceStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubled_unitary_chart_split_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n := (n + n))) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  first | exact @GlobalTheory.LFun.DblSplit.exists_dbl_chart | exact GlobalTheory.LFun.DblSplit.exists_dbl_chart | (intros; apply GlobalTheory.LFun.DblSplit.exists_dbl_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerSubConjNotMemSelfConjugatePlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjMovesResidue

theorem exists_sub_star_notMem : ∀ (D : D7) (Q : Pl D.host.E), IsConjPl (D := D) Q Q →
    ∃ δ δ' : 𝓞 D.host.E, (δ' : D.host.E) = star (δ : D.host.E) ∧ δ - δ' ∉ Q.asIdeal := by
  intro D Q _
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host Q.asIdeal Q.isMaximal
  refine ⟨θ, t, ?_, h2⟩
  change algebraMap (𝓞 D.host.E) D.host.E t = _
  rw [h1, Formalism.BasicNotions.Examples₂.star_eq_conj]

end GlobalTheory.ConjMovesResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRiStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_basis_unimodular_hermitian_local_ring : ∀ (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O), (∀ x, s (s x) = x) → (∃ τ : O, τ + s τ = 1) → (∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u) → ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) O), Formalism.UG.cT s Q = Q → IsUnit Q → ∃ a : GL (Fin n) O, Formalism.UG.cT s a.1 * Q * a.1 = 1 := by
  first | exact @GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing | exact GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing | (intros; apply GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTrans
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Unf.MajLoc

theorem exists_compact_sub {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (K Q : Set G)
    (hK : IsCompact K) (hQ : IsCompact Q) : ∃ K' : Set G, IsCompact K' ∧ ∀ k ∈ K, ∀ x ∈ Q, k - x ∈ K' :=
  ⟨_, (hK.prod hQ).image continuous_sub, fun k hk x hx => ⟨(k, x), ⟨hk, hx⟩, rfl⟩⟩

theorem summable_of_tsum_ne_top {α β : Type*} (f : β → ℝ) (hf : ∀ y, 0 ≤ f y) (h : (∑' y, ENNReal.ofReal (f y)) ≠ ⊤)
    (e : α → β) (he : Function.Injective e) : Summable fun a => f (e a) :=
  ((ENNReal.summable_toReal h).congr fun y => ENNReal.toReal_ofReal (hf y)).comp_injective he

theorem inv_pow_le {a c R : ℝ} (N : ℕ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hR : 0 ≤ R) (h : c ≤ a + R) :
    ((1 + a) ^ N)⁻¹ ≤ (1 + R) ^ N * ((1 + c) ^ N)⁻¹ := by
  have hle : 1 + c ≤ (1 + R) * (1 + a) := by nlinarith [mul_nonneg ha hR]
  have hA : 0 < (1 + a) ^ N := by positivity
  have hB : 0 < (1 + c) ^ N := by positivity
  rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hle N

theorem realSize_neg {D : D7} (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : realSize θ (-x) = realSize θ x := by
  unfold realSize
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : compAt θ τ (-x) i j = -compAt θ τ x i j := by
    show θ τ (infPart D (-x i j)) = -θ τ (infPart D (x i j))
    rw [RingHom.map_neg (infPart D), RingHom.map_neg (θ τ)]
  rw [this, norm_neg]

theorem maj_add_le {D : D7} (θ : InfFam D) {m n : ℕ} (K K' : Set (Mx D m n)) (N : ℕ) (x y : Mx D m n) (R : ℝ)
    (hR : 0 ≤ R) (hx : realSize θ x ≤ R) (hK : ∀ k ∈ K, k - x ∈ K') :
    maj θ K N (x + y) ≤ (1 + R) ^ N * maj θ K' N y := by
  by_cases hb : InBox K (x + y)
  · have hb' : InBox K' y := by
      obtain ⟨k, hk, hkx⟩ := hb
      refine ⟨k - x, hK k hk, ?_⟩
      have : y - (k - x) = x + y - k := by abel
      rw [this]; exact hkx
    unfold maj
    rw [if_pos hb, if_pos hb']
    have hadd := GlobalTheory.MajSum.realSize_add_le θ (x + y) (-x)
    have e2 : x + y + -x = y := by abel
    rw [e2, realSize_neg] at hadd
    exact inv_pow_le N (realSize_nonneg θ _) (realSize_nonneg θ _) hR (by linarith)
  · have e0 : maj θ K N (x + y) = 0 := by
      unfold maj
      rw [if_neg hb]
    rw [e0]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N _)

theorem summable_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K Q : Set (Mx D m n),
    IsCompact K → IsCompact Q → ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧
      ∀ x ∈ Q, ∀ ξ, GlobalTheory.Unf.maj θ K N (x + rat ξ) ≤ b ξ := by
  intro D θ hθ m n
  obtain ⟨N, hN⟩ := GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ m n
  refine ⟨N, fun K Q hK hQ => ?_⟩
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) := GlobalTheory.Unf.MajMeas.continuous_realSize hθ
  obtain ⟨K', hK', hKK⟩ := @exists_compact_sub (Mx D m n) _ _ (lattice_Mx D m n).1 K Q hK hQ
  obtain ⟨R, hR⟩ := (hQ.image hcont).bddAbove
  have hs : Summable fun ξ : Matrix (Fin m) (Fin n) D.host.E => maj θ K' N (rat ξ) :=
    summable_of_tsum_ne_top (fun y : ratMx D m n => maj θ K' N y) (fun y => maj_nonneg θ K' N y) (hN K' hK')
      (fun ξ => ⟨rat ξ, rat_mem ξ⟩) fun a b h => rat_injective (congrArg Subtype.val h)
  exact ⟨fun ξ => (1 + max R 0) ^ N * maj θ K' N (rat ξ), hs.mul_left _, fun x hx ξ =>
    maj_add_le θ K K' N x (rat ξ) (max R 0) (le_max_right _ _) ((hR ⟨x, hx, rfl⟩).trans (le_max_left _ _))
      fun k hk => hKK k hk x hx⟩

end GlobalTheory.Unf.MajLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopologicalIsoParahoricChartSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChartSplitIso

variable {D : D7}

def projEmb {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  (φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight

theorem splitProj_projEmb {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (x : Fv D.host.F v ⊗[D.host.F] D.host.E) : GlobalTheory.AdelicU.splitProj (projEmb φ) x = φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    have e : (a ⊗ₜ[D.host.F] x : Fv D.host.F v ⊗[D.host.F] D.host.E) = a • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [GlobalTheory.AdelicU.splitProj_tmul, e, map_smul, smul_eq_mul]
    rfl

def reindexGL {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (K : Type) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (ε : ι ≃ κ) : GL κ K ≃ₜ* GL ι K where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv K K ε.symm).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩

theorem reindexGL_val {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (K : Type) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (ε : ι ≃ κ) (x : GL κ K) : (reindexGL K ε x).1 = x.1.submatrix ε ε := rfl

theorem grpCo_eq {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (V : HSp D)
    (hJ : IsHermND D.sp.cm.sig V.gram) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    grpCo φ V B g = GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (projEmb φ) B
      (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g) := by
  refine Units.ext ?_
  rw [GlobalTheory.AdelicU.splitEquivIn_apply]
  simp only [grpCo, Units.val_mul]
  congr 2
  exact Matrix.ext fun i j => (splitProj_projEmb φ _).symm

end GlobalTheory.ChartSplitIso

namespace GlobalTheory.ChartSplitIso

theorem exists_equiv_emb : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v)
    (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ →
    IsChart s k φ ι → ∃ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v,
      ∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y) := by
  intro D s k v φ ι _ _ hι
  obtain ⟨ε, -, hε⟩ := hι
  have hJ : IsHermND D.sp.cm.sig s.V.gram := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 s.V
  let Ψ := GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (projEmb φ) (frCo φ s.β)
  refine ⟨(reindexGL (Fv D.host.F v) ε).symm.trans Ψ.symm, fun y => (hε y).1.symm.trans ?_⟩
  change GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v (ι y)) = _
  congr 1
  apply Ψ.injective
  apply (reindexGL (Fv D.host.F v) ε).injective
  refine Units.ext ?_
  rw [reindexGL_val, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply,
    ContinuousMulEquiv.apply_symm_apply, ← (hε y).2, grpCo_eq φ s.V hJ]

end GlobalTheory.ChartSplitIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilDatumExistence

theorem weilDatumExists : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.WeilDatumExists D := by
  intro D S T ψ χS χT hψ hS hT rS rT
  exact GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hS hT rS rT

end GlobalTheory.WeilDatumExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueInertPlaceAndSegmentStatement
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
theorem _root_.GlobalTheory.T.heckeChar_value_inert_place_and_segment : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → Formalism.L2.Theta.ResEta D χ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χ w → val (F := D.host.F) χ w = (-1) ^ n ∧ ∀ (qu z : ℂˣ) (t : ℕ), (qu : ℂ) = qV D.host.F v → seg w z t = (GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str qu t).map (z * ·) := by
  first | exact @GlobalTheory.ChainOnto.val_seg_of_isInertAt | exact GlobalTheory.ChainOnto.val_seg_of_isInertAt | (intros; apply GlobalTheory.ChainOnto.val_seg_of_isInertAt <;> assumption)
end

