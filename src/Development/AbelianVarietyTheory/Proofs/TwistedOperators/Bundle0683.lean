module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0681
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjections
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0679

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelOneCosetAtExceptionalPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.OneCosetBF.one_coset_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xZero (F.dJ ρ h)), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h g hg hc
  exact GlobalTheory.OneCosetBF.assemble _ _ _ _ G.pl.S0 ⟨G.pl.v0, by simp [GlobalTheory.ChiGrid.Places.S0]⟩
    (_root_.GlobalTheory.OneCosetBFPlace.one_coset_place D hD T L μ0 hL sc G W M hM F hF ρ h) g hg hc.pt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainCompositesExistLiftCombinations
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.ChainLifts

theorem chainEx (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules)
    (hCR : GlobalTheory.Published.CuspRapidDecay) (hCW : GlobalTheory.Published.CasselmanWallach) (hDF : DepFixed) (hCM : CoreModels) : ChainEx := by
  intro D hq hsz T L μ0 hL sc hgap G W Mv hM v r₀ M₀ hr₀
  have hCom : (gridCom W).Is := _root_.GlobalTheory.CoreOnto.comOK D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hStage := _root_.GlobalTheory.CoreOnto.StageProof.stageOK D hq T L μ0 hL sc G W Mv hM
  have hPre := GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence hDF D hq hsz T L μ0 hL sc hgap G W Mv hM
  have hCM' := hCM D hq T L μ0 hL sc G W Mv hM
  have hStep := _root_.GlobalTheory.EvenOnto.StepExists.stepEx hDS hHC hCR hCW D
  have hConj := _root_.GlobalTheory.EvenOnto.ConjVal.values_conj_hecke hCR D
  have hEx := _root_.GlobalTheory.ExchPf.exchLaw D
  have hRL := _root_.GlobalTheory.ReLatPf.reLatLaw_holds D

  have rapid : ∀ i, i ≤ D.R.m → ∀ r, IsCoreLat G i r → ∀ M (y : (gridStage G v i r M).CC (gridCom W)) w,
      GlobalTheory.Grow.RapidDec (G.V (.core i)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
    intro i hi r hr M y w
    have hs := (hStage i hi).2 r hr v M
    have h1 := (hConj (gridCom W) hCom i hi _ hs).1 y w
    exact ((hRL.2.1 _ r W.θ _ M ∅).2.2.2.2 _).1 h1.2.2.2.2

  have ext : ∀ k (F₀ : Fn G (.core 0)) (F : Fn G (.core (k + 1))) (f : Sch G (.coreDown k)), Dep W (.core k) f →
      GlobalTheory.Grow.RapidDec (G.V (.core (k + 1))) F → F₀ ∈ Below W v k (dn W v k f F) → F₀ ∈ Below W v (k + 1) F := by
    rintro k F₀ F f hf hF ⟨Ψ, h1, h2, h3, h4⟩
    refine ⟨Function.update Ψ (k + 1) F, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases eq_or_ne i (k + 1) with rfl | hne
      · rw [Function.update_self]; exact hF
      · rw [Function.update_of_ne hne]; exact h1 i (by omega)
    · intro i hi
      rcases Nat.lt_or_ge i k with hik | hik
      · obtain ⟨f', hf', e⟩ := h2 i hik
        refine ⟨f', hf', ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact e
      · obtain rfl : i = k := by omega
        refine ⟨f, hf, ?_⟩
        rw [Function.update_of_ne (by omega), Function.update_self]
        exact h4
    · rw [Function.update_of_ne (by omega)]; exact h3
    · exact Function.update_self _ _ _
  have key : ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧ ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k
      (gridStage G v k r M) Θ ∧ ∃ (I : Type) (N : I → SmT (gridStage G v k r M).M →ₗ[ℂ] SmT (gridStage G v 0 r₀ M₀).M),
      (∀ ι y w, GlobalTheory.EvenOnto.PiLocalization₂.val (Θ y) (N ι w) ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)) ∧
      (gridStage G v 0 r₀ M₀).KF ≤ Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w} := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨r₀, M₀, hr₀, LinearMap.id, GlobalTheory.EvenOnto.Reach.zero, PUnit, fun _ => LinearMap.id, ?_, ?_⟩
      · intro _ y w
        refine ⟨Function.update (fun i => (0 : Fn G (.core i))) 0 (GlobalTheory.EvenOnto.PiLocalization₂.val y w), ?_, ?_, ?_, ?_⟩
        · intro i hi
          obtain rfl : i = 0 := by omega
          show GlobalTheory.Grow.RapidDec _ (GlobalTheory.EvenOnto.PiLocalization₂.val y w)
          exact rapid 0 (Nat.zero_le _) r₀ hr₀ M₀ y w
        · intro i hi; omega
        · exact Function.update_self _ _ _
        · exact Function.update_self _ _ _
      · intro x hx
        exact Submodule.subset_span ⟨PUnit.unit, x, hx, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := ih (by omega)
      obtain ⟨r', hr'⟩ := (hStage (k + 1) hk).1
      obtain ⟨M', -⟩ := hCM' (k + 1) hk
      have hs := (hStage k (by omega)).2 r hr v M
      have hs' := (hStage (k + 1) hk).2 r' hr' v M'
      obtain ⟨ω, f, hpre, hexch, hdep⟩ := hPre k (by omega) r r' hr hr' v M M'
      have hkm : k < (gridCom W).m := by show k < D.R.m; omega
      obtain ⟨p, hpω, hpf, hp⟩ := hStep (gridCom W) hCom k hkm _ _ hs hs' ω f hpre
      subst hpω hpf
      refine ⟨r', M', hr', Θ ∘ₗ p.io, GlobalTheory.EvenOnto.Reach.step hΘ hs' p hp, I × PolF D _ _,
        fun q => N q.1 ∘ₗ p.It q.2, ?_, ?_⟩
      · rintro ⟨ι, P⟩ y w
        have h1 := ha ι (p.io y) (p.It P w)
        have hth : IsThetaFunO W.ψ (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P) :=
          ((hEx W.ψ (G.V (.core k)) (G.V (.core (k + 1))) W.ψ_std).1 _).2 (hdep P).1
        have heq : GlobalTheory.EvenOnto.PiLocalization₂.val (p.io y) (p.It P w) =
            dn W v k (exch (G.V (.core k)) (G.V (.core (k + 1))) (p.pt P)) (GlobalTheory.EvenOnto.PiLocalization₂.val y w) := by
          funext g
          refine (hp.io.eq y P w g).symm.trans ?_
          simp only [Formalism.IndefR.Lift.liftInt, dn]
          congr 1
          funext h
          congr 1
          show _ = thetaKO (W.om (.core k)) (negGA _ h) g _
          unfold thetaKO
          rw [hexch _ hth g h]
          have hadj : GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0 = 0 := by
            simp [GlobalTheory.PairLift.adjO]
          show _ = (p.ω (g, h) (p.pt P)) (GlobalTheory.PairLift.adjO (G.V (.core k)) (G.V (.core (k + 1))) 0)
          rw [hadj]
        rw [heq] at h1
        exact ext k _ _ _ (hdep P) (rapid (k + 1) hk r' hr' M' y w) h1
      · intro x hx
        have hx' := hb hx
        refine (Submodule.span_le.2 ?_) hx'
        rintro _ ⟨ι, w, hw, rfl⟩
        have hon := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ _ _ W.θ W.ψ ((gridCom W).a k) ((gridCom W).a k) p.ω p.f p.It
          hCom.inf ⟨(gridCom W).χ k, (gridCom W).χ k, hp.pre.weil, fun τ => ⟨hCom.exp k hkm τ, hCom.exp k hkm τ⟩⟩
          hp.pre.vac hp.it hw
        have hmap : (Submodule.span ℂ {w' | ∃ P, ∃ v' ∈ (gridStage G v (k + 1) r' M').KF, w' = p.It P v'}).map (N ι) ≤
            Submodule.span ℂ {x | ∃ q : I × PolF D _ _, ∃ w ∈ (gridStage G v (k + 1) r' M').KF, x = (N q.1 ∘ₗ p.It q.2) w} := by
          rw [Submodule.map_span]
          refine Submodule.span_le.2 ?_
          rintro _ ⟨_, ⟨P, v', hv', rfl⟩, rfl⟩
          exact Submodule.subset_span ⟨(ι, P), v', hv', rfl⟩
        exact hmap (Submodule.mem_map_of_mem hon)
  intro k hk
  obtain ⟨r, M, hr, Θ, hΘ, I, N, ha, hb⟩ := key k hk
  refine ⟨r, M, hr, Θ, hΘ, fun y x hx => ?_⟩
  let φ : SmT (gridStage G v 0 r₀ M₀).M →ₗ[ℂ] Fn G (.core 0) := (Θ y).1
  have hmap : (Submodule.span ℂ {x | ∃ ι, ∃ w ∈ (gridStage G v k r M).KF, x = N ι w}).map φ ≤
      Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (GlobalTheory.EvenOnto.PiLocalization₂.val y w)} := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨ι, w, -, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨w, ha ι y w⟩
  exact hmap (Submodule.mem_map_of_mem (hb hx))

end GlobalTheory.ChainLifts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHaarVolumeOfConjugateLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_volume_of_conjugate_lattice : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D,
    ∀ la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), la.IsHaarMeasure →
    ∃ V₀ : ℝ, 0 < V₀ ∧ ∀ t β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      la.real {n | (⟨b j, hb⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hb⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} *
        (GlobalTheory.RowWt.colCoef ch t β j : ℝ) = V₀ := by
  first | exact @GlobalTheory.CellIdx.vol_mul_colCoef | exact GlobalTheory.CellIdx.vol_mul_colCoef | (intros; apply GlobalTheory.CellIdx.vol_mul_colCoef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantLastVertexLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

open GlobalTheory.ExpansionInvariance in
theorem pairPts_last_invariant (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (ht : t ∈ U) (hβ : β ∈ S.supp t Φ) (hτ : S.IsExpansion t Φ β τ)
    (hv : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m)))
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m))
    (hx : x D.R.m = finEmb G.sp.topDec (y D.R.m)) (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) :
    pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  have hm := D.R.two_le_m
  have h0x : Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0 = x 0 :=
    Function.update_of_ne (by omega) _ _
  have h0y : Function.update y D.R.m (y D.R.m * k) 0 = y 0 := Function.update_of_ne (by omega) _ _
  rw [h0x, h0y, GlobalTheory.FunObj.SumModel.finEmb_mul, ← hx]
  have hth : ∀ d ∈ τ.support, (∀ j, IsThetaFunO W.ψ _ _ (S.Z.vec (d.1 j))) ∧ ∀ i, IsThetaFunO W.ψ _ _ (S.Z.vec (d.2 i)) :=
    fun d hd => ⟨fun j => vec_theta S (defPair_top t j) (inRange_top t j) _ ((hv d hd).1 j),
      fun i => vec_theta S (defPair_chi i) (inRange_chi i) _ ((hv d hd).2 i)⟩
  obtain ⟨M, hM⟩ := GlobalTheory.ArrowMultilinear.pairing_multilinear S t x y (Ψ (x 0)) (F (y 0))
  set uc : PureDat G t → ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ := fun d =>
    Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D) (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D))))
    with huc
  set ur : PureDat G t → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ := fun d =>
    Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) with hur
  have thc : ∀ d ∈ τ.support, ∀ j, IsThetaFunO W.ψ _ _ (uc d j) := by
    intro d hd j
    by_cases hj : j = lastIx D
    · subst hj
      simp only [huc, Function.update_self]
      exact colShift_theta S t _ ((hth d hd).1 _)
    · simp only [huc, Function.update_of_ne hj]
      exact (hth d hd).1 j
  have thr : ∀ d ∈ τ.support, ∀ i, IsThetaFunO W.ψ _ _ (ur d i) := by
    intro d hd i
    by_cases hi : i = lastIx D
    · subst hi
      simp only [hur, Function.update_self]
      exact rowShift_theta S k ((hth d hd).2 _)
    · simp only [hur, Function.update_of_ne hi]
      exact (hth d hd).2 i
  have lhs : pairPts S τ (Function.update x D.R.m (x D.R.m * finEmb G.sp.topDec k)) (Function.update y D.R.m (y D.R.m * k))
      (Ψ (x 0)) (F (y 0)) = τ.sum fun d a => a * M (fun j => toTh W _ (uc d j)) (fun i => toTh W _ (ur d i)) := by
    simp only [pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq, GlobalTheory.LastColumnMove.colMapV_update_last S _ x _ ((hth d hd).1 _), GlobalTheory.LastRowMove.rowMapV_update_last S _ y _ ((hth d hd).2 _)]
    have e1 : (fun j : Fin D.R.m => (toTh W _ (uc d j) : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) = uc d :=
      funext fun j => coe_toTh W _ (thc d hd j)
    have e2 : (fun i : Fin D.R.m => (toTh W _ (ur d i) : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) = ur d :=
      funext fun i => coe_toTh W _ (thr d hd i)
    rw [e1, e2]
  have rhs : pairPts S τ x y (Ψ (x 0)) (F (y 0)) =
      τ.sum fun d a => a * M (fun j => toTh W _ (S.Z.vec (d.1 j))) (fun i => toTh W _ (S.Z.vec (d.2 i))) := by
    simp only [pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq]
    have e1 : (fun j : Fin D.R.m => (toTh W _ (S.Z.vec (d.1 j)) : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) = fun j : Fin D.R.m => S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh W _ (S.Z.vec (d.2 i)) : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        fun i : Fin D.R.m => S.Z.vec (d.2 i) :=
      funext fun i => coe_toTh W _ ((hth d hd).2 i)
    rw [e1, e2]
  rw [lhs, rhs]
  refine GlobalTheory.funProd_multilinear_sum_eq M τ _ _ _ _ fun w v => ?_
  have key := _root_.GlobalTheory.LastVertexTensor.productFn_invariant S hL hde hc ht hβ hτ hv k hk w v
  simp only [Finsupp.sum] at key ⊢
  refine (Finset.sum_congr rfl fun d hd => ?_).trans (key.trans (Finset.sum_congr rfl fun d hd => ?_))
  · simp only [coe_toTh W _ (thc d hd _), coe_toTh W _ (thr d hd _)]
    rfl
  · simp only [coe_toTh W _ ((hth d hd).1 _), coe_toTh W _ ((hth d hd).2 _)]

end GlobalTheory.LastVertexInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionTensorSumInvariantGridRowLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVertexInv

theorem sum_prod_moveV_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, moveV S j hj k (vecOf S d) a (z a)) = τ.sum fun d c => c * ∏ a, vecOf S d a (z a) := by
  intro D T L sc G W U S t Φ β τ μ₀ hμ hq hQ hU hβ hE hv j hj k hk z
  obtain ⟨c₁, c₂, Tm, h1, h2, hT⟩ := GlobalTheory.RowVertexInv.FactorTheta.vecOf_eq_intertwiner S hE hv j hj k hk
  have hB := _root_.GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq S hμ hq hQ hU hβ hE hv j hj k hk c₁ c₂ h1 h2
  let M : MultilinearMap (RingHom.id ℂ) (fun a : Fin D.R.m ⊕ Fin D.R.m => ↥(⊤ : Submodule ℂ (FactorFn G t a))) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ (Fin D.R.m ⊕ Fin D.R.m) ℂ).compLinearMap fun a =>
      (LinearMap.proj (z a)) ∘ₗ Tm a ∘ₗ (⊤ : Submodule ℂ (FactorFn G t a)).subtype
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq (X := fun a => WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)))
    (fun a => ⊤) M τ τ (fun d a => ⟨scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a, trivial⟩)
    (fun d a => ⟨fnOf d a, trivial⟩) hB
  simp only [smul_eq_mul] at key
  convert key using 1
  · refine Finsupp.sum_congr fun d hd => ?_
    congr 1
    simp only [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply]
    exact Finset.prod_congr rfl fun a _ => by rw [(hT d hd a).2]
  · refine Finsupp.sum_congr fun d hd => ?_
    congr 1
    simp only [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply]
    exact Finset.prod_congr rfl fun a _ => by rw [(hT d hd a).1]

end GlobalTheory.RowVertexInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselLatticeSplits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.SplitsFB

theorem inv_neg_mat {D : D7} {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem symplO_negSp {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have e : hO (negSp S) T x y = -hO S T x y := by
    unfold hO
    rw [negSp_gram, inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplO
  rw [e, mul_neg, map_neg]

theorem symplO_zero_left' {D : D7} (S T : HSp D) (y : WO S T) : symplO S T 0 y = 0 := by
  unfold symplO hO
  simp

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem sd_grid (i : ℕ) (h1 : 1 ≤ i) (h : i ≤ D.R.m) : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) :=
  (G.isV (X := .grid i 0) (by show _ ∧ _; constructor <;> omega) (by intro j hj; injection hj with h2; omega)).sd

theorem latRow_mxAt (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u} (hu : u ∈ latRow G i) : MxAt (fun _ => True) u :=
  ((_root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega)) (fun _ => True) u).1
    hu.1).1

theorem latRow_pair (W : G.Weil) (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u u'} (hu : u ∈ latRow G i) (hu' : u' ∈ latRow G i) :
    W.ψ (symplO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) u u') = 1 := by
  have := (_root_.GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega))
    (fun _ => True) u (latRow_mxAt G i h1 h hu)).1 hu.1 u' hu'.1
  rwa [symplO_negSp, AddChar.map_neg_eq_inv, inv_eq_one] at this

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {x : Mx D m n} (hx : MxAt P x) (y : Mx D n k) : MxAt P (x ⬝ y) :=
  fun i j => by
    show (x * y) i j ∈ _
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

end


set_option maxHeartbeats 2000000 in
theorem splits_FB : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hS := _root_.GlobalTheory.ProjLat.latRow_proj D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hT := _root_.GlobalTheory.AscFin.latRow_proj_tgt D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hC := _root_.GlobalTheory.CharXFB.charx_fb D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hB := _root_.GlobalTheory.RowBig.latRow_le_latBig D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) (by omega)
  refine ⟨fun u hu => ?_⟩
  set dV := F.dJ (σ + 1) h with hdV
  set dW := F.dB σ h' with hdW
  obtain ⟨hX, hY⟩ := hS u hu
  have e1 := dV.sum_eq_one
  have e2 := dW.sum_eq_one
  have h0 : u ⬝ (dV.j0 ⬝ dV.p0) ∈ latRow G (2 * σ + 2) := by
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    have e : u ⬝ (dV.j0 ⬝ dV.p0) = u - u ⬝ (dV.jX ⬝ dV.pX) - u ⬝ (dV.jY ⬝ dV.pY) := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem hu hX) hY
  set w := u ⬝ (dV.j0 ⬝ dV.p0) with hw
  obtain ⟨gX, gY⟩ := hT w h0
  have g0 : (dW.j0 ⬝ dW.p0) ⬝ w ∈ latRow G (2 * σ + 2) := by
    have s : (dW.jX ⬝ dW.pX) ⬝ w + (dW.j0 ⬝ dW.p0) ⬝ w + (dW.jY ⬝ dW.pY) ⬝ w = w := by
      rw [← Matrix.add_mul, ← Matrix.add_mul, e2, Matrix.one_mul]
    have e : (dW.j0 ⬝ dW.p0) ⬝ w = w - (dW.jX ⬝ dW.pX) ⬝ w - (dW.jY ⬝ dW.pY) ⬝ w := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem h0 gX) gY
  have hA1 : dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extX_apply, Matrix.mul_assoc]; exact hX
  have hA2 : dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extY_apply, Matrix.mul_assoc]; exact hY
  have hB1 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) = (dW.jX ⬝ dW.pX) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, hw]; simp only [Matrix.mul_assoc]
  have hB2 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) = (dW.jY ⬝ dW.pY) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, hw]; simp only [Matrix.mul_assoc]
  have hG0 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) = (dW.j0 ⬝ dW.p0) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, hw]; simp only [Matrix.mul_assoc]
  have heq : u = dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) + dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) +
      dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0)) + dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0)) +
        dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) := by
    rw [map_add (f := _), map_add (f := _), hB1, hB2, hG0, HypDec.extX_apply, HypDec.extY_apply, ← Matrix.add_mul, ← Matrix.add_mul,
      show dW.jX ⬝ dW.pX + dW.jY ⬝ dW.pY + dW.j0 ⬝ dW.p0 = 1 from (add_right_comm _ _ _).trans e2, Matrix.one_mul, hw,
      Matrix.mul_assoc, Matrix.mul_assoc]
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    conv_lhs => rw [← s]
    abel
  refine ⟨u ⬝ dV.jX, hA1, u ⬝ dV.jY, AddSubgroup.subset_closure
      ⟨mxAt_mul (latRow_mxAt G (2 * σ + 2) (by omega) (by omega) hu) _,
        fun a ha => latRow_pair G W (2 * σ + 2) (by omega) (by omega) ha hA2⟩,
    dW.pX ⬝ (u ⬝ dV.j0), ?_, dW.pY ⬝ (u ⬝ dV.j0), ?_, dW.p0 ⬝ (u ⬝ dV.j0), ?_, heq, hC _ hA2, ?_⟩
  · show dV.ext0 _ (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB1]; exact hB gX
  · show dV.ext0 _ (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB2]; exact hB gY
  · show dV.ext0 _ (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) ∈ latRow G (2 * σ + 2)
    rw [hG0]; exact g0
  · rw [map_zero, symplO_zero_left', AddChar.map_zero_eq_one]

end GlobalTheory.AscFin.SplitsFB
end
end

