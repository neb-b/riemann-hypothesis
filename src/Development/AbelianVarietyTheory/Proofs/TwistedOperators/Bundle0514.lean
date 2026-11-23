module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0503
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegerOutsidePrimePowDvdMaximalIdealPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.SplitPtLev

theorem dvd_of_mem_maxIdeal_pow : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (w : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e w → ∀ (d : ℕ) (m : 𝓞 D.host.E),
  m ∉ w.asIdeal ^ (d + 1) → ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k], (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E)) := by
  intro D k _ _ _ _ p w he d m hm z hz
  let f : 𝓞 D.host.E → k := fun x => p.pr (incA D (x : D.host.E))
  have fmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    simp only [f, map_mul]
  obtain ⟨t, ht, ht2⟩ : ∃ t ∈ w.asIdeal, t ∉ w.asIdeal ^ 2 := by
    obtain ⟨t, ht, ht2⟩ := Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top 1
    exact ⟨t, by simpa using ht, ht2⟩
  have h1w : (1 : 𝓞 D.host.E) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  obtain ⟨q, hq⟩ := (GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p w he t 1 ht ht2 h1w).1
  have hunit : ∀ x, x ∉ w.asIdeal → valuation k (f x) = 1 := fun x hx =>
    (GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p w he t x ht ht2 hx).2
  obtain ⟨s, hs, hsw⟩ : ∃ s, s ∉ w.asIdeal ∧ ∀ x ∈ w.asIdeal, ∃ y, s * x = y * t := by
    obtain ⟨J, hJ⟩ : w.asIdeal ∣ Ideal.span {t} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ht)
    have hJw : ¬ J ≤ w.asIdeal := by
      intro h
      apply ht2
      have : Ideal.span {t} ≤ w.asIdeal ^ 2 := by
        rw [hJ, pow_two]
        exact Ideal.mul_mono_right h
      exact this (Ideal.mem_span_singleton_self t)
    obtain ⟨s, hsJ, hsw⟩ := Set.not_subset.1 hJw
    refine ⟨s, hsw, fun x hx => ?_⟩
    have : s * x ∈ Ideal.span {t} := by
      rw [hJ, mul_comm s x]
      exact Ideal.mul_mem_mul hx hsJ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨y, hy.symm⟩
  have hq1 : valuation k ((q.1 : 𝒪[k]) : k) ≤ 1 := (GlobalTheory.FinPl.SplitPt.val_unif_lt_one q).le
  have key : ∀ n (x : 𝓞 D.host.E), x ∉ w.asIdeal ^ (n + 1) →
      valuation k ((q.1 : 𝒪[k]) : k) ^ n ≤ valuation k (f x) := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [pow_zero, hunit x (by simpa using hx)]
    | succ n ih =>
      intro x hx
      by_cases hxw : x ∈ w.asIdeal
      · obtain ⟨y, hy⟩ := hsw x hxw
        have hy' : y ∉ w.asIdeal ^ (n + 1) := by
          intro hy1
          have hsx : s * x ∈ w.asIdeal ^ (n + 1 + 1) := by
            rw [hy, pow_succ]
            exact Ideal.mul_mem_mul hy1 ht
          rcases Ideal.IsPrime.mul_mem_pow w.asIdeal hsx with h | h
          · exact hs h
          · exact hx h
        have h1 := congrArg (fun u => valuation k (f u)) hy
        simp only [fmul, Valuation.map_mul, hunit s hs, one_mul] at h1
        rw [h1, ← hq, pow_succ]
        rw [hq]
        exact mul_le_mul_of_nonneg_right (ih y hy') zero_le'
      · rw [hunit x hxw]
        exact pow_le_one₀ zero_le' hq1
  have hzle : ∀ n, ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n,
      valuation k (z : k) ≤ valuation k ((q.1 : 𝒪[k]) : k) ^ n := by
    intro n
    induction n with
    | zero =>
      intro z _
      rw [pow_zero]
      exact z.2
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun x y hx hy => ?_)
      · have hy1 : valuation k (y : k) < 1 := by
          have : y ∈ nonunits 𝒪[k] := (IsLocalRing.mem_maximalIdeal y).1 hy
          exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 this
        rw [MulMemClass.coe_mul, Valuation.map_mul, pow_succ]
        exact mul_le_mul' (ih x hx) (GlobalTheory.FinPl.SplitPt.val_le_unif q hy1)
      · rw [AddMemClass.coe_add]
        exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  have hmv := key d m hm
  have hpos : 0 < valuation k (f m) :=
    lt_of_lt_of_le (pow_pos (GlobalTheory.FinPl.SplitPt.val_unif_pos q) d) hmv
  have hf0 : f m ≠ 0 := fun h => by simp [h] at hpos
  refine ⟨(z : k) / f m, ?_, ?_⟩
  · show valuation k ((z : k) / f m) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ ((hzle d z hz).trans hmv) zero_le'
  · exact (div_mul_cancel₀ _ hf0).symm

end GlobalTheory.SplitPtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvContCast
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenConvProof

variable {D : D7}

theorem invCont_cast {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hc : Continuous φ) (hl : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    Continuous (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
        φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact ⟨hc, hl⟩

theorem genPer_conv : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t a, ch.S.SumOK t (ch.Phi a) →
    ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M →
      ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y Q ξ η, GenConv ch t a M d y Q ξ η := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro t a hOK β hβ M hM τ hτ d hd y Q ξ η
  have hL := s.core.lev
  have hm := s.core.models
  have hcol : GlobalTheory.DefConv.IsInvCont (.top 0) (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) :=
    ⟨GlobalTheory.RowBplus.pairVec_cont ch.G ch.W.θ ch.W.θ_is ξ (col_mem ch a),
      fun γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g⟩
  have hx := (hm.HX t).2.1.le (LinearMap.mem_range_self (R.HX t).e y)
  have hform : GlobalTheory.DefConv.IsInvCont (.grid 0 D.R.m) (formGen ch t y η) := by
    have k := invCont_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
      ((LinearMap.continuous_of_finiteDimensional η).comp
        (GlobalTheory.ThetaIntegrand.ext_continuous R.cX hm.cX R.βX (R.datXt t) hx))
      (fun γ hγ g => by simp only [GlobalTheory.ThetaIntegrand.ext_invariant R.cX hx γ hγ g])
    exact ⟨k.1, k.2⟩
  have hv := hOK.vec β τ hτ d hd
  have hcG : Path.Fam.All (fun a f => GlobalTheory.DefConv.Good ch.W M a f)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j)) :=
    GlobalTheory.DefConv.all_colFam t _ _ fun j => GlobalTheory.DefConv.good_col ch.W M j.2 _
      (GlobalTheory.DefConv.theta_fock ch.W ch.S.toGridChoice (p := .top t j) (by show (j : ℕ) + 1 ≤ D.R.m; omega)
        (by show (j : ℕ) + 1 ≤ D.R.m; omega) (d.1 j) (hv.1 j) (Q.1 j))
      (GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .top j) (show (j : ℕ) ≤ D.R.m by omega) rfl) (hM.1 j j.2)
  have hrG : Path.Fam.All (fun a f => GlobalTheory.DefConv.Good ch.W M a f)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) :=
    GlobalTheory.DefConv.all_rowFam D.R.m _ _ fun i => GlobalTheory.DefConv.good_row ch.W M i.2 _
      (GlobalTheory.DefConv.theta_fock ch.W ch.S.toGridChoice (p := .chi i D.R.m)
        (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨by omega, rfl⟩)
        (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) (d.2 i) (hv.2 i) (Q.2 i))
      (GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .grid i D.R.m) ⟨by omega, le_rfl⟩ (by simp [Node.neg]))
      (hM.2 i (by omega))
  obtain ⟨hc1, hc2⟩ := GlobalTheory.DefConv.path ch.W M hcol _ _ hcG
  obtain ⟨hr1, hr2⟩ := GlobalTheory.DefConv.path ch.W M hform _ _ hrG
  refine ⟨hc1, hr1, ?_⟩
  obtain ⟨hac, hamul, haQ⟩ := _root_.GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational ch.G.sp.topDec
  have hpos := GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by simp [Node.neg])
  obtain ⟨Cc, hCc, hcov⟩ := GlobalTheory.definite_unitary_cocompact _ hpos
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.grid D.R.m D.R.m))
  obtain ⟨hH, hfd⟩ := (hM.2 D.R.m le_rfl).haar_fund
  refine GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact _ _ _ Cc hfd hCc hcov _
    ((hc2.1.comp hac).mul hr2.1) fun γ hγ g => ?_
  simp only [hamul, hc2.2 _ (haQ γ hγ), hr2.2 γ hγ]

end GlobalTheory.GenConvProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Classical

noncomputable section

namespace GlobalTheory.KFinDecomp

theorem assemble_finset {ι : Type} [DecidableEq ι] {U : ι → Type} [∀ τ, AddCommGroup (U τ)] [∀ τ, Module ℂ (U τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (𝒞 : Set E) (Ty : ι → E → Prop)
    (R : ∀ τ, U τ → U τ → (E → E) → Prop) (m : ι → ℕ) (a : ∀ τ, Fin (m τ) → U τ)
    (A : ∀ τ, Fin (m τ) → U τ → E → E)
    (hadd : ∀ τ j u, ∀ f ∈ 𝒞, ∀ f' ∈ 𝒞, A τ j u (f + f') = A τ j u f + A τ j u f')
    (hsmul : ∀ τ j u (c : ℂ), ∀ f ∈ 𝒞, A τ j u (c • f) = c • A τ j u f)
    (hmaps : ∀ τ j u, ∀ f ∈ 𝒞, A τ j u f ∈ 𝒞)
    (hkeep : ∀ τ j u τ', τ' ≠ τ → ∀ f ∈ 𝒞, Ty τ' f → Ty τ' (A τ j u f))
    (hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f))
    (hadd' : ∀ τ j, ∀ f ∈ 𝒞, ∀ u u', A τ j (u + u') f = A τ j u f + A τ j u' f)
    (hsmul' : ∀ τ j, ∀ f ∈ 𝒞, ∀ (c : ℂ) u, A τ j (c • u) f = c • A τ j u f)
    (hR : ∀ τ j, ∀ f ∈ 𝒞, ∀ u w Φ, R τ u w Φ → A τ j w f = Φ (A τ j u f))
    (hsum : ∀ τ, ∀ f ∈ 𝒞, Ty τ f → f = ∑ j, A τ j (a τ j) f)
    (ψ : E) (hψ : ψ ∈ 𝒞) (hTy : ∀ τ, Ty τ ψ) (s : Finset ι) :
    ∃ (κ : Type) (_ : Fintype κ) (T : κ → (∀ τ, U τ) → E) (u : κ → ∀ τ, U τ),
      (∀ k v, T k v ∈ 𝒞) ∧ (∀ k v, ∀ τ ∉ s, Ty τ (T k v)) ∧
      (∀ k v, ∀ τ ∉ s, ∀ w, T k (Function.update v τ w) = T k v) ∧
      (∀ k v, ∀ τ ∈ s, ∀ x y, T k (Function.update v τ (x + y)) =
        T k (Function.update v τ x) + T k (Function.update v τ y)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ (c : ℂ) x, T k (Function.update v τ (c • x)) = c • T k (Function.update v τ x)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ w Φ, R τ (v τ) w Φ → T k (Function.update v τ w) = Φ (T k v)) ∧
      ψ = ∑ k, T k (u k) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ _ => ψ, fun _ _ => 0, fun _ _ => hψ, fun _ _ τ _ => hTy τ,
      fun _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · simp
  | @insert τ₀ s hτ₀ ih =>
    obtain ⟨κ, hκ, T, u, hT𝒞, hTTy, hTfix, hTadd, hTsmul, hTR, hψs⟩ := ih

    refine ⟨κ × Fin (m τ₀), inferInstance, fun p v => A τ₀ p.2 (v τ₀) (T p.1 v),
      fun p => Function.update (u p.1) τ₀ (a τ₀ p.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p v
      exact hmaps _ _ _ _ (hT𝒞 _ _)
    · intro p v τ hτ
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      exact hkeep τ₀ p.2 (v τ₀) τ hne _ (hT𝒞 _ _) (hTTy _ _ τ hs)
    · intro p v τ hτ w
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) = A τ₀ p.2 (v τ₀) (T p.1 v)
      rw [Function.update_of_ne hne.symm, hTfix p.1 v τ hs w]
    · intro p v τ hτ x y
      show A τ₀ p.2 (Function.update v τ (x + y) τ₀) (T p.1 (Function.update v τ (x + y))) =
        A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x)) +
          A τ₀ p.2 (Function.update v τ y τ₀) (T p.1 (Function.update v τ y))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hadd' τ p.2 _ (hT𝒞 _ _) x y
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          Function.update_of_ne (Ne.symm h), hTadd p.1 v τ hs x y]
        exact hadd τ₀ p.2 (v τ₀) _ (hT𝒞 _ _) _ (hT𝒞 _ _)
    · intro p v τ hτ c x
      show A τ₀ p.2 (Function.update v τ (c • x) τ₀) (T p.1 (Function.update v τ (c • x))) =
        c • A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hsmul' τ p.2 _ (hT𝒞 _ _) c x
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          hTsmul p.1 v τ hs c x]
        exact hsmul τ₀ p.2 (v τ₀) c _ (hT𝒞 _ _)
    · intro p v τ hτ w Φ hRw
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) =
        Φ (A τ₀ p.2 (v τ₀) (T p.1 v))
      by_cases h : τ = τ₀
      · subst h
        rw [Function.update_self, hTfix p.1 v τ hτ₀]
        exact hR τ p.2 _ (hT𝒞 _ _) (v τ) w Φ hRw
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), hTR p.1 v τ hs w Φ hRw]
        exact (hcomm τ₀ p.2 (v τ₀) τ h (v τ) w Φ hRw _ (hT𝒞 _ _)).symm ▸ rfl
    ·
      have hterm : ∀ k, T k (u k) = ∑ j, A τ₀ j (a τ₀ j) (T k (u k)) := fun k =>
        hsum τ₀ _ (hT𝒞 _ _) (hTTy _ _ τ₀ hτ₀)
      rw [Fintype.sum_prod_type, hψs]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm k]
      refine Finset.sum_congr rfl fun j _ => ?_
      show A τ₀ j (a τ₀ j) (T k (u k)) =
        A τ₀ j (Function.update (u k) τ₀ (a τ₀ j) τ₀) (T k (Function.update (u k) τ₀ (a τ₀ j)))
      rw [Function.update_self, hTfix k (u k) τ₀ hτ₀]

theorem assemble_places : ∀ (D : D7) (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop), (∀ f ∈ 𝒞, Continuous f) → (∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N 𝒞 Ty τ) → ∀ ψ ∈ 𝒞, (∀ τ, Ty τ ψ) → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j v, T₀ j v ∈ 𝒞) ∧ (∀ j, ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = N.M.rep τ k (v τ) → T₀ j (Function.update v τ w) = rTr N.V (atTau θ N.V τ k) (T₀ j v)) ∧ (∀ j, ∀ τ, ∀ X ∈ lieAt N.V τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = dRep (N.M.rep τ) X (v τ) → T₀ j (Function.update v τ w) = Rder θ N.V τ X (T₀ j v)) ∧ ψ = ∑ j, T₀ j (u j) := by
  intro D θ N 𝒞 Ty hcont hdec ψ hψ hTy
  unfold GlobalTheory.KFinDecomp.DecompAt at hdec
  choose m a A hop hlin hsum using hdec

  have hK : ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, k ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := by
    intro τ k hk
    have hu : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (N.M.fr_unit τ)
    have h := (GlobalTheory.Chain.RealLine.Semi.conj_compact N.M τ (k := N.M.fr τ * k * (N.M.fr τ)⁻¹) hk).1
    have he : (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ = k :=
      calc (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ
          = ((N.M.fr τ)⁻¹ * N.M.fr τ) * k * ((N.M.fr τ)⁻¹ * N.M.fr τ) := by simp only [mul_assoc]
        _ = k := by rw [Matrix.nonsing_inv_mul _ hu, one_mul, mul_one]
    rwa [he] at h

  let R : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ →
      ((GA D N.V → ℂ) → (GA D N.V → ℂ)) → Prop := fun τ x y Φ =>
    (∃ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, (y : N.M.H τ) = N.M.rep τ k x ∧
        Φ = fun f => rTr N.V (atTau θ N.V τ k) f) ∨
      (∃ X ∈ lieAt N.V τ, (y : N.M.H τ) = dRep (N.M.rep τ) X x ∧ Φ = fun f => Rder θ N.V τ X f)
  have hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f) := by
    rintro τ j u τ' hne x y Φ (⟨k, hk, -, rfl⟩ | ⟨X, hX, -, rfl⟩) f hf
    · exact (hop τ j u).tr τ' hne k (hK τ' k hk) f hf
    · exact (hop τ j u).lie τ' hne X hX f hf
  have hRel : ∀ τ j, ∀ f ∈ 𝒞, ∀ x y Φ, R τ x y Φ → A τ j y f = Φ (A τ j x f) := by
    rintro τ j f hf x y Φ (⟨k, hk, hy, rfl⟩ | ⟨X, hX, hy, rfl⟩)
    · exact (hlin τ j f hf).2.2.1 k hk x y hy
    · exact (hlin τ j f hf).2.2.2 X hX x y hy
  obtain ⟨κ, hκ, T, u, hT𝒞, -, -, hTadd, hTsmul, hTR, hψT⟩ :=
    GlobalTheory.KFinDecomp.assemble_finset (U := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) 𝒞 Ty R m a A
      (fun τ j x f hf f' hf' => (hop τ j x).add f f' (hcont f hf) (hcont f' hf'))
      (fun τ j x c f hf => (hop τ j x).smul c f (hcont f hf))
      (fun τ j x f hf => (hop τ j x).maps f hf)
      (fun τ j x τ' hne f hf h' => (hop τ j x).keep τ' hne f hf h')
      hcomm
      (fun τ j f hf x x' => (hlin τ j f hf).1 x x')
      (fun τ j f hf c x => (hlin τ j f hf).2.1 c x)
      hRel hsum ψ hψ hTy Finset.univ

  let e := Fintype.equivFin κ
  let T₀ : Fin (Fintype.card κ) → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M := fun j =>
    (⟨T (e.symm j),
      fun v τ x y => by convert hTadd (e.symm j) v τ (Finset.mem_univ τ) x y,
      fun v τ c x => by convert hTsmul (e.symm j) v τ (Finset.mem_univ τ) c x⟩ :
      MultilinearMap (RingHom.id ℂ) (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) (GA D N.V → ℂ))
  refine ⟨Fintype.card κ, T₀, fun j => u (e.symm j), fun j v => hT𝒞 (e.symm j) v, ?_, ?_, ?_⟩
  · intro j τ k hk v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inl ⟨k, hk, hw, rfl⟩)
  · intro j τ X hX v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inr ⟨X, hX, hw, rfl⟩)
  · rw [hψT]
    exact (Equiv.sum_comp e.symm (fun k => T k (u k))).symm

end GlobalTheory.KFinDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVectorAdjointRowIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftDat

theorem rowAdj_isIntM_of_mem : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4 v hv
  rcases Nat.eq_zero_or_pos T.rank with h0 | hpos
  · intro i j; exact absurd j.2 (by omega)
  have hS : 0 < S.rank := lt_of_lt_of_le hpos hn
  let i0 : Fin S.rank := ⟨0, hS⟩
  let y : Matrix (Fin S.rank) (Fin T.rank) D.host.E := vecMulVec (Pi.single i0 1) v
  have hy : y ∈ tens (stdL D.host.E S.rank) C.X.Λ :=
    AddSubgroup.subset_closure ⟨_, Submodule.subset_span ⟨i0, rfl⟩, v, hv, rfl⟩
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hfin : finPart D (cA D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce])
  have hA : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) C.X.Λ,
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) C.X.Λ :=
    fun o z hz => GlobalTheory.LiftLevel.smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have h0 : finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
    rw [GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hy
  have hx : cA D e • finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) :=
    GlobalTheory.LiftLevel.smul_mem_hatA_of_int hA hfin h0
  have hhalf : IsHalf (cA D e) (cA D e • finW S T y) := fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hce]
  have hint := ((hgen _ hhalf).1).2 hx
  have hM : ∀ N : Matrix (Fin S.rank) (Fin T.rank) (EAf D),
      HMul.hMul βS.val (HMul.hMul (HMul.hMul (βS⁻¹).val N) βT.val) = HMul.hMul N βT.val := by
    intro N
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, βS.mul_inv, Matrix.one_mul]
  have key : ∀ j, GlobalTheory.LiftDat.rowAdj T βT a e v 0 j =
      GlobalTheory.LiftLevel.adjA S T βS βT a (cA D e • finW S T y) i0 j := by
    intro j
    simp only [GlobalTheory.LiftLevel.adjA, frMapAdj]
    rw [hM]
    simp only [GlobalTheory.LiftDat.rowAdj, Matrix.smul_apply, C.m.gS, inv_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    congr 1
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, finW, y, vecMulVec_apply, Pi.single_eq_same, one_mul, i0]
  intro i j
  rw [Fin.fin_one_eq_zero i, key]
  exact hint i0 j

end GlobalTheory.LiftDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulIdempotentHalfAtSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ (c : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D c → GlobalTheory.SplitHecke.Chart c v π → ∀ k : ℕ, 0 < k → (AddSubgroup.map (nsmulAddMonoidHom k) ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c) = Nat.card (v.adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : v.adicCompletionIntegers D.host.F)}) ^ (S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT
  letI := hS
  letI := hT
  exact GlobalTheory.HalfIndex.relIndex_nsmul_half S T ΛS ΛT inferInstance inferInstance
end

