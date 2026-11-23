module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnArrowRealAverageFunctional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.LastColAvg

theorem exps_chi : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ0 : T}, L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∃ (a b : D.what₂.Tau → ℚ) (e₁ e₂ : D.what₂.Tau → ℤ),
      (∀ τ, HasInfExp D (G.chrS (.chi i D.R.m : Pair T)) τ (a τ)) ∧ (∀ τ, HasInfExp D (G.chrT (.chi i D.R.m : Pair T)) τ (b τ)) ∧
      (∀ τ, (e₁ τ : ℚ) = a τ + sgnP (.chi i D.R.m : Pair T) * (G.pS (.chi i D.R.m : Pair T)).rank / 2) ∧
      (∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP (.chi i D.R.m : Pair T) * (G.pT (.chi i D.R.m : Pair T)).rank / 2)) := by
  intro D T L sc G μ0 hL i hi
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : ∀ τ, HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  have hatt : ∀ (n : ℕ) τ, HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
    intro n τ
    unfold Formalism.IndefR.Lift.attChr
    split_ifs
    · rw [sub_eq_add_neg]
      exact GlobalTheory.Chain.StepVac.hasInfExp_mul (h0 τ) (GlobalTheory.Chain.StepVac.hasInfExp_inv (GlobalTheory.SquareExps.eta_exp hL τ))
    · simpa using h0 τ
  refine ⟨fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pS (.chi i D.R.m : Pair T)).rank then 1 / 2 else 0,
    fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pT (.chi i D.R.m : Pair T)).rank then 1 / 2 else 0,
    fun τ => (cen D sc.cGap τ (D.R.m - i) : ℤ) - (((G.pS (.chi i D.R.m : Pair T)).rank + 1) / 2 : ℕ),
    fun τ => ((((G.pT (.chi i D.R.m : Pair T)).rank + 1) / 2 : ℕ) : ℤ) - (cen D sc.cGap τ (D.R.m - i) : ℤ),
    fun τ => hatt _ τ, fun τ => hatt _ τ, fun τ => ?_, fun τ => ?_⟩
  · simp only [sgnP]
    rcases Nat.even_or_odd (G.pS (.chi i D.R.m : Pair T)).rank with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
      push_cast; ring
    · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
      push_cast; ring
  · simp only [sgnP]
    rcases Nat.even_or_odd (G.pT (.chi i D.R.m : Pair T)).rank with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
      push_cast; ring
    · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
      push_cast; ring

theorem ker_fock_moved_fin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m → ∀ (t : T), t ∈ U → ∀ (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    ∀ (P : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank) (x : GA D (G.V (.grid i D.R.m))) (y : GA D (G.V (.grid (i + 1) D.R.m))),
    W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (movedVec t S d) P) x y =
      W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (S.Z.vec d) P) (x * (S.N.u (.grid i D.R.m)).1) (y * (S.N.u (.grid (i + 1) D.R.m)).1) := by
  intro D T L sc G W U S μ0 hL i hi t ht d hd P x y
  have hp : DefPair D.R.m (.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hn := DefPair.nodes hp
  have hom := W.om_is (.chi i D.R.m) (by
    simp only [DefPair, DefNode] at hp hn; simp only [Pair.InRange, Node.InRange]; omega)
  obtain ⟨h1, -⟩ := _root_.GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd
  have m1 : (G.toPair (.chi i D.R.m) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1).1 ∈
      GfC (G.pS (.chi i D.R.m : Pair T)) := negGA_mem_GfC _ (S.N.u _).2
  have m2 : (G.toPair (.chi i D.R.m) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1).2 ∈
      GfC (G.pT (.chi i D.R.m : Pair T)) := (S.N.u _).2
  have e : W.fock (.chi i D.R.m) (movedVec t S d) P =
      W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1)
        (W.fock (.chi i D.R.m) (S.Z.vec d) P) :=
    (GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ _ hom W.θ W.θ_is _ m1 _ m2 _ _ _ _ (S.Z.vec d) P h1).symm
  rw [e]
  unfold GridData.Weil.ker
  rw [GlobalTheory.RowClaim.toPair_mul]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem real_average : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∀ (Q : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank)
      (Λ : Module.Dual ℂ (VV ℂ (wt G (.grid i D.R.m)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid (i + 1) D.R.m))), ∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.grid i D.R.m))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.grid i D.R.m)) (h : GA D (G.V (.grid (i + 1) D.R.m))) (v : VV ℂ (wt G (.grid i D.R.m))),
        ∫ k, W.kerA (.right i D.R.m : Arrow T) (W.fock (.chi i D.R.m) (movedVec t S d) Q)
            ((x : GA D (G.V (.grid i D.R.m))) * (k : GA D (G.V (.grid i D.R.m)))) h *
            Λ (realAct W.θ S.N.fr (.grid i D.R.m) ((k : GA D (G.V (.grid i D.R.m)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.grid (i + 1) D.R.m) h⁻¹
            (fockComp W S.N.frC (.chi i D.R.m : Pair T) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  intro D T L sc G W U S μ0 hL i hi Q Λ
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := exps_chi G hL i hi
  obtain ⟨σ₀, hσf, hσr⟩ := _root_.GlobalTheory.FockFrameChange.exists_frame_change S hL i hi
  obtain ⟨Λ', hΛ'⟩ := _root_.GlobalTheory.RowHoweAvg.real_average_jet S hL i hi a b ha hb e₁ e₂ he₁ he₂ (σ₀ Q) Λ
  refine ⟨Λ', fun t ht d hd κ hκ hκp x h v => ?_⟩
  have hp : DefPair D.R.m (.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hh : h = ((finOf _ h : GfC (G.V (.grid (i + 1) D.R.m))) : GA D (G.V (.grid (i + 1) D.R.m))) *
      ((infOf _ h : GinfC (G.V (.grid (i + 1) D.R.m))) : GA D (G.V (.grid (i + 1) D.R.m))) := by
    rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC _ (infOf _ h).2 (finOf _ h).2, infOf_mul_finOf]
  let ℓ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] ℂ :=
    ((LinearMap.proj 0 : (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
      W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) ((x * S.N.u _ : FinPt G (.grid i D.R.m)) : GA D (G.V (.grid i D.R.m)))
        ((finOf _ h * S.N.u _ : FinPt G (.grid (i + 1) D.R.m)) : GA D (G.V (.grid (i + 1) D.R.m))))) ∘ₗ
      fockIn W S.N.frC (.chi i D.R.m) (S.Z.vec d)
  have key : ∀ k : GinfC (G.V (.grid i D.R.m)),
      W.kerA (.right i D.R.m : Arrow T) (W.fock (.chi i D.R.m) (movedVec t S d) Q)
        ((x : GA D (G.V (.grid i D.R.m))) * (k : GA D (G.V (.grid i D.R.m)))) h =
      realChar W (.chi i D.R.m) e₁ e₂ (k : GA D (G.V (.grid i D.R.m))) (infOf _ h : GA D (G.V (.grid (i + 1) D.R.m))) *
        ℓ (realSubst W S.N.frC (.chi i D.R.m) (k : GA D (G.V (.grid i D.R.m))) (infOf _ h : GA D (G.V (.grid (i + 1) D.R.m))) (σ₀ Q)) := by
    intro k
    show W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (movedVec t S d) Q) _ _ = _
    conv_lhs => rw [hh]
    rw [ker_fock_moved_real hL W S t hp d hd a b ha hb e₁ e₂ he₁ he₂ _ k.2 _ (infOf _ h).2 Q _ _,
      ker_fock_moved_fin S hL i hi t ht d hd, hσf t ht d hd, hσr _ k.2 _ (infOf _ h).2]
    rfl
  simp_rw [key]
  rw [hΛ' ℓ κ hκ hκp _ (infOf _ h).2 v]
  have hY : realAct W.θ S.N.fr (.grid (i + 1) D.R.m) h⁻¹ =
      realAct W.θ S.N.fr (.grid (i + 1) D.R.m) ((infOf _ h : GA D (G.V (.grid (i + 1) D.R.m))))⁻¹ := by
    conv_lhs => rw [hh]
    rw [mul_inv_rev, map_mul, realAct_fin _ _ _ (inv_mem (finOf _ h).2), mul_one]
  rw [hY]
  rfl

end GlobalTheory.LastColAvg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftCast
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

theorem left_cast {D : D7} {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
      φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact hφ

theorem gen_left : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch =>
    (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
    ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  refine ⟨fun a ξ γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g, fun t y η => ?_⟩
  have hm := hS.core.models
  exact left_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
    (fun γ hγ g => congrArg η
      (GlobalTheory.ThetaProjEquiv.ext_left R.cX ((R.HX t).e y) _ _ ((hm.HX t).2.1.le ⟨y, rfl⟩) γ hγ g))

end GlobalTheory.RowReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftGroupPointsPairTrivialShiftedTensorLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel.PairTriv

variable {D : D7}

theorem partAt_eq_smul {S T : HSp D} (a : AE D) (w : WO S T) : GlobalTheory.LiftLevel.partAt a w = a • w := by
  ext i j
  rfl

theorem hatA_tens_mono {S T : HSp D} (Λ : Lt D.host.E S.rank) {L L' : Lt D.host.E T.rank} (h : L ≤ L') :
    hatA S T (tens Λ L) ≤ hatA S T (tens Λ L') := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, y, hy, rfl⟩
  refine ⟨α, hα, y, ?_, rfl⟩
  refine (AddSubgroup.closure_mono ?_) hy
  rintro z ⟨v, hv, u, hu, rfl⟩
  exact ⟨v, hv, u, h hu, rfl⟩

theorem actO_back {S T : HSp D} (k : GA D S) (x : WO S T) : actO S T k 1 (actO S T k⁻¹ 1 x) = x := by
  have := GlobalTheory.WeilVacMove.actO_inv_actO (S := S) (T := T) k⁻¹ (1 : GA D T) x
  simpa using this

theorem pair_trivial : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), ∀ t ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1 := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg hodd e he a k₀ Λ' hab hmov hgen hmv Lv hLv u hu t ht
  have hsd : SelfD C.X (Lv.sh C.X.Λ) :=
    GlobalTheory.SW.Lev.selfD_idq Lv.ne_bot Lv.proper Lv.cop (GlobalTheory.SW.Lev.selfD_of_sympl C.sympl)
  have hV := GlobalTheory.SW.Base.stdL_mem_Vset (E := D.host.E) S.rank 1

  have hw : actO S T k₀⁻¹ 1 u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) :=
    (GlobalTheory.TensLatMove.mem_hatA_iff S T C.m.gS k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hmv
      (GlobalTheory.OneMapRef.Term.isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩

  obtain ⟨ht1, ht2, ht3⟩ := ht
  have hh0 : IsHalf (cA D e) (actO S T k₀⁻¹ 1 t) := GlobalTheory.WeilVacMove.isHalf_actO _ _ _ ht1
  have hfr := hmov.2.2 _ hh0
  rw [actO_back] at hfr
  have ht0 : actO S T k₀⁻¹ 1 t ∈ hatA S T (tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ)) :=
    ((hgen _ hh0).2).1 ⟨hfr ▸ ht2, fun PP hPP => hfr ▸ ht3 PP hPP⟩
  rw [← hLv] at ht0
  have ht0' := hatA_tens_mono (stdL D.host.E S.rank) (GlobalTheory.SW.Lev.smul_le_idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ) ht0
  have hF := _root_.GlobalTheory.FormMatch.forms_match D S T C
  set t₀ := actO S T k₀⁻¹ 1 t with ht₀
  set w := actO S T k₀⁻¹ 1 u with hw₀
  have et : t = actO S T k₀ 1 t₀ := (actO_back k₀ t).symm
  have eu : GlobalTheory.LiftLevel.partAt e u = actO S T k₀ 1 (e • w) := by
    rw [partAt_eq_smul, GlobalTheory.OneMapRef.Term.actO_smul, actO_back]
  have hhalf : cA D e • t₀ = t₀ := by
    ext i j
    exact hh0 i j
  have key : symplO S T t (GlobalTheory.LiftLevel.partAt e u) = symplO S T t₀ w := by
    rw [et, eu, hF.2.2.2.2.2.2.1, (hF.2.2.2.2.2.1 t₀ (e • w) 0).2, GlobalTheory.SplitScalar.symplO_smul, hhalf,
      ← (hF.2.2.2.2.2.1 t₀ w 0).2]
  rw [key]
  exact GlobalTheory.OneMapRef.Term.char_hatA C hV hsd t₀ ht0' w hw

end GlobalTheory.LiftLevel.PairTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralLeOfTsum
section
namespace I195MixedCoordinates_6e87f5aea1eb7b4a07c1c83e

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_6e87f5aea1eb7b4a07c1c83e

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FlatSup

theorem lintegral_le_of_tsum {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [ν.IsMulLeftInvariant] {𝓤 : Set G} (h : IsFundamentalDomain Γ 𝓤 ν)
    (h1 : ν 𝓤 = 1) (f : G → ENNReal) (hf : Measurable f) (B : ENNReal) (hB : ∀ u, ∑' γ : Γ, f (γ.1 * u) ≤ B) :
    ∫⁻ u, f u ∂ν ≤ B := by
  rw [h.lintegral_eq_tsum'' f, ← lintegral_tsum]
  · calc _ ≤ ∫⁻ _ in 𝓤, B ∂ν := lintegral_mono fun u => hB u
      _ = B := by rw [setLIntegral_const, h1, mul_one]
  · exact fun γ => (hf.comp (measurable_const_mul γ.1)).aemeasurable

theorem rat_cancel {D : D7} {m ρ : ℕ} {x : Matrix (Fin m) (Fin ρ) D.host.E} (hx : LinearIndependent D.host.E x.transpose)
    {a b : Mx D ρ ρ} (ha : a ∈ ratMx D ρ ρ) (hb : b ∈ ratMx D ρ ρ)
    (h : (rat x : Mx D m ρ) ⬝ a = (rat x : Mx D m ρ) ⬝ b) : a = b := by
  obtain ⟨a, rfl⟩ := mem_ratMx.1 ha
  obtain ⟨b, rfl⟩ := mem_ratMx.1 hb
  rw [← rat_mul, ← rat_mul] at h
  have h2 := rat_injective h
  have hi : Function.Injective x.mulVec := Matrix.mulVec_injective_iff.2 hx
  refine congrArg rat (Matrix.ext fun i j => ?_)
  have h3 : x *ᵥ (fun k => a k j) = x *ᵥ (fun k => b k j) := by
    funext l
    exact congrFun (congrFun h2 l) j
  exact congrFun (hi h3) i

theorem uni_bound (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (s : Step ψ V V₀ W W₀ ρ σ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : LinearIndependent D.host.E x.transpose)
    (Φ : WO V W → ℂ) (hΦ : IsThetaFunO ψ V W Φ) : ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ g h (w : WO V₀ W),
      ∫⁻ u : UX D ρ, ‖dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1) w‖ₑ ∂s.vU.ν ≤
        ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
  obtain ⟨C, A, hC⟩ := _root_.GlobalTheory.MixedAbsGrowth.mixed_abs_growth D ψ V W s.χV s.χW s.om s.weil V₀ ρ dV s.vS Φ hΦ
  obtain ⟨om', hW'⟩ := (_root_.GlobalTheory.Desc.weil_data_descend D ψ V W s.χV s.χW s.om s.weil).1 V₀ ρ dV
  have hMS := _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ V V₀ W ρ dV s.χV s.χW s.om om' s.weil hW' s.vS.μ s.vS.𝓕 s.vS.covol
  have hmix := (_root_.GlobalTheory.MixCont.mixed_coords_continuous D ψ V V₀ W W₀ ρ σ dV dW s.vS s.vT s.χV s.χW s.om s.weil Φ hΦ).1
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.UnitU.cocompact D ρ
  obtain ⟨c, hc⟩ := exists_height_le_of_isCompact V (hK.image (dV.continuous_levi.comp continuous_subtype_val))
  have hc'1 : 1 ≤ max c 1 := le_max_right _ _
  have hC₀0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0 * max c 1 ^ A, A, mul_nonneg hC₀0 (pow_nonneg (zero_le_one.trans hc'1) _), fun g h w => ?_⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : Countable (UXQ D ρ) := (GlobalTheory.UnitU.rational D ρ).1
  obtain ⟨hH, 𝓤, h𝓤, h1⟩ := s.vU.unit
  have hval : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hxu : Continuous fun u : UX D ρ => (rat x : Mx D W.rank ρ) ⬝ u.1.1 := continuous_const.matrix_mul hval
  refine lintegral_le_of_tsum (UXQ D ρ) s.vU.ν h𝓤 h1 _ ?_ _ fun u => ?_
  · have hf : Continuous fun u : UX D ρ => (((g, h), ((rat x : Mx D W.rank ρ) ⬝ u.1.1, w)) :
        (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) := continuous_const.prodMk (hxu.prodMk continuous_const)
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2.enorm.measurable
  · obtain ⟨γ₀, hγ₀, k, hk, rfl⟩ := hcov u
    have hp : ((dV.levi k.1 * g, h) : GA D V × GA D W) = (dV.levi k.1, 1) * (g, h) := by simp
    have hom : s.om (dV.levi k.1 * g, h) Φ = s.om (dV.levi k.1, 1) (s.om (g, h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    let φ : UXQ D ρ → ratMx D W.rank ρ := fun γ =>
      ⟨(rat x : Mx D W.rank ρ) ⬝ (γ.1 * γ₀).1.1, ratMx_mul (rat_mem x) (mul_mem γ.2 hγ₀).1⟩
    have hφ : Function.Injective φ := fun a b hab => by
      have h3 := rat_cancel hx (mul_mem a.2 hγ₀).1 (mul_mem b.2 hγ₀).1 (congrArg Subtype.val hab)
      exact Subtype.ext (mul_right_cancel (Subtype.ext (Units.ext h3)))
    have key : ∀ γ : UXQ D ρ, (_root_.I195MixedCoordinates_6e87f5aea1eb7b4a07c1c83e.source dV) W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ (γ.1 * (γ₀ * k)).1.1) =
        (_root_.I195MixedCoordinates_6e87f5aea1eb7b4a07c1c83e.source dV) W ψ s.vS.μ s.vS.𝓕 (s.om (dV.levi k.1 * g, h) Φ) (φ γ) := by
      intro γ
      change (_root_.I195MixedCoordinates_071817f88d1fbc2886640714.source dV) W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) _ = (_root_.I195MixedCoordinates_071817f88d1fbc2886640714.source dV) W ψ s.vS.μ s.vS.𝓕 (s.om (dV.levi k.1 * g, h) Φ) _
      rw [hom, GlobalTheory.Unf.TermLaw.mixS_levi_uni dV (hMS _ (s.weil.om_pres _ _ hΦ)) k.2, ← mul_assoc]
      congr 1
      exact (Matrix.mul_assoc _ _ _).symm
    change (∑' γ : UXQ D ρ, ‖(_root_.I195MixedCoordinates_6e87f5aea1eb7b4a07c1c83e.source dV) W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ (γ.1 * (γ₀ * k)).1.1) w‖ₑ) ≤ _
    simp_rw [show ∀ γ : UXQ D ρ, (_root_.I195MixedCoordinates_6e87f5aea1eb7b4a07c1c83e.source dV) W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ (γ.1 * (γ₀ * k)).1.1) w = (_root_.I195MixedCoordinates_6e87f5aea1eb7b4a07c1c83e.source dV) W ψ s.vS.μ s.vS.𝓕 (s.om (dV.levi k.1 * g, h) Φ) (φ γ) w from fun γ => congrFun (key γ) w]
    refine (ENNReal.tsum_comp_le_tsum_of_injective hφ
      (fun y : ratMx D W.rank ρ => ‖dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (dV.levi k.1 * g, h) Φ) y w‖ₑ)).trans
      ((hC _ h w).trans (ENNReal.ofReal_le_ofReal ?_))
    have hk' : height V (dV.levi k.1) ≤ max c 1 := (hc _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
    have hkg : height V (dV.levi k.1 * g) ≤ max c 1 * height V g :=
      (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right hk' (height_pos V g).le)
    have hx0 : 0 ≤ height V (dV.levi k.1 * g) * height W h := mul_nonneg (height_pos V _).le (height_pos W h).le
    have hx1 : height V (dV.levi k.1 * g) * height W h ≤ max c 1 * (height V g * height W h) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkg (height_pos W h).le
    calc C * (height V (dV.levi k.1 * g) * height W h) ^ A ≤ max C 0 * (height V (dV.levi k.1 * g) * height W h) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx0 _)
      _ ≤ max C 0 * (max c 1 * (height V g * height W h)) ^ A :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 _) hC₀0
      _ = _ := by rw [mul_pow, mul_assoc]

theorem sfinite_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (ν : Measure G) [ν.IsHaarMeasure] : SFinite ν := inferInstance

theorem sfinite_fin {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν] : SFinite ν := inferInstance

theorem flat_sup_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h y w, ‖flatS dV dW s (rat x) y (s.om (g, h) Φ) w‖ ≤ C * (height V g * height W h) ^ A := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x hx Φ hΦ
  obtain ⟨C, A, hC0, hC⟩ := uni_bound D ψ V V₀ W W₀ ρ σ dV dW s x hx Φ hΦ
  refine ⟨C, A, fun g h y w => ?_⟩
  have hn : ∀ a, ‖ψ a‖ = 1 := s.weil.std.1.2.1
  have hne : ∀ a, ‖ψ a‖ₑ = 1 := fun a => by rw [← ofReal_norm, hn, ENNReal.ofReal_one]
  have hmix := (_root_.GlobalTheory.MixCont.mixed_coords_continuous D ψ V V₀ W W₀ ρ σ dV dW s.vS s.vT s.χV s.χW s.om s.weil Φ hΦ).1
  have hT := s.vT.covol
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  obtain ⟨j1, j2, j3, j4, -⟩ := lattice_Mx D σ V₀.rank
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D σ V₀.rank) := ⟨rfl⟩
  haveI := s.vU.unit.1
  haveI : IsFiniteMeasure (s.vT.μ.restrict s.vT.𝓕) := ⟨by rw [Measure.restrict_apply_univ, hT.2.2]; exact ENNReal.one_lt_top⟩
  haveI := sfinite_haar s.vU.ν
  haveI := sfinite_fin (s.vT.μ.restrict s.vT.𝓕)
  let F : UX D ρ → Mx D σ V₀.rank → ENNReal := fun u ξ =>
    ‖dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1) (dW.incX V₀ ξ + dW.incAdj V₀ y + dW.inc0 V₀ w)‖ₑ
  have hval : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hxu : Continuous fun u : UX D ρ => (rat x : Mx D W.rank ρ) ⬝ u.1.1 := continuous_const.matrix_mul hval
  have hX : Continuous (dW.incX V₀) := continuous_const.matrix_mul continuous_id
  have hFm : Measurable (Function.uncurry F) := by
    have hf : Continuous fun p : UX D ρ × Mx D σ V₀.rank => (((g, h), ((rat x : Mx D W.rank ρ) ⬝ p.1.1.1,
        dW.incX V₀ p.2 + dW.incAdj V₀ y + dW.inc0 V₀ w)) : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk
        (((hX.comp continuous_snd).add continuous_const).add continuous_const))
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2.enorm.measurable
  have h1 : ∀ u : UX D ρ, ‖flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (rat x) y (s.om (g, h) Φ) w u‖ₑ ≤
      ∫⁻ ξ in s.vT.𝓕, F u ξ ∂s.vT.μ := by
    intro u
    unfold flatFun evalAt
    have e1 : ‖star (psiUni ψ u.1)‖ₑ = 1 := by
      rw [← ofReal_norm, norm_star, show ‖psiUni ψ u.1‖ = 1 from hn _, ENNReal.ofReal_one]
    rw [enorm_mul, e1, one_mul]
    unfold _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun ξ => le_of_eq ?_)
    simp only [F]
    change ‖heisO ψ V₀ W (dW.incX V₀ ξ) (heisO ψ V₀ W (dW.incAdj V₀ y) (heisO ψ V₀ W (dW.inc0 V₀ w) (dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1)))) 0‖ₑ = _
    rw [dW.integrandT_eq, enorm_mul, hne, one_mul]
  have h2 : ‖flatS dV dW s (rat x) y (s.om (g, h) Φ) w‖ₑ ≤ ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
    unfold flatS flatAt
    refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono h1).trans ?_)
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    calc _ ≤ ∫⁻ _ in s.vT.𝓕, ENNReal.ofReal (C * (height V g * height W h) ^ A) ∂s.vT.μ :=
          lintegral_mono fun ξ => hC g h _
      _ = _ := by rw [setLIntegral_const, hT.2.2, mul_one]
  rw [← ofReal_norm] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 (pow_nonneg
    (mul_nonneg (height_pos V g).le (height_pos W h).le) _))).1 h2

end GlobalTheory.FlatSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPlaceModelLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor


open GlobalTheory.SplitLinear GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.VecInv in
open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm in
theorem om_placeModel_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (e a : AE D), IsSplitIdem D e → e + cA D e = idem D (.inl v) → (a = e ∨ a = cA D e) → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∃ r : ℝ, 0 < r ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = ((r : ℂ) * ((splitFacO χS χT x y : Circle) : ℂ)) • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ hW hB v e a he _ ha Tm hTm g h hg hh x y hx hy
  have orth : ∀ b : AE D, IsSplitIdem D b → GlobalTheory.PlaceModelSum.IsOrthSum b := fun b hb =>
    ⟨Unit, {()}, fun _ => b, fun _ _ => hb, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => b) ()).symm⟩
  have ho := orth e he
  rcases ha with ha | ha
  · rw [ha] at hTm ⊢
    refine ⟨modFac S T x y, modFac_pos S T x y, fun Φ hΦ => ?_⟩
    rw [law_orth hW hB.2.2.1 hB.2.2.2.1 ho he.2.1 (base_theta hB) hB.2.2.2.2.2.lat one_ne_zero hTm hg hh hx hy Φ hΦ,
      fac, mul_comm]
  · rw [ha] at hTm ⊢
    have ho' := ho.conj
    have sc : ∀ (V : HSp D) (k : GA D V), SuppAt e V k → SuppAt (cA D e) V k := fun V k hk i j => by
      rw [GlobalTheory.SplitOnto.cA_cA, add_comm]; exact hk i j
    have dx := det_conj ho'.idem hx
    have dy := det_conj ho'.idem hy
    refine ⟨modFac S T (detAt _ ho'.idem S g) (detAt _ ho'.idem T h), modFac_pos S T _ _, fun Φ hΦ => ?_⟩
    rw [law_orth hW hB.2.2.1 hB.2.2.2.1 ho' (by rw [GlobalTheory.SplitOnto.cA_cA, mul_comm, he.2.1]) (base_theta hB)
      hB.2.2.2.2.2.lat one_ne_zero hTm (sc S g hg) (sc T h hh) (isDetAt_detAt _ ho'.idem S g)
      (isDetAt_detAt _ ho'.idem T h) Φ hΦ, fac, mul_comm, splitFacO, splitFacO,
      GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resT _ _ dx, GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resS _ _ dy]

end GlobalTheory.PlaceTensor
end

