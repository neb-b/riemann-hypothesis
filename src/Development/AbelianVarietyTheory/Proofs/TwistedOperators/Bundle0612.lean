module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierIndexRationalPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

theorem std_eq_colLat_one' {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

theorem even_bot' {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

theorem vac_jet_ne_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hX : IsBottomTri W i j X) :
    ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac
      (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set f : WO A WW → ℂ := fun w => starRingEnd ℂ (X.vac w) with hfdef
  have hf0 : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s X.rA.Λ X.rW.Λ f :=
    GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
  have hf : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s (colLat (1 : GL (Fin A.rank) D.host.E) : Set _)
      (colLat (1 : GL (Fin WW.rank) D.host.E) : Set _) f := by
    rw [← std_eq_colLat_one' X.rA.Λ hX.std.2.1, ← std_eq_colLat_one' X.rW.Λ hX.stdW.2.1]
    exact hf0
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin A.rank) D.host.E).1 * A.gram *
      (1 : GL (Fin A.rank) D.host.E).1 = 1 := by
    rw [hX.std.1]
    simp [Formalism.UG.cT]
  have hW : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin WW.rank) D.host.E).1 * WW.gram *
      (1 : GL (Fin WW.rank) D.host.E).1 = 1 := by
    rw [hX.stdW.1]
    simp [Formalism.UG.cT]
  have hcA : ∀ τ, IsCartanInv (gramAt D A τ) (X.rA.s τ) := fun τ => (hIs.rigA.2.2 τ).1
  have hcW : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hIs.rigW.2.2 τ).1
  have hBA : (fun τ => (1 : GL (Fin A.rank) D.host.E).1.map (tauE D τ)) = X.rA.B := by
    funext τ
    rw [(hX.std.2.2 τ).2]
    simp
  have hBW : (fun τ => (1 : GL (Fin WW.rank) D.host.E).1.map (tauE D τ)) = X.rW.B := by
    funext τ
    rw [(hX.stdW.2.2 τ).2]
    simp
  obtain ⟨δ, hC, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex D.host.ccK δ hC).1
  obtain ⟨e0, he0, he0ne⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hC t0 ht0 A.rank WW.rank (even_bot' hX)
  obtain ⟨c, hc⟩ := GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ
    ht0 e0 he0 f hf
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D he0.1.1 he0ne
  refine ⟨α, ?_⟩
  change pureTensorO W.ψ W.θ (negSp A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial α 1) 0 ≠ 0
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial W.ψ W.θ A WW X.rA.s X.rW.s X.rA.B X.rW.B X.vac hψ hθ α 0, map_ne_zero,
    ← hBA, ← hBW, hc α, GlobalTheory.FockPos.applyAt0_monomial']
  have hprod : (α.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  exact mul_ne_zero c.ne_zero (mul_ne_zero hprod (mul_ne_zero hfac hα))

end GlobalTheory.MovedJetNZ

end

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

end GlobalTheory.MovedJetNZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingVacuumTranslateSource
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.VacTranslateLeft

theorem exists_open_fix_translate_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∀ u : WO S T, u.map (infPart D) = 0 →
    ∃ U : Subgroup (GA D S), IsOpen (U : Set (GA D S)) ∧ ∀ κ ∈ U, κ ∈ GfC S →
      heisO ψ S T (actO S T κ 1 u) f₀ = heisO ψ S T u f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT hS hT f₀ hvac u hu
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO'
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) u hu
  have hN : 0 < 2 * (2 * 2) * M * M := by positivity
  have hev := GlobalTheory.LatNhds.eventually_move S T ΛS ΛT hS hT u hu (2 * (2 * 2) * M * M) hN
  have hc : Filter.Tendsto (fun κ : GA D S => (κ, (1 : GA D T))) (𝓝 1) (𝓝 1) := by
    have := (continuous_id.prodMk (continuous_const (y := (1 : GA D T)))).tendsto (1 : GA D S)
    simpa only [Prod.mk_one_one, id] using this
  have hev' := hc.eventually hev
  have key : ∃ n : ℕ, ∀ κ ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial κ →
      ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T κ 1 u = u + (2 * (2 * 2) * M * M) • l := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    obtain ⟨l, hl, e⟩ := hn
    exact hkne n l hl e
  obtain ⟨n, hn⟩ := key
  refine ⟨GlobalTheory.VacFixTarget.congGroup S n.factorial, GlobalTheory.VacFixTarget.isOpen_congGroup S n.factorial_pos,
    fun κ hκc hκ => ?_⟩
  obtain ⟨l, hl, e⟩ := hn κ hκ hκc
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have e2 : (2 * (2 * 2) * M * M) • l = 2 • ((2 * 2) • (M • (M • l))) := by
    simp only [smul_smul]
    congr 1
    ring
  have hu' : (2 * 2) • (M • (M • l)) ∈
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :=
    AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hl M) M) _
  have hs : ψ (symplOH S T u (2 • ((2 * 2) • (M • (M • l))))) = 1 := by
    rw [two_nsmul, GlobalTheory.SplitScalar.symplOH_add_right, GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.Mem.CoefInv.symplO_nsmul,
      ← GlobalTheory.Mem.CoefInv.symplO_nsmul, smul_comm M (2 * 2) u]
    exact GlobalTheory.VacTranslate.psi_four_eq_one hvac.2.lat.1 hw₀ hMu (AddSubgroup.nsmul_mem _ hl M)
  have h := GlobalTheory.SplitScalar.heisO_heisO ψ S T u (2 • ((2 * 2) • (M • (M • l)))) f₀
  rw [hvac.2.lat.1 _ hu', hs, one_smul] at h
  rw [e, e2, h]

end GlobalTheory.VacTranslateLeft

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupFixesVacuumDefiniteBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixSource

theorem om_pow_eq_fst {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)) (k : GA D S)
    (f : WO S V → ℂ) (c : ℂ) (hc : om (k, 1) f = c • f) : ∀ m : ℕ, om (k ^ m, 1) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    have e : ((k ^ (m + 1), (1 : GA D V)) : GA D S × GA D V) = (k ^ m, 1) * (k, 1) := by
      rw [pow_succ, Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]


set_option maxHeartbeats 1000000 in
theorem exists_open_fix_vac_source : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' → X.ω' t (κ, 1) X.vac' = X.vac' := by
  intro D T L sc G W i j A A' WW X hX t
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  have hvac : IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ X.vac' := hX.is.isVac'
  have hθ : IsInfFam W.θ := hvac.2.inf
  have hsdS : IsSelfDualC A' X.rA'.Λ := hX.is.rigA'.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hcS : ∀ τ, IsCartanInv (gramAt D A' τ) (X.rA'.s τ) := fun τ => (hX.is.rigA'.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hev := (GlobalTheory.LatNhds.eventually_actO D A' WW X.rA'.Λ X.rW.Λ hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D A' WW X.rA'.Λ X.rW.Λ hsdS hsdT)).1
  have hpair : Filter.Tendsto (fun x : GA D A' => ((x, (1 : GA D WW)) : GA D A' × GA D WW)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const :
      Continuous fun x : GA D A' => ((x, (1 : GA D WW)) : GA D A' × GA D WW))).tendsto 1
    exact this
  have hev' := hpair.eventually hev
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC A', GlobalTheory.Member.FinCong A' n.factorial x →
      ∀ u ∈ (latO A' WW (X.rA'.Λ : Set (Fin A'.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        actO A' WW x 1 u ∈
          (latO A' WW (X.rA'.Λ : Set (Fin A'.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk hkc u hu hu' using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC A', GlobalTheory.Member.FinCong A' n₁.factorial k →
      ∃ c : ℂ, ‖c‖ = 1 ∧ X.ω' t (k, 1) X.vac' = c • X.vac' := by
    intro k hk hc
    have hΛ : ∀ u : WO A' WW, u ∈ (latO A' WW (X.rA'.Λ : Set (Fin A'.rank → D.host.E))
        (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO A' WW
        (X.rA'.Λ : Set (Fin A'.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        u = actO A' WW k 1 u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO A' WW k⁻¹ 1 u, hn₁ k⁻¹ (inv_mem hk) (GlobalTheory.Member.PrincLevel.finCong_inv hc) u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ (1 : GA D WW) u
        rw [inv_inv, inv_one] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk hc u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ A' WW _ _ (X.ω' t) hW hθ
      X.rA'.s X.rA'.s X.rW.s X.rW.s _ _ _ _ k 1
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ A' hk τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one WW W.θ τ (X.rW.s τ)) hΛ X.vac' hvac
    exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig A') (Formalism.L2.Fam.ThC.fixSig WW)
      X.rA'.s X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT X.rA'.Λ X.rW.Λ
      hsdS hsdT X.vac' _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D A' => X.ω' t (k, 1) X.vac' w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_id.prodMk continuous_const)
  have key : ∃ n : ℕ, ∀ k ∈ GfC A', GlobalTheory.Member.FinCong A' (n₁.factorial * n.factorial) k →
      X.ω' t (k, 1) X.vac' = X.vac' := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, X.ω' t (k n ^ m, 1) X.vac' = c • X.vac' ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (om_pow_eq_fst _ (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup A' (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup A' (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : X.ω' t ((1 : GA D A'), (1 : GA D WW)) X.vac' w₀ = X.vac' w₀ := by
      show X.ω' t 1 X.vac' w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖X.vac' w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (X.vac' w₀)]
  obtain ⟨n, hn⟩ := key
  exact ⟨GlobalTheory.VacFixTarget.congGroup A' (n₁.factorial * n.factorial),
    GlobalTheory.VacFixTarget.isOpen_congGroup A' (Nat.mul_pos n₁.factorial_pos n.factorial_pos), fun κ hU hκ => hn κ hκ hU⟩

end GlobalTheory.VacFixSource
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPlacesEmbedding
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.SplitSphLeft

theorem vac_unique_split_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M.vac v))) →
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) →
        ∃ c : ℂ, φ = c • G.M.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v hs hψv θ _ hvac φ hφ hfix
  classical
  have hat : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  let cf : latAtV G.V G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (G.M.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • f)) →
      ∀ γ : latAtV G.V G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) f = cf γ • f := by
    intro f hf h γ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h γ γ.2 r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) ↔
      ∀ l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ (latAtV G.V G.W v) hat
      (fun z hz => GlobalTheory.T.splitPlace_tensorLattice_selfDual F E σ B hTr.base G.V G.W _ _ _ _ hTr.geo.hV hTr.geo.hW v hs hψv z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v),
      t • l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v G.M.co hTr.geo.hV.lat.toIsLattice hTr.geo.hW.lat.toIsLattice
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := _root_.GlobalTheory.selfDual_exists_snd_of_orth v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun γ : latAtV G.V G.W v => GlobalTheory.LatVac.locCo G.M.co v γ) cf
    (fun u hu => ?_) φ (G.M.vac v) (hloc φ hφ hfix) (hloc _ (hTr.geo.hM.vac v).1 hvac) (hTr.geo.hM.vac v).2.1
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

theorem isUnram_of_unramified' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
  intro P hP
  rw [Ideal.ramificationIdx_eq_one_iff]
  infer_instance

end GlobalTheory.SplitSphLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameTestFunctionTransposeIntegralGLMulEqChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.FFunLeftInv
open GlobalTheory.SplitFlip

theorem fFun_transpose_mul_of_mem_KO : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (u : GL A k), u ∈ KO k A → ∀ h : GL D k,
      (ν (gdet u) : ℂ) * fFun μ σ ν Ψ (u.valᵀ * (X0 k σ * (invT h).val)) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ A A' D _ _ _ _ _ _ μ _ σ ν Ψ u hu h
  classical
  let P : Matrix A A k → Matrix D D k := fun X => (fromBlocks X 0 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm
  have hP : ∀ X Y, P X * P Y = P (X * Y) := fun X Y => by
    simp only [P, Matrix.submatrix_mul_equiv, fromBlocks_multiply]; simp
  have hP1 : P 1 = 1 := by simp [P, fromBlocks_one]
  let m : GL D k := ⟨P u.valᵀ, P (u⁻¹).valᵀ, by rw [hP, ← transpose_mul, Units.inv_mul, transpose_one, hP1],
    by rw [hP, ← transpose_mul, Units.mul_inv, transpose_one, hP1]⟩
  set h' : GL D k := invT m * h with hh'
  have e1 : u.valᵀ * (X0 k σ * (invT h).val) = X0 k σ * (invT h').val := by
    rw [hh', map_mul, invT_invT, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 1
    ext i j
    rw [frameMatrixFirstColumnBlock_mul_apply]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [m, P, X0, Matrix.mul_apply, eq_comm]
  have e2 : Y0 k σ * h'.val = Y0 k σ * h.val := by
    rw [hh', Units.val_mul, ← Matrix.mul_assoc]
    congr 1
    ext i j
    rw [invT_val]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [m, P, Y0, Matrix.mul_apply, eq_comm]
    rw [Matrix.one_apply]
    simp [eq_comm]
  have e3 : gdet h' = (gdet u)⁻¹ * gdet h := by
    rw [hh', gdet_mul, gdet_invT]
    congr 2
    ext
    simp [m, P, Matrix.GeneralLinearGroup.val_det_apply, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
  have hv : valuation k ((gdet u)⁻¹ : kˣ) = 1 := by
    rw [← map_inv]; exact valuation_gdet_of_mem_KO (inv_mem hu)
  rw [e1, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, e2, e3, apow_mul, apow_of_valuation_eq_one hv, map_mul, Units.val_mul, map_inv]
  have : (ν (gdet u) : ℂ) * ((ν (gdet u))⁻¹ : ℂˣ) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination ((ν (gdet h) : ℂ) * apow (gdet h) ((Fintype.card D : ℂ) / 2) * smallF μ ν Ψ (Y0 k σ * h.val)) * this

end GlobalTheory.FFunLeftInv
end

