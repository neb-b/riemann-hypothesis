module

public import Mathlib
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCF
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0598
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixTarget

theorem om_pow_eq_snd {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)) (k : GA D V)
    (f : WO S V → ℂ) (c : ℂ) (hc : om (1, k) f = c • f) : ∀ m : ℕ, om (1, k ^ m) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    have e : (((1 : GA D S), k ^ (m + 1)) : GA D S × GA D V) = (1, k ^ m) * (1, k) := by
      rw [pow_succ, Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

def congGroup {D : D7} (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | GlobalTheory.Member.FinCong V N k}
  one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V N
  mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
  inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha

theorem isOpen_congGroup {D : D7} (V : HSp D) {N : ℕ} (hN : 0 < N) : IsOpen (congGroup V N : Set (GA D V)) :=
  Subgroup.isOpen_of_mem_nhds _ (g := 1) (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN)

end GlobalTheory.VacFixTarget

namespace GlobalTheory.VacFixTarget

open Formalism.L2.Fam.ThC (fixSig)

theorem isThetaFunO_fixSig {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ}
    (h : IsThetaFunO ψ S T f) : IsThetaFunO ψ (fixSig S) (fixSig T) f :=
  ⟨h.quasi, h.level, h.cont, h.smooth⟩

theorem isVacO_fixSig {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : IsVacO ψ θ (fixSig S) (fixSig T) sS sT LS LT f :=
  ⟨h.1, h.2.inf, isThetaFunO_fixSig h.2.theta, h.2.lat, h.2.fock, h.2.norm⟩

end GlobalTheory.VacFixTarget

namespace GlobalTheory.VacFixTarget

open GlobalTheory.Grid (neg)


set_option maxHeartbeats 1000000 in
theorem exists_open_fix_vac_target : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac := by
  intro D T L sc G W i j A A' WW X hX t
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
  have hvac : IsVacO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ X.vac := hX.is.isVac
  have hθ : IsInfFam W.θ := hvac.2.inf
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hone : ∀ κ : GA D WW, (X.ω t).toSgn true (1, κ) = X.ω t (1, κ) := fun κ => by
    simp [GlobalTheory.Grid.WRep.toSgn]
  have hev := (GlobalTheory.LatNhds.eventually_actO D (neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D (neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT)).1
  have hpair : Filter.Tendsto (fun x : GA D WW => (((1 : GA D (neg A)), x) : GA D (neg A) × GA D WW)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_const.prodMk continuous_id :
      Continuous fun x : GA D WW => (((1 : GA D (neg A)), x) : GA D (neg A) × GA D WW))).tendsto 1
    exact this
  have hev' := hpair.eventually hev
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC WW, GlobalTheory.Member.FinCong WW n.factorial x →
      ∀ u ∈ (latO (neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        actO (neg A) WW 1 x u ∈
          (latO (neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk hkc u hu hu' using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC WW, GlobalTheory.Member.FinCong WW n₁.factorial k →
      ∃ c : ℂ, ‖c‖ = 1 ∧ (X.ω t).toSgn true (1, k) X.vac = c • X.vac := by
    intro k hk hc
    have hΛ : ∀ u : WO (neg A) WW, u ∈ (latO (neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E))
        (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO (neg A) WW
        (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        u = actO (neg A) WW 1 k u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO (neg A) WW 1 k⁻¹ u, hn₁ k⁻¹ (inv_mem hk) (GlobalTheory.Member.PrincLevel.finCong_inv hc) u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO (1 : GA D (neg A)) k⁻¹ u
        rw [inv_inv, inv_one] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk hc u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hW hθ
      (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rW.s X.rW.s _ _ _ _ 1 k
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one (neg A) W.θ τ (-X.rA.s τ))
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ WW hk τ, Matrix.one_mul, Matrix.mul_one]) hΛ X.vac hvac
    exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig (neg A)) (Formalism.L2.Fam.ThC.fixSig WW)
      (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT X.rA.Λ X.rW.Λ
      hsdS hsdT X.vac _ (isVacO_fixSig hvac) (isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D WW => (X.ω t).toSgn true (1, k) X.vac w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_const.prodMk continuous_id)
  have key : ∃ n : ℕ, ∀ k ∈ GfC WW, GlobalTheory.Member.FinCong WW (n₁.factorial * n.factorial) k →
      (X.ω t).toSgn true (1, k) X.vac = X.vac := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, (X.ω t).toSgn true (1, k n ^ m) X.vac = c • X.vac ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (om_pow_eq_snd _ (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup WW (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup WW (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : (X.ω t).toSgn true ((1 : GA D (neg A)), (1 : GA D WW)) X.vac w₀ = X.vac w₀ := by
      show (X.ω t).toSgn true 1 X.vac w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖X.vac w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (X.vac w₀)]
  obtain ⟨n, hn⟩ := key
  refine ⟨congGroup WW (n₁.factorial * n.factorial),
    isOpen_congGroup WW (Nat.mul_pos n₁.factorial_pos n.factorial_pos), fun κ hU hκ => ?_⟩
  rw [← hone]
  exact hn κ hκ hU

end GlobalTheory.VacFixTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtCastMulReal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Move

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem integral_ker_move (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    {K : Subgroup (GL (Fin (G.V p.small).rank) (Lev.EAf D))} (hM : M.IsAt p.small K)
    (k : GA D (G.V p.small)) (k' : GA D (G.V p.big))
    (hk : MeasurePreserving (fun g : GA D (G.V p.small) => g * k) (M.ν p.small) (M.ν p.small))
    (hk' : Measurable fun g : GA D (G.V p.small) => g * k⁻¹)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (hF : ∀ γ ∈ GQ (G.V p.small), ∀ g, F (γ * g) = F g) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (h * k') * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p (W.om p (G.toPair p k k') f) g h * F (g * k) ∂M.ν p.small := by
  rw [← setIntegral_fd_mul_right M hM k hk hk' (fun g => W.ker p f g (h * k') * F g) ?_]
  · congr 1
    funext g
    rw [ker_mul]
  · intro γ hγ g
    have e := ker_rat_left W p hp f hf γ hγ 1 (one_mem _) g (h * k')
    rw [one_mul] at e
    simp only [e, hF γ hγ g]

theorem integral_ker_left (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (γ : GA D (G.V p.big)) (hγ : γ ∈ GQ (G.V p.big)) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (γ * h) * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p f g h * F g ∂M.ν p.small := by
  congr 1
  funext g
  have e := ker_rat_left W p hp f hf 1 (one_mem _) γ hγ g h
  rw [one_mul] at e
  rw [e]

end Move

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Paths

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem pathLift_column_leftInvariant (W : G.Weil) (M : Vol G) (t : T) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ γ ∈ GQ (G.V (.top n)), ∀ h,
      liftP W M (colPath t n) (colFam t n f) φ (γ * h) = liftP W M (colPath t n) (colFam t n f) φ h
  | 0, _, _, _, _, hφ, γ, hγ, h => hφ γ hγ h
  | n + 1, hn, f, hf, φ, _, γ, hγ, h => by
    show liftA W M (.col t n) (f (Fin.last n)) _ (γ * h) = liftA W M (.col t n) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.top t n) hn _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_row_leftInvariant (W : G.Weil) (M : Vol G) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ γ ∈ GQ (G.V (.grid n D.R.m)), ∀ h,
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (γ * h) = liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F h
  | 0, _, _, _, _, hF, γ, hγ, h => hF γ hγ h
  | n + 1, hn, f, hf, F, _, γ, hγ, h => by
    show liftA W M (.right n D.R.m) (f (Fin.last n)) _ (γ * h) = liftA W M (.right n D.R.m) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.chi n D.R.m) ⟨hn, le_rfl⟩ _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_column_translate (W : G.Weil) (M : Vol G) (t : T) (κ : ∀ n : ℕ, GA D (G.V (.top n))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ j, j < n → (∃ K, M.IsAt (.top j) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.top j)) => g * κ j) (M.ν (.top j)) (M.ν (.top j)) ∧
      Measurable (fun g : GA D (G.V (.top j)) => g * (κ j)⁻¹)) →
    ∀ (f f' : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    (∀ j : Fin n, W.om (.top t j) (G.toPair (.top t j) (κ j) (κ (j + 1))) (f j) = f' j) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ h, liftP W M (colPath t n) (colFam t n f) φ (h * κ n) =
      liftP W M (colPath t n) (colFam t n f') (fun x => φ (x * κ 0)) h := by
  intro n
  induction n with
  | zero =>
    intros
    rfl
  | succ n ih =>
    intro hn hκ f f' hf hff φ hφ h
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) φ) (h * κ (n + 1)) =
      liftA W M (.col t n) (f' (Fin.last n))
        (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) (fun x => φ (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.top t n) hn hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_column_leftInvariant W M t n (by omega) _ (fun j => hf j.castSucc) φ hφ) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [ih (by omega) (fun j hj => hκ j (by omega)) _ _ (fun j => hf j.castSucc)
      (fun j => hff j.castSucc) φ hφ g]
    rfl

theorem pathLift_row_translate (W : G.Weil) (M : Vol G) (κ : ∀ n : ℕ, GA D (G.V (.grid n D.R.m))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ i, i < n → (∃ K, M.IsAt (.grid i D.R.m) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.grid i D.R.m)) => g * κ i) (M.ν (.grid i D.R.m)) (M.ν (.grid i D.R.m)) ∧
      Measurable (fun g : GA D (G.V (.grid i D.R.m)) => g * (κ i)⁻¹)) →
    ∀ (f f' : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    (∀ i : Fin n, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (κ i) (κ (i + 1))) (f i) = f' i) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ h, liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (h * κ n) =
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f') (fun x => F (x * κ 0)) h := by
  intro n
  induction n with
  | zero =>
    intros
    rfl
  | succ n ih =>
    intro hn hκ f f' hf hff F hF h
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f i.castSucc) F)
        (h * κ (n + 1)) =
      liftA W M (.right n D.R.m) (f' (Fin.last n))
        (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f' i.castSucc) (fun x => F (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.chi n D.R.m) ⟨hn, le_rfl⟩ hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_row_leftInvariant W M n (by omega) _ (fun i => hf i.castSucc) F hF) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [ih (by omega) (fun i hi => hκ i (by omega)) _ _ (fun i => hf i.castSucc)
      (fun i => hff i.castSucc) F hF g]
    rfl

end Paths

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Coef

variable {D : D7}

theorem pairVec_mul_real {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) {k : GA D V}
    (hk : k ∈ GinfC V) (x : GA D V) :
    pairVec c (ξ ∘ₗ c.ρ k⁻¹) Ψ x = pairVec c ξ Ψ (x * k) := by
  have e : (finHom V).rangeRestrict (x * k) = (finHom V).rangeRestrict x := by
    have hk1 : (finHom V).rangeRestrict k = 1 := Subtype.ext (by simpa using MonoidHom.mem_ker.1 hk)
    rw [map_mul, hk1, mul_one]
  have h3 : c.ρ (x * k)⁻¹ = c.ρ k⁻¹ * c.ρ x⁻¹ := (congrArg c.ρ (mul_inv_rev x k)).trans (c.ρ.map_mul _ _)
  show ξ (c.ρ k⁻¹ (c.ρ x⁻¹ (Ψ ((finHom V).rangeRestrict x)))) =
    ξ (c.ρ (x * k)⁻¹ (Ψ ((finHom V).rangeRestrict (x * k))))
  exact (congrArg (fun A : Module.End ℂ c.W => ξ (A (Ψ ((finHom V).rangeRestrict x)))) h3.symm).trans
    (congrArg (fun z => ξ (c.ρ (x * k)⁻¹ (Ψ z))) e.symm)

theorem ext_cast_mul_real {X Y : LSp D} (e : X = Y) (c : CoefA Y.sp) (v : Bridge.Gf Y.sp → c.W) (η : Module.Dual ℂ c.W)
    {k : GA D X.sp} (hk : k ∈ GinfC X.sp) (g : GA D X.sp) :
    (η ∘ₗ c.ρ (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) k)⁻¹) (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g)) =
      η (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) (g * k))) := by
  subst e
  exact pairVec_mul_real c η v hk g

end Coef

section Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem formGen_mul_real (t : T) (y : (R.HX t).H) (η : Module.Dual ℂ R.cX.W) {k : GA D (ch.G.V (.grid 0 D.R.m))}
    (hk : k ∈ GinfC (ch.G.V (.grid 0 D.R.m))) (g : GA D (ch.G.V (.grid 0 D.R.m))) :
    formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) k)⁻¹) g =
      formGen ch t y η (g * k) :=
  ext_cast_mul_real (colY_m R.toLevCh) R.cX _ η hk g

end Gen

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameGramUnitaryIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.FinTransJet

theorem inV_stdL_eq_colLat {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    GlobalTheory.MovedDict.inV B (Formalism.MainNotions.StandardLatticesGL3.stdL D n) = (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) := by
  have hc := GlobalTheory.ColStd.colLat_comap_eq_stdLat B
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.L2.Pj.stdLat D.host.E n := hy
    rw [← hc] at hy'
    exact hy'
  · intro hx
    refine ⟨(B⁻¹ : GL (Fin n) D.host.E).1.mulVec x, ?_, ?_⟩
    · show _ ∈ Formalism.L2.Pj.stdLat D.host.E n
      rw [← hc, Submodule.mem_comap]
      simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]
      exact hx
    · simp only [Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]

end GlobalTheory.FinTransJet

namespace GlobalTheory.FinTransJet

end GlobalTheory.FinTransJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadingKernelsMatchCosetsThroughFrameStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeReading_kernels_match_cosets_through_frame : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
          ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C, (∃ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z) ∧
          ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (κ i).n,
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
              σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f z) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) := by
  first | exact @GlobalTheory.HeckeTerm.heckeTerm | exact GlobalTheory.HeckeTerm.heckeTerm | (intros; apply GlobalTheory.HeckeTerm.heckeTerm <;> assumption)
end
end

