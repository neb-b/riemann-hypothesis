module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultTEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefPerEqGenPer
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def formGen (t : T) (y : (R.HX t).H) (η : Module.Dual ℂ R.cX.W) : Fn ch.G (.grid 0 D.R.m) := fun g =>
  η (R.cX.ext ((R.HX t).e y) (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) g))

def genPer (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H) (Q : PolCol ch.G × PolRow ch.G)
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) : ℂ :=
  defPer t ch.S.toGridChoice M Q d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (formGen ch t y η)

end Gen

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Gen2

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def GenConv (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H) (Q : PolCol ch.G × PolRow ch.G)
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) : Prop :=
  PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) ∧
    PathConv ch.W M (rowPath _ D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) (formGen ch t y η) ∧
    IntegrableOn (fun h => liftP ch.W M (colPath t D.R.m)
        (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j))
          (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (stabilizerEmbedding ch.G.sp.topDec h) *
        liftP ch.W M (rowPath _ D.R.m D.R.m)
          (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) (formGen ch t y η) h)
      (M.fd (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m))

end Gen2

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem mulSingle_ne {m : ℕ} (κ : GL (Fin (Γ.rank (0, m))) k) {X : ℕ × ℕ} (h : X ≠ (0, m)) :
    (Pi.mulSingle (0, m) κ : Γ.VertexGroup) X = 1 := Pi.mulSingle_eq_of_ne h _

theorem moveArgs_fill (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (x : ColArgs Γ) (y : RowArgs Γ)
    (e : Vars Γ) :
    Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (fill hs x y e) = fill hs x (Function.update y 0 ((κ⁻¹).val * y 0)) e := by
  funext b
  cases b with
  | theta i j =>
    by_cases h : i = Γ.m
    · subst h
      rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt, hm]), mulSingle_ne κ (by simp [Edge.src, hm])]
      simp [fill]
    · simp [moveArgs, fill, h]
  | ex i j =>
    by_cases hj : j = Γ.m
    · subst hj
      by_cases hi : i = 0
      · subst hi
        rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), fill_ex, fill_ex]
        simp only [Edge.src, Pi.mulSingle_eq_same, Function.update_self, map_one, inv_one, Units.val_one, Matrix.one_mul]
        rw [Matrix.transpose_mul, Assignment.read, invT_val]
      · rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), mulSingle_ne κ (by simp [Edge.src, hi])]
        simp [fill, Function.update_of_ne hi]
    · simp [moveArgs, fill, hj]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem moveArgs_mul (s : Assignment) (g g' : Γ.VertexGroup) (z : Γ.Args) :
    Γ.moveArgs s (g * g') z = Γ.moveArgs s g' (Γ.moveArgs s g z) := by
  funext b
  simp only [moveArgs, Pi.mul_apply, map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem mulSingle_comm (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) :
    Pi.mulSingle (0, Γ.m) κ * g = g * Pi.mulSingle (0, Γ.m) κ := by
  funext X
  by_cases h : X = (0, Γ.m)
  · subst h; simp [hg]
  · simp [Pi.mulSingle_eq_of_ne h]

theorem elt_zero_m (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) {J : Γ.Level} (ρ : Reps hs J) (β : Cosets hs J) : ρ.elt β (0, Γ.m) = 1 := by
  simp [Reps.elt, onColumn, Ne.symm hm]

theorem prod_edgeFactor (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod =
      Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) := by
  have h1 : ∀ b : Edge, b.src ≠ (0, Γ.m) → b.tgt ≠ (0, Γ.m) → Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) b = 1 := by
    intro b hs ht
    simp [edgeFactor, Pi.mulSingle_eq_of_ne hs, Pi.mulSingle_eq_of_ne ht]
  obtain ⟨n, hn⟩ : ∃ n, Γ.m = n + 1 := ⟨Γ.m - 1, by omega⟩
  rw [oppositePath, List.map_append, List.prod_append]
  have h2 : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src, hm]) (by simp [Edge.tgt, hm])
  rw [h2, mul_one]
  have h3 : List.range Γ.m = 0 :: (List.range n).map Nat.succ := by rw [hn, List.range_succ_eq_map]
  rw [h3, List.map_cons, List.map_cons, List.prod_cons]
  have h4 : ((((List.range n).map Nat.succ).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src]) (by simp [Edge.tgt])
  rw [h4, mul_one]

variable [MeasurableSpace k] [BorelSpace k]

theorem moved_law (keep : Bool) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) (κ : GL (Fin (Γ.rank (0, Γ.m))) k)
    (T : Γ.Args → ℂ) (c : ℂ) (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (z : Γ.Args) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
      moved Γ keep g T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) = c * moved Γ keep g T z := by
  have h1 := congrFun hlaw (Γ.moveArgs .one g z)
  simp only [pathAct, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : Γ.moveArgs .one g (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) =
      Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z) := by
    rw [← moveArgs_mul, ← moveArgs_mul, mulSingle_comm κ g hg]
  simp only [moved, pathAct, h2]
  calc _ = (if keep then (1 : ℂ) else (((charFactor Γ g)⁻¹ : ℂˣ) : ℂ)) * ((oppositePath Γ.m).map (Γ.edgeFactor .one g)).prod *
        (((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
          T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z))) := by ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}
  [MeasurableSpace k] [BorelSpace k]

theorem datum_law (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (ψ : AddChar k Circle) (ν : Measure k) {J : Γ.Level} (keep : Bool)
    (ρ : Reps hs J) (T : Γ.Args → ℂ) (β : Cosets hs J) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (c : ℂ)
    (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (x : ColArgs Γ) (y : RowArgs Γ) :
    Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) *
        (unfTerm ψ ν keep ρ T β).datum x (Function.update y 0 ((κ⁻¹).val * y 0)) =
      c * (unfTerm ψ ν keep ρ T β).datum x y := by
  simp only [unfTerm, flatTensor, flatIntegrand, ← moveArgs_fill hs hm κ x y]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  have h := moved_law keep (ρ.elt β) (elt_zero_m hs hm ρ β) κ T c hlaw (fill hs x y e)
  rw [prod_edgeFactor hm] at h
  simp only
  rw [← mul_assoc, h, mul_assoc]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def kapAt (S : GridChoice W U) (t : T) (w : Pl D.host.E) (k : FinPt G (.grid 0 D.R.m)) :
    GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w) :=
  inBasis (rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (S.B.β 0 D.R.m) w (finG (G.V (.grid 0 D.R.m)) k)

theorem edgeFactor_ne_zero {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : GlobalTheory.SplitFlip.Grid k) (g : Γ.VertexGroup) (b : GlobalTheory.SplitFlip.Edge) : Γ.edgeFactor .one g b ≠ 0 := by
  simp only [GlobalTheory.SplitFlip.Grid.edgeFactor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
    (GlobalTheory.SplitFlip.apow_ne_zero _ _)

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

theorem prod_update_comp {m : ℕ} {X : Fin m → Type} (F : ∀ i, X i → ℂ) (i₀ : Fin m) (f : X i₀ → X i₀) (ys : ∀ i, X i) :
    ∏ i, Function.update F i₀ (fun y => F i₀ (f y)) i (ys i) = ∏ i, F i (Function.update ys i₀ (f (ys i₀)) i) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem sum_update_comp {κ : Type} {m n : ℕ} {X : Fin n → Type} {Y : Fin m → Type} (τ : κ →₀ ℂ) (A : κ → ∀ j, X j → ℂ)
    (B : κ → ∀ i, Y i → ℂ) (i₀ : Fin m) (f : Y i₀ → Y i₀) (xs : ∀ j, X j) (ys : ∀ i, Y i) :
    (τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, Function.update (B d) i₀ (fun y => B d i₀ (f y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, B d i (Function.update ys i₀ (f (ys i₀)) i) :=
  Finset.sum_congr rfl fun d _ => by beta_reduce; rw [prod_update_comp]

theorem key_cancel (s PE PL P P' : ℂ) (h1 : PE ≠ 0) (h2 : s * PL = PE) (h3 : PE * P' = PL * P) : s * P' = P :=
  mul_left_cancel₀ h1 (by linear_combination s * h3 + P * h2)

end GlobalTheory.FirstRowTermLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainWeilDatumExtendsToStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.StepExists


set_option maxHeartbeats 1000000 in
theorem stepEx : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, StepEx D := by
  intro h1 h2 h3 h4 D c hc k hk s s' hs hs' ω f hpre
  obtain ⟨X, hX, -, -, hX3, hX4, hX5⟩ := _root_.GlobalTheory.RealPlaceTheta.exists_record_theta_all h1 h2
  have I : Inputs D X := _root_.GlobalTheory.PairLift.inputs_of_chosenSeries h1 h2 h3 h4 D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X I (_root_.GlobalTheory.PairLift.cuspAll_of_lowAll D X I (_root_.GlobalTheory.PairLift.lowAll_of_lowFock D X I (_root_.GlobalTheory.LowerMembersRule.lowFock D X I)))
  have hrule : ∀ τ, RulePar X (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ) := fun τ =>
    ((_root_.GlobalTheory.EvenOnto.upPair_arch h1 h2 D c.t _ _ _ _ (hpre.par τ)).2 X hX3 hX4 hX5).1
  have hwe : IsWeilExp c.ψ s.V s'.V (c.a k) (c.a k) ω :=
    ⟨c.χ k, c.χ k, hpre.weil, fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  obtain ⟨It, hIt⟩ := (_root_.GlobalTheory.EvenOnto.upPair_itW h1 h2 D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf
    hpre.par).1
  have hItW := hIt ω f hwe hpre.vac
  have hL := hPL s.par s'.par (c.a k) (c.a k) hrule s.V s'.V s.M s'.M c.θ c.ψ hc.inf ω hwe f It hpre.vac hItW
    s'.ν s'.fd hs'.haar hs'.fund f (isVacF_of_isVacVec hpre.vac)

  have hlev : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v h,
      IntegrableOn (fun g => thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) *
        (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g) s'.fd s'.ν ∧
      ∫ g in s'.fd, thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) * (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g ∂s'.ν =
        u (It φ v) h := by
    intro F
    obtain ⟨F', hF', hint⟩ := hL _ (GlobalTheory.ChainOnto.multT_le_noLevel c.θ s'.M _ _ F.2)
    refine ⟨F', ?_, hint⟩
    have hlaw : ∀ P v, ∀ κ ∈ s.J, ∀ g, F' (It P v) (g * κ) = F' (It P v) g := by
      intro P v κ hκ g
      rw [← (hint P v (g * κ)).2, ← (hint P v g).2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
      have hm : ((g * κ, g') : GA D s.V × GA D s'.V) = (g, g') * (κ, 1) := by simp
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply, hpre.law P κ hκ 1 (one_mem _)]
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s.V s.par s.M c.θ hc.inf _ _ (fun κ hκ => hs.fin hκ) F' hF' ?_
    intro w hw κ hκ g
    have hx := _root_.GlobalTheory.ItOnto.kfinSpan_le_span_it h1 h2 D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.a k) (c.a k) ω f It hc.inf hwe
      hpre.vac hItW hw
    suffices e : F' w (g * κ) = F' w g by rw [e]; simp
    clear hw
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨P, v, _, rfl⟩ := hx; exact hlaw P v κ hκ g
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
    | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]

  let pt : PolF D s'.V.rank s.V.rank →ₗ[ℂ] (WO s.V s'.V → ℂ) :=
    pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f
  have hp : ptOf c.ψ c.θ s.M s'.M f = pt := rfl
  have hint : ∀ F : s'.CC c, ∀ φ v g, IntegrableOn (fun h => (LinearMap.proj 0 ∘ₗ ω (g, h)) (pt φ) *
      (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v h) s'.fd s'.ν := fun F φ v g => by
    obtain ⟨u, -, hu⟩ := hlev F
    exact (hu φ v g).1
  obtain ⟨B, hB⟩ := GlobalTheory.Chain.IoLift.exists_trilinear s'.ν s'.fd (fun g h => LinearMap.proj 0 ∘ₗ ω (g, h)) pt
    (s'.CC c) hint
  have hex : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v, u (It φ v) = B φ v F := fun F => by
    obtain ⟨u, hu, he⟩ := hlev F
    refine ⟨u, hu, fun φ v => ?_⟩
    rw [hB]
    funext g
    exact ((he φ v g).2).symm
  have hun : ∀ u ∈ s.CC c, (∀ φ v, u (It φ v) = 0) → u = 0 := fun u hu h0 => by
    obtain ⟨φ, v, hne⟩ : ∃ φ v, It φ v ≠ 0 := by
      by_contra hn
      exact hItW.ne (LinearMap.ext₂ fun φ v => by_contra fun h => hn ⟨φ, v, h⟩)
    exact GlobalTheory.Grid.Sep.multT_eq_zero hu hne (h0 φ v)
  obtain ⟨io, hio⟩ := GlobalTheory.Chain.IoLift.ioExists_of_forall (T := It) (C' := s.CC c) hint B hB hex hun
  exact ⟨⟨ω, f, It, io⟩, rfl, rfl, ⟨hpre, hItW, hio⟩⟩

end GlobalTheory.EvenOnto.StepExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStepFockVectorsSphericalLatticeVac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.FockOff

theorem latO_le {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {p q : HeightOneSpectrum (𝓞 D.host.F) → Prop} (h : ∀ v, p v → q v) : latO S T LS LT p ≤ latO S T LS LT q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

end GlobalTheory.EvenOnto.FockOff


open GlobalTheory.EvenOnto.FockOff in
theorem GlobalTheory.EvenOnto.fock_sph_vac : ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ) := by
  intro D c hc k hk s s' hs hs' p hp φ
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  have hv := hp.pre.vac
  have hF : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) :=
    GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hv.theta hv.vac φ
  have hpt : ∀ φ', IsThetaFunO c.ψ s.V s'.V (p.pt φ') := fun φ' =>
    (GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hv.theta hv.vac φ').1
  have hle : latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      (fun v => v ∉ c.S) ≤ latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      fun _ => True := latO_le _ _ _ _ fun _ _ => trivial
  have fix : ∀ u ∈ latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      (fun v => v ∉ c.S), heisO c.ψ s.V s'.V u p.f = p.f → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hθ _ _ _ _ p.f hpt u
      (GlobalTheory.VacGood.infPart_latO (hle hu)) h0 φ
  have hsph := hp.pre.sph
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) :=
    ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hsph.1 u hu),
      fun e he u hu hh => fix u hu (hsph.2 e he u hu hh)⟩
  refine ⟨hF.1, hF, hS, fun v hv => ⟨hF.1, ?_, ?_⟩⟩
  · intro u hu
    exact hS.1 u (latO_le _ _ _ _ (fun w hw => hw ▸ hv) hu)
  · intro e he u hu hh
    exact hS.2 e he u (latO_le _ _ _ _ (fun w hw => hw ▸ hv) hu) hh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitChoose

theorem isUnit_two_of_not_mem : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    IsUnit (2 : v.adicCompletionIntegers F) := by
  intro F _ _ v h
  have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h
  rwa [map_ofNat] at this

theorem exists_admissible_unipotent_splitPlace_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v hv hψ h2 g hg
  obtain ⟨π₁, π₂, b₁, b₂, hP, hS⟩ := GlobalTheory.T.exists_local_dictionary_splitPlace σ B W r s hB hW v hv hψ
  exact GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt _root_.GlobalTheory.exists_dual_pair_isUnit_det_blocks σ W v hW.skew (isUnit_two_of_not_mem v h2) π₁ π₂ b₁ b₂ hP hS g hg

end GlobalTheory.SplitChoose
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingMemStabilizerAuxiliaryLatticeStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEmbedding_mem_stabilizer_auxiliaryLattice : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (y : GfC A), Lev.finE A y.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) Λ) → Lev.finE B (finEmb d y).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) := by
  first | exact @GlobalTheory.FinEmbLat.finEmb_mem_stabGL | exact GlobalTheory.FinEmbLat.finEmb_mem_stabGL | (intros; apply GlobalTheory.FinEmbLat.finEmb_mem_stabGL <;> assumption)
end
end

