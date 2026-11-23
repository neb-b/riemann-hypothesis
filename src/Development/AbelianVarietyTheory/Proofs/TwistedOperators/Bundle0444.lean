module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExOfSeparates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols Separates rowForm)

noncomputable section

namespace GlobalTheory.RowEx

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


set_option maxHeartbeats 1000000 in
theorem inj_of_sep_conv {ch : Choice R} (hM : R.IsModels) (hsep : Separates R ch.W ch.M ch.w ch.ρ ch.ξ)
    (hconv : ∀ a u, ConvK ch a u) (u : R.HE.H) (hu : ∀ a, psiK ch a u = 0) : u = 0 := by
  by_contra h0
  have hmem : R.HE.e u ∈ R.EEat R.triv := hM.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have hne : R.HE.e u ≠ 0 := fun h => h0 (hM.HE.1 (h.trans (map_zero _).symm))
  obtain ⟨Ψ, hΨ, Φ, -, hf⟩ := hsep _ hmem hne
  apply hf
  rw [← span_col_eq_cols ch Φ] at hΨ
  have key : ∀ x ∈ Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}),
      BplusConv ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) ∧
        Bplus ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : ch.Phi a = Φ := ha
      have h1 : FConv ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) := hconv a u
      have h2 : fPsiPhi ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) = 0 := hu a
      rw [ha'] at h1 h2
      exact ⟨h1.2, h2⟩
    | zero =>
      rw [LinearMap.map_zero (pairVec (coefPlus ch.G ch.W.θ) ch.ξ)]; exact bplusConv_zero ch.W ch.M _
    | add x y _ _ hx hy =>
      rw [LinearMap.map_add (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) x y]
      obtain ⟨hc, he⟩ := bplusConv_add ch.W ch.M hx.1 hy.1
      exact ⟨hc, by rw [he, hx.2, hy.2, add_zero]⟩
    | smul c x _ hx =>
      rw [LinearMap.map_smul (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) c x]
      obtain ⟨hc, he⟩ := bplusConv_smul ch.W ch.M c hx.1
      exact ⟨hc, by rw [he, hx.2, mul_zero]⟩
  exact (key Ψ hΨ).2


set_option maxHeartbeats 1000000 in
theorem isEx_of_separates (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate) (hL : LinB) (hB : BaseEx) : IsEx := by
  obtain ⟨C1, hL⟩ := hL
  obtain ⟨C2, hB⟩ := hB
  refine ⟨max 6510 (max C1 C2), fun ε CF hCF => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, hL⟩ := hL ε CF (le_trans (le_max_left _ _) (le_of_max_le_right hCF))
  obtain ⟨x3, hB⟩ := hB ε CF (le_trans (le_max_right _ _) (le_of_max_le_right hCF))
  refine ⟨max x1 (max x2 x3), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset G W hW S₀ => ?_⟩
  have hx1 : x1 ≤ large₂.sc.x := le_of_max_le_left hx
  have hx2 : x2 ≤ large₂.sc.x := le_trans (le_max_left _ _) (le_of_max_le_right hx)
  have hx3 : x3 ≤ large₂.sc.x := le_trans (le_max_right _ _) (le_of_max_le_right hx)
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS0, hbase⟩ := hB D large₂ hε hx3 Γ Pl0 T A Ks R F hset G W hW S₀
  obtain ⟨ρ', ξ', hsep⟩ := hS D large₂ hε hx1 hset.size hset.eser Γ Pl0 T A Ks R hset.core.lev hset.grp G W hbase.weil M
    hbase.vol _ hbase.w_ne
  have hconv := hL D large₂ hε hx2 Γ Pl0 T A Ks R F hset _ rfl (hbase.withReal ρ' ξ')
  exact ⟨M, ρ', ξ', cv, rm, S, rp, n, e, c, hS0,
    hbase.is_withReal (inj_of_sep_conv hset.core.models hsep hconv)⟩

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipMatch

section Generic

def pairM {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) : k := ∑ i, ∑ j, X i j * Y i j

def chart {k k' A C A' C' : Type} [Field k] [Field k'] [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    (j : k ≃+* k') (eA : A ≃ A') (eC : C ≃ C') (g : GL A k') (h : GL C k') (X : Matrix A C k) : Matrix A' C' k' :=
  reindex eA eC (g.val * X.map j * h.val)

def IsLocIso {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    (j : k ≃+* k') : Prop :=
  Continuous j ∧ Continuous j.symm ∧ ∀ x, j x ∈ (ValuativeRel.valuation k').integer ↔ x ∈ (ValuativeRel.valuation k).integer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coX {n d : ℕ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin d) (Fv F v) :=
  (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ

def coY (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Fin n) (Fin d) (Fv F v) :=
  -(b.1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (Y.J.map t)ᵀ * c.1)

def IsMixChart {n d : ℕ} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (A A' : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    {k R C : Type} [Add k] [Zero k] (co tr mu : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix R C k) (P : Finset C) : Prop :=
  (∀ u ∈ A, At (evFin F v) u ∧ (∀ r, ∀ s ∈ P, tr u r s = 0) ∧ (∀ r, ∀ s ∉ P, mu u r s = 0) ∧ co u = tr u + mu u) ∧
    ∀ u ∈ A', At (evFin F v) u ∧ (∀ r, ∀ s ∉ P, tr u r s = 0) ∧ ∀ r, ∀ s ∈ P, mu u r s = 0

end Generic

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def mixHalfS {i j : ℕ} (e : Num G i j) (ε : AE D) :
    Set (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :=
  {u | IsHalf ε (mulG (spW₁ G i j) (colV e u)ᵀ) ∧ IsHalf ε (adjV₁ e u)}

def mixCoS (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) :=
  fromCols (B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩
      ((mulG (spW₁ G i j) (colV e u)ᵀ).map fun a => cpt w (toEAf D a)))
    (B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩ ((adjV₁ e u).map fun a => cpt w (toEAf D a)))ᵀ

def colsEq (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) :
    Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ (locGrid G t w).Cols i j :=
  e.symm.trans (Equiv.sumCongr (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
    (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm))


variable (G) in
theorem rankW (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW G i j).rank = (locGrid G t w).rank (i + 1, j + 1) := by
  rw [rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ) + 1)) ⟨Nat.succ_le_of_lt i.2, Nat.succ_le_of_lt j.2⟩]


variable (G) in
theorem rankW₁ (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW₁ G i j).rank = (locGrid G t w).rank (i, j) := by
  rw [rank_vertex G t w (X := ((i : ℕ), (j : ℕ))) ⟨le_of_lt i.2, le_of_lt j.2⟩]

def IsPlaceIso {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E) (j : Fv D.host.F v ≃+* Kw w) : Prop :=
  ∀ a : AE D, j (piW τ a) = cpt w (toEAf D a)

def xiAt (w : Pl D.host.E) : Kw w := algebraMap D.host.E (Kw w) D.host.xi0

def basCols (B : Frames G) {i j : ℕ} (e : Num G i j) (w : Pl D.host.E) :
    Matrix (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w) :=
  GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val)

def IsDoublyCompatible (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop :=
  IsTied t i j e Bs Γ X ∧ Γ.V'.L = GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid i j))

end Grid

end GlobalTheory.FlipMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunOFockMovedVecTop
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowClaim

theorem isThetaFunO_fock_movedVec_top {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {j : ℕ} (hj : j < D.R.m)
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (t : T) (d : FinDatum G t (.top t j))
    (hd : S.Z.HasVec d) :
    IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (W.fock (.top t j) (movedVec t S d) Q) := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hω := W.om_is _ hr
  obtain ⟨f, hf⟩ := hd
  have hf0 : IsThetaFunO W.ψ _ _ f :=
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is hf ((S.Z.vac_is (.top t j) (show j + 1 ≤ D.R.m by omega)).2.theta)
  have hv : IsThetaFunO W.ψ _ _ (S.Z.vec d) := by
    rw [Normal.vec, FinDatum.vec_eq W hf]
    exact hω.om_pres _ _ hf0
  have hm : IsThetaFunO W.ψ _ _ (movedVec t S d) := hω.om_pres _ _ hv
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hm Q

theorem kerA_col_aut_cont : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (t : T), t ∈ U → ∀ (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    (∀ γ ∈ GQ (G.V (.top j)), ∀ g h, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) (γ * g) h =
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) g h) ∧
    ∀ z h, Continuous fun k : GinfC (G.V (.top j)) =>
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) (z * k) h := by
  intro D T L sc G W U S μ0 _ j hj Q t _ d hd
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hω := W.om_is _ hr
  have hF := isThetaFunO_fock_movedVec_top S hj Q t d hd
  refine ⟨fun γ hγ g h => ?_, fun z h => ?_⟩
  · show thetaKO (W.om (.top t j)) (γ * g) h _ = thetaKO (W.om (.top t j)) g h _
    have e : ((γ * g, h) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) = (γ, 1) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hF)
  · show Continuous fun k : GinfC (G.V (.top j)) => thetaKO (W.om (.top t j)) (z * k) h _
    exact (hω.om_cont _ hF 0).comp ((continuous_const.mul continuous_subtype_val).prodMk continuous_const)

end GlobalTheory.RowClaim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeyFinHolds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEx

theorem keyFin_holds : KeyFin := by
  classical
  intro P Ξ hΞ
  let U : Key P := {p | p.1 ∈ Ξ ∧ {w | ¬ p.1.UnrAt w}.Finite ∧ ∀ w ∈ p.2, ¬ p.1.UnrAt w}
  have hU : U.Finite := by
    refine (hΞ.biUnion (t := fun ξ => {p ∈ U | p.1 = ξ}) fun ξ _ => ?_).subset fun p hp => Set.mem_biUnion hp.1 ⟨hp, rfl⟩
    by_cases hf : {w | ¬ ξ.UnrAt w}.Finite
    · refine ((hf.toFinset.powerset.finite_toSet).image fun Q => (ξ, Q)).subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact ⟨Q, Finset.mem_coe.2 (Finset.mem_powerset.2 fun w hw => hf.mem_toFinset.2 (h.2.2 w hw)), rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact hf h.2.1
  refine ⟨{κ | κ ⊆ U}, hU.finite_subsets, ?_⟩
  rintro X T L μ₀ rfl hL h
  refine ⟨keyOf L, ?_, HEq.rfl⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨ξ, h1, h2⟩ := h t
  refine ⟨by rw [← eq_of_heq h2] at h1; exact h1, ?_, fun w hw => (hL.Q_ram t w).2 (Or.inl hw)⟩
  refine ((L.Q t).finite_toSet.union ((L.Q t).finite_toSet.image Formalism.DivisionValues.conjPl)).subset fun w hw => ?_
  rcases (hL.Q_ram t w).1 hw with h | ⟨w', h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨w', h, (GlobalTheory.GoodPrimes.isConjPl_iff.1 h').symm⟩

end GlobalTheory.RowEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LargeScaleSizesImplyGapConditions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sizeGap_of_sizes : SizeGap :=
  fun _ => ⟨0, fun _ large₂ _ _ h => GlobalTheory.RowSizes.sizes_of_sizeRows large₂ h⟩

end GlobalTheory.SepRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatAtVSelfDual
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.PsiUnrSelfDual

open GlobalTheory.InertSelfDual

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem latAtV_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr B.ψ v →
    (∀ z : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z →
      (z ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W v ↔ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W v,
        B.ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F G.V.J)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F G.W.J) z γ) = 1)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hunr z hz
  have hV := hT.geo.hV
  have hW := hT.geo.hW
  constructor
  · intro hzm γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V G.W _ _ _ _ hT.base hV hW v (-1) 1
      (by rw [map_one]; exact one_mem _) z hzm γ hγ
    simpa using h
  · intro hψ
    haveI := hT.base.unram
    obtain ⟨m, s, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
    obtain ⟨k, S, T, hS, hTm, hTS⟩ := exists_formFrame σ G.V.J (det_ne_zero_of_herm σ B hV) G.V.L hV.lat
      (fun y hy => (hV.dual y).2 fun x hx => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]; exact RingOfIntegers.isIntegral_coe r)
    obtain ⟨k', S', T', hS', hTm', hTS'⟩ := exists_formFrame σ G.W.J (det_ne_zero_of_skew σ B hW) G.W.L hW.lat
      (fun y hy => (hW.dual y).2 fun x hx o => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]
        exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
    set C := incM F (G.V.J * S.map σ)ᵀ * z * (incM F (G.W.J * S'.map σ)ᵀ)ᵀ with hC
    have hCat : ∀ j l, At (evFin F v) (C j l) := fun j l u hu => by
      have hz' : u • z = 0 := hz u hu
      have h1 : u • C = incM F (G.V.J * S.map σ)ᵀ * (u • z) * (incM F (G.W.J * S'.map σ)ᵀ)ᵀ := by
        rw [hC, Matrix.mul_smul, Matrix.smul_mul]
      rw [hz', Matrix.mul_zero, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 j) l
      simpa using this
    have hint : ∀ (e : E), IsIntegral ℤ e → ∀ j l, evFin F v (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
        (inclR (F := F) (AF F) (σ e) * C j l)) ∈ v.adicCompletionIntegers F := by
      intro e hei j l
      set M := incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l)) with hM
      set t := symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z M with ht
      have hx : (fun i => e * S i j) ∈ G.V.L := by
        have := G.V.L.smul_mem (⟨e, hei⟩ : 𝓞 E) (hS j)
        convert this using 1
        ext i; first | rfl | simp [Algebra.smul_def]
      have htat : At (evFin F v) t := fun u hu => by
        have := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V.J) (incM F G.W.J) (-1) u 1 z M
        rw [hz u hu, one_smul, mul_one, GlobalTheory.LatVacArith.symp_zero_left] at this
        exact this.symm
      have htC : t = -Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) (σ e) * C j l) := by
        rw [ht, symp, hM, hTens_frame, neg_one_mul, map_neg]
      have key : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v t * y) = 1 := by
        intro y hy
        have hmem : GlobalTheory.LatVac.liftV v y • M ∈ latAtV G.V G.W v :=
          AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v y, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hy,
            _, hx, _, hS' l, rfl⟩
        have h1 := hψ _ hmem
        have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V.J) (incM F G.W.J) (-1) 1 (GlobalTheory.LatVac.liftV v y) z M
        rw [one_smul, one_mul] at h2
        rw [h2] at h1
        have hat2 : At (evFin F v) (GlobalTheory.LatVac.liftV v y * t) := fun u hu => by
          have := htat u hu
          rw [smul_eq_mul] at this ⊢
          rw [mul_left_comm, this, mul_zero]
        rw [GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
        exact h1
      have := (hunr _).1 key
      rw [htC, map_neg] at this
      exact neg_mem_iff.1 this
    have hσ : Function.Bijective σ := AlgHom.bijective σ
    have hint' : ∀ i j l, evFin F v (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
        (inclR (F := F) (AF F) (c i : E) * C j l)) ∈ v.adicCompletionIntegers F := by
      intro i j l
      obtain ⟨e, he⟩ := hσ.2 (c i : E)
      have hei : IsIntegral ℤ e := by
        rw [← isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) hσ.1]
        show IsIntegral ℤ (σ e)
        rw [he]; exact RingOfIntegers.isIntegral_coe _
      have := hint e hei j l
      rwa [he] at this
    rw [decomp T (G.V.J * S.map σ)ᵀ T' (G.W.J * S'.map σ)ᵀ hTS hTS' z, ← hC]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun l _ => ?_
    rw [trace_expand s c hsc (C j l), Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨_, fun u hu => ?_, hint' i j l, fun r => (s i : E) * T r j, ?_, fun r => T' r l, hTm' l, ?_⟩
    · rw [smul_eq_mul, ← smul_eq_mul, ← map_smul, ← mul_smul_comm]
      have := hCat j l u hu
      rw [this, mul_zero, map_zero]
    · have := G.V.L.smul_mem (s i) (hTm j)
      convert this using 1
      ext r; simp [Algebra.smul_def]
    · rw [smul_assoc]
      congr 1
      ext p q
      simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, map_mul, smul_eq_mul]
      ring

end GlobalTheory.PsiUnrSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestChoiceDatumSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

namespace GlobalTheory.ChoiceSurjectivity

theorem choice_phi_surj : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (Φ : ch.G.Datum), ∃ a, ch.Phi a = Φ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F _ ch _ Φ
  obtain ⟨i⟩ := GlobalTheory.TestLat.SlopeModel.nonempty_idx (LaP ch.G)
  refine ⟨ch.e.symm ((Φ, Quotient.mk'' 1), i), ?_⟩
  simp [Choice.Phi, datumOf]

end GlobalTheory.ChoiceSurjectivity
end

