module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJets
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0631

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVal

theorem givenLevel_inner {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) :
    ∀ p : ℕ × ℕ, 1 ≤ p.1 → 1 ≤ p.2 → givenLevel G t w p = KO (Kw w) _ := by
  rintro ⟨_ | a, _ | b⟩ h1 h2
  · simp at h1
  · simp at h1
  · simp at h2
  · rfl

theorem oneAt : Big fun ch => OneAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t Φ β hβ w hw0 i
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc w.2
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hcond : HasConductor (psiAt ch.W w.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w.1 w.2).square 0 hm 0 hm).cond
  have hce : depthAt ch.G w.1 = cosExp ch.G w.1 := by
    have e : 1 ≤ cosExp ch.G w.1 := by
      classical
      unfold cosExp
      rw [if_pos hw0]
      exact ch.G.pl.depth_pos _ _
    rw [depthAt, max_eq_left e]
  rw [hce] at hT
  haveI := (isUnitVol_unitVol w.1).1
  have hJ : ∀ j, 0 < j → j < (locGrid ch.G t w.1).m →
      givenLevel ch.G t w.1 ((locGrid ch.G t w.1).m, j) = KO (Kw w.1) _ := fun j hj hj' =>
    givenLevel_inner ch.G t w.1 _ (by change 1 ≤ D.R.m; omega) hj
  have key := OneCosetProof.oneCoset_of_isTensor (ν := unitVol w.1) one_le_sLen hcond hT hJ
  have hk : keepAt ch.G w.1 = false := by
    classical
    unfold keepAt
    simp [hw0]
  have hβw := hβ w
  rw [hk] at hβw
  exact key (β w) hβw i

end GlobalTheory.RowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestTopLevelLastIffGridVertexLevelVolumeOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastLevUnit

open GlobalTheory.FunObj.UnfModel GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx ValuativeRel

section Loc
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem symPr_of_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ} (hc : c = 0) (C : Subgroup (GL (n ⊕ Fin c) k)) :
    symPr C = C.comap (embX c) := by
  subst hc; exact symPr_zero C

theorem embX_frame_int {a c b : ℕ} (h : a + c = b) (z : GL (Fin a) k) :
    (∀ i j : Fin b, (embX c z).val ((frame h).symm i) ((frame h).symm j) ∈ 𝒪[k]) ↔ ∀ i j, z.val i j ∈ 𝒪[k] := by
  constructor
  · intro H i j
    have := H (frame h (.inl i)) (frame h (.inl j))
    simpa [embX] using this
  · intro H i j
    generalize (frame h).symm i = r
    generalize (frame h).symm j = s
    rcases r with r | r <;> rcases s with s | s <;> simp only [embX, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
    · exact H r s
    · exact zero_mem _
    · exact zero_mem _
    · rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _

theorem embX_mem_frame_KO {a c b : ℕ} (h : a + c = b) (x : GL (Fin a) k) :
    embX c x ∈ (KO k (Fin b)).map (frameGL (k := k) h).toMonoidHom ↔ x ∈ KO k (Fin a) := by
  rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, mem_KO_iff, mem_KO_iff, ← map_inv, ← map_inv]
  exact and_congr (embX_frame_int h x) (embX_frame_int h x⁻¹)

theorem symPr_conjLevel_last {Γ : Grid k} (hs : 1 ≤ Γ.s) (J : Γ.Level) (g : Γ.VertexGroup) {j : ℕ} (hj : j < Γ.m)
    (hlast : j + 1 = Γ.m) (hJ : J (Γ.m, j) = KO k _) (hg : g (Γ.m, j) = 1) :
    symPr (conjLevel hs J g hj) = KO k (Fin (topRank Γ j)) := by
  rw [symPr_of_eq_zero (by omega), conjLevel, hJ, hg]
  ext x
  rw [Subgroup.mem_comap, map_one]
  have e : Subgroup.map (MulEquiv.toMonoidHom (1 : MulAut (GL (Fin (Γ.rank (Γ.m, j))) k))) (KO k (Fin (Γ.rank (Γ.m, j)))) =
      KO k _ := Subgroup.map_id _
  rw [e]
  exact embX_mem_frame_KO _ x

end Loc
end GlobalTheory.LastLevUnit

namespace GlobalTheory.LastLevUnit

open GlobalTheory.FunObj.UnfModel GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx ValuativeRel GlobalTheory.FunObj.LevRowSucc

theorem elt_last {k : Type*} [Field k] {Γ : Grid k} {hs : 1 ≤ Γ.s} {J : Γ.Level} (ρ : Reps hs J) (β : Cosets hs J) {j : ℕ}
    (hj : j + 2 = Γ.m) : ρ.elt β (Γ.m, j + 1) = 1 := by
  rw [Reps.elt, onColumn_apply]
  dsimp only
  rw [dite_eq_right (by omega)]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem givenLevel_pos (G : GridData L sc) (t : T) (w : Pl D.host.E) :
    ∀ X : ℕ × ℕ, X.1 ≠ 0 → X.2 ≠ 0 → givenLevel G t w X = KO (Kw w) (Fin ((locGrid G t w).rank X))
  | (0, _), h, _ => absurd rfl h
  | (_ + 1, 0), _, h => absurd rfl h
  | (_ + 1, _ + 1), _, _ => rfl

theorem levTop_last_inf_UA {G : GridData L sc} (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (β : CosFam G t) (j : ℕ) (h : j + 1 < D.R.m) (hj : j + 2 = D.R.m) :
    S.levTop t Φ β (j + 1) h ⊓ UA D.sp.cm (G.V (.top (j + 1))).gram = G.levMax (.top (j + 1)) := by
  rw [GridData.levMax]
  exact prodLev_inf_UA (S.βp_is (j + 1) h.le) (G.isV (X := .top (j + 1)) h.le fun _ e => by cases e).sd (locPl G t) _ _
    fun w => symPr_conjLevel_last one_le_sLen (givenLevel G t w.1) ((repsAt G t w.1).elt (β w)) h (by show j + 1 + 1 = D.R.m; omega)
      (givenLevel_pos G t w.1 _ (by show D.R.m ≠ 0; omega) (by show j + 1 ≠ 0; omega)) (elt_last _ _ hj)

theorem levTop_inf_UA_levJ {G : GridData L sc} (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (β : CosFam G t) : ∀ n (h : n < D.R.m), n + 1 = D.R.m → 2 ≤ D.R.m →
    S.levTop t Φ β n h ⊓ UA D.sp.cm (G.V (.top n)).gram = levJ G t (.top n)
  | 0, _, h1, h2 => absurd h1 (by omega)
  | j + 1, h, h1, _ => levTop_last_inf_UA W S t Φ β j h (by omega)

theorem levTop_iff_levJ : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ β (h : D.R.m - 1 < D.R.m), 2 ≤ D.R.m → ∀ (k : FinPt ch.G (.top (D.R.m - 1))),
    finG (ch.G.V (.top (D.R.m - 1))) k ∈ ch.S.toGridChoice.levTop t Φ β (D.R.m - 1) h ↔
      finG (ch.G.V (.top (D.R.m - 1))) k ∈ levJ ch.G t (.top (D.R.m - 1)) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t Φ β h hm k => by
    have hU : finG (ch.G.V (.top (D.R.m - 1))) k ∈ UA D.sp.cm (ch.G.V (.top (D.R.m - 1))).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
    rw [← levTop_inf_UA_levJ ch.W ch.S.toGridChoice t Φ β (D.R.m - 1) h (by omega) hm]
    exact ⟨fun h' => ⟨h', hU⟩, fun h' => h'.1⟩⟩⟩

end GlobalTheory.LastLevUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticesDifferentiableOperator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct

open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedDict

theorem negGA_mem_GfC' {D : D7} (V : HSp D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem jetTab_heisO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → ∀ f : WO (G.pS p) (G.pT p) → ℂ,
    IsThetaFunO W.ψ _ _ f → ∀ w : WO (G.pS p) (G.pT p), ∀ (x : FinPt G p.small) (y : FinPt G p.big)
    (mon : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ),
    jetTab W B p (heisO W.ψ _ _ w f) x y mon = fockIn W B p (heisO W.ψ _ _ (actO _ _ (G.toPair p x y).1 (G.toPair p x y).2 w)
      (W.om p (G.toPair p x y) f)) (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) 0 := by
  intro D T L sc G W B p hp f hf w x y mon
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have mem : (G.toPair p x y).1 ∈ GfC (G.pS p) ∧ (G.toPair p x y).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC' _ y.2, x.2⟩
    | mu t i j => exact ⟨x.2, y.2⟩
    | core i => exact ⟨negGA_mem_GfC' _ y.2, x.2⟩
    | top t j => exact ⟨x.2, y.2⟩
  have hth := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all W.ψ_std hf w
  have e := GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om p) hom W.θ W.θ_is _ mem.1 _ mem.2
    (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) _ (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) hth
  rw [hom.om_heis _ _ w f hf] at e
  simp only [jetTab, GlobalTheory.FunObj.kerFin, GridData.Weil.ker, thetaKO, fockIn]
  rw [e]

theorem actO_nsmul {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T) (n : ℕ) (w : WO S T) :
    actO S T g h (n • w) = n • actO S T g h w := by
  unfold actO
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, Matrix.mul_add, Matrix.add_mul, ih]

end GlobalTheory.MovedDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDoubleStepFlatContractionExpand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DblStepLoc

theorem contr_flat_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (σ : ℕ) (B : GlobalTheory.Unf.BesLev D (σ + 1)) (J : GlobalTheory.Unf.JacLev D (σ + 1)) (B' : GlobalTheory.Unf.BesLev D σ) (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c : ℕ) (F : GlobalTheory.LocMod.Dbl p B J B' n₀ n₁ n₂ c) (s₁ : GlobalTheory.Unf.StepBF ψ B J) (s₂ : GlobalTheory.Unf.StepFB ψ J B') (l : GlobalTheory.Unf.Link B B'.L B'.ζ) (vL : GlobalTheory.Unf.VolM D B'.L.rank J.W₀.rank) T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k)) (c₁ : I → WO B.A J.W₀ →₀ ℂ) (c₂ : I → WO J.W₀ B'.A →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ F.F₀ F.F₁ (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ F.F₁ F.F₂ (c₂ i) (Ξ₂ i).1) → (∀ q, GlobalTheory.LocFlat.contr ψk ν (GlobalTheory.LocFlat.flCol ψk ν (σ + 1 + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ₂.1) q = ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2)) → GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ Φ₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ Φ₂)) = ∑ i ∈ S, x i • biComb ψ B.A J.W₀ B'.A (c₁ i) (c₂ i) (GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ O₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ O₂))) := by
  intro D k _ _ _ _ _ _ ν hν p ψ hstd ψk hchar hcond σ B J B' n₀ _ _ n₁ _ _ n₂ _ _ c F s₁ s₂ l vL T₁ T₂ hT₁ hT₂
    Φ₁ Φ₂ O₁ O₂ hO₁ hO₂ I S x Ξ₁ Ξ₂ c₁ c₂ hcomb hcontr
  have hcσ : c = 2 * σ := by have := F.bes.1; omega
  have hBF := GlobalTheory.FlatBFLoc.flatBF_of_laws D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  have hFB := GlobalTheory.LocMod.flatFB_holds D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  have hCL := GlobalTheory.ContrLocProof.contrLoc D GlobalTheory.LocFlat.contrFactor
  have hψc : Continuous ψk := hcond.continuous
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes p B F.s F.F₀ F.G₀ F.bes
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.LocMod.GValProof.core_of_bes p B' (F.s * p.xi) F.F₂ F.G₂ F.bes'
  have hjac : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := by
    rw [← GlobalTheory.LocMod.GValProof.hz_link p B B' l]; exact F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF k p ν hν.1 ψ ψk hchar (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁
    hC₀ F.bes F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB k p ν hν.1 ψ ψk hchar σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂
    hjac hC₂ F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL k p ν hν.1 ψ hstd ψk hchar (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂
    hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hfl := GlobalTheory.LocFlat.flat_SB_onto k ψk ν hψc hν.1
  have m₁ := fun Φ : GlobalTheory.SplitWeil.SB _ =>
    ((hfl n₁ n₀ (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 Φ.1 Φ.2
  have m₂ := fun Φ : GlobalTheory.SplitWeil.SB _ =>
    ((hfl n₂ n₁ (c + 1) (σ + 1) (by omega)).2 (by omega)).1 Φ.1 Φ.2
  let Ψ₁ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₁ Φ₁⟩
  let Ψ₂ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₂ Φ₂⟩
  let P₁ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₁ O₁⟩
  let P₂ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₂ O₂⟩
  rw [hU₁e Φ₁ Ψ₁ rfl, hU₂e Φ₂ Ψ₂ rfl, hU₁e O₁ P₁ rfl, hU₂e O₂ P₂ rfl]
  obtain ⟨Ξ, hΞ, e1⟩ := hΛe Ψ₁ Ψ₂
  obtain ⟨ΞO, hΞO, e2⟩ := hΛe P₁ P₂
  rw [e1, e2]
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator k ψk ν hcond hν
  let Q₁ : GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let Q₂ : GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  have hP₁ : P₁.1 = Set.indicator {x : Matrix n₁ (n₀ ⊕ Unit) k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer}
      fun _ => 1 := by
    simp only [P₁]
    rw [hO₁, (hun n₁ n₀ n₀ (c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)]
  have hP₂ : P₂.1 = Set.indicator {x : Matrix (n₂ ⊕ Unit) n₁ k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer}
      fun _ => 1 := by
    simp only [P₂]
    rw [hO₂, (hun n₂ n₁ n₀ (c + 1) (σ + 1)).2.1 (by omega) (by omega)]
  have hΞO' : ∀ q, ΞO.1 q = Q₁.1 q.1 * Q₂.1 q.2 := by
    intro q
    rw [hΞO, hP₁, hP₂]
    exact (hun n₁ n₀ n₂ 0 0).2.2 q
  let Pr : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k × Matrix n₂ n₁ k) := fun i => GlobalTheory.LocFlat.CFac.prodSB (Ξ₁ i) (Ξ₂ i)
  have hPr : ∀ i q, (Pr i).1 q = (Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2 := fun i q => rfl
  have hΞs : Ξ = ∑ i ∈ S, x i • Pr i := by
    apply Subtype.ext
    funext q
    rw [hΞ]
    refine (hcontr q).trans ?_
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hPr]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΞs, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul]
  congr 1
  exact (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ _ _ _).1 B.A J.W₀ B'.A F.F₀ F.F₁ F.F₂ Λ (c₁ i) (c₂ i) (Ξ₁ i) Q₁ (Ξ₂ i) Q₂
    (Pr i) ΞO hΛ (hcomb i hi).1 (hcomb i hi).2 rfl rfl (hPr i) hΞO'

end GlobalTheory.DblStepLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceScalarsMulEqOppositePathEdgeFactors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

namespace GlobalTheory.RowVacScalar


set_option maxHeartbeats 1000000 in
theorem splitScal_mul_eq_oppositePath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ w ∈ locPl G t, (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    GlobalTheory.RowVacScalar.splitScal G (.chi j D.R.m) w (G.toPair (.chi j D.R.m) 1 (moved S j k)).1
                 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 *
      GlobalTheory.RowVacScalar.splitScal G (.chi (j + 1) D.R.m) w (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 =
    ((oppositePath D.R.m).map ((locGrid G t w).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  intro D T L sc G W U S t ht j hj k hk w hw hs
  have hK : inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
      (finG (G.V (.grid (j + 1) D.R.m)) k) ∈ GlobalTheory.SplitWeil.KO (Kw w) _ := by
    have h1 := hk
    simp only [GridChoice.levRow, prodLev, Subgroup.mem_inf, Subgroup.mem_iInf] at h1
    have h2 := h1.1 ⟨w, hw⟩
    rw [Subgroup.mem_comap] at h2
    rwa [GlobalTheory.LastRowLat.givenLevel_inner G t w (j + 1, D.R.m) (by simp) (by simp; have := D.R.two_le_m; omega)] at h2
  have he : idemAt w * idemAt w = idemAt w := (Classical.epsilon_spec hs).1.1
  have d1 : ∀ V : HSp D, detIdl (idemAt w) V 1 = 1 := fun V => by
    unfold detIdl; split_ifs <;> simp
  have dneg : detIdl (idemAt w) (negSp (G.V (.grid (j + 1) D.R.m))) (negGA _ (moved S j k)) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := by
    refine Units.ext ?_
    rw [detIdl_val he, detIdl_val he, mt_negGA]
  have hpar : Odd (G.pS (.chi (j + 1) D.R.m)).rank ↔ Odd (G.pT (.chi j D.R.m)).rank := by
    have r0 := (rank_vertex G t w (X := (j, D.R.m)) ⟨by omega, le_rfl⟩).symm
    have r2 := (rank_vertex G t w (X := (j + 1 + 1, D.R.m)) ⟨by omega, le_rfl⟩).symm
    change Odd (G.V (.grid (j + 1 + 1) D.R.m)).rank ↔ Odd (G.V (.grid j D.R.m)).rank
    rw [r0, r2]
    simp only [Grid.rank, locGrid]
    rw [show D.R.r + D.R.m * D.R.t + (j + 1 + 1) * sLen D = (D.R.r + D.R.m * D.R.t + j * sLen D) + 2 * sLen D by ring]
    rw [Nat.odd_add]
    exact ⟨fun h => h.2 (even_two_mul _), fun h => ⟨fun _ => even_two_mul _, fun _ => h⟩⟩
  have key : ∀ (a b η : (AE D)ˣ →* Circle) (n n' : ℕ), (Odd n ↔ Odd n') → ∀ x,
      (Formalism.IndefR.Lift.attChr a η n x)⁻¹ * Formalism.IndefR.Lift.attChr b η n' x = (a x)⁻¹ * b x := by
    intro a b η n n' h x
    unfold Formalism.IndefR.Lift.attChr
    by_cases hn : Odd n
    · rw [if_pos hn, if_pos (h.1 hn), MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev, inv_inv,
        mul_comm (η x), mul_mul_mul_comm, mul_inv_cancel, mul_one]
    · rw [if_neg hn, if_neg (fun h' => hn (h.2 h'))]
  have hχ : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ y, ((G.ch.chi i (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((G.ch.chiH i).loc w y : ℂˣ) : ℂ) := fun i h1 h2 y => by
    have := congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq (G.ch.chi_eq i h1 h2) w)
    simpa [GlobalTheory.LFun.locChar] using this
  refine Eq.trans ?_ (_root_.GlobalTheory.OppositeEdges.oppositePath_prod_mulSingle (locGrid G t w) j hj _ hK).symm
  simp only [splitScal, GridData.toPair, splitFacO, map_one, d1, inv_one, one_mul, mul_one]
  have eqS : detIdl (idemAt w) (G.pS (Pair.chi j D.R.m)) ((negGA (G.V (Node.grid (j + 1) D.R.m))) (moved S j k)) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := dneg
  have eqT : detIdl (idemAt w) (G.pT (Pair.chi (j + 1) D.R.m)) (moved S j k) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := rfl
  rw [eqS, eqT, GlobalTheory.T.determinantIdeleAtSplitPlace_moved_gridNode S t j hj k w hs, ← Circle.coe_mul]
  rw [GridData.chrT, GridData.chrS]
  rw [key (G.chr (Pair.chi j D.R.m)) (G.chr (Pair.chi (j + 1) D.R.m)) L.eta _ _ hpar.symm]
  rw [Circle.coe_mul, Circle.coe_inv]
  dsimp only [GridData.chr]
  rw [hχ _ (by omega) (by omega), hχ _ (by omega) (by omega)]
  simp only [locGrid, Units.val_inv_eq_inv_val]
  exact mul_comm _ _

end GlobalTheory.RowVacScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareFlipEquivariantBlockDiagonalColumnSubstitu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.SquareFlipCols

theorem squareFlip_blockDiag_cols : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ψ ν ϖ e hϖ hψ he hν Φ hΦ M₁ hM₁ M₂ hM₂ X
  have h1 : fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) =
      fun Y => fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val) :=
    funext (_root_.GlobalTheory.BlockSubst.fourierSum_blockDiag_one ψ ϖ e hϖ hψ Φ hΦ M₁ hM₁ M₂ hM₂)
  have h2 : phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
      (fun Y => fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) =
      ((ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ)) • fun Z => phiA μ σ ν ϖ e
        (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)
          (Z * fromBlocks M₁.val 0 0 (invT M₂).val) :=
    funext fun Z => by rw [Pi.smul_apply, smul_eq_mul]; exact _root_.GlobalTheory.FrameSubst.phiA_blockSubst μ σ ν ϖ e _ M₁ hM₁ M₂ hM₂ Z
  have hd := GlobalTheory.FrameDepth.hasDepth_phiA (hμ := by assumption) k A A' (D₁ ⊕ D₂) μ σ ν ϖ e
    (blockUnits ϖ e (Assignment.one.block D₁ D₂)) _ hϖ he hν
    ((FourierDepth.fourier_exchange k A' (D₁ ⊕ D₂) ψ ϖ e _ hϖ hψ).1 Φ hΦ)
  have h3 : HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) (phiA μ σ ν ϖ e
      (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)) := by
    rw [← latA_blockLat]; exact hd
  unfold squareFlip
  rw [h1, h2, map_smul, Pi.smul_apply, smul_eq_mul,
    GlobalTheory.T.inversePartialFourierSum_comp_fromBlocks ψ⁻¹ ϖ e hϖ (hasConductor_inv hψ) _ h3 M₁ hM₁ M₂ hM₂ X]

end GlobalTheory.SquareFlipCols
end
end

