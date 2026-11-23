module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.StdHalfLat

variable {D : D7}

theorem idemSum_mul_eq_zero {P P' : Finset (Pl D.host.E)} {e e' : AE D} (he : IsIdemSum e P) (he' : IsIdemSum e' P')
    (hPP : ∀ w ∈ P, ∀ w' ∈ P', w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w') : e * (e' + cA D e') = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := he'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨h1, h2⟩ := hPP w hw w' hw'
  rw [mul_add, Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h1,
    Formalism.IndefR.Fin.idem_orth_conj (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h2, add_zero]

theorem ne_and_not_conj {S : Finset ℕ} {w w' : Pl D.host.E} (hw : ¬ Off S w) (hw' : Off S w') :
    w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w' := by
  unfold Off at hw hw'
  push_neg at hw
  obtain ⟨q, hq, hqw⟩ := hw
  refine ⟨fun h => hw' q hq (h ▸ hqw), fun h => ?_⟩
  obtain ⟨c', hc', hc'eq⟩ := h _ hqw
  apply hw' q hq
  have : c' = (q : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [hc'eq]
    simp
  rwa [this] at hc'

theorem actO_eq_self_of_half {S T : HSp D} {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0)
    {g : GA D S} {h : GA D T} (hg : SuppAt a S g) (hh : SuppAt b T h) {x : WO S T} (hx : IsHalf e x) :
    actO S T g h x = x := by
  have hx' : ∀ c : AE D, e * c = 0 → (1 - c) • x = x := fun c hc => by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← hx i j, ← mul_assoc, sub_mul, one_mul, mul_comm c e, hc, sub_zero]
  unfold actO
  have k1 : HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    conv_lhs => rw [← hx' _ hb]
    rw [Matrix.mul_smul, ← Matrix.smul_mul, GlobalTheory.SplitScalar.off_smul_mt hh, Matrix.smul_mul, Matrix.one_mul, hx' _ hb]
  rw [k1]
  conv_lhs => rw [← hx' _ ha]
  rw [Matrix.smul_mul, ← Matrix.mul_smul, GlobalTheory.SplitScalar.off_smul_mt_inv hg, Matrix.mul_smul, Matrix.mul_one, hx' _ ha]

theorem suppAt_inv' {a : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt a V g) : SuppAt a V g⁻¹ := by
  have h := GlobalTheory.SplitScalar.off_smul_mt_inv hg
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero] at h
  exact fun i j => (congrFun (congrFun h i) j).symm

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem actO_mem_latO_of_hat {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    {u : WO S T} (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    exact GlobalTheory.AdelicLatMove.rankOne_mem_latO S T ΛS' ΛT' a ha _
      (hS _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (hT _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_of_half {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hS' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS',
      (mt S g⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    (hT' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT',
      (mt T h⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT)
    {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0) (hg : SuppAt a S g) (hh : SuppAt b T h)
    {x : WO S T} (hx : IsHalf e x) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      x ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  constructor
  · intro hm
    have := actO_mem_latO_of_hat g h hS hT hm
    rwa [actO_eq_self_of_half ha hb hg hh hx] at this
  · intro hm
    have := actO_mem_latO_of_hat g⁻¹ h⁻¹ hS' hT' hm
    rwa [actO_eq_self_of_half ha hb (suppAt_inv' hg) (suppAt_inv' hh) hx] at this

theorem half_nsmul {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := fun i j => by
  have h := hx i j
  simp only [Matrix.smul_apply, nsmul_eq_mul]
  linear_combination (k : AE D) * h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem hat_moves {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {X : Node} (hX : DefNode D.R.m X) :
    (∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)),
      (mt (G.V X) (N.u X).1).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X)) ∧
    ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X),
      (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)) := by
  refine ⟨fun v hv => (N.u_lat X hX v).1 hv, fun v hv => (N.u_lat X hX _).2 ?_⟩
  have e : (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1).1 *ᵥ ((mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v) = v := by
    rw [show (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) = (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1⁻¹).1 from rfl,
      Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [e]
  exact hv

theorem exists_kill {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {t : T} (ht : t ∈ U) {p : Pair T} (d : FinDatum G t p) {X : Node} (hX : DefNode D.R.m X) :
    ∃ a : AE D, d.e * (a + cA D a) = 0 ∧ SuppAt a (G.V X) (N.u X).1 := by
  obtain ⟨P', e', he', hsupp, hoff⟩ := N.u_supp X hX
  refine ⟨e', idemSum_mul_eq_zero d.e_is he' fun w hw w' hw' => ne_and_not_conj ?_ (hoff w' hw'), hsupp⟩
  intro hw0
  have h3 := N.off w hw0
  rcases d.P_over w hw with h | ⟨w'', hw'', h⟩
  · exact h3.1 h
  · exact h3.2.1 t ht w'' hw'' h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.LastVertexMove

open GlobalTheory.StdHalfLat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem isSBHalf_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p,
    d.P = locPl G t → IsSBHalf d.e (stdLat S p) d.fn := by
  intro D T L sc G W U S t ht p hp d _
  have key : ∀ x, IsHalf d.e x →
      (x ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) (fun _ => True) ↔ x ∈ stdLat S p) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hp.nodes
    rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h2
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h1
      have m2 := hat_moves S.N h2
      have m1 := hat_moves S.N h1
      exact (mem_latO_iff_of_half (negGA _ (S.N.u (.grid (i + 1) j)).1) (S.N.u (.grid i j)).1
        m2.1 (fun v hv => by rw [← map_inv]; exact m2.2 v hv) m1.1 m1.2 ha hb hga hgb hx).symm
    · exact hp.elim
    · exact hp.elim
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h1
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h2
      have m1 := hat_moves S.N h1
      have m2 := hat_moves S.N h2
      exact (mem_latO_iff_of_half (S.N.u (.top j)).1 (S.N.u (.top (j + 1))).1
        m1.1 m1.2 m2.1 m2.2 ha hb hga hgb hx).symm
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := d.sb
  refine ⟨hsupp, k, hk, fun u hu hub y => hinv u ((key u hub).2 hu) hub y, fun y hy => ?_⟩
  exact (key _ (half_nsmul (hsupp y hy) k)).1 (hfin y hy)

end GlobalTheory.LastVertexMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainIntertwinersRowZeroUnitVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin.RowArrows

theorem vY_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) {k : ℕ} (hk : k + 1 < D.R.m) : R.vY t k ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D k) (Yc D (k + 1)) // a.map (infPart D) = 0} => heisO R.ψ _ _ a (R.vac k)) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ hk)) (h.chain.vY t k hk)

theorem vX_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) : R.vX t ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D (D.R.m - 1)) D.sp.X' // a.map (infPart D) = 0} => heisO R.ψ _ _ a R.vacX) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by have := D.R.two_le_m; omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ h.lev.βX) (h.chain.vX t)

theorem chainIntertwiners_rowZero_unitVacua : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → IsItW R.θ (GlobalTheory.Grid.row0 R j).M (GlobalTheory.Grid.row0 R (j + 1)).M (GlobalTheory.Grid.th0 R t j).ω (GlobalTheory.Grid.fock R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac) (GlobalTheory.Grid.th0 R t j).It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F h _ G' W _ G _ _ _ _ t j hj
  unfold GlobalTheory.Grid.th0
  by_cases h1 : j + 1 < D.R.m
  · rw [dite_eq_left h1]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepY R t j)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R h1))
    have hω := h.chain.ωY t j h1
    rw [GlobalTheory.Grid.chrStep_eq_muAt] at hω
    exact (hc.2 ⟨hω, (h.chain.vY t j h1).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vY t j h1).1.2.theta (vY_mem_span_core h t h1) (h.chain.ItY t j h1)⟩).intw
  · have h2 : j + 1 = D.R.m := by omega
    rw [dite_eq_right h1, dite_eq_left h2]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepX R t)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_pred_eq_chainVertexAtRowZero_last R h2) (GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R h1))
    have hω := h.chain.ωX t
    rw [(congrArg _ h2.symm).trans (GlobalTheory.Grid.chrStep_eq_muAt R t j)] at hω
    exact (hc.2 ⟨hω, (h.chain.vX t).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vX t).1.2.theta (vX_mem_span_core h t) (h.chain.ItX t)⟩).intw

end GlobalTheory.GridJoin.RowArrows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlaceIdealMulLatticeCompletionEq
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

namespace GlobalTheory.ConjPlaceLat


set_option maxHeartbeats 1000000 in
theorem cA_mul_mem_latV_smul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (w : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e w →
  ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (𝔪 : Ideal (𝓞 D.host.E)), (∃ m ∈ 𝔪, m ∉ (Formalism.DivisionValues.conjPl w).asIdeal) →
  ∀ z : Fin S.rank → AE D, z ∈ latV S L (· = p.v) → (fun i => cA D p.e * z i) ∈ latV S (𝔪 • L) (· = p.v) := by
  intro D k _ _ _ _ p w hw S L 𝔪 hm z hz
  obtain ⟨m, hm𝔪, hmw⟩ := hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmw (Ideal.zero_mem _)
  have hmE : (m : D.host.E) ≠ 0 := by exact_mod_cast hm0
  have hc := GlobalTheory.SplitHeckeAdj.idem_conj S hw
  have hu : finPart D (cA D p.e * incA D ((m : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hmw ((hc.2 m hm0).2 h)
  have h1 : ∀ y ∈ latV S L (· = p.v), (fun i => incA D (m : D.host.E) * y i) ∈ latV S (𝔪 • L) (· = p.v) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      refine AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, m • x, Submodule.smul_mem_smul hm𝔪 hx, ?_⟩
      funext i
      show (1 : AF D.host.F) ⊗ₜ[D.host.F] (m : D.host.E) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, one_mul, Pi.smul_apply, Algebra.smul_def]
    | zero =>
      convert zero_mem (latV S (𝔪 • L) (· = p.v)) using 1
      funext i
      simp
    | add y y' _ _ h h' =>
      convert add_mem h h' using 1
      funext i
      simp [mul_add]
    | neg y _ h =>
      convert neg_mem h using 1
      funext i
      simp
  have key : (fun i => cA D p.e * z i) =
      fun i => cA D p.e * incA D ((m : D.host.E)⁻¹) * (incA D (m : D.host.E) * z i) := by
    funext i
    rw [mul_assoc, ← mul_assoc (incA D _), ← map_mul, inv_mul_cancel₀ hmE, map_one, one_mul]
  rw [key]
  exact GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hu (h1 z hz)

end GlobalTheory.ConjPlaceLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedLevelElementKeepsStandardLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

open Matrix

theorem mulVec_conj_mulVec_eq {n : ℕ} {R : Type} [CommRing R] (a g : GL (Fin n) R) (v : Fin n → R) :
    (a : Matrix (Fin n) (Fin n) R) *ᵥ (((a⁻¹ * g * a : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) R) *ᵥ ((a : Matrix (Fin n) (Fin n) R) *ᵥ v) := by
  simp only [Matrix.mulVec_mulVec, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]


set_option maxHeartbeats 1000000 in
theorem moved_keeps_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D, (v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔ Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m)))) := by
  intro D T L sc G W U S t j hj k hk v
  have hD : DefNode D.R.m (.grid (j + 1) D.R.m) := ⟨hj.le, rfl⟩
  have hmax : finG (G.V (.grid (j + 1) D.R.m)) k ∈ G.levMax (.grid (j + 1) D.R.m) := by
    rw [← GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA W S t j hj.le]
    exact Subgroup.mem_inf.2 ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  rw [GridData.levMax, congLev_top] at hmax
  have hst := (Subgroup.mem_inf.1 hmax).2
  have e : Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (S.N.u (.grid (j + 1) D.R.m)).1)⁻¹ * finG (G.V (.grid (j + 1) D.R.m)) k * Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (S.N.u (.grid (j + 1) D.R.m)).1 := by
    rw [moved]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rfl
  rw [S.N.u_lat _ hD v, S.N.u_lat _ hD, e, mulVec_conj_mulVec_eq]
  exact hst _

end GlobalTheory.RowVertexInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.RowVacScalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def idemAt (w : Pl D.host.E) : AE D := Classical.epsilon fun e : AE D => Formalism.L2.NTheta.IsIdemAt e w


open Classical in
def detIdl (e : AE D) (V : HSp D) (g : GA D V) : (AE D)ˣ :=
  if he : e * e = e then GlobalTheory.VecInv.detAt e he V g else 1


open Classical in
theorem detIdl_val {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) :
    ((detIdl e V g : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := by
  rw [detIdl, dite_eq_left he]; rfl

def splitScal (G : GridData L sc) (p : Pair T) (w : Pl D.host.E) (g : GA D (G.pS p)) (h : GA D (G.pT p)) : ℂ :=
  ((splitFacO (G.chrS p) (G.chrT p) (detIdl (idemAt w) (G.pS p) g) (detIdl (idemAt w) (G.pT p) h) : Circle) : ℂ)

end GlobalTheory.RowVacScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableIntertwiningPair
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

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedDict.Entire

theorem differentiable_U' {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (U D T x G) := by
  have h : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
    unfold Hf
    fun_prop
  unfold U
  fun_prop

theorem differentiable_Iop' {D : D7} {T : Tor D} {N N' : ℕ} (A B : AddSubgroup (VC D N N'))
    {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) : Differentiable ℂ (Iop D T A B G) := by
  unfold Iop
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    exact (Differentiable.fun_sum fun q _ => (differentiable_U' _ hG).const_mul _).const_mul _

end GlobalTheory.MovedDict.Entire
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → finE (Yc D 0) κ ∈ St β → (((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ ∀ PP ∈ R.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) := by
  first | exact @GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent | exact GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent | (intros; apply GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent <;> assumption)
end

