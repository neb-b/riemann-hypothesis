module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0680
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnermostIntegrandLeftPeriodInvariantLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaDifferByTwistValuesLargeDepth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemBesselGroupOfLocalLatticeMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLiftBes
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_suppAt_locAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    {w : Pl D.host.E} (ew : AE D) (hew : Formalism.L2.NTheta.IsIdemAt ew w) {j : ℕ} (hj : j ≤ D.R.m)
    (x : GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w)) :
    ∃ h : GA D (G.V (.grid D.R.m j)), SuppAt ew _ h ∧ GlobalTheory.RowRep.locAt B t w j hj h = x := by
  have he : IsIdemSum ew {w} := ⟨⟨fun _ => ew, fun PP hPP => by rw [Finset.mem_singleton.1 hPP]; exact hew,
    (Finset.sum_singleton (fun _ => ew) w).symm⟩, hew.1.2.1⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.RowRep.exists_inBasis_eq (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w x
  obtain ⟨h, hh, hl⟩ := GlobalTheory.RowRep.exists_suppAt_loc_eq (G.V (.grid D.R.m j)) {w} ew he fun w' => (Finset.mem_singleton.1 w'.2).symm ▸ g'
  exact ⟨h, hh, hg' _ (hl ⟨w, Finset.mem_singleton_self w⟩)⟩

end GlobalTheory.RowLiftBes

namespace GlobalTheory.RowLiftBes
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem mem_besGrp_of_hasLoc : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t j σ, j ∈ idx D → ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m) (h' : j + 2 * σ + 2 = D.R.m)
    (r : GA D (ch.G.V (.grid D.R.m j))) (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj r g → (∀ w, g w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
    r ∈ besGrp (besDecAt ch.G j σ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t j σ hi hj hj' h' r g ⟨e, he, hsupp, hloc⟩ hg
  refine _root_.GlobalTheory.RowAssemble.mem_of_loc _ (locPl ch.G t) e he _ r hsupp fun w hw ew hew => ?_
  obtain ⟨h, hs, hl⟩ := exists_suppAt_locAt ch.S.B t ew hew hj (g ⟨w, hw⟩)
  refine ⟨h, GlobalTheory.T.mem_besselGroup_of_localMatrix_gridNode ch.S.toGridChoice (Set.mem_univ t) hw ew hew hj hj' h' h hs (hl ▸ hg ⟨w, hw⟩), hs, ?_⟩
  exact GlobalTheory.RowBaseUniq.loc_eq_of_inBasis _ _ _ (hl.trans (hloc ⟨w, hw⟩).symm)

end GlobalTheory.RowLiftBes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiGroupOfLocalLatticeMatricesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_fourierJacobiGroup_of_local_lattice_matrices : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t j σ, j ∈ idx D → ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m) (hσ : D.R.m - 1 - j = 2 * σ),
    1 ≤ σ → ∀ (r : GA D (ch.G.V (.grid D.R.m j))) (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj r g → (∀ w, g w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
    r ∈ jacGrp (rowJac ch.G j hj' σ hσ) := by
  first | exact @GlobalTheory.RowLift.mem_jacGrp_of_hasLoc | exact GlobalTheory.RowLift.mem_jacGrp_of_hasLoc | (intros; apply GlobalTheory.RowLift.mem_jacGrp_of_hasLoc <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShift0Model
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.LastVertexMove GlobalTheory.LastVertexInv GlobalTheory.FirstRowVertex

namespace GlobalTheory.FirstRowShift

private theorem locPl_under_mem_S0_or_Q {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  classical
  intro w hw
  rcases Finset.mem_union.mp hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    left
    rw [G.pl.w_over v hv]
    exact hv
  · exact Or.inr ⟨w, h, rfl⟩

private theorem isSBHalf_of_half_mem_iff {D : D7} {A B : HSp D} {e : AE D} {Λ Λ' : AddSubgroup (WO A B)}
    (hΛ : ∀ x, IsHalf e x → (x ∈ Λ ↔ x ∈ Λ')) {Φ : WO A B → ℂ} (hΦ : IsSBHalf e Λ Φ) : IsSBHalf e Λ' Φ := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  refine ⟨h1, k, hk, fun u hu hue t => h2 u ((hΛ u hue).mpr hu) hue t, fun t ht => ?_⟩
  exact (hΛ _ (GlobalTheory.StdHalfLat.half_nsmul (h1 t ht) k)).mp (h3 t ht)

theorem sb_std_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {e : AE D}, t ∈ U → IsIdemSum e (locPl G t) → ∀ i : Fin D.R.m,
    ∀ Φ : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ,
      IsSBHalf e (latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (G.latS (.chi i D.R.m : Pair T) : Set _) (G.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) Φ →
      IsSBHalf e (stdLat S (.chi i D.R.m)) Φ := by
  intro D T L sc G W U S t e ht he i Φ hΦ
  have hS : DefNode D.R.m (Node.grid ((i : ℕ) + 1) D.R.m) := ⟨i.isLt, rfl⟩
  have hT : DefNode D.R.m (Node.grid (i : ℕ) D.R.m) := ⟨i.isLt.le, rfl⟩
  obtain ⟨a, ha, hga⟩ := GlobalTheory.StdHalfLat.exists_kill S.N ht
    (FinDatum.ind G t (Pair.chi (i : ℕ) D.R.m) (locPl G t) (locPl_under_mem_S0_or_Q G t) e he) hS
  obtain ⟨b, hb, hgb⟩ := GlobalTheory.StdHalfLat.exists_kill S.N ht
    (FinDatum.ind G t (Pair.chi (i : ℕ) D.R.m) (locPl G t) (locPl_under_mem_S0_or_Q G t) e he) hT
  have ha' : e * (a + cA D a) = 0 := ha
  have hb' : e * (b + cA D b) = 0 := hb
  obtain ⟨hS1, hS2⟩ := GlobalTheory.StdHalfLat.hat_moves S.N hS
  obtain ⟨hT1, hT2⟩ := GlobalTheory.StdHalfLat.hat_moves S.N hT
  have hga' : SuppAt a (G.pS (Pair.chi (i : ℕ) D.R.m)) (negGA _ (S.N.u (Node.grid ((i : ℕ) + 1) D.R.m)).1) := by
    unfold SuppAt
    rw [mt_negGA]
    exact hga
  unfold GlobalTheory.LastVertexMove.stdLat
  refine isSBHalf_of_half_mem_iff (fun x hx => ?_) hΦ
  refine (GlobalTheory.StdHalfLat.mem_latO_iff_of_half (S := G.pS (Pair.chi (i : ℕ) D.R.m)) (T := G.pT (Pair.chi (i : ℕ) D.R.m))
    (negGA _ (S.N.u (Node.grid ((i : ℕ) + 1) D.R.m)).1) (S.N.u (Node.grid (i : ℕ) D.R.m)).1
    (fun v hv => ?_) (fun v hv => ?_) hT1 hT2 ha' hb' hga' hgb hx).symm
  · rw [mt_negGA]
    exact hS1 v hv
  · rw [← map_inv (negGA (G.V (Node.grid ((i : ℕ) + 1) D.R.m))), mt_negGA]
    exact hS2 v hv

theorem actO_inv_actO {D : D7} {A B : HSp D} (g : GA D A) (h : GA D B) (u : WO A B) :
    actO A B g⁻¹ h⁻¹ (actO A B g h u) = u := by
  rw [← GlobalTheory.SplitLinear.actO_mul, inv_mul_cancel, inv_mul_cancel]
  simp [actO]

theorem vac_first : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m)),
    (∀ x : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)), actO _ _ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T) ↔ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T)) →
    ∃ c : ℂ, W.om (.chi (firstIx D) D.R.m : Pair T) (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1) (S.Z.vac (.chi (firstIx D) D.R.m : Pair T)) = c • S.Z.vac (.chi (firstIx D) D.R.m : Pair T) := by
  intro D T L sc G W U S k hlat
  refine GlobalTheory.RowChiVac.vac_chi_scalar S (i := ((firstIx D : Fin D.R.m) : ℕ)) (firstIx D).isLt _ 1 ?_
  intro u
  have h := hlat (actO _ _
    (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1
    (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2 u)
  rw [actO_inv_actO] at h
  exact h

end GlobalTheory.FirstRowShift


open GlobalTheory.FirstRowShift in
theorem GlobalTheory.FirstRowShift.rowShift0_model : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T} {e : AE D},
    t ∈ U → IsIdemSum e (locPl G t) →
    ∀ k : FinPt G (.grid 0 D.R.m), finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) →
    ∃ c : ℂ, W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1) (S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) =
        c • S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ∧
      ∀ Tm : (WO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) → ℂ),
        IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
          (latO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (S.N.latS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) (S.N.latT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) fun _ => True) 1 (S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) Tm →
        ∀ Φ : WO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) → ℂ,
          IsSBHalf e (latO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.latS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) (G.latT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) fun _ => True) Φ →
          GlobalTheory.FirstRowVertex.rowShift0 S k (Tm Φ) =
            c • Tm (fun y => Φ (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
              (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹
              (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) := by
  intro D T L sc G W U S μ₀ hL t e ht he k hk
  have hlat := GlobalTheory.FirstRowLat.rowPt0_inv_mem_stdLat_iff S hL ht k hk
  obtain ⟨c, hc⟩ := vac_first S k hlat
  refine ⟨c, hc, fun Tm hT Φ hΦ => ?_⟩
  exact GlobalTheory.LastVertexTensor.om_model S (GlobalTheory.LastVertexInv.defPair_chi (T := T) (firstIx D))
    (GlobalTheory.LastVertexInv.inRange_chi (T := T) (firstIx D)) he Tm hT _ c hlat hc Φ (sb_std_row S ht he (firstIx D) Φ hΦ)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestColumnInductionLocalToGlobalExpansionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_columnInduction_localToGlobalExpansion : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∀ (I : locPl ch.G t → Type) (S : ∀ w, Finset (I w)) (x : ∀ w, I w → ℂ) (d : ∀ w, I w → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : ∀ w, I w → Combs ch.G), (∀ w, ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).e = eL w ∧ IsCombOf ch.W (d w i j) ((c w i).1 j)) → (∀ w (y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))), (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0) → ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ) (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).e = e ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧ (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (u j)) → ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 u) 0) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ u : ColPt ch.G, evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) 1 u 0 = (∏ w, ζ w) * ∑ a ∈ SJ, xJ a * evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
  first | exact @GlobalTheory.LocAsm.columnInduction | exact GlobalTheory.LocAsm.columnInduction | (intros; apply GlobalTheory.LocAsm.columnInduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedIntegrandBiInvariantLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowInv

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def mvD (t : T) (j : ℕ) (k : GA D (ch.G.V (.grid D.R.m j))) (Φ : SchDown ch.G t) : SchDown ch.G t := fun i =>
  ch.W.om (.mu t D.R.m i) ((Pi.mulSingle j k : Pts ch.G) i, (Pi.mulSingle j k : Pts ch.G) (i + 1)) (Φ i)

theorem mulSingle_fin {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} (hk : k ∈ GfC _) (i : ℕ) :
    (Pi.mulSingle j k : Pts ch.G) i ∈ GfC _ := by
  rcases eq_or_ne i j with rfl | hi
  · rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hi]
    exact one_mem _

theorem om_move (t : T) {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} (hk : k ∈ GfC _) {Φ : SchDown ch.G t}
    (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (P : PolDown ch.G) (i : ℕ) (hi : i < D.R.m)
    (g : GA D (ch.G.V (.grid D.R.m i))) (g' : GA D (ch.G.V (.grid D.R.m (i + 1)))) :
    ch.W.om (.mu t D.R.m i) (g * (Pi.mulSingle j k : Pts ch.G) i, g' * (Pi.mulSingle j k : Pts ch.G) (i + 1))
        (fockD ch.W t Φ P ⟨i, hi⟩) =
      ch.W.om (.mu t D.R.m i) (g, g') (fockD ch.W t (mvD ch t j k Φ) P ⟨i, hi⟩) := by
  have hom := ch.W.om_is (.mu t D.R.m i) ⟨le_rfl, hi⟩
  have hb := mulSingle_fin ch hk i
  have hb' := mulSingle_fin ch hk (i + 1)
  have key := GlobalTheory.OrientedHeis.om_pureTensorO D ch.W.ψ ch.W.θ (ch.G.pS (.mu t D.R.m i)) (ch.G.pT (.mu t D.R.m i))
    (ch.G.chrS (.mu t D.R.m i)) (ch.G.chrT (.mu t D.R.m i)) (ch.W.om (.mu t D.R.m i)) hom ch.W.θ_is
    (ch.G.cartS ch.W.cart (.mu t D.R.m i)) (ch.G.cartS ch.W.cart (.mu t D.R.m i))
    (ch.G.onS ch.W.onb (.mu t D.R.m i)) (ch.G.onS ch.W.onb (.mu t D.R.m i))
    (ch.G.onT ch.W.cart (.mu t D.R.m i)) (ch.G.onT ch.W.cart (.mu t D.R.m i))
    (ch.G.onT ch.W.onb (.mu t D.R.m i)) (ch.G.onT ch.W.onb (.mu t D.R.m i)) _ _
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) (Φ ⟨i, hi⟩) (hΦ ⟨i, hi⟩) (P ⟨i, hi⟩)
  have e1 : ((g * (Pi.mulSingle j k : Pts ch.G) i, g' * (Pi.mulSingle j k : Pts ch.G) (i + 1)) :
      GA D (ch.G.V (.grid D.R.m i)) × GA D (ch.G.V (.grid D.R.m (i + 1)))) =
      (g, g') * ((Pi.mulSingle j k : Pts ch.G) i, (Pi.mulSingle j k : Pts ch.G) (i + 1)) := rfl
  rw [e1, map_mul, Module.End.mul_apply]
  exact congrArg (ch.W.om (.mu t D.R.m i) (g, g')) key.2

theorem lastDat_congr {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}
    (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj)) (g g' : GA D (G.V (.grid D.R.m j)))
    (Φ₁ Φ₁' : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ)
    (e : Wl.om (.mu t D.R.m j) (g, 1) Φ₁ = Wl.om (.mu t D.R.m j) (g', 1) Φ₁') :
    lastDat Wl hM j hj vN g Φ₁ Φ₂ = lastDat Wl hM j hj vN g' Φ₁' Φ₂ := by
  have e' : (lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁ = (lastAt G Wl t hM j hj vN).s.om (g', 1) Φ₁' := e
  unfold lastDat
  rw [e']

theorem down_theta {t : T} {Φ : ch.G.Datum} {τ : SchRow ch.G × SchDown ch.G t →₀ ℂ} (hτ : IsFlipFin t ch.S.B ch.rm Φ τ)
    {d : SchRow ch.G × SchDown ch.G t} (hd : d ∈ τ.support) (j : Fin D.R.m) : IsThetaFunO ch.W.ψ _ _ (d.2 j) := by
  obtain ⟨e, _he, φ, hφ, _⟩ := hτ
  have hv := ch.rm.vT_is t D.R.m j le_rfl j.2
  exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt ch.W.ψ_std ch.W.θ_is ((hφ d hd).2 j).2 hv.2.theta

theorem fockD_theta (t : T) {Φ : SchDown ch.G t} (hΦ : ∀ j, IsThetaFunO ch.W.ψ _ _ (Φ j)) (P : PolDown ch.G) (j : Fin D.R.m) :
    IsThetaFunO ch.W.ψ _ _ (fockD ch.W t Φ P j) := by
  have hom := ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, j.2⟩
  have key := GlobalTheory.OrientedHeis.om_pureTensorO D ch.W.ψ ch.W.θ (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j))
    (ch.G.chrS (.mu t D.R.m j)) (ch.G.chrT (.mu t D.R.m j)) (ch.W.om (.mu t D.R.m j)) hom ch.W.θ_is
    (ch.G.cartS ch.W.cart (.mu t D.R.m j)) (ch.G.cartS ch.W.cart (.mu t D.R.m j))
    (ch.G.onS ch.W.onb (.mu t D.R.m j)) (ch.G.onS ch.W.onb (.mu t D.R.m j))
    (ch.G.onT ch.W.cart (.mu t D.R.m j)) (ch.G.onT ch.W.cart (.mu t D.R.m j))
    (ch.G.onT ch.W.onb (.mu t D.R.m j)) (ch.G.onT ch.W.onb (.mu t D.R.m j)) 1 1
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.one_mul]) (Φ j) (hΦ j) (P j)
  exact key.1

theorem mvD_theta (t : T) {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} {Φ : SchDown ch.G t}
    (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (i : Fin D.R.m) : IsThetaFunO ch.W.ψ _ _ (mvD ch t j k Φ i) :=
  (ch.W.om_is (.mu t D.R.m i) ⟨le_rfl, i.2⟩).om_pres _ _ (hΦ i)

theorem update_eq_mul (h : Pts ch.G) (j : ℕ) (k : GA D (ch.G.V (.grid D.R.m j))) :
    Function.update h j (h j * k) = h * Pi.mulSingle j k := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

theorem conAt_move (t : T) {M : Vol ch.G} (hM : M.Is t) {j : ℕ} (hj : j ∈ idx D) {k : GA D (ch.G.V (.grid D.R.m j))}
    (hk : k ∈ GfC _) {Φ : SchDown ch.G t} (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (P : PolDown ch.G) (h : Pts ch.G) :
    conAt ch.W hM (fockD ch.W t Φ P) (h * Pi.mulSingle j k) = conAt ch.W hM (fockD ch.W t (mvD ch t j k Φ) P) h := by
  have hjm : j ≤ D.R.m - 2 := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  funext j'
  unfold conAt
  by_cases h0 : j' + 2 * 0 + 2 = D.R.m
  · rw [dite_eq_left h0, dite_eq_left h0]
    have hne1 : j' + 1 ≠ j := by omega
    have hne2 : j' + 1 + 1 ≠ j := by omega
    have hmv : mvD ch t j k Φ ⟨j' + 1, by omega⟩ = Φ ⟨j' + 1, by omega⟩ := by
      simp only [mvD, Fin.val_mk, Pi.mulSingle_eq_of_ne hne1, Pi.mulSingle_eq_of_ne hne2, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hf : fockD ch.W t (mvD ch t j k Φ) P ⟨j' + 1, by omega⟩ = fockD ch.W t Φ P ⟨j' + 1, by omega⟩ := by
      unfold fockD
      rw [hmv]
    rw [hf]
    refine lastDat_congr ch.W hM j' h0 _ _ _ _ _ _ ?_
    have e := om_move ch t hk hΦ P j' (by omega) (h j') 1
    rw [Pi.mulSingle_eq_of_ne hne1, one_mul] at e
    exact e
  rw [dite_eq_right h0, dite_eq_right h0]
  by_cases h1 : j' + 2 * ((D.R.m - 4 - j') / 2 + 1) + 2 = D.R.m
  · refine dite_congr rfl (fun h1' => ?_) (fun _ => rfl)
    have e1 := om_move ch t hk hΦ P j' (by omega) (h j') (h (j' + 1))
    have e2 := om_move ch t hk hΦ P (j' + 1) (by omega) (h (j' + 1)) (h (j' + 1 + 1))
    simp only [Pi.mul_apply]
    rw [e1, e2]
  · refine dite_congr rfl (fun h1' => absurd h1' h1) (fun _ => rfl)

theorem inv_of (hB : BasicAt ch) (hC : ConLin ch) (hK : KFix ch) (hR : RInv ch) (hT : TensAt ch) : InvAt ch := by
  intro t a τ hτ M hM P y j hj h
  refine ⟨fun r hr => ?_, fun k hk => ?_⟩
  · unfold tot
    refine Finsupp.sum_congr fun d hd => ?_
    rw [hR t M hM _ d.1 (fockD_theta ch t (down_theta ch hτ hd) P.2)
      (fun i => (hB.2.2.2.2.1 t _ τ hτ M hM d hd P.2 h).2 i) P.1 _ _ (hB.1 a) (hB.2.1 t y) j hj r hr h]
  · have hk' : k ∈ GfC _ := (Subgroup.mem_inf.1 hk).1
    have hmv : ∀ d ∈ τ.support, conAt ch.W hM (fockD ch.W t d.2 P.2) (h * Pi.mulSingle j k) =
        conAt ch.W hM (fockD ch.W t (mvD ch t j k d.2) P.2) h := fun d hd =>
      conAt_move ch t hM hj hk' (down_theta ch hτ hd) P.2 h
    rw [update_eq_mul]
    unfold tot
    simp only [Finsupp.sum]
    refine Eq.trans (Finset.sum_congr rfl fun d hd =>
      congrArg (fun C => τ d * per ch.W M t C d.1 P.1 (colFn ch a) (formTop ch t y)) (hmv d hd)) ?_
    let Φs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → SchDown ch.G t :=
      Sum.elim (fun d => mvD ch t j k d.2) (fun d => d.2)
    let fs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → SchRow ch.G := Sum.elim (·.1) (·.1)
    let xs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → ℂ := Sum.elim (fun d => τ d) (fun d => -τ d)
    have hth : ∀ i ∈ τ.support.disjSum τ.support, ∀ n, IsThetaFunO ch.W.ψ _ _ (Φs i n) := by
      rintro (d | d) hd n
      · exact mvD_theta ch t (down_theta ch hτ (Finset.inl_mem_disjSum.1 hd)) n
      · exact down_theta ch hτ (Finset.inr_mem_disjSum.1 hd) n
    have hvan : ∀ (yr : RowPt ch.G) (v : ∀ j : Fin D.R.m, WO (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1)))),
        ∑ i ∈ τ.support.disjSum τ.support, xs i * ((∏ n, fs i n (yr n)) * ∏ n, Φs i n (v n)) = 0 := by
      intro yr v
      have hk2 := hK t _ τ hτ j hj k hk yr v
      simp only [Finsupp.sum] at hk2
      rw [Finset.sum_disjSum]
      simp only [xs, fs, Φs, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
      rw [← sub_eq_add_neg, sub_eq_zero]
      exact hk2
    have hgood : ∀ i ∈ τ.support.disjSum τ.support, Good ch.W (conAt ch.W hM (fockD ch.W t (Φs i) P.2) h) (fs i) := by
      rintro (d | d) hd
      · have hd' := Finset.inl_mem_disjSum.1 hd
        show Good ch.W (conAt ch.W hM (fockD ch.W t (mvD ch t j k d.2) P.2) h) d.1
        rw [← hmv d hd']
        exact hB.2.2.2.2.1 t _ τ hτ M hM d hd' P.2 _
      · exact hB.2.2.2.2.1 t _ τ hτ M hM d (Finset.inr_mem_disjSum.1 hd) P.2 h
    have key := hT t M (hB.2.2.1 t M hM) _ _ (hB.1 a) (hB.2.1 t y) _ (τ.support.disjSum τ.support) xs
      (fun i => conAt ch.W hM (fockD ch.W t (Φs i) P.2) h) fs hgood (hC t M hM P.2 h _ _ xs fs Φs hth hvan) P.1
    rw [Finset.sum_disjSum] at key
    simp only [xs, fs, Φs, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
    rw [← sub_eq_zero, sub_eq_add_neg]
    exact key

theorem main : Big fun ch => InvAt ch :=
  big_mono (fun ch h => inv_of ch h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (Big.and _root_.GlobalTheory.RowBasic.basicAt (Big.and _root_.GlobalTheory.RowVal.conLin_big (Big.and _root_.GlobalTheory.RowKFix.kfix (Big.and _root_.GlobalTheory.RowLeftInv.rinv _root_.GlobalTheory.RowVal.tensAt_big))))

end GlobalTheory.RowInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaRealUpToTwistLargeDepth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal.OneVac

theorem isBiVac_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (LA : Set (Fin A.rank → D.host.E))
    (LS : Set (Fin S.rank → D.host.E)) (LA' : Set (Fin A'.rank → D.host.E)) :
    IsBiVac ψ A S A' LA LS LA' 0 ∧ IsBiSmooth (0 : WO A S → WO S A' → ℂ) := by
  have hz : ∀ (X Y : HSp D) (u : WO X Y), heisO ψ X Y u (0 : WO X Y → ℂ) = 0 := fun X Y u => by
    simpa using GlobalTheory.SeeSaw.Scale.heisO_smul ψ X Y u 0 0
  have h : ∀ (X Y : HSp D) (Λ : AddSubgroup (WO X Y)),
      IsThetaFunO ψ X Y (0 : WO X Y → ℂ) ∧ IsLatVac (heisO ψ X Y) Λ (0 : WO X Y → ℂ) := fun X Y Λ =>
    ⟨⟨fun γ w => by simp, ⟨⊤, isOpen_univ, fun u _ _ => hz X Y u⟩, continuous_const, fun k L hL hf w => contDiff_const⟩,
      fun u _ => hz X Y _, fun e _ u _ _ => hz X Y u⟩
  exact ⟨⟨continuous_const, fun v => h A S _, fun u => h S A' _⟩, fun n L L' _ _ _ _ u v => contDiff_const⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem vacAt_of (h₁ : VacReal ch) (h₂ : VacTw ch) : VacAt ch := by
  obtain ⟨hb, z, hz, htw⟩ := h₂
  refine ⟨hb, z, hz, fun P p hp => ?_⟩
  by_cases hex : ∃ (t : T) (M : Vol ch.G), M.Is t
  · obtain ⟨t₀, M₀, hM₀⟩ := hex
    obtain ⟨b₀, hb₀⟩ := hb t₀
    refine ⟨fun j => ((z t₀ j : ℂ)⁻¹) • conAt ch.W hM₀ (fockD ch.W t₀ (fun j => ch.rm.vT D.R.m j) P) (p * b₀) j,
      fun j hj hj' => ?_, fun t M hM b hbt j hj hj' => ?_⟩
    · obtain ⟨hv, hs⟩ := h₁ t₀ M₀ hM₀ b₀ hb₀ P p hp j hj hj'
      exact ⟨GlobalTheory.SeeSaw.Scale.isBiVac_smul _ hv, GlobalTheory.SeeSaw.Scale.isBiSmooth_smul _ hs⟩
    · have e := htw t t₀ M M₀ hM hM₀ b b₀ hbt hb₀ P p hp j hj hj'
      rw [smul_comm, ← e, smul_smul, inv_mul_cancel₀ (z t₀ j).ne_zero, one_smul]
  · exact ⟨0, fun j _ _ => isBiVac_zero _ _ _ _ _ _ _, fun t M hM => absurd ⟨t, M, hM⟩ hex⟩

theorem big_vacAt : Big fun ch => VacAt ch :=
  GlobalTheory.RowReal.big_mono (Q := fun ch => VacReal ch ∧ VacTw ch) (fun ch h => vacAt_of ch h.1 h.2)
    (Big.and _root_.GlobalTheory.VacRealPf.vacReal _root_.GlobalTheory.RowVacTw.vacTw)

end GlobalTheory.RowVal.OneVac

end
end

