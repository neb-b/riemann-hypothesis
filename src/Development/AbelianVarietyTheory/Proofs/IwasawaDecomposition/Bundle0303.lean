module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankBaseRowsIsotypicEqGoodFormsIsotypic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.Mem.R3.IsotMult

theorem finrank_isot_killed_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] (S0 X Y : Type) [AddCommGroup S0] [Module ℂ S0] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (ρ' : Representation ℂ H Y) (C : Submodule ℂ X) (C' : Submodule ℂ Y) (I : Set (MonoidAlgebra ℂ H)), σ0.IsIrreducible → (killed σ0 I ≠ ⊥ → (homInto σ0 ρ C ≠ ⊥ ∨ homInto σ0 ρ' C' ≠ ⊥) → GlobalTheory.PRep.IsAdmissible σ0) → (killed σ0 I ≠ ⊥ → GlobalTheory.PRep.IsAdmissible σ0 → Module.rank ℂ (homInto σ0 ρ C) = Module.rank ℂ (homInto σ0 ρ' C')) → (∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) → (∀ y ∈ killed ρ' I, IsOpen {g : H | ρ' g y = y}) → FiniteDimensional ℂ ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) → FiniteDimensional ℂ ((⨆ f ∈ homInto σ0 ρ' C', LinearMap.range f) ⊓ killed ρ' I : Submodule ℂ Y) → Module.finrank ℂ ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) = Module.finrank ℂ ((⨆ f ∈ homInto σ0 ρ' C', LinearMap.range f) ⊓ killed ρ' I : Submodule ℂ Y) := by
  intro H _ _ S0 X Y _ _ _ _ _ _ σ0 ρ ρ' C C' I hirr hadm hrank ho ho' f f'
  classical
  have hbot : ∀ {Z : Type} [AddCommGroup Z] [Module ℂ Z] (τ : Representation ℂ H Z) (B : Submodule ℂ Z),
      homInto σ0 τ B = ⊥ → (⨆ g ∈ homInto σ0 τ B, LinearMap.range g) = ⊥ := by
    intro Z _ _ τ B h
    refine iSup₂_eq_bot.2 fun g hg => ?_
    rw [h, Submodule.mem_bot] at hg
    rw [hg, LinearMap.range_zero]
  by_cases hk : killed σ0 I = ⊥
  · rw [_root_.GlobalTheory.RepCount.iSup_range_homInto_inf_killed_eq_bot _ _ _ σ0 ρ C I hirr hk, _root_.GlobalTheory.RepCount.iSup_range_homInto_inf_killed_eq_bot _ _ _ σ0 ρ' C' I hirr hk,
      finrank_bot, finrank_bot]
  by_cases h0 : homInto σ0 ρ C = ⊥ ∧ homInto σ0 ρ' C' = ⊥
  · rw [hbot ρ C h0.1, hbot ρ' C' h0.2, bot_inf_eq, bot_inf_eq, finrank_bot, finrank_bot]
  have hadm0 := hadm hk (not_and_or.1 h0)
  have hr := hrank hk hadm0
  have hdec : ∀ {Z : Type} [AddCommGroup Z] [Module ℂ Z] (τ : Representation ℂ H Z) (B : Submodule ℂ Z),
      IsDecomp τ (⨆ g ∈ homInto σ0 τ B, LinearMap.range g) := by
    intro Z _ _ τ B x hx _
    refine (iSup₂_le (fun g hg => ?_) : (⨆ g ∈ homInto σ0 τ B, LinearMap.range g) ≤ irrSum τ _) hx
    rintro _ ⟨s, rfl⟩
    exact GlobalTheory.RepCount.apply_mem_irrSum hirr hadm0
      ⟨fun t => (le_iSup₂_of_le g hg le_rfl : LinearMap.range g ≤ _) ⟨t, rfl⟩, hg.2⟩ s
  refine _root_.GlobalTheory.RepCount.finrank_inf_killed_eq H X Y ρ ρ' _ _ I (hdec ρ C) (hdec ρ' C') ?_ ho ho' f f'
  intro W _ _ σ hσ _ _
  by_cases hz : homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) = ⊥ ∧
      homInto σ ρ' (⨆ g ∈ homInto σ0 ρ' C', LinearMap.range g) = ⊥
  · rw [hz.1, hz.2, rank_bot, rank_bot]
  have he : Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) := by
    rcases not_and_or.1 hz with h | h
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact _root_.GlobalTheory.IsoRankMult.iso_of_hom_into_sum _ _ _ _ σ0 σ ρ C hirr hσ g hg hg0
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact _root_.GlobalTheory.IsoRankMult.iso_of_hom_into_sum _ _ _ _ σ0 σ ρ' C' hirr hσ g hg hg0
  rw [_root_.GlobalTheory.MultIso.rank_homInto_iSup_range _ _ _ _ σ0 σ ρ C he, _root_.GlobalTheory.MultIso.rank_homInto_iSup_range _ _ _ _ σ0 σ ρ' C' he]
  exact hr

end GlobalTheory.Mem.R3.IsotMult

namespace GlobalTheory.Mem.R3.IsotMult

theorem isotL_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G]
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P' : LevelP L.Pg L.r ℂ) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (π : Formalism.L2.NG.FinTyp D.host.E n) (hs : L.s = 0) (hQ : L.Q = ∅) (hl : LiftsExist V β L) :
    principalLevelFrame.isotL θ P M (levS V β (withP L P')) (levChi V β (withP L P')) (gaL V β L eG c) π =
      (⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f) ⊓
        killed (finRep M) (eqSet V β L eG c P' (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) := by
  have e1 := _root_.GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed θ M β L eG c P' (∅ : Set Empty) Empty.elim Empty.elim Empty.elim hs hQ hl
  have htop : hPart M (levG V β (flag1L L)) (∅ : Set Empty) Empty.elim Empty.elim Empty.elim = ⊤ :=
    eq_top_iff.2 fun x _ => GlobalTheory.PartDims.mem_hPart.2 fun P hP => hP.elim
  rw [htop, inf_top_eq] at e1
  have hle : (⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f) ≤ allMaps θ M :=
    iSup₂_le fun f hf => by rintro _ ⟨s, rfl⟩; exact hf.1 s
  show goodPart θ M (levS V β (withP L P')) (levChi V β (withP L P')) (gaL V β L eG c) ⊓
    principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = _
  rw [e1, _root_.GlobalTheory.IsotHom.isotIn_eq_iSup_homInto]
  exact le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
    (le_inf (le_inf (inf_le_left.trans hle) inf_le_right) inf_le_left)

end GlobalTheory.Mem.R3.IsotMult

namespace GlobalTheory.Mem.R3.IsotMult


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem finrank_isotL_transfer (hHC : GlobalTheory.Published.HarishChandraFinite) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) (hD : CuspDecomp D) (hM : MultEq R)
    (hF : D.host.F = maximalRealSubfield D.host.E) {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (i : Fin D.R.m)
    (PW : principalLevelFrame.RowPsi (Wc D i) n) (hPY : GlobalTheory.StdFrame.StdPsi hF PY) (hPW : GlobalTheory.StdFrame.StdPsi hF PW)
    (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)) (P : LevelP R.Pg D.R.r ℂ) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (hfin : FiniteDimensional ℂ (principalLevelFrame.isotL R.θ PY M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 π)) :
    Module.finrank ℂ (principalLevelFrame.isotL R.θ PY M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 π) =
      Module.finrank ℂ (principalLevelFrame.isotL R.θ PW (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P))
        (R.eWf i (sg0 D A)) π) := by
  classical
  obtain ⟨c, hc⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  obtain ⟨c', hc'⟩ := hC.lev.βW i
  have hrk : (Yc D 0).rank = (Wc D i).rank := GlobalTheory.PartDims.rank_zeroth_component_eq.trans (GlobalTheory.PartDims.rank_weight_component_eq i).symm
  obtain ⟨j, Φ, hΦ⟩ := GlobalTheory.FinIsoExists.exists_isFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg hrk
    hc hc' (_root_.GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg)
  obtain ⟨h, hh⟩ := GlobalTheory.KapIsot.frames_inner (Yc D 0) (Wc D i) hF PY PW hPY hPW
    (by rw [GlobalTheory.PartDims.rank_zeroth_component_eq]; exact GlobalTheory.KapIsot.odd_r D.R) _ _ _ j Φ hΦ
  have eY := isotL_eq R.θ M₀ (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) P PY π rfl rfl
    (GlobalTheory.DimFull.liftsY' hC)
  have eW := isotL_eq R.θ (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG (RealDat.eC (A := A) (sg0 D A)) P PW π rfl rfl
    (GlobalTheory.DimFull.liftsW' hC i)
  have e3 : RealDat.eC (A := A) (sg0 D A) = RealDat.eC (A := A) D.what₂.embLL := by rw [GlobalTheory.PartDims.sign_at_base_place_eq_embedding R]
  have hl := _root_.GlobalTheory.LevTrans.levtrans (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi
    (fun _ _ => 1) j Φ hΦ
  have e4 : killed ((finRep (R.MW i (sg0 D A))).comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC (Yc D 0)) _)
        (eqSet (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) P (∅ : Set Empty) Empty.elim
          Empty.elim Empty.elim) =
      killed (finRep (R.MW i (sg0 D A))) (eqSet (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG
        (RealDat.eC (A := A) D.what₂.embLL) P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) :=
    _root_.GlobalTheory.CuspMult.EqTrans.killed_eqSet_comp (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi (fun _ _ => 1) Φ R.eG _ P
      (∅ : Set Empty) Empty.elim Empty.elim Empty.elim _ _ hrk (fun κ => (hl κ).1) (fun κ => (hl κ).2) (fun P0 => P0.elim)
  have eF := _root_.GlobalTheory.FrameIsot.iSup_homInto_frame_conj (Yc D 0) (Wc D i) PY PW Φ h hh _ (finRep (R.MW i (sg0 D A)))
    (allMaps R.θ (R.MW i (sg0 D A))) π
  have eY' : principalLevelFrame.isotL R.θ PY M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 π = _ := eY
  have eW' : principalLevelFrame.isotL R.θ PW (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P))
      (R.eWf i (sg0 D A)) π = _ := eW
  rw [e3, ← e4, ← eF] at eW'
  have hWle : principalLevelFrame.isotL R.θ PW (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P))
      (R.eWf i (sg0 D A)) π ≤ R.Wall i (sg0 D A) :=
    inf_le_left.trans ((GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _).trans inf_le_left)
  have fW := (GlobalTheory.PartDims.finrank_comap (hC.models.HW i (sg0 D A)) hWle).2
  rw [eY'] at hfin ⊢
  rw [eW'] at fW ⊢
  haveI := GlobalTheory.PartDims.isTopologicalGroup_GA (Yc D 0)
  have hne : Nontrivial π.S := Submodule.nontrivial_iff_ne_bot.2 π.ne
  have hirr : Representation.IsIrreducible (((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PY).symm.toMonoidHom) : Representation ℂ (GfC (Yc D 0)) π.S) := by
    refine GlobalTheory.KapIsot.isIrreducible_of fun U hU => GlobalTheory.OccRowVec.finRep_irr π U fun g x hx => ?_
    have := hU (GlobalTheory.KapIsot.eqv PY g) x hx
    simpa using this
  refine finrank_isot_killed_eq _ _ _ _ ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PY).symm.toMonoidHom) (finRep M₀)
    ((finRep (R.MW i (sg0 D A))).comp Φ.toMulEquiv.toMonoidHom) (allMaps R.θ M₀) (allMaps R.θ (R.MW i (sg0 D A))) _ hirr
    (fun hk hor => _root_.GlobalTheory.AdmOfHom.isAdmissible_finRep hHC R.θ hC.models.inf (Yc D 0) (Wc D i) M₀ (R.MW i (sg0 D A)) Φ (R.βY 0)
      (R.dat0 R.triv) R.eG _ P PY π rfl rfl hk hor)
    (fun hk hadm => ?_) (fun x hx => GlobalTheory.PartDims.isOpen_stab rfl rfl hx) (fun x hx => GlobalTheory.PartDims.isOpen_stab rfl rfl hx)
    hfin fW
  rw [GlobalTheory.PartDims.homInto_comp]
  exact hM i M₀ j Φ hΦ π.S _ hirr hadm (GlobalTheory.PartDims.isGoodRep_of_killed rfl rfl (GlobalTheory.DimFull.liftsY' hC) hk)

end GlobalTheory.Mem.R3.IsotMult

namespace GlobalTheory.Mem.R3.IsotMult


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem finrank_isotE_eq_isotL : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → ∀ (i : Fin D.R.m) (π : D.what₂.FT), Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) = Module.finrank ℂ (principalLevelFrame.isotL R.toRealDat.θ (Y.PW i) (R.toRealDat.MW i (sg0 D A3.A)) (levS _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  intro _ _ h3 _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ hX hD hM i π
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex).1
  obtain ⟨M₀, c, hc⟩ := GlobalTheory.PartDims.exists_conjModel (S' := parA (Ptw D) 0)
    (fun τ => by rw [Nat.zero_min]; exact (dualPar_dualPar _).symm) (R.toRealDat.MY 0)
  have hr := _root_.GlobalTheory.IsotConj.conj_rank R.toRealDat.θ (R.toRealDat.MY 0) M₀ c hc
    (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false)))
    (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false)))
    (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levL F.lv2 false D.what₂.embLL)))
    R.toRealDat.e0 R.toRealDat.e0 Y.PY (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))
    (fun k hk => GlobalTheory.PartDims.star_levChi false hk)
    (GlobalTheory.PartDims.gaL_star (L := R.toRealDat.dat0 R.toRealDat.triv) R.toRealDat.eG _ rfl rfl
      (_root_.GlobalTheory.CuspMult.idemOf_coeff_real D.what₂.embLL A3.A.X hH.ok.ok2.irr hX))
  have hE : R.toRealDat.EEat (R.toRealDat.levR F.lv2 false) ≤ R.toRealDat.EEat R.toRealDat.triv :=
    GlobalTheory.PartDims.goodPart_le_flag (L := R.toRealDat.dat0 R.toRealDat.triv) R.toRealDat.θ _ rfl rfl _ _
  have fE : FiniteDimensional ℂ (principalLevelFrame.isotL R.toRealDat.θ Y.PY (R.toRealDat.MY 0)
      (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false)))
      (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0
      (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π)))) :=
    (GlobalTheory.PartDims.finrank_comap hC.models.HE (inf_le_left.trans hE)).2
  have f1 : FiniteDimensional ℂ (principalLevelFrame.isotL R.toRealDat.θ Y.PY M₀
      (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levL F.lv2 false D.what₂.embLL)))
      (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levL F.lv2 false D.what₂.embLL))) R.toRealDat.e0
      (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) :=
    Module.rank_lt_aleph0_iff.1 (lt_of_eq_of_lt hr.symm (Module.rank_lt_aleph0_iff.2 fE))
  have hl : R.toRealDat.levL F.lv2 false (sg0 D A3.A) = R.toRealDat.levL F.lv2 false D.what₂.embLL := by
    rw [GlobalTheory.PartDims.sign_at_base_place_eq_embedding R.toRealDat]
  rw [hl]
  refine (congrArg Cardinal.toNat hr).trans ?_
  exact finrank_isotL_transfer h3 R.toRealDat F.lv2 hC hD hM Y.hF Y.PY i (Y.PW i) Y.stdPsi.1 (Y.stdPsi.2 i) M₀
    (R.toRealDat.levL F.lv2 false D.what₂.embLL) _ f1

end GlobalTheory.Mem.R3.IsotMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsEquiv
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.StepZero

section Gen
open _root_.Formalism.L2.Forms
variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem mem_formsK (S : GStep E K n) (hS : S.Free) (hF : (S.fam emb lam).Ok) (x : S.Cl → VV K lam) : x ∈ S.FormsK emb lam hF := by
  intro c γ
  have hγ : (γ : S.G c.1) = 1 := hS c.1 γ (S.rp c.1 c.2) γ.2
  show (S.rho emb lam c.1) (γ : S.G c.1) (x c) = x c
  rw [hγ, map_one]
  rfl

theorem forms_equiv (S S' : GStep E K n) (hS : S.Free) (hS' : S'.Free) (hF : (S.fam emb lam).Ok) (hF' : (S'.fam emb lam).Ok)
    (e0 : S.Cl ≃ S'.Cl) (hL : ∀ c, S'.Lsh _ (S'.rep (e0 c)) = S.Lsh _ (S.rep c)) :
    ∃ e : (S.hlat emb lam hF).V ≃ₗ[K] (S'.hlat emb lam hF').V,
      (∀ x, x ∈ (S.hlat emb lam hF).L ↔ e x ∈ (S'.hlat emb lam hF').L) ∧
        ∀ x, S'.embF emb σ lam hF' (e x) = fun c => S.embF emb σ lam hF x (e0.symm c) := by
  let f : S.FormsK emb lam hF →ₗ[K] S'.FormsK emb lam hF' :=
    { toFun := fun x => ⟨fun c => x.1 (e0.symm c), mem_formsK emb lam S' hS' hF' _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : S'.FormsK emb lam hF' →ₗ[K] S.FormsK emb lam hF :=
    { toFun := fun y => ⟨fun c => y.1 (e0 c), mem_formsK emb lam S hS hF _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, ?_, ?_⟩
  · ext y c
    simp [f, g]
  · ext x c
    simp [f, g]
  · intro x
    constructor
    · intro hx c
      have h1 := hx (e0.symm c)
      have h2 := hL (e0.symm c)
      rw [Equiv.apply_symm_apply] at h2
      show x.1 (e0.symm c) ∈ delAtr emb lam (S'.Lsh c.1 (S'.rep c))
      rw [h2]
      exact h1
    · intro hx c
      have h1 : x.1 (e0.symm (e0 c)) ∈ delAtr emb lam (S'.Lsh (e0 c).1 (S'.rep (e0 c))) := hx (e0 c)
      rw [hL c, Equiv.symm_apply_apply] at h1
      exact h1
  · intro x
    rfl
end Gen

attribute [local instance] GlobalTheory.Mem.Col2.starE


set_option maxHeartbeats 1600000 in
theorem law0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ l : I.Laws, I.Law0 l := by
  intro B X I hI l u a
  obtain ⟨e, he1, he2⟩ := forms_equiv B.fields.emb B.embLL (lamT (B.hcW u) 0) (I.stp u I.mu0 0) (I.stp u a 0)
    (l.lev u I.mu0).free0 (l.lev u a).free0 ((l.fmL u I.mu0).fam 0) ((l.fmL u a).fam 0) (I.eCls0 l u a)
    (fun c => by
      have h := (_root_.GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco I hI u a (l.idx0 a).some).2 c
      show ((I.stp u a 0).rep (I.cl0 u a (l.idx0 a).some c)).1.1.deco.1.Lsh = ((I.stp u I.mu0 0).rep c).1.1.deco.1.Lsh
      rw [h])
  exact ⟨e, he1, fun x => he2 x⟩

end GlobalTheory.Mem.Col2.StepZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.LiftGen

open GlobalTheory.RealWeil

theorem deriv_eq_of_norm {B H : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Φ : B →L[ℂ] H) {u v : ℝ → B} {A G A' : B} (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0)
    (hn : ∀ t : ℝ, ‖Φ (v t - v 0 - (t : ℂ) • A')‖ = ‖Φ (u t - u 0 - (t : ℂ) • A)‖) : Φ G = Φ A' := by
  have h1 : HasDerivAt (fun t => Φ (u t)) (Φ A) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  have h2 : HasDerivAt (fun t => Φ (v t)) (Φ G) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  refine h2.unique ?_
  rw [hasDerivAt_iff_isLittleO] at h1 ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h1 ⊢
  refine h1.congr_left fun t => ?_
  have := hn t
  rw [map_sub, map_sub, map_sub, map_sub, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul] at this
  simp only [sub_zero]
  exact this.symm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem deriv_om (hψ : IsStdChar D ψ (-1)) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : GlobalTheory.Ker.IsWeak ψ S T om) (p : GA D S × GA D T) {u v : ℝ → BB ψ S T} {A G : BB ψ S T}
    (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0) (hut : ∀ t, IsThetaFunO ψ S T (u t).1)
    (hA : IsThetaFunO ψ S T A.1) (e : ∀ t, ((v t).1 : WO S T → ℂ) = om p (u t).1) :
    (G.1 : WO S T → ℂ) = om p A.1 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  let A' : BB ψ S T := toB hψ _ (hW.om_pres p _ hA)
  have hA' : (A'.1 : WO S T → ℂ) = om p A.1 := coe_toB _ _ _
  have hk : ∀ a b : BB ψ S T, IsThetaFunO ψ S T b.1 → (a.1 : WO S T → ℂ) = om p b.1 →
      ‖toL2 _ _ (μ.restrict 𝓕) a‖ = ‖toL2 _ _ (μ.restrict 𝓕) b‖ := by
    intro a b hb hab
    rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2, hab]
    exact hW.om_unit μ 𝓕 hμ h𝓕 p _ hb
  have key : toL2 _ _ (μ.restrict 𝓕) G = toL2 _ _ (μ.restrict 𝓕) A' := by
    refine deriv_eq_of_norm _ hu hv fun t => ?_
    have e1 : ((u t - u 0 - (t : ℂ) • A).1 : WO S T → ℂ) =
        ((u t).1 : WO S T → ℂ) - ((u 0).1 : WO S T → ℂ) - (t : ℂ) • (A.1 : WO S T → ℂ) := rfl
    have e2 : ((v t - v 0 - (t : ℂ) • A').1 : WO S T → ℂ) = om p (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1, map_sub, map_sub, map_smul, ← e, ← e, ← hA']
      rfl
    have h3 : IsThetaFunO ψ S T (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1]
      exact (thetaSub ψ S T).sub_mem ((thetaSub ψ S T).sub_mem (hut t) (hut 0)) ((thetaSub ψ S T).smul_mem _ hA)
    exact hk _ _ h3 e2
  have h4 := lintegral_norm_sq_eq_toL2 (μ.restrict 𝓕) (G - A')
  rw [map_sub, key, sub_self, enorm_zero, zero_pow two_ne_zero,
    lintegral_eq_zero_iff ((G - A').1.continuous.measurable.enorm.pow_const 2)] at h4
  have h5 := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ (G - A').1.continuous
    (BB_norm_periodic hψ _) (by filter_upwards [h4] with x hx; simpa using hx)
  rw [← hA']
  exact sub_eq_zero.1 h5

theorem hasDerivAt_om : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∀ p w, HasDerivAt (fun t => om (p * γ t) F.1 w) (om p (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F).1 w) 0 := by
  intro D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨lam, hlam⟩ := _root_.GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨x, d, -, hxd⟩ := _root_.GlobalTheory.Mem.Lift.exists_isCCR_theta D θ σ h ψ hψ S T
  refine ⟨lam, fun F hF p w => ?_⟩
  obtain ⟨u, hu, hud⟩ := hlam F hF
  have hA : IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F).1 := by
    have h1 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨F.1, hF⟩).2
    rw [hxd X ⟨F.1, hF⟩ F rfl] at h1
    exact (thetaSub ψ S T).add_mem h1 ((thetaSub ψ S T).smul_mem lam hF)
  have : IsTopologicalGroup (GA D S) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S).2.2.2.2.1
  have : IsTopologicalGroup (GA D T) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T).2.2.2.2.1
  have hn : ∀ V : HSp D, (GinfC V).Normal := fun V => MonoidHom.normal_ker _
  obtain ⟨lam', hlam'⟩ := _root_.GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ S T om hW hc (fun t => p * γ t * p⁻¹)
    ((continuous_const.mul hγ).mul continuous_const) (fun s t => by rw [hadd]; group)
    (fun t => ⟨(hn S).conj_mem _ (hinf t).1 p.1, (hn T).conj_mem _ (hinf t).2 p.2⟩)
    (mM θ S T p * X * mM θ S T p⁻¹) (fun k l => by
      simp only [map_mul, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun j _ => (HasDerivAt.fun_sum fun i _ => (hX i j).const_mul _).mul_const _)
  obtain ⟨v, hv, hvd⟩ := hlam' (toB hψ _ (hW.om_pres p _ hF)) (by rw [coe_toB]; exact hW.om_pres p _ hF)
  have e : ∀ t, ((v t).1 : WO S T → ℂ) = om (p * γ t) F.1 := fun t => by
    rw [hv, coe_toB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  have key := deriv_om hψ hW p hud hvd (fun t => by rw [hu]; exact hW.om_pres _ _ hF) hA
    (fun t => by rw [e, hu, map_mul, Module.End.mul_apply])
  rw [← key]
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hvd
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  exact (congrFun (e t) w).symm

end GlobalTheory.Mem.LiftGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HermTransport

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open scoped TensorProduct

theorem reGL_refl_apply' {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  ext a b
  simp [reGL]

theorem reGL_refl_hom' {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_refl_apply' R g

omit [StarRing E] in
theorem reL_refl' {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x
  simp [reL, reV]

theorem classTie_of_reindex (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) {σ : E →ₐ[F] E}
    (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ a b, J a b = S.gram (Fin.cast h.symm a) (Fin.cast h.symm b))
    {U' : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))} {Lb' : Submodule (𝓞 E) (Fin n → E)}
    {cl cl' : Type} (e : cl' ≃ cl) {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) S.V)
    (y : cl → UPts σ J (Formalism.L2.Herm.Af F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) :
      ClassSet ((ratPts σ J (Formalism.L2.Herm.Af F)).subgroupOf (UPts σ J (Formalism.L2.Herm.Af F)))
        (U'.subgroupOf (UPts σ J (Formalism.L2.Herm.Af F))))))
    (y_lat : ∀ c (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      x ∈ Formalism.L2.Herm.hatL (F := F) (reL h (Formalism.L2.Herm.crdLat S (lat c))) ↔
        ((y c).1⁻¹).1 *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Lb')
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J)
    (stabI_inj : ∀ c, Function.Injective (stabI c))
    (stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (Formalism.L2.Herm.Af F)) γ.1 ∈ U'.map (MulAut.conj (y c).1).toMonoidHom)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) (U : Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (hLb : Lb' = reL h Lb) (hU : U' = U.map (reGL h _).toMonoidHom) :
    ∃ C : Formalism.L2.Herm.ClassTie hc S Lb U (fun c' => stab (e c')) (fun c' => lat (e c')),
      (∀ c', (y (e c')).1 = reGL h _ (C.y c').1) ∧ ∀ c' s, (stabI (e c') s).1 = reGL h _ (C.stabI c' s).1 := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := by
    ext a b
    simpa using hJ a b
  subst hLb
  subst hU
  have hU0 : U.map (reGL (rfl : S.rank = S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)).toMonoidHom = U := by
    rw [reGL_refl_hom', Subgroup.map_id]
  rw [hU0] at y_bij stabI_range
  simp only [reL_refl'] at y_lat
  refine ⟨⟨fun c' => y (e c'), y_bij.comp e.bijective, fun c' x => y_lat (e c') x, fun c' => stabI (e c'),
    fun c' => stabI_inj (e c'), fun c' γ => stabI_range (e c') γ⟩,
    fun c' => (reGL_refl_apply' _ _).symm, fun c' s => (reGL_refl_apply' _ _).symm⟩

end Gen

theorem latCrd_eq_reL (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    latCrd D i hi L = reL (rankN D i hi) (Formalism.L2.Herm.crdLat (D.sp.X i) L) := by
  ext x
  simp [latCrd, reL, Formalism.L2.Herm.crdLat, reV, Formalism.L2.Herm.crd]

theorem classTie_of_chart : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  intro D i hi T bad cl cl' e stab _ lat K T' f' L hLb hU
  exact classTie_of_reindex D.sp.cm (D.sp.X i) (rankN D i hi) rfl (fun a b => rfl) e lat K.y K.y_bij
    (fun c x => by rw [← latCrd_eq_reL]; exact K.y_lat c x) K.stabI K.stabI_inj K.stabI_range L.Lb L.U hLb hU

end GlobalTheory.HermTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatibleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embeddings_tower_compatible : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (_ : IsPlaceOver A v'), IsLocalExt L h → ∀ (ι : Ω →ₐ[K] Kbar v) (ι' : Ω →ₐ[L] Kbar v'), IsLocEmb A v ι → IsLocEmb A v' ι' → ∃ (f : v.adicCompletion K →+* v'.adicCompletion L) (b : Kbar v ≃+* Kbar v'), Continuous f ∧ (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) ∧ (∀ z, b (ι z) = ι' z) ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ (letI := f.toAlgebra; Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L ∧ Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ (∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) ∧ ∀ z : L, Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z)) := by
  first | exact @GlobalTheory.LocalExtCompletion.exists_completion_ext | exact GlobalTheory.LocalExtCompletion.exists_completion_ext | (intros; apply GlobalTheory.LocalExtCompletion.exists_completion_ext <;> assumption)
end

