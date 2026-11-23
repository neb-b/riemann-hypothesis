module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingInMovedRowData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProvisionalRowsFurtherCompatibilitiesAtState
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0467

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelsExtendedDataCorrespondFieldEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LevBC

theorem exists_intCast_of_card_prime {R : Type} [Ring R] (h : (Nat.card R).Prime) (x : R) : ∃ n : ℤ, (n : R) = x := by
  have hfin : Finite R := Nat.finite_of_card_ne_zero h.ne_zero
  have htop : AddSubgroup.zmultiples (1 : R) = ⊤ := by
    rcases h.eq_one_or_self_of_dvd _ (AddSubgroup.card_addSubgroup_dvd_card (AddSubgroup.zmultiples (1 : R))) with h1 | h1
    · exfalso
      have hb := AddSubgroup.eq_bot_of_card_eq _ h1
      have h10 : (1 : R) = 0 := by
        have : (1 : R) ∈ AddSubgroup.zmultiples (1 : R) := AddSubgroup.mem_zmultiples 1
        rw [hb] at this
        exact (AddSubgroup.mem_bot).1 this
      have : Subsingleton R := subsingleton_of_zero_eq_one h10.symm
      rw [Nat.card_unique] at h
      exact Nat.not_prime_one h
    · exact AddSubgroup.eq_top_of_card_eq _ h1
  have hx : x ∈ AddSubgroup.zmultiples (1 : R) := by rw [htop]; exact AddSubgroup.mem_top x
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  exact ⟨n, by rw [← hn, zsmul_one]⟩

theorem exists_intCast_vGs (B : Base) (px : PreX B.toPre) (PP : Pl B.host.E) (hPP : PP ∈ (B.primes px).vGs)
    (c : 𝓞 B.host.E ⧸ PP.asIdeal) : ∃ n : ℤ, (n : 𝓞 B.host.E ⧸ PP.asIdeal) = c := by
  classical
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B px
  have hi : ∃ i, PP ∈ (B.primes px).vG i := by
    rcases Finset.mem_union.1 hPP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hi
  have hn := hPr.vG_norm i PP hi
  have hp := hPr.g_prime i
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
  rw [← hn] at hp
  exact exists_intCast_of_card_prime hp c

theorem baseLevelCharacter_map_coefficientRingHom {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {LL LL' : Type} [CommRing LL] [CommRing LL']
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) (ψ' : ∀ PP : Pl E, AddChar (kP PP) LL') (φ : LL →+* LL')
    (h : ∀ PP ∈ Pg, ∀ c, ψ' PP c = φ (ψ PP c)) (x : (P0 Pg r ψ).H) (x' : (P0 Pg r ψ').H) (hx : (x : G0 Pg r) = x') :
    (((P0 Pg r ψ').chi x' : LL'ˣ) : LL') = φ (((P0 Pg r ψ).chi x : LLˣ) : LL) := by
  obtain ⟨x, hxm⟩ := x
  obtain ⟨x', hxm'⟩ := x'
  simp only at hx
  subst hx
  show ((((∏ PP : ↥Pg, (addCharHom (ψ' PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hxm'⟩ : LL'ˣ)) : LL') =
    φ (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hxm⟩ : LLˣ) : LL)
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LLˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LLˣ) := ⟨fun _ _ _ => rfl⟩
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LL'ˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LL'ˣ) := ⟨fun _ _ _ => rfl⟩
  rw [prod_apply, prod_apply, Units.coe_prod, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact h PP.1 PP.2 _

theorem lev_bc (B B' : Base) (h : B'.toPre = B.toPre) (px : PreX B.toPre) (px' : PreX B'.toPre) (hp : HEq px' px)
    (I : ColIn B px) (I' : ColIn B' px') (hI : I.Ok) (hI' : I'.Ok) (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x)
    (g : Gc B px) (g' : Gc B' px') (hg : HEq g' g) :
    (g' ∈ lev0 I' ↔ g ∈ lev0 I) ∧ ∀ (h0 : g ∈ lev0 I) (h0' : g' ∈ lev0 I'),
      ((chr0 I' ⟨g', h0'⟩ : B'.LLˣ) : B'.LL) = φ (chr0 I ⟨g, h0⟩ : B.LLˣ) := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h px px' hp I I' hI hI' φ hφ g g' hg
  subst h
  cases hp
  cases hg
  refine ⟨Iff.rfl, fun h0 h0' => ?_⟩
  refine baseLevelCharacter_map_coefficientRingHom _ _ _ _ φ (fun PP hPP c => ?_) ⟨_, h0⟩ ⟨_, h0'⟩ rfl
  rw [psiC_of_mem _ hPP, psiC_of_mem I' hPP]
  obtain ⟨n, hn⟩ := exists_intCast_vGs _ _ PP hPP (Formalism.L2.Col.redP PP P'.host.xi0 * c)
  have e1 := hI'.weil ⟨PP, hPP⟩ c n hn.symm
  have e2 := hI.weil ⟨PP, hPP⟩ c n hn.symm
  have e3 := hφ (I.Ch.psi0 ⟨PP, hPP⟩ c)
  exact RingHom.injective _ (e1.trans (e2.symm.trans e3.symm))

end GlobalTheory.Mem.R3.LevBC

namespace GlobalTheory.Mem.R3.Rw

theorem extN_baseLevel_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (g' ∈ (z'.F.lv2.lvl false).P ↔ g ∈ (z.F.lv2.lvl false).P) ∧ ∀ (hg : g ∈ (z.F.lv2.lvl false).P) (hg' : g' ∈ (z'.F.lv2.lvl false).P), (((z'.F.lv2.lvl false).ψ ⟨g', hg'⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.F.lv2.lvl false).ψ ⟨g, hg⟩ : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w hE _ _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ hφ g g' hg
  exact GlobalTheory.Mem.R3.LevBC.lev_bc B B' hE.1 w.px w'.px hpx w.I w'.I w.ok w'.ok φ hφ g g' hg

end GlobalTheory.Mem.R3.Rw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevOffType
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.Col2.TC.chartLev_off_type : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), (∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → ∀ x, x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Uloc v ↔ x ∈ F.levJ.Uloc v := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF h1 β0 v hv x
  have hi : B.R.m - 1 ≤ (I.rec7 l Z).R.m := Nat.sub_le _ _
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) hi).1
  haveI : NeZero ((I.rec7 l Z).R.N (B.R.m - 1)) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  obtain ⟨k, H⟩ := hF.mid (B.R.m - 1) h1 (succ_pred_m _)
  have hLbE : (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Lb = F.levJ.Lb := F.levJ_Lb h1 β0
  have hLb : ∀ x, x ∈ F.levJ.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N (B.R.m - 1)) (X.piT u) := by
    intro x
    rw [← hLbE]
    exact H.lb _ x
  have hL : F.levJ.Lb = rll_dLat ((I.rec7 l Z).R.N (B.R.m - 1)) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 F.levJ.Lb ?_
    rw [hF.piU]; exact hLb
  have hnb : v ∉ badG (I.rec7 l Z) := by
    rintro (h | h)
    · exact hv 0 h
    · exact hv 1 h
  by_cases hT : (((I.rec7 l Z).mem u).A.T : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · have e1 := GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev F.atT.piU (s F.atT.piU) rfl hpq hTp (hLbE.trans hL) v hT (_root_.GlobalTheory.LevelUnif.dvd_of_val_lt_one (I.rec7 l Z) u F.atT v hT) x
    have e2 := GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram F.levJ F.atT.piU (s F.atT.piU) rfl hpq hTp hL v hT (_root_.GlobalTheory.LevelUnif.dvd_of_val_lt_one (I.rec7 l Z) u F.atT v hT) x
    rw [hLbE] at e1
    exact e1.trans e2.symm
  · have e1 := (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Uloc_hyp v hnb hT
    have e2 := F.levJ.Uloc_hyp v hnb hT
    rw [hLbE] at e1
    rw [e1, e2]
    exact Iff.rfl


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.Col2.TC.chartLev_stab_vec : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → (∀ j v h, F.glevJ.fr j v h = 1) → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)), ∃ w : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v, ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) x, x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Uloc v ↔ (x ∈ F.levJ.Uloc v ∧ ∀ j (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) *ᵥ w j v hv = w j v hv) := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF hfr h1 β0
  haveI : NeZero ((I.rec7 l Z).R.N (B.R.m - 1)) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.Mem.Col2.TC.typeRead_core I hI hP l Z u F hF hfr h1 β0
  refine ⟨w, fun v x => ?_⟩
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) = 1 :=
    ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  by_cases hv : ∃ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · have hput : ∀ (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f (badG (I.rec7 l Z))),
        x ∈ S.Uloc v ↔ rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ S.U := by
      intro S
      constructor
      · intro hx
        have hxU := S.Uloc_le v hx
        rw [hgram] at hxU
        refine (S.U_eq _).2 ⟨?_, fun v' => ?_⟩
        · have := rll_put_mem_UAd (I.rec7 l Z).sp.cm ((I.rec7 l Z).R.N (B.R.m - 1)) v hxU
          rw [hgram]; exact this
        · by_cases e : v' = v
          · subst e; rw [rll_put_self]; exact hx
          · rw [rll_put_ne _ v v' e]; exact one_mem _
      · intro hx
        have := ((S.U_eq _).1 hx).2 v
        rwa [rll_put_self] at this
    rw [hput]
    constructor
    · intro hx
      have hJ : rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ F.levJ.U := F.levJ_le h1 β0 hx
      have hxJ : x ∈ F.levJ.Uloc v := by
        have := ((F.levJ.U_eq _).1 hJ).2 v
        first
          | (convert this using 2; exact (rll_put_self _ v x).symm)
          | exact (congrArg (· ∈ F.levJ.Uloc v) (rll_put_self ((I.rec7 l Z).R.N (B.R.m - 1)) v x)).mp this
          | exact (rll_put_self ((I.rec7 l Z).R.N (B.R.m - 1)) v x) ▸ this
      exact ⟨hxJ, (hw v hv x hxJ).1 hx⟩
    · rintro ⟨hxJ, hs⟩
      exact (hw v hv x hxJ).2 hs
  · push_neg at hv
    rw [GlobalTheory.Mem.Col2.TC.chartLev_off_type I hI hP l Z u F hF h1 β0 v (fun j => hv j) x]
    exact ⟨fun h => ⟨h, fun j hj => absurd hj (hv j)⟩, fun h => h.1⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassifiedTorusTorsionPointEqUniformisationTorus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

noncomputable section

namespace GlobalTheory.TorusTorsionPoint

theorem eq_torus_of_classify : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), FormalEq P.U.toUnifPre x₀ g₀ → ∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) (τ : Multiplicative P.D.toPre.X →* A'ˣ) (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → ∀ (g : GtPt P.D.toPre (Over.mk (spMap (f.comp a)))), (∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ)))) → ∀ (h : Over.mk (spMap (f.comp a)) ⟶ N), GtPt.IsPull h.left g₀ g → h.left ≫ x₀.left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ := by
  intro E _ _ _ H R _ _ _ t P N g₀ x₀ hform A A' _ _ a ha f t₀ m₀ τ z hz g hg h hpull
  have ha' : ∀ x ∈ maximalIdeal R, (f.comp a) x = 0 := fun x hx => by
    rw [RingHom.comp_apply, ha x hx, map_zero]
  have hρ := GlobalTheory.TorusPart.map_pow_one_eq_zero ha
  have hρ' := GlobalTheory.TorusPart.map_pow_one_eq_zero ha'
  have eR : (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ =
      (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X ≫ (P.U.gt 0).i.left) ≫
        pullback.fst t.G.hom (thick R (maximalIdeal R) 0) := by
    rw [Over.comp_left, Category.assoc]
    have k := GlobalTheory.TorusPart.gtTorus_left (P.U.gt 0) hρ m₀.cart
    exact (congrArg (z.left ≫ ·) k).trans (by simp only [Category.assoc])
  have hN : (h.left ≫ x₀.left) ≫ t.G.hom = GlobalTheory.TorusPart.thickPt 0 hρ' ≫ thick R (maximalIdeal R) 0 := by
    rw [GlobalTheory.TorusPart.thickPt_thick, Category.assoc, Over.w x₀, Over.w h]; rfl
  let y₁ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 t.G).left :=
    pullback.lift (h.left ≫ x₀.left) (GlobalTheory.TorusPart.thickPt 0 hρ') hN
  let y₂ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 t.G).left :=
    z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X ≫ (P.U.gt 0).i.left
  have e₁ : h.left ≫ x₀.left = y₁ ≫ pullback.fst t.G.hom (thick R (maximalIdeal R) 0) :=
    (pullback.lift_fst _ _ _).symm
  have hP := (GlobalTheory.TorsionFormCompare.formalEq_iff P.U.toUnifPre x₀ g₀).1 hform
  have hc := hP 0 (Sp A') h.left y₁ e₁.symm
  obtain ⟨hb, hv⟩ := (GlobalTheory.FormalPoint.hasCoords_iff _ 0 g₀ h.left y₁).1 hc
  suffices hy : y₁ = y₂ by rw [eR, e₁, hy]
  refine GlobalTheory.TorusCoord.ext_of_val (P.U.gt 0) y₁ y₂ ?_ ?_
  · rw [hb, ← hpull.1, (hg 0).1, GlobalTheory.TorusCoord.pG_left]
    have hk : (P.U.gt 0).i.left ≫ (P.U.gt 0).q.left =
        (splitTorus _ P.D.toPre.X).hom ≫ eSec (thickObj R (maximalIdeal R) 0 P.D.toPre.P.A) := by
      have := congrArg Over.Hom.left (P.U.gt 0).isKernel.w
      rw [Over.comp_left, Over.comp_left] at this
      exact this
    have hE : eSec (thickObj R (maximalIdeal R) 0 P.D.toPre.P.A) ≫
        pullback.fst P.D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
        thick R (maximalIdeal R) 0 ≫ eSec P.D.toPre.P.A :=
      GlobalTheory.UnitValue.eSec_pullback_fst _ _
    have hz' : z.left ≫ (splitTorus (Sp A) P.D.toPre.X).hom = spMap f := Over.w z
    have hfa : spMap f ≫ spMap a = spMap (f.comp a) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    simp only [y₂, Category.assoc]
    rw [reassoc_of% hk, hE, ← Category.assoc (GlobalTheory.SplitTorus.bcMap _ _), GlobalTheory.SplitTorus.bcMap_hom,
      Category.assoc, reassoc_of% (GlobalTheory.TorusPart.thickPt_thick hρ), reassoc_of% hz', reassoc_of% hfa]
    rfl
  · intro χ w J hJ
    rw [hv χ w J hJ]
    have l₁ : val (g₀.s χ) h.left w J = gm (𝟙 _) w ⊤ (unitOn (τ (Multiplicative.ofAdd χ))) := by
      have c₁ := val_corr hJ (hpull.2 χ) (𝟙 _)
      rw [val_pull hJ, Category.id_comp] at c₁
      exact c₁.symm.trans (GlobalTheory.TorusTorsion.TorusVal.val_eq (hg χ) (𝟙 _) hJ)
    rw [l₁]
    let Z₀ : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) :=
      Over.mk ((z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X) ≫
        (splitTorus _ P.D.toPre.X).hom)
    let τ' : Z₀ ⟶ splitTorus _ P.D.toPre.X :=
      Over.homMk (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X) rfl
    have k := GlobalTheory.TorusCoord.val_t_act (P.U.gt 0) τ' 1 χ (𝟙 Z₀.left) w J hJ
    have k₁ : 𝟙 Z₀.left ≫ (τ' ≫ (P.U.gt 0).i * 1).left = y₂ := by
      rw [_root_.mul_one, Category.id_comp, Over.comp_left]
      simp only [τ', y₂, Over.homMk_left, Category.assoc]
    have k₂ : val ((P.U.gt 0).t χ) (𝟙 Z₀.left ≫ (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 t.G).left) w J = 1 := by
      have e : (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 t.G).left = Z₀.hom ≫ eSec (thickObj R (maximalIdeal R) 0 t.G) := by
        rw [Hom.one_def, Over.comp_left]; rfl
      rw [e, Category.id_comp, ← val_pull hJ, val_corr hJ ((P.U.gt 0).t_unit χ), val_one]
    have k₃ : GlobalTheory.splitTorusPointsEquiv _ P.D.toPre.X Z₀ τ' (Multiplicative.ofAdd χ) =
        unitOn (τ (Multiplicative.ofAdd χ)) := by
      refine Units.ext ?_
      rw [← hz χ, GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val,
        GlobalTheory.SplitTorus.charUnit_val]
      simp only [τ', Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        GlobalTheory.SplitTorus.bcMap_appTop_chi]
    rw [k₁, k₂, k₃, _root_.mul_one] at k
    exact k.symm

end GlobalTheory.TorusTorsionPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLayerConditionsTrueColumnsLaterStages
section
noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

variable {B : Base} {C : Cols B} {Z : Later B C} (Z' : Later B C)


set_option maxHeartbeats 4000000 in
def forms0Re {u : B.Word} (T : Forms0 (recOf Z) u) : Forms0 (recOf Z') u :=
  { T with
    atT := atTTRe Z' T.atT
    cls0 := clsRe Z' T.cls0
    val0 := valRe Z' T.val0
    lv0 := lvRe Z' T.lv0 }

set_option maxHeartbeats 4000000 in
theorem columnFormsAlongLaterStages_stageZero_eq (T : ColsTiedSym (recOf Z)) (u : B.Word) :
    ((colsRe Z' T).forms u).to0 = forms0Re Z' (T.forms u).to0 := rfl


open Formalism.MainNotions.G in
set_option maxHeartbeats 4000000 in
theorem forms0Re_setGat (g : ∀ u (w : (recOf Z).what₂.places.Pl),
      GIdx (recOf Z).host ((recOf Z).mem u).A.T ((recOf Z).what₂.places.resChar w) → GAtP ((recOf Z).what₂.places.resChar w))
    (hd : ∀ u w h, (g u w h).d = Module.finrank ℂ ((recOf Z).mem u).A.Mu0) {u : B.Word} (T : Forms0 (recOf Z) u) :
    forms0Re { Z with G := { Z.G with gat := g, gat_d := hd } } T = Formalism.L2.G.forms0Set (recOf Z) g hd T := rfl

end Re

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

section Std

variable (l : I.Laws) {Z : Later B (I.cols l)} (Z' : Later B (I.cols l))


set_option maxHeartbeats 8000000 in
theorem stdC_colsRe (T : ColsTiedSym (I.rec7 l Z)) (h : I.StdC l Z T) : I.StdC l Z' (colsRe Z' T) := fun u =>
  { h u with gl := { (h u).gl with } }


set_option maxHeartbeats 8000000 in
theorem stdLvC_colsRe (T : ColsTiedSym (I.rec7 l Z)) (u : B.Word) (h : I.StdLvC l Z u (T.forms u)) :
    I.StdLvC l Z' u ((colsRe Z' T).forms u) := h

end Std

variable (h : I.Ok) (p : TC.Pins B X) (l : I.Laws)

variable (Z : Later B (I.cols l))

theorem dGam_cols (u : B.Word) (a : I.ι) : ((I.cols l).chTw u a).DGam = DGam B.fields.E B.R := rfl

theorem colLay_of_tie (T : ColsTiedSym (I.rec7 l Z)) : ColLay (I.rec7 l Z) T.herm.base.lev0 (errOf T.herm) :=
  colLay_of_tied ⟨B, I.cols l, Z.W, Z.V, Z.S, Z.N, Z.G⟩ ⟨X⟩ (dGam_cols I l) T


open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl in
theorem colLay_colT : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z),
    ColLay (w.D Z) t.full.1.base.lev0 (Formalism.L2.Herm.toErrXS t.full.1) := by
  intro B f T w Z t
  have e : errOf t.C.herm = Formalism.L2.Herm.toErrXS t.full.1 :=
    GlobalTheory.Mem.Col2.TC.ExtraTie.errX_eq t.full.1 t.C.herm t.full.2 (errOf t.C.herm) (errOf_piG _) (errOf_piT _) (errOf_vPl _)
  have hl : t.full.1.base.lev0 = t.C.herm.base.lev0 :=
    congrArg (fun H : Formalism.L2.Herm.ColsHermS (w.D Z) => H.base.lev0) t.full.2
  rw [hl, ← e]
  exact colLay_of_tie w.I w.l Z t.C

end GlobalTheory.Mem.Top.ColOwe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruenceOneMatricesMemNhdsOneStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceOne_matrices_mem_nhds_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ N ∈ nhds (1 : GL (Fin n) (AfE F E)), ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → 0 < m →
      ∀ k : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k → GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k⁻¹ → k ∈ N := by
  first | exact @GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds | exact GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds | (intros; apply GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingOfRowLiftFamilyMovedData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

theorem readPk_pin_exists : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Inputs (w.D o.Z) → o.Fits → ∀ m : Moved o, ∃ (s : Side0 o) (r : ReadPk m s), r.Pin := by
  intro B f T w Z₀ hX Wt z₀ q o hIn hF m
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.Mem.R3.Rw.exists_side_reading_level_zero B f T w Z₀ hX Wt z₀ q o hIn hF m
  obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := _root_.GlobalTheory.Mem.R3.Rw.read_of_moved B f T w Z₀ hX Wt z₀ q o hIn hF m s
  obtain ⟨Z⟩ := hs Y h2 h9 h10 h11
  exact ⟨s, ⟨Y, Z, h1, h2, h3, h4, h5, h6, h7⟩, ⟨h8, h9, h10, h11, h12⟩⟩

end GlobalTheory.Mem.R3.Rw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProvisionalRowsFurtherCompatibilitiesAtStateStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.provisionalRows_furtherCompatibilities_at_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ t : RowsT K w x.o.Z P.Wt x.s.p0, t.r = x.rowsAre hη → Nonempty (RXs t) := by
  first | exact @GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state | exact GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state | (intros; apply GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state <;> assumption)
end

