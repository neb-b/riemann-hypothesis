module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsQuotOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantsReductionIsLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaReductionBaseLatticeBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultisetBaseLatticeEqJumpsMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPolyBase
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneReductionFrobeniusPullbackEqShift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
public import Formalism.SatakeDualWeyl.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionBoundOfWeightHyp
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExactLocalConditionsTopCore
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TopDict

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

theorem mk_mem_unr_iff {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (I : Subgroup G) (z : ↥(Z1 π ⊤)) :
    (Submodule.Quotient.mk z : H1 π ⊤) ∈ unr π I ↔ ∃ b, ∀ g ∈ I, (z : G → M) g = π g b - b := by
  constructor
  · rintro ⟨z', ⟨b, hb⟩, h⟩
    obtain ⟨b', -, hb'⟩ := (Submodule.Quotient.eq _).mp h
    refine ⟨b - b', fun g hg => ?_⟩
    have h1 : π g b' - b' = (z' : G → M) g - (z : G → M) g := congrFun hb' g
    rw [hb g hg] at h1
    have h2 : (z : G → M) g = π g b - b - (π g b' - b') := by rw [h1]; abel
    rw [h2, map_sub]
    abel
  · rintro ⟨b, hb⟩
    exact ⟨z, ⟨b, hb⟩, rfl⟩

theorem admissibleExtension_iff_equivariantCoefIso {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ}
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (Γ : GalData G Qp LL O) (t : ℕ) (Ut : ZMod n → Multiset ℤ)
    {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (W : Representation O G M) (W' : Representation O G M') (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x))
    (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X)
    (hzz : ∀ g, z' g = LinearEquiv.rTensor X e (z g)) (hz : z ∈ Z1 (twCoef W χ X) ⊤)
    (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0) :
    Admissible PD emb Γ t Ut (Ea W χ hc ⟨z, hz⟩) ↔ Admissible PD emb Γ t Ut (Ea W' χ hc ⟨z', hz'⟩) := by
  obtain ⟨f, hf⟩ := (GlobalTheory.T.equivariantIso_transport_cocycles_extensions W W' e he χ X z z' hzz).2.1 hz hz' hc
  have hf' : ∀ g x, f.symm (Ea W' χ hc ⟨z', hz'⟩ g x) = Ea W χ hc ⟨z, hz⟩ g (f.symm x) :=
    fun g x => f.injective (by rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  exact ⟨fun h => h.of_equiv f hf, fun h => h.of_equiv f.symm hf'⟩

theorem WachMod_mem_B1_iff {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (z : G → M) : z ∈ B1 π ⊤ ↔ ∃ m, ∀ g, z g = π g m - m := by
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Submodule.mem_top, funext fun g => (hm g).symm⟩


set_option maxHeartbeats 8000000 in
theorem topCore_of_typings : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P), GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P →
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P → ∀ (K LL : FinExt l) (hA : CaseA K LL) (lam : ↥(OL LL)),
    Irreducible lam → tableLineDegreeTwo.TopCore (P.PD K) (H.W K 1 LL hA.2.2).emb lam (IK K) := by
  intro l _ P AI hT H hSA hSB hSC K LL hA lam hlam h5 t h w η typ U V _ _ _ _ _ _ _ _ _ _ _ ρ T₀ χ hyp X _ _ _
  let T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := LocLat.mk V ρ hyp.2.2.1 T₀
  have hcard := _root_.GlobalTheory.Per.LetterJumps.card_jumps_letter P AI hT H K LL hA V ρ U hyp.2.2.2.1 hyp.2.2.2.2.1
  obtain ⟨r, D, ε, hHyp, hDt, hcount, hchi⟩ := _root_.GlobalTheory.TopWindow.exists_topData_galData P H K LL hA lam hlam h5 t h w η typ U T χ hyp hcard
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hHyp.1⟩
  let S : TopSit P := ⟨K, LL, _, r, (H.W K 1 LL hA.2.2).emb, D, ⟨lam, T, χ 1, ε⟩, hHyp⟩
  have hkill : ∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0 := by
    obtain ⟨_, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    exact _root_.GlobalTheory.finite_module_killed_by_pow_of_not_isUnit (↥(OL LL)) lam hlam.not_isUnit X
  have hCl := GlobalTheory.AdmClosure.admissible_closed S
  obtain ⟨hL0, hLc⟩ := GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hCl (StdAdm.stdAdm S (CrysRules.crysCalc AI hT S) hCl)
  have hpoly : tableLineDegreeTwo.resPoly ρ χ t = tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t := by
    funext g
    change tableLineDegreeTwo.resPoly ρ χ t g = tableLineDegreeTwo.resPoly ρ S.Γ.chi D.t g
    rw [hDt]
    unfold tableLineDegreeTwo.resPoly
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [hchi c hc]
  have key : ∀ (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T'.ρ) (z : S.G → ↥L.T ⊗[S.O] X)
      (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤),
      tableLineDegreeTwo.IsAdmCoc (P.PD K) (H.W K 1 LL hA.2.2).emb lam (tableLineDegreeTwo.jTil U w t) (tableLineDegreeTwo.resPoly ρ χ t) L X (χ 1) z ↔
      ∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩) := by
    intro T' L z hz
    rw [hpoly]
    exact exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha =>
      GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext S (tableLineDegreeTwo.jTil U w t) hcount T' L X z hz a ha

  have ext_iff : ∀ (c : ℕ) {Mc : Type} [AddCommGroup Mc] [Module S.O Mc] (Wc : Representation S.O S.G Mc)
      (e : S.O ≃ₗ[S.O] Mc), (∀ g x, e (S.Γ.Wchi c g x) = Wc g (e x)) →
      ∀ (z₀ : S.G → S.O ⊗[S.O] X) (z : S.G → Mc ⊗[S.O] X), (∀ g, z g = LinearEquiv.rTensor X e (z₀ g)) →
      ∀ (hz₀ : z₀ ∈ Z1 (twCoef (S.Γ.Wchi c) S.Γ.χ₁ X) ⊤) (hz : z ∈ Z1 (twCoef Wc S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea Wc S.Γ.χ₁ ha ⟨z, hz⟩)) ↔
        (∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (S.Γ.Wchi c) S.Γ.χ₁ ha ⟨z₀, hz₀⟩))) := by
    intro c Mc _ _ Wc e he z₀ z hzz hz₀ hz
    refine exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha => ?_
    exact (admissibleExtension_iff_equivariantCoefIso (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut (S.Γ.Wchi c) Wc e he S.Γ.χ₁ X z₀ z hzz hz₀ hz ha).symm
  refine ⟨?_, ?_, ?_⟩
  · intro ρ' T₀' hρ' hTT z hz
    have hz' : z ∈ Z1 (twCoef (latRep T₀) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff T₀ X (χ 1)).2 z).1 hz
    rw [key T T₀ z hz', _root_.GlobalTheory.admissible_eventually_iff_mem_cls S S.Γ.W₀ X hkill (hL0 X).2.1 ⟨z, hz'⟩]
    have hA' := ((hSA K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2).2.2.2.2 X).2
    exact (Set.ext_iff.1 hA' (Submodule.Quotient.mk ⟨z, hz'⟩)).trans
      (SetLike.mem_coe.trans (GlobalTheory.T.period_data_dual_exact (P.PD K) T₀ ρ' T₀' X (χ 1) hρ' hTT z hz'))
  · intro c hc Lc z hz
    have hc' := Finset.mem_Icc.1 hc
    have hc1 : c ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨by omega, hc'.2⟩
    have hχc : S.Γ.chi c = χ c := hchi c hc1
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_stableLattice_integralCharacter LL (χ c) Lc
    have he' : ∀ g x, e (S.Γ.Wchi c g x) = latRep Lc g (e x) := fun g x =>
      (congrArg (fun θ : S.G →* S.Oˣ => e (Formalism.GaloisCohomology.scalRep S.O θ g x)) hχc).trans (he g x)
    let z₀ : S.G → S.O ⊗[S.O] X := fun g => (LinearEquiv.rTensor X e).symm (z g)
    have hzz : ∀ g, z g = LinearEquiv.rTensor X e (z₀ g) := fun g => (LinearEquiv.apply_symm_apply _ _).symm
    obtain ⟨hZ, -, hB, -⟩ := GlobalTheory.T.equivariantIso_transport_cocycles_extensions (S.Γ.Wchi c) (latRep Lc) e he' (χ 1) X z₀ z hzz
    have hz' : z ∈ Z1 (twCoef (latRep Lc) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff Lc X (χ 1)).2 z).1 hz
    have hz₀ := hZ.2 hz'
    have hcont := (hyp.2.2.2.2.2 c hc1).2.1
    let Tc : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      LocLat.mk ↥LL.1 (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c))) (fun x => hcont.mul continuous_const) Lc
    rw [key Tc Lc z hz', ext_iff c (latRep Lc) e he' z₀ z hzz hz₀ hz',
      _root_.GlobalTheory.admissible_eventually_iff_mem_cls S (S.Γ.Wchi c) X hkill ((hLc c (by omega) (by rw [hDt]; exact hc'.2)) X).2.1 ⟨z₀, hz₀⟩]
    have hB' := hSB K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp c hc'.1 (by rw [hDt]; exact hc'.2) X
    change _ ∈ adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi c) X ↔ _
    rw [show adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi c) X = {0} from hB',
      Set.mem_singleton_iff, Submodule.Quotient.mk_eq_zero]
    change z₀ ∈ B1 (twCoef (S.Γ.Wchi c) S.Γ.χ₁ X) ⊤ ↔ _
    rw [hB, WachMod_mem_B1_iff]
    exact exists_congr fun m => forall_congr' fun g =>
      iff_of_eq (congrArg (fun y => z g = y - m) ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff Lc X (χ 1)).1 g m).symm)
  · intro L₁ z hz
    have h1 : 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨le_rfl, hyp.1⟩
    have hχc : S.Γ.chi 1 = χ 1 := hchi 1 h1
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_stableLattice_integralCharacter LL (χ 1) L₁
    have he' : ∀ g x, e (S.Γ.Wchi 1 g x) = latRep L₁ g (e x) := fun g x =>
      (congrArg (fun θ : S.G →* S.Oˣ => e (Formalism.GaloisCohomology.scalRep S.O θ g x)) hχc).trans (he g x)
    let z₀ : S.G → S.O ⊗[S.O] X := fun g => (LinearEquiv.rTensor X e).symm (z g)
    have hzz : ∀ g, z g = LinearEquiv.rTensor X e (z₀ g) := fun g => (LinearEquiv.apply_symm_apply _ _).symm
    obtain ⟨hZ, -, -, hU⟩ := GlobalTheory.T.equivariantIso_transport_cocycles_extensions (S.Γ.Wchi 1) (latRep L₁) e he' (χ 1) X z₀ z hzz
    have hz' : z ∈ Z1 (twCoef (latRep L₁) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff L₁ X (χ 1)).2 z).1 hz
    have hz₀ := hZ.2 hz'
    have hcont := (hyp.2.2.2.2.2 1 h1).2.1
    let Tc : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      LocLat.mk ↥LL.1 (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ 1))) (fun x => hcont.mul continuous_const) L₁
    rw [key Tc L₁ z hz', ext_iff 1 (latRep L₁) e he' z₀ z hzz hz₀ hz',
      _root_.GlobalTheory.admissible_eventually_iff_mem_cls S (S.Γ.Wchi 1) X hkill ((hLc 1 le_rfl (by rw [hDt]; exact hyp.1)) X).2.1 ⟨z₀, hz₀⟩]
    have hC' := hSC K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2 X
    change _ ∈ adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi 1) X ↔ _
    rw [hC', GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia_eq_unr]
    rw [SetLike.mem_coe, mk_mem_unr_iff, hU]
    exact exists_congr fun m => forall_congr' fun g => forall_congr' fun _ =>
      iff_of_eq (congrArg (fun y => z g = y - m) ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff L₁ X (χ 1)).1 g m).symm)

end GlobalTheory.TopDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModThOfPres
section
noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.BasePairs

def RedN {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P} {S : TopSit P} {k : Type} [Field k]
    [Algebra S.O k] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {F : DFun R S.n S.G}
    {τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))} {γ : (S.W H).Gam} (p : Pres (S.W H) F ι τ γ)
    (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)) (N : Lats k S.n A.m) :
    Prop :=
  ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y

theorem exists_modTh_of_pres {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P} {S : TopSit P} {k : Type}
    [Field k] [Algebra S.O k] [CharP k l] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {F : DFun R S.n S.G}
    {τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))} {γ : (S.W H).Gam} (p : Pres (S.W H) F ι τ γ)
    (hC : S.CrysCalc) (hk : S.IsRes k) (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι)
    (hτ : ∀ i, (S.W H).emb (τ i) = S.emb i) (hγ : ((S.W H).χΓ γ : S.O) = 1 + (l : S.O))
    (hQ : GlobalTheory.WachUse.QN (S.W H)) :
    ∃ M : ModTh F S.D, (∀ σ, (M.ω σ : k) = algebraMap S.O k (S.Γ.ε σ)) ∧
      (∃ q : ↥S.Γ.T₀.L.T →ₗ[S.O] (Fin M.T.m → k), Function.Surjective q ∧
        KerIs S.Γ.lam q ∧ ∀ σ x, q (twistRep S.Γ.W₀ S.Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x)) ∧
      ∀ (A : Ob k S.G) (N : Type) [AddCommGroup N] [Module S.O N] (π : Representation S.O S.G N)
        (e : N ≃ₗ[S.O] (Fin A.m → k)), S.admitted π → (∀ σ x, e (twistRep π S.Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) →
        ∃ L, M.Model A L := by
  have hG : IsTopGal (P.PD S.K) S.emb S.D S.Γ := S.hyp.2.1
  have : FiniteDimensional ℚ_[l] ↥S.LL.1 := S.LL.2
  have : IsDiscreteValuationRing S.O := by
    unfold TopSit.O Formalism.BasicNotions.Loc.OL
    exact GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l ↥S.LL.1
  have : IsFractionRing S.O ↥S.LL.1 := by
    unfold TopSit.O Formalism.BasicNotions.Loc.OL
    exact GlobalTheory.isFractionRing_integralClosure_padicInt l ↥S.LL.1
  have hθ : IsCrysChar (P.PD S.K) S.emb S.Γ.χ₁⁻¹ (fun i => -S.D.w i) :=
    (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hG.2.1 hG.2.2.1).2
  have hlam : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  have hpoly : ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ),
      Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U →
      ∀ N : Lats k S.n A.m, RedN p T A q N → ∀ (i : ZMod S.n) (s : ℕ),
      (∀ u ∈ U i, ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) → EPoly ((F.D A).γ i) (N i) s := by
    intro T A q U hq hK hc N hN i s hs
    exact BaseLatticeE.ePoly_base H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN i s hs
  exact exists_real hθ hk hlam hC.1 hC.2.1 p.obj
    (fun T A q U hq hK hc => _root_.GlobalTheory.Present.RedLat.red_isLat H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc)
    (fun T A q U hq hK hc N hN w w' hw =>
      _root_.GlobalTheory.BaseABC.base_abc H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN w w' hw)
    (fun T A q U hq hK hc N hN i x =>
      _root_.GlobalTheory.BaseSen.sen_base H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN i x)
    hpoly
    (fun T A q U hq hK hc N hN a hm ha i =>
      _root_.GlobalTheory.RankOneReduction.pull_eq_sh H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN a hm ha i)
    (fun T A q U hq hK hc T' A' q' U' hq' hK' hc' Z C r V hr hKr hcr f g a b hb hs ha hb' hfa hgb
        N N' L hN hN' hL i =>
      GlobalTheory.Present.SumRed.reduction_sum H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc T' A' q' U' hq' hK'
        hc' Z C r V hr hKr hcr f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i)
    hG hC.2.2.1 (fun ω hω e h0 h1 => omega_pow_ne_one S k ω hω e h0 h1)

theorem real_of_presented : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P)
    (E : LocFon l P AI H) (S : TopSit P), S.RealD H → GlobalTheory.WachUse.QN (S.W H) → S.CrysCalc → S.Real := by
  intro l _ P AI H _ S hR hQ hC
  unfold TopSit.Real
  intro k _ _ _ hk
  have h1 := @hR k _ _ _ hk
  obtain ⟨R, ι, hι, F, τ, γ, hτ, hγ, hp⟩ := h1
  have h2 := exists_modTh_of_pres (H := H) (S := S) (k := k) (R := R) (ι := ι) (F := F)
    (τ := τ) (γ := γ) hp.some hC hk hι hτ hγ hQ
  exact ⟨R, ι, hι, F, h2⟩

end GlobalTheory.BasePairs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.SplitDecl

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem embTypeUc_iff (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    EmbeddingTypes.EmbTypeUc τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i false w hw τ := by
  constructor
  · rintro ⟨h1, φ, hφ, h2⟩
    refine ⟨h1, (starRingEnd ℂ).comp φ, ?_, fun x y hy => by simpa using h2 x y hy⟩
    show ((starRingEnd ℂ).comp φ).comp (D.host.conj : D.host.E →+* D.host.E) ∈
      D.host.cmType
    have : ((starRingEnd ℂ).comp φ).comp (D.host.conj : D.host.E →+* D.host.E) = φ := by
      ext1 x
      simp [GlobalTheory.SplitRowProbe.conj_sqrt]
    rw [this]; exact hφ
  · rintro ⟨h1, ψ, hψ, h2⟩
    refine ⟨h1, ψ.comp (D.host.conj : D.host.E →+* D.host.E), hψ, fun x y hy => ?_⟩
    rw [h2 x y hy]
    simp [GlobalTheory.SplitRowProbe.conj_sqrt]

theorem embTypeUe_iff (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    EmbeddingTypes.EmbTypeUe ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  cases ep
  · simp only [EmbeddingTypes.EmbTypeUe, Bool.false_eq_true, if_false]
    exact embTypeUc_iff τ
  · simp only [EmbeddingTypes.EmbTypeUe, if_true]
    rfl

theorem plTypeUe_iff (ep : Bool) :
    EmbeddingTypes.PlTypeUe i w hw ep ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.PlIn (N := D.nd) D.nbr i ep w hw := by
  constructor
  · intro h
    exact ⟨GlobalTheory.SplitRowProbe.nonempty_emb D i w hw, fun τ => (embTypeUe_iff ep τ).1 (h τ)⟩
  · intro h τ
    exact (embTypeUe_iff ep τ).2 (h.2 τ)

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

def decl (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) : TruncatedSeriesCountingIdentities.Decl D i where
  row := (placesOver_finite D.host.E (D.nd.l i) hl).toFinset.filter
    (fun v => v ∉ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep)
  col := (placesOver_finite D.host.E (D.nd.l i) hl).toFinset.filter
    (fun v => v ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep)
  disj := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    exact (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
  cover := by
    intro v
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    tauto

theorem mem_col (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) (v) :
    v ∈ (decl D i hl ep).col ↔ v ∈ placesOver D.host.E (D.nd.l i) ∧
      v ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
  simp [decl]

theorem mem_row (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) (v) :
    v ∈ (decl D i hl ep).row ↔ v ∈ placesOver D.host.E (D.nd.l i) ∧
      v ∉ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
  simp [decl]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) →
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.hypL i := by
  intro D i ep hs
  obtain ⟨hPl, hTy⟩ := GlobalTheory.SplitRowAll.splitRow_at D
  have hP := hPl _ hs
  have hT := hTy i hs
  have hl : D.nd.l i ≠ 0 := hs.1.ne_zero
  refine ⟨⟨decl D i hl ep, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_col, plTypeUe_iff]
    constructor
    · rintro ⟨-, hv', h⟩
      exact h
    · intro h
      exact ⟨hv, hv, h⟩
  · intro v
    rw [mem_row]
    constructor
    · rintro ⟨hv, hnc⟩
      obtain ⟨-, ⟨v', hv', hc⟩, -⟩ := hP v hv
      have hx := (hT.2.2.2 ep).1 v hv v' hc
      have hv'c : v' ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
        rcases hx with h | h
        · exact absurd h.1 hnc
        · exact h.1
      exact ⟨v', (mem_col D i hl ep v').2 ⟨hv', hv'c⟩, GlobalTheory.Proof.ConjugatePlaces.isConjPl_symm hc⟩
    · rintro ⟨u, hu, hc⟩
      obtain ⟨hu, huc⟩ := (mem_col D i hl ep u).1 hu
      obtain ⟨-, ⟨u', hu', hc'⟩, -⟩ := hP u hu
      have he : v = u' := GlobalTheory.Proof.ConjugatePlaces.isConjPl_unique hc hc'
      subst he
      refine ⟨hu', fun hvc => ?_⟩
      rcases (hT.2.2.2 ep).1 u hu v hc with h | h
      · exact h.2 hvc
      · exact h.2 huc
  · obtain ⟨-, h5, -, -, hg, hcls⟩ := hs
    exact ⟨le_trans (by norm_num) h5, Or.inl hcls, fun _ v hv => (hP v hv).1, hg 0, hg 1⟩

end GlobalTheory.SplitDecl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSumOfRank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.IndexCount

theorem rank_le (D : D7) (i : Fin D.R.m) : 2 * (Wc D i).rank + 5 ≤ (Vc D i).rank := by
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have := D.R.rank_add_five_le
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  omega

theorem two_le_absNorm {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem indexSum_of_rank {D : D7} (W : HSp D) (n : ℕ) (hn : 2 * W.rank + 5 ≤ n) : IndexSum W n := by
  let q : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ)
  let z : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v =>
    (∏ i ∈ Finset.range W.rank, (1 - q v ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1
  have hq : ∀ v, 2 ≤ q v := fun v => two_le_absNorm v
  have hσ : (W.rank : ℝ) + 5 / 2 ≤ (n : ℝ) / 2 := by
    have : ((2 * W.rank + 5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this; linarith
  have hz : ∀ v, z v < 1 ∧ z v ≤ 16 * q v ^ (-(3 : ℝ)) := fun v => GlobalTheory.lattice_zeta_sq_bound (q v) W.rank ((n : ℝ) / 2) (hq v) hσ
  have h8 : ∀ v, 8 * q v ^ (-(4 : ℝ)) ≤ 8 * q v ^ (-(3 : ℝ)) ∧ 8 * q v ^ (-(4 : ℝ)) ≤ 1 / 2 := by
    intro v
    have h1 : (1 : ℝ) ≤ q v := le_trans (by norm_num) (hq v)
    have hle : q v ^ (-(4 : ℝ)) ≤ q v ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    refine ⟨by linarith, ?_⟩
    have : q v ^ (-(4 : ℝ)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (hq v) (by norm_num)
    have h2 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h2] at this; linarith
  refine ⟨fun v => max (z v) (8 * q v ^ (-(4 : ℝ))), ?_, ?_, ?_⟩
  · have hs : Summable fun v : HeightOneSpectrum (𝓞 D.host.F) => 16 * q v ^ (-(3 : ℝ)) :=
      (GlobalTheory.summable_absNorm_rpow_heightOneSpectrum D.host.F 3 (by norm_num)).mul_left 16
    refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_) hs
    · exact le_trans (by positivity) (le_max_right _ _)
    · refine max_le (hz v).2 ?_
      have h3 : 0 ≤ q v ^ (-(3 : ℝ)) := by positivity
      linarith [(h8 v).1]
  · intro v
    exact max_lt (hz v).1 (by linarith [(h8 v).2])
  · intro v f hf C hC hd
    rcases _root_.GlobalTheory.PlaceDichotomy.split_or_inert_idem D v f hf with hs | hi
    · exact le_trans (_root_.GlobalTheory.SplitIndexSum.indexSum_split D W n hn v f hf hs C hC hd) (le_max_left _ _)
    · exact le_trans (_root_.GlobalTheory.InertIdx.indexSum_inert D W n hn v f hf hi C hC hd) (le_max_right _ _)

theorem indexSum_holds : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, IndexSum (Wc D i) (Vc D i).rank := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i
  exact indexSum_of_rank (Wc D i) (Vc D i).rank (rank_le D i)

end GlobalTheory.IndexCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionBoundOfWeightHypStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_bound_of_weight_hyp : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (a b : ℤ) (hle : Gj K s ≤ GK K), a < b → HypW S E T M0 h0 → letI := zlMod LL T; letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b)) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; TorsKilledBy (repQ (D.locA l) (Gj K s) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) (l : ℤ_[l]) ((l : ℤ_[l]) ^ cLL l (mN l s (M0 + h0)) (vdegMs S (mN l s (M0 + h0))) (Jset S T) a b) := by
  first | exact @GlobalTheory.TorsLL.torsion_bound_at_level | exact GlobalTheory.TorsLL.torsion_bound_at_level | (intros; apply GlobalTheory.TorsLL.torsion_bound_at_level <;> assumption)
end

