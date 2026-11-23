module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatum
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjLiftData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_galConj_mu (R : RealDat D A Ks) (hL : R.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (μ' : (AE D)ˣ →* Circle) (hμ : ChiAt R i σ μ') :
    ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hL.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hL.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

theorem exists_galConj_eta (R : RealDat D A Ks) (hL : R.Is A.μ0) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (η' : (AE D)ˣ →* Circle) (hη : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η') :
    ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [GlobalTheory.EtaConjChar.twVal_half _ P (GlobalTheory.EtaConjChar.locK_eq_one hH hη.2.1 P), GlobalTheory.EtaConjChar.twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl,
    ← hL.eta.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl, ← hy1, ← hy2, hσ.1]

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q : Finset (Pl D.host.E)} (hQ : Q = ∅) (s : ℂ →+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x) :
    s ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ => χ, ξ⟩ x : ℂˣ) : ℂ) =
      ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (Units.map s.toMonoidHom).comp (χ PP), ξ'⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp [h1]

theorem is_congr {Γ Gr W : Type} [Group Γ] [Group Gr] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gr}
    {ρ : Γ →* Module.End ℂ W} {J J' : Subgroup Gr} (hJ : J = J') {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    (h : ∀ x hx hx', χ ⟨x, hx⟩ = χ' ⟨x, hx'⟩) {I : Type} [Fintype I] {y : I → Gr} {H : HMod (Gr → W)}
    (hH : H.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y)) : H.Is (Bridge.AdForms ι ρ J' χ') (Bridge.adInner ι J' y) := by
  subst hJ
  obtain rfl : χ = χ' := MonoidHom.ext fun x => h x.1 x.2 x.2
  exact hH


set_option maxHeartbeats 1000000 in
theorem isLiftDataC_of_liftData : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ μ' η', ChiAt R i σ μ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ s m, GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io ∧ IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) ∧ Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y ∧ H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L _ i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hL
  classical
  have : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  obtain ⟨s, hs⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL D.what₂.embLL σ
  have hE : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s := ⟨fun a => (hs a).symm, hσ⟩
  obtain ⟨hω, hvec, hio, -⟩ := hL
  obtain ⟨μH, hμ1, hμ2⟩ := exists_galConj_mu R hC.lev i σ s hE μ' hμ
  obtain ⟨ηH, hη1, hη2⟩ := exists_galConj_eta R hC.lev σ s hE η' hη
  have hQ := GlobalTheory.LiftLower.Q_base hC.lev
  let m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ := fun PP =>
    (Units.map (s : ℂ →+* ℂ).toMonoidHom).comp (R.chi ((i : ℕ) + 1) PP)⁻¹
  have hp : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.PrimeToHost R A.μ0 := by
    intro PP hPP
    rcases hPP with hPP | hPP
    · exact GlobalTheory.LiftScalarCompare.primeToHost hC.lev PP hPP
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsConjChars R i A.μ0 s μ' η' m := by
    refine ⟨μH, ηH, hμ1, hη1, hμ2, hη2, fun PP hPP a k u hk hu => ?_⟩
    have hg : PP ∈ R.Pg := hPP.resolve_right (by simp [hQ])
    have h1 := hμ1 PP k
    have h2 := hC.lev.chi i PP hg a k u hk hu
    rw [hC.lev.xi_base, mul_one] at h1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal, Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one] at h1
    apply Units.ext
    rw [h1, ← h2]
    rfl
  have hlv : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      (R.datWp i R.triv) (R.Q A.μ0) m f₀ f := by
    have hv := hvec.vec
    rw [hQ]
    unfold Datum.IsThPVecOf at hv
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec
    have hq : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
        Datum.omegaQ ∅ (Wc D i).rank m (-1) y = Datum.omegaQ ∅ (Wc D i).rank (fun _ => 1) (-1) y := by
      intro y
      simp [Datum.omegaQ]
    simp only [GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv, hq]
    exact hv
  obtain ⟨χ', hχ, hH⟩ := hf.model
  have key : ∀ k : levJ R i A.μ0, χ' k = levFn (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)
      (Formalism.UG.bc (Lev.swapAE D) k.1.1) := fun k => Units.ext <| (hχ k).elim fun y hy =>
    hy.2.symm.trans ((hs y).symm.trans ((congrArg s hy.1).trans
      (levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hQ (s : ℂ →+* ℂ) (fun PP => (R.chi ((i : ℕ) + 1) PP)⁻¹) (R.xiR A.μ0) m _)))
  have hH' := is_congr (GlobalTheory.Survey.LevelVectorSizeBounds.grp_triv R i A.μ0 m).symm
    (χ' := GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (fun x hx _ => key ⟨x, hx⟩) hH
  refine ⟨s, m, ⟨hC, hp, hE, GlobalTheory.Survey.LevelVectorSizeBounds.isLocal_triv R, hm, hω, hvec.onb, hlv, fun P => hvec.theta P, hf.coef, hio⟩,
    hC.models.νV i A.μ0, (R.B.L i A.μ0).pres.reps, hH'⟩

end GlobalTheory.ConjLiftData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepCharactersEqGridRowZeroRanks
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem arrS_cast_weil_vac {D : D7} {S S' T T' : Node D} (hS : S = S') (hT : T = T') (a : ArrS S T)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) {α : Type} (ω' : α)
    (hw : IsWeil ψ false S.V T.V χS χT a.ω) (hv : IsVac ψ θ false S T a.vac) (ho : HEq a.ω ω') :
    IsWeil ψ false S'.V T'.V χS χT (a.cast hS hT).ω ∧ IsVac ψ θ false S' T' (a.cast hS hT).vac ∧
      HEq (a.cast hS hT).ω ω' := by
  subst hS hT
  exact ⟨hw, hv, ho⟩

theorem chainStepCharacters_eq_gridRowZero_ranks {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (j : ℕ) :
    Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) =
      (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

theorem testGridRowZeroArrows_weil_vacua_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → GlobalTheory.Grid.IsWeil R.ψ false (GlobalTheory.Grid.row0 R j).V (GlobalTheory.Grid.row0 R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (GlobalTheory.Grid.th0 R t j).ω ∧ GlobalTheory.Grid.IsVac R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac ∧ HEq (GlobalTheory.Grid.th0 R t j).ω (W.om (.mu t 0 j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ _ _ t j hj
  have hc := chainStepCharacters_eq_gridRowZero_ranks R t j
  by_cases h : j + 1 < D.R.m
  · have hw : IsWeil R.ψ false (nodeY R j).V (nodeY R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepY R t j).ω := by
      have := hR.chain.ωY t j h
      rw [hc] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R j) (nodeY R (j + 1)) (stepY R t j).vac := (hR.chain.vY t j h).1
    have key := arrS_cast_weil_vac (nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (nodeY_eq_chainVertexAtRowZero_of_lt R h) (stepY R t j) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omY t j h).symm
    unfold th0
    rw [dite_eq_left h]
    exact key
  · have h' : j + 1 = D.R.m := by omega
    have hw : IsWeil R.ψ false (nodeY R (D.R.m - 1)).V (nodeX R).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepX R t).ω := by
      have hc' : Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m =
          (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
        rw [← h']; exact hc
      have := hR.chain.ωX t
      rw [hc'] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R (D.R.m - 1)) (nodeX R) (stepX R t).vac := (hR.chain.vX t).1
    have key := arrS_cast_weil_vac (nodeY_pred_eq_chainVertexAtRowZero_last R h') (nodeX_eq_chainVertexAtRowZero_of_ge R h) (stepX R t) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omX t j h').symm
    unfold th0
    rw [dite_eq_right h, dite_eq_left h']
    exact key

end GlobalTheory.GridJoin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateThetaLiftMatchedHeckeCombinationStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_theta_lift_matched_hecke_combination : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → GlobalTheory.GalLift.IsProjOf R i σ thP th → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.VacFix R.ψ ω P → ∀ cV cW, GlobalTheory.Hk3.Match R.ψ ω P (GlobalTheory.Hk3.dualC cV) cW → ∀ y y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) → (R.HW i σ).e (th y') = postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) := by
  first | exact @GlobalTheory.ConjLiftHecke.lift_match | exact GlobalTheory.ConjLiftHecke.lift_match | (intros; apply GlobalTheory.ConjLiftHecke.lift_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerEquivariantRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.ConjEquivReal


set_option maxHeartbeats 1000000 in
theorem conjMap_update_real : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Yc D 0) τ), ∀ (v : (MP R).Vec) (w : (MP R).sm τ), (w : (MP R).H τ) = (MP R).rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) = rTr (Yc D 0) (atTau R.θ (Yc D 0) τ g) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hlev hgrp hmod hhost hιE t c ht hconj hc Φ hΦ hrep τ g hg v w hw
  classical
  obtain ⟨hfin, hreal, -⟩ := GlobalTheory.IotaReal.iotaX_real_finite R F X h hlev hgrp hmod hιE
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  obtain ⟨-, Rm, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  have hint : ∀ (x : X.B.I.Ginf) (z : X.B.Hs), Φ (X.B.σs x z) = X.B.R (x, 1) (Φ z) := by
    obtain ⟨B, hB, rfl⟩ := hΦ
    intro x z
    have hb : B (X.B.σs x z) = X.B.R (x, 1) (B z) := DFunLike.congr_fun (hB x) z
    show X.B.Re (B (X.B.σs x z)) = X.B.R (x, 1) (X.B.Re (B z))
    rw [hb]
    obtain ⟨-, hT⟩ := X.B.Re_spec
    apply ext_inner_left ℂ
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_left (X.B.R (x, 1)), hT, hT]
    congr 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← Rm, ← ContinuousLinearMap.comp_apply (X.B.R (x, 1)), ← Rm]
    simp
  have hσ1 : ∀ v', X.B.σ v' 1 = 1 := fun v' => (X.ds v').2.2.1.1.1
  have hvec : GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w) = fun v' =>
      X.B.σ v' (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v')) (GlobalTheory.ConjRowMult.vecC X (MP R) c v v') := by
    rw [GlobalTheory.ConjRowMult.vecC_update]
    funext v'
    by_cases hv : v' = X.pl.symm τ
    · subst hv
      rw [Function.update_self, hw, hc τ g hg]
      unfold GlobalTheory.ConjRowMult.vecC
      rw [Equiv.piCongrLeft_apply_apply]
    · rw [Function.update_of_ne hv, ha1 v' hv,
        show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v')) = 1 from rfl, hσ1]
      rfl
  have hsig : X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w)) =
      X.B.σs ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1) (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have ea : iotaX X h (atTau R.θ (D.sp.Y 0) τ g) = ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1, 1) :=
    Prod.ext rfl ha2
  have hcomm : iotaX X h t⁻¹ * iotaX X h (atTau R.θ (D.sp.Y 0) τ g) =
      iotaX X h (atTau R.θ (D.sp.Y 0) τ g) * iotaX X h t⁻¹ := by
    have h1 : (iotaX X h t).1 = 1 := (hfin t).1 ht
    erw [map_inv]
    refine Prod.ext ?_ ?_
    · simp [h1]
    · simp [ha2]
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (iotaX X h (atTau R.θ (D.sp.Y 0) τ g))
  funext y
  show _ = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v (y * atTau R.θ (D.sp.Y 0) τ g)
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [hsig, hint, ← ea,
    GlobalTheory.ConjRowMult.contRepL_spec X hψ', GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  simp only [map_mul]
  rw [mul_assoc, hcomm, mul_assoc]

end GlobalTheory.ConjEquivReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerHasColumnLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ConjRowLevel

private theorem inner_R_eq_inner_R_inv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a : X.B.I.GA)
    (x z : X.B.I.L2 X.B.μf X.B.fund) : ⟪x, X.B.R a z⟫_ℂ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
  obtain ⟨h1, hmul, hnorm, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  let L : X.B.I.L2 X.B.μf X.B.fund →ₗᵢ[ℂ] X.B.I.L2 X.B.μf X.B.fund :=
    { toLinearMap := (X.B.R a⁻¹ : X.B.I.L2 X.B.μf X.B.fund →ₗ[ℂ] X.B.I.L2 X.B.μf X.B.fund)
      norm_map' := hnorm a⁻¹ }
  have hback : X.B.R a⁻¹ (X.B.R a z) = z := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, inv_mul_cancel, h1]
    rfl
  calc ⟪x, X.B.R a z⟫_ℂ = ⟪L x, L (X.B.R a z)⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
      show ⟪X.B.R a⁻¹ x, X.B.R a⁻¹ (X.B.R a z)⟫_ℂ = _
      rw [hback]

private theorem e_inv_mul_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2)
    (y : X.B.I.Gf) : X.B.e (k⁻¹ * y) = X.chi2 k * X.B.e y := by
  classical
  obtain ⟨_, hmulK, hinvK, hchi, hnorm⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have he : ∀ z, X.B.e z = if z ∈ X.K2 then star (X.chi2 z) / ((X.B.μf X.K2).toReal : ℂ) else 0 :=
    X.e_eq
  have hunit : X.chi2 k * star (X.chi2 k) = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj, hnorm k hk]
    norm_num
  by_cases hy : y ∈ X.K2
  · have hky : k⁻¹ * y ∈ X.K2 := hmulK _ (hinvK _ hk) _ hy
    have hsplit : X.chi2 y = X.chi2 k * X.chi2 (k⁻¹ * y) := by
      rw [← hchi _ hk _ hky, mul_inv_cancel_left]
    rw [he, he, if_pos hky, if_pos hy, hsplit, star_mul']
    linear_combination (-(star (X.chi2 (k⁻¹ * y)) / ((X.B.μf X.K2).toReal : ℂ))) * hunit
  · have hky : k⁻¹ * y ∉ X.K2 := fun h => hy (by simpa using hmulK _ hk _ h)
    rw [he, he, if_neg hky, if_neg hy, mul_zero]

theorem reg_comp_Re {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨-, hmul, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  ext1 y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    inner_R_eq_inner_R_inv X, X.B.Re_spec.2, X.B.Re_spec.2]
  have hstep : ∀ g : X.B.I.Gf,
      ⟪X.B.R (1, k)⁻¹ x, X.B.R (1, g) y⟫_ℂ = ⟪x, X.B.R (1, k * g) y⟫_ℂ := by
    intro g
    have hprod : (((1 : X.B.I.Ginf), k * g) : X.B.I.GA) = (1, k) * (1, g) := by simp
    rw [hprod, hmul, ContinuousLinearMap.comp_apply]
    exact (inner_R_eq_inner_R_inv X (1, k) x _).symm
  simp_rw [hstep]
  have hinv := integral_mul_left_eq_self (μ := X.B.μf)
    (fun g' => X.B.e (k⁻¹ * g') * ⟪x, X.B.R (1, g') y⟫_ℂ) k
  simp only [inv_mul_cancel_left] at hinv
  rw [hinv]
  simp_rw [e_inv_mul_eq_chi2_mul X k hk, mul_assoc]
  exact integral_const_mul _ _
private theorem contRep_mul_right_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Φ : X.B.Hs →L[ℂ] L2X X)
    (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) (v : X.B.Hs) {ψ : X.B.I.GA → ℂ}
    (hψ : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ v) ψ) (κ : X.B.I.Gf) (hκ : κ ∈ X.K2) :
    ∀ z, ψ (z * ((1 : X.B.I.Ginf), κ)) = X.chi2 κ * ψ z := by
  obtain ⟨A, -, hA⟩ := Submodule.mem_map.1 hΦ
  have hΦv : Φ v = X.B.Re (A v) := by
    rw [← hA]
    rfl
  have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1 : X.B.I.Ginf), κ)
  have hR : X.B.R ((1 : X.B.I.Ginf), κ) (Φ v) = X.chi2 κ • Φ v := by
    rw [hΦv, ← ContinuousLinearMap.comp_apply, reg_comp_Re X κ hκ, ContinuousLinearMap.smul_apply]
  rw [hR] at h1
  have h2 := Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 κ) hψ
  have heq := Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 h2
  intro z
  simpa using congrFun heq z

theorem conjMap_level : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ _ _ t c _ hconj _ Φ hΦ hcont u k hk g
  obtain ⟨ψ, hψ⟩ := hcont u
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hmem, hval⟩ := hconj k
  have hk' : ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧
      ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hmem.1 hk
  have hv := hval hk
  obtain ⟨hp1, hp2⟩ := hk'
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 := ⟨_, rfl⟩
  have hq : (iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹) = ((1 : X.B.I.Ginf), κ) := Prod.ext hp1 hκdef.symm
  have hκ : κ ∈ X.K2 := by
    rw [hκdef]
    exact hp2
  have hv' : star (X.chi2 κ) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k := by
    rw [hκdef]
    exact hv
  have hsplit : (iotaX X h).toMulEquiv (g * k * t⁻¹) =
      (iotaX X h).toMulEquiv (g * t⁻¹) * ((1 : X.B.I.Ginf), κ) := by
    rw [← hq]
    calc (iotaX X h).toMulEquiv (g * k * t⁻¹)
        = (iotaX X h).toMulEquiv (g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹)) := by
          rw [show g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹) = g * k * t⁻¹ by group]
      _ = _ := map_mul _ _ _
  change star (ψ ((iotaX X h).toMulEquiv (g * k * t⁻¹))) = _ * star (ψ ((iotaX X h).toMulEquiv (g * t⁻¹)))
  rw [hsplit, contRep_mul_right_eq_chi2_mul X Φ hΦ _ hψ κ hκ, star_mul', hv']

end GlobalTheory.ConjRowLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedThetaCharactersRestrictionRamificationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ i t s cμ cη m, IsConjChars R i t s cμ cη m → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP)) ∧ (∀ Z : Finset (Pl D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ Z) → GlobalTheory.StepLaw.UnrOff cμ Z ∧ GlobalTheory.StepLaw.UnrOff (cμ * cη⁻¹) Z) ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ finS R t → UnrAt cμ w ∧ UnrAt (cμ * cη⁻¹) w := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t s cμ cη m hc
  obtain ⟨μ', η', hμ, hη, ecμ, ecη, hres⟩ := hc
  obtain ⟨-, p1, p2, p3⟩ := _root_.GlobalTheory.levCh_unramified_places D T R.toLevCh A.μ0 hL t
  have uη : ∀ P, η'.UnrAt P := fun P => GlobalTheory.ConjSplitChars.unrAt_conj hη (R.C.isEta.unr P)
  have uμ : ∀ P : Pl D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) →
      μ'.UnrAt P := fun P hP => GlobalTheory.ConjSplitChars.unrAt_conj hμ (((p3 P hP).2 i).mul (p3 P hP).1)
  have tμ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → μ'.TameAt PP := by
    intro PP hPP
    refine GlobalTheory.ConjSplitChars.tameAt_conj hμ ?_
    rcases hPP with hP | hP
    · exact ((R.C.isMu0 i).tame PP).mul ((p1 PP hP).levelLe 1)
    · exact ((p2 PP hP i).levelLe 1).mul (hL.xi_tame t PP)
  have rη : ∀ PP, GlobalTheory.StepLaw.ResAt cη⁻¹ PP 1 := fun PP => by
    have := ((_root_.GlobalTheory.ResLoc.resAt_of_chrEq D cη η' ecη PP).2 (uη PP)).inv
    rwa [inv_one] at this
  have uoη : ∀ Z, GlobalTheory.StepLaw.UnrOff cη Z := fun Z v ε hε _ =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cη η' ecη v ε hε fun P _ => uη P
  refine ⟨fun PP hPP => ?_, fun Z hZ => ?_, fun w hw => ?_⟩
  · have h1 := (_root_.GlobalTheory.ResLoc.resAt_of_chrEq D cμ μ' ecμ PP).1 (m PP) (tμ PP hPP) (hres PP hPP)
    refine ⟨h1, ?_⟩
    have := h1.mul (rη PP)
    rwa [mul_one] at this
  · have h1 : GlobalTheory.StepLaw.UnrOff cμ Z := fun v ε hε hv =>
      GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cμ μ' ecμ v ε hε fun P hP => uμ P fun PP hPP => hP ▸ hv PP (hZ PP hPP)
    exact ⟨h1, h1.mul (uoη Z).inv⟩
  · have hw' : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ w.under (𝓞 D.host.F) := fun PP hPP he =>
      hw (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, he⟩)
    have h1 : UnrAt cμ w := (unrAt_iff_of_chrEq ecμ w).2 (uμ w hw')
    exact ⟨h1, h1.mul ((unrAt_iff_of_chrEq ecη w).2 (uη w)).inv⟩
end

