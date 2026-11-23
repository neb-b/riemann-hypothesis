module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperators
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0481
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteLiftCommLevelPrimeOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftsAtLevel

variable {D : D7}

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt P' c :=
  fun u hu a b => AllBij.idAt_mono h (hc u hu a b)

theorem comb_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hstd : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {c : WO S T →₀ ℂ} (hc : IsFinComb c) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (comb ψ S T c f) φ = comb ψ S T c (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  classical
  have e : ∀ g : WO S T → ℂ, comb ψ S T c g =
      ∑ i, c (c.support.equivFin.symm i) • heisO ψ S T (c.support.equivFin.symm i) g := by
    intro g
    unfold comb
    rw [← Finset.sum_coe_sort c.support]
    exact Fintype.sum_equiv c.support.equivFin _ _ (fun x => by simp)
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hstd hθ sS sT BS BT f hf c.support.card
    (fun i => c (c.support.equivFin.symm i)) (fun i => (c.support.equivFin.symm i : WO S T))
    (fun i => hc _ (c.support.equivFin.symm i).2) φ).1
  rw [e, e, key]

theorem vac_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {x : DefSp S} {y : DefSp T}
    {f₀ : WO S T → ℂ} (hvac : IsVacO ψ θ S T x.s y.s x.L y.L f₀) (P : Pl D → Prop)
    (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    Vac ψ S T x.L y.L P (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := by
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ
  have hle : latO S T (x.L : Set _) (y.L : Set _) P ≤ latO S T (x.L : Set _) (y.L : Set _) fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  refine ⟨hth φ, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu' 2)) (hvac.2.lat.1 u hu') φ
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u
      (GlobalTheory.VacGood.infPart_latO hu') (hvac.2.lat.2 e he u hu' hh) φ

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sOp_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) ∧
      ∀ i', RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, c', hc, -⟩ := _root_.GlobalTheory.FinPl.ramBijective_holds D k (p i) n q (χ₀ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_ram hinj β Q q χ₀ hχ (ε i) i ih

theorem isIdele_idele (p : SplitPt D k) (x : kˣ) : p.IsIdele x (p.idele x) := by
  unfold SplitPt.IsIdele
  rw [SplitPt.idele_val]
  ring

end Local

theorem chrPow_mul_neg (μ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) : chrPow μ a e * chrPow μ a (-e) = 1 := by
  simp only [chrPow, ← Circle.coe_mul, _root_.zpow_neg, mul_inv_cancel, Circle.coe_one]

end GlobalTheory.SeeSaw.LiftsAtLevel

namespace GlobalTheory.SeeSaw.LiftsAtLevel


open GlobalTheory.FinPl.ValDbl in
theorem pt_over {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {v : VCom c} {o : TDat c k ι} {t : Tup c} {w : VTup t} (hc : c.Is) (ht : t.Is) (hv : v.Is) (hVF : VForm v w)
    (hSh : ShapeOff v o) (j : ℕ) (hj : j < D.R.m) (α : t.Ch j) (γ : t.Ch (j + 1))
    (P : PolF D (c.X (j + 1)).rank (c.X j).rank) (i : ι) :
    ∃ f₀, Over c.ψ (o.β j i) (o.β (j + 1) i) (c.x j).L (c.x (j + 1)).L f₀ (phiOne (o.Q j i) (o.Q (j + 1) i))
      ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) := by
  have hk := ht.ker j hj α γ
  have hvac : IsVacO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).L (c.x (j + 1)).L (c.vac j) := hk.vac
  have hstd := hc.std
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  set f := pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B (c.vac j) P
    with hfdef
  have hfV : ∀ Pp, Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L Pp f := fun Pp => vac_pureTensorO hvac Pp P
  have hpt : (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P =
      comb c.ψ _ _ (w.dQ j α γ) (comb c.ψ _ _ (v.dG j) (comb c.ψ _ _ (v.dT j) f)) := by
    show pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B
      (comb c.ψ _ _ (t.dd j α γ) (c.vac j)) P = _
    rw [comb_pureTensorO hstd hc.inf _ _ _ _ hvac.2.theta (c := t.dd j α γ) hk.fin P]
    exact hVF.dd j hj α γ f (hfV fun _ => True).1
  have hrep := hSh.rep j hj f (hfV _)
  have hpl : Places o.p o.I (· ∈ v.tP) :=
    ⟨hSh.pre.nodup, hSh.pre.all, hSh.pre.inj, hSh.pre.tP, fun i => (hSh.pre.char i).2⟩
  have hAC := (_root_.GlobalTheory.FinPl.allComb D k ι o.p o.I (· ∈ v.tP) hpl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ hstd
    (c.X j) (c.X (j + 1)) (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L hxS.sd hxT.sd
    (fun i => phiOne (o.Q j i) (o.Q (j + 1) i))).2.2
  have hdG : CombAt (fun x => ¬ x ∈ v.tP) (v.dG j) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hv.disj hx ht') (hv.atG j).2.1
  have hdQ : CombAt (fun x => ¬ x ∈ v.tP) (w.dQ j α γ) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hVF.disjT hx ht') ((hVF.atQ j).2.2 α γ)
  obtain ⟨hV1, hO1⟩ := hAC (v.dG j) hdG f (hfV _)
  obtain ⟨hV2, hO2⟩ := hAC (w.dQ j α γ) hdQ _ hV1
  have hO := hO2 _ (hO1 _ hrep)
  obtain ⟨g, hg, -⟩ := overAll_last hstd (fun i => (hSh.pre.char i).2) hSh.pre.inj o.I hSh.pre.nodup _ _
    (fun j' => vac_at ((hSh.pre.tP _).2 ⟨j', rfl⟩) hV2) hO i (hSh.pre.all i)
  exact ⟨g, hpt ▸ hg⟩

end GlobalTheory.SeeSaw.LiftsAtLevel


open GlobalTheory.SeeSaw.LiftsAtLevel in
theorem GlobalTheory.SeeSaw.liftS_of_exact : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom c) (o : TDat c k ι) (t : Tup c) (w : VTup t), LiftExact D → c.Is → t.Is → v.Is → VForm v w → ShapeOff v o → (∀ j, j < D.R.m → ∃ μ, IsWeilDatumO c.ψ _ _ μ μ (t.kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v) → LiftS o t := by
  intro D c k _ _ _ _ ι v o t w hLE hc ht hv hVF hSh hμ j hj α γ P φ hφ
  obtain ⟨μ, hW, hU⟩ := hμ j hj
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  have hk := ht.ker j hj α γ
  have hφ' : IsContAut (c.X j) φ ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ := hφ
  set F := (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P with hF
  have hOv := pt_over hc ht hv hVF hSh j hj α γ P
  have hlift : ∀ φ', (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P φ' =
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F := fun φ' => rfl

  have hram : ∀ φ', (IsContAut (c.X j) φ' ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ') →
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F ∈ o.Ram (j + 1) := by
    intro φ' h'
    refine ⟨?_, fun i => ?_⟩
    · rw [← hlift]
      exact (GlobalTheory.SeeSaw.LiftSumProof.liftSum D c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) hxS hxT _ hk P).2.1 φ' h'.1
    · obtain ⟨f₀, hf₀⟩ := hOv i
      obtain ⟨c₀, -, H⟩ := _root_.GlobalTheory.FinPl.lift_sOp_comm D k (o.p i) (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) o.q (o.χ i) (o.hχ i) c.ψ
        (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i)
        (o.Q (j + 1) i)
      exact (H _ _ f₀ F hf₀ φ' (h'.2 i)).1
  refine ⟨by rw [hlift]; exact hram φ hφ', fun η => ?_⟩

  have key : ∀ l : List ι, l.foldr (fun i φ' => sOp (o.β (j + 1) i) (o.Q (j + 1) i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ')
        (liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ F) =
      ((((resCard k : ℝ) ^ ((((c.X (j + 1)).rank : ℝ) - (c.X j).rank) / 2) : ℝ) : ℂ) ^ l.length) •
        liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕
          (l.foldr (fun i φ' => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ') φ) F := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldr_cons, List.length_cons]
      rw [ih, GlobalTheory.FinPl.ValDbl.sOp_smul]
      obtain ⟨e, -, hE⟩ := hLE k (o.p i) o.q (o.χ i) (o.hχ i)
      obtain ⟨f₀, hf₀⟩ := hOv i
      have hr := (foldr_ram hSh.pre.inj (o.β j) (o.Q j) o.q o.χ o.hχ η l hφ').2 i
      rw [hE (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW
        (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i) (o.Q (j + 1) i) _ (isIdele_idele (o.p i) o.q.unit) _ _ f₀ F hf₀ _ hr
        (η i), mul_assoc, chrPow_mul_neg, mul_one, smul_smul, pow_succ]
      simp only [Fintype.card_fin]
  simp only [TDat.S, TDat.cL, hlift]
  exact key o.I
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDat

theorem exists_o {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ o : WO S T →₀ ℂ, (∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x) ∧
      ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
        Tm Φ₁ = comb ψ S T o (Tm Φ₀) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := GlobalTheory.SeeSaw.LocPlInhab.exists_latInd q FS FT hS hT
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨o, o1, fun Tm hTm a b hb ha => ?_⟩
  obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
  obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
  exact o2 Tm hTm

theorem idem_eq {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n : ℕ} (a : Fin n → AE D)
    (pl : Fin n ≃ P) (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i).1) : e = ∑ i, a i := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P, ← Equiv.sum_comp pl]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.LocMod.PinInhab.idem_unique (hes _ (pl i).2) (ha i)

theorem isThetaAt_smul {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ} {f₀ Φ f : Mx D m n → ℂ}
    {κ : ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ B hs e Λ c f₀ (κ • Φ) f) : IsThetaAt ψ B hs e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨hex, hall⟩ := h
  refine ⟨hex, fun Tm hTm => ?_⟩
  rw [hall Tm hTm, map_smul, smul_smul, inv_mul_cancel₀ hκ, one_smul]

end GlobalTheory.MidDat

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepSmallPairsValueAllGluedSplitPlacesProo
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VertexAllProof

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem over_self {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {p : SplitPt D k}
    {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] {α : Frame p S m'} {β : Frame p T m}
    {g f : WO S T → ℂ} {Φ : Matrix m m' k → ℂ} (h : Over ψ α β LS LT g Φ f) (hU : p.UnitAA)
    (ΛS : Submodule 𝒪[k] (m' → k)) (ΛT : Submodule 𝒪[k] (m → k)) (hLS : α.IsLat LS ΛS) (hLT : β.IsLat LT ΛT) :
    Over ψ α β LS LT g (latInd ΛS ΛT) g := by
  obtain ⟨hS, hT, hvac, -, ⟨Tm, hTm⟩, -⟩ := h
  have hE := _root_.GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D k p m m' S T α β LS LT hS hT hU ΛS ΛT hLS hLT
  refine ⟨hS, hT, hvac, _root_.GlobalTheory.FinPl.latInd_mem_SB_of_selfDual D k p m m' S T α β LS LT hS hT ΛS ΛT hLS hLT, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
  have hv := hT'.vac
  rw [one_smul] at hv
  change g = T' (extFun α β (latInd ΛS ΛT))
  rw [hE, hv]

theorem overAll_nil {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type}
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
    {LS : Lat S} {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type}
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
    {LS : Lat S} {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ} {i : ι} {l : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: l) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' :=
  Iff.rfl

end GlobalTheory.FinPl.VertexAllProof


open GlobalTheory.FinPl.VertexAllProof in
theorem GlobalTheory.FinPl.vertexAll : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  intro D k _ _ _ _ ι p I P hPl q ψ χ hχ hc
  have hvg := fun i => GlobalTheory.T.gluedPlace_doubleStep_exact_signed_constant D k (p i) q ψ (χ i) (hχ i) (hc i)
  refine ⟨fun i => (hvg i).choose, fun i => (hvg i).choose_spec.1, ?_⟩
  intro n n' n'' _ _ _ _ _ _
  have hrc := fun i => (hvg i).choose_spec.2 n n' n''
  choose r e hr hre using hrc
  refine ⟨r, e, hr, ?_⟩
  intro σ B J B' s₁ s₂ l vL hunr a b a' M₀ M₁ M₂ _ _ _ hgl Ξ₁ Ξ₂ _ _
  have hP : ∀ i, P (p i).v := fun i => (hPl.mem _).2 ⟨i, rfl⟩
  have hmaps : ∀ (ls : List ι) (φ : GA D B.A → ℂ), a.Ram φ →
      a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun i => (hvg i).choose) ls φ) := fun ls φ hφ =>
    (_root_.GlobalTheory.FinPl.allBijective_all D k ι p q χ hχ (fun i => (hvg i).choose) n' B.A B.V₀ a hPl.inj ls).1.mapsTo hφ
  have hV : ∀ ls : List ι, ∀ Ξ₁' Ξ₂',
      OverAll ψ a.α₀ b.β M₀ M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) ls Ξ₁ Ξ₁' →
      OverAll ψ b.β a'.α₀ M₁ M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) ls Ξ₂ Ξ₂' →
      ∀ φ, a.Ram φ → hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
        (ls.map fun i => (r i : ℂ) * chrPow s₁.χW ((p i).idele q.unit) (e i)).prod •
          hand0 s₁ s₂ l vL (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun i => (hvg i).choose) ls φ) Ξ₁' Ξ₂' := by
    intro ls
    induction ls with
    | nil =>
      intro Ξ₁' Ξ₂' h1 h2 φ _
      rw [overAll_nil.1 h1, overAll_nil.1 h2, List.map_nil, List.prod_nil, one_smul]
      rfl
    | cons i ls ih =>
      intro Ξ₁' Ξ₂' h1 h2 φ hφ
      obtain ⟨g₁, hg₁, hΞ₁'⟩ := overAll_cons.1 h1
      obtain ⟨g₂, hg₂, hΞ₂'⟩ := overAll_cons.1 h2
      have ho₁ := over_self hΞ₁' (hgl i).1.unit _ _ (hgl i).1.lat (hgl i).2.2
      have ho₂ := over_self hΞ₂' (hgl i).1.unit _ _ (hgl i).2.2 (hgl i).2.1.lat
      obtain ⟨F, hF, hFP⟩ := (hmaps ls φ hφ).2 i
      have hv := hre i (a.P i) (b.Q i) (a'.P i) σ B J B' s₁ s₂ l vL (hunr _ (hP i)).1 (hunr _ (hP i)).2 (a.α i)
        (a.α₀ i) (b.β i) (a'.α i) (a'.α₀ i) (hgl i).1.sum (hgl i).2.1.sum M₀ M₁ M₁ M₂ g₁ g₁ Ξ₁' g₂ g₂ Ξ₂' ho₁ hΞ₁'
        ho₂ hΞ₂' F hF
      have hsop := ((_root_.GlobalTheory.FinPl.ramBijective_holds D k (p i) n' q (χ i) (hχ i) _ rfl ((hvg i).choose) B.A (a.α i) (a.P i)).2.1 F hF).2
      rw [ih g₁ g₂ hg₁ hg₂ φ hφ, ← hFP, hv, ← hsop, hFP, smul_smul, List.map_cons, List.prod_cons, mul_comm]
      rfl
  intro Ξ₁' Ξ₂' h1 h2 φ hφ
  exact hV I Ξ₁' Ξ₂' h1 h2 φ hφ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLastPeriodClassDataOfLastStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem exists_clsT_of_pinTop : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∃ E : ClsT (realOf u R g s J) (tupOf R P u g t r k tl), E.Is := by
  intro B X I hI hPins l Z u G iG iGf Pl0 T F Ks iK iNK iA R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG
  choose h hh using fun c : (I.fm l u a).clsP => GlobalTheory.Core.Rk.Top.Model.hasMat_exists (K.y c)
  choose G' hG' using hG 0
  obtain ⟨hrep, hst⟩ := GlobalTheory.T.last_space_moved_level_class_points_representatives I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh
  refine ⟨clsTop R g P r k tl s J UT h eW ε G', hrep, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.lastPeriod_law_movedLevel I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG
  · intro n hn f v β c x hx
    show trc (k.eT n hn β) (f.1 v) (h c * x) = ellTop R P eW ε G' c f (J v x)
    rw [hTop.eT n hn β, trc_single_apply, ellTop_apply, GlobalTheory.T.form_translate_real_point_read_by_period I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh G' (fun f => (hG' f).1) f v c x hx]
    ring
  · exact GlobalTheory.T.lastPeriod_tail_eq_lowered_evaluation_period I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh hst G' (fun f => (hG' f).1)

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawRationalPointsHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatLaw

theorem isHalf_actO {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

theorem law_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy z
  obtain ⟨hsupp, k, hk, hper, -⟩ := hΦ
  set ez := z.map fun r => A.e * incA (I.rec7 l Z) r with hez
  by_cases hw : IsHalf A.e (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez)
  · obtain ⟨z', v, hv, hvh, hwe⟩ := _root_.GlobalTheory.AdForm.DenseHalf.half_eq_rat_add_nsmul _ _ A.e _ hA.idem k hk _ hw
    have hΦw : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = p * A.xi i hi α γ z' := by
      rw [hwe, hper v hv hvh, hp z']
    rw [hΦw, hp z]
    by_cases hp0 : p = 0
    · simp [hp0]
    · have hxi : ∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E)
          (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t →
          z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t →
          A.xi i hi α γ z₁ = A.xi i hi α γ z₂ := by
        intro z₁ z₂ t ht hth he
        have h1 := hp z₁
        rw [he, hper t ht hth, hp z₂] at h1
        exact (mul_left_cancel₀ hp0 h1).symm
      have hL := _root_.GlobalTheory.AdForm.XiLaw.xi_law I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ κ' x y hx hy z z' v hv hvh hwe
      linear_combination p * hL
  · have h1 : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = 0 := by
      by_contra h
      exact hw (hsupp _ h)
    have h2 : Φ ez = 0 := by
      by_contra h
      exact hw (GlobalTheory.AdForm.RatLaw.isHalf_actO _ _ (hsupp _ h))
    rw [h1, h2]
    simp

end GlobalTheory.AdForm.RatLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_equation : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), SplitAt { v with N := N₁ } { o with M := M₁ } ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.SplitAtPlaces.splitAt_places | exact GlobalTheory.SplitAtPlaces.splitAt_places | (intros; apply GlobalTheory.SplitAtPlaces.splitAt_places <;> assumption)
end

