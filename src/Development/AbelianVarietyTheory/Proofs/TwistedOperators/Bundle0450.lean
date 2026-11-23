module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Lean
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrPhaseOfTrFlip
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

open GlobalTheory.SplitWeil GlobalTheory.SplitFlip MeasureTheory
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.RowEx.PhaseCarry

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {K : Type} [Field K] (σ : K →+* ℂ)

def PhW (Γ : Grid k) (hs : 1 ≤ Γ.s) (J : Γ.Level) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool) (ϖ : kˣ) (c : ℕ)
    (T : Γ.Args → ℂ) (β : Cosets hs J) : Prop :=
  ∀ x y e, (unfTerm ψ ν keep (Reps.through hs J (stair Γ ϖ c)) T β).datum x y ≠ 0 →
    moved Γ keep ((Reps.through hs J (stair Γ ϖ c)).elt β) T (fill hs x y e) ≠ 0 → (ψ (phase x e) : ℂ) ∈ Set.range σ

def SuW (Γ : Grid k) (hs : 1 ≤ Γ.s) (J : Γ.Level) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool) (ϖ : kˣ) (c : ℕ)
    (T : Γ.Args → ℂ) (β : Cosets hs J) : Prop :=
  β ∈ unfSupport ψ ν keep (Reps.through hs J (stair Γ ϖ c)) T

end Loc

section Loc2

variable {k : Type} {_ : Field k} {_ : ValuativeRel k} {_ : TopologicalSpace k} {_ : IsNonarchimedeanLocalField k}
  {_ : MeasurableSpace k} {_ : BorelSpace k} {K : Type} [Field K] (σ : K →+* ℂ)

theorem congrW {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level} (hJ : HEq J J')
    {ψ ψ' : AddChar k Circle} (hψ : ψ = ψ') {ν ν' : Measure k} (hν : ν = ν') {keep keep' : Bool} (hk : keep = keep')
    (ϖ : kˣ) {c c' : ℕ} (hc : c = c') {T : Γ.Args → ℂ} {T' : Γ'.Args → ℂ} (hT : HEq T T') {β : Cosets hs J}
    {β' : Cosets hs' J'} (hβ : HEq β β') :
    (PhW σ Γ hs J ψ ν keep ϖ c T β ↔ PhW σ Γ' hs' J' ψ' ν' keep' ϖ c' T' β') ∧
      (SuW Γ hs J ψ ν keep ϖ c T β ↔ SuW Γ' hs' J' ψ' ν' keep' ϖ c' T' β') := by
  subst hΓ hψ hν hk hc
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq hβ
  exact ⟨Iff.rfl, Iff.rfl⟩

def castCos {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level} (hJ : HEq J J')
    (β : Cosets hs J) : Cosets hs' J' := by
  subst hΓ
  obtain rfl := eq_of_heq hJ
  exact β

theorem castCos_heq {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level}
    (hJ : HEq J J') (β : Cosets hs J) : HEq (castCos hΓ (hs' := hs') hJ β) β := by
  subst hΓ
  obtain rfl := eq_of_heq hJ
  rfl

end Loc2


set_option maxHeartbeats 4000000 in
theorem trPhase_of_trFlip : TrFlip → TrPhase := by
  intro hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA M σ hS t' Φ' β' hβ'
  obtain ⟨Φ, hΦ⟩ := hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA Φ'
  have hpre := hA.l.pre
  have hv0 := hA.g.v0
  have hw := hA.g.w
  have hQ := hA.l.Q t'
  have hψ := hA.w.ψ
  clear hF hA
  rcases X with ⟨⟨P⟩, _, _, _, _, _, _⟩
  rcases X' with ⟨⟨P'⟩, _, _, _, _, _, _⟩
  dsimp only at hpre
  subst hpre
  replace hv0 := eq_of_heq hv0
  replace hw := eq_of_heq hw
  replace hQ := eq_of_heq hQ
  replace hψ := eq_of_heq hψ
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
    rfl
  have hloc : locPl G' t' = locPl G (ι t') := by
    unfold locPl
    rw [hW0, hQ]
    rfl
  have hcos : ∀ w, cosExp G' w = cosExp G w := fun w => by
    unfold cosExp Places.depth
    rw [hW0, hv0]
    rfl
  have hkeep : ∀ w, keepAt G' w = keepAt G w := fun w => by
    unfold keepAt
    rw [hW0]
    rfl
  have hpsi : ∀ w, psiAt W' w = psiAt W w := fun w => by
    ext x
    show (W'.ψ _ : ℂ) = W.ψ _
    rw [hψ]
    rfl
  have hmem : ∀ w, w ∈ locPl G (ι t') → w ∈ locPl G' t' := fun w h => hloc ▸ h
  have hF3 := fun w (h : w ∈ locPl G' t') => hΦ t' w w HEq.rfl h
  have hΓ : ∀ w (h : w ∈ locPl G' t'), locGrid G' t' w = locGrid G (ι t') w := fun w h => eq_of_heq (hF3 w h).1
  let β : CosFam G (ι t') := fun w => castCos (hΓ w.1 (hmem _ w.2)) (hF3 w.1 (hmem _ w.2)).2.1 (β' ⟨w.1, hmem _ w.2⟩)
  have hβh : ∀ w : locPl G (ι t'), HEq (β' ⟨w.1, hmem _ w.2⟩) (β w) := fun w => (castCos_heq _ _ _).symm
  have hβ : β ∈ S.supp (ι t') Φ := fun w =>
    ((congrW σ (hΓ w.1 (hmem _ w.2)) (hF3 w.1 (hmem _ w.2)).2.1 (hpsi w.1) rfl (hkeep w.1) (unifAt w.1)
      (hcos w.1) (hF3 w.1 (hmem _ w.2)).2.2 (hβh w)).2).mp (hβ' ⟨w.1, hmem _ w.2⟩)
  intro w'
  have hw' : w'.1 ∈ locPl G (ι t') := hloc ▸ w'.2
  exact ((congrW σ (hΓ w'.1 w'.2) (hF3 w'.1 w'.2).2.1 (hpsi w'.1) rfl (hkeep w'.1) (unifAt w'.1)
      (hcos w'.1) (hF3 w'.1 w'.2).2.2 (hβh ⟨w'.1, hw'⟩)).1).mpr (hS (ι t') Φ β hβ ⟨w'.1, hw'⟩)

end GlobalTheory.RowEx.PhaseCarry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoLeMOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx.CarryGrid

open scoped nonZeroDivisors

variable {D : D7} {T : Type}

theorem vtxOf_pos (L : LevCh D T) (Vs : ℕ → ℕ → LSp D) (i j : ℕ) (h : 1 ≤ i) : vtxOf L Vs i j = Vs i j := by
  cases i with
  | zero => omega
  | succ i => rfl

theorem xOf_pos (X₀ : LSp D) (Xs : ℕ → LSp D) (j : ℕ) (h : 1 ≤ j) : xOf X₀ Xs j = Xs j := by
  cases j with
  | zero => omega
  | succ j => rfl

def castDec {A A' B B' : HSp D} {c : ℕ} {ε : D.host.E} (ea : A = A') (eb : B = B') (d : HermitianOrthogonalExtensionData A B c ε) :
    HermitianOrthogonalExtensionData A' B' c ε := by
  subst ea eb; exact d

theorem castDec_ι {A A' B B' : HSp D} {c : ℕ} {ε : D.host.E} (ea : A = A') (eb : B = B') (d : HermitianOrthogonalExtensionData A B c ε) :
    HEq (castDec ea eb d).ι d.ι := by
  subst ea eb; rfl

theorem castDec_a {A A' B B' : HSp D} {c : ℕ} {ε : D.host.E} (ea : A = A') (eb : B = B') (d : HermitianOrthogonalExtensionData A B c ε) :
    HEq (castDec ea eb d).a d.a := by
  subst ea eb; rfl

theorem castDec_lat {Y Y' Z Z' : LSp D} {c : ℕ} {ε : D.host.E} (ey : Y = Y') (ez : Z = Z') (d : HermitianOrthogonalExtensionData Y.sp Z.sp c ε)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h : Z.lat = d.lat Y.lat 𝔟) :
    Z'.lat = (castDec (congrArg LSp.sp ey) (congrArg LSp.sp ez) d).lat Y'.lat 𝔟 := by
  subst ey ez; exact h

theorem two_le_m_of (L : LevCh D T) : 2 ≤ D.R.m := D.R.two_le_m

theorem firstCore (L : LevCh D T) (μ0 : T) (h : L.Is μ0) : ∃ Z : LSp D, Z.IsV (rankP D 0) ((D.R.m - 0 + 1) / 2) ∧
    ∃ d : HermitianOrthogonalExtensionData (Yc D 0) Z.sp 1 1, Z.lat = d.lat (L.ΛY 0) fun _ => 1 := by
  have hY := colY_isV D T L μ0 h 0 (Nat.zero_le _)
  obtain ⟨μ, hμ⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨Z, hZ, d, hd⟩ := GlobalTheory.GridSpaces.exists_line _ hY (by unfold rankV; omega)
  refine ⟨Z, ?_, d, hd⟩
  have e1 : rankP D 0 = rankV D 0 0 + 1 := by simp [rankP, nRk, rankV]
  have e2 : (D.R.m - 0 + 1) / 2 = (D.R.m - 0) / 2 := by omega
  rw [e1, e2]; exact hZ

abbrev recOf (_L : LevCh D T) : D7 := D

-- Comparing the types of copied fields in the kernel avoids unfolding the stage records in the elaborator.
open Lean Elab Tactic in
local elab "exact_by_kernel " term:term : tactic =>
  closeMainGoalUsing `exact_by_kernel fun target _ => do
    let value ← elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    let actual ← instantiateMVars (← Meta.inferType value)
    let target ← instantiateMVars target
    let lctx ← instantiateLCtxMVars (← getLCtx)
    match Kernel.isDefEq (← getEnv) lctx actual target with
    | .ok true => pure value
    | .ok false => throwError "expected{indentExpr target}\nbut the term has type{indentExpr actual}"
    | .error error => throwError (error.toMessageData (← getOptions))

local macro "copyDec% " d:term:max : term =>
  `({ ι := by exact_by_kernel ($d).ι
      isom := by exact_by_kernel ($d).isom
      a := by exact_by_kernel ($d).a
      gram := by exact_by_kernel ($d).gram
      perp := by exact_by_kernel ($d).perp
      rank := by exact_by_kernel ($d).rank })

local macro "copyIsV% " h:term:max : term =>
  `(⟨by exact_by_kernel ($h).rank, by exact_by_kernel ($h).sigOK,
    by exact_by_kernel ($h).sig, by exact_by_kernel ($h).sd⟩)

set_option maxHeartbeats 16000000 in
theorem carryG : CarryG := by
  intro X X' T T' L L' μ₀ μ₀' ι hA sc G
  obtain ⟨B, Cc, Wr, Vd, Ss, Nn, Gj⟩ := X
  obtain ⟨B', Cc', Wr', Vd', Ss', Nn', Gj'⟩ := X'
  cases B
  cases B'
  have hpre := hA.pre
  dsimp only at hpre
  subst hpre
  obtain ⟨f, f', hf, hC, hC'⟩ := hA.C
  have hf2 := eq_of_heq hf
  subst hf2
  have hPg : ∀ PP, PP ∈ L'.Pg ↔ PP ∈ L.Pg := by
    intro PP
    have h2 : PP ∈ L.Pg ↔ ∃ k, L.C.P.Div k PP := hA.is.Pg PP
    rw [hA.is'.Pg, h2, hC, hC']
    exact Iff.rfl
  have hQ : ∀ t, L'.Q t = L.Q (ι t) := fun t => eq_of_heq (hA.Q t)
  let pl' : Places L' :=
    { v0 := (by with_unfolding_all exact (G.pl.v0 :))
      basePlace_over_qZero := (by with_unfolding_all exact (G.pl.basePlace_over_qZero :))
      w := (by with_unfolding_all exact (G.pl.w :))
      w_over := (by with_unfolding_all exact (G.pl.w_over :))
      w_split := (by with_unfolding_all exact (G.pl.w_split :))
      w_g := fun v k h => (hPg _).2 ((by with_unfolding_all exact ((G.pl.w_g v k h) :)))
      w_de := (by with_unfolding_all exact (G.pl.w_de :))
      w_Q := fun t PP hPP h => (by with_unfolding_all exact ((G.pl.w_Q (ι t) PP (hQ t ▸ hPP) h) :))
      levelPlace_ne_basePlace := fun t PP hPP => (by with_unfolding_all exact ((G.pl.levelPlace_ne_basePlace (ι t) PP (hQ t ▸ hPP)) :)) }
  let ch' : Chars pl' sc.cGap :=
    { chiH := (by with_unfolding_all exact (G.ch.chiH :))
      chi := (by with_unfolding_all exact (G.ch.chi :))
      chi_eq := (by with_unfolding_all exact (G.ch.chi_eq :))
      triv := (by with_unfolding_all exact (G.ch.triv :))
      inf := (by with_unfolding_all exact (G.ch.inf :))
      unr := (by with_unfolding_all exact (G.ch.unr :))
      lev1 := (by with_unfolding_all exact (G.ch.lev1 :))
      wild := (by with_unfolding_all exact (G.ch.wild :))
      lev0 := (by with_unfolding_all exact (G.ch.lev0 :)) }
  have hmX := two_le_m_of L
  have hmX' := two_le_m_of L'
  have h1X := Nat.le_of_succ_le hmX
  have h1X' := Nat.le_of_succ_le hmX'
  obtain ⟨P₀, hP₀, d₀, hd₀⟩ := firstCore L' μ₀' hA.is'
  let Vs' : ℕ → ℕ → type_of% P₀ := fun i j => ⟨(by with_unfolding_all exact ((G.sp.Vs i j).sp :)), (by with_unfolding_all exact ((G.sp.Vs i j).lat :))⟩
  let Xs' : ℕ → type_of% P₀ := fun j => ⟨(by with_unfolding_all exact ((G.sp.Xs j).sp :)), (by with_unfolding_all exact ((G.sp.Xs j).lat :))⟩
  let P' : ℕ → type_of% P₀ := fun i => match i with
    | 0 => P₀
    | k + 1 => ⟨(by with_unfolding_all exact ((G.sp.P (k + 1)).sp :)), (by with_unfolding_all exact ((G.sp.P (k + 1)).lat :))⟩
  let sp' : Vertices L' (pl'.stA sc) (pl'.stAbar sc) :=
    { Vs := Vs'
      P := P'
      Xs := Xs'
      V_is := fun i j h1 h2 h3 => copyIsV% (G.sp.V_is i j h1 h2 h3)
      P_is := fun i hi => match i, hi with
        | 0, _ => hP₀
        | k + 1, hi => copyIsV% (G.sp.P_is (k + 1) hi)
      X_is := fun j h1 h2 => copyIsV% (G.sp.X_is j h1 h2)
      dec0 := d₀
      lat0 := hd₀
      colDec := fun i h h' => match i, h, h' with
        | 0, h, _ => absurd h (by omega)
        | k + 1, h, h' => copyDec% (G.sp.colDec (k + 1) h h')
      colLat := by
        intro i
        cases i with
        | zero => intro h; omega
        | succ k =>
          intro h h'
          exact_by_kernel G.sp.colLat (k + 1) h h'
      rowDecS := fun j h => castDec rfl (congrArg LSp.sp (vtxOf_pos L' Vs' _ (j + 1) h1X').symm)
        (copyDec% (castDec rfl (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ (j + 1) h1X)) (G.sp.rowDecS j h)))
      rowLat := fun j h => castDec_lat rfl (vtxOf_pos L' Vs' _ (j + 1) h1X').symm _ _
        (by
          exact_by_kernel (castDec_lat rfl (vtxOf_pos L G.sp.Vs _ (j + 1) h1X)
            (G.sp.rowDecS j h) _ (G.sp.rowLat j h)))
      topDec := castDec (congrArg LSp.sp (vtxOf_pos L' Vs' _ _ h1X').symm) (congrArg LSp.sp (xOf_pos (P' _) Xs' _ h1X').symm)
        (copyDec% (castDec (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (congrArg LSp.sp (xOf_pos (G.sp.P _) G.sp.Xs _ h1X))
          G.sp.topDec))
      topLat := castDec_lat (vtxOf_pos L' Vs' _ _ h1X').symm (xOf_pos (P' _) Xs' _ h1X').symm _ _
        (by
          exact_by_kernel (castDec_lat (vtxOf_pos L G.sp.Vs _ _ h1X)
            (xOf_pos (G.sp.P _) G.sp.Xs _ h1X) G.sp.topDec _ G.sp.topLat)) }
  refine ⟨⟨pl', ch', sp'⟩, (by with_unfolding_all exact ((HEq.refl G.pl.v0) :)), (by with_unfolding_all exact ((HEq.refl G.pl.w) :)), (by with_unfolding_all exact ((HEq.refl G.ch.chiH) :)), (by with_unfolding_all exact ((HEq.refl G.ch.chi) :)),
    fun i j => ⟨(by with_unfolding_all exact ((HEq.refl (G.V (.grid (i + 1) j))) :)), (by with_unfolding_all exact ((HEq.refl (G.Λ (.grid (i + 1) j))) :))⟩, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero =>
      have hP : ∀ n, 1 ≤ n → HEq (P' n).sp (G.sp.P n).sp ∧ HEq (P' n).lat (G.sp.P n).lat := by
        intro n hn
        cases n with
        | zero => omega
        | succ n => exact ⟨(by with_unfolding_all exact ((HEq.refl (G.sp.P (n + 1)).sp) :)), (by with_unfolding_all exact ((HEq.refl (G.sp.P (n + 1)).lat) :))⟩
      exact (by with_unfolding_all exact ((hP _ h1X') :))
    | succ j => exact ⟨(by with_unfolding_all exact ((HEq.refl (G.V (.top (j + 1)))) :)), (by with_unfolding_all exact ((HEq.refl (G.Λ (.top (j + 1)))) :))⟩
  · intro j h h'
    cases j with
    | zero =>
      have hc : ∀ n (h1 : 1 ≤ n) (h2 : n ≤ (recOf L').R.m), HEq (sp'.colDec n h1 h2).ι (G.sp.colDec n h1 h2).ι ∧
          HEq (sp'.colDec n h1 h2).a (G.sp.colDec n h1 h2).a := by
        intro n h1 h2
        cases n with
        | zero => omega
        | succ n => exact ⟨(by with_unfolding_all exact ((HEq.refl (G.sp.colDec (n + 1) h1 h2).ι) :)), (by with_unfolding_all exact ((HEq.refl (G.sp.colDec (n + 1) h1 h2).a) :))⟩
      exact (by with_unfolding_all exact ((hc _ h' le_rfl) :))
    | succ j =>
      refine ⟨(castDec_ι _ _ _).trans ?_, (castDec_a _ _ _).trans ?_⟩
      · exact (by with_unfolding_all exact ((castDec_ι rfl (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (G.sp.rowDecS j h)) :))
      · exact (by with_unfolding_all exact ((castDec_a rfl (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X)) (G.sp.rowDecS j h)) :))
  · refine ⟨(castDec_ι _ _ _).trans ?_, (castDec_a _ _ _).trans ?_⟩
    · exact (by with_unfolding_all exact ((castDec_ι (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X))
        (congrArg LSp.sp (xOf_pos (G.sp.P _) G.sp.Xs _ h1X)) G.sp.topDec) :))
    · exact (by with_unfolding_all exact ((castDec_a (congrArg LSp.sp (vtxOf_pos L G.sp.Vs _ _ h1X))
        (congrArg LSp.sp (xOf_pos (G.sp.P _) G.sp.Xs _ h1X)) G.sp.topDec) :))

end GlobalTheory.RowEx.CarryGrid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperLeftBlockEqSubmatrixOfRankEq
section
noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoActRoad

section Lattice

variable {D : D7} {V : HSp D}

variable {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

theorem le_of_half {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} {Pg : Finset (Pl D.host.E)}
    (h : l.Mb = ∏ w ∈ Pg, w.asIdeal) {w : Pl D.host.E} (hw : w ∈ Pg) : l.Mb ≤ w.asIdeal :=
  h.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hw))

end Lattice

section Group

variable {D : D7} {V : HSp D} (β : GL (Fin V.rank) (EAf D))

variable {β} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem liftsExist_of_half (hβ : IsSDFrame V β Λ 1) (l : Level H) (L : LevDat D.host.E ℂ V.rank) (hQ : L.Q = ∅)
    (h : l.Mb = ∏ w ∈ L.Pg, w.asIdeal) : LiftsExist V β L := by
  obtain ⟨c, hc⟩ := hβ
  refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP h1 PP' h' => ?_) (hQ ▸ Finset.disjoint_empty_right _)
  rcases h' with h' | h'
  · exact GlobalTheory.LevelAction.not_isConjPl l (le_of_half h h1) (le_of_half h h')
  · exact absurd (hQ ▸ h') (Finset.notMem_empty _)

end Group

section Record

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open Classical in
theorem exists_half_prod {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (hM : l.M = D.host.g 0 * D.host.g 1) :
    (∀ Pg : Finset (Pl D.host.E), (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → l.Mb = ∏ w ∈ Pg, w.asIdeal) ∧
      ∃ Pg : Finset (Pl D.host.E), l.Mb = ∏ w ∈ Pg, w.asIdeal := by
  have hprod := l.prod
  rw [hM] at hprod
  have hs : Squarefree l.Mb := (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (l.Mb * _)).of_mul_left
  refine ⟨fun Pg h => GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ h,
    (Ideal.finite_factors hs.ne_zero).toFinset, GlobalTheory.CoverHalf.eq_prod_of_squarefree hs _ fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]

theorem mem_Pg_iff {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (w : Pl D.host.E) :
    w ∈ L.Pg ↔ (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb ≤ w.asIdeal := by
  rw [hL.Pg, GlobalTheory.HalfOnRecord.designLevel_Mb, GlobalTheory.CoverHalf.prod_map_le_iff]
  rfl

theorem designLevel_prod {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) :
    (GlobalTheory.HalfOnRecord.designLevel L.C.P).Mb = ∏ w ∈ L.Pg, w.asIdeal :=
  (exists_half_prod _ rfl).1 _ (mem_Pg_iff hL)

theorem levelLiftsExist_gridVertexSpaces {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) :
    LiftsExist (Wc D i) (L.βW i) (L.datWp i L.triv) :=
  liftsExist_of_half (hL.βW i) (GlobalTheory.HalfOnRecord.designLevel L.C.P) _ rfl (designLevel_prod hL)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

end Record

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

open GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts (LevGrp IsGeoRep UnitConstEquivariant)
open GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv (Cusp IsGeo ReadTwist KeepsIntegral ConstEquiv GeoActAt)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}

end Main

end GlobalTheory.GeoActRoad
end
end

