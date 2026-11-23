module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0847
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupRelIffSameData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7}

theorem exists_setupRel (h : SameGeo D D') {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (ρ : Setup X) :
    ∃ ρ' : Setup X', SetupRel ρ ρ' := by
  obtain ⟨gR, ghost, gsp, gTau, ginstTau, geTau, ghc⟩ := h
  obtain ⟨_, _, _, _, _, w, _⟩ := D
  obtain ⟨_, _, _, _, _, w', _⟩ := D'
  dsimp only at gR ghost gsp gTau ginstTau geTau ghc
  subst gR; subst ghost; subst gsp
  cases w; cases w'
  dsimp only at gTau ginstTau geTau ghc
  subst gTau; subst ginstTau; subst geTau; subst ghc
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, xO0, xcrO0, xalgO0, xtopO0, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, xS0, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  dsimp only at a1 a2 a3
  subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl xO0 xcrO0 xalgO0 xtopO0 xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xS0 xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst xO0; subst xcrO0; subst xalgO0; subst xtopO0; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xS0; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  obtain ⟨rc, ch, bad, e, ek, B, om, Cl, rep, β, eG⟩ := ρ
  rename_i fin
  refine ⟨@Setup.mk _ _ _ ⟨rc.κ, rc.art⟩ ch bad e ek
    (fun i j b => ⟨(B i j b).hr, ⟨(B i j b).F.ψ, (B i j b).F.θ, (B i j b).F.sT, (B i j b).F.BS, (B i j b).F.BT, (B i j b).F.ΛS,
      (B i j b).F.ΛT, (B i j b).F.βS, (B i j b).F.βT, (B i j b).F.f₀⟩, ⟨(B i j b).G.Pg, (B i j b).G.P, (B i j b).G.mu⟩,
      ⟨(B i j b).de.Q, (B i j b).de.chi, (B i j b).de.res⟩,
      ⟨(B i j b).w.p, (B i j b).w.q, (B i j b).w.ap, (B i j b).w.am, (B i j b).w.c, (B i j b).w.lam⟩, (B i j b).mu0, (B i j b).eta⟩)
    om (fun i j b t => Cl i j b ⟨t.Q, t.chi, t.res⟩) (fun i j b t => fin i j b ⟨t.Q, t.chi, t.res⟩)
    (fun i j b t => rep i j b ⟨t.Q, t.chi, t.res⟩) β eG,
    ⟨.rfl, .rfl⟩, .rfl, .rfl, .rfl, .rfl, ?_, .rfl, ?_, ?_, .rfl, ?_⟩
  · intro i i' hi j j' hj b
    cases hi; cases Fin.ext hj
    exact ⟨⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩, ⟨.rfl, .rfl, .rfl⟩, ⟨.rfl, .rfl, .rfl⟩,
      ⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩, .rfl, .rfl⟩
  · rintro i i' hi j j' hj b ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨r1, r2, r3⟩
    cases hi; cases Fin.ext hj; cases r1; cases r2; cases r3
    rfl
  · rintro i i' hi j j' hj b ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨r1, r2, r3⟩
    cases hi; cases Fin.ext hj; cases r1; cases r2; cases r3
    exact HEq.rfl
  · intro i i' hi j j' hj b
    cases hi; cases Fin.ext hj
    exact HEq.rfl

theorem RecipRel.good (h : SameGeo D D') {Ω Ω' : Type} [i1 : Field Ω] [i2 : Algebra D.host.E Ω] [i1' : Field Ω']
    [i2' : Algebra D'.host.E Ω'] (hΩ : Ω = Ω') (h1 : HEq i1 i1') (h2 : HEq i2 i2') {a : Recip D Ω} {a' : Recip D' Ω'}
    (r : RecipRel a a') (g : a.Good) : a'.Good := by
  obtain ⟨gR, ghost, gsp, gTau, ginstTau, geTau, ghc⟩ := h
  obtain ⟨_, _, _, _, _, w, _⟩ := D
  obtain ⟨_, _, _, _, _, w', _⟩ := D'
  dsimp only at gR ghost gsp gTau ginstTau geTau ghc
  subst gR; subst ghost; subst gsp
  cases w; cases w'
  dsimp only at gTau ginstTau geTau ghc
  subst gTau; subst ginstTau; subst geTau; subst ghc
  subst hΩ; subst h1; subst h2
  obtain ⟨κ, art⟩ := a
  obtain ⟨κ', art'⟩ := a'
  obtain ⟨r1, r2⟩ := r
  cases r1; cases r2
  exact ⟨g.1, g.2, g.3, g.4⟩

theorem SetupRel.good_of (h : SameGeo D D') {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (hδ : HEq X.delta X'.delta)
    (he : ∀ i i', HEq i i' → ∀ b x', ∃ x, HEq (sideEmb X i b x) (sideEmb X' i' b x') ∧ embLL0 D x = embLL0 D' x')
    {ρ : Setup X} {ρ' : Setup X'} (r : SetupRel ρ ρ') (g : ρ.Good) : ρ'.Good := by
  have grc := r.rc.good h (eq_of_heq h1.Om) h1.instOm h1.algOm g.rc
  have h0 := h
  obtain ⟨gR, ghost, gsp, gTau, ginstTau, geTau, ghc⟩ := h
  obtain ⟨_, _, _, _, _, w, _⟩ := D
  obtain ⟨_, _, _, _, _, w', _⟩ := D'
  dsimp only at gR ghost gsp gTau ginstTau geTau ghc
  subst gR; subst ghost; subst gsp
  cases w; cases w'
  dsimp only at gTau ginstTau geTau ghc
  subst gTau; subst ginstTau; subst geTau; subst ghc
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, xO0, xcrO0, xalgO0, xtopO0, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, xS0, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  dsimp only at a1 a2 a3
  subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl xO0 xcrO0 xalgO0 xtopO0 xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xS0 xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst xO0; subst xcrO0; subst xalgO0; subst xtopO0; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xS0; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  dsimp only at hδ
  subst hδ
  obtain ⟨⟨κ, art⟩, ch, bad, e, ek, B, om, Cl, rep, β, eG⟩ := ρ
  obtain ⟨⟨κ', art'⟩, ch', bad', e', ek', B', om', Cl', rep', β', eG'⟩ := ρ'
  obtain ⟨⟨r1, r2⟩, r3, r4, r5, r6, r7, r8, r9, r10, -, -⟩ := r
  dsimp only at r1 r2 r3 r4 r5 r6 r8
  subst r1 r2 r3 r4 r5 r6 r8
  refine ⟨grc, fun i => ⟨(g.ch i).1, (g.ch i).2⟩, g.bad_ne, g.goodSetup_bad_mem_badPlaces, g.goodSetup_badPlaces_conj, g.goodSetup_placesOverTwo_subset, g.goodSetup_count_eq_zero_off_badPlaces, fun i b x' => ?_, g.ek_e,
    fun i j b => (r7 i i .rfl j j rfl b).good h0 .rfl .rfl (g.base i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).1 (g.latS i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).2.1 (g.latT i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).2.2 (g.Pg i j b), fun i j b => ?_, fun i j b t ht => ?_,
    fun i j b t ht ha => ?_⟩
  · obtain ⟨x, h3, h4⟩ := he i i .rfl b x'
    exact (congrArg (e i b) (eq_of_heq h3).symm).trans ((g.e_LL0 i b x).trans h4)
  · have t := (r7 i i .rfl j j rfl b).de
    rw [g.delta i j b] at t
    exact TwistRel.eq ⟨t.1.symm, t.2.symm, t.3.symm⟩
  · exact (r7 i i .rfl j j rfl b).isWeil h0 .rfl .rfl .rfl .rfl
      (g.weil i j b ⟨t.Q, t.chi, t.res⟩ (TwistRel.good h0.symm ⟨.rfl, .rfl, .rfl⟩ ht))
  · exact (r7 i i .rfl j j rfl b).isClassSystem h0 .rfl .rfl (t := ⟨t.Q, t.chi, t.res⟩) ⟨.rfl, .rfl, .rfl⟩
      (r9 i i .rfl j j rfl b _ t ⟨.rfl, .rfl, .rfl⟩) (r10 i i .rfl j j rfl b _ t ⟨.rfl, .rfl, .rfl⟩)
      (g.classes i j b ⟨t.Q, t.chi, t.res⟩ (TwistRel.good h0.symm ⟨.rfl, .rfl, .rfl⟩ ht)
        ((r7 i i .rfl j j rfl b).adm h0 .rfl .rfl .rfl ha))

theorem val_move {T T' : Type} {n n' : ℕ} (hT : T = T') (hn : n = n') {a : T → GL (Fin n) ℂ} {a' : T' → GL (Fin n') ℂ}
    {c : T → Matrix (Fin n) (Fin n) ℂ} {c' : T' → Matrix (Fin n') (Fin n') ℂ} (ha : HEq a a') (hc : HEq c c')
    (g : ∀ τ, (a τ).val = c τ) (τ : T') : (a' τ).val = c' τ := by
  subst hT hn ha hc
  exact g τ

theorem mem_move {R R' : Ranks} {H : Host R} {H' : Host R'} (hR : R = R') (hH : HEq H H') {T T' : Type} (hT : T = T')
    {p : T → Finset (Pl H.E)} {p' : T' → Finset (Pl H'.E)} {c : T → Set (Pl H.E)} {c' : T' → Set (Pl H'.E)} (hp : HEq p p')
    (hc : HEq c c') {i : T} {i' : T'} (hi : HEq i i') {P : Pl H.E} {P' : Pl H'.E} (hP : HEq P P') (g : P ∈ p i → P ∈ c i) :
    P' ∈ p' i' → P' ∈ c' i' := by
  subst hR; subst hH; subst hT hp hc hi hP
  exact g

theorem grp_move {R R' : Ranks} {H : Host R} {H' : Host R'} {L L' : Fin 2 → Type} (hR : R = R') (hH : HEq H H') (hL : L = L')
    {r r' : ℕ} (e : r = R.r) (e' : r' = R'.r) {A B : Finset (Pl H.E)} {A' B' : Finset (Pl H'.E)} (hA : HEq A A') (hB : HEq B B')
    {u : (∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))) ≃* G0 A r}
    {u' : (∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))) ≃* G0 A' r'} (hu : HEq u u')
    {c : G0 B R.r ≃* ∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))}
    {c' : G0 B' R'.r ≃* ∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))} (hc : HEq c c')
    (g : ∀ x P (h : P ∈ A) (h' : P ∈ B) (a b : Fin r), (u x ⟨P, h⟩).val a b = (c.symm x ⟨P, h'⟩).val (Fin.cast e a) (Fin.cast e b)) :
    ∀ x P (h : P ∈ A') (h' : P ∈ B') (a b : Fin r'),
      (u' x ⟨P, h⟩).val a b = (c'.symm x ⟨P, h'⟩).val (Fin.cast e' a) (Fin.cast e' b) := by
  subst hR; subst hH; subst hL e e' hA hB hu hc
  exact g

theorem heq_app {T T' A : Type} (hT : T = T') {f : T → A} {f' : T' → A} (hf : HEq f f') {i : T} {i' : T'} (hi : HEq i i') :
    f i = f' i' := by
  subst hT hf hi
  rfl

variable {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem SetupRel.good (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (r : SetupRel ρ ρ') (g : ρ.Good) : ρ'.Good :=
  r.good_of h.sameGeo h.gal h.set h.delta (fun _ _ hi b x => ⟨e x, h.sideEmb_heq hi b x, h.embLL0_eq x⟩) g

theorem SetupRel.realPin (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (r : SetupRel ρ ρ') (p : RealPin X.R X.cG ρ) : RealPin X'.R X'.cG ρ' := by
  have G := h.sameGeo
  have back : ∀ (i' : D'.ntw.Tw) (j' : Fin D'.R.m), ∃ i : D.ntw.Tw, ∃ j : Fin D.R.m, HEq i i' ∧ (j : ℕ) = j' :=
    fun i' j' => ⟨cast h.Tw_eq.symm i', Fin.cast (congrArg Ranks.m h.gal.R).symm j', cast_heq _ _, rfl⟩
  have chain : ∀ {A A' : Type} {a c : A} {a' c' : A'}, HEq a a' → a = c → HEq c c' → a' = c' :=
    fun h1 h2 h3 => eq_of_heq (h1.symm.trans ((heq_of_eq h2).trans h3))
  constructor
  case deltaPl =>
    intro i' t' P' h1 h2
    obtain ⟨t, P, h3, h4⟩ := m.Q i' t' P' h1 h2
    exact mem_move h.gal.R h.gal.host h.Tw_eq h.set.pD r.ch (cast_heq h.Tw_eq.symm i') h4 (p.deltaPl _ t P h3) h2
  all_goals
    intro i' j' b
    obtain ⟨i, j, hi, hj⟩ := back i' j'
    have q := r.B i i' hi j j' hj b
    obtain ⟨hV, hW, rV, rW, hp, hm⟩ := G.spaces hj
  · exact chain q.F.ψ (p.psi i j b) m.ψ
  · exact chain q.F.θ (p.inf i j b) m.θ
  · exact chain q.F.sT (p.cartT i j b) ((m.MW j j' hj).cart_onb G hW).1
  · exact val_move h.Tau rV q.F.BS (m.BV j j' hj) (p.onbS i j b)
  · exact chain q.F.BT (p.onbT i j b) ((m.MW j j' hj).cart_onb G hW).2
  · exact chain q.F.ΛS (p.latS i j b) (m.ΛV j j' hj)
  · exact chain q.F.ΛT (p.latT i j b) (m.ΛW j j' hj)
  · exact chain q.F.βS (p.frS i j b) (m.βV j j' hj)
  · exact chain q.F.βT (p.frT i j b) (m.βW j j' hj)
  · exact chain q.F.f₀ (p.vac i j b) (m.vacP j j' hj)
  · exact chain q.G.Pg (p.Pg i j b) m.Pg
  · exact grp_move h.gal.R h.gal.host (eq_of_heq h.gal.PlG) (FWT.rank_Wc j) (FWT.rank_Wc j') q.G.Pg m.Pg
      (r.eG i i' hi j j' hj b) m.cG (p.grp i j b)
  · exact chain q.mu0 (p.mu0 i j b) (hj ▸ m.mu0 j)
  · exact chain q.eta (p.eta i j b) m.eta
  · exact G.chrEq q.de.chi (heq_app h.Tw_eq h.set.l hi ▸ m.delAt _) (p.delta i j b)
  · exact congrFun (chain q.w.ap (funext (p.ap i j b)) hp)
  · exact congrFun (chain q.w.am (funext (p.am i j b)) hm)

theorem BaseRel.sameBase {S T : HSp D} {S' T' : HSp D'} {B : Base S T} {B' : Base S' T'} (r : BaseRel B B') : SameBase B B' :=
  ⟨r.F.1, r.F.2, r.F.3, r.F.4, r.F.5, r.F.6, r.F.7, r.F.8, r.F.9, r.F.10, r.G.1, r.G.2, r.G.3, ⟨r.de.1, r.de.2, r.de.3⟩,
    r.w.1, r.w.2, r.w.3, r.w.4, r.w.5, r.w.6, r.mu0, r.eta⟩

theorem SameBase.baseRel {S T : HSp D} {S' T' : HSp D'} {B : Base S T} {B' : Base S' T'} (r : SameBase B B') : BaseRel B B' :=
  ⟨⟨r.ψ, r.θ, r.sT, r.BS, r.BT, r.ΛS, r.ΛT, r.βS, r.βT, r.f₀⟩, ⟨r.Pg, r.P, r.mu⟩, ⟨r.de.1, r.de.2, r.de.3⟩,
    ⟨r.p, r.q, r.ap, r.am, r.c, r.lam⟩, r.mu0, r.eta⟩

theorem setupRel_iff_sameData {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} : SetupRel ρ ρ' ↔ SameData ρ ρ' :=
  ⟨fun r => ⟨r.rc.1, r.rc.2, r.ch, r.bad, r.e, r.ek, fun i i' hi j j' hj b => (r.B i i' hi j j' hj b).sameBase, r.om,
      fun i i' hi j j' hj b t t' ht => ⟨r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩, r.rep i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩⟩,
      r.β, r.eG⟩,
    fun r => ⟨⟨r.κ, r.art⟩, r.ch, r.bad, r.e, r.ek, fun i i' hi j j' hj b => (r.B i i' hi j j' hj b).baseRel, r.om,
      fun i i' hi j j' hj b t t' ht => (r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩).1,
      fun i i' hi j j' hj b t t' ht => (r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩).2, r.β, r.eG⟩⟩

theorem setup_move_data : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameData ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' := by
  intro D D' ι e h X X' m ρ g p
  obtain ⟨ρ', r⟩ := exists_setupRel h.sameGeo h.gal h.set ρ
  exact ⟨ρ', setupRel_iff_sameData.1 r, r.good h g, r.realPin h m p⟩

end GlobalTheory.TwInputs.Move

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.LocKerMod

theorem idxAt_frame : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := GlobalTheory.T.localLatticeIndex_cartanDecomposition_eq_normPow

theorem latIndex_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = idxAt T w h g := _root_.GlobalTheory.LocKerMod.latIndex_embV_inert

theorem latIndex_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = idxAt T w h g * idxAt T w' h' g := GlobalTheory.T.selfDualLatticeIndex_splitPlace_eq_mul
end GlobalTheory.LocKerMod

namespace GlobalTheory.LocKerMod
open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.LFun.SplitTie

theorem idx_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c e → ∀ (d : Fin T.rank → ℤ) (t : GU c T.rank), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c T.rank, ∀ k₂ ∈ KU c T.rank, latIndex T (GlobalTheory.FinZeta.embV T v (e.symm (k₁ * t * k₂))) = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  intro D T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨-, ⟨a, ha, -, hea⟩, -⟩ := he
  have hϖ : IsUnifV D.host.E w ϖ := hU.2.2.2.1
  have hK : ∀ k ∈ KU c T.rank, (k : GL (Fin T.rank) (w.adicCompletion D.host.E)) ∈ KGL w (n := T.rank) :=
    fun k hk => (Subgroup.mem_subgroupOf.1 hk).2
  rw [latIndex_inert D T v w h hw]
  refine idxAt_frame D T v w h a ha ϖ hϖ d (t : GL (Fin T.rank) (w.adicCompletion D.host.E)) ht _ (hK k₁ hk₁) _
    (hK k₂ hk₂) _ ?_
  have h1 := hea (e.symm (k₁ * t * k₂))
  rw [MulEquiv.apply_symm_apply] at h1
  rw [show ((k₁ : GL (Fin T.rank) (w.adicCompletion D.host.E)) * t * k₂) = ((k₁ * t * k₂ : GU c T.rank) : GL (Fin T.rank) (w.adicCompletion D.host.E)) by simp, h1]
  group

theorem idx_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), latIndex T (GlobalTheory.FinZeta.embV T v (e.symm (k₁ * t * k₂))) = qV D.host.E w ^ (∑ i, |d i|).toNat := by
  intro D T v w h hv e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  have hE := isCMExt_host D
  have hJ := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 T
  have hL := SelfDual.isSelfDualAt_frameLat D T v
  have hspan : Submodule.span D.host.E (frameLat T : Set (Fin T.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (T.L0 : Set T.V) = ⊤ := by
      let W := Submodule.span D.host.E (T.L0 : Set T.V)
      change W = ⊤
      by_contra h
      let e : T.V ≃ₗ⋆[D.host.E] T.V :=
        (T.frame.equivFun.trans (starLinearEquiv D.host.E)).trans T.frame.equivFun.symm
      let g : T.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (T.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E T.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ T.L0 := by
        rw [← T.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : T.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : T.hT y (e x) = 0 := by
          rw [(T.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] T.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict T.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) T.L0 := Module.Finite.iff_fg.mpr T.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat T : Set (Fin T.rank → D.host.E)) =
        T.frame.equivFun.toLinearMap '' (T.L0 : Set T.V) :=
      (T.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨-, w', hne, hu, -, -, -⟩ := GlobalTheory.LFun.SplitChart.split_chart_and_places hE hJ (frameLat_fg T)
    hspan h hv hL
  have h' : w'.under (𝓞 D.host.F) = v := (hu w').2 (Or.inr rfl)
  obtain ⟨c, hc, hqc, -, he'⟩ := exists_conj_chart hE hJ hL hne h h' he
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    unfold IsUnifV at hϖ
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hO : ∀ a, c a ∈ Formalism.UG.Ov D.host.E w' ↔ a ∈ Formalism.UG.Ov D.host.E w := fun a => map_mem_Ov_iff c hc a
  have htinv : ((t⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)) : Matrix _ _ _) = Matrix.diagonal (fun i => ϖ ^ (-d i)) := by
    have h1 : (t : Matrix _ _ _) * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
      rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv h1]
  have hdiag : (invT c T.rank t).1 = Matrix.diagonal (fun i => c ϖ ^ (-d i)) := by
    ext i j
    rw [invT_val, htinv, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [map_zpow₀]
    · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]
  have hunif : IsUnifV D.host.E w' (c ϖ) := by
    unfold IsUnifV at hϖ ⊢
    rw [hc, hϖ]
  have hK : ∀ k ∈ KGL w (n := T.rank), invT c T.rank k ∈ KGL w' (n := T.rank) := fun k hk => (mem_iff_invT c hO k).1 hk
  obtain ⟨⟨a, ha, hea⟩, -⟩ := he
  obtain ⟨⟨a', ha', hea'⟩, -⟩ := he'
  rw [latIndex_split D T v w w' h h' hv hne]
  have e1 : GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)) = a * (k₁ * t * k₂) * a⁻¹ := by
    have := hea (e.symm (k₁ * t * k₂))
    rw [MulEquiv.apply_symm_apply] at this
    calc _ = a * (a⁻¹ * GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)) * a) * a⁻¹ := by group
      _ = _ := by rw [← this]
  have e2 : GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' (e.symm (k₁ * t * k₂)) =
      a' * (invT c T.rank k₁ * invT c T.rank t * invT c T.rank k₂) * a'⁻¹ := by
    have := hea' (e.symm (k₁ * t * k₂))
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, map_mul, map_mul] at this
    calc _ = a' * (a'⁻¹ * GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' (e.symm (k₁ * t * k₂)) * a') * a'⁻¹ := by group
      _ = _ := by rw [← this]
  have hs : ∑ i, |d i| = (∑ i, max (d i) 0) + ∑ i, max (-d i) 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total 0 (d i) with hd | hd
    · rw [abs_of_nonneg hd, max_eq_left hd, max_eq_right (by omega), add_zero]
    · rw [abs_of_nonpos hd, max_eq_right hd, max_eq_left (by omega), zero_add]
  rw [idxAt_frame D T v w h a ha ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ _ e1,
    idxAt_frame D T v w' h' a' ha' (c ϖ) hunif (fun i => -d i) _ hdiag _ (hK k₁ hk₁) _ (hK k₂ hk₂) _ e2, hqc,
    ← pow_add, hs, Int.toNat_add (Finset.sum_nonneg fun i _ => le_max_right _ _) (Finset.sum_nonneg fun i _ => le_max_right _ _)]
end GlobalTheory.LocKerMod

namespace GlobalTheory.LocKerMod

theorem exists_over {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
      (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  exact ⟨⟨Q, hQ.isPrime, fun h0 => v.ne_bot (by
    rw [← e, h0, Ideal.under_bot])⟩,
    HeightOneSpectrum.ext e⟩

theorem norm_split (q : ℕ) (hq : 0 < q) (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) (m s : ℤ) (hs : 0 ≤ s) :
    ‖z ^ m * (q : ℂ) ^ (-((N : ℂ) / 2) * (s : ℂ))‖ ^ 2 * ((q ^ s.toNat : ℕ) : ℝ) ^ N = 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [norm_mul, norm_zpow, hz, _root_.one_zpow, one_mul, show (q : ℂ) = ((q : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hq']
  have hre : (-((N : ℂ) / 2) * (s : ℂ)).re = -((N : ℝ) / 2) * s := by
    simp [Complex.mul_re]
  rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, Nat.cast_pow, ← Real.rpow_natCast (q : ℝ) s.toNat,
    ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, ← Real.rpow_add hq']
  have : (s.toNat : ℝ) = s := by exact_mod_cast Int.toNat_of_nonneg hs
  rw [this]
  have : -((N : ℝ) / 2) * s * ((2 : ℕ) : ℝ) + s * N = 0 := by push_cast; ring
  rw [this, Real.rpow_zero]

theorem norm_inert (q : ℕ) (hq : 0 < q) (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) (m : ℤ) (hm : 0 ≤ m) :
    ‖(z * ((q : ℂ) ^ N)⁻¹) ^ m‖ ^ 2 * (((q ^ 2) ^ m.toNat : ℕ) : ℝ) ^ N = 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  simp only [Int.toNat_natCast, zpow_natCast, norm_pow, norm_mul, norm_inv, hz, one_mul, Complex.norm_natCast]
  push_cast
  rw [← pow_mul, ← pow_mul, ← pow_mul, inv_pow, ← pow_mul]
  rw [show N * (k * 2) = 2 * (k * N) by ring]
  exact inv_mul_cancel₀ (pow_ne_zero _ hq'.ne')

theorem sq_norm_mul_latIndex : ∀ (D : D7) (T : HSp D) (N : ℕ) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.FinZeta.Gv T v → ℂ), GlobalTheory.FinZeta.IsLocKer T N (GlobalTheory.LFun.val χ) v φ → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) → ∀ a : GlobalTheory.FinZeta.Gv T v, ‖φ a‖ ^ 2 * (latIndex T (GlobalTheory.FinZeta.embV T v a) : ℝ) ^ N = 1 := by
  intro D T N χ v φ hφ _ a
  obtain ⟨w, h⟩ := exists_over (D := D) v
  by_cases hs : IsSplit (E := D.host.E) v
  · obtain ⟨e, he⟩ := (GlobalTheory.ChartsAll.exists_charts D T v w h).1 hs
    have hk := (hφ w h).1 hs e he
    obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := D.host.E) w
    obtain ⟨d, -, k₁, hk₁, k₂, hk₂, ec⟩ :=
      Formalism.UG.Final.CartanDecomp D.host.E w T.rank ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ (e a)
    have htd : (k₁⁻¹ * e a * k₂⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 =
        Matrix.diagonal (fun i => ϖ ^ d i) := by
      rw [Units.val_mul, Units.val_mul, ec]
      simp [Matrix.mul_assoc]
      rfl
    have ha : a = e.symm (k₁ * (k₁⁻¹ * e a * k₂⁻¹) * k₂) := by
      rw [show k₁ * (k₁⁻¹ * e a * k₂⁻¹) * k₂ = e a by group, MulEquiv.symm_apply_apply]
    have hv := hk ϖ hϖ d _ htd k₁ hk₁ k₂ hk₂
    rw [Function.comp_apply, ← ha] at hv
    rw [hv]
    conv_lhs => rw [ha]
    rw [idx_split D T v w h hs e he ϖ hϖ d _ htd k₁ hk₁ k₂ hk₂]
    exact norm_split _ (Nat.pos_of_ne_zero fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
      _ (GlobalTheory.LFun.norm_val χ w) N _ _ (Finset.sum_nonneg fun i _ => abs_nonneg (d i))
  · have hI := GlobalTheory.LFun.exists_isInertChart D.sp.cm.sig (isCMExt_host D) v
    obtain ⟨hw, -, hch⟩ := (GlobalTheory.ChartsAll.exists_charts D T v w h).2 hs
    obtain ⟨-, ⟨c, hc, -⟩, -, hN, H⟩ := hI.2 w h hw
    obtain ⟨ϖ, hU⟩ := (H c hc).1
    obtain ⟨e, he⟩ := hch c hc
    have hk := (hφ w h).2 hw c ϖ e hU he
    obtain ⟨d, t, -, ht, k₁, hk₁, k₂, hk₂, ea⟩ := GlobalTheory.LFun.cartanU hU (e a)
    have ha : a = e.symm (k₁ * t * k₂) := by rw [← ea, MulEquiv.symm_apply_apply]
    have hv := hk d t ht k₁ hk₁ k₂ hk₂
    rw [Function.comp_apply, ← ha] at hv
    rw [hv]
    conv_lhs => rw [ha]
    rw [idx_inert D T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂]
    have hq : qV D.host.E w = qV D.host.F v ^ 2 := hN
    rw [hq]
    exact norm_inert _ (Nat.pos_of_ne_zero fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
      _ (GlobalTheory.LFun.norm_val χ w) N _ (Finset.sum_nonneg fun i _ => le_max_right _ _)

end GlobalTheory.LocKerMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterUnitValue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TupleCharAtType

theorem natCast_notMem {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) : ((q : ℕ) : 𝓞 E) ∉ v.asIdeal := fun hv' => by
  obtain ⟨s, t, hst⟩ : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem isUnitAt_of_notMem {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} (u : 𝓞 E)
    (hu : (u : E) ≠ 0) (hv : u ∉ v.asIdeal) : IsUnitAt v (atFin v (Units.mk0 (u : E) hu)) := by
  show Valued.v ((u : E) : v.adicCompletion E) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv

end GlobalTheory.TupleCharAtType
end

