module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem
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

structure SameGeo (D D' : D7) : Prop where
  R : D.R = D'.R
  host : HEq D.host D'.host
  sp : HEq D.sp D'.sp
  Tau : D.what₂.Tau = D'.what₂.Tau
  instTau : HEq D.what₂.instTau D'.what₂.instTau
  eTau : HEq D.eTau D'.eTau
  hc : HEq D.hc D'.hc

theorem CopyTw.sameGeo {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) :
    SameGeo D D' := ⟨h.gal.R, h.gal.host, h.sp, h.Tau, h.instTau, h.eTau, h.hc⟩

scoped macro "geo_cases " h:ident D:ident D':ident : tactic =>
  `(tactic| (
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := $h
    cases $D:ident with | mk R host sp vol volp what₂ eTau hc => ?_
    cases $D':ident with | mk R' host' sp' vol' volp' rows' eTau' hc' => ?_
    dsimp only at a1 a2 a3 a4 a5 a6 a7
    subst a1; subst a2; subst a3
    cases what₂; cases rows'
    dsimp only at a4 a5 a6 a7
    subst a4; subst a5; subst a6; subst a7))

variable {D D' : D7}

structure RecipRel {Ω Ω' : Type} [Field Ω] [Algebra D.host.E Ω] [Field Ω'] [Algebra D'.host.E Ω'] (a : Recip D Ω) (a' : Recip D' Ω') :
    Prop where
  κ : HEq a.κ a'.κ
  art : HEq a.art a'.art

structure TwistRel {A : Type} [CommGroup A] (t : Twist D A) (t' : Twist D' A) : Prop where
  Q : HEq t.Q t'.Q
  chi : HEq t.chi t'.chi
  res : HEq t.res t'.res

structure FrameRel {S T : HSp D} {S' T' : HSp D'} (F : Frame S T) (F' : Frame S' T') : Prop where
  ψ : HEq F.ψ F'.ψ
  θ : HEq F.θ F'.θ
  sT : HEq F.sT F'.sT
  BS : HEq F.BS F'.BS
  BT : HEq F.BT F'.BT
  ΛS : HEq F.ΛS F'.ΛS
  ΛT : HEq F.ΛT F'.ΛT
  βS : HEq F.βS F'.βS
  βT : HEq F.βT F'.βT
  f₀ : HEq F.f₀ F'.f₀

structure TypeRel {r r' : ℕ} (G : TypeDat D r) (G' : TypeDat D' r') : Prop where
  Pg : HEq G.Pg G'.Pg
  P : HEq G.P G'.P
  mu : HEq G.mu G'.mu

structure WeightRel {n n' : ℕ} (w : Weight D n) (w' : Weight D' n') : Prop where
  p : HEq w.p w'.p
  q : HEq w.q w'.q
  ap : HEq w.ap w'.ap
  am : HEq w.am w'.am
  c : HEq w.c w'.c
  lam : HEq w.lam w'.lam

structure BaseRel {S T : HSp D} {S' T' : HSp D'} (B : Base S T) (B' : Base S' T') : Prop where
  F : FrameRel B.F B'.F
  G : TypeRel B.G B'.G
  de : TwistRel B.de B'.de
  w : WeightRel B.w B'.w
  mu0 : HEq B.mu0 B'.mu0
  eta : HEq B.eta B'.eta

theorem TwistRel.good (h : SameGeo D D') {A : Type} [CommGroup A] {t : Twist D A} {t' : Twist D' A} (r : TwistRel t t')
    (g : t.Good) : t'.Good := by
  geo_cases h D D'
  obtain ⟨Q, chi, res⟩ := t
  obtain ⟨Q', chi', res'⟩ := t'
  obtain ⟨r1, r2, r3⟩ := r
  cases r1; cases r2; cases r3
  exact ⟨g.1, g.2, g.3, g.4, g.5, g.6⟩

scoped macro "base_cases " r:ident B:ident B':ident : tactic =>
  `(tactic| (
    obtain ⟨hr, ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _, _, _⟩, _, _⟩ := $B
    obtain ⟨hr', ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _, _, _⟩, _, _⟩ := $B'
    obtain ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩, ⟨g1, g2, g3⟩, ⟨d1, d2, d3⟩, ⟨w1, w2, w3, w4, w5, w6⟩, m1, m2⟩ := $r
    dsimp only at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 g1 g2 g3 d1 d2 d3 w1 w2 w3 w4 w5 w6 m1 m2
    subst f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 g1 g2 g3 d1 d2 d3 w1 w2 w3 w4 w5 w6 m1 m2))

theorem BaseRel.good (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') (g : B.Good) : B'.Good := by
  have gd := r.de.good h g.de
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  have v := g.frame.vac.2
  refine ⟨g.even, g.odd, ⟨g.frame.1, g.frame.2, g.frame.3, g.frame.4, g.frame.5, g.frame.6, g.frame.7, g.frame.8, g.frame.vac.1, ?_⟩,
    gd, ⟨g.places.1, g.places.2, g.places.3⟩, ⟨g.wt.1, g.wt.2⟩, g.sig, g.sigOK, g.eta, g.hecke, g.real, g.unram, g.tame, g.inf⟩
  exact ⟨v.1, ⟨v.2.1, v.2.2, v.2.3, v.2.4⟩, v.3, v.4, v.5⟩

theorem BaseRel.isWeil (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') {ν : (AE D)ˣ →* Circle} {ν' : (AE D')ˣ →* Circle} (hν : HEq ν ν')
    {ω : PairRep S T} {ω' : PairRep S' T'} (hω : HEq ω ω') (g : B.IsWeil ν ω) : B'.IsWeil ν' ω' := by
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  subst hν; subst hω
  refine ⟨g.1, g.2, g.3, g.4, g.5, fun p f a => ?_, fun x y w f a => g.7 x y w f ⟨a.1, a.2, a.3, a.4⟩,
    fun x hx y hy f a => g.8 x hx y hy f ⟨a.1, a.2, a.3, a.4⟩, fun f a => g.9 f ⟨a.1, a.2, a.3, a.4⟩,
    fun μ F h1 h2 p f a => g.10 μ F h1 h2 p f ⟨a.1, a.2, a.3, a.4⟩, fun e he x y h1 h2 z w h3 h4 => ?_⟩
  · have b := g.6 p f ⟨a.1, a.2, a.3, a.4⟩
    exact ⟨b.1, b.2, b.3, b.4⟩
  · obtain ⟨r, hr, h5⟩ := g.11 e he x y h1 h2 z w h3 h4
    exact ⟨r, hr, fun l h6 f a => h5 l (fun u hu f a => h6 u hu f ⟨a.1, a.2, a.3, a.4⟩) f ⟨a.1, a.2, a.3, a.4⟩⟩

theorem BaseRel.adm (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') {Q : Finset (Pl D.host.E)} {Q' : Finset (Pl D'.host.E)} (hQ : HEq Q Q')
    (g : B'.admitted Q') : B.admitted Q := by
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  subst hQ
  exact ⟨⟨g.1.1, g.1.2, g.1.3⟩, g.2⟩

theorem BaseRel.isClassSystem (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') {t : Twist D Circle} {t' : Twist D' Circle} (ht : TwistRel t t') {I I' : Type} (hI : I = I')
    {y : I → GA D S} {y' : I' → GA D' S'} (hy : HEq y y') (g : IsClassSystem S (B.levJ t) y) :
    IsClassSystem S' (B'.levJ t') y' := by
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  obtain ⟨Q, chi, res⟩ := t
  obtain ⟨Q', chi', res'⟩ := t'
  obtain ⟨r1, r2, r3⟩ := ht
  cases r1; cases r2; cases r3
  subst hI; subst hy
  exact ⟨g.1, g.2, g.3⟩

theorem BaseRel.isBaseFrame (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') :
    (Lev.IsBaseFrame S B.F.βS B.F.ΛS 1 → Lev.IsBaseFrame S' B'.F.βS B'.F.ΛS 1) ∧
    (Lev.IsBaseFrame T B.F.βT B.F.ΛT 1 → Lev.IsBaseFrame T' B'.F.βT B'.F.ΛT 1) ∧
    ((∀ P ∈ B.G.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k)) → ∀ P ∈ B'.G.Pg, ∃ k, P ∈ placesOver D'.host.E (D'.host.g k)) := by
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  exact ⟨id, id, id⟩

theorem SameGeo.symm (h : SameGeo D D') : SameGeo D' D :=
  ⟨h.R.symm, h.host.symm, h.sp.symm, h.Tau.symm, h.instTau.symm, h.eTau.symm, h.hc.symm⟩

theorem SameGeo.spaces (h : SameGeo D D') {j : Fin D.R.m} {j' : Fin D'.R.m} (hj : (j : ℕ) = j') :
    HEq (Vc D j) (Vc D' j') ∧ HEq (Wc D j) (Wc D' j') ∧ (Vc D j).rank = (Vc D' j').rank ∧ (Wc D j).rank = (Wc D' j').rank ∧
    HEq (fun τ => aPl D j ((Wc D j).sig (tauE D τ)).1 τ) (fun τ => aPl D' j' ((Wc D' j').sig (tauE D' τ)).1 τ) ∧
    HEq (fun τ => aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ)
      (fun τ => aMi D' j' ((Wc D' j').sig (tauE D' τ)).1 ((Wc D' j').sig (tauE D' τ)).2 τ) := by
  geo_cases h D D'
  cases Fin.ext hj
  exact ⟨HEq.rfl, HEq.rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩

theorem SameModel.cart_onb (h : SameGeo D D') {V : HSp D} {V' : HSp D'} (hV : HEq V V') {P : D.what₂.Tau → SPar}
    {P' : D'.what₂.Tau → SPar} {M : Mult.DSModel V P} {M' : Mult.DSModel V' P'} (r : SameModel M M') :
    HEq (cart M) (cart M') ∧ HEq (onb M) (onb M') := by
  have h1 := r.ε
  have h2 := r.fr
  clear r
  geo_cases h D D'
  subst hV
  cases M; cases M'
  dsimp only at h1 h2
  subst h1; subst h2
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem SameGeo.chrEq (h : SameGeo D D') {c : (AE D)ˣ →* Circle} {c' : (AE D')ˣ →* Circle} (hc : HEq c c')
    {χ : Formalism.L2.Host.HChar D.host.E} {χ' : Formalism.L2.Host.HChar D'.host.E} (hχ : HEq χ χ') (g : ChrEq c χ) : ChrEq c' χ' := by
  geo_cases h D D'
  subst hc; subst hχ
  exact g

section Setup

variable {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}

structure SetupRel (ρ : Setup X) (ρ' : Setup X') : Prop where
  rc : RecipRel ρ.rc ρ'.rc
  ch : HEq ρ.ch ρ'.ch
  bad : HEq ρ.bad ρ'.bad
  e : HEq ρ.e ρ'.e
  ek : HEq ρ.ek ρ'.ek
  B : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b, BaseRel (ρ.B i j b) (ρ'.B i' j' b)
  om : HEq ρ.om ρ'.om
  Cl : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b t t', TwistRel t t' →
    ρ.Cl i j b t = ρ'.Cl i' j' b t'
  rep : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b t t', TwistRel t t' →
    HEq (ρ.rep i j b t) (ρ'.rep i' j' b t')
  β : HEq ρ.β ρ'.β
  eG : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b, HEq (ρ.eG i j b) (ρ'.eG i' j' b)

end Setup

theorem TwistRel.eq {A : Type} [CommGroup A] {t t' : Twist D A} (r : TwistRel t t') : t = t' := by
  obtain ⟨Q, chi, res⟩ := t
  obtain ⟨Q', chi', res'⟩ := t'
  obtain ⟨r1, r2, r3⟩ := r
  cases r1; cases r2; cases r3
  rfl

end GlobalTheory.TwInputs.Move

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowDiagonalMulMemLatticeIff
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.CellDec.RowPos
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_val (v : HeightOneSpectrum (𝓞 E)) (x : GA E n) (i j : Fin n) :
    (compV E n v x).val i j = pLoc E v (pFin E (x.val i j)) := rfl

theorem row_unip_mul {R : Type} [CommRing R] {m : ℕ} {U : GL (Fin (m + 1)) R}
    (hU : U ∈ GlobalTheory.SmGL.unipB R (Fin (m + 1))) (K : GL (Fin (m + 1)) R) (i : Fin (m + 1)) :
    (U * K).val (Fin.last m) i = K.val (Fin.last m) i := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hU
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · rw [h2, one_mul]
  · intro j _ hj
    rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sub_single_apply {m : ℕ} (y : Fin (m + 1) → Af E) (i : Fin (m + 1)) (v : HeightOneSpectrum (𝓞 E)) :
    (((y - Pi.single (Fin.last m) (1 : Af E)) : Fin (m + 1) → Af E) i) v = y i v - if i = Fin.last m then 1 else 0 := by
  change pLoc E v ((y - Pi.single (Fin.last m) (1 : Af E) : Fin (m + 1) → Af E) i) = pLoc E v (y i) - _
  rw [Pi.sub_apply, map_sub]
  congr 1
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]

theorem val_sub_ite_le_one {v : HeightOneSpectrum (𝓞 E)} {x : v.adicCompletion E} (hx : Valued.v x ≤ 1) (p : Prop)
    [Decidable p] : Valued.v (x - if p then 1 else 0) ≤ 1 := by
  refine (Valuation.map_sub _ _ _).trans (max_le hx ?_)
  split_ifs
  · rw [map_one]
  · rw [map_zero]; exact zero_le'

end GlobalTheory.CellDec.RowPos


open GlobalTheory.CellDec GlobalTheory.CellDec.RowPos in
theorem GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      ((fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈
        GlobalTheory.ThetaPoisson.latt (m + 1) J ↔
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J) := by
  intro E _ _ m T ϖ hϖ J hJ g hg l hl
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hgv : ∀ v i, (pFin E ((u * k).val (Fin.last m) i)) v = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i
    change pLoc E v _ = _
    rw [← compV_val, map_mul, row_unip_mul (compV_mem_unipB v hu)]
  have htv : ∀ v i, (pFin E ((tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) v =
      ((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) *
        (pFin E ((u * k).val (Fin.last m) i)) v := by
    intro v i
    change pLoc E v _ = _ * pLoc E v _
    rw [← compV_val, ← compV_val, map_mul (compV E (m + 1) v), compV_tl, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul]
  refine forall_congr' fun i => ?_
  rw [GroundTheory.Global.mem_idealFiniteAdeles, GroundTheory.Global.mem_idealFiniteAdeles]
  refine forall_congr' fun v => ?_
  rw [sub_single_apply, sub_single_apply]
  beta_reduce
  rw [htv]
  by_cases hv : v ∈ T
  · rw [l.2 v hv]
    simp
  · rw [hJ v hv]
    have hK := (GlobalTheory.AdelicU.mem_GLint_iff.1 (mem_US.1 hk v hv)).1 (Fin.last m) i
    have hK' : Valued.v ((compV E (m + 1) v k).val (Fin.last m) i) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hK
    have hϖ1 : Valued.v ((ϖ v : v.adicCompletion E)) ≤ 1 := by
      rw [hϖ v]; exact le_of_lt (by decide)
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (hl v)
    have hp : Valued.v (((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)) ≤ 1 := by
      rw [ha, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one' hϖ1 a
    rw [hgv, neg_zero, WithZero.exp_zero]
    refine ⟨fun _ => val_sub_ite_le_one hK' _, fun _ => val_sub_ite_le_one ?_ _⟩
    rw [map_mul]
    exact mul_le_one' hp hK'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowSubSingleNotMemLatticeOfNegExponent
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.CellDec.lastRow_sub_notMem_latt : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (w : HeightOneSpectrum (𝓞 E)),
      l.1 w (Fin.last m) < 0 →
      (fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∉
        GlobalTheory.ThetaPoisson.latt (m + 1) J := by
  intro E _ _ m T ϖ hϖ J hJ g hg l w hlw hmem
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hwT : w ∉ T := fun h => by rw [l.2 w h] at hlw; simp at hlw
  set a := l.1 w (Fin.last m) with ha
  set K := GlobalTheory.CellDec.compV E (m+1) w k with hKdef
  have hK : K ∈ GlobalTheory.LFun.KGL w (n := (m+1)) := GlobalTheory.CellDec.mem_US.1 hk w hwT
  obtain ⟨-, hK2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have hU := (GlobalTheory.SmGL.mem_unipB _).1 (GlobalTheory.CellDec.compV_mem_unipB w hu)
  have hent : ∀ i, (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
      ((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i := by
    intro i
    have h1 : (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
        (GlobalTheory.CellDec.compV E (m+1) w (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k))).val (Fin.last m) i := rfl
    rw [h1, map_mul, map_mul, GlobalTheory.CellDec.compV_tl, Units.val_mul, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hU.2, one_mul]
    · intro j _ hj
      rw [hU.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

  have hb : ∀ i, Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i -
      (if i = Fin.last m then 1 else 0)) ≤ 1 := by
    intro i
    have h2 := (GroundTheory.Global.mem_idealFiniteAdeles J).1 (hmem i) w
    rw [hJ w hwT, neg_zero, WithZero.exp_zero] at h2
    convert h2 using 2
    rw [← hent i]
    by_cases hi : i = Fin.last m
    · subst hi; simp
    · simp [hi]
  have hϖv : Valued.v ((ϖ w : w.adicCompletion E)) = WithZero.exp (-1 : ℤ) := hϖ w
  have hrow : ∀ i, Valued.v (K.val (Fin.last m) i) < 1 := by
    intro i
    have hle : Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) ≤ 1 := by
      by_cases hi : i = Fin.last m
      · have := hb i
        rw [if_pos hi] at this
        calc _ = Valued.v ((((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i - 1) + 1) := by
              rw [sub_add_cancel]
          _ ≤ max _ _ := Valuation.map_add _ _ _
          _ ≤ 1 := max_le this (by simp)
      · simpa [hi] using hb i
    have e : K.val (Fin.last m) i = ((ϖ w ^ (-a) : (w.adicCompletion E)ˣ) : w.adicCompletion E) *
        (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) := by
      rw [← mul_assoc, ← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
    rw [e, Valuation.map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖv, ← WithZero.exp_zsmul]
    have hlt : WithZero.exp ((-a) • (-1 : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; simp; omega
    calc _ ≤ WithZero.exp ((-a) • (-1 : ℤ)) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  have hone : ∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m) = 1 := by
    have := congrArg (fun M : Matrix (Fin (m+1)) (Fin (m+1)) (w.adicCompletion E) => M (Fin.last m) (Fin.last m))
      (Units.mul_inv K)
    simpa [Matrix.mul_apply] using this
  have hlt : Valued.v (∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Valuation.map_mul]
    have hj : Valued.v ((K⁻¹).val j (Fin.last m)) ≤ 1 := hK2 j (Fin.last m)
    calc _ ≤ Valued.v (K.val (Fin.last m) j) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hrow j
  rw [hone, map_one] at hlt
  exact lt_irrefl _ hlt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRow
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEul

open Matrix

theorem decomp_lastRow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
      g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ := by
  intro E _ _ _ m S J hJ N hN Φ hs g hg hΦ hind
  have hrow : ∀ h : GA E (m + 1), Pi.single (Fin.last m) 1 ᵥ* h.val = fun j => GlobalTheory.ZEul.lastRow h j := fun h => by
    rw [Matrix.single_one_vecMul]; rfl
  have hℓ : ∀ i : Fin (m + 1), i ≤ Fin.last m := Fin.le_last
  have hi : (fun i => pInf E ((Pi.single (Fin.last m) 1 ᵥ* g.val) i)) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := by
    rw [hrow]; exact hs (subset_tsupport _ hΦ)
  have hind' : ∀ i : Fin (m + 1), GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
      GlobalTheory.RSJ.natLat E N := by
    by_contra hc
    exact hind (by rw [GlobalTheory.RSJ.indN, if_neg hc])
  have hf : ∀ v ∈ S, ∀ j, Valued.v ((pFin E ((Pi.single (Fin.last m) 1 ᵥ* g.val) j) -
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j) v) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := by
    intro v hv j
    rw [hrow]
    have e : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j = if (j : ℕ) + 1 = m + 1 then 1 else 0 := by
      rw [Pi.single_apply]
      congr 1
      simp [Fin.ext_iff]
    rw [e]
    exact hN _ (hind' j) v hv
  obtain ⟨u, hu, p, hp, κ, hκ, e⟩ := GlobalTheory.RSLocalPart.exists_decomp hℓ hJ hg hi hf
  refine ⟨u, (GlobalTheory.SmGL.mem_unipB _).1 hu, p, ⟨hp.2, hp.1⟩, κ, hκ, ?_⟩
  rw [← e, hrow]
  congr 1
  rw [hrow] at hi
  have hu' := GlobalTheory.RSTheta.isUnit_of_mem_rowSet hi
  rw [← map_inv]
  congr 1
  have hm : GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) =
      GlobalTheory.RSTheta.rowMat (Fin.last m) (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) := by
    ext i j
    simp only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
    congr 1
    simp [Fin.ext_iff]
  have hd : IsUnit (GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i))).det := by
    rw [hm, GlobalTheory.RSTheta.det_rowMat]; exact hu'
  rw [GlobalTheory.RSJ.secInv, dite_eq_left hd]
  congr 1
  exact Units.ext (hm.trans (GlobalTheory.RSTheta.val_rowGL hu').symm)

end GlobalTheory.ZEul
end
end

