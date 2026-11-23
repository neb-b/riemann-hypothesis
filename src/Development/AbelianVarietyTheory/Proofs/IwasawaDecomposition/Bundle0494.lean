module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivAllEnl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
set_option maxHeartbeats 4000000

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.EqvMove

open Formalism.L2.DIV

variable {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ)
  (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)

abbrev datW (Pg : Finset (Pl D.host.E)) : LevDat D.host.E ℂ (Wc D i).rank :=
  datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B

def EqAtP (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {G : Type} [Group G] (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (β : GL (Fin (Wc D i).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) (eG : G → G0 Pg D.R.r) (X : G → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) β (datW i Pg) (eG g) k →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n,
      actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f ∈ T.cuspA ((i : ℕ) + 1) a n ∧
      ∃ y : T.Q.c.F, (y : ℂ) = X g ∧
        ∀ h, phiAt T i σ hV c (actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f) h = σ y * phiAt T i σ hV c f (h * k)

def EquivP (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {G : Type} [Group G] (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (β : GL (Fin (Wc D i).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) (eG : G → G0 Pg D.R.r) (X : G → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) β (datW i Pg) (eG g) k →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n,
      actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f ∈ T.cuspA ((i : ℕ) + 1) a n ∧
        ∀ h, phiAt T i σ hV c (actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f) h = X g * phiAt T i σ hV c f (h * k)

section Gen

variable {D : D7} (T : CoreJ D) (i : Fin D.R.m) (κi : WeightFamilies.Wt D ((i : ℕ) + 1))

theorem phi_eq_phiAt {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : T.R ((i : ℕ) + 1)) : O.phi cc f = phiAt T i O.s0 O.hV cc f := by
  have key : ∀ (σ : T.Q.c.F →+* ℂ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ),
      adel W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (castDict hV (T.mu ((i : ℕ) + 1) σ)) c) (rdU (T.U ((i : ℕ) + 1) σ) f) =
      castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) c) (rdU (T.U ((i : ℕ) + 1) σ) f)) := by
    intro σ W hV c
    subst hV
    rfl
  exact key O.s0 _ O.hV cc

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

theorem eqAt_iff (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)
    (halg : ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = (y : ℂ)) (hχ : R.grp_chiW) :
    EqAt T R κ O σ hV c ↔ EqAtP T i σ hV c (wtA (κ i)) (κ i).n O.lev (R.βW i) R.Pg (fun g => R.eG g)
      (fun g => D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) := by
  constructor
  · intro h g k hk f hf
    obtain ⟨h1, y, hy, h2⟩ := h g k hk f hf
    exact ⟨h1, y, (halg y).symm.trans (hy.trans (hχ i g).symm), h2⟩
  · intro h g k hk f hf
    obtain ⟨h1, y, hy, h2⟩ := h g k hk f hf
    exact ⟨h1, y, (halg y).trans (hy.trans (hχ i g)), h2⟩

theorem equivAt_iff {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ)
    (hχ : R.grp_chiW) :
    O.EquivAt κi cc ↔ EquivP T i O.s0 O.hV cc (wtA κi) κi.n O.lev (R.βW i) R.Pg (fun g => R.eG g)
      (fun g => D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) := by
  constructor
  · intro h g k hk f hf
    obtain ⟨h1, h2⟩ := h g k hk f hf
    refine ⟨h1, fun x => ?_⟩
    have := h2 x
    rw [phi_eq_phiAt, phi_eq_phiAt] at this
    rw [this, ← hχ i g]
  · intro h g k hk f hf
    obtain ⟨h1, h2⟩ := h g k hk f hf
    refine ⟨h1, fun x => ?_⟩
    rw [phi_eq_phiAt, phi_eq_phiAt, h2 x, ← hχ i g]

end Gen

section Congr

variable {D : D7} (T : CoreJ D) (i : Fin D.R.m)

theorem eqAtP_congr {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) {σ σ' : T.Q.c.F →+* ℂ} (hσ : σ' = σ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (hV' : T.V ((i : ℕ) + 1) σ' = Wc D i)
    {c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ} {c' : (T.U ((i : ℕ) + 1) σ').Comp → ℂ} (hc : HEq c' c)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La}
    {lev' : G' → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La} (hl : HEq lev' lev)
    {β β' : GL (Fin (Wc D i).rank) (EAf D)} (hβ : β' = β) {Pg Pg' : Finset (Pl D.host.E)} (hP : Pg' = Pg)
    {eG : G → G0 Pg D.R.r} {eG' : G' → G0 Pg' D.R.r} (he : HEq eG' eG) {X : G → ℂ} {X' : G' → ℂ} (hX : HEq X' X) :
    EqAtP T i σ' hV' c' a' n' lev' β' Pg' eG' X' ↔ EqAtP T i σ hV c a n lev β Pg eG X := by
  subst ha hn hσ hG hβ hP
  cases hi; cases hc; cases hl; cases he; cases hX
  rfl

theorem equivP_congr {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) {σ σ' : T.Q.c.F →+* ℂ} (hσ : σ' = σ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (hV' : T.V ((i : ℕ) + 1) σ' = Wc D i)
    {c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ} {c' : (T.U ((i : ℕ) + 1) σ').Comp → ℂ} (hc : HEq c' c)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La}
    {lev' : G' → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La} (hl : HEq lev' lev)
    {β β' : GL (Fin (Wc D i).rank) (EAf D)} (hβ : β' = β) {Pg Pg' : Finset (Pl D.host.E)} (hP : Pg' = Pg)
    {eG : G → G0 Pg D.R.r} {eG' : G' → G0 Pg' D.R.r} (he : HEq eG' eG) {X : G → ℂ} {X' : G' → ℂ} (hX : HEq X' X) :
    EquivP T i σ' hV' c' a' n' lev' β' Pg' eG' X' ↔ EquivP T i σ hV c a n lev β Pg eG X := by
  subst ha hn hσ hG hβ hP
  cases hi; cases hc; cases hl; cases he; cases hX
  rfl

end Congr

theorem heq_fun_of {G G' : Type} {Y : Type} (hG : G' = G) (X : G → Y) (X' : G' → Y)
    (h : ∀ g' g, HEq g' g → X' g' = X g) : HEq X' X := by
  subst hG
  exact heq_of_eq (funext fun g => h g g HEq.rfl)

theorem heq_coe_eG {E : Type} [Field E] [NumberField E] {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G)
    (hi : HEq iG' iG) {Pg Pg' : Finset (Pl E)} {r : ℕ} (hP : Pg' = Pg) (e : G ≃* G0 Pg r) (e' : G' ≃* G0 Pg' r)
    (h : HEq e' e) : HEq (fun g => e' g) (fun g => e g) := by
  subst hG hP
  cases hi
  cases h
  rfl

theorem equivAll_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (O' : ∀ i, OMDat core'.toCore R'.toRealDat i Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev) →
        EquivAll core' R'.toRealDat κ' O' ∧ ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          (z.geo.O i).EquivAt (z.geo.κ i) (z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0) →
          (O' i').EquivAt (κ' i') (core'.cE ((i' : ℕ) + 1) (O' i').s0) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg' hcore Xg tr R' cG' hP hRS κ' hκ O' hO
  obtain ⟨h1, -, -, hR⟩ := hE
  have hι := enlEmb_spec hR
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hG : Gc _ w'.px = Gc B w.px := by rw [hpx']; rfl
  have hi : HEq (inferInstance : Group (Gc _ w'.px)) (inferInstance : Group (Gc B w.px)) := by rw [hpx']; exact HEq.rfl
  have hχ' : R'.toRealDat.grp_chiW := hP.char.base.grp.chiW
  have hχ : z.R.toRealDat.grp_chiW := z.pins.char.base.grp.chiW
  obtain ⟨-, -, hβW, -, -, -, -, -, -, hPg, heG, -, hI, -⟩ := hRS.1
  rcases core' with ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩
  obtain ⟨hH, hl, hc, hDw, hXo, hU, hV, hdict, hmu, -, hcE, -, -, -⟩ := hcore
  obtain rfl : H' = z.core.Q.H := eq_of_heq hH
  obtain rfl : l' = z.core.Q.l := eq_of_heq hl
  obtain rfl : c' = z.core.Q.c := eq_of_heq hc
  obtain rfl : Dw' = z.core.Q.Dw := eq_of_heq hDw
  obtain rfl : Xo' = z.core.Q.Xo := eq_of_heq hXo
  obtain rfl : U' = z.core.U := eq_of_heq hU
  obtain rfl : V' = z.core.V := eq_of_heq hV
  obtain rfl : dict' = z.core.dict := eq_of_heq hdict
  obtain rfl : mu' = z.core.mu := eq_of_heq hmu
  obtain rfl : cE' = z.core.cE := eq_of_heq hcE

  refine ⟨fun i σ hg hV' hex => ?_, fun i i' hii hE => ?_⟩
  · obtain ⟨c₁, hcu, hq⟩ := hex
    have hA' := (eqAt_iff _ i R'.toRealDat κ' (O' i) σ hV' c₁ halg' hχ').1 hq
    obtain ⟨a1, a2, a3⟩ := hκ i i rfl
    have ha : wtA (κ' i) = wtA (z.geo.κ i) := by
      have e1 := eq_of_heq a1
      have e2 := eq_of_heq a2
      unfold wtA
      rw [e1, e2]
      rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hιc⟩ := hI i i rfl
    obtain ⟨-, -, hchi, -⟩ := hιc (enlEmb hR) hι
    have hX : HEq (fun g => (w'.st Z').toD7.what₂.embLL (((R'.FW i).chi g : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL))
        (fun g => (w.st Z).toD7.what₂.embLL (((z.R.FW i).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) :=
      heq_fun_of hG _ _ fun g' g hgg => by rw [hchi g' g hgg]; exact hι _
    have he := heq_coe_eG hG hi (eq_of_heq hPg) z.R.eG R'.eG heG
    have hβ : R'.βW i = z.R.βW i := congrFun (eq_of_heq hβW) i
    have key := eqAtP_congr z.core i ha a3 (σ := σ) (σ' := σ) rfl hV' hV' (c := c₁) (c' := c₁) HEq.rfl hG hi (hO i i rfl) hβ
      (eq_of_heq hPg) he hX
    have hA := key.1 ((hA'))
    have hz := z.geo.equivAll i σ hg hV' ⟨c₁, hcu, (eqAt_iff z.core i z.R.toRealDat z.geo.κ (z.geo.O i) σ hV' c₁ z.alg_eq hχ).2 hA⟩
    have hB := (eqAt_iff z.core i z.R.toRealDat z.geo.κ (z.geo.O i) σ hV' _ z.alg_eq hχ).1 hz
    have key2 := eqAtP_congr z.core i ha a3 (σ := σ) (σ' := σ) rfl hV' hV' (c := z.core.cE ((i : ℕ) + 1) σ)
      (c' := z.core.cE ((i : ℕ) + 1) σ) HEq.rfl hG hi (hO i i rfl) hβ (eq_of_heq hPg) he hX
    exact (eqAt_iff _ i R'.toRealDat κ' (O' i) σ hV' _ halg' hχ').2 ((key2.mpr hB))

  · obtain rfl : i = i' := Fin.ext hii
    obtain ⟨a1, a2, a3⟩ := hκ i i rfl
    have ha : wtA (κ' i) = wtA (z.geo.κ i) := by
      have e1 := eq_of_heq a1
      have e2 := eq_of_heq a2
      unfold wtA
      rw [e1, e2]
      rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hιc⟩ := hI i i rfl
    obtain ⟨-, -, hchi, -⟩ := hιc (enlEmb hR) hι
    have hX : HEq (fun g => (w'.st Z').toD7.what₂.embLL (((R'.FW i).chi g : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL))
        (fun g => (w.st Z).toD7.what₂.embLL (((z.R.FW i).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) :=
      heq_fun_of hG _ _ fun g' g hgg => by rw [hchi g' g hgg]; exact hι _
    have he := heq_coe_eG hG hi (eq_of_heq hPg) z.R.eG R'.eG heG
    have hβ : R'.βW i = z.R.βW i := congrFun (eq_of_heq hβW) i
    have hB := (equivAt_iff z.core i (z.geo.κ i) z.R.toRealDat (z.geo.O i) _ hχ).1 hE
    have hσ : (O' i).s0 = (z.geo.O i).s0 := (sOv_eq _ _ _).trans (sOv_eq _ _ _).symm
    have key := equivP_congr z.core i ha a3 hσ (z.geo.O i).hV (O' i).hV (c := z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0)
      (c' := z.core.cE ((i : ℕ) + 1) (O' i).s0) (by rw [hσ]) hG hi (hO i i rfl) hβ (eq_of_heq hPg) he hX
    exact (equivAt_iff (D := (w'.st Z').toD7) _ i (κ' i) R'.toRealDat (O' i) _ hχ').2 ((key.mpr hB))

end GlobalTheory.Mem.R3.Rw.EqvMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCastMap
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

section Alg

theorem coef_agree {L K L' K' I W W' : Type} [Field L] [Field K] [Field L'] [Field K'] [Fintype I] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] {n : ℕ} (lam : I → DomWeight n) {σL : L →+* ℂ} {σK : K →+* ℂ} {σL' : L' →+* ℂ} {σK' : K' →+* ℂ}
    (jL : L →+* K) (jL' : L' →+* K') (inc : K →+* K') (h : σK.comp jL = σL) (h' : σK'.comp jL' = σL') (hi : σK'.comp inc = σK)
    (s : Function.Surjective jL) (s' : Function.Surjective jL')
    {cL : VV L lam →ₛₗ[σL] W} {cK : VV K lam →ₛₗ[σK] W} {cL' : VV L' lam →ₛₗ[σL'] W'} {cK' : VV K' lam →ₛₗ[σK'] W'}
    (hc : ∀ v : VV L lam, ∃ v' : VV K lam, (v' : Pol K I n) = MvPolynomial.map jL (v : Pol L I n) ∧ cK v' = cL v)
    (hc' : ∀ v : VV L' lam, ∃ v' : VV K' lam, (v' : Pol K' I n) = MvPolynomial.map jL' (v : Pol L' I n) ∧ cK' v' = cL' v)
    (ha : ∀ (v : VV L lam) (v' : VV L' lam), HEq (MvPolynomial.map σL' v'.1) (MvPolynomial.map σL v.1) → HEq (cL' v') (cL v))
    (v : VV K lam) (v' : VV K' lam) (e : (v' : Pol K' I n) = MvPolynomial.map inc (v : Pol K I n)) : HEq (cK' v') (cK v) := by
  have key : ∀ {L K : Type} [Field L] [Field K] (jL : L →+* K), Function.Surjective jL → ∀ v : VV K lam,
      ∃ u : VV L lam, (v : Pol K I n) = MvPolynomial.map jL (u : Pol L I n) := by
    intro L K _ _ jL s v
    let q := (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).symm
    refine ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV q.toRingHom lam _ v.2⟩, ?_⟩
    have : jL.comp q.toRingHom = RingHom.id K := RingHom.ext fun x => (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).apply_symm_apply x
    rw [MvPolynomial.map_map, this, MvPolynomial.map_id]
  obtain ⟨u, hu⟩ := key jL s v
  obtain ⟨u', hu'⟩ := key jL' s' v'
  obtain ⟨a, a1, a2⟩ := hc u
  obtain ⟨b, b1, b2⟩ := hc' u'
  obtain rfl : a = v := Subtype.ext (a1.trans hu.symm)
  obtain rfl : b = v' := Subtype.ext (b1.trans hu'.symm)
  rw [a2, b2]
  refine ha u u' (heq_of_eq ?_)
  rw [← h, ← h', ← MvPolynomial.map_map, ← MvPolynomial.map_map, ← hu, ← hu', e, MvPolynomial.map_map, hi]

theorem exists_cast_map {K V W W' : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* ℂ}
    (n : NormedAddCommGroup W) (p : InnerProductSpace ℂ W) (n' : NormedAddCommGroup W') (p' : InnerProductSpace ℂ W')
    (hW : HEq W' W) (hn : HEq n' n) (hp : HEq p' p) (c' : V →ₛₗ[σ] W') :
    ∃ c : V →ₛₗ[σ] W, HEq c' c ∧ ∀ v, HEq (c' v) (c v) := by
  cases hW; cases hn; cases hp
  exact ⟨c', HEq.rfl, fun _ => HEq.rfl⟩

end Alg

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Change

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (c₃ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hs : O.c'.F ≤ c₃.F)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (h : O.Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

abbrev bc : OMDat C R i Unit (fun _ => A.μ0) :=
  merge (tup := fun _ : Unit => A.μ0) (fun _ => O) c₃ (O.hle.trans hs) (fun _ => hs) ((incF O.c' c₃ hs).comp O.jL) O.hV c0₃ O.lev
    io₃ hw₃ (fun _ => 1) (fun _ => h) v₀

structure IsBC (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (J' : Subgroup (Bridge.Gf (Vc D i))) : Prop where
  c0 : ∀ (v : VsV D i O.c'.F) (v' : VsV D i c₃.F), (v' : Pol c₃.F D.what₂.Tau (Vc D i).rank) =
    MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F D.what₂.Tau (Vc D i).rank) → c0₃ v' = O.c0' v
  io : IoOver hs (lamV D i) O.io io₃
  reps : RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ())
  placeEx : PlaceEx R i A.μ0 h O.c0'
  thAd : ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ())
  plc : ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x
  pins : (bc O c₃ hs c0₃ io₃ hw₃ h v₀).Pins κ v₀ ι x₀


set_option maxHeartbeats 1600000 in
theorem exists_isBC (hV : R.models_HV) {κ ι x₀} (hO : O.Pins κ v₀ ι x₀)
    (hc0 : ∀ (v : VsV D i O.c'.F) (v' : VsV D i c₃.F), (v' : Pol c₃.F D.what₂.Tau (Vc D i).rank) =
      MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F D.what₂.Tau (Vc D i).rank) → c0₃ v' = O.c0' v) :
    ∃ io₃ hw₃ h J', IsBC O c₃ hs c0₃ io₃ hw₃ h v₀ κ ι x₀ J' := by
  obtain ⟨io₃, hw₃, hio, hover⟩ := GlobalTheory.IoExtend.exists_ioLFRec_over _ _ _ _ O.c' c₃ hs _ _ (tauE D) (lamV D i) (wtA κ) O.io O.hw hO.io
  obtain ⟨h, J', hr, hpl, hth, hplc⟩ := (hO.tuple ()).reps
  obtain ⟨a, ha, hca⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO.cxi
  refine ⟨io₃, hw₃, h, J', hc0, hover, hr, hpl, hth, hplc, ⟨?_, hO.lift.std, hO.lift.v0, ?_, hO.lift.lev⟩,
    fun j => ⟨?_, (hO.tuple ()).B, (hO.tuple ()).xi, (hO.tuple ()).phi, (hO.tuple ()).half⟩,
    ⟨hO.act.1, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O.hle.trans hs) _ _ hO.act.1).1⟩, fun j => hO.bad (), fun j => hO.reps (),
    fun j => ⟨fun k => congrArg (incF _ c₃ hs) ((hO.ep ()).1 k), epIs_map hs (hO.ep ()).2⟩, hio,
    fun j k q => phiHat_covBC hs _ 1 _ _ q (hO.w () k q),
    fun j => covPin_covBC hs _ one_ne_zero (hO.cov ()), ?_, fun j => hO.model₂ ()⟩
  · exact (RingHom.ext fun _ => rfl : _ = (inC O.c').comp O.jL).trans hO.lift.field
  · obtain ⟨g, r, c0L, hT, hc⟩ := hO.lift.c0
    refine ⟨g, r, c0L, hT, fun v => ?_⟩
    obtain ⟨v', hv', e⟩ := hc v
    exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV (incF O.c' c₃ hs) _ _ v'.2⟩, (congrArg (MvPolynomial.map (incF O.c' c₃ hs)) hv').trans (MvPolynomial.map_map _ _ _),
      (hc0 v' _ rfl).trans e⟩
  · refine ⟨h, J', repsR_map _ hr, fun x₀ => ?_, thAdIs_thAdOf R i A.μ0 h c0₃ hV hr.2.2.1 hr.2.2.2.2.2.1 v₀, fun _ => Iff.rfl⟩
    obtain ⟨x, hx⟩ := hpl x₀
    exact ⟨fun k => ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV (incF O.c' c₃ hs) _ _ (x k).2⟩, fun k => (hx k).trans (hc0 _ _ rfl).symm⟩
  · refine (cXiVal_iff _ _ _ _ _ _ _ _ _).2 ⟨a, ha, fun j => ?_⟩
    have key := GlobalTheory.OneMapAll.cXiAt_covBC D _ _ _ _ _ _ _ _ hs _ _ _ 1 _ _ _ _ _ _ (hO.cov ()).1.2.2.2.2.2.2.2.1 (hca ())
    exact (congrArg (GlobalTheory.OneMapAll.CXiAt _ _ _ _ _ _ _ _ _) (one_mul a)).mp key

end Change

section Tuple


open Classical in
variable (D) in
def TupOver (i : Fin D.R.m) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (βV : ∀ i, GL (Fin (Vc D i).rank) (Lev.EAf D))
    (βW : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)) (χ : Formalism.L2.Host.HChar D.host.E) (ξ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) {K' : Type} [Field K'] (σ' : K' →+* ℂ)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (bad : ℕ) (Mb I : Ideal (𝓞 D.host.E)) (N : Submodule (𝓞 D.host.E) La) {Cl : Type} (h : Cl → GA D (Vc D i))
    (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K')
    (B : Ideal (𝓞 D.host.E) → K') (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (φ : (Fin (Vc D i).rank → La ⧸ N) → K') : Prop :=
  (bad ≠ 0 ∧ (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    J' ≤ (levEnv (Vc D i) (βV i) (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ∧
    J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ≠ 0 ∧
    vol = ((J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J : ℕ) : K')⁻¹ ∧
    Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) ∧
    ∀ k, SplitOffBad (Vc D i) bad (h k) ∧ Lh k = Bridge.hLat (Vc D i) (fin _ (h k)) ∧
      gam k = Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin _ (h k)))) ∧
  (∀ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ → cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ →
    σ' (B cc) = ((χ.onId (cc : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)) ∧
  (∀ (g : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) g x →
    ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) = ((ξ x : Circle) : ℂ)) ∧
  (∃ e : AE D, IsIdemSum e (Pg ∪ Q) ∧ ∀ x : Fin (Vc D i).rank → La,
    IsIntM (uMat (Vc D i) (Wc D i) (βV i) (βW i) e fun b => ι (x b)) ∧
    σ' (φ fun b => Submodule.Quotient.mk (x b)) =
      omegaK Pg (fun PP => redM PP (uMat (Vc D i) (Wc D i) (βV i) (βW i) e fun b => ι (x b))) *
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (uMat (Vc D i) (Wc D i) (βV i) (βW i) e fun b => ι (x b)))) ∧
  (Mb = ∏ PP ∈ Pg, PP.asIdeal ∧ (∀ PP ∈ Q, I ≤ PP.asIdeal) ∧
    ∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)

variable {i : Fin D.R.m} {K' : Type} [Field K'] {σ' : K' →+* ℂ}
  {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {bad : ℕ} {Mb I : Ideal (𝓞 D.host.E)} {N : Submodule (𝓞 D.host.E) La} {Cl : Type} {h : Cl → GA D (Vc D i)}
  {J' : Subgroup (Bridge.Gf (Vc D i))} {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
  {B : Ideal (𝓞 D.host.E) → K'} {xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} {φ : (Fin (Vc D i).rank → La ⧸ N) → K'}


set_option maxHeartbeats 1000000 in
theorem tupOver_iff {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T0) :
    TupOver D i R.Pg (R.Q t) R.βV R.βW (R.C.mu0 i * R.xiH t * R.C.eta⁻¹) (R.xi t) (R.xiR t) σ' ι bad Mb I N h J' Lh gam vol B xi φ ↔
      RepsR R i t h bad J' Lh gam vol ∧ BIs R i σ' t bad B ∧ XiIs R i t xi ∧ PhiIs R i σ' t ι N φ ∧ HalfIs R t Mb I := Iff.rfl

theorem tupOver_cast {Pg₁ Pg₂ Q₁ Q₂ : Finset (Formalism.L2.DIV.Pl D.host.E)} {βV₁ βV₂ βW₁ βW₂ χ₁ χ₂ ξ₁ ξ₂ ξR₁ ξR₂}
    (hP : HEq Pg₂ Pg₁) (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅) (hV : HEq βV₂ βV₁) (hW : HEq βW₂ βW₁) (hχ : χ₂ = χ₁) (hξ : ξ₂ = ξ₁)
    (H : TupOver D i Pg₁ Q₁ βV₁ βW₁ χ₁ ξ₁ ξR₁ σ' ι bad Mb I N h J' Lh gam vol B xi φ) :
    TupOver D i Pg₂ Q₂ βV₂ βW₂ χ₂ ξ₂ ξR₂ σ' ι bad Mb I N h J' Lh gam vol B xi φ := by
  cases hP; cases hV; cases hW
  subst hQ₁ hQ₂ hχ hξ
  obtain ⟨h1, h2, h3, ⟨e, he, h4⟩, h5⟩ := H
  refine ⟨h1, h2, h3, ⟨e, he, fun x => ⟨(h4 x).1, (h4 x).2.trans ?_⟩⟩, h5⟩
  simp [omegaQ]

end Tuple

section Same

variable {D' : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0' T0' : Type} {A' : FamIn D'.what₂.LL G' Pl0' T0' D'.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  {C' : Core D'} [Algebra C'.Q.c.F D'.what₂.LL] {R' : RealDat D' A' C'.Q.c.F} {i' : Fin D'.R.m}

structure SameGeo (O' : OMDat C' R' i' Unit (fun _ => A'.μ0)) (M : OMDat C R i Unit (fun _ => A.μ0)) : Prop where
  c' : HEq O'.c' M.c'
  lev : HEq O'.lev M.lev
  dδ : HEq O'.dδ M.dδ
  Cl' : O'.Cl' = M.Cl'
  fCl : HEq O'.fCl M.fCl
  bad : O'.bad = M.bad
  Lh : HEq O'.Lh M.Lh
  La : HEq O'.La M.La
  Nc : HEq O'.Nc M.Nc
  gam : HEq O'.gam M.gam
  vol : HEq O'.vol M.vol
  ep : HEq O'.ep M.ep
  B : HEq O'.B M.B
  epF : HEq O'.epF M.epF
  io : HEq O'.io M.io
  hw : HEq O'.hw M.hw
  φ : HEq O'.φ M.φ
  w : HEq O'.w M.w
  U₂ : HEq O'.U₂ M.U₂
  dict₂ : HEq O'.dict₂ M.dict₂
  xi : HEq O'.xi M.xi

def IsBCOf (O' : OMDat C' R' i' Unit (fun _ => A'.μ0)) (v₀' : (R'.MW i' (sg0 D' A')).Vec) (O : OMDat C R i Unit (fun _ => A.μ0))
    (v₀ : (R.MW i (sg0 D A)).Vec) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (P : Prop) : Prop :=
  ∃ c₃ hs c0₃ io₃ hw₃ h J', IsBC O c₃ hs c0₃ io₃ hw₃ h v₀ κ ι x₀ J' ∧ SameGeo O' (bc O c₃ hs c0₃ io₃ hw₃ h v₀) ∧
    (HEq O'.c0' c0₃ ∨ P) ∧ ∃ (h' : O'.Cl' () → GA D' (Vc D' i')) (J'' : Subgroup (Bridge.Gf (Vc D' i'))), HEq h' h ∧ HEq J'' J' ∧
      RepsR R' i' A'.μ0 h' (O'.bad ()) J'' (O'.Lh ()) (O'.gam ()) (O'.vol ()) ∧ PlaceEx R' i' A'.μ0 h' O'.c0' ∧
      ThAdIs R' i' A'.μ0 h' O'.c0' v₀' (O'.thAd ()) ∧ ∀ x, O'.Plc () x ↔ ∃ x₀, Place R' i' A'.μ0 h' O'.c0' (jVx R' i' A'.μ0 x₀) x

theorem IsBCOf.lev {O' : OMDat C' R' i' Unit (fun _ => A'.μ0)} {v₀'} {O : OMDat C R i Unit (fun _ => A.μ0)} {v₀ κ ι x₀ P}
    (h : IsBCOf O' v₀' O v₀ κ ι x₀ P) : HEq O'.lev O.lev := by
  obtain ⟨_, _, _, _, _, _, _, -, hs, -⟩ := h
  exact hs.lev

end Same

theorem wtA_eq {j : ℕ} (κ κ' : WeightFamilies.Wt D j) (hP : κ'.aP = κ.aP) (hM : κ'.aM = κ.aM) : wtA κ' = wtA κ := by
  funext x
  simp only [wtA, hP, hM]

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReadingRationalAtTwistExtendsIntegralUnitarStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelReading_rationalAtTwist_extends_integralUnitary : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n : ℕ} [NeZero n] {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {J : Matrix (Fin n) (Fin n) E}, J = 1 →
    ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ),
    (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → (∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P') →
    (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F);
      ∀ᶠ (u : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) →
    RdLevOn hc (RatAt Q) S.U S.chi Λ emb Q HQ lamQ →
    RdLevOn hc Set.univ S.U S.chi Λ emb Q HQ lamQ := by
  first | exact @GlobalTheory.SeeSaw.TwLev.Approx.rd_all | exact GlobalTheory.SeeSaw.TwLev.Approx.rd_all | (intros; apply GlobalTheory.SeeSaw.TwLev.Approx.rd_all <;> assumption)
end

