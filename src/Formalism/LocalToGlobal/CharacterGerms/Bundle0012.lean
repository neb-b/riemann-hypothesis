module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0007
public import Formalism.LocalToGlobal.CharacterGerms.RowTieVal

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)

abbrev rd (o : Orb) : RowData C V d (I o) (JJ (I o)) := (Y.raw (p o)).rowData (H o)

def imgFam : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgO (fun o => Y.raw (p o)) (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

theorem valO_of (ν : ℝ) (hν : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x) (hs : PairsSep Y p) (hv : ValEqPSt Y p H Ls n) :
    ValO (fun o => rd Y p H o) n (imgFam Y p Ls n) ν := by
  intro Po hPo kind hk S t ht gr hg
  obtain ⟨P, hP, hQ⟩ := hPo
  obtain ⟨f, hf, he⟩ := hv hs P hP Po hQ kind hk S t ht gr hg
  have hx := hν _ ⟨P, hP, f, hf, rfl⟩
  rw [he, map_prod_add] at hx
  exact hx

theorem lower_of_nuPlE (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x := by
  intro x hx
  have h1 : (ν : EReal) ≤ (WithBot.some x : WithBot (WithTop ℝ)) := hν.trans (biInf_le _ hx)
  exact WithBot.coe_le_coe.1 h1

variable (F : ∀ o, Flag (rd Y p H o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

def BlockMembershipChart : Prop := BlockMembership (fun o => rd Y p H o) n F (imgFam Y p Ls n) Z ga

def BlockAdmissibleChart : Prop := BlockAdmissible (fun o => rd Y p H o) F Z ga

theorem valBlocks_of (ν : ℝ) (hν : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x) (hs : PairsSep Y p)
    (hv : ValEqPSt Y p H Ls n) (hJ : JetProdSt) (hM : BlockMembershipChart Y p H Ls n F Z ga) (hA : BlockAdmissibleChart Y p H F Z ga) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_G (valO_of Y p H Ls n ν hν hs hv) hJ F Z ga hM hA

theorem valBlocks_of_nuPlE (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : PairsSep Y p)
    (hv : ValEqPSt Y p H Ls n) (hJ : JetProdSt) (hM : BlockMembershipChart Y p H Ls n F Z ga) (hA : BlockAdmissibleChart Y p H F Z ga) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_of Y p H Ls n F Z ga ν (lower_of_nuPlE Y Ls n ν hν) hs hv hJ hM hA

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def VF.RR {C : Type} [Field C] (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

section Chart

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def a3B (C3 : IntChart T io y) : FB T.Fr (chD C3.ch) (𝓞 E) := letI := io.toAlgebra; C3.ch.B

def a3h (C3 : IntChart T io y) : PS T.Fr 2 (chD C3.ch) := letI := io.toAlgebra; C3.ch.h

def chartUnitVectors (C3 : IntChart T io y) : Lt1 Dw → Fin (chD C3.ch) → T.Fr := letI := io.toAlgebra; C3.ch.uvec

def EmbOK (T : CDVR) (V : VF C) (ι : T.Fr →+* C) : Prop :=
  ∀ x : T.Fr, x ≠ 0 → V.v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)

def eOf (T : CDVR) (V : VF C) : ℕ := (vV T.V ((V.l : ℕ) : T.Fr)).toNat

structure IsBC (C3 : IntChart T io y) (ι : T.Fr →+* C) (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)) : Prop where
  F : ∀ j, Y.B.G.F j = MvPowerSeries.map ι ((a3B C3).G.F j)
  act : ∀ a j, Y.B.A.act a j = MvPowerSeries.map ι ((a3B C3).A.act a j)
  ph1 : Y.B.ph1 = MvPowerSeries.map ι (a3B C3).ph1
  ph2 : Y.B.ph2 = MvPowerSeries.map ι (a3B C3).ph2
  sy : Y.B.sy = MvPowerSeries.map ι (a3B C3).sy
  ad : ∀ a, Y.B.ad a = MvPowerSeries.map ι ((a3B C3).ad a)
  h : Y.h = MvPowerSeries.map ι (a3h C3)
  w0 : Y.w0 = H.w0
  k : Y.k = k

def chartLetterSystem (C3 : IntChart T io y) (V : VF C) (ι : T.Fr →+* C) (a : (E →+* ℂ) × ℕ → ℕ) : LetSys C (chD C3.ch) where
  ι := fun N => LtN Dw N
  fin := fun _ => inferInstance
  cp := fun _ ℓ => ℓ.2.2
  uv := fun _ ℓ i => ι (chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩ i)
  FF := fun N => HaO Dw.mult N C V.RR ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)

end Chart

structure Lab (E : Type) [Field E] (Orb : Type) (d : ℕ) where
  tau : Orb → Fin 2 → ZMod d → (E →+* ℂ)
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Orb → Fin 2 → ZMod d → Prop

abbrev Lab.II {Orb : Type} {d : ℕ} (lab : Lab E Orb d) (Dw : Datum H) (o : Orb) (g : Fin 2) : Type :=
  Σ a : ZMod d, Fin (Dw.mult (lab.tau o g a))

section Pairs

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

def emA3 (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (τ : E →+* ℂ) : 𝓞 E →+* C := (ι.comp io).comp (embK c τ)

def lieBasisVector (C3 : IntChart T io y) (ι : T.Fr →+* C) (lab : Lab E Orb d) (o : Orb) (g : Fin 2) (x : lab.II Dw o g) :
    Fin (chD C3.ch) → C := fun i => ι (chartUnitVectors C3 ⟨lab.tau o g x.1, x.2⟩ i)

structure LabArith (V : VF C) (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (lab : Lab E Orb d) : Prop where
  inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2
  conj : ∀ o a, lab.tau o 1 a = ComplexEmbedding.conjugate (lab.tau o 0 a)
  frob : ∀ o g a x, V.MM (emA3 io ι (lab.tau o g (a + 1)) x - emA3 io ι (lab.tau o g a) x ^ V.l)
  sep : ∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' →
    ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2.1 x.2.2) a - emA3 io ι (lab.tau x'.1 x'.2.1 x'.2.2) a) = 0
  unr : ∀ o g, ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (lab.tau o g a) ε - 1)) ∧
    ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (lab.tau o g a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y

structure LabGeo (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) (lab : Lab E Orb d) :
    Prop where
  em_int : ∀ o g a x, V.Ge 0 (emA3 io ι (lab.tau o g a) x)
  em_conj : ∀ o a x, emA3 io ι (lab.tau o 1 a) x = emA3 io ι (lab.tau o 0 a) (star x)
  u_int : ∀ o g x i, V.Ge 0 (lieBasisVector C3 ι lab o g x i)
  u_eig : ∀ o g (x : lab.II Dw o g) a, linAct (Y.B.A.act a) (lieBasisVector C3 ι lab o g x) =
    emA3 io ι (lab.tau o g x.1) a • lieBasisVector C3 ι lab o g x
  u_sat : ∀ o g, ∃ w : Fin (chD C3.ch) → lab.II Dw o g → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o g, ∑ x, lieBasisVector C3 ι lab o g q x * w x q' = if q = q' then 1 else 0
  u_full : ∀ o g a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o g a) x • v) →
    ∃ b : lab.II Dw o g → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • lieBasisVector C3 ι lab o g q

def pairOfLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (o : Orb) : PairData Y d (lab.II Dw o) where
  em := fun g a => emA3 io ι (lab.tau o g a)
  em_int := hg.em_int o
  em_conj := hg.em_conj o
  em_frob := ha.frob o
  em_sep := fun p p' hp => ha.sep (o, p) (o, p') (fun h => hp (Prod.mk.inj h).2)
  em_unr := ha.unr o
  u := lieBasisVector C3 ι lab o
  ty := fun _ x => x.1
  u_int := hg.u_int o
  u_eig := hg.u_eig o
  u_sat := fun g => by
    obtain ⟨w, h1, h2⟩ := hg.u_sat o g
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  u_full := hg.u_full o
  n := lab.n
  j := lab.j
  j' := lab.j'
  big := lab.big o

theorem pairsSep_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) : PairsSep Y (pairOfLab ha hg) :=
  fun x x' h => ha.sep x x' h

end Pairs

section Named

variable (Xo c)

def BCExSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → IsAlgClosed C →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → V.l ≠ 2 →
    H.w0 + star H.w0 = 1 → ∀ k : ℕ, V.v (k : C) = 0 → ∃ Y : FBChart C V (𝓞 E) (chD C3.ch), IsBC C3 ι k Y

def HostTraceIdentity (H : Host E) : Prop := (∀ a : 𝓞 E, star a = H.bar a) → H.w0 + star H.w0 = 1

def DescentSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C3 (eOf T V) k a n ≤ Y.nuPlE (chartLetterSystem C3 V ι a) n

def LabGeoSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → LabGeo C3 ι Y lab

end Named

def Lab.RankOK {Orb : Type} {d : ℕ} (lab : Lab E Orb d) (Dw : Datum H) : Prop :=
  ∀ o, (∀ g a, lab.big o (1 - g) a ↔ ¬ lab.big o g a) ∧
    (∀ g a, lab.big o g a → Dw.mult (lab.tau o g a) = lab.n + lab.j) ∧
    (∀ g a, ¬ lab.big o g a → Dw.mult (lab.tau o g a) = lab.j')

section Top

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb] {d : ℕ} [NeZero d]

end Top

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

structure SelfData {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (d : ℕ) (I0 : Type) [Fintype I0] where

  em : ZMod d → (O →+* C)
  em_int : ∀ a x, V.Ge 0 (em a x)
  em_frob : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)
  em_sep : ∀ a a' : ZMod d, a ≠ a' → ∃ x, V.v (em a x - em a' x) = 0

  em_unr : ∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧
    ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y

  hd : ZMod d
  hd_ne : hd ≠ 0
  hd_two : hd + hd = 0
  em_conj : ∀ a x, em a (star x) = em (a + hd) x

  e : I0 → Fin dd → C
  ty0 : I0 → ZMod d
  e_int : ∀ c i, V.Ge 0 (e c i)
  e_eig : ∀ c x, linAct (Y.B.A.act x) (e c) = em (ty0 c) x • e c
  e_sat : ∃ w : Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
    ∀ c c' : I0, ∑ x, e c x * w x c' = if c = c' then 1 else 0
  e_full : ∀ a (v : Fin dd → C), (∀ x, linAct (Y.B.A.act x) v = em a x • v) →
    ∃ b : I0 → C, (∀ c, ty0 c ≠ a → b c = 0) ∧ v = ∑ c, b c • e c

  gm : ZMod d → Matrix (Fin 2) (Fin 2) C
  gm_lim : ∀ N : ℕ, ∃ M : Matrix (Fin 2) (Fin 2) O, ∀ a r s, V.Ge N (gm a r s - em a (M r s))

  gm_hyp : ∀ a (s s' : Fin 2), ∑ r, gm (a + hd) r s * gm a r s' = if s = s' then 0 else 1
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Fin 2 → ZMod d → Prop

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def inCol (col : Fin 2) (f : MvPowerSeries (Fin dd) C) : MvPowerSeries (Fin 2 × Fin dd) C :=
  MvPowerSeries.subst
    (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) f

def hCol (col : Fin 2) (h : PS C 2 dd) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C :=
  MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
    (MvPowerSeries.X (p.1, (col, p.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) h

def FBChart.rawSelf (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    RawChart C d (fun _ => I0) (Fin 2 × Fin dd) where
  lg := fun x => inCol x.1 (un1 (Y.lg x.2))
  ex := fun x => inCol x.1 (un1 (Y.ex x.2))
  h := ∑ col, hCol col Y.h
  k := Y.k
  u := fun g c x => p.gm (p.ty0 c) x.1 g * p.e c x.2
  ty := fun g c => if g = 0 then p.ty0 c else p.ty0 c + p.hd
  n := p.n
  j := p.j
  j' := p.j'
  big := p.big

def AllSelf (Φ : ∀ (C : Type) [Field C] (_V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin 2 × Fin dd) → Prop) : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0),
    Φ C V d (fun _ => I0) dd (Y.rawSelf p)

def CartSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => ∀ g, X.CartHyp V g

def AxesSelfSt : Prop := AllSelf fun _ _ _ _ _ _ _ X => X.AxesSt

def GermZeroSelfConjugate : Prop := AllSelf fun _ _ V _ _ _ _ X => ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H

def CEqSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.CEqSt H

def IndependenceBoundSelfConjugate : Prop :=
  AllSelf fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H

section Val

variable {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

def IsImgS (X : ∀ o, RawChart C d (fun _ => I0 o) (Fin 2 × Fin dd)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) {ι : Type}
    (cp : ι → Fin n) (uv : ι → Fin dd → C) (P : MvPolynomial ι C)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => I0 o) C) : Prop :=
  ∃ co : ι → Fin N × (WVO fun o (_ : Fin 2) => I0 o) → C,
    (∀ ℓ ∈ P.vars, ∃ ρ col, pl (ρ, col) = cp ℓ ∧ (∀ ρ' w, ρ' ≠ ρ → co ℓ (ρ', w) = 0) ∧
      (fun x : Fin 2 × Fin dd => if x.1 = col then uv ℓ x.2 else 0) =
        ∑ w : (WVO fun o (_ : Fin 2) => I0 o), co ℓ (ρ, w) • (X w.1).u w.2.1 w.2.2) ∧
    Q = MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (co ℓ x) * MvPolynomial.X x) P

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

def SelfSep : Prop :=
  ∀ x x' : Orb × ZMod d, x ≠ x' → ∃ a : O, V.v ((p x.1).em x.2 a - (p x'.1).em x'.2 a) = 0

def ValEqSelfSt : Prop :=
  SelfSep Y p → ∀ (N : ℕ) (pl : Fin N × Fin 2 ↪ Fin n), ∀ P ∈ Ls.FF n,
    ∀ Po : ∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C,
    IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o)) →
    ∀ kind : Orb → Fin N → Option (Fin 2 × ZMod d × ZMod d),
    (∀ o, RowsOK ((Y.rawSelf (p o)).rowData (H o)).G ((Y.rawSelf (p o)).rowData (H o)).Alt (Po o) (kind o)) →
    ∀ (S : ∀ o g, Sys (((Y.rawSelf (p o)).rowData (H o)).G g)) (t : ∀ o (_ : Fin 2), I0 o → MvPowerSeries (I0 o) C),
    (∀ o g, (S o g).IsT (t o g)) →
    ∀ gr : ∀ o, Fin N → MvPowerSeries (WV fun _ => I0 o) C, (∀ o ρ, gr o ρ ∈ IntGerm V (t o)) →
      ∃ f : PS C n dd, IntS V f ∧
        Y.nab Ls n f P = ∏ o, ValOf ((Y.rawSelf (p o)).rowData (H o)).hL (Po o) (kind o) (gr o)

theorem val_self (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n) (N : ℕ) (pl : Fin N × Fin 2 ↪ Fin n)
    (P : MvPolynomial (Ls.ι n) C) (hP : P ∈ Ls.FF n) (Po : ∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C)
    (hQ : IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o)))
    (kind : Orb → Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (hk : ∀ o, RowsOK ((Y.rawSelf (p o)).rowData (H o)).G ((Y.rawSelf (p o)).rowData (H o)).Alt (Po o) (kind o))
    (S : ∀ o g, Sys (((Y.rawSelf (p o)).rowData (H o)).G g)) (t : ∀ o (_ : Fin 2), I0 o → MvPowerSeries (I0 o) C)
    (ht : ∀ o g, (S o g).IsT (t o g))
    (gr : ∀ o, Fin N → MvPowerSeries (WV fun _ => I0 o) C) (hg : ∀ o ρ, gr o ρ ∈ IntGerm V (t o)) :
    Y.nuPlE Ls n ≤ (WithBot.some
      (∑ o, V.v (ValOf ((Y.rawSelf (p o)).rowData (H o)).hL (Po o) (kind o) (gr o))) : WithBot (WithTop ℝ)) := by
  obtain ⟨f, hf, e⟩ := hv hs N pl P hP Po hQ kind hk S t ht gr hg
  have h1 : V.v (Y.nab Ls n f P) =
      ∑ o, V.v (ValOf ((Y.rawSelf (p o)).rowData (H o)).hL (Po o) (kind o) (gr o)) := by
    rw [e]
    exact map_prod_add V Finset.univ _
  rw [← h1]
  exact iInf₂_le (f := fun x (_ : x ∈ Y.valSet Ls n) => (WithBot.some x : WithBot (WithTop ℝ)))
    (V.v (Y.nab Ls n f P)) ⟨P, hP, f, hf, rfl⟩

end Val

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieValCut
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

def rowOf {n : ℕ} (b : Fin n) (F : MvPowerSeries (WVO I) C) : MvPowerSeries (Fin n × WVO I) C :=
  MvPowerSeries.subst (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C)) F

def toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) F

end Defs

def LeafSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (H : X.Hyps V) (n : ℕ) (Po : MvPolynomial (Fin n × WV I) C)
    (kind : Fin n → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt Po kind →
    ∀ gr : Fin n → MvPowerSeries (WV I) C,
      jetAt0 Po (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) = ValOf (X.rowData H).hL Po kind gr

end Formalism.L2.FormalSeriesBounds
end
end

