module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Formalism.LocalToGlobal.Columns.Bundle0005
public import Formalism.LocalToGlobal.Columns.GoodXgE
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
section
noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

structure ColLay (D : D7) (lev : LevelData D) (eX : ErrX D) : Prop where
  piG_lev : PiGLevel D lev eX
  piT_lev : PiTLevel D lev eX
  seen : SeenDef D eX
  tauOf : TauOfDef D eX
  one : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamChoice_at D
  atT : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧
    (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
    ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x)

def GatNum (s : Scale) (D : D7) : Prop :=
  ∀ u w hg, (D.gat u w hg).P.r = (if (D.what₂.places.resChar w : ℝ) < s.p0 D.R.k then G.rG s else 1) ∧
    (D.gat u w hg).e = ⌈(1 : ℝ) * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) s.a⌉₊

structure GyLay (K : Ctx) (D : D7) (Gt : GatTies D) (cmp : LatCmp D) (Gy : G.LatInst D) : Prop where
  vram : cmp.VramDef Gy
  fills : FillsAll Gt Gy
  led : ∀ L : SizeData₂ D, L.sc = K.s → WtEq L K.a K.b → Val K.C K.cD K.ch L → ∀ X : G.Inst D L, CanonInst X → G.EpDef X K.C.cX.Ce →
    G.KapIDef X K.C.GK → (∀ w, G.ParametersFill X K.C.GK w) → G.LatTied Gt X Gy

def ExportAt (D : D7) (nch : NChoice D) (xd : ThData D) : Prop :=
  ∃ (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)),
    (∀ i, D.ntw.NonzeroIndexPlace i → GlobalTheory.TwAll.goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.pin (BlochKatoReduction.bk0 D)) (twEOf xd) N0 i) ∧
    ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (nch.twI w) ∧ TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (nch.twI w)

section Lemmas

variable {D : D7}


end Lemmas

structure Core (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) : Type 1 where
  isOver : K.Over X.B.toPre
  xi : X.C.Tup → HChar X.B.host.E
  mu : MuIs X f T xi
  forced : ∀ p : ℕ, p.Prime → ((∃ i, p = X.B.host.g i) ∨ p = X.B.host.d ∨ (p : ℝ) ≤ K.s.X'' X.B.R.n) → p ∈ T.pl
  O : Obj2 X.toD7
  col : ColLay X.toD7 O.lev O.errX
  gatNum : GatNum K.s X.toD7
  gy : GyLay K X.toD7 O.gatT O.cmp O.Gy
  r : RowT X.toD7 (Fr.at X f) xi
  p0_eq : O.p0 = r.p0
  X_eq : O.X = r.X
  amb_eq : O.amb = r.amb
  ambientBase_heq : HEq O.amb0 r.amb0
  mtStable : DQ.MtStableAt X.toD7
  th_io : O.th.TieIo
  gauge_def : letI := X.toD7.host.cmStar; O.gauge.IsGauge
  real : Formalism.L2.Theta.RealTied X.toD7
  dsig_eq : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)
  del : X.S.s.Del = (Delv K.s K.cD : ℚ)
  etaF : X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  chiT : ∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
    ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))
  nch_tie : NChTie X.toD7 O.nch
  nch_Q : ∀ w, X.B.places.resChar w ∈ T.pl → O.nch.Q w = T.Q w ∧ O.nch.k' w = T.k w

end GlobalTheory.Mem.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
section
noncomputable section

namespace GlobalTheory.Mem.HD

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld NumberField IsDedekindDomain

def LevEx (D : D7) : Prop :=
  ∀ p, p ∈ D.host.levelPrimes ↔
    (∃ i, p = D.host.g i) ∨ p = D.host.pde ∨ p = D.host.pde' ∨ (∃ u, p = (D.mem u).A.T) ∨ p = q0Av D

def ExFld (B : Pre) (f : Fr B) (δ : FieldDat B) (F : IntermediateField ℚ ℂ) : Prop := F = listField δ f

def qb (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) : Fld := M.comap ι.toRatAlgHom

theorem mem_qb {ι : Qb →+* ℂ} {M : IntermediateField ℚ ℂ} {x : Qb} : x ∈ qb ι M ↔ ι x ∈ M := Iff.rfl

abbrev KC (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {GlobalTheory.Published.sqrtNegNat d}

structure HostPins (D : D7) (nch : NChoice D) : Prop where
  Tu_g : ∀ u i, (D.mem u).A.T ≠ D.host.g i
  fin : {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite
  Qw_Tu : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ nch.Q w, ∀ u, ¬ OverP D.host (D.mem u).A.T v
  gal : IsGalois ℚ D.what₂.LL
  hilb : ∃ M : IntermediateField ℚ ℂ, IsRayFieldIn D.host.φ₀ ⊤ M ∧
    ∀ z ∈ M, IsIntegral ℤ z → ∃ y : D.what₂.O, D.what₂.embLL (D.what₂.OtoLL y) = z

structure TupPins {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) : Prop where
  ram : ∀ μ v, ¬ (Tp.xi μ).UnrAt v → IsSplitPl D.host v ∧ (Ideal.absNorm v.asIdeal).Prime ∧
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ^ 2 ∧ ∀ k, ¬ OverP D.host (D.host.g k) v
  atl : ∀ w v, OverP D.host (D.what₂.places.resChar w) v → (Tp.xi (D.what₂.muAt w)).UnrAt v

end GlobalTheory.Mem.HD

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

theorem isAbsIrrChar_comp {K G H : Type} [Field K] [Group G] [Group H] (e : G ≃* H) {χ : H → K} (h : IsAbsIrrChar χ) :
    IsAbsIrrChar fun g => χ (e g) := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  refine ⟨n, ρ.comp e.toMonoidHom, ?_, fun t => hχ (e t)⟩
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun q => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective
      (congrArg (Subrepresentation.toSubmodule (ρ := ρ.comp e.toMonoidHom)) q :))
  · let S' : Subrepresentation ρ := ⟨S.toSubmodule, fun g v hv => by
      obtain ⟨x, rfl⟩ := e.surjective g
      exact S.apply_mem_toSubmodule x hv⟩
    rcases hρ.eq_bot_or_eq_top S' with q | q
    · exact Or.inl (Subrepresentation.toSubmodule_injective (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) q :))
    · exact Or.inr (Subrepresentation.toSubmodule_injective (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) q :))

theorem isAbsIrrChar_comp_iff {K G H : Type} [Field K] [Group G] [Group H] (e : G ≃* H) {χ : H → K} :
    (IsAbsIrrChar fun g => χ (e g)) ↔ IsAbsIrrChar χ :=
  ⟨fun h => by simpa using isAbsIrrChar_comp e.symm h, isAbsIrrChar_comp e⟩

section Base

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px)

abbrev Gc (B : Base) (px : PreX B.toPre) : Type := Formalism.L2.Col.G0 B.fields.E (B.primes px).vGs B.R.r

abbrev PlS (B : Base) (px : PreX B.toPre) : Type := letI := B.fields.starE; Formalism.L2.Col.LevOff (E := B.fields.E) ∅ (B.primes px).vGs ∅

abbrev PlI (B : Base) (px : PreX B.toPre) : Type := letI := B.fields.starE; Formalism.L2.Col.LevOffI (E := B.fields.E) ∅ (B.primes px).vGs ∅


open Classical in
def tuOf (U : Set I.ι) : Finset (Tup B.fields.F B.fields.E B.fields.K I.S) :=
  (Finset.univ.filter fun a => a ∈ U).image I.tup

abbrev TupU (U : Set I.ι) : Type := TupF (X := B.fields) (tuOf I U)


open Classical in
def ixOf (U : Set I.ι) (t : TupU I U) : I.ι := if h : ∃ a, I.tup a = t.1 then h.choose else I.mu0


open Classical in
def xiValOf (τ : Tup B.fields.F B.fields.E B.fields.K I.S) (P : HeightOneSpectrum (𝓞 B.fields.E)) : B.LLˣ :=
  if h : ∃ z : B.LLˣ, ∃ a, I.tup a = τ ∧ B.embLL (z : B.LL) = (((I.xi a).val P : ℂˣ) : ℂ) then h.choose else 1

abbrev TrI (B : Base) (px : PreX B.toPre) : Type :=
  Fin B.R.m → (PlI B px × List ℕ → B.LL) → PlI B px × List ℕ → B.LL

def famC (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL)) (tr : TrI B px) :
    FamIn3 B.LL (Gc B px) (PlS B px) (PlI B px) (List ℕ) (TupU I U) B.R.m :=
  colIn3 (X := B.fields) (Pr := B.primes px) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr


open Classical in
def psiC : ∀ PP : Pl B.host.E, AddChar (kP PP) B.LL :=
  fun PP => if h : PP ∈ (B.primes px).vGs then I.Ch.psi0 ⟨PP, h⟩ else 1

def lev0 : Subgroup (Gc B px) := (P0 (B.primes px).vGs B.R.r (psiC I)).H

def chr0 : lev0 I →* B.LLˣ := (P0 (B.primes px).vGs B.R.r (psiC I)).chi

def lev1 : Subgroup (Gc B px) := (Formalism.L2.Col.rPsymF (R := B.R) I.Ch).grp

def chr1 : lev1 I →* B.LLˣ := (Formalism.L2.Col.rPsymF (R := B.R) I.Ch).chr

def usedOf (T : Top.TwDat B) (Wt : Set B.places.Pl) : Set I.ι := {a | ∃ w ∈ Wt, I.xi a = T.xiTw I.C w}

def SelHalf : Prop :=
  ∀ a b : I.ι, ∀ P ∈ I.Q a, ∀ P' ∈ I.Q b, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 B.host.E) ∈ P.asIdeal ∧ (p : 𝓞 B.host.E) ∈ P'.asIdeal) →
    P.asIdeal.comap (algebraMap (𝓞 B.host.K) (𝓞 B.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 B.host.K) (𝓞 B.host.E))

def ValsIn : Prop :=
  (∀ a P, (I.xi a).UnrAt P → ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) ∧
    ∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (kP P))

theorem mem_tuOf {U : Set I.ι} {τ : Tup B.fields.F B.fields.E B.fields.K I.S} : τ ∈ tuOf I U ↔ ∃ a ∈ U, I.tup a = τ := by
  unfold tuOf
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem tup_mem_tuOf {U : Set I.ι} {a : I.ι} : I.tup a ∈ tuOf I U ↔ a ∈ U :=
  (mem_tuOf I).trans ⟨fun ⟨_, hb, e⟩ => I.tup_inj e ▸ hb, fun h => ⟨a, h, rfl⟩⟩

theorem ixOf_eq {U : Set I.ι} {t : TupU I U} {a : I.ι} (h : I.tup a = t.1) : ixOf I U t = a := by
  have h' : ∃ a, I.tup a = t.1 := ⟨a, h⟩
  unfold ixOf
  rw [dite_eq_left h']
  exact I.tup_inj (h'.choose_spec.trans h.symm)

theorem tup_ixOf {U : Set I.ι} (t : TupU I U) : I.tup (ixOf I U t) = t.1 := by
  have h : ∃ a, I.tup a = t.1 := by
    rcases t.2 with h | h
    · exact ⟨I.mu0, I.trueColumn_tuple_trivial_eq_one.trans h.symm⟩
    · obtain ⟨a, -, e⟩ := (mem_tuOf I).1 h
      exact ⟨a, e⟩
  obtain ⟨a, ha⟩ := h
  rw [ixOf_eq I ha, ha]

theorem ixOf_mu0F (U : Set I.ι) : ixOf I U (mu0F (X := B.fields) (tuOf I U)) = I.mu0 := ixOf_eq I I.trueColumn_tuple_trivial_eq_one

theorem ixOf_injective (U : Set I.ι) : Function.Injective (ixOf I U) := fun t t' h =>
  Subtype.ext ((tup_ixOf I t).symm.trans ((congrArg I.tup h).trans (tup_ixOf I t')))

theorem mem_range_ixOf {U : Set I.ι} {a : I.ι} : a ∈ Set.range (ixOf I U) ↔ a = I.mu0 ∨ a ∈ U := by
  constructor
  · rintro ⟨t, rfl⟩
    rcases t.2 with h | h
    · exact Or.inl (ixOf_eq I (I.trueColumn_tuple_trivial_eq_one.trans h.symm))
    · exact Or.inr ((tup_mem_tuOf I).1 (by rw [tup_ixOf]; exact h))
  · rintro (rfl | h)
    · exact ⟨_, ixOf_mu0F I U⟩
    · exact ⟨⟨I.tup a, Or.inr ((tup_mem_tuOf I).2 h)⟩, ixOf_eq I rfl⟩

theorem usedOf_mono (T : Top.TwDat B) {Wt Wt' : Set B.places.Pl} (h : Wt ⊆ Wt') : usedOf I T Wt ⊆ usedOf I T Wt' :=
  fun _ ⟨w, hw, e⟩ => ⟨w, h hw, e⟩

section Fields

variable (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL)) (tr : TrI B px)

end Fields

theorem embLL_xiValOf (a : I.ι) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (h : ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) :
    B.embLL (xiValOf I (I.tup a) P : B.LL) = (((I.xi a).val P : ℂˣ) : ℂ) := by
  obtain ⟨z, hz⟩ := h
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact Units.ne_zero _ (hz.symm.trans (map_zero _))
  have h' : ∃ z : B.LLˣ, ∃ b, I.tup b = I.tup a ∧ B.embLL (z : B.LL) = (((I.xi b).val P : ℂˣ) : ℂ) :=
    ⟨Units.mk0 z hz0, a, rfl, hz⟩
  unfold xiValOf
  rw [dite_eq_left h']
  obtain ⟨b, hb, e⟩ := h'.choose_spec
  rw [e, I.tup_inj hb]

theorem psiC_of_mem {PP : Pl B.host.E} (h : PP ∈ (B.primes px).vGs) : psiC I PP = I.Ch.psi0 ⟨PP, h⟩ := by
  unfold psiC
  rw [dite_eq_left h]

theorem ValsIn.embLL_xiValOf {I : ColIn B px} (h : ValsIn I) (a : I.ι) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hP : (I.xi a).UnrAt P) : B.embLL (xiValOf I (I.tup a) P : B.LL) = (((I.xi a).val P : ℂˣ) : ℂ) :=
  GlobalTheory.Mem.R3.embLL_xiValOf I a P (h.1 a P hP)

end Base

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px)

abbrev famR (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) :
    FamIn3 X.toD7.what₂.LL (Gc X.B px) (PlS X.B px) (PlI X.B px) (List ℕ) (TupU I U) X.toD7.R.m :=
  famC I hX U Xg tr

structure LevOf (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) : Prop where

  is : L.Is (mu0F (X := X.B.fields) (tuOf I U))

  C : L.C = Top.Fr.at X I.C

  xiH : ∀ t, L.xiH t = I.xi (ixOf I U t)

  Pg : L.Pg = (X.B.primes px).vGs

  Q : ∀ t, L.Q t = I.Q (ixOf I U t)

  beta : (∀ i, L.βV i = 1) ∧ L.βX = 1

def IsPlacewiseIdentity {Pg : Finset (Pl X.toD7.host.E)} (eG : Gc X.B px ≃* G0 Pg X.toD7.R.r) : Prop :=
  ∀ (g : Gc X.B px) (P : Pl X.toD7.host.E) (h : P ∈ (X.B.primes px).vGs) (h' : P ∈ Pg), eG g ⟨P, h'⟩ = g ⟨P, h⟩

def GoodSet (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)) : Prop :=
  letI : Fintype (G0g X.toD7.nd) := Fintype.ofEquiv _ eR.toEquiv
  (∀ χ : Gc X.B px → X.B.LL, χ ∈ Xg ↔ (fun g => χ (eR.symm g)) ∈ Formalism.L2.Col.XgE X.B.embLL X.toD7.ntypes.e0) ∧
    ∀ g, X.B.embLL ((idemOf Xg).coeff g) = X.toD7.ntypes.e0.coeff (eR g)

theorem goodSet_iff (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)) :
    GoodSet X (px := px) eR Xg ↔
      (∀ χ : Gc X.B px → X.B.LL, χ ∈ Xg ↔ IsAbsIrrChar χ ∧
        ∑ g : Gc X.B px, X.toD7.ntypes.e0.coeff (eR g) * X.B.embLL (χ g) = X.B.embLL (χ 1)) ∧
      ∀ g, X.B.embLL ((idemOf Xg).coeff g) = X.toD7.ntypes.e0.coeff (eR g) := by
  let _ : Fintype (G0g X.toD7.nd) := Fintype.ofEquiv _ eR.toEquiv
  refine and_congr_left' (forall_congr' fun χ => iff_congr Iff.rfl ?_)
  rw [Formalism.L2.Col.mem_XgE, ← Equiv.sum_comp eR.toEquiv, isAbsIrrChar_comp_iff eR.symm]
  simp

theorem GoodSet.irr {eR : Gc X.B px ≃* G0g X.toD7.nd} {Xg : Finset (Gc X.B px → X.B.LL)}
    (h : GoodSet X (px := px) eR Xg) : ∀ χ ∈ Xg, IsAbsIrrChar χ :=
  fun χ hχ => ((((goodSet_iff X eR Xg).1 h).1 χ).1 hχ).1

structure GrpAt : Prop where

  pl : ∃ plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ (X.B.primes px).vGs,
    ∀ kv, ((plg kv).1 : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2 ∧ I.C.P.Div kv.1 (plg kv).1

  idem : IsIdempotentElem X.toD7.ntypes.e0

  cen : X.toD7.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g X.toD7.nd))

end Record

end GlobalTheory.Mem.R3

end
end

