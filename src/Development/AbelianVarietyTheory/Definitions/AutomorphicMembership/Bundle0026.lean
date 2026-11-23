module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.Divisibility.Bundle0006
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowLower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStagesClauses
section
noncomputable section

namespace GlobalTheory.Mem.Top.V4.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem mem_iff {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) (w : X.B.places.Pl) : w ∈ Wt ↔ X.W.muAt w ≠ X.C.mu0 := by
  refine ⟨fun hw he => ?_, fun hw => by_contra fun hn => hw (h.off w hn)⟩
  have h1 := h.tw w
  rw [← h.on w hw, he, h.mu0] at h1
  exact (TwFin.tw_fin X.B f T).2.1 w h1.symm

variable (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM)






end GlobalTheory.Mem.Top.V4.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InclUInjective
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}

def plB (X : Stages) : X.B.places.Pl ≃ HeightOneSpectrum (𝓞 X.toD7.what₂.LL) := X.toD7.plEq

theorem plB_conj (w : X.B.places.Pl) : plB X (X.B.places.conj w) = Formalism.DivisionValues.conjPl (plB X w) := by
  have hc := plConjEq X.toD7
  exact hc w

def ConjStable (X : Stages) (Wt : Set X.B.places.Pl) : Prop := ∀ w ∈ Wt, X.B.places.conj w ∈ Wt

theorem ConjStable.symm_mem_iff {Wt : Set X.B.places.Pl} (h : ConjStable X Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    (plB X).symm (Formalism.DivisionValues.conjPl v) ∈ Wt ↔ (plB X).symm v ∈ Wt := by
  constructor
  · intro hv
    have e : X.B.places.conj ((plB X).symm (Formalism.DivisionValues.conjPl v)) = (plB X).symm v := by
      apply (plB X).injective
      rw [plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    rw [← e]
    exact h _ hv
  · intro hv
    have e : X.B.places.conj ((plB X).symm v) = (plB X).symm (Formalism.DivisionValues.conjPl v) := by
      apply (plB X).injective
      rw [plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [← e]
    exact h _ hv

theorem tuOf_mono (I : ColIn X.B px) {U U' : Set I.ι} (h : U' ⊆ U) : tuOf I U' ⊆ tuOf I U := by
  intro τ hτ
  obtain ⟨a, ha, rfl⟩ := (mem_tuOf I).1 hτ
  exact (mem_tuOf I).2 ⟨a, h ha, rfl⟩

def inclU (I : ColIn X.B px) {U U' : Set I.ι} (h : U' ⊆ U) : TupU I U' → TupU I U := TupF.incl (tuOf_mono I h)

theorem inclU_injective {U U' : Set I.ι} (h : U' ⊆ U) : Function.Injective (inclU I h) := by
  intro s t hst
  have hv : (inclU I h s).1 = (inclU I h t).1 := congrArg Subtype.val hst
  exact Subtype.ext hv

theorem ixOf_inclU {U U' : Set I.ι} (h : U' ⊆ U) (t : TupU I U') : ixOf I U (inclU I h t) = ixOf I U' t := rfl

variable {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

theorem plB_mem_twPl (w : X.B.places.Pl) : plB X w ∈ z.R.twPl ↔ w ∈ Wt := by
  exact (z.mu w).1

theorem xi_mu {w : X.B.places.Pl} (hw : w ∈ Wt) : I.xi (ixOf I (usedOf I T Wt) (z.R.mu (plB X w))) = T.xiTw I.C w := by
  have hm := (z.mu w).2
  rw [if_pos hw] at hm
  exact hm

theorem mu_mem (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∈ Wt') :
    (z.R.mu v).1 ∈ tuOf I (usedOf I T Wt') := by
  have hx := z.xi_mu (h hv)
  rw [Equiv.apply_symm_apply] at hx
  have hu : ixOf I (usedOf I T Wt) (z.R.mu v) ∈ usedOf I T Wt' := ⟨(plB X).symm v, hv, hx⟩
  have hm := (tup_mem_tuOf I).2 hu
  rwa [tup_ixOf] at hm


open Classical in
def resMu (h : Wt' ⊆ Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : TupU I (usedOf I T Wt') :=
  if hv : (plB X).symm v ∈ Wt' then ⟨(z.R.mu v).1, Or.inr (z.mu_mem h hv)⟩ else mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))


open Classical in
def resTw (Wt' : Set X.B.places.Pl) : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :=
  z.R.twPl.filter fun v => (plB X).symm v ∈ Wt'

theorem mem_twPl (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : v ∈ z.R.twPl ↔ (plB X).symm v ∈ Wt := by
  have hm := z.plB_mem_twPl ((plB X).symm v)
  rwa [Equiv.apply_symm_apply] at hm

theorem mem_resTw (h : Wt' ⊆ Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : v ∈ z.resTw Wt' ↔ (plB X).symm v ∈ Wt' := by
  classical
  unfold resTw
  rw [Finset.mem_filter, z.mem_twPl]
  exact ⟨fun hv => hv.2, fun hv => ⟨h hv, hv⟩⟩

theorem inclU_resMu (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∈ Wt') :
    inclU I (usedOf_mono I T h) (z.resMu h v) = z.R.mu v := by
  have e : z.resMu h v = ⟨(z.R.mu v).1, Or.inr (z.mu_mem h hv)⟩ := dif_pos hv
  rw [e]
  rfl

theorem resMu_off (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∉ Wt') :
    z.resMu h v = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt')) := by
  exact dif_neg hv

theorem resMu_used (h : Wt' ⊆ Wt) (t : TupU I (usedOf I T Wt')) :
    t = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt')) ∨ ∃ v, z.resMu h v = t := by
  obtain ⟨τ, hτ | hτ⟩ := t
  · left
    exact Subtype.ext hτ
  · right
    obtain ⟨a, ha, rfl⟩ := (mem_tuOf I).1 hτ
    obtain ⟨w, hw, hxa⟩ := ha
    refine ⟨plB X w, ?_⟩
    have hw' : (plB X).symm (plB X w) ∈ Wt' := by
      rw [Equiv.symm_apply_apply]
      exact hw

    have hau : a ∈ usedOf I T Wt := usedOf_mono I T h ⟨w, hw, hxa⟩
    obtain ⟨ta, hta⟩ : ∃ ta : TupU I (usedOf I T Wt), ta.1 = I.tup a :=
      ⟨⟨I.tup a, Or.inr ((tup_mem_tuOf I).2 hau)⟩, rfl⟩
    have hix : ixOf I (usedOf I T Wt) ta = a := ixOf_eq I hta.symm
    have hs := z.xi_mu (h hw)
    have hxi : z.R.toLevCh.xiH ta = z.R.toLevCh.xiH (z.R.mu (plB X w)) := by
      rw [z.lev.xiH, z.lev.xiH, hix, hs, hxa]

    have he := z.lev.is.xi_inj hxi
    have e : z.resMu h (plB X w) = ⟨(z.R.mu (plB X w)).1, Or.inr (z.mu_mem h hw')⟩ := dif_pos hw'
    rw [e]
    apply Subtype.ext
    show (z.R.mu (plB X w)).1 = I.tup a
    rw [← he]
    exact hta

theorem muOf_res (h : Wt' ⊆ Wt) : MuOf X I T Wt' (z.resMu h) (z.resTw Wt') := by
  intro w
  have hpl : (plB X).symm (X.toD7.plEq w) = w := (plB X).symm_apply_apply w
  refine ⟨?_, ?_⟩
  · rw [z.mem_resTw h, hpl]
  · by_cases hw : w ∈ Wt'
    · rw [if_pos hw]
      have hw' : (plB X).symm (X.toD7.plEq w) ∈ Wt' := by
        rw [hpl]
        exact hw
      rw [← ixOf_inclU (usedOf_mono I T h), z.inclU_resMu h hw']
      exact z.xi_mu (h hw)
    · rw [if_neg hw]
      have hw' : (plB X).symm (X.toD7.plEq w) ∉ Wt' := by
        rw [hpl]
        exact hw
      rw [z.resMu_off h hw', ixOf_mu0F]

      have hb := z.lev.is.xi_base
      rw [z.lev.xiH, ixOf_mu0F] at hb
      exact hb


set_option maxHeartbeats 1000000 in
def resR (h : Wt' ⊆ Wt) : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt') z.Xg z.tr) z.core.Q.c.F :=
  Res.dat3 (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (inclU I (usedOf_mono I T h))
    (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt')


set_option maxHeartbeats 1000000 in
theorem newTup (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Res.NewTup (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (f := inclU I (usedOf_mono I T h))
      (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt') := by
  constructor
  case sub =>
    intro v hv
    exact (z.mem_twPl v).2 (h ((z.mem_resTw h v).1 hv))
  case conj =>
    intro v
    rw [z.mem_resTw h, z.mem_resTw h]
    exact hc.symm_mem_iff v
  case on =>
    intro v hv
    exact z.inclU_resMu h ((z.mem_resTw h v).1 hv)
  case off =>
    intro v hv
    exact z.resMu_off h fun hv' => hv ((z.mem_resTw h v).2 hv')
  case used =>
    exact z.resMu_used h

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RecExGOfRecAtG
section
noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem exists_du_nat (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (C : FC) (cD ch : ℝ) (P : PreCh) (q1 : ℕ)
    (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c →
    ∃ du : P.Word → ℕ, (∀ u, 0 < du u) ∧ ∀ u, (du u : ℝ) = duP P u := by
  obtain ⟨x0, h⟩ := Inh.g_big eps h0 h1
  refine ⟨x0, fun s C cD ch P q1 a b c hs hx hok => ?_⟩
  choose du hpos hdu using fun u => DuInt.duStarOf_nat P.R P.H (P.hcW u) hok.arith.2.1
    fun i => h s P.R _ hs hx hok.rank (hok.val.2.2.2.2.1 i).1
  exact ⟨du, hpos, hdu⟩

namespace Inh

end Inh

end GlobalTheory.Mem.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ValTransOfEq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Generic

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {N : Type} [AddCommGroup N] [Module ℂ N] {P P' : Submodule ℂ N}
  {ip : N → N → ℂ} {j : X ≃ₗ[ℂ] P}

theorem hilbTie_ofEq (e : P = P') (h : HilbTie P ip j) : HilbTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) := fun x y => h x y

theorem projTie_ofEq {Y : Type} {f : Y → X} {g g' : Y → N} (e : P = P') (h : ProjTie P ip j f g) (hg : ∀ y, g' y = g y) :
    ProjTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) f g' := fun x y => (h x y).trans (congrArg (ip (j x)) (hg y).symm)


omit [NormedAddCommGroup X] [InnerProductSpace ℂ X] in
theorem le_of_eqs {Q Q' : Submodule ℂ N} (e : P = P') (e' : Q = Q') (h : P ≤ Q) : P' ≤ Q' := e ▸ e' ▸ h

theorem val_trans_ofEq (e : P = P') (x : X) : ((j.trans (LinearEquiv.ofEq _ _ e)) x).1 = (j x).1 := rfl

theorem map_incl {Q Q' : Submodule ℂ N} {Z : Type} (e : P = P') (e' : Q = Q') (h : P ≤ Q) (j : X ≃ₗ[ℂ] P) {f : Q → Z} (f' : Q' → Z)
    (hf : ∀ v, f' (LinearEquiv.ofEq _ _ e' v) = f v) (y : X) :
    f' (Submodule.inclusion (le_of_eqs e e' h) ((j.trans (LinearEquiv.ofEq _ _ e)) y)) = f (Submodule.inclusion h (j y)) := by
  subst e e'
  exact hf (Submodule.inclusion h (j y))

end Generic

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A} {tupT : a.D.what₂.Tup → T}
  {hm : 0 < a.D.R.m} {hTop : TopMultH R}

def stepB (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : spCC c F tupT hm hTop l μ (k + 1)) : (toChainReal R F tupT hm hTop).Amb k :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioC l ((μ)) k ((v))).1 : _))

theorem stepB_eq (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) :
    stepB c l μ k (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v) =
      ((toChainReal R F tupT hm hTop).ioC l μ k v).1 := (ioCB_eq c l μ k v)

def topB (l : Bool) (μ : a.D.what₂.Tup) (v : spCCX c F tupT hm hTop l μ) : (toChainReal R F tupT hm hTop).Amb (a.D.R.m - 1) :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioX l ((μ)) ((v))).1 : _))

theorem topB_eq (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) :
    topB c l μ (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v) =
      ((toChainReal R F tupT hm hTop).ioX l μ v).1 := (ioXB'_eq c l μ v)

section Rows

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {X : RowSide a.D EE} {l : Bool}

def rowIds (I : RowIds X (toChainReal R F tupT hm hTop) l) : RowIds (rowSide c X) (chainB c.to F tupT hm hTop) l :=
  @RowIds.mk c.to.D EE _ _ _ (rowSide c X) (chainB c.to F tupT hm hTop) l
    ((by with_unfolding_all exact ((I.jE.trans (LinearEquiv.ofEq _ _ (congrFun (spEEc_eq c F tupT hm hTop) l))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) => (I.jM μ h j h1 h2).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) => (I.jX μ h).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ))) :)))
    ((I.prt))


set_option maxHeartbeats 4000000 in
theorem rowSideReal_tr {I : RowIds X (toChainReal R F tupT hm hTop) l} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE}
    {ty : Fin n → a.D.what₂.FT} (H : RowSideReal X (toChainReal R F tupT hm hTop) l I bs ty) :
    RowSideReal (rowSide c X) (chainB c.to F tupT hm hTop) l (rowIds c I) bs ((ty)) := by
  refine @RowSideReal.mk _ _ _ _ _ _ _ _ _ _ _ _ ?parY ?lvl ?lvlP ?lvlX ?ee ?mult ?multX ?io0 ?io0X ?io ?ioTop ?ft ?prt_disj
  case parY =>
    exact (H.parY)
  case lvl =>
    exact (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (spEEc_eq c F tupT hm hTop) l) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) 0) (H.lvl μ hμ))
  case lvlP =>
    exact (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) =>
      le_of_eqs (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) j) (H.lvlP μ hμ j h1 h2))
  case lvlX =>
    exact (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) (H.lvlX μ hμ))
  case ee =>
    exact (hilbTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) H.ee)
  case mult =>
    intro μ hμ j h1 h2
    letI := X.instMult μ j
    letI := X.instMulti μ j
    have t := hilbTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (H.mult μ hμ j h1 h2)
    with_unfolding_all exact t
  case multX =>
    intro h μ hμ
    letI := X.instMult μ a.D.R.m
    letI := X.instMulti μ a.D.R.m
    have t := hilbTie_ofEq (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (H.multX h μ hμ)
    with_unfolding_all exact t
  case io0 =>
    have t := (fun (h : 2 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) (H.io0 h μ hμ (okB_imp c ok)) fun y =>
        map_incl (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (0 + 1))
          (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (0 + 1)) (H.lvlP μ hμ 1 le_rfl (by omega))
          (I.jM μ hμ 1 le_rfl (by omega)) (stepB c l μ 0) (stepB_eq c l μ 0) y)
    with_unfolding_all exact t
  case io0X =>
    have t := (fun (h : a.D.R.m = 1) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) (H.io0X h μ hμ (okB_imp c ok)) fun y =>
        congrArg (cast (congrArg (toChainReal R F tupT hm hTop).Amb (show a.D.R.m - 1 = 0 by omega)))
          (map_incl (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ)
            (H.lvlX μ hμ) (I.jX μ hμ) (topB c l μ) (topB_eq c l μ) (cast (congrArg (X.Mult μ) h.symm) y)))
    with_unfolding_all exact t
  case io =>
    intro μ hμ ok j h1 h2
    letI := X.instMult μ j
    letI := X.instMulti μ j
    letI := X.instMult μ (j + 1)
    letI := X.instMulti μ (j + 1)
    have t := projTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (H.io μ hμ (okB_imp c ok) j h1 h2) fun y =>
        map_incl (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (j + 1))
          (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (j + 1)) (H.lvlP μ hμ (j + 1) (by omega) h2)
          (I.jM μ hμ (j + 1) (by omega) h2) (stepB c l μ j) (stepB_eq c l μ j) y
    with_unfolding_all exact t
  case ioTop =>
    have t := (fun (h : 2 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (a.D.R.m - 1)) (H.ioTop h μ hμ (okB_imp c ok)) fun y =>
        map_incl (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ)
          (H.lvlX μ hμ) (I.jX μ hμ) (topB c l μ) (topB_eq c l μ) y)
    with_unfolding_all exact t
  case ft =>
    exact (fun σ => cast (congrArg (· ∈ I.prt (ty σ)) (val_trans_ofEq (j := I.jE) (congrFun (spEEc_eq c F tupT hm hTop) l) (bs σ)).symm) (H.ft σ))
  case prt_disj =>
    exact (H.prt_disj)

end Rows

variable {hinj : ∀ i t, Function.Injective (R.extV i t)}


variable (F tupT hm hTop hinj) in
def spWc : type_of% (toLiftReal R F tupT hm hTop hinj).Wc := ((liftB c.to F tupT hm hTop hinj).Wc)


variable (F tupT hm hTop hinj) in
theorem spWc_eq : (toLiftReal R F tupT hm hTop hinj).Wc = spWc c F tupT hm hTop hinj := (lift_Wc c.to F tupT hm hTop hinj)


variable (F tupT hm hTop hinj) in
def spMultW : type_of% (toLiftReal R F tupT hm hTop hinj).MultW := ((liftB c.to F tupT hm hTop hinj).MultW)


variable (F tupT hm hTop hinj) in
theorem spMultW_eq : (toLiftReal R F tupT hm hTop hinj).MultW = spMultW c F tupT hm hTop hinj := (lift_MultW c.to F tupT hm hTop hinj)

def liftIds (I : LiftIds (toLiftReal R F tupT hm hTop hinj)) : LiftIds (liftB c.to F tupT hm hTop hinj) :=
  @LiftIds.mk c.to.D (chainB c.to F tupT hm hTop) (liftB c.to F tupT hm hTop hinj)
    ((by with_unfolding_all exact ((fun i : Fin a.D.R.m => (I.jMj i).trans (LinearEquiv.ofEq _ _ (congrFun (spWc_eq c F tupT hm hTop hinj) i))) :)))
    ((I.jMt)) ((I.prtW))

theorem liftTie_tr {I : LiftIds (toLiftReal R F tupT hm hTop hinj)} (H : LiftTie (toLiftReal R F tupT hm hTop hinj) I) :
    LiftTie (liftB c.to F tupT hm hTop hinj) (liftIds c I) := by
  refine @LiftTie.mk _ _ _ _ ((H.hol)) (by with_unfolding_all exact (fun i => hilbTie_ofEq (congrFun (spWc_eq c F tupT hm hTop hinj) i) (H.mj i))) ((H.mt)) ?_ (by with_unfolding_all exact H.isot) ((H.prtW_disj)) ((H.lamP))
  with_unfolding_all exact (cast (congrArg₂ (fun (P : type_of% (toLiftReal R F tupT hm hTop hinj).MultW) (Q : type_of% (toLiftReal R F tupT hm hTop hinj).Wc) =>
    ∀ μ (hμ : Used0 a.D μ) (i : Fin a.D.R.m) (x : a.D.what₂.Mt μ (i + 1)) (w : (toLiftReal R F tupT hm hTop hinj).AmbW i),
      Lift.IsThetaP ((toLiftReal R F tupT hm hTop hinj).measV μ i) ((toLiftReal R F tupT hm hTop hinj).fdV μ i)
        ((toLiftReal R F tupT hm hTop hinj).thW μ i) ((toLiftReal R F tupT hm hTop hinj).ptW μ i) ((toLiftReal R F tupT hm hTop hinj).ioK i)
        ((toLiftReal R F tupT hm hTop hinj).Amt μ i) ((toLiftReal R F tupT hm hTop hinj).thC μ i) → w ∈ P i →
      w ∘ₗ (toLiftReal R F tupT hm hTop hinj).embK i = (toLiftReal R F tupT hm hTop hinj).thC μ i (I.jMt μ hμ i x) →
      (toLiftReal R F tupT hm hTop hinj).eW i ∘ₗ w ∈ Q i →
      (I.jMj i (a.D.what₂.thetaP μ (i + 1) x)).1 = (toLiftReal R F tupT hm hTop hinj).eW i ∘ₗ w)
    (spMultW_eq c F tupT hm hTop hinj) (spWc_eq c F tupT hm hTop hinj)) H.theta)

theorem recTied_tr {X0 : BaseLevelRowSide a.D} {Ish : RowIds (RowSide.sharp a.D) (toChainReal R F tupT hm hTop) true}
    {Iz : RowIds X0.s (toChainReal R F tupT hm hTop) false} {IL : LiftIds (toLiftReal R F tupT hm hTop hinj)} {K : ColReal a.D}
    (H : RecTied a.D X0 (toChainReal R F tupT hm hTop) Ish Iz (toLiftReal R F tupT hm hTop hinj) IL K) :
    RecTied c.to.D (baseLevelRowSideTransport c X0) (chainB c.to F tupT hm hTop) ((rowIds c Ish)) ((by with_unfolding_all exact @rowIds B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz)) (liftB c.to F tupT hm hTop hinj)
      (liftIds c IL) (colReal c K) :=
  @RecTied.mk _ _ _ _ _ _ _ _ ((rowSideReal_tr c H.sharp)) ((by with_unfolding_all exact @rowSideReal_tr B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz (@Rows.Data.D0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.onb0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.ft0 (@Late.D B C a).R (@Late.D B C a).what₂) (@RecTied.base (@Late.D B C a) X0 (@toChainReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop) Ish Iz (@toLiftReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop hinj) IL K H))) (liftTie_tr c H.lift)
    (@ColTieR.mk _ _ _ ((H.col.tup)) ((H.col.xi0)) ((H.col.bu)))

def mjTie (x : MjTie R F) : @MjTie c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) :=
  @MjTie.mk c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) ((x.eW))
    ((by with_unfolding_all exact ((cast (congrArg (fun W : type_of% R.Wat => ∀ i, LinearMap.range (x.eW i) =
      (W i (sg0 a.D A) (R.levL F false (sg0 a.D A))).comap (R.HW i (sg0 a.D A)).e) (wat_eq c.to R)) x.eW_range) :)))
    ((x.eW_norm)) ((x.eW_lat))

end Chain

end GlobalTheory.Mem.R3.Tr

end
end

