module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0849
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0842
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0841
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BaseClassSum

variable {D : D7} {S T : HSp D}

theorem series_move {B : Base S T} (hB : B.Good) (hS : S.SigOK) {t : Twist D Circle} (ht : t.Good) (hQ : B.admitted t.Q)
    {ω : PairRep S T} (hω : B.IsWeil t.chi ω) {h h' : GA D S} (hh : h ∈ GfC S) (hh' : h' ∈ GfC S) (γ : GQ S) (k : B.levJ t)
    (e : finPt S h = Bridge.ratF S γ * finPt S h' * (k : Bridge.Gf S)) (P : PolF D T.rank S.rank) :
    series B.F ω (B.vecFlat t) h P =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • series B.F ω (B.vecFlat t) h' (B.act ((γ⁻¹ : GQ S) : GA D S) P) := by
  obtain ⟨hsplit, hcomm, htriv, -, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨x, hx⟩ := (k : Bridge.Gf S).2
  obtain ⟨kk, hkk, -, -, -, hfk⟩ := GlobalTheory.LiftUnfold.exists_fin_mul_real S x
  have hkk' : finPt S kk = (k : Bridge.Gf S) := hfk.trans (Subtype.ext hx)
  obtain ⟨ga, hga, gf, hgf, hγ⟩ := hsplit (γ : GA D S)
  have hfγ : Bridge.ratF S γ = finPt S gf := by
    change finPt S (γ : GA D S) = _
    rw [hγ]
    dsimp only [finPt]
    rw [map_mul]
    have : (finHom S).rangeRestrict ga = 1 := Subtype.ext (MonoidHom.mem_ker.1 hga)
    rw [this, one_mul]
  have eh : h = (γ : GA D S) * h' * ga⁻¹ * kk := by
    have eg : gf = (γ : GA D S) * ga⁻¹ := by
      rw [hγ, hcomm ga hga gf hgf, mul_inv_cancel_right]
    have e1 : h = gf * h' * kk := by
      set y := (gf * h' * kk)⁻¹ * h with hy
      have hyf : y ∈ GfC S := mul_mem (inv_mem (mul_mem (mul_mem hgf hh') hkk)) hh
      have hyi : y ∈ GinfC S := by
        have : finPt S y = 1 := by
          rw [hy]
          dsimp only [finPt] at hkk' hfγ e ⊢
          rw [map_mul, map_inv, map_mul, map_mul, hkk', ← hfγ]
          change _ * ((finHom S).rangeRestrict h) = 1
          rw [e]
          exact inv_mul_cancel _
        exact MonoidHom.mem_ker.2 (congrArg Subtype.val this)
      have := htriv y hyi hyf
      rw [hy, inv_mul_eq_one] at this
      exact this.symm
    rw [e1, eg, mul_assoc (γ : GA D S) ga⁻¹ h', hcomm ga⁻¹ (inv_mem hga) h' hh', ← mul_assoc]
  have hact : B.act ((γ⁻¹ : GQ S) : GA D S) = B.act ga⁻¹ := by
    have hr : GlobalTheory.ExportSeries.realGL B.F.θ S gf = 1 := by
      funext τ
      show Formalism.UG.bc (B.F.θ τ) (infHom S gf) = 1
      rw [MonoidHom.mem_ker.1 hgf, map_one]
    rw [Base.act, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_inv, hγ, _root_.mul_inv_rev, map_mul, map_inv _ gf, hr,
      inv_one, one_mul]
  have hJ : finPt S kk ∈ B.levJ t := hkk' ▸ k.2
  have hθf : ∀ P, IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat t) P) := Base.isThetaFunO_fock_vecAt hB hQ _
  have hk : ω (kk, 1) (B.F.fock (B.vecFlat t) P) = ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat t) P := by
    have h1 := GlobalTheory.ExportSeries.DualType.dual_type_fock hB hS ht hQ hω hkk hJ P
    have e2 : ((B.levLam t ⟨_, hJ⟩ : ℂˣ) : ℂ) = ((B.levLam t k : ℂˣ) : ℂ) :=
      congrArg (fun z : B.levJ t => ((B.levLam t z : ℂˣ) : ℂ)) (Subtype.ext hkk')
    rw [← e2]
    exact h1
  have ha : ω (ga⁻¹, 1) (B.F.fock (B.vecFlat t) P) = B.F.fock (B.vecFlat t) (B.act ga⁻¹ P) :=
    GlobalTheory.RealFockAction.om_fock_vecAt D S T B t ω t.Q _ hB ht hQ hω ga⁻¹ (inv_mem hga) P
  have ep : ∀ g : GA D T, (((γ : GA D S) * h' * ga⁻¹ * kk, g) : GA D S × GA D T) =
      ((γ : GA D S), 1) * ((h', g) * ((ga⁻¹, 1) * (kk, 1))) := fun g => by
    ext <;> simp [mul_assoc]
  have key : ∀ g : GA D T, ω (h, g) (B.F.fock (B.vecFlat t) P) 0 =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ * ω (h', g) (B.F.fock (B.vecFlat t) (B.act ga⁻¹ P)) 0 := fun g => by
    rw [eh, ep g, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hk, map_smul, ha,
      map_smul, map_smul, Pi.smul_apply, hω.om_aut _ γ.2 1 (one_mem _) _ (hω.om_pres _ _ (hθf _)), smul_eq_mul]
  refine funext fun g => ?_
  rw [Pi.smul_apply, smul_eq_mul, hact]
  exact key g

theorem series_triv (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h P = ρ.theta i j b h P := by
  have key : ∀ t : Twist D Circle, t.Q = ∅ → t.chi = 1 →
      series (ρ.B i j b).F (ρ.om i j b t.chi) ((ρ.B i j b).vecFlat t) h P = ρ.theta i j b h P := by
    rintro ⟨_, _, r⟩ rfl rfl
    show series _ _ ((ρ.B i j b).vecAt ∅ _) h P = series _ _ (ρ.B i j b).vecBase h P
    rw [Base.vecAt_empty]
  exact key _ (half_empty _) (charOf_one _ _)

theorem term_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank} (hF : F ∈ (ρ.B i j b).formsC (ρ.tw i b 0 ∅ 1))
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h (F (finPt _ h)) ∈
      Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hB := hρ.base i j b
  have hω := hρ.weil i j b _ hg
  obtain ⟨γ, s, h', k, hs, hoff, hh', hsupp, e⟩ := GlobalTheory.RankReps.exists_rep_split_levJ D ρ hρ i j b h hh
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF).2 γ (finPt _ h') k
  have hval : F (finPt _ h') ∈ (ρ.B i j b).valSpace := ((ρ.B i j b).mem_formsC.1 hF).1 _
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [e, hlaw, LinearMap.map_smul, series_move hB (D.sp.V_sig _) hg ha hω hh hh' γ k e, hinv, smul_smul,
    mul_inv_cancel₀ (Units.ne_zero _), one_smul, series_triv]

  have hspan : F (finPt _ h') ∈ Submodule.span ℂ (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) := by
    have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
      have h1 := hB.sig τ
      have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
      rw [← h1] at h2
      exact h2.le
    have h2 := (GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span D (Wc D j).rank (Vc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS _ (Formalism.L2.Host.embLL0 D) (labLL0 D)
      (ρ.eO i b).range ((ρ.B i j b).latAt (finPt _ h')) hB.wt hm (hρ.isCoefRing i b)
      (GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b h')).2
    have h3 : (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) =
        (harmLat (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.eO i b).range (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS
          ((ρ.B i j b).latAt (finPt _ h')) : Set (PolF D (Wc D j).rank (Vc D j).rank)) := rfl
    rw [h3, h2]
    exact hval
  have hmap := Submodule.mem_map_of_mem (f := (ρ.B i j b).theta (ρ.om i j b 1) h') hspan
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨s, h', P, ⟨hs, hoff, hh', hsupp, hP⟩, rfl⟩

theorem sum_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank}
    (hF : F ∈ Submodule.span ℂ (ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))) :
    ρ.sum i j b 0 ∅ 1 F ∈ Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hc := hρ.classes i j b _ hg ha
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hF' := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
    rw [Setup.sum, Base.classSum_apply]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (term_mem_span hρ i j b hF'.1 (hc.fin c))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end GlobalTheory.BaseClassSum

namespace GlobalTheory.TwInputs

theorem spanGood_of_sumOnto : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), ∀ i, SumOnto rd i → SpanGood rd i := by
  intro D ρ hρ rd i hS j b x hx
  obtain ⟨F, hF, e⟩ := hS j b x hx
  rw [e]
  exact GlobalTheory.BaseClassSum.sum_mem_span hρ i j b hF

end GlobalTheory.TwInputs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeSameMap
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
namespace GlobalTheory.TwInputs.Move.Forms

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def fiOfEq (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) : NX.FormsIso (X.R.FW a) (X.R.FW b) :=
  hab ▸
    { eK := RingEquiv.refl _
      eK_LL := fun _ => rfl
      e := LinearEquiv.refl _ _
      eG := MulEquiv.refl _
      eW := fun _ => LinearIsometryEquiv.refl _ _
      wk := fun _ => Iff.rfl
      mkK := fun _ => Iff.rfl
      rho := fun _ _ => rfl
      chi := fun _ => rfl
      j := fun _ _ => rfl }

theorem fiOfEq_eG (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) (g : X.Γ) : (fiOfEq X hab).eG g = g := by
  subst hab; rfl

variable (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
  (YS : NX.NExpRealS X.R X.cG S)

theorem fiOfEq_forms (j : Fin D.R.m) {a b : Fin D'.R.m} (ha : (j : ℕ) = a) (hb : (j : ℕ) = b) (hab : a = b) (x : (X.R.FW j).WK) :
    (fiOfEq X' hab).e ((m.forms j a ha).φ x) = (m.forms j b hb).φ x := by
  subst hab; rfl

include h in
theorem lt_m {n : ℕ} (h2 : n + 1 ≤ D'.R.m) : n < D.R.m := by
  have h3 : D.R.m = D'.R.m := by rw [h.gal.R]
  omega

abbrev dat : NX.RatDat D'.ntw :=
  NX.ratDatR X'.R X'.cG (m.kKsOf (e := e) YS (NX.idxOf D 0)) (m.kKsOf_spec h YS _)

abbrev back (i' : D'.ntw.Tw) : D.ntw.Tw := cast h.Tw_eq.symm i'

theorem back_heq (i' : D'.ntw.Tw) : HEq (back h i') i' := cast_heq _ _

def eFm (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) : 1 ≤ j → j ≤ D'.R.m →
    (D'.nexp.Fm i' j b ≃ₗ[FractionRing (D'.ntw.O i')] NX.Fm (dat h m YS) i' j b) :=
  match j with
  | 0 => fun h1 _ => absurd h1 (by decide)
  | n + 1 => fun _ h2 => m.eFOf h YS _ _ (back_heq h i') ⟨n, lt_m h h2⟩ b

def ks (j : Fin D.R.m) : KsIso ι (show S.Ks ≃+* (dat h m YS).Ks from (YS.fi j).eK.trans m.eK)
    (show S.G ≃* (dat h m YS).G from (YS.fi j).eG.trans m.γ) (S.A ((j : ℕ) + 1)) ((dat h m YS).A ((j : ℕ) + 1)) := m.ksOf h YS j

theorem eFm_cast {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (h1 h2)
    (x : D.nexp.Fm i ((j : ℕ) + 1) b) :
    eFm h m YS i' ((j : ℕ) + 1) b h1 h2 (h.fmCast hi _ b x) =
      fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j) (YS.eF i _ b (Nat.le_add_left _ _) j.2 x) := by
  obtain rfl : i = back h i' := eq_of_heq (hi.trans (back_heq h i').symm)
  exact h.eFMove_fmCast hi (S' := dat h m YS) (ks h m YS j) _ x

theorem sup_move (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b)
    (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (x : D'.nexp.Fm i' j b) :
    x ∈ D'.nexp.Bsup i' j b ↔ eFm h m YS i' j b h1 h2 x ∈ NX.Bsup (dat h m YS) i' j b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  rw [eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2 x, fmOf_mem_Bsup, ← hsup]
  exact ((record_heq h.gal h.set h.frm h.Bsup h.delta hi).1 _ b _ _ (h.fmCast_heq hi _ b x).symm).1.symm

theorem rho_move (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) : NX.RhoStab (dat h m YS) j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact (KsIso.rhoStab_iff (S' := dat h m YS) (ks h m YS ⟨n, lt_m h h2⟩)).1 (YS.rho _ h1 (lt_m h h2))

theorem chi_move (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) : NX.ChiInLL0 (dat h m YS) j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact KsIso.chiInLL0 (S' := dat h m YS) (ks h m YS ⟨n, lt_m h h2⟩) h.LL0 (YS.chi _ h1 (lt_m h h2))

theorem act_move (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (g : G0g D'.nd) (x : D'.nexp.Fm i' j b) :
    eFm h m YS i' j b h1 h2 (D'.nexp.actG i' j b g x) =
      NX.actG (dat h m YS) i' j b (rho_move h m YS j h1 h2) (chi_move h m YS j h1 h2) g (eFm h m YS i' j b h1 h2 x) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  obtain ⟨g, rfl⟩ := h.grpEquiv.surjective g
  have e1 : D'.nexp.actG i' (n + 1) b (h.grpEquiv g) (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.actG _ (n + 1) b g x) :=
    eq_of_heq ((((record_heq h.gal h.set h.frm h.Bsup h.delta hi).1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.1 _ _
      (h.grpEquiv_heq g).symm).symm.trans (h.fmCast_heq hi _ b _).symm)
  rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, YS.act]
  refine fmOf_actG (S' := dat h m YS) _ _ _ _ _ _ _ _ ?_ _
  refine (dat h m YS).eG.symm_apply_eq.2 ?_
  refine Eq.symm ((m.cG_eG h _).trans (congrArg h.grpEquiv ?_))
  exact (YS.geq _ _).trans (S.eG.apply_symm_apply g)

def tie (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) : NX.NExpRealS X'.R X'.cG (dat h m YS) where
  fi j := fiOfEq X' (NX.idxOf_succ D' j)
  geq j g := congrArg (fun g => X'.cG (X'.R.eG g)) (fiOfEq_eG X' _ g)
  rho := rho_move h m YS
  chi := chi_move h m YS
  eF := eFm h m YS
  bsup i j b h1 h2 := ⟨1, one_ne_zero, fun x hx => by rw [one_smul]; exact (sup_move h m YS hsup i j b h1 h2 x).1 hx,
    fun x hx => by rw [one_smul]; exact (sup_move h m YS hsup i j b h1 h2 x).2 hx⟩
  act := act_move h m YS

theorem read_move (j : Fin D.R.m) (y : (S.A ((j : ℕ) + 1)).WK) :
    SameMap (evidence X j ((YS.fi j).e y))
      (evidence X' (h.cm j) ((fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e ((ks h m YS j).φ y).1)) := by
  have e1 := fiOfEq_forms m j (a := NX.idxOf D' ((j : ℕ) + 1)) (b := h.cm j)
    (congrArg Fin.val (NX.idxOf_succ D' (h.cm j))).symm rfl (NX.idxOf_succ D' (h.cm j)) ((KsIso.ofFormsIso (YS.fi j)).φ y)
  exact (congrArg (fun z => SameMap (evidence X j ((YS.fi j).e y)) (evidence X' (h.cm j) z)) e1).mpr
    (m.read j (h.cm j) rfl ((KsIso.ofFormsIso (YS.fi j)).φ y))

theorem rdRel_move (hsup) (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) (hs : SameSetup ρ ρ') (hρ : ρ.Good) (hρ' : ρ'.Good) (c : ℂ) :
    RdRel h (fun i j b => realRd YS X.geo.v₀ hρ i j b c) (fun i j b => realRd (tie h m YS hsup) X'.geo.v₀ hρ' i j b c) := by
  intro i i' hi j b f
  have hG := (hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl).1
  refine Function.hfunext hG.symm fun g' g hg => heq_of_eq ?_
  change c⁻¹ * evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b
      (eFm h m YS i' ((j : ℕ) + 1) b (Nat.le_add_left _ _) (h.cm j).2 (h.fmCast hi _ b f)) g' =
    c⁻¹ * evK YS X.geo.v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) g
  have key : ∀ z : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b (fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j) z) g' =
        evK YS X.geo.v₀ hρ i j b z g := fun z => by
    induction z using TensorProduct.induction_on with
    | zero =>
      exact (congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
        (fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j)).map_zero).trans
          ((congrFun (map_zero _) _).trans (congrFun (evK YS X.geo.v₀ hρ i j b).map_zero g).symm)
    | add x y hx hy =>
      refine (congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
        ((fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j)).map_add x y)).trans ?_
      refine (congrFun ((evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b).map_add _ _) g').trans ?_
      rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx, hy]
    | tmul a y =>
      exact congrArg₂ (· * ·)
        ((record_heq h.gal h.set h.frm h.Bsup h.delta hi).2.1 _ _ hs.e b _ _ (h.frac_heq hi a).symm).symm
        (read_move h m YS j y _ _ (m.v₀ j (h.cm j) rfl) _ _ hg.symm).symm
  exact congrArg (c⁻¹ * ·) ((congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
    (eFm_cast h m YS hi j b _ _ f)).trans (key _))

variable {YS} (H : NX.NExpRealH X.R X.cG S YS)


omit H in
include h m in
theorem hecke_sameMap (j : Fin D.R.m) {R : Finset (GA D (Wc D j))} {R' : Finset (GA D' (Wc D' (h.cm j)))}
    (hF : ∀ F F', HEq F F' → HEq (Mult.heckeLin (Wc D j) R F) (Mult.heckeLin (Wc D' (h.cm j)) R' F'))
    {T₁ T₂ : Mult.MMap (model X j)} {T₁' T₂' : Mult.MMap (model X' (h.cm j))} (h1 : SameMap T₁ T₁') (h2 : SameMap T₂ T₂') {c : ℂ}
    (h3 : T₁ = c • Mult.heckeOn (model X j) R T₂) : T₁' = c • Mult.heckeOn (model X' (h.cm j)) R' T₂' := by
  obtain ⟨hG, hW, -⟩ := hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl
  refine MultilinearMap.ext fun v' => funext fun g' => ?_
  obtain ⟨v, hv⟩ := exists_sameVec h.gal.R h.gal.host h.Tau h.eTau hW (m.MW j (h.cm j) rfl) v'
  obtain ⟨g, hg⟩ : ∃ g : GA D (Wc D j), HEq g g' := ⟨cast hG.symm g', cast_heq _ _⟩
  have e1 := hF (T₂ v) (T₂' v') (Function.hfunext hG fun a a' haa => heq_of_eq (h2 v v' hv a a' haa))
  have e2 : ∀ {A B : Type} {f : A → ℂ} {f' : B → ℂ} {a : A} {b : B}, A = B → HEq f f' → HEq a b → f a = f' b := by
    intro A B f f' a b h1 h2 h3
    subst h1; subst h2; subst h3; rfl
  rw [← h1 v v' hv g g' hg, h3]
  exact congrArg (c * ·) (e2 hG e1 hg)

end GlobalTheory.TwInputs.Move.Forms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalIffUnrOfLawsT
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.RecT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RecT.SphLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def consEquiv (n : ℕ) : ((Fin 1 → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := Fin.cons (v.1 0) v.2
  invFun f := (fun _ => f 0, Fin.tail f)
  map_add' x y := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv v := Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; simp) (funext fun j => by simp [Fin.tail])
  right_inv f := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

theorem diag_sum_iso {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    ((WDRep.diag h fun _ : Fin 1 => c 0).sum (WDRep.diag h fun i : Fin n => c i.succ)).Iso (WDRep.diag h c) := by
  refine ⟨consEquiv n, fun σ v => ?_, fun v => ?_⟩
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]

theorem sumList_cons (x : WD h) (l : List (WD h)) : sumList (x :: l) = x.lpSum (sumList l) := rfl

theorem sumList_ofFn_diag : ∀ (n : ℕ) (c : Fin n → ℂˣ),
    sumList (List.ofFn fun i => WD.mk (WDRep.diag h fun _ : Fin 1 => c i)) = WD.mk (WDRep.diag h c)
  | 0, c => by
      rw [List.ofFn_zero]
      show WD.lpZero (h := h) = _
      unfold WD.lpZero
      congr 2
      funext i
      exact i.elim0
  | n + 1, c => by
      rw [List.ofFn_succ]
      rw [sumList_cons]
      rw [sumList_ofFn_diag n (fun i => c i.succ), WD.lpSum_mk]
      exact WD.sound (diag_sum_iso c)

theorem zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.segmentRepresentation'
    GlobalTheory.grothendieckRingPolynomial_outright

theorem geometricLemma : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_holds

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem sat (H : LawsT a ha rc) (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ) (hα : HasSatake x.rep α) :
    rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar GlobalTheory.langlandsExhaustionGL_holds
    GlobalTheory.langlandsMultisegments_outright GlobalTheory.standardCosocleGL_holds zelevinskyPolynomialRing geometricLemma
    GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

end GlobalTheory.RecT.SphLaw

namespace GlobalTheory.RecT

theorem isSpherical_iff_unr_of_lawsT : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsT a ha rc → ∀ x : IrrGL (k := w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr := by
  intro E Ω _ _ _ _ _ A w h a ha rc H x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  constructor
  · intro hs
    obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) x.1
      ⟨x.2.rep.V, x.2.rep.ρ, x.2.rep.smooth, x.2.rep.irr⟩ hs
    rw [SphLaw.sat H x α hα]
    exact (WD.unr_mk _).2 (WDRep.unr_diag _)
  · intro hu
    obtain ⟨α, hα⟩ := GlobalTheory.LocLanglands.unr_eq_diag_inv E Ω A w h (rc x) hu
    obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
    have φ := equivRep π
    have hπ' : HasSatake (cls π).rep α := ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hπ.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
    have e1 := SphLaw.sat H (cls π) α hπ'
    have hsupp := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (w.adicCompletion E) _
      (fun i => unrChar (w.adicCompletion E) (α i)) (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ _))
      (cls π).2.rep hπ'.2.2
    have hg : Good (cls π) := Model.good_of_toral ⟨_, hsupp, fun y hy => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
      rfl⟩
    have e2 : x = cls π := H.inj x (cls π) hg (hα.trans e1.symm)
    rw [e2]
    exact hπ'.2.1

end GlobalTheory.RecT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RtMemIsoTyp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsType

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (h : GAf L n)
    (f : GAf L n → W) (hf : f ∈ NG.isoTyp ρ S) : NG.rt L n h f ∈ NG.isoTyp ρ S := by
  have hle : NG.isoTyp ρ S ≤ (NG.isoTyp ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun U hU => ?_
    intro a ha
    have hU' : U ≤ NG.isoTyp ρ S := le_sSup hU
    exact hU' (hU.1.1.stable h a ha)
  exact hle hf

end GlobalTheory.CenKeepsType
end

