module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombSmulLeft
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.QPl GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw.RescTest
variable {D : D7} {c : Comm D} {t : Tup c}

theorem root_ne {z : ℂ} (h : ∃ n : ℕ, 0 < n ∧ z ^ n = 1) : z ≠ 0 := by
  obtain ⟨n, hn, h⟩ := h
  rintro rfl
  simp [hn.ne'] at h

theorem comb_lc (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T e f = Finsupp.linearCombination ℂ (fun x => heisO ψ S T x f) e := rfl

theorem comb_smul_left (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • e) f = a • comb ψ S T e f := by
  rw [comb_lc, comb_lc, map_smul]

theorem trc_lc {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) :
    trc e f = Finsupp.linearCombination ℂ (fun g => rTrans g f) e := rfl

theorem trc_smul_left {V : HSp D} (a : ℂ) (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (a • e) f = a • trc e f := by
  rw [trc_lc, trc_lc, map_smul]

theorem biComb_smul2 (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a b : ℂ) (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' (a • e) (b • e') C = (a * b) • biComb ψ A S A' e e' C := by
  funext u x
  simp only [biComb, comb_smul_left, Pi.smul_apply, smul_eq_mul]
  have : (fun u' => b * comb ψ S A' e' (C u') x) = b • fun u' => comb ψ S A' e' (C u') x := rfl
  rw [this]
  have h2 : ∀ f : WO A S → ℂ, comb ψ A S e (b • f) = b • comb ψ A S e f := fun f => by
    funext y
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h2, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem biLift_move {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS (a • φ) C = a • biLift oma omb vA vS φ C := by
  funext h
  simp only [biLift, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem biLift_smul' {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS φ (a • C) = a • biLift oma omb vA vS φ C := by
  funext h₂
  have h2 : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) 0 =
      a * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 := by
    intro h₀ h₁
    have e : (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) = a • (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
      funext fun v => by
        rw [show (fun u => a * C u v) = a • (fun u => C u v) from rfl, map_smul]
        rfl
    rw [e, map_smul]
    rfl
  simp only [biLift, Pi.smul_apply, smul_eq_mul, h2]
  simp_rw [show ∀ x y : ℂ, x * (a * y) = a * (x * y) from fun x y => mul_left_comm x a y, integral_const_mul]

theorem hand_smul_fun {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (a : ℂ)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ (a • φ) g h₁ h₂ = a • Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ := by
  have e : ∀ Ξ, handBF s₁ l (a • φ) Ξ = star a • handBF s₁ l φ Ξ := fun Ξ => by
    funext h w
    simp only [GlobalTheory.Unf.handBF, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, star_mul']
  unfold Chain.hand
  have := GlobalTheory.HandHom.handFB_smul s₂ vL (star a) 1 (handBF s₁ l φ (flatBF s₁ (s₁.om (g, h₁) Φ₁))) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))
  rw [one_smul, star_star, mul_one] at this
  rw [e, this]

theorem sum_supp {G : Type} (a : ℂ) (e : G →₀ ℂ) (F : G → ℂ) :
    ∑ g ∈ (a • e).support, (a • e) g * F g = ∑ g ∈ e.support, e g * (a * F g) := by
  have h : ∀ (e : G →₀ ℂ) (F : G → ℂ), ∑ g ∈ e.support, e g * F g = Finsupp.linearCombination ℂ F e := fun _ _ => rfl
  rw [h, map_smul, ← h, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem contAut_smul {V : HSp D} (a : ℂ) {φ : GA D V → ℂ} (h : IsContAut V φ) : IsContAut V (a • φ) :=
  ⟨fun γ hγ g => by simp only [Pi.smul_apply, h.1 γ hγ g], h.2.const_smul a⟩

def free (w : VTup t) : VTup t := { w with FX := fun _ _ => Set.univ }

theorem qpin_free {v : VCom c} {w : VTup t} (h : QPin v w) : QPin v (free w) := by
  obtain ⟨F, h⟩ := h
  exact ⟨F, h.inj, h.places, h.kom, h.mid, h.lastc, h.eQ, h.eQT, h.dQ, h.ε, h.εT, h.FY, h.cQ⟩

theorem inner (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ≠ 0) (w : VTup t) (j : ℕ) (β : t.Ch (j + 1 + 1))
    (φ : t.Ch j → GA D (c.X j) → ℂ) (C) :
    (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ ((resc w s).dQ j α γ) ((resc w s).dQ (j + 1) γ β) C)) =
      (s (j + 1 + 1) β)⁻¹ • ∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (s j α • φ α)
        (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) C) := by
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
  simp only [resc, biComb_smul2, Comm.bl, biLift_smul', biLift_move, smul_smul]
  congr 1
  have := hs (j + 1) γ
  field_simp

theorem qlast_resc (v : VCom c) (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ≠ 0) (H : QLast v (free w)) :
    QLast v (resc w s) := by
  intro j h Ψ₁ Ψ₂ h₁ h₂ φ hφ f hf hf'
  have := H j h Ψ₁ Ψ₂ h₁ h₂ (fun α => s j α • φ α) (fun α => ⟨contAut_smul _ (hφ α).1, trivial⟩) f hf hf'
  simp only [inner s hs]
  refine Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (this.trans (congrArg _ (Finset.sum_congr rfl fun β _ => Eq.symm ?_)))
  · refine (sum_supp _ _ _).trans (Finset.sum_congr rfl fun g _ => ?_)
    simp only [Comm.bl, biLift_move, Pi.smul_apply, smul_eq_mul, mul_left_comm (f _) (s j α), integral_const_mul]
    rfl
  · congr 1
    funext h'
    have e : trc ((resc w s).εT (j + 1 + 1) h β) f = s (j + 1 + 1) β • trc (w.εT (j + 1 + 1) h β) f := trc_smul_left _ _ _
    rw [e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, mul_inv_cancel₀ (hs _ _), one_mul]
    rfl

theorem qlaw_resc (v : VCom c) (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ≠ 0) (H : QLaw v (free w)) :
    QLaw v (resc w s) := by
  intro j σ h ρ₁ μ₁ ρ₂ μ₂ n₁ n₂ Ψ₁ Ψ₂ h₁ h₂ φ hφ f hf hf'
  have := H j σ h ρ₁ μ₁ ρ₂ μ₂ n₁ n₂ Ψ₁ Ψ₂ h₁ h₂ (fun α => s j α • φ α) (fun α => ⟨contAut_smul _ (hφ α).1, trivial⟩) f hf hf'
  simp only [inner s hs]
  refine cast (congrArg₂ (Iter2 ρ₁ μ₁ ρ₂ μ₂) (Eq.symm ?_) (Eq.symm ?_)) this
  · funext q₁ q₂
    refine Finset.sum_congr rfl fun α _ => (sum_supp _ _ _).trans (Finset.sum_congr rfl fun g _ => ?_)
    congr 1
    have e := GlobalTheory.HandHom.per_smul (c.B (j + 1 + 1) σ (idx_step h)) c.ψ (s j α) 1
      (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (w.eQ j) Ψ₁)
            (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)
    rw [one_smul, mul_one, ← hand_smul_fun] at e
    exact e.symm
  · refine congrArg _ (Finset.sum_congr rfl fun β _ => ?_)
    have e : trc ((resc w s).ε (j + 1 + 1) β) f = s (j + 1 + 1) β • trc (w.ε (j + 1 + 1) β) f := trc_smul_left _ _ _
    rw [e]
    refine (GlobalTheory.HandHom.per_smul _ _ _ _ _ _).trans ?_
    rw [inv_mul_cancel₀ (hs _ _), one_mul]
    rfl

theorem qfin_resc (v : VCom c) (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (H : QFin v w) : QFin v (resc w s) := by
  intro j σ h
  obtain ⟨K, T, a, b, c', d, e, f⟩ := H j σ h
  exact ⟨K, T, a, b, c', d, e, fun Ψ hΨ α g hg => f Ψ hΨ α g (Finsupp.support_smul hg)⟩

theorem laws_of_qpinU (v : VCom c) (H : ∀ w : VTup t, QPin v w → QLaw v w ∧ QLast v w ∧ QFin v w) (w : VTup t)
    (h : QPinU v w) : QLaw v w ∧ QLast v w ∧ QFin v w := by
  obtain ⟨w₀, s, hs, h, rfl⟩ := h
  exact ⟨qlaw_resc v _ s (fun j α => root_ne (hs j α)) (H _ (qpin_free h)).1,
    qlast_resc v _ s (fun j α => root_ne (hs j α)) (H _ (qpin_free h)).2.1, qfin_resc v _ s (H _ h).2.2⟩

end GlobalTheory.QTw.RescTest
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFramedAdapted
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

section Frame

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {A : Formalism.BasicNotions.TH.HSp D}

theorem besVec_ne_zero (B : SBes X h u ψ A) : B.d.i₀ *ᵥ vecB B.o B.ζ ≠ 0 := fun h0 => by
  apply B.line.2
  have e : B.L.gram *ᵥ B.ζ = (B.o.iBᴴ * (B.d.i₀ᴴ * (D.sp.Y 0).gram)) *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) := by
    rw [← B.o.isoB, ← B.d.iso]
    simp only [vecB, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, h0]; simp

end Frame

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def InPlace : Prop := Placed f B ∧ Framed B

variable {f B}

variable (f B)

theorem shift_tOf (a₀ a : GA D (D.sp.X 0)) :
    (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * tOf f B a₀ a =
      embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) := by
  unfold tOf
  rw [mul_assoc, mul_inv_cancel_left]

theorem tOf_eq_iff (a₀ a : GA D (D.sp.X 0)) (t : GA D (D.sp.Y 0)) :
    tOf f B a₀ a = t ↔ embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) =
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * t := by
  rw [← shift_tOf, mul_right_inj]

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

abbrev chrK (W : RealPack ex) (t : W.P.T) (j : ℕ) : (AE (I.rec7 l Z))ˣ →* Circle := (pk W).toLevCh.mu t (j + 1)


set_option maxHeartbeats 1000000 in
structure QJ (a : GeoAll W u) (t : W.P.T) where
  Ch₀ : ℕ → Type
  A : TwDat I l Z u (W.P.I.tup t) Ch₀
  r : ℕ
  pl : Fin r → Pl (I.rec7 l Z).host.E
  mem : ∀ i, pl i ∈ (pk W).Q t
  E : ∀ i, QExt (a.Q (pl i) ⟨t, mem i⟩) (chrK W t)
  P : Fin r → BadPr I (W.P.I.tup t)
  hψ : ∀ i, Continuous (a.Q (pl i) ⟨t, mem i⟩).ψk
  sg : Fin r → ℂ
  π : ∀ i j, Ch₀ j → (E i).Ch j
  ι : ∀ j, (∀ i, (E i).Ch j) → Ch₀ j

variable {a : GeoAll W u} {t : W.P.T} (J : QJ a t)

abbrev QJ.G (i : Fin J.r) := a.Q (J.pl i) ⟨t, J.mem i⟩

abbrev QJ.Ch (j : ℕ) : Type := ∀ i, (J.E i).Ch j

structure QJ.Reads : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (pk W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = chrK W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((pk W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))

  cos : ∀ i β (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → (J.E i).cos (J.π i ((J.G i).s + 1) β) =
      Submodule.Quotient.mk fun r => (ofSplit (J.G i).q).pr (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2 (e r))

  std : ∀ j, j + 1 < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)

  pen : ∀ j (hj : j + 1 = B.R.m) β, ∃ k₀ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j),
    k₀ ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) k₀ = (TC.kStd X u (B.R.N j)).1 ∧ J.A.kA j β = k₀ * h ∧
    h ∈ GlobalTheory.FinPl.grpAt _ (fun p => ∃ i, (J.G i).q.v = p) ∧
    ∀ i (e : (J.G i).s + 1 = j), ∃ g ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J,
      (mt _ (e ▸ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1)))).map (J.G i).q.pr =
        ((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁ * ((J.G i).FX ((J.G i).s + 1) le_rfl).γ
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i

  cosG : ∀ (n : Fin a.n) y (e : XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r,
      (ofSplit (a.G n).q).pr (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ y)).1.2 (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k]
  live : J.A.Live J.ι

end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZero

open GlobalTheory.ChainOnto (Com)

variable {D : D7}

section Common

variable {c : Comm D} {v : VCom c}

def Red (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1

structure LocAt (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)) : Prop where
  idem : Formalism.L2.NTheta.IsIdemAt G.q.e PP
  under : G.q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  frame : ∀ a (ha : 0 + a = G.s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) 0 ≃ Fin (c.V 0).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit G.q) (c.V 0) b β
      (((G.FY 0 a ha).β * ((G.S.T (Fin D.R.t)).bas 0 a ha).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) 0 a ha (e.symm i))

structure Bot (cm : Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) : Prop where
  com : cm.Is
  psi : cm.ψ = c.ψ
  mem : st.st.Is cm 0
  fin : b ∈ GfC (c.V 0)
  typ : IsTypePlaces cm.Pg
  loc : ∀ PP : cm.Pg, LocAt (G PP) PP.1 b st.β
  grp : ∀ g : ∀ PP : cm.Pg, GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1), g ∈ cm.P.H ↔ ∀ PP, ∃ x, Red (G PP) PP.1 x (g PP)
  chr : ∀ (g : cm.P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, Red (G PP) PP.1 (x PP) (g.1 PP)) →
    cm.P.chi g = ∏ PP, (G PP).S.P.lam (x PP)

end Common

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

variable {W : RealPack ex} {u : D.what₂.Word}



end GlobalTheory.LevZero

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def PrimTop {c : Comm D} (tP : Finset (GlobalTheory.FinPl.Pl D)) (ζ₀ : Fin c.Lz.rank → D.host.E) : Prop :=
  ∀ p, p ∉ tP → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = p),
    a • ratV (vecB (c.oT D.R.m rfl) ζ₀) ∈ GlobalTheory.FinPl.latV (c.X D.R.m) (c.x D.R.m).L (· = p) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = p)

end GlobalTheory.MiTop

end
end

