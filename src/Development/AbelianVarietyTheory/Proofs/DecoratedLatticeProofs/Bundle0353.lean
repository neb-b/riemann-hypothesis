module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstOffLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepOff

theorem vac_off {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} {w : VTup t} (hc : c.Is) (hv : v.Is) (hf : VForm v w)
    (j : ℕ) (hj : j + 1 < D.R.m) (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ)
    (hΨ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ) :
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ)) := by
  have h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) Ψ := by
    have h1 := (GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (offP v w) (fun p => ¬ offP v w p)
      (fun p hp hn => hn hp)).2.2.2.2 (v.N j) (v.N (j + 1)) Ψ (hv.sd j (by omega)) (hv.sd (j + 1) hj)
    have h2 : (fun p => offP v w p ∨ ¬ offP v w p) = fun _ : Pl D => True := by
      funext p; exact propext ⟨fun _ => trivial, fun _ => em _⟩
    rw [h2] at h1
    exact (h1.1 hΨ).1
  have hQ := ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ w.Q) (offP v w)
    (fun p hp hn => hn.2 hp)).2.1 (w.eQ j) (hf.atQ j).1).2 _ _ _ h0
  exact ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ v.gP) (offP v w)
    (fun p hp hn => hn.1 hp)).2.1 (v.eG j) (hv.atG j).1).2 _ _ _ hQ

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * κ) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hf _ hoff _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ _ G x a _ f _ κ hκ q₁ q₂
  have k₁ := vac_off hc hv hf j (by omega) Ψ₁ h₁
  have k₂ := vac_off hc hv hf (j + 1) (by omega) Ψ₂ h₂
  obtain ⟨e₁, e₂⟩ := (hoff j σ h _ _ k₁ k₂).1 κ hκ
  have a₁ : ∀ g, t.om j (g, q₁ * κ) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) =
      t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    have : ((g, q₁ * κ) : GA D (c.V j) × GA D (c.V (j + 1))) = (g, q₁) * (1, κ) := by simp
    rw [this, map_mul, Module.End.mul_apply, e₁]
  have a₂ : t.om (j + 1) (q₁ * κ, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      t.om (j + 1) (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    have : ((q₁ * κ, q₂) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (q₁, q₂) * (κ, 1) := by simp
    rw [this, map_mul, Module.End.mul_apply, e₂]
  rw [← (ht.sBF j (σ + 1) h).1] at a₁
  rw [← (ht.sFB j σ h).1] at a₂
  unfold integ Chain.hand
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  erw [a₁ g, a₂]

end GlobalTheory.DStepOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondFixedLeve
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepLev

theorem comm_inf_fin {D : D7} (V : HSp D) {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  have ha' : finHom V a = 1 := ha
  have hb' : infHom V b = 1 := hb
  have h := GlobalTheory.LevelCut.eq_one_of_parts V (a * b * (b * a)⁻¹)
    (show infHom V _ = 1 by simp [hb']) (show finHom V _ = 1 by simp [ha'])
  exact mul_inv_eq_one.mp h

theorem per_hand_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)}
    {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (g : GA D B.V) (q₁ : GA D J.W) (q₂ k : GA D B'.V)
    (s : ℂ) (hs : s ≠ 0) (hom : s₂.om (1, k) Φ₂ = s⁻¹ • Φ₂) (f f' : GA D B'.V → ℂ) (hf : f' = s • f) :
    B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ (q₂ * k)) f' = B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ q₂) f := by
  have e : ((q₁, q₂ * k) : GA D J.W × GA D B'.V) = (q₁, q₂) * (1, k) := by simp
  have hh := GlobalTheory.HandHom.handFB_smul s₂ vL 1 s⁻¹
  simp only [one_smul, star_one, one_mul] at hh
  unfold Chain.hand
  rw [hf, e, map_mul, Module.End.mul_apply, hom, LinearMap.map_smul, GlobalTheory.HandHom.flatFB_smul, hh, GlobalTheory.HandHom.per_smul,
    inv_mul_cancel₀ hs, one_mul]

theorem rTrans_eigen {G : Type} [Group G] (a b k q : G) (F : G → ℂ) (s : ℂ) (hcm : a * k = k * a)
    (h : rTrans k (rTrans b F) = s • rTrans b F) :
    rTrans (q * k) (rTrans (a * b) F) = s • rTrans q (rTrans (a * b) F) := by
  funext g
  have := congrFun h (g * q * a)
  simp only [rTrans, Pi.smul_apply] at this ⊢
  rw [show g * (q * k) * (a * b) = g * q * a * k * b by
    rw [mul_assoc (g * q) a k, hcm]; simp only [mul_assoc], this]
  simp only [mul_assoc]

theorem vac_comb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (LS : Lat S) (LT : Lat T)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (P Q : Pl D → Prop) (hPQ : ∀ p, Q p → ¬ P p) (e : WO S T →₀ ℂ)
    (he : CombAt Q e) (f : WO S T → ℂ) (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P (comb ψ S T e f) := by
  have h0 : Vac ψ S T LS LT P f := by
    have e : (fun p : Pl D => P p ∨ ¬ P p) = fun _ => True := by
      funext p; exact propext ⟨fun _ => trivial, fun _ => em _⟩
    refine (((GlobalTheory.DisjComb.main D ψ hψ S T P (fun p => ¬ P p) (fun p hp hq => hq hp)).2.2.2.2 LS LT f hS hT).1 ?_).1
    rw [e]; exact hf
  exact ((GlobalTheory.DisjComb.main D ψ hψ S T Q P hPQ).2.1 e he).2 _ _ _ h0


set_option maxHeartbeats 1000000 in
theorem integ_mul_level : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1 + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * k) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ _ hΨ₂ φ _ G x a ha f hf k hk q₁ q₂
  have hlt : j + 1 + 1 < D.R.m := by omega
  obtain ⟨s, hs, h1, -, h3⟩ := hF.lawG (j + 1) hlt k hk
  have hom := h1 _ (vac_comb c.ψ hc.std _ _ _ _ (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) hlt) (· ∈ v.gP) (· ∈ w.Q)
    (fun p hp => Finset.disjoint_left.1 hF.disjG hp) _ (hF.atQ (j + 1)).1 Ψ₂ hΨ₂)
  have hkf : k ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ k ((hv.JG _ hlt).1 hk)
  have hr : rTrans (q₂ * k) f = s • rTrans q₂ f := by
    rw [hf]; exact rTrans_eigen a _ k q₂ _ s (comm_inf_fin _ ha hkf) (h3 G x)
  rw [← (ht.sFB j σ h).1] at hom
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (w.ε j α g * ·) (per_hand_mul (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ (φ α) g q₁ q₂ k
    s hs hom _ _ hr)

end GlobalTheory.DStepLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondOffLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepOffSnd

theorem vac_off {D : D7} {c : Comm D} (v : VCom c) {t : Tup c} (w : VTup t) (hc : c.Is) (hv : v.Is) (hw : VForm v w)
    (i : ℕ) (hi : i + 1 < D.R.m) (Ψ : WO (c.V i) (c.V (i + 1)) → ℂ)
    (hΨ : Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (fun _ => True) Ψ) :
    Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (offP v w) (comb c.ψ _ _ (v.eG i) (comb c.ψ _ _ (w.eQ i) Ψ)) := by
  have h0 : Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (offP v w) Ψ := by
    have key := (GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (offP v w) (fun p => ¬ offP v w p)
      (fun p hp hn => hn hp)).2.2.2.2 (v.N i) (v.N (i + 1)) Ψ (hv.sd i (by omega)) (hv.sd (i + 1) hi)
    have e : (fun p => offP v w p ∨ ¬ offP v w p) = fun _ => True := by
      funext p; exact eq_true (Classical.em _)
    rw [e] at key
    exact (key.1 hΨ).1
  have h1 := ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (· ∈ w.Q) (offP v w)
      (fun p hp hn => hn.2 hp)).2.1 (w.eQ i) (hw.atQ i).1).2 _ _ _ h0
  exact ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (· ∈ v.gP) (offP v w)
      (fun p hp hn => hn.1 hp)).2.1 (v.eG i) (hv.atG i).1).2 _ _ _ h1

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * κ) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hw _ hoff _ _ _ _ j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ _ G x a ha f hf κ hκ q₁ q₂
  have hΦ₁ := vac_off v w hc hv hw j (by omega) Ψ₁ hΨ₁
  have hΦ₂ := vac_off v w hc hv hw (j + 1) (by omega) Ψ₂ hΨ₂
  have hfix := (hoff j σ h _ _ hΦ₁ hΦ₂).2.1 κ hκ
  have hom : t.om (j + 1) (q₁, q₂ * κ) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      t.om (j + 1) (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    have e : ((q₁, q₂ * κ) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (q₁, q₂) * (1, κ) := by simp
    rw [e, map_mul, Module.End.mul_apply, hfix]
  have hrow : rTrans κ f = f := by
    rw [hf]; exact (hw.row (j + 1 + 1) (by omega) G x a ha).2 κ hκ
  have hr : rTrans (q₂ * κ) f = rTrans q₂ f := by
    conv_rhs => rw [← hrow]
    funext g; simp only [rTrans, mul_assoc]
  have hs := (ht.sFB j σ h).1
  have hom' : (t.sFB j σ h).om (q₁, q₂ * κ) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      (t.sFB j σ h).om (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    rw [hs]; exact hom
  unfold integ Chain.hand
  rw [hr]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (fun Z => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
    (handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α) (flatBF (t.sBF j (σ + 1) h)
      ((t.sBF j (σ + 1) h).om (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))))) (flatFB (t.sFB j σ h) Z))
      (rTrans q₂ f)) hom'

end GlobalTheory.DStepOffSnd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenomNotMemOfPrInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem mem_prime_iff_pr_inv_notMem {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.L2.NTheta.IsIdemAt p.e P) (x : 𝓞 D.host.E) (hx : x ≠ 0) :
    x ∈ P.asIdeal ↔ p.pr (incA D ((x : D.host.E)⁻¹)) ∉ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr]
  exact h.2 x hx

theorem exists_denom_notMem_of_pr_int : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ a : D.host.E, p.pr (incA D a) ∈ 𝒪[k] →
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 D.host.E,
      algebraMap (𝓞 D.host.E) D.host.E c = algebraMap (𝓞 D.host.E) D.host.E s * a := by
  intro D k _ _ _ _ p P h a ha
  obtain ⟨n, ⟨d, hd⟩, hnd | hnd⟩ := P.exists_primeCompl_mul_eq_or_mul_eq (K := D.host.E) a
  · exact ⟨d, hd, n, by rw [← hnd, mul_comm]⟩
  · have hd' : d ∉ P.asIdeal := hd
    have hd0 : d ≠ 0 := fun h0 => hd' (h0 ▸ P.asIdeal.zero_mem)
    have hnd' : a * (n : D.host.E) = (d : D.host.E) := hnd
    have hdE : (d : D.host.E) ≠ 0 := fun h0 => hd0 (RingOfIntegers.coe_eq_zero_iff.mp h0)
    have hnE : (n : D.host.E) ≠ 0 := fun h0 => hdE (by rw [← hnd', h0, mul_zero])
    have hn0 : n ≠ 0 := fun h0 => hnE (by rw [h0]; rfl)
    refine ⟨n, fun hn => ?_, d, by rw [mul_comm]; exact hnd.symm⟩
    have h1 := (mem_prime_iff_pr_inv_notMem p P h n hn0).1 hn
    have h2 := not_not.1 (mt (mem_prime_iff_pr_inv_notMem p P h d hd0).2 hd')
    apply h1
    have h3 : (n : D.host.E)⁻¹ = a * (d : D.host.E)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hdE, ← hnd', mul_comm a, inv_mul_cancel_left₀ hnE]
    rw [h3, map_mul, map_mul]
    exact mul_mem ha h2

end GlobalTheory.PhiOneVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsCombAt
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.CombAt

theorem exists_isCombAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    (Ξ : Matrix Y Y' k → ℂ) : ∃ c : WO S T →₀ ℂ, p.IsCombAt ψ FS FT c Ξ := by
  by_cases h : ∃ Φ : SB (Matrix Y Y' k), Φ.1 = Ξ
  · obtain ⟨Φ, hΦ⟩ := h
    obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
    have hne : O ≠ 0 := by
      rintro rfl
      simp at hO0
    obtain ⟨c, h1, h2⟩ := GlobalTheory.LocComb.exists_comb D k p Y Y' S T FS FT ψ hψ O Φ hne
    refine ⟨c, h1, fun Tm hT Φ₀ Φ' h₀ h' => ?_⟩
    obtain rfl : Φ' = Φ := Subtype.ext (h'.trans hΦ.symm)
    obtain rfl : Φ₀ = O := Subtype.ext (h₀.trans hO.symm)
    exact h2 Tm hT
  · exact ⟨0, by simp, fun Tm _ Φ₀ Φ _ h' => (h ⟨Φ, h'⟩).elim⟩

end GlobalTheory.LocMod.CombAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsIdemSumConjOfIsIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

namespace GlobalTheory.IdemSumConj

theorem exists_isIdemSum_cA :
    ∀ (D : D7) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q →
      ∃ Q' : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum (cA D E₂) Q' := by
  intro D P e h
  classical
  refine ⟨P.image Formalism.L2.DIV.conjPl, ?_⟩
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  refine ⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl
  · rw [Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by
      rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]
    simp only [Formalism.L2.DIV.conjPl_conjPl]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
  · rw [GlobalTheory.MovedIdem.cA_cA, mul_comm]; exact hc

end GlobalTheory.IdemSumConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocPlOff
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.LocPlInhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem exists_latInd (q : GlobalTheory.FinPl.SplitPt D k) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 0 = 1 ∧
      Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem q
  have h1 : {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} =
      (((latO S T M M' fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε q.split.1 heε h).1
    have h3 : q.e • (Witness.upH (ofSplit q) FS FT) x = (ofSplit q).up FS FT x :=
      (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (Witness.up_half (ofSplit q) FS FT x))
    rwa [h3] at h2
  rw [h1]
  have ho := Witness.lat_open (ofSplit q) FS FT hS hT
  have hk := Witness.lat_compact (ofSplit q) FS FT hS hT
  generalize ((latO S T _ _ fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) = A at ho hk
  have hcl : IsClopen (A : Set (Matrix Y Y' k)) := ⟨A.isClosed_of_isOpen ho, ho⟩
  exact ⟨⟨(A : Set (Matrix Y Y' k)).indicator 1, (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
      HasCompactSupport.intro hk fun x hx => Set.indicator_of_notMem hx _⟩, Set.indicator_of_mem A.zero_mem _, rfl⟩


end GlobalTheory.SeeSaw.LocPlInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulAnnihilatorHalfMemStandardHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfAnnStd

variable {D : D7}

theorem symplO_nsmul_swap (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := GlobalTheory.PlaceModel.symplO_smul S T (N : AE D) x y
  rwa [map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h

theorem exists_nsmul_frame_mem (S T : HSp D) : ∃ N : ℕ, 0 < N ∧
    ∀ y ∈ latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) (fun _ => True), N • y ∈ stdHom S T := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S).1.fg (GlobalTheory.PlaceModel.isSelfDualC_latFrame T).1.fg
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.AdForm.exists_nsmul_mem_stdHom S T
  refine ⟨K * M, Nat.mul_pos hK hM, fun y hy => ?_⟩
  rw [mul_smul]
  refine hKm _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, GlobalTheory.LatVac.infPart_of_mem hy i j,
      mul_zero, Matrix.zero_apply]
  · rw [Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact hden y hy i j

theorem exists_nsmul_ann_mem_stdHom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∃ N : ℕ, 0 < N ∧ ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → N • u ∈ stdHom S T := by
  intro D ψ hψ S T Q e he
  obtain ⟨N, hN, hNm⟩ := exists_nsmul_frame_mem S T
  refine ⟨N * N, Nat.mul_pos hN hN, fun u hu hann => ?_⟩
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.AnnihBox.infPart_cA' e (GlobalTheory.PlaceDatum.infPart_idemSum he)
  have hfix : cA D e • u = u := Matrix.ext fun i j => hu i j
  have hall : ∀ x ∈ stdHom S T, ψ (symplO S T x u) = 1 := fun x hx => by
    have h := hann (e • x) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hx) fun i j => by
        change e * (e * _) = e * _
        rw [← mul_assoc, hee]
    rwa [GlobalTheory.PlaceModel.symplO_smul, hfix] at h
  rw [mul_smul]
  refine hNm _ (((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1 _ (Matrix.ext fun i j => ?_)).2 fun y hy => ?_)
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, ← hu i j, RingHom.map_mul, hinf, zero_mul,
      mul_zero, Matrix.zero_apply]
  · rw [symplO_nsmul_swap, GlobalTheory.PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, hall _ (hNm y hy), inv_one]

end GlobalTheory.HalfAnnStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenFix
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.OneComb

theorem exists_open_fix' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Y : Type} [Fintype Y] [DecidableEq Y]
    (L : Level (GL Y k)) (hL : IsOpen (L.J : Set (GL Y k))) (α : GL Y k) :
    ∃ U : Subgroup (GL Y k), IsOpen (U : Set (GL Y k)) ∧ ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL Y k) A),
      IsSmoothRep σ → ∀ v : A, (∀ j : L.J, σ (j : GL Y k) v = (L.lam j : ℂ) • v) → ∀ u ∈ U, σ u (σ α v) = σ α v := by
  by_cases h : IsOpen ((L.lam.ker.map L.J.subtype : Subgroup (GL Y k)) : Set (GL Y k))
  · refine ⟨(L.lam.ker.map L.J.subtype).comap (MulAut.conj α⁻¹).toMonoidHom,
      h.preimage ((continuous_const.mul continuous_id).mul continuous_const), fun A _ _ σ _ v hv u hu => ?_⟩
    obtain ⟨j, hj, e⟩ := hu
    have e' : u * α = α * j := by
      have e2 : (j : GL Y k) = α⁻¹ * u * α⁻¹⁻¹ := e
      simp [e2, mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e', map_mul, Module.End.mul_apply, hv, show L.lam j = 1 from hj, Units.val_one, one_smul]
  · refine ⟨⊤, isOpen_univ, fun A _ _ σ hσ v hv u _ => ?_⟩
    obtain rfl : v = 0 := by
      by_contra v0
      refine h (Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
        ((hL.inter (hσ v)).mem_nhds ⟨L.J.one_mem, by simp⟩) fun g hg => ⟨⟨g, hg.1⟩, Units.ext ?_, rfl⟩))
      exact smul_left_injective ℂ v0 (((hv ⟨g, hg.1⟩).symm.trans hg.2).trans (one_smul ℂ v).symm)
    simp

theorem exists_isOneComb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ), 1 ≤ P → P ≤ c → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ ν : Measure k, IsSelfDual ψ ν → ∀ (L : Level (GL (n ⊕ Fin c) k)), IsCO L.J → ∀ α, ∃ e, IsOneComb ψ ν P L α e := by
  intro k _ _ _ _ _ _ n _ _ c P h1 hP ψ hψc hψ1 ν hν L hL α
  obtain ⟨U, hU, h⟩ := exists_open_fix' L hL.1 α
  obtain ⟨e, e', he⟩ := _root_.GlobalTheory.PosOne.toOne_uniform k n c P h1 hP ψ hψc hψ1 ν hν U hU
  refine ⟨e.mapDomain (· * α), fun A _ _ σ hσ l hl v hv => ?_⟩
  rw [(he A σ hσ l _ hl (h A σ hσ v hv)).1, GlobalTheory.PosOne.comb, GlobalTheory.PosOne.comb,
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_mul _ _ _)]
  simp only [map_mul, Module.End.mul_apply]

end GlobalTheory.QPl.OneComb
end
end

