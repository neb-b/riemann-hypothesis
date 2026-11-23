module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawCommonRealDatumBiThetaVacuumContraction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VReal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem biTheta_add {A S A' : HSp D} {f g : WO A S → WO S A' → ℂ} (hf : IsBiTheta ψ A S A' f)
    (hg : IsBiTheta ψ A S A' g) : IsBiTheta ψ A S A' (f + g) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · intro n L L' hL hL' hLf hL'f u v
    exact (hf.smooth n L L' hL hL' hLf hL'f u v).add (hg.smooth n L L' hL hL' hLf hL'f u v)
  · simp only [Pi.add_apply]; rw [hf.quasiL, hg.quasiL]; ring
  · simp only [Pi.add_apply]; rw [hf.quasiR, hg.quasiR]; ring
  · obtain ⟨U, hU, hUf⟩ := hf.levL
    obtain ⟨V, hV, hVf⟩ := hg.levL
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    funext u
    have h1 := congrFun (hUf a ha.1 ha' v) u
    have h2 := congrFun (hVf a ha.2 ha' v) u
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  · obtain ⟨U, hU, hUf⟩ := hf.levR
    obtain ⟨V, hV, hVf⟩ := hg.levR
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    funext v
    have h1 := congrFun (hUf a ha.1 ha' u) v
    have h2 := congrFun (hVf a ha.2 ha' u) v
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]

theorem biTheta_zero {A S A' : HSp D} : IsBiTheta ψ A S A' 0 := by
  refine ⟨?_, fun n L L' _ _ _ _ u v => ?_, fun γ u v => by simp, fun γ u v => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ v => ?_⟩,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ u => ?_⟩⟩
  · simp only [Pi.zero_apply]; exact continuous_const
  · simp only [Pi.zero_apply]; exact contDiff_const
  · funext x; simp [heisO]
  · funext x; simp [heisO]

theorem biTheta_app (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} (o : BiOp A S A')
    (ho : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i)) {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) :
    IsBiTheta ψ A S A' (o.app ψ C) := by
  unfold BiOp.app
  exact Finset.sum_induction _ (IsBiTheta ψ A S A') (fun f g hf hg => biTheta_add hf hg) biTheta_zero
    fun i _ => GlobalTheory.FrComb.biTheta_combL hψ (GlobalTheory.FrComb.biTheta_combR hψ hC (ho i).2) (ho i).1

theorem heisO_add {S T : HSp D} (w : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T w (f + g) = heisO ψ S T w f + heisO ψ S T w g := by
  funext x; simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_zero {S T : HSp D} (w : WO S T) : heisO ψ S T w 0 = 0 := by
  funext x; simp [heisO]

theorem latVac_add {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f)
    (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f + g) :=
  ⟨fun u hu => by rw [heisO_add, hf.1 u hu, hg.1 u hu],
    fun e he u hu hh => by rw [heisO_add, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩

theorem latVac_zero {S T : HSp D} {Λ : AddSubgroup (WO S T)} : IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun u _ => heisO_zero _, fun _ _ u _ _ => heisO_zero u⟩

theorem latVac_sum {S T : HSp D} {Λ : AddSubgroup (WO S T)} {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, IsLatVac (heisO ψ S T) Λ (F i)) : IsLatVac (heisO ψ S T) Λ (∑ i ∈ s, F i) :=
  Finset.sum_induction _ _ (fun _ _ hf hg => latVac_add hf hg) latVac_zero h

def combEnd (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : Module.End ℂ (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext u; simp only [GlobalTheory.FrComb.comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext u
    simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

theorem vac_of_true {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {f : WO S T → ℂ}
    (h : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v hv => absurd trivial hv, rest⟩
  unfold Vac IsLatVac at h ⊢
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem vac_union (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (P : Pl D → Prop) (LS : Lat S) (LT : Lat T) (f : WO S T → ℂ)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (h1 : Vac ψ S T LS LT P f) (h2 : Vac ψ S T LS LT (fun p => ¬ P p) f) :
    Vac ψ S T LS LT (fun _ => True) f := by
  have H := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun p => ¬ P p) (fun p hp hq => hq hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => P p ∨ ¬ P p) = fun _ => True := funext fun p => propext ⟨fun _ => trivial, fun _ => em _⟩
  have h3 := H.2 ⟨h1, h2⟩
  rwa [e] at h3

theorem real_of (hψ : IsStdChar D ψ (-1)) (P : Pl D → Prop)
    (hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt P e → IsFinComb e ∧
      ∀ LS LT f, Vac ψ S T LS LT (fun p => ¬ P p) f → Vac ψ S T LS LT (fun p => ¬ P p) (comb ψ S T e f))
    {A S A' : HSp D} {LA : Lat A} {LS : Lat S} {LA' : Lat A'} (hA : IsSelfDualC A LA) (hS : IsSelfDualC S LS)
    (hA' : IsSelfDualC A' LA') (o : BiOp A S A') (ho : ∀ i, CombAt P (o.u i) ∧ CombAt P (o.u' i))
    {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) (hoff : BiVacAt ψ LA LS LA' (fun p => ¬ P p) C)
    (hon : BiVacAt ψ LA LS LA' P (o.app ψ C)) :
    IsBiTheta ψ A S A' (o.app ψ C) ∧ IsBiVac ψ A S A' LA LS LA' (o.app ψ C) ∧ IsBiSmooth (o.app ψ C) := by
  have hfin : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i) :=
    fun i => ⟨(hcomb _ _ _ (ho i).1).1, (hcomb _ _ _ (ho i).2).1⟩
  have hB := biTheta_app hψ o hfin hC
  have hoffApp : BiVacAt ψ LA LS LA' (fun p => ¬ P p) (o.app ψ C) := by
    refine ⟨fun v => ⟨GlobalTheory.FrComb.slice_left hB v, ?_⟩, fun u => ⟨GlobalTheory.FrComb.slice_right hB u, ?_⟩⟩
    · have e : (fun u => o.app ψ C u v) = ∑ i, fun u => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext u; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      have hR := GlobalTheory.FrComb.biTheta_combR hψ hC (hfin i).2
      have hg : Vac ψ A S LA LS (fun p => ¬ P p) (fun u' => comb ψ S A' (o.u' i) (C u') v) :=
        ⟨GlobalTheory.FrComb.slice_left hR v, GlobalTheory.FrComb.latVac_opR (fun v => (hoff.1 v).2) (combEnd ψ S A' (o.u' i)) v⟩
      exact ((hcomb _ _ _ (ho i).1).2 LA LS _ hg).2
    · have e : o.app ψ C u = ∑ i, fun v => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext v; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      exact GlobalTheory.FrComb.latVac_opL (K := fun u' => comb ψ S A' (o.u' i) (C u'))
        (fun u' => ((hcomb _ _ _ (ho i).2).2 LS LA' _ (hoff.2 u')).2) (combEnd ψ A S (o.u i)) u
  have hT : BiVacAt ψ LA LS LA' (fun _ => True) (o.app ψ C) :=
    ⟨fun v => vac_union hψ _ _ P _ _ _ hA hS (hon.1 v) (hoffApp.1 v),
      fun u => vac_union hψ _ _ P _ _ _ hS hA' (hon.2 u) (hoffApp.2 u)⟩
  exact ⟨hB, ⟨hB.cont, fun v => hT.1 v, fun u => hT.2 u⟩, hB.smooth⟩

theorem v_real : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VacLaw (t := t) v → TLaw v w → FlatLaw D → (∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) ∧ ∀ j h Ψ₁ Ψ₂, WeilOK (t := t) v → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  intro D c v t w hc hv ht hV hT hF
  have hψ := hc.std
  have hfl := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hF c.ψ
  have hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt (· ∈ v.tP) e → IsFinComb e ∧
      ∀ LS LT f, Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) f → Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) (comb c.ψ S T e f) :=
    fun S T e he => (GlobalTheory.DisjComb.main D c.ψ hψ S T (· ∈ v.tP) (fun p => ¬ p ∈ v.tP) (fun p hp hq => hq hp)).2.1 e he
  refine ⟨fun j σ h Ψ₁ Ψ₂ h1 h2 => ?_, fun j h Ψ₁ Ψ₂ hW h1 h2 => ?_⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) :=
      (GlobalTheory.ContrComb.contr_comb_main D c.ψ hψ (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
        (c.vL j σ h) (flatBF (t.sBF j (σ + 1) h) Ψ₁) (flatFB (t.sFB j σ h) Ψ₂)
        (hfl.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) Ψ₁ h1.1)
        (hfl.2 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) Ψ₂ h2.1)).1
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) :=
      GlobalTheory.LastBiTheta.isBiTheta_lastBi D c.ψ hψ _ _ _ _ _ _ _ (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (hW.tau j h).2 (flatBF (t.sBF j 0 h) Ψ₁) (fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w))
        (hfl.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) Ψ₁ h1.1) ((GlobalTheory.WeilSrc.Zero.theta_iff (c.jac j 0 h).d Ψ₂).2 h2.1)
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩

end GlobalTheory.VReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFlatMapContractionSupportAtLevelPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw.PlaceSupp

theorem supp_ctr : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp2 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F₁ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F₁ → ∀ (F₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ), Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = Gi.q.v) F₂ → ∀ (x : GA D (c.V (j + 1 + 1))), SuppAt Gi.q.e (c.V (j + 1 + 1)) x → c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (Gi.eg j) F₁) (t.om (j + 1) (1, x) (comb c.ψ _ _ (Gi.eg (j + 1)) F₂)) ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, SuppAt Gi.q.e (c.V (j + 1 + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  intro D c v hc hv hG t ht Gi hch j σ h F₁ hF₁ F₂ hF₂ x hx hne
  have hs := Gi.hs
  obtain ⟨μ, hμ, hμu, -, h2⟩ := hch
  obtain ⟨hPhi, hLev⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq Gi.k _ _ Gi.S (Fin D.R.t) μ hμ hμu
  have a₀ : j + (2 * σ + 1 + 1 + 1) = Gi.s + 1 := by omega
  have a₁ : j + 1 + (2 * σ + 1 + 1) = Gi.s + 1 := by omega
  have a₂ : j + 1 + 1 + (2 * σ + 1) = Gi.s + 1 := by omega
  have b₀ : j + (2 * σ + 1 + 1) = Gi.s := by omega
  have b₁ : j + 1 + (2 * σ + 1) = Gi.s := by omega
  obtain ⟨T₁, hT₁, hO₁⟩ := (_root_.GlobalTheory.LocMod.indicator_vac D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1)) (Gi.FY j _ a₀) (Gi.FY (j + 1) _ a₁)
    c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (Gi.latY j _ a₀) (Gi.latY (j + 1) _ a₁)).2 F₁ hF₁
  obtain ⟨T₂, hT₂, hO₂⟩ := (_root_.GlobalTheory.LocMod.indicator_vac D Gi.k Gi.q Gi.unit _ _ (c.V (j + 1)) (c.V (j + 1 + 1)) (Gi.FY (j + 1) _ a₁)
    (Gi.FY (j + 1 + 1) _ a₂) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N (j + 1)) (v.N (j + 1 + 1)) (hv.sd (j + 1) (by omega))
    (hv.sd (j + 1 + 1) (by omega)) (Gi.latY (j + 1) _ a₁) (Gi.latY (j + 1 + 1) _ a₂)).2 F₂ hF₂
  obtain ⟨O₁, h1⟩ := GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  obtain ⟨O₂, h1'⟩ := GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1) ⊕ Fin (2 * σ + 1))
    (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
  have m₁ : (Gi.S.T (Fin D.R.t)).Phi j _ b₀ ∈ GlobalTheory.SplitWeil.SB _ := (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 j _ b₀
  have m₂ : (Gi.S.T (Fin D.R.t)).Phi (j + 1) _ b₁ ∈ GlobalTheory.SplitWeil.SB _ :=
    (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 (j + 1) _ b₁
  have e₁ := (Gi.eg_is j _ b₀).2 T₁ hT₁ O₁ ⟨_, m₁⟩ h1 rfl
  have e₂ := (Gi.eg_is (j + 1) _ b₁).2 T₂ hT₂ O₂ ⟨_, m₂⟩ h1' rfl
  rw [hO₁ O₁ h1] at e₁
  rw [hO₂ O₂ h1'] at e₂
  rw [← e₁, ← e₂, ← (ht.sFB j σ h).1] at hne
  let F : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1)) (2 * σ) :=
    { s := Gi.sc j
      s_ne := fun h0 => by
        have h3 := Gi.sc_unit j
        rw [h0, map_zero] at h3
        exact zero_ne_one h3
      F₀ := Gi.FX j (by omega)
      F₁ := Gi.FX (j + 1) (by omega)
      F₂ := Gi.FX (j + 1 + 1) (by omega)
      G₀ := Gi.FY j _ a₀
      G₁ := Gi.FY (j + 1) _ a₁
      G₂ := Gi.FY (j + 1 + 1) _ a₂
      bes := Gi.bes j (σ + 1) h _ a₀
      jac := Gi.jac j (σ + 1) h _ a₁
      bes' := by
        rw [← Gi.sc_step j]
        exact Gi.bes (j + 1 + 1) σ (idx_step h) _ a₂ }
  obtain ⟨r, hr, hrs, u, uk, hu, huk, hxr⟩ := hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμ) (Fin D.R.t) c.ψ
    Gi.char j (2 * σ) (by omega) σ _ _ _ F (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (h2 j σ h).1
    T₁ T₂ hT₁ hT₂ ⟨_, m₁⟩ ⟨_, m₂⟩ (hPhi j _ b₀).symm (hPhi (j + 1) _ b₁).symm x hx hne
  rw [(hLev (j + 1 + 1) _ a₂).1] at huk
  exact ⟨r, hr, hrs, u, uk, hu, huk, hxr⟩

end GlobalTheory.SeeSaw.PlaceSupp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawRhs

variable {D : D7}

theorem latO_mono (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hv' => hv v (fun hp => hv' (h v hp)), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono S T _ _ h hu),
    fun e he u hu hh => hf.2.2 e he u (latO_mono S T _ _ h hu) hh⟩

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : idAt D P ≤ idAt D P' := by
  intro x hx
  simp only [idAt, Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) {S T : HSp D} {c : WO S T →₀ ℂ}
    (hc : CombAt P c) : CombAt P' c := fun u hu i j => idAt_mono h (hc u hu i j)

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ x ∈ c.support, c x * (ψ (symplOH S T w x) * f (w + x)) := by
  simp [comb, heisO, Finset.sum_apply]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (a • C) = a • biComb ψ A S A' c c' C := by
  funext u v
  simp only [biComb, Pi.smul_apply, smul_eq_mul, comb_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem comb_comm2 (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (e : WO A S →₀ ℂ) (d' : WO S A' →₀ ℂ)
    (G : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' d' (fun v' => comb ψ A S e (fun u'' => G u'' v') u) v =
      comb ψ A S e (fun u'' => comb ψ S A' d' (G u'') v) u := by
  simp only [comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem biComb_biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (d e : WO A S →₀ ℂ) (d' e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    biComb ψ A S A' d d' (biComb ψ A S A' e e' C) u v =
      comb ψ A S d (comb ψ A S e (fun u'' => comb ψ S A' d' (comb ψ S A' e' (C u'')) v)) u := by
  simp only [biComb]
  congr 1
  funext u'
  exact comb_comm2 ψ A S A' e d' (fun u'' v' => comb ψ S A' e' (C u'') v') u' v

theorem biLift_smul {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS φ (a • C) = a • biLift oma omb vA vS φ C := by
  funext h₂
  have h1 : ∀ h₀ h₁ v, oma (h₀, h₁) (fun u => a * C u v) 0 = a * oma (h₀, h₁) (fun u => C u v) 0 := by
    intro h₀ h₁ v
    rw [show (fun u => a * C u v) = a • (fun u => C u v) from rfl, map_smul]
    rfl
  have h2 : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) 0 =
      a * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 := by
    intro h₀ h₁
    have e : (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) = a • (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
      funext fun v => h1 h₀ h₁ v
    rw [e, map_smul]
    rfl
  simp only [biLift, Pi.smul_apply, smul_eq_mul, h2]
  simp_rw [show ∀ x y : ℂ, x * (a * y) = a * (x * y) from fun x y => mul_left_comm x a y, integral_const_mul]

theorem theta_comb_left {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} (Y : WO A S → WO S A' → ℂ)
    (hY : ∀ v, IsThetaFunO ψ A S (fun u => Y u v)) (c : WO S A' →₀ ℂ) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => comb ψ S A' c (Y u) v) := by
  classical
  have key : ∀ s : Finset (WO S A'),
      IsThetaFunO ψ A S (fun u => ∑ x ∈ s, c x * (ψ (symplOH S A' v x) * Y u (v + x))) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact Formalism.IndefR.Fock.CCR.theta_zero ψ A S
    · intro x s hx ih
      have := Formalism.IndefR.Fock.CCR.theta_add_smul ih (hY (v + x)) (c x * ψ (symplOH S A' v x))
      convert this using 1
      funext u
      simp only [Finset.sum_insert hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  simpa only [comb_apply] using key c.support

end GlobalTheory.SeeSawRhs

namespace GlobalTheory.SeeSawRhs

theorem unfolded_eq_kernel_data : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → GValue (t := t) v → TLaw v w → FlatLaw D → BiAct D → ∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ β, (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂)))) = (v.cG j * w.cT j) • t.two j (fun α => v.Sad j (φ α)) ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) β := by
  intro D c v t w hc hv _ hF hG hT _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ β
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  have top : ∀ (P : Pl D → Prop) p, P p → True := fun _ _ _ => trivial
  simp only [Comm.bl]
  rw [hG.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)]
  obtain ⟨hBV, hTL⟩ := hT.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)
  simp only [Comm.bl] at hTL
  set X₀ := c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ with hX₀
  set Y := (v.op j).app c.ψ X₀ with hY
  have hQG : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.mp hF.disjG hp
  have hoff : ∀ p, (p ∈ w.Q ∨ p ∈ v.gP) → p ∉ v.tP := by
    rintro p (hp | hp)
    · exact Finset.disjoint_left.mp hF.disjT hp
    · exact Finset.disjoint_left.mp hv.disj hp
  have prod := fun (S T : HSp D) => (_root_.GlobalTheory.DisjComb.main D c.ψ hc.std S T (· ∈ w.Q) (· ∈ v.gP) hQG).2.2.2.1
  unfold Tup.two
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  obtain ⟨d₁, hd₁, ed₁⟩ := prod _ _ (w.dQ j α γ) (v.dG j)
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ j).2.2 α γ)) (combAt_mono (fun p hp => Or.inr hp) (hv.atG j).2.1)
  obtain ⟨d₂, hd₂, ed₂⟩ := prod _ _ (w.dQ (j + 1) γ β) (v.dG (j + 1))
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ (j + 1)).2.2 γ β))
    (combAt_mono (fun p hp => Or.inr hp) (hv.atG (j + 1)).2.1)
  have e1 : biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) X₀) =
      biComb c.ψ _ _ _ d₁ d₂ X₀ := by
    funext u v'
    rw [biComb_biComb]
    simp only [biComb, ed₁, ed₂]
  have e2 : biComb c.ψ _ _ _ d₁ d₂ (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) Y) =
      biComb c.ψ _ _ _ (t.dd j α γ) (t.dd (j + 1) γ β) Y := by
    funext u v'
    rw [biComb_biComb, ed₁]
    have hF' : (fun u'' => comb c.ψ _ _ d₂ (comb c.ψ _ _ (v.dT (j + 1)) (Y u'')) v') =
        fun u'' => comb c.ψ _ _ (t.dd (j + 1) γ β) (Y u'') v' := by
      funext u''
      rw [ed₂, ← hF.dd (j + 1) hj1 γ β _ (hBV.2 u'').1]
    rw [hF', ← hF.dd j hj α γ _ (theta_comb_left Y (fun v'' => (hBV.1 v'').1) _ v')]
    rfl
  rw [biComb_smul, biLift_smul, e1, hTL d₁ d₂ (combAt_mono hoff hd₁) (combAt_mono hoff hd₂) (φ α) (hφ α), e2,
    smul_smul]

end GlobalTheory.SeeSawRhs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GSuppFirst

theorem gsupp1_at : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  intro D c v hc hv hG t ht Gi hch j σ h F hF x hx hflat
  have hs := Gi.hs
  obtain ⟨Tm, hTm, hTmO⟩ := (_root_.GlobalTheory.LocMod.indicator_vac D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1))
    (Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)) (Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond
    (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Gi.latY j _ _) (Gi.latY (j + 1) _ _)).2 F hF
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Gi.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  have H2 : j + (2 * σ + 1 + 1) = Gi.s := by omega
  let Φ : GlobalTheory.SplitWeil.SB _ := ⟨_, (GModel.phi_sb Gi).1 j (2 * σ + 1 + 1) H2⟩
  have hcomb : Tm Φ = comb c.ψ _ _ (Gi.eg j) F := by
    rw [← hTmO O hO]; exact (Gi.eg_is j (2 * σ + 1 + 1) H2).2 Tm hTm O Φ hO rfl
  obtain ⟨μ, hμt, hμu, hBF, -⟩ := hch
  have hW := MuUnits.withMu_eq Gi.k Gi.s D.R.k Gi.S (Fin D.R.t) μ hμt hμu
  let Fd : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1)) (2 * σ) :=
    { s := Gi.sc j
      s_ne := fun h0 => by have := Gi.sc_unit j; rw [h0, map_zero] at this; exact zero_ne_one this
      F₀ := Gi.FX j (by omega)
      F₁ := Gi.FX (j + 1) (by omega)
      F₂ := Gi.FX (j + 1 + 1) (by omega)
      G₀ := Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)
      G₁ := Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)
      G₂ := Gi.FY (j + 1 + 1) (2 * σ + 1) (by omega)
      bes := Gi.bes j (σ + 1) h _ _
      jac := Gi.jac j (σ + 1) h _ _
      bes' := by rw [← Gi.sc_step j]; exact Gi.bes (j + 1 + 1) σ (idx_step h) _ _ }
  have hΦ : Φ.1 = ((withMu Gi.S μ hμt).T (Fin D.R.t)).Phi j (2 * σ + 1 + 1) (by omega) := (hW.1 j _ _).symm
  have hflat' : flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (1, x) (Tm Φ)) ≠ 0 := by
    rw [(ht.sBF j (σ + 1) h).1, hcomb]; exact hflat
  obtain ⟨r, hr, hrs, u, uk, hloc, huk, hxr⟩ := hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμt) (Fin D.R.t) c.ψ
    Gi.char j (2 * σ) (by omega) σ _ _ _ Fd (t.sBF j (σ + 1) h) (hBF j (σ + 1) h).1 Tm hTm Φ hΦ x hx hflat'
  refine ⟨r, hr, hrs, u, uk, hloc, ?_, hxr⟩
  rw [← (hW.2 (j + 1) (2 * σ + 1 + 1) (by omega)).1]; exact huk

end GlobalTheory.SeeSaw.GSuppFirst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLinearModelGLPairApplyMemSchwartzBruhatFu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitWeil.ValOne

theorem om_val_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a]
    [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)),
    om μ g h Φ.1 ∈ SB (Matrix b a k) :=
  fun _ _ _ _ _ _ _ _ _ _ _ μ g h Φ => GlobalTheory.SplitWeil.om_mem_SB μ g h Φ.2

end GlobalTheory.SplitWeil.ValOne
end

