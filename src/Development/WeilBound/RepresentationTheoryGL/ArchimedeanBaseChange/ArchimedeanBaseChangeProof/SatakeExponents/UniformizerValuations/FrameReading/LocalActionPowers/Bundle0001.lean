module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0560
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FaSlot
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.Sl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)}

def cpH (a b : ℕ) : ∀ i : Slot S, Hf E a b →* GLw a i.pl × GLw b i.pl
  | .inl w => GlobalTheory.CompanionTheory.FinLevelTw.atHom a b w.1
  | .inr w => (GlobalTheory.CompanionTheory.FinLevelTw.atHom a b w.1).comp (thP E a b)

def eH (a b : ℕ) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl →* Hf E a b
  | .inl w => (locGL E a w.1).prodMap (locGL E b w.1)
  | .inr w => (thP E a b).comp ((locGL E a w.1).prodMap (locGL E b w.1))

theorem atH_loc_self (w : Pl E) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.SuppFinTw.atH a b w ((locGL E a w m.1, locGL E b w m.2) : Hf E a b) = m :=
  Prod.ext (pLoc_locGL w m.1) (pLoc_locGL w m.2)

theorem atH_loc_ne {w v : Pl E} (h : v ≠ w) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.SuppFinTw.atH a b v ((locGL E a w m.1, locGL E b w m.2) : Hf E a b) = 1 :=
  Prod.ext (pLoc_locGL_of_ne h m.1) (pLoc_locGL_of_ne h m.2)

theorem atH_thP_loc_ne {w v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ w) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.SuppFinTw.atH a b v (thP E a b ((locGL E a w m.1, locGL E b w m.2) : Hf E a b)) = 1 := by
  have := GlobalTheory.CompanionTheory.SuppFinTw.atH_thP_congr (a := a) (b := b) (u := v) rfl
    (g := ((locGL E a w m.1, locGL E b w m.2) : Hf E a b)) (h := 1) (by rw [atH_loc_ne h, map_one])
  rw [this, map_one, map_one]

theorem cpH_eH_self (hS : IsSection S) (i : Slot S) (m : GLw a i.pl × GLw b i.pl) : cpH a b i (eH a b i m) = m := by
  rcases i with w | w
  · exact atH_loc_self w.1 m
  · exact (congrArg (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w.1) (GlobalTheory.CompanionTheory.SuppFinTw.thP_thP _)).trans (atH_loc_self w.1 m)

theorem cpH_eH_ne (hS : IsSection S) (i j : Slot S) (m : GLw a i.pl × GLw b i.pl) (h : j ≠ i) :
    cpH a b j (eH a b i m) = 1 := by
  rcases i with w | w <;> rcases j with v | v
  · exact atH_loc_ne (fun e => h (congrArg Sum.inl (Subtype.ext e))) m
  · exact atH_thP_loc_ne (w := w.1) (v := v.1)
      (fun e => GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS v.2.1 v.2.2 (e ▸ w.2)) m
  · refine atH_thP_loc_ne (w := w.1) (v := v.1) (fun e => ?_) m
    have e' : v.1 = GlobalTheory.EulerTw.cPl E w.1 := by rw [← e, GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl]
    exact GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 (e' ▸ v.2)
  · exact (congrArg (GlobalTheory.CompanionTheory.SuppFinTw.atH a b v.1) (GlobalTheory.CompanionTheory.SuppFinTw.thP_thP _)).trans
      (atH_loc_ne (fun e => h (congrArg Sum.inr (Subtype.ext e))) m)

end PositivityTheory.Rg.BcB.F.FA.Sl

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FmTermZero
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

attribute [local instance] borelG borelF borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : Pl E → Type} [∀ w, Fintype (κ w)]
  {S : Set (Pl E)} {P : Finset (Pl E)} {B : Block E} {e : B.κ ≃ ∀ w : P, κ w}

theorem fm_term_zero (hP : (↑P : Set (Pl E)) ⊆ S) {L : LM κ B.a B.b} (hL : L.Ok P) (x z : B.κ) (w : P)
    (hw : L.m w.1 (e x w) (e z w) = 0) (G : H E B.a B.b → ℂ) (y : H E B.a B.b) :
    ∫ h, fm S P B e L x z h * G (y * finH h) ∂B.ν = 0 := by
  have h0 : ∀ h, finFn S (L.ent P (e x) (e z)) L.t h = 0 := by
    intro h
    by_contra hne
    apply (GlobalTheory.CompanionTheory.FinTestTw.factors_ne_zero (hL.1 _ _) hL.2 hne w.1 (hP w.2)).1
    simp only [LM.ent, dif_pos w.2]
    exact congrFun hw _
  simp [fm, h0]

theorem fm_term_act (hS : IsSection S) (hFC : FinConv) (hFA : FinAct) {L : LM κ B.a B.b} (hL : L.Ok P) (x z : B.κ)
    (i₀ : Slot S) (G : H E B.a B.b → ℂ) (hG : HasLev G)
    (hfix : ∀ i, i ≠ i₀ → actS (L.ent P (e x) (e z)) L.t i G = G) (y : H E B.a B.b) :
    ∫ h, fm S P B e L x z h * G (y * finH h) ∂B.ν = actS (L.ent P (e x) (e z)) L.t i₀ G y := by
  have hv : B.vol ≠ 0 := (hFC E B S hS).1
  have key := hFA E B S hS (L.ent P (e x) (e z)) L.t (hL.1 _ _) hL.2 G hG [i₀] (List.nodup_singleton _)
    (fun i hi => hfix i (by simpa using hi)) y
  simp only [List.foldr_cons, List.foldr_nil] at key
  simp only [fm, mul_assoc]
  rw [integral_const_mul, key, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

end

theorem fmAtP_holds : FmAtPOf := by
  intro hFC hFA E _ _ _ κ _ S P B e hS hP A L w₀ F hL hF hQ p x
  funext y
  set g : κ w₀ → B.κ := fun t => e.symm (Function.update (e x) w₀ t) with hg
  have hginj : Function.Injective g := by
    intro t t' h
    have := congrArg (fun z => e z w₀) h
    simpa [hg] using this
  have hterm : ∀ z : B.κ, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν =
      ∑ t : κ w₀, if z = g t then actP w₀.1 (L.m w₀ (e x w₀) t) (F (p, g t)) y else 0 := by
    intro z
    by_cases hz : ∃ t, z = g t
    · obtain ⟨t, rfl⟩ := hz
      rw [Finset.sum_eq_single t (fun t' _ ht' => if_neg fun h => ht' (hginj h).symm) (by simp), if_pos rfl]
      have hez : e (g t) = Function.update (e x) w₀ t := by simp [hg]
      rw [fm_term_act hS hFC hFA hL x (g t) (Sum.inl ⟨w₀.1, hP w₀.2⟩) (F (p, g t)) (hF _) ?_ y]
      · simp only [actS, LM.ent]
        rw [hez]
        simp
      · intro i hi
        refine hQ.2 i hi p x (g t) fun w hw => ?_
        rw [hez]
        have hne : w ≠ w₀ := by
          rintro rfl
          exact hw (hP w.2) rfl
        rw [Function.update_of_ne hne]
    · rw [Finset.sum_eq_zero fun t _ => if_neg fun h => hz ⟨t, h⟩]
      have : ∃ w : P, w ≠ w₀ ∧ e x w ≠ e z w := by
        by_contra hall
        push Not at hall
        apply hz
        refine ⟨e z w₀, e.injective ?_⟩
        simp only [hg, Equiv.apply_symm_apply]
        funext w
        by_cases hw : w = w₀
        · subst hw; simp
        · rw [Function.update_of_ne hw]; exact (hall w hw).symm
      obtain ⟨w, hw, hne⟩ := this
      refine fm_term_zero hP hL x z w ?_ _ y
      refine hQ.1 w.1 w.2 (fun h hh => ?_) _ _ hne
      apply hw
      apply Subtype.ext
      have := congrArg Slot.pl hh
      simpa [Slot.pl] using this.symm
  show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_comm]
  simp [Finset.sum_ite_eq', hg]

theorem fmOff_holds : FmOffOf := by
  intro hFC hFA E _ _ _ κ _ S P B e hS hP A L i₀ F hL hF hoff hQ p x
  funext y
  show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _
  rw [Finset.sum_eq_single x]
  · rw [fm_term_act hS hFC hFA hL x x i₀ (F (p, x)) (hF _) (fun i hi => hQ.2 i hi p x x fun _ _ => rfl) y]
    rcases i₀ with ⟨w, hw⟩ | ⟨w, hw⟩
    · have hwP : w ∉ P := fun h => hoff w h hw rfl
      simp [actS, LM.ent, dif_neg hwP]
    · rfl
  · intro z _ hz
    have : ∃ w : P, e x w ≠ e z w := by
      by_contra hall
      push Not at hall
      exact hz (e.injective (funext hall)).symm
    obtain ⟨w, hne⟩ := this
    exact fm_term_zero hP hL x z w (hQ.1 w.1 w.2 (hoff w.1 w.2) _ _ hne) _ y
  · simp

end PositivityTheory.Rg.BcB.F.FA

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Pfmone
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

section Gen

set_option linter.unusedSectionVars false

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [FirstCountableTopology Γ] [LocallyCompactSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (ν : Measure Γ) [ν.IsHaarMeasure]

theorem cont_of_rinv {f : Γ → ℂ} {U : Subgroup Γ} (hU : IsOpen (U : Set Γ)) (hf : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  refine (continuousAt_const (y := f g)).congr ?_
  have hm : {y : Γ | g⁻¹ * y ∈ U} ∈ 𝓝 g :=
    (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [U.one_mem])
  filter_upwards [hm] with y hy
  have := hf _ hy g
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem cont_convL {φ₁ φ₂ : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂) :
    Continuous fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
  have e : (fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) = fun g => ∫ h in tsupport φ₁, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
    funext g
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hh, zero_mul]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ s₁.isCompact
  exact (h₁.comp continuous_snd).mul (h₂.comp (continuous_snd.inv.mul continuous_fst))

theorem supp_convL {φ₁ φ₂ : Γ → ℂ} (s₁ : HasCompactSupport φ₁) (s₂ : HasCompactSupport φ₂) :
    HasCompactSupport fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
  refine HasCompactSupport.intro (s₁.isCompact.mul s₂.isCompact) fun g hg => ?_
  have : ∀ h, φ₁ h * φ₂ (h⁻¹ * g) = 0 := by
    intro h
    by_cases h1 : h ∈ tsupport φ₁
    · have h2 : h⁻¹ * g ∉ tsupport φ₂ := fun h2 => hg (Set.mem_mul.2 ⟨h, h1, h⁻¹ * g, h2, mul_inv_cancel_left h g⟩)
      rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  simp [this]

theorem cont_convR {φ₂ f : Γ → ℂ} (h₂ : Continuous φ₂) (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Continuous fun h => ∫ k, φ₂ k * f (h * k) ∂ν := by
  have e : (fun h => ∫ k, φ₂ k * f (h * k) ∂ν) = fun h => ∫ k in tsupport φ₂, φ₂ k * f (h * k) ∂ν := by
    funext h
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hk, zero_mul]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ s₂.isCompact
  exact (h₂.comp continuous_snd).mul (hf.comp (continuous_fst.mul continuous_snd))

theorem int_L {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Integrable (fun g => (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g) ν :=
  ((cont_convL ν h₁ s₁ h₂).mul hf).integrable_of_hasCompactSupport ((supp_convL ν s₁ s₂).mul_right)

theorem int_R {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Integrable (fun h => φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν) ν :=
  (h₁.mul (cont_convR ν h₂ s₂ hf)).integrable_of_hasCompactSupport s₁.mul_right

theorem swap_key {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    ∫ g, (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g ∂ν = ∫ h, φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν ∂ν := by
  have hc : Continuous (Function.uncurry fun g h : Γ => φ₁ h * φ₂ (h⁻¹ * g) * f g) :=
    ((h₁.comp continuous_snd).mul (h₂.comp (continuous_snd.inv.mul continuous_fst))).mul (hf.comp continuous_fst)
  have hs : HasCompactSupport (Function.uncurry fun g h : Γ => φ₁ h * φ₂ (h⁻¹ * g) * f g) := by
    refine HasCompactSupport.intro ((s₁.isCompact.mul s₂.isCompact).prod s₁.isCompact) fun p hp => ?_
    show φ₁ p.2 * φ₂ (p.2⁻¹ * p.1) * f p.1 = 0
    by_cases h1 : p.2 ∈ tsupport φ₁
    · have h2 : p.2⁻¹ * p.1 ∉ tsupport φ₂ := fun h2 =>
        hp ⟨Set.mem_mul.2 ⟨p.2, h1, p.2⁻¹ * p.1, h2, mul_inv_cancel_left p.2 p.1⟩, h1⟩
      rw [image_eq_zero_of_notMem_tsupport h2, mul_zero, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  calc ∫ g, (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g ∂ν
      = ∫ g, ∫ h, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ h, ∫ g, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν ∂ν := integral_integral_swap_of_hasCompactSupport hc hs
    _ = ∫ h, φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        have e1 := integral_mul_left_eq_self (μ := ν) (fun g => φ₂ (h⁻¹ * g) * f g) h
        simp only [inv_mul_cancel_left] at e1
        show ∫ g, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν = φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν
        rw [e1, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        show φ₁ h * φ₂ (h⁻¹ * g) * f g = φ₁ h * (φ₂ (h⁻¹ * g) * f g)
        ring

end Gen

theorem finH_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (g h : Hf E a b) :
    finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

attribute [local instance] borelG borelF borelH

theorem convMul_holds : Tail.ConvMul := by
  set_option synthInstance.maxHeartbeats 400000 in
  intro E _ _ _ B A ψ ψ' U F hψ hψ' hU hF
  have := B.hν
  have : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  refine ⟨?_, ?_⟩
  · funext i X
    obtain ⟨p, x₀⟩ := i
    have hfc : ∀ z, Continuous fun g => F (p, z) (X * finH g) := by
      intro z
      refine cont_of_rinv hU fun u hu g => ?_
      rw [finH_mul', ← mul_assoc, hF _ u hu]
    simp only [convF, mulF]
    calc ∑ z, ∫ g, (∑ w, ∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν
        = ∑ z, ∑ w, ∫ g, (∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν := by
          refine Finset.sum_congr rfl fun z _ => ?_
          simp_rw [Finset.sum_mul]
          exact integral_finsetSum _ fun w _ =>
            int_L B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)
      _ = ∑ w, ∑ z, ∫ g, (∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν :=
          Finset.sum_comm
      _ = ∑ w, ∑ z, ∫ h, ψ x₀ w h * ∫ k, ψ' w z k * F (p, z) (X * finH h * finH k) ∂B.ν ∂B.ν := by
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
          rw [swap_key B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)]
          simp only [finH_mul', mul_assoc]
      _ = ∑ w, ∫ h, ψ x₀ w h * ∑ z, ∫ k, ψ' w z k * F (p, z) (X * finH h * finH k) ∂B.ν ∂B.ν := by
          refine Finset.sum_congr rfl fun w _ => ?_
          simp_rw [Finset.mul_sum]
          refine (integral_finsetSum _ fun z _ => ?_).symm
          have := int_R B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)
          simpa only [finH_mul', mul_assoc] using this
  · intro hψU i u hu x
    simp only [convF]
    refine Finset.sum_congr rfl fun z _ => ?_
    have e := integral_mul_left_eq_self (μ := B.ν) (fun k => ψ' i.2 z k * F (i.1, z) (x * finH k)) u
    simp only [hψU _ _ u hu, finH_mul', ← mul_assoc] at e
    exact e

theorem fmOneOf_holds : FmOneOf := by
  intro hOff hIdem E _ _ _ κ _ S P B e hS hP U₁ U₂ L A F w₀ hU₁ hU₂ hL hD hF hw₀
  have hLev : ∀ i, HasLev (F i) := fun i => (hF i).1

  have hxy : ∀ x y : B.κ, (∀ w : P, e x w = e y w) → x = y := fun x y h => e.injective (funext h)

  have hent : ∀ (x : B.κ) (w : Pl E), (w ∉ P → L.s w = idem (U₁ w)) → L.ent P (e x) (e x) w = idem (U₁ w) := by
    intro x w hw
    unfold LM.ent
    split_ifs with h
    · rw [hD w h]; simp
    · exact hw h
  have hP1 : ∀ (w : Pl E) (G : H E B.a B.b → ℂ), w ∈ S → HasLev G → G ∈ fixed (pairRt B.a B.b w) (U₁ w) →
      actP w (idem (U₁ w)) G = G := fun w G _ hG hfx =>
    ((hIdem E B.a B.b w (U₁ w) G (hU₁.1 w).1 (hU₁.1 w).2 hG).1).2 hfx
  have hT1 : ∀ (w : Pl E) (G : H E B.a B.b → ℂ), HasLev G → G ∈ fixed (pairRtT B.a B.b w) (U₂ w) →
      actT w (idem (U₂ w)) G = G := fun w G hG hfx =>
    ((hIdem E B.a B.b w (U₂ w) G (hU₂.1 w).1 (hU₂.1 w).2 hG).2).2 hfx
  refine ⟨fun hw₀P hs ht i => ?_, fun hsp hs ht i => ?_⟩
  · have hne : ∀ w ∈ P, ∀ h : w ∈ S, (Sum.inl ⟨w₀, hw₀⟩ : Slot S) ≠ Sum.inl ⟨w, h⟩ := by
      intro w hwP h heq
      have : w₀ = w := congrArg Subtype.val (Sum.inl_injective heq)
      exact hw₀P (this ▸ hwP)
    have hQ : Quiet S P B e L (Sum.inl ⟨w₀, hw₀⟩) F := by
      refine ⟨fun w hwP hw x y hxy' => ?_, fun j hj p x y hxe => ?_⟩
      · rw [hD w hwP, if_neg hxy']
      · have hx : x = y := hxy x y fun w => hxe w fun h => hne w.1 w.2 h
        subst hx
        rcases j with ⟨w, hwS⟩ | ⟨w, hwS, hwsp⟩
        · have hww : w ≠ w₀ := fun h => hj (by subst h; rfl)
          show actP w (L.ent P (e x) (e x) w) (F (p, x)) = F (p, x)
          rw [hent x w fun _ => hs w hww]
          exact hP1 w _ hwS (hLev _) ((hF _).2 w hwS).1
        · show actT w (L.t w) (F (p, x)) = F (p, x)
          rw [ht w]
          exact hT1 w _ (hLev _) (((hF _).2 w hwS).2 hwsp)
    obtain ⟨p, x⟩ := i
    exact hOff E κ S P B e hS hP A L (Sum.inl ⟨w₀, hw₀⟩) F hL hLev hne hQ p x
  · have hne : ∀ w ∈ P, ∀ h : w ∈ S, (Sum.inr ⟨w₀, hw₀, hsp⟩ : Slot S) ≠ Sum.inl ⟨w, h⟩ := by
      intro w _ h heq
      cases heq
    have hQ : Quiet S P B e L (Sum.inr ⟨w₀, hw₀, hsp⟩) F := by
      refine ⟨fun w hwP hw x y hxy' => ?_, fun j hj p x y hxe => ?_⟩
      · rw [hD w hwP, if_neg hxy']
      · have hx : x = y := hxy x y fun w => hxe w fun h => hne w.1 w.2 h
        subst hx
        rcases j with ⟨w, hwS⟩ | ⟨w, hwS, hwsp⟩
        · show actP w (L.ent P (e x) (e x) w) (F (p, x)) = F (p, x)
          rw [hent x w fun _ => hs w]
          exact hP1 w _ hwS (hLev _) ((hF _).2 w hwS).1
        · have hww : w ≠ w₀ := fun h => hj (by subst h; rfl)
          show actT w (L.t w) (F (p, x)) = F (p, x)
          rw [ht w hww]
          exact hT1 w _ (hLev _) (((hF _).2 w hwS).2 hwsp)
    obtain ⟨p, x⟩ := i
    exact hOff E κ S P B e hS hP A L (Sum.inr ⟨w₀, hw₀, hsp⟩) F hL hLev hne hQ p x

end PositivityTheory.Rg.BcB.F.FA

end
end

