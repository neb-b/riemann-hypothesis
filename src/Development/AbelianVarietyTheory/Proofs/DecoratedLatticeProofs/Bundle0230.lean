module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepIteratedQuotientIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.Assemble

section Quot

variable {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}

theorem quotient_integral_finset_sum_eq {ι : Type} (s : Finset ι) (F : ι → G → ℂ) (Z : ι → ℂ)
    (hF : ∀ i ∈ s, IsQuotIntL1 μR μG (F i) (Z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i ∈ s, F i x) (∑ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsQuotIntL1.zero
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have h3 := h1.add h2
    rw [Finset.sum_insert ha]
    convert h3 using 1
    funext x
    rw [Finset.sum_insert ha]
    rfl

theorem quotient_integral_finset_sum_smul {ι : Type} (s : Finset ι) (a : ι → ℂ) (F : ι → G → ℂ) (Z : ι → ℂ)
    (hF : ∀ i ∈ s, IsQuotIntL1 μR μG (F i) (Z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i ∈ s, a i * F i x) (∑ i ∈ s, a i * Z i) :=
  quotient_integral_finset_sum_eq s (fun i x => a i * F i x) (fun i => a i * Z i) fun i hi => (hF i hi).smul (a i)

end Quot

end GlobalTheory.SeeSaw.Assemble

end

noncomputable section

namespace GlobalTheory.SeeSaw.Assemble


set_option maxHeartbeats 4000000 in
theorem doubleStep_tuple : ∀ (D : D7) (c : Comm D) (t : Tup c), DoubleStep D → c.Is → t.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ), (∀ a, IsContAut (c.X j) (φ a)) → RapidDec _ f → RapidDec _ (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) → ∃ F₁ : GA D (c.V (j + 1)) → ℂ, IsQuotIntL1 (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ F₁ (t.perF j (σ + 1) h φ (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁))) ∧ ∀ h₁, IsQuotIntL1 (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ (t.integrand j σ h P₁ P₂ φ f h₁) (F₁ h₁) := by
  intro D c t hDS hc ht j σ h P₁ P₂ φ f hφ hf hrap
  obtain ⟨hom₁, hvW₁⟩ := ht.sBF j (σ + 1) h
  obtain ⟨hom₂, hvW₂⟩ := ht.sFB j σ h
  have hj1 : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  have hΦ₁ := ht.pt j hj1 P₁
  have hΦ₂ := ht.pt (j + 1) hj2 P₂

  have hstep : ∀ α, ∀ g : GA D (c.V j), ∃ f₁ : GA D (c.V (j + 1)) → ℂ,
      IsQuotIntL1 (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ f₁
        ((c.B j (σ + 1) h).per c.ψ (φ α) (rTrans g (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
          (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁)))) ∧
      ∀ h₁, IsQuotIntL1 (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ
        (fun h₂ => (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
          (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (t.pt j P₁) (t.pt (j + 1) P₂) (φ α) g h₁ h₂)
          (rTrans h₂ f)) (f₁ h₁) := by
    intro α g
    have hr : RapidDec _ ((t.sFB j σ h).lift f (t.pt (j + 1) P₂)) := by
      unfold Step.lift; rw [hom₂, hvW₂]; exact hrap
    obtain ⟨-, f₁, h1, h2⟩ := hDS c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (t.pt j P₁) (t.pt (j + 1) P₂) (φ α) f g
      hΦ₁ hΦ₂ (hφ α) hf hr
    refine ⟨f₁, ?_, fun h₁ => ?_⟩
    · have h1' := h1
      unfold Step.lift at h1'
      rw [hom₁, hvW₁, hom₂, hvW₂] at h1'
      exact h1'
    · have h2' := h2 h₁
      rw [hvW₂] at h2'
      exact h2'
  choose f₁ hf₁ using hstep

  have hw := (t.sBF j (σ + 1) h).weil
  rw [hom₁] at hw
  have hcont := (GlobalTheory.Unf.LiftRapid.lift_conv_cont_growth D c.ψ (c.V j) (c.V (j + 1)) _ _ (t.om j) hw (c.vol (j + 1))
    (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁) hrap hΦ₁).2.2.1
  refine ⟨fun h₁ => ∑ α, ∑ g ∈ (t.e j α).support, t.e j α g * f₁ α g h₁, ?_, fun h₁ => ?_⟩
  · have hper : ∀ α, (c.B j (σ + 1) h).per c.ψ (φ α) (trc (t.e j α) (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁))) =
        ∑ g ∈ (t.e j α).support, t.e j α g * (c.B j (σ + 1) h).per c.ψ (φ α) (rTrans g (liftS (t.om j) (c.vol (j + 1)).μ
          (c.vol (j + 1)).𝓕 (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂))
          (t.pt j P₁))) := fun α =>
      ((_root_.GlobalTheory.SeeSaw.per_linear_trc D c.ψ hc.std (σ + 1) (c.B j (σ + 1) h) (φ α) (hφ α)).2 (t.e j α) _ hcont).2
    unfold Tup.perF
    simp only [hper]
    exact quotient_integral_finset_sum_eq _ _ _ fun α _ =>
      quotient_integral_finset_sum_smul _ _ _ _ fun g _ => (hf₁ α g).1
  · unfold Tup.integrand
    exact quotient_integral_finset_sum_eq _ _ _ fun α _ =>
      quotient_integral_finset_sum_smul _ _ _ _ fun g _ => (hf₁ α g).2 h₁

end GlobalTheory.SeeSaw.Assemble

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi


set_option maxHeartbeats 1000000 in
theorem colForm_of_dec {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u)
    (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0))
    (hθ : IsInfFam θ) (hE : IdE X) (hAd : B.Adapted tr.wt) (hH0 : IsTransportAdelicCorrection tr a₀)
    (hLM : Formalism.L2.SG.ColDict.LevelMatch X tr hK) (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0))
    (c : (D.mem u).C.cls 0) (γ : GL (Fin (D.R.N 0)) D.host.E) (κ : F.cls0.lev.U)
    (hγ : γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)))
    (hx : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g =
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (F.cls0.y c).1 * κ.1).1) :
    (F.cls0.lev.chi κ : ℂ) * GlobalTheory.AdForm.atFr (fun z => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z)
        (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
          GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) =
      B.colForm T.1 (rieszJ tr (F.val0.eY y)) (g * a₀⁻¹) := by
  obtain ⟨aγ, hQ, hfγ, hiγ⟩ := GlobalTheory.T.exists_rationalAdelicPoint_of_unitary_baseSpace D θ hθ γ hγ
  obtain ⟨γ', hγ'1, hγ'2⟩ := _root_.GlobalTheory.Core.Mi.toH_rat D X h u ψ B aγ hQ
  have finv : ∀ (a : GA D (D.sp.X 0)) (Bm : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)),
      Bm * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = 1 →
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = Bm := by
    intro a Bm hB
    have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = 1 := by
      rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
    calc _ = (Bm * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) *
          GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ := by rw [hB, one_mul]
      _ = Bm := by rw [mul_assoc, h1, mul_one]
  have iinv : ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau) (Bm : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ),
      Bm * GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = 1 →
      GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ = Bm := by
    intro a τ Bm hB
    have h1 : GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ = 1 := by
      rw [← unitaryAdelicPointInfiniteMatrices_base_space_mul, mul_inv_cancel, unitaryAdelicPointInfiniteMatrices_base_space_one]
    calc _ = (Bm * GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ) *
          GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ := by rw [hB, one_mul]
      _ = Bm := by rw [mul_assoc, h1, mul_one]
  have hfγi : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) aγ⁻¹ =
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ⁻¹).1 := by
    apply finv
    rw [hfγ, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hh : ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) * (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    have : (tr.h0⁻¹).1.1 * tr.h0.1.1 = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    exact this
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ = (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH0.2
  have hfa0i : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ = ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) :=
    finv _ _ (by rw [e0]; exact hh)
  have hiγi : ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) aγ⁻¹ τ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ := by
    intro τ
    apply iinv
    rw [hiγ τ]
    unfold Formalism.L2.Forms.atInf
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨r, hr⟩ : ∃ r, r = aγ⁻¹ * g * a₀⁻¹ := ⟨_, rfl⟩
  have hg : g * a₀⁻¹ = aγ * r := by rw [hr]; group
  have hκP : κ.1 ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((F.cls0.lev.U_eq κ.1).1 κ.2).1
  obtain ⟨yk, hyk⟩ : ∃ yk : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), yk = tr.h0 * ⟨κ.1, hκP⟩ * tr.h0⁻¹ := ⟨_, rfl⟩
  have hfr : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r =
      ((F.cls0.y c * tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) * (yk.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    rw [hr, unitaryAdelicPointFiniteMatrix_base_space_mul, unitaryAdelicPointFiniteMatrix_base_space_mul, hfγi, hx, hfa0i]
    have : (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ⁻¹).1 *
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (F.cls0.y c).1 * κ.1).1 *
        (tr.h0⁻¹).1.1 = (F.cls0.y c * tr.h0⁻¹).1.1 * yk.1.1 := by
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [hyk]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_inv]
      group
    exact this
  have hir : ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ := by
    intro τ
    rw [hr, unitaryAdelicPointInfiniteMatrices_base_space_mul, unitaryAdelicPointInfiniteMatrices_base_space_mul, hiγi, unitaryAdelicPointInfiniteMatrices_eq_one_of_finite θ a₀⁻¹ (inv_mem hH0.1), mul_one]

  have hRfin := _root_.GlobalTheory.Core.Mi.FinFrame.repM_toH D X h u ψ B F tr hE hAd r
  have hreal := _root_.GlobalTheory.Core.Mi.sTil_toH_eq_infM D X h u ψ B F tr θ hθ hE hAd r
  obtain ⟨κ'', hκ''⟩ : ∃ κ'' : Hfin X u, κ'' = (tr.hc c)⁻¹ * (B.toH r).2 := ⟨_, rfl⟩
  have hmulκ : ((tr.hc c : Hfin X u) : X.B.I.Gf) * (κ'' : X.B.I.Gf) = ((B.toH r).2 : X.B.I.Gf) := by
    rw [hκ'', ← Subgroup.coe_mul, mul_inv_cancel_left]
  have hRk : RepM X tr.wt tr.ιA (κ'' : X.B.I.Gf) (yk.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine RepM_cancel (tr.hc_rep c) ?_
    rw [hmulκ, ← hfr]
    exact hRfin
  have hRF : Formalism.L2.SG.ColDict.RepF X tr.wt tr.ιA (κ'' : X.B.I.Gf) yk := hRk
  have hconj : ((tr.h0⁻¹ * yk * tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) = κ.1 := by
    rw [hyk]
    simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
  have hκU : ((tr.h0⁻¹ * yk * tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈ F.cls0.lev.U := hconj ▸ κ.2
  obtain ⟨hmemIff, hpsi⟩ := hLM.2 κ'' yk hRF
  have hmem : κ'' ∈ Ku X u hK := hmemIff.2 hκU
  have hpsiv := hpsi hmem hκU
  have hchi : ((F.cls0.lev.chi ⟨_, hκU⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi κ : ℂˣ) : ℂ) := by
    congr 2
    exact Subtype.ext hconj

  have hdet : ∀ τ, IsUnit (GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ * (F.val0.eY y).1 τ).det := by
    intro τ
    rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ((F.val0.eY y).2 τ)
    refine Matrix.isUnit_det_of_right_inverse (B := GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r⁻¹ τ) ?_
    rw [← unitaryAdelicPointInfiniteMatrices_base_space_mul, mul_inv_cancel, unitaryAdelicPointInfiniteMatrices_base_space_one]
  let z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) :=
    ⟨fun τ => GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ * (F.val0.eY y).1 τ, hdet⟩
  have htr : Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH r).1 : X.B.I.Ginf)) (F.val0.eY y) z' := by
    intro τ
    show _ = _ * _
    rw [hreal τ]
  have hriesz := _root_.GlobalTheory.Core.Mi.piU_rieszJ D X u F tr ((B.toH r).1 : X.B.I.Ginf) (B.toH r).1.2 (F.val0.eY y) z' htr

  have hlhs : GlobalTheory.AdForm.atFr (fun w => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) w)
      (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) =
      tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z' := by
    have hfun : (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) = z'.1 := by
      funext τ
      show _ = _ * _
      rw [hir τ]
    unfold GlobalTheory.AdForm.atFr
    rw [dite_eq_left (by rw [hfun]; exact z'.2)]
    congr 1
    exact Subtype.ext hfun
  refine Eq.trans (congrArg (fun t => ((F.cls0.lev.chi κ : ℂˣ) : ℂ) * t) hlhs) ?_

  have hT := T.2
  have hT1 := hT.1 (rieszJ tr (F.val0.eY y))
  have htoHaγ : B.toH aγ = (iotaI X u γ', iotaF X u γ') := Prod.ext hγ'1.symm hγ'2.symm
  have hdec : B.toH r = ((1 : Hinf X u), tr.hc c) * ((B.toH r).1, (1 : Hfin X u)) * ((1 : Hinf X u), κ'') := by
    ext
    · simp
    · simp [hκ'']
  have eR : B.colForm T.1 (rieszJ tr (F.val0.eY y)) (g * a₀⁻¹) =
      ((psiK X u hK ⟨κ'', hmem⟩ : ℂˣ) : ℂ) * tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z' := by
    have hx1 : B.toH (g * a₀⁻¹) = (iotaI X u γ', iotaF X u γ') *
        (((1 : Hinf X u), tr.hc c) * ((B.toH r).1, (1 : Hfin X u)) * ((1 : Hinf X u), κ'')) :=
      (congrArg B.toH hg).trans ((toH_mul B aγ r).trans (congrArg₂ (· * ·) htoHaγ hdec))
    unfold SBes.colForm
    rewrite [hx1, hT1.1 γ', hT1.2 _ ⟨κ'', hmem⟩]
    have h3 := hT.2 (B.toH r).1 (rieszJ tr (F.val0.eY y)) ((1 : Hinf X u), tr.hc c)
    have h4 := Formalism.L2.SG.ColDict.inner_shP X u T.1 (tr.hc c) (rieszJ tr z')
    have h5 := inner_rieszJ tr z' (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c))
    have h6 := congrArg (fun v => T.1 v ((1 : Hinf X u), tr.hc c)) hriesz
    refine congrArg (fun t => ((psiK X u hK ⟨κ'', hmem⟩ : ℂˣ) : ℂ) * t) ?_
    exact h3.symm.trans (h6.trans (h4.symm.trans h5))
  refine Eq.trans ?_ eR.symm
  exact congrArg (fun t => t * tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z') (hchi.symm.trans hpsiv.symm)

end GlobalTheory.Core.Mi

theorem GlobalTheory.Core.Mi.colDict_rd_eq_colForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0)), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → Formalism.L2.SG.ColDict.LevelMatch X tr hK → ∃ ξ : (D.mem u).C.Y 0 → X.Vpi u, Submodule.span ℂ (Set.range ξ) = ⊤ ∧ ∀ (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0)), (chart0 F).rd θ (Formalism.L2.SG.ColDict.colDictL X tr hK T) y g = B.colForm T.1 (ξ y) (g * a₀⁻¹) := by
  intro D X h u ψ B F tr hK θ a₀ hθ hE hAd hH0 hLM
  refine ⟨fun y => GlobalTheory.Core.Mi.rieszJ tr (F.val0.eY y), GlobalTheory.Core.Mi.span_rieszJ tr, ?_⟩
  intro T y g
  unfold GlobalTheory.AdForm.Chart.rd chart0 GlobalTheory.AdForm.rdS
  simp only
  have hd : ∃ p, GlobalTheory.AdForm.IsDec F.cls0.toChart.lev F.cls0.toChart.y
      (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p := _root_.GlobalTheory.Core.Mi.exists_isDec_finM D u F g
  rw [dite_eq_left hd]
  have hfe : (fun z => Formalism.L2.SG.ColDict.colDictL X tr hK T (id hd.choose.1) (F.val0.eY.symm z)) =
      (fun w => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc hd.choose.1)) w) :=
    funext (GlobalTheory.Core.Mi.colDictL_eY_symm tr hK T hd.choose.1)
  rw [hfe]
  exact GlobalTheory.Core.Mi.colForm_of_dec X h u ψ B F tr hK θ a₀ hθ hE hAd hH0 hLM T y g hd.choose.1 hd.choose.2.1 hd.choose.2.2
    hd.choose_spec.1 hd.choose_spec.2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramifiedStatement
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem fullLattice_of_isSelfDualAt
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin n → E)} (hLat : Submodule.IsLattice E L)
    {v : HeightOneSpectrum (𝓞 F)} (hL : IsSelfDualAt σ J L v) : Submodule.IsFullLattice E L := by
  classical
  refine { toIsLattice := hLat, span_eq_top := ?_ }
  by_contra hspan
  obtain ⟨f, hf, hker⟩ := (Submodule.span E (L : Set (Fin n → E))).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hspan)
  let coeff (i : Fin n) : E := f (fun j => if i = j then 1 else 0)
  have hcoeff (x : Fin n → E) : f x = ∑ i, x i * coeff i := f.pi_apply_eq_sum_univ x
  let w := J⁻¹ *ᵥ fun i => σ (coeff i)
  have hw : J *ᵥ w = fun i => σ (coeff i) := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ.2.isUnit, Matrix.one_mulVec]
  have hw_ne : w ≠ 0 := by
    intro hw_zero
    have hc (i : Fin n) : coeff i = 0 := σ.injective (by
      simpa [hw_zero] using (congrFun hw i).symm)
    apply hf
    exact LinearMap.ext fun x => by simp [hcoeff, hc]
  have hOrth (x : Fin n → E) (hx : x ∈ L) : hE σ J x w = 0 := by
    have hfx : f x = 0 := LinearMap.mem_ker.mp (hker (Submodule.subset_span hx))
    unfold hE Formalism.UG.hform
    simp only [mul_assoc, ← Finset.mul_sum]
    change (∑ i, σ (x i) * (J *ᵥ w) i) = 0
    rw [hw]
    calc
      _ = σ (f x) := by rw [hcoeff, map_sum]; simp only [map_mul]
      _ = 0 := by rw [hfx, map_zero]
  let wLoc : Fin n → Fv F v ⊗[F] E := fun i => (1 : Fv F v) ⊗ₜ[F] w i
  let pairing : (Fin n → Fv F v ⊗[F] E) →+ (Fv F v ⊗[F] E) :=
    { toFun := fun x => hLin σ J (Fv F v) wLoc x
      map_zero' := by simp [hLin, hR, Formalism.UG.hform]
      map_add' := fun x y => by
        simp [hLin, hR, Formalism.UG.hform, add_mul, Finset.sum_add_distrib] }
  have hZero : ∀ x ∈ latLoc F L v, pairing x = 0 := by
    intro z hz
    refine latLoc_induction (p := fun x => pairing x = 0) (fun a _ x hx => ?_) (map_zero pairing)
      (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
      (fun x hx => by rw [map_neg, hx, neg_zero]) hz
    change hLin σ J (Fv F v) wLoc (fun i => a ⊗ₜ[F] x i) = 0
    have h := congrArg (fun z : E => a ⊗ₜ[F] z) (hOrth x hx)
    simpa [hLin, hR, hE, Formalism.UG.hform, wLoc, sigR, JR, inclR,
      TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul] using h
  have hLine (a : Fv F v) : (fun i => a ⊗ₜ[F] w i) ∈ latLoc F L v := by
    rw [show latLoc F L v = dualLoc σ J L v from hL]
    change ∀ x ∈ latLoc F L v, hLin σ J (Fv F v) (fun i => a ⊗ₜ[F] w i) x ∈ intLoc F E v
    intro x hx
    have he : (fun i => a ⊗ₜ[F] w i) = (a ⊗ₜ[F] (1 : E)) • wLoc := by
      funext i
      change _ = (a ⊗ₜ[F] (1 : E)) * ((1 : Fv F v) ⊗ₜ[F] w i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [he, hLin_smul_left, show hLin σ J (Fv F v) wLoc x = 0 from hZero x hx, mul_zero]
    exact zero_mem _
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw_ne
  change w i ≠ 0 at hi
  obtain ⟨C, hC⟩ := GlobalTheory.LocalLatticeBound.exists_bound_latLoc L v
  let τ : E →ₐ[F] FvBar F v := IsAlgClosed.lift
  have hpos : 0 < absBar F v (τ (w i)) :=
    pos_iff_ne_zero.mpr fun h => hi (τ.injective (by simpa using (absBar_eq_zero F v).mp h))
  let _ : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨a, ha⟩ := NormedField.exists_lt_nnNorm (Fv F v) (C / absBar F v (τ (w i)))
  have hbound := (le_absFin F v τ (a ⊗ₜ[F] w i)).trans (hC _ (hLine a) i)
  rw [finEmb_tmul, absBar_mul, absBar_algebraMap] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hpos).mp ha)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_stabilizers_selfDual_lattices_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (L L' : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → Submodule.IsLattice E L' → ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt σ J L v → IsSelfDualAt σ J L' v → ∃ g : GLoc σ J v, ∀ k : GLoc σ J v, k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v := by
  intro F E _ _ _ _ _ σ hCM hU n J hJ L L' hLat hLat' v hL hL'
  exact GlobalTheory.SelfDualStabConj.exists_conj_stabLoc F E σ hCM hU n J hJ L L'
    (fullLattice_of_isSelfDualAt hJ hLat hL)
    (fullLattice_of_isSelfDualAt hJ hLat' hL') v hL hL'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEvalAtOfMem
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

section Transport

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}

theorem qdet_map (f : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    Formalism.REAL.qdet (fun a b => f (E a b)) u = f (Formalism.REAL.qdet E u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod,
    List.map_ofFn, Function.comp_def, map_add, AlgHom.commutes, apply_ite f, map_zero]

end Transport

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

end GlobalTheory.CapelliUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroSourceSlice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extS_slice :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO A T →₀ ℂ) (f : WO S T → ℂ) (y : WO L T) (w : WO A T), comb ψ A T c (fun w' => f ((o.resS T).symm (w', y))) w = comb ψ S T (extS o T c) f ((o.resS T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  classical
  have hinj : Function.Injective (fun a : WO A T => (o.resS T).symm (a, 0)) := fun a b h => by
    simpa using h
  unfold comb extS
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h),
    Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, Pi.smul_apply, Pi.smul_apply, heisO_resS_symm]

end GlobalTheory.FinPl.ExtZero
end

