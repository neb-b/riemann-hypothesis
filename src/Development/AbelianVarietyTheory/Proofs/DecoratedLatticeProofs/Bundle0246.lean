module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsTransportLinearRelations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LastStepsX

variable {D : D7}

theorem liftS_smul {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (a : ℂ)
    (G : GA D T → ℂ) (f : WO S T → ℂ) : liftS om ν 𝓕 (a • G) f = a • liftS om ν 𝓕 G f := by
  funext g
  simp only [liftS, Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem trc_smul {V : HSp D} (e : GA D V →₀ ℂ) (a : ℂ) (f : GA D V → ℂ) : trc e (a • f) = a • trc e f := by
  funext x
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

theorem perF_smul {c : Comm D} (t : Tup c) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (φ : t.Ch j → GA D (c.X j) → ℂ)
    (a : ℂ) (f : GA D (c.V j) → ℂ) : t.perF j ρ h φ (a • f) = a * t.perF j ρ h φ f := by
  simp only [Tup.perF, trc_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have e := GlobalTheory.HandHom.per_smul (c.B j ρ h) c.ψ 1 a (φ α) (trc (t.e j α) f)
  rw [one_smul, one_mul] at e
  exact e

theorem contAut_trc {V : HSp D} (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, hf.1 γ hγ]
  · have e : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := by
      funext x
      simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact continuous_finsetSum _ fun g _ => continuous_const.mul (hf.2.comp (continuous_mul_const g))

theorem contAut_emb {S A B : HSp D} (o : OrthDec S A B) {f : GA D S → ℂ} (hf : IsContAut S f) :
    Continuous (fun h : GA D A => f (o.emb (h, 1))) ∧ ∀ γ ∈ GQ A, ∀ g, f (o.emb (γ * g, 1)) = f (o.emb (g, 1)) := by
  refine ⟨hf.2.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const)), fun γ hγ g => ?_⟩
  have e : o.emb (γ * g, 1) = o.emb (γ, 1) * o.emb (g, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, hf.1 _ (o.emb_mem_GQ hγ (one_mem _))]

theorem integrableOn_contAut {V : HSp D} (hV : CoCpt V) (vol : Vol V) {f : GA D V → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : IntegrableOn f vol.𝓕 vol.μ :=
  (GlobalTheory.CocompactParam.continuous_integral_param D V hV vol Unit (fun g _ => f g) (hc.comp continuous_fst)
    (fun γ hγ g _ => hi γ hγ g)).1 ()

theorem io_ioT {c : Comm D} (t : Tup c) (ht : t.Is) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (F : t.CT)
    (P₁ : PolF D (c.V (j + 1)).rank (c.V j).rank) (P₂ : PolF D c.T.rank (c.V (j + 1)).rank) (v : SmT c.MT) :
    (t.cI j * t.cI (j + 1)) • ((t.io j (t.ioT j h F)).1 (c.It j P₁ (c.ItT j h P₂ v))) =
      liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.omT j h) c.volT.μ c.volT.𝓕 (F.1 v) (t.ptT j h P₂)) (t.pt j P₁) := by
  rw [ht.ioT j h F P₂ v, liftS_smul, ht.io j (by omega) (t.ioT j h F) P₁ (c.ItT j h P₂ v), smul_smul, mul_comm]

theorem perT_comb {c : Comm D} (t : Tup c) (n : ℕ) (h : n = D.R.m) {Y : Type} (S : Finset Y) (k : ℂ) (a : Y → ℂ)
    (φ : Y → t.Ch n → GA D (c.X n) → ℂ) (f : GA D c.T → ℂ)
    (hi : ∀ y' β, IntegrableOn (fun h' => trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) c.volT.𝓕 c.volT.μ) :
    t.perT n h (fun β => k • ∑ y' ∈ S, a y' • φ y' β) f = k * ∑ y' ∈ S, a y' * t.perT n h (φ y') f := by
  have e1 : ∀ β, ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1)) ∂c.volT.μ
      = ∑ y' ∈ S, k * a y' * ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1)) ∂c.volT.μ := by
    intro β
    have e2 : (fun h' => trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1))) =
        fun h' => ∑ y' ∈ S, (k * a y') * (trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) := by
      funext h'
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y' _ => by ring
    rw [e2, integral_finsetSum _ (fun y' _ => (hi y' β).const_mul _)]
    simp_rw [integral_const_mul]
  simp only [Tup.perT, e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun β _ => by ring

end GlobalTheory.SeeSaw.LastStepsX


set_option maxHeartbeats 4000000 in
open GlobalTheory.SeeSaw.LastStepsX in
theorem GlobalTheory.SeeSaw.lastX_of_laws : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), RapidVal D → c.Is → (∀ s, (t s).Is) → ValLastX t → TwoX t → PerX t → RdX t → LastX t := by
  intro hHC D c 𝒯 t hRV hc ht hVL hTX hPX hRD
  intro j h I _ s α ψ F hψ hF y v
  obtain ⟨χ, hχ⟩ := hRD j (by omega)
  obtain ⟨χ₂, hχ₂⟩ := hRD (j + 1 + 1) (by omega)
  refine _root_.GlobalTheory.SeeSaw.perF_rel_of_steps hHC D c 𝒯 t hc j 0 h I s (fun i => α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)))
    (fun i β => (t (s i)).rd j β (ψ i) y) (fun i => (t (s i)).io j ((t (s i)).ioT j h (F i))) ht
    (fun i β => (hχ (s i) (ψ i) (hψ i) β y).1) c.T c.T c.parT c.MT (c.ItT j h) (hc.spanT j h) ?_ v
  intro P₁ P₂ w
  obtain ⟨C, hCr, hC⟩ := hVL j h P₁ P₂
  obtain ⟨a, ha⟩ := hTX j (by omega) C hCr y
  choose b hb using fun y' => hPX (j + 1 + 1) h y' w
  have hterm : ∀ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) * (t (s i)).perF j 0 h (fun β => (t (s i)).rd j β (ψ i) y)
      (((t (s i)).io j ((t (s i)).ioT j h (F i))).1 (c.It j P₁ (c.ItT j h P₂ w))) =
      ∑ y' ∈ a.support, a y' * b y' * (α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1) * (t (s i)).cP) *
        (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i)) := by
    intro i
    have hSψ : (t (s i)).S j (ψ i) ∈ (t (s i)).Ram j := (ht (s i)).stabS j (by omega) _ (hψ i)
    have hψ₁ := (ht (s i)).stabK j (by omega) _ hSψ
    have hψ₂ := (ht (s i)).stabK (j + 1) (by omega) _ hψ₁
    rw [mul_assoc, ← perF_smul, io_ioT (t (s i)) (ht (s i)) j h (F i) P₁ P₂ w, hC (s i) (ψ i) (hψ i) y (F i) w]
    have e2 : (t (s i)).two j (fun β => (t (s i)).rd j β ((t (s i)).S j (ψ i)) y) C = fun β =>
        ((t (s i)).cK j * (t (s i)).cK (j + 1)) • ∑ y' ∈ a.support, a y' •
          (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y' :=
      funext fun β => ha (s i) _ hSψ β
    have hE : RapidDec c.T ((F i).1 w) := by
      obtain ⟨J, χ', hle⟩ := (ht (s i)).CT
      exact hRV c.θ hc.inf c.T c.parT c.MT J χ' _ (hle (F i).2) w
    have e3 := perT_comb (t (s i)) (j + 1 + 1) h a.support ((t (s i)).cK j * (t (s i)).cK (j + 1)) a
      (fun y' β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w)
      (fun y' β => by
        have ht' := contAut_trc ((t (s i)).eT (j + 1 + 1) h β) ⟨hE.1, hE.2.1⟩
        obtain ⟨hcont, hinv⟩ := contAut_emb (c.oT (j + 1 + 1) h) (hχ₂ (s i) _ hψ₂ β y').1
        exact integrableOn_contAut hc.cpt c.volT (ht'.2.mul hcont) (fun γ hγ g => by rw [ht'.1 γ hγ g, hinv γ hγ g]))
    beta_reduce at e3
    have hb' : ∀ y', (t (s i)).perT (j + 1 + 1) h
        (fun β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w) =
        (t (s i)).cP * b y' * (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i) :=
      fun y' => hb y' (s i) _ hψ₂ (F i)
    rw [e2, e3]
    simp only [hb', Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [← Finset.mul_sum, hF, mul_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawPeriodsLinearRelationsDoubleStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.VanMany

theorem quot_lin {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G} {I : Type}
    [Fintype I] (α : I → ℂ) (f : I → G → ℂ) (z : I → ℂ) (h : ∀ i, IsQuotIntL1 μR μG (f i) (z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i, α i * f i x) (∑ i, α i * z i) := by
  classical
  have key : ∀ S : Finset I, IsQuotIntL1 μR μG (fun x => ∑ i ∈ S, α i * f i x) (∑ i ∈ S, α i * z i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact IsQuotIntL1.zero
    | insert i S hi ih =>
      have := ((h i).smul (α i)).add ih
      have e : (fun x => ∑ j ∈ insert i S, α j * f j x) = α i • f i + (fun x => ∑ j ∈ S, α j * f j x) := by
        funext x
        simp [Finset.sum_insert hi]
      rw [e, Finset.sum_insert hi]
      exact this
  exact key Finset.univ

theorem iteratedQuotientIntegral_finite_linearCombination {G₁ G₂ : Type} [Group G₁] [MeasurableSpace G₁] [TopologicalSpace G₁] [Group G₂] [MeasurableSpace G₂]
    [TopologicalSpace G₂] {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} (ρ₁ : Measure R₁) (μ₁ : Measure G₁) (ρ₂ : Measure R₂)
    (μ₂ : Measure G₂) {I : Type} [Fintype I] (α : I → ℂ) (f : I → G₁ → G₂ → ℂ) (v : I → ℂ)
    (h : ∀ i, Iter2 ρ₁ μ₁ ρ₂ μ₂ (f i) (v i)) :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ => ∑ i, α i * f i q₁ q₂) (∑ i, α i * v i) := by
  choose g hg1 hg2 using h
  exact ⟨fun q => ∑ i, α i * g i q, quot_lin α g v hg1, fun q => quot_lin α (fun i => f i q) (fun i => g i q) fun i => hg2 i q⟩

theorem invsupp : ∀ (D : D7) (c : Comm D) (t : Tup c), t.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ) (K₁ : Subgroup (GA D (c.V (j + 1)))) (T₁ : Finset (GA D (c.V (j + 1)))), (∀ k ∈ K₁, ∃ a : ℂ, a ≠ 0 ∧ t.om j (1, k) (t.pt j P₁) = a⁻¹ • t.pt j P₁ ∧ t.om (j + 1) (k, 1) (t.pt (j + 1) P₂) = a • t.pt (j + 1) P₂) → (∀ α, ∀ g ∈ (t.e j α).support, ∀ h₁, flatBF (t.sBF j (σ + 1) h) (t.om j (g, h₁) (t.pt j P₁)) ≠ 0 → ∃ q ∈ T₁, InCell (jacGrp (c.jac j (σ + 1) h).d) q K₁ h₁) → (∀ h₁, ∀ k ∈ K₁, t.integrand j σ h P₁ P₂ φ f (h₁ * k) = t.integrand j σ h P₁ P₂ φ f h₁) ∧ (∀ h₁, t.integrand j σ h P₁ P₂ φ f h₁ ≠ 0 → ∃ q ∈ T₁, InCell (jacGrp (c.jac j (σ + 1) h).d) q K₁ h₁) := by
  intro D c t ht j σ h P₁ P₂ φ f K₁ T₁ hlaw hsupp
  obtain ⟨hs1om, -⟩ := ht.sBF j (σ + 1) h
  obtain ⟨hs2om, -⟩ := ht.sFB j σ h
  have HH := fun φ' => GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) φ'
  have per0 : ∀ f', (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ 0 f' = 0 := by
    intro f'
    have := (HH (fun _ => 0)).2.2 0 1 0 f'
    simpa using this
  refine ⟨fun h₁ k hk => ?_, fun h₁ hne => ?_⟩
  · obtain ⟨a, ha, h1, h2⟩ := hlaw k hk
    have key : ∀ α g h₂, Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (t.pt j P₁)
        (t.pt (j + 1) P₂) (φ α) g (h₁ * k) h₂ = Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h)
        (t.pt j P₁) (t.pt (j + 1) P₂) (φ α) g h₁ h₂ := by
      intro α g h₂
      simp only [Chain.hand]
      have m1 : (t.sBF j (σ + 1) h).om (g, h₁ * k) (t.pt j P₁) = a⁻¹ • (t.sBF j (σ + 1) h).om (g, h₁) (t.pt j P₁) := by
        have hm : ((g, h₁ * k) : GA D (c.V j) × GA D (c.V (j + 1))) = (g, h₁) * (1, k) := by simp
        rw [hm, map_mul, Module.End.mul_apply, hs1om, h1, map_smul]
      have m2 : (t.sFB j σ h).om (h₁ * k, h₂) (t.pt (j + 1) P₂) = a • (t.sFB j σ h).om (h₁, h₂) (t.pt (j + 1) P₂) := by
        have hm : ((h₁ * k, h₂) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (h₁, h₂) * (k, 1) := by simp
        rw [hm, map_mul, Module.End.mul_apply, hs2om, h2, map_smul]
      rw [m1, m2, (HH (φ α)).1, inv_mul_cancel₀ ha, one_smul]
    funext h₂
    simp only [Tup.integrand, key]
  · by_contra hno
    push_neg at hno
    apply hne
    funext h₂
    simp only [Tup.integrand, Pi.zero_apply]
    refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun g hg => ?_
    have hflat : flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (g, h₁) (t.pt j P₁)) = 0 := by
      by_contra hf
      rw [hs1om] at hf
      obtain ⟨q, hq, hc⟩ := hsupp α g hg h₁ hf
      exact hno q hq hc
    simp only [Chain.hand, hflat, (HH (φ α)).2.1, per0, mul_zero]

theorem vanMany : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (f : I → GA D (c.V (j + 1 + 1)) → ℂ), (∀ i a, IsContAut (c.X j) (φ i a)) → (∀ i, RapidDec _ (f i)) → (∀ i, RapidDec _ (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂))) → (∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∃ v : I → ℂ, (∀ i, Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) (a * q₁.1) (a' * q₂.1)) (v i)) ∧ ∑ i, α i * v i = 0) → ∑ i, α i * (t (s i)).perF j (σ + 1) h (φ i) (liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂)) ((t (s i)).pt j P₁)) = 0 := by
  classical
  intro D c 𝒯 t hDS hc ht hloc j σ h P₁ P₂ I _ s α φ f hφ hf hlift hV
  rcases isEmpty_or_nonempty I with hI | hI
  · simp
  obtain ⟨i₀⟩ := hI
  have hA := fun i => _root_.GlobalTheory.SeeSaw.Assemble.doubleStep_tuple D c (t (s i)) hDS hc (ht (s i)) j σ h P₁ P₂ (φ i) (f i) (hφ i) (hf i) (hlift i)
  choose F₁ hF₁ hF₂ using hA
  have hL := fun i => hloc (s i) j σ h P₁ P₂
  choose K₁ T₁ hK₁f hK₁c hK₁o hT₁ hlaw hsupp using hL
  have hIS := fun i => invsupp D c (t (s i)) (ht (s i)) j σ h P₁ P₂ (φ i) (f i) (K₁ i) (T₁ i) (hlaw i) (hsupp i)
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (c.V (j + 1))
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (c.V (j + 1 + 1))
  obtain ⟨gA₁, gB₁, gc₁, ge₁, gμ₁, gR₁⟩ := _root_.GlobalTheory.AdelicSplit.adelic_split D (c.V (j + 1))
  obtain ⟨gA₂, gB₂, gc₂, ge₂, gμ₂, gR₂⟩ := _root_.GlobalTheory.AdelicSplit.adelic_split D (c.V (j + 1 + 1))
  obtain ⟨⟨jsplit, -, jinvf⟩, -⟩ := gR₁ _ _ (c.jac j (σ + 1) h).d
  obtain ⟨-, bes⟩ := gR₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d
  obtain ⟨bsplit, -, binvf⟩ := bes _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o
  obtain ⟨jcl, jH, jI⟩ := GlobalTheory.QuotZero.jac_haar_inv (c.J j (σ + 1) h)
  obtain ⟨bcl, bH, bI⟩ := GlobalTheory.QuotZero.bes_haar_inv (c.B (j + 1 + 1) σ (idx_step h))
  have hQ1 := quot_lin α F₁ _ hF₁
  have hQ2 := fun h₁ => quot_lin α (fun i => (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) h₁) (fun i => F₁ i h₁)
    (fun i => hF₂ i h₁)
  refine _root_.GlobalTheory.VanCore.vanish (GA D (c.V (j + 1))) (GA D (c.V (j + 1 + 1))) (GinfC _) (GfC _) (jacGrp (c.jac j (σ + 1) h).d)
    (GinfC _) (GfC _) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
    gA₁ gB₁ jcl gc₁ ge₁ jsplit gA₂ gB₂ bcl gc₂ ge₂ bsplit
    (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ (c.ρJ j (σ + 1) h) (c.μf (j + 1))
    (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
    jH jI (c.vol (j + 1)).haar (hc.ρJ _ _ _) (jinvf _ (hc.ρJ _ _ _)) (hc.μf _) (gμ₁ _ (hc.μf _))
    bH bI (c.vol (j + 1 + 1)).haar (hc.ρB _ _ _) (binvf _ (hc.ρB _ _ _)) (hc.μf _)
    (⨅ i, K₁ i) (⋃ i, (K₁ i : Set (GA D (c.V (j + 1))))) (Finset.univ.biUnion T₁) ?_ ?_ ?_ ?_ ?_ ?_
    _ (fun h₁ h₂ => ∑ i, α i * (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) h₁ h₂) _ hQ1 hQ2 ?_ ?_ ?_
  · exact iInf_le_of_le i₀ (hK₁f i₀)
  · rw [Subgroup.coe_iInf]
    exact IsCompact.of_isClosed_subset (hK₁c i₀) (isClosed_iInter fun i => (hK₁c i).isClosed) (Set.iInter_subset _ i₀)
  · have e : (((⨅ i, K₁ i).subgroupOf (GfC (c.V (j + 1))) : Subgroup (GfC (c.V (j + 1)))) : Set (GfC (c.V (j + 1)))) =
        ⋂ i, (((K₁ i).subgroupOf (GfC (c.V (j + 1))) : Subgroup (GfC (c.V (j + 1)))) : Set (GfC (c.V (j + 1)))) := by
      ext x
      simp [Subgroup.mem_subgroupOf, Subgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun i => hK₁o i
  · exact isCompact_iUnion fun i => hK₁c i
  · exact Set.iUnion_subset fun i => hK₁f i
  · intro q hq
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hq
    exact hT₁ i q hi
  · intro h₁ k hk
    funext h₂
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hIS i).1 h₁ k (Subgroup.mem_iInf.1 hk i)]
  · intro h₁ hne
    have : ∃ i, (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) h₁ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hne
      funext h₂
      simp [hcon]
    obtain ⟨i, hi⟩ := this
    obtain ⟨q, hq, r, hr, a, ha, k, hk, e⟩ := (hIS i).2 h₁ hi
    exact ⟨q, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hq⟩, r, hr, a, ha, k, Set.mem_iUnion.2 ⟨i, hk⟩, e⟩
  · intro a ha a' ha'
    obtain ⟨v, hv, hsum⟩ := hV a ha a' ha'
    have := iteratedQuotientIntegral_finite_linearCombination (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) α _ v hv
    rw [hsum] at this
    exact this

end GlobalTheory.SeeSaw.VanMany
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.ReadLaws

theorem isInv_of_isUni {ι : Type} {n : ℕ} {u : ι → Matrix (Fin n) (Fin n) ℂ} (hu : IsUni u) : IsInv u := by
  intro τ
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp (hu τ))
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨_, h⟩

def trFr {ι : Type} {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : IsInv g)
    (y : Frames G) : Frames G :=
  ⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩

theorem continuous_valC {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {lam : ι → DomWeight n}
    {Φ : Frames G → ℂ} (hΦ : Φ ∈ ValC G lam) {X : Type} [TopologicalSpace X] {f : X → ι → Matrix (Fin n) (Fin n) ℂ}
    (hf : Continuous f) (hi : ∀ x τ, IsUnit (f x τ).det) : Continuous fun x => Φ ⟨f x, hi x⟩ := by
  obtain ⟨P, -, rfl⟩ := hΦ
  have e : (fun x => fnOf G (shiftOf lam) 1 P (⟨f x, hi x⟩ : Frames G)) =
      fun x => (∏ τ, (f x τ).det ^ shiftOf lam τ) * GlobalTheory.KJInf.evalAt (f x) P :=
    funext fun x => GlobalTheory.KJInf.ValPol.fnOf_one_apply _ P _
  rw [e]
  simp only [GlobalTheory.KJInf.ValPol.evalAt_eq]
  refine Continuous.mul (continuous_finsetProd _ fun τ _ => ?_) ?_
  · exact (((continuous_apply τ).comp hf).matrix_det).zpow₀ _ fun x => Or.inl (hi x τ).ne_zero
  · exact (MvPolynomial.continuous_eval P).comp
      (continuous_pi fun v => ((continuous_apply v.1).comp hf).matrix_elem v.2.1 v.2.2)

end GlobalTheory.SeeSaw.ReadLaws


open GlobalTheory.SeeSaw.ReadLaws in
theorem GlobalTheory.SeeSaw.scalarForm_laws : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → ρ.Is → A.Forms → ∀ j hj, ∀ ψ ∈ t.Ram j, ∀ β, (∀ y, IsContAut (c.X j) (t.rd j β ψ y)) ∧ (∀ y g (κ : A.U j β), t.rd j β ψ y (g * κ.1) = (A.chi j β κ : ℂ) * t.rd j β ψ y g) ∧ (∀ y y' g, ∀ k ∈ GinfC (c.X j), IsTr (ρ.r j hj k) (ρ.fr j y) (ρ.fr j y') → t.rd j β ψ y (g * k) = t.rd j β ψ y' g) ∧ ∀ g, (fun z => t.rd j β ψ ((ρ.fr j).symm z) g) ∈ ValC _ (ρ.lam j) := by
  intro D c t ρ A _hc hρ hA j hj ψ hψ β
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (c.X j)
  have hr := hρ.uni j hj
  have hinv : ∀ k : GinfC (c.X j), IsInv (ρ.r j hj k.1) := fun k => isInv_of_isUni (hr.uni k)
  have hR := hA.reps j hj β
  have hrd : ∀ y γ, γ ∈ GQ (c.X j) → ∀ a k (hk : k ∈ GinfC (c.X j)) (κ : A.U j β),
      t.rd j β ψ y (γ * (A.h j β a * k) * κ.1) =
        (A.chi j β κ : ℂ) * A.val j β ψ a (trFr (ρ.r j hj k) (hinv ⟨k, hk⟩) (ρ.fr j y)) :=
    fun y γ hγ a k hk κ => hA.rd j hj ψ hψ β y γ hγ a k hk κ _ (fun τ => rfl)
  have hcomm : ∀ k ∈ GinfC (c.X j), ∀ κ ∈ GfC (c.X j), k * κ = κ * k := fun k hk κ hκ =>
    (GlobalTheory.AutMult.commute_inf_fin (V := c.X j) ⟨k, hk⟩ ⟨κ, hκ⟩).eq
  refine ⟨fun y => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro γ' hγ' g
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ' * (γ * (A.h j β a * k) * κ) = (γ' * γ) * (A.h j β a * k) * (⟨κ, hκ⟩ : A.U j β).1 := by
      simp only [mul_assoc]
    rw [e, hrd y _ (mul_mem hγ' hγ) a k hk, hrd y γ hγ a k hk ⟨κ, hκ⟩]
  · rw [continuous_iff_continuousAt]
    intro g0
    obtain ⟨γ, hγ, a, k0, hk0, κ0, hκ0, rfl⟩ := hR.dec g0
    set q : GA D (c.X j) → GA D (c.X j) := fun g => (γ * A.h j β a)⁻¹ * g with hqdef
    have hq : Continuous q := continuous_const.mul continuous_id
    set W : Set (GA D (c.X j)) :=
      {g | ((GlobalTheory.AutMult.toFin (c.X j) (q g) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β} with hWdef
    have hW : IsOpen W := hR.opn.preimage ((GlobalTheory.AutMult.continuous_toFin (c.X j)).comp hq)
    have h0 : GlobalTheory.AutMult.toFin (c.X j) (q (γ * (A.h j β a * k0) * κ0)) = ⟨κ0, hR.le hκ0⟩ := by
      have e : q (γ * (A.h j β a * k0) * κ0) =
          ((⟨k0, hk0⟩ : GinfC (c.X j)) : GA D (c.X j)) * ((⟨κ0, hR.le hκ0⟩ : GfC (c.X j)) : GA D (c.X j)) := by
        show (γ * A.h j β a)⁻¹ * (γ * (A.h j β a * k0) * κ0) = k0 * κ0
        group
      rw [e, map_mul, GlobalTheory.AutMult.toFin_coe_inf, GlobalTheory.AutMult.toFin_coe, one_mul]
    have hg0 : γ * (A.h j β a * k0) * κ0 ∈ W := by
      show ((GlobalTheory.AutMult.toFin (c.X j) (q _) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β
      rw [h0]
      exact hκ0
    refine ContinuousOn.continuousAt ?_ (hW.mem_nhds hg0)
    rw [continuousOn_iff_continuous_restrict]
    have hU : ∀ g : W, ((GlobalTheory.AutMult.toFin (c.X j) (q g.1) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β := fun g => g.2
    show Continuous fun g : W => t.rd j β ψ y g.1
    have key : (fun g : W => t.rd j β ψ y g.1) = fun g : W => (A.chi j β ⟨_, hU g⟩ : ℂ) *
        A.val j β ψ a (trFr (ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1) (hinv _) (ρ.fr j y)) := by
      funext g
      have e : g.1 = γ * (A.h j β a * (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1) * (⟨_, hU g⟩ : A.U j β).1 := by
        have h1 := GlobalTheory.AutMult.toInf_mul_toFin (q g.1)
        calc g.1 = (γ * A.h j β a) * q g.1 := by
              show g.1 = (γ * A.h j β a) * ((γ * A.h j β a)⁻¹ * g.1)
              group
          _ = _ := by
              conv_lhs => rw [← h1]
              simp only [mul_assoc]
      exact (congrArg (t.rd j β ψ y) e).trans (hrd y γ hγ a _ (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).2 _)
    rw [key]
    refine Continuous.mul ?_ ?_
    · have hc : Continuous fun g : W => (⟨_, hU g⟩ : A.U j β) :=
        Continuous.subtype_mk (continuous_subtype_val.comp
          ((GlobalTheory.AutMult.continuous_toFin (c.X j)).comp (hq.comp continuous_subtype_val))) _
      exact (hA.chi j hj β).comp hc
    · have hk : Continuous fun g : W => ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1 :=
        hr.cont.comp ((GlobalTheory.AutMult.continuous_toInf (c.X j)).comp (hq.comp continuous_subtype_val))
      exact continuous_valC (f := fun g : W => fun τ => ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1 τ * (ρ.fr j y).1 τ)
        (hA.valC j hj ψ hψ β a) (continuous_pi fun τ => ((continuous_apply τ).comp hk).matrix_mul continuous_const) _
  · intro y g κ'
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ * (A.h j β a * k) * κ * κ'.1 = γ * (A.h j β a * k) * ((⟨κ, hκ⟩ : A.U j β) * κ').1 := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e, hrd y γ hγ a k hk, hrd y γ hγ a k hk ⟨κ, hκ⟩, map_mul, Units.val_mul]
    ring
  · intro y y' g k' hk' htr
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ * (A.h j β a * k) * κ * k' = γ * (A.h j β a * (k * k')) * (⟨κ, hκ⟩ : A.U j β).1 := by
      rw [mul_assoc _ κ k', ← hcomm k' hk' κ (hR.le hκ)]
      simp only [mul_assoc]
    rw [e, hrd y γ hγ a _ (mul_mem hk hk'), hrd y' γ hγ a k hk ⟨κ, hκ⟩]
    have hY : trFr (ρ.r j hj (k * k')) (hinv ⟨k * k', mul_mem hk hk'⟩) (ρ.fr j y) =
        trFr (ρ.r j hj k) (hinv ⟨k, hk⟩) (ρ.fr j y') := by
      apply Subtype.ext
      funext τ
      have hm : ρ.r j hj (k * k') τ = ρ.r j hj k τ * ρ.r j hj k' τ := hr.mul ⟨k, hk⟩ ⟨k', hk'⟩ τ
      show ρ.r j hj (k * k') τ * (ρ.fr j y).1 τ = ρ.r j hj k τ * (ρ.fr j y').1 τ
      rw [htr τ, hm, Matrix.mul_assoc]
    rw [hY]
  · intro g
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have hv := hA.valC j hj ψ hψ β a
    refine (GlobalTheory.KJInf.valC_poly _ _ _ _).2.2.1 ((A.chi j β ⟨κ, hκ⟩ : ℂ) • A.val j β ψ a) (Submodule.smul_mem _ _ hv)
      (ρ.r j hj k) _ ?_ (hinv ⟨k, hk⟩)
    intro z z' hz
    rw [hA.rd j hj ψ hψ β _ γ hγ a k hk ⟨κ, hκ⟩ z' (by rwa [Equiv.apply_symm_apply])]
    rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitWeilPhiInnerProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem phiQ_ip : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ), r ≤ a → r ≤ b → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (phiQ (a := a) (b := b) v r mu) (phiQ (a := a) (b := b) v r mu) = (((GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal * (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (b - r)))⁻¹) : ℝ) : ℂ) ∧ phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  intro D PP v φ hP a b r hra hrb ξ mu hL ν hν
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  refine ⟨?_, GlobalTheory.T.twistPlaceChainStepDatum_mem_schwartzBruhat D PP v φ hP a b r ξ mu hL⟩
  have h1 := _root_.GlobalTheory.NrmVol.phiQ_mul_conj_eq_indicator D PP v φ hP a b r ξ mu hL
  have h3 := GlobalTheory.T.measurableSet_twistPlaceChainStepDatumMatrixSupport D v a b r
  obtain ⟨e1, e2⟩ := GlobalTheory.T.twistPlaceChainStepDatumSupport_eq_valuative D v a b r
  have h4 := _root_.GlobalTheory.RectBlockVolume.vol_topBlock_KO (Fv D.host.F v) ν hν a b r hra hrb
  rw [← e1, ← e2, (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hP).2] at h4
  unfold GlobalTheory.SplitWeil.ip
  simp_rw [h1]
  rw [integral_indicator_const _ h3, Measure.real, h4, zinv]
  simp

end GlobalTheory.NrmVol
end
end

