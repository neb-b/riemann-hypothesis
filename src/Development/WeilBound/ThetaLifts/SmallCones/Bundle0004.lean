module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0003
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0001
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0002
public import Development.WeilBound.ThetaLifts.SmallCones.UnfPar
public import Development.WeilBound.ThetaLifts.SmallCones.UnfAbs
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0025

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeEx
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem int_prod {α β : Type} [TopologicalSpace α] [TopologicalSpace β] [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α]
    [BorelSpace β] [SecondCountableTopology α] [SecondCountableTopology β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    {θ : α × β → ℂ} (hθ : Continuous θ) {w : α → ℂ} (hw : Continuous w) {a : α → ℝ} (ha : ∀ l, ‖w l‖ = a l)
    (hfin : ∫⁻ l, (∫⁻ g, ‖θ (l, g)‖ₑ ∂ν) * ENNReal.ofReal (a l) ∂μ < ⊤) : Integrable (fun x => θ x * w x.1) (μ.prod ν) := by
  have hc : Continuous fun x : α × β => θ x * w x.1 := hθ.mul (hw.comp continuous_fst)
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hc.measurable.enorm.aemeasurable]
  convert hfin using 3 with l
  simp only [enorm_mul]
  rw [lintegral_mul_const' _ _ (by simp), ← ha, ofReal_norm_eq_enorm]

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure LineOK (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (M₀ : Model σ X₁ W₁) (om₀ : Rep σ X₁ W₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (μ : Measure (AE F E)ˣ) (u : (AE F E)ˣ → Ten F E n d) (ν : Chr F E) (z : ℕ)
    (S : Submodule ℂ (Fn F n d)) : Prop where
  le : ∀ Ψ ∈ S, Ψ ∈ schA F (Fin n × Fin d)
  stab : ∀ x, ∀ Ψ ∈ S, om x Ψ ∈ S
  sch : ∀ l, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u l) Ψ) ∈ schA F (Fin n₁ × Fin d₁)
  th : ∀ g h, ∃ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), ∀ Φ ∈ schA F _, l Φ = theta om₀ Φ g h
  int : ∀ Ψ ∈ S, ∀ h₁, Integrable (fun x : (AE F E)ˣ × UA σ X₁.J =>
    theta om₀ (e (M.co.rho B.ψ (u x.1) Ψ)) x.2 h₁ * ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z)) (μ.prod (M₀.μ.restrict M₀.dom))
  lam : ∀ Ψ ∈ schA F (Fin n × Fin d), ∃ Ψ₁ ∈ schA F (Fin n₁ × Fin d₁), ∀ l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
    Integrable (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) μ ∧
    l₁ Ψ₁ = ∫ l, l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁}
  {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν : Chr F E} {z : ℕ}
  {S : Submodule ℂ (Fn F n d)}

theorem LineOK.theta_sum (h : LineOK B M om M₀ om₀ e μ u ν z S) {m : ℕ} (c : Fin m → ℂ) {Ψ : Fin m → Fn F n₁ d₁}
    (hΨ : ∀ i, Ψ i ∈ schA F (Fin n₁ × Fin d₁)) (g h₁) : theta om₀ (∑ i, c i • Ψ i) g h₁ = ∑ i, c i * theta om₀ (Ψ i) g h₁ := by
  obtain ⟨l, -, hl⟩ := h.th g h₁
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hl _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΨ i)), map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hl _ (hΨ i), smul_eq_mul]

theorem LineOK.val_sum (h : LineOK B M om M₀ om₀ e μ u ν z S) {m : ℕ} (c : Fin m → ℂ) {Ψ : Fin m → Fn F n d} (hΨ : ∀ i, Ψ i ∈ S)
    (l g h₁) : theta om₀ (e (M.co.rho B.ψ (u l) (∑ i, c i • Ψ i))) g h₁ =
      ∑ i, c i * theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rho_linear, map_sum]
  simp only [map_smul]
  exact h.theta_sum c (fun i => h.sch l _ (h.le _ (hΨ i))) g h₁

theorem LineOK.coneI_eq [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (h₁ : UA σ W₁.J) :
    coneI B M om M₀ om₀ e K μK μ u ν z Φ h₁ = M₀.I om₀ (cone B M om e K μK μ u ν z Φ) h₁ := by
  choose Λ hΛ hΛ' using fun i => h.lam (Ψ i) (h.le _ (hΨ i))
  have h1 : cone B M om e K μK μ u ν z Φ = ∑ i, (∫ k, c i k ∂μK) • Λ i := by
    funext y
    have e1 : ∀ k : K, ∫ l, e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ =
        ∑ i, c i k * Λ i y := fun k => by
      have e2 := fun i => hΛ' i _ (ev_adm y)
      simp only [LinearMap.proj_apply] at e2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hd, rho_linear, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [integral_finsetSum _ fun i _ => by simpa only [mul_assoc] using (e2 i).1.const_mul (c i k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(e2 i).2, ← integral_const_mul]
      simp only [mul_assoc]
    simp only [cone, e1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ fun i _ => (hc i).mul_const _]
    simp only [integral_mul_const]
  have h2 : ∀ i g, theta om₀ (Λ i) g h₁ =
      ∫ l, theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ∂μ := fun i g => by
    obtain ⟨l, hl, hl'⟩ := h.th g h₁
    rw [← hl' _ (hΛ i), (hΛ' i l hl).2]
    simp only [hl' _ (h.sch _ _ (h.le _ (hΨ i))), mul_assoc]
  have h3 : ∀ i, IntegrableOn (fun g => theta om₀ (Λ i) g h₁) M₀.dom M₀.μ := fun i => by
    simp only [h2]
    exact (h.int _ (hΨ i) h₁).integral_prod_right
  set T : Fin m → ℂ := fun i => M₀.I om₀ (Λ i) h₁ with hT
  have h4 : ∀ i, ∫ l, M₀.I om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ∂μ = T i := fun i => by
    simp only [hT, Model.I, h2]
    rw [← integral_integral_swap (h.int _ (hΨ i) h₁)]
    simp only [integral_mul_const]
  have h5 : ∀ i, Integrable (fun l => M₀.I om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) μ :=
    fun i => by
      have := (h.int _ (hΨ i) h₁).integral_prod_left
      simpa only [integral_mul_const, Model.I] using this
  have h6 : ∀ k : K, ∫ l, M₀.I om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) h₁ * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ =
      ∑ i, c i k * T i := fun k => by
    rw [← Finset.sum_congr rfl fun i _ => congrArg (c i k * ·) (h4 i)]
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ fun i _ => (h5 i).const_mul _]
    refine integral_congr_ae ?_
    have : ∀ᵐ l ∂μ, ∀ i, Integrable (fun g => theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ *
        ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) (M₀.μ.restrict M₀.dom) :=
      ae_all_iff.2 fun i => (h.int _ (hΨ i) h₁).prod_right_ae
    filter_upwards [this] with l hl
    simp only [Model.I, hd, h.val_sum _ hΨ, mul_assoc, ← integral_mul_const, ← integral_const_mul, Finset.sum_mul]
    rw [integral_finsetSum _ fun i _ => (hl i).const_mul _]
  rw [h1]
  simp only [coneI, h6]
  rw [integral_finsetSum _ fun i _ => (hc i).mul_const _]
  simp only [integral_mul_const, Model.I, h.theta_sum _ hΛ]
  rw [integral_finsetSum _ fun i _ => (h3 i).const_mul _]
  simp only [integral_const_mul, hT, Model.I]

end Core

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.GenAnisoOf
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}

theorem dom_change (hG : GrpTop) (hE : EpsOf) (hB : B.IsGood σ) {r s : ℕ} (hX : X.IsHerm σ B r s)
    {m m' : Measure (UA σ X.J)} {D D' : Set (UA σ X.J)} (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure)
    (hd : IsFundamentalDomain (ratU σ X.J) D m) (hd' : IsFundamentalDomain (ratU σ X.J) D' m') :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : UA σ X.J → ℂ, (∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g) →
      ∫ g in D, φ g ∂m = c * ∫ g in D', φ g ∂m' := by
  obtain ⟨b1, b2, b3, b4, -⟩ := hG F E σ hB.cm n X.J (hE F E σ B hB n X r s (Or.inl hX)).1
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hc : m = Measure.haarScalarFactor m m' • m' := Measure.isMulLeftInvariant_eq_smul m m'
  have hpos : 0 < Measure.haarScalarFactor m m' := Measure.haarScalarFactor_pos_of_isHaarMeasure m m'
  have hac : m ≪ m' := by
    rw [hc]; exact Measure.smul_absolutelyContinuous
  have hd'' : IsFundamentalDomain (ratU σ X.J) D' m := hd'.mono hac
  refine ⟨((Measure.haarScalarFactor m m' : NNReal) : ℂ), ?_, fun φ hφ => ?_⟩
  · exact_mod_cast hpos.ne'
  · have h1 : ∫ g in D, φ g ∂m = ∫ g in D', φ g ∂m := hd.setIntegral_eq hd'' fun γ g => hφ γ γ.2 g
    rw [h1]
    conv_lhs => rw [hc]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]

theorem isLevi_one : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 1 :=
  ⟨by rw [mat_one', Matrix.one_mulVec, Units.val_one, one_smul],
    by rw [mat_one', Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul],
    by rw [mat_one', mat_one', Matrix.one_mul, Matrix.mul_one]⟩

theorem weil_bound (hW : WeilConv) {M : Model σ X W} {χX χW om r s r' s'} (hp : IsPair B M χX χW om r s r' s')
    (hr : d + 2 * min r s < 2 * n ∨ min r s = 0) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ (C : ℝ) (k : ℕ), ∀ h, ∫⁻ g in M.dom, ‖theta om Φ g h‖ₑ ∂M.μ ≤ ENNReal.ofReal (C * (ht h : ℝ) ^ k) := by
  obtain ⟨h1, C, k, h2⟩ := (hW F E σ B n d X W M χX χW om r s r' s' hp hr).1 Φ hΦ
  refine ⟨C, k, fun h => ?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm (h1 h)]
  exact ENNReal.ofReal_le_ofReal (h2 h)

theorem zero_term (hM : MixW) (hT : ThetaBasic) {M : Model σ X W} {M₁ : Model σ X W₁} {χX χW om om₁ r s r' s' r₁ s₁ i₀ i₁}
    (hp : IsPair B M χX χW om r s r' s') (hp₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    {e} (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) {c : ℂ} (hc : ∀ φ : UA σ X.J → ℂ, (∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g) →
      ∫ g in M.dom, φ g ∂M.μ = c * ∫ g in M₁.dom, φ g ∂M₁.μ) (C₀ : ℂ) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    HasLaw W₁ H' χX ((n : ℝ) / 2) (fun h => ∫ g in M.dom, C₀ * thetaSum F (e (om (g, h) Φ)) ∂M.μ) ∧
      ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h, ∫ g in M.dom, C₀ * thetaSum F (e (om (g, p * h) Φ)) ∂M.μ =
        C₀ * c * M₁.I om₁ (e (om (1, h) Φ)) h₁ := by
  have key : ∀ g t h₁ p, IsLevi H' t h₁ p → ∀ h, thetaSum F (e (om (g, p * h) Φ)) =
      (χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * theta om₁ (e (om (1, h) Φ)) g h₁ := fun g t h₁ p hl h => by
    have := hM F E σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hp₁ e he g t h₁ p hl 1 (one_mem _) _
      (pair_pres hp (1, h) hΦ)
    rw [om_mul, Prod.mk_mul_mk, mul_one, one_mul] at this
    rw [this, thetaSum_smul', theta]
  have key1 : ∀ g h₁ p, IsLevi H' 1 h₁ p → ∀ h, thetaSum F (e (om (g, p * h) Φ)) = theta om₁ (e (om (1, h) Φ)) g h₁ :=
    fun g h₁ p hl h => by rw [key g 1 h₁ p hl h]; simp
  refine ⟨fun t m hl h => ?_, fun h₁ p hl h => ?_⟩
  · simp only [key _ t 1 m hl h, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have := key1 g 1 1 isLevi_one h
    rw [one_mul] at this
    simp only [this]
    ring
  · obtain ⟨-, t2, -⟩ := (hT F E σ B n d₁ X W₁ M₁ χX χW om₁ r s r₁ s₁ hp₁).1 _ (he.maps _ (pair_pres hp (1, h) hΦ))
    simp only [key1 _ h₁ p hl h]
    rw [integral_const_mul, hc _ fun γ hγ g => by simpa using t2 γ hγ 1 (one_mem _) g h₁, mul_assoc, Model.I]

theorem genAniso_of (hK : CTKernel) (hF : CTFub) (hM : MixW) (hW : WeilConv) (hT : ThetaBasic) (hWi : Witt) (hG : GrpTop)
    (hE : EpsOf) : GenAniso := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ H' i₀ i₁ r s r' s' r₁ s₁ X' M M₁ hX hrs hH e he
  subst hX
  by_cases h0 : ∃ χX χW om om₁, IsPair B M χX χW om r s r' s' ∧ IsPair B M₁ χX χW om₁ r s r₁ s₁
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om om₁ h1 h2 => absurd ⟨χX, χW, om, om₁, h1, h2⟩ h0⟩
  obtain ⟨_, _, _, _, q, q₁⟩ := h0
  obtain ⟨C₀, hC₀, h1, -⟩ := hK F E σ B n d d₁ X' W W₁ M M₁ H' i₀ i₁ hH q₁.good e he
  obtain ⟨c, hc0, hc⟩ := dom_change hG hE q.base q.herm q.good.haar q₁.good.haar q.good.dom q₁.good.dom
  refine ⟨C₀ * c, mul_ne_zero hC₀ hc0, fun χX χW om om₁ hp hp₁ Φ hΦ => ?_⟩
  obtain ⟨z1, z2⟩ := zero_term hM hT hp hp₁ hH he hc C₀ hΦ
  exact ⟨_, (hF F E σ B n d X' W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ (weil_bound hW hp (Or.inr hrs) hΦ) _
    (h1 ((hWi F E σ B n X' r s hp.base hp.herm).1 hrs) χX χW om r s r' s' hp Φ hΦ)).2, z1, z2⟩

theorem genBig_of (hK : CTKernel) (hF : CTFub) (hA : ConeA) (hM : MixW) (hW : WeilConv) (hT : ThetaBasic) (hWi : Witt)
    (hG : GrpTop) (hE : EpsOf) : GenBig := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ e g₁ g₀ he₀ he z hz K μK μ hI hμK hμ
  by_cases h0 : ∃ χX χW om, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1)
  swap
  · exact ⟨1, 1, one_ne_zero, one_ne_zero, fun χX χW om _ _ h1 => absurd ⟨χX, χW, om, h1⟩ h0⟩
  obtain ⟨_, _, _, q⟩ := h0
  obtain ⟨C₀, hC₀, -, h1⟩ := hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' g₁ e₀ he₀
  obtain ⟨C₁, hC₁, h2⟩ := h1 n₁ X₁ H j₀ j₁ M₀ hH g₀ e he
  obtain ⟨κ, hκ, h3⟩ := hA F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨c, hc0, hc⟩ := dom_change hG hE q.base q.herm q.good.haar g₁.haar q.good.dom g₁.dom
  obtain ⟨γ, hγ⟩ := (hWi F E σ B n X _ _ q.base q.herm).2 n₁ H (adapted_x_ne hH) hH.xx
  refine ⟨C₀ * c, C₁ * κ, mul_ne_zero hC₀ hc0, mul_ne_zero hC₁ hκ, fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ hfin => ?_⟩
  obtain ⟨z1, z2⟩ := zero_term hM hT hp hp₁ hH' he₀ hc C₀ hΦ
  obtain ⟨a1, a2, a3⟩ := h3 χX χW om om₀ hp hp₀ Φ hΦ hfin
  obtain ⟨f1, f2⟩ := hF F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ hH' Φ hΦ
    (weil_bound hW hp (Or.inl (by omega)) hΦ) _ fun g => (h2 γ hγ χX χW om _ _ _ _ hp Φ hΦ g).2
  refine ⟨_, fun h => C₁ * κ * coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) 1, ?_, z1,
    fun t m hl h => ?_, fun h₁ p hl h => ⟨?_, z2 h₁ p hl h⟩⟩
  · convert f2 using 1
    funext h
    obtain ⟨-, b2, b3⟩ := a1 γ hγ h
    have b4 := b2.const_mul C₁
    have b5 := (f1 h).sub b4
    rw [Pi.add_apply, mul_assoc, ← b3, ← integral_const_mul, ← integral_add _ b4]
    · rfl
    · refine b5.congr (Eventually.of_forall fun g => ?_)
      exact add_sub_cancel_right _ _
  · simp only [a2 t 1 m hl h]
    ring
  · simp only [a2 1 h₁ p hl h, a3]
    simp

end PositivityTheory.ThKCT
end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.UnfParH
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.PlacePermOperatorBicommutantSpan
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.Doubling (absE)

noncomputable section

namespace PositivityTheory.ThKCT.Unf

theorem Par.transport {G G' N H H' T : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [TopologicalSpace N]
    [MeasurableSpace N] [Group H] [TopologicalSpace H] [Group H'] [TopologicalSpace H'] [CommGroup T] [TopologicalSpace T]
    {μN : Measure N} {nn : N → G} {ι : H →* G} {mm : T →* G} {χ : T →* ℝ≥0} (h : Par μN nn ι mm χ) (Φ : G ≃ₜ* G') (Ψ : H ≃ₜ* H') :
    Par μN (fun p => Φ (nn p)) ((Φ : G →* G').comp (ι.comp (Ψ.symm : H' →* H))) ((Φ : G →* G').comp mm) χ := by
  refine ⟨Φ.continuous.comp h.cn, Φ.continuous.comp (h.ci.comp Ψ.symm.continuous),
    Φ.continuous.comp h.cm, h.cχ, ?_, ?_, ?_, ?_, ?_, h.ne⟩
  · have := (Φ.toHomeomorph.isClosedEmbedding.comp h.emb).comp
      ((Homeomorph.refl N).prodCongr (Ψ.symm.toHomeomorph.prodCongr (Homeomorph.refl T))).isClosedEmbedding
    refine (congrArg IsClosedEmbedding (funext fun z => ?_)).mp this
    exact (map_mul Φ _ _).trans (congrArg (· * _) (map_mul Φ _ _))
  · intro p
    obtain ⟨L, a, b⟩ := h.h1 p
    exact ⟨L, a, fun x => by rw [← map_mul, b]⟩
  · intro u
    obtain ⟨L, a, b⟩ := h.h2 (Ψ.symm u)
    exact ⟨L, a, fun x => (map_mul Φ _ _).symm.trans ((congrArg Φ (b x)).trans (map_mul Φ _ _))⟩
  · intro t
    obtain ⟨L, a, b, c⟩ := h.h3 t
    exact ⟨L, a, b, fun x => (map_mul Φ _ _).symm.trans ((congrArg Φ (c x)).trans (map_mul Φ _ _))⟩
  · intro u t
    exact (map_mul Φ _ _).symm.trans ((congrArg Φ (h.h4 _ t)).trans (map_mul Φ _ _))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem parH (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) :
    ∃ (N : Type) (_ : TopologicalSpace N) (_ : SecondCountableTopology N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (μN : Measure N) (_ : SigmaFinite μN) (_ : IsFiniteMeasureOnCompacts μN) (nn : N → HA (AF F) σ (hypJ J))
      (ι : HA (AF F) σ J →* HA (AF F) σ (hypJ J)) (mm : (AF F ⊗[F] E)ˣ →* HA (AF F) σ (hypJ J)) (χ : (AF F ⊗[F] E)ˣ →* ℝ≥0) (p₀ : N),
      Par μN nn ι mm χ ∧ (∀ a, χ a * absE F E a ^ (M + 1) = 1) ∧ nn p₀ = 1 ∧
      (∀ p u (a : (AF F ⊗[F] E)ˣ), ∃ b r w, (nn p * ι u * mm a).1.val =
        pm (a : AF F ⊗[F] E) b r (sigR (AF F) σ (a⁻¹ : (AF F ⊗[F] E)ˣ)) w u.1.val ∧ (p = p₀ → b = 0 ∧ r = 0 ∧ w = 0)) ∧
      (∀ (h : HA (AF F) σ (hypJ J)) (a : (AF F ⊗[F] E)ˣ), h.1.val *ᵥ Pi.single 0 1 = (a : AF F ⊗[F] E) • Pi.single 0 1 →
        ∃ p u, h = nn p * ι u * mm a) ∧
      (∀ p, ∃ R : N → N, MeasurePreserving R μN μN ∧ ∀ x, nn x * nn p = nn (R x)) ∧
      ∃ C : Set N, IsCompact C ∧ ∀ p, ∃ q, HA.mat (AF F) σ (hypJ J) (nn q) ∈ HFin (AF F) σ (hypJ J) ∧ ∃ p' ∈ C, nn q * nn p = nn p' := by
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 M
  have : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm M J hJ (AF F)
  obtain ⟨nn, ι, mm, c, hval, hΨ, cn, ci, cm, cc, n0, nmul, -, hin, hmn, hmi, -, hdec, rn, -, -⟩ := par2 F E σ hcm M J hJ
  set μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E) := Measure.addHaar with hμW
  set μA : Measure (AF F) := Measure.addHaar with hμA
  obtain ⟨χ, χc, χ1, χ2⟩ := modulus hcm M μW μA inferInstance inferInstance
  obtain ⟨⟨CW, hCW, hW⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.CocW.main F E σ hcm 1 M
  obtain ⟨⟨CA, hCA, hA⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact F
  refine ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, μW.prod μA, inferInstance, inferInstance, nn, ι, mm, χ,
    (0, 0), ⟨cn, ci, cm, χc, hΨ, fun p => ⟨fun x => (p.1 + x.1, p.2 + x.2 + c p.1 x.1), ?_, fun x => nmul _ _ _ _⟩,
      fun u => ⟨Prod.map (actW (AF F) σ J u) id, ?_, fun x => hin u _ _⟩, fun t => ⟨_, ?_, χ1 t, fun x => hmn t _ _⟩, hmi,
      NeZero.ne _⟩, χ2, n0, fun p u a => ?_, fun h a ha => hdec h a ?_,
    fun p => ⟨fun x => (x.1 + p.1, x.2 + p.2 + c x.1 p.1), ?_, fun x => nmul _ _ _ _⟩, CW ×ˢ CA, hCW.prod hCA, fun ⟨w, t⟩ => ?_⟩
  · refine (measurePreserving_add_left μW p.1).skew_product (g := fun w y => p.2 + y + c p.1 w) ?_ (ae_of_all _ fun w => ?_)
    · exact ((continuous_const.add continuous_snd).add (cc.comp (continuous_const.prodMk continuous_fst))).measurable
    · simpa only [add_right_comm p.2] using map_add_left_eq_self μA (p.2 + c p.1 w)
  · exact MeasurePreserving.prod ⟨((hact 1).1.comp (continuous_const.prodMk continuous_id)).measurable,
      _root_.GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq F E σ hcm M J hJ μW inferInstance u⟩ (MeasurePreserving.id μA)
  · exact Continuous.measurable (by fun_prop)
  · obtain ⟨b, r, e1, e2⟩ := hval p u a
    exact ⟨b, r, _, e1, fun hp => ⟨(e2 hp).1, (e2 hp).2, by rw [hp]; exact smul_zero _⟩⟩
  · have e : eOne (AF F ⊗[F] E) (M + 1) = fun _ => Pi.single 0 1 := by
      funext k i
      refine Fin.cases rfl (fun i => ?_) i
      simp [eOne]
    rw [e]
    exact funext fun _ => ha
  · refine (measurePreserving_add_right μW p.1).skew_product (g := fun w y => y + p.2 + c w p.1) ?_ (ae_of_all _ fun w => ?_)
    · exact ((continuous_snd.add continuous_const).add (cc.comp (continuous_fst.prodMk continuous_const))).measurable
    · simpa only [add_assoc] using map_add_right_eq_self μA (p.2 + c w p.1)
  · obtain ⟨X, hX⟩ := hW w
    obtain ⟨r, hr⟩ := hA (t + c (ratTup (AF F) (-X)) w)
    refine ⟨_, rn (-X) (-r), _, ⟨?_, ?_⟩, nmul _ _ _ _⟩
    · have e : ratTup (F := F) (AF F) (-X) = -ratTup (AF F) X := funext fun a => funext fun i => map_neg _ _
      rwa [e, neg_add_eq_sub]
    · rwa [map_neg, add_assoc, neg_add_eq_sub]

end PositivityTheory.ThKCT.Unf
end
end

