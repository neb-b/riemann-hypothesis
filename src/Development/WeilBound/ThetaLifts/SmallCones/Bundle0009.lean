module

public import Development.WeilBound.ThetaLifts.SmallCones.KerPol
public import Development.WeilBound.ThetaLifts.SmallCones.KerUni
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.SmallCones.IsoActFree
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0008
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0004
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0001
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0002
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConstantTermRationalUnipotentInvariant
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open GlobalTheory.Doubling (absE)
open Matrix (vecMulVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
variable {H : Plane E n n₁} {H' : Plane E d d₁} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

def tm (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (H' : Plane E d d₁) {n₂ d₂ : ℕ} (e : Fn F n d →ₗ[ℂ] Fn F n₂ d₂)
    (U : Matrix (Fin n) (Fin d) E) (Φ : Fn F n d) (u : unip σ W H') : ℂ :=
  thetaSum F (e (M.co.rho B.ψ (incM F U) (om (1, u.1) Φ)))

section Gen

variable {n₂ d₂ : ℕ} {X₂ : Spc F E n₂} {W₂ : Spc F E d₂} {M₂ : Model σ X₂ W₂} {e : Fn F n d →ₗ[ℂ] Fn F n₂ d₂}
  {ι : Matrix (Fin n) (Fin n₂) E} {ι' : Matrix (Fin d) (Fin d₂) E} {I : Set (Ten F E n d)}

theorem tm_cont (hA : EvAdm) (hp : IsPair B M χX χW om r s r' s') (hM₂ : M₂.IsGood B.ψ) (he : IsEv B M M₂ ι ι' I e) (U) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : Continuous (tm B M om H' e U Φ) := by
  obtain ⟨⟨l, hl, hθ⟩, -, h⟩ := hA F E σ B n d n₂ d₂ X W X₂ W₂ M M₂ hp.base hp.good hM₂
  obtain ⟨l', hl', h'⟩ := h ι ι' I e he (incM F U) l hl
  have hc := ((IsUWeilPair.isUSplitting hp.weil).cont l' hl' Φ hΦ).comp
    (f := fun u : unip σ W H' => ((1 : UA σ X.J), u.1)) (continuous_const.prodMk continuous_subtype_val)
  refine hc.congr fun u => ?_
  rw [Function.comp_apply, h' _ (om_mem hp _ hΦ), hθ _ (he.maps _ (rho_mem M hp.base.std _ (om_mem hp _ hΦ)))]
  rfl

theorem tm_eq (hp : IsPair B M χX χW om r s r' s') (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ)
    (U) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : unip σ W H') :
    tm B M om H' e U Φ u = thetaSum F (e (M.co.rho B.ψ (incM F U * (mat u.1⁻¹)ᵀ) Φ)) := by
  rw [tm, rho_om hp _ _ hΦ, hi _ u.2 _ (rho_mem M hp.base.std _ hΦ)]

theorem tm_mul (U) (Φ) (u v : unip σ W H') : tm B M om H' e U Φ (u * v) = tm B M om H' e U (om (1, v.1) Φ) u := by
  rw [tm, tm, om_om]
  simp

theorem tm_one (U) (Φ) : tm B M om H' e U Φ 1 = thetaSum F (e (M.co.rho B.ψ (incM F U) Φ)) := by
  rw [tm, show ((1 : UA σ X.J), (1 : unip σ W H').1) = 1 from rfl, map_one]
  rfl

end Gen


variable (σ W H') in
structure MeanOK (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')) : Prop where
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  dom : IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ
  one : μ 𝓕 = 1
  cnt : Countable (ratU σ W.J)

variable {μ : Measure (unip σ W H')} {𝓕 : Set (unip σ W H')}

theorem MeanOK.zero (h : MeanOK σ W H' μ 𝓕) {f : unip σ W H' → ℂ} (hl : ∀ γ : unip σ W H', γ.1 ∈ ratU σ W.J → ∀ x, f (γ * x) = f x)
    {g} {c : ℂ} (hc : c ≠ 1) (hr : ∀ x, f (x * g) = c * f x) : ∫ x in 𝓕, f x ∂μ = 0 := by
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have := h.haar
  have := h.right
  have := h.cnt
  have : Countable ((ratU σ W.J).subgroupOf (unip σ W H')) :=
    Function.Injective.countable (f := fun x => (⟨x.1.1, x.2⟩ : ratU σ W.J)) fun a b e =>
      Subtype.ext (Subtype.ext (congrArg (fun y : ratU σ W.J => y.1) e))
  exact mean_zero _ μ h.dom hl hc hr

theorem MeanOK.sum (h : MeanOK σ W H' μ 𝓕) {ι : Type} [Countable ι] {f : ι → unip σ W H' → ℂ} (hf : ∀ i, Continuous (f i))
    {b : ι → ℝ} (hb : Summable b) (hfb : ∀ i x, ‖f i x‖ ≤ b i) {s : unip σ W H' → ℂ} (hs : ∀ x, HasSum (fun i => f i x) (s x)) :
    HasSum (fun i => ∫ x in 𝓕, f i x ∂μ) (∫ x in 𝓕, s x ∂μ) := by
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hb' : BorelSpace (unip σ W H') := Subtype.borelSpace _
  exact @mean_hasSum (unip σ W H') _ _ hb' _ _ μ _ h.one _ hf _ hb hfb _ hs

theorem MeanOK.const (h : MeanOK σ W H' μ 𝓕) (c : ℂ) : ∫ _x in 𝓕, c ∂μ = c := by
  rw [setIntegral_const, Measure.real, h.one, ENNReal.toReal_one, one_smul]

theorem exists_psi {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) : ∃ a, ψ a ≠ 1 := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 (std_ne_one h)
  exact ⟨a, by simpa using ha⟩

theorem bf0 {R : Type} [CommRing R] {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} (u) : bf c J u 0 = 0 := by
  simpa using bf_smul_r (c := c) (J := J) 0 u 0

theorem mid_vv (a : Fin n → AE F E) (z : Fin d₁ → AE F E) : vecMulVec a (incM F H'.ι *ᵥ z) =
    incM F (1 : Matrix (Fin n) (Fin n) E) * vecMulVec a z * (incM F H'.ι)ᵀ := by
  rw [incM_one, Matrix.one_mul, vv_mul_r]

section Zero

variable {M₁ : Model σ X W₁} {e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁}

theorem constant_term_norm_eq_theta (hp : IsPair B M χX χW om r s r' s') (h' : PG σ W W₁ H' (-1)) (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ) (x : Fin n → E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : unip σ W H') : ∃ w, ‖tm B M om H' e₀ (vecMulVec x H'.y) Φ u‖ =
      ‖thetaSum F (M₁.co.rho B.ψ w (e₀ (M.co.rho B.ψ (incM F (vecMulVec x H'.y)) Φ)))‖ := by
  obtain ⟨a, z, e⟩ := unip_y h' (inv_mem u.2)
  have h := hp.base.std
  refine ⟨vecMulVec (incV F x) z, ?_⟩
  rw [tm_eq hp hi _ hΦ, incM_vv, vv_mul_r, e, Matrix.vecMulVec_add, Matrix.vecMulVec_add, add_assoc,
    ev_I h he ⟨a • incV F x, by rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]⟩ _ hΦ, mid_vv, ev_mid h he _ _ hΦ,
    theta_smul, theta_smul, norm_mul, norm_mul, std_norm h, std_norm h, one_mul, one_mul]

theorem constant_term_rational_unipotent_invariant (hp : IsPair B M χX χW om r s r' s') (h' : PG σ W W₁ H' (-1)) (hM₁ : M₁.IsGood B.ψ)
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ) (x : Fin n → E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (γ : unip σ W H') (hγ : γ.1 ∈ ratU σ W.J) (u : unip σ W H') :
    tm B M om H' e₀ (vecMulVec x H'.y) Φ (γ * u) = tm B M om H' e₀ (vecMulVec x H'.y) Φ u := by
  obtain ⟨a, z, e⟩ := unip_y_rat h' (inv_mem γ.2) (inv_mem hγ)
  have h := hp.base.std
  have hΨ := om_mem hp (1, u.1) hΦ
  have e1 : vecMulVec (incV F x) (incV F (H'.ι *ᵥ z)) =
      incM F (1 : Matrix (Fin n) (Fin n) E) * incM F (vecMulVec x z) * (incM F H'.ι)ᵀ := by rw [← inc_mulVec, mid_vv, incM_vv]
  rw [tm_mul, tm_eq hp hi _ hΨ, incM_vv, vv_mul_r, e, Matrix.vecMulVec_add, Matrix.vecMulVec_add, add_assoc,
    ev_I h he ⟨inclR (F := F) (AF F) a • incV F x, by rw [incV_smul, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]⟩ _ hΨ,
    ← incM_vv, ← incM_vv, ← incM_vv, ← incM_add, psi_rat h, one_smul, incM_add, incM_vv x (H'.ι *ᵥ z), e1, ev_mid h he _ _ hΨ, ← e1,
    ← incM_vv, psi_rat h, one_smul, theta_rho_rat h hM₁]
  rfl

theorem constant_term_anisotropic_integral_zero (hm : MeanOK σ W H' μ 𝓕) (hp : IsPair B M χX χW om r s r' s') (h' : PG σ W W₁ H' (-1)) (hM₁ : M₁.IsGood B.ψ)
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Φ) = e₀ Φ) {x : Fin n → E} (hx : form σ X.J x x ≠ 0) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : ∫ u in 𝓕, tm B M om H' e₀ (vecMulVec x H'.y) Φ u ∂μ = 0 := by
  have h := hp.base.std
  obtain ⟨a, ha⟩ := exists_psi h
  have hq : σ (form σ X.J x x) = form σ X.J x x := by
    rw [PositivityTheory.ThKG.Tow.Pln.form_swap hp.base.cm (ε := 1) (fun i j => by rw [hp.herm.herm, one_mul]), one_mul]
  set c : AE F E := algebraMap (AF F) (AE F E) a * inclR (F := F) (AF F) (form σ X.J x x)⁻¹ with hc
  obtain ⟨g, hg⟩ := exists_eich h' 0 c (by
    rw [hc, map_mul, AlgHom.commutes, cA_inc, map_inv₀ σ, hq, Matrix.mulVec_zero, bf0]
    push_cast
    ring)
  refine hm.zero (constant_term_rational_unipotent_invariant hp h' hM₁ he hi x hΦ) (g := g) ha fun u => ?_
  obtain ⟨b, z, e⟩ := unip_y h' (inv_mem u.2)
  have e2 : mat (u * g).1⁻¹ *ᵥ incV F H'.y = c • incV F H'.x + mat u.1⁻¹ *ᵥ incV F H'.y := by
    rw [Subgroup.coe_mul, mul_inv_rev, Fr.mat_mul, ← Matrix.mulVec_mulVec, hg, eich_apply, e]
    simp only [Matrix.mulVec_zero, bf_add_l, bf_smul_l, h'.ad.xx, h'.ad.ix, h'.ad.yx, mul_zero, zero_add, h'.ad.ee, one_smul, bf0,
      neg_zero, zero_smul, add_zero]
    exact add_comm _ _
  rw [tm_eq hp hi _ hΦ, tm_eq hp hi _ hΦ, incM_vv, vv_mul_r, vv_mul_r, e2, Matrix.vecMulVec_add,
    ev_I h he ⟨c • incV F x, by rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]⟩ _ hΦ, theta_smul, half_sy hp.base (a := a)]
  rw [hT_vv, e, bf_inc]
  simp only [bf_add_r, bf_smul_l, bf_smul_r, h'.ad.xx, h'.ad.xi, h'.ad.xy, mul_zero, zero_add, mul_one]
  rw [hc, mul_left_comm, ← map_mul, mul_inv_cancel₀ hx, map_one, mul_one]

end Zero

section Cone

variable {M₂ : Model σ X₁ W₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}

theorem tA_eig (hp : IsPair B M χX χW om r s r' s') (h' : PG σ W W₁ H' (-1)) (he : IsEv B M M₂ H.ι H'.ι (sumA H H') e)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ) (w : Fin d₁ → E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : unip σ W H') : tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ u =
      B.ψ (-(⅟(2 : AF F) * sy σ X W (incM F (vA H.y H'.y H'.ι (H.x, w)) * (mat u.1⁻¹)ᵀ - incM F (vA H.y H'.y H'.ι (H.x, w)))
        (incM F (vA H.y H'.y H'.ι (H.x, w))))) * tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ 1 := by
  obtain ⟨a, z, e1⟩ := unip_y h' (inv_mem u.2)
  obtain ⟨b, e2⟩ := (Fr.mem_unip.1 (inv_mem u.2)).2 (incV F w)
  rw [tm_eq hp hi _ hΦ, tm_one, ← theta_smul, ← ev_I hp.base.std he ?_ _ hΦ, sub_add_cancel]
  refine ⟨a • incV F H.x + b • incV F H.y, z, ?_⟩
  rw [vA_apply, incM_add, incM_vv, incM_vv, Matrix.add_mul, vv_mul_r, vv_mul_r, ← inc_mulVec, e1, e2]
  simp only [Matrix.vecMulVec_add, Matrix.add_vecMulVec, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]
  abel

theorem tA_zero (hm : MeanOK σ W H' μ 𝓕) (hp : IsPair B M χX χW om r s r' s') (h : PG σ X X₁ H 1) (h' : PG σ W W₁ H' (-1))
    (he : IsEv B M M₂ H.ι H'.ι (sumA H H') e)
    (hi : ∀ u ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, u) Φ) = e Φ) {w : Fin d₁ → E} (hw : w ≠ 0) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : ∫ u in 𝓕, tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ u ∂μ = 0 := by
  have hψ := hp.base.std
  obtain ⟨a, ha⟩ := exists_psi hψ
  obtain ⟨z₀, hz₀⟩ : ∃ z, bf σ.toRingHom W.J (H'.ι *ᵥ z) (H'.ι *ᵥ w) ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hw (h'.nd_low w h0)
  set i2 : AE F E := algebraMap (AF F) (AE F E) (⅟2) with hi2
  have h2 : i2 * 2 = 1 := by rw [hi2, ← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  have hc2 : cA σ i2 = i2 := AlgHom.commutes _ _
  set z : Fin d₁ → AE F E := (i2 * algebraMap (AF F) (AE F E) a) • incV F ((bf σ.toRingHom W.J (H'.ι *ᵥ z₀) (H'.ι *ᵥ w))⁻¹ • z₀) with hz
  have hb : bf (cA σ).toRingHom (incM F W.J) (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ incV F w) = i2 * algebraMap (AF F) (AE F E) a := by
    rw [hz, Matrix.mulVec_smul, bf_smul_l, inc_mulVec, inc_mulVec, bf_inc, Matrix.mulVec_smul]
    rw [show form σ W.J _ _ = 1 from (bf_smul_l (c := σ.toRingHom) _ _ _).trans (inv_mul_cancel₀ hz₀), map_one, mul_one]
  have hb' : bf (cA σ).toRingHom (incM F W.J) (incM F H'.ι *ᵥ incV F w) (incM F H'.ι *ᵥ z) = -(i2 * algebraMap (AF F) (AE F E) a) := by
    rw [h'.ad.symm, hb, map_mul]
    change _ * (cA σ _ * cA σ _) = _
    rw [hc2, AlgHom.commutes]
    push_cast
    ring
  clear_value z
  obtain ⟨g, hg⟩ := exists_eich h' z (-(i2 * bf (cA σ).toRingHom (incM F W.J) (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ z))) (by
    have := h'.ad.symm (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ z)
    rw [map_neg, map_mul, hc2]
    change _ = _ * cA σ _ at this
    linear_combination i2 * this - bf (cA σ).toRingHom (incM F W.J) (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ z) * h2)
  have hgc : tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ g = B.ψ a * tm B M om H' e (vA H.y H'.y H'.ι (H.x, w)) Φ 1 := by
    rw [tA_eig hp h' he hi w hΦ g, half_sy hp.base (a := a)]
    rw [vA_apply, incM_add, incM_vv, incM_vv, Matrix.add_mul, vv_mul_r, vv_mul_r, ← inc_mulVec, hg, eich_y h'.ad, eich_i h'.ad, hb',
      sub_eq_add_neg, ← neg_one_smul (AE F E) (vecMulVec _ _ + vecMulVec _ _)]
    simp only [hT_add_l, hT_add_r, hT_smul_l, hT_vv, bf_add_l, bf_smul_l, h.ad.xx, h.ad.xy, h.ad.yx, h.ad.yy, h'.ad.xi, h'.ad.yi,
      h'.ad.xy, h'.ad.yy, h'.ad.iy, hb]
    push_cast
    linear_combination algebraMap (AF F) (AE F E) a * h2
  refine hm.zero (fun γ hγ u => ?_) (g := g) ha fun u => ?_
  · obtain ⟨D, hD⟩ := Fr.mem_ratU.1 (inv_mem hγ)
    rw [tm_mul, tA_eig hp h' he hi w (om_mem hp _ hΦ), hD,
      show ∀ U : Matrix (Fin n) (Fin d) E, incM F U * (incM F D)ᵀ - incM F U = incM F (U * Dᵀ - U) from fun U => by
        simp only [incM, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.transpose_map],
      psi_rat hψ, one_mul, ← tm_mul, one_mul]
  · rw [tm_mul, tA_eig hp h' he hi w (om_mem hp _ hΦ), ← tm_mul, one_mul, hgc, tA_eig hp h' he hi w hΦ u]
    ring

end Cone

end PositivityTheory.ThKCT.Ker

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.GenSmallOf
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem genSmall_of (hK : CTKernel) (hF : CTFub) (hCB : ConeB) (h2 : TwoExp) (hM : MixAB) (hMW : MixW) (hC : EvCone) (hWi : Witt)
    (hD : StabDec) (hU : UnipEx) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hSD : SoDecay) (hV : FinVolU) (hSF : SoFin)
    (hSt : SoStab) (hZ : SoZeroA') (hSe : SoEv) : GenSmall := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eB hM₁ hM₀ he₀ heB z hz K μK μ hI hμK hμ
  by_cases hex : ∃ χX χW om, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1)
  swap
  · exact ⟨1, 1, one_ne_zero, one_ne_zero, fun χX χW om _ _ hp => absurd ⟨χX, χW, om, hp⟩ hex⟩
  obtain ⟨χ0, χ0', o, hq⟩ := hex
  obtain ⟨⟨eA, heA⟩, -⟩ := hC F E σ B n d X W M χ0 χ0' o _ _ _ _ hq _ _ X₁ W₁ H H' i₀ i₁ j₀ j₁ M₀ hH hH' hM₀
  obtain ⟨C₀, hC₀, -, hK1⟩ := hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀
  obtain ⟨C₁, hC₁, hK2⟩ := hK1 n₁ X₁ H j₀ j₁ M₀ hH hM₀ eA heA
  obtain ⟨c, hc, h2'⟩ := h2 F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hq.base hq.herm hq.skew hq.good hM₀
    eA eB heA heB
  obtain ⟨κ, hκ, hB⟩ := hCB F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' eB heB z hz K μK μ hI hμK hμ
  obtain ⟨γ, hγ⟩ := (hWi F E σ B n X _ _ hq.base hq.herm).2 n₁ H (adapted_x_ne hH) hH.xx
  obtain ⟨κ₁, hκ₁, hch⟩ := dom_change hG hE hq.base hq.herm hq.good.haar hM₁.haar hq.good.dom hM₁.dom
  refine ⟨C₀ * κ₁, C₁ * c * κ, mul_ne_zero hC₀ hκ₁, mul_ne_zero (mul_ne_zero hC₁ hc) hκ,
    fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ hfin => ?_⟩
  have hle := (hSF F E σ B n d X W M χX χW om _ _ _ _ hp).2.2.1
  have hs := hle Φ hΦ
  have hst := hSt F E σ B n d X W M χX χW om _ _ _ _ hp
  obtain ⟨hmA, hmB⟩ := hM F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀
  replace hmA := hmA eA heA
  have hu := (hU F E σ B n n₁ X X₁ H j₀ j₁ _ _ hp.base (Or.inl hp.herm) hH).2.2.2.2.2.1
  have lB := lawsB hp heB (hmB eB heB) hz.1 hH.rank hH'.xx fun m hm => (hu m hm).2
  obtain ⟨b1, b2, b3⟩ := hB χX χW om om₀ hp hp₀ Φ hΦ hfin
  replace b1 := b1 γ hγ
  have k1 := hK2 γ hγ χX χW om _ _ _ _ hp Φ hs
  have hsch : ∀ {I e}, IsEv B M M₀ H.ι H'.ι I e → ∀ w, ∀ Ψ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ w Ψ) ∈ schA F (Fin n₁ × Fin d₁) := fun he w Ψ h => he.maps _ (rho_mem M hp.base.std w h)
  set L : UA σ X.J → UA σ W.J → ℂ := fun g h =>
    ∑' q : MulAction.orbitRel.Quotient Eˣ (IsoV σ X), -thetaSum F (eA (om (γ q.out * g, h) Φ)) with hL
  have hlines : ∀ g h, (Summable fun x => thv B M om eB (shiftB σ H H' 1) Φ h (γ x * g)) →
      ∑' x, thv B M om eA (shiftA H H' 1) Φ h (γ x * g) - c * ∑' x, thv B M om eB (shiftB σ H H' 1) Φ h (γ x * g) = L g h := by
    intro g h hsB
    have hsA : Summable fun x => thv B M om eA (shiftA H H' 1) Φ h (γ x * g) := (k1 g).1 h
    rw [← tsum_mul_left, ← hsA.tsum_sub (hsB.mul_left c), orbit_sum isoAct_free (hsA.sub (hsB.mul_left c))]
    refine tsum_congr fun q => ?_
    have hΨ := pair_pres hp (γ q.out * g, h) hs
    obtain ⟨sA, sB, e2⟩ := h2' _ hΨ
    have vA : ∀ ξ : Eˣ, thv B M om eA (shiftA H H' 1) Φ h (γ (ξ • q.out) * g) =
        thetaSum F (eA (M.co.rho B.ψ (incM F ((ξ : E) • Matrix.vecMulVec H.x H'.y)) (om (γ q.out * g, h) Φ))) := fun ξ => by
      rw [(lawsTA hp hmA fun m hm => (hu m hm).1).mult hD hU hTB hp hp₀ hH (hsch heA _) hs hγ h g q.out ξ ξ (map_inv _ _).symm
        (by simp only [MonoidHom.inv_apply, hp.hW.2 ξ, GlobalTheory.Doubling.absE_inclR]; simp), incM_smul, incM_vecMulVec]
      rfl
    let φ : Eˣ ≃ Eˣ := (Equiv.inv Eˣ).trans (conjE hp.base.cm)
    have vB : ∀ ξ : Eˣ, thv B M om eB (shiftB σ H H' 1) Φ h (γ (ξ • q.out) * g) =
        thetaSum F (eB (M.co.rho B.ψ (incM F ((φ ξ : E) • Matrix.vecMulVec H.y H'.x)) (om (γ q.out * g, h) Φ))) := fun ξ => by
      rw [lB.toLawsT.mult hD hU hTB hp hp₀ hH (hsch heB _) hs hγ h g q.out ξ ξ⁻¹ rfl
        (by simp only [hp.hW.2 ξ⁻¹, GlobalTheory.Doubling.absE_inclR]; simp), incM_smul, incM_vecMulVec, shiftB]
      congr 4
    simp only [vA, vB]
    have sA' : Summable fun ξ : Eˣ => thetaSum F (eA (M.co.rho B.ψ (incM F ((ξ : E) • Matrix.vecMulVec H.x H'.y))
        (om (γ q.out * g, h) Φ))) := sA.comp_injective Units.val_injective
    have sB' : Summable fun ξ : Eˣ => thetaSum F (eB (M.co.rho B.ψ (incM F ((φ ξ : E) • Matrix.vecMulVec H.y H'.x))
        (om (γ q.out * g, h) Φ))) := (sB.comp_injective Units.val_injective).comp_injective φ.injective
    rw [sA'.tsum_sub (sB'.mul_left c), tsum_mul_left,
      φ.tsum_eq fun ξ : Eˣ => thetaSum F (eB (M.co.rho B.ψ (incM F ((ξ : E) • Matrix.vecMulVec H.y H'.x)) (om (γ q.out * g, h) Φ))),
      units_sum sA, units_sum sB, e2]
    have z0 : ∀ v : Matrix (Fin n) (Fin d) E, incM F ((0 : E) • v) = 0 := fun v => by rw [incM_smul, map_zero, zero_smul]
    have zB := (hSe F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hp.base hp.herm hp.skew hp.good hM₀ eB heB _
      (hst (γ q.out * g, h) Φ hΦ)).1
    simp only [z0, rho_zero, zB]
    simp [thetaSum]
  obtain ⟨Cd, kd, hdec⟩ := hSD F E σ B n d X W M χX χW om _ _ _ _ hp Φ hΦ 0
  have hvol := hV F E σ hp.base.cm n X.J (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1 M.μ M.dom hp.good.haar hp.good.dom
  obtain ⟨f1, f2⟩ := hF F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ hH' Φ hs
    ⟨Cd * (M.μ M.dom).toReal, kd, fun h => by
      calc _ ≤ ∫⁻ _ in M.dom, ENNReal.ofReal (Cd * (ht h : ℝ) ^ kd) ∂M.μ := lintegral_mono fun g => by
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (by simpa using hdec g h)
        _ = _ := by
            rw [setLIntegral_const, mul_right_comm, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvol.ne]⟩
    _ fun g => (k1 g).2
  refine ⟨fun h => ∫ g in M.dom, (C₀ * thetaSum F (e₀ (om (g, h) Φ)) + C₁ * L g h) ∂M.μ,
    fun h => C₁ * c * κ * coneI B M om M₀ om₀ eB K μK μ (shiftB σ H H') χW z (om (1, h) Φ) 1, ?_, fun t m hm h => ?_,
    fun t m hm h => by dsimp only; rw [b2 t 1 m hm h]; ring, fun h₁ p hl h => ⟨?_, fun hso => ?_⟩⟩
  · convert f2 using 1
    funext h
    obtain ⟨a1, a2, a3⟩ := b1 h
    rw [Pi.add_apply, mul_assoc (C₁ * c), ← a3, ← integral_const_mul, ← eq_sub_iff_add_eq, ← integral_sub (f1 h) (a2.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [a1] with g hg
    rw [← hlines g h hg]
    simp only [thv]
    ring
  · dsimp only
    rw [← integral_const_mul]
    congr 1
    funext g
    have m1 : ∀ g', om (g', m * h) Φ = om (1, m) (om (g', h) Φ) := fun g' => by simp [om_mul]
    have m2 := hMW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ 1 t 1 m hm 1 (one_mem _) _
      (pair_pres hp (g, h) hs)
    rw [one_mul] at m2
    simp only [hL, m1, m2, hmA.levi (levi_one H) hm (pair_pres hp _ hs), thetaSum_smul', ← Prod.one_eq_mk, map_one,
      Module.End.one_apply, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, one_mul, ← mul_neg, tsum_mul_left]
    ring
  · dsimp only
    rw [b2 1 h₁ p hl h, b3]
    simp
  · have hz0 : ∀ g, L g (p * h) = 0 := fun g => by
      have : ∀ g', eA (om (g', p * h) Φ) = 0 := fun g' => by
        refine hZ F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hp.base hp.herm hp.skew hp.good hM₀ M₁ hM₁
          ⟨χX, χW, om₁, om₀, _, _, _, _, _, _, hp₁, hp₀⟩ e₀ eA he₀ heA _ (pair_pres hp _ hs) ?_
        have m2 := hMW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ g' 1 h₁ p hl 1 (one_mem _) _
          (pair_pres hp (1, h) hs)
        rw [one_mul, om_mul, Prod.mk_mul_mk, mul_one] at m2
        rw [m2]
        exact Submodule.smul_mem _ _ (hSt F E σ B n d₁ X W₁ M₁ χX χW om₁ _ _ _ _ hp₁ _ _ hso)
      simp [hL, this, thetaSum]
    simp only [hz0, mul_zero, add_zero]
    exact (zero_term hMW hTB hp hp₁ hH' he₀ hch C₀ hs).2 h₁ p hl h

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.MixABOf
section
noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open Matrix (vecMulVec)

theorem mixAB_of (hW : MixW) (hX : MixX) (hZ : EvZero) (hP : PairEx) (hE : ThetaExp) (hU : EvUniq) : MixAB := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀
  have hB := hp.base
  have hψ := hB.std
  have p := pg_herm hB hH hp.herm
  have p' := pg_skew hB hH' hp.skew
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨⟨M₁, g₁⟩, h1⟩ := hP F E σ B hB n d₁ X W₁ _ _ _ _ hp.herm hp₀.skew
    obtain ⟨om₁, hp₁⟩ := h1 χX χW hp.hX hp.hW hp.resX hp₀.resW M₁ g₁
    have hz := hZ F E σ B n d X W M χX χW om _ _ _ _ hp d₁ X W₁ H' i₀ i₁ M₁ rfl hH' g₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hz
    obtain ⟨⟨e₁, he₁⟩, h2⟩ := hX F E σ B n d₁ X W₁ M₁ χX χW om₁ _ _ _ _ hp₁ n₁ X₁ H j₀ j₁ M₀ om₀ _ _ hH hp₀
    have hc := isEv_comp hψ hp.good g₁ hp₀.good he₀ he₁
      (comp_ne (polX p (skew_det hp₀.skew)) hE hB hp.good g₁ hp₀.good he₀ he₁) (K := isoA H H') (by
        rintro u (h | ⟨z, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.one_mul, vv_mul_r]⟩)
    rw [Matrix.one_mul, Matrix.mul_one] at hc
    obtain ⟨c, -, hc⟩ := (polA p p').uniq hU hB hp.good hp₀.good (isEv_sumA hψ p' hc) (isEv_sumA hψ p' he)
    intro t g₁ q hq u hu t' h₁ q' hq' u' hu' Φ hΦ
    rw [hc _ (pair_pres hp _ hΦ), hc _ hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
      hW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ _ t' h₁ q' hq' u' hu' Φ hΦ, map_smul,
      h2 e₁ he₁ h₁ t g₁ q hq u hu _ (he₀.maps Φ hΦ), map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  · obtain ⟨⟨M₁, g₁⟩, h1⟩ := hP F E σ B hB n₁ d X₁ W _ _ _ _ hp₀.herm hp.skew
    obtain ⟨om₁, hp₁⟩ := h1 χX χW hp.hX hp.hW hp₀.resX hp.resW M₁ g₁
    obtain ⟨⟨e₀, he₀⟩, h2⟩ := hX F E σ B n d X W M χX χW om _ _ _ _ hp n₁ X₁ H j₀ j₁ M₁ om₁ _ _ hH hp₁
    have hz := hZ F E σ B n₁ d X₁ W M₁ χX χW om₁ _ _ _ _ hp₁ d₁ X₁ W₁ H' i₀ i₁ M₀ rfl hH' hp₀.good
    obtain ⟨⟨e₁, he₁⟩, -⟩ := hz
    have hc := isEv_comp hψ hp.good g₁ hp₀.good he₀ he₁
      (comp_ne (pol0 (herm_det hp₀.herm) p') hE hB hp.good g₁ hp₀.good he₀ he₁) (K := isoB H H') (by
        rintro u (h | ⟨z, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec]⟩)
    rw [Matrix.one_mul, Matrix.mul_one] at hc
    obtain ⟨c, -, hc⟩ := (polB p p').uniq hU hB hp.good hp₀.good (isEv_sumB hψ p hc) (isEv_sumB hψ p he)
    intro t g₁ q hq u hu t' h₁ q' hq' u' hu' Φ hΦ
    rw [hc _ (pair_pres hp _ hΦ), hc _ hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
      h2 e₀ he₀ _ t g₁ q hq u hu Φ hΦ, map_smul,
      hW F E σ B n₁ d X₁ W M₁ χX χW om₁ _ _ _ _ hp₁ d₁ W₁ H' i₀ i₁ M₀ om₀ _ _ hH' hp₀ e₁ he₁ _ t' h₁ q' hq' u' hu' _ (he₀.maps Φ hΦ),
      map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring

end PositivityTheory.ThKCT.Ker
end
end

