module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem Base.OtoLL_injective' (B : Base) : Function.Injective B.OtoLL := by
  intro x y h
  apply RingOfIntegers.ext
  exact Subtype.ext h

theorem hermitianCodeWordStages_ringOfIntegers_full : ∀ X : Stages, OFull X.toD7 := by
  intro X
  refine ⟨X.B.OtoLL_injective', ?_⟩
  let f : X.B.Ks →+* ℂ := X.B.embLL.comp (algebraMap X.B.Ks X.B.LL)
  have hle : FO X.toD7 ≤ f.toRatAlgHom.fieldRange := by
    rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    exact ⟨algebraMap (𝓞 X.B.Ks) X.B.Ks y, rfl⟩
  intro z hz hint
  obtain ⟨x, rfl⟩ := hle hz
  have hx : IsIntegral ℤ x := (isIntegral_algHom_iff f.toIntAlgHom f.injective).1 hint
  exact ⟨(⟨x, hx⟩ : 𝓞 X.B.Ks), rfl⟩

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesTypeNormsPrincipal
section
noncomputable section

namespace GlobalTheory.Mem.TypeNormPin

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2.Pj

section Push

variable {K F : Type} [Field K] [Field F] (φ : K →+* F)

theorem span_image_span (S : Set K) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 K) S : Set K)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    have : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
      change φ ((b : K) * x) = _
      rw [map_mul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 K) K →* Submodule (𝓞 F) F where
  toFun M := Submodule.span (𝓞 F) (φ '' M)
  map_one' := by rw [Submodule.one_eq_span, span_image_span, Set.image_singleton, map_one, Submodule.one_eq_span]
  map_mul' M N := by
    rw [Submodule.mul_eq_span_mul_set, span_image_span, Set.image_mul, Submodule.span_mul_span]

theorem extend_span (S : Set K) : extend φ (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 F) (φ '' S) :=
  span_image_span φ S

end Push

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem emb_sqrt_iff (g : R.GG) :
    H.emb g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ↔ g ∈ R.Psi :=
  (factEmb R H).2 g

theorem cmHostBaseEmbedding_sqrtMinusD : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem conj_ne : starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

theorem emb_sqrt_cases (σ : H.E →+* ℂ) : σ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ∨
    starRingEnd ℂ (σ H.sqrtMinusD) = Complex.I * (Real.sqrt H.d : ℂ) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
    apply H.φ₀.injective
    rw [map_pow, cmHostBaseEmbedding_sqrtMinusD, h0]
    simp
  have h1 : σ H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 := by
    rw [← map_pow, h, h0]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact Or.inl h2
  · right; rw [h2]; simp

def embSum : Tau R ⊕ Tau R → (H.E →+* ℂ) :=
  Sum.elim (fun g => H.emb g) (fun g => (starRingEnd ℂ).comp (H.emb g))

theorem embSum_bij : Function.Bijective (embSum H) := by
  refine ⟨?_, fun σ => ?_⟩
  · have hne : ∀ a b : Tau R, H.emb a ≠ (starRingEnd ℂ).comp (H.emb b) := fun a b h => by
      have h1 := DFunLike.congr_fun h H.sqrtMinusD
      rw [RingHom.comp_apply, (emb_sqrt_iff H _).2 a.2, (emb_sqrt_iff H _).2 b.2] at h1
      exact conj_ne H h1.symm
    rintro (a | a) (b | b) hab
    · exact congrArg _ (Subtype.ext ((factEmb R H).1.1 hab))
    · exact absurd hab (hne a b)
    · exact absurd hab.symm (hne b a)
    · refine congrArg _ (Subtype.ext ((factEmb R H).1.1 (RingHom.ext fun x => ?_)))
      exact (starRingEnd ℂ).injective (DFunLike.congr_fun hab x)
  · rcases emb_sqrt_cases H σ with h | h
    · obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
      exact ⟨Sum.inl ⟨g, (emb_sqrt_iff H g).1 h⟩, rfl⟩
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 ((starRingEnd ℂ).comp σ)
      refine ⟨Sum.inr ⟨g, (emb_sqrt_iff H g).1 (by rw [hg]; exact h)⟩, RingHom.ext fun x => ?_⟩
      change starRingEnd ℂ (H.emb g x) = _
      rw [hg]; simp

theorem emb_conj (g : R.GG) (x : H.E) : H.emb g (H.conj x) = starRingEnd ℂ (H.emb g x) :=
  H.conjE_apply _ x

end Host

theorem exists_hom (X : Stages) (Q : Par X.toD7) (h : Q.PinField) :
    ∃ φ : X.B.Ks →+* Q.c.F, ∀ x : X.B.Ks, ((φ x : Q.c.F) : ℂ) = X.B.embLL x := by
  let e : 𝓞 Q.c.F ≃+* 𝓞 X.B.Ks := Q.eO
  have he : ∀ y : 𝓞 Q.c.F, X.B.embLL ((e y : X.B.Ks) : X.B.LL) = ((y : Q.c.F) : ℂ) := h
  let φ : X.B.Ks ≃+* Q.c.F := IsFractionRing.ringEquivOfRingEquiv e.symm
  have hφ : ∀ y : 𝓞 X.B.Ks, ((φ (algebraMap _ X.B.Ks y) : Q.c.F) : ℂ) =
      X.B.embLL ((algebraMap _ X.B.Ks y : X.B.Ks) : X.B.LL) := fun y => by
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  refine ⟨φ.toRingHom, fun x => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) x
  change ((φ (_ / _) : Q.c.F) : ℂ) = _
  rw [map_div₀, IntermediateField.coe_div, hφ, hφ, IntermediateField.coe_div, map_div₀]

theorem kPsiIn_of_hom (B : Base) [IsCMField B.host.E] {Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host B.host.E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level Hh} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum Hh)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ B.R.m) (hp : Dw.p = (B.R.sigW j).1) (hq : Dw.q = (B.R.sigW j).2)
    (h1 : (Hh.rt : B.host.E) = B.host.sqrtMinusD) (h2 : Hh.rt0 = B.host.φ₀ B.host.sqrtMinusD)
    (φ : B.Ks →+* c.F) (hφ : ∀ x : B.Ks, ((φ x : c.F) : ℂ) = B.embLL x) : KPsiIn (Dw := Dw) c := by
  intro 𝔞 h𝔞
  obtain ⟨β, hβ0, hβ, habs⟩ := B.kPsi j hj1 hj2 𝔞 h𝔞
  have hE : ∀ y, B.embLL (B.embE y) = B.host.φ₀ y := fun y => RingHom.congr_fun B.embE_φ₀ y
  have himg : ∀ (τ : B.host.E →+* ℂ) (f : B.host.E → B.host.E), (∀ a, B.host.φ₀ (f a) = τ a) →
      φ '' {x : B.Ks | ∃ a ∈ 𝔞, (x : B.LL) = B.embE (f (a : B.host.E))} =
        (embK c τ) '' (𝔞 : Set (𝓞 B.host.E)) := by
    intro τ f hf
    ext z
    constructor
    · rintro ⟨x, ⟨a, ha, hx⟩, rfl⟩
      refine ⟨a, ha, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hx, hE, hf]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨_, B.E_le_Ks (f a)⟩, ⟨a, ha, rfl⟩, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hE, hf]
  refine ⟨φ β, (map_ne_zero φ).2 hβ0, ?_, fun σ => ?_⟩
  · have := congrArg (extend φ) hβ
    rw [extend_span, Set.image_singleton, map_prod] at this
    rw [this, ← (embSum_bij B.host).prod_comp fun τ =>
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 B.host.E))) ^ Dw.mult τ,
      Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    have hs : B.host.emb g B.host.sqrtMinusD = Complex.I * (Real.sqrt B.host.d : ℂ) :=
      (emb_sqrt_iff B.host _).2 g.2
    have h0 : Hh.rt0 = Complex.I * (Real.sqrt B.host.d : ℂ) := h2.trans (cmHostBaseEmbedding_sqrtMinusD B.host)
    have m1 : Dw.mult (embSum B.host (Sum.inl g)) = (B.R.sigW j).1 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos (by rw [h1, h0]; exact hs)]
      exact hp
    have m2 : Dw.mult (embSum B.host (Sum.inr g)) = (B.R.sigW j).2 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_neg]
      · exact hq
      · rw [h1, h0]
        change ¬ starRingEnd ℂ (B.host.emb g B.host.sqrtMinusD) = _
        rw [hs]
        exact conj_ne B.host
    rw [map_mul, map_pow, map_pow, extend_span, extend_span, m1, m2,
      himg (embSum B.host (Sum.inl g)) (B.host.sigmaOf g) (fun _ => rfl),
      himg (embSum B.host (Sum.inr g)) (fun a => B.host.sigmaOf g (B.host.conj a))
        (fun a => emb_conj B.host g a)]
  · rw [hp, hq]
    exact habs (σ.comp φ)

theorem hermitianCodeWordStages_typeNorms_principal : ∀ X : Stages, OKPsi X.toD7 := by
  intro X Q hQ j hj
  obtain ⟨φ, hφ⟩ := exists_hom X Q hQ.2.2.1
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  obtain ⟨-, h1, h2, -⟩ := hQ.1
  exact @kPsiIn_of_hom X.B (instCMHost X.toD7) Q.H Q.l Q.c (Q.Dw j) j hj.1 hj.2 hp hq h1 h2 φ hφ

end GlobalTheory.Mem.TypeNormPin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqIntegralOfAe
section
open Formalism.BasicNotions Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem inner_eq_integral_of_ae {α : Type} [MeasurableSpace α] {m : Measure α} (f g : Lp ℂ 2 m) (f' g' : α → ℂ)
    (hf : f =ᵐ[m] f') (hg : g =ᵐ[m] g') : ⟪f, g⟫_ℂ = ∫ x, star (f' x) * g' x ∂m := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]
  rfl

theorem eq_smul_of_eval {α A E V : Type} [MeasurableSpace α] {m : Measure α} [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ (Lp ℂ 2 m)) (φ : E → V → α → ℂ) (p : V → V → ℂ)
    (hS : ∀ T T', ∃ k : ℂ, ∀ v v', ∫ x, star (φ T v x) * φ T' v' x ∂m = k * p v v')
    (v₁ v₀ : V) (hp : p v₁ v₁ = 1) (j' : E ≃ₗ[ℂ] W) (hj' : ∀ T, ((j' T : W) : Lp ℂ 2 m) =ᵐ[m] φ T v₁)
    (e : A → E) (j : A → W) (a : ℂ) (hj : ∀ F, ((j F : W) : Lp ℂ 2 m) =ᵐ[m] fun x => a * φ (e F) v₀ x) (F : A) :
    j F = (a * p v₁ v₀) • j' (e F) := by
  have hmix : ∀ T : E, ⟪j' T, j F⟫_ℂ = (a * p v₁ v₀) * ⟪j' T, j' (e F)⟫_ℂ := by
    intro T
    obtain ⟨k, hk⟩ := hS T (e F)
    have h1 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj F)
    have h2 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj' (e F))
    rw [hk, hp, mul_one] at h2
    have h3 : ∫ x, star (φ T v₁ x) * (a * φ (e F) v₀ x) ∂m = a * ∫ x, star (φ T v₁ x) * φ (e F) v₀ x ∂m := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [h3, hk] at h1
    rw [Submodule.coe_inner, Submodule.coe_inner, h1, h2]
    ring
  obtain ⟨T, hT⟩ := j'.surjective (j F - (a * p v₁ v₀) • j' (e F))
  have hz : ⟪j F - (a * p v₁ v₀) • j' (e F), j F - (a * p v₁ v₀) • j' (e F)⟫_ℂ = 0 := by
    conv_lhs => enter [2]; rw [← hT]
    rw [inner_sub_right, inner_smul_right, hmix, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_conj_scalar {A W H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W] [AddCommGroup H]
    [Module ℂ H] (s : W →ₗ⋆[ℂ] H) (j f : A →ₗ[ℂ] W) (hj : Function.Injective j) (β : ℂ) (h : ∀ F, j F = β • f F) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ F, s (f F) = κ • s (j F) := by
  by_cases h0 : β = 0
  · refine ⟨1, one_ne_zero, fun F => ?_⟩
    have hF : j F = 0 := by rw [h, h0, zero_smul]
    have hF0 : F = 0 := hj (hF.trans (map_zero j).symm)
    subst hF0
    simp
  · refine ⟨(starRingEnd ℂ β)⁻¹, inv_ne_zero ((map_ne_zero _).2 h0), fun F => ?_⟩
    rw [h, LinearMap.map_smulₛₗ, smul_smul, inv_mul_cancel₀ ((map_ne_zero _).2 h0), one_smul]

theorem sEEofTT_eq_smul_conjHH : ∀ (D : D7) (S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar) (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0))) (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ), (∀ T ∈ E, ∀ T' ∈ E, ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v (ι.symm x * t)) * T' v' (ι.symm x * t) ∂(muX St) = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) → EvalTieT M μ 𝓕 E St G ι t c → ∀ (e : D.what₂.EE →ₗ[ℂ] E) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (v₀ : M.Vec) (a : ℂ), (∀ F, ((j F : EEC St G) : L2X St) =ᵐ[muX St] fun x => a * ev M v₀ (e F : MMap M) (ι.symm x * t)) → ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ F, sEEofTT M μ 𝓕 E St G ι t c (e F) = κ₀ • conjHH St G (j F) := by
  intro D S M E St G μ 𝓕 ι t c hS hT e j v₀ a hj
  have hv := hT.choose_spec.1
  have hj' := fun T => (hT.choose_spec.2.choose_spec T).1
  have hp : ∏ τ, ⟪(hT.choose τ : M.H τ), (hT.choose τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    simp
  have hkey := eq_smul_of_eval (m := muX St) (EEC St G) (fun (T : E) (v : M.Vec) x => (T : MMap M) v (ι.symm x * t))
    (fun v v' => ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) (fun T T' => hS T T.2 T' T'.2) hT.choose v₀ hp
    hT.choose_spec.2.choose hj' e j a hj
  have hs : sEEofTT M μ 𝓕 E St G ι t c
      = (conjHH St G).toLinearMap.comp hT.choose_spec.2.choose.toLinearMap := dif_pos hT
  rw [hs]
  exact exists_conj_scalar (conjHH St G).toLinearMap j.toLinearEquiv.toLinearMap
    (hT.choose_spec.2.choose.toLinearMap.comp e) j.injective _ hkey

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.IntByParts

theorem setIntegral_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (a : G) :
    ∫ g in 𝓕, Φ (g * a) ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hm : MeasurePreserving (fun g : G => g * a) μ μ := measurePreserving_mul_right μ a
  have h' : IsFundamentalDomain Γ ((fun g : G => g * a) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc _ _ _
  rw [← hm.setIntegral_preimage_emb (measurableEmbedding_mulRight a) Φ 𝓕]
  exact h.setIntegral_eq h' (f := fun g => Φ (g * a)) fun γ g => by
    change Φ ((γ : G) * g * a) = _
    rw [mul_assoc, hΦ _ γ.2]

theorem setIntegral_deriv_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) {Φ Φ' : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) (hc' : Continuous Φ')
    {B B' : ℝ} (hB : ∀ g, ‖Φ g‖ ≤ B) (hB' : ∀ g, ‖Φ' g‖ ≤ B') {a : ℝ → G} (h0 : a 0 = 1)
    (hd : ∀ g t, HasDerivAt (fun s : ℝ => Φ (g * a s)) (Φ' (g * a t)) t) : ∫ g in 𝓕, Φ' g ∂μ = 0 := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ) (x₀ := 0)
    (F := fun t g => Φ (g * a t)) (F' := fun t g => Φ' (g * a t)) (s := Set.univ) (bound := fun _ => B')
    Filter.univ_mem
    (.of_forall fun t => (hc.comp (continuous_mul_const _)).measurable.aestronglyMeasurable)
    (Integrable.of_bound (hc.comp (continuous_mul_const _)).measurable.aestronglyMeasurable B
      (.of_forall fun g => hB _))
    (hc'.comp (continuous_mul_const _)).measurable.aestronglyMeasurable
    (.of_forall fun g t _ => hB' _) (integrable_const _) (.of_forall fun g t _ => hd g t)
  have h2 := key.2
  simp only [setIntegral_mul_right Γ μ h hΦ, h0, mul_one] at h2
  exact h2.unique (hasDerivAt_const _ _)

variable {D : D7} {θ : InfF D} {V : HSp D}

theorem mul_cont_bounded {φ F : GA D V → ℂ} (hφ : IsMod θ V φ) (hF : F ∈ Decay θ V) :
    Continuous (fun g => φ g * F g) ∧ ∃ B : ℝ, ∀ g, ‖φ g * F g‖ ≤ B := by
  obtain ⟨c1, N, C, hC⟩ := hφ.2.2 [] (by simp)
  obtain ⟨c2, hr⟩ := hF.2.2 [] (by simp)
  obtain ⟨B, hB⟩ := IsRapidDecay.mul_bounded (φ := F) (ψ := φ) hr hφ.2.1 hC
  exact ⟨Continuous.mul c1 c2, B, fun g => by rw [norm_mul]; exact hB g⟩

theorem integral_Rder_mul : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ F, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ ∧ ∫ g in 𝓕, Rder θ V τ X φ g * F g ∂μ = -∫ g in 𝓕, φ g * Rder θ V τ X F g ∂μ := by
  intro D θ hθ V μ 𝓕 hq τ X hX φ F hφ hF
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hfin := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 hq).2
  haveI := hq.1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hq.1).1
  have int : ∀ {φ F : GA D V → ℂ}, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ := by
    intro φ F hφ hF
    obtain ⟨c, B, hB⟩ := mul_cont_bounded hφ hF
    exact Measure.integrableOn_of_bounded (M := B) hfin c.measurable.aestronglyMeasurable (.of_forall hB)
  refine ⟨int hφ hF, ?_⟩
  obtain ⟨c0, B0, hB0⟩ := mul_cont_bounded hφ hF
  obtain ⟨c1, B1, hB1⟩ := mul_cont_bounded (hφ.rder hX) hF
  obtain ⟨c2, B2, hB2⟩ := mul_cont_bounded hφ (Rder_mem_Decay hF hX)
  have key := setIntegral_deriv_eq_zero (GQ V) μ hq.2 hfin (Φ := fun g => φ g * F g)
    (Φ' := fun g => Rder θ V τ X φ g * F g + φ g * Rder θ V τ X F g)
    (fun γ hγ g => by simp only [hφ.2.1 γ hγ, hF.2.1 γ hγ]) c0 (c1.add c2) hB0
    (fun g => (norm_add_le _ _).trans (add_le_add (hB1 g) (hB2 g))) (oneP_zero (V := V) (τ := τ) (X := X) hθ)
    fun g t => (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hφ.1 hX) g t).mul
      (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hF.1 hX) g t)
  rw [integral_add (int (hφ.rder hX) hF) (int hφ (Rder_mem_Decay hF hX))] at key
  exact eq_neg_of_add_eq_zero_left key

end GlobalTheory.Mem.IntByParts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.VB

section Generic

variable {X : Scheme.{0}} [IsIntegral X]

theorem genRank_twist {F : X.Modules} {M : LB X} (hM : M.IsLB) :
    genRank (twist F M) = genRank F :=
  have ⟨e⟩ := Twist.nonempty_stalkEquiv (F := F) hM (genericPoint X)
  e.finrank_eq

theorem exists_germ_ne_zero {F : X.Modules} (h : QCoh.IsGloballyGenerated F)
    (hr : genRank F ≠ 0) :
    ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0 := by
  obtain ⟨n, s, hs⟩ := QCoh.isGloballyGenerated_iff_spanStalks.1 h
  by_contra! H
  have : Subsingleton (genStalk F) := subsingleton_of_forall_eq 0 fun t => by
    have ht := (hs (genericPoint X)).ge (Submodule.mem_top (x := t))
    have e : (Set.range fun i => ((F.presheaf.germ ⊤ (genericPoint X) trivial (s i) :
        (F.presheaf.stalk (genericPoint X) :)))) ⊆ {0} := by
      rintro _ ⟨i, rfl⟩
      exact H _
    simpa using Submodule.span_mono e ht
  exact hr Module.finrank_zero_of_subsingleton

theorem mono_sectionHom {F : X.Modules} (s : Γ(F, ⊤))
    (hs : F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0) : Mono (QCoh.sectionHom s) := by
  refine QCoh.mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hη := genericPoint_mem hx
  apply (QCoh.structureModuleSectionsEquiv W).injective
  have e' : (QCoh.structureModuleSectionsEquiv W a - QCoh.structureModuleSectionsEquiv W b) •
      Twist.resM F (le_top : W ≤ ⊤) s = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact e
  have e'' := congrArg (F.presheaf.germ W _ hη) e'
  rw [QCoh.germ_smul, Twist.germ_resM, map_zero] at e''
  have := (smul_eq_zero.1 e'').resolve_right hs
  exact sub_eq_zero.1 (germ_injective_of_isIntegral X _ hη (this.trans (map_zero _).symm))

end Generic

variable {κ : Type} [Field κ] {Z : Scheme.{0}} [IsIntegral Z] [Algebra κ Γ(Z, ⊤)]

theorem interNum_one_of_genRank_eq (hp : IsProjOver (strHom κ (X := Z))) (hd : topologicalKrullDim Z = 1)
    {N : LB Z} (hN : N.IsLB) (r : ℕ) :
    ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G ![N] = r * interNum κ (structureModule Z) ![N] := by
  have hf := algebraMap_eq_strHom κ Z
  have hL := isLB_vecOne hN
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    have h0 : QCoh.suppDim G ≤ 0 := suppDim_le_zero hd h
    have : QCoh.suppDim G < Fintype.card (Fin 1) := h0.trans_lt (by simp)
    rw [interNum_eq_zero_of_isProjOver hf G hp this hL]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) ![N] = interNum κ G ![N] :=
      (diffVanish_chiPic_of_isProjOver (d := 1) hf G hp
        ((QCoh.suppDim_le G).trans_eq (by rw [hd]; rfl))).interNum_twist (by simp) hL hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

theorem interNum_one_eq_genRank_mul : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z]
    [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → topologicalKrullDim Z = 1 →
    ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (N : LB Z), N.IsLB →
      interNum κ G ![N] = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) ![N] :=
  fun _ _ _ _ _ hp hd G _ _ hN => interNum_one_of_genRank_eq hp hd hN _ G rfl

end GlobalTheory.VB
end
end

