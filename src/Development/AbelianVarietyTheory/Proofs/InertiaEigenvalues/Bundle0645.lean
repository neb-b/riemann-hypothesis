module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UnitaryBC

namespace GlobalTheory.BaseChangeBridge

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_equiv_of_isSubquotient {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible) (h : GlobalTheory.SmGL.IsSubquotient σ ρ) :
    ∃ e : W ≃ₗ[ℂ] V, ∀ g x, e (σ g x) = ρ g (e x) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨hW, -⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ
  obtain ⟨-, hρ'⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ
  have hS : S.toSubmodule = ⊤ := by
    rcases hρ' S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : W)
      obtain ⟨v, rfl⟩ := hf x
      have hv : v = 0 := by
        exact Subtype.ext ((Submodule.eq_bot_iff _).1 e v v.2)
      subst hv
      exact hx (map_zero f.toLinearMap)
    · exact e
  let g : V →ₗ[ℂ] W := f.toLinearMap ∘ₗ (LinearEquiv.ofTop S.toSubmodule hS).symm.toLinearMap
  have hg : ∀ x v, g (ρ x v) = σ x (g v) := fun x v => by
    have := LinearMap.congr_fun (f.isIntertwining' x) ((LinearEquiv.ofTop S.toSubmodule hS).symm v)
    exact this
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨v, rfl⟩ := hf y
    refine ⟨(v : V), ?_⟩
    change f ((LinearEquiv.ofTop S.toSubmodule hS).symm (v : V)) = f v
    congr 1
  have ginj : Function.Injective g := by
    rcases hρ' (LinearMap.ker g) (fun x v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hg, hv, map_zero]) with e | e
    · exact LinearMap.ker_eq_bot.1 e
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : W)
      obtain ⟨v, rfl⟩ := gsurj y
      exact hy (LinearMap.mem_ker.1 (e ▸ Submodule.mem_top))
  let e0 := LinearEquiv.ofBijective g ⟨ginj, gsurj⟩
  refine ⟨e0.symm, fun x y => e0.injective ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  change σ x y = g (ρ x (e0.symm y))
  rw [hg]
  change σ x y = σ x (e0 (e0.symm y))
  rw [LinearEquiv.apply_symm_apply]

variable {H : Type} [Group H]

theorem isSpherical_of_equiv {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) {K : Subgroup H} (h : GlobalTheory.LGrp.IsSpherical σ K) :
    GlobalTheory.LGrp.IsSpherical ρ K := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  exact (Submodule.ne_bot_iff _).2 ⟨e x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← he, GlobalTheory.LGrp.mem_fixed.1 hx k hk],
    by simpa using h0⟩

theorem symm_equivariant {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) (g : H) (y : V) : e.symm (ρ g y) = σ g (e.symm y) :=
  e.injective (by rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply])

end General

section Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasSatGL_of_equiv {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} (e : W ≃ₗ[ℂ] V) (he : ∀ g x, e (σ g x) = ρ g (e x))
    {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w σ B) : GlobalTheory.LFun.HasSatGL w ρ B := by
  refine ⟨isSpherical_of_equiv e he h.1, fun y hy h0 => ?_⟩
  have hx : e.symm y ∈ GlobalTheory.PRep.fixed σ (GlobalTheory.LFun.KGL w (n := n)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← symm_equivariant e he, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
  have h0' : e.symm y ≠ 0 := by simpa using h0
  have := (h.2 _ hx h0').map e.toLinearMap he (by simpa using h0)
  simpa using this

end Local

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isCompAlong_of_equiv {π : Submodule ℂ (UA E n → ℂ)} {Gv : Subgroup (UA E n)} {H : Type} [Group H]
    {p : Gv →* H} {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) (hρ : ρ.IsIrreducible) (h : IsCompAlong π Gv p σ) :
    IsCompAlong π Gv p ρ := by
  obtain ⟨-, f, h0, hf, hfi⟩ := h
  refine ⟨hρ, f ∘ₗ e.symm.toLinearMap, fun h1 => h0 ?_, fun v => hf _, fun x v => ?_⟩
  · refine LinearMap.ext fun y => ?_
    simpa using LinearMap.congr_fun h1 (e y)
  · simp [symm_equivariant e he, hfi]

end CM

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem main : GlobalTheory.Published.BaseChangeIsobaric → GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    GlobalTheory.Published.BaseChangeDefiniteUnitary := by
  intro hBC hB E _ _ _ hun n hn π hπ
  obtain ⟨c, N, h, V, σ, m, P, H⟩ := hBC E hun n hn π hπ
  refine ⟨c, N, h, V, σ, m, ?_⟩
  have hirr : ∀ w, (locProd h w (σ · w)).IsIrreducible := fun w =>
    ((GlobalTheory.SmGL.MultiIrr.products_irreducible hB (w.adicCompletion E)).1 c N (Fin n) (GlobalTheory.SmGL.stdBlocks N h)
      (fun i => (σ i w).V) (fun i => (σ i w).ρ) (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
      (fun i => GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E (N i) (V i) (H.discrete i) w (σ i w)
        (H.loc i w))).2.1
  exact
    { pos := H.pos
      discrete := H.discrete
      csd := H.csd
      loc := H.loc
      inf := H.inf
      unram := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isSpherical_of_equiv e he (H.unram w hw)
      inert := fun w s ϖ q hs hq α hα => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact hasSatGL_of_equiv e he (H.inert w s ϖ q hs hq α hα)
      split := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isCompAlong_of_equiv e he (hirr w) (H.split w hw)
      weight := H.weight }

end GlobalTheory.BaseChangeBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedVectorCoefficientLeftInvariantLevelGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.CoefLeft

theorem ip_eq_of_sq {X : Type} [MeasurableSpace X] (ν : Measure X) (a b c d : X → ℂ)
    (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) (hc : MemLp c 2 ν) (hd : MemLp d 2 ν)
    (h : ∀ z : ℂ, ∫⁻ x, ‖c x + z * d x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖a x + z * b x‖ₑ ^ 2 ∂ν) :
    ∫ x, star (c x) * d x ∂ν = ∫ x, star (a x) * b x ∂ν := by
  have pt : ∀ p q : ℂ, star p * q = (1/4 : ℂ) * ((((‖p + 1 * q‖ ^ 2 : ℝ)) : ℂ) - ((‖p + (-1) * q‖ ^ 2 : ℝ) : ℂ)
      + Complex.I * ((‖p + (-Complex.I) * q‖ ^ 2 : ℝ) : ℂ) - Complex.I * ((‖p + Complex.I * q‖ ^ 2 : ℝ) : ℂ)) := by
    intro p q
    have e : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * (starRingEnd ℂ) w := by
      intro w; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e, map_add (f := _), map_mul, map_neg, map_one, Complex.conj_I]
    show (starRingEnd ℂ) p * q = _
    ring_nf
    try (simp only [Complex.I_sq]; ring)
  have mem : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν → ∀ z : ℂ,
      Integrable (fun x => (((‖f x + z * g x‖ ^ 2 : ℝ)) : ℂ)) ν := by
    intro f g hf hg z
    have h2 : MemLp (fun x => f x + z * g x) 2 ν := hf.add (hg.const_mul z)
    have : Integrable (fun x => ‖f x + z * g x‖ ^ 2) ν := by
      have := h2.integrable_norm_pow (p := 2) (by norm_num)
      simpa using this
    exact this.ofReal
  have Q : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν → ∀ z : ℂ,
      ∫ x, (((‖f x + z * g x‖ ^ 2 : ℝ)) : ℂ) ∂ν = (((∫⁻ x, ‖f x + z * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ) := by
    intro f g hf hg z
    rw [integral_complex_ofReal]
    congr 1
    have hm : AEStronglyMeasurable (fun x => f x + z * g x) ν :=
      (hf.add (hg.const_mul z)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x + z * g x‖ ^ 2)
      (Filter.Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity) (hm.norm.pow 2)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have expand : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν →
      ∫ x, star (f x) * g x ∂ν = (1/4 : ℂ) * ((((∫⁻ x, ‖f x + 1 * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        - (((∫⁻ x, ‖f x + (-1) * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        + Complex.I * (((∫⁻ x, ‖f x + (-Complex.I) * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        - Complex.I * (((∫⁻ x, ‖f x + Complex.I * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)) := by
    intro f g hf hg
    simp_rw [pt (f _) (g _)]
    rw [integral_const_mul, integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
      Q f g hf hg, Q f g hf hg, Q f g hf hg, Q f g hf hg]
    · exact mem f g hf hg 1
    · exact mem f g hf hg (-1)
    · exact (mem f g hf hg 1).sub (mem f g hf hg (-1))
    · exact (mem f g hf hg (-Complex.I)).const_mul _
    · exact ((mem f g hf hg 1).sub (mem f g hf hg (-1))).add ((mem f g hf hg (-Complex.I)).const_mul _)
    · exact (mem f g hf hg Complex.I).const_mul _
  rw [expand c d hc hd, expand a b ha hb, h 1, h (-1), h (-Complex.I), h Complex.I]

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

variable {D : D7}

theorem isThetaFunO_add_smul {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f g : WO S T' → ℂ}
    (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) (z : ℂ) : IsThetaFunO ψ S T' (f + z • g) := {
  quasi γ w := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    obtain ⟨U₂, hU₂, h₂⟩ := hg.level
    refine ⟨U₁ ⊓ U₂, by rw [AddSubgroup.coe_inf]; exact hU₁.inter hU₂, fun u hu hu0 => ?_⟩
    have e1 := h₁ u hu.1 hu0
    have e2 := h₂ u hu.2 hu0
    funext w
    have e1' := congrFun e1 w
    have e2' := congrFun e2 w
    simp only [heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1' e2' ⊢
    rw [← e1', ← e2']; ring_nf
  cont := hf.cont.add (hg.cont.const_smul z)
  smooth k L hL hL0 w := by
    have := (hf.smooth k L hL hL0 w).add ((hg.smooth k L hL hL0 w).const_smul z)
    simpa only [Pi.add_apply, Pi.smul_apply] using this }

theorem memLp_two_of_lintegral {X : Type} [MeasurableSpace X] {ν : Measure X} {f : X → ℂ}
    (hm : AEStronglyMeasurable f ν) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν < ⊤) : MemLp f 2 ν := by
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa [enorm_pow] using h

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

theorem aesm_of_theta {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T' → ℂ} (ν : Measure (WO S T'))
    (hf : IsThetaFunO ψ S T' f) : AEStronglyMeasurable f ν := by
  haveI : OpensMeasurableSpace (WO S T') := ⟨le_rfl⟩
  exact hf.cont.aestronglyMeasurable

theorem thetaInner_weilRep {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} (hW : IsWeilDatumO ψ S T' χS χT om)
    {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (hμ : IsCovolOne (ratL T' S) μ 𝓕) (p : GA D S × GA D T')
    {u v : WO S T' → ℂ} (hu : IsThetaFunO ψ S T' u) (hv : IsThetaFunO ψ S T' v)
    (hu2 : ∫⁻ w in 𝓕, ‖u w‖ₑ ^ 2 ∂μ < ⊤) (hv2 : ∫⁻ w in 𝓕, ‖v w‖ₑ ^ 2 ∂μ < ⊤) :
    thetaIP μ 𝓕 (om p u) (om p v) = thetaIP μ 𝓕 u v := by
  have un := fun f (hf : IsThetaFunO ψ S T' f) => hW.om_unit μ 𝓕 hμ.1 hμ.2.1 p f hf
  unfold thetaIP
  refine ip_eq_of_sq (μ.restrict 𝓕) u v (om p u) (om p v)
    (memLp_two_of_lintegral (aesm_of_theta _ hu) hu2) (memLp_two_of_lintegral (aesm_of_theta _ hv) hv2)
    (memLp_two_of_lintegral (aesm_of_theta _ (hW.om_pres p u hu)) (by rw [un u hu]; exact hu2))
    (memLp_two_of_lintegral (aesm_of_theta _ (hW.om_pres p v hv)) (by rw [un v hv]; exact hv2)) (fun z => ?_)
  have := un (u + z • v) (isThetaFunO_add_smul hu hv z)
  simpa only [map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this

theorem thetaIP₂ {D : D7} {S T' : HSp D} {μ : Measure (WO S T')} {𝓕 : Set (WO S T')}
    {v : WO S T' → ℂ} (h : thetaIP μ 𝓕 v v ≠ 0) : ∫⁻ w in 𝓕, ‖v w‖ₑ ^ 2 ∂μ < ⊤ := by
  have hi : Integrable (fun w => star (v w) * v w) (μ.restrict 𝓕) := by
    by_contra hn
    exact h (integral_undef hn)
  have := hi.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at this
  simpa [enorm_mul, sq] using this

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft


set_option maxHeartbeats 1000000 in
theorem coef_lev_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hfix μ 𝓕 hμ k hk g
  have hW := hL.thP.ωP i t
  have hv1 : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
    have := hfix k hk 1
    rwa [Model.pureTensor_one] at this
  have hvθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [Model.pureTensor_one] at this
  unfold coef
  by_cases h0 : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
  · rw [h0, div_zero, div_zero]
  congr 1
  have e : R.ωP i t (1, k * g) = R.ωP i t (1, k) * R.ωP i t (1, g) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply]
  have hv2 := thetaIP₂ h0
  have huθ := hW.om_pres (1, g) _ hvθ
  have hu2 : ∫⁻ w in 𝓕, ‖R.ωP i t (1, g) (R.vP i t) w‖ₑ ^ 2 ∂μ < ⊤ := by
    rw [hW.om_unit μ 𝓕 hμ.1 hμ.2.1 (1, g) _ hvθ]; exact hv2
  have key := thetaInner_weilRep hW hμ (1, k) huθ hvθ hu2 hv2
  rwa [hv1] at key

end GlobalTheory.RawLift.CoefLeft

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassWachPairJumpsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1f_class_wach_pair_filtration_jumps : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  first | exact @GlobalTheory.NL.CrystallineDescent.pow_smul_from_complex | exact GlobalTheory.NL.CrystallineDescent.pow_smul_from_complex | (intros; apply GlobalTheory.NL.CrystallineDescent.pow_smul_from_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasStringOfLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.LiftInjProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hasString_of_lift (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ok : Pl D.host.E → Prop)
    (h1 : UnrCorr R i t fun w => ¬ ok w) (h1' : UnrCorr R i t ok)
    (h2 : ParamsEx R i t) (h3 : DownEig R i t) {h} (hh : GlobalTheory.Hk3.IsOpsV R i t h) {s : Sys D} {y} (hy : IsEigV R i t h s y)
    (h0 : R.thF i t y ≠ 0) : HasString R i t s := by
  obtain ⟨c, hc⟩ := h3 h hh s
  obtain ⟨B, hB⟩ := h2.1 h hh s y hy (fun e => h0 (by rw [e, map_zero]))
  obtain ⟨B', hB', hb⟩ := h2.2 c ((Submodule.ne_bot_iff _).2 ⟨_, hc y hy, h0⟩)
  refine ⟨B, hB, fun w hw => ⟨(B' w).map (fun a : ℂˣ => ((a * valV R i t w * (valW R i t w)⁻¹ : ℂˣ) : ℂ)), ?_, fun a ha => ?_⟩⟩
  · by_cases hw' : ok w
    · exact h1' h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
    · exact h1 h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
  obtain ⟨b, hb', rfl⟩ := Multiset.mem_map.1 ha
  have e1 : ‖(valV R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  have e2 : ‖(valW R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  simpa [e1, e2] using hb w hw b hb'

theorem liftInj_of_typeNZ : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → (∀ i, TypeNZ R i A.μ0 ∧ DownEig R i A.μ0 ∧ UnrCorr R i A.μ0 (fun w => ¬ IsConjPl w w) ∧ UnrCorr R i A.μ0 (fun w => IsConjPl w w) ∧ ParamsEx R i A.μ0) → GlobalTheory.LiftRows.LiftInj R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ hZ
  intro i h hops s x y hx hy hxne hyG hy0
  obtain ⟨hT, hDE, hU1, hU2, hPE⟩ := hZ i
  have hF : R.thF i A.μ0 x ≠ 0 := by
    intro h0
    apply hxne
    apply (hG.core.models.HW i (sg0 D A)).1
    rw [hG.core.thP.thG i A.μ0 x, h0, map_zero, map_zero]
  exact hT h hops s (hasString_of_lift R i A.μ0 (fun w => IsConjPl w w) hU1 hU2 hPE hDE hops hx hF) y hy hyG hy0

end GlobalTheory.LiftInjProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorsRationalFormsCommute
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HkKs

theorem comm_of_conj {K F V : Type} [Field K] [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
    (e : F ≃ₗ[K] V) (A B : Module.End K F) (A' B' : Module.End K V) (a c : K) (ha : a ≠ 0) (hc : c ≠ 0)
    (hA : ∀ x, e (A x) = a • A' (e x)) (hB : ∀ x, e (B x) = c • B' (e x)) (h : A * B = B * A) :
    A' * B' = B' * A' := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  have h1 : e (A (B x)) = (a * c) • A' (B' (e x)) := by
    rw [hA, hB, map_smul, smul_smul]
  have h2 : e (B (A x)) = (a * c) • B' (A' (e x)) := by
    rw [hB, hA, map_smul, smul_smul, mul_comm c a]
  have h3 : e (A (B x)) = e (B (A x)) := by
    rw [← Module.End.mul_apply, h, Module.End.mul_apply]
  rw [h1, h2] at h3
  have h4 := congrArg (fun z => (a * c)⁻¹ • z) h3
  simp only [inv_smul_smul₀ (mul_ne_zero ha hc)] at h4
  simpa using h4

theorem baseChange_inj {Ks K M : Type} [Field Ks] [Field K] [Algebra Ks K] [AddCommGroup M] [Module Ks M]
    {f g : Module.End Ks M}
    (h : Module.End.baseChangeHom Ks K M f = Module.End.baseChangeHom Ks K M g) : f = g := by
  have hinj : Function.Injective fun y : M => ((1 : K) ⊗ₜ[Ks] y : K ⊗[Ks] M) := by
    have h0 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap Ks K)
      (algebraMap Ks K).injective
    intro y y' hy
    apply (TensorProduct.lid Ks M).symm.injective
    apply h0
    simpa using hy
  ext x
  apply hinj
  exact LinearMap.congr_fun h ((1 : K) ⊗ₜ[Ks] x)

end GlobalTheory.HkKs

namespace GlobalTheory.HkKs


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem opK_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y), CommG D → HkComm D →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) k P k' P', HkIdx i k P → HkIdx i k' P' →
      GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) *
                   GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) =
        GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) *
          GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) ∧
      ∀ g : S.G, GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) * rhoKG S j (Y.rho j h1 h2) g =
        rhoKG S j (Y.rho j h1 h2) g * GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S Y H hCG hHk i hi j h1 h2 b k P k' P' hP hP'
  have hj : j ∈ Finset.Icc 1 D.R.m := Finset.mem_Icc.2 ⟨h1, h2⟩
  have hc : ∀ k P, H.cHk i b k P ≠ 0 := fun k P => by
    rw [H.cHk_pow]; exact pow_ne_zero _ (H.cHk_unit i b P).ne_zero
  have hkE : ∀ k P, HkIdx i k P → ∀ x, Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
      H.cHk i b k P • hkFR S i j b (H.hL j) (H.hs j h1 h2) k P (Y.eF i j b h1 h2 x) := by
    intro k P hP x
    exact H.hkEq i j b h1 h2 k P x hP.2.2.2 hP.2.2.1 hP.2.1
  constructor
  · have hcm := comm_of_conj (Y.eF i j b h1 h2) (D.nexp.hkF i j b k P) (D.nexp.hkF i j b k' P') _ _ _ _
      (hc k P) (hc k' P') (hkE k P hP) (hkE k' P' hP') (hHk i hi j hj b k P k' P' hP hP').eq
    apply baseChange_inj (K := KB S i b)
    rw [map_mul, map_mul]
    exact hcm
  · intro g
    have hne : (show FractionRing (D.ntw.O i) from (readLL0 S i b (chiL S j (Y.chi j h1 h2) (S.eG.symm (S.eG g))))⁻¹) ≠ 0 := by
      refine inv_ne_zero ((_root_.map_ne_zero _).2 fun h0 => ?_)
      exact Units.ne_zero _ (congrArg Subtype.val h0)
    have hA : ∀ x, Y.eF i j b h1 h2 (D.nexp.actG i j b (S.eG g) x) =
        (show FractionRing (D.ntw.O i) from (readLL0 S i b (chiL S j (Y.chi j h1 h2) (S.eG.symm (S.eG g))))⁻¹) •
          (show Module.End (FractionRing (D.ntw.O i)) (Fm S i j b) from
            Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j (Y.rho j h1 h2) (S.eG.symm (S.eG g))))
            (Y.eF i j b h1 h2 x) := by
      intro x
      rw [Y.act]
      rfl
    have hCG' : (D.nexp.actG i j b (S.eG g)).toLinearMap * D.nexp.hkF i j b k P =
        D.nexp.hkF i j b k P * (D.nexp.actG i j b (S.eG g)).toLinearMap := hCG i hi b j hj (S.eG g) k P hP
    have hcm := comm_of_conj (Y.eF i j b h1 h2) _ _ _ _ _ _ hne (hc k P) hA (hkE k P hP) hCG'
    rw [MulEquiv.symm_apply_apply] at hcm
    symm
    apply baseChange_inj (K := KB S i b)
    rw [map_mul, map_mul]
    exact hcm

end GlobalTheory.HkKs
end
end

