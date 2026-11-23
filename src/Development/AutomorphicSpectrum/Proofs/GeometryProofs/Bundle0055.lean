module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0051
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisChangeIntegral
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentiableOnStarStar
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Conj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.Regular

section Polydisc

variable {n a : ℕ}

theorem norm_star_vec (z : Fin n → ℂ) : ‖star z‖ = ‖z‖ := by
  simp only [Pi.norm_def, Pi.star_apply]
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  simp [nnnorm_star]

theorem star_mem_ball {ρ : ℝ} {z : Fin n → ℂ} :
    star z ∈ Metric.ball (0 : Fin n → ℂ) ρ ↔ z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
  simp only [mem_ball_zero_iff, norm_star_vec]

theorem star_mem_punct {ρ : ℝ} {z : Fin n → ℂ} : star z ∈ punct n a ρ ↔ z ∈ punct n a ρ := by
  simp only [punct, Set.mem_setOf_eq, star_mem_ball, Pi.star_apply, ne_eq, star_eq_zero]

theorem star_mem_logCover (h : a ≤ n) {w : Fin n → ℂ} : star w ∈ logCover h ↔ w ∈ logCover h := by
  simp only [logCover, Set.mem_setOf_eq, Pi.star_apply, Complex.star_def, Complex.conj_re,
    RCLike.norm_conj, Complex.norm_conj]

theorem star_expCover (w : Fin n → ℂ) : star (expCover a w) = expCover a (star w) := by
  funext k
  simp only [expCover, Pi.star_apply]
  split_ifs
  · simp [Complex.exp_conj]
  · rfl

theorem star_real_smul (ρ : ℝ) (z : Fin n → ℂ) : star ((ρ : ℂ) • z) = (ρ : ℂ) • star z := by
  funext k
  simp

theorem differentiableOn_star_star {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F]
    [StarModule ℂ F] [ContinuousStar F] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] [ContinuousStar V] {f : V → F} {B : Set V} (hB : IsOpen B) (hs : ∀ z, star z ∈ B ↔ z ∈ B)
    (hf : DifferentiableOn ℂ f B) : DifferentiableOn ℂ (fun z => star (f (star z))) B := by
  intro z hz
  have h1 : DifferentiableAt ℂ f (star z) := hf.differentiableAt (hB.mem_nhds ((hs z).2 hz))
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

end Polydisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def conjPts {R : Type} [CommRing R] {n : ℕ} (ψ : (Fin n → ℂ) → (R →+* ℂ)) (z : Fin n → ℂ) : R →+* ℂ :=
  (starRingEnd ℂ).comp (ψ (star z))

theorem isHolPts_conjPts {R : Type} [CommRing R] {n : ℕ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} {ρ : ℝ}
    (h : IsHolPts (Metric.ball 0 ρ) ψ) : IsHolPts (Metric.ball 0 ρ) (conjPts ψ) :=
  ⟨Metric.isOpen_ball, fun r => differentiableOn_star_star (f := fun b => ψ b r) Metric.isOpen_ball
    (fun _ => star_mem_ball) (h.2 r)⟩

def chart {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) :
    BdryChart Xo ((starRingEnd ℂ).comp σ) n a where
  a_le := C.a_le
  R := C.R
  t := C.t
  g := C.g
  dim := C.dim
  M := C.M
  ψ := conjPts C.ψ
  hol := isHolPts_conjPts C.hol
  V := C.V
  j := C.j
  j_open := C.j_open
  k := C.k
  tV := C.tV
  m₁ := C.m₁
  m₂ := C.m₂
  pt z := spMap (starRingEnd ℂ) ≫ C.pt (star z)
  pt_eq z hz := by
    obtain ⟨h1, h2⟩ := C.pt_eq (star z) (star_mem_punct.2 hz)
    constructor
    · rw [Category.assoc, h1]
      exact (Spec.map_comp _ _).symm
    · rw [Category.assoc, h2]
      exact (Spec.map_comp _ _).symm

end GlobalTheory.CompanionTheory.Ar.Flat.Conj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigExt

theorem mem_eigSp_iff' {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    (ρ : O →+* Module.End R E) (σ : O →+* R) (v : E) :
    v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem eigSp_ext :
    ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → (∀ a e, ρ' a (j e) = j (ρ a e)) → eigSp ρ' (i.comp σ) = Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) := by
  intro F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ hj hspan hcomp
  obtain ⟨n, a, c, hsum, hcas⟩ := GlobalTheory.CompanionTheory.Ar.ScaledCasimir.exists_scaledCasimir F

  let P' : V' →ₗ[Ω'] V' := ∑ m, i (σ (c m)) • ρ' (a m)
  have hP'apply : ∀ w, P' w = ∑ m, i (σ (c m)) • ρ' (a m) w := fun w => by
    simp [P', LinearMap.sum_apply]
  have hscal : ∑ m, i (σ (c m)) * i (σ (a m)) = ((NumberField.discr F : ℤ) : Ω') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_intCast (i.comp σ), ← hsum, map_sum]
    simp [map_mul]
  have hP'eig : ∀ w ∈ eigSp ρ' (i.comp σ), P' w = ((NumberField.discr F : ℤ) : Ω') • w := by
    intro w hw
    have hw' := (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ' (i.comp σ) w).mp hw
    calc P' w = ∑ m, i (σ (c m)) • ρ' (a m) w := hP'apply w
      _ = ∑ m, (i (σ (c m)) * i (σ (a m))) • w :=
          Finset.sum_congr rfl fun m _ => by rw [hw', RingHom.comp_apply, smul_smul]
      _ = _ := by rw [← Finset.sum_smul, hscal]
  have hP'j : ∀ e, P' (j e) = j (∑ m, σ (c m) • ρ (a m) e) := by
    intro e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP'apply, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcomp, hj.1]
  have hPe : ∀ e, ∑ m, σ (c m) • ρ (a m) e ∈ eigSp ρ σ := fun e =>
    (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ σ _).mpr fun b => hcas Ω V ρ σ b e
  apply le_antisymm
  · intro w hw
    have hle : Submodule.span Ω' (Set.range j) ≤
        (Submodule.span Ω' (j '' (eigSp ρ σ : Set V))).comap P' := by
      rw [Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hP'j]
      exact Submodule.subset_span ⟨_, hPe e, rfl⟩
    have hmem : P' w ∈ Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) :=
      hle (by rw [hspan]; exact Submodule.mem_top)
    rw [hP'eig w hw] at hmem
    have hd : ((NumberField.discr F : ℤ) : Ω') ≠ 0 := by
      rw [← map_intCast i]
      exact (map_ne_zero i).mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))
    have h2 := Submodule.smul_mem _ ((NumberField.discr F : ℤ) : Ω')⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ σ v).mp hv
    refine (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ' (i.comp σ) (j v)).mpr fun b => ?_
    rw [hcomp, hv' b, hj.1, RingHom.comp_apply]

end GlobalTheory.CompanionTheory.Ar.EigExt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbeddingFactorsThroughCmType
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LabelCover

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_ext {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K] (τ : 𝓞 E →+* K) :
    ∃ ψ : E →+* K, ψ.comp (algebraMap (𝓞 E) E) = τ := by
  have hker : RingHom.ker τ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [Ideal.under_def, RingHom.comap_ker, RingHom.ker_eq_bot_iff_eq_zero]
    intro n hn
    simpa using hn
  have hinj : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot τ).mpr hker
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩

theorem charZero_of_coeff {F : IntermediateField ℚ ℂ} {k : Type} [Field k] (φ : F →+* k) : CharZero k :=
  (RingHom.charZero_iff (φ.comp (algebraMap ℚ F)).injective).mp inferInstance

theorem exists_factor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {k : Type} [Field k] [IsAlgClosed k] (φ : c.F →+* k) (ψ : E →+* k) :
    ∃ τ₁ : E →+* ℂ, φ.comp (τ₁.codRestrict c.F (c.conj τ₁)) = ψ := by
  haveI : CharZero k := charZero_of_coeff φ
  let g : (E →+* ℂ) → (E →+* k) := fun τ => φ.comp (τ.codRestrict c.F (c.conj τ))
  have hg : Function.Injective g := by
    intro τ τ' h
    ext a
    have h1 := RingHom.congr_fun h a
    simp only [g, RingHom.comp_apply] at h1
    exact congrArg Subtype.val (φ.injective h1)
  have hcard : Fintype.card (E →+* ℂ) = Fintype.card (E →+* k) := by
    rw [NumberField.Embeddings.card, NumberField.Embeddings.card]
  obtain ⟨τ₁, hτ₁⟩ := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, hcard⟩).2 ψ
  exact ⟨τ₁, hτ₁⟩

theorem exists_label : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (ρ₀ : c.F), (ρ₀ : ℂ) = H.rt0 → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (τ : 𝓞 E →+* k),
    (τ H.rt = φ ρ₀ → ∃ t : CMType H, φ.comp (labelEmb c (.inl t)) = τ) ∧
    (τ H.rt ≠ φ ρ₀ → ∃ t : CMType H, φ.comp (labelEmb c (.inr t)) = τ) := by
  intro E _ _ _ H l c ρ₀ hρ₀ k _ _ φ τ
  haveI : CharZero k := charZero_of_coeff φ
  obtain ⟨ψ, hψ⟩ := exists_ext τ
  obtain ⟨τ₁, hτ₁⟩ := exists_factor c φ ψ
  have key : ∀ a : 𝓞 E, φ ⟨τ₁ (a : E), c.conj τ₁ (a : E)⟩ = τ a := by
    intro a
    rw [← hψ, ← hτ₁]
    rfl
  have hrt : τ₁ (H.rt : E) = H.rt0 ↔ τ H.rt = φ ρ₀ := by
    constructor
    · intro h
      rw [← key]
      congr 1
      exact Subtype.ext (h.trans hρ₀.symm)
    · intro h
      rw [← key] at h
      rw [← hρ₀]
      exact congrArg Subtype.val (φ.injective h)
  refine ⟨fun h => ⟨⟨τ₁, hrt.mpr h⟩, RingHom.ext fun a => key a⟩, fun h => ?_⟩
  have hne : τ₁ (H.rt : E) ≠ H.rt0 := fun h' => h (hrt.mp h')
  have hsqE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hsq : τ₁ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hsqE, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  have hneg : τ₁ (H.rt : E) = -H.rt0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : H.rt0.re = 0 := by
    have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h1 h2
    have h3 : H.rt0.re * H.rt0.im = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exfalso
      rw [h4] at h1
      nlinarith [sq_nonneg H.rt0.re]
  have hconj : (starRingEnd ℂ) (-H.rt0) = H.rt0 := by
    apply Complex.ext <;> simp [hre]
  refine ⟨⟨τ₁.comp (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom, ?_⟩, ?_⟩
  · show τ₁ (NumberField.IsCMField.complexConj E (H.rt : E)) = H.rt0
    rw [NumberField.IsCMField.complexEmbedding_complexConj, hneg, hconj]
  · refine RingHom.ext fun a => ?_
    rw [← key a, RingHom.comp_apply]
    refine congrArg φ (Subtype.ext ?_)
    show τ₁ (NumberField.IsCMField.complexConj E ((H.bar a : 𝓞 E) : E)) = τ₁ (a : E)
    rw [H.bar_eq, NumberField.IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.LabelCover
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelLeft
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Flags

theorem isExtOver_mk (Ω K E : Type) [Field Ω] [Field K] [Algebra Ω K] [AddCommGroup E] [Module Ω E] :
    IsExtOver (algebraMap Ω K) (TensorProduct.mk Ω K E 1).toAddMonoidHom := by
  refine ⟨fun a e => ?_, fun n b hb => ?_⟩
  · show (1 : K) ⊗ₜ[Ω] (a • e) = algebraMap Ω K a • ((1 : K) ⊗ₜ[Ω] e)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  · exact Module.Flat.linearIndependent_one_tmul hb

theorem pull_isFlagVB_genB : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom).IsFlagVBOn Set.univ (genB c s) := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hx hgen hVB hTw hc hx' hgen' hd hch s p' _
  classical
  obtain ⟨⟨c₁, J⟩, hcJ⟩ := hx'.cover p'
  obtain ⟨hx0, hchart, hmin⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios Ω E κ x S r n φ c X' ξ' p' c₁ J hcJ
  obtain ⟨hfp, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' _ ξ' f _ hd p'
  have hInC : InChart ξ x c₁ ⟨f p'.1, hfp⟩ := (hch p' c₁ hfp).2 hchart
  obtain ⟨U, hU, β₀, hspan, hfr⟩ := hVB s ⟨f p'.1, hfp⟩ trivial
  have hfr0 := hfr ⟨f p'.1, hfp⟩ trivial hU
  obtain ⟨B₀, hBreg, hAreg, hBA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse X Ω ξ E κ x (L s) (m s) (n s) (r s) (φ s) (hTw s) _ c₁ hInC β₀ hfr0
  have hxΩ : x c₁ ≠ 0 := hInC.1
  have hCex : ∀ l, ∃ C : Fin (r s) → Ω, c s l = ∑ a, C a • β₀ a := by
    intro l
    have : c s l ∈ Submodule.span Ω (Set.range β₀) := by
      rw [hspan, ← (hc s).2]
      exact Submodule.subset_span ⟨l, rfl⟩
    obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
    exact ⟨C, hC.symm⟩
  choose C hC using hCex
  set ι := algebraMap Ω (GenField Ω r) with hι
  let A₀ : Matrix (Fin (n s)) (Fin (r s)) Ω := Matrix.of (fun j a => φ s j (β₀ a) / x c₁ ^ m s)
  let A : Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) := A₀.map ι
  let B : Matrix (Fin (r s)) (Fin (n s)) (GenField Ω r) := B₀.map ι
  let Cm : Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := Matrix.of (fun a l => ι (C l a))
  let G : Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := Cm * genU Ω r s
  let a : GenField Ω r := ι (x c₁ ^ m s)
  have ha : a ≠ 0 := by
    simpa [a] using pow_ne_zero (m s) hx0
  have hF : flagMat φ c s = a • (A * G) := by
    have h1 : (Matrix.of (fun j l => ι (φ s j (c s l))) : Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r))
        = a • (A * Cm) := by
      ext j l
      simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, A, Cm, A₀, Matrix.map_apply, smul_eq_mul,
        Finset.mul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hC l, map_sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_smul, smul_eq_mul, a, ← map_mul]
      congr 1
      field_simp
    rw [flagMat, h1, Matrix.smul_mul, Matrix.mul_assoc]
  have hBA' : B * A = 1 := by
    have := congrArg (fun M : Matrix (Fin (r s)) (Fin (r s)) Ω => M.map ι) hBA
    simpa [B, A, A₀, Matrix.map_mul] using this
  haveI : IsLocalRing (regAt ξ' p') := EigSplit.isLocalRing_regAt p'
  obtain ⟨P, hPreg, hP0, hPinv, hPflag⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted (GenField Ω r) (regAt ξ' p') (r s) (fun c i => G i c) (fun k =>
    GlobalTheory.T.minor_ratio_regular_of_invertible (GenField Ω r) (regAt ξ' p') (n s) (r s) A B G a k (J ⟨s, k⟩)
      (fun j l => hreg _ (hAreg j l)) (fun l j => hreg _ (hBreg l j)) hBA' ha
      (by have := (hmin ⟨s, k⟩).1; rwa [show flagMat φ c (⟨s, k⟩ : Σ s, Fin (r s)).1 = a • (A * G) from hF] at this)
      (by have := (hmin ⟨s, k⟩).2; rwa [show flagMat φ c (⟨s, k⟩ : Σ s, Fin (r s)).1 = a • (A * G) from hF] at this))
  have hext := isExtOver_mk Ω (GenField Ω r) E
  let β : Fin (r s) → TensorProduct Ω (GenField Ω r) E := fun a => TensorProduct.mk Ω (GenField Ω r) E 1 (β₀ a)
  let T : (Fin (r s) → GenField Ω r) →ₗ[GenField Ω r] TensorProduct Ω (GenField Ω r) E :=
    Fintype.linearCombination (GenField Ω r) β
  have hTapp : ∀ v, T v = ∑ a, v a • β a := fun v => by simp [T, Fintype.linearCombination_apply]
  have hmap : ∀ (w : Fin (r s) → Fin (r s) → GenField Ω r) (i : ℕ),
      flagStep (GenField Ω r) (fun k => T (w k)) i = (flagStep (GenField Ω r) w i).map T := by
    intro w i
    simp only [flagStep, Submodule.map_span, Set.image_image]
  have hgenB : genB c s = fun k => T (fun a => G a k) := by
    funext k
    rw [hTapp]
    simp only [genB, G, Matrix.mul_apply, Cm, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hC l, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 : TensorProduct.mk Ω (GenField Ω r) E 1 (C l b • β₀ b) = ι (C l b) • β b := hext.1 (C l b) (β₀ b)
    rw [h1, smul_smul, mul_comm]
  have hPfun : (fun k => ∑ a, P a k • β a) = fun k => T (fun a => P a k) := by
    funext k
    rw [hTapp]
  obtain ⟨U₁, hU₁, hq₁⟩ := EigSplit.exists_open_forall_mem_regAt p'
    (fun ab : Fin (r s) × Fin (r s) => P ab.1 ab.2) (fun ab => hPreg _ _)
  have hdetreg : P.det ∈ regAt ξ' p' := by
    rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hPreg _ _)
  obtain ⟨U₂, hU₂, hq₂⟩ := (regAt_unitAt_open X' _ ξ' p' P.det).2 ⟨hP0, hdetreg, hPinv⟩
  refine ⟨(f ⁻¹ᵁ U) ⊓ U₁ ⊓ U₂, ⟨⟨hU, hU₁⟩, hU₂⟩, fun k => ∑ a, P a k • β a, ?_, ?_⟩
  · intro i
    rw [hgenB, hPfun, hmap, hmap, hPflag]
  · rintro q - ⟨⟨hqU, hq1⟩, hq2⟩
    obtain ⟨hqf, -, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' _ ξ' f _ hd q
    have hfq := hfr ⟨f q.1, hqf⟩ trivial hqU
    have hpull := FlagPull.pull_isFrameAt hd hext q hqf hfq
    exact _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb X' _ ξ' _ _ _ β q P hpull (fun a b => hq₁ q hq1 (a, b)) (hq₂ q hq2)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Flags
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagHeightBoundArithVar
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V]
  [Module Ω V]

theorem patch_eq_of_subset {S₀ S : Finset ℕ} (h : S₀ ⊆ S) (L₀ : Lat ξ V) (Lp : ℕ → Lat ξ V) {q : Cpt ξ}
    (hq : ∀ p ∈ S, p ∉ S₀ → ¬ InFibre ξ p q) : Lat.patch S₀ L₀ Lp q = Lat.patch S L₀ Lp q := by
  have hmem : ∀ p, (p ∈ S₀ ∧ InFibre ξ p q) ↔ (p ∈ S ∧ InFibre ξ p q) := fun p =>
    ⟨fun ⟨a, b⟩ => ⟨h a, b⟩, fun ⟨a, b⟩ => ⟨by_contra fun c => hq p a c b, b⟩⟩
  have hex : (∃ p ∈ S₀, InFibre ξ p q) ↔ ∃ p ∈ S, InFibre ξ p q := exists_congr hmem
  simp only [Lat.patch]
  by_cases hc : ∃ p ∈ S, InFibre ξ p q
  · rw [if_pos hc, if_pos (hex.2 hc)]
    refine le_antisymm (le_iInf₂ fun p hp => le_iInf fun hf => ?_) (le_iInf₂ fun p hp => le_iInf fun hf => ?_)
    · exact iInf₂_le_of_le p ((hmem p).2 ⟨hp, hf⟩).1 (iInf_le _ hf)
    · exact iInf₂_le_of_le p (h hp) (iInf_le _ hf)
  · rw [if_neg hc, if_neg (fun c => hc (hex.1 c))]

theorem gr_congr_at {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V) (i : Fin r) {q : Cpt ξ} (hq : L q = L' q) :
    L.gr b i q = L'.gr b i q := by
  simp only [Lat.gr, hq]

theorem tens_congr_at {I : Type} [Fintype I] {Λ Λ' : I → Lat ξ Ω} (a : I → ℤ) {q : Cpt ξ}
    (hq : ∀ i, Λ i q = Λ' i q) : Lat.tens Λ a q = Lat.tens Λ' a q := by
  simp only [Lat.tens, Lat.IsGenAt, hq]

end General

theorem rootLat_shrink_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (q : Cpt 𝔐.ξ), (∀ p ∈ S, p ∉ S₀ → ¬ InFibre 𝔐.ξ p q) → ∀ r, (Fl.shrink S₀ h hvb hsub).rootLat r q = Fl.rootLat r q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ Fl S₀ h hvb hsub q hq r
  refine tens_congr_at (Λ := fun _ : Unit => (𝔐.VAt S₀ (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1)
    (HodgeCpt.rootIdx D r).2) (Λ' := fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1)
    (HodgeCpt.rootIdx D r).2) _ fun _ => gr_congr_at _ _ ?_
  exact patch_eq_of_subset h _ _ hq

end GlobalTheory.CompanionTheory.Ar.Num

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagVectorBundleTransport
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagIso

theorem flag_graded_transport : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (e : X' ≅ X) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (φ : V ≃ₗ[Ω] V') (L : Lat ξ V) (L' : Lat ξ' V') (r : ℕ) (b : Fin r → V), ξ' ≫ e.hom = ξ → (∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) (v : V), v ∈ L ⟨e.hom q.1, h⟩ ↔ φ v ∈ L' q) → (L.IsFlagVBOn Set.univ b ↔ L'.IsFlagVBOn Set.univ (fun i => φ (b i))) ∧ ∀ (i : Fin r) (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), (L'.gr (fun i => φ (b i)) i q : Set Ω) = L.gr b i ⟨e.hom q.1, h⟩ :=
  @PositivityTheory.UnitarySelfGeneration.flag_bundle_iff_under_isomorphism

end GlobalTheory.CompanionTheory.Ar.FlagIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineDegreeSpecialFibre
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem propZ_numerical : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → NumTrivMod L (algebraMap O Ω ϖ) → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p :=
  @PositivityTheory.Xgn.normal_proper_line_order

end GlobalTheory.CompanionTheory.Ar.Flat
end

