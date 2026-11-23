module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralIff
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.IntegralData

theorem integralIff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntegralIffSt Xo c := by
  intro E _ _ _ H Dw l Xo c T io y
  constructor
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩
    exact ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩
  · rintro ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩

end GlobalTheory.IntegralData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExpChain

theorem isDerivAt0_comp_linear {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem isHolTo_slice {g m : ℕ} {X : Scheme.{0}} (e : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : IsHolTo (Set.univ ×ˢ Set.univ) e) : IsHolTo Set.univ (fun z => e (0, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hj : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin m → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage hj.continuous
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, true_and] using h3
  · exact h2.comp hj.differentiableOn fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩

theorem isHolTo_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) :
    IsHolTo Set.univ (fun z => (F.ex k P z).left) := by
  have h := (F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have h2 := isHolTo_slice _ h
  simp only at h2
  exact h2

theorem isDerivAt0_ex_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → ∀ (k' : Fin F.n) (P' : (F.Di k').La →+ (Fin g → ℂ)) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsPeriod (F.Di k') ty P' → (∀ z, (F.ex k' P' (L z)).left = (F.ex k P z).left) → ∀ w (v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)), IsDerivAt0 (fun z => (F.ex k P z).left) w v ↔ IsDerivAt0 (fun z => (F.ex k' P' z).left) (L w) v := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P _ k' P' L hP' hL w v
  rw [← isDerivAt0_comp_linear _ (isHolTo_ex F k' P' hP') L w v]
  simp only [hL]

end GlobalTheory.ExpChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DerivEig

open GlobalTheory.HolHom

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem fst_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.fst (epsMul s x) = x.fst := by
  simp [epsMul]

theorem snd_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.snd (epsMul s x) = s * x.snd := by
  simp [epsMul]

theorem isDerivAt_epsMul {c : V → (Sp ℂ ⟶ X)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt c z w v)
    (s : ℂ) : HolHom.IsDerivAt c z (s • w) (spMap (epsMul s) ≫ v) := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← h.1]
    congr 2
    ext1
    exact RingHom.ext fun x => fst_epsMul s x
  · rw [valR_spMap _ _ _ ((le_preimage_dual_iff h.1 U).2 hU), snd_epsMul, h.2 U hU, map_smul, smul_eq_mul]

theorem isDerivAt_of_comp_linear {c : V → (Sp ℂ ⟶ X)} (hc : HolAt c 0) (L : V →L[ℂ] V) {w : V}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt (fun t => c (L t)) 0 w v) : HolHom.IsDerivAt c 0 (L w) v := by
  have h0 : c (L 0) = c 0 := by rw [map_zero]
  refine ⟨h.1.trans h0, fun U hU f => ?_⟩
  rw [h.2 U (by beta_reduce; rw [h0]; exact hU) f]
  have h1 : HasFDerivAt (fun t => valAt' (c t) U f) (fderiv ℂ (fun t => valAt' (c t) U f) 0) (L 0) := by
    rw [map_zero]; exact ((hc U hU).2 f).hasFDerivAt
  exact congrArg (· w) (h1.comp 0 L.hasFDerivAt).fderiv

end General

theorem eq_of_relab_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) {τ τ' : E →+* ℂ}
    (h : ∀ a : 𝓞 E, relab c σ τ (a : E) = relab c σ τ' (a : E)) : τ = τ' := by
  refine IsLocalization.ringHom_ext (𝓞 E)⁰ (RingHom.ext fun a => ?_)
  exact congrArg Subtype.val (σ.injective (h a))

end GlobalTheory.DerivEig


open GlobalTheory.HolHom GlobalTheory.DerivEig in
theorem GlobalTheory.isEigAt_iff_of_isDerivAt0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∀ (w : Fin g → ℂ) (v : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)) (τ : E →+* ℂ), IsDerivAt0 (fun z => (F.ex k P z).left) w v → (IsEigAt c τ v ↔ ∀ j, w j ≠ 0 → (e j).1 = τ) := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP w v τ hv
  have hhol : HolAt (fun z => (F.ex k P z).left) 0 := holAt_of_isHolTo (isHolTo_ex F k hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  have hact : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (fun j => relab c σ (e j).1 (a : E) * w j) (v ≫ (Xo.univ.t.act.act a).left) := by
    intro a
    let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
      ContinuousLinearMap.pi fun j => relab c σ (e j).1 (a : E) • ContinuousLinearMap.proj j
    have h1 := hv'.comp (Xo.univ.t.act.act a).left
    have h2 : (fun t => (F.ex k P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (F.ex k P (L t)).left := by
      funext t
      rw [← Over.comp_left, ← F.ex_lin k P hP a t]
      rfl
    rw [h2] at h1
    exact isDerivAt_of_comp_linear hhol L h1
  have hsc : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (relab c σ τ (a : E) • w) (spMap (epsMul (algebraMap c.F (CAt σ) (embK c τ a))) ≫ v) :=
    fun a => isDerivAt_epsMul hv' _
  constructor
  · intro h j hj
    refine eq_of_relab_eq c σ fun a => ?_
    have h1 := hact a
    have h2 : HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)
        (v ≫ (Xo.univ.t.act.act a).left) :=
      Eq.mpr (congrArg (HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)) (h a)) (hsc a)
    have h3 := eq_of_forall_fderiv_eq hhol (F.ex_diff k P hP).2 fun U hU f =>
      (h1.2 U hU f).symm.trans (h2.2 U hU f)
    exact mul_right_cancel₀ hj (congrFun h3 j)
  · intro h a
    have h1 := hact a
    have h3 : (fun j => relab c σ (e j).1 (a : E) * w j) = relab c σ τ (a : E) • w := by
      funext j
      by_cases hj : w j = 0
      · simp [hj]
      · rw [h j hj]; rfl
    rw [h3] at h1
    exact h1.unique (hsc a)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem isIntegral_rat_zeta_of_coeff (n : ℕ) : IsIntegral ℚ (zeta n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : zeta 0 = 1 := by simp [zeta]
    rw [this]; exact isIntegral_one
  · have h := Complex.isPrimitiveRoot_exp n hn.ne'
    exact (h.isIntegral hn).tower_top

theorem exists_coeff_containing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (s : Finset ℂ), (∀ z ∈ s, IsAlgebraic ℚ z) → ∃ c : Coeff l, ∀ z ∈ s, z ∈ c.F := by
  intro E _ _ _ H l s hs
  classical
  let b := Module.finBasis ℚ E
  let S : Set ℂ := (s : Set ℂ) ∪ Set.range (fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2)) ∪
    {zeta l.M', H.rt0, zeta l.A}
  have hfin : S.Finite := ((s.finite_toSet).union (Set.finite_range _)).union (Set.toFinite _)
  haveI : Finite S := hfin.to_subtype
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x ((hx | ⟨p, rfl⟩) | hx)
    · exact (hs x hx).isIntegral
    · exact (Algebra.IsIntegral.isIntegral (R := ℚ) (b p.2)).map p.1.toRatAlgHom
    · rcases hx with rfl | rfl | rfl
      · exact isIntegral_rat_zeta_of_coeff _
      · refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
        rw [H.sqrt_neg_disc_sq]
        exact (isIntegral_natCast _).neg
      · exact isIntegral_rat_zeta_of_coeff _
  have hsub : S ⊆ IntermediateField.adjoin ℚ S := IntermediateField.subset_adjoin _ _
  refine ⟨⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint, ?_, ?_, ?_⟩, ?_⟩
  · intro τ a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr a, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _ (hsub (Or.inl (Or.inr ⟨(τ, i), rfl⟩)))
  · exact hsub (Or.inr (by simp))
  · refine IntermediateField.adjoin.mono _ _ _ ?_
    intro x hx
    exact Or.inr (Or.inr hx)
  · intro z hz
    exact hsub (Or.inl (Or.inl hz))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
section
namespace GlobalTheory.LocalQuad

theorem landherrSt_of_hasseNormSt : GlobalTheory.Published.HasseNormSt → GlobalTheory.Published.LandherrSt :=
  fun H => GlobalTheory.Published.landherrSt_of_landherr (landherr_of_hasseNormSt H)

end GlobalTheory.LocalQuad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemDualCuspCharacterLatticeIffAdaptedBasis
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem mem_crdI_one_iff_of_adapted {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    {X : Data E r} (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E)
    (h : ∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) (v : Fin ρ → E) :
    v ∈ FJ.crdI 1 cu ↔ ∀ b, v b ∈ cc' b := by
  constructor
  · intro hv
    unfold FJ.crdI at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, hax⟩ := hv
      rw [← h, ← hax]
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 (FractionalIdeal.mem_coe.1 ha)
      rw [algebraMap_smul]
      exact X.Λ.smul_mem o hx.1
    | zero => exact fun b => (cc' b).zero_mem
    | add x y _ _ hx hy =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 (hx b)) (FractionalIdeal.mem_coe.2 (hy b)))
    | smul c x _ hx =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.smul_mem _ c (FractionalIdeal.mem_coe.2 (hx b)))
  · intro hv
    refine Submodule.subset_span ⟨1, FractionalIdeal.mem_coe.2 (FractionalIdeal.one_mem_one _),
      ∑ i, v i • cu.e i, ⟨(h v).2 hv, ?_⟩, one_smul _ _⟩
    exact (show ∑ i, v i • cu.e i ∈ Submodule.span E (Set.range cu.e) from
      sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem mem_dualOE_xcFD_one_iff_of_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ u : Fin ρ → E, u ∈ FJ.dualOE (FJ.XcFD 1 cu) ↔ ∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  intro E _ _ _ r ρ X cu cc' h u
  have hc := mem_crdI_one_iff_of_adapted cu cc' h
  constructor
  · intro hu a y hy
    have hm : (Pi.single a y : Fin ρ → E) ∈ FJ.XcFD 1 cu := by
      refine Submodule.subset_span fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (x a) ((hc x).1 hx a)
      refine ⟨n, ?_⟩
      rw [← hn]
      congr 1
      simp [Pi.single_apply]
    have h2 := hu _ hm
    simpa [Pi.single_apply] using h2
  · intro hu x hx
    change ∑ i, u i * x i ∈ (algebraMap (𝓞 E) E).range
    unfold FJ.XcFD at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine sum_mem fun i _ => hu i (x i) fun a' ha' => ?_
      have hm : (Pi.single i a' : Fin ρ → E) ∈ FJ.crdI 1 cu := by
        rw [hc]
        intro b
        by_cases hb : b = i
        · subst hb; simpa using ha'
        · rw [Pi.single_eq_of_ne hb]; exact (cc' b).zero_mem
      obtain ⟨n, hn⟩ := hx _ hm
      refine ⟨n, ?_⟩
      rw [hn]
      congr 1
      simp [Pi.single_apply]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul c x _ hx =>
      have e : ∑ i, u i * (c • x) i = algebraMap (𝓞 E) E c * ∑ i, u i * x i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def]; ring
      rw [e]
      exact mul_mem ⟨c, rfl⟩ hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PerFrLact
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PerGam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma perFr_lact (X : Data E r) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = perFr X x v τ i := by
  have hm : ∀ t : X.Ψ, mat (lact γ x) t = (γ : Matrix (Fin r) (Fin r) E).map t.1 * mat x t := fun _ => rfl
  have hu : ∀ t : E →+* ℂ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map t).det := fun t =>
    (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map t.mapMatrix)
  unfold perFr
  simp only [hm, GlobalTheory.PerMove.emb_mulVec]
  split_ifs
  · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _),
      Matrix.mul_one]
  · rfl
  · rw [GlobalTheory.PerMove.col_mul, GlobalTheory.PerMove.hermC_unitary _ _ _ hγ]
  · rfl
  · rfl


omit [IsCMField E] in
lemma exists_equiv (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (hγ : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ) :
    ∃ f : Λ ≃ₗ[𝓞 E] Λ, ∀ a, (f a : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) := by
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨{ toFun := fun a => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E), (hγ _).1 a.2⟩
            invFun := fun a => ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E),
              (hγ _).2 (by rw [hri]; exact a.2)⟩
            map_add' := fun a b => Subtype.ext (by simp [Matrix.mulVec_add])
            map_smul' := fun s a => Subtype.ext (by simp [Matrix.mulVec_smul])
            left_inv := fun a => Subtype.ext (hli _)
            right_inv := fun a => Subtype.ext (hri _) }, fun _ => rfl⟩

end GlobalTheory.PerGam

namespace GlobalTheory

theorem per_gam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ γ ∈ (M.X k).Γ, ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La, ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) ∧ ∀ x ∈ (M.X k).dom, ∀ a, Pf (lact γ x) (gam a) = Pf x a := by
  intro E _ _ _ H Dw l Xo c σ g e F r M _ hB _ k Pf hP γ hγ
  obtain ⟨⟨hU, hS⟩, hM, hA⟩ := (hB.gam k γ).1 hγ
  obtain ⟨f, hf⟩ := PerGam.exists_equiv _ γ hS
  let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La := (M.φ k).trans (f.trans (M.φ k).symm)
  have hg : ∀ a, (M.φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
    intro a
    rw [← hf]
    simp [gam]
  have key : ∀ (n : ℕ) (a b : (F.Di k).La),
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + n • (M.φ k b : Fin r → E) → gam a = a + n • b := by
    intro n a b h
    apply (M.φ k).injective
    apply Subtype.ext
    rw [hg, h, map_add (f := _), map_nsmul]
    rfl
  refine ⟨gam, ⟨fun a b => ?_, fun a ha => ?_, fun a => ?_⟩, fun x _ a => ?_⟩
  · have h1 := hB.ef k (gam a) (gam b)
    rw [hg, hg, hU, ← hB.ef k a b] at h1
    exact_mod_cast h1
  · obtain ⟨b, hb⟩ := hM a ha
    exact ⟨b, key _ a b hb⟩
  · obtain ⟨b, hb⟩ := hA a
    exact ⟨b, key _ a b hb⟩
  · funext j
    rw [hP, hP, hg, PerGam.perFr_lact _ γ hU]

end GlobalTheory
end

