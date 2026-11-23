module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulFinrankBalancedSymmIntBilinForms
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRankSym

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem host_bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E _

theorem host_bar_rt (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    have h3 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h2] at h3
    have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have h5 : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
    have h6 := congrArg Complex.re h4
    simp [sq, h5] at h6
    have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  · exact h

variable (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]

def rtMul : X →ₗ[ℤ] X := (DistribSMul.toAddMonoidHom X H.rt).toIntLinearMap

variable {H X}

theorem rtMul_apply (y : X) : rtMul H X y = H.rt • y := rfl

theorem rt_smul_rt_smul (y : X) : H.rt • H.rt • y = -((H.d : ℤ) • y) := by
  rw [smul_smul, ← sq, H.rt_sq, neg_smul, ← Int.cast_natCast, Int.cast_smul_eq_zsmul]

theorem flip_mem_balBil {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ GlobalTheory.BalRank.balBil H.bar X) :
    β.flip ∈ GlobalTheory.BalRank.balBil H.bar X := by
  intro a y z
  show β z (a • y) = β (H.bar a • z) y
  rw [hβ (H.bar a) z y, host_bar_bar]

theorem comp_rt_mem_balBil {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ GlobalTheory.BalRank.balBil H.bar X) :
    β ∘ₗ rtMul H X ∈ GlobalTheory.BalRank.balBil H.bar X := by
  intro a y z
  simp only [LinearMap.comp_apply, rtMul_apply]
  rw [smul_comm, hβ]

theorem comp_rt_antisymm {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ GlobalTheory.BalRank.balBil H.bar X)
    (hs : ∀ y z, β y z = β z y) (y z : X) : β (H.rt • y) z = -β (H.rt • z) y := by
  rw [hβ, host_bar_rt, neg_smul, map_neg, hs]

theorem comp_rt_symm {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ GlobalTheory.BalRank.balBil H.bar X)
    (hs : ∀ y z, β y z = -β z y) (y z : X) : β (H.rt • y) z = β (H.rt • z) y := by
  rw [hβ, host_bar_rt, neg_smul, map_neg, hs, neg_neg]

end GlobalTheory.BalRankSym

namespace GlobalTheory.BalRankSym

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]

def symPart : GlobalTheory.BalRank.balBil H.bar X →ₗ[ℤ] balForms H.bar X where
  toFun β := ⟨β.1 + β.1.flip, fun y z => by simp [add_comm], fun a y z => by
    have h1 := β.2 a y z
    have h2 := flip_mem_balBil β.2 a y z
    simp only [LinearMap.add_apply]
    rw [h1, h2]⟩
  map_add' β γ := by
    apply Subtype.ext
    ext y z
    simp only [Submodule.coe_add, LinearMap.add_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply]
    ring
  map_smul' n β := by
    apply Subtype.ext
    ext y z
    simp only [SetLike.val_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply, RingHom.id_apply, smul_eq_mul]
    ring

def antiPart : GlobalTheory.BalRank.balBil H.bar X →ₗ[ℤ] balForms H.bar X where
  toFun β := ⟨(β.1 - β.1.flip) ∘ₗ rtMul H X,
    fun y z => by
      have hm : β.1 - β.1.flip ∈ GlobalTheory.BalRank.balBil H.bar X := sub_mem β.2 (flip_mem_balBil β.2)
      have := comp_rt_symm hm (fun y z => by simp) y z
      simpa [rtMul_apply] using this,
    comp_rt_mem_balBil (sub_mem β.2 (flip_mem_balBil β.2))⟩
  map_add' β γ := by
    apply Subtype.ext
    ext y z
    simp only [Submodule.coe_add, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply]
    ring
  map_smul' n β := by
    apply Subtype.ext
    ext y z
    simp only [SetLike.val_smul, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply,
      RingHom.id_apply, smul_eq_mul]
    ring

def symIncl : balForms H.bar X →ₗ[ℤ] GlobalTheory.BalRank.balBil H.bar X where
  toFun s := ⟨s.1, s.2.2⟩
  map_add' s t := rfl
  map_smul' n t := rfl

def rtPart : balForms H.bar X →ₗ[ℤ] GlobalTheory.BalRank.balBil H.bar X where
  toFun t := ⟨t.1 ∘ₗ rtMul H X, comp_rt_mem_balBil t.2.2⟩
  map_add' s t := by
    apply Subtype.ext
    ext y z
    simp
  map_smul' n t := by
    apply Subtype.ext
    ext y z
    simp

variable {H X}

theorem symPart_antiPart_injective :
    Function.Injective (LinearMap.prod (symPart H X) (antiPart H X)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro β hβ
  rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at hβ
  obtain ⟨h1, h2⟩ := hβ
  have e1 : ∀ y z, β.1 y z + β.1 z y = 0 := fun y z => by
    have := congrArg (fun γ : balForms H.bar X => γ.1 y z) h1
    simpa [symPart] using this
  have e2 : ∀ y z, β.1 (H.rt • y) z - β.1 z (H.rt • y) = 0 := fun y z => by
    have := congrArg (fun γ : balForms H.bar X => γ.1 y z) h2
    simpa [antiPart, rtMul_apply] using this
  have hd : (H.d : ℤ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have e3 : ∀ y z, β.1 y z - β.1 z y = 0 := fun y z => by
    have := e2 (H.rt • y) z
    rw [rt_smul_rt_smul, map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply, map_neg, map_zsmul] at this
    simp only [smul_eq_mul] at this
    have : (H.d : ℤ) * (β.1 y z - β.1 z y) = 0 := by linear_combination -this
    exact (mul_eq_zero.1 this).resolve_left hd
  apply Subtype.ext
  ext y z
  have := e1 y z
  have := e3 y z
  simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply]
  omega

theorem symIncl_rtPart_injective :
    Function.Injective (LinearMap.coprod (symIncl H X) (rtPart H X)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨s, t⟩ hst
  rw [LinearMap.mem_ker, LinearMap.coprod_apply] at hst
  have e : ∀ y z, s.1 y z + t.1 (H.rt • y) z = 0 := fun y z => by
    have := congrArg (fun γ : GlobalTheory.BalRank.balBil H.bar X => γ.1 y z) hst
    simpa [symIncl, rtPart, rtMul_apply, Submodule.coe_inclusion] using this
  have hd : (H.d : ℤ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have et : ∀ y z, t.1 (H.rt • y) z = 0 := fun y z => by
    have a1 := e y z
    have a2 := e z y
    have a3 := s.2.1 y z
    have a4 := comp_rt_antisymm t.2.2 t.2.1 y z
    omega
  have ht : ∀ y z, t.1 y z = 0 := fun y z => by
    have := et (H.rt • y) z
    rw [rt_smul_rt_smul, map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply] at this
    simp only [smul_eq_mul] at this
    have : (H.d : ℤ) * t.1 y z = 0 := by linear_combination -this
    exact (mul_eq_zero.1 this).resolve_left hd
  have hs : ∀ y z, s.1 y z = 0 := fun y z => by
    have := e y z
    rw [et] at this
    omega
  simp only [Prod.mk_eq_zero]
  exact ⟨Subtype.ext (LinearMap.ext fun y => LinearMap.ext fun z => hs y z),
    Subtype.ext (LinearMap.ext fun y => LinearMap.ext fun z => ht y z)⟩

theorem two_mul_finrank_balForms (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] :
    2 * Module.finrank ℤ (balForms H.bar X) = Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar X) := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (symPart_antiPart_injective (H := H) (X := X))
  have h2 := LinearMap.finrank_le_finrank_of_injective (symIncl_rtPart_injective (H := H) (X := X))
  rw [Module.finrank_prod] at h1 h2
  omega

end GlobalTheory.BalRankSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitDivisorSupportNotMemModuliRange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.SuppTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem isLocallyNoetherian_model {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω]
    (M : RatModel o' Ω) : IsLocallyNoetherian M.Z := by
  haveI := ArithBase.ded (o := o') (Ω := Ω)
  haveI := M.lft
  exact LocallyOfFiniteType.isLocallyNoetherian M.s

theorem centre_apply {X : Scheme.{0}} {x : X} {V : Type} [CommRing V] [IsLocalRing V] (g : X.presheaf.stalk x →+* V)
    [IsLocalHom g] : (spMap g ≫ X.fromSpecStalk x) (closedPoint V) = x := by
  refine (Scheme.Hom.comp_apply _ _ _).trans
    (Eq.trans (congrArg (X.fromSpecStalk x) ?_) (Scheme.fromSpecStalk_closedPoint (x := x)))
  exact comap_closedPoint g

theorem exists_uTrait_centre {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω)
    (y₀ : Sp Ω ⟶ Xo.XF c) (x : M.Z) :
    ∃ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V),
      ξ (closedPoint T.V) = x ∧ jK T.V ≫ ξ = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  haveI := ArithBase.char (o := o') (Ω := Ω)
  haveI := isLocallyNoetherian_model M
  haveI : CharZero (M.Z.presheaf.stalk x) := RingHom.charZero (M.stalkHom x)
  obtain ⟨V, _, _, _, θ, ⟨hd, hcomp, -⟩, hθ, hl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.Z.presheaf.stalk x)
  haveI := hd
  haveI := hcomp
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, -, hfl, -, hc, hy⟩ := GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V hB hd (spMap γ₀ ≫ y₀)
  haveI := hfl
  refine ⟨T, spMap (f.comp θ) ≫ M.Z.fromSpecStalk x, fK.comp γ₀, centre_apply _, ?_, ?_⟩
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← GlobalTheory.Poinc.GenTrait.spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e,
      ← Formalism.L2.Pj.spMap_comp', Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']

end GlobalTheory.UPoinc.SuppTrait

namespace GlobalTheory.UPoinc.SuppTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem lift_i_of_closedPoint (C : UCompact Xo c) (V : Type) [CommRing V] [IsLocalRing V] (g : Sp V ⟶ C.Z)
    (hg : g (closedPoint V) ∈ Set.range C.i) : ∃ σ : Sp V ⟶ Xo.XF c, σ ≫ C.i = g := by
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  haveI := C.iF_open
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := inferInstance
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) :=
    (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  obtain ⟨x, hx⟩ := hg
  let φ : C.o →+* V := (Spec.preimage (g ≫ C.z)).hom
  have hφ : spMap φ = g ≫ C.z := Spec.map_preimage _
  have hc : spMap φ (closedPoint V) = spMap C.b ((C.iF ≫ pullback.snd C.z (spMap C.b)) x) := by
    rw [hφ]
    refine (Scheme.Hom.comp_apply g C.z _).trans ((congrArg C.z hx.symm).trans ?_)
    show C.z ((C.iF ≫ pullback.fst C.z (spMap C.b)) x) = _
    rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc]
    rfl
  have hunit : ∀ a : C.o, a ≠ 0 → IsUnit (φ a) := by
    intro a ha
    by_contra hn
    have hm : a ∈ (spMap φ (closedPoint V)).asIdeal := by
      show φ a ∈ (closedPoint V).asIdeal
      exact (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [hc] at hm
    haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).isPrime
    have hb : C.b a ∈ ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal := hm
    rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal), Ideal.mem_bot] at hb
    exact ha (C.inj (hb.trans (map_zero C.b).symm))
  let ψ : c.F →+* V := IsLocalization.lift (M := nonZeroDivisors C.o) (S := c.F) (g := φ)
    (fun a => hunit a (nonZeroDivisors.ne_zero a.2))
  have hψ : ψ.comp C.b = φ := RingHom.ext fun a => IsLocalization.lift_eq (M := nonZeroDivisors C.o) (S := c.F) _ a
  have hsq : g ≫ C.z = spMap ψ ≫ spMap C.b := by
    rw [← hφ, ← hψ]; exact GlobalTheory.UTraitPt.spMap_comp_eq _ _
  let g₁ : Sp V ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap ψ) hsq
  have e1 : g₁ ≫ pullback.fst C.z (spMap C.b) = g := pullback.lift_fst _ _ _
  have hx₁ : g₁ (closedPoint V) = C.iF x := hinj ((Scheme.Hom.comp_apply g₁ (pullback.fst C.z (spMap C.b)) _).symm.trans
    ((congrArg (fun h : Sp V ⟶ C.Z => h (closedPoint V)) e1).trans
      (hx.symm.trans (Scheme.Hom.comp_apply C.iF (pullback.fst C.z (spMap C.b)) x))))
  have hr : Set.range g₁ ⊆ Set.range C.iF := by
    rintro _ ⟨w, rfl⟩
    have hs : g₁ w ⤳ g₁ (closedPoint V) := (IsLocalRing.specializes_closedPoint w).map g₁.continuous
    rw [hx₁] at hs
    exact hs.mem_open (IsOpenImmersion.isOpen_range C.iF) ⟨x, rfl⟩
  refine ⟨IsOpenImmersion.lift C.iF g₁ hr, ?_⟩
  show _ ≫ C.iF ≫ pullback.fst C.z (spMap C.b) = g
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

theorem subsingleton_of_extends (T : UTrait Xo c) (σ : Sp T.V ⟶ Xo.XF c) (h : jK T.V ≫ σ = T.y) :
    Subsingleton T.P.D.toPre.X := by
  obtain ⟨hdvr, -, -⟩ := T.cdvr
  haveI := hdvr
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  have hsemi := Xo.univ.t.semi
  have hAb : IsAbelianScheme Xo.univ.t.G :=
    { comm := hsemi.comm, smooth := hsemi.smooth, proper := Xo.univ.proper, geomConnected := hsemi.geomConnected }
  let f : Sp T.V ⟶ Xo.X := σ ≫ pullback.fst _ _
  have hB : IsAbelianScheme ((Over.pullback f).obj Xo.univ.t.G) := by
    have := hAb.comm
    have := hAb.smooth
    have := hAb.proper
    have := hAb.geomConnected
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · change Smooth (pullback.snd Xo.univ.t.G.hom f)
      infer_instance
    · change IsProper (pullback.snd Xo.univ.t.G.hom f)
      infer_instance
    · change GeometricallyConnected (pullback.snd Xo.univ.t.G.hom f)
      infer_instance
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso m₁.cart (isGrpPullback_pullback T.t.G (jK T.V))
  have h₂ := (isGrpPullback_pullback ((Over.pullback f).obj Xo.univ.t.G) (jK T.V)).comp
    (isGrpPullback_pullback Xo.univ.t.G f)
  obtain ⟨e₂, he₂, -⟩ := grpPullback_iso (m₂.cart.congr (by rw [← h, Category.assoc]) rfl) h₂
  haveI := he₁
  haveI := he₂
  have hsemiB : IsSemiAbelian ((Over.pullback f).obj Xo.univ.t.G) := by
    open MonObj in
    have := hB.proper
    refine ⟨hB.comm, hB.smooth, inferInstance, inferInstance, hB.geomConnected, ?_⟩
    intro Ω _ _ p
    let A := (Over.pullback p).obj ((Over.pullback f).obj Xo.univ.t.G)
    have hA : IsAbelianScheme A := by
      have := hB.comm
      have := hB.smooth
      have := hB.proper
      have := hB.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd _ p); infer_instance
      · change IsProper (pullback.snd _ p); infer_instance
      · change GeometricallyConnected (pullback.snd _ p); infer_instance
    have hunit : IsIso (toUnit (splitTorus (Sp Ω) PUnit)) := by
      have h : 𝟙 (splitTorus (Sp Ω) PUnit) = 1 := by
        rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
        congr 1
      exact ⟨η, h.symm, toUnit_unique _ _⟩
    exact ⟨{ X := PUnit
             B := A
             isAbelian := hA
             q := 𝟙 A
             q_hom := inferInstance
             q_flat := by rw [Over.id_left]; infer_instance
             q_surjective := by rw [Over.id_left]; infer_instance
             q_quasiCompact := by rw [Over.id_left]; infer_instance
             i := toUnit _ ≫ η
             i_hom := by have := hA.comm; infer_instance
             isKernel := by have := hunit; exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩ }⟩
  obtain ⟨F, -, -⟩ := GlobalTheory.Poinc.TraitUniq.extIso T.t.semi hsemiB (e₁.symm ≪≫ e₂)
    (show IsMonHom (e₁.inv ≫ e₂.hom) from inferInstance)
  have hp : IsProper T.t.G.hom := by
    have := hB.proper
    have : IsIso F.hom.left := inferInstanceAs (IsIso ((Over.forget _).map F.hom))
    rw [← Over.w F.hom]
    infer_instance
  exact GlobalTheory.ChartNotAb.subsingleton_of_closed_mem_abLocus T.P (fun _ _ _ _ _ => inferInstance)

end GlobalTheory.UPoinc.SuppTrait


open GlobalTheory.UPoinc.SuppTrait in
theorem GlobalTheory.UPoinc.SuppTrait.support_not_mem_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (ι : ℕ) (D : GlobalTheory.EffCartierData Y.Z), (∀ y ∈ D.idealSheaf.support, y ∉ U₀) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hhom ι D hoff hord y hy hC
  obtain ⟨T, ξ, γ, hcen, hgen, hTy⟩ := exists_uTrait_centre Y X₁.uΩ y
  have hU₀ : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hAdm.1.ne (x := w) trivial
  have hthru : ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y := by
    refine ⟨spMap γ ≫ IsOpenImmersion.lift U₀.ι Y.pt hU₀, by rw [Category.assoc, IsOpenImmersion.lift_fac, hgen], ?_⟩
    rw [Category.assoc, out.u₀_gen _ (IsOpenImmersion.lift_fac _ _ _)]
    obtain ⟨x', hx', hu⟩ := X₁.lies_uΩ
    exact ⟨spMap γ ≫ x', by rw [Category.assoc, hx'], by rw [Category.assoc, hu, hTy]⟩
  obtain ⟨a, ha, hJ⟩ := hord T ξ hthru
  have hpt : Y.pt ≫ πY ≫ X₁.π = X₁.uΩ ≫ C.i := by
    have h : Y.pt ≫ πY = X₁.M.pt := hhom.trans (by
      rw [show spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom = 𝟙 _ from Spec.map_id _, Category.id_comp])
    rw [← Category.assoc, h, X₁.comp, Category.assoc]
  have hsq : jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ C.i := by
    rw [← Category.assoc, hgen, Category.assoc, hpt, hTy]
    simp only [USetup.uΩ, Category.assoc]
  obtain ⟨σ, hσ⟩ := lift_i_of_closedPoint C T.V (ξ ≫ πY ≫ X₁.π) (by
    show X₁.π (πY (ξ (closedPoint T.V))) ∈ _
    rw [hcen]; exact hC)
  haveI := C.isPreimmersion_i
  have hσ' : jK T.V ≫ σ = T.y := by
    rw [← cancel_mono C.i, Category.assoc, hσ, hsq]
  haveI := subsingleton_of_extends T σ hσ'
  have ha0 : a = 0 := by
    rw [InvFun.evalZ, InvFun.eval_of_subsingleton, mul_zero] at ha
    exact_mod_cast ha
  subst ha0
  rw [pow_zero, Ideal.span_singleton_one] at hJ
  have htop : FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V)) = ⊤ := by
    by_contra h
    have hle : (FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V))).map (Scheme.stalkClosedPointTo ξ).hom ≤
        maximalIdeal T.V := Ideal.map_le_iff_le_comap.2 fun b hb =>
          (map_mem_nonunits_iff _ b).2 (IsLocalRing.le_maximalIdeal h hb)
    have hle' : idlAlong D.idealSheaf ξ ≤ maximalIdeal T.V := hle
    rw [hJ] at hle'
    exact (maximalIdeal.isMaximal T.V).ne_top (top_le_iff.1 hle')
  exact (mem_support_iff_stalkId _ y).1 hy (hcen ▸ htop)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelOfSecondCoordTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_kernel_of_secondCoord_trivial : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → (∀ j, x ≫ GlobalTheory.ZarhinFam.pb c.A B j = 1) → ∀ j, ∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.KerC.ker_zarhinPolarization_of_pullback) | (exact GlobalTheory.ZarhinFam.KerC.ker_zarhinPolarization_of_pullback) | (intros; apply GlobalTheory.ZarhinFam.KerC.ker_zarhinPolarization_of_pullback  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_kernel_secondCoord_equations : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ j, ((∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i) ≫ la) * (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ d = 1 := by
  first | (exact @GlobalTheory.ZarhinKerB.zarhinBundle_kernel) | (exact GlobalTheory.ZarhinKerB.zarhinBundle_kernel) | (intros; apply GlobalTheory.ZarhinKerB.zarhinBundle_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductMkPointBasicFactsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinProductMkPoint_basic_facts : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T T' : Over S} (f : T' ⟶ T) (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (g : T ⟶ GlobalTheory.ZarhinFam.Zob A B) (n : ℕ), f ≫ GlobalTheory.ZarhinFam.mkZ A B u v = GlobalTheory.ZarhinFam.mkZ A B (fun i => f ≫ u i) (fun j => f ≫ v j) ∧ GlobalTheory.ZarhinFam.mkZ A B u v ^ n = GlobalTheory.ZarhinFam.mkZ A B (fun i => u i ^ n) (fun j => v j ^ n) ∧ (GlobalTheory.ZarhinFam.mkZ A B u v = 1 ↔ (∀ i, u i = 1) ∧ ∀ j, v j = 1) ∧ g = GlobalTheory.ZarhinFam.mkZ A B (fun i => g ≫ GlobalTheory.ZarhinFam.pa A B i) (fun j => g ≫ GlobalTheory.ZarhinFam.pb A B j) := by
  first | (exact @GlobalTheory.ZarhinFam.PtFacts.mkZ_facts) | (exact GlobalTheory.ZarhinFam.PtFacts.mkZ_facts) | (intros; apply GlobalTheory.ZarhinFam.PtFacts.mkZ_facts <;> assumption)
end

