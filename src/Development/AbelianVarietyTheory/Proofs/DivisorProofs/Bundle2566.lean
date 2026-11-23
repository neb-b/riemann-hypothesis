module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleEqTopOfSupMaximalSmulEqTop
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

theorem submodule_eq_top_of_sup_maximal_smul_eq_top :
    ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
      (M : Submodule R N), (∀ m : Ideal R, m.IsMaximal → M ⊔ m • ⊤ = ⊤) → M = ⊤ := by
  intro R _ N _ _ _ M h

  have hQ : ∀ m : Ideal R, m.IsMaximal → (⊤ : Submodule R (N ⧸ M)) ≤ m • ⊤ := by
    intro m hm
    have h1 := congrArg (Submodule.map M.mkQ) (h m hm)
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
    have h2 : Submodule.map M.mkQ M = ⊥ := Submodule.mkQ_map_self M
    rw [h2, bot_sup_eq] at h1
    rw [h1]
  have hfg : (⊤ : Submodule R (N ⧸ M)).FG := Module.Finite.fg_top
  have hann : Module.annihilator R (N ⧸ M) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ hfg (hQ m hm)
    have hrm : r ∈ m := hle (Module.mem_annihilator.mpr fun q => hr q Submodule.mem_top)
    have : (1 : R) ∈ m := by
      have := m.sub_mem hrm hr1
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr this)
  rw [eq_top_iff]
  intro n _
  have h1 : (1 : R) ∈ Module.annihilator R (N ⧸ M) := hann ▸ Submodule.mem_top
  have h0 : (Submodule.Quotient.mk n : N ⧸ M) = 0 := by
    simpa using Module.mem_annihilator.mp h1 (Submodule.Quotient.mk n)
  exact (Submodule.Quotient.mk_eq_zero M).mp h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def TorChar {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) : Prop :=
  χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ ∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ →
    ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A),
      p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧
      x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left

def TransExp {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ a τ : X₁.S.Gam) (e : ℕ) : Prop :=
  ∀ χ, TorChar 𝔪 τ χ → ∀ (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T →
    ∀ c, lab c = a → ∀ (C' : Type) (lab' : C' → X₁.S.Gam) (T' : (Fin 8 → X) → C' → V), 𝔪.Terms x₀ lab' T' →
    ∀ c', lab' c' = a + τ → ∀ mu : Fin 8 → X,
      ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * algebraMap V (FractionRing V) (T mu c) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * algebraMap V (FractionRing V) (T' mu c')

theorem sumF_const_mul {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {K : Type} [Field K]
    [Algebra (FractionRing R) K] {Ix : Type} {x : Ix → K} {s : K} (c : K) (h : SumF I K x s) :
    SumF I K (fun j => c * x j) (c * s) := by
  letI : Module R K := Module.compHom K (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hlim⟩ := h
  let f : K →ₗ[R] K :=
    { toFun := fun y => c * y
      map_add' := fun y z => mul_add c y z
      map_smul' := fun r y => by
        change c * ((algebraMap R (FractionRing R) r : FractionRing R) • y) = (algebraMap R (FractionRing R) r : FractionRing R) • (c * y)
        rw [Algebra.smul_def, Algebra.smul_def]; ring }
  refine ⟨N.map f, hN.map f, ⟨s, hs, rfl⟩, fun j => ⟨x j, hx j, rfl⟩, fun k => ?_⟩
  obtain ⟨S, hS⟩ := hlim k
  refine ⟨S, fun T hT => ?_⟩
  have := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at this
  convert this using 1
  change c * s - ∑ j ∈ T, c * x j = c * (s - ∑ j ∈ T, x j)
  rw [mul_sub, Finset.mul_sum]

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.TwistSum₂

theorem sumI_of_sumF_mul {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] {Ix : Type}
    (y : Ix → V) (v : V) (d : FractionRing V) (hd : d ≠ 0)
    (h : SumF (maximalIdeal V) (FractionRing V) (fun i => algebraMap V (FractionRing V) (y i) * d)
      (algebraMap V (FractionRing V) v * d)) :
    SumI (maximalIdeal V) y v := by
  classical
  have hsm : ∀ (r : V) (x : FractionRing V), r • x = algebraMap V (FractionRing V) r * x := Algebra.smul_def
  have hmod : (Module.compHom (FractionRing V) (algebraMap V (FractionRing V)) : Module V (FractionRing V)) =
      Algebra.toModule := Module.ext' _ _ fun r x => (Algebra.smul_def r x).symm
  unfold SumF at h
  rw [hmod] at h
  obtain ⟨N, hN, -, -, hS⟩ := h
  let P : Submodule V (FractionRing V) := N ⊔ Submodule.span V {d}
  haveI : Module.Finite V P := Module.Finite.iff_fg.mpr (hN.sup (Submodule.fg_span_singleton d))
  let L : Submodule V P := (Submodule.span V {d}).comap P.subtype
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal V) L
  refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS (n + k)
  refine ⟨S, fun T hT => ?_⟩
  set w : V := v - ∑ i ∈ T, y i with hw
  have e : algebraMap V (FractionRing V) w * d =
      algebraMap V (FractionRing V) v * d - ∑ i ∈ T, algebraMap V (FractionRing V) (y i) * d := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sub, map_sum, sub_mul, Finset.sum_mul]
  have h1 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ (n + k) • N := e ▸ hS T hT
  have hwP : algebraMap V (FractionRing V) w * d ∈ P :=
    Submodule.mem_sup_right (by rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d))
  let p : P := ⟨_, hwP⟩
  have hp1 : p ∈ maximalIdeal V ^ (n + k) • (⊤ : Submodule V P) :=
    (Submodule.mem_smul_top_iff _ P p).2 (Submodule.smul_mono le_rfl le_sup_left h1)
  have hp2 : p ∈ L := by
    show algebraMap V (FractionRing V) w * d ∈ Submodule.span V {d}
    rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  have hp3 : p ∈ maximalIdeal V ^ n • L := by
    have := (hk (n + k) (Nat.le_add_left _ _)).le ⟨hp1, hp2⟩
    rw [Nat.add_sub_cancel] at this
    exact Submodule.smul_mono le_rfl inf_le_right this
  have hp4 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ n • Submodule.span V {d} := by
    have := Submodule.mem_map_of_mem (f := P.subtype) hp3
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _) this
  obtain ⟨u, hu, hud⟩ := Submodule.mem_smul_span_singleton.1 hp4
  rw [hsm] at hud
  have hwu : w = u := IsFractionRing.injective V (FractionRing V) (mul_right_cancel₀ hd hud).symm
  rw [hwu]
  simpa using Submodule.smul_mem_smul hu (Submodule.mem_top : (1 : V) ∈ (⊤ : Submodule V V))

end GlobalTheory.Poinc.TwistSum₂

namespace GlobalTheory.Poinc.TwistSum₂

open GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem val_stalkHom (X₁ : Setup F W i) (z₁ : X₁.M.Z) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) [IsLocalHom ev] (a : X₁.M.Z.presheaf.stalk z₁) :
    X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (X₁.M.stalkHom z₁ a) =
      algebraMap V (FractionRing V) (ev a) := by
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have h : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) ⤳ z₁ := specializes_of_eq hc
  have e := RatModel.val_spMap_comp (algebraMap V (FractionRing V)) (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) h
    (X₁.M.stalkEquiv z₁ a)
  rw [RatModel.coe_stalkEquiv] at e
  refine e.trans (congrArg _ ?_)
  have hψ : Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) ≫
      X₁.M.Z.fromSpecStalk z₁ = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have heq : spMap ev = Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫
      Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) := by
    rw [← cancel_mono (X₁.M.Z.fromSpecStalk z₁), hψ]
  have hφψ := Spec.map_injective heq
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  exact (congrArg (fun φ => φ.hom a) hφψ).symm

theorem twistSum_of_sumF : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (e : ℕ), 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 → (∀ mu, ∃ a : X₁.S.Gam, 𝔪.YY a mu) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) → SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) → TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ C lab T sg c τ χ e hθ hY hχ hS
  intro zt h hzt hh wt hwt
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have hsp : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₁.M) (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.closedPoint (FractionRing V)))
  have hgen : (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) ⤳ z₁ := by
    have h1 : (jK V) (closedPoint (FractionRing V)) ⤳ closedPoint V := IsLocalRing.specializes_closedPoint _
    have h2 := h1.map (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁).continuous
    rw [hc] at h2
    exact h2
  have hO : ∀ s, X₁.M.stalkHom z₁ s ∈
      X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := fun s =>
    RatModel.O_le_of_specializes hgen (X₁.M.stalkEquiv z₁ s).2
  have hR : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := 𝔪.reg
  have hyK : ∀ (a : X₁.Ω₁) (ha : a ∈ X₁.S.R), 𝔪.yK ⟨a, ha⟩ = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a :=
    fun a ha => 𝔪.yK_eq ⟨a, ha⟩
  have hyA : ∀ b : X₁.o₁, 𝔪.yK (algebraMap X₁.o₁ X₁.S.R b) =
      X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (algebraMap X₁.o₁ X₁.Ω₁ b) := fun b => by
    rw [𝔪.yK_eq, Subalgebra.coe_algebraMap]
  have hzt' : algebraMap V (FractionRing V) (ev zt) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := by
    rw [← val_stalkHom X₁ z₁ ev, hzt, hyA]
  have hth0 : X₁.S.th x₀ ≠ 0 := by
    intro h0
    apply hθ
    rw [hyK, h0, RatModel.val_zero]
  have hh' : algebraMap V (FractionRing V) (ev h) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ =
      𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩ := by
    rw [← val_stalkHom X₁ z₁ ev, hyA, hyK, hyK, ← RatModel.val_mul hsp (hO h) (hR _ (X₁.S.th_mem x₀)),
      ← RatModel.val_mul hsp (hR _ (Subalgebra.algebraMap_mem _ _)) (hR _ (X₁.S.th_mem _)), hh,
      div_mul_cancel₀ _ hth0]
  have hterm : ∀ mu : Fin 8 → X, ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) *
      (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) =
      algebraMap V (FractionRing V) (ev zt ^ (wt mu).val * T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro mu
    obtain ⟨a, ha⟩ := hY mu
    rw [hχ a mu ha, ← hwt a mu ha, pow_mul, map_pow, map_pow, ← hzt', map_mul, map_pow]
    ring
  refine TwistSum₂.sumI_of_sumF_mul _ _ _ hθ ?_
  convert hS using 1
  · funext mu
    exact (hterm mu).symm

end GlobalTheory.Poinc.TwistSum₂
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFunctionFieldModelHomOfProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjModelSurj

theorem surjective_of_isProjOver (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (X M : RatModel o Ω) (f : M.Z ⟶ X.Z)
    (hf : X.IsHom M (AlgHom.id o Ω) f) (hM : IsProjOver M.s) : Function.Surjective f := by
  obtain ⟨N, i, hi, hs⟩ := hM
  haveI : IsProper (PSpace.str o N) := isProper_str o N
  haveI : IsProper M.s := hs ▸ inferInstance
  haveI : IsSeparated X.s := X.sep
  haveI : IsProper (f ≫ X.s) := by rw [hf.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : IsProper f := IsProper.of_comp f X.s
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have hgen : genericPoint X.Z ∈ Set.range f := by
    have w : Sp Ω := IsLocalRing.closedPoint Ω
    refine ⟨M.pt w, ?_⟩
    have h : (M.pt ≫ f) w = (spMap (AlgHom.id o Ω).toRingHom ≫ X.pt) w := by rw [hf]
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact X.pt_apply _
  intro x
  obtain ⟨y, hy⟩ := (genericPoint_specializes x).mem_closed hcl hgen
  exact ⟨y, hy⟩

end GlobalTheory.ProjModelSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SvalEqSecRatioMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TermWeight

theorem sval_eq_secRatio_mul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a b : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) (hz : r z ∈ nonzeroLocus a) :
    sval b r z J = gs r z (nonzeroLocus a) (GlobalTheory.ProjSpace.secRatio a b) * sval a r z J := by
  have hm : r z ∈ nonzeroLocus a ⊓ LB.wchart L φ (fun k => J (r ≫ φ k)) := ⟨hz, hJ.mem φ r⟩
  have e := congrArg (gs r z _) (GlobalTheory.ProjSpace.secRatio_on a b (fun k => J (r ≫ φ k))
    (W := nonzeroLocus a ⊓ LB.wchart L φ (fun k => J (r ≫ φ k))) inf_le_left inf_le_right)
  exact (gs_res r z inf_le_right hm _).symm.trans (e.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z inf_le_left hm _) (gs_res r z inf_le_right hm _))))

theorem isWt_secRatio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (i : splitTorus (Sp R) D.X ⟶ Y.H), (∀ (χ : D.X) (Z : Over (Sp R)) (t : Z ⟶ splitTorus (Sp R) D.X) (g : Z ⟶ Y.H) (z : Z.left) J, Good D.P.L z J → val ((Y.Φ Z ((t ≫ i) * g)).s χ) (𝟙 _) z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * val ((Y.Φ Z g).s χ) (𝟙 _) z J) → IsPullback i (toUnit _) Y.q η[D.P.A] → ∀ (k : ℕ) (α : D.X) (b₀ : D.SecB k 0) (b : D.SecB k α) (τ₀ τ : SecK D.P.L Y.q.left k), IsTermOf Y b₀ τ₀ → IsTermOf Y b τ → GlobalTheory.UU.IsWt i (nonzeroLocus τ₀) (GlobalTheory.ProjSpace.secRatio τ₀ τ) α := by
  intro R _ _ D Y i hi hk k α b₀ b τ₀ τ h₀ h
  have := Y.isMonHom_q
  refine GlobalTheory.GtCoordCompare.isWt_of_gs fun Z t g hg z => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  have hq : (((t ≫ i) * g) ≫ Y.q).left = (g ≫ Y.q).left := GlobalTheory.GtCoordCompare.act_comp hk.w t g
  have z₁ : val ((Y.Φ Z ((t ≫ i) * g)).s 0) (𝟙 _) z J = 1 := GlobalTheory.TorusModel.cv_zero _ hJ
  have z₂ : val ((Y.Φ Z g).s 0) (𝟙 _) z J = 1 := GlobalTheory.TorusModel.cv_zero _ hJ
  have e₀ : sval τ₀ ((t ≫ i) * g).left z J = sval τ₀ g.left z J := by
    rw [h₀ Z _ z J hJ, h₀ Z g z J hJ, hq, z₁, z₂]
  have e : sval τ ((t ≫ i) * g).left z J =
      (gm t.left z ⊤ (charUnit (Sp R) D.X α)).val * sval τ g.left z J := by
    rw [h Z _ z J hJ, h Z g z J hJ, hq, hi α Z t g z J hJ, Units.val_mul, mul_left_comm]
  have hz : g.left z ∈ nonzeroLocus τ₀ := hg (Set.mem_univ z)
  have hu : IsUnit (sval τ₀ g.left z J) := (TermLocus.isUnit_sval_iff τ₀ _ z hJ).2 hz
  have hz' : ((t ≫ i) * g).left z ∈ nonzeroLocus τ₀ := (TermLocus.isUnit_sval_iff τ₀ _ z hJ).1 (e₀ ▸ hu)
  refine hu.mul_right_cancel ?_
  rw [_root_.mul_assoc, ← sval_eq_secRatio_mul τ₀ τ g.left z hJ hz, ← e, sval_eq_secRatio_mul τ₀ τ _ z hJ hz', e₀]

end GlobalTheory.Mum.TermWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseDataPullbackAlongMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.PullFrom

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem good_exists {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun k => k.elim)
  exact ⟨J, hJ⟩

private theorem sq_ext_lemma {S Z : Scheme.{0}} {G : Over S} {f g : Z ⟶ (G2 G).left}
    (h₁ : f ≫ (fst G G).left = g ≫ (fst G G).left) (h₂ : f ≫ (snd G G).left = g ≫ (snd G G).left) : f = g :=
  Over.tensorObj_ext _ _ h₁ h₂

theorem pullData_of_dataFrom : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (Q' : Data V) (e' : Q'.X ≃+ (Fin T.r → ℤ)), (∀ i, θ (s i) ≠ 0) → DataFrom T iw s ε n Q e → DataFrom T (θ.comp iw) (fun i => θ (s i)) ε n Q' e' → PullData Q θ Q' (e'.trans e.symm) := by
  intro o W _ _ _ T R V _ _ _ _ θ iw I _ s ε n Q e Q' e' hs hQ hQ'
  obtain ⟨β₀, β₀₂, w₀, hpb₀, hsq₀, hw₀, hc₀, hτ₀⟩ := hQ
  obtain ⟨β₁, β₁₂, w₁, hpb₁, hsq₁, hw₁, hc₁, hτ₁⟩ := hQ'
  have hcomp : spMap θ ≫ spMap iw = spMap (θ.comp iw) := (spMap_comp_ring iw θ).symm

  obtain ⟨β, β₂, hpb, hsq, hβ, hβ₂⟩ := _root_.GlobalTheory.GrpCancel.exists_cancel_square (Sp V) (Sp R) (Sp W) Q'.B Q.B T.B (spMap θ) (spMap iw)
    β₁ β₀ β₁₂ β₀₂ (hcomp ▸ hpb₁) hpb₀ hsq₁ hsq₀

  obtain ⟨w, hw, hrel⟩ := _root_.GlobalTheory.LamCancel.lam_cancel (Sp V) (Sp R) (Sp W) Q'.B Q.B T.B Q'.M.L Q.M.L T.M.L Q'.M.isLB Q.M.isLB
    T.M.isLB β₂ β₀₂ β₁₂ hβ₂ w₀ hw₀ w₁ hw₁

  have hcc : ∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c ((e'.trans e.symm) a)).left := by
    intro a
    apply hpb₀.1.hom_ext
    · simp only [Category.assoc, hβ, hc₁, hc₀, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
      rw [← hcomp, Category.assoc]
    · simp only [Category.assoc, hpb.1.w]
      simp

  have hsqT : ∀ a b : Q.X, (lift (Q.c a) (Q.c b)).left ≫ β₀₂ =
      spMap iw ≫ (lift (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b))).left := by
    intro a b
    apply sq_ext_lemma
    · rw [Category.assoc, hsq₀.1, ← Category.assoc, ← Over.comp_left, lift_fst, hc₀, Category.assoc,
        ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hsq₀.2, ← Category.assoc, ← Over.comp_left, lift_snd, hc₀, Category.assoc,
        ← Over.comp_left, lift_snd]
  refine ⟨β, β₂, w, hpb, hsq, hw, hcc, ?_⟩
  intro a b
  set a₀ := (e'.trans e.symm) a with ha₀def
  set b₀ := (e'.trans e.symm) b with hb₀def
  have ha₀ : e a₀ = e' a := by simp [a₀]
  have hb₀ : e b₀ = e' b := by simp [b₀]

  have hsqQ : (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left ≫ β₂ =
      ((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a₀) (Q.c b₀)).left := by
    have h₁ : (lift (Q.c a₀) (Q.c b₀)).left ≫ (fst Q.B Q.B).left = (Q.c a₀).left := by
      rw [← Over.comp_left, lift_fst]
    have h₂ : (lift (Q.c a₀) (Q.c b₀)).left ≫ (snd Q.B Q.B).left = (Q.c b₀).left := by
      rw [← Over.comp_left, lift_snd]
    apply sq_ext_lemma
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc,
        hcc, Category.assoc, Category.assoc, h₁]
      rfl
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc,
        hcc, Category.assoc, Category.assoc, h₂]
      rfl
  obtain ⟨k₀, hk₀, hv₀⟩ := hτ₀ a₀ b₀
  obtain ⟨k₁, hk₁, hv₁⟩ := hτ₁ a b
  obtain ⟨x, y, hy, hxy, hxy'⟩ :=
    GlobalTheory.LaurentFrac.exists_frac R V θ s (fun i => (n : ℤ) * ε i (e' a) (e' b)) hs

  obtain ⟨u, hu, hvu⟩ := _root_.GlobalTheory.GenTransport.gen_transport (Sp R) (Sp W) Q.B T.B Q.M.L T.M.L Q.M.isLB T.M.isLB β₀₂ w₀ hw₀
    (𝟙_ (Over (Sp R))) (𝟙_ (Over (Sp W))) (Q.c a₀) (Q.c b₀) (T.c₀ ((n : ℤ) • e a₀))
    (T.c₀ ((n : ℤ) • e b₀)) (spMap iw) (hsqT a₀ b₀) (T.τ₀ _ _) (T.τ₀_gen _ _)
  refine ⟨u, x, y, k₀, k₁, hu, hy, ?_, ?_, ?_, ?_⟩
  · rw [hk₀, ha₀, hb₀]
    exact hxy
  · rw [hk₁]
    exact hxy'
  · intro z J hJ
    obtain ⟨J₀, hJ₀⟩ := good_exists T.M.isLB z
    have hl : (toUnit (TK R)).left ≫ (lift (Q.c a₀) (Q.c b₀)).left =
        (lift (toUnit (TK R) ≫ Q.c a₀) (toUnit (TK R) ≫ Q.c b₀)).left := by
      rw [← Over.comp_left, comp_lift]
    rw [hv₀ z J₀ J hJ₀ hJ, hvu _ _ z J₀ J hJ₀ hJ, hl]
    rfl
  · intro z J J' hJ hJ'
    obtain ⟨J₀, hJ₀⟩ := good_exists T.M.isLB z
    rw [ha₀, hb₀] at hvu
    rw [hv₁ z J₀ J' hJ₀ hJ', hrel _ _ z J' J J₀ hJ' hJ hJ₀, hvu _ ((TK V).hom ≫ spMap θ) z J₀ J hJ₀ hJ, hsqQ,
      Category.assoc ((TK V).hom) (spMap θ) (spMap iw), hcomp, _root_.mul_assoc]

end GlobalTheory.PullFrom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoint_conj_algClosure_automorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  first | exact @GlobalTheory.isThetaPt_conj | exact GlobalTheory.isThetaPt_conj | (intros; apply GlobalTheory.isThetaPt_conj <;> assumption)
end

