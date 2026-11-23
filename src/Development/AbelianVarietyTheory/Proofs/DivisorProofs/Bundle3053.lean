module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOrdersAllTraitsOverModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.AllTraits

theorem localPeriods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R) (c₀ : ℕ), IsNoetherianRing R ∧ CharZero R ∧ GlobalTheory.Poinc.Eq8.IsCpl j ∧ 1 ≤ c₀ ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → T.y ≫ C.i = jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ a, ∃ k : ℕ, (k : ℤ) = c₀ * T.be (e a) (e a) ∧ Associated (ψ (p a)) (T.ϖ ^ k) := _root_.GlobalTheory.UPoinc.UPeriods.main

theorem traitThroughOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (x : Y.Z) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], IsAdicComplete (maximalIdeal A) A → ∀ θ : Y.Z.presheaf.stalk x →+* A, Function.Injective θ → IsLocalHom θ → ∃ (T : UTrait Xo c) (f : A →+* T.V), Function.Injective f ∧ IsLocalHom f ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ T.y ≫ C.i = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π := _root_.GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr

theorem pow_exp_eq {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (h : Irreducible ϖ) {a b : ℕ}
    (e : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.dvd) ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.symm.dvd)

theorem form_eq_zero {X I : Type} [AddCommGroup X] (B : LinearMap.BilinForm ℤ X) (hB : ∀ a b, B a b = B b a) (b : I → X)
    (hb : Submodule.span ℤ (Set.range b) = ⊤) (h : ∀ i j, B (b i + b j) (b i + b j) = 0) : B = 0 := by
  have h1 : ∀ i j, B (b i) (b i) + 2 * B (b i) (b j) + B (b j) (b j) = 0 := by
    intro i j
    have := h i j
    simp only [map_add (f := _), LinearMap.add_apply] at this
    rw [hB (b j) (b i)] at this
    linarith
  have h2 : ∀ i, B (b i) (b i) = 0 := fun i => by have := h1 i i; linarith
  have h3 : ∀ i j, B (b i) (b j) = 0 := fun i j => by have := h1 i j; have := h2 i; have := h2 j; linarith
  refine LinearMap.ext_on_range hb fun i => LinearMap.ext_on_range hb fun j => ?_
  simpa using h3 i j

theorem idlAlong_ne_bot {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) (h : (jK R ≫ ξ) (closedPoint (FractionRing R)) ∉ J.support) : idlAlong J ξ ≠ ⊥ := by
  intro h0
  have h1 := idlAlong_eq_top_of_notMem_support X J _ _ h
  have hmap : ∀ {S : Type} [CommRing S] [IsLocalRing S] (χ : Sp S ⟶ X)
      (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1),
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of S)).hom).hom := by
    intro S _ _ χ U hle
    have hx : χ (closedPoint S) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have h2 : idlAlong J (jK R ≫ ξ) = (idlAlong J ξ).map (algebraMap R (FractionRing R)) := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
    have hle' : ⊤ ≤ (jK R ≫ ξ) ⁻¹ᵁ U := fun x _ => hle (show jK R x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [hmap ξ ⟨U, hU⟩ hle, hmap _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (jK R ≫ ξ).appLE U ⊤ hle' = ξ.appLE U ⊤ hle ≫ (jK R).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  rw [h0, Ideal.map_bot] at h2
  exact bot_ne_top (h2.symm.trans h1)

theorem isCpl_props {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] [IsLocalRing R]
    {j : O →+* R} (hj : GlobalTheory.Poinc.Eq8.IsCpl j) : Function.Injective j ∧ IsLocalHom j ∧
      ∀ (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ φ : O →+* V, IsLocalHom φ →
        ∃ ψ : R →+* V, IsLocalHom ψ ∧ ψ.comp j = φ := by
  obtain ⟨e, he⟩ := hj
  have hj : j = e.toRingHom.comp (algebraMap O _) := RingHom.ext fun a => (he a).symm
  have hl : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)) := inferInstance
  refine ⟨?_, ?_, fun V _ _ hV φ hφ => ?_⟩
  · rw [hj]
    exact e.injective.comp (AdicCompletion.of_injective (maximalIdeal O) O)
  · refine ⟨fun a ha => ?_⟩
    rw [← he, MulEquiv.isUnit_map] at ha
    exact isUnit_of_map_unit _ _ ha
  · obtain ⟨ψ, h1, h2⟩ := GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend O V hV φ hφ
    refine ⟨ψ.comp e.symm.toRingHom, ⟨fun a ha => ?_⟩, RingHom.ext fun a => ?_⟩
    · have := isUnit_of_map_unit ψ _ ha
      exact (MulEquiv.isUnit_map e.symm).1 this
    · rw [← h2, RingHom.comp_apply, ← he]
      simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem finite_lat (T : UTrait Xo c) : Module.Finite (𝓞 E) T.P.D.toPre.X :=
  Module.Finite.of_restrictScalars_finite ℤ _ _

theorem projective_lat (T : UTrait Xo c) : Module.Projective (𝓞 E) T.P.D.toPre.X := by
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := finite_lat T
  have : Module.Flat (𝓞 E) T.P.D.toPre.X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨a, hx⟩
    by_contra hx0
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (a : 𝓞 E)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero (nonZeroDivisors.coe_ne_zero a))
    have h : n • x = 0 := by
      have hx' : (a : 𝓞 E) • x = 0 := hx
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hx', smul_zero]
    exact hx0 ((smul_eq_zero.1 h).resolve_left hn)
  have : Module.FinitePresentation (𝓞 E) T.P.D.toPre.X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem be_nonneg (T : UTrait Xo c) (x : T.P.D.toPre.X) : 0 ≤ T.be x x := by
  by_cases hx : x = 0
  · subst hx; simp
  · obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
    fin_cases j
    simpa using hj.le

theorem be_bal (T : UTrait Xo c) : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X := by
  rw [balForms_eq_levelForms]; exact T.lev

theorem evalZ_prop {φ : InvFun (𝓞 E)} (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (T T' : UTrait Xo c)
    (e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X) (m s : ℕ) (he : ∀ a b, (m : ℤ) * T'.be (e a) (e b) = s * T.be a b) :
    (m : ℝ) * φ.evalZ T'.be = s * φ.evalZ T.be := by
  haveI := finite_lat T
  haveI := projective_lat T
  haveI := finite_lat T'
  have hon := hφ T.P.D.toPre.X (_root_.GlobalTheory.UPoinc.UTrait.finrank_le_min E H Dw l Xo c T)
  have hc := toReal_mem_psdCone_of_nonneg E H _ T.be (be_bal T) (be_nonneg T)
  have hc' := toReal_mem_psdCone_of_nonneg E H _ (pull e.toLinearMap T'.be) (pull_mem _ (be_bal T'))
    (fun x => be_nonneg T' (e x))
  rw [← evalR_toReal φ T.be, ← hon.homog _ hc s s.cast_nonneg,
    ← evalZ_pull φ (r := e.toLinearMap) e.surjective, ← evalR_toReal, ← hon.homog _ hc' m m.cast_nonneg]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h

end GlobalTheory.UPoinc.AllTraits


open GlobalTheory.UPoinc.AllTraits in
theorem GlobalTheory.UPoinc.AllTraits.orders_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (ι : ℕ) (D : GlobalTheory.EffCartierData Y.Z), (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hEE hHom ι D hD hgen
  intro W _ _ _ hW ϖ hϖ χ y hy _ t tK h1 h2 P be hbe hmono
  let T₀ : UTrait Xo c :=
    { V := W, cdvr := hW, ϖ := ϖ, irr := hϖ, y := y, t := t, gen := ⟨tK, h1, h2⟩, P := P, be := be, lev := hbe, mono := hmono }
  haveI : IsDiscreteValuationRing W := hW.1
  haveI : IsDedekindDomain X₁.o₁ := ArithBase.ded X₁.Ω₁
  haveI := Y.lft
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have hWc : IsAdicComplete (maximalIdeal W) W := hW.2.1
  obtain ⟨R, _, _, _, j, Λ, _, _, p, c₀, hRn, hRc, hj, hc, hper⟩ :=
    localPeriods E H Dw hpq l Xo c C X₁ Y U₀ EE out πY hAdm hEE hHom (χ (closedPoint W))
  obtain ⟨jinj, jloc, jext⟩ := isCpl_props hj
  obtain ⟨ψ, ψloc, hψ⟩ := jext W hWc (Scheme.stalkClosedPointTo χ).hom inferInstance
  have hξ : spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk (χ (closedPoint W)) = χ := by
    rw [hψ]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ
  obtain ⟨d, hd⟩ : ∃ d, FinalTheorems.stalkId D.idealSheaf (χ (closedPoint W)) = Ideal.span {d} := by
    obtain ⟨i, hi⟩ := D.exists_mem (χ (closedPoint W))
    exact ⟨_, D.stalkId_idealSheaf i _ hi⟩
  have hid : idlAlong D.idealSheaf χ = Ideal.span {ψ (j d)} := by
    rw [idlAlong, hd, Ideal.map_span, Set.image_singleton, ← hψ]
    rfl
  have hnot : (jK W ≫ χ) (closedPoint (FractionRing W)) ∉ D.idealSheaf.support := by
    intro hs
    refine hD _ hs ⟨y (closedPoint (FractionRing W)), ?_⟩
    exact congrArg (fun f => f.base (closedPoint (FractionRing W))) hy
  have hne := idlAlong_ne_bot D.idealSheaf χ hnot
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  refine ⟨a, ?_, ha⟩
  have hda : Associated (ψ (j d)) (ϖ ^ a) := Ideal.span_singleton_eq_span_singleton.1 (hid.symm.trans ha)
  obtain ⟨e, he⟩ := hper T₀ ψ ψloc (by rw [hξ]; exact hy)
  choose k hk hk' using he
  haveI := T₀.P.D.toPre.finX
  obtain ⟨N, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := T₀.P.D.toPre.X)
  obtain ⟨A, _, _, _, ϖ', ψ', m, m', k', hA, hϖ', ψ'inj, ψ'loc, hm, hm', hk''⟩ :=
    GlobalTheory.PropDvr.exists_cdvr_proportional R W ϖ hϖ ψ ψloc (Option (Fin N × Fin N))
      (fun i => i.elim (j d) fun ii => p (e.symm (b ii.1 + b ii.2)))
      (fun i => i.elim a fun ii => k (e.symm (b ii.1 + b ii.2)))
      (by rintro (_ | ii); exacts [hda, hk' _])
  haveI : CharZero A := (RingHom.charZero_iff ψ'inj).1 hRc
  haveI := jloc
  haveI := ψ'loc
  obtain ⟨T', f, finj, floc, hthru, hyC⟩ := traitThroughOpen E H Dw hpq l Xo c C X₁ Y U₀ EE out πY hAdm hEE hHom
    (χ (closedPoint W)) A hA (ψ'.comp j) (ψ'inj.comp jinj) inferInstance
  haveI := floc
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  obtain ⟨e', he'⟩ := hper T' (f.comp ψ') inferInstance (by rw [RingHom.comp_assoc]; exact hyC)
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    ((map_ne_zero_iff f finj).2 hϖ'.ne_zero) T'.irr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr
    exact hϖ'.not_isUnit ((isUnit_map_iff f ϖ').1 (associated_one_iff_isUnit.1 hr))
  have hpow : ∀ {x : A} {n : ℕ}, Associated x (ϖ' ^ n) → Associated (f x) (T'.ϖ ^ (r * n)) := by
    intro x n h
    have h1 := h.map f
    rw [map_pow] at h1
    rw [pow_mul]
    exact h1.trans hr.pow_pow
  obtain ⟨a', ha', hid'⟩ := hgen T' _ hthru
  rw [GlobalTheory.TraitStalk.idlAlong_spMap_fromSpecStalk _ _ _ _ _ inferInstance, hd, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hid'
  have h0 := hk'' none
  have ea : a' = r * k' none := pow_exp_eq T'.irr (hid'.symm.trans (hpow h0.1))
  have h02 : m * k' none = m' * a := h0.2
  let Eq' := e.symm.trans e'
  have hz := form_eq_zero ((m : ℤ) • pull Eq'.toLinearMap T'.be - ((m' * r : ℕ) : ℤ) • T₀.be)
    (fun x z => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, pull_apply]
      rw [T₀.lev.1 x z, T'.lev.1]) b hb (fun i i' => by
      obtain ⟨n, hl, hl'⟩ := he' (e.symm (b i + b i'))
      obtain ⟨h1, h2⟩ := hk'' (some (i, i'))
      have h3 : n = r * k' (some (i, i')) := pow_exp_eq T'.irr (hl'.symm.trans (hpow h1))
      have h4 := hk (e.symm (b i + b i'))
      rw [e.apply_symm_apply] at h4
      have h5 : (m : ℤ) * k' (some (i, i')) = m' * k (e.symm (b i + b i')) := by exact_mod_cast h2
      have hc0 : (c₀ : ℤ) ≠ 0 := by omega
      change (m : ℤ) * T'.be (e' (e.symm (b i + b i'))) (e' (e.symm (b i + b i'))) -
        ((m' * r : ℕ) : ℤ) * T₀.be (b i + b i') (b i + b i') = 0
      refine mul_left_cancel₀ hc0 ?_
      rw [h3] at hl
      push_cast at hl ⊢
      linear_combination (-(m : ℤ)) * hl + r * h5 + m' * r * h4)
  have hev : (m : ℝ) * φ.evalZ T'.be = ((m' * r : ℕ) : ℝ) * φ.evalZ be := evalZ_prop hφ T₀ T' Eq' m (m' * r) fun x z =>
    sub_eq_zero.1 (congrArg (fun B : LinearMap.BilinForm ℤ T₀.P.D.toPre.X => B x z) hz)
  have h02' : (m : ℝ) * k' none = m' * a := by exact_mod_cast h02
  have hmr : ((m' : ℝ) * r) ≠ 0 := by
    have : m' ≠ 0 := by omega
    positivity
  refine mul_left_cancel₀ hmr ?_
  rw [ea] at ha'
  push_cast at ha' hev
  linear_combination (-(r : ℝ)) * h02' + m * ha' + ι * hev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsolutelyIntegrallyClose
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.HInvAic

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

theorem eqv_spMap_equiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) :
    Eqv R (spMap (e : A →+* B)) F := by
  intro n
  have h1 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id B; ext x; simp
  have h2 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id A; ext x; simp
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h2, pull_id]
  · rw [← pull_comp, h1, pull_id]

end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem alg (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O] :
    AIC T → SH O → IndEt T O → IsDomain O ∧ AIC O := by
  intro hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  obtain ⟨-, hac⟩ := (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT
  haveI : IsIntegrallyClosed T := ((GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT).1
  refine GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local T O hInd ?_
  intro E _ _ _ P _
  obtain ⟨hd, hc⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale T P (Localization.AtPrime P)
  exact ⟨hd, (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed _).2 ⟨hc, GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' T E P hac⟩⟩
end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem tensor_map_eq (T O : Type) [CommRing T] [CommRing O] [Algebra T O] :
    (Algebra.TensorProduct.map (AlgHom.id T O) (Algebra.ofId T (Polynomial T))).toRingHom =
      (((polyEquivTensor T O).toRingEquiv : Polynomial O →+* O ⊗[T] Polynomial T).comp Polynomial.C).comp
        ((Algebra.TensorProduct.rid T T O).toRingEquiv : O ⊗[T] T →+* O) := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o t =>
    simp only [RingHom.comp_apply, AlgEquiv.coe_toRingEquiv, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Algebra.TensorProduct.rid_tmul, polyEquivTensor_apply, Polynomial.eval₂_C]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.ofId_apply, Polynomial.algebraMap_eq]
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Polynomial.algebraMap_eq]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  intro q _ T _ _ hT hq i
  have hφ : ((Algebra.ofId T (Polynomial T)).toRingHom : T →+* Polynomial T) = Polynomial.C := by
    ext x <;> simp [Algebra.ofId_apply]
  rw [← hφ]
  apply GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) T T (Polynomial T) (Algebra.ofId T (Polynomial T))

  intro O _ _ hSH hInd
  obtain ⟨hdom, haic⟩ := alg T O hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  have hC := GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain q O haic hqO i
  rw [tensor_map_eq, spMap_comp, spMap_comp]
  exact eqv_comp _ _ _ (eqv_comp _ _ _ (eqv_spMap_equiv _ _) hC) (eqv_spMap_equiv _ _)

end GlobalTheory.HInvAic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commutatorPairing_value_heckePoints : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∃ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u := by
  first | (exact @GlobalTheory.HeckeWeilLift.exists_weilIs_hecke) | (exact GlobalTheory.HeckeWeilLift.exists_weilIs_hecke) | (intros; apply GlobalTheory.HeckeWeilLift.exists_weilIs_hecke <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateHeatOperatorPeriodShift
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatDefect

theorem exists_gauge_translate : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])), e.IsGen → ∀ (k : ℕ) (τ : SecM Y.q.left Q.P.L k), ∃ ρ : SecM Y.q.left Q.P.L k, (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) := by
  intro R _ _ Q O _ _ _ oa Y x e he k τ
  obtain ⟨ρ, hρ⟩ := exists_sec (L := Q.P.L) Q.P.isLB
    (φ' := fun _ : Fin 1 => Y.q.left) (ε' := fun _ => (k : ℤ))
    (by
      intro U _ g
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [zpow_mul, zpow_mul, zpow_one, zpow_neg_one, _root_.mul_comm]
      exact inv_mul_cancel_right _ _)
    (pullMulSec τ (𝟙 Y.H * (toUnit Y.H ≫ x)).left (GeneratorPullback.powGen Q.P.L _ _ e k) (ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen _ _ _ e he k))
  refine ⟨ρ, fun Z r z J hJ => ?_⟩
  rw [hρ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ]
  congr 1
  exact congrArg Units.val (map_pow _ _ _)

theorem exists_conj_shift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∀ mu : Dd.toPre.X, ∃ (h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X →+ R) (π π' : R), IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) (σ₁ σ₁' : Dd.toPre.SecB k (α + k • mu)), 1 ≤ k → ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → TActs Y h k (α + k • mu) σ₁ σ₁' → ∃ σ'' : Dd.toPre.SecB k α, TActs Y h' k α σ σ'' ∧ ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hm ht D hD h hb mu
  obtain ⟨x, e, β, w, π, π', he, hwe, hTR⟩ := GlobalTheory.T.thetaShift_fourierTerm_translation_gauge R Dd O oa Y m t gam hm ht D hD mu
  obtain ⟨h', hb', hΘ, hu, hint⟩ :=
    GlobalTheory.T.heatOperator_conj_translation_gauge R Dd.toPre O oa Y n (fun a => v a) dd hv D h hb x e β he hwe
  refine ⟨h', w, π, π', hb', hΘ, hu, ?_⟩
  intro k α σ σ₁ σ₁' hk hs hA
  obtain ⟨τ₁, τ₁', hτ₁, hτ₁', hA₁⟩ := hA
  obtain ⟨σ'', τ, τ'', hτ, hτ'', hA'⟩ := _root_.GlobalTheory.Heat.heat_acts_on_terms R Dd O oa Y n v dd hv D h' hb' k α σ
  obtain ⟨ρ, hρ⟩ := exists_gauge_translate Y x e he k τ₁
  obtain ⟨ρ', hρ'⟩ := exists_gauge_translate Y x e he k τ₁'
  have hAρ := hint k τ₁ τ₁' ρ ρ' hρ hρ' hA₁
  obtain ⟨a, b, -, hab⟩ := hTR k α hk
  obtain ⟨h1, h2⟩ := hab σ σ₁ τ τ₁ ρ hs hτ hτ₁ hρ
  exact ⟨σ'', ⟨τ, τ'', hτ, hτ'', hA'⟩, h2 σ'' σ₁' τ'' τ₁' ρ' hτ'' hτ₁' hρ'
    (_root_.GlobalTheory.Heat.Heat.acts_const_at_points Y.H Y.q.left Dd.toPre.P.L Dd.toPre.P.isLB (fun a => v a) dd hv D h' k a b ρ τ ρ' τ'' h1 hAρ hA')⟩

end GlobalTheory.HeatDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNatMulFiniteAdeleAwayPIntegralStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral : ∀ (p : ℕ) [Fact p.Prime] (a : AfP p), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ IsIntAf ((j : AfP p) * a) := by
  first | (exact @GlobalTheory.DenAway.exists_coprime_nat_adele) | (exact GlobalTheory.DenAway.exists_coprime_nat_adele) | (intros; apply GlobalTheory.DenAway.exists_coprime_nat_adele  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletioStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ ∀ v ∈ LaHat D, j • A v ∈ LaHat D := by
  first | (exact @GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem) | (exact GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem) | (intros; apply GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointLiftZeroFirstCoordinateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPoint_lift_zero_first_coordinate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g)), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivBy L Q oQ iw s ε e g hD → ∀ a : D'.La, ∃ p : QkPt Q (FractionRing V) l.M', IsLevPt L iw hD a p := by
  first | exact @GlobalTheory.UCanon.exists_levPt | exact GlobalTheory.UCanon.exists_levPt | (intros; apply GlobalTheory.UCanon.exists_levPt <;> assumption)
end

