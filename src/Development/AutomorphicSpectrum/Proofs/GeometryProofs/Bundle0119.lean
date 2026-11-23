module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.UnitAtOfIsLineGenOn
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineGeneratorGeometric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstRatio

theorem ratio_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : Cpt ξ}
    {W : Type} [AddCommGroup W] [Module Ω W] {e : W} {s t : Ω} (he : e ≠ 0) (hs : s ≠ 0)
    (hst : Submodule.span (regAt ξ x) {s • e} = Submodule.span (regAt ξ x) {t • e}) : t / s ∈ regAt ξ x := by
  have : t • e ∈ Submodule.span (regAt ξ x) {s • e} := hst ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp this
  have hr' : ((r : Ω) * s) • e = t • e := by rw [mul_smul]; exact hr
  have := smul_left_injective Ω he hr'
  rw [← this, mul_div_cancel_right₀ _ hs]; exact r.2

theorem exists_smul_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : Cpt ξ}
    {W : Type} [AddCommGroup W] [Module Ω W] {a a' : W} {α α' : Ω} (hα' : α' ≠ 0)
    (h : Submodule.span (regAt ξ x) {α • a} = Submodule.span (regAt ξ x) {α' • a'}) : ∃ f : Ω, a' = f • a := by
  have : α' • a' ∈ Submodule.span (regAt ξ x) {α • a} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp this
  have hr' : ((r : Ω) * α) • a = α' • a' := by rw [mul_smul]; exact hr
  refine ⟨α'⁻¹ * ((r : Ω) * α), ?_⟩
  rw [mul_smul, hr', smul_smul, inv_mul_cancel₀ hα', one_smul]

theorem unit_of_coeff {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {A B : Lat ξ V} {p q : ℕ} {a : ⋀[Ω]^p V} {b : ⋀[Ω]^q V} {s t : Ω}
    {x : Cpt ξ} (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (h : IsCoeffAt A B p q a b x 1)
    (h' : IsCoeffAt A B p q (s • a) (t • b) x 1) : unitAt ξ x (s / t) := by
  obtain ⟨α, β, hα, -, hA, hB, e⟩ := h
  obtain ⟨α', β', hα', -, hA', hB', e'⟩ := h'
  rw [_root_.one_mul] at e e'
  subst e e'
  rw [smul_smul] at hA' hB'
  have k1 := ratio_mem ha hα (hA.symm.trans hA')
  have k2 := ratio_mem ha (mul_ne_zero hα' hs) (hA'.symm.trans hA)
  have k3 := ratio_mem hb hα (hB.symm.trans hB')
  have k4 := ratio_mem hb (mul_ne_zero hα' ht) (hB'.symm.trans hB)
  refine ⟨div_ne_zero hs ht, ?_, ?_⟩
  · have := mul_mem k1 k4
    convert this using 1; field_simp
  · have := mul_mem k2 k3
    convert this using 1; field_simp

theorem exists_factors {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V}
    {T : Set (Cpt ξ)} (hT : T.Nonempty) (h : IsLineGenOn A B p q a b T) (h' : IsLineGenOn A B p q a' b' T) :
    ∃ s t : Ω, s ≠ 0 ∧ t ≠ 0 ∧ a' = s • a ∧ b' = t • b ∧ ∀ x ∈ T, unitAt ξ x (s / t) := by
  obtain ⟨ha, hb, h⟩ := h
  obtain ⟨ha', hb', h'⟩ := h'
  obtain ⟨x₀, hx₀⟩ := hT
  obtain ⟨s, hs⟩ : ∃ s : Ω, a' = s • a := by
    obtain ⟨α, β, -, -, hA, -, -⟩ := h x₀ hx₀
    obtain ⟨α', β', hα', -, hA', -, -⟩ := h' x₀ hx₀
    exact exists_smul_eq hα' (hA.symm.trans hA')
  obtain ⟨t, ht⟩ : ∃ t : Ω, b' = t • b := by
    obtain ⟨α, β, -, -, -, hB, -⟩ := h x₀ hx₀
    obtain ⟨α', β', -, hβ', -, hB', -⟩ := h' x₀ hx₀
    exact exists_smul_eq hβ' (hB.symm.trans hB')
  have hs0 : s ≠ 0 := by rintro rfl; exact ha' (by rw [hs, zero_smul])
  have ht0 : t ≠ 0 := by rintro rfl; exact hb' (by rw [ht, zero_smul])
  refine ⟨s, t, hs0, ht0, hs, ht, fun x hx => ?_⟩
  have := h' x hx
  rw [hs, ht] at this
  exact unit_of_coeff ha hb hs0 ht0 (h x hx) this

theorem isProper_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

theorem const_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (a a' : ⋀[Z.Ω]^D.p Z.V) (b b' : ⋀[Z.Ω]^D.q Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → Z.IsGeom → IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib → IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a' b' Z.genFib → ∃ (x : c.F) (s t : Z.Ω), x ≠ 0 ∧ t ≠ 0 ∧ s = Z.inc x * t ∧ a' = s • a ∧ b' = t • b := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ a a' b b' ⟨hβ, hN, hfrac⟩ hG h h'
  haveI : IsDomain O := hβ.isDomain β
  letI : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  have halg : ∀ o : O, algebraMap O Z.Ω o = Z.inc (β o) := fun _ => rfl
  have hover : (Z.ξ₀ ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom (algebraMap O Z.Ω)) := by
    have e : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap Z.inc ≫ spMap β := by
      rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
        ← Category.assoc, Z.over_inc]
    rw [e, spMap, spMap, ← Spec.map_comp]
    rfl
  have hinj : Function.Injective (algebraMap O Z.Ω) := Z.inc.injective.comp hβ
  have hcc : ConstClosed O Z.Ω := by
    rintro w ⟨f, hf0, hf⟩
    obtain ⟨x, rfl⟩ := hG w ⟨f.map β, (Polynomial.map_ne_zero_iff hβ).2 hf0, by
      rw [Polynomial.eval₂_map]; exact hf⟩
    obtain ⟨u, v, hv, e⟩ := hfrac x
    refine ⟨u, v, fun h0 => hv (by rw [h0, map_zero]), ?_⟩
    rw [halg, halg, ← map_mul, e]
  have hsub : genFibre O (Z.ξ₀ ≫ Y.j) ⊆ Z.genFib := by
    intro p hp
    have hbot : (Y.s p.1).asIdeal = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun o ho => ?_
      by_contra h0
      exact ((ConstReg.regular_const _ _ _ O Y.s hover p o).2 Z.gen).1 (hp o h0) ho
    obtain ⟨w⟩ : Nonempty (Sp c.F) := inferInstance
    have e : Y.s p.1 = spMap β w := by
      refine PrimeSpectrum.ext ?_
      rw [hbot]
      refine ((Submodule.eq_bot_iff _).2 fun o ho => ?_).symm
      have h1 : β o ∈ w.asIdeal := ho
      by_contra h0
      have h2 : β o ≠ 0 := fun e0 => h0 (hβ (by rw [e0, map_zero]))
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (isUnit_iff_ne_zero.2 h2))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    exact ⟨z, hz⟩
  have hne : Z.genFib.Nonempty := ⟨⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩, ⟨Y.jQ (genPt Z.ξ₀), rfl⟩⟩
  obtain ⟨s, t, hs, ht, rfl, rfl, hu⟩ := exists_factors hne h h'
  haveI : IsProper Y.s := isProper_of_proj Y.proj
  let L : Lat (Z.ξ₀ ≫ Y.j) Z.Ω := fun p => Submodule.span (regAt (Z.ξ₀ ≫ Y.j) p) {1}
  obtain ⟨x', y', hy', e⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.Flat.mem_lat_genFibre_iff_const_mul Y.X Z.Ω (Z.ξ₀ ≫ Y.j) O Y.s hover hinj Z.gen hcc L 1
    (fun p _ => ⟨one_ne_zero, rfl⟩) (s / t)).1 (fun p hp =>
      Submodule.mem_span_singleton.2 ⟨⟨s / t, (hu p (hsub hp)).2.1⟩, by
        show (s / t) * 1 = _
        rw [_root_.mul_one]⟩)
  have hy : β y' ≠ 0 := fun h0 => hy' (hβ (by rw [h0, map_zero]))
  rw [_root_.mul_one, halg, halg] at e
  have hx' : β x' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at e
    exact (mul_ne_zero (div_ne_zero hs ht) (by simpa using hy)) e
  refine ⟨β x' / β y', s, t, div_ne_zero hx' hy, ht, ?_, rfl, rfl⟩
  have hyΩ : Z.inc (β y') ≠ 0 := by simpa using hy
  rw [map_div₀, ← e]
  field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.ConstRatio
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

open GlobalTheory.HolHom

variable {R : Type} [CommRing R]

def cst {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem valR_cst {C : Type} [CommRing C] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (θ : R →+* C)
    (y : Sp C ⟶ X) (hy : y ≫ p = spMap θ) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : R) : evalHom y U h (cst p U a) = θ a := by
  have e := GlobalTheory.TangentOrigin.evalPt_constFn p y U h a
  have e2 := GlobalTheory.TangentOrigin.evalPt_spMap θ a
  rw [hy] at e
  exact e.trans e2

theorem exists_pt {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) (θ : R →+* ℂ)
    (χ : Γ(G.left, V) →+* ℂ) (hχ : ∀ r, χ (cst G.hom V r) = θ r) :
    ∃ x : Over.mk (spMap θ) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = χ a := by
  obtain ⟨y, hy, he⟩ := GlobalTheory.TangentOrigin.exists_evalPt_eq hV χ
  have hy' : y ≫ G.hom = spMap θ := GlobalTheory.TangentOrigin.eq_spMap_of_evalPt _ θ (fun a => by
    rw [← GlobalTheory.TangentOrigin.evalPt_constFn G.hom y V hy a, he]; exact hχ a)
  refine ⟨Over.homMk y hy', hy, fun a => ?_⟩
  show valAt' y V a = χ a
  rw [GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hy, he]

theorem val_cst {G : Over (Sp R)} (V : G.left.Opens) {θ : R →+* ℂ} (x : Over.mk (spMap θ) ⟶ G)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (r : R) : valAt' x.left V (cst G.hom V r) = θ r :=
  (GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hx _).trans (valR_cst G.hom V θ x.left (Over.w x) hx r)

theorem pt_ext {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) {θ : R →+* ℂ}
    {x y : Over.mk (spMap θ) ⟶ G} (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V)
    (h : ∀ a, valAt' x.left V a = valAt' y.left V a) : x = y :=
  Over.OverMorphism.ext (point_ext hV hx hy h)

theorem tan_der {X : Scheme.{0}} {x : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) {V : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ D : Γ(X, V) →+ ℂ, (∀ f, D f = TrivSqZeroExt.snd (valR v V f)) ∧
      ∀ f f', D (f * f') = valAt' x V f * D f' + valAt' x V f' * D f := by
  have hv := (le_preimage_dual_iff h V).2 hx
  refine ⟨AddMonoidHom.mk' (fun f => TrivSqZeroExt.snd (valR v V f)) fun a b => ?_, fun _ => rfl, fun f f' => ?_⟩
  · simp only [valR_eq _ _ hv, map_add (f := _), TrivSqZeroExt.snd_add]
  · have e1 := fst_valR h hx f
    have e2 := fst_valR h hx f'
    simp only [AddMonoidHom.mk'_apply]
    rw [← e1, ← e2]
    simp only [valR_eq _ _ hv, map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

theorem one_left_spMap {G : Over (Sp R)} [GrpObj G] (θ : R →+* ℂ) :
    (1 : Over.mk (spMap θ) ⟶ G).left = spMap θ ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left := by
  have e : (Over.homMk (spMap θ) (by simp) : Over.mk (spMap θ) ⟶ Over.mk (𝟙 (Sp R))) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  exact (congrArg (fun q => Over.Hom.left q) e).symm

theorem tan_base {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap θ) ≫ (M.pt w).left) =
      (1 : Over.mk (spMap θ) ⟶ G).left := by
  rw [one_left_spMap, ← M.tan w, ← Category.assoc, ← Category.assoc]
  congr 1
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  show TrivSqZeroExt.fst (dualMap θ x) = θ (TrivSqZeroExt.fst x)
  simp [dualMap]

theorem tan_over {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    (spMap (dualMap θ) ≫ (M.pt w).left) ≫ G.hom = spMap ((algebraMap ℂ (DualNumber ℂ)).comp θ) := by
  have e : (M.pt w).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) := Over.w (M.pt w)
  rw [Category.assoc, e, Category.comp_id]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairFramesOnSet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator

theorem exists_ιMulti_eq_smul {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {v b : Fin r → E} (h : ∀ i, v i ∈ Submodule.span Ω (Set.range b)) :
    ∃ α : Ω, exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  classical
  have hc : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • b j = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (h i)
  choose c hc using hc
  have hv : v = fun i => ∑ j, c i j • b j := funext fun i => (hc i).symm
  have hsum : exteriorPower.ιMulti Ω r v =
      ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
    rw [hv]
    refine ((exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
      (fun i j => c i j • b j)).trans (Finset.sum_congr rfl fun f _ => ?_)
    exact (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
      (fun i => c i (f i)) (fun i => b (f i))
  have hmem : exteriorPower.ιMulti Ω r v ∈ Submodule.span Ω {exteriorPower.ιMulti Ω r b} := by
    rw [hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ]
      have hm := Submodule.mem_span_singleton_self (R := Ω) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨α, hα.symm⟩

theorem frame_mem_of_isVBOn {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hv : L.IsFrameAt v x) (i : Fin r) : v i ∈ V := by
  obtain ⟨U, hU, e, he, hfr⟩ := hL x hx
  have h1 : v i ∈ L x := hv.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  rw [(hfr x hx hU).2] at h1
  have h2 : Submodule.span (regAt ξ x) (Set.range e) ≤
      (Submodule.span Ω (Set.range e)).restrictScalars (regAt ξ x) :=
    Submodule.span_le.2 fun _ hy => Submodule.subset_span hy
  exact he ▸ h2 h1

theorem exists_wedge_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v b : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hb : Submodule.span Ω (Set.range b) = V) (hv : L.IsFrameAt v x) :
    ∃ α : Ω, α ≠ 0 ∧ exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  obtain ⟨α, hα⟩ := exists_ιMulti_eq_smul (v := v) (b := b)
    fun i => hb ▸ frame_mem_of_isVBOn hx hL hv i
  refine ⟨α, ?_, hα⟩
  rintro rfl
  exact GenModel.ιMulti_ne_zero hv.1 (by rw [hα, zero_smul])

theorem isGenAt_div : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (Vp Vq : Submodule Ω V) (T : Set (Cpt ξ)) (b₁ v₁ : Fin p → V) (b₂ v₂ : Fin q → V) (x : Cpt ξ), x ∈ T → A.IsVBOn T p Vp → B.IsVBOn T q Vq → LinearIndependent Ω b₁ → Submodule.span Ω (Set.range b₁) = Vp → LinearIndependent Ω b₂ → Submodule.span Ω (Set.range b₂) = Vq → A.IsFrameAt v₁ x → B.IsFrameAt v₂ x → ∃ α κ : Ω, α ≠ 0 ∧ κ ≠ 0 ∧ exteriorPower.ιMulti Ω p v₁ = α • exteriorPower.ιMulti Ω p b₁ ∧ exteriorPower.ιMulti Ω q v₂ = κ • exteriorPower.ιMulti Ω q b₂ ∧ (lineLat A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂)).IsGenAt x (α / κ) := by
  intro X Ω _ ξ V _ _ A B p q Vp Vq T b₁ v₁ b₂ v₂ x hx hA hB hb₁ hs₁ hb₂ hs₂ hv₁ hv₂
  obtain ⟨α, hα, e₁⟩ := exists_wedge_coeff hx hA hs₁ hv₁
  obtain ⟨κ, hκ, e₂⟩ := exists_wedge_coeff hx hB hs₂ hv₂
  have hco : IsCoeffAt A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂) x (κ / α) :=
    ⟨α, κ, hα, hκ, by rw [GenModel.wedge_of_frame hv₁, e₁], by rw [GenModel.wedge_of_frame hv₂, e₂],
      div_mul_cancel₀ _ hα⟩
  have key := _root_.GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isVBOn_gen_frames X Ω ξ V A B p q Vp Vq T _ _ hA hB (GenModel.ιMulti_ne_zero hb₁)
    (GenModel.ιMulti_ne_zero hb₂) ⟨x, hx, _, hco⟩
  exact ⟨α, κ, hα, hκ, e₁, e₂, key.2.2 x hx v₁ v₂ α κ hv₁ hv₂ e₁ e₂⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.EigDir

open GlobalTheory.HolHom GlobalTheory.DerivEig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σK : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem isComb_iff_isCombAt (x : Sp ℂ ⟶ Xo.X) {n : ℕ} (c : Fin n → ℂ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (w : epsAt x ⟶ Xo.univ.t.G) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ Formalism.L2.Pj.IsCombAt x (fun i => (v i).left) c w.left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, by rw [hw]⟩
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, Over.OverMorphism.ext hw.symm⟩

theorem isTanAt_of_isEigVec (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (v : epsAt x ⟶ Xo.univ.t.G)
    (h : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act x χ v) : Formalism.L2.Pj.IsTanAt x v.left :=
  ⟨Over.w v, h.1⟩

theorem isEigVec_of_isDerivAt0 (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (FU.Di i) ty P) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (hχ : ∀ a : 𝓞 E, χ a = τ (a : E))
    (w : Fin g → ℂ) (hw : ∀ k, w k ≠ 0 → ty k = τ) (v : epsAt (FU.u i P) ⟶ Xo.univ.t.G)
    (hv : IsDerivAt0 (fun z => (FU.ex i P z).left) w v.left) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ v := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have hhol : HolAt (fun z => (FU.ex i P z).left) 0 := holAt_of_isHolTo (isHolTo_ex FU i hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  refine ⟨(h1 _ _ hv).2, fun a => ?_⟩
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
    ContinuousLinearMap.pi fun k => ty k (a : E) • ContinuousLinearMap.proj k
  have e1 := hv'.comp (Xo.univ.t.act.act a).left
  have e2 : (fun t => (FU.ex i P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (FU.ex i P (L t)).left := by
    funext t
    rw [← Over.comp_left, ← FU.ex_lin i P hP a t]
    rfl
  rw [e2] at e1
  have e3 := isDerivAt_of_comp_linear hhol L e1
  have e4 : L w = χ a • w := by
    funext k
    by_cases hk : w k = 0
    · simp [L, hk]
    · simp [L, hw k hk, hχ a]
  rw [e4] at e3
  exact e3.unique (isDerivAt_epsMul hv' _)

end GlobalTheory.CompanionTheory.Ar.Flat.EigDir


open GlobalTheory.CompanionTheory.Ar.Flat.EigDir in
theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σK : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (n : ℕ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)), IsPeriod (FU.Di i) ty P → x = FU.u i P → (∀ a : 𝓞 E, χ a = τ (a : E)) → IsEigFrame Xo.univ.t.act x χ v → ∃ V : Fin n → Fin g → ℂ, (∀ a u, IsDerivAt0 (fun z => (FU.ex i P z).left) u (v a).left ↔ u = V a) ∧ LinearIndependent ℂ V ∧ ∀ z, tyPart ty τ z ∈ Submodule.span ℂ (Set.range V) := by
  intro E _ _ _ H D l Xo σK g ty FU i P x χ τ n v hP hx hχ hF
  subst hx
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have ht : ∀ a, Formalism.L2.Pj.IsTanAt (FU.u i P) (v a).left := fun a => isTanAt_of_isEigVec _ χ _ (hF.1 a)
  choose V hV hVu using fun a => h3 _ (ht a)
  have comb : ∀ (c : Fin n → ℂ) (w : epsAt (FU.u i P) ⟶ Xo.univ.t.G),
      GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ IsDerivAt0 (fun z => (FU.ex i P z).left) (∑ k, c k • V k) w.left := fun c w =>
    (isComb_iff_isCombAt _ c v w).trans
      (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H D l Xo σK g ty FU i P hP n (fun k => (v k).left) V hV c w.left)
  refine ⟨V, fun a u => ⟨fun h => hVu a u h, fun h => h ▸ hV a⟩, ?_, fun z => ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 0
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ 0 (fun k hk => absurd rfl hk) w hw
    obtain ⟨c₀, -, hu⟩ := hF.2 w hw'
    have a1 := hu c ((comb c w).2 (by rw [hc]; exact hw))
    have a2 := hu 0 ((comb 0 w).2 (by simpa using hw))
    intro k
    exact congrFun (a1.trans a2.symm) k
  · obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 (tyPart ty τ z)
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ _ (fun k hk => ?_) w hw
    · obtain ⟨c, hc, -⟩ := hF.2 w hw'
      have e := (h3 _ (isTanAt_of_isEigVec _ χ _ hw')).unique ((comb c w).1 hc) hw
      rw [← e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · by_contra hne
      exact hk (by simp [tyPart, hne])
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointCoordsExist
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.TupleCoords

private theorem valR_eq_valMap {A : Type} [CommRing A] {X : Scheme} (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ (TopologicalSpace.Opens.map x.base).obj U) (f : X.presheaf.obj (op U)) :
    valR x U f = (GlobalTheory.Points.valMap x U h).hom f := by
  simp only [valR, dif_pos h, GlobalTheory.Points.valMap, CommRingCat.hom_comp, RingHom.comp_apply]

theorem exists_tuple_eq_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (r : ℕ) (p : Sp Ω ⟶ PSpace ℚ r),
    ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' := by
  intro Ω _ _ r p
  let y0 : Sp Ω := (default : PrimeSpectrum Ω)
  obtain ⟨i, hi0⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℚ r (p.base y0)
  have hi : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj (GlobalTheory.ProjSpace.chart ℚ r i) := by
    intro y _
    have hy : y = y0 := Subsingleton.elim (α := PrimeSpectrum Ω) y y0
    subst hy
    exact hi0
  set t : Fin (r + 1) → Ω := fun j => valR p (GlobalTheory.ProjSpace.chart ℚ r i) (GlobalTheory.ProjSpace.ratio ℚ r i j)
    with ht_def
  have hti : t i = 1 := by
    simp only [ht_def, valR_eq_valMap p _ hi]
    rw [show GlobalTheory.ProjSpace.ratio ℚ r i i = 1 from GlobalTheory.ProjSpace.ratioOn_self]
    exact map_one _
  have hti0 : t i ≠ 0 := by rw [hti]; exact one_ne_zero
  have htne : t ≠ 0 := fun h => hti0 (congr_fun h i)
  refine ⟨t, htne, ?_⟩
  have hq : ⊤ ≤ (TopologicalSpace.Opens.map (point ℚ t htne).base).obj (GlobalTheory.ProjSpace.chart ℚ r i) :=
    (GlobalTheory.TuplePoint.le_point_preimage_iff i).2 hti0
  refine GlobalTheory.Points.ext_of_valR (GlobalTheory.ProjSpace.isAffineOpen_chart ℚ r i) hi hq ?_
  intro f
  obtain ⟨P, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℚ r i f
  rw [valR_eq_valMap p _ hi, valR_eq_valMap _ _ hq]
  have key : (GlobalTheory.Points.valMap p _ hi).hom.comp (MvPolynomial.aeval (R := ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom
      = (GlobalTheory.Points.valMap (point ℚ t htne) _ hq).hom.comp
          (MvPolynomial.aeval (R := ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
    rw [← valR_eq_valMap p _ hi, ← valR_eq_valMap _ _ hq,
      GlobalTheory.TuplePoint.valR_point_ratio hti0 j, hti, div_one]
  exact RingHom.congr_fun key P

end GlobalTheory.CompanionTheory.Ar.TupleCoords
end

