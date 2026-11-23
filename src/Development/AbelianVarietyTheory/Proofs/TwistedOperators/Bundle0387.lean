module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioLocalFunctionsGeometricFibreDescendsBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.GlobalSectionsBijection

theorem toΓ_bij (S : Type) [CommRing S] : Function.Bijective (toΓ S) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)

theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  (Scheme.Hom.app_eq_appLE _).symm

theorem spMap_appLE_toΓ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) (a : T) :
    ((spMap χ).appLE ⊤ ⊤ le_top).hom (toΓ T a) = toΓ Ω (χ a) := by
  rw [appLE_top_top]
  exact (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom χ))).symm

theorem compat {T Ω : Type} [CommRing T] [CommRing Ω] {Y : Scheme.{0}} (q : Y ⟶ Sp T) (χ : T →+* Ω)
    (w : Sp Ω ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hw : w ≫ q = spMap χ) (a : T) :
    (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := by
  have key : (q.appLE ⊤ U le_top ≫ w.appLE U ⊤ h) = (w ≫ q).appLE ⊤ ⊤ le_top :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [← CommRingCat.comp_apply, key]
  have : ∀ g : Sp Ω ⟶ Sp T, g = spMap χ → (g.appLE ⊤ ⊤ le_top).hom (toΓ T a) = toΓ Ω (χ a) := by
    rintro _ rfl; exact spMap_appLE_toΓ χ a
  exact this _ hw

end GlobalTheory.GlobalSectionsBijection

namespace GlobalTheory.GlobalSectionsBijection

theorem ne_zero_of_mem {Ω : Type} [CommRing Ω] {Y : Scheme.{0}} (w : Sp Ω ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (s : Γ(Y, U)) (x : Sp Ω) (hx : w x ∈ Y.basicOpen s) : (w.appLE U ⊤ h).hom s ≠ 0 := by
  intro h0
  have e := Scheme.basicOpen_appLE w ⊤ U h s
  rw [h0, Scheme.basicOpen_zero] at e
  have : x ∈ (⊤ ⊓ w ⁻¹ᵁ Y.basicOpen s : (Sp Ω).Opens) := ⟨trivial, hx⟩
  rw [← e] at this
  exact this

theorem mem_of_ne_zero {Ω : Type} [Field Ω] {Y : Scheme.{0}} (w : Sp Ω ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (s : Γ(Y, U)) (hs : (w.appLE U ⊤ h).hom s ≠ 0) (x : Sp Ω) : w x ∈ Y.basicOpen s := by
  set g := (w.appLE U ⊤ h).hom s
  have hu : IsUnit g := by
    have e0 : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom g ≠ 0 := by
      intro e0
      apply hs
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom e0
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, map_zero] at this
      exact this
    have := (IsUnit.mk0 _ e0).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id] at this
    exact this
  have e := Scheme.basicOpen_appLE w ⊤ U h s
  rw [Scheme.basicOpen_of_isUnit _ hu] at e
  have : x ∈ (⊤ : (Sp Ω).Opens) := trivial
  rw [e] at this
  exact this.2

theorem exists_geom (Y : Scheme.{0}) (y : Y) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (w : Sp Ω ⟶ Y), ∀ x, w x = y := by
  refine ⟨AlgebraicClosure (Y.residueField y), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
      Y.fromSpecResidueField y, fun x => ?_⟩
  have : (Y.fromSpecResidueField y) ((Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y))))) x) ∈ Set.range (Y.fromSpecResidueField y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at this
  exact this

end GlobalTheory.GlobalSectionsBijection

namespace GlobalTheory.GlobalSectionsBijection

theorem fromSpec_appLE_top {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W) :
    hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(Y, W)).inv := by
  rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  rw [show (eqToHom hW.fromSpec_preimage_self).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

theorem chart_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    (c : Γ(Y, V) →+* R) : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ V := by
  intro x _
  show hV.fromSpec (spMap c x) ∈ (V : Set Y)
  rw [← hV.range_fromSpec]
  exact ⟨_, rfl⟩

theorem chart_eval {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    (c : Γ(Y, V) →+* R) (U' : Y.Opens) (hle : V ≤ U') (h : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ U')
    (s : Γ(Y, U')) :
    ((spMap c ≫ hV.fromSpec).appLE U' ⊤ h).hom s = toΓ R (c ((Y.presheaf.map (homOfLE hle).op).hom s)) := by
  have h' := chart_top hV c
  have e1 : (spMap c ≫ hV.fromSpec).appLE U' ⊤ h =
      Y.presheaf.map (homOfLE hle).op ≫ (spMap c ≫ hV.fromSpec).appLE V ⊤ h' :=
    (Scheme.Hom.map_appLE _ _ _).symm
  have e0 : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by simp
  have e2 : (spMap c ≫ hV.fromSpec).appLE V ⊤ h' =
      hV.fromSpec.appLE V ⊤ e0 ≫ (spMap c).appLE ⊤ ⊤ le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e1, e2, fromSpec_appLE_top]
  simp only [CommRingCat.comp_apply]
  exact spMap_appLE_toΓ c _

end GlobalTheory.GlobalSectionsBijection

namespace GlobalTheory.GlobalSectionsBijection

theorem chart_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R T : Type} [CommRing R] [CommRing T]
    (q : Y ⟶ Sp T) (c : Γ(Y, V) →+* R) :
    (spMap c ≫ hV.fromSpec) ≫ q = spMap (c.comp ((q.appLE ⊤ V le_top).hom.comp (toΓ T))) := by
  apply ext_of_isAffine
  rw [← appLE_top_top, ← appLE_top_top]
  ext x
  obtain ⟨a, rfl⟩ := (toΓ_bij T).2 x
  have key : ((spMap c ≫ hV.fromSpec) ≫ q).appLE ⊤ ⊤ le_top =
      q.appLE ⊤ V le_top ≫ (spMap c ≫ hV.fromSpec).appLE V ⊤ (chart_top hV c) :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [key, CommRingCat.comp_apply, chart_eval hV c V le_rfl, spMap_appLE_toΓ]
  simp

end GlobalTheory.GlobalSectionsBijection


open GlobalTheory.GlobalSectionsBijection in
theorem GlobalTheory.ratio_descends : ∀ (T : Type) [CommRing T] [IsReduced T] (Y : Scheme.{0}) (q : Y ⟶ Sp T) (I₀ : Type) (U : I₀ → Y.Opens) (t t₀ : ∀ j, Γ(Y, U j)), Smooth q → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω), ∃ α : Ω, (∀ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ → (w.appLE (U j) ⊤ h).hom (t j) = toΓ Ω α * (w.appLE (U j) ⊤ h).hom (t₀ j)) ∧ ∃ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ ∧ (w.appLE (U j) ⊤ h).hom (t₀ j) ≠ 0) → ∃ a : T, ∀ j, t j = (q.appLE ⊤ (U j) le_top).hom (toΓ T a) * t₀ j := by
  intro T _ _ Y q I₀ U t t₀ hq H
  haveI := hq
  haveI : IsReduced Y := GlobalTheory.isReduced_of_smooth_of_isReduced q
  let F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ Ω], (T →ₐ[ℤ] Ω) → Ω :=
    fun Ω _ _ _ χ => Classical.choose (H Ω χ.toRingHom)
  have hF : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ Ω] (χ : T →ₐ[ℤ] Ω) (j : I₀) (w : Sp Ω ⟶ Y)
      (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ.toRingHom →
      (w.appLE (U j) ⊤ h).hom (t j) = toΓ Ω (F Ω χ) * (w.appLE (U j) ⊤ h).hom (t₀ j) :=
    fun Ω _ _ _ χ => (Classical.choose_spec (H Ω χ.toRingHom)).1
  refine (_root_.GlobalTheory.SmoothLocalDescent.exists_of_smooth_locally ℤ T F ?_).elim ?_
  · intro p
    let κ := p.asIdeal.ResidueField
    let Ω := AlgebraicClosure κ
    let χ : T →+* Ω := (algebraMap κ Ω).comp (algebraMap T κ)
    obtain ⟨α, hα, j, w, h, hwq, hne⟩ := H Ω χ
    have hyD : w default ∈ Y.basicOpen (t₀ j) := mem_of_ne_zero w (U j) h (t₀ j) hne default
    obtain ⟨V, hV, hyV, hVD⟩ := exists_isAffineOpen_mem_and_subset hyD
    have hVU : V ≤ U j := hVD.trans (Y.basicOpen_le _)
    let φ : T →+* Γ(Y, V) := (q.appLE ⊤ V le_top).hom.comp (toΓ T)
    letI := φ.toAlgebra
    have hu : IsUnit ((Y.presheaf.map (homOfLE hVU).op).hom (t₀ j)) := by
      have h0 := Y.toRingedSpace.isUnit_res_basicOpen (t₀ j)
      have h1 := h0.map (Y.presheaf.map (homOfLE hVD).op).hom
      convert h1 using 1
      exact congrArg (fun f => (CommRingCat.Hom.hom f) (t₀ j))
        (Y.presheaf.map_comp (homOfLE (Y.basicOpen_le (t₀ j))).op (homOfLE hVD).op)
    let b' : Γ(Y, V) := (Y.presheaf.map (homOfLE hVU).op).hom (t j) * ↑hu.unit⁻¹
    refine ⟨Γ(Y, V), inferInstance, inferInstance, inferInstance, inferInstance, b', ?_, ?_, ?_⟩
    · show φ.Smooth
      exact (RingHom.Smooth.of_bijective (toΓ_bij T)).comp (q.smooth_appLE (isAffineOpen_top _) hV le_top)
    · have hwV : ⊤ ≤ w ⁻¹ᵁ V := fun x _ => by
        show w x ∈ V
        rw [Subsingleton.elim x default]; exact hyV
      let ψ : Γ(Y, V) →+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp (w.appLE V ⊤ hwV).hom
      have hψφ : ψ.comp φ = χ := by
        ext a
        show (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((w.appLE V ⊤ hwV).hom ((q.appLE ⊤ V le_top).hom (toΓ T a))) = χ a
        rw [compat q χ w V hwV hwq a, toΓ, ← CommRingCat.comp_apply, Iso.inv_hom_id]
        rfl
      refine ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩, PrimeSpectrum.ext ?_⟩
      show Ideal.comap φ (RingHom.ker ψ) = p.asIdeal
      rw [RingHom.comap_ker, hψφ]
      ext a
      simp only [RingHom.mem_ker, χ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap κ Ω).injective]
      rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    · intro Ω' _ _ _ χ'
      let c : Γ(Y, V) →+* Ω' := χ'.toRingHom
      have hw'U : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ U j := fun x hx => hVU (chart_top hV c hx)
      have hcomp : (spMap c ≫ hV.fromSpec) ≫ q =
          spMap (χ'.comp (IsScalarTower.toAlgHom ℤ T Γ(Y, V))).toRingHom := chart_comp hV q c
      have e := hF Ω' _ j _ hw'U hcomp
      rw [chart_eval hV c (U j) hVU, chart_eval hV c (U j) hVU, ← map_mul] at e
      have e2 := (toΓ_bij Ω').1 e
      show c (_ * _) = _
      rw [map_mul, e2, _root_.mul_assoc, ← map_mul, hu.mul_val_inv, map_one, _root_.mul_one]
  · intro a ha
    refine ⟨a, fun j => ?_⟩
    rw [← sub_eq_zero]
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro y hy
    exfalso
    obtain ⟨Ω, _, _, w, hw⟩ := exists_geom Y y
    have hyU : y ∈ U j := Y.basicOpen_le _ hy
    have h : ⊤ ≤ w ⁻¹ᵁ U j := fun x _ => by
      show w x ∈ U j
      rw [hw]; exact hyU
    let χ : T →+* Ω := (Spec.preimage (w ≫ q)).hom
    have hχ : w ≫ q = spMap χ := (Spec.map_preimage (w ≫ q)).symm
    have e1 := hF Ω χ.toIntAlgHom j w h hχ
    have e2 := ha Ω χ.toIntAlgHom
    apply ne_zero_of_mem w (U j) h _ default (by rw [hw]; exact hy)
    rw [map_sub, map_mul, compat q χ w (U j) h hχ a, e1]
    rw [← e2]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
section
open GlobalTheory.ArchUniq GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace GlobalTheory.ArchUniq.SchrTransport

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coords (P : V → V → ℝ) (hP : IsPairing P) [FiniteDimensional ℝ V] (n : ℕ) (hn : Module.finrank ℝ V = n) :
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, pPart (φ v) = C v.1) ∧ ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2 := by
  let C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)
  have hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) := by
    simp [Module.finrank_prod, hn]
  let φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim
  have hφ : ∀ v, φ v = pairCoordsL C hP v := fun v => rfl
  refine ⟨C, φ, fun v => ?_, fun v y => ?_⟩
  · ext i; simp [hφ, pPart, pairCoordsL]
  · rw [pair_expand C hP y v.2]
    simp [hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]

theorem schr_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (v : V × V) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    schrF P v (f ∘ C) = rhoFun (φ v) f ∘ C := by
  funext y
  have h2 : ⟪pPart (φ v), qPart (φ v)⟫ = -P v.1 v.2 := by rw [hp, real_inner_comm, hq]
  have h3 : ⟪C v.1, qPart (φ v)⟫ = -P v.1 v.2 := by rw [real_inner_comm, hq]
  simp only [schrF, rhoFun, phase, Function.comp_apply, map_add (f := _), hp, hq, h3]
  congr 2
  push_cast
  ring

theorem dRho_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (u : V × V) (g : 𝓢(V, ℂ)) (h : Sch (Fin n))
    (hg : ⇑g = ⇑h ∘ ⇑C) (y : V) :
    fderiv ℝ (⇑g) y u.1 - 2 * Real.pi * Complex.I * (P y u.2 : ℂ) * g y = dRho (φ u) h (C y) := by
  have hd : HasFDerivAt (⇑h ∘ ⇑C) ((fderiv ℝ (⇑h) (C y)).comp (C : V →L[ℝ] EuclideanSpace ℝ (Fin n))) y :=
    (h.hasFDerivAt (C y)).comp y C.hasFDerivAt
  rw [dRho_apply, hg, hd.fderiv, hp, hq]
  simp
  ring

theorem quad_eq_sum {l : Type} [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    quad X = ∑ p : (l ⊕ l) × (l ⊕ l), ((4 * Real.pi * Complex.I : ℂ)⁻¹ *
      ((((X * Matrix.J l ℝ) p.1 p.2 + (X * Matrix.J l ℝ) p.2 p.1) / 2 : ℝ) : ℂ)) •
        (dRho (Pi.single p.1 1) * dRho (Pi.single p.2 1)) := by
  rw [quad, Fintype.sum_prod_type, Finset.smul_sum]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => (4 * Real.pi * Complex.I : ℂ)⁻¹ • (((X * Matrix.J l ℝ) a b / 2 : ℝ) : ℂ) •
    (dRho (Pi.single b 1) * dRho (Pi.single a 1))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [smul_smul]
  rw [← add_smul]
  congr 1
  push_cast
  ring

theorem haar_coords {n : ℕ} [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, 0 < k ∧ ∀ F : V → ℝ, ∫ y, F y ∂μ = k * ∫ x, F (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ),
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), fun F => ?_⟩
  have h1 : ∫ y, F y ∂μ = ∫ x, F (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, F (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

theorem transport : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    (∀ (A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n)),
      (∀ w, Continuous fun t => A' t w) → (∀ s t f, T' (s + t) f = T' s (T' t f)) → (∀ f, T' 0 f = f) →
      (∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f)) →
      (∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T' t f y) →
      ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℂ),
        ∀ f y, HasDerivAt (fun t => T' t f y) (quad X f y + c * f y) 0) →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro V _ _ _ _ _ μ hμ P hP n hn H A T hAc hTadd hT0 hTi hTl2 hTc
  obtain ⟨C, φ, hp, hq⟩ := coords P hP n hn
  have hS := schr_coords P C φ hp hq
  let toE : 𝓢(V, ℂ) →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n) := fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := haar_coords μ C
  have c1 : ∀ w, Continuous fun t => A' t w := by
    intro w
    exact (φ.toLinearMap.continuous_of_finiteDimensional).comp (hAc (φ.symm w))
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have c6 : ∀ f y, Continuous fun t => T' t f y := by
    intro h y
    exact hTc (toV h) (C.symm y)
  obtain ⟨X, c, hX⟩ := H A' T' c1 c2 c3 c4 c5 c6
  let eq := (Fintype.equivFin ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n))).symm
  let S := X * Matrix.J (Fin n) ℝ
  refine ⟨Fintype.card ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)), fun i => φ.symm (Pi.single (eq i).1 1),
    fun i => φ.symm (Pi.single (eq i).2 1),
    fun i => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S (eq i).1 (eq i).2 + S (eq i).2 (eq i).1) / 2 : ℝ) : ℂ), c, ?_⟩
  intro f g₁ g₂ hg₁ hg₂ y
  have hf : ⇑f = ⇑(toE f) ∘ ⇑C := by ext x; simp [htoE]
  have h1 : ∀ i, ⇑(g₁ i) = ⇑(dRho (Pi.single (eq i).2 1) (toE f)) ∘ ⇑C := fun i => by
    ext x
    rw [hg₁, dRho_coords P C φ hp hq _ f (toE f) hf, LinearEquiv.apply_symm_apply]
    rfl
  have h2 : ∀ i, g₂ i y = dRho (Pi.single (eq i).1 1) (dRho (Pi.single (eq i).2 1) (toE f)) (C y) := fun i => by
    rw [hg₂, dRho_coords P C φ hp hq _ (g₁ i) _ (h1 i), LinearEquiv.apply_symm_apply]
  have hd := hX (toE f) (C y)
  have e1 : (fun t => T' t (toE f) (C y)) = fun t => T t f y := by
    funext t
    simp [hT', htoE, hVE]
  rw [e1] at hd
  convert hd using 1
  have e2 : toE f (C y) = f y := by simp [htoE]
  rw [e2, quad_eq_sum]
  congr 1
  simp only [h2, ContinuousLinearMap.coe_sum', Finset.sum_apply, SchwartzMap.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, SchwartzMap.smul_apply, ContinuousLinearMap.mul_apply, smul_eq_mul]
  exact Equiv.sum_comp eq (fun p => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S p.1 p.2 + S p.2 p.1) / 2 : ℝ) : ℂ) *
    dRho (Pi.single p.1 1) (dRho (Pi.single p.2 1) (toE f)) (C y))

end GlobalTheory.ArchUniq.SchrTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelSymplecticEqOrientedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.SympForm

theorem symplO_eq_symp_one {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x y =
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) 1 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹)) x y := by
  unfold symplO GlobalTheory.WeilM.symp hO GlobalTheory.WeilM.hTens
  congr 1
  have h : ∀ j l, (1 : AE D) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) j l =
      incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := fun j l => by
    rw [one_mul, ← map_mul]
    rfl
  have hc : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig z = cA D z := fun z => rfl
  simp only [Finset.mul_sum, hc]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
  have h' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ d c = incA D (T.gram c d) := rfl
  rw [h']
  linear_combination (-(x d a * incA D (T.gram c d) * cA D (y c b))) * h a b

end GlobalTheory.SquareAgree.SympForm


open GlobalTheory.SquareAgree.SympForm in
theorem GlobalTheory.SquareAgree.SympForm.symp_model_eq_symplO : ∀ (D : D7) (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
    Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram → Ws.J = D.host.xi0 • reindex e e X.gramᵀ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ u v, GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) u v = symplO (sgn ε S) X (cS u) (cS v) := by
  intro D ε S X d e Vs Ws hJ hJW cS hc u v
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E,
    (if ε then -1 else 1 : D.host.E) • S.gram = G := ⟨_, rfl⟩
  rw [hGdef] at hc
  have hs : (sgn ε S).gram = G := by
    rw [← hGdef]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  have hVJ : Vs.J = -G := by
    rw [hJ, ← hGdef]; cases ε <;> simp
  have hdet : IsUnit G.det := by rw [← hs]; exact (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hHG : (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hherm : ∀ i j, D.sp.cm.sig (G i j) = G j i := by
    intro i j
    have h := (sgn ε S).herm.eq ((sgn ε S).frame i) ((sgn ε S).frame j)
    rw [← hs]
    simpa [HSpace.gram, CMData.sig, starRingEnd_apply] using h
  have hG : (G.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (G.map (incA D))ᵀ := by
    ext i j
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (G i j)) = incA D (G j i)
    rw [← hherm i j]
    rfl
  have key := hTens_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e (X.gram.map (incA D)) (incA D D.host.xi0) hHG hG u v
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -(G.map (incA D)) := by
    rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = incA D D.host.xi0 • reindex e e (X.gram.map (incA D))ᵀ := by
    rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _
  have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) = incA D D.host.xi0 • (G⁻¹).map (incA D) := by
    rw [hs]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _
  have e4 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ = (X.gram.map (incA D))ᵀ := rfl
  rw [symplO_eq_symp_one, e3, e4, hc, hc, e1, e2]
  have e5 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G = G.map (incA D) := by ext i j; rfl
  simp only [e5]
  unfold GlobalTheory.WeilM.symp
  simp only [key, one_mul, neg_one_mul]

end
end

