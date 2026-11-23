module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsPreconnectedBlockUnits
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BijectiveAppTopBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.UniversalConstants

theorem bijective_appTop_baseChange : ∀ (R : Type) [Field R] (X : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X), IsProper X.hom → GeometricallyIntegral X.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) := by
  intro R _ X _ hp hg R' _ g X' π f' H
  have := GlobalTheory.ProperFunctions.isIso_appTop_baseChange_of_field H
  exact ConcreteCategory.bijective_of_isIso f'.appTop

end GlobalTheory.UniversalConstants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmFieldHostElementAddConjEqOne
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DiagDifferent

theorem trace_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (a : E) :
    Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem conj_rt {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : cc (H.rt : E) = -(H.rt : E) := by
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have hsq : (cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
    unfold cc
    rw [← map_pow, hs, map_neg, map_natCast]
  refine (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left fun h1 => ?_
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 := IsCMField.complexEmbedding_complexConj E τ (H.rt : E)
  unfold cc at h1
  rw [h1] at h2
  have h3 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hs, map_neg, map_natCast]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2.symm
  rw [hr] at h3
  have h4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem cmField_host_element_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h2 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h1
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  rw [conj_rt] at h2
  have : (2 : E) * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h1 + h2
  exact mul_left_cancel₀ two_ne_zero this

theorem trace_even_real_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (∀ a ∈ I, cc a ∈ I) → cc x = x → ((∀ s ∈ I, cc s = s → ∃ n : ℤ, Algebra.trace ℚ E (x * s) = 2 * n) ↔ ∀ s ∈ I, ∃ n : ℤ, Algebra.trace ℚ E (x * s) = n) := by
  intro E _ _ _ H I x hI hx
  have hmul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => map_mul _ a b
  have hadd : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => map_add _ a b
  have hcc : ∀ a : E, cc (cc a) = a := fun a => IsCMField.complexConj_apply_apply E a
  constructor
  · intro h s hs
    have hm : s + cc s ∈ I := Submodule.add_mem (I : Submodule (𝓞 E) E) hs (hI s hs)
    obtain ⟨n, hn⟩ := h (s + cc s) hm (by rw [hadd, hcc, add_comm])
    refine ⟨n, ?_⟩
    have e : x * cc s = cc (x * s) := by rw [hmul, hx]
    rw [mul_add, map_add (f := _), e, trace_conj] at hn
    linarith
  · intro h s hs hcs
    have hm : (H.w0 : E) * s ∈ I := Submodule.smul_mem (I : Submodule (𝓞 E) E) H.w0 hs
    obtain ⟨n, hn⟩ := h _ hm
    refine ⟨n, ?_⟩
    have e : x * s = x * ((H.w0 : E) * s) + cc (x * ((H.w0 : E) * s)) := by
      rw [hmul, hmul, hx, hcs]
      linear_combination (-(x * s)) * cmField_host_element_add_conj_eq_one H
    rw [e, map_add (f := _), trace_conj, hn]
    ring

end GlobalTheory.DiagDifferent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
section
noncomputable section

namespace GlobalTheory.TanDeriv

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.TanMod

def evAt {R : Type} [CommRing R] {Y : Scheme.{0}} (W : Sp R ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U)
    (f : Γ(Y, U)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((W.appLE U ⊤ h).hom f)

theorem evAt_congr {R : Type} [CommRing R] {Y : Scheme.{0}} {W W' : Sp R ⟶ Y} (e : W = W') (U : Y.Opens)
    (h : ⊤ ≤ W ⁻¹ᵁ U) (h' : ⊤ ≤ W' ⁻¹ᵁ U) (f : Γ(Y, U)) : evAt W U h f = evAt W' U h' f := by
  subst e; rfl

theorem evAt_comp {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ W) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evAt (spMap φ ≫ W) U h' f = φ (evAt W U h f) := by
  have h1 : (spMap φ ≫ W).appLE U ⊤ h' = W.appLE U ⊤ h ≫ (spMap φ).appTop := by
    have : (spMap φ).appTop = (spMap φ).appLE ⊤ ⊤ le_top := (Scheme.Hom.app_eq_appLE (spMap φ))
    rw [this]
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) W U ⊤ ⊤ h le_top).symm
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h3 := congrArg (fun ψ => ψ.hom ((W.appLE U ⊤ h).hom f)) h2
  unfold evAt
  rw [h1]
  exact h3

theorem top_le_of_comp {R A : Type} [CommRing R] [CommRing A] (p : R →+* A)
    (hs : Function.Surjective p) (hn : ∀ x, p x = 0 → x * x = 0) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ (spMap p ≫ W) ⁻¹ᵁ U) : ⊤ ≤ W ⁻¹ᵁ U := by
  intro x _
  have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap p) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    have h3 : a * a ∈ (show PrimeSpectrum R from x).asIdeal := by
      rw [hn a ha]; exact Ideal.zero_mem _
    exact ((show PrimeSpectrum R from x).isPrime.mem_or_mem h3).elim id id
  obtain ⟨y, hy⟩ := hx
  have h4 : (show Sp A from y) ∈ (spMap p ≫ W) ⁻¹ᵁ U := h trivial
  have h5 : spMap p (show Sp A from y) = x := hy
  rw [← h5]
  exact h4

theorem comp_top_le {R A : Type} [CommRing R] [CommRing A] (p : R →+* A) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U) : ⊤ ≤ (spMap p ≫ W) ⁻¹ᵁ U :=
  fun y _ => h (show spMap p y ∈ (⊤ : (Sp R).Opens) from trivial)

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G]

theorem snd_evAt_mul (u v : overAt x0 (DualNumber S) ⟶ G) (hu0 : smT x0 0 u = 1) (hv0 : smT x0 0 v = 1)
    (U : G.left.Opens) (hu : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from u.left) ⁻¹ᵁ U)
    (hv : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from v.left) ⁻¹ᵁ U)
    (huv : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from (u * v).left) ⁻¹ᵁ U) (f : Γ(G.left, U)) :
    (evAt (R := DualNumber S) (u * v).left U huv f).snd =
      (evAt (R := DualNumber S) u.left U hu f).snd + (evAt (R := DualNumber S) v.left U hv f).snd := by
  have hz : (0 : S →ₗ[S] S) = (0 : S) • (LinearMap.id : S →ₗ[S] S) := by simp
  let P : overAt x0 (TrivSqZeroExt S (S × S)) ⟶ G :=
    (homAt x0 (tm (LinearMap.inl S S S)) ≫ u) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v)
  have e1 : homAt x0 (tm (LinearMap.fst S S S)) ≫ P = u := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change _ * smT x0 0 v = _
    rw [hv0, _root_.mul_one]
  have e2 : homAt x0 (tm (LinearMap.snd S S S)) ≫ P = v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change smT x0 0 u * _ = _
    rw [hu0, _root_.one_mul]
  have e3 : homAt x0 (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S)) ≫ P = u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.coprod_inl, LinearMap.coprod_inr, TrivSqZeroExt.map_id, homAt_id, Category.id_comp,
      Category.id_comp]
  have f1 : spMap (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = u.left :=
    congrArg (fun φ => φ.left) e1
  have f2 : spMap (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = v.left :=
    congrArg (fun φ => φ.left) e2
  have f3 : spMap (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = (u * v).left :=
    congrArg (fun φ => φ.left) e3
  have hP : ⊤ ≤ (show Sp (TrivSqZeroExt S (S × S)) ⟶ G.left from P.left) ⁻¹ᵁ U := by
    refine top_le_of_comp (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ?_ ?_ _ U ?_
    · intro y
      refine ⟨tm (LinearMap.inl S S S) y, ?_⟩
      ext <;> simp
    · intro x hx
      have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
      ext <;> simp [h1]
    · exact f1 ▸ hu
  rw [← evAt_congr f1 U (comp_top_le _ _ U hP) hu, ← evAt_congr f2 U (comp_top_le _ _ U hP) hv,
    ← evAt_congr f3 U (comp_top_le _ _ U hP) huv, evAt_comp _ _ U hP, evAt_comp _ _ U hP, evAt_comp _ _ U hP]
  simp

variable [IsCommMonObj G]

theorem tan_top_le (U : G.left.Opens)
    (h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U) (m : TanSp x0 G) :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from m.pt.left) ⁻¹ᵁ U := by
  refine top_le_of_comp (TrivSqZeroExt.fstHom S S S).toRingHom ?_ ?_ _ U ?_
  · intro y
    exact ⟨TrivSqZeroExt.inl y, rfl⟩
  · intro x hx
    have h1 : x.fst = 0 := hx
    ext <;> simp [h1]
  · exact (unit_of_smT_zero x0 _ m.tan).symm ▸ h1

def derivAt (U : G.left.Opens) (h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U)
    (f : Γ(G.left, U)) : TanSp x0 G →ₗ[S] S where
  toFun m := (evAt (R := DualNumber S) m.pt.left U (tan_top_le U h1 m) f).snd
  map_add' m n := snd_evAt_mul m.pt n.pt m.tan n.tan U _ _ _ f
  map_smul' a m := by
    have := evAt_comp (epsMul a) (show Sp (DualNumber S) ⟶ G.left from m.pt.left) U (tan_top_le U h1 m)
      (tan_top_le U h1 (a • m)) f
    refine (congrArg TrivSqZeroExt.snd this).trans ?_
    simp [epsMul]

theorem derivAt_sum {m : ℕ} (b : Fin m → TanSp x0 G) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ G.left)
    (hw : w = (∑ i, a i • b i).pt.left) (U : G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (hv : ∀ i, ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from (b i).pt.left) ⁻¹ᵁ U) (f : Γ(G.left, U)) :
    (evAt w U h f).snd = ∑ i, a i * (evAt (R := DualNumber S) (b i).pt.left U (hv i) f).snd := by
  subst hw
  have h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U :=
    (unit_of_smT_zero x0 _ (∑ i, a i • b i).tan) ▸ comp_top_le _ _ U h
  have key := map_sum (derivAt U h1 f) (fun i => a i • b i) Finset.univ
  simp only [map_smul, smul_eq_mul] at key
  exact key

theorem derivative_tangent_combination_universal_group_eval {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hv0 : ∀ i, IsTanAt x (v i)) (hw : IsCombAt x v a w)
    (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)) :
    (evAt w U h f).snd = ∑ i, a i * (evAt (v i) U (hv i) f).snd := by
  let b : Fin m → TanSp x Xo.univ.t.G := fun i =>
    TanSp.mk (Over.homMk (v i) (hv0 i).1) (smT_zero_of x _ (hv0 i).2)
  refine derivAt_sum b a w ?_ U h hv f
  obtain ⟨u, hu, rfl⟩ := hw
  have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
  subst hub
  rw [List.prod_ofFn, ← TanSp.pt_sum]

end SlopeTestRemainingChoices

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem deriv_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), (∀ i, IsTanAt x (v i)) → IsCombAt x v a w → ∀ (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)), TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom ((w.appLE U ⊤ h).hom f)) = ∑ i, a i * TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom (((v i).appLE U ⊤ (hv i)).hom f)) := by
  intro E _ _ _ H Dw l Xo S _ x m v a w hv0 hw U h hv f
  exact derivative_tangent_combination_universal_group_eval Xo x v a w hv0 hw U h hv f

end GlobalTheory.TanDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameRingOverTestRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem FrameRing_of_algEquiv {K : Type} [Field K] {J : Type} (m : J → ℕ) {R A B : Type} [CommRing R] [Algebra K R]
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (π : R →ₐ[K] A)
    (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ) (h : FrameRing m π X s) (e : A ≃ₐ[K] B) :
    FrameRing m ((e : A →ₐ[K] B).comp π) (fun τ => (X τ).map e) (Units.map (e : A →* B) s) := by
  refine ⟨fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩
  · have := (h.1 τ).map (e : A →+* B)
    rw [RingHom.map_det] at this
    exact this
  · obtain ⟨k, ⟨h1, h2, h3⟩, hu⟩ := h.2 T ψ g a hg
    refine ⟨k.comp (e.symm : B →ₐ[K] A), ⟨?_, fun τ => ?_, ?_⟩, ?_⟩
    · rw [← h1]; ext x; simp
    · rw [← h2 τ]; ext i j; simp
    · rw [← h3]; simp
    · rintro k' ⟨h1', h2', h3'⟩
      have : k'.comp (e : A →ₐ[K] B) = k := by
        refine hu _ ⟨?_, fun τ => ?_, ?_⟩
        · rw [← h1']; rfl
        · rw [← h2' τ]; ext i j; simp
        · rw [← h3']; simp
      rw [← this]; ext x; simp

theorem exists_frameRing_reduced {K : Type} [Field K] {J : Type} [Fintype J] (m : J → ℕ) (R : Type) [CommRing R]
    [Algebra K R] [Algebra.FiniteType K R] [IsReduced R] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra K A) (π : R →ₐ[K] A)
      (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ),
      Algebra.FiniteType K A ∧ IsReduced A ∧ FrameRing m π X s := by
  let σ := Option (Σ τ, Fin (m τ) × Fin (m τ))
  let P := MvPolynomial σ R
  let Y : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) P := fun τ => Matrix.of fun i j => MvPolynomial.X (some ⟨τ, i, j⟩)
  let d : P := MvPolynomial.X none * ∏ τ, (Y τ).det
  let A := Localization.Away d
  have hd : IsUnit (algebraMap P A d) := IsLocalization.Away.algebraMap_isUnit d
  have hs : IsUnit (algebraMap P A (MvPolynomial.X none)) := by
    exact isUnit_of_dvd_unit (map_dvd (algebraMap P A) (dvd_mul_right _ _)) hd
  have hY : ∀ τ, IsUnit (algebraMap P A (Y τ).det) := by
    intro τ
    have h0 : (Y τ).det ∣ d :=
      Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun τ => (Y τ).det) (Finset.mem_univ τ)) _
    exact isUnit_of_dvd_unit (map_dvd (algebraMap P A) h0) hd
  have hPred : IsReduced P := inferInstance
  have hPft : Algebra.FiniteType R P := inferInstance
  have hAft : Algebra.FiniteType P A := inferInstance
  have hPft' : Algebra.FiniteType K P := Algebra.FiniteType.trans inferInstance hPft
  refine ⟨A, inferInstance, inferInstance, IsScalarTower.toAlgHom K R A, fun τ => (Y τ).map (algebraMap P A),
    hs.unit, Algebra.FiniteType.trans hPft' hAft, inferInstance, fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩
  · have := hY τ
    rw [RingHom.map_det] at this
    exact this
  · let v : σ → T := fun o => Option.elim o (a : T) (fun x => g x.1 x.2.1 x.2.2)
    let φ : P →ₐ[K] T := MvPolynomial.aevalTower ψ v
    have hφY : ∀ τ, (Y τ).map φ = g τ := by
      intro τ; ext i j
      simp [φ, Y, v, P]
    have hφs : φ (MvPolynomial.X none) = a := by simp [φ, v, P]
    have hφd : IsUnit (φ d) := by
      simp only [d, map_mul, map_prod, hφs]
      refine a.isUnit.mul (IsUnit.prod_univ_iff.2 fun τ => ?_)
      rw [AlgHom.map_det]
      have := hg τ
      rw [← hφY τ] at this
      exact this
    let k : A →ₐ[K] T := IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := φ) (by
      rintro ⟨_, n, rfl⟩
      simpa using hφd.pow n)
    have hk : ∀ x : P, k (algebraMap P A x) = φ x := fun x => by simp [k]
    refine ⟨k, ⟨?_, fun τ => ?_, ?_⟩, ?_⟩
    · ext x
      change k (algebraMap R A x) = ψ x
      rw [IsScalarTower.algebraMap_apply R P A, hk]
      simp [φ, P]
    · rw [← hφY τ]; ext i j; simp [hk]
    · simp [hk, hφs]
    · rintro k' ⟨h1, h2, h3⟩
      have key : (k' : A →+* T).comp (algebraMap P A) = (φ : P →+* T) := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun o => ?_)
        · have := AlgHom.congr_fun h1 r
          change k' (algebraMap R A r) = ψ r at this
          rw [IsScalarTower.algebraMap_apply R P A] at this
          have h' : φ (MvPolynomial.C r) = ψ r := by simp [φ, P]
          exact this.trans h'.symm
        · rcases o with _ | ⟨τ, i, j⟩
          · exact h3.trans hφs.symm
          · have a1 := congrFun (congrFun (h2 τ) i) j
            have a2 := congrFun (congrFun (hφY τ) i) j
            exact a1.trans a2.symm
      apply AlgHom.coe_ringHom_injective
      apply IsLocalization.ringHom_ext (Submonoid.powers d)
      rw [key]
      ext x
      · exact (hk _).symm
      · exact (hk _).symm

theorem exists_frameRing_testRing :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), FrameRing m π X s := by
  intro K _ J _ m p
  obtain ⟨h1, h2⟩ := (reduced_finiteType_iff_testRing K).2 p
  obtain ⟨A, _, _, π, X, s, hft, hred, hF⟩ := exists_frameRing_reduced (K := K) m p.R
  obtain ⟨q, ⟨e⟩⟩ := (reduced_finiteType_iff_testRing K).1 A hft hred
  exact ⟨q, _, _, _, FrameRing_of_algEquiv m π X s hF e.symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeDatumOfSelfDualLatticeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeDatum_of_selfDual_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r → E)), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → Λ'.FG → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (ξ * herm Gm v y) = n) ↔ v ∈ Λ') → ∃ (D' : Datum H) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧ LinearMap.range φ' = Λ' ∧ (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) := by
  first | exact @GlobalTheory.LatticeDatum.exists_datum_of_selfDual | exact GlobalTheory.LatticeDatum.exists_datum_of_selfDual | (intros; apply GlobalTheory.LatticeDatum.exists_datum_of_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPeriodMulVec
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PeriodLin


open NumberField AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
theorem _root_.GlobalTheory.PeriodLin.exists_period_mulVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P → IsUnit h₀.det → (∀ j j', h₀ j j' ≠ 0 → ty j = ty j') → ∃ P' : D.La →+ (Fin g → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' ∧ ∀ a, P' a = h₀ *ᵥ P a := by
  intro E _ _ _ H D g ty P h₀ hP hu hty
  refine ⟨(h₀.mulVecLin).toAddMonoidHom.comp P,
    _root_.GlobalTheory.PeriodConn.isPeriod_mulVec hP (isUnit_iff_ne_zero.mp hu) fun i j hij => ?_,
    fun a => rfl⟩
  by_contra hne
  exact hij (hty i j hne)

end GlobalTheory.PeriodLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem isDerivAt0_ex_isTanAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → (∀ w v, IsDerivAt0 (fun z => (F.ex k P z).left) w v → IsTanAt (F.u k P) v) ∧ (∀ w, ∃! v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsDerivAt0 (fun z => (F.ex k P z).left) w v) ∧ ∀ v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsTanAt (F.u k P) v → ∃! w, IsDerivAt0 (fun z => (F.ex k P z).left) w v := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P hP
  have h0 := (F.ex_ker k P hP 0).2 (zero_mem _)
  refine ⟨fun w v hv => ⟨((HolHom.isDerivAt0_iff _ _ _).1 hv).over, ?_⟩, fun w => ?_, fun v hv => ?_⟩
  · exact hv.1.trans (congrArg (·.left) h0)
  · obtain ⟨v, hv, -⟩ := (F.ex_diff k P hP).1 w
    exact ⟨v.left, hv, fun v' hv' =>
      ((HolHom.isDerivAt0_iff _ _ _).1 hv').unique ((HolHom.isDerivAt0_iff _ _ _).1 hv)⟩
  · exact (F.ex_diff k P hP).2 (Over.homMk v hv.1) (hv.2.trans (congrArg (·.left) h0).symm)

end GlobalTheory
end
end

