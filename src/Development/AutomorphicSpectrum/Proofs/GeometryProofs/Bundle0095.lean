module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberPointsGlue
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Chart (dAway dAway_ext dAway_lift isUnit_dAway Ld toL fromL toL_comp fromL_comp fromL_toL)

namespace GlobalTheory.CompanionTheory.Ar.LieFinGlue

variable {R : Type} [CommRing R]

theorem dualMap_algebraMap_eq_dAway (s : R) : dualMap (algebraMap R (Localization.Away s)) = dAway s := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]

theorem dualMap_comp_dualMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (p : B →+* C) (q : A →+* B) :
    (dualMap p).comp (dualMap q) = dualMap (p.comp q) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem span_range_inl {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤) :
    Ideal.span (Set.range fun k => (TrivSqZeroExt.inl (f k) : DualNumber R)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom R R)) hf
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

theorem spMap_algebraMap_eq (s : R) :
    spMap (algebraMap (DualNumber R) (Ld s)) = spMap (toL s) ≫ spMap (dAway s) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toL_comp]

theorem sep_base {X : Scheme.{0}} {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤)
    (a b : Sp R ⟶ X)
    (h : ∀ i, spMap (algebraMap R (Localization.Away (f i))) ≫ a =
      spMap (algebraMap R (Localization.Away (f i))) ≫ b) : a = b :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) _ hf).openCover _ _
    fun (k : J) => h k

theorem sep_dual {X : Scheme.{0}} {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤)
    (a b : Sp (DualNumber R) ⟶ X)
    (h : ∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ a =
      spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ b) : a = b := by
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber R)) _ (span_range_inl f hf)).openCover
    _ _ fun (k : J) => ?_
  have hk := h k
  rw [dualMap_algebraMap_eq_dAway] at hk
  show spMap (algebraMap (DualNumber R) (Ld (f k))) ≫ a = spMap (algebraMap (DualNumber R) (Ld (f k))) ≫ b
  rw [spMap_algebraMap_eq, Category.assoc, Category.assoc, hk]

theorem compat_of_pair {X : Scheme.{0}} {J : Type} (f : J → R)
    (w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X)
    (hw : ∀ i j (a : Localization.Away (f i) →+* Localization.Away (f i * f j))
      (b : Localization.Away (f j) →+* Localization.Away (f i * f j)),
      a.comp (algebraMap R _) = algebraMap R _ → b.comp (algebraMap R _) = algebraMap R _ →
      spMap (dualMap a) ≫ w i = spMap (dualMap b) ≫ w j)
    (i j : J) (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (f i)) →+* T)
    (β : DualNumber (Localization.Away (f j)) →+* T) (h : α.comp (dAway (f i)) = β.comp (dAway (f j))) :
    Spec.map (CommRingCat.ofHom α) ≫ w i = Spec.map (CommRingCat.ofHom β) ≫ w j := by
  have hi : IsUnit ((α.comp (dAway (f i))) (TrivSqZeroExt.inl (f i))) := (isUnit_dAway (f i)).map α
  have hj : IsUnit ((α.comp (dAway (f i))) (TrivSqZeroExt.inl (f j))) := by
    rw [h]
    exact (isUnit_dAway (f j)).map β
  have hij : IsUnit ((α.comp (dAway (f i))) (TrivSqZeroExt.inl (f i * f j))) := by
    rw [TrivSqZeroExt.inl_mul, map_mul]
    exact hi.mul hj
  obtain ⟨χ, hχ⟩ := dAway_lift (f i * f j) (α.comp (dAway (f i))) hij
  have hu : IsUnit (algebraMap R (Localization.Away (f i * f j)) (f i * f j)) :=
    IsLocalization.Away.algebraMap_isUnit (f i * f j)
  rw [map_mul] at hu
  have ui : IsUnit (algebraMap R (Localization.Away (f i * f j)) (f i)) := isUnit_of_mul_isUnit_left hu
  have uj : IsUnit (algebraMap R (Localization.Away (f i * f j)) (f j)) := isUnit_of_mul_isUnit_right hu
  let a : Localization.Away (f i) →+* Localization.Away (f i * f j) := IsLocalization.Away.lift (f i) ui
  let b : Localization.Away (f j) →+* Localization.Away (f i * f j) := IsLocalization.Away.lift (f j) uj
  have ha : a.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp _ ui
  have hb : b.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp _ uj
  have hα : χ.comp (dualMap a) = α := dAway_ext (f i) (by
    rw [RingHom.comp_assoc, ← dualMap_algebraMap_eq_dAway (f i), dualMap_comp_dualMap, ha,
      dualMap_algebraMap_eq_dAway, hχ, dualMap_algebraMap_eq_dAway])
  have hβ : χ.comp (dualMap b) = β := dAway_ext (f j) (by
    rw [RingHom.comp_assoc, ← dualMap_algebraMap_eq_dAway (f j), dualMap_comp_dualMap, hb,
      dualMap_algebraMap_eq_dAway, hχ, dualMap_algebraMap_eq_dAway, h])
  have e := hw i j a b ha hb
  rw [← hα, ← hβ, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg (Spec.map (CommRingCat.ofHom χ) ≫ ·) e


set_option backward.isDefEq.respectTransparency false in
theorem glue_of_compat {X : Scheme.{0}} {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤)
    (w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X)
    (hc : ∀ k l (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (f k)) →+* T)
      (β : DualNumber (Localization.Away (f l)) →+* T), α.comp (dAway (f k)) = β.comp (dAway (f l)) →
      Spec.map (CommRingCat.ofHom α) ≫ w k = Spec.map (CommRingCat.ofHom β) ≫ w l) :
    ∃ v : Sp (DualNumber R) ⟶ X, ∀ i, spMap (dAway (f i)) ≫ v = w i := by
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber R)) _
    (span_range_inl f hf)).openCover
  let g : ∀ k, 𝒰.X k ⟶ X := fun k => Spec.map (CommRingCat.ofHom (toL (f k))) ≫ w k
  have hg : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ g k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ g l := by
    refine fun (k : J) (l : J) => Scheme.Cover.hom_ext (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.openCover _ _
      fun (i : (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.I₀) => ?_
    let a : Spec ((pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i) ⟶ pullback (𝒰.f k) (𝒰.f l) :=
      (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.f i
    let A : CommRingCat.of (Ld (f k)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.fst (𝒰.f k) (𝒰.f l))
    let B : CommRingCat.of (Ld (f l)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.snd (𝒰.f k) (𝒰.f l))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap (DualNumber R) (Ld (f k))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap (DualNumber R) (Ld (f l))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc]
      exact congrArg (a ≫ ·) pullback.condition
    have key : A.hom.comp (algebraMap (DualNumber R) (Ld (f k))) =
        B.hom.comp (algebraMap (DualNumber R) (Ld (f l))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hkey : (A.hom.comp (toL (f k))).comp (dAway (f k)) = (B.hom.comp (toL (f l))).comp (dAway (f l)) := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, toL_comp, toL_comp]
      exact key
    have h := hc k l _ (A.hom.comp (toL (f k))) (B.hom.comp (toL (f l))) hkey
    show a ≫ pullback.fst (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (f k))) ≫ w k =
      a ≫ pullback.snd (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (f l))) ≫ w l
    rw [← Category.assoc a, ← Category.assoc a, ← ea, ← eb, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    exact h
  refine ⟨𝒰.glueMorphisms g hg, fun k => ?_⟩
  have hι : 𝒰.f k ≫ 𝒰.glueMorphisms g hg = g k := Scheme.Cover.ι_glueMorphisms 𝒰 g hg k
  have e : spMap (dAway (f k)) = Spec.map (CommRingCat.ofHom (fromL (f k))) ≫ 𝒰.f k := by
    show _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber R) (Ld (f k))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_comp]
  rw [e, Category.assoc, hι]
  show Spec.map (CommRingCat.ofHom (fromL (f k))) ≫ Spec.map (CommRingCat.ofHom (toL (f k))) ≫ w k = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_toL, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp]

theorem dual_glue : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (J : Type) [Finite J] (f : J → R),
    Ideal.span (Set.range f) = ⊤ →
  (∀ a b : Sp R ⟶ X, (∀ i, spMap (algebraMap R (Localization.Away (f i))) ≫ a = spMap (algebraMap R (Localization.Away (f i))) ≫ b) → a = b) ∧
  (∀ a b : Sp (DualNumber R) ⟶ X,
    (∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ a = spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ b) → a = b) ∧
  ∀ w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X,
    (∀ i j (a : Localization.Away (f i) →+* Localization.Away (f i * f j)) (b : Localization.Away (f j) →+* Localization.Away (f i * f j)),
      a.comp (algebraMap R _) = algebraMap R _ → b.comp (algebraMap R _) = algebraMap R _ →
      spMap (dualMap a) ≫ w i = spMap (dualMap b) ≫ w j) →
    ∃ v : Sp (DualNumber R) ⟶ X, ∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ v = w i := by
  intro X R _ J _ f hf
  refine ⟨sep_base f hf, sep_dual f hf, fun w hw => ?_⟩
  obtain ⟨v, hv⟩ := glue_of_compat f hf w (compat_of_pair f w hw)
  exact ⟨v, fun i => by rw [dualMap_algebraMap_eq_dAway]; exact hv i⟩

end GlobalTheory.CompanionTheory.Ar.LieFinGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Flat.KonstReg

theorem exists_const_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ g₀ : c.F →+* 𝔐.X.presheaf.stalk p.1, (genMap 𝔐.ξ p).comp g₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 p hunit
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hs : 𝔐.ξ ≫ (𝔐.f ≫ Y.s) = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) Ω)) := 𝔐.cst_over
  let h : 𝓞 c.F →+* 𝔐.X.presheaf.stalk p.1 :=
    (𝔐.X.presheaf.germ ⊤ p.1 trivial).hom.comp
      ((𝔐.f ≫ Y.s).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv.hom)
  have hgen : ∀ o : 𝓞 c.F, genMap 𝔐.ξ p (h o) = 𝔐.cst (algebraMap (𝓞 c.F) c.F o) :=
    fun o => Flat.ConstReg.genMap_germ_const 𝔐.ξ (𝔐.f ≫ Y.s) hs p o
  have hu : ∀ o : 𝓞 c.F, o ≠ 0 → IsUnit (h o) := by
    intro o ho
    have hI : (Ideal.span {o}).comap (algebraMap ℤ (𝓞 c.F)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ho (Ideal.mem_span_singleton_self o) (Algebra.IsIntegral.isIntegral o)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hn
    have hnat : IsUnit ((n.natAbs : ℕ) : 𝔐.X.presheaf.stalk p.1) := hunit _ (Int.natAbs_ne_zero.mpr hn0)
    have hint : IsUnit (h (algebraMap ℤ (𝓞 c.F) n)) := by
      rw [eq_intCast (algebraMap ℤ (𝓞 c.F)), map_intCast]
      rcases Int.natAbs_eq n with hn' | hn'
      · rw [hn']
        simpa using hnat
      · rw [hn']
        simpa using hnat
    exact isUnit_of_dvd_unit (map_dvd h hn) hint
  refine ⟨IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F)
    (fun z => hu z.1 (nonZeroDivisors.ne_zero z.2)), ?_⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F))
  ext o
  simp only [RingHom.comp_apply, IsLocalization.lift_eq]
  exact hgen o

end GlobalTheory.CompanionTheory.Ar.Flat.KonstReg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LabelCount

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem emb_ext {τ τ' : E →+* ℂ} (h : ∀ a : 𝓞 E, τ (a : E) = τ' (a : E)) : τ = τ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  simp at h2
  exact H.d_prime.ne_zero h2

theorem rt0_ne_neg (H : Host E) : H.rt0 ≠ -H.rt0 := by
  intro h
  have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination h
  exact rt0_ne_zero H ((mul_eq_zero.mp h2).resolve_left two_ne_zero)

theorem labelEmb_injective (c : Coeff l) : Function.Injective (labelEmb (H := H) c) := by
  have val : ∀ {s t : CMType H ⊕ CMType H}, labelEmb c s = labelEmb c t → ∀ a : 𝓞 E,
      ((labelEmb c s a : c.F) : ℂ) = ((labelEmb c t a : c.F) : ℂ) := fun h a => by rw [h]
  rintro (τ | τ) (τ' | τ') h
  · refine congrArg Sum.inl (Subtype.ext (emb_ext fun a => val h a))
  · exact absurd ((HodgeCptTest.labelEmb_inl_rt c τ).symm.trans
      ((val h H.rt).trans (HodgeCptTest.labelEmb_inr_rt c τ'))) (rt0_ne_neg H)
  · exact absurd ((HodgeCptTest.labelEmb_inl_rt c τ').symm.trans
      ((val h H.rt).symm.trans (HodgeCptTest.labelEmb_inr_rt c τ))) (rt0_ne_neg H)
  · refine congrArg Sum.inr (Subtype.ext (emb_ext fun a => ?_))
    have := val h (H.bar.symm a)
    simpa [labelEmb] using this

def labelCx (H : Host E) : CMType H ⊕ CMType H → (E →+* ℂ) :=
  Sum.elim (fun τ => τ.1) (fun τ => (starRingEnd ℂ).comp τ.1)

theorem labelCx_bijective (H : Host E) : Function.Bijective (labelCx H) := by
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have h1 := RingHom.congr_fun h (H.rt : E)
      simp only [labelCx, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply, τ.2, τ'.2,
        HodgeCptTest.imaginary_root_conj] at h1
      exact absurd h1 (rt0_ne_neg H)
    · have h1 := RingHom.congr_fun h (H.rt : E)
      simp only [labelCx, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply, τ.2, τ'.2,
        HodgeCptTest.imaginary_root_conj] at h1
      exact absurd h1.symm (rt0_ne_neg H)
    · refine congrArg Sum.inr (Subtype.ext (RingHom.ext fun x => ?_))
      exact (starRingEnd ℂ).injective (RingHom.congr_fun h x)
  · intro σ
    have hsq : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have hrt : σ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hsq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hrt with hp | hm
    · exact ⟨.inl ⟨σ, hp⟩, rfl⟩
    · have ht : ((starRingEnd ℂ).comp σ) (H.rt : E) = H.rt0 := by
        simp [hm, HodgeCptTest.imaginary_root_conj]
      refine ⟨.inr ⟨(starRingEnd ℂ).comp σ, ht⟩, RingHom.ext fun x => ?_⟩
      simp [labelCx]

theorem labels_injective_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) [Fintype (CMType H)] (Ω : Type) [Field Ω] (cst : c.F →+* Ω),
    Function.Injective (fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s)) ∧
      Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H l c _ Ω _ cst
  refine ⟨fun s t h => labelEmb_injective c (RingHom.ext fun a => cst.injective (RingHom.congr_fun h a)), ?_⟩
  rw [Fintype.card_of_bijective (labelCx_bijective H), NumberField.Embeddings.card]

end GlobalTheory.CompanionTheory.Ar.LabelCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodPointOrConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich

theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    Function.Injective r := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [eq_bot_iff]
  intro n hn
  have h0 : r (algebraMap ℤ (𝓞 F) n) = 0 := hn
  have : (n : ℂ) = 0 := by simpa using h0
  simpa using this

theorem exists_extension_to_field {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    ∃ r' : F →+* ℂ, r'.comp (algebraMap (𝓞 F) F) = r :=
  ⟨IsFractionRing.lift (K := F) (ringOfIntegers_hom_injective r), RingHom.ext fun a => by
    simp only [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := F) (ringOfIntegers_hom_injective r) a⟩

theorem conj_eq_neg_of_sq_eq_neg_natCast {x : ℂ} {d : ℕ} (h : x ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ x = -x := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : x.re = 0 := by
    by_contra hne
    have : x.im = 0 := by
      have : x.re * x.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_pos.2 hne]
  apply Complex.ext <;> simp [h0]

theorem goodPt_or_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), GoodPt 𝔐 z ∨ GoodPt 𝔐 (spMap (starRingEnd ℂ) ≫ z) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 z
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let r : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have hr : z ≫ 𝔐.f ≫ Y.s = spMap r := by
    simp [r, spMap]
  obtain ⟨τ, hτ⟩ := exists_extension_to_field r
  have h1 := congrArg (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ_sq
  have h2 : ((τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exact Or.inl ⟨τ, by rw [hr, hτ], h⟩
  · refine Or.inr ⟨(starRingEnd ℂ).comp τ, ?_, ?_⟩
    · rw [Category.assoc, hr, ← hτ]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]
    · rw [RingHom.comp_assoc, RingHom.comp_apply, h, map_neg,
        conj_eq_neg_of_sq_eq_neg_natCast H.sqrt_neg_disc_sq, neg_neg]

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedSandwichDegreeBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

theorem cls_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (p : Cpt ξ) (c : (k : K) → J k), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p →
    ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (κ : Ω), (∀ n : ℕ, flagStep Ω b n = flagStep Ω b₀ n) ∧
      V.IsFrameAt b p ∧ (∀ j, (m : Ω) • b j ∈ M.lat p) ∧ (∀ j l, π j (b l) = if j = l then 1 else 0) ∧
      (∀ j, ∀ e ∈ M.lat p, (m : Ω) * π j e ∈ regAt ξ p) ∧ κ ≠ 0 ∧ κ ∈ regAt ξ p ∧ κ⁻¹ ∈ regAt ξ p ∧
      ∀ (e : Li) (t : Ω), e ∈ flagStep Ω b₀ (i + 1) → IsCls b₀ i e t → t / gen y a e₀ c = π i e * κ := by
  intro X Ω _ ξ K _ J y G _ Li _ _ M V r b₀ m i a e₀ _hb₀ hS hD p c hc
  obtain ⟨b, π, hf, hfr, hm, hπ, hr⟩ := hS p

  have hker : flagStep Ω b₀ i ≤ LinearMap.ker (π i) := by
    rw [← hf]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hne : i ≠ k := by
      rintro rfl
      simp at hk
    simp [hπ, hne]
  have hkill : ∀ (e : Li) (t : Ω), e - t • b₀ i ∈ flagStep Ω b₀ i → π i e = t * π i (b₀ i) := by
    intro e t h
    have h1 : π i (e - t • b₀ i) = 0 := hker h
    simpa [sub_eq_zero] using h1

  have hbi : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← hf]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [Flag.step_succ] at hbi
  obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.1 hbi
  obtain ⟨u', rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hone : u' * π i (b₀ i) = 1 := by
    have h1 : π i (b i) = 1 := by simp [hπ]
    have h2 : π i z = 0 := hker hz
    rw [← hzw] at h1
    simpa [h2] using h1
  have hu' : u' ≠ 0 := left_ne_zero_of_mul_eq_one hone
  have hw0 : π i (b₀ i) ≠ 0 := right_ne_zero_of_mul_eq_one hone
  have hcls : b i - u' • b₀ i ∈ flagStep Ω b₀ i := by
    have : b i - u' • b₀ i = z := by rw [← hzw]; abel
    rw [this]; exact hz

  have hreg : ∀ e ∈ V p, π i e ∈ regAt ξ p := by
    intro e he
    rw [hfr.2] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hπ]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simp [zero_mem]
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul s x _ hx =>
      have : π i (s • x) = (s : Ω) * π i x := (π i).map_smul (s : Ω) x
      rw [this]
      exact mul_mem s.2 hx

  have hgen : (V.gr b₀ i) p = Submodule.span (regAt ξ p) {u'} := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro s ⟨e, he, hs⟩
      have h1 := hkill e s hs
      refine Submodule.mem_span_singleton.2 ⟨⟨π i e, hreg e he⟩, ?_⟩
      show π i e * u' = s
      rw [h1, _root_.mul_assoc, mul_comm (π i (b₀ i)), hone, _root_.mul_one]
    · rintro _ rfl
      exact ⟨b i, by rw [hfr.2]; exact Submodule.subset_span ⟨i, rfl⟩, hcls⟩
  have hdeg : (V.gr b₀ i) p = Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    have := hD.2 p (Set.mem_univ p) c hc
    rw [this]
    rfl
  have hspan : Submodule.span (regAt ξ p) {u'} = Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    rw [← hgen, hdeg]
  have a1 : u' ∈ Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    rw [← hspan]; exact Submodule.mem_span_singleton_self _
  have a2 : gen y a e₀ c ∈ Submodule.span (regAt ξ p) {u'} := by
    rw [hspan]; exact Submodule.mem_span_singleton_self _
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 a1
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 a2
  have hα' : (α : Ω) * gen y a e₀ c = u' := hα
  have hβ' : (β : Ω) * u' = gen y a e₀ c := hβ
  have hg0 : gen y a e₀ c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hα'
    exact hu' hα'.symm
  have hκ : u' / gen y a e₀ c = α := by
    rw [← hα']; field_simp
  have hκi : (u' / gen y a e₀ c)⁻¹ = β := by
    rw [inv_div, ← hβ']; field_simp
  refine ⟨b, π, u' / gen y a e₀ c, hf, hfr, hm, hπ, hr, div_ne_zero hu' hg0, ?_, ?_, ?_⟩
  · rw [hκ]; exact α.2
  · rw [hκi]; exact β.2
  · intro e t _ hcl
    have h1 := hkill e t hcl
    have h2 : t = π i e * u' := by
      rw [h1, _root_.mul_assoc, mul_comm (π i (b₀ i)), hone, _root_.mul_one]
    rw [h2, mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionGeneratorValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_section_generator_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G) (B : Type) [CommRing B] [Algebra k B], homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ τ₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) τ₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet B Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val τ (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_unit | exact GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_unit <;> assumption)
end

