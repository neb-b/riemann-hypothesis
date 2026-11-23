module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionDualNumberFibreProductAffineMilnor
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen


open IsLocalRing in
theorem smallExt_fibre_ring : ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∃ (P : Type) (_ : CommRing P) (i : C →+* P) (p σ : P →+* C) (q : P →+* DualNumber (IsLocalRing.ResidueField C)), p.comp i = RingHom.id C ∧ σ.comp i = RingHom.id C ∧ q.comp i = (dnInl _).comp (IsLocalRing.residue C) ∧ IsClosedImmersion (spMap σ) ∧ Surjective (spMap σ) ∧ Milnor (spMap p) (spMap σ) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) ∧ Milnor (spMap p) (spMap q) (spMap (IsLocalRing.residue C)) (spMap (dnFst _)) := by
  intro C _ _ e he hm hne
  have hee : e * e = 0 := hm e he
  obtain ⟨φ, hφ⟩ : ∃ φ : ResidueField C →+ C, ∀ c, φ (residue C c) = c * e := by
    refine ⟨(Submodule.liftQ (maximalIdeal C) (LinearMap.toSpanSingleton C C e) ?_).toAddMonoidHom, fun c ↦ ?_⟩
    · intro a ha
      simpa using hm a ha
    · rfl
  have hφ0 : ∀ x, φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ] at hx
    rw [residue_eq_zero_iff]
    by_contra hc
    have hu : IsUnit c := by simpa using hc
    exact hne (hu.mul_right_eq_zero.mp hx)
  let P : Subring (C × DualNumber (ResidueField C)) :=
    RingHom.eqLocus ((residue C).comp (RingHom.fst _ _)) ((dnFst _).comp (RingHom.snd _ _))
  have hP : ∀ x : C × DualNumber (ResidueField C), x ∈ P ↔ residue C x.1 = x.2.fst := fun x ↦ Iff.rfl
  let p : P →+* C := (RingHom.fst _ _).comp P.subtype
  let q : P →+* DualNumber (ResidueField C) := (RingHom.snd _ _).comp P.subtype
  let i : C →+* P := RingHom.codRestrict ((RingHom.id C).prod ((dnInl _).comp (residue C))) P
    (fun c ↦ (hP _).2 rfl)
  let σ : P →+* C :=
    { toFun := fun x ↦ x.1.1 + φ x.1.2.snd
      map_one' := by simp
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add, TrivSqZeroExt.snd_add, map_add (f := _)]
        ring
      map_mul' := by
        rintro ⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩
        have hx' : residue C a = x.fst := hx
        have hy' : residue C b = y.fst := hy
        obtain ⟨c, hc⟩ := residue_surjective (R := C) x.snd
        obtain ⟨d, hd⟩ := residue_surjective (R := C) y.snd
        show a * b + φ (x * y).snd = (a + φ x.snd) * (b + φ y.snd)
        rw [DualNumber.snd_mul, ← hx', ← hy', ← hc, ← hd, ← map_mul, ← map_mul, ← map_add (f := _), hφ, hφ, hφ]
        linear_combination (-(c * d)) * hee }
  have hσ : ∀ x : P, σ x = x.1.1 + φ x.1.2.snd := fun _ ↦ rfl
  have hσi : σ.comp i = RingHom.id C := by
    ext c
    show c + φ (TrivSqZeroExt.inl (residue C c) : DualNumber _).snd = c
    simp
  have hsurj : Function.Surjective σ := fun c ↦ ⟨i c, RingHom.congr_fun hσi c⟩
  have hφmem : ∀ x, φ x ∈ Ideal.span {e} := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ]
    exact Ideal.mem_span_singleton'.2 ⟨c, rfl⟩
  have hker : RingHom.ker σ ≤ nilradical P := by
    rintro ⟨⟨a, x⟩, hx⟩ h
    have hx' : residue C a = x.fst := hx
    have h' : a + φ x.snd = 0 := h
    obtain ⟨c, hc⟩ := residue_surjective (R := C) x.snd
    rw [← hc, hφ] at h'
    have ha : a = -c * e := by linear_combination h'
    have h0 : x.fst = 0 := by
      rw [← hx', residue_eq_zero_iff, ha]
      exact Ideal.mul_mem_left _ _ he
    refine mem_nilradical.2 ⟨2, ?_⟩
    rw [pow_two]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show a * a = 0
      rw [ha]
      linear_combination (c * c) * hee
    · show x * x = 0
      ext
      · simp [h0]
      · simp [DualNumber.snd_mul, h0]
  refine ⟨P, inferInstance, i, p, σ, q, rfl, hσi, rfl, ?_, ?_, ?_, ?_⟩
  · exact IsClosedImmersion.spec_of_surjective _ hsurj
  · refine ⟨fun x ↦ ?_⟩
    have := range_comap_of_surjective _ σ hsurj
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker σ : Set P) := fun a ha ↦
      @nilradical_le_prime _ _ x.asIdeal x.isPrime _ (hker ha)
    rw [← this] at hx
    exact hx
  · refine _root_.GlobalTheory.DualOpen.milnor_of_ring_square _ _ _ _ _ _ _ _ ?_ ?_ ?_ Ideal.Quotient.mk_surjective
    · refine RingHom.ext fun x ↦ ?_
      refine (Ideal.Quotient.eq.2 ?_).symm
      show x.1.1 + φ x.1.2.snd - x.1.1 ∈ _
      simpa using hφmem _
    · rintro ⟨⟨a, x⟩, hx⟩ h1 h2
      have hx' : residue C a = x.fst := hx
      have h1' : a = 0 := h1
      have h2' : a + φ x.snd = 0 := h2
      subst h1'
      rw [zero_add] at h2'
      refine Subtype.ext (Prod.ext rfl ?_)
      show x = 0
      ext
      · simp [← hx']
      · simpa using hφ0 _ h2'
    · intro a b hab
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hab.symm)
      refine ⟨⟨(a, ⟨residue C a, residue C c⟩), rfl⟩, rfl, ?_⟩
      show a + φ (residue C c) = b
      rw [hφ, hc]
      ring
  · refine _root_.GlobalTheory.DualOpen.milnor_of_ring_square _ _ _ _ _ _ _ _ ?_ ?_ ?_ (fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩)
    · exact RingHom.ext fun x ↦ x.2
    · intro x h1 h2
      exact Subtype.ext (Prod.ext h1 h2)
    · intro a b hab
      exact ⟨⟨(a, b), hab⟩, rfl, rfl⟩

end GlobalTheory.DualOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoprodDescOfSmoothPieces
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

theorem smooth_desc_of_isColimit : ∀ {S S₁ S₂ X₁ X₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂), Smooth x₁ → Smooth x₂ → Smooth (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) := by
  intro S S₁ S₂ X₁ X₂ u₁ u₂ ⟨hc⟩ x₁ x₂ h₁ h₂
  let e := Limits.IsColimit.coconePointUniqueUpToIso (Limits.coprodIsCoprod S₁ S₂) hc
  have e₁ : Limits.coprod.inl ≫ e.hom = u₁ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.left⟩
  have e₂ : Limits.coprod.inr ≫ e.hom = u₂ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.right⟩
  have i₁ : IsOpenImmersion (Limits.coprod.inl : S₁ ⟶ S₁ ⨿ S₂) := inferInstance
  have i₂ : IsOpenImmersion (Limits.coprod.inr : S₂ ⟶ S₁ ⨿ S₂) := inferInstance
  have : IsIso e.hom := Iso.isIso_hom e
  have ie : IsOpenImmersion e.hom := inferInstance
  have o₁ : IsOpenImmersion u₁ := e₁ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₁ ie)
  have o₂ : IsOpenImmersion u₂ := e₂ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₂ ie)
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (coprodOpenCover.{0, 0} X₁ X₂) ?_
  rintro (_ | _)
  · show Smooth (Limits.coprod.inl ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inl_desc]; infer_instance
  · show Smooth (Limits.coprod.inr ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inr_desc]; infer_instance

end GlobalTheory.ProdGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDescendsFiniteFlatSurje
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjRelDim

theorem eq_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f] (p : Y ⟶ S)
    [Nonempty Y] {g m : ℕ} (hX : SmoothOfRelativeDimension g (f ≫ p)) (hY : SmoothOfRelativeDimension m p) :
    g = m := by
  let y : Y := Classical.arbitrary Y
  let t := S.fromSpecResidueField (p y)
  have hpb₂ := IsPullback.of_hasPullback p t
  have hpb₁ := IsPullback.of_hasPullback f (pullback.fst p t)
  have hpX : IsPullback (pullback.fst f (pullback.fst p t))
      (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t) (f ≫ p) t := hpb₁.paste_vert hpb₂
  have hgK : SmoothOfRelativeDimension g (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hpX hX
  have hmK : SmoothOfRelativeDimension m (pullback.snd p t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange m).of_isPullback hpb₂ hY
  obtain ⟨w, hw⟩ : p y ∈ Set.range t := by
    rw [Scheme.range_fromSpecResidueField]; rfl
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y w hw.symm
  obtain ⟨a, -⟩ := (pullback.snd f (pullback.fst p t)).surjective z
  have : Nonempty ↥(pullback f (pullback.fst p t)) := ⟨a⟩
  exact GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := (p y |> S.residueField))
    (pullback.snd f (pullback.fst p t)) (pullback.snd p t) hgK hmK

theorem smoothOfRelativeDimension_of_finite_surjective : ∀ (S : Scheme.{0}) (A B : Over S) (g : ℕ) (q : A ⟶ B),
    SmoothOfRelativeDimension g A.hom → Smooth B.hom → IsFinite q.left → Flat q.left → Surjective q.left →
    SmoothOfRelativeDimension g B.hom := by
  intro S A B g q hg hB hfin _ hsurj
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim B.hom
  have hn : ∀ y, n y = g := fun y => by
    have : Nonempty (W y) := ⟨⟨y, hW y⟩⟩
    have hd' := hd y
    have : Surjective (q.left ∣_ W y) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
    have hX : SmoothOfRelativeDimension g ((q.left ∣_ W y) ≫ (W y).ι ≫ B.hom) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q]
      have : SmoothOfRelativeDimension (0 + g) ((q.left ⁻¹ᵁ W y).ι ≫ A.hom) := inferInstance
      simpa using this
    exact (eq_of_finite_surjective (q.left ∣_ W y) ((W y).ι ≫ B.hom) hX hd').symm
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FiniteSurjRelDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionFiniteSurjectiveAbelian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjDimField

theorem smoothOfRelativeDimension_of_finite_surjective : ∀ (K : Type) [Field K] [IsAlgClosed K]
    (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' →
    IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g A'.hom := by
  intro K _ _ A A' _ _ g q hA hA' hfin hsurj hg
  have := hA.geomConnected
  have := hA'.geomConnected
  have := hA'.smooth
  have : ConnectedSpace A.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A.hom) (𝟙 _) (𝟙 _) A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have : ConnectedSpace A'.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A'.hom) (𝟙 _) (𝟙 _) A'.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected A'.hom (Classical.arbitrary A'.left)
  have hw : q.left ≫ A'.hom = A.hom := Over.w q
  have hg' : SmoothOfRelativeDimension g (q.left ≫ A'.hom) := by rw [hw]; exact hg
  have e := GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := K) q.left A'.hom hg' hm
  subst e
  exact hm

end GlobalTheory.FiniteSurjDimField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPresentationRelationsCombinationNormal
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothRel

theorem derivation_mem_of_mem_sq {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (I : Ideal A) {x : A} (hx : x ∈ I ^ 2) : D x ∈ I := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact I.add_mem (I.mul_mem_right _ hy) (I.mul_mem_right _ hz)
  · rw [map_add (f := _)]; exact I.add_mem hy hz

theorem taylor_rem_mem {R σ : Type} [CommRing R] [Fintype σ] (I : Ideal (MvPolynomial σ R))
    (u : σ → MvPolynomial σ R) (hu : ∀ i, u i ∈ I) (h : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + u i) h - h
      - ∑ i, MvPolynomial.pderiv i h * u i ∈ I ^ 2 := by
  classical
  induction h using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := Ideal.add_mem _ hp hq
    convert this using 1
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]; ring
  | mul_X p s hp =>
    have hD : ∑ i, MvPolynomial.pderiv i p * u i ∈ I :=
      Ideal.sum_mem _ fun i _ ↦ I.mul_mem_left _ (hu i)
    have h2 : (∑ i, MvPolynomial.pderiv i p * u i) * u s ∈ I ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hD (hu s)
    have h3 := Ideal.add_mem _ h2 ((I ^ 2).mul_mem_left (MvPolynomial.X s + u s) hp)
    have hs : ∑ i, MvPolynomial.pderiv i (p * MvPolynomial.X s) * u i
        = p * u s + MvPolynomial.X s * ∑ i, MvPolynomial.pderiv i p * u i := by
      simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · simp [Pi.single_apply]
      · exact Finset.sum_congr rfl fun i _ => by ring
    convert h3 using 1
    rw [map_mul, MvPolynomial.aeval_X, hs]; ring

theorem relations_combination :
    ∀ (R₀ : Type) [CommRing R₀] (n r : ℕ) (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (b : Fin r → Fin r → Fin r → MvPolynomial (Fin n) R₀), (∀ j, MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) → (∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2) ∧ ∀ j m, MvPolynomial.pderiv m (g j) + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * MvPolynomial.pderiv m (g k) ∈ Ideal.span (Set.range g) := by
  intro R₀ _ n r g a b hrel
  set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ
  have hg : ∀ k, g k ∈ J := fun k => Ideal.subset_span ⟨k, rfl⟩
  have hu : ∀ i, (∑ k, a i k * g k) ∈ J := fun i =>
    Ideal.sum_mem _ fun k _ => J.mul_mem_left _ (hg k)
  have h1 : ∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ J ^ 2 := by
    intro j
    have hT := taylor_rem_mem J (fun i => ∑ k, a i k * g k) hu (g j)
    have hA : MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) ∈ J ^ 2 := by
      rw [hrel j]
      exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ =>
        (J ^ 2).mul_mem_left _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hg k) (hg l))
    have := Ideal.sub_mem _ hA hT
    convert this using 1
    ring
  refine ⟨h1, fun j m => ?_⟩
  have hF := derivation_mem_of_mem_sq (MvPolynomial.pderiv m) J (h1 j)
  have hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0 := fun k =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hg k)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hF ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [Derivation.leibniz, map_sum, map_add (f := _), map_mul, hg0, smul_eq_mul, mul_add,
    Finset.sum_add_distrib] using hF

end GlobalTheory.SmoothRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSnc
section
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

open ReciprocityTheory.AnForm.R

namespace GlobalTheory.SncLocal

theorem mem_comps_of_compList {X : Scheme.{0}} {B : Set X} {m : ℕ} {C : Fin m → Closeds X}
    (hC : FinalTheorems.CompList B C) (i : Fin m) : (C i : Set X) ∈ ReciprocityTheory.AnForm.R.comps B := by
  classical
  refine ⟨⟨hC.1 i, hC.2.1 ▸ Set.subset_iUnion (fun j => (C j : Set X)) i⟩, fun D hD hiD => ?_⟩
  obtain ⟨z, hz, hDz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hD.1)
    (Finset.univ.image fun j => (C j : Set X))
    (fun z hz => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      exact (C j).isClosed)
    (by
      refine hD.2.trans (hC.2.1 ▸ Set.iUnion_subset fun j => ?_)
      exact Set.subset_sUnion_of_mem (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
  have hij : i = j := hC.2.2 i j (hiD.trans hDz)
  subst hij
  exact hDz

theorem lSncAt_of_snc (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X)
    (hB : Snc (Scheme.IdealSheafData.vanishingIdeal B)) (hC : CompList (B : Set X) C) (x : X) :
    LSncAt X C x := by
  obtain ⟨hreg, U, hx, n, f, J, hrsp, hZU⟩ := hB x
  haveI := hreg
  have hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) = B := by simp
  obtain ⟨O, hxO, -, hO⟩ := exists_open_comps x U hx f J hrsp hZU
  have key : ∀ i : {i : Fin m // x ∈ C i}, ∃ j ∈ J,
      ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) (f j) x (C i.1) ∧
      stalkId (Scheme.IdealSheafData.vanishingIdeal (C i.1)) x =
        Ideal.span {X.presheaf.germ U.1 x hx (f j)} := by
    rintro ⟨i, hxi⟩
    have hCi : ((C i : Closeds X) : Set X) ∈
        ReciprocityTheory.AnForm.R.comps ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) :=
      hs ▸ mem_comps_of_compList hC i
    have hO' := hO _ hCi
    have hq : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ (C i : Set X) ↔
        ∃ j ∈ J, ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X)
          (f j) x (C i) ∧ X.presheaf.germ U.1 x hx (f j) ∈ q.asIdeal := by
      intro q
      have hqO : X.fromSpecStalk x q ∈ (O : Set X) := by
        have h : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
        rw [Scheme.range_fromSpecStalk] at h
        exact Specializes.mem_open h O.isOpen hxO
      have h := Set.ext_iff.1 hO' (X.fromSpecStalk x q)
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and,
        GlobalTheory.SncComponents.fromSpecStalk_mem_zeroLocus_iff U x hx] at h
      exact h
    obtain ⟨j, hj, hbj, -⟩ := (hq (IsLocalRing.closedPoint _)).1
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hxi)
    refine ⟨j, hj, hbj, ?_⟩
    have hCC : (C i).compl.compl = C i := SetLike.coe_injective (compl_compl _)
    have hp : Prime (X.presheaf.germ U.1 x hx (f j)) :=
      prime_of_regular_params (fun i => X.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 j
    have h := GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl (C i).compl x
      (X.presheaf.germ U.1 x hx (f j)) fun q => by
        refine not_congr ((hq q).trans ⟨?_, fun h => ⟨j, hj, hbj, h⟩⟩)
        rintro ⟨k, hk, hbk, h⟩
        by_cases hjk : j = k
        · exact hjk ▸ h
        · exact absurd rfl (branch_ne x U hx f J hrsp hZU hj hk hjk hbj hbk)
    rw [hCC] at h
    rw [h]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  choose g hgJ hgb hgs using key
  refine ⟨hreg, n, fun k => X.presheaf.germ U.1 x hx (f k), ⟨g, fun a b hab => ?_⟩, hrsp, hgs⟩
  have h1 := hgb a
  rw [hab] at h1
  obtain ⟨D, -, hD⟩ := existsUnique_branch x U hx f J hrsp hZU (g b) (hgJ b)
  have e : (C a.1 : Set X) = C b.1 := (hD _ h1).trans (hD _ (hgb b)).symm
  exact Subtype.ext (hC.2.2 _ _ e.le)

theorem lSncAt_of_snc' : ∀ (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X), Snc (Scheme.IdealSheafData.vanishingIdeal B) → CompList (B : Set X) C → ∀ x : X, LSncAt X C x :=
  fun X _ B m C hB hC x => lSncAt_of_snc X B m C hB hC x

end GlobalTheory.SncLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanLogDerGermsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_logDer_germs' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∈ (j₀ TF.Y Z).opensRange → Submodule.span ((X₀ TF.Y Z).presheaf.stalk x) (Set.range δ) = ⊤ := by
  first | exact @GlobalTheory.LogKSDiv.span_logDer_germs | exact GlobalTheory.LogKSDiv.span_logDer_germs | (intros; apply GlobalTheory.LogKSDiv.span_logDer_germs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkIdPow
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.Poinc

theorem stalkId_pow' {Y : Scheme.{0}} (I : Y.IdealSheafData) (a : ℕ) (y : Y) :
    ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (I ^ a) y = ReciprocityTheory.AnForm.R.FinalTheorems.stalkId I y ^ a := by
  obtain ⟨W, hW, h₁, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  rw [ds_stalkId_eq_map _ ⟨W, hW⟩ y h₁, ds_stalkId_eq_map _ ⟨W, hW⟩ y h₁, ← Ideal.map_pow]
  rfl

theorem valOn_pow : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S)
    (φ : InvFun ℤ) (J : S.IdealSheafData) (d k : ℕ), ValOn F j φ J d → ValOn F j φ (J ^ k) (k * d) := by
  intro o _ ζ g n F S j φ J d k h T ξ hξ
  obtain ⟨a, ha, hJ⟩ := h T ξ hξ
  refine ⟨k * a, ?_, ?_⟩
  · push_cast; rw [ha]; ring
  · rw [idlAlong, stalkId_pow', Ideal.map_pow, ← idlAlong, hJ, Ideal.span_singleton_pow, pow_mul']

end GlobalTheory.Poinc
end

