module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupKilledNearPointOfFibre

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLiftOfFormallySmooth
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

theorem exists_ringHom_lift_of_formallySmooth {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    (φ : R →+* A) (hφ : φ.FormallySmooth) (ψ : R →+* C) (I : Ideal C) (hI : IsNilpotent I)
    (g : A →+* C ⧸ I) (hg : g.comp φ = (Ideal.Quotient.mk I).comp ψ) :
    ∃ F : A →+* C, (∀ x, Ideal.Quotient.mk I (F x) = g x) ∧ ∀ r, F (φ r) = ψ r := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  haveI : Algebra.FormallySmooth R A := hφ
  let g' : A →ₐ[R] C ⧸ I :=
    { g with
      commutes' := fun r => by
        have := congrArg (· r) hg
        exact this }
  refine ⟨(Algebra.FormallySmooth.lift I hI g').toRingHom, fun x => ?_, fun r => ?_⟩
  · exact Algebra.FormallySmooth.mk_lift I hI g' x
  · have := (Algebra.FormallySmooth.lift I hI g').commutes r
    simpa [RingHom.algebraMap_toAlgebra] using this

def powModP (p : ℕ) (hp : p.Prime) (B : Type) [CommRing B] :
    B →+* B ⧸ Ideal.span {(p : B)} where
  toFun z := Ideal.Quotient.mk _ (z ^ p)
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]
  map_zero' := by simp [zero_pow hp.ne_zero]
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
    rw [hr, map_add (f := _), map_add (f := _)]
    have : Ideal.Quotient.mk (Ideal.span {(p : B)}) ((p : B) * x * y * r) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, mul_assoc, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [this, add_zero]

theorem frob_lift_etale_chart :
    ∀ (p : ℕ) [Fact p.Prime] {n : ℕ} {B : Type} [CommRing B]
      (φ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B), φ.Etale →
      ∃ F : B →+* B, (∀ z, ∃ w, F z = z ^ p + p * w) ∧
        ∀ l, F (φ (MvPolynomial.X l)) = φ (MvPolynomial.X l) ^ p := by
  intro p hpf n B _ φ hφ
  have hp : p.Prime := hpf.out
  set I : Ideal B := Ideal.span {(p : B)} with hIdef
  have hp2 : ((p : B)) ^ 2 = 0 := by
    have : ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) = 0 := by
      rw [← map_natCast (MvPolynomial.C (σ := Fin n)), ZMod.natCast_self, map_zero]
    calc ((p : B)) ^ 2 = φ ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) := by
          rw [map_natCast]; push_cast; rfl
      _ = 0 := by rw [this, map_zero]
  have hI : IsNilpotent I := by
    refine ⟨2, ?_⟩
    rw [hIdef, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.zero_eq_bot]
  have hsm : φ.FormallySmooth := by
    letI := φ.toAlgebra
    haveI : Algebra.Etale _ B := hφ
    show Algebra.FormallySmooth _ B
    infer_instance
  let ψ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B :=
    φ.comp (MvPolynomial.expand p).toRingHom
  have hg : (powModP p hp B).comp φ = (Ideal.Quotient.mk I).comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact congrArg (· r) (Subsingleton.elim ((((powModP p hp B).comp φ)).comp MvPolynomial.C)
        (((Ideal.Quotient.mk I).comp ψ).comp MvPolynomial.C))
    · intro i
      simp [ψ, powModP, I]
  obtain ⟨F, hF1, hF2⟩ := exists_ringHom_lift_of_formallySmooth φ hsm ψ I hI (powModP p hp B) hg
  refine ⟨F, fun z => ?_, fun l => ?_⟩
  · have h1 := hF1 z
    have : F z - z ^ p ∈ I := by
      rw [← Ideal.Quotient.eq]
      exact h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨w, by rw [mul_comm]; linear_combination -hw⟩
  · rw [hF2]
    simp [ψ]

end GlobalTheory.DI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhdCommutingDerivations
section
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.SecondOrderNbhd

open TrivSqZeroExt

noncomputable def deform {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) : O →+* DualNumber R where
  toFun x := inl (f x) + inr (f (D x))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] lemma deform_fst {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).fst = f x := by
  simp [deform]

@[simp] lemma deform_snd {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).snd = f (D x) := by
  simp [deform]

lemma isNilpotent_span_of_sq {C : Type} [CommRing C] {e : C} (h : e * e = 0) :
    IsNilpotent (Ideal.span {e}) := by
  refine ⟨2, ?_⟩
  rw [Ideal.span_singleton_pow, pow_two, h]
  simp

theorem exists_second_order_nbhd : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  intro O _ _ D₁ D₂ h
  let i : O →+* DualNumber O := (inlHom O O)
  let j : DualNumber O →+* DualNumber (DualNumber O) := inlHom _ _
  let e₁ : DualNumber (DualNumber O) := inl DualNumber.eps
  let e₂ : DualNumber (DualNumber O) := DualNumber.eps
  have h1 : e₁ * e₁ = 0 := by
    simp only [e₁]; rw [inl_mul_inl, DualNumber.eps_mul_eps]; simp
  have h2 : e₂ * e₂ = 0 := DualNumber.eps_mul_eps
  refine ⟨DualNumber (DualNumber O), inferInstance, Ideal.span {e₁} + Ideal.span {e₂},
    j.comp i, j.comp (deform D₁ (RingHom.id O)), deform D₂ i,
    deform D₂ (deform D₁ (RingHom.id O)), e₁, e₂, ?_, ?_, ?_, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Commute.all _ _).isNilpotent_add (isNilpotent_span_of_sq h1) (isNilpotent_span_of_sq h2)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · intro x; ext <;> simp [i, j, e₁]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₁, h]
  · intro x hx
    have := congrArg (fun z : DualNumber (DualNumber O) => z.snd.snd) hx
    simpa [i, j, e₁, e₂] using this

end GlobalTheory.SecondOrderNbhd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallConjFixedOfValuation
section
open Polynomial

namespace GlobalTheory.UnitLemma

noncomputable def UQ.cInt (K : UQ) : K.O ≃+* K.O :=
  let f := algebraMap K.O K.E
  have hf : Function.Injective f := IsFractionRing.injective K.O K.E
  let d : K.O → K.O := fun x => Classical.choose (K.c_int x)
  have hd : ∀ x, f (d x) = K.c (f x) := fun x => (Classical.choose_spec (K.c_int x)).symm
  have hdd : ∀ x, d (d x) = x := fun x => hf (by rw [hd, hd, K.c_c])
  { toFun := d
    invFun := d
    left_inv := hdd
    right_inv := hdd
    map_mul' := fun a b => hf (by rw [hd, map_mul, map_mul, map_mul, hd, hd])
    map_add' := fun a b => hf (by rw [hd, map_add (f := _), map_add (f := _), map_add (f := _), hd, hd]) }

theorem UQ.cInt_spec (K : UQ) (x : K.O) :
    algebraMap K.O K.E (K.cInt x) = K.c (algebraMap K.O K.E x) :=
  (Classical.choose_spec (K.c_int x)).symm

theorem val_algebraMap_irreducible_pow (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E] {s : O} (hs : Irreducible s) (n : ℕ) :
    val O (algebraMap O E (s ^ n)) = n := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation s = WithZero.exp (-1 : ℤ) :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hs.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hs)
  unfold val
  rw [map_pow, map_pow, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, h1]
  simp

theorem exists_small_val (K : UQ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : K.O, K.Small t ∧ val K.O (algebraMap K.O K.E t) = k := by
  have hm : ∀ a : K.O, a ∈ IsLocalRing.maximalIdeal K.O ↔ ¬ IsUnit a := fun a =>
    IsLocalRing.mem_maximalIdeal a
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hcϖ : Irreducible (K.cInt ϖ) := (MulEquiv.irreducible_iff (K.cInt : K.O ≃* K.O)).mpr hϖ
  obtain ⟨ε, hε⟩ := IsDiscreteValuationRing.associated_of_irreducible K.O hϖ hcϖ
  obtain ⟨x, y, hxy, hunit⟩ := K.c_res
  have hcx : K.cInt x = y :=
    IsFractionRing.injective K.O K.E (by rw [K.cInt_spec, hxy])
  have hcc : ∀ a, K.cInt (K.cInt a) = a := fun a => K.cInt.symm_apply_apply a

  obtain ⟨s, hs, hsc⟩ : ∃ s : K.O, Irreducible s ∧ K.cInt s = s := by
    by_cases h1 : IsUnit (1 + (ε : K.O))
    · refine ⟨ϖ + K.cInt ϖ, ?_, ?_⟩
      · have : ϖ + K.cInt ϖ = ϖ * h1.unit := by rw [← hε]; simp [mul_add]
        rw [this]
        exact (associated_mul_unit_right ϖ _ h1.unit.isUnit).irreducible hϖ
      · rw [map_add (f := _), hcc, add_comm]
    · by_cases h2 : IsUnit (x + y * (ε : K.O))
      · refine ⟨x * ϖ + K.cInt (x * ϖ), ?_, ?_⟩
        · have : x * ϖ + K.cInt (x * ϖ) = ϖ * h2.unit := by
            rw [map_mul, hcx, ← hε]; simp; ring
          rw [this]
          exact (associated_mul_unit_right ϖ _ h2.unit.isUnit).irreducible hϖ
        · rw [map_add (f := _), hcc, add_comm]
      · apply absurd _ hunit
        have e : x - y = (x + y * (ε : K.O)) - y * (1 + (ε : K.O)) := by ring
        rw [e]
        exact Ideal.sub_mem _ ((hm _).mpr h2) (Ideal.mul_mem_left _ _ ((hm _).mpr h1))
  refine ⟨s ^ k, ⟨pow_ne_zero _ hs.ne_zero, ?_, ?_⟩, val_algebraMap_irreducible_pow K.O hs k⟩
  · exact Ideal.pow_mem_of_mem _ ((hm s).mpr hs.not_isUnit) k hk
  · rw [← K.cInt_spec, map_pow, hsc]

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSectionLiftBasicOpenAffine
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem awayMap_surjective_of_surjective (π : R →+* R₀) (hπ : Function.Surjective π) (f : R) :
    Function.Surjective (Localization.awayMap π f) :=
  Localization.awayMap_surjective_iff.2 fun a =>
    (hπ a).elim fun b hb => ⟨b, 0, by simp [hb]⟩

theorem isNilpotent_of_awayMap_eq_zero (π : R →+* R₀) (hnil : IsNilpotent (RingHom.ker π)) (f : R)
    (x : Localization.Away f) (hx : Localization.awayMap π f x = 0) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
  have hc : (Localization.awayMap π f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap R₀ (Localization.Away (π f))).comp π := IsLocalization.map_comp _
  have h1 : algebraMap R₀ (Localization.Away (π f)) (π a) = 0 := by
    have := congrArg (Localization.awayMap π f) hs
    rw [map_mul, hx, zero_mul] at this
    rw [← RingHom.comp_apply, ← hc, RingHom.comp_apply, ← this]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (π f)) _ _).1 h1
  have hmem : f ^ k * a ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_mul, map_pow]; exact hk
  have h0 : (f ^ k * a) ^ N = 0 := by
    have := Ideal.pow_mem_pow hmem N
    rw [hN] at this
    exact Ideal.mem_bot.1 this
  have hu : IsUnit (algebraMap R (Localization.Away f) (s * f ^ k)) := by
    rw [map_mul, map_pow]
    exact (IsLocalization.map_units _ s).mul ((IsLocalization.Away.algebraMap_isUnit f).pow k)
  refine ⟨N, (hu.pow N).mul_left_eq_zero.1 ?_⟩
  rw [← mul_pow, map_mul, ← mul_assoc, hs, ← map_mul, mul_comm a, ← map_pow, h0, map_zero]

theorem exists_liftIn_unfolded : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤ := by
  intro R R₀ _ _ π hπ hnil X hX g₀ hg p
  haveI := hX
  have hker : RingHom.ker π ≤ p.asIdeal := fun a ha => by
    obtain ⟨N, hN⟩ := hnil
    have := Ideal.pow_mem_pow ha N
    rw [hN] at this
    exact p.isPrime.mem_of_pow_mem N ((Ideal.mem_bot.1 this) ▸ p.asIdeal.zero_mem)
  obtain ⟨p₀, hp₀⟩ : p ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [_root_.range_comap_of_surjective (R := R) R₀ π hπ]
    exact hker
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g₀ p₀)) isOpen_univ
  obtain ⟨_, ⟨r, rfl⟩, hp₀r, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p₀) (u := {q : PrimeSpectrum R₀ | g₀ q ∈ V}) hxV (g₀ ⁻¹ᵁ V).isOpen
  obtain ⟨f, rfl⟩ := hπ r
  refine ⟨f, ?_, V, hV, ?_⟩
  · rw [← hp₀]
    exact hp₀r
  have hsurj := awayMap_surjective_of_surjective π hπ f
  have hnilL := isNilpotent_of_awayMap_eq_zero π hnil f
  have hc : (Localization.awayMap π f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap R₀ (Localization.Away (π f))).comp π := IsLocalization.map_comp _
  have hx0 : Set.range (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀) ⊆ V := by
    rintro _ ⟨q, rfl⟩
    apply hsub
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away (π f)) (π f)).subset ⟨q, rfl⟩
  obtain ⟨x, h₁, h₂⟩ := GlobalTheory.exists_lift_of_smooth_of_isAffineOpen X.hom (isAffineOpen_top (Sp R)) hV
    (fun _ _ => trivial) (CommRingCat.ofHom (Localization.awayMap π f))
    (spMap (algebraMap R (Localization.Away f))) (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀)
    (by
      rw [Category.assoc, hg, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact (congrArg (fun φ : R →+* Localization.Away (π f) => φ a) hc).symm)
    (fun _ _ => trivial) hx0 (by
      intro R' A _ _ _ _ _ _ π' hπ' φ
      exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.exists_lift_nil π'
        (fun c => (hsurj c).imp fun b hb => (hπ' b).trans hb)
        (fun a ha => hnilL a (by rw [RingHom.mem_ker] at ha; rw [← ha]; exact (hπ' a).symm)) φ)
  refine ⟨x, h₂, h₁, top_unique fun q _ => ?_⟩
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (Localization.awayMap π f)) := by
    rw [_root_.range_comap_of_surjective (R := Localization.Away f) _ _ hsurj]
    intro a ha
    obtain ⟨n, hn⟩ := hnilL a ha
    exact (q : PrimeSpectrum (Localization.Away f)).isPrime.mem_of_pow_mem n (hn ▸ q.asIdeal.zero_mem)
  show x q ∈ V
  have : x q = (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀) q' := by
    rw [← h₁]
    exact congrArg x hq'.symm
  rw [this]
  exact hx0 ⟨q', rfl⟩

theorem exists_liftIn : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ GlobalTheory.SecLift.LiftIn π X g₀ f V :=
  exists_liftIn_unfolded

end GlobalTheory.SecLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulDvdOfLocalizationAtPrimeTensor
section
open scoped TensorProduct
open TensorProduct

namespace GlobalTheory

theorem exists_smul_dvd_of_localization_atPrime_tensor :
    ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    (Q : Ideal O) [Q.IsPrime] (b : R) (m : O ⊗[R] C),
    (∃ m' : Localization.AtPrime Q ⊗[R] C,
      (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C m = algebraMap R (Localization.AtPrime Q) b • m') →
    ∃ s ∉ Q, ∃ m' : O ⊗[R] C, s • m = algebraMap R O b • m' := by
  intro R C O _ _ _ _ _ Q _ b m ⟨m', hm'⟩
  let f := AlgebraTensorModule.rTensor R C (Algebra.linearMap O (Localization.AtPrime Q))
  haveI : IsLocalizedModule Q.primeCompl f := inferInstance
  have hf : ∀ x, (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C x = f x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [f]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [hf, algebraMap_smul] at hm'
  obtain ⟨⟨m'', t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective Q.primeCompl f m'
  simp only [Function.uncurry_apply_pair] at hm'
  have h2 : f ((t : O) • m) = f (b • m'') := by
    rw [LinearMap.map_smul, hm', smul_comm (t : O) b, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
      LinearMap.map_smul_of_tower]
  obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := Q.primeCompl) h2
  refine ⟨(u : O) * t, (Q.primeCompl.mul_mem u.2 t.2 : _), (u : O) • m'', ?_⟩
  rw [algebraMap_smul, mul_smul]
  simpa [Submonoid.smul_def, smul_comm (u : O) b] using hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitFormLocalizationEtaleNbhdStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_form_localization_etale_nbhd : ∀ (B A₂ : Type) [CommRing B] [CommRing A₂] [Algebra B A₂] (f : B), IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} ∧ algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) := by
  first | (exact @GlobalTheory.DivUnitForm.unit_form) | (exact GlobalTheory.DivUnitForm.unit_form) | (intros; apply GlobalTheory.DivUnitForm.unit_form  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitZetaAct
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem ch_eq_exp_pow_val (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I / N) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]; congr 1; ring

theorem exists_unit_zetaAct : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ), ∃ a : (ZMod N)ˣ, ZetaAct g N a := by
  intro N _ g
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hg : IsPrimitiveRoot (g (Complex.exp (2 * Real.pi * Complex.I / N))) N :=
    hζ.map_of_injective g.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hcop : i.Coprime N := by
    rw [← hi] at hg
    exact (hζ.pow_iff_coprime (NeZero.pos N) i).mp hg
  refine ⟨ZMod.unitOfCoprime i hcop, fun j => ?_⟩
  rw [ch_eq_exp_pow_val, ch_eq_exp_pow_val, map_pow, ← hi, ← pow_mul, ZMod.coe_unitOfCoprime,
    ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  conv_lhs => rw [← Nat.div_add_mod (i * j.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePointsStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_closedImmersion_of_affine_points : ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X), (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) → ∃ z : T ⟶ Z, z ≫ i = g := by
  first | (exact @GlobalTheory.factor_closedImmersion_of_affine_points) | (exact GlobalTheory.factor_closedImmersion_of_affine_points) | (intros; apply GlobalTheory.factor_closedImmersion_of_affine_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

abbrev genPt {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) : Z := π (genericPoint Y)

abbrev fieldK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z)
    (hK : IsField (Z.presheaf.stalk (genPt π))) : Field (Z.presheaf.stalk (genPt π)) :=
  hK.toField

abbrev algKL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) :
    Algebra (Z.presheaf.stalk (genPt π)) Y.functionField :=
  (π.stalkMap (genericPoint Y)).hom.toAlgebra

abbrev algAK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Z, U) (Z.presheaf.stalk (genPt π)) :=
  (Z.presheaf.germ U (genPt π) h).hom.toAlgebra

abbrev algBL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
  (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) h).hom.toAlgebra


open scoped Classical in
def famIdeal {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) [IsAffineHom π]
    (hK : IsField (Z.presheaf.stalk (genPt π)))
    (hfd : letI := fieldK π hK; letI := algKL π
      FiniteDimensional (Z.presheaf.stalk (genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) : Ideal Γ(Z, U) := by
  classical
  exact if h : genPt π ∈ U.1 then
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    GlobalTheory.NormSheaf.normIdeal Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField Γ(Y, π ⁻¹ᵁ U.1)
      (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
  else ⊤

end GlobalTheory.NormSheafDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupKilledNearPointOfFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_subgroup_killed_near_point_of_fibre : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (Z : Over S') (i : Z ⟶ G) (V₀ : S'.Opens) (d : ℕ) (s : S'), Mono i → s ∈ V₀ → IsFinite (Z.hom ∣_ V₀) → (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) → (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) → (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) → IsUnit ((d : ℕ) : S'.residueField s) → (∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s), T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1) → ∃ V : S'.Opens, s ∈ V ∧ V ≤ V₀ ∧ ∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V : Set S') → (z ≫ i) ^ d = 1 := by
  first | (exact @GlobalTheory.FiniteKilled.killed_near) | (exact GlobalTheory.FiniteKilled.killed_near) | (intros; apply GlobalTheory.FiniteKilled.killed_near  <;> assumption)
end

