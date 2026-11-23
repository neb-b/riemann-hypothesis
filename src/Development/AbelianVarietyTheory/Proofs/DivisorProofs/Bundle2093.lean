module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0013
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.SubAddEqZeroOfEqAdd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSpMapQuotientSpanBaseChange
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotBaseChange

theorem isPushout_quot_span (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R)
    (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f})
    (hρ : ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π) :
    IsPushout (CommRingCat.ofHom π) (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π f}))) (CommRingCat.ofHom ρ) := by
  refine ⟨⟨by ext a; exact (congr($hρ a)).symm⟩, ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift (Ideal.span {π f}) s.inl.hom ?_)) ?_ ?_ ?_⟩⟩
  · intro b hb
    have e : ∀ a, s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := fun a => congr($(s.condition) a)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [map_mul, e, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f), map_zero, mul_zero]
  · intro s
    ext b
    rfl
  · intro s
    ext a
    have e : s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := congr($(s.condition) a)
    have e2 : ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (π a) := congr($hρ a)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [e2, Ideal.Quotient.lift_mk, e]
  · intro s m h₁ _
    ext b
    have e : m.hom (Ideal.Quotient.mk _ b) = s.inl.hom b := congr($h₁ b)
    exact e

theorem isPullback_spMap_quot : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π → IsPullback (spMap (Ideal.Quotient.mk (Ideal.span {π f}))) (spMap ρ) (spMap π) (spMap (Ideal.Quotient.mk (Ideal.span {f}))) := by
  intro R R₀ _ _ π f ρ hρ
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot_span R R₀ π f ρ hρ)

end GlobalTheory.QuotBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

section LocalizationBaseChange

variable {R R' C' L ν σ : Type} [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R')
  [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C')

theorem localization_baseChange_ext (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (w₁ w₂ : L →+* T)
    (h₁ : ∀ r : R', w₁ (algebraMap C' L (algebraMap R' C' r)) = w₂ (algebraMap C' L (algebraMap R' C' r)))
    (h₂ : ∀ i, w₁ (algebraMap C' L (ξ i)) = w₂ (algebraMap C' L (ξ i))) : w₁ = w₂ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.aeval ξ (MvPolynomial.map a h)))
  refine RingHom.ext fun c => ?_
  obtain ⟨P, rfl⟩ := hsurj c
  have e : w₁.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) =
      w₂.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa using h₁ r
    · intro i
      simpa using h₂ i
  exact congr($e P)

theorem localization_baseChange_desc (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    (hker : ∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 →
      MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (u : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* T) (v : R' →+* T)
    (huv : ∀ r : R, u (algebraMap R _ r) = v (a r)) :
    ∃ w : L →+* T, (∀ G : MvPolynomial ν R, w (algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G))) =
        u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G))) ∧
      ∀ r : R', w (algebraMap C' L (algebraMap R' C' r)) = v r := by
  let θ : MvPolynomial ν R' →+* T := MvPolynomial.eval₂Hom v (fun i ↦
    u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.X i))))
  have hθ : θ.comp (MvPolynomial.map a) = u.comp ((algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F))
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))).comp (Ideal.Quotient.mk _)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.map_C, θ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [← huv]
      rfl
    · intro i
      simp [θ]
  have hθ' : ∀ G, θ (MvPolynomial.map a G) =
      u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) :=
    fun G ↦ congr($hθ G)
  have hunit : IsUnit (θ (MvPolynomial.map a h)) := by
    rw [hθ']
    exact (IsLocalization.Away.algebraMap_isUnit _).map u
  have hspan : Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ≤ RingHom.ker θ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hθ', (Ideal.Quotient.eq_zero_iff_mem (a := F s) (I := Ideal.span (Set.range F))).2 (Ideal.subset_span ⟨s, rfl⟩),
      map_zero, map_zero]
  have hk : RingHom.ker (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom ≤ RingHom.ker θ := by
    intro G hG
    rw [RingHom.mem_ker] at hG
    have e := RingHom.mem_ker.1 (hspan (hker G hG))
    rw [map_mul] at e
    exact RingHom.mem_ker.2 ((hunit.mul_right_eq_zero).1 e)
  let θ' : C' →+* T := (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.liftOfRightInverse
    (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨θ, hk⟩
  have hθ'e : ∀ P, θ' (MvPolynomial.aeval ξ P) = θ P := fun P ↦
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ P
  have hu2 : IsUnit (θ' (MvPolynomial.aeval ξ (MvPolynomial.map a h))) := by
    rw [hθ'e]
    exact hunit
  refine ⟨IsLocalization.Away.lift (MvPolynomial.aeval ξ (MvPolynomial.map a h)) hu2, fun G ↦ ?_, fun r ↦ ?_⟩
  · rw [IsLocalization.Away.lift_eq, hθ'e, hθ']
  · rw [IsLocalization.Away.lift_eq, ← MvPolynomial.aeval_C (R := R') ξ r, hθ'e]
    simp [θ]

end LocalizationBaseChange

theorem isPushout_localization_baseChange : ∀ (R R' C' L ν σ : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R') [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C'), Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → (∀ s, MvPolynomial.aeval ξ (MvPolynomial.map a (F s)) = 0) → (∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 → MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s))) → IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L → ∃ α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L, IsPushout (CommRingCat.ofHom (algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)))) (CommRingCat.ofHom a) (CommRingCat.ofHom α) (CommRingCat.ofHom ((algebraMap C' L).comp (algebraMap R' C'))) ∧ ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := by
  intro R R' C' L ν σ _ _ _ _ a _ _ F h ξ hsurj hF hker hL
  have hI : Ideal.span (Set.range F) ≤
      RingHom.ker ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a)) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    exact RingHom.mem_ker.2 (hF s)
  let β := Ideal.Quotient.lift (Ideal.span (Set.range F))
    ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a))
    (fun x hx ↦ RingHom.mem_ker.1 (hI hx))
  have hβ : ∀ G, β (Ideal.Quotient.mk _ G) = MvPolynomial.aeval ξ (MvPolynomial.map a G) := fun G ↦ rfl
  have hu : IsUnit (((algebraMap C' L).comp β) (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
    rw [RingHom.comp_apply, hβ]
    exact IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L :=
    IsLocalization.Away.lift (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) hu
  have hα : ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _
      (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := fun G ↦ by
    simp only [α]
    rw [IsLocalization.Away.lift_eq, RingHom.comp_apply, hβ]
  have hR : ∀ r : R, algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) r =
      algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.C r)) :=
    fun r ↦ rfl
  refine ⟨α, IsPushout.of_isColimit' ⟨?_⟩ (PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (Classical.choose (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r))))) ?_ ?_ ?_), hα⟩
  · ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [hR, hα]
    simp
  · intro s
    obtain ⟨hd1, -⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun G ↦ ?_
    simp only [RingHom.comp_apply]
    rw [hα, hd1]
  · intro s
    obtain ⟨-, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact hd2 r
  · intro s m h₁ h₂
    obtain ⟨hd1, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_ofHom]
    apply localization_baseChange_ext a h ξ hsurj
    · intro r
      rw [hd2]
      exact congr($h₂ r)
    · intro i
      have e : algebraMap C' L (ξ i) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a (MvPolynomial.X i))) := by
        simp
      rw [e, hd1, ← hα]
      exact congr($h₁ _)

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiAffineCartierSectionGeneratingLocusAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.LocusQA

open GlobalTheory.Cartier.CartierDiv

variable {Y : Scheme.{0}} [IsIntegral Y] {y : Y}

theorem regAt_pow {f : Y.functionField} (hf : RegAt y f) (n : ℕ) : RegAt y (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem unitAt_pow_iff {f : Y.functionField} (hf : RegAt y f) {n : ℕ} (hn : n ≠ 0) :
    UnitAt y (f ^ n) ↔ UnitAt y f := by
  obtain ⟨a, rfl⟩ := hf
  refine ⟨fun ⟨b, hb, e⟩ => ?_, fun ⟨b, hb, e⟩ => ⟨b ^ n, hb.pow n, by rw [map_pow, e]⟩⟩
  rw [← map_pow] at e
  obtain rfl := IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField e
  exact ⟨a, (isUnit_pow_iff hn).1 hb, rfl⟩

theorem regAt_div {f g : Y.functionField} (hf : RegAt y f) (hg : UnitAt y g) : RegAt y (f / g) := by
  rw [div_eq_mul_inv]; exact hf.mul hg.inv.regAt

theorem unitAt_div_iff {f g : Y.functionField} (hg : UnitAt y g) : UnitAt y (f / g) ↔ UnitAt y f := by
  refine ⟨fun h => ?_, fun h => by rw [div_eq_mul_inv]; exact h.mul hg.inv⟩
  have := h.mul hg
  rwa [div_mul_cancel₀ _ hg.ne_zero] at this

theorem pow_div_pow_eqn {K : Type} [Field K] (a b c : K) (hc : c ≠ 0) (m n : ℕ) :
    (a * c ^ m) ^ n / (b * c ^ n) ^ m = a ^ n / b ^ m := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m n, mul_div_mul_right _ _ (pow_ne_zero _ hc)]

theorem isQuasiAffine_locus : ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (D : CartierDiv Y), AmpleDiv D → ∀ (k : ℕ), 1 ≤ k → ∀ s ∈ Sec D k, ∀ V : Y.Opens,
    (V : Set Y) = locus D k s → V.toScheme.IsQuasiAffine := by
  intro Y _ _ _ D hD k hk s hs V hV
  have memV : ∀ y, y ∈ V ↔ (k • D).GeneratesAt y s := fun y => by
    rw [← SetLike.mem_coe, hV]; rfl
  have loc : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (s * (e : Y.functionField) ^ k) ∧ (y ∈ V ↔ UnitAt y (s * (e : Y.functionField) ^ k)) := by
    intro y e he
    have h := he.nsmul k
    have h1 := h.regularAt_iff.1 (hs y)
    have h2 := (memV y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have stepC : ∀ k', 1 ≤ k' → ∀ u ∈ Sec D k', ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y) = locus D k' u →
      IsAffineOpen (V ⊓ U) := by
    intro k' hk' u hu U hUa hUl
    have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
      rw [← SetLike.mem_coe, hUl]; rfl
    have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
        (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
      intro y e he
      have h := he.nsmul k'
      have h2 := (memU y).trans h.generatesAt_iff
      rw [Units.val_pow_eq_pow_val] at h2
      exact h2
    by_cases hg : genericPoint Y ∈ U
    swap
    · have : U = ⊥ := eq_bot_iff.2 fun y hy => (hg (gen_mem hy)).elim
      rw [this, inf_bot_eq]
      exact isAffineOpen_bot Y
    have hreg : ∀ y ∈ U, RegAt y (s ^ k' / u ^ k) := by
      intro y hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hB := (locU y e he).1 hy
      rw [← pow_div_pow_eqn s u _ e.ne_zero k k']
      exact regAt_div (regAt_pow (loc y e he).1 _) ((unitAt_pow_iff hB.regAt (by omega)).2 hB)
    obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
    have e₁ : V ⊓ U = Y.basicOpen a := by
      ext y
      refine ⟨fun ⟨hyV, hyU⟩ => ?_, fun hy => ?_⟩
      · obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        refine (unitAt_fnOf_iff hyU hg a).1 ?_
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)]
        exact (loc y e he).2.1 hyV
      · have hyU : y ∈ U := Y.basicOpen_le a hy
        obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        have h := (unitAt_fnOf_iff hyU hg a).2 hy
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)] at h
        exact ⟨(loc y e he).2.2 h, hyU⟩
    rw [e₁]
    exact hUa.basicOpen a
  have : CompactSpace V := by
    choose kk hkk u hu U hUa hUl hxU using hD
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set Y)) (fun y => (U y).isOpen)
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxU y⟩)
    have e : (V : Set Y) = ⋃ y ∈ t, ((V ⊓ U y : Y.Opens) : Set Y) := by
      refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun y _ => fun z hz => hz.1)
      obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
      exact Set.mem_iUnion₂.2 ⟨y, hy, hz, hzy⟩
    have hc : IsCompact (V : Set Y) := e ▸ t.isCompact_biUnion fun y _ =>
      (stepC (kk y) (hkk y) (u y) (hu y) (U y) (hUa y) (hUl y)).isCompact
    exact isCompact_iff_compactSpace.mp hc
  have : CompactSpace V.toScheme := inferInstanceAs (CompactSpace V)
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen _ fun x => ?_
  obtain ⟨k', hk', u, hu, U, hUa, hUl, hxU⟩ := hD x.1
  have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
    rw [← SetLike.mem_coe, hUl]; rfl
  have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (u * (e : Y.functionField) ^ k') ∧ (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
    intro y e he
    have h := he.nsmul k'
    have h1 := h.regularAt_iff.1 (hu y)
    have h2 := (memU y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have hg : genericPoint Y ∈ V := gen_mem x.2
  have hreg : ∀ y ∈ V, RegAt y (u ^ k / s ^ k') := by
    intro y hy
    obtain ⟨e, he⟩ := D.exists_isEqn y
    have hA := (loc y e he).2.1 hy
    rw [← pow_div_pow_eqn u s _ e.ne_zero k' k]
    exact regAt_div (regAt_pow (locU y e he).1 _) ((unitAt_pow_iff hA.regAt (by omega)).2 hA)
  obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
  have e₁ : Y.basicOpen a = V ⊓ U := by
    ext y
    refine ⟨fun hy => ?_, fun ⟨hyV, hyU⟩ => ?_⟩
    · have hyV : y ∈ V := Y.basicOpen_le a hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      have h := (unitAt_fnOf_iff hyV hg a).2 hy
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)] at h
      exact ⟨hyV, (locU y e he).2.2 h⟩
    · obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      refine (unitAt_fnOf_iff hyV hg a).1 ?_
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)]
      exact (locU y e he).2.1 hyU
  have him := Scheme.Opens.ι_image_basicOpen_topIso_inv (U := V) a
  rw [e₁] at him
  refine ⟨V.topIso.inv a, ?_, ?_⟩
  · rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, him]
    exact stepC k' hk' u hu U hUa hUl
  · have hm : V.ι x ∈ V.ι ''ᵁ V.toScheme.basicOpen (V.topIso.inv a) := by
      rw [him]; exact ⟨x.2, hxU⟩
    obtain ⟨z, hz, hzx⟩ := hm
    rwa [V.ι.isOpenEmbedding.injective hzx] at hz

end GlobalTheory.Desc.LocusQA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiProjectiveOfFiniteOverCyclotomicAwayPullb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayQProj

theorem finiteType_closure {K : Type} [CommRing K] {s : Set K} (hs : s.Finite) :
    (Int.castRingHom (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have e : Algebra.adjoin ℤ s ≃+* Subring.closure s :=
    RingEquiv.subringCongr (s := (Algebra.adjoin ℤ s).toSubring) (by rw [Algebra.adjoin_int]; rfl)
  have h' : Algebra.FiniteType ℤ (Subring.closure s) := h.equiv (AlgEquiv.ofRingEquiv (f := e) fun x => by simp)
  have := RingHom.finiteType_algebraMap.2 h'
  rwa [RingHom.eq_intCast' (algebraMap ℤ (Subring.closure s))] at this

theorem finiteType_cycAway (M : ℕ) : (Int.castRingHom (cycAway M)).FiniteType :=
  finiteType_closure (Set.toFinite _)

theorem isQProjOver_comp_spMap {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.FiniteType)
    {Y : Scheme.{0}} {s : Y ⟶ Sp B} (h : IsQProjOver s) : IsQProjOver (s ≫ spMap f) := by
  obtain ⟨_, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  have : LocallyOfFiniteType (spMap f) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hf
  exact (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB _).2 ⟨inferInstance, hL⟩

theorem isQProjOver_of_isFinite_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) :=
  fun M _ _ _ _ _ _ hs _ π _ =>
    isQProjOver_comp_of_isFinite π
      (isQProjOver_of_isPullback (IsPullback.of_hasPullback _ _) (isQProjOver_comp_spMap (finiteType_cycAway M) hs))

end GlobalTheory.CycAwayQProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRadicalSpanProdRelativeRegularParameters
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelParamRad

theorem prod_dvd_of_forall_dvd {R : Type} [CommMonoidWithZero R] :
    ∀ (m : ℕ) (t : Fin m → R), (∀ k, Prime (t k)) → (∀ i j, t i ∣ t j → i = j) →
      ∀ x : R, (∀ k, t k ∣ x) → ∏ k, t k ∣ x := by
  intro m
  induction m with
  | zero => intro t _ _ x _; simp
  | succ m ih =>
    intro t hp hd x hx
    obtain ⟨y, rfl⟩ := hx 0
    rw [Fin.prod_univ_succ]
    refine mul_dvd_mul_left _ (ih (fun k => t k.succ) (fun k => hp _) (fun i j h => Fin.succ_injective _ (hd _ _ h)) y
      fun k => ?_)
    refine ((hp k.succ).dvd_or_dvd (hx k.succ)).resolve_left fun h => ?_
    exact Fin.succ_ne_zero k (hd _ _ h)

theorem isRadical_span_prod : ∀ (o R : Type) [CommRing o] [CommRing R] [IsRegularLocalRing R] [IsDomain R] (b : o →+* R)
    (m : ℕ) (t : Fin m → R), IsRelParam b t → (Ideal.span {∏ k, t k}).IsRadical := by
  intro o R _ _ _ _ b m t h
  have hp : ∀ k, Prime (t k) := fun k => prime_of_not_mem_sq (h.1 k) (h.notMem_sq k)
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  exact prod_dvd_of_forall_dvd m t hp (fun i j hij => h.eq_of_dvd hij) x
    fun k => (hp k).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem t (Finset.mem_univ k)).trans hn)

end GlobalTheory.RelParamRad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricRigidifiedBundleBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyVals

theorem isSymmetric_bL : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    L.IsSymmetric → (KeyVals.bL L ξ).IsSymmetric :=
  fun _ G _ _ L _ _ ξ h =>
    CubePf.sym_pull (cubeMapOf (isGrpPullback_pullback G ξ)) L (bL L ξ).isLB (bL L ξ).rigGen h

end GlobalTheory.KeyVals
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

def IsogTarget {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) (c : ℕ) {L : Type} [Field L] (ξ ζ : Sp L ⟶ M.X) : Prop :=
  ξ ≫ M.s = ζ ≫ M.s ∧ ∃ (o o' : Obj b N (ξ ≫ M.s)) (ψ : o.A ⟶ o'.A),
    Nonempty (ObjMap o M.univ ξ) ∧ Nonempty (ObjMap o' M.univ ζ) ∧ IsPIsog c o o' ψ

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

