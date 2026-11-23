module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.HermitianLattices.TraceFormBilinSeparatingLeftIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsFiniteUnitaryClassesOfDualEqSmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsChartWithParameters
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.RelChart

open GlobalTheory.TangentOrigin

theorem evalPt_appLE {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV ((φ.appLE U V e).hom f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem top_le_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ φ ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage]
  exact fun _ hp => e (hV hp)

theorem dual_ext {P R : Type} [CommRing P] [CommRing R] (ψ : P →+* R) (hψ : ψ.Etale)
    (F F' : R →+* DualNumber ℂ) (h : ∀ a, F (ψ a) = F' (ψ a)) (h0 : ∀ r, fstC (F r) = fstC (F' r)) : F = F' := by
  let _ := ψ.toAlgebra
  let _ : Algebra P (DualNumber ℂ) := (F'.comp ψ).toAlgebra
  have _ : Algebra.Etale P R := hψ
  let G : R →ₐ[P] DualNumber ℂ := { F with commutes' := h }
  let G₀ : R →ₐ[P] DualNumber ℂ := { F' with commutes' := fun _ => rfl }
  have hnil : IsNilpotent (RingHom.ker fstC) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' fstC hnil G G₀ h0
  exact RingHom.ext fun r => AlgHom.congr_fun hG r

theorem exists_chart_with_parameters :
    (∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x) → (∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') := by
  classical
  intro hring m g Z X p B y b₀ z₀ hp hB hb₀ hy hz₀
  obtain ⟨V, hV, U, hU, hz, hle, hsm⟩ :=
    hp.exists_isStandardSmoothOfRelativeDimension (z₀ (default : PrimeSpectrum ℂ))
  obtain ⟨ψ, hψC, hψ⟩ := hsm.exists_etale_mvPolynomial
  have hC : ∀ a, ψ (MvPolynomial.C a) = (p.appLE V U hle).hom a := fun a => RingHom.congr_fun hψC a
  have hzU : ⊤ ≤ z₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem z₀ U).2 hz
  have hy₀ : ⊤ ≤ y b₀ ⁻¹ᵁ V := hz₀ ▸ top_le_comp z₀ p hle hzU
  let φ : (Fin m → ℂ) → (Γ(X, V) →+* ℂ) := fun b =>
    if h : ⊤ ≤ y b ⁻¹ᵁ V then evalPt (y b) V h else evalPt (y b₀) V hy₀
  have hφ : ∀ b, ⊤ ≤ y b ⁻¹ᵁ V → ∀ a, φ b a = valAt' (y b) V a := fun b h a => by
    simp only [φ, dif_pos h, valAt'_eq_evalPt _ _ h]
  have hover : ∀ b (x : Sp ℂ ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = y b →
      ∀ a, evalPt x U hx (ψ (MvPolynomial.C a)) = φ b a := fun b x hx hxb a => by
    rw [hφ b (hxb ▸ top_le_comp x p hle hx), hC, ← valAt'_eq_evalPt, valAt'_appLE _ _ _ _ _ _ hx, hxb]
  obtain ⟨N, σ, n, f, O, hN, hO, h₀, hσd, hσ, hrec⟩ := hring m g Γ(X, V) Γ(Z, U) ψ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ V} φ b₀
    (evalPt z₀ U hzU) hψ (hy V 0).1 ⟨hb₀, hy₀⟩
    (fun a => (hy V a).2.congr fun b hb => hφ b hb.2 a) (hover b₀ z₀ hzU hz₀)
  choose s hsU hs using fun q => exists_evalPt_eq hU (σ q)
  have hval : ∀ q a, valAt' (s q) U a = σ q a := fun q a => by
    rw [valAt'_eq_evalPt _ _ (hsU q), hs]
  refine ⟨U, fun i => ψ (MvPolynomial.X i), n, f, N, O, s, hN, hO, hzU, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [valAt'_eq_evalPt _ _ hzU] using h₀
  · intro W a
    refine holFamily_of_affine valAt'_rules N Z s (fun q _ => ⟨U, hU, hsU q, ?_, fun r => ?_⟩) W a
    · simp only [hsU, and_true]
      exact hN
    · simp only [hsU, and_true, hval]
      exact hσd r
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hσ q hq
    refine ⟨ext_evalPt hV (top_le_comp _ p hle (hsU q)) h1.2 (RingHom.ext fun a => ?_), hsU q,
      fun i => (hval _ _).trans (h3 i)⟩
    rw [← evalPt_appLE _ p V U hle a (hsU q), hs, ← hC, h2, hφ _ h1.2, valAt'_eq_evalPt]
  · intro b x hxb hx hxO
    simp only [valAt'_eq_evalPt _ _ hx] at hxO ⊢
    obtain ⟨h1, h2⟩ := hrec b (evalPt x U hx) (hover b x hx hxb) hxO
    exact ⟨h1, ext_evalPt hU (hsU _) hx ((hs _).trans h2)⟩
  · intro v v' h h' hvp hv0 hvt
    refine ext_evalPt hU h h' (dual_ext ψ hψ _ _ (fun a => ?_) fun r => ?_)
    · have : (evalPt v U h).comp ψ = (evalPt v' U h').comp ψ := by
        refine MvPolynomial.ringHom_ext (fun c => ?_) hvt
        simp only [RingHom.comp_apply, hC]
        rw [evalPt_appLE v p V U hle c h (top_le_comp v p hle h),
          evalPt_appLE v' p V U hle c h' (top_le_comp v' p hle h')]
        simp only [hvp]
      exact RingHom.congr_fun this a
    · rw [← evalPt_spMap_comp fstC v U h ((top_le_preimage_iff v U).1 h),
        ← evalPt_spMap_comp fstC v' U h' ((top_le_preimage_iff v' U).1 h')]
      have hv0' : spMap fstC ≫ v = spMap fstC ≫ v' := hv0
      simp only [hv0']

end GlobalTheory.RelChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingOfHomogeneousKerEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_hom_of_ker_eq {P L M : Type} [CommRing P] [Field L] [Field M]
    (Φ : P →+* L) (Ψ : P →+* M) (h : RingHom.ker Φ = RingHom.ker Ψ) :
    ∃ (S : Subfield L) (e : S →+* M), ∃ hS : ∀ p, Φ p ∈ S, ∀ p, e ⟨Φ p, hS p⟩ = Ψ p := by
  haveI : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime Φ
  let Q := P ⧸ RingHom.ker Φ
  let f1 : Q →+* L := RingHom.kerLift Φ
  have hf1 : Function.Injective f1 := RingHom.kerLift_injective Φ
  let f2 : Q →+* M := Ideal.Quotient.lift _ Ψ (fun a ha => by
    rw [h] at ha; exact ha)
  have hf2 : Function.Injective f2 :=
    RingHom.lift_injective_of_ker_le_ideal _ _ h.ge
  let i1 : FractionRing Q →+* L := IsFractionRing.lift hf1
  let i2 : FractionRing Q →+* M := IsFractionRing.lift hf2
  have h1 : ∀ p, i1 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Φ p := fun p => by
    simp only [i1, IsFractionRing.lift_algebraMap]
    exact RingHom.kerLift_mk Φ p
  have h2 : ∀ p, i2 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Ψ p := fun p => by
    simp only [i2, IsFractionRing.lift_algebraMap]
    rfl
  refine ⟨i1.fieldRange, i2.comp i1.rangeRestrictFieldEquiv.symm.toRingHom,
    fun p => ⟨_, h1 p⟩, fun p => ?_⟩
  have : i1.rangeRestrictFieldEquiv.symm ⟨Φ p, ⟨_, h1 p⟩⟩
      = algebraMap Q _ (Ideal.Quotient.mk _ p) := by
    rw [RingEquiv.symm_apply_eq]
    exact Subtype.ext (h1 p).symm
  rw [← h2 p, ← this]
  rfl

theorem exists_embedding_of_homogeneous_ker_eq :
    ∀ (o K σ : Type) [CommRing o] [Field K] (β : o →+* K) (em : o →+* ℂ) (u : σ → K) (w : σ → ℂ) (a₀ : σ), u a₀ ≠ 0 → Subfield.closure (Set.range β ∪ Set.range (fun a => u a / u a₀)) = ⊤ → RingHom.ker (MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X)) = RingHom.ker (MvPolynomial.eval₂Hom em w) → ∃ (e : K →+* ℂ) (c : ℂ), c ≠ 0 ∧ e.comp β = em ∧ ∀ a, e (u a) = c * w a := by
  intro o K σ _ _ β em u w a₀ hu hcl hker
  let i0 : Polynomial K →+* RatFunc K := algebraMap _ _
  have hi0 : Function.Injective i0 := IsFractionRing.injective _ _
  set Φ₀ := MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
    (fun a => Polynomial.C (u a) * Polynomial.X) with hΦ₀
  have hk : RingHom.ker (i0.comp Φ₀) = RingHom.ker (MvPolynomial.eval₂Hom em w) := by
    rw [← hker]
    ext p
    simp only [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff i0 hi0]
  obtain ⟨S, e, hS, he⟩ := exists_hom_of_ker_eq _ _ hk
  let j : K →+* RatFunc K := i0.comp Polynomial.C
  have hC : ∀ r, (i0.comp Φ₀) (MvPolynomial.C r) = j (β r) := fun r => by
    simp [hΦ₀, j]
  have hX : ∀ a, (i0.comp Φ₀) (MvPolynomial.X a) = j (u a) * i0 Polynomial.X := fun a => by
    simp [hΦ₀, j]
  have hT : i0 Polynomial.X ≠ 0 := (map_ne_zero_iff i0 hi0).2 Polynomial.X_ne_zero
  have hdiv : ∀ a, j (u a / u a₀)
      = (i0.comp Φ₀) (MvPolynomial.X a) / (i0.comp Φ₀) (MvPolynomial.X a₀) := fun a => by
    rw [hX, hX, map_div₀, mul_div_mul_right _ _ hT]
  have hj : ∀ x, j x ∈ S := by
    have : (⊤ : Subfield K) ≤ S.comap j := by
      rw [← hcl, Subfield.closure_le]
      rintro x (⟨r, rfl⟩ | ⟨a, rfl⟩)
      · show j (β r) ∈ S
        rw [← hC]; exact hS _
      · show j (u a / u a₀) ∈ S
        rw [hdiv]; exact S.div_mem (hS _) (hS _)
    exact fun x => this (Subfield.mem_top x)
  let e' : K →+* ℂ := e.comp (j.codRestrict S hj)
  have hw : w a₀ ≠ 0 := by
    intro h0
    have : MvPolynomial.X a₀ ∈ RingHom.ker (i0.comp Φ₀) := by
      rw [hk, RingHom.mem_ker]; simpa using h0
    rw [RingHom.mem_ker, hX] at this
    exact mul_ne_zero ((map_ne_zero j).2 hu) hT this
  have hr : ∀ a, e' (u a / u a₀) = w a / w a₀ := fun a => by
    have h1 := he (MvPolynomial.X a)
    have h2 := he (MvPolynomial.X a₀)
    rw [MvPolynomial.eval₂Hom_X'] at h1 h2
    rw [← h1, ← h2, ← map_div₀]
    exact congrArg e (Subtype.ext (hdiv a))
  have he0 : e' (u a₀) ≠ 0 := (map_ne_zero e').2 hu
  refine ⟨e', e' (u a₀) / w a₀, div_ne_zero he0 hw, ?_, fun a => ?_⟩
  · ext r
    have h1 := he (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C] at h1
    rw [← h1]
    exact congrArg e (Subtype.ext (hC r).symm)
  · have h := hr a
    rw [map_div₀, div_eq_iff he0] at h
    rw [h]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFieldPullbackAppTopBijectiveAndTriv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.GeomFibre

theorem bijective_appTop (K : Type) [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper f] : Function.Bijective f.appTop.hom := by
  have hfin : f.appTop.hom.Finite := finite_appTop_of_universallyClosed K f
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e
  have hfin' : (f.appTop.hom.comp e.hom).Finite := hfin.comp (RingHom.Finite.of_surjective _ he.2)
  have hb : Function.Bijective (f.appTop.hom.comp e.hom) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral (k := K) _ hfin'.to_isIntegral
  exact (Function.Bijective.of_comp_iff _ he).1 hb

theorem exists_field_pullback_appTop_bijective_and_triv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → IsProper f → GeometricallyIntegral f → ∀ (K : Type) [Field K] (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → Triv (M.pull π) → ∃ (K₀ : Type) (_ : Field K₀) (g₀ : R →+* K₀) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K₀)), RingHom.ker g₀ = RingHom.ker g ∧ IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) ∧ Function.Bijective f₀.appTop.hom ∧ Triv (M.pull π₀) := by
  intro R _ X f M _ _ _ K _ g X' π f' h ⟨t, ht⟩
  let a : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have h₁ := IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom a))
  have h₂ : IsPullback (pullback.fst f' (Spec.map (CommRingCat.ofHom a)) ≫ π)
      (pullback.snd f' (Spec.map (CommRingCat.ofHom a))) f (Spec.map (CommRingCat.ofHom (a.comp g))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact h₁.paste_horiz h
  have : IsIntegral (pullback f' (Spec.map (CommRingCat.ofHom a))) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ h₂
  have : IsProper (pullback.snd f' (Spec.map (CommRingCat.ofHom a))) :=
    MorphismProperty.of_isPullback (P := @IsProper) h₂ inferInstance
  refine ⟨AlgebraicClosure K, inferInstance, a.comp g, _, _, _, RingHom.ker_comp_of_injective g a.injective,
    h₂, bijective_appTop _ _, ?_⟩
  exact ⟨_, LB.isGen_pullGen M _ _ t ht _⟩

end GlobalTheory.GeomFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteClassesOfTraceFormDualEq
section
namespace GlobalTheory.DatumClasses

section Varying

open Module Submodule NumberField GlobalTheory.HermClass

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_finite_classes_of_forms {V : Type} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {α : Type*}
    (h : α → V →ₗ[E] V →ₗ⋆[E] E) (hs : ∀ a x y, h a y x = star (h a x y))
    (hnd : ∀ a y, (∀ x, h a y x = 0) → y = 0) {N : ℤ} (hN : N ≠ 0)
    (Λ : α → Submodule ℤ V)
    (hfg : ∀ a, (Λ a).FG) (hsp : ∀ a, span E (Λ a : Set V) = ⊤)
    (hO : ∀ a, ∀ c : E, IsIntegral ℤ c → ∀ x ∈ Λ a, c • x ∈ Λ a)
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ (h a x y))
    (hdual : ∀ a y, (∀ x ∈ Λ a, IsIntegral ℤ (h a y x)) → (N : E) • y ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : V ≃ₗ[E] V, (∀ x y, h s (γ x) (γ y) = h a x y) ∧
      ∀ x, x ∈ Λ a ↔ γ x ∈ Λ s := by
  classical
  set n := finrank E V with hn
  obtain ⟨D, hD, hD0, H⟩ := exists_finite_orthogonal_lengths (E := E) n hN
  obtain ⟨M, hM, hMD⟩ := exists_int_mul_isIntegral E (hD.image fun a => a⁻¹)
  choose v hvΛ hvo hvD using fun a =>
    H V (h a) (Λ a) rfl (hs a) (hnd a) (hfg a) (hsp a) (hO a) (hint a) (hdual a)
  have hv0 : ∀ a i, h a (v a i) (v a i) ≠ 0 := fun a i h0 => hD0 (h0 ▸ hvD a i)
  have hsum : ∀ a (c : Fin n → E) j,
      h a (∑ i, c i • v a i) (v a j) = c j * h a (v a j) (v a j) := by
    intro a c j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hvo a i j hij]
    · simp
  have hli : ∀ a, LinearIndependent E (v a) := fun a => Fintype.linearIndependent_iff.2
    fun c hc j => by
      have := hsum a c j
      rw [hc, map_zero, LinearMap.zero_apply] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (hv0 a j)
  let B : α → Basis (Fin n) E V := fun a =>
    basisOfLinearIndependentOfCardEqFinrank' (v a) (hli a) (by simp [hn])
  have hB : ∀ a i, B a i = v a i := fun a i => by simp [B]
  let φ : α → V ≃ₗ[E] (Fin n → E) := fun a => (B a).equivFun
  have hφ : ∀ a c, (φ a).symm c = ∑ i, c i • v a i := fun a c => by
    simp [φ, Basis.equivFun_symm_apply, hB]
  have hform : ∀ a c c', h a ((φ a).symm c) ((φ a).symm c') =
      ∑ j, star (c' j) * (c j * h a (v a j) (v a j)) := fun a c c' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, hφ, map_sum (h a _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulₛₗ, hsum, starRingEnd_apply, smul_eq_mul]
  let L : α → Submodule ℤ (Fin n → E) := fun a => (Λ a).map ((φ a).toLinearMap.restrictScalars ℤ)
  have hL : ∀ a c, c ∈ L a ↔ (φ a).symm c ∈ Λ a := fun a c =>
    ⟨by rintro ⟨x, hx, rfl⟩; simpa using hx, fun hc => ⟨_, hc, by simp⟩⟩
  let L₀ : Submodule ℤ (Fin n → E) :=
    Submodule.pi Set.univ fun _ => Subalgebra.toSubmodule (integralClosure ℤ E)
  have hL₀ : L₀.FG := Submodule.fg_pi fun _ => fg_integers E
  have hLF : ∀ a, L₀ ≤ L a ∧ ∀ x ∈ L a, (M : E) • x ∈ L₀ := fun a => by
    refine ⟨fun c hc => ?_, fun c hc j _ => ?_⟩
    · rw [hL, hφ]
      exact sum_mem fun i _ => hO a _ (hc i trivial) _ (hvΛ a i)
    · have h1 := hint a _ ((hL a c).1 hc) _ (hvΛ a j)
      rw [hφ, hsum] at h1
      have h2 := (hMD _ ⟨_, hvD a j, rfl⟩).mul h1
      change IsIntegral ℤ ((M : E) * c j)
      rwa [mul_mul_mul_comm, inv_mul_cancel₀ (hv0 a j), mul_one] at h2
  have hF := finite_between (E := E) L₀ hL₀ hM
  obtain ⟨S, hS, hSa⟩ := exists_finite_representatives
    (fun a => ((fun i => h a (v a i) (v a i), L a) :
      (Fin n → E) × Submodule ℤ (Fin n → E))) (by
    refine ((Set.Finite.pi' fun _ : Fin n => hD).prod hF).subset ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨hvD a, hLF a⟩)
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hs, he⟩ := hSa a
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  refine ⟨s, hs, (φ a).trans (φ s).symm, fun x x' => ?_, fun x => ?_⟩
  · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hform]
    conv_rhs => rw [← (φ a).symm_apply_apply x, ← (φ a).symm_apply_apply x', hform]
    exact Finset.sum_congr rfl fun j _ => by rw [congrFun h1 j]
  · rw [LinearEquiv.trans_apply, ← hL, h2, hL, LinearEquiv.symm_apply_apply]

end Varying

section Matrices

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_finite_classes_of_traceFormDual_eq {α : Type*} {ξ0 : E} (h0 : ξ0 ≠ 0)
    (G : α → Matrix (Fin r) (Fin r) E) (hG : ∀ s a b, cc (G s a b) = G s b a)
    (hdet : ∀ s, (G s).det ≠ 0) (Λ : α → Submodule (𝓞 E) (Fin r → E))
    (hΛ : ∀ s, IsLattice (Λ s)) (hself : ∀ s, traceFormDual ξ0 (G s) (Λ s) = Λ s) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : (Fin r → E) ≃ₗ[E] (Fin r → E),
      (∀ x y, herm (G s) (γ x) (γ y) = herm (G a) x y) ∧ ∀ x, x ∈ Λ a ↔ γ x ∈ Λ s := by
  classical
  have hc : ∀ x : E, cc x = star x := fun _ => rfl
  obtain ⟨D, hD, hDa⟩ := HermClass.exists_int_mul_isIntegral_of_trace E
  obtain ⟨M, hM, hMa⟩ := HermClass.exists_int_mul_isIntegral E (Set.toFinite {-ξ0, (-ξ0)⁻¹})
  have hN : M * D ≠ 0 := mul_ne_zero hM hD
  have hN' : ((M * D : ℤ) : E) ≠ 0 := by exact_mod_cast hN
  choose h hh using fun s => exists_sesquilinear_eq_herm (G s)
  have hs : ∀ s x y, h s y x = star (h s x y) := fun s x y => by
    rw [hh, hh, ← hc, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_conj (G s) (hG s)]
  have hnd : ∀ s y, (∀ x, h s y x = 0) → y = 0 := fun s y hy =>
    ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.eq_zero_of_herm (G s) (hdet s) y fun x => by rw [← hh, hy]
  obtain ⟨S, hS, H⟩ := exists_finite_classes_of_forms (fun s => ((M * D : ℤ) : E) • h s)
    (fun s x y => by simp [hs s x y])
    (fun s y hy => hnd s y fun x => by
      have := hy x
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hN')
    (mul_ne_zero hM hN) (fun a => (Λ a).restrictScalars ℤ)
    (fun a => by
      have : Module.Finite (𝓞 E) (Λ a) := Module.Finite.iff_fg.2 (hΛ a).1
      exact Module.Finite.iff_fg.1 (Module.Finite.trans (R := ℤ) (𝓞 E) (Λ a)))
    (fun a => (hΛ a).2) (fun a c hc x hx => (Λ a).smul_mem (⟨c, hc⟩ : 𝓞 E) hx)
    (fun a x hx y hy => by
      have h1 : IsIntegral ℤ ((D : E) * (-ξ0 * herm (G a) x y)) := hDa _ fun t ht => by
        have h2 : t • x ∈ traceFormDual ξ0 (G a) (Λ a) := by
          rw [hself]; exact (Λ a).smul_mem (⟨t, ht⟩ : 𝓞 E) hx
        obtain ⟨k, hk⟩ := mem_traceFormDual.1 h2 y hy
        exact ⟨k, by rw [← hk, EFf_smul_eq_trace, mul_comm]⟩
      have h3 := (hMa _ (Or.inr rfl)).mul h1
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hh]
      have h4 : ((M * D : ℤ) : E) * herm (G a) x y =
          (M : E) * (-ξ0)⁻¹ * ((D : E) * (-ξ0 * herm (G a) x y)) := by
        push_cast; field_simp
      rw [h4]; exact h3)
    (fun a y hy => by
      change _ ∈ Λ a
      rw [← hself, mem_traceFormDual]
      intro x hx
      have h1 := hy x hx
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hh] at h1
      have h2 := (hMa _ (Or.inl rfl)).mul h1
      have h3 := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) h2
      obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
      refine ⟨k, ?_⟩
      rw [EFf_smul_eq_trace, ← eq_intCast (algebraMap ℤ ℚ), hk]
      congr 1
      push_cast; ring)
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hsS, γ, h1, h2⟩ := H a
  refine ⟨s, hsS, γ, fun x y => ?_, h2⟩
  have := h1 x y
  simp only [LinearMap.smul_apply, smul_eq_mul, hh] at this
  exact mul_left_cancel₀ hN' this

end Matrices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem finite_data_of_signature :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ),
      ∃ (n : ℕ) (Di : Fin n → Datum H), (∀ i, (Di i).p = p ∧ (Di i).q = q) ∧
        ∀ D' : Datum H, D'.p = p → D'.q = q →
          ∃ (i : Fin n) (e : D'.La ≃ₗ[𝓞 E] (Di i).La),
            ∀ x y, (Di i).EF (e x) (e y) = D'.EF x y := by
  intro E _ _ _ H p q
  obtain ⟨ξ0, hξ, h0⟩ := FD.exists_imag (E := E)
  let α := {D : Datum H // D.p = p ∧ D.q = q}
  have hemb : ∀ a : α, ∃ φ : a.1.La →ₗ[𝓞 E] (Fin (p + q) → E), IsLatticeEmb φ := by
    rintro ⟨D, rfl, rfl⟩
    exact datum_exists_isLatticeEmb D
  choose φ hφ using hemb
  have spec := fun a : α => datum_gram_spec a.1 (hφ a) h0 hξ
  obtain ⟨S, hS, HS⟩ := exists_finite_classes_of_traceFormDual_eq h0
    (fun a : α => (hφ a).gram ξ0 a.1.EF) (fun a => (spec a).1) (fun a => (spec a).2.1)
    (fun a => LinearMap.range (φ a)) (fun a => (hφ a).2)
    (fun a => (perfect_iff_traceFormDual_eq h0 (spec a).2.1 (hφ a).2).mp (spec a).2.2.2)
  obtain ⟨n, f, hf⟩ := hS.fin_param
  refine ⟨n, fun i => (f i).1, fun i => (f i).2, fun D' hp hq => ?_⟩
  obtain ⟨s, hs, g, h1, h2⟩ := HS ⟨D', hp, hq⟩
  obtain ⟨i, rfl⟩ : s ∈ Set.range f := hf.2 ▸ hs
  set a : α := ⟨D', hp, hq⟩
  have hmap : (LinearMap.range (φ a)).map (g.restrictScalars (𝓞 E)).toLinearMap =
      LinearMap.range (φ (f i)) := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h2 x).1 hx
    · intro hv
      exact ⟨g.symm v, (h2 _).2 (by simpa using hv), by simp⟩
  let e : D'.La ≃ₗ[𝓞 E] (f i).1.La := (LinearEquiv.ofInjective (φ a) (hφ a).1).trans
    (((g.restrictScalars (𝓞 E)).ofSubmodules _ _ hmap).trans
      (LinearEquiv.ofInjective (φ (f i)) (hφ (f i)).1).symm)
  have he : ∀ x, φ (f i) (e x) = g (φ a x) := fun x => by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.ofInjective_symm_apply]
    rfl
  refine ⟨i, e, fun x y => ?_⟩
  have : (((f i).1.EF (e x) (e y) : ℤ) : ℚ) = D'.EF x y := by
    rw [← (spec (f i)).2.2.1, he, he, FD.EFf, h1, ← FD.EFf, (spec a).2.2.1]
  exact_mod_cast this

end GlobalTheory.DatumClasses
end

