module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import ReciprocityTheory.Chebotarev.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchFactorMulPSeriesEqIntegral
section
noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

theorem archFactor_mul_pSeries_eq_integral : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (F : NumberField.RingOfIntegers K → ℂ) (C : ℝ), (∀ α, ‖F α‖ ≤ C) → (∀ (u : (NumberField.RingOfIntegers K)ˣ) (α : NumberField.RingOfIntegers K), F ((u : NumberField.RingOfIntegers K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : NumberField.RingOfIntegers K) * α : NumberField.RingOfIntegers K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∀ p : (I → ℝ) → ℝ, Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) → ∀ s : ℂ, 1 < s.re → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s = 2 ^ Fintype.card I * ∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
  intro K _ _ _ I _ φ hφ n hn F C hF hinv p hp hp0 hsum s hs
  haveI : Countable (𝓞 K) := (RingOfIntegers.basis K).equivFun.injective.countable
  haveI : Countable (𝓞 K)ˣ := (Units.val_injective (α := 𝓞 K)).countable
  have hs0 : 0 < s.re := by linarith
  set tm : 𝓞 K → (I → ℝ) → ℂ := fun α => GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) with htm
  have hulog_inv : ∀ u : (𝓞 K)ˣ, GlobalTheory.HeckeTheta.ulog φ u⁻¹ = - GlobalTheory.HeckeTheta.ulog φ u := by
    intro u; funext i
    simp only [GlobalTheory.HeckeTheta.ulog, Pi.neg_apply]
    rw [← Real.log_inv, ← inv_pow, ← norm_inv, ← map_inv₀]
    congr 4
    have h := congrArg (fun x : 𝓞 K => (x : K)) (Units.inv_mul u)
    push_cast at h
    exact eq_inv_of_mul_eq_one_left h
  have hsum' : ∀ y, HasSum (fun u : (𝓞 K)ˣ => p (y - GlobalTheory.HeckeTheta.ulog φ u)) 1 := by
    intro y
    rw [← (Equiv.inv (𝓞 K)ˣ).hasSum_iff]
    simpa [Function.comp_def, hulog_inv, sub_neg_eq_add] using hsum y
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hsum y) 1 (fun u _ => hp0 _)
    have h1 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h1] using h
  have hemb0 : GlobalTheory.HeckeTheta.emb φ ((0 : 𝓞 K) : K) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  have htm0 : tm 0 = 0 := by funext y; simp only [htm, hemb0, GlobalTheory.HeckeMellin.term_zero hn]; rfl
  have hint : ∀ α : 𝓞 K, Integrable (tm α) := by
    intro α
    by_cases h : α = 0
    · subst h; rw [htm0]; exact integrable_zero _ _ _
    · exact (_root_.GlobalTheory.HeckeMellinOne.mellin_term K I φ hφ n s hs0 α h).1
  have hshift : ∀ (u : (𝓞 K)ˣ) (α : 𝓞 K) y, tm ((u : 𝓞 K) * α) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * tm α (y + GlobalTheory.HeckeTheta.ulog φ u) := by
    intro u α y
    have : (((u : 𝓞 K) * α : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (α : K) := by push_cast; rfl
    simp only [htm, this]
    exact _root_.GlobalTheory.HeckeShift.term_unit_mul K I φ hφ n s u α y
  have hwtu : ∀ u : (𝓞 K)ˣ, ‖GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K)‖ = 1 := fun u =>
    GlobalTheory.HeckeStrip.norm_wt φ n (by
      have := u.ne_zero
      exact_mod_cast this)
  have hgen : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) ≠ 0 := by
    intro J h
    haveI := J.2.2
    exact J.2.1 ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J.1).2 h)
  have hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {(haveI := J.2.2; Submodule.IsPrincipal.generator J.1)} = J.1 := by
    intro J; haveI := J.2.2; exact Ideal.span_singleton_generator J.1

  have horb : ∀ g : 𝓞 K, g ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => ∫ y, p y * ‖tm ((u : 𝓞 K) * g) y‖) (∫ y, ‖tm g y‖) ∧
      HasSum (fun u : (𝓞 K)ˣ => F ((u : 𝓞 K) * g) * ∫ y, (p y : ℂ) * tm ((u : 𝓞 K) * g) y) (F g * ∫ y, tm g y) := by
    intro g hg
    have hO := _root_.GlobalTheory.OrbitUnfold.orbit_unfold I (𝓞 K)ˣ (GlobalTheory.HeckeTheta.ulog φ) p hp hp0 hsum' (tm g) (hint g)
    constructor
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr hO.2
      simp only [hshift, norm_mul, hwtu, one_mul]
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr (hO.1.mul_left (F g))
      have hw : F ((u : 𝓞 K) * g) * GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) = F g := by
        have h1 := hinv u g
        have hgK : (g : K) ≠ 0 := by exact_mod_cast hg
        have : (((u : 𝓞 K) * g : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (g : K) := by push_cast; rfl
        rw [this, GlobalTheory.HeckeStrip.wt_mul] at h1
        have hne : GlobalTheory.HeckeStrip.wt φ n (g : K) ≠ 0 := by
          rw [← norm_ne_zero_iff, GlobalTheory.HeckeStrip.norm_wt φ n hgK]; exact one_ne_zero
        exact mul_right_cancel₀ hne (by rw [mul_assoc, h1])
      simp only [hshift]
      rw [← hw, mul_assoc]
      congr 1
      rw [← integral_const_mul]
      congr 1; funext y; ring

  set cst : ℝ := ∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2) with hcst
  have hnorm : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖ = cst * ((Ideal.absNorm J.1 : ℕ) : ℝ) ^ (-s.re) := by
    intro J
    rw [(_root_.GlobalTheory.HeckeMellinOne.mellin_term K I φ hφ n s hs0 _ (hgen J)).2.2, hspan J]
  have hb : Summable (fun J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) := by
    simp only [hnorm]
    exact (((ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal K hs).comp_injective Subtype.val_injective).mul_left cst)
  have hR := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℝ (fun α => ∫ y, p y * ‖tm α y‖) (by simp [htm0])
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J u => ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).1)
    (fun J u => le_of_eq (Real.norm_of_nonneg (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))))
    (fun J => (horb _ (hgen J)).1) hb
  have hI := GlobalTheory.T.hasSum_integral_theta_mellin_interchange I (𝓞 K) (fun α => GlobalTheory.HeckeTheta.emb φ (α : K)) F C hF n s p hp hp0 hp1 hint hR.summable
  have hU := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℂ (fun α => F α * ∫ y, (p y : ℂ) * tm α y) (by simp [htm0])
    (fun J => F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) * ∫ y, tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y) (fun J u => C * ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => C * ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).2)
    (fun J u => by
      rw [norm_mul]
      refine mul_le_mul (hF _) ((norm_integral_le_integral_norm _).trans (le_of_eq ?_)) (norm_nonneg _)
        ((norm_nonneg _).trans (hF 0))
      congr 1; funext y; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp0 y)])
    (fun J => (horb _ (hgen J)).1.mul_left C) (hb.mul_left C)
  rw [hI.unique hU, GlobalTheory.HeckeStrip.pSeries, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext J
  have h3 := (_root_.GlobalTheory.HeckeMellinOne.mellin_term K I φ hφ n s hs0 _ (hgen J)).2.1
  rw [hspan J] at h3
  simp only [GlobalTheory.HeckeStrip.pval]
  linear_combination (-F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) * h3

end GlobalTheory.HeckeMellin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLocalFiniteLengthAndSocleElement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory

theorem artinianLocal_finiteLength_and_socle_element :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R],
      (∃ n : ℕ, Module.length R R = n) ∧
      (¬ IsField R → ∃ t : R, t ≠ 0 ∧ (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) ∧
        Module.length (R ⧸ Ideal.span {t}) (R ⧸ Ideal.span {t}) < Module.length R R) := by
  intro R _ _ _
  have hfin : IsFiniteLength R R :=
    isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  have hne : Module.length R R ≠ ⊤ := Module.length_ne_top_iff.2 hfin
  refine ⟨⟨(Module.length R R).toNat, (ENat.natCast_toNat hne).symm⟩, ?_⟩
  intro hnf
  classical
  set m := IsLocalRing.maximalIdeal R with hmdef
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hk
  have hex : ∃ n : ℕ, m ^ n = ⊥ := ⟨k, hk⟩
  have hn : m ^ Nat.find hex = ⊥ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, Ideal.one_eq_top] at hn
    exact top_ne_bot hn
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hjne : m ^ j ≠ ⊥ := Nat.find_min hex (by omega)
  obtain ⟨t, htm, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hjne
  have hkill : ∀ a ∈ m, a * t = 0 := by
    intro a ha
    have h1 : a * t ∈ m ^ (j + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha htm
    have hj' : Nat.find hex = j + 1 := hj
    rw [← hj', hn] at h1
    exact (Submodule.mem_bot R).1 h1
  refine ⟨t, ht0, hkill, ?_⟩
  set I : Ideal R := Ideal.span {t}
  rw [Module.length_eq_of_surjective (S := R) (R := R ⧸ I) (M := R ⧸ I)
    Ideal.Quotient.mk_surjective |>.symm]
  have hadd := Module.length_eq_add_of_exact (R := R) I.subtype I.mkQ I.injective_subtype
    I.mkQ_surjective (LinearMap.exact_subtype_mkQ I)
  have hI : Module.length R I ≠ 0 := by
    rw [Ne, Module.length_eq_zero_iff]
    intro hs
    have : (⟨t, Ideal.subset_span rfl⟩ : I) = 0 := Subsingleton.elim _ _
    exact ht0 (congrArg Subtype.val this)
  have hQ : Module.length R (R ⧸ I) ≠ ⊤ := by
    intro h
    rw [hadd, h] at hne
    simp at hne
  rw [hadd]
  lift Module.length R (R ⧸ I) to ℕ using hQ with q
  lift Module.length R I to ℕ using (by
    intro h; rw [hadd, h] at hne; simp at hne) with i
  norm_cast
  norm_cast at hI
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocal
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.AzumayaLocal

theorem mem_left {A Λ : Type} [CommRing A] [Ring Λ] [Algebra A Λ] {I : Ideal A} (w : Λ) {z : Λ}
    (hz : z ∈ I • (⊤ : Submodule A Λ)) : w * z ∈ I • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun a ha t _ => ?_) (fun x y hx hy => ?_)
  · rw [mul_smul_comm]; exact Submodule.smul_mem_smul ha trivial
  · rw [mul_add]; exact Submodule.add_mem _ hx hy

theorem mem_right {A Λ : Type} [CommRing A] [Ring Λ] [Algebra A Λ] {I : Ideal A} (w : Λ) {z : Λ}
    (hz : z ∈ I • (⊤ : Submodule A Λ)) : z * w ∈ I • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun a ha t _ => ?_) (fun x y hx hy => ?_)
  · rw [smul_mul_assoc]; exact Submodule.smul_mem_smul ha trivial
  · rw [add_mul]; exact Submodule.add_mem _ hx hy

end GlobalTheory.AzumayaLocal

theorem GlobalTheory.AzumayaLocal.finite_residueField : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A], Finite (IsLocalRing.ResidueField A) := by
  intro ℓ _ A _ _ _ _
  have hmax : (maximalIdeal A).comap (algebraMap ℤ_[ℓ] A) = maximalIdeal ℤ_[ℓ] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal A))
  haveI : IsLocalHom (algebraMap ℤ_[ℓ] A) := ⟨fun x hx => by
    by_contra h
    have : x ∈ (maximalIdeal A).comap (algebraMap ℤ_[ℓ] A) := by rw [hmax]; exact h
    exact (mem_maximalIdeal _).1 this hx⟩
  have : Finite (IsLocalRing.ResidueField ℤ_[ℓ]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[ℓ])

theorem GlobalTheory.AzumayaLocal.exists_right_inverse : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Finite A Λ] (u : Λ), u - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) → ∃ v : Λ, u * v = 1 := by
  intro A _ _ Λ _ _ _ u hu
  let f : Λ →ₗ[A] Λ := LinearMap.mulLeft A u
  have hle : (⊤ : Submodule A Λ) ≤ LinearMap.range f ⊔ (maximalIdeal A) • (⊤ : Submodule A Λ) := by
    intro y _
    have hy : y = u * y - (u - 1) * y := by noncomm_ring
    rw [hy]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨y, rfl⟩)
      (Submodule.mem_sup_right (GlobalTheory.AzumayaLocal.mem_right y hu))
  have htop : LinearMap.range f = ⊤ :=
    top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle)
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop 1
  exact ⟨v, hv⟩

theorem GlobalTheory.AzumayaLocal.corner_eq_smul : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Finite A Λ] (e : Λ), IsIdempotentElem e → (∀ y : Λ, ∃ c : A, e * y * e - c • e ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) → ∀ y : Λ, ∃ c : A, e * y * e = c • e := by
  intro A _ _ Λ _ _ _ e he h y
  let g : Λ →ₗ[A] Λ := (LinearMap.mulRight A e).comp (LinearMap.mulLeft A e)
  have hg : ∀ z, g z = e * z * e := fun z => rfl
  have hge : g e = e := by rw [hg, he.eq, he.eq]
  have hgg : ∀ z, g (e * z * e) = e * z * e := by
    intro z
    rw [hg, ← mul_assoc, ← mul_assoc, he.eq, mul_assoc (e * z) e e, he.eq]
  have hS : LinearMap.range g ≤ A ∙ e := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (by rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map g)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨c, hc⟩ := h z
    have key : g z - c • e = g (e * z * e - c • e) := by
      rw [map_sub, map_smul, hgg, hge, hg]
    have hmem : g z - c • e ∈ (maximalIdeal A) • LinearMap.range g := by
      rw [key, LinearMap.range_eq_map, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem hc
    rw [show g z = c • e + (g z - c • e) by abel]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)) hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hS ⟨y, rfl⟩)
  exact ⟨c, hc.symm⟩

namespace GlobalTheory.AzumayaLocal

theorem azumaya_local_matrix : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro ℓ _ A _ _ _ _ Λ _ _ _ _ n hn
  haveI : IsAdicComplete (maximalIdeal A) A :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[ℓ] A
  haveI : Finite (ResidueField A) := GlobalTheory.AzumayaLocal.finite_residueField ℓ A
  haveI : Nontrivial Λ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact zero_ne_one (FaithfulSMul.algebraMap_injective A Λ
      (Subsingleton.elim (algebraMap A Λ 0) (algebraMap A Λ 1)))
  set M := (maximalIdeal A) • (⊤ : Submodule A Λ) with hM
  obtain ⟨x, h1, h2, N, a, b, h3⟩ := GlobalTheory.T.exists_residue_idempotent' A Λ
  obtain ⟨e, he, hex⟩ := GlobalTheory.T.exists_idempotent_lift_adicComplete_free_algebra A (maximalIdeal A) Λ x h1
  have hcorner : ∀ y : Λ, ∃ c : A, e * y * e - c • e ∈ M := by
    intro y
    obtain ⟨c, hc⟩ := h2 y
    refine ⟨c, ?_⟩
    have : e * y * e - c • e = (x * y * x - c • x) + ((e - x) * (y * e) + x * y * (e - x) - c • (e - x)) := by
      simp only [sub_mul, mul_sub, smul_sub, mul_assoc]; abel
    rw [this]
    exact M.add_mem hc (M.sub_mem (M.add_mem (mem_right _ hex) (mem_left _ hex)) (M.smul_mem c hex))
  have hu : ∑ i, a i * e * b i - 1 ∈ M := by
    have : ∑ i, a i * e * b i - 1 = (∑ i, a i * x * b i - 1) + ∑ i, a i * (e - x) * b i := by
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]; abel
    rw [this]
    exact M.add_mem h3 (M.sum_mem fun i _ => mem_right _ (mem_left _ hex))
  obtain ⟨v, hv⟩ := GlobalTheory.AzumayaLocal.exists_right_inverse A Λ _ hu
  exact GlobalTheory.T.nonempty_algEquiv_matrix_of_isAzumaya_of_full_idempotent A Λ n hn e he (GlobalTheory.AzumayaLocal.corner_eq_smul A Λ e he hcorner) ⟨N, a, fun i => b i * v, by
    rw [← hv, Finset.sum_mul]; simp only [mul_assoc]⟩

end GlobalTheory.AzumayaLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfSplitInjectiveFgProjectiveConstantRan
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem bijective_of_split_of_FP : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by
  intro R _ M N _ _ _ _ n hM hN f r hrf
  obtain ⟨hMf, hMp, hMr⟩ := hM
  obtain ⟨hNf, hNp, hNr⟩ := hN
  have hinj : Function.Injective f := fun a b h => by
    have := congrArg r h; rwa [hrf, hrf] at this
  let K := LinearMap.ker r
  let π : N →ₗ[R] K := LinearMap.codRestrict K (LinearMap.id - f ∘ₗ r) (fun x => by
    show r (x - f (r x)) = 0
    simp [hrf])
  have hπ : ∀ k : K, π (k : N) = k := fun k => by
    ext; simp [π, LinearMap.mem_ker.1 k.2]
  haveI : Module.Finite R K := Module.Finite.of_surjective π (fun k => ⟨k, hπ k⟩)
  haveI : Module.Projective R K := Module.Projective.of_split K.subtype π (by ext k; simp [hπ])
  let e : N ≃ₗ[R] M × K :=
    { toFun := fun x => (r x, π x)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp
      invFun := fun p => f p.1 + (p.2 : N)
      left_inv := fun x => by simp [π]
      right_inv := fun p => by
        obtain ⟨m, k⟩ := p
        have hk : r (k : N) = 0 := k.2
        ext
        · simp [hrf, hk]
        · simp [π, hrf, hk] }
  have hK : Module.rankAtStalk (R := R) K = 0 := by
    have h1 := Module.rankAtStalk_eq_of_equiv e
    rw [Module.rankAtStalk_prod] at h1
    funext p
    have h2 := congrFun h1 p
    simp only [Pi.add_apply, hMr p, hNr p] at h2
    simp only [Pi.zero_apply]; omega
  haveI : Subsingleton K := Module.rankAtStalk_eq_zero_iff_subsingleton.1 hK
  refine ⟨hinj, fun y => ⟨r y, ?_⟩⟩
  have : π y = 0 := Subsingleton.elim _ _
  have h3 := congrArg Subtype.val this
  simp [π, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlatStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  first | (exact @GlobalTheory.EtC.hyp_spec_coAug_of_etFF) | (exact GlobalTheory.EtC.hyp_spec_coAug_of_etFF) | (intros; apply GlobalTheory.EtC.hyp_spec_coAug_of_etFF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamHypercohomologyCupAnticomm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem cupHyp_add_cupHyp_swap : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  intro R _ C _ F a b
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rw [cupHyp_mk, cupHyp_mk, ← map_add (f := _)]
  refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * b.1.1 T T' φ), 0), ?_⟩
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
  · simp only [cechDeRhamTotalDifferentialOne_functionPart, Submodule.coe_add, Prod.fst_add, Pi.add_apply, coe_cupZZ, cupTot_apply,
      cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_mul, map_neg]
    ring
  · simp only [dTot1_a, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, coe_cupZZ,
      cupTot_a, map_neg, Derivation.leibniz, Pi.zero_apply, map_zero]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    module
  · simp only [dTot1_η, Submodule.coe_add, Prod.snd_add, Pi.add_apply, coe_cupZZ, cupTot_η,
      Pi.zero_apply, map_zero]
    rw [wedge_swap (a.1.2 T), neg_add_cancel]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CliffordSemidirectPrimeIndexIrreducibleCharacterStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → (∀ δ, χ (inl δ * inr s) = 0) ∨ (IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧ ∑ᶠ g, χ (inl g * inr s) * star (χ (inl g * inr s)) = (Nat.card G : ℂ)) := by
  first | (exact @GlobalTheory.Shin.clifford_prime_index) | (exact GlobalTheory.Shin.clifford_prime_index) | (intros; apply GlobalTheory.Shin.clifford_prime_index <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [DecidableEq ι]

def colDer {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (Pol ι d a) :=
  ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a,
    S k j • (LinearMap.mulLeft ℂ (X (τ, i, k) : Pol ι d a) ∘ₗ (pderiv (τ, i, j)).toLinearMap)

def atPl {a : ℕ} (τ : ι) (g : Matrix (Fin a) (Fin a) ℂ) : ι → Matrix (Fin a) (Fin a) ℂ :=
  Function.update 1 τ g

theorem colDer_apply {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colDer τ S P = ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a, S k j • (X (τ, i, k) * pderiv (τ, i, j) P) := by
  simp [colDer, LinearMap.sum_apply]

theorem colDer_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (v : Var ι d a) :
    colDer (d := d) τ S (X v) = if v.1 = τ then ∑ k, S k v.2.2 • (X (τ, v.2.1, k) : Pol ι d a) else 0 := by
  obtain ⟨σ, i₀, j₀⟩ := v
  rw [colDer_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.ext_iff]
  by_cases h : σ = τ
  · subst h
    simp only [if_true]
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  · simp [h, Ne.symm h]

end GlobalTheory.ColLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerConeStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degW_blattner_le_of_blattnerCone : ∀ (p q : ℕ) (M : GKMod p q) (lam : Ix p q → ℚ) (c θ : ℚ), ConeTypes M lam → (∀ a, (θ < lam a → 0 ≤ shiftNu c (blattner lam) a) ∧ (lam a ≤ θ → shiftNu c (blattner lam) a ≤ 0)) → ∀ μ v, IsHW M.act μ v → degW c (blattner lam) ≤ degW c μ := by
  first | exact @GlobalTheory.FlowLemma.degW_blattner_le | exact GlobalTheory.FlowLemma.degW_blattner_le | (intros; apply GlobalTheory.FlowLemma.degW_blattner_le <;> assumption)
end

