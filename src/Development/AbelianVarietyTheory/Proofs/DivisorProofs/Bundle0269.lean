module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHeckeTermDecayIntegrand
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay

noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay

theorem continuous_qZ (σ : ℂ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) : Continuous (qZ σ a b m y) := by
  unfold qZ
  have h1 : Continuous fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ (-a) :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I).zpow₀ (-a)
      fun t => Or.inl (GlobalTheory.HeckeTwo.TermSmooth.u_ne hy t)
  have h2 : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) :=
    (by fun_prop : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.2 (by positivity)
  exact (h1.mul h2).mul continuous_const

theorem norm_qZ (σ : ℂ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    ‖qZ σ a b m y t‖ = (t ^ 2 + y ^ 2) ^ (-((a : ℝ) / 2 + b + σ.re)) * |y| ^ m := by
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold qZ
  rw [norm_mul, norm_mul, norm_zpow, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_eq_rpow, ← Real.rpow_intCast,
    ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
  congr 2
  simp
  ring

theorem integrable_qZ : ∀ σ ∈ halfPlane, ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∀ y : ℝ, y ≠ 0 →
    MeasureTheory.Integrable (qZ σ a b m y) := by
  intro σ hσ a b m hab y hy
  have hσ' : -1 / 2 < σ.re := hσ
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  have he1 : 1 / 2 < e := by rw [he]; linarith
  set κ := min 1 (y ^ 2) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  refine (((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (r := 2 * e) (by simp; linarith)).const_mul
    (κ ^ (-e) * |y| ^ m))).mono' (continuous_qZ σ a b m hy).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t => ?_)
  rw [norm_qZ σ a b m hy t]
  have hQk : κ * (1 + ‖t‖ ^ 2) ≤ t ^ 2 + y ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ y ^ 2 := min_le_right _ _
    nlinarith [sq_nonneg t]
  have hA : (t ^ 2 + y ^ 2) ^ (-e) ≤ κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2) := by
    rw [show -(2 * e) / 2 = -e by ring, ← Real.mul_rpow hκ0.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hQk (by linarith)
  calc (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m ≤ (κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2)) * |y| ^ m :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end GlobalTheory.HeckeTwo.TermDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureOverGenericFibreHartogs
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.ClosureHartogs

theorem closure_hart : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (τ : D →ₗ[GlobalTheory.LocAcyc.GenFib A R] GlobalTheory.LocAcyc.GenFib A R),
      (∀ c ∈ GlobalTheory.KeyOriginNoeth.closure A R D, ∃ r : R, algebraMap R _ r = τ c) →
    ∀ (a₀ : A), a₀ ≠ 0 → ∀ (n : ℕ) (x y : Fin n → D),
      (∀ i, y i ∈ GlobalTheory.KeyOriginNoeth.closure A R D) →
      (∀ d : D, ∑ i, x i * algebraMap _ D (τ (y i * d)) =
        GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ hHR hinj D _ _ τ hτC a₀ ha₀ n x y hy hid
  set F := GlobalTheory.LocAcyc.GenFib A R
  set C := GlobalTheory.KeyOriginNoeth.closure A R D
  letI : Algebra R D := (GlobalTheory.KeyOriginNoeth.baseHom A R D).toAlgebra
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  have hbase : ∀ r : R, GlobalTheory.KeyOriginNoeth.baseHom A R D r = algebraMap F D (algebraMap R F r) :=
    fun r => rfl
  have hmemC : ∀ z : D, z ∈ C ↔ IsIntegral R z := fun z => Iff.rfl
  have hsmulC : ∀ (r : R) (c : C), ((r • c : C) : D) = GlobalTheory.KeyOriginNoeth.baseHom A R D r * c :=
    fun r c => rfl
  have hτm : ∀ (f : F) (w : D), τ (algebraMap F D f * w) = f * τ w := by
    intro f w; rw [← Algebra.smul_def, τ.map_smul, smul_eq_mul]

  have hunit : ∀ a : A, a ≠ 0 → IsUnit (algebraMap R F (algebraMap A R a)) := by
    intro a ha
    exact IsLocalization.map_units F
      (⟨algebraMap A R a, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ :
        nonZeroDivisors A)⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))

  let N : Submodule R D :=
    { carrier := {d | ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z)}
      add_mem' := by
        intro d₁ d₂ h₁ h₂ z hz
        obtain ⟨r₁, e₁⟩ := h₁ z hz
        obtain ⟨r₂, e₂⟩ := h₂ z hz
        exact ⟨r₁ + r₂, by rw [map_add (f := _), e₁, e₂, add_mul, map_add (f := _)]⟩
      zero_mem' := by
        intro z _
        exact ⟨0, by simp⟩
      smul_mem' := by
        intro r d h z hz
        obtain ⟨r₁, e₁⟩ := h z hz
        refine ⟨r * r₁, ?_⟩
        rw [Algebra.smul_def, mul_assoc]
        change _ = τ (algebraMap F D (algebraMap R F r) * (d * z))
        rw [hτm, ← e₁, map_mul] }
  have hmemN : ∀ d, d ∈ N ↔ ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z) := fun d => Iff.rfl
  have h1N : (1 : D) ∈ N := by
    intro z hz
    simpa using hτC z hz

  obtain ⟨c₀, hc₀⟩ := hunit a₀ ha₀
  let S : Submodule R D := Submodule.span R (Set.range fun i => algebraMap F D (↑c₀⁻¹ : F) * x i)
  have hNS : N ≤ S := by
    intro d hd
    have hr : ∀ i, ∃ r : R, algebraMap R F r = τ (y i * d) := by
      intro i
      obtain ⟨r, e⟩ := hd (y i) (hy i)
      exact ⟨r, by rw [e, mul_comm]⟩
    choose r hr using hr
    have hd' : d = ∑ i, r i • (algebraMap F D (↑c₀⁻¹ : F) * x i) := by
      have h := hid d
      have h2 : d = algebraMap F D (↑c₀⁻¹ : F) *
          (GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) := by
        rw [hbase, ← mul_assoc, ← map_mul, ← hc₀, Units.inv_mul, map_one, one_mul]
      rw [h2, ← h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, ← hr i]
      change _ = algebraMap F D (algebraMap R F (r i)) * _
      ring
    rw [hd']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hSnoeth : IsNoetherian R S :=
    isNoetherian_of_fg_of_noetherian S (Submodule.fg_span (Set.finite_range _))

  intro a ha m hm
  obtain ⟨c, hc⟩ := hunit a ha
  set ξ : D := algebraMap F D (↑c⁻¹ : F) * (m : D) with hξ

  have hξN : ∀ d ∈ N, ξ * d ∈ N := by
    intro d hd z hz
    have hmz : (m : D) * z ∈ C := C.mul_mem m.2 hz
    obtain ⟨r₀, e₀⟩ := hd _ hmz
    have hdiv : ∃ r'' : R, r₀ = algebraMap A R a • r'' := by
      apply hHR a ha r₀
      intro p hp hph
      obtain ⟨u, hu, m', hm'⟩ := hm p hp hph
      have hm'z : (m' : D) * z ∈ C := C.mul_mem m'.2 hz
      obtain ⟨r', e'⟩ := hd _ hm'z
      refine ⟨u, hu, r', ?_⟩
      apply hinj
      have hv := congrArg Subtype.val hm'
      rw [hsmulC, hsmulC, hbase, hbase] at hv
      rw [smul_eq_mul, smul_eq_mul, map_mul, map_mul, e₀, e', ← hτm, ← hτm]
      congr 1
      linear_combination (d * z) * hv
    obtain ⟨r'', e''⟩ := hdiv
    refine ⟨r'', ?_⟩
    have : ξ * d * z = algebraMap F D (↑c⁻¹ : F) * (d * ((m : D) * z)) := by
      rw [hξ]; ring
    rw [this, hτm, ← e₀, e'', smul_eq_mul, map_mul, ← hc, ← mul_assoc, Units.inv_mul, one_mul]
  have hpow : ∀ k : ℕ, ξ ^ k ∈ N := by
    intro k
    induction k with
    | zero => simpa using h1N
    | succ k ih => rw [pow_succ']; exact hξN _ ih
  have hadj : Subalgebra.toSubmodule (Algebra.adjoin R {ξ}) ≤ S := by
    rw [Algebra.adjoin_eq_span]
    refine le_trans ?_ hNS
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hw
    exact hpow k
  have hfg : (Subalgebra.toSubmodule (Algebra.adjoin R {ξ})).FG :=
    isNoetherian_submodule.mp hSnoeth _ hadj
  have hξC : ξ ∈ C :=
    (hmemC ξ).mpr (IsIntegral.of_mem_of_fg _ hfg ξ (Algebra.self_mem_adjoin_singleton R ξ))
  refine ⟨⟨ξ, hξC⟩, Subtype.ext ?_⟩
  rw [hsmulC, hbase]
  change (m : D) = algebraMap F D (algebraMap R F (algebraMap A R a)) * ξ
  rw [hξ, ← mul_assoc, ← map_mul, ← hc, Units.mul_inv, map_one, one_mul]

end GlobalTheory.ClosureHartogs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTransposeInvTranspose
section
noncomputable section

namespace GlobalTheory.InvTransposeEnds

section General

variable {G H V W Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

theorem isIrreducible_comp {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (φ : H →* G)
    (hφ : Function.Surjective φ) : Representation.IsIrreducible (ρ.comp φ) := by
  haveI hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule e)
  · let S' : Subrepresentation ρ := ⟨S.toSubmodule, fun g v hv => by
      obtain ⟨x, rfl⟩ := hφ g
      exact S.apply_mem_toSubmodule x hv⟩
    rcases h.eq_bot_or_eq_top S' with e | e
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))

end General

end GlobalTheory.InvTransposeEnds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingAtPrimeOfEtale
section
open GlobalTheory.EtC

open TensorProduct

namespace GlobalTheory

theorem isAlgClosed_fractionRing_atPrime_of_etale : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime]
    [IsDomain (Localization.AtPrime P)],
    IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  intro T E _ _ _ _ _ P _ _ hK
  haveI : Module.Flat T (Localization.AtPrime P) := Module.Flat.trans T E (Localization.AtPrime P)
  have hTEp : Function.Injective (algebraMap T (Localization.AtPrime P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    by_contra h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := (Localization.AtPrime P))
      (mem_nonZeroDivisors_of_ne_zero h0)
    apply one_ne_zero (α := (Localization.AtPrime P))
    apply hreg
    simp [Algebra.smul_def, ht]
  have hTL : Function.Injective (algebraMap T (FractionRing (Localization.AtPrime P))) := by
    rw [IsScalarTower.algebraMap_eq T (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
    exact (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))).comp hTEp
  haveI : FaithfulSMul T (FractionRing (Localization.AtPrime P)) := (faithfulSMul_iff_algebraMap_injective T (FractionRing (Localization.AtPrime P))).2 hTL
  letI : Algebra (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : IsScalarTower T (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.isScalarTower_liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : Module.Finite (FractionRing T) ((FractionRing T) ⊗[T] E) := Algebra.FormallyUnramified.finite_of_free (FractionRing T) ((FractionRing T) ⊗[T] E)
  let φ : (FractionRing T) ⊗[T] E →ₐ[(FractionRing T)] (FractionRing (Localization.AtPrime P)) := Algebra.TensorProduct.lift (Algebra.ofId (FractionRing T) (FractionRing (Localization.AtPrime P)))
    (IsScalarTower.toAlgHom T E (FractionRing (Localization.AtPrime P))) (fun _ _ => Commute.all _ _)
  have hE : ∀ e : E, IsIntegral (FractionRing T) (algebraMap E (FractionRing (Localization.AtPrime P)) e) := by
    intro e
    have h1 : IsIntegral (FractionRing T) ((1 : (FractionRing T)) ⊗ₜ[T] e) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map φ
    simpa [φ] using h2
  have hEp : ∀ x : (Localization.AtPrime P), algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) x ∈ algebraicClosure (FractionRing T) (FractionRing (Localization.AtPrime P)) := by
    intro x
    obtain ⟨⟨e, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have hs : algebraMap E (FractionRing (Localization.AtPrime P)) s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))).2
        (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero
    have heq : algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (IsLocalization.mk' (Localization.AtPrime P) e s) =
        algebraMap E (FractionRing (Localization.AtPrime P)) e / algebraMap E (FractionRing (Localization.AtPrime P)) s := by
      rw [eq_div_iff hs, IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) e,
        IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (s : E), ← map_mul, IsLocalization.mk'_spec]
    simp only at heq ⊢
    rw [heq]
    exact div_mem (mem_algebraicClosure_iff.2 (hE e).isAlgebraic)
      (mem_algebraicClosure_iff.2 (hE s).isAlgebraic)
  have hL : (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))).IsIntegral := by
    intro z
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (Localization.AtPrime P) z
    exact (mem_algebraicClosure_iff.1 (div_mem (hEp x) (hEp y))).isIntegral
  haveI := hK
  exact IsAlgClosed.of_ringEquiv (FractionRing T) (FractionRing (Localization.AtPrime P))
    (RingEquiv.ofBijective (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))) (IsAlgClosed.ringHom_bijective_of_isIntegral _ hL))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfLocalIdealPointProperty
section
noncomputable section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PtClosed

theorem closed_of_points : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S), P R' x → P R'' (spMap g ≫ x)) →
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
     ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
    ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), (∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ P R' x := by
  intro S P hBC hLoc hCov
  have hrep : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      Represents (ptQ P V hV) (killIdeal (ptQ P V hV)) := by
    intro V hV
    obtain ⟨s, hs, hJ⟩ := _root_.GlobalTheory.PtClosed.affine_local_represents S P hCov V hV
    have hQbc : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'')
        (f : Γ(S, V) →+* R'), ptQ P V hV R' f → ptQ P V hV R'' (g.comp f) := by
      intro R' _ R'' _ g f hf
      have := hBC R' R'' g _ hf
      simpa [ptQ, spMap, CommRingCat.ofHom_comp, Spec.map_comp] using this
    have hQloc : ∀ (R' : Type) [CommRing R'] (f : Γ(S, V) →+* R') (t : Finset R'),
        Ideal.span (t : Set R') = ⊤ →
        (∀ r ∈ t, ptQ P V hV (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) →
        ptQ P V hV R' f := by
      intro R' _ f t ht H
      refine hLoc R' _ t ht fun r hr ↦ ?_
      have := H r hr
      simpa [ptQ, spMap, CommRingCat.ofHom_comp, Spec.map_comp] using this
    obtain ⟨J, hJ'⟩ := _root_.GlobalTheory.PtClosed.represents_of_away_cover Γ(S, V) (ptQ P V hV) hQbc hQloc s hs hJ
    exact represents_killIdeal hJ'
  let I : S.IdealSheafData :=
    { ideal := fun V ↦ killIdeal (ptQ P V.1 V.2)
      map_ideal_basicOpen := fun U f ↦ by
        have h1 := represents_restrict S P U.1 (S.basicOpen f) U.2 (U.2.basicOpen f) (S.basicOpen_le f) _
          (hrep U.1 U.2)
        exact (killIdeal_eq h1).symm }
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun R' _ x ↦ ?_⟩
  have key : I ≤ x.ker ↔ P R' x := by
    rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
    constructor
    · intro h
      exact GlobalTheory.T.affinePointProperty_of_le_ker_app S P hLoc hrep R' x fun V hV ↦ h ⟨V, hV⟩
    · intro h V
      exact _root_.GlobalTheory.PtClosed.killIdeal_le_ker_app S P hBC R' x h V.1 V.2
  rw [← key]
  constructor
  · rintro ⟨y, rfl⟩
    have := y.le_ker_comp I.subschemeι
    rwa [Scheme.IdealSheafData.ker_subschemeι] at this
  · intro h
    exact ⟨IsClosedImmersion.lift I.subschemeι x (by rwa [Scheme.IdealSheafData.ker_subschemeι]),
      IsClosedImmersion.lift_fac _ _ _⟩
end GlobalTheory.PtClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainMonicRootsOfIsIndEtaleLocal
section
open GlobalTheory.EtC

namespace GlobalTheory.LocalIndEtAIC

open Polynomial IsLocalRing

theorem lift_atComap {W O : Type} [CommRing W] [CommRing O] [IsLocalRing O] (v : W →+* O) :
    ∃ φ : Localization.AtPrime ((maximalIdeal O).comap v) →+* O,
      ∀ w, φ (algebraMap W _ w) = v w := by
  have hu : ∀ y : ((maximalIdeal O).comap v).primeCompl, IsUnit (v y) := fun y => by
    by_contra hy
    exact y.2 hy
  exact ⟨IsLocalization.lift hu, fun w => IsLocalization.lift_eq hu w⟩

theorem isDomain_aic_of_indEt : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O],
    IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime],
      IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  intro T O _ _ _ _ h hE
  have hdom : IsDomain O := by
    refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
    let I : Ideal (MvPolynomial (Fin 2) T) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    haveI : Algebra.FinitePresentation T (MvPolynomial (Fin 2) T ⧸ I) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
    let g : (MvPolynomial (Fin 2) T ⧸ I) →ₐ[T] O :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        simp [hxy])
    obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
    let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
    have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
      have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
      exact this.trans (MvPolynomial.aeval_X _ i)
    have h0 : w 0 * w 1 = 0 := by
      have : Ideal.Quotient.mkₐ T I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ T I (MvPolynomial.X 1) = 0 := by
        rw [← map_mul]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      simp only [w, ← map_mul, this, map_zero]
    obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
    haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
    have hm : algebraMap W (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) (w 0) *
        algebraMap W _ (w 1) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp hm with h1 | h1
    · left
      have e := hφ (w 0)
      rw [h1, map_zero] at e
      have := hw 0
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
    · right
      have e := hφ (w 1)
      rw [h1, map_zero] at e
      have := hw 1
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
  refine ⟨hdom, ?_⟩
  intro p hpm hdeg
  set n := p.natDegree with hn
  let g : MvPolynomial (Fin n) T →ₐ[T] O := MvPolynomial.aeval (fun i => p.coeff i)
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let c : Fin n → W := fun i => u (MvPolynomial.X i)
  have hc : ∀ i, v (c i) = p.coeff i := fun i => by
    have := DFunLike.congr_fun huv (MvPolynomial.X i)
    exact this.trans (MvPolynomial.aeval_X _ i)
  let p' : W[X] := X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp'm : p'.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hp' : p'.map (v : W →+* O) = p := by
    conv_rhs => rw [hpm.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [p', Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C]
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
    simp [hc]
    rfl
  have hp'd : p'.natDegree = n := by
    have e1 := hp'm.natDegree_map (v : W →+* O)
    rw [hp'] at e1
    rw [← e1]
  obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
  set L := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))
  haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
  have hL := (hE W ((maximalIdeal O).comap (v : W →+* O))).2
  have hmL : (p'.map (algebraMap W L)).Monic := hp'm.map _
  have hdL : 0 < (p'.map (algebraMap W L)).natDegree := by
    rw [hp'm.natDegree_map, hp'd]; exact hdeg
  obtain ⟨r, hr⟩ := hL _ hmL hdL
  refine ⟨φ r, ?_⟩
  have hcomp : φ.comp (algebraMap W L) = (v : W →+* O) := RingHom.ext hφ
  have hpL : p = (p'.map (algebraMap W L)).map φ := by rw [Polynomial.map_map, hcomp, hp']
  rw [hpL, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]

end GlobalTheory.LocalIndEtAIC
end

