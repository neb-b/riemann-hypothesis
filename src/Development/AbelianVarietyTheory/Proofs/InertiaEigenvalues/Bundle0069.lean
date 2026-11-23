module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMulRightInvariantOfCovolumeOne
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueFieldMapAdicCompletionSurjective
section
open IsLocalRing

namespace GlobalTheory

theorem residueField_map_adicCompletion_surjective (W : Type*) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] :
    Function.Surjective (ResidueField.map (algebraMap W (AdicCompletion (maximalIdeal W) W))) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal W) 1 x)
  refine ⟨residue W w, ?_⟩
  rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff]
  intro hu
  have h1 := hu.map (AdicCompletion.evalₐ (maximalIdeal W) 1)
  rw [map_sub, AlgHom.commutes, ← hw, Ideal.Quotient.algebraMap_eq, sub_self] at h1
  haveI : Nontrivial (W ⧸ maximalIdeal W ^ 1) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [pow_one]; exact (maximalIdeal.isMaximal W).ne_top)
  exact not_isUnit_zero h1

theorem finite_residueField_of_dominating (D : Type*) [CommRing D] [IsDomain D] [IsLocalRing D]
    [IsNoetherianRing D] [Ring.DimensionLEOne D] (hD : ¬ IsField D) [Finite (ResidueField D)]
    (V : ValuationSubring (FractionRing D))
    (h1 : ∀ r, algebraMap D (FractionRing D) r ∈ V)
    [IsLocalHom ((algebraMap D (FractionRing D)).codRestrict V h1)] :
    Finite (ResidueField V) := by
  set f := (algebraMap D (FractionRing D)).codRestrict V h1 with hf
  letI : Algebra D V := f.toAlgebra
  haveI : IsLocalHom (algebraMap D V) := ‹IsLocalHom f›
  haveI : FaithfulSMul D V := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    fun a b hab => IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val hab)
  have hB : ∀ x : V, ∃ c : D, c ≠ 0 ∧ ∃ b : D, algebraMap D V c * x = algebraMap D V b := by
    intro x
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors D) (x : FractionRing D)
    refine ⟨c, nonZeroDivisors.coe_ne_zero c, b, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_mul] at hbc ⊢
    change algebraMap D (FractionRing D) c * x = algebraMap D (FractionRing D) b
    rw [mul_comm]; exact hbc
  have hm : maximalIdeal D ≠ ⊥ := fun h => hD (isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  haveI := finite_quotient_span_of_birational hB ha0
  have hle : Ideal.span {algebraMap D V a} ≤ maximalIdeal V := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact map_nonunit (algebraMap D V) a ha
  have hsurj : Function.Surjective (Ideal.Quotient.factorₐ D hle).toLinearMap := by
    intro y
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ v, rfl⟩
  haveI : Module.Finite D (ResidueField V) := Module.Finite.of_surjective _ hsurj
  haveI : Module.Finite (ResidueField D) (ResidueField V) :=
    Module.Finite.of_restrictScalars_finite D _ _
  exact Module.finite_of_finite (ResidueField D)

theorem exists_complete_dvr_finite_residueField : ∀ (D : Type) [CommRing D] [IsDomain D] [IsLocalRing D], IsNoetherianRing D → ringKrullDim D = 1 → Finite (ResidueField D) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (maximalIdeal V) V) (g : D →+* V), Function.Injective g ∧ IsLocalHom g ∧ Finite (ResidueField V) := by
  intro D _ _ _ hN hdim hF
  have hD : ¬ IsField D := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hdim; exact zero_ne_one hdim
  haveI : Ring.KrullDimLE 1 D := Ring.krullDimLE_iff.mpr (by simp [hdim])
  haveI : Ring.DimensionLEOne D :=
    ⟨fun hp hpr => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this _ hp hpr⟩
  obtain ⟨V, hV, h⟩ :=
    exists_discreteValuationSubring_dominating D (FractionRing D) (FractionRing D) hD
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hfin : Finite (ResidueField V) := finite_residueField_of_dominating D hD V h1
  obtain ⟨hi, hl⟩ := injective_and_isLocalHom_adicCompletion_comp
      ((algebraMap D (FractionRing D)).codRestrict V h1)
      fun a b hab => IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val hab)
  exact ⟨AdicCompletion (maximalIdeal V) V, inferInstance, inferInstance, inferInstance,
    inferInstance, _, hi, hl,
    Finite.of_surjective _ (residueField_map_adicCompletion_surjective V)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RieszEigenvectorSesquilinearFunctionSpace
section
open scoped ComplexConjugate

namespace GlobalTheory

lemma sesq_rules_of_combination {X : Type} (C : Submodule ℂ (X → ℂ)) (F : (X → ℂ) → (X → ℂ) → ℂ)
    (hl : ∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → F (a • f + f') g = star a * F f g + F f' g)
    (hr : ∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → F f (a • g + g') = a * F f g + F f g') :
    (∀ f f' g, f ∈ C → f' ∈ C → g ∈ C → F (f + f') g = F f g + F f' g) ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F (a • f) g = star a * F f g) ∧
    (∀ f g g', f ∈ C → g ∈ C → g' ∈ C → F f (g + g') = F f g + F f g') ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F f (a • g) = a * F f g) := by
  have l0 : ∀ g, g ∈ C → F 0 g = 0 := by
    intro g hg
    have := hl 1 0 0 g C.zero_mem C.zero_mem hg
    simp only [one_smul, add_zero, star_one, one_mul] at this
    linear_combination -this
  have r0 : ∀ f, f ∈ C → F f 0 = 0 := by
    intro f hf
    have := hr 1 f 0 0 hf C.zero_mem C.zero_mem
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f f' g hf hf' hg
    simpa using hl 1 f f' g hf hf' hg
  · intro a f g hf hg
    have := hl a f 0 g hf C.zero_mem hg
    rwa [add_zero, l0 g hg, add_zero] at this
  · intro f g g' hf hg hg'
    simpa using hr 1 f g g' hf hg hg'
  · intro a f g hf hg
    have := hr a f g 0 hf hg C.zero_mem
    rwa [add_zero, r0 f hf, add_zero] at this

theorem riesz_and_eigenvector_of_sesq_on_fun_space : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) := by
  intro X C hfin ip Φ hl hr hs hp Φl Φr
  haveI := hfin
  obtain ⟨ipa, ips, ipa', ips'⟩ := sesq_rules_of_combination C ip hl hr
  obtain ⟨Φa, Φs, Φa', Φs'⟩ := sesq_rules_of_combination C Φ Φl Φr
  let B : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun x y => ip (y : X → ℂ) x)
    (fun m₁ m₂ n => by simp only [Submodule.coe_add]; exact ipa' _ _ _ n.2 m₁.2 m₂.2)
    (fun c m n => by
      simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]; exact ips' c _ _ n.2 m.2)
    (fun m n₁ n₂ => by simp only [Submodule.coe_add]; exact ipa _ _ _ n₁.2 n₂.2 m.2)
    (fun c m n => by
      simp only [Submodule.coe_smul, smul_eq_mul, starRingEnd_apply]; exact ips c _ _ n.2 m.2)
  have Bsym : ∀ x y, B x y = conj (B y x) := by
    intro x y
    simp only [B, LinearMap.mk₂'ₛₗ_apply, starRingEnd_apply]
    exact hs _ _ x.2 y.2
  have Bpos : ∀ x, x ≠ 0 → 0 < (B x x).re := by
    intro x hx
    simp only [B, LinearMap.mk₂'ₛₗ_apply]
    exact hp _ x.2 (by rwa [ne_eq, Submodule.coe_eq_zero])
  let ipA : ℂ →ₗ[ℂ] ℂ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun a b => conj b * a) (by intros; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)
  have riesz : ∀ L : C →ₗ[ℂ] ℂ, ∃ x : C, ∀ y : C, ip (x : X → ℂ) y = L y := by
    intro L
    obtain ⟨x, hx, -⟩ := hermitian_adjoint_exists_unique ℂ C ipA B Bsym Bpos L 1
    exact ⟨x, fun y => by have := hx y; simpa [B, ipA] using this⟩
  refine ⟨?_, ?_⟩
  · intro f hf
    let L : C →ₗ[ℂ] ℂ :=
      { toFun := fun g => Φ f g
        map_add' := fun g g' => Φa' _ _ _ hf g.2 g'.2
        map_smul' := fun c g => Φs' c _ _ hf g.2 }
    obtain ⟨x, hx⟩ := riesz L
    exact ⟨x, x.2, fun g hg => hx ⟨g, hg⟩⟩
  · intro hC
    let large₂ : C → (C →ₗ[ℂ] ℂ) := fun g =>
      { toFun := fun f => star (Φ f g)
        map_add' := fun f f' => by
          simp only [Submodule.coe_add]; rw [Φa _ _ _ f.2 f'.2 g.2, star_add]
        map_smul' := fun c f => by
          simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
          rw [Φs c _ _ f.2 g.2, star_mul, star_star, mul_comm] }
    have hex : ∀ g : C, ∃ x : C, ∀ f : C, ip (f : X → ℂ) x = Φ f g := by
      intro g
      obtain ⟨x, hx⟩ := riesz (large₂ g)
      refine ⟨x, fun f => ?_⟩
      rw [hs _ _ x.2 f.2, hx f]
      simp [large₂]
    choose R hR using hex
    have inj : ∀ x y : C, (∀ f : C, ip (f : X → ℂ) x = ip f y) → x = y := by
      intro x y h
      by_contra hne
      have hd : ((x - y : C) : X → ℂ) = (-1 : ℂ) • (y : X → ℂ) + x := by
        rw [Submodule.coe_sub]; ext t; simp; ring
      have h1 := hr (-1) ((x - y : C) : X → ℂ) y x (x - y).2 y.2 x.2
      rw [← hd, h (x - y)] at h1
      have h2 := hp _ (x - y).2 (by rwa [ne_eq, Submodule.coe_eq_zero, sub_eq_zero])
      have h3 : ip ((x - y : C) : X → ℂ) ((x - y : C) : X → ℂ) = 0 := by rw [h1]; ring
      rw [h3] at h2
      simp at h2
    let Rl : Module.End ℂ C :=
      { toFun := R
        map_add' := fun g g' => inj _ _ (fun f => by
          rw [hR, Submodule.coe_add, Submodule.coe_add, ipa' _ _ _ f.2 (R g).2 (R g').2, hR, hR,
            Φa' _ _ _ f.2 g.2 g'.2])
        map_smul' := fun c g => inj _ _ (fun f => by
          rw [hR, Submodule.coe_smul, RingHom.id_apply, Submodule.coe_smul, ips' c _ _ f.2 (R g).2, hR,
            Φs' c _ _ f.2 g.2]) }
    haveI : Nontrivial C := Submodule.nontrivial_iff_ne_bot.mpr hC
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue Rl
    obtain ⟨e, he⟩ := hc.exists_hasEigenvector
    refine ⟨c, e, e.2, by rw [ne_eq, Submodule.coe_eq_zero]; exact he.2, fun f hf => ?_⟩
    rw [← hR e ⟨f, hf⟩]
    show ip f ((Rl e : C) : X → ℂ) = _
    rw [he.apply_eq_smul, Submodule.coe_smul, ips' c _ _ hf e.2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomApplyEqPowOfPowPowEqSelf
section
namespace GlobalTheory

open Polynomial

theorem ringHom_apply_eq_pow_of_pow_pow_eq_self :
    ∀ {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (τ : k →+* k) (N : ℕ), 0 < N →
      ∀ (z : k), z ^ p ^ N = z → ∃ e : ℕ, τ z = z ^ p ^ e := by
  first
  | exact @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow
  | exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow
  | (apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

def rowS {h : ℕ} (ϖ : F) (lam : Fin h → F) (L U : ℕ) (x : Fin h → F) (r : Fin h) : F :=
  ∑ j, ∑ n ∈ Icc (-(L : ℤ)) U, term p ϖ lam x r j n

def winPt {h : ℕ} (π : Fin h → F) (L : ℕ) (z : Fin h → F) : Fin h → F :=
  fun j => π j * z j ^ (p ^ h) ^ (L - 1)

def coefB {h : ℕ} (ϖ : F) (lam π : Fin h → F) (L U m : ℕ) : Matrix (Fin h) (Fin h) F :=
  Matrix.of fun r j => if m ≤ L + U then
    (term p ϖ lam π r j ((m : ℤ) - L) / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) else 0

theorem rowT_eq_rowS {h : ℕ} (ϖ : F) (lam : Fin h → F) (K : ℕ) (x : Fin h → F) (r : Fin h) :
    rowT p ϖ lam K x r = rowS p ϖ lam K K x r := rfl

end GlobalTheory.PMonE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearIteratePrimePowSubMemFiltration
section
namespace GlobalTheory

theorem semilinear_sub_mem_pow_succ_smul {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (n : Ideal A) (γ : A →+* A) (Y : N →+ N) (hY : ∀ a x, Y (a • x) = γ a • Y x)
    (hγ : ∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1))
    (h1 : ∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) (k : ℕ) (x : N)
    (hx : x ∈ n ^ k • (⊤ : Submodule A N)) :
    Y x - x ∈ n ^ (k + 1) • (⊤ : Submodule A N) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have e : Y (a • y) - a • y = γ a • (Y y - y) + (γ a - a) • y := by
      rw [hY, smul_sub, sub_smul]; abel
    have hga : γ a ∈ n ^ k := by
      have h2 : γ a - a ∈ n ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) (hγ k a ha)
      simpa using (n ^ k).add_mem h2 ha
    rw [e]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem_smul (hγ k a ha) trivial)
    rw [pow_succ, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hga (h1 y)
  · intro y z hy hz
    have e : Y (y + z) - (y + z) = (Y y - y) + (Y z - z) := by
      rw [map_add (f := _)]; abel
    rw [e]
    exact Submodule.add_mem _ hy hz

theorem semilinear_sub_one_pow_mem {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (n : Ideal A) (γ : A →+* A) (Y : N →+ N) (hY : ∀ a x, Y (a • x) = γ a • Y x)
    (hγ : ∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1))
    (h1 : ∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) (k : ℕ) (x : N) :
    ((Y.toIntLinearMap - 1 : Module.End ℤ N) ^ k) x ∈ n ^ k • (⊤ : Submodule A N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (Y.toIntLinearMap - 1 : Module.End ℤ N), Module.End.mul_apply]
    exact semilinear_sub_mem_pow_succ_smul n γ Y hY hγ h1 k _ ih

theorem semilinear_iterate_prime_pow_sub_mem :
    ∀ (l : ℕ) [Fact l.Prime] (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (n : Ideal A) (γ : A →+* A) (Y : N →+ N), (∀ a x, Y (a • x) = γ a • Y x) → (∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1)) → (∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) → ∀ b : ℕ, 1 ≤ b → ∀ x, Y^[l ^ b] x - x ∈ (Ideal.span {((l : A)) ^ 2} ⊔ n ^ (l ^ (b - 1))) • (⊤ : Submodule A N) := by
  intro l _ A N _ _ _ n γ Y hY hγ h1 b hb x
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (GlobalTheory.one_add_X_pow_prime_pow_sub_one_mem_span l b hb)
  set D : Module.End ℤ N := Y.toIntLinearMap - 1 with hD
  have h := congrArg (Polynomial.aeval D) huv
  rw [mul_comm u, mul_comm v] at h
  simp only [map_add (f := _), map_mul, map_pow, map_sub, map_one, map_natCast, Polynomial.aeval_X] at h
  have hYD : (1 + D) = Y.toIntLinearMap := by rw [hD]; abel
  rw [hYD] at h
  have h' := congrArg (fun f : Module.End ℤ N => f x) h
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply] at h'
  have e : (Y.toIntLinearMap ^ (l ^ b)) x = Y^[l ^ b] x := by
    rw [Module.End.pow_apply]; rfl
  rw [e] at h'
  rw [← h']
  refine Submodule.add_mem _ ?_ ?_
  · have e2 : ∀ y : N, (((l : Module.End ℤ N)) ^ 2) y = ((l : A) ^ 2) • y := by
      intro y
      rw [← Nat.cast_pow, ← Nat.cast_pow, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    rw [e2]
    exact Submodule.smul_mem_smul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) trivial
  · exact Submodule.smul_mono_left le_sup_right
      (semilinear_sub_one_pow_mem n γ Y hY hγ h1 _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetLIntegralAverageAbelianQuotient
section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace GlobalTheory.UnipAvg

section Covolume

variable {U : Type*} [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]

theorem measurePreserving_mulEquiv_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (c : U ≃* U) (hc : Measurable c) (hc' : Measurable c.symm)
    (h₁ : ∀ b ∈ U₀, c b ∈ U₀) (h₂ : ∀ b ∈ U₀, c.symm b ∈ U₀) : MeasurePreserving c ν ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  let e : U ≃ᵐ U := ⟨c.toEquiv, hc, hc'⟩
  haveI : SigmaFinite (ν.map c) := e.sigmaFinite_map
  haveI : (ν.map c).IsMulLeftInvariant := ⟨fun g => by
    rw [map_map (measurable_const_mul g) hc]
    conv_rhs => rw [← map_mul_left_eq_self ν (c.symm g), map_map hc (measurable_const_mul _)]
    congr 1
    ext x
    simp⟩
  have h := measure_eq_div_smul (ν.map c) ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  have hq : QuasiMeasurePreserving c ν ν := ⟨hc.aemeasurable, by rw [h]; exact smul_absolutelyContinuous⟩
  have hD' : IsFundamentalDomain U₀ (c ⁻¹' D) ν :=
    hD.preimage_of_equiv hq (e := fun b : U₀ => (⟨c.symm b, h₂ b b.2⟩ : U₀))
      ⟨fun b b' hb => Subtype.ext (c.symm.injective (congrArg Subtype.val hb)),
        fun b => ⟨⟨c b, h₁ b b.2⟩, Subtype.ext (c.symm_apply_apply b)⟩⟩
      (fun b x => by
        change c (c.symm b * x) = b * c x
        simp)
  have h1 : (ν.map c) D = 1 := by
    have : (ν.map c) D = ν (c ⁻¹' D) := e.map_apply (μ := ν) D
    rw [this, hD'.measure_eq hD, hνD]
  refine ⟨hc, ?_⟩
  rw [h, h1, hνD]; simp

theorem setLIntegral_mul_right_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (f : U → ℝ≥0∞) (hf : ∀ b ∈ U₀, ∀ u, f (b * u) = f u) (v : U) :
    ∫⁻ u in D, f (u * v) ∂ν = ∫⁻ u in D, f u ∂ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  haveI := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  have hD' : IsFundamentalDomain U₀ ((· * v) ⁻¹' D) ν :=
    hD.preimage_of_equiv (quasiMeasurePreserving_mul_right ν v) (e := id) Function.bijective_id
      (fun g x => mul_assoc (g : U) x v)
  rw [hD.setLIntegral_eq hD' (fun u => f (u * v)) (fun b x => by
    change f ((b : U) * x * v) = _
    rw [mul_assoc, hf _ b.2])]
  exact (measurePreserving_mul_right ν v).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.mulRight v).measurableEmbedding f D

end Covolume

theorem setLIntegral_add_left_of_periodic {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    (ν : Measure A) [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀] {D : Set A}
    (hD : IsAddFundamentalDomain A₀ D ν) (f : A → ℝ≥0∞) (hf : ∀ b ∈ A₀, ∀ y, f (b + y) = f y) (t : A) :
    ∫⁻ y in D, f (t + y) ∂ν = ∫⁻ y in D, f y ∂ν := by
  haveI : VAddInvariantMeasure A₀ A ν := ⟨fun γ s _ => measure_preimage_add ν (γ : A) s⟩
  have hD' : IsAddFundamentalDomain A₀ ((t + ·) ⁻¹' D) ν :=
    hD.preimage_of_equiv (measurePreserving_add_left ν t).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => add_left_comm t (g : A) x)
  rw [hD.setLIntegral_eq hD' (fun u => f (t + u)) (fun b x => by
    change f (t + ((b : A) + x)) = _
    rw [add_left_comm, hf _ b.2])]
  exact (measurePreserving_add_left ν t).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft t).measurableEmbedding f D

theorem exists_covolume_one_of_cocompact {U : Type*} [Group U] [TopologicalSpace U] [IsTopologicalGroup U]
    [LocallyCompactSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (U₀ : Subgroup U) [DiscreteTopology U₀] {K : Set U} (hK : IsCompact K) (hcov : ∀ u, ∃ b ∈ U₀, b * u ∈ K) :
    ∃ (ν : Measure U) (D : Set U), SigmaFinite ν ∧ ν.IsMulLeftInvariant ∧ IsFundamentalDomain U₀ D ν ∧ ν D = 1 := by
  haveI := countable_of_discrete_subgroup U₀
  obtain ⟨D, -, -, hD⟩ := exists_isFundamentalDomain_subgroup U₀
  let m : Measure U := haar
  haveI : SMulInvariantMeasure U₀ U m := ⟨fun γ s _ => measure_preimage_mul m (γ : U) s⟩
  have h0 : m D ≠ 0 := (hD m).measure_ne_zero (NeZero.ne m)
  have h1 : m D ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := m)))
    rw [(hD m).measure_eq_tsum K]
    refine le_trans (measure_mono fun u hu => ?_) (measure_iUnion_le _)
    obtain ⟨b, hb, hbu⟩ := hcov u
    exact mem_iUnion.2 ⟨(⟨b, hb⟩ : U₀)⁻¹, mem_inv_smul_set_iff.2 hbu, hu⟩
  haveI : ((m D)⁻¹ • m).IsHaarMeasure := IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0)
  exact ⟨(m D)⁻¹ • m, D, inferInstance, inferInstance, hD _, by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]⟩

theorem setLIntegral_average_abelian_quotient : ∀ (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (Γ U : Subgroup G) [DiscreteTopology Γ], IsClosed (U : Set G) → (∀ γ ∈ Γ, ∀ u ∈ U, γ⁻¹ * u * γ ∈ U) → (∃ K : Set G, IsCompact K ∧ ∀ u ∈ U, ∃ γ ∈ Γ, γ ∈ U ∧ γ * u ∈ K) → ∀ (ι : A → G), (∀ x y, ι (x + y) = ι x * ι y) → Measurable ι → (∀ x, ι x ∈ U) → ∀ (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀], (∀ b ∈ A₀, ι b ∈ Γ) → ∀ (D : Set A), IsAddFundamentalDomain A₀ D ν → ν D = 1 → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (Φ : G → ENNReal), Measurable Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) → (∀ u ∈ U, ∃ y : A, ∀ g, Φ (u * g) = Φ (ι y * g)) → ∫⁻ g in 𝓕, Φ g ∂μ = ∫⁻ g in 𝓕, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂μ := by
  intro G A _ _ _ _ _ _ _ _ _ _ _ _ μ _ _ Γ U _ hU hnorm ⟨K, hK, hcov⟩ ι hadd hιm hιU ν _ _ A₀ _ hA₀ D hD hνD 𝓕 h𝓕
    Φ hΦ hinv hact
  haveI := countable_of_discrete_subgroup Γ
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : DiscreteTopology (Γ.subgroupOf U) :=
    DiscreteTopology.of_continuous_injective (f := fun b : Γ.subgroupOf U => (⟨(b : U), b.2⟩ : Γ))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun b b' h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h)))
  haveI := countable_of_discrete_subgroup (Γ.subgroupOf U)
  obtain ⟨m, E, _, _, hE, hmE⟩ := exists_covolume_one_of_cocompact (Γ.subgroupOf U)
    (hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK) (fun u => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov u u.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  have hconj : ∀ a ∈ (Γ : Set G), ∃ c : U → U, MeasurePreserving c m m ∧
      ∀ u, U.subtype (c u) = a⁻¹ * U.subtype u * a := by
    intro a ha
    have ha' : ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun u hu => by simpa using hnorm a⁻¹ (Γ.inv_mem ha) u hu
    let c : U ≃* U :=
      { toFun := fun u => ⟨a⁻¹ * u * a, hnorm a ha u u.2⟩
        invFun := fun u => ⟨a * u * a⁻¹, ha' u u.2⟩
        left_inv := fun u => Subtype.ext (by simp only; group)
        right_inv := fun u => Subtype.ext (by simp only; group)
        map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    exact ⟨c, measurePreserving_mulEquiv_of_covolume_one m _ hE hmE c
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (fun b hb => Γ.mul_mem (Γ.mul_mem (Γ.inv_mem ha) hb) ha)
      (fun b hb => Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)), fun _ => rfl⟩
  rw [setLIntegral_average U.subtype Subtype.val_injective measurable_subtype_coe μ m Γ (Γ.subgroupOf U)
    (fun b hb => hb) Γ (fun γ hγ => ⟨γ, hγ, 1, one_mem _, by simp⟩) hconj hE hmE h𝓕 Φ hΦ hinv]
  refine lintegral_congr fun g => ?_
  calc ∫⁻ u in E, Φ (U.subtype u * g) ∂m = ∫⁻ _y in D, ∫⁻ u in E, Φ ((u : G) * g) ∂m ∂ν := by simp [hνD]
    _ = ∫⁻ y in D, ∫⁻ u in E, Φ ((u : G) * (ι y * g)) ∂m ∂ν := by
        refine lintegral_congr fun y => ?_
        rw [← setLIntegral_mul_right_of_covolume_one m _ hE hmE (fun u => Φ ((u : G) * g))
          (fun b hb u => by rw [Subgroup.coe_mul, mul_assoc, hinv (b : G) hb]) ⟨ι y, hιU y⟩]
        simp only [Subgroup.coe_mul, mul_assoc]
    _ = ∫⁻ u in E, ∫⁻ y in D, Φ ((u : G) * (ι y * g)) ∂ν ∂m :=
        lintegral_lintegral_swap (hΦ.comp ((measurable_subtype_coe.comp measurable_snd).mul
          ((hιm.comp measurable_fst).mul_const g))).aemeasurable
    _ = ∫⁻ _u in E, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂m := by
        refine lintegral_congr fun u => ?_
        obtain ⟨t, ht⟩ := hact u u.2
        rw [← setLIntegral_add_left_of_periodic ν A₀ hD (fun y => Φ (ι y * g))
          (fun b hb y => by rw [hadd, mul_assoc, hinv _ (hA₀ b hb)]) t]
        simp only [ht, hadd, mul_assoc]
    _ = ∫⁻ y in D, Φ (ι y * g) ∂ν := by simp [hmE]

end GlobalTheory.UnipAvg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLeOneOfSqSubSelfIntegralBasisStatement
section
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] {ι : Type} [Fintype ι] (b : Module.Basis ι E E'), (∀ i, IsIntegral ℤ (b i)) → ∀ (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E')), w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal → ∀ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) → w''.valuation E' ε ≤ 1 := by
  first | exact @GlobalTheory.integral_of_sq_sub_integral | exact GlobalTheory.integral_of_sq_sub_integral | (intros; apply GlobalTheory.integral_of_sq_sub_integral <;> assumption)
end

