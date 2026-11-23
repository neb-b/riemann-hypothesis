module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0011
public import GroundTheory.HeightsAndTheta.Theta.CMDatum
public import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.MemRangeIffIsIntegral

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace UnitaryReduction

namespace DualHomPf

open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate

section NumberFieldFacts

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

open Classical

end NumberFieldFacts

section DualLattice

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

end DualLattice

section DualBasis

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_extend_of_submodule (A : Submodule (𝓞 E) V) (s : A →ₗ[𝓞 E] 𝓞 E) :
    ∃ σ : V →ₗ[E] E, ∀ x : A, σ (x : V) = ((s x : 𝓞 E) : E) := by
  classical
  obtain ⟨bs, hbA, _hspan, hli⟩ := exists_linearIndependent E (A : Set V)
  let bb := Basis.span hli
  let σ₀ := bb.constr E (fun i : bs => ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E))
  obtain ⟨σ, hσ⟩ := LinearMap.exists_extend σ₀
  have hrange : Set.range ((↑) : bs → V) = bs := Subtype.range_coe
  have hσb : ∀ i : bs, σ (i : V) = ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E) := by
    intro i
    have hi : (i : V) ∈ Submodule.span E (Set.range ((↑) : bs → V)) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 : σ (i : V) = σ₀ ⟨i, hi⟩ := by
      rw [← hσ]; rfl
    have h2 : (⟨i, hi⟩ : Submodule.span E (Set.range ((↑) : bs → V))) = bb i := by
      ext; rw [Basis.span_apply]
    rw [h1, h2, Basis.constr_basis]

  have hP : ∀ y ∈ Submodule.span (𝓞 E) (bs : Set V), ∀ hy : y ∈ A,
      σ y = ((s ⟨y, hy⟩ : 𝓞 E) : E) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => intro hxA; exact hσb ⟨x, hx⟩
    | zero => intro h0; simp [show (⟨0, h0⟩ : A) = 0 from rfl]
    | add x y hx hy ihx ihy =>
      intro hxyA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have hyA : y ∈ A := Submodule.span_le.mpr hbA hy
      rw [map_add (f := _), ihx hxA, ihy hyA, show (⟨x + y, hxyA⟩ : A) = ⟨x, hxA⟩ + ⟨y, hyA⟩ from rfl,
        map_add]
      push_cast; rfl
    | smul c x hx ihx =>
      intro hcxA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have e1 : σ (c • x) = (c : E) * σ x := by
        rw [← algebraMap_smul E c x, LinearMap.map_smul, smul_eq_mul,
          RingOfIntegers.coe_eq_algebraMap]
      have e2 : s ⟨c • x, hcxA⟩ = c * s ⟨x, hxA⟩ := by
        rw [show (⟨c • x, hcxA⟩ : A) = c • ⟨x, hxA⟩ from rfl, LinearMap.map_smul, smul_eq_mul]
      rw [e1, e2, ihx hxA]
      simp
  refine ⟨σ, fun x => ?_⟩
  have hx : (x : V) ∈ Submodule.span E (bs : Set V) := by
    rw [_hspan]; exact Submodule.subset_span x.2
  obtain ⟨m, c, v, hv, hxv⟩ : ∃ (m : ℕ) (c : Fin m → E) (v : Fin m → V), (∀ i, v i ∈ bs) ∧
      (x : V) = ∑ i, c i • v i := by
    obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').mp hx
    exact ⟨m, c, fun i => (g i : V), fun i => (g i).2, hg.symm⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ c
  choose o ho using fun i => hd i (Finset.mem_univ i)
  have hdx : ((d : 𝓞 E) : E) • (x : V) = ∑ i, o i • v i := by
    rw [hxv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul E (o i) (v i), ho i, Algebra.smul_def, mul_smul,
      RingOfIntegers.coe_eq_algebraMap]
  have hyP : ∑ i, o i • v i ∈ Submodule.span (𝓞 E) (bs : Set V) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hv i))
  have hyA : ∑ i, o i • v i ∈ A := Submodule.span_le.mpr hbA hyP
  have key := hP _ hyP hyA
  have hyeq : (⟨∑ i, o i • v i, hyA⟩ : A) = (d : 𝓞 E) • x := by
    apply Subtype.ext
    change (∑ i, o i • v i) = (d : 𝓞 E) • (x : V)
    rw [← hdx, ← algebraMap_smul E (d : 𝓞 E) (x : V), RingOfIntegers.coe_eq_algebraMap]
  rw [hyeq, map_smul, smul_eq_mul, ← hdx, map_smul, smul_eq_mul] at key
  have hd0 : ((d : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero d (by exact_mod_cast h)
  push_cast at key
  exact mul_left_cancel₀ hd0 key

end DualBasis

section DualBasis2

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_dualBasis (A : Submodule (𝓞 E) V) (hA : A.FG) :
    ∃ (n : ℕ) (a : Fin n → V) (σ : Fin n → (V →ₗ[E] E)),
      (∀ i, a i ∈ A) ∧ (∀ i, ∀ x ∈ A, σ i x ∈ Set.range (algebraMap (𝓞 E) E)) ∧
      ∀ x ∈ espan A, x = ∑ i, σ i x • a i := by
  classical
  have : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.mpr hA
  have : Module.Flat (𝓞 E) A := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have h1 : ((a : 𝓞 E) : E) • (x : V) = 0 := by
      rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
      exact congrArg Subtype.val ha
    have ha0 : ((a : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero a (by exact_mod_cast h)
    rw [Submodule.mem_bot]
    exact Subtype.ext ((smul_eq_zero.mp h1).resolve_left ha0)
  have : Module.FinitePresentation (𝓞 E) A := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) A := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) A
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  choose σ hσ using fun i : Fin n => exists_extend_of_submodule A ((LinearMap.proj i).comp h)
  have hxA : ∀ x : A, (x : V) = ∑ i, σ i x • (f (Pi.single i 1) : V) := by
    intro x
    have h1 : x = f (h x) := (LinearMap.congr_fun hh x).symm
    have h2 : h x = ∑ i, h x i • (Pi.single i 1 : Fin n → 𝓞 E) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h1, h2]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.coe_smul, hσ i x, ← algebraMap_smul E (h x i),
      RingOfIntegers.coe_eq_algebraMap]
    rfl
  refine ⟨n, fun i => (f (Pi.single i 1) : V), σ, fun i => (f (Pi.single i 1)).2, ?_, ?_⟩
  · intro i x hx
    exact ⟨h ⟨x, hx⟩ i, by rw [hσ i ⟨x, hx⟩, RingOfIntegers.coe_eq_algebraMap]; rfl⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hxA ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz =>
      conv_lhs => rw [hy, hz]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [map_add (f := _), add_smul]
    | smul c y _ hy =>
      conv_lhs => rw [hy]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]

end DualBasis2

section Fibres

variable {E : Type} [Field E] [NumberField E]

variable (S : MetSpace E) (τ : InfinitePlace E)

end Fibres

section Adjoints

variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]

end Adjoints

section IdealMaps

variable {E : Type} [Field E] [NumberField E]
variable {V V' : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']

end IdealMaps

section FibMaps

variable {E : Type} [Field E] [NumberField E]

end FibMaps

end DualHomPf

open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace DualHomPf
open scoped InnerProductSpace nonZeroDivisors

end UnitaryReduction

end GroundTheory.Heights₂.Theta
