module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0007

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.DualBasis
section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc

abbrev Oloc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

abbrev Lloc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (Lb : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (Oloc F E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (Oloc F E v) Lb

abbrev hloc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (z y : Fin n → E ⊗[F] v.adicCompletion F) : E ⊗[F] v.adicCompletion F :=
  hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z y

def SigInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)),
    ∀ c ∈ Oloc F E v, sigR σ (v.adicCompletion F) c ∈ Oloc F E v

def UnitLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (s : 𝓞 F), s ∉ v.asIdeal →
    ∃ u ∈ Oloc F E v, inclE (F := F) (v.adicCompletion F) (algebraMap F E (s : F)) * u = 1

def Nondeg : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ),
    Module.Finite (𝓞 E) Lb →
    (∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) → (T : E) • y ∈ Lb) →
    T ≠ 0 → ∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y = 0) → y = 0

def SpanTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ),
    Module.Finite (𝓞 E) Lb →
    (∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) → (T : E) • y ∈ Lb) →
    T ≠ 0 → Submodule.span E (Lb : Set (Fin n → E)) = ⊤

def LocBasis : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (Lb : Submodule (𝓞 E) (Fin n → E)),
    Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ →
    ∃ (x : Fin n → Fin n → E) (s : 𝓞 F), s ∉ v.asIdeal ∧ (∀ i, x i ∈ Lb) ∧
      ∀ z ∈ Lb, ∃ a : Fin n → 𝓞 E, algebraMap F E (s : F) • z = ∑ i, ((a i : 𝓞 E) : E) • x i

def DualBasis : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x : Fin n → Fin n → E),
    Submodule.span E (Set.range x) = ⊤ →
    (∀ y : Fin n → E, (∀ i, hform (σ : E →+* E) J (x i) y = 0) → y = 0) →
    ∃ y : Fin n → Fin n → E, (∀ i j, hform (σ : E →+* E) J (x i) (y j) = if i = j then 1 else 0) ∧
      ∀ w : Fin n → E, ∃ c : Fin n → E, w = ∑ j, c j • y j

def FwdDir : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Lb : Submodule (𝓞 E) (Fin n → E)),
    (∀ x ∈ Lb, ∀ y ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) →
    ∀ y ∈ Lloc F E n v Lb, ∀ z ∈ Lloc F E n v Lb, hloc σ J v z y ∈ Oloc F E v

def BwdDir : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ),
    Module.Finite (𝓞 E) Lb →
    (∀ x ∈ Lb, ∀ y ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) →
    (∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) → (T : E) • y ∈ Lb) →
    (T : 𝓞 F) ∉ v.asIdeal →
    ∀ y, (∀ z ∈ Lloc F E n v Lb, hloc σ J v z y ∈ Oloc F E v) → y ∈ Lloc F E n v Lb

end PI.SelfDualLoc.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.HformSumRight
section
open Matrix

noncomputable section

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (σ : A →+* A) (J : Matrix n n A)

theorem hform_add_right (x y y' : n → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [PI.SelfDualLoc.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right (x : n → A) (c : A) (y : n → A) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [PI.SelfDualLoc.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_add_left (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [PI.SelfDualLoc.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (c : A) (x y : n → A) :
    hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [PI.SelfDualLoc.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_zero_left (y : n → A) : hform σ J 0 y = 0 := by
  simp [PI.SelfDualLoc.hform]

theorem hform_zero_right (x : n → A) : hform σ J x 0 = 0 := by
  simp [PI.SelfDualLoc.hform]

theorem hform_sum_right {ι : Type} (s : Finset ι) (x : n → A) (f : ι → n → A) :
    hform σ J x (∑ k ∈ s, f k) = ∑ k ∈ s, hform σ J x (f k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hform_zero_right σ J x
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_right, ih]

theorem hform_sum_left {ι : Type} (s : Finset ι) (f : ι → n → A) (y : n → A) :
    hform σ J (∑ k ∈ s, f k) y = ∑ k ∈ s, hform σ J (f k) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hform_zero_left σ J y
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_left, ih]

theorem hform_map {B : Type} [CommRing B] (τ : B →+* B) (f : A →+* B)
    (hf : ∀ a, f (σ a) = τ (f a)) (x y : n → A) :
    hform τ (J.map f) (fun i => f (x i)) (fun i => f (y i)) = f (hform σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PI.SelfDualLoc.hform, map_sum, map_mul, hf, Matrix.map_apply]

end PI.SelfDualLoc.W
end
end

