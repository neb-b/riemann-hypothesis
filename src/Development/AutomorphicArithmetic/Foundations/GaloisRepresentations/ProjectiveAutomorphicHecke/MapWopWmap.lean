module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001

@[expose] public section

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open Module

universe u v

section Words

variable {F A J : Type*} [CommSemiring F] [Semiring A] [Algebra F A]

def wop (T : J → A) (t : List J →₀ F) : A := t.sum fun w c => c • (w.map T).prod

@[simp] theorem wop_zero (T : J → A) : wop T (0 : List J →₀ F) = 0 := Finsupp.sum_zero_index

theorem wop_add (T : J → A) (s t : List J →₀ F) : wop T (s + t) = wop T s + wop T t :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

@[simp] theorem wop_single (T : J → A) (w : List J) (c : F) : wop T (Finsupp.single w c) = c • (w.map T).prod :=
  Finsupp.sum_single_index (zero_smul _ _)

def wmul (s t : List J →₀ F) : List J →₀ F := s.sum fun w a => t.sum fun w' b => Finsupp.single (w ++ w') (a * b)

theorem wop_sum {ι : Type*} (T : J → A) (s : Finset ι) (f : ι → List J →₀ F) :
    wop T (∑ i ∈ s, f i) = ∑ i ∈ s, wop T (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, wop_add, ih]

theorem wop_wmul (T : J → A) (s t : List J →₀ F) : wop T (wmul s t) = wop T s * wop T t := by
  unfold wmul
  simp only [Finsupp.sum, wop_sum, wop_single]
  unfold wop
  simp only [Finsupp.sum, Finset.sum_mul_sum, List.map_append, List.prod_append, smul_mul_smul_comm]

theorem map_wop {B : Type*} [Semiring B] [Algebra F B] (g : A →ₐ[F] B) (T : J → A) (t : List J →₀ F) :
    g (wop T t) = wop (fun j => g (T j)) t := by
  unfold wop
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, map_smul, map_list_prod, List.map_map]
  rfl

def wmap {K : Type*} [CommSemiring K] (f : F →+* K) (t : List J →₀ F) : List J →₀ K := t.mapRange f f.map_zero

theorem map_wop_wmap {K B : Type*} [CommSemiring K] [Semiring B] [Algebra K B] (f : F →+* K) (g : A →+* B)
    (hg : ∀ c, g (algebraMap F A c) = algebraMap K B (f c)) (T : J → A) (t : List J →₀ F) :
    g (wop T t) = wop (fun j => g (T j)) (wmap f t) := by
  unfold wop wmap
  rw [Finsupp.sum_mapRange_index (h := fun w (c : K) => c • (List.map (fun j => g (T j)) w).prod) (fun _ => zero_smul _ _)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, Algebra.smul_def, map_mul, hg, map_list_prod, List.map_map]
  rfl

end Words

def Cert {F A J : Type*} [Field F] [Ring A] [Algebra F A] (T : J → A) (θ : J → F) (t : List J →₀ F) : Prop :=
  wop θ t = 1 ∧ IsIdempotentElem (wop T t) ∧ ∀ j, ∃ N : ℕ, (T j - algebraMap F A (θ j)) ^ N * wop T t = 0

abbrev gen {F W J : Type*} [Field F] [AddCommGroup W] [Module F W] (T : J → End F W) (θ : J → F) : Submodule F W :=
  ⨅ j, (T j).maxGenEigenspace (θ j)

def ProjOne : Prop := ∀ (F : Type) [Field F] (A : Type u) [Ring A] [Algebra F A] [Module.Finite F A] (J : Type) (T : J → A),
  (∀ i j, Commute (T i) (T j)) → ∀ θ : J → F, ∃ t, Cert T θ t

def ProjTrace : Prop := ∀ (F : Type) [Field F] (W : Type u) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  (U : Submodule F W) (p u : End F W), LinearMap.IsProj U p → ∀ h : ∀ x ∈ U, u x ∈ U,
  LinearMap.trace F W (u * p) = LinearMap.trace F U (u.restrict h)

def TracePow : Prop := ∀ (F : Type) [Field F] [CharZero F] (W : Type u) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  (q s : End F W), IsIdempotentElem q → q ≠ 0 → Commute q s → (∀ x, s (q x) = 0 → q x = 0) →
  ∀ j₀ : ℕ, ∃ j, j₀ ≤ j ∧ LinearMap.trace F W (q * s ^ j) ≠ 0

section Ext

open GlobalTheory.LKDef.HeckeTraceForms

def rop {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (r : H →₀ ℂ) (Φ : H → V) : H → V :=
  fun g => r.sum fun u a => a • Φ (g * u)

def KerForm {Γ H A V : Type} [Group Γ] [Group H] [Group A] [AddCommGroup V] [Module ℂ V] (ι : Γ →* H) (K : Subgroup H)
    (ξ : Representation ℂ Γ V) (c : H →* A) (φ : H → V) : Prop :=
  (∀ γ, ∀ k ∈ K, c (ι γ) = c k → c k = 1) ∧ (∀ γ u, c (ι γ) = 1 → c u = 1 → φ (ι γ * u) = ξ γ (φ u)) ∧
    ∀ k ∈ K, ∀ u, c k = 1 → c u = 1 → φ (u * k) = φ u

def ExtZero : Prop := ∀ (Γ H A V : Type) [Group Γ] [Group H] [Group A] [AddCommGroup V] [Module ℂ V] (ι : Γ →* H) (K : Subgroup H)
  (ξ : Representation ℂ Γ V) (c : H →* A) (φ : H → V), KerForm ι K ξ c φ →
  ∃ Φ ∈ forms ι K ξ, (∀ u, c u = 1 → Φ u = φ u) ∧ ∀ g, Φ g ≠ 0 → ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k

def CentralChar {Γ H Z V : Type} [Group Γ] [Group H] [Group Z] [AddCommGroup V] [Module ℂ V] (ι : Γ →* H) (K : Subgroup H)
    (ξ : Representation ℂ Γ V) (ζ : Z →* H) (ψ : Z →* ℂˣ) (Φ : H → V) : Prop :=
  (∀ z g, Φ (g * ζ z) = (ψ z : ℂ) • Φ g) ∧ (∀ z, ζ z ∈ K → ψ z = 1) ∧
    ∀ z γ (a : ℂ), ζ z = ι γ → (∀ v, ξ γ v = a • v) → (ψ z : ℂ) = a

end Ext

end UpperTheory.Gal.CertificateRingHomMap

end
