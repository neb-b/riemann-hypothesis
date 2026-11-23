module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
section
namespace GlobalTheory

open scoped BigOperators

section JetWedge

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}

noncomputable def jetWedge (ω : M [⋀^Fin D]→ₗ[A] N) : (A × M) [⋀^Fin (D + 1)]→ₗ[A] N :=
  AlternatingMap.alternatizeUncurryFin
    ((LinearMap.fst A A M).smulRight (ω.compLinearMap (LinearMap.snd A A M)))

theorem jetWedge_apply (ω : M [⋀^Fin D]→ₗ[A] N) (v : Fin (D + 1) → A × M) :
    jetWedge ω v =
      ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * (v i).1) • ω (fun k => (v (i.succAbove k)).2) := by
  rw [jetWedge, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, ← Int.cast_smul_eq_zsmul A]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  rfl

theorem jetWedge_shear (ω : M [⋀^Fin D]→ₗ[A] N) (h : A) (u : M) (v : Fin (D + 1) → A × M) :
    jetWedge ω (fun i => (h * (v i).1, h • (v i).2 + (v i).1 • u)) = h ^ (D + 1) • jetWedge ω v := by
  classical
  let φ : (A × M) →ₗ[A] (A × M) :=
    (h • LinearMap.fst A A M).prod (h • LinearMap.snd A A M + (LinearMap.fst A A M).smulRight u)
  let g : Option M → A × M := fun o => o.elim (1, 0) (fun m => (0, m))
  have hg : Submodule.span A (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, m⟩ -
    have : ((a, m) : A × M) = a • g none + g (some m) := by simp [g]
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))
      (Submodule.subset_span ⟨some m, rfl⟩)
  have key : ((jetWedge ω).compLinearMap φ).toMultilinearMap
      = (h ^ (D + 1) • jetWedge ω).toMultilinearMap := by
    refine MultilinearMap.ext_of_span_eq_top (g := fun _ => g) (fun _ => hg) fun j => ?_
    change jetWedge ω (fun i => φ (g (j i))) = h ^ (D + 1) • jetWedge ω (fun i => g (j i))
    by_cases hj : ∃ a b, a ≠ b ∧ j a = j b
    · obtain ⟨a, b, hab, hjab⟩ := hj
      rw [(jetWedge ω).map_eq_zero_of_eq _ (i := a) (j := b) (by simp only [hjab]) hab,
        (jetWedge ω).map_eq_zero_of_eq _ (i := a) (j := b) (by simp only [hjab]) hab, smul_zero]
    · push Not at hj
      rw [jetWedge_apply, jetWedge_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases hi : j i with
      | some m => simp [φ, g]
      | none =>
        have hk : ∀ k : Fin D, (g (j (i.succAbove k))).1 = 0 := by
          intro k
          cases hk : j (i.succAbove k) with
          | some m => simp [g]
          | none => exact absurd (hk.trans hi.symm) (hj _ _ (Fin.succAbove_ne i k))
        have : (fun k : Fin D => (φ (g (j (i.succAbove k)))).2)
            = fun k : Fin D => h • (g (j (i.succAbove k))).2 := by
          funext k
          simp [φ, hk k]
        rw [this, ω.map_smul_univ (fun _ => h)]
        simp only [φ, g, smul_smul]
        congr 1
        simp
        ring
  exact congrArg (fun F => F v) key

theorem alternating_map_sum_smul_eq_det_smul {n : ℕ} (ω : M [⋀^Fin n]→ₗ[A] N)
    (a : Matrix (Fin n) (Fin n) A) (w : Fin n → M) :
    ω (fun i => ∑ k, a i k • w k) = a.det • ω w := by
  classical
  let φ : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A w
  have key : ω.compLinearMap φ
      = ((LinearMap.toSpanSingleton A N (ω w)).compAlternatingMap Matrix.detRowAlternating) := by
    refine Module.Basis.ext_alternating (Pi.basisFun A (Fin n)) fun v hv => ?_
    have hb : Function.Bijective v := Finite.injective_iff_bijective.mp hv
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v hb
    have e1 : (fun i => (Pi.basisFun A (Fin n)) (v i)) = (Pi.basisFun A (Fin n)) ∘ σ := rfl
    rw [e1, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e2 : (Matrix.detRowAlternating : (Fin n → A) [⋀^Fin n]→ₗ[A] A) (Pi.basisFun A (Fin n))
        = 1 := by
      rw [← Matrix.det_one (n := Fin n)]
      change Matrix.det _ = _
      congr 1
      ext i j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simp only [LinearMap.compAlternatingMap_apply, e2, LinearMap.toSpanSingleton_apply, one_smul,
      AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp [φ]
  have := congrArg (fun F : (Fin n → A) [⋀^Fin n]→ₗ[A] N => F a) key
  have e3 : (fun i => ∑ k, a i k • w k) = fun i => φ (a i) := by
    funext i
    exact (Fintype.linearCombination_apply A w (a i)).symm
  rw [e3]
  exact this

theorem alternating_sub_mem_smul_top (ω : M [⋀^Fin D]→ₗ[A] N) (I : Ideal A) (v w : Fin D → M)
    (hvw : ∀ k, v k - w k ∈ I • (⊤ : Submodule A M)) :
    ω v - ω w ∈ I • (⊤ : Submodule A N) := by
  classical
  have key : ∀ s : Finset (Fin D), ω (s.piecewise v w) - ω w ∈ I • (⊤ : Submodule A N) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have h1 : s.piecewise v w = Function.update (s.piecewise v w) i (w i) := by
        rw [eq_comm, Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hi]
      have h2 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          = ω.toMultilinearMap.toLinearMap (s.piecewise v w) i (v i - w i) := by
        rw [map_sub, Finset.piecewise_insert]
        conv_lhs => rw [h1]
        simp
      have h3 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          ∈ I • (⊤ : Submodule A N) := by
        rw [h2]
        have := Submodule.mem_map_of_mem
          (f := ω.toMultilinearMap.toLinearMap (s.piecewise v w) i) (hvw i)
        rw [Submodule.map_smul''] at this
        exact Submodule.smul_mono le_rfl le_top this
      simpa using add_mem h3 ih
  simpa using key Finset.univ

end JetWedge

section JacForm

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}

noncomputable def jacForm (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)
    (f : Fin (D + 1) → A) : N :=
  ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * f i) • ω (fun k => d (f (i.succAbove k)))

variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)

theorem jacForm_eq_jetWedge (f : Fin (D + 1) → A) :
    jacForm d ω f = jetWedge ω (fun i => (f i, d (f i))) := by
  rw [jetWedge_apply, jacForm]

theorem jacForm_mul (h : A) (f : Fin (D + 1) → A) :
    jacForm d ω (fun i => h * f i) = h ^ (D + 1) • jacForm d ω f := by
  rw [jacForm_eq_jetWedge, jacForm_eq_jetWedge, ← jetWedge_shear ω h (d h)]
  simp only [Derivation.leibniz]

theorem form_d_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    ω (fun k => d (h * g k)) - h ^ D • ω (fun k => d (g k)) ∈ I • (⊤ : Submodule A N) := by
  have : h ^ D • ω (fun k => d (g k)) = ω (fun k => h • d (g k)) := by
    rw [ω.map_smul_univ (fun _ => h)]
    simp
  rw [this]
  refine alternating_sub_mem_smul_top ω I _ _ fun k => ?_
  rw [Derivation.leibniz, add_sub_cancel_left]
  exact Submodule.smul_mem_smul (hg k) Submodule.mem_top

variable [Module R N] [IsScalarTower R A N] [IsScalarTower R A M]

end JacForm

section RestrictScalars

variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}

def altRestrictScalars (ω : M [⋀^Fin D]→ₗ[B] N) : M [⋀^Fin D]→ₗ[A] N where
  toMultilinearMap := ω.toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' v _ _ hv hij := ω.map_eq_zero_of_eq v hv hij

variable {A} {L : Type*} [AddCommGroup L] [Module A L]

variable (B D) in
noncomputable def exteriorPowerMapOver (φ : L →ₗ[A] M) : (⋀[A]^D L) →ₗ[A] (⋀[B]^D M) :=
  exteriorPower.alternatingMapLinearEquiv
    ((altRestrictScalars A (exteriorPower.ιMulti B D (M := M))).compLinearMap φ)

@[simp] theorem exteriorPowerMapOver_ιMulti (φ : L →ₗ[A] M) (v : Fin D → L) :
    exteriorPowerMapOver B D φ (exteriorPower.ιMulti A D v)
      = exteriorPower.ιMulti B D (fun k => φ (v k)) := by
  simp only [exteriorPowerMapOver,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

end RestrictScalars

section Jac

variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}

open KaehlerDifferential

noncomputable def dWedge (g : Fin D → A) : ⋀[A]^D Ω[A⁄R] :=
  exteriorPower.ιMulti A D (fun k => KaehlerDifferential.D R A (g k))

noncomputable def jac (f : Fin (D + 1) → A) : ⋀[A]^D Ω[A⁄R] :=
  ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * f i) • dWedge R (fun k => f (i.succAbove k))

theorem jac_mul (h : A) (f : Fin (D + 1) → A) :
    jac R (fun i => h * f i) = h ^ (D + 1) • jac R f :=
  jacForm_mul _ _ h f

theorem dWedge_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    dWedge R (fun k => h * g k) - h ^ D • dWedge R g ∈ I • (⊤ : Submodule A (⋀[A]^D Ω[A⁄R])) :=
  form_d_mul_sub_mem _ _ I h g hg


variable {R}

theorem map_jac (S B : Type*) [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [IsScalarTower R S B] [SMulCommClass S A B]
    (f : Fin (D + 1) → A) :
    exteriorPowerMapOver B D (KaehlerDifferential.map R S A B) (jac R f)
      = jac S (fun i => algebraMap A B (f i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [jac, jac, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, dWedge, exteriorPowerMapOver_ιMulti, ← algebraMap_smul B]
  simp [dWedge]

end Jac

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CoeConjEquivSymm
section
namespace GlobalTheory.ConjugationEquiv

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjEquiv (N : Subgroup G) (b : G) (hb : ∀ u : G, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N where
  toFun u := ⟨b * (u : G) * b⁻¹, (hb u).1 u.2⟩
  invFun u := ⟨b⁻¹ * (u : G) * b, (hb _).2 (by
    have h : b * (b⁻¹ * (u : G) * b) * b⁻¹ = u := by group
    rw [h]; exact u.2)⟩
  left_inv u := Subtype.ext (by
    show b⁻¹ * (b * (u : G) * b⁻¹) * b = u
    group)
  right_inv u := Subtype.ext (by
    show b * (b⁻¹ * (u : G) * b) * b⁻¹ = u
    group)
  map_mul' u v := Subtype.ext (by
    show b * ((u : G) * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹)
    group)
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end GlobalTheory.ConjugationEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ContrAtEqComapMap
section
namespace GlobalTheory.LocalSaturationContraction

variable {B : Type*} [CommRing B]

def satAt (b : B) (P : Ideal B) [hP : P.IsPrime] : Ideal B where
  carrier := {x | ∃ s, s ∉ P ∧ s * x ∈ Ideal.span {b}}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one P).1 hP.ne_top, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    have : s * t * (x + y) = t * (s * x) + s * (t * y) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ hy)
  smul_mem' := by
    rintro c x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    have : s * (c • x) = c * (s * x) := by rw [smul_eq_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hx

variable (b : B) (P : Ideal B) [P.IsPrime]

end GlobalTheory.LocalSaturationContraction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ContractMultilinearApply
section
open scoped TensorProduct BigOperators

namespace GlobalTheory.MultilinearContraction

section

variable {ι : Type*} [Fintype ι] [dι : DecidableEq ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

omit [Fintype ι] dι in
private theorem apply_update (φ : ∀ i, X i →ₗ[R] R) [inst : DecidableEq ι] (x : ∀ i, X i) (k : ι)
    (y : X k) (i : ι) :
    φ i (Function.update x k y i) = Function.update (fun i => φ i (x i)) k (φ k y) i := by
  by_cases h : i = k
  · subst h
    simp
  · simp [Function.update_of_ne h]

def contractMultilinear (φ : ∀ i, X i →ₗ[R] R) (j : ι) : (Π i, X i) →ₘₗ[R] X j where
  toFun x := (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j
  map_update_add' := by
    intro inst x k y z
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [apply_update]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁,
        Function.update_self, smul_add]
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_add (f := _),
        add_mul, add_smul]
  map_update_smul' := by
    intro inst x k c y
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [apply_update]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁, Function.update_self, RingHom.id_apply]
      exact smul_comm _ _ _
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_smul,
        RingHom.id_apply, smul_eq_mul, mul_assoc, mul_smul]

@[simp] theorem contractMultilinear_apply (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contractMultilinear φ j x = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := rfl

noncomputable def contract (φ : ∀ i, X i →ₗ[R] R) (j : ι) : (⨂[R] i, X i) →ₗ[R] X j :=
  PiTensorProduct.lift (contractMultilinear φ j)

theorem contract_def (φ : ∀ i, X i →ₗ[R] R) (j : ι) :
    contract φ j = PiTensorProduct.lift (contractMultilinear φ j) := rfl

@[simp] theorem contract_tprod (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contract φ j (⨂ₜ[R] i, x i) = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := by
  rw [contract_def, PiTensorProduct.lift.tprod, contractMultilinear_apply]

end

section

variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

def prodMultilinear (φ : ∀ i, X i →ₗ[R] R) : (Π i, X i) →ₘₗ[R] R :=
  (MultilinearMap.mkPiAlgebra R ι R).compLinearMap φ

@[simp] theorem prodMultilinear_apply (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodMultilinear φ x = ∏ i, φ i (x i) := rfl

noncomputable def prodForm (φ : ∀ i, X i →ₗ[R] R) : (⨂[R] i, X i) →ₗ[R] R :=
  PiTensorProduct.lift (prodMultilinear φ)

theorem prodForm_def (φ : ∀ i, X i →ₗ[R] R) :
    prodForm φ = PiTensorProduct.lift (prodMultilinear φ) := rfl

@[simp] theorem prodForm_tprod (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodForm φ (⨂ₜ[R] i, x i) = ∏ i, φ i (x i) := by
  rw [prodForm_def, PiTensorProduct.lift.tprod, prodMultilinear_apply]

end

end GlobalTheory.MultilinearContraction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DoubleCosetSetoidRelIffMem
section
namespace GlobalTheory.DoubleCosetSetoid

section Rep

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

def repStabilizer (ρ : Representation k G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]

end Rep

section Cont

variable {𝕜 G E : Type*} [NontriviallyNormedField 𝕜] [Group G] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]

def clmStabilizer (π : G →* (E →L[𝕜] E)) (v : E) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ContinuousLinearMap.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply]

end Cont

section DoubleCoset

variable {G : Type*} [Group G]

def doubleCosetSetoid (H K : Subgroup G) : Setoid G where
  r x y := ∃ h ∈ H, ∃ k ∈ K, y = h * x * k
  iseqv :=
    { refl := fun x => ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      symm := by
        rintro x y ⟨h, hh, k, hk, rfl⟩
        exact ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, by group⟩
      trans := by
        rintro x y z ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        exact ⟨h' * h, H.mul_mem hh' hh, k * k', K.mul_mem hk hk', by group⟩ }

end DoubleCoset

end GlobalTheory.DoubleCosetSetoid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
section
namespace GlobalTheory.AddEquivOfSurjectiveKernel

universe u_1 u_2 u_3

theorem exists_addEquiv_of_surjective_of_ker_iff {A : Type u_1} {B : Type u_2} {C : Type u_3}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : A →+ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a : A, f a = 0 ↔ g a = 0) :
    ∃ e : B ≃+ C, ∀ a : A, e (f a) = g a := by
  have key : ∀ a b : A, f a = f b ↔ g a = g b := by
    intro a b
    rw [← sub_eq_zero, ← map_sub, h, map_sub, sub_eq_zero]
  choose s hs using hf
  choose t ht using hg
  have h1 : ∀ a, g (s (f a)) = g a := fun a => (key _ _).1 (hs _)
  have h2 : ∀ a, f (t (g a)) = f a := fun a => (key _ _).2 (ht _)
  refine ⟨{ toFun := fun b => g (s b)
            invFun := fun c => f (t c)
            left_inv := fun b => by
              show f (t (g (s b))) = b
              rw [h2, hs]
            right_inv := fun c => by
              show g (s (f (t c))) = c
              rw [h1, ht]
            map_add' := fun x y => by
              show g (s (x + y)) = g (s x) + g (s y)
              rw [← map_add (f := _), ← key, map_add (f := _), hs, hs, hs] }, fun a => h1 a⟩

end GlobalTheory.AddEquivOfSurjectiveKernel
end

