module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

@[expose] public section

noncomputable section

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.CuspMult GlobalTheory.SmallThetaModules UniformSpace Filter
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
open scoped InnerProductSpace ComplexConjugate TensorProduct

namespace GlobalTheory.AutMult

section Two

variable {G G₁ G₂ H H₁ H₂ : Type} [Group G] [Group G₁] [Group G₂] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

def IsTensorMap (p₁ : G →* G₁) (p₂ : G →* G₂) (π₁ : G₁ →* (H₁ →L[ℂ] H₁)) (π₂ : G₂ →* (H₂ →L[ℂ] H₂))
    (π : G →* (H →L[ℂ] H)) (J : H₁ ⊗[ℂ] H₂ →ₗᵢ[ℂ] H) : Prop :=
  DenseRange J ∧ ∀ g x y, π g (J (x ⊗ₜ y)) = J (π₁ (p₁ g) x ⊗ₜ π₂ (p₂ g) y)


variable (H₁ H₂) in
abbrev HTensor : Type := Completion (H₁ ⊗[ℂ] H₂)

def hTensor (p₁ : G →* G₁) (p₂ : G →* G₂) (π₁ : G₁ →* (H₁ →L[ℂ] H₁)) (π₂ : G₂ →* (H₂ →L[ℂ] H₂)) :
    G →* (HTensor H₁ H₂ →L[ℂ] HTensor H₁ H₂) where
  toFun g := (TensorProduct.mapL (π₁ (p₁ g)) (π₂ (p₂ g))).completion
  map_one' := ContinuousLinearMap.ext fun z => Completion.induction_on z
    (isClosed_eq (ContinuousLinearMap.continuous _) continuous_id) fun a => by
      rw [ContinuousLinearMap.completion_apply_coe, map_one, map_one, map_one, map_one]
      exact congrArg _ (by simp [ContinuousLinearMap.one_def])
  map_mul' g h := ContinuousLinearMap.ext fun z => Completion.induction_on z
    (isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)) fun a => by
      simp only [map_mul, TensorProduct.mapL_mul, mul_apply_eq_comp, ContinuousLinearMap.completion_apply_coe]

variable {p₁ : G →* G₁} {p₂ : G →* G₂} {π₁ : G₁ →* (H₁ →L[ℂ] H₁)} {π₂ : G₂ →* (H₂ →L[ℂ] H₂)} {π : G →* (H →L[ℂ] H)}
  {J : H₁ ⊗[ℂ] H₂ →ₗᵢ[ℂ] H}

theorem hTensor_coe (g : G) (a : H₁ ⊗[ℂ] H₂) :
    hTensor p₁ p₂ π₁ π₂ g a = TensorProduct.mapL (π₁ (p₁ g)) (π₂ (p₂ g)) a :=
  ContinuousLinearMap.completion_apply_coe _ a

end Two

section Many

variable {ι G H W : Type} {Γ Hs N : ι → Type} [Group G] [∀ i, Group (Γ i)] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [AddCommGroup W] [Module ℂ W]
  [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]

structure IsRestrTensor (p : ∀ i, G →* Γ i) (δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)) (ξ : ∀ i, Hs i)
    (π : G →* (H →L[ℂ] H)) (B : (∀ i, Hs i) → H) : Prop where

  unit : ∀ᶠ i in cofinite, ‖ξ i‖ = 1

  fixed : ∀ g, ∀ᶠ i in cofinite, δ i (p i g) (ξ i) = ξ i

  inner_pure : ∀ y y', Restr ξ y → Restr ξ y' → ⟪B y', B y⟫_ℂ = ∏ᶠ i, ⟪y' i, y i⟫_ℂ

  dense : (Submodule.span ℂ {v | ∃ y, Restr ξ y ∧ v = B y}).topologicalClosure = ⊤

  apply_pure : ∀ g y, Restr ξ y → π g (B y) = B fun i => δ i (p i g) (y i)

theorem restr_map {M : ι → Type} {ξ y : ∀ i, M i} {f : ∀ i, M i → M i} (hf : ∀ᶠ i in cofinite, f i (ξ i) = ξ i)
    (hy : Restr ξ y) : Restr ξ fun i => f i (y i) :=
  (Set.Finite.union hy hf).subset fun i hi => by
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, not_or, not_not] at hn
    exact hi ((congrArg (f i) hn.1).trans hn.2)

theorem restr_self {M : ι → Type} (ξ : ∀ i, M i) : Restr ξ ξ := by simp [Restr]

variable {p : ∀ i, G →* Γ i} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)} {ξ y y' : ∀ i, Hs i} {π : G →* (H →L[ℂ] H)}
  {B : (∀ i, Hs i) → H}

theorem IsRestrTensor.finite_mulSupport (h : IsRestrTensor p δ ξ π B) (hy : Restr ξ y) (hy' : Restr ξ y') :
    (Function.mulSupport fun i => ⟪y' i, y i⟫_ℂ).Finite :=
  ((Set.Finite.union hy hy').union h.unit).subset fun i hi => by
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, not_or, not_not] at hn
    exact hi (by beta_reduce; rw [hn.1.1, hn.1.2, inner_self_eq_norm_sq_to_K, hn.2]; simp)

theorem IsRestrTensor.ext (h : IsRestrTensor p δ ξ π B) {v w : H} (e : ∀ y, Restr ξ y → ⟪B y, v⟫_ℂ = ⟪B y, w⟫_ℂ) :
    v = w := by
  have : (Submodule.span ℂ {v | ∃ y, Restr ξ y ∧ v = B y}).topologicalClosure ≤ (ℂ ∙ (v - w))ᗮ :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 (by rw [inner_sub_right, e y hy, sub_self])))
      (Submodule.isClosed_orthogonal _)
  exact sub_eq_zero.1 (inner_self_eq_zero.1
    (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (this (h.dense.ge Submodule.mem_top))))

theorem IsRestrTensor.inner_update [DecidableEq ι] (h : IsRestrTensor p δ ξ π B) (hy : Restr ξ y) (hy' : Restr ξ y')
    (i : ι) (x : Hs i) :
    ⟪B y', B (Function.update y i x)⟫_ℂ = ⟪y' i, x⟫_ℂ * ∏ᶠ (j) (_ : j ≠ i), ⟪y' j, y j⟫_ℂ := by
  rw [h.inner_pure _ _ (restr_update hy i x) hy',
    ← mul_finprod_cond_ne i (h.finite_mulSupport (restr_update hy i x) hy'), Function.update_self]
  congr 1
  exact finprod_congr fun j => finprod_congr fun hj => by rw [Function.update_of_ne hj]

theorem IsRestrTensor.pure_update [DecidableEq ι] (h : IsRestrTensor p δ ξ π B) (hy : Restr ξ y) (i : ι) (c : ℂ)
    (a b : Hs i) : B (Function.update y i (c • a + b)) = c • B (Function.update y i a) + B (Function.update y i b) :=
  h.ext fun z hz => by
    simp only [inner_add_right, inner_smul_right, h.inner_update hy hz]
    ring

def restrRep (p : ∀ i, G →* Γ i) (σ : ∀ i, Representation ℂ (Γ i) (N i)) (s : ∀ i, N i)
    (h : ∀ g, ∀ᶠ i in cofinite, σ i (p i g) (s i) = s i) : Representation ℂ G (RTens s) :=
  let a : G → AdmFun s → AdmFun s := fun g l => ⟨fun i => l.1 i ∘ₗ σ i (p i g),
    (Set.Finite.union l.2 (h g)).subset fun i hi => by
      by_contra hn
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, not_or, not_not] at hn
      exact hi ((congrArg (l.1 i) hn.2).trans hn.1)⟩
  { toFun := fun g => (LinearMap.funLeft ℂ ℂ (a g)).restrict (p := RTens s) (q := RTens s) fun _ hz =>
      (Submodule.span_le (p := (RTens s).comap (LinearMap.funLeft ℂ ℂ (a g)))).2 (by
        rintro _ ⟨y, hy, rfl⟩
        exact Submodule.subset_span ⟨_, restr_map (f := fun i => σ i (p i g)) (h g) hy, rfl⟩) hz
    map_one' := LinearMap.ext fun z => Subtype.ext (funext fun l => congrArg z.1 (Subtype.ext (funext fun i => by
      simp only [a, map_one]; rfl)))
    map_mul' := fun g g' => LinearMap.ext fun z => Subtype.ext (funext fun l => congrArg z.1 (Subtype.ext
      (funext fun i => by simp only [a, map_mul]; rfl))) }

def IsRestrTensorAlg (p : ∀ i, G →* Γ i) (σ : ∀ i, Representation ℂ (Γ i) (N i)) (s : ∀ i, N i)
    (ρ : Representation ℂ G W) : Prop :=
  (∀ᶠ i in cofinite, s i ≠ 0) ∧
    ∃ h : ∀ g, ∀ᶠ i in cofinite, σ i (p i g) (s i) = s i, Nonempty (ρ.Equiv (restrRep p σ s h))

end Many

section Mixed

variable {G G₁ G₂ H K W : Type} [Group G] [Group G₁] [Group G₂] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [AddCommGroup W] [Module ℂ W]


variable (H) in
def postRep (ρ : G →* (K →L[ℂ] K)) : Representation ℂ G (H →L[ℂ] K) where
  toFun g := (ContinuousLinearMap.compL ℂ H K K (ρ g)).toLinearMap
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

variable {j₁ : G₁ →* G} {j₂ : G₂ →* G} {σ : Representation ℂ G₁ W} {δ : G₂ →* (H →L[ℂ] H)} {ρ : G →* (K →L[ℂ] K)}
  {U U' : Submodule ℂ K} {T : W →ₗ[ℂ] (H →L[ℂ] K)}

theorem injective_of_mem_homInto {X : Type} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G₁ X}
    {C : Submodule ℂ X} {f : W →ₗ[ℂ] X} (hσ : σ.IsIrreducible) (hf : f ∈ homInto σ τ C) (h0 : f ≠ 0) :
    Function.Injective f := by
  rcases eq_bot_or_eq_top (f.intertwiningMap_of_isIntertwiningMap σ τ hf.2).ker with e | e
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have : x ∈ (f.intertwiningMap_of_isIntertwiningMap σ τ hf.2).ker := hx
    rwa [e] at this
  · refine absurd (LinearMap.ext fun x => ?_) h0
    have : x ∈ (f.intertwiningMap_of_isIntertwiningMap σ τ hf.2).ker := by rw [e]; trivial
    exact this

theorem rank_homInto_congr {W' X : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X]
    {σ' : Representation ℂ G₁ W'} (e : σ.Equiv σ') (τ : Representation ℂ G₁ X) (C : Submodule ℂ X) :
    Module.rank ℂ (homInto σ τ C) = Module.rank ℂ (homInto σ' τ C) := by
  have key : ∀ {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ G₁ W}
      {σ' : Representation ℂ G₁ W'}, σ.Equiv σ' → Module.rank ℂ (homInto σ' τ C) ≤ Module.rank ℂ (homInto σ τ C) :=
    fun {W W'} _ _ _ _ σ σ' e => LinearMap.rank_le_of_injective (M := homInto σ' τ C) (M₁ := homInto σ τ C)
      { toFun := fun T => ⟨T.1 ∘ₗ e.toLinearMap, fun x => T.2.1 _,
          fun g x => (congrArg T.1 (DFunLike.congr_fun (e.isIntertwining' g) x)).trans (T.2.2 g _)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      fun T T' h => Subtype.ext (LinearMap.ext fun y => by
        obtain ⟨x, rfl⟩ := e.surjective y
        exact DFunLike.congr_fun (congrArg Subtype.val h) x)
  exact le_antisymm (key e.symm) (key e)

variable [TopologicalSpace G] [TopologicalSpace G₂] [CompleteSpace K]

end Mixed

section MixedPi

variable {ι G G₁ K W : Type} {Γ Hs : ι → Type} [Fintype ι] [DecidableEq ι] [Group G] [Group G₁] [∀ i, Group (Γ i)]
  [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [AddCommGroup W] [Module ℂ W]

def homPi (e : ∀ i, Γ i →* G) (δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)) (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) :
    Submodule ℂ (ContinuousMultilinearMap ℂ Hs K) where
  carrier := {Φ | (∀ y, Φ y ∈ U) ∧ ∀ i g y, Φ (Function.update y i (δ i g (y i))) = ρ (e i g) (Φ y)}
  add_mem' := fun h h' => ⟨fun y => U.add_mem (h.1 y) (h'.1 y), fun i g y => by simp [h.2 i g y, h'.2 i g y]⟩
  zero_mem' := ⟨fun _ => U.zero_mem, fun i g y => by simp⟩
  smul_mem' := fun c _ h => ⟨fun y => U.smul_mem c (h.1 y), fun i g y => by simp [h.2 i g y]⟩


variable (Hs) in
def postRepPi (ρ : G →* (K →L[ℂ] K)) : Representation ℂ G (ContinuousMultilinearMap ℂ Hs K) where
  toFun g := (ContinuousLinearMap.compContinuousMultilinearMapL ℂ Hs K K (ρ g)).toLinearMap
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

def homTensorPi (j : G₁ →* G) (e : ∀ i, Γ i →* G) (σ : Representation ℂ G₁ W) (δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i))
    (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) : Submodule ℂ (W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs K) :=
  homInto σ (postRepPi Hs (ρ.comp j)) (homPi e δ ρ U)

def multTensorPi (j : G₁ →* G) (e : ∀ i, Γ i →* G) (σ : Representation ℂ G₁ W) (δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i))
    (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) : Cardinal := Module.rank ℂ (homTensorPi j e σ δ ρ U)

def IsTensorCopyPi (j : G₁ →* G) (e : ∀ i, Γ i →* G) (σ : Representation ℂ G₁ W) (δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i))
    (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) : Prop :=
  ∃ T ∈ homTensorPi j e σ δ ρ ⊤, Function.Injective T ∧
    (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = U

def bePi (Φ Φ' : ContinuousMultilinearMap ℂ Hs K) : ℂ :=
  ⟪Φ' fun i => unitVec (H := Hs i), Φ fun i => unitVec (H := Hs i)⟫_ℂ

variable {j : G₁ →* G} {e : ∀ i, Γ i →* G} {σ : Representation ℂ G₁ W} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)}
  {ρ : G →* (K →L[ℂ] K)} {U U' : Submodule ℂ K} {Φ Φ' : ContinuousMultilinearMap ℂ Hs K}
  {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs K}


omit [Fintype ι] in
theorem mem_homPi : Φ ∈ homPi e δ ρ U ↔
    (∀ y, Φ y ∈ U) ∧ ∀ i g y, Φ (Function.update y i (δ i g (y i))) = ρ (e i g) (Φ y) := Iff.rfl


omit [Fintype ι] in
theorem mem_homTensorPi : T ∈ homTensorPi j e σ δ ρ U ↔ (∀ w y, T w y ∈ U) ∧
    (∀ g w y, T (σ g w) y = ρ (j g) (T w y)) ∧
      ∀ i g w y, T w (Function.update y i (δ i g (y i))) = ρ (e i g) (T w y) :=
  ⟨fun h => ⟨fun w => (h.1 w).1, fun g w y => DFunLike.congr_fun (h.2 g w) y, fun i g w => (h.1 w).2 i g⟩,
    fun h => ⟨fun w => ⟨h.1 w, fun i g => h.2.2 i g w⟩, fun g w => ContinuousMultilinearMap.ext (h.2.1 g w)⟩⟩


omit [Fintype ι] in
theorem homTensorPi_mono (h : U ≤ U') : homTensorPi j e σ δ ρ U ≤ homTensorPi j e σ δ ρ U' :=
  fun _ hT => ⟨fun w => ⟨fun y => h ((hT.1 w).1 y), (hT.1 w).2⟩, hT.2⟩


omit [Fintype ι] in
theorem multTensorPi_congr {W' : Type} [AddCommGroup W'] [Module ℂ W'] {σ' : Representation ℂ G₁ W'} (f : σ.Equiv σ') :
    multTensorPi j e σ δ ρ U = multTensorPi j e σ' δ ρ U := rank_homInto_congr f _ _


omit [Fintype ι] in
theorem toContinuousLinearMap_mem_homIn (h : Φ ∈ homPi e δ ρ U) (y : ∀ i, Hs i) (i : ι) :
    Φ.toContinuousLinearMap y i ∈ homIn (δ i) (ρ.comp (e i)) U :=
  ⟨fun _ => h.1 _, fun g x => by
    have := h.2 i g (Function.update y i x)
    rwa [Function.update_self, Function.update_idem] at this⟩

variable [TopologicalSpace G] [∀ i, TopologicalSpace (Γ i)] [CompleteSpace K]

theorem inner_eq_bePi (hδ : ∀ i, IsIrrUnitary (δ i)) (hρ : IsUnitaryRep ρ) (h : Φ ∈ homPi e δ ρ U)
    (h' : Φ' ∈ homPi e δ ρ U') (y y' : ∀ i, Hs i) : ⟪Φ' y', Φ y⟫_ℂ = bePi Φ Φ' * ∏ i, ⟪y' i, y i⟫_ℂ := by
  let u : ∀ i, Hs i := fun i => unitVec (H := Hs i)
  have key : ∀ s : Finset ι, ⟪Φ' y', Φ y⟫_ℂ = ⟪Φ' (s.piecewise u y'),
      Φ (s.piecewise u y)⟫_ℂ * ∏ i ∈ s, ⟪y' i, y i⟫_ℂ := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have := (hδ i).complete
      let A := Φ.toContinuousLinearMap (s.piecewise u y) i
      let A' := Φ'.toContinuousLinearMap (s.piecewise u y') i
      have hA (g : Γ i) (x : Hs i) : A (δ i g x) = ρ (e i g) (A x) :=
        (toContinuousLinearMap_mem_homIn h (s.piecewise u y) i).2 g x
      have hA' (g : Γ i) (x : Hs i) : A' (δ i g x) = ρ (e i g) (A' x) :=
        (toContinuousLinearMap_mem_homIn h' (s.piecewise u y') i).2 g x
      have h1 : ⟪A' (y' i), A (y i)⟫_ℂ = ⟪A' (u i), A (u i)⟫_ℂ * ⟪y' i, y i⟫_ℂ := by
        obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur (Hs i) (Γ i) (δ i) (hδ i).unitary.norm_apply
          (fun S hS hstable => (hδ i).irred.2 S ⟨hS, hstable⟩) (A'.adjoint ∘L A) (fun g => by
            refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun z => ?_
            change ⟪z, δ i g (A'.adjoint (A x))⟫_ℂ = ⟪z, A'.adjoint (A (δ i g x))⟫_ℂ
            calc
              _ = ⟪δ i g⁻¹ z, A'.adjoint (A x)⟫_ℂ := by
                simpa only [inv_inv] using ((hδ i).unitary.inner_apply_left g⁻¹ z (A'.adjoint (A x))).symm
              _ = _ := by
                rw [ContinuousLinearMap.adjoint_inner_right, hA', hρ.inner_apply_left,
                  ← map_inv, inv_inv, ← hA, ContinuousLinearMap.adjoint_inner_right])
        have inner_eq (x z : Hs i) : ⟪A' z, A x⟫_ℂ = c * ⟪z, x⟫_ℂ := by
          have hx : A'.adjoint (A x) = c • x := by
            simpa using DFunLike.congr_fun hc x
          rw [← ContinuousLinearMap.adjoint_inner_right, hx, inner_smul_right]
        have := (hδ i).irred.1
        have hu : ∃ x : Hs i, ‖x‖ = 1 := exists_norm_eq (Hs i) zero_le_one
        have hnorm : ‖u i‖ = 1 := by
          change ‖unitVec (H := Hs i)‖ = 1
          rw [unitVec, dite_eq_left hu]
          exact hu.choose_spec
        rw [inner_eq (y i) (y' i), inner_eq (u i) (u i), inner_self_eq_norm_sq_to_K, hnorm]
        simp
      rw [Finset.prod_insert hi, Finset.piecewise_insert, Finset.piecewise_insert, ← mul_assoc, ih]
      congr 1
      refine Eq.trans ?_ h1
      simp only [A, A', ContinuousMultilinearMap.toContinuousLinearMap_apply]
      rw [← s.piecewise_eq_of_notMem u y hi, ← s.piecewise_eq_of_notMem u y' hi,
        Function.update_eq_self, Function.update_eq_self]
  simpa only [Finset.piecewise_univ, bePi, u] using key Finset.univ

theorem bePi_self_pos (hδ : ∀ i, IsIrrUnitary (δ i)) (hρ : IsUnitaryRep ρ) (h : Φ ∈ homPi e δ ρ U) (h0 : Φ ≠ 0) :
    0 < (bePi Φ Φ).re :=
  (re_inner_self_pos (𝕜 := ℂ)).2 fun e => h0 (ContinuousMultilinearMap.ext fun y => inner_self_eq_zero.1 (by
    rw [inner_eq_bePi hδ hρ h h, bePi, e, inner_zero_left, zero_mul]))

end MixedPi

theorem isRestrTensor_charRep {ι G : Type} {Γ : ι → Type} [Group G] [∀ i, Group (Γ i)] (p : ∀ i, G →* Γ i)
    (χ : ∀ i, Γ i →* Circle) (ψ : G →* Circle) (h : ∀ g, ∀ᶠ i in cofinite, χ i (p i g) = 1)
    (hψ : ∀ g, (ψ g : ℂ) = ∏ᶠ i, (χ i (p i g) : ℂ)) :
    IsRestrTensor p (fun i => charRep (χ i)) (fun _ => 1) (charRep ψ) (fun y => ∏ᶠ i, y i) := by
  refine ⟨Eventually.of_forall (fun _ => norm_one), ?_, ?_, ?_, ?_⟩
  · intro g
    exact (h g).mono fun i hi => by simp [charRep, hi]
  · intro y y' hy hy'
    have h' : (Function.mulSupport fun i => conj (y' i)).Finite := Set.Finite.subset hy' fun i hi e => hi (by simp [e])
    simp only [RCLike.inner_apply]
    rw [finprod_mul_distrib hy h', map_finprod _ hy']
  · exact eq_top_iff.2 (le_trans (fun z _ => by
      simpa using Submodule.smul_mem _ z (Submodule.subset_span (s := {v : ℂ | ∃ y : ι → ℂ, Restr (fun _ => 1) y ∧
        v = ∏ᶠ i, y i}) ⟨_, restr_self _, finprod_one.symm⟩)) (Submodule.le_topologicalClosure _))
  · intro g y hy
    change (ψ g : ℂ) * ∏ᶠ i, y i = ∏ᶠ i, (χ i (p i g) : ℂ) * y i
    rw [finprod_mul_distrib (Set.Finite.subset (h g) fun i hi e => hi (by simp [show χ i (p i g) = 1 from e])) hy, hψ]

end GlobalTheory.AutMult

end
