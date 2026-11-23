module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.TensorProductTheorem.MatrixCoeff
section
noncomputable section

namespace GroundTheory.Automorphic

open Set

namespace RestrictedTensor

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

def orbitSpan (ρ : Representation ℂ G V) (v : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (range fun g => ρ g v)
  apply_mem_toSubmodule g x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem mem_orbitSpan_self (ρ : Representation ℂ G V) (v : V) : v ∈ (orbitSpan ρ v).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem orbitSpan_eq_top {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) :
    orbitSpan ρ v = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (orbitSpan ρ v) with h | h
  · exfalso
    apply hv
    have := mem_orbitSpan_self ρ v
    rw [h] at this
    exact this
  · exact h

theorem mem_span_orbit {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) (x : V) :
    x ∈ Submodule.span ℂ (range fun g => ρ g v) := by
  have := orbitSpan_eq_top (ρ := ρ) hv
  have hx : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
  rw [← this] at hx
  exact hx

theorem eq_zero_of_forall_apply {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    {l : Module.Dual ℂ V} (h : ∀ g, l (ρ g v) = 0) : l = 0 := by
  ext x
  have hx := mem_span_orbit (ρ := ρ) hv x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact h g
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem eq_zero_of_forall_apply_act {ρ : Representation ℂ G V} [ρ.IsIrreducible]
    {l : Module.Dual ℂ V} (hl : l ≠ 0) {x : V} (h : ∀ g, l (ρ g x) = 0) : x = 0 := by
  by_contra hx
  exact hl (eq_zero_of_forall_apply (ρ := ρ) hx h)

def orbitMap (ρ : Representation ℂ G V) (v : V) : (G →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun g => ρ g v

theorem orbitMap_apply (ρ : Representation ℂ G V) (v : V) (c : G →₀ ℂ) :
    orbitMap ρ v c = c.sum fun g a => a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_apply]

theorem orbitMap_single (ρ : Representation ℂ G V) (v : V) (g : G) (a : ℂ) :
    orbitMap ρ v (Finsupp.single g a) = a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_single]

theorem orbitMap_mapDomain (ρ : Representation ℂ G V) (v : V) (h : G) (c : G →₀ ℂ) :
    orbitMap ρ v (Finsupp.mapDomain (h * ·) c) = ρ h (orbitMap ρ v c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [orbitMap]
  | add c d hc hd => rw [Finsupp.mapDomain_add, map_add (f := _), hc, hd, map_add (f := _), map_add (f := _)]
  | single g a => simp [Finsupp.mapDomain_single, orbitMap_single, map_mul]

theorem range_orbitMap (ρ : Representation ℂ G V) (v : V) :
    LinearMap.range (orbitMap ρ v) = Submodule.span ℂ (range fun g => ρ g v) := by
  rw [orbitMap, Finsupp.range_linearCombination]

theorem linearForm_orbitMap (ρ : Representation ℂ G V) (v : V) (l : Module.Dual ℂ V) (h : G)
    (c : G →₀ ℂ) : l (ρ h (orbitMap ρ v c)) = c.sum fun g a => a * l (ρ (h * g) v) := by
  rw [orbitMap_apply, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]

theorem nonempty_equiv_of_matrixCoeff_eq {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    [ρ.IsIrreducible] [σ.IsIrreducible] {v : V} {l : Module.Dual ℂ V} {w : W}
    {m : Module.Dual ℂ W} (h : ∀ g, l (ρ g v) = m (σ g w)) (hne : ∃ g, l (ρ g v) ≠ 0) :
    Nonempty (ρ.Equiv σ) := by
  obtain ⟨g₀, hg₀⟩ := hne
  have hv : v ≠ 0 := by rintro rfl; simp at hg₀
  have hm : m ≠ 0 := by rintro rfl; exact hg₀ (by rw [h]; rfl)

  have hker : LinearMap.ker (orbitMap ρ v) ≤ LinearMap.ker (orbitMap σ w) := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    refine eq_zero_of_forall_apply_act (ρ := σ) hm fun k => ?_
    rw [linearForm_orbitMap]
    have := linearForm_orbitMap ρ v l k c
    rw [hc, map_zero, map_zero] at this
    rw [this]
    exact Finsupp.sum_congr fun g _ => by rw [h]
  have hsurj : Function.Surjective (orbitMap ρ v) := by
    rw [← LinearMap.range_eq_top, range_orbitMap]
    exact eq_top_iff.2 fun x _ => mem_span_orbit hv x
  let e := LinearMap.quotKerEquivOfSurjective (orbitMap ρ v) hsurj
  let F : V →ₗ[ℂ] W := ((LinearMap.ker (orbitMap ρ v)).liftQ (orbitMap σ w) hker).comp
    e.symm.toLinearMap
  have hF : ∀ c, F (orbitMap ρ v c) = orbitMap σ w c := by
    intro c
    have : e.symm (orbitMap ρ v c) = Submodule.Quotient.mk c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hFint : ∀ g x, F (ρ g x) = σ g (F x) := by
    intro g x
    obtain ⟨c, rfl⟩ := hsurj x
    rw [← orbitMap_mapDomain, hF, hF, orbitMap_mapDomain]
  let Fi : Representation.IntertwiningMap ρ σ := ⟨F, fun g => LinearMap.ext fun x => hFint g x⟩
  have hFi0 : Fi ≠ 0 := by
    intro h0
    have h1 : F v = w := by
      have := hF (Finsupp.single 1 1)
      rwa [orbitMap_single, orbitMap_single, one_smul, one_smul, map_one,
        Module.End.one_apply, map_one, Module.End.one_apply] at this
    have h2 : F v = 0 := by
      have : Fi v = 0 := by rw [h0]; rfl
      exact this
    apply hg₀
    rw [h, ← h1, h2, map_zero, map_zero]
  rcases Representation.IsIrreducible.bijective_or_eq_zero Fi with hb | h0
  · exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective F hb)
      fun g => LinearMap.ext fun x => hFint g x⟩
  · exact absurd h0 hFi0

end RestrictedTensor

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.TensorProductTheorem.Operators
section
noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def IsStable (T : Set (End ℂ M)) (p : Submodule ℂ M) : Prop :=
  ∀ t ∈ T, ∀ x ∈ p, t x ∈ p

def IsSimpleUnder (T : Set (End ℂ M)) : Prop :=
  Nontrivial M ∧ ∀ p : Submodule ℂ M, IsStable T p → p = ⊥ ∨ p = ⊤

theorem IsStable.adjoin {T : Set (End ℂ M)} {p : Submodule ℂ M} (h : IsStable T p) :
    ∀ a ∈ Algebra.adjoin ℂ T, ∀ x ∈ p, a x ∈ p := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem t ht => exact h t ht
  | algebraMap c =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact p.smul_mem c hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.add_apply]
    exact p.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [Module.End.mul_apply]
    exact ha _ (hb x hx)

theorem commute_of_mem_adjoin {T : Set (End ℂ M)} {a : End ℂ M} (ha : ∀ t ∈ T, Commute a t) :
    ∀ b ∈ Algebra.adjoin ℂ T, Commute a b := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem t ht => exact ha t ht
  | algebraMap c => exact (Algebra.commutes' c a).symm
  | add b c _ _ hb hc => exact hb.add_right hc
  | mul b c _ _ hb hc => exact hb.mul_right hc

theorem IsStable.mono {T₁ T₂ : Set (End ℂ M)} {p : Submodule ℂ M} (h : IsStable T₂ p)
    (hT : T₁ ⊆ T₂) : IsStable T₁ p :=
  fun t ht => h t (hT ht)

variable [FiniteDimensional ℂ M]

theorem adjoin_eq_top {T : Set (End ℂ M)} (h : IsSimpleUnder T) : Algebra.adjoin ℂ T = ⊤ := by
  have := h.1
  set A := Algebra.adjoin ℂ T
  have hsimple : IsSimpleModule A M := by
    have : Nontrivial (Submodule A M) := (Submodule.nontrivial_iff A).2 h.1
    refine { eq_bot_or_eq_top := fun p => ?_ }
    have hst : IsStable T (p.restrictScalars ℂ) := by
      intro t ht x hx
      have : (⟨t, Algebra.subset_adjoin ht⟩ : A) • x ∈ p := p.smul_mem _ hx
      exact this
    rcases h.2 _ hst with h0 | h0
    · left
      rw [← Submodule.restrictScalars_eq_bot_iff ℂ]
      exact h0
    · right
      rw [← Submodule.restrictScalars_eq_top_iff ℂ]
      exact h0
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ (A := A) (V := M)
  have : Module.Finite (End A M) M := Module.Finite.of_restrictScalars_finite ℂ (End A M) M
  have hsurj := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := M)
  refine eq_top_iff.2 fun φ _ => ?_
  have hφ : ∀ (f : End A M) (x : M), φ (f x) = f (φ x) := by
    intro f x
    obtain ⟨c, rfl⟩ := hb.2 f
    simp [Algebra.algebraMap_eq_smul_one]
  let ψ : End (End A M) M :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun f x => hφ f x }
  obtain ⟨a, ha⟩ := hsurj ψ
  have : (a : End ℂ M) = φ := by
    ext x
    have := congrArg (fun g : End (End A M) M => g x) ha
    exact this
  rw [← this]
  exact a.2


omit [FiniteDimensional ℂ M] in
theorem eq_zero_of_forall_mem {T₁ T₂ : Set (End ℂ M)} (h : IsSimpleUnder (T₁ ∪ T₂))
    (hc : ∀ a ∈ T₁, ∀ b ∈ T₂, Commute a b) {N : Submodule ℂ M} (hN : N ≠ ⊥) (hNs : IsStable T₁ N)
    {a : End ℂ M} (ha : ∀ b ∈ T₂, Commute a b) (h0 : ∀ x ∈ N, a x = 0) : a = 0 := by
  set B := Algebra.adjoin ℂ T₂
  set P : Submodule ℂ M := ⨆ b : B, N.map (b : End ℂ M)
  have hmap : ∀ b : B, N.map (b : End ℂ M) ≤ P := fun b => le_iSup (fun b : B => N.map (b : End ℂ M)) b
  have hst : IsStable (T₁ ∪ T₂) P := by
    intro t ht x hx
    have hle : P ≤ P.comap t := by
      refine iSup_le fun b => ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [Submodule.mem_comap]
      rcases ht with ht | ht
      · have hcomm : Commute t (b : End ℂ M) :=
          commute_of_mem_adjoin (fun s hs => hc t ht s hs) b b.2
        have : t ((b : End ℂ M) n) = (b : End ℂ M) (t n) := by
          rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
        rw [this]
        exact hmap b ⟨t n, hNs t ht n hn, rfl⟩
      · have htb : t * (b : End ℂ M) ∈ B := B.mul_mem (Algebra.subset_adjoin ht) b.2
        exact hmap ⟨_, htb⟩ ⟨n, hn, rfl⟩
    exact hle hx
  have hP : P ≠ ⊥ := by
    intro hP
    apply hN
    rw [eq_bot_iff]
    intro n hn
    have : n ∈ P := hmap 1 ⟨n, hn, by simp⟩
    rwa [hP] at this
  have hPtop : P = ⊤ := (h.2 P hst).resolve_left hP
  have hker : P ≤ LinearMap.ker a := by
    refine iSup_le fun b => ?_
    rintro _ ⟨n, hn, rfl⟩
    rw [LinearMap.mem_ker]
    have hcomm : Commute a (b : End ℂ M) := commute_of_mem_adjoin ha b b.2
    rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, h0 n hn, map_zero]
  ext x
  have : x ∈ LinearMap.ker a := hker (hPtop ▸ Submodule.mem_top)
  simpa using this

def restrictSet (T : Set (End ℂ M)) (N : Submodule ℂ M) (hN : IsStable T N) : Set (End ℂ N) :=
  Set.range fun t : T => (t : End ℂ M).restrict (hN t t.2)


omit [FiniteDimensional ℂ M] in
theorem exists_of_mem_adjoin_restrictSet {T : Set (End ℂ M)} {N : Submodule ℂ M}
    (hN : IsStable T N) {b : End ℂ N} (hb : b ∈ Algebra.adjoin ℂ (restrictSet T N hN)) :
    ∃ a ∈ Algebra.adjoin ℂ T, ∀ x : N, (b x : M) = a x := by
  let S : Subalgebra ℂ (End ℂ N) :=
    { carrier := {b | ∃ a ∈ Algebra.adjoin ℂ T, ∀ x : N, (b x : M) = a x}
      mul_mem' := by
        rintro b₁ b₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        exact ⟨a₁ * a₂, Subalgebra.mul_mem _ ha₁ ha₂, fun x => by
          rw [Module.End.mul_apply, h₁, Module.End.mul_apply, h₂]⟩
      add_mem' := by
        rintro b₁ b₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        exact ⟨a₁ + a₂, Subalgebra.add_mem _ ha₁ ha₂, fun x => by
          rw [LinearMap.add_apply, Submodule.coe_add, h₁, h₂, LinearMap.add_apply]⟩
      algebraMap_mem' := fun c => ⟨algebraMap ℂ (End ℂ M) c, Subalgebra.algebraMap_mem _ c,
        fun x => by simp [Algebra.algebraMap_eq_smul_one]⟩ }
  have : Algebra.adjoin ℂ (restrictSet T N hN) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨t, Algebra.subset_adjoin t.2, fun x => rfl⟩
  exact this hb

theorem exists_simple_stable (T : Set (End ℂ M)) [Nontrivial M] :
    ∃ (N : Submodule ℂ M) (hN : IsStable T N), N ≠ ⊥ ∧ IsSimpleUnder (restrictSet T N hN) := by
  classical
  have hex : ∃ d, ∃ N : Submodule ℂ M, N ≠ ⊥ ∧ IsStable T N ∧ Module.finrank ℂ N = d :=
    ⟨_, ⊤, top_ne_bot, fun _ _ _ _ => trivial, rfl⟩
  obtain ⟨N, hN0, hNs, hNd⟩ := Nat.find_spec hex
  have hmin : ∀ N' : Submodule ℂ M, N' ≠ ⊥ → IsStable T N' → Module.finrank ℂ N ≤ Module.finrank ℂ N' :=
    fun N' h1 h2 => hNd ▸ Nat.find_min' hex ⟨N', h1, h2, rfl⟩
  refine ⟨N, hNs, hN0, ?_, ?_⟩
  · exact Submodule.nontrivial_iff_ne_bot.2 hN0
  · intro q hq
    by_cases hq0 : q = ⊥
    · exact Or.inl hq0
    right
    have hst : IsStable T (q.map N.subtype) := by
      rintro t ht _ ⟨x, hx, rfl⟩
      exact ⟨(t : End ℂ M).restrict (hNs t ht) x, hq _ ⟨⟨t, ht⟩, rfl⟩ x hx, rfl⟩
    have hne : q.map N.subtype ≠ ⊥ := by
      intro h0
      apply hq0
      rw [eq_bot_iff]
      intro x hx
      have : (x : M) ∈ q.map N.subtype := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    have hle := hmin _ hne hst
    rw [Submodule.finrank_map_subtype_eq] at hle
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le q) hle)

end RestrictedTensor

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.TensorProductTheorem.PeterssonComplement
section
noncomputable section

namespace GroundTheory.Automorphic

namespace PeterssonComplement

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)

variable {ι}

theorem aeval_mem {T : Module.End ℂ V} {Z : Submodule ℂ V} (hZ : ∀ z ∈ Z, T z ∈ Z) (q : ℂ[X]) :
    ∀ z ∈ Z, aeval T q z ∈ Z := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro z hz
    rw [aeval_C, Module.algebraMap_end_apply]
    exact Z.smul_mem a hz
  | add p q hp hq =>
    intro z hz
    rw [map_add (f := _), LinearMap.add_apply]
    exact Z.add_mem (hp z hz) (hq z hz)
  | monomial k a ih =>
    intro z hz
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (hZ z hz)

theorem apply_aeval_comm (T : Module.End ℂ V) (q : ℂ[X]) (z : V) : T (aeval T q z) = aeval T q (T z) := by
  have h := (Commute.all (X : ℂ[X]) q).map (aeval T)
  rw [aeval_X] at h
  exact congrArg (fun L : Module.End ℂ V => L z) h.eq

end PeterssonComplement

end GroundTheory.Automorphic
end
end

