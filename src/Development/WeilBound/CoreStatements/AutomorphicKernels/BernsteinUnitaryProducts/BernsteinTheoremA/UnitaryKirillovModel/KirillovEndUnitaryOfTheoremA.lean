module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0011
public import GroundTheory.AutomorphicForms.Bundle0007
public import GroundTheory.AutomorphicForms.Bundle0004
public import GroundTheory.AutomorphicForms.GLnLocal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast

@[expose] public section

noncomputable section

open GroundTheory.Automorphic

namespace PositivityTheory.PfBern.Unit

section General

variable {G : Type} [Group G] [TopologicalSpace G]

def conjFn (g : G) (f : G → ℂ) : G → ℂ := fun x => f (g⁻¹ * x * g)


variable (G) in
abbrev testFn : Submodule ℂ (G → ℂ) := locallyConstantCompactSupport G ℂ ℂ


variable (G) in
def PInvIsGInv (P : Subgroup G) : Prop :=
  ∀ D : (G → ℂ) →ₗ[ℂ] ℂ, (∀ p ∈ P, ∀ f ∈ testFn G, D (conjFn p f) = D f) →
    ∀ (g : G), ∀ f ∈ testFn G, D (conjFn g f) = D f

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def HasTraceDistr (ρ : Representation ℂ G V) : Prop :=
  ∃ D : Module.End ℂ V →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ,
    (∀ (g : G) (S : Module.End ℂ V), ∀ f ∈ testFn G, D (ρ g⁻¹ * S * ρ g) f = D S (conjFn g f)) ∧
    (∀ S : Module.End ℂ V, (∀ f ∈ testFn G, D S f = 0) → S = 0)

abbrev Sesq (V : Type) [AddCommGroup V] [Module ℂ V] : Type := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

def HasFormTraceDistr (ρ : Representation ℂ G V) : Prop :=
  ∃ D : Sesq V →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ,
    (∀ (g : G) (B : Sesq V), ∀ f ∈ testFn G, D ((B ∘ₗ ρ g).compl₂ (ρ g)) f = D B (conjFn g f)) ∧
    (∀ B : Sesq V, (∀ f ∈ testFn G, D B f = 0) → B = 0)

def InvFormScalar (ρ : Representation ℂ G V) (B₀ : Sesq V) : Prop :=
  ∀ B : Sesq V, (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∃ c : ℂ, B = c • B₀

def PFormScalar (P : Subgroup G) (ρ : Representation ℂ G V) (B₀ : Sesq V) : Prop :=
  ∀ B : Sesq V, (∀ p ∈ P, ∀ v w, B (ρ p v) (ρ p w) = B v w) → ∃ c : ℂ, B = c • B₀

theorem form_inv_of_trace (P : Subgroup G) (ρ : Representation ℂ G V) (hA : PInvIsGInv G P)
    (hD : HasFormTraceDistr ρ) (B : Sesq V) (hB : ∀ p ∈ P, ∀ v w, B (ρ p v) (ρ p w) = B v w) (g : G) (v w : V) :
    B (ρ g v) (ρ g w) = B v w := by
  obtain ⟨D, hequiv, hfaith⟩ := hD
  have hP : ∀ p ∈ P, ∀ f ∈ testFn G, D B (conjFn p f) = D B f := by
    intro p hp f hf
    have e : (B ∘ₗ ρ p).compl₂ (ρ p) = B := by
      ext v w
      exact hB p hp v w
    rw [← hequiv p B f hf, e]
  have hG := hA (D B) hP
  have h0 : (B ∘ₗ ρ g).compl₂ (ρ g) - B = 0 := hfaith _ fun f hf => by
    rw [map_sub, LinearMap.sub_apply, hequiv g B f hf, hG g f hf, sub_self]
  have h1 := congrArg (fun C : Sesq V => C v w) (sub_eq_zero.1 h0)
  simpa using h1

theorem pFormScalar_of (P : Subgroup G) (ρ : Representation ℂ G V) (B₀ : Sesq V) (hA : PInvIsGInv G P)
    (hD : HasFormTraceDistr ρ) (hS : InvFormScalar ρ B₀) : PFormScalar P ρ B₀ :=
  fun B hB => hS B (form_inv_of_trace P ρ hA hD B hB)

private theorem eigen_lemma (W : Submodule ℂ V) [FiniteDimensional ℂ W] [Nontrivial W] (B B₀ : Sesq V)
    (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re) :
    ∃ c : ℂ, ∃ x : V, x ∈ W ∧ x ≠ 0 ∧ ∀ y ∈ W, B x y = c * B₀ x y := by
  let b := Module.finBasis ℂ W
  let L0 : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun x j => B₀ (x : V) (b j : V)
      map_add' := by
        intro x y
        ext j
        simp
      map_smul' := by
        intro c x
        ext j
        simp }
  let L : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun x j => B (x : V) (b j : V)
      map_add' := by
        intro x y
        ext j
        simp
      map_smul' := by
        intro c x
        ext j
        simp }
  have hext : ∀ (C : Sesq V) (c : ℂ) (x : V), (∀ j, C x (b j : V) = c * B₀ x (b j : V)) →
      ∀ y ∈ W, C x y = c * B₀ x y := by
    intro C c x h y hy
    have key : (C x).comp W.subtype = c • ((B₀ x).comp W.subtype) := by
      apply b.ext
      intro j
      simp [h j]
    have := LinearMap.congr_fun key ⟨y, hy⟩
    simpa using this
  have hinj : Function.Injective L0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∀ j, B₀ (x : V) (b j : V) = 0 * B₀ (x : V) (b j : V) := by
      intro j
      have := congrFun hx j
      simpa [L0] using this
    have hxx := hext B₀ 0 x h0 x x.2
    by_contra hne
    have hx0 : (x : V) ≠ 0 := by simpa using hne
    have := hpos _ hx0
    rw [hxx] at this
    simp at this
  let E := L0.linearEquivOfInjective hinj (by simp)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (E.symm.toLinearMap ∘ₗ L)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  refine ⟨c, x, x.2, ?_, ?_⟩
  · simpa using hx.2
  · apply hext B c x
    intro j
    have h1 := hx.apply_eq_smul
    have h2 : L x = E (c • x) := by
      rw [← h1]
      simp
    have h3 := congrFun h2 j
    simpa [E, L, L0, LinearMap.linearEquivOfInjective_apply] using h3

theorem invFormScalar_of_admissible [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (ρ : Representation ℂ G V) (hadm : GroundTheory.Automorphic.IsAdmissible ρ) [ρ.IsIrreducible]
    (B₀ : Sesq V) (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re) (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) :
    InvFormScalar ρ B₀ := by
  intro B hB
  obtain ⟨v0, hv0⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  obtain ⟨K, hKc, hKle⟩ := hasBasis_nhds_one_compactOpenSubgroup.mem_iff.1
    ((hadm.1 v0).mem_nhds (stabilizerOf ρ v0).one_mem)
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  haveI : FiniteDimensional ℂ (fixedVectors ρ (K : Subgroup G)) := hadm.2 _ hKc hKo
  have hv0W : v0 ∈ fixedVectors ρ (K : Subgroup G) := mem_fixedVectors.2 (fun k hk => hKle hk)
  haveI : Nontrivial (fixedVectors ρ (K : Subgroup G)) :=
    ⟨⟨⟨v0, hv0W⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, x0, hx0W, hx0, hxy⟩ := eigen_lemma (fixedVectors ρ (K : Subgroup G)) B B₀ hpos
  refine ⟨c, ?_⟩
  have hB'inv : ∀ g v w, (B - c • B₀) (ρ g v) (ρ g w) = (B - c • B₀) v w := by
    intro g v w
    simp [hB, hinv]
  have hW0 : ∀ y ∈ fixedVectors ρ (K : Subgroup G), (B - c • B₀) x0 y = 0 := by
    intro y hy
    simp [hxy y hy]
  have hall : ∀ y, (B - c • B₀) x0 y = 0 := by
    intro y
    have hker : coinvariantsKer ρ (K : Subgroup G) ≤ LinearMap.ker ((B - c • B₀) x0) := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨k, v⟩, rfl⟩
      have hk : ρ (k : G) x0 = x0 := (mem_fixedVectors.1 hx0W) k k.2
      have e := hB'inv k x0 v
      rw [hk] at e
      change (B - c • B₀) x0 (ρ (k : G) v - v) = 0
      rw [map_sub, e, sub_self]
    have h1 := hker (sub_fixedProj_mem hadm.1 hKc hKo y)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    rw [h1]
    exact hW0 _ (fixedProj ρ hadm.1 hKc hKo y).2
  let U : Subrepresentation ρ := ⟨LinearMap.ker (B - c • B₀), by
    intro g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    ext w
    have hw : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.zero_apply, ← hw, hB'inv, hv, LinearMap.zero_apply]⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top U with h | h
  · exfalso
    have hmem : x0 ∈ U.toSubmodule := LinearMap.mem_ker.2 (LinearMap.ext hall)
    rw [h] at hmem
    exact hx0 ((Submodule.mem_bot ℂ).1 hmem)
  · have hmem : ∀ v, v ∈ U.toSubmodule := by
      intro v
      rw [h]
      exact Submodule.mem_top
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    have h2 := LinearMap.congr_fun (LinearMap.mem_ker.1 (hmem v)) w
    simpa [sub_eq_zero] using h2

end General

section GeneralLinearIntegers

def TheoremA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop := ∀ n : ℕ, PInvIsGInv (GL (Fin (n + 1)) k) (GlobalTheory.BZMir.Mir k n)

def FormTraceDistrGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) k) V),
    GroundTheory.Automorphic.IsAdmissible π → π.IsIrreducible → (∃ B₀ : Sesq V, (∀ v w, B₀ w v = starRingEnd ℂ (B₀ v w)) ∧
      (∀ v, v ≠ 0 → 0 < (B₀ v v).re) ∧ ∀ g v w, B₀ (π g v) (π g w) = B₀ v w) → HasFormTraceDistr π

def FormSchurGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) k) V)
    (B₀ : Sesq V), GroundTheory.Automorphic.IsAdmissible π → π.IsIrreducible → (∀ v w, B₀ w v = starRingEnd ℂ (B₀ v w)) →
    (∀ v, v ≠ 0 → 0 < (B₀ v v).re) → (∀ g v w, B₀ (π g v) (π g w) = B₀ v w) → InvFormScalar π B₀

def KirillovForm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) k) V)
    (B₀ : Sesq V), GroundTheory.Automorphic.IsAdmissible π → π.IsIrreducible → (∀ v w, B₀ w v = starRingEnd ℂ (B₀ v w)) →
    (∀ v, v ≠ 0 → 0 < (B₀ v v).re) → (∀ g v w, B₀ (π g v) (π g w) = B₀ v w) → PFormScalar (GlobalTheory.BZMir.Mir k n) π B₀

theorem kirillovForm_of_theoremA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : TheoremA k) (hD : FormTraceDistrGL k) (hS : FormSchurGL k) :
    KirillovForm k := by
  intro n V _ _ π B₀ hadm hirr h1 h2 h3
  exact pFormScalar_of _ π B₀ (hA n) (hD n V π hadm hirr ⟨B₀, h1, h2, h3⟩) (hS n V π B₀ hadm hirr h1 h2 h3)

theorem formSchurGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : FormSchurGL k := by
  intro n V _ _ π B₀ hadm hirr _ h2 h3
  exact invFormScalar_of_admissible π hadm B₀ h2 h3

theorem kirillovForm_of_theoremA' (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : TheoremA k) (hD : FormTraceDistrGL k) : KirillovForm k :=
  kirillovForm_of_theoremA k hA hD (formSchurGL k)

end GeneralLinearIntegers

end PositivityTheory.PfBern.Unit
