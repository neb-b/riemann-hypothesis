module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0094
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CuspidalMultiplicityOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π π' : CuspSub E a),
    CG.mk π = CG.mk π' → π.V = π'.V

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def DiscreteSpectrumResidual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E N), IsDiscrete V ∧ IsSpehOf V π d) ∧
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    (∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → IsIsoGL V V' → V = V') ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → ∀ w, (∃ σ σ', π.IsLocComp w σ ∧ IsLocCompGL V w σ') ∧
        ∀ σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
          GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

def IsUnitaryLSeg (δ : IrrGL (k := k)) : Prop := (∃ Δ : Segment k, IsLSeg Δ δ.rep) ∧ IsUnitarisable δ.rep

def factors (δ : List (IrrGL (k := k))) (τ : List (IrrGL (k := k) × ℝ)) : List (IrrGL (k := k)) :=
  δ ++ τ.flatMap fun p => [p.1.nu (p.2 : ℝ), p.1.nu ((-p.2 : ℝ) : ℂ)]

def IsComplementaryProduct (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (δ : List (IrrGL (k := k))) (τ : List (IrrGL (k := k) × ℝ)), (∀ x ∈ δ, IsUnitaryLSeg x) ∧
    (∀ p ∈ τ, IsUnitaryLSeg p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
    ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), List.ofFn x = factors δ τ ∧
      Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.GenericUnitary

namespace GlobalTheory.Published

def GenericUnitaryDualGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsGeneric π → GenericUnitary.IsComplementaryProduct π

end GlobalTheory.Published

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

theorem exists_of_mem_factors {δ : List (IrrGL (k := k))} {τ : List (IrrGL (k := k) × ℝ)} (hδ : ∀ x ∈ δ, IsUnitaryLSeg x)
    (hτ : ∀ p ∈ τ, IsUnitaryLSeg p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) {y : IrrGL (k := k)} (hy : y ∈ factors δ τ) :
    ∃ (x : IrrGL (k := k)) (s : ℝ), IsUnitaryLSeg x ∧ |s| < 1 / 2 ∧ y = x.nu s := by
  rcases List.mem_append.1 hy with hy | hy
  · exact ⟨y, 0, hδ y hy, by norm_num, by simp⟩
  · obtain ⟨p, hp, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨h1, h2, h3⟩ := hτ p hp
    rcases List.mem_pair.1 hy with rfl | rfl
    · exact ⟨p.1, p.2, h1, by rwa [abs_of_pos h2], rfl⟩
    · exact ⟨p.1, -p.2, h1, by rwa [abs_neg, abs_of_pos h2], rfl⟩

theorem IsComplementaryProduct.exists_prod {π : Representation ℂ (GL (Fin N) k) V} (H : IsComplementaryProduct π) :
    ∃ (h : ℕ) (δ : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, IsUnitarisable (δ j).rep) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, φ⟩ := H
  choose y s hy hs e using fun j => exists_of_mem_factors hδ hτ (y := x j) (hx ▸ List.mem_ofFn.2 ⟨j, rfl⟩)
  choose Δ hΔ using fun j => (hy j).1
  obtain rfl : x = fun j => (y j).nu (s j) := funext e
  exact ⟨h, y, Δ, s, hΔ, fun j => (hy j).2, hs, hd, φ⟩

theorem isUnitarisable_of_equiv {G : Type} [Group G] {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem isUnitaryLSeg_of_isCusp {ρ : IrrGL (k := k)} (hρ : ρ.IsCusp) (hu : IsUnitarisable ρ.rep) : IsUnitaryLSeg ρ :=
  ⟨⟨_, (single_spec hρ).2.1⟩, hu⟩

end GlobalTheory.GenericUnitary

namespace GlobalTheory.Published

theorem GenericUnitaryDualGL.exists_prod (H : GenericUnitaryDualGL) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π)
    (hg : IsGeneric π) :
    ∃ (h : ℕ) (δ : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, IsUnitarisable (δ j).rep) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) :=
  (H k N V π hs hi hu hg).exists_prod

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.IdeleCovolume

namespace GlobalTheory.DiscSpec.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem eq_one_of_isAbsPow {ν : HChar E} (h : ν.IsAbsPow 0) : ν = 1 :=
  GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val E ν (fun k => Units.ext (by simpa using h.2.2 k)) fun v _ => Units.ext (by simpa using h.2.1 v)

theorem left_lattice {a : ℕ} {π : CuspSub E a} (h : IsNormalised π) {φ : Sm E a} (hφ : φ ∈ π.V) :
    ∀ γ ∈ latticeGL E a, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E a) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E a ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact (π.cusp φ hφ).1.left γ)
    (Subgroup.zpowers_le.2 (h φ hφ 1))
  exact this

theorem continuous_form (π : CuspSub E 1) {φ : Sm E 1} (hφ : φ ∈ π.V) : Continuous φ.1 := by
  obtain ⟨ω, h⟩ := RankOne.exists_char π
  have e : φ.1 = fun g => ((ω g : ℂˣ) : ℂ) * φ.1 1 := funext fun g => by
    have h1 : φ.1 (1 * g) = ((ω g : ℂˣ) : ℂ) * φ.1 1 := congrFun (congrArg Subtype.val (h g φ hφ)) 1
    rwa [one_mul] at h1
  rw [e]
  exact (Units.continuous_val.comp (RankOne.continuous_char π ω h)).mul continuous_const

theorem isUnitary_of_isNormalised {π : CuspSub E 1} (h : IsNormalised π) : π.IsUnitary := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  refine (CG.isUnitary_mk _).1 ((CG.isUnitary_ofChar_iff χ).2 ?_)
  have hφ : mulChi 1 χ (oneFn E 1) ∈ ((CuspSub.triv E le_rfl).twist χ).V :=
    ⟨_, Submodule.mem_span_singleton_self _, rfl⟩
  obtain ⟨K, hK, hcov⟩ := exists_compact_latticeGL E
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_form _ hφ).continuousOn
  have hb : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov (CG.oneByOne x)
    have h1 := hC _ hk
    rw [left_lattice h hφ γ hγ, mulChi_apply] at h1
    change ‖1 * ((χ.1 (GeneralLinearGroup.det (CG.oneByOne x)) : ℂˣ) : ℂ)‖ ≤ C at h1
    rwa [CG.det_oneByOne, one_mul] at h1
  have hle : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ 1 := fun x => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hc)
    have := hb (x ^ n)
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    linarith
  intro x
  refine le_antisymm (hle x) ?_
  have := hle x⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at this
  exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this

end GlobalTheory.DiscSpec.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalConverseGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ), 0 < m →
    ∀ π₁ π₂ : IrrRep (GL (Fin (m + 1)) k), IsCuspidal π₁.ρ → IsCuspidal π₂.ρ →
      (∀ τ : IrrRep (GL (Fin m) k), ∃ e : ℂ, HasPairEps ψ π₁.ρ τ.ρ e ∧ HasPairEps ψ π₂.ρ τ.ρ e) →
      Nonempty (π₁.ρ.Equiv π₂.ρ)

end GlobalTheory.Published

end
end

