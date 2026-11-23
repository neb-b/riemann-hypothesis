module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsComplOrthogonalOfNoCommonIrreducibleTypes
section
open Module

namespace GlobalTheory.IsotypicOrth

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
  {σ : K →* K}

lemma pair_left (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    (k : K) (x y : V) : B (ρ k x) y = B x (ρ (σ k⁻¹) y) := by
  rw [← hB k x (ρ (σ k⁻¹) y), map_inv, Representation.self_inv_apply]

lemma left_ker_zero (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x = 0 := by
  let T : Subrepresentation ρ :=
    ⟨S₁.toSubmodule ⊓ ⨅ y ∈ S.toSubmodule, LinearMap.ker (B.flip y), by
      intro k x hx
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.flip_apply] at hx ⊢
      refine ⟨S₁.apply_mem_toSubmodule k hx.1, fun y hy => ?_⟩
      rw [pair_left B hB]
      exact hx.2 _ (S.apply_mem_toSubmodule _ hy)⟩
  have hle : T ≤ S₁ := fun x hx => (Submodule.mem_inf.mp hx).1
  have hmem : ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x ∈ T.toSubmodule := by
    intro x hx h0
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    exact ⟨hx, h0⟩
  rcases h₁.le_iff.mp hle with h | h
  · intro x hx h0
    have hT : T.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    have := hmem x hx h0
    rw [hT] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exfalso
    obtain ⟨x, hx, y, hy, hne⟩ := hn
    have hT : T.toSubmodule = S₁.toSubmodule := congrArg Subrepresentation.toSubmodule h
    rw [← hT] at hx
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.flip_apply] at hx
    exact hne (hx.2 y hy)

lemma right_ker_zero (hσ : Function.Surjective σ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h : IsAtom S)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    ∀ y ∈ S.toSubmodule, (∀ x ∈ S₁.toSubmodule, B x y = 0) → y = 0 := by
  let T : Subrepresentation ρ :=
    ⟨S.toSubmodule ⊓ ⨅ x ∈ S₁.toSubmodule, LinearMap.ker (B x), by
      intro k' y hy
      obtain ⟨k, rfl⟩ := hσ k'
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      refine ⟨S.apply_mem_toSubmodule _ hy.1, fun x hx => ?_⟩
      have e := hB k (ρ k⁻¹ x) y
      rw [Representation.self_inv_apply] at e
      rw [e]
      exact hy.2 _ (S₁.apply_mem_toSubmodule _ hx)⟩
  have hle : T ≤ S := fun x hx => (Submodule.mem_inf.mp hx).1
  have hmem : ∀ y ∈ S.toSubmodule, (∀ x ∈ S₁.toSubmodule, B x y = 0) → y ∈ T.toSubmodule := by
    intro y hy h0
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    exact ⟨hy, h0⟩
  rcases h.le_iff.mp hle with h' | h'
  · intro y hy h0
    have hT : T.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h'
    have := hmem y hy h0
    rw [hT] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exfalso
    obtain ⟨x, hx, y, hy, hne⟩ := hn
    have hT : T.toSubmodule = S.toSubmodule := congrArg Subrepresentation.toSubmodule h'
    rw [← hT] at hy
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy
    exact hne (hy.2 x hx)

lemma restr_injective (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Function.Injective (B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  apply Subtype.ext
  refine left_ker_zero B hB h₁ hn a a.2 fun y hy => ?_
  have := LinearMap.congr_fun ha ⟨y, hy⟩
  simpa [LinearMap.domRestrict₁₂_apply] using this

lemma restr_flip_injective (hσ : Function.Surjective σ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h : IsAtom S)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Function.Injective (B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule).flip := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  apply Subtype.ext
  refine right_ker_zero hσ B hB h hn a a.2 fun x hx => ?_
  have := LinearMap.congr_fun ha ⟨x, hx⟩
  simpa [LinearMap.domRestrict₁₂_apply] using this

theorem nonempty_equiv_of_pair (hσ : Function.Surjective σ)
    (hfin : ∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S₂ S : Subrepresentation ρ} (h₁ : IsAtom S₁) (h₂ : IsAtom S₂) (h : IsAtom S)
    (hn₁ : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0)
    (hn₂ : ∃ x ∈ S₂.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) := by
  haveI := hfin S₁ h₁
  haveI := hfin S₂ h₂
  haveI := hfin S h
  set f₁ := B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule with hf₁def
  set f₂ := B.domRestrict₁₂ S₂.toSubmodule S.toSubmodule with hf₂def
  have i₁ : Function.Injective f₁ := restr_injective B hB h₁ hn₁
  have i₂ : Function.Injective f₂ := restr_injective B hB h₂ hn₂
  have j₁ : Function.Injective f₁.flip := restr_flip_injective hσ B hB h hn₁
  have j₂ : Function.Injective f₂.flip := restr_flip_injective hσ B hB h hn₂
  have d₁ : finrank ℂ S₁.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule) := by
    rw [Subspace.dual_finrank_eq]
    refine le_antisymm ?_ ?_
    · exact (LinearMap.finrank_le_finrank_of_injective i₁).trans_eq Subspace.dual_finrank_eq
    · exact (LinearMap.finrank_le_finrank_of_injective j₁).trans_eq Subspace.dual_finrank_eq
  have d₂ : finrank ℂ S₂.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule) := by
    rw [Subspace.dual_finrank_eq]
    refine le_antisymm ?_ ?_
    · exact (LinearMap.finrank_le_finrank_of_injective i₂).trans_eq Subspace.dual_finrank_eq
    · exact (LinearMap.finrank_le_finrank_of_injective j₂).trans_eq Subspace.dual_finrank_eq
  let e₁ := LinearEquiv.ofBijective f₁ ⟨i₁, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₁).mp i₁⟩
  let e₂ := LinearEquiv.ofBijective f₂ ⟨i₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₂).mp i₂⟩
  let e := e₁.trans e₂.symm
  have hfe : ∀ x, f₂ (e x) = f₁ x := by
    intro x
    have h1 : ∀ z, e₁ z = f₁ z := fun z => LinearEquiv.ofBijective_apply _ _
    have h2 : ∀ z, e₂ z = f₂ z := fun z => LinearEquiv.ofBijective_apply _ _
    rw [← h1, ← h2]
    simp [e]
  have hcomm : ∀ (x : S₁.toSubmodule) (y : S.toSubmodule), B (e x : V) y = B x y := by
    intro x y
    have := LinearMap.congr_fun (hfe x) y
    simpa [f₁, f₂, LinearMap.domRestrict₁₂_apply] using this
  refine ⟨Representation.Equiv.mk e fun k => ?_⟩
  apply LinearMap.ext
  intro x
  apply i₂
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf₂def, LinearMap.domRestrict₁₂_apply]
  rw [hcomm]
  change B (ρ k x) y = B (ρ k (e x)) y
  rw [pair_left B hB, pair_left B hB]
  exact (hcomm x ⟨_, S.apply_mem_toSubmodule _ y.2⟩).symm

lemma exists_atom_pair
    (hsum : ∀ X : Subrepresentation ρ,
      X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (Y : Subrepresentation ρ) (ψ : V)
    (h : ∃ y ∈ Y.toSubmodule, B y ψ ≠ 0) :
    ∃ S₁ : Subrepresentation ρ, IsAtom S₁ ∧ S₁ ≤ Y ∧ ∃ x ∈ S₁.toSubmodule, B x ψ ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨y, hy, hne⟩ := h
  apply hne
  have hle : Y.toSubmodule ≤ LinearMap.ker (B.flip ψ) := by
    rw [hsum Y]
    exact iSup₂_le fun S hS x hx => by simpa using hc S hS.1 hS.2 x hx
  simpa using hle hy

end GlobalTheory.IsotypicOrth

namespace GlobalTheory.IsotypicOrth

theorem orth_isCompl : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V) (σ : K →* K), Function.Surjective σ → (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) → ∀ X Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule → (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) → IsCompl (⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)) (⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)) := by
  intro K V _ _ _ ρ σ hσ hfin hsum B _hl hr hB X Y hXY hiso
  constructor
  · rw [Submodule.disjoint_def]
    intro ψ h1 h2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h1 h2
    apply hr
    intro φ
    have : φ ∈ X.toSubmodule ⊔ Y.toSubmodule := by rw [hXY.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
    rw [map_add (f := _), LinearMap.add_apply, h1 b hb, h2 a ha, add_zero]
  · rw [codisjoint_iff, eq_top_iff]
    have htop := hsum ⊤
    change (⊤ : Submodule ℂ V) = _ at htop
    rw [htop]
    refine iSup₂_le fun S hS => ?_
    by_cases hY : S.toSubmodule ≤ ⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)
    · exact le_sup_of_le_left hY
    by_cases hX : S.toSubmodule ≤ ⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)
    · exact le_sup_of_le_right hX
    exfalso
    obtain ⟨ψ₁, hψ₁, hψ₁'⟩ := SetLike.not_le_iff_exists.mp hY
    obtain ⟨ψ₂, hψ₂, hψ₂'⟩ := SetLike.not_le_iff_exists.mp hX
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, not_forall] at hψ₁' hψ₂'
    obtain ⟨y, hy, hy'⟩ := hψ₁'
    obtain ⟨x, hx, hx'⟩ := hψ₂'
    obtain ⟨S₁, a₁, l₁, x₁, hx₁, n₁⟩ := exists_atom_pair hsum B Y ψ₁ ⟨y, hy, hy'⟩
    obtain ⟨S₂, a₂, l₂, x₂, hx₂, n₂⟩ := exists_atom_pair hsum B X ψ₂ ⟨x, hx, hx'⟩
    have e := nonempty_equiv_of_pair hσ hfin B hB a₁ a₂ hS.1 ⟨x₁, hx₁, ψ₁, hψ₁, n₁⟩
      ⟨x₂, hx₂, ψ₂, hψ₂, n₂⟩
    exact (hiso S₁ S₂ a₁ a₂ l₁ l₂).false e.some

end GlobalTheory.IsotypicOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsNilpotentOfTracePow
section
open Polynomial

namespace GlobalTheory.NilpotentOfTracePowers

theorem trace_mul_aeval {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) (p : K[X]) :
    LinearMap.trace K V (f * aeval f p) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, map_smul, ← pow_succ', h (i + 1) (by omega), smul_zero]

theorem exists_pow_eq {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    ∃ (m : ℕ) (g : K[X]), f ^ m = f ^ m * aeval f (X * g) := by
  have hp : f.charpoly ≠ 0 := f.charpoly_monic.ne_zero
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f.charpoly hp 0
  set m := rootMultiplicity 0 f.charpoly
  have hc : q.coeff 0 ≠ 0 := by
    intro h0
    apply hnd
    rw [map_zero, sub_zero]
    exact X_dvd_iff.mpr h0
  have h0 : aeval f f.charpoly = 0 := f.aeval_self_charpoly
  have hpoly : (X : K[X]) ^ m = X ^ m * (X * (C (-(q.coeff 0)⁻¹) * q.divX))
      + C (q.coeff 0)⁻¹ * f.charpoly := by
    have h1 : X * q.divX + C (q.coeff 0) = q := X_mul_divX_add q
    have h2 : C (q.coeff 0)⁻¹ * C (q.coeff 0) = (1 : K[X]) := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    rw [map_zero, sub_zero] at hq
    rw [map_neg]
    linear_combination (-C (q.coeff 0)⁻¹) * hq + (C (q.coeff 0)⁻¹ * X ^ m) * h1 - X ^ m * h2
  refine ⟨m, C (-(q.coeff 0)⁻¹) * q.divX, ?_⟩
  have := congrArg (aeval f) hpoly
  rw [map_add (f := _), map_mul (aeval f) _ f.charpoly, h0, mul_zero, add_zero, map_mul, map_pow,
    aeval_X] at this
  exact this

theorem isNilpotent_of_trace_pow {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  obtain ⟨m, g, hm⟩ := exists_pow_eq f
  have hiter : ∀ j : ℕ, f ^ m = f ^ m * aeval f ((X * g) ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', map_mul, ← mul_assoc, ← hm, ← ih]
  set e : Module.End K V := aeval f ((X * g) ^ (m + 1)) with he
  have he1 : e = aeval f (X * g ^ (m + 1)) * f ^ m := by
    have : (X * g) ^ (m + 1) = (X * g ^ (m + 1)) * X ^ m := by ring
    rw [he, this, map_mul (aeval f) _ (X ^ m), map_pow, aeval_X]
  have hid : IsIdempotentElem e := by
    unfold IsIdempotentElem
    conv_lhs => enter [1]; rw [he1]
    rw [mul_assoc, ← hiter (m + 1), ← he1]
  have htr : LinearMap.trace K V e = 0 := by
    have : (X * g) ^ (m + 1) = X * (g ^ (m + 1) * X ^ m) := by ring
    rw [he, this, map_mul, aeval_X]
    exact trace_mul_aeval f h _
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    { map_mem := fun x => LinearMap.mem_range_self e x
      map_id := by
        rintro _ ⟨x, rfl⟩
        exact LinearMap.congr_fun hid x }
  have hrk : Module.finrank K (LinearMap.range e) = 0 := by
    have := hproj.trace
    rw [htr] at this
    exact_mod_cast this.symm
  have he0 : e = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hrk)
  exact ⟨m, by rw [hiter (m + 1), ← he, he0, mul_zero]⟩

end GlobalTheory.NilpotentOfTracePowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedQuotientOfArtinianOfMaximalLe
section
namespace GlobalTheory

open scoped BigOperators

theorem quotient_maximal_le_sq {A : Type} [CommRing A] (I : Ideal A)
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2)
    (M : Ideal (A ⧸ I)) (hM : M.IsMaximal) : M ≤ M ^ 2 := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  set m := M.comap (Ideal.Quotient.mk I) with hm
  have hmax : m.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hIm : I ≤ m := by
    intro x hx
    simp [hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have key := Ideal.map_mono (f := Ideal.Quotient.mk I) (h m hmax hIm)
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_quotient_self, bot_sup_eq,
    hm, Ideal.map_comap_of_surjective _ hsurj] at key
  exact key

theorem pow_eq_self_of_le_sq {R : Type} [CommRing R] (M : Ideal R) (h : M ≤ M ^ 2) :
    ∀ k : ℕ, M ^ (k + 1) = M := by
  have h2 : M * M = M := by
    rw [← sq]; exact le_antisymm (Ideal.pow_le_self two_ne_zero) h
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, h2]

theorem isReduced_quotient_of_artinian_of_maximal_le (A : Type) [CommRing A] (I : Ideal A)
    (hart : IsArtinianRing (A ⧸ I))
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) : IsReduced (A ⧸ I) := by
  classical
  set R := A ⧸ I
  haveI : Finite (MaximalSpectrum R) := inferInstance
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  set J : Ideal R := ∏ M : MaximalSpectrum R, M.asIdeal with hJ
  have hJinf : J = ⨅ M ∈ (Finset.univ : Finset (MaximalSpectrum R)), M.asIdeal := by
    rw [hJ]
    apply Ideal.prod_eq_iInf_of_pairwise_isCoprime
    intro a _ b _ hab
    exact Ideal.isCoprime_of_isMaximal (fun e => hab (MaximalSpectrum.ext e))
  have hpow : ∀ k : ℕ, J ^ (k + 1) = J := by
    intro k
    rw [hJ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun M _ => ?_)
    exact pow_eq_self_of_le_sq _ (quotient_maximal_le_sq I h M.asIdeal M.isMaximal) k
  have hJjac : J ≤ Ideal.jacobson ⊥ := by
    rw [hJinf]
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    by_contra hu
    obtain ⟨M, hMmax, hM⟩ := Ideal.exists_le_maximal (Ideal.span {x * y + 1})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hxM : x ∈ M := by
      have := (Submodule.mem_iInf _).mp hx ⟨M, hMmax⟩
      simpa using this
    have h1 : x * y + 1 ∈ M := hM (Ideal.subset_span rfl)
    have : (1 : R) ∈ M := by
      have := M.sub_mem h1 (M.mul_mem_right y hxM)
      simpa using this
    exact hMmax.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hJbot : J = ⊥ := by
    rw [← hpow n]
    refine le_bot_iff.mp ?_
    calc J ^ (n + 1) ≤ (Ideal.jacobson ⊥) ^ (n + 1) := Ideal.pow_right_mono hJjac _
      _ ≤ (Ideal.jacobson ⊥) ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
      _ = ⊥ := hn
  refine ⟨fun x hx => ?_⟩
  have hxJ : x ∈ J := by
    rw [hJinf]
    refine (Submodule.mem_iInf _).mpr (fun M => (Submodule.mem_iInf _).mpr (fun _ => ?_))
    exact (hx.map (Ideal.Quotient.mk M.asIdeal)).eq_zero |> Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hJbot] at hxJ
  exact (Submodule.mem_bot R).mp hxJ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthLeOfForallFgSubmoduleLengthLe
section
open Pointwise

namespace GlobalTheory

theorem length_le_of_forall_fg_length_le (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞)
    (h : ∀ N : Submodule O M, N.FG → Module.length O N ≤ b) : Module.length O M ≤ b := by
  rw [Module.length_eq_height]
  refine Order.height_le_iff'.2 fun p _ => ?_
  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hx1 hx2 using hx
  set N : Submodule O M := Submodule.span O (Set.range x) with hN
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range x)
  have hxN : ∀ i, x i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  let q : LTSeries (Submodule O N) :=
    { length := p.length
      toFun := fun i => (p i).comap N.subtype
      step := fun i => by
        refine lt_of_le_of_ne (Submodule.comap_mono (p.step i).le) ?_
        intro heq
        have h1 : (⟨x i, hxN i⟩ : N) ∈ (p i.succ).comap N.subtype := hx1 i
        rw [← heq] at h1
        exact hx2 i h1 }
  have h2 : (q.length : ℕ∞) ≤ Order.height (⊤ : Submodule O N) :=
    Order.length_le_height le_top
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height (⊤ : Submodule O N) := h2
    _ = Module.length O N := (Module.length_eq_height (R := O) (M := N)).symm
    _ ≤ b := h N hNfg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientScalarMul
section
open Pointwise

namespace GlobalTheory

theorem length_quot_smul_range_finite_free : ∀ (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (a : O), Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) = (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  intro O M _ _ _ _ _ _ a
  classical
  set d := Module.finrank O M
  let e : M ≃ₗ[O] (Fin d → O) := (Module.finBasis O M).equivFun
  have hmap : (LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))).map (e : M →ₗ[O] (Fin d → O))
      = Submodule.pi Set.univ (fun _ : Fin d => (Ideal.span {a} : Submodule O O)) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
    · intro h
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (h i)
      refine ⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [← hc i, mul_comm]
  let f := (Submodule.Quotient.equiv _ _ e hmap).trans
    (Submodule.quotientPi (fun _ : Fin d => (Ideal.span {a} : Submodule O O)))
  rw [f.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCardMatricesMulEqZero
section
open Matrix

namespace GlobalTheory

def killersEquiv {k : Type} [Field k] {m n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    {w : Matrix (Fin m) (Fin n) k // w * A = 0} ≃ (Fin m → LinearMap.ker (Aᵀ).mulVecLin) where
  toFun w i := ⟨w.1 i, by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
    funext l
    have := congrFun (congrFun w.2 i) l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  invFun f := ⟨Matrix.of fun i => (f i).1, by
    ext i l
    have h := (f i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at h
    have := congrFun h l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  left_inv w := by ext i l; rfl
  right_inv f := by ext i l; rfl

theorem natCard_matrices_mul_eq_zero (k : Type) [Field k] [Finite k] (m n j : ℕ)
    (A : Matrix (Fin n) (Fin n) k)
    (h : Module.finrank k (LinearMap.range A.mulVecLin) + j = n) :
    Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  have h1 : Module.finrank k (LinearMap.range (Aᵀ).mulVecLin)
      = Module.finrank k (LinearMap.range A.mulVecLin) := Matrix.rank_transpose A
  have h2 := LinearMap.finrank_range_add_finrank_ker (Aᵀ).mulVecLin
  rw [h1, Module.finrank_fin_fun] at h2
  have h3 : Module.finrank k (LinearMap.ker (Aᵀ).mulVecLin) = j := by omega
  rw [Nat.card_congr (killersEquiv A), Nat.card_fun, Module.natCard_eq_pow_finrank (K := k), h3,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, pow_mul]

end GlobalTheory
end

