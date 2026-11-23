module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ShiftSingleInt
section
namespace GlobalTheory.IntegerShiftSingle

universe u_1 u_2 u_3

theorem shift_single_int {ι : Type u_1} {R : Type u_2} {E : Type u_3} [DecidableEq ι] [Ring R]
    {F : (ι → R) → E} (h : ∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x)
    (i : ι) (k : ℤ) : ∀ x : ι → R, F (x + Pi.single i ((k : ℤ) : R)) = F x := by
  induction k using Int.induction_on with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    have : x + Pi.single i (((m : ℤ) + 1 : ℤ) : R) = (x + Pi.single i ((m : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [Int.cast_add, Int.cast_one, Pi.single_add, add_assoc]
    rw [this, h, ih]
  | pred m ih =>
    intro x
    have : x + Pi.single i ((-(m : ℤ) : ℤ) : R) = (x + Pi.single i ((-(m : ℤ) - 1 : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [add_assoc, ← Pi.single_add]
      congr 2
      push_cast
      first | rfl | ring | abel | simp
    rw [← ih x, this, h]

theorem main {ι : Type u_1} {R : Type u_2} {E : Type u_3} [Fintype ι] [inst : DecidableEq ι] [inst_1 : Ring R]
    {F : (ι → R) → E} : (∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x) →
    ∀ (n : ι → ℤ) (x : ι → R), F (x + fun (i : ι) ↦ (↑(n i) : R)) = F x := by
  intro h n x
  have key : ∀ s : Finset ι, ∀ y : ι → R, F (y + ∑ i ∈ s, Pi.single i ((n i : ℤ) : R)) = F y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [Finset.sum_insert ha, ← add_assoc, ih, shift_single_int h]
  have hsum : (fun i : ι => ((n i : ℤ) : R)) = ∑ i ∈ Finset.univ, Pi.single i ((n i : ℤ) : R) := by
    rw [Finset.univ_sum_single]
  rw [hsum]
  exact key Finset.univ x

end GlobalTheory.IntegerShiftSingle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.SpanEvalEqTop
section
namespace GlobalTheory.EvaluationSpanTopToricGeometry

theorem span_eval_eq_top {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
      = ⊤ := by

  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set v : V := (Module.evalEquiv ℂ V).symm f with hv
  have hfv : Module.evalEquiv ℂ V v = f := by rw [hv, LinearEquiv.apply_symm_apply]
  have hv0 : v = 0 := by
    apply Subtype.ext
    funext x
    have hx : (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype ∈ LinearMap.ker f :=
      hle (Submodule.subset_span ⟨x, rfl⟩)
    rw [LinearMap.mem_ker, ← hfv] at hx
    exact hx
  apply hf0
  rw [← hfv, hv0, map_zero]

theorem exists_sum_mul {X Y : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (L : Submodule ℂ (Y → ℂ)) (F : X → Y → ℂ) (hV : ∀ y : Y, (fun x : X => F x y) ∈ V)
    (hL : ∀ x : X, F x ∈ L) :
    ∃ (n : ℕ) (h : Fin n → X → ℂ) (k : Fin n → Y → ℂ),
      (∀ i : Fin n, h i ∈ V ∧ k i ∈ L) ∧
        ∀ (x : X) (y : Y), F x y = ∑ i : Fin n, h i x * k i y := by

  let Φ : Module.Dual ℂ V →ₗ[ℂ] (Y → ℂ) :=
    { toFun := fun φ y => φ ⟨fun x => F x y, hV y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

  have hΦ : ∀ φ, Φ φ ∈ L := by
    have hle : Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
        ≤ L.comap Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hL x
    intro φ
    exact hle (by rw [span_eval_eq_top V]; trivial)
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V, fun i => (b i : X → ℂ), fun i => Φ (b.coord i), fun i => ⟨(b i).2, hΦ _⟩, ?_⟩
  intro x y
  have hs := congrArg (fun w : V => (w : X → ℂ) x) (b.sum_repr ⟨fun x' => F x' y, hV y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  rw [← hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.EvaluationSpanTopToricGeometry
end

