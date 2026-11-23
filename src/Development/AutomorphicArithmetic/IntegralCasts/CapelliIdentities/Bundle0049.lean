module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ParabolicUnipotentGL
section
noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep.{u_1} :
    {n : ℕ} →
      {M : Type u_1} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → (Fin n → Fin n → Module.End ℂ M) → Prop :=
    fun {n : ℕ} {M : Type u_1} [AddCommGroup M] [_root_.Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b =
          (if b = c then E a d else (0 : Module.End ℂ M)) - if d = a then E c b else (0 : Module.End ℂ M)

noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.U :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Fin n → Module.End ℂ V) → ℕ → Submodule ℂ (Module.End ℂ V) :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) ↦
      Submodule.span ℂ
        {x : Module.End ℂ V |
          ∃ (l : List (Fin n × Fin n)), l.length ≤ k ∧ x = (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod}

namespace UpperTheory.Reformulated.B.ParabolicUnipotentGL

section helpers

variable {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

private abbrev P (l : List (Fin n × Fin n)) : Module.End ℂ V :=
  (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod

private theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

private theorem monomial_mem_filtration_of_length_le (l : List (Fin n × Fin n)) {k : ℕ} (h : l.length ≤ k) : P E l ∈ U E k :=
  Submodule.subset_span ⟨l, h, rfl⟩

private theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 := by
  have := monomial_mem_filtration_of_length_le E [(a, b)] (k := 1) (by simp)
  simpa [P] using this

private theorem mul_mem_U {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine Submodule.subset_span ⟨l ++ m, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · simp
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

private theorem gen_comm_mem (hE : IsGlRep E) (a b c d : Fin n) :
    E a b * E c d - E c d * E a b ∈ U E 1 := by
  rw [hE a b c d]
  refine sub_mem ?_ ?_
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _

private theorem gen_comm_P (hE : IsGlRep E) (a b : Fin n) (l : List (Fin n × Fin n)) :
    E a b * P E l - P E l * E a b ∈ U E l.length := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : E a b * P E (p :: t) - P E (p :: t) * E a b
        = (E a b * E p.1 p.2 - E p.1 p.2 * E a b) * P E t
          + E p.1 p.2 * (E a b * P E t - P E t * E a b) := by
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e, List.length_cons, add_comm t.length 1]
    exact add_mem (mul_mem_U E (gen_comm_mem E hE _ _ _ _) (monomial_mem_filtration_of_length_le E t le_rfl))
      (mul_mem_U E (gen_mem E _ _) ih)

private theorem monomial_commutator_mem_filtration (hE : IsGlRep E) (l : List (Fin n × Fin n)) (q : Fin n × Fin n)
    (m : List (Fin n × Fin n)) :
    P E l * P E (q :: m) - P E (q :: m) * P E l ∈ U E (l.length + m.length) := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : P E (p :: t) * P E (q :: m) - P E (q :: m) * P E (p :: t)
        = E p.1 p.2 * (P E t * P E (q :: m) - P E (q :: m) * P E t)
          + (E p.1 p.2 * P E (q :: m) - P E (q :: m) * E p.1 p.2) * P E t := by
      generalize P E (q :: m) = y
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e]
    refine add_mem ?_ ?_
    · exact U_mono E (by simp only [List.length_cons]; omega) (mul_mem_U E (gen_mem E _ _) ih)
    · exact U_mono E (by simp only [List.length_cons]; omega)
        (mul_mem_U E (gen_comm_P E hE _ _ (q :: m)) (monomial_mem_filtration_of_length_le E t le_rfl))

end helpers

end UpperTheory.Reformulated.B.ParabolicUnipotentGL

theorem UpperTheory.Reformulated.B.ParabolicUnipotentGL.main :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep E →
        ∀ {j k : ℕ} {x y : Module.End ℂ V},
          x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E j →
            y ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E k → x * y - y * x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E (j + k - (1 : ℕ)) := by
  intro n V _ _ E hE j k x y hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      cases m with
      | nil => simp
      | cons q t =>
        simp only [List.length_cons] at hm
        exact UpperTheory.Reformulated.B.ParabolicUnipotentGL.U_mono E (by omega) (UpperTheory.Reformulated.B.ParabolicUnipotentGL.monomial_commutator_mem_filtration E hE l q t)
    | zero => simp
    | add a b _ _ ha hb =>
      have e : x * (a + b) - (a + b) * x = (x * a - a * x) + (x * b - b * x) := by noncomm_ring
      rw [e]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : x * (c • a) - (c • a) * x = c • (x * a - a * x) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [e]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb =>
    have e : (a + b) * y - y * (a + b) = (a * y - y * a) + (b * y - y * b) := by noncomm_ring
    rw [e]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : (c • a) * y - y * (c • a) = c • (a * y - y * a) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PartialDerivMonomialLaplace
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Gs1.Wt :
    ℕ → Type :=
    fun (n : ℕ) ↦ Fin n → ℝ

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gs1.FR :
    ℕ → Type :=
    fun (n : ℕ) ↦ AddMonoidAlgebra ℂ (UpperTheory.Reformulated.B.Gs1.Wt n)

theorem UpperTheory.Reformulated.B.Gs1.aux3 :
    ∀ {n : ℕ} (a : Fin n) (f : UpperTheory.Reformulated.B.Gs1.FR n) (x : UpperTheory.Reformulated.B.Gs1.Wt n),
      (↑(x a) : ℂ) * (f.coeff : UpperTheory.Reformulated.B.Gs1.Wt n → ℂ) x ≠ (0 : ℂ) → x ∈ f.coeff.support := by
  intro n a f x h
  exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul h)

noncomputable def UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace :
    {n : ℕ} → Fin n → UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n :=
    fun {n : ℕ} (a : Fin n) (f : UpperTheory.Reformulated.B.Gs1.FR n) ↦
      AddMonoidAlgebra.ofCoeff
        (Finsupp.onFinset f.coeff.support
          (fun (x : UpperTheory.Reformulated.B.Gs1.Wt n) ↦ (↑(x a) : ℂ) * (f.coeff : UpperTheory.Reformulated.B.Gs1.Wt n → ℂ) x)
          (UpperTheory.Reformulated.B.Gs1.aux3 a f))

theorem UpperTheory.Reformulated.B.Gs1.aux5 :
    ∀ {n : ℕ} (a : Fin n) (f g : UpperTheory.Reformulated.B.Gs1.FR n),
      UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a (f + g) = UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a f + UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a g := by
  intro n a f g
  ext x
  simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace, mul_add]

theorem UpperTheory.Reformulated.B.Gs1.aux6 :
    ∀ {n : ℕ} (a : Fin n) (c : ℂ) (f : UpperTheory.Reformulated.B.Gs1.FR n),
      UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a (c • f) = (RingHom.id ℂ : ℂ → ℂ) c • UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a f := by
  intro n a c f
  ext x
  simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace, mul_left_comm]

noncomputable def UpperTheory.Reformulated.B.Gs1.lapD :
    {n : ℕ} → Fin n → UpperTheory.Reformulated.B.Gs1.FR n →ₗ[ℂ] UpperTheory.Reformulated.B.Gs1.FR n :=
    fun {n : ℕ} (a : Fin n) ↦
      { toFun := UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a, map_add' := UpperTheory.Reformulated.B.Gs1.aux5 a, map_smul' := UpperTheory.Reformulated.B.Gs1.aux6 a :
        UpperTheory.Reformulated.B.Gs1.FR n →ₗ[ℂ] UpperTheory.Reformulated.B.Gs1.FR n }

private theorem UpperTheory.Reformulated.B.Gs1.lapD_single {n : ℕ} (a : Fin n) (x : UpperTheory.Reformulated.B.Gs1.Wt n) (c : ℂ) :
    UpperTheory.Reformulated.B.Gs1.lapD a (AddMonoidAlgebra.single x c) =
      AddMonoidAlgebra.single x ((x a : ℂ) * c) := by
  classical
  change UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a _ = _
  ext y
  by_cases h : x = y
  · subst h
    simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace]
  · simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace, Finsupp.single_apply, h]

theorem UpperTheory.Reformulated.B.Gs1.lapD_mul :
    ∀ {n : ℕ} (a : Fin n) (f g : UpperTheory.Reformulated.B.Gs1.FR n),
      (UpperTheory.Reformulated.B.Gs1.lapD a : UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n) (f * g) =
        (UpperTheory.Reformulated.B.Gs1.lapD a : UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n) f * g +
          f * (UpperTheory.Reformulated.B.Gs1.lapD a : UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n) g := by
  intro n a f g
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
    rw [add_mul, map_add (f := _), map_add (f := _), h₁, h₂, add_mul, add_mul]
    abel
  | single x c =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ =>
      rw [mul_add, map_add (f := _), map_add (f := _), h₁, h₂, mul_add, mul_add]
      abel
    | single y d =>
      simp only [AddMonoidAlgebra.single_mul_single, UpperTheory.Reformulated.B.Gs1.lapD_single]
      rw [← AddMonoidAlgebra.single_add]
      congr 1
      simp only [Pi.add_apply, Complex.ofReal_add]
      ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PbMem
section
namespace UpperTheory.Reformulated.B.Qi43

theorem pb_mem {B C : Type} [Group B] [Group C] (J : B →* C) (UQ : Subgroup C)
    (hc : ∀ u ∈ UQ, ∀ g : B, Commute u (J g)) (K : Subgroup B) (x : C) :
    x ∈ UQ ⊔ Subgroup.map J K ↔ ∃ u ∈ UQ, ∃ k ∈ K, x = u * J k := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, K.one_mem, by simp⟩
      · obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨1, UQ.one_mem, k, hk, by simp⟩
    | one => exact ⟨1, UQ.one_mem, 1, K.one_mem, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hy
      obtain ⟨v, hv, l, hl, rfl⟩ := hz
      refine ⟨u * v, UQ.mul_mem hu hv, k * l, K.mul_mem hk hl, ?_⟩
      rw [map_mul, mul_assoc, ← mul_assoc (J k), ← (hc v hv k).eq]
      simp only [mul_assoc]
    | inv y _ hy =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hy
      refine ⟨u⁻¹, UQ.inv_mem hu, k⁻¹, K.inv_mem hk, ?_⟩
      rw [(hc u hu k).eq, mul_inv_rev, map_inv]
  · rintro ⟨u, hu, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
      (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem J hk))

end UpperTheory.Reformulated.B.Qi43
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Per
section
namespace PeriodicSumRangeMul

private lemma per {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (h : ∀ (i : ℕ), g (i + P) = g i) (k x : ℕ) : g (k * P + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P + x = (k * P + x) + P by ring, h, ih]

end PeriodicSumRangeMul

theorem UpperTheory.Reformulated.B.Yra7.main :
    ∀ {N : Type} [inst : AddCommGroup N] (g : ℕ → N) (P : ℕ),
      (∀ (i : ℕ), g (i + P) = g i) → ∀ (k : ℕ), ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i := by
  intro N _ g P h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P = k * P + P by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => PeriodicSumRangeMul.per g P h k x)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMulSelf
section
noncomputable def UpperTheory.Reformulated.B.Yzd3.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)

theorem UpperTheory.Reformulated.B.Yzd3.phi_mul_self :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd3.Phi a R * UpperTheory.Reformulated.B.Yzd3.Phi a R = (-1 : R) ^ (a - (1 : ℕ)) • (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i k
  have hi := i.2
  have hk := k.2
  have hj : a - 1 - (i : ℕ) < a := by omega
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.Yzd3.Phi, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨a - 1 - (i : ℕ), hj⟩ : Fin a)]
  · have h1 : (i : ℕ) + (a - 1 - (i : ℕ)) + 1 = a := by omega
    dsimp only
    rw [if_pos h1]
    by_cases hik : i = k
    · subst hik
      have h2 : (a - 1 - (i : ℕ)) + (i : ℕ) + 1 = a := by omega
      rw [if_pos h2, if_pos rfl, mul_one, ← pow_add]
      congr 1
      omega
    · have h2 : ¬ ((a - 1 - (i : ℕ)) + (k : ℕ) + 1 = a) := by
        intro h
        exact hik (Fin.ext (by omega))
      rw [if_neg h2, if_neg hik, mul_zero, mul_zero]
  · intro j _ hne
    have h1 : ¬ ((i : ℕ) + (j : ℕ) + 1 = a) := by
      intro h
      exact hne (Fin.ext (by simp only []; omega))
    rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMulTranspose
section
noncomputable def UpperTheory.Reformulated.B.Yzd2.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)

theorem UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd2.Phi a R * (UpperTheory.Reformulated.B.Yzd2.Phi a R).transpose = (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, UpperTheory.Reformulated.B.Yzd2.Phi, Matrix.of_apply,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h
    have hi := i.isLt
    let k : Fin a := ⟨a - 1 - (i : ℕ), by omega⟩
    have hk : (k : ℕ) = a - 1 - (i : ℕ) := rfl
    rw [Finset.sum_eq_single k]
    · have h1 : (i : ℕ) + (k : ℕ) + 1 = a := by omega
      rw [if_pos h1, if_pos rfl, ← mul_pow]
      simp
    · intro b _ hb
      have h1 : ¬ ((i : ℕ) + (b : ℕ) + 1 = a) := by
        intro h2
        apply hb
        ext
        omega
      simp [h1]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h1 : (i : ℕ) + (k : ℕ) + 1 = a
    · have h2 : ¬ ((j : ℕ) + (k : ℕ) + 1 = a) := by
        intro h2
        apply h
        ext
        omega
      simp [h2]
    · simp [h1]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PiSpanVariable
section
theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X :
    ∀ {O σ : Type} [inst : CommRing O] (s : Finset σ)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ), (∀ i ∈ s, (n : σ → ℕ) i = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range MvPowerSeries.X) := by
  intro O σ inst s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a t hat ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n a = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n a = 0 then MvPowerSeries.coeff n f else 0 := fun n => rfl
    have h1 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) := by
      apply ih
      intro n hn
      rw [hg]
      split_ifs with h
      · apply hf
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X a : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub, hg, if_pos hm, sub_self]
    have h3 : f - g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Plc
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe49.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.Qe49.exists_prime_mem :
    ∀ {E : Type} [inst : Field E] [NumberField E] (w : UpperTheory.Reformulated.B.Qe49.Plc E),
      ∃ (q : ℕ), Nat.Prime q ∧ (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ w
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  refine ⟨ringChar (NumberField.RingOfIntegers E ⧸ w.asIdeal),
    CharP.prime_ringChar _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PolyInMul
section
noncomputable def UpperTheory.Reformulated.B.Qk18.PolyIn :
    {R : Type} → [inst : Ring R] → [Algebra ℂ R] → (ℂ → R) → ℕ → Prop :=
    fun {R : Type} [Ring R] [Algebra ℂ R] (f : ℂ → R) (d : ℕ) ↦
      ∃ (a : ℕ → R), ∀ (s : ℂ), f s = ∑ k ∈ Finset.range (d + (1 : ℕ)), s ^ k • a k

theorem UpperTheory.Reformulated.B.Qk18.polyIn_mul :
    ∀ {R : Type} [inst : Ring R] [inst_1 : Algebra ℂ R] {f g : ℂ → R} {d₁ d₂ : ℕ},
      UpperTheory.Reformulated.B.Qk18.PolyIn f d₁ →
        UpperTheory.Reformulated.B.Qk18.PolyIn g d₂ → UpperTheory.Reformulated.B.Qk18.PolyIn (fun (t : ℂ) ↦ f t * g t) (d₁ + d₂) := by
  intro R _ _ f g d₁ d₂ hf hg
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun n => ∑ i ∈ Finset.range (d₁ + 1), ∑ j ∈ Finset.range (d₂ + 1),
    if i + j = n then a i * b j else 0, fun s => ?_⟩
  show f s * g s = _
  rw [ha s, hb s, Finset.sum_mul_sum]
  simp only [Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hmem : i + j ∈ Finset.range (d₁ + d₂ + 1) := by
    rw [Finset.mem_range] at hi hj ⊢
    omega
  rw [Finset.sum_eq_single_of_mem (i + j) hmem]
  · rw [if_pos rfl, smul_mul_smul_comm, pow_add]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), smul_zero]
end

