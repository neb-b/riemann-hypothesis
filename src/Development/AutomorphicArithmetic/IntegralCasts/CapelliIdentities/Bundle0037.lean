module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InverseOmegaHolds
section
noncomputable def UpperTheory.Reformulated.B.Gwa1.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.Gwa1.IsWq :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      have c : ℂ_[p] →+* PowerSeries ℂ_[p] := Algebra.algebraMap ℂ_[p] (PowerSeries ℂ_[p]);
      have X : PowerSeries ℂ_[p] := PowerSeries.X;
      wq =
        (1 : PowerSeries ℂ_[p]) + (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₁ * X * wq +
                (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₂ * X ^ (2 : ℕ) * wq +
              (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₃ * X ^ (3 : ℕ) * wq ^ (2 : ℕ) +
            (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₄ * X ^ (4 : ℕ) * wq ^ (2 : ℕ) +
          (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₆ * X ^ (6 : ℕ) * wq ^ (3 : ℕ)

noncomputable def UpperTheory.Reformulated.B.Gwa1.dX.{u_1} :
    {A : Type u_1} → [CommRing A] → PowerSeries A → PowerSeries A :=
    fun {A : Type u_1} [CommRing A] (f : PowerSeries A) ↦
      PowerSeries.mk fun (n : ℕ) ↦ ((↑n : A) + (1 : A)) * (PowerSeries.coeff (n + (1 : ℕ)) : PowerSeries A → A) f

noncomputable def UpperTheory.Reformulated.B.Gwa1.omegaW :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → PowerSeries ℂ_[p] :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      have c : ℂ_[p] →+* PowerSeries ℂ_[p] := Algebra.algebraMap ℂ_[p] (PowerSeries ℂ_[p]);
      have X : PowerSeries ℂ_[p] := PowerSeries.X;
      ((-2 : PowerSeries ℂ_[p]) * wq - X * UpperTheory.Reformulated.B.Gwa1.dX wq) *
        (wq *
            ((c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₁ * X + (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₃ * X ^ (3 : ℕ) * wq -
              (2 : PowerSeries ℂ_[p])))⁻¹

noncomputable def UpperTheory.Reformulated.B.Gwa1.flog :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → PowerSeries ℂ_[p] :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      PowerSeries.mk fun (n : ℕ) ↦
        if n = (0 : ℕ) then (0 : ℂ_[p])
        else (PowerSeries.coeff (n - (1 : ℕ)) : PowerSeries ℂ_[p] → ℂ_[p]) (UpperTheory.Reformulated.B.Gwa1.omegaW W wq) / (↑n : ℂ_[p])

noncomputable def UpperTheory.Reformulated.B.Gwa1.InvOmega :
    Prop :=
    ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₁ →
        UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₂ →
          UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₃ →
            UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₄ →
              UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₆ →
                UpperTheory.Reformulated.B.Gwa1.IsWq W wq →
                  ∃ (v : PowerSeries ℂ_[p]),
                    (∀ (n : ℕ), UpperTheory.Reformulated.B.Gwa1.IsIntP ((PowerSeries.coeff n : PowerSeries ℂ_[p] → ℂ_[p]) v)) ∧
                      v * UpperTheory.Reformulated.B.Gwa1.dX (UpperTheory.Reformulated.B.Gwa1.flog W wq) = (1 : PowerSeries ℂ_[p])

namespace UpperTheory.Reformulated.B.Gwa1

open PowerSeries

private def lowIn {R : Type*} [CommRing R] (O : Subring R) (n : ℕ) : Subring R⟦X⟧ where
  carrier := {f | ∀ k < n, coeff k f ∈ O}
  mul_mem' := by
    intro f g hf hg k hk
    rw [coeff_mul]
    refine O.sum_mem fun x hx => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    exact O.mul_mem (hf _ (by omega)) (hg _ (by omega))
  one_mem' := by
    intro k _
    rw [coeff_one]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' := by
    intro f g hf hg k hk
    rw [map_add (f := _)]
    exact O.add_mem (hf k hk) (hg k hk)
  zero_mem' := by
    intro k _
    rw [map_zero]
    exact O.zero_mem
  neg_mem' := by
    intro f hf k hk
    rw [map_neg]
    exact O.neg_mem (hf k hk)

private theorem C_mem {R : Type*} [CommRing R] {O : Subring R} (n : ℕ) {a : R} (ha : a ∈ O) :
    (C a : R⟦X⟧) ∈ lowIn O n := by
  intro k _
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact O.zero_mem

private theorem X_mem {R : Type*} [CommRing R] (O : Subring R) (n : ℕ) :
    (X : R⟦X⟧) ∈ lowIn O n := by
  intro k _
  rw [coeff_X]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

private theorem X_mul_mem {R : Type*} [CommRing R] {O : Subring R} {n : ℕ} {f : R⟦X⟧}
    (hf : f ∈ lowIn O n) : X * f ∈ lowIn O (n + 1) := by
  intro k hk
  cases k with
  | zero => rw [coeff_zero_X_mul]; exact O.zero_mem
  | succ k => rw [coeff_succ_X_mul]; exact hf k (by omega)

private theorem w_mem {R : Type*} [CommRing R] {O : Subring R} {a₁ a₂ a₃ a₄ a₆ : R}
    (h₁ : a₁ ∈ O) (h₂ : a₂ ∈ O) (h₃ : a₃ ∈ O) (h₄ : a₄ ∈ O) (h₆ : a₆ ∈ O) {w : R⟦X⟧}
    (hw : w = 1 + C a₁ * X * w + C a₂ * X ^ 2 * w + C a₃ * X ^ 3 * w ^ 2 + C a₄ * X ^ 4 * w ^ 2
      + C a₆ * X ^ 6 * w ^ 3) (n : ℕ) : w ∈ lowIn O n := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have e : w = 1 + X * (C a₁ * w + C a₂ * X * w + C a₃ * X ^ 2 * w ^ 2 + C a₄ * X ^ 3 * w ^ 2
      + C a₆ * X ^ 5 * w ^ 3) := by linear_combination hw
    have hX := X_mem O n
    rw [e]
    exact add_mem (one_mem _) (X_mul_mem (add_mem (add_mem (add_mem (add_mem
      (mul_mem (C_mem n h₁) ih)
      (mul_mem (mul_mem (C_mem n h₂) hX) ih))
      (mul_mem (mul_mem (C_mem n h₃) (pow_mem hX _)) (pow_mem ih _)))
      (mul_mem (mul_mem (C_mem n h₄) (pow_mem hX _)) (pow_mem ih _)))
      (mul_mem (mul_mem (C_mem n h₆) (pow_mem hX _)) (pow_mem ih _))))

private theorem dX_eq {R : Type*} [CommRing R] (f : R⟦X⟧) : dX f = derivative f := by
  ext n
  rw [coeff_derivative, dX, coeff_mk, mul_comm]

private theorem key {R : Type*} [CommRing R] {a₁ a₂ a₃ a₄ a₆ : R} {w : R⟦X⟧}
    (hw : w = 1 + C a₁ * X * w + C a₂ * X ^ 2 * w + C a₃ * X ^ 3 * w ^ 2 + C a₄ * X ^ 4 * w ^ 2
      + C a₆ * X ^ 6 * w ^ 3) :
    (1 - C a₁ * X - C a₂ * X ^ 2 - 2 * (C a₃ * X ^ 3 * w) - 2 * (C a₄ * X ^ 4 * w)
      - 3 * (C a₆ * X ^ 6 * w ^ 2)) * (-2 * w - X * dX w)
      = w * (C a₁ * X + C a₃ * X ^ 3 * w - 2) := by
  have h := congrArg (derivative (R := R)) hw
  simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X,
    Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul] at h
  rw [dX_eq]
  push_cast at h
  linear_combination (-X) * h

private noncomputable def ball (p : ℕ) [Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro x y hx hy
    change ‖x * y‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by
    change ‖(1 : ℂ_[p])‖ ≤ 1
    rw [norm_one]
  add_mem' := by
    intro x y hx hy
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by
    change ‖(0 : ℂ_[p])‖ ≤ 1
    rw [norm_zero]
    exact zero_le_one
  neg_mem' := by
    intro x hx
    change ‖-x‖ ≤ 1
    rw [norm_neg]
    exact hx

private theorem dX_flog {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p])
    (w : ℂ_[p]⟦X⟧) : dX (flog W w) = omegaW W w := by
  ext n
  have hn : ((n : ℂ_[p]) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [dX, coeff_mk, flog, coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
    Nat.cast_add_one, mul_div_cancel₀ _ hn]

end UpperTheory.Reformulated.B.Gwa1

open PowerSeries in
theorem UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds :
    UpperTheory.Reformulated.B.Gwa1.InvOmega := by
  intro p _ W w h₁ h₂ h₃ h₄ h₆ hw
  have hw' : w = 1 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * X ^ 3 * w ^ 2
      + C W.a₄ * X ^ 4 * w ^ 2 + C W.a₆ * X ^ 6 * w ^ 3 := hw
  refine ⟨1 - C W.a₁ * X - C W.a₂ * X ^ 2 - 2 * (C W.a₃ * X ^ 3 * w) - 2 * (C W.a₄ * X ^ 4 * w)
      - 3 * (C W.a₆ * X ^ 6 * w ^ 2), fun n => ?_, ?_⟩
  · have hX := X_mem (ball p) (n + 1)
    have ih := w_mem (O := ball p) h₁ h₂ h₃ h₄ h₆ hw' (n + 1)
    have c₁ := C_mem (O := ball p) (n + 1) h₁
    have c₂ := C_mem (O := ball p) (n + 1) h₂
    have c₃ := C_mem (O := ball p) (n + 1) h₃
    have c₄ := C_mem (O := ball p) (n + 1) h₄
    have c₆ := C_mem (O := ball p) (n + 1) h₆
    exact (sub_mem (sub_mem (sub_mem (sub_mem (sub_mem (one_mem _) (mul_mem c₁ hX))
      (mul_mem c₂ (pow_mem hX _)))
      (mul_mem (ofNat_mem _ 2) (mul_mem (mul_mem c₃ (pow_mem hX _)) ih)))
      (mul_mem (ofNat_mem _ 2) (mul_mem (mul_mem c₄ (pow_mem hX _)) ih)))
      (mul_mem (ofNat_mem _ 3) (mul_mem (mul_mem c₆ (pow_mem hX _)) (pow_mem ih _))) :
        _ ∈ lowIn (ball p) (n + 1)) n (Nat.lt_succ_self n)
  · have h0 : constantCoeff w = 1 := by
      have h := congrArg constantCoeff hw'
      simpa using h
    have hu : constantCoeff (w * (C W.a₁ * X + C W.a₃ * X ^ 3 * w - 2)) ≠ 0 := by
      simp [h0, map_ofNat]
    have ho : omegaW W w = (-2 * w - X * dX w) * (w * (C W.a₁ * X + C W.a₃ * X ^ 3 * w - 2))⁻¹ :=
      rfl
    rw [dX_flog, ho, ← mul_assoc, key hw']
    exact PowerSeries.mul_inv_cancel _ hu
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrIffSpan
section
private theorem UpperTheory.Reformulated.B.Qe4.subalgebra_eq_top {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ s ∈ S, ∀ v ∈ N, s v ∈ N) → N = ⊥ ∨ N = ⊤) : S = ⊤ := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [eq_top_iff]
    intro f _
    rw [Subsingleton.elim f 0]
    exact S.zero_mem
  haveI : IsSimpleModule S V := by
    refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun N => ?_ }
    rcases h (N.restrictScalars K) (fun s hs v hv => N.smul_mem (⟨s, hs⟩ : S) hv) with h1 | h1
    · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff K S V).1 h1)
    · exact Or.inr ((Submodule.restrictScalars_eq_top_iff K S V).1 h1)
  rw [eq_top_iff]
  intro f _
  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K
          (A := S) (V := V)).2 φ
        exact f.map_smul c v }
  classical
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density (R := S) F (Finset.univ.image b)
  have : f = (r : Module.End K V) :=
    b.ext fun i => hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]
  exact r.2

theorem UpperTheory.Reformulated.B.Qe4.irrIffSpan :
    ∀ {K G ι : Type} [inst : Field K] [IsAlgClosed K] [inst_2 : Group G]
    [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (ρ : G →* Matrix ι ι K),
    (∀ (N : Submodule K (ι → K)), (∀ (g : G), ∀ v ∈ N, ((ρ : G → Matrix ι ι K) g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) ↔
      Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) = ⊤ := by
  intro K G ι _ _ _ _ _ ρ
  constructor
  · intro h
    have hmul : ∀ x y : Matrix ι ι K, x ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) →
        y ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) →
        x * y ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) := by
      intro x y hx hy
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
      exact ⟨a * c, map_mul ρ a c⟩
    let A : Subalgebra K (Matrix ι ι K) :=
      (Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K))).toSubalgebra
        (Submodule.subset_span ⟨1, map_one ρ⟩) hmul
    let e : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K) := Matrix.toLinAlgEquiv'
    have hS : A.map (e : Matrix ι ι K →ₐ[K] Module.End K (ι → K)) = ⊤ := by
      refine UpperTheory.Reformulated.B.Qe4.subalgebra_eq_top _ fun N hN => h N fun g v hv => ?_
      exact hN (e (ρ g)) ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩ v hv
    rw [eq_top_iff]
    intro M _
    have hM : e M ∈ A.map (e : Matrix ι ι K →ₐ[K] Module.End K (ι → K)) := by
      rw [hS]; exact Algebra.mem_top
    obtain ⟨x, hx, hxe⟩ := hM
    have : x = M := e.injective hxe
    rw [← this]
    exact hx
  · intro h N hN
    have hall : ∀ M : Matrix ι ι K, ∀ v ∈ N, M.mulVec v ∈ N := by
      intro M v hv
      have hM : M ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) := by
        rw [h]; exact Submodule.mem_top
      induction hM using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hN g v hv
      | zero => rw [Matrix.zero_mulVec]; exact N.zero_mem
      | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact N.add_mem hx hy
      | smul c x _ hx => rw [Matrix.smul_mulVec]; exact N.smul_mem c hx
    by_cases hb : N = ⊥
    · exact Or.inl hb
    right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).1 hb
    rw [eq_top_iff]
    intro w _
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv0
    have := hall (LinearMap.toMatrix' (φ.smulRight w)) v hv
    rw [LinearMap.toMatrix'_mulVec] at this
    simpa [hφ] using this
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleInvariant
section
noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.IrreducibleInvariant.exists_ne :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] (ρ : Γ →* GL (Fin (2 : ℕ)) k),
      UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrr ρ →
        ∀ (g : GL (Fin (2 : ℕ)) k),
          ∃ (s : Γ),
            (↑(g * (ρ : Γ → GL (Fin (2 : ℕ)) k) s * g⁻¹) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) k) (0 : Fin (2 : ℕ))
                (1 : Fin (2 : ℕ)) ≠
              (0 : k) := by
  intro Γ k _ _ ρ hirr g
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, hmin⟩ := hirr
  let L : Submodule k (Fin 2 → k) :=
    LinearMap.ker ((LinearMap.proj (0 : Fin 2) : (Fin 2 → k) →ₗ[k] k) ∘ₗ
      Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) k))
  have hL : ∀ v, v ∈ L ↔ ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) 0 = 0 := fun v => Iff.rfl
  have hg : ∀ w : Fin 2 → k, (g : Matrix (Fin 2) (Fin 2) k).mulVec
      (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ L := by
    intro s v hv
    rw [hL] at hv ⊢
    have key : (g : Matrix (Fin 2) (Fin 2) k).mulVec
        (((ρ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec v) =
        ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec
          ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
        inv_mul_cancel_right]
    rw [key]
    generalize (g : Matrix (Fin 2) (Fin 2) k).mulVec v = w at hv
    have h01 := hcon s
    generalize ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = M at h01
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv, h01]
  rcases hmin L le_top hinv with h | h
  · have h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 1 1) ∈ L := by
      rw [hL, hg]
      simp
    rw [h, Submodule.mem_bot] at h1
    have h2 := hg (Pi.single 1 1)
    rw [h1, Matrix.mulVec_zero] at h2
    have h3 := congrFun h2 1
    simp at h3
  · have h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 0 1) ∈ L := by
      rw [h]
      exact Submodule.mem_top
    rw [hL, hg] at h1
    simp at h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleInvariantSubspaces
section
noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.irr_conj :
    ∀ {k : Type} [inst : Field k] {Γ : Type} [inst_1 : Group Γ] {n : ℕ} (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k),
      (∀ (x : Γ), (r' : Γ → GL (Fin n) k) x = g * (r : Γ → GL (Fin n) k) x * g⁻¹) →
        UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr r' → UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr r := by
  intro k _ Γ _ n r r' g h hirr
  obtain ⟨hne, -, hmin⟩ := hirr
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  have hgg : ∀ v : Fin n → k, (↑(g⁻¹) : Matrix (Fin n) (Fin n) k).mulVec
      ((↑g : Matrix (Fin n) (Fin n) k).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv r'
      (W.comap (Matrix.mulVecLin (↑(g⁻¹) : Matrix (Fin n) (Fin n) k))) := by
    intro x v hv
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [h x, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgg]
    exact hW x _ hv
  rcases hmin _ le_top hinv with h0 | h1
  · left
    rw [Submodule.eq_bot_iff] at h0 ⊢
    intro v hv
    have h2 : (↑g : Matrix (Fin n) (Fin n) k).mulVec v = 0 := by
      apply h0
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hgg]
      exact hv
    rw [← hgg v, h2, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at h1 ⊢
    intro v
    have h2 := h1 ((↑g : Matrix (Fin n) (Fin n) k).mulVec v)
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, hgg] at h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleOfSpanningMatrices
section
theorem UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top :
    ∀ {K G ι : Type} [inst : Field K] [inst_1 : Fintype ι]
    [DecidableEq ι] (f : G → Matrix ι ι K),
    Submodule.span K (Set.range f) = ⊤ →
      ∀ (N : Submodule K (ι → K)), (∀ (g : G), ∀ v ∈ N, (f g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro K G ι _ _ _ f hf N hN
  have key : ∀ A : Matrix ι ι K, ∀ v ∈ N, A.mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range f) := by rw [hf]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero => rw [Matrix.zero_mulVec]; exact N.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact N.add_mem hx hy
    | smul a x _ hx => rw [Matrix.smul_mulVec]; exact N.smul_mem a hx
  by_cases h : N = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h1 := key (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0) v hv
    have h2 : (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [h2] at h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralIffNormLeOne
section
open Polynomial

theorem UpperTheory.padicAlgCl_isIntegral_iff_norm_le_one :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ (1 : ℝ) := by
  intro l _ x
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hx
  have key : ‖x‖ ≤ (1 : ℝ) ↔ ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 :=
    spectralValue_le_one_iff hm
  rw [key]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact ((minpoly ℤ_[l] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]
end

