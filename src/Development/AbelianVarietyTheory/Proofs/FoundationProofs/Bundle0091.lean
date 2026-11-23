module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetSurvivalProductOfTwoGroups
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_mem_sup_twKer_prod : ∀ (G₁ G₂ V : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V), IsSmooth ρ → ∀ (U₁ : Subgroup G₁) (U₂ : Subgroup G₂) (J₁ : Set G₁) (J₂ : Set G₂) (θ₁ : G₁ → ℂ) (θ₂ : G₂ → ℂ), (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₁ W), IsSmooth σ → ∀ w ∈ twKer σ U₁ 1, IsEig σ J₁ θ₁ w → w = 0) → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₂ W), IsSmooth σ → ∀ w ∈ twKer σ U₂ 1, IsEig σ J₂ θ₂ w → w = 0) → ∀ v ∈ twKer (ρ.comp (MonoidHom.inl G₁ G₂)) U₁ 1 ⊔ twKer (ρ.comp (MonoidHom.inr G₁ G₂)) U₂ 1, IsEig (ρ.comp (MonoidHom.inl G₁ G₂)) J₁ θ₁ v → IsEig (ρ.comp (MonoidHom.inr G₁ G₂)) J₂ θ₂ v → v = 0 := by
  intro G₁ G₂ V _ _ _ _ _ _ _ _ ρ hρ U₁ U₂ J₁ J₂ θ₁ θ₂ h₁ h₂ v hv e₁ e₂
  have s₁ : IsSmooth (ρ.comp (MonoidHom.inl G₁ G₂)) := fun w =>
    (hρ w).preimage (f := fun g : G₁ => ((g, 1) : G₁ × G₂)) (by fun_prop)
  have s₂ : IsSmooth (ρ.comp (MonoidHom.inr G₁ G₂)) := fun w =>
    (hρ w).preimage (f := fun g : G₂ => ((1, g) : G₁ × G₂)) (by fun_prop)
  set ρ₁ : Representation ℂ G₁ V := ρ.comp (MonoidHom.inl G₁ G₂) with hρ₁
  set ρ₂ : Representation ℂ G₂ V := ρ.comp (MonoidHom.inr G₁ G₂) with hρ₂
  have comm : ∀ (a : G₁) (b : G₂) (w : V), ρ₁ a (ρ₂ b w) = ρ₂ b (ρ₁ a w) := by
    intro a b w
    change ρ (a, 1) (ρ (1, b) w) = ρ (1, b) (ρ (a, 1) w)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  set A : Submodule ℂ V := twKer ρ₂ U₂ 1 with hA
  have hst : ∀ g : G₁, A ≤ A.comap (ρ₁ g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, x, rfl⟩
    refine Submodule.subset_span ⟨n, ρ₁ g x, ?_⟩
    rw [map_sub, map_smul, comm]
  let σ : Representation ℂ G₁ (V ⧸ A) := Representation.quotient ρ₁ A hst
  have hσ : ∀ g x, σ g (A.mkQ x) = A.mkQ (ρ₁ g x) := fun g x => rfl
  have sσ : IsSmooth σ := by
    intro w
    obtain ⟨x, rfl⟩ := A.mkQ_surjective w
    let S : Subgroup G₁ :=
      { carrier := {g | σ g (A.mkQ x) = A.mkQ x}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have : (S : Set G₁) ∈ nhds (1 : G₁) := by
      refine Filter.mem_of_superset ((s₁ x).mem_nhds (by simp)) ?_
      intro g hg
      change σ g (A.mkQ x) = A.mkQ x
      rw [hσ, show ρ₁ g x = x from hg]
    exact S.isOpen_of_mem_nhds this
  have hmap : twKer ρ₁ U₁ 1 ≤ (twKer σ U₁ 1).comap A.mkQ := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, x, rfl⟩
    refine Submodule.subset_span ⟨n, A.mkQ x, ?_⟩
    rw [map_sub, map_smul, hσ]
  have hA0 : A ≤ (twKer σ U₁ 1).comap A.mkQ := by
    intro x hx
    have : A.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero A).2 hx
    rw [Submodule.mem_comap, this]
    exact zero_mem _
  have hv' : A.mkQ v ∈ twKer σ U₁ 1 := sup_le hmap hA0 hv
  have hz : A.mkQ v = 0 := h₁ _ σ sσ _ hv' (by
    intro h hh
    rw [hσ, e₁ h hh, map_smul])
  exact h₂ V ρ₂ s₂ v ((Submodule.Quotient.mk_eq_zero A).1 hz) e₂

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoDimRepQuadraticRelation
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.CayleyHamiltonId

theorem exists_decomp {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (P : ι → ι → Module.End E U)
    (hP : ∀ i j k l, P i j * P k l = if j = k then P i l else 0)
    (h1 : ∑ i, P i i = 1) :
    ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (ι → E)) (s : Fin m → (ι → E) →ₗ[E] U),
      (∀ i (M : Matrix ι ι E), π i ∘ₗ (∑ a, ∑ b, M a b • P a b) = Matrix.toLin' M ∘ₗ π i) ∧
      (∀ i (M : Matrix ι ι E), (∑ a, ∑ b, M a b • P a b) ∘ₗ s i = s i ∘ₗ Matrix.toLin' M) ∧
      (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧
      ∑ i, s i ∘ₗ π i = LinearMap.id := by
  classical
  have hPa : ∀ i j k l u, P i j (P k l u) = if j = k then P i l u else 0 := by
    intro i j k l u
    have := LinearMap.congr_fun (hP i j k l) u
    rw [Module.End.mul_apply] at this
    rw [this]; split_ifs <;> rfl
  set W := LinearMap.range (P i₀ i₀)
  have hW : ∀ k u, P i₀ k u ∈ W := fun k u => ⟨P i₀ k u, by rw [hPa, if_pos rfl]⟩
  have hfix : ∀ w ∈ W, P i₀ i₀ w = w := by
    rintro _ ⟨u, rfl⟩; rw [hPa, if_pos rfl]
  let b := Module.finBasis E W
  let π : Fin (Module.finrank E W) → U →ₗ[E] (ι → E) :=
    fun i => LinearMap.pi fun k => (b.coord i).comp (LinearMap.codRestrict W (P i₀ k) (hW k))
  let s : Fin (Module.finrank E W) → (ι → E) →ₗ[E] U :=
    fun i => ∑ k, (LinearMap.proj k : (ι → E) →ₗ[E] E).smulRight (P k i₀ (b i))
  have hπ : ∀ i u k, π i u k = b.repr ⟨P i₀ k u, hW k u⟩ i := fun i u k => rfl
  have hs : ∀ i v, s i v = ∑ k, v k • P k i₀ (b i) := by
    intro i v; simp [s, LinearMap.sum_apply]
  have hrec : ∀ k u, ∑ i, b.repr ⟨P i₀ k u, hW k u⟩ i • (b i : U) = P i₀ k u := by
    intro k u
    have h' := congrArg Subtype.val (b.sum_repr ⟨P i₀ k u, hW k u⟩)
    rw [Submodule.coe_sum] at h'
    simpa only [Submodule.coe_smul] using h'
  refine ⟨Module.finrank E W, π, s, ?_, ?_, ?_, ?_⟩
  · intro i M
    ext u k
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hπ]
    have e : (⟨P i₀ k ((∑ a, ∑ b', M a b' • P a b') u), hW k _⟩ : W)
        = ∑ b', M k b' • (⟨P i₀ b' u, hW b' u⟩ : W) := by
      apply Subtype.ext
      set_option synthInstance.maxHeartbeats 100000 in
        simp [LinearMap.sum_apply, map_sum, map_smul, hPa]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, Finsupp.finsetSum_apply]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hπ]
  · intro i M
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [LinearMap.sum_apply, map_sum, map_smul, hPa, Matrix.mulVec, dotProduct, Finset.sum_smul,
      mul_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  · intro i j
    refine LinearMap.ext fun v => funext fun k => ?_
    simp only [LinearMap.comp_apply, hπ, hs]
    have e : (⟨P i₀ k (∑ l, v l • P l i₀ (b j)), hW k _⟩ : W) = v k • b j := by
      apply Subtype.ext
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_smul, hPa, hfix _ (b j).2]
    rw [e]
    split_ifs with h
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h]
  · ext u
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, hs, hπ, LinearMap.id_apply]
    rw [Finset.sum_comm]
    have hk : ∀ k, ∑ x, b.repr ⟨P i₀ k u, hW k u⟩ x • P k i₀ (b x) = P k k u := by
      intro k
      have := congrArg (P k i₀) (hrec k u)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simp only [map_smul] at this
      rw [this, hPa, if_pos rfl]
    simp only [hk]
    rw [← LinearMap.sum_apply, h1, Module.End.one_apply]

theorem isotypic_of_quadratic_relation : ∀ {E : Type} [Field E] [IsAlgClosed E], (2 : E) ≠ 0 → ∀ {G : Type} [Group G] (ρ : G →* GL (Fin 2) E), (∀ W : Submodule E (Fin 2 → E), (∀ g w, w ∈ W → (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] (σ : G →* Module.End E U), (∀ g, σ g * σ g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σ g + Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0) → ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (Fin 2 → E)) (s : Fin m → (Fin 2 → E) →ₗ[E] U), (∀ i g, π i ∘ₗ σ g = Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E) ∘ₗ π i) ∧ (∀ i g, σ g ∘ₗ s i = s i ∘ₗ Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E)) ∧ (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧ ∑ i, s i ∘ₗ π i = LinearMap.id := by
  intro E _ _ h2 G _ ρ hirr U _ _ _ σ hrel
  classical
  let R : G →* Matrix (Fin 2) (Fin 2) E := (Units.coeHom _).comp ρ
  have hRg : ∀ g, R g = (ρ g : Matrix (Fin 2) (Fin 2) E) := fun g => rfl
  have hspan := GlobalTheory.BurnsideMonoid.span_matrix_eq_top_of_isAlgClosed R (fun W hW => hirr W hW)
  let Φ : MonoidAlgebra E G →ₐ[E] Module.End E U := MonoidAlgebra.lift E (Module.End E U) G σ
  let Ψ : MonoidAlgebra E G →ₐ[E] Matrix (Fin 2) (Fin 2) E :=
    MonoidAlgebra.lift E (Matrix (Fin 2) (Fin 2) E) G R
  have hΦ : ∀ g c, Φ (MonoidAlgebra.single g c) = c • σ g := fun g c => MonoidAlgebra.lift_single _ _ _
  have hΨ : ∀ g c, Ψ (MonoidAlgebra.single g c) = c • R g := fun g c => MonoidAlgebra.lift_single _ _ _
  have hsurj : ∀ M, ∃ y, Ψ y = M := by
    intro M
    have hle : Submodule.span E (Set.range R) ≤ LinearMap.range Ψ.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simp [hΨ]⟩
    obtain ⟨y, hy⟩ := hle (hspan ▸ Submodule.mem_top : M ∈ Submodule.span E (Set.range R))
    exact ⟨y, hy⟩

  have hinv : ∀ g, (R g).det • σ g⁻¹ = (R g).trace • 1 - σ g := by
    intro g
    have h := congrArg (· * σ g⁻¹) (hrel g)
    have hgg : σ g * σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, hgg, mul_one, one_mul, zero_mul] at h
    rw [hRg]
    linear_combination (norm := module) h
  have hpair : ∀ g h, σ g * σ h + σ h * σ g - (R h).trace • σ g - (R g).trace • σ h
      + ((R g).trace * (R h).trace - (R g * R h).trace) • (1 : Module.End E U) = 0 := by
    intro g h
    have e1 := hinv (g * h)
    have e2 : (R (g*h)).det • σ (g*h)⁻¹ = ((R h).det • σ h⁻¹) * ((R g).det • σ g⁻¹) := by
      rw [_root_.mul_inv_rev, map_mul σ, map_mul R, det_mul, smul_mul_smul_comm, mul_comm (R g).det]
    rw [e2, hinv g, hinv h, map_mul σ, map_mul R] at e1
    simp only [mul_sub, sub_mul, smul_mul_smul_comm, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm] at e1
    linear_combination (norm := module) e1
  have hB : ∀ x y, Φ x * Φ y + Φ y * Φ x - (Ψ y).trace • Φ x - (Ψ x).trace • Φ y
      + ((Ψ x).trace * (Ψ y).trace - (Ψ x * Ψ y).trace) • (1 : Module.End E U) = 0 := by
    intro x y
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x₁ x₂ h₁ h₂ =>
      simp only [map_add (f := _), add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢
      linear_combination (norm := module) h₁ + h₂
    | single g c =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add y₁ y₂ h₁ h₂ =>
        simp only [map_add (f := _), add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢
        linear_combination (norm := module) h₁ + h₂
      | single h d =>
        simp only [hΦ, hΨ, trace_smul, smul_mul_smul_comm, smul_eq_mul]
        linear_combination (norm := module) (c * d) • hpair g h

  have hanti : ∀ x y, Ψ x = 0 → Φ x * Φ y + Φ y * Φ x = (Ψ y).trace • Φ x := by
    intro x y hx
    have := hB x y
    simp only [hx, trace_zero, zero_mul, mul_zero, sub_self, zero_smul, add_zero, sub_zero] at this
    linear_combination (norm := module) this
  have h2c : ∀ X : Module.End E U, X + X = 0 → X = 0 := by
    intro X hX
    rw [← two_smul E X] at hX
    exact (smul_eq_zero.mp hX).resolve_left h2
  obtain ⟨y₁, hy₁⟩ := hsurj (Matrix.single 0 1 1)
  obtain ⟨y₂, hy₂⟩ := hsurj (Matrix.single 1 0 1)
  have hc : Ψ (y₁ * y₂ - y₂ * y₁) = !![1, 0; 0, -1] := by
    rw [map_sub, map_mul, map_mul, hy₁, hy₂]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  have hc2 : Ψ ((y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1) = 0 := by
    rw [map_sub, map_mul, hc, map_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have ht1 : (Ψ y₁).trace = 0 := by rw [hy₁]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]
  have ht2 : (Ψ y₂).trace = 0 := by rw [hy₂]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]
  have htc : (Ψ (y₁ * y₂ - y₂ * y₁)).trace = 0 := by rw [hc]; simp [Matrix.trace, Fin.sum_univ_two]
  have hJ : ∀ x, Ψ x = 0 → Φ x = 0 := by
    intro x hx
    set N := Φ x
    set a := Φ y₁
    set b := Φ y₂
    have e1 : N * a = -(a * N) := eq_neg_of_add_eq_zero_left (by rw [hanti x y₁ hx, ht1, zero_smul])
    have e2 : N * b = -(b * N) := eq_neg_of_add_eq_zero_left (by rw [hanti x y₂ hx, ht2, zero_smul])
    have k1 : N * (a * b) = a * b * N := by
      rw [← mul_assoc, e1, neg_mul, mul_assoc, e2, mul_neg, neg_neg, mul_assoc]
    have k2 : N * (b * a) = b * a * N := by
      rw [← mul_assoc, e2, neg_mul, mul_assoc, e1, mul_neg, neg_neg, mul_assoc]
    have hC : Φ (y₁ * y₂ - y₂ * y₁) = a * b - b * a := by rw [map_sub, map_mul, map_mul]
    have hNC : N * (a * b - b * a) = 0 := by
      have h3 := hanti x (y₁ * y₂ - y₂ * y₁) hx
      rw [htc, zero_smul, hC] at h3
      apply h2c
      have : (a * b - b * a) * N = N * (a * b - b * a) := by rw [mul_sub, sub_mul, k1, k2]
      rw [this] at h3; exact h3
    set x' := (y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1
    have hN' : Φ x' * Φ x' = 0 := by
      apply h2c
      rw [hanti x' x' hc2, hc2, trace_zero, zero_smul]
    have hNN' : N * Φ x' = -N := by
      have hx' : Φ x' = (a * b - b * a) * (a * b - b * a) - 1 := by
        simp only [x']; rw [map_sub, map_mul, hC, map_one]
      rw [hx', mul_sub, mul_one, ← mul_assoc, hNC, zero_mul, zero_sub]
    have h5 : N * Φ x' * Φ x' = 0 := by rw [mul_assoc, hN', mul_zero]
    rw [hNN', neg_mul, hNN', neg_neg] at h5
    exact h5

  have hΦeq : ∀ x y, Ψ x = Ψ y → Φ x = Φ y := by
    intro x y h
    have := hJ (x - y) (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  choose yP hyP using fun i j : Fin 2 => hsurj (Matrix.single i j 1)
  let P : Fin 2 → Fin 2 → Module.End E U := fun i j => Φ (yP i j)
  have hP : ∀ i j k l, P i j * P k l = if j = k then P i l else 0 := by
    intro i j k l
    simp only [P, ← map_mul]
    split_ifs with h
    · subst h
      apply hΦeq
      rw [map_mul, hyP, hyP, hyP, Matrix.single_mul_single_same, mul_one]
    · rw [← map_zero Φ]
      apply hΦeq
      rw [map_mul, hyP, hyP, map_zero]
      simp [h]
  have hsum : ∑ i, P i i = 1 := by
    simp only [P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_one Φ]
    apply hΦeq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [hyP]
    rw [Fin.sum_univ_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, Matrix.one_apply]
  have hσ : ∀ g, σ g = ∑ a, ∑ b, (R g) a b • P a b := by
    intro g
    have e : σ g = Φ (MonoidAlgebra.single g 1) := by rw [hΦ, one_smul]
    rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, ← map_smul, ← map_sum]
    apply hΦeq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hΨ, hyP, one_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single (R g)
  obtain ⟨m, π, s, k1, k2, k3, k4⟩ := exists_decomp (0 : Fin 2) P hP hsum
  refine ⟨m, π, s, fun i g => ?_, fun i g => ?_, k3, k4⟩
  · rw [hσ g]; exact k1 i (R g)
  · rw [hσ g]; exact k2 i (R g)

end GlobalTheory.CayleyHamiltonId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLaws
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.SlPLaws
open MvPolynomial

variable {R : Type} [CommRing R]

theorem slP_X (m : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    slP (R := R) m (X i) = (m i 0 : R) • X 0 + (m i 1 : R) • X 1 := by
  simp [slP]

theorem polySlash_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP (m * m') p = slP m' (slP m p) := by
  have h : (slP (R := R) (m * m')) = (slP m').comp (slP m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, slP_X, map_add (f := _), map_smul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    simp only [smul_add, add_smul, smul_smul, mul_comm]
    abel
  rw [h]; rfl

theorem polySlash_one' (p : MvPolynomial (Fin 2) R) : slP 1 p = p := by
  have h : (slP (R := R) 1) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [h]; rfl

theorem polySlash_isHomogeneous (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R)
    (hp : p.IsHomogeneous w) : (slP m p).IsHomogeneous w := by
  have := IsHomogeneous.aeval (τ := Fin 2) (S := R) (n := 1) hp (fun i => (m i 0 : R) • X 0 + (m i 1 : R) • X 1) (fun i => by
    apply IsHomogeneous.add
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 0).C_mul _
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 1).C_mul _)
  rw [one_mul] at this
  simpa [slP] using this

theorem eval_slP (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    eval u (slP m p) = eval (m.map (Int.castRingHom R) *ᵥ u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, eval_X]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem map_slP {S : Type} [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, map_X, map_add (f := _)]
    simp [MvPolynomial.smul_eq_C_mul]

theorem polySlash_congr (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R)
    (h : ∀ i j, (m i j : R) = (m' i j : R)) : slP m p = slP m' p := by
  simp only [slP, h]

theorem polySlash_neg_one (w : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p.IsHomogeneous w) :
    slP (-1) p = (-1 : R) ^ w • p := by
  have e : (slP (R := R) (-1)) = aeval fun i => (-1 : R) • X i := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [e]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hw := hp (mem_support_iff.mp hv)
  rw [aeval_monomial]
  simp only [smul_pow, Finsupp.prod_pow]
  have hw' : v 0 + v 1 = w := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]; simp
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, ← hw']
  simp only [smul_eq_C_mul, algebraMap_eq, pow_add, map_mul, map_pow, map_neg, map_one]
  ring

end GlobalTheory.KZ.SlPLaws

namespace GlobalTheory.KZ

theorem polySlash_laws : ∀ (R : Type) [CommRing R], (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), slP (m * m') p = slP m' (slP m p)) ∧ (∀ p : MvPolynomial (Fin 2) R, slP 1 p = p) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → (slP m p).IsHomogeneous w) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R), MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p)) ∧ (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), (∀ i j, (m i j : R) = (m' i j : R)) → slP m p = slP m' p) ∧ (∀ (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → slP (-1) p = (-1 : R) ^ w • p) := by
  intro R _
  exact ⟨SlPLaws.polySlash_mul, SlPLaws.polySlash_one', SlPLaws.polySlash_isHomogeneous, SlPLaws.eval_slP, fun S _ f => SlPLaws.map_slP f,
    fun m m' p h => SlPLaws.polySlash_congr m m' p h, fun w p hp => SlPLaws.polySlash_neg_one w p hp⟩

end GlobalTheory.KZ
end

