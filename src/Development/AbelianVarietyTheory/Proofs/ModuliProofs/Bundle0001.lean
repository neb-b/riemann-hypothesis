module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AnalyticAtEntry
section
namespace GlobalTheory.AnalyticMatrixEntries

universe u_1 u_2

theorem analyticAt_entry {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {ι : Type*} (b : Module.Basis ι ℂ E) {A : X → E →L[ℂ] E} {a : X}
    (hA : AnalyticAt ℂ A a) (i j : ι) :
    AnalyticAt ℂ (fun z : X ↦ b.repr (A z (b j)) i) a := by
  let L : (E →L[ℂ] E) →L[ℂ] ℂ :=
    (LinearMap.toContinuousLinearMap (b.coord i)).comp (ContinuousLinearMap.apply ℂ E (b j))
  have h := (L.analyticAt (A a)).comp hA
  convert h using 1
  funext z
  simp [L, Module.Basis.coord_apply]

theorem analyticAt_det {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : X → E →L[ℂ] E} {a : X} (hA : AnalyticAt ℂ A a) :
    AnalyticAt ℂ (fun z : X ↦ LinearMap.det (A z : E →ₗ[ℂ] E)) a := by
  let b := Module.finBasis ℂ E
  have hfun : (fun z : X => LinearMap.det (A z : E →ₗ[ℂ] E)) =
      fun z => ∑ σ : Equiv.Perm (Fin (Module.finrank ℂ E)),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, b.repr (A z (b i)) (σ i) := by
    funext z
    rw [← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [LinearMap.toMatrix_apply]
  rw [hfun]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ?_)
  exact analyticAt_entry b hA (σ i) i

end GlobalTheory.AnalyticMatrixEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetBicharacterPowFour
section
open scoped TensorProduct

namespace GlobalTheory

private theorem sum_pairing_eq_card_ite_one {Γ K : Type} [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] [Field K]
    (X : Γ → Γ → K) (h0 : ∀ a b, X a b ≠ 0) (hl : ∀ a a' b, X (a * a') b = X a b * X a' b)
    (hr : ∀ a b b', X a (b * b') = X a b * X a b')
    (hnd : ∀ a, (∀ b, X a b = 1) → a = 1) (c : Γ) :
    (∑ b, X c b) = if c = 1 then (Fintype.card Γ : K) else 0 := by
  split_ifs with hc
  · subst hc
    have h1 : ∀ b, X 1 b = 1 := by
      intro b
      have h := hl 1 1 b
      rw [one_mul] at h
      have hb := h0 1 b
      have : X 1 b * (X 1 b - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hb
      · exact sub_eq_zero.mp h'
    simp [h1]
  · obtain ⟨b₀, hb₀⟩ : ∃ b₀, X c b₀ ≠ 1 := by
      by_contra hne
      simp only [not_exists, ne_eq, not_not] at hne
      exact hc (hnd c hne)
    have hshift : (∑ b, X c b) = X c b₀ * ∑ b, X c b := by
      rw [Finset.mul_sum]
      simp_rw [← hr]
      exact (Equiv.sum_comp (Equiv.mulLeft b₀) (fun b => X c b)).symm
    have : (X c b₀ - 1) * ∑ b, X c b = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hb₀
    · exact h'

theorem det_bicharacter_pow_four :
    ∀ (Γ K : Type) [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] [Field K] (X : Γ → Γ → K), (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → (Matrix.of X).det ^ 4 = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by
  intro Γ K _ _ _ _ X h0 hl hr hnd
  set M : Matrix Γ Γ K := Matrix.of X with hM
  have hMP : M * Matrix.transpose (M.submatrix (Equiv.inv Γ) id) = (Fintype.card Γ : K) • (1 : Matrix Γ Γ K) := by
    ext a a'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, hM,
      Matrix.of_apply, Equiv.inv_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp_rw [← hl]
    rw [sum_pairing_eq_card_ite_one X h0 hl hr hnd]
    by_cases h : a = a'
    · subst h; simp
    · have : a * a'⁻¹ ≠ 1 := fun e => h (mul_inv_eq_one.mp e)
      simp [h, this]
  have hdet := congrArg Matrix.det hMP
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_permute, Matrix.det_smul, Matrix.det_one,
    mul_one] at hdet
  have hs : ((Equiv.Perm.sign (Equiv.inv Γ) : ℤ) : K) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.inv Γ)) with e | e <;> simp [e]
  calc M.det ^ 4 = (M.det * (((Equiv.Perm.sign (Equiv.inv Γ) : ℤ) : K) * M.det)) ^ 2 := by
        rw [mul_pow, mul_pow, hs]; ring
    _ = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by rw [hdet, ← pow_mul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetUpdateRowAlternatingMulVecMem
section
open scoped TensorProduct

namespace GlobalTheory

theorem det_updateRow_single_mul_sub_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (i j : Fin g) :
    x j * (m.updateRow p (Pi.single i 1)).det - x i * (m.updateRow p (Pi.single j 1)).det ∈ I := by
  set m' := m.updateRow p (Pi.single i 1) with hm'
  have h1 : m'.adjugate.mulVec (m'.mulVec x) = m'.det • x := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : ∑ q, m'.adjugate j q * m'.mulVec x q = m'.det * x j := by
    have := congrFun h1 j
    simpa [Matrix.mulVec, dotProduct] using this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at h2
  have h3 : m'.adjugate j p = (m.updateRow p (Pi.single j 1)).det := by
    rw [Matrix.adjugate_apply, hm', Matrix.updateRow_idem]
  have h4 : m'.mulVec x p = x i := by
    simp [hm', Matrix.mulVec]
  rw [h3, h4] at h2
  have h5 : ∑ q ∈ Finset.univ.erase p, m'.adjugate j q * m'.mulVec x q ∈ I := by
    refine I.sum_mem fun q hq => I.mul_mem_left _ ?_
    have hq' : q ≠ p := Finset.ne_of_mem_erase hq
    have : m'.mulVec x q = m.mulVec x q := by
      simp [hm', Matrix.mulVec, Matrix.updateRow_ne hq']
    rw [this]
    exact hm q hq'
  convert h5 using 1
  linear_combination -h2

theorem det_updateRow_alternating_mulVec_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (s : Matrix (Fin g) (Fin g) T)
    (hs : s.transpose = -s) (hd : ∀ i, s i i = 0) :
    (m.updateRow p (s.mulVec x)).det ∈ I := by
  have h1 : (m.updateRow p (s.mulVec x)).det
      = ∑ ij : Fin g × Fin g,
          s ij.1 ij.2 * (x ij.2 * (m.updateRow p (Pi.single ij.1 1)).det) := by
    have e : ∀ v : Fin g → T, (m.updateRow p v).det
        = ∑ i, v i * (m.updateRow p (Pi.single i 1)).det := by
      intro v
      have := Matrix.cramer_transpose_apply m v p
      rw [← this, Matrix.cramer_eq_adjugate_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.adjugate_transpose, Matrix.transpose_apply, Matrix.adjugate_apply, mul_comm]
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) Prod.swap_swap
  · rintro ⟨i, j⟩
    rw [← map_add (f := _), Ideal.Quotient.eq_zero_iff_mem]
    have hji : s j i = - s i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have := I.mul_mem_left (s i j) (det_updateRow_single_mul_sub_mem x I m p hm i j)
    convert this using 1
    simp only [Prod.fst_swap, Prod.snd_swap, hji]
    ring
  · rintro ⟨i, j⟩ h e
    apply h
    have : j = i := congrArg Prod.fst e
    subst this
    simp [hd]

theorem det_sub_det_mem_span_of_mulVec_eq :
    ∀ (T : Type) [CommRing T] (g : ℕ) (x : Fin g → T), (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) → ∀ c c' : Matrix (Fin g) (Fin g) T, c.mulVec x = c'.mulVec x → c.det - c'.det ∈ Ideal.span (Set.range (c.mulVec x)) := by
  intro T _ g x hx c c' hc
  set I := Ideal.span (Set.range (c.mulVec x)) with hI
  let M : Finset (Fin g) → Matrix (Fin g) (Fin g) T :=
    fun S => Matrix.of fun i => if i ∈ S then c' i else c i
  have hM : ∀ S q, (M S).mulVec x q = c.mulVec x q := by
    intro S q
    by_cases h : q ∈ S
    · rw [hc]; simp [M, Matrix.mulVec, h]
    · simp [M, Matrix.mulVec, h]
  have key : ∀ S : Finset (Fin g), c.det - (M S).det ∈ I := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : M ∅ = c := by ext i j; simp [M]
      simp [this]
    | insert p S hp ih =>
      obtain ⟨s, hs, hd, hr⟩ := hx (c p - c' p) (by
        have := congrFun hc p
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr this)
      have h1 := det_updateRow_alternating_mulVec_mem x I (M S) p
        (fun q _ => by rw [hM]; exact Ideal.subset_span ⟨q, rfl⟩) s hs hd
      rw [← hr] at h1
      have e1 : (M S).updateRow p (c' p) = M (insert p S) := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M]
        · simp [M, Matrix.updateRow_ne h, h]
      have e2 : (M S).updateRow p (c p) = M S := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M, hp]
        · simp [Matrix.updateRow_ne h]
      have e3 := Matrix.det_updateRow_add (M S) p (c p - c' p) (c' p)
      rw [sub_add_cancel, e1, e2] at e3
      have := I.add_mem ih h1
      convert this using 1
      linear_combination e3
  have := key Finset.univ
  have e : M Finset.univ = c' := by ext i j; simp [M]
  rwa [e] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_common_eigenvector_mem {K V ι : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : ι → V →ₗ[K] V)
    (hT : ∀ i j v, T i (T j v) = T j (T i v)) (W : Submodule K V) (hW : W ≠ ⊥)
    (hs : ∀ i, ∀ v ∈ W, T i v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ l : K, T i v = l • v := by
  obtain ⟨U, ⟨hUW, hU0, hUs⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min
      {U | U ≤ W ∧ U ≠ ⊥ ∧ ∀ i, ∀ v ∈ U, T i v ∈ U} ⟨W, le_rfl, hW, hs⟩
  obtain ⟨v, hvU, hv0⟩ := (Submodule.ne_bot_iff U).1 hU0
  refine ⟨v, hUW hvU, hv0, fun i => ?_⟩
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU0
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue ((T i).restrict (hUs i))
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  have hw1 : T i w = l • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  let U' : Submodule K V := U ⊓ LinearMap.ker (T i - l • LinearMap.id)
  have hmem : ∀ x, x ∈ U' ↔ x ∈ U ∧ T i x = l • x := by
    intro x
    simp [U', sub_eq_zero]
  have hU' : U' = U := by
    by_contra hne
    refine hmin U' ⟨le_trans inf_le_left hUW, ?_, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
    · exact (Submodule.ne_bot_iff _).2 ⟨w, (hmem _).2 ⟨w.2, hw1⟩, hw0⟩
    · intro j x hx
      obtain ⟨h1, h2⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨hUs j x h1, by rw [hT, h2, map_smul]⟩
  exact ⟨l, ((hmem v).1 (hU'.symm ▸ hvU)).2⟩

section
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]

theorem lTensor_comp_mulLeft_of_balanced {N : Type*} [AddCommGroup N] [Module O N]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (α : H →ₗ[O] N) (h : H) :
    LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) Θ = h • LinearMap.lTensor H α Θ := by
  have h1 : ∀ t : H ⊗[O] H, LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) t
      = LinearMap.lTensor H α (((1 : H) ⊗ₜ[O] h) * t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), mul_add, hx, hy]
  have h2 : ∀ t : H ⊗[O] H, h • LinearMap.lTensor H α t
      = LinearMap.lTensor H α ((h ⊗ₜ[O] (1 : H)) * t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), mul_add, smul_add, hx, hy]
  rw [h1, h2, hΘ]

noncomputable def contractRight (Θ : H ⊗[O] H) : Module.Dual O H →ₗ[O] H where
  toFun α := TensorProduct.rid O H (LinearMap.lTensor H α Θ)
  map_add' a b := by simp [LinearMap.lTensor_add]
  map_smul' c a := by simp [LinearMap.lTensor_smul]

theorem contractRight_apply (Θ : H ⊗[O] H) (α : Module.Dual O H) :
    contractRight Θ α = TensorProduct.rid O H (LinearMap.lTensor H α Θ) := rfl

theorem sum_contractRight_coord_tmul {ι : Type*} [Fintype ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) : ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] b j = Θ := by
  induction Θ using TensorProduct.induction_on with
  | zero => simp [contractRight_apply]
  | tmul x y =>
    simp only [contractRight_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, Module.Basis.coord_apply, b.sum_repr]
  | add x y hx hy =>
    simp only [contractRight_apply, map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib] at *
    rw [hx, hy]

theorem contractRight_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) :
    contractRight Θ (Algebra.trace O H) = Algebra.TensorProduct.lmul' O Θ := by
  have htr : Algebra.trace O H = ∑ j, (b.coord j) ∘ₗ LinearMap.mulLeft O (b j) := by
    ext y
    rw [Algebra.trace_eq_matrix_trace b]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]
  have hr : ∀ (h : H) (t : H ⊗[O] O),
      TensorProduct.rid O H (h • t) = h * TensorProduct.rid O H t := by
    intro h t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), mul_add, smul_add, hx, hy]
  conv_rhs => rw [← sum_contractRight_coord_tmul b Θ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [htr, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [contractRight_apply, lTensor_comp_mulLeft_of_balanced Θ hΘ, hr, ← contractRight_apply]
  simp [mul_comm]

theorem eq_zero_of_lTensor_eq_zero_of_balanced [Module.Free O H] [Module.Finite O H]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra O K]
    (hK : ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0)
    (α : H →ₗ[O] K) (hα : LinearMap.lTensor H α Θ = 0) : α = 0 := by
  classical
  by_contra hne
  let b := Module.Free.chooseBasis O H
  haveI : FiniteDimensional K (H →ₗ[O] K) := Module.Finite.equiv (b.constr K)
  have hsm : ∀ (l : K) (a : H →ₗ[O] K), LinearMap.lTensor H a Θ = 0 →
      LinearMap.lTensor H (l • a) Θ = 0 := by
    intro l a ha
    have : l • a = LinearMap.mulLeft O l ∘ₗ a := by ext; simp
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, ha, map_zero]
  let W : Submodule K (H →ₗ[O] K) :=
    { carrier := {a | LinearMap.lTensor H a Θ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        simp [LinearMap.lTensor_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := fun l a ha => hsm l a ha }
  let T : H → (H →ₗ[O] K) →ₗ[K] (H →ₗ[O] K) := fun h =>
    { toFun := fun a => a ∘ₗ LinearMap.mulLeft O h
      map_add' := fun a b => by ext; simp
      map_smul' := fun l a => by ext; simp }
  obtain ⟨v, hvW, hv0, hv⟩ := exists_common_eigenvector_mem T
    (fun i j a => by ext; simp [T, mul_left_comm]) W
    ((Submodule.ne_bot_iff _).2 ⟨α, hα, hne⟩)
    (fun h a ha => by
      change LinearMap.lTensor H (a ∘ₗ LinearMap.mulLeft O h) Θ = 0
      rw [lTensor_comp_mulLeft_of_balanced Θ hΘ, show LinearMap.lTensor H a Θ = 0 from ha,
        smul_zero])
  choose l hl using hv
  have hl' : ∀ h x, v (h * x) = l h * v x := fun h x => by
    simpa [T] using LinearMap.congr_fun (hl h) x
  have hv1 : v 1 ≠ 0 := by
    intro h0
    apply hv0
    ext x
    simpa [h0] using hl' x 1
  let ga : H →ₐ[O] K := AlgHom.ofLinearMap ((v 1)⁻¹ • v) (by simp [hv1]) (by
    intro x y
    have h1 := hl' x y
    have h2 := hl' x 1
    rw [mul_one] at h2
    simp only [LinearMap.smul_apply, smul_eq_mul, h1, h2]
    field_simp)
  apply hK ga
  have : ∀ t : H ⊗[O] H, Algebra.TensorProduct.map (AlgHom.id O H) ga t
      = LinearMap.lTensor H ((v 1)⁻¹ • v) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [ga]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [this]
  exact hsm _ _ hvW

end

theorem dvd_trace_of_balanced_tensor :
    ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Free O H] [Module.Finite O H] (Θ : H ⊗[O] H) (c : O), ((∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0) → ∀ h : H, c ∣ Algebra.trace O H h := by
  intro O H _ _ _ _ _ _ Θ c ⟨hΘ, hc, hK⟩ h
  classical
  let b := Module.Free.chooseBasis O H
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply O (IsLocalRing.ResidueField O) K,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero]
  have hdet : IsUnit (LinearMap.toMatrix b.dualBasis b (contractRight Θ)).det := by
    by_contra hnu
    have h0 := hm _ ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [RingHom.map_det] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have : b.constr O v = 0 := by
      apply eq_zero_of_lTensor_eq_zero_of_balanced Θ hΘ K (hK K hm)
      have hv' : ∀ i, ∑ j, b.repr (contractRight Θ (b.coord j)) i • v j = 0 := by
        intro i
        have := congrFun hv i
        simpa [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, Algebra.smul_def,
          Module.Basis.coe_dualBasis] using this
      have e : LinearMap.lTensor H (b.constr O v) Θ
          = ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] v j := by
        conv_lhs => rw [← sum_contractRight_coord_tmul b Θ]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum]
      rw [e]
      calc ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] v j
          = ∑ j, ∑ i, b i ⊗ₜ[O] (b.repr (contractRight Θ (b.coord j)) i • v j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            conv_lhs => rw [← b.sum_repr (contractRight Θ (b.coord j))]
            simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul]
        _ = 0 := by
            rw [Finset.sum_comm]
            simp only [← TensorProduct.tmul_sum, hv', TensorProduct.tmul_zero,
              Finset.sum_const_zero]
    exact (b.constr O).injective (by rw [this, map_zero])
  let e := LinearEquiv.ofIsUnitDet hdet
  have he : ∀ a, e a = contractRight Θ a := fun a => rfl
  have : Algebra.trace O H = c • e.symm 1 := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply, he, contractRight_trace b Θ hΘ, hc, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact Dvd.intro _ rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCommonAlgClosedExtension
section
namespace GlobalTheory.CommonAlgClosedExtension

open scoped TensorProduct

theorem exists_common_algClosed_extension (K₀ K K' : Type) [Field K₀] [Field K] [Field K']
    (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      RingHom.comp j i = RingHom.comp j' i' := by
  letI : Algebra K₀ K := i.toAlgebra
  letI : Algebra K₀ K' := i'.toAlgebra
  haveI : Nontrivial (K ⊗[K₀] K') := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  letI : Field ((K ⊗[K₀] K') ⧸ m) := Ideal.Quotient.field m
  let φ : (K ⊗[K₀] K') →+* AlgebraicClosure ((K ⊗[K₀] K') ⧸ m) :=
    (algebraMap ((K ⊗[K₀] K') ⧸ m) _).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure ((K ⊗[K₀] K') ⧸ m), inferInstance, inferInstance,
    φ.comp (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).toRingHom,
    φ.comp (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).toRingHom, ?_⟩
  ext x
  have h1 := (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).commutes x
  have h2 := (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).commutes x
  exact congrArg φ (h1.trans h2.symm)

end GlobalTheory.CommonAlgClosedExtension
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelProdPow
section
namespace GlobalTheory.RelationPowers

theorem rel_pow {G U : Type} [Monoid G] [Monoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (x : G) (c : U) (h : R x c) (k : ℕ) : R (x ^ k) (c ^ k) := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact hmul _ _ _ _ ih h

theorem rel_prod_pow {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ) (h : ∀ i, R (y i) (c i)) :
    R (List.prod (List.ofFn fun i : Fin n => y i ^ a i)) (∏ i : Fin n, c i ^ a i) := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact hmul _ _ _ _ (rel_pow R h1 hmul _ _ (h 0) _)
      (ih (fun i => y i.succ) (fun i => c i.succ) (fun i => a i.succ) (fun i => h i.succ))

end GlobalTheory.RelationPowers
end

