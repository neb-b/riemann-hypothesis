module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PartialSumRootNonneg
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CapQdet
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

theorem capelliQdet : CapelliQdetStatement := by
  refine ⟨fun 𝒰 _ _ n E x => ?_, fun n lam ω => ?_⟩
  · unfold Capelli.capelliC Capelli.cminor Formalism.REAL.qdet Formalism.REAL.qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [zsmul_eq_mul]
    congr 1
    congr 1
    refine congrArg List.ofFn (funext fun j => ?_)
    simp only [Capelli.capEntry, Formalism.REAL.Tm, id, add_comm]
  · unfold Formalism.QuantumDeterminants.capP thV
    refine Finset.prod_congr rfl fun t _ => ?_
    push_cast
    ring

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ExistsCommutingProjectionImage
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem pi_submodule_finiteDimensional {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => S) := by
  let g : (Fin n → S) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun c => S.subtype ∘ₗ LinearMap.proj c
  have : Submodule.pi Set.univ (fun _ : Fin n => S) = LinearMap.range g := by
    ext f
    constructor
    · intro hf
      exact ⟨fun c => ⟨f c, mem_pi_submodule_iff.1 hf c⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact mem_pi_submodule_iff.2 fun c => by simp [g]
  rw [this]
  infer_instance

section HidaSetting

variable {ε : Fin n → Bool} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
  {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] {EN : Fin n → Fin n → Module.End ℂ N}
  {φ : (Fin n → M) →ₗ[ℂ] N} {θ : ℝ}

theorem eigenspace_K_finite (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    {x : Fin n → M} (hx : x ∈ Xs (eeVd E) (genSub E V) θ) :
    ∃ S : Submodule ℂ (Fin n → M), S ≤ Xs (eeVd E) (genSub E V) θ ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (tensVd E) S ∧ x ∈ S := by
  classical
  have hxg := (mem_euler_eigenspace_iff.1 hx).1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => generated_submodule_stable_under_action V a b hv
  choose m hm using fun c => exists_layer_of_mem_genSub hE hVk (hxg c)
  set K := Finset.univ.sup m
  have hxK : ∀ c, x c ∈ layer ε E V K := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hfdL : FiniteDimensional ℂ (layer ε E V K) := finiteDimensional_layer hVfd K
  have hLk := layer_kStable hE hVk K
  have := pi_submodule_finiteDimensional (n := n) (layer ε E V K)
  refine ⟨Submodule.pi Set.univ (fun _ => layer ε E V K) ⊓ Xs (eeVd E) (genSub E V) θ, inf_le_right,
    Submodule.finiteDimensional_of_le inf_le_left, ?_, ⟨mem_pi_submodule_iff.2 hxK, hx⟩⟩
  intro a b hab f hf
  refine ⟨mem_pi_submodule_iff.2 fun c => ?_, euler_eigenspace_stable_under_action hE hGs a b hf.2⟩
  rw [tensor_dual_action_apply_component]
  refine sub_mem (hLk a b hab _ (mem_pi_submodule_iff.1 hf.1 c)) ?_
  split_ifs
  · exact mem_pi_submodule_iff.1 hf.1 a
  · exact zero_mem _

theorem image_eigenspace_K_finite (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f))
    {y : N} (hy : y ∈ (Xs (eeVd E) (genSub E V) θ).map φ) :
    ∃ T : Submodule ℂ N, T ≤ (Xs (eeVd E) (genSub E V) θ).map φ ∧ FiniteDimensional ℂ T ∧
      IsKStableSub ε EN T ∧ y ∈ T := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨S, hSX, hfd, hSk, hxS⟩ := eigenspace_K_finite hE hVfd hVk hx
  refine ⟨S.map φ, Submodule.map_mono hSX, inferInstance, ?_, Submodule.mem_map_of_mem hxS⟩
  intro a b hab v hv
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hv
  rw [← hφ a b f (mem_euler_eigenspace_iff.1 (hSX hf)).1]
  exact Submodule.mem_map_of_mem (hSk a b hab f hf)

theorem image_weights_in_root_cone (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f))
    {Λ : Fin n → ℝ}
    (hK2 : ∀ (μ : Fin n → ℝ) (f : Fin n → M), f ∈ Xs (eeVd E) (genSub E V) θ → f ≠ 0 →
      IsKHWVec ε (tensVd E) μ f → InRootCone (μ - Λ))
    {μ : Fin n → ℝ} {y : N} (hy : y ∈ (Xs (eeVd E) (genSub E V) θ).map φ) (hy0 : y ≠ 0)
    (hμ : IsKHWVec ε EN μ y) : InRootCone (μ - Λ) := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨S, hSX, hfd, hSk, hxS⟩ := eigenspace_K_finite hE hVfd hVk hx
  obtain ⟨x1, hx1S, hkhw, hfx⟩ := exists_highest_weight_lift_pi (isKUnitary_of_isInfUnitary hU) φ hfd hSk
    (fun a b _ z hz => hφ a b z (mem_euler_eigenspace_iff.1 (hSX hz)).1) hxS hμ
  have hx10 : x1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact hy0 hfx.symm
  exact hK2 μ x1 (hSX hx1S) hx10 hkhw

end HidaSetting

section Gen

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
  {N : Type*} [AddCommGroup N] [Module ℂ N] {EN : Fin n → Fin n → Module.End ℂ N}

theorem exists_commuting_projection_image (V : Submodule ℂ M)
    (hGen : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) →
      f ∈ genSub (tensVd E) (Submodule.pi Set.univ fun _ => V))
    (P : Module.End ℂ (Fin n → M)) (hPg : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → ∀ c, P f c ∈ genSub E V)
    (hPc : ∀ a b, Commute P (tensVd E a b)) (φ : (Fin n → M) →ₗ[ℂ] N)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f))
    {x : Fin n → M} (hx : ∀ c, x c ∈ genSub E V) (hPx : φ (P x) ≠ 0) :
    ∃ u : Fin n → M, (∀ c, u c ∈ V) ∧ φ (P u) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => generated_submodule_stable_under_action V a b hv
  set T : Submodule ℂ (Fin n → M) :=
    Submodule.pi Set.univ (fun _ => genSub E V) ⊓ LinearMap.ker (φ ∘ₗ P) with hT
  have hle : genSub (tensVd E) (Submodule.pi Set.univ fun _ => V) ≤ T := by
    unfold genSub
    refine sInf_le ⟨fun u hu => ⟨mem_pi_submodule_iff.2 fun c => le_generatedSubmodule_dual V (mem_pi_submodule_iff.1 hu c), ?_⟩,
      fun a b v hv => ⟨mem_pi_submodule_iff.2 (dualTensorAction_mem hGs a b (mem_pi_submodule_iff.1 hv.1)), ?_⟩⟩
    · exact LinearMap.mem_ker.2 (hcon u (mem_pi_submodule_iff.1 hu))
    · have hv2 : φ (P v) = 0 := LinearMap.mem_ker.1 hv.2
      refine LinearMap.mem_ker.2 ?_
      rw [LinearMap.comp_apply]
      have hc := (hPc a b).eq
      have : P (tensVd E a b v) = tensVd E a b (P v) := by
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
      rw [this, hφ a b _ (hPg v (mem_pi_submodule_iff.1 hv.1)), hv2, map_zero]
  have hxT := hle (hGen x hx)
  exact hPx (LinearMap.mem_ker.1 hxT.2)

end Gen

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.HcVOfCentralChar
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem gapCentral (n : ℕ) : GapCentralStatement n := by
  intro ε lam h ⟨_, hg, hN⟩
  unfold hNeed at hN
  have hA := (le_max_left _ _).trans_lt hN
  have hB := (le_max_right _ _).trans_lt hN
  have hB1 := (le_max_left _ _).trans_lt hB
  have hB2 := (le_max_right _ _).trans_lt hB
  have hA1 : 1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤
      max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) := le_max_right _ _
  have hM : 2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) ≤
      max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) := le_max_left _ _
  have hs := Real.sqrt_nonneg (2 * (min (pOf ε) (qOf ε) : ℝ))
  have hn : (0 : ℝ) ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) := by positivity
  have hP := mul_nonneg hs (by linarith : (0 : ℝ) ≤
      4 * max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) + 1 -
        (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ))
  exact ⟨hg, by linarith, by linarith, by nlinarith⟩

theorem hcV_of_centralChar (n : ℕ) (hCC : CentralCharStatement n) : HcVStatement n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hc hVK hint hanti hgap hp hq ω y hy
  have hle : V ≤ genSub E V := le_sInf fun T hT => hT.1
  exact hCC ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq ω y (hle hy)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ProdShiftEqAevalProd
section
noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Gen

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
  {V : Submodule ℂ M}

theorem generatedSubmodule_stable (a b : Fin n) {v : M} (hv : v ∈ genSub E V) : E a b v ∈ genSub E V := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem le_generatedSubmodule : V ≤ genSub E V := le_sInf fun _ hT => hT.1

theorem eulerAction_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem tensorAction_mem_generated {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) (a b : Fin n) :
    ∀ c, tensV E a b f c ∈ genSub E V := by
  intro c
  rw [entry_bounds_of_partialSum]
  refine Submodule.add_mem _ (generatedSubmodule_stable a b (hf c)) ?_
  split_ifs
  · exact hf b
  · exact Submodule.zero_mem _

theorem eulerAction_mem_generated {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) : ∀ d, eeV E f d ∈ genSub E V := by
  intro d
  rw [eulerAction_apply]
  exact Submodule.sum_mem _ fun c _ => generatedSubmodule_stable c d (hf c)

theorem tensorAction_comm_euler (hE : IsGlRep E) (a b : Fin n) (f : Fin n → M) :
    tensV E a b (eeV E f) = eeV E (tensV E a b f) := by
  have key : ∀ c d, E a b (E d c (f d)) = E d c (E a b (f d)) +
      ((if b = d then E a c (f d) else 0) - (if c = a then E d b (f d) else 0)) := by
    intro c d
    have h := LinearMap.congr_fun (hE a b d c) (f d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply,
      apply_ite (fun T : Module.End ℂ M => T (f d)), LinearMap.zero_apply] at h
    rw [← h]; abel
  funext c
  set_option synthInstance.maxHeartbeats 100000 in
    rw [entry_bounds_of_partialSum, eulerAction_apply, eulerAction_apply, eulerAction_apply, map_sum]
  simp only [entry_bounds_of_partialSum, map_add (f := _), key, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ d, (if b = d then E a c (f d) else 0) = E a c (f b) := by simp
  have e2 : ∑ d, E d c (if d = a then f b else 0) = E a c (f b) := by simp [apply_ite]
  rw [e1, e2]
  by_cases hca : c = a
  · subst hca; simp; abel
  · simp [hca]

theorem finiteDimensional_pi_submodule (hV : FiniteDimensional ℂ V) :
    FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => V) := by
  let F : (Fin n → V) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun i => V.subtype ∘ₗ LinearMap.proj i
  have : Submodule.pi Set.univ (fun _ : Fin n => V) ≤ LinearMap.range F := by
    intro f hf
    exact ⟨fun i => ⟨f i, hf i (Set.mem_univ i)⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le this

end Gen

section Poly

variable {X' : Type*} [AddCommGroup X'] [Module ℂ X']

theorem aeval_induction (A : Module.End ℂ X') (P : Module.End ℂ X' → Prop) (h1 : ∀ a : ℂ, P (a • 1))
    (hadd : ∀ S T, P S → P T → P (S + T)) (hmul : ∀ S, P S → P (S * A)) (p : ℂ[X]) :
    P (aeval A p) := by
  induction p using Polynomial.induction_on with
  | C a => rw [aeval_C, Algebra.algebraMap_eq_smul_one]; exact h1 a
  | add p q hp hq => rw [map_add (f := _)]; exact hadd _ _ hp hq
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact hmul _ h

theorem aeval_mul_commute {A B : Module.End ℂ X'} (h : A * B = B * A) (p : ℂ[X]) :
    aeval A p * B = B * aeval A p := by
  refine aeval_induction A (fun S => S * B = B * S) ?_ ?_ ?_ p
  · intro a; rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  · intro S T hS hT; rw [add_mul, mul_add, hS, hT]
  · intro S hS; rw [mul_assoc, h, ← mul_assoc, hS, mul_assoc]

theorem aeval_mem_of_stable_alt {A : Module.End ℂ X'} {G : Submodule ℂ X'} (hG : ∀ x ∈ G, A x ∈ G) (p : ℂ[X]) :
    ∀ x ∈ G, aeval A p x ∈ G := by
  refine aeval_induction A (fun S => ∀ x ∈ G, S x ∈ G) ?_ ?_ ?_ p
  · intro a x hx; exact G.smul_mem a hx
  · intro S T hS hT x hx; exact G.add_mem (hS x hx) (hT x hx)
  · intro S hS x hx; exact hS _ (hG x hx)

theorem prodShift_eq_aeval_prod (A : Module.End ℂ X') (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C ((θ t : ℝ) : ℂ))) := by
  rw [prodShift, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun t => ?_)
  simp [Algebra.algebraMap_eq_smul_one]

end Poly

section Xs

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
  {V : Submodule ℂ M}

def k3bP (θ : Fin n → ℝ) (s : Fin n) : ℂ[X] := ∏ t ∈ univ.erase s, (X - C ((θ t : ℝ) : ℂ))

theorem mem_eigenTensorSpace_gen_iff {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs (eeV E) (genSub E V) θ ↔ (∀ c, f c ∈ genSub E V) ∧ eeV E f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_pi, sub_eq_zero]

theorem lagrange_mem_generated (p : ℂ[X]) {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) :
    ∀ c, aeval (eeV E) p f c ∈ genSub E V := by
  have := aeval_mem_of_stable_alt (A := eeV E) (G := Submodule.pi Set.univ fun _ => genSub E V)
    (fun x hx => fun c _ => eulerAction_mem_generated (fun c => hx c (Set.mem_univ c)) c) p f (fun c _ => hf c)
  exact fun c => this c (Set.mem_univ c)

theorem lagrange_mem_eigenTensorSpace {θ : Fin n → ℝ}
    (hK1 : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → prodShift (eeV E) θ f = 0) (s : Fin n)
    {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) :
    aeval (eeV E) (k3bP θ s) f ∈ Xs (eeV E) (genSub E V) (θ s) := by
  rw [mem_eigenTensorSpace_gen_iff]
  refine ⟨lagrange_mem_generated _ hf, ?_⟩
  have h := hK1 f hf
  rw [prodShift_eq_aeval_prod, ← Finset.mul_prod_erase univ (fun t => X - C ((θ t : ℝ) : ℂ)) (mem_univ s),
    map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact h

theorem lagrange_on_eigenTensorSpace (θ : Fin n → ℝ) (s : Fin n) {x : Fin n → M}
    (hx : x ∈ Xs (eeV E) (genSub E V) (θ s)) :
    aeval (eeV E) (k3bP θ s) x = (k3bP θ s).eval ((θ s : ℝ) : ℂ) • x :=
  Module.End.aeval_apply_of_mem_apply_eq_smul (mem_eigenTensorSpace_gen_iff.1 hx).2

theorem lagrangeFactor_eval_ne_zero_of_injective {θ : Fin n → ℝ} (hθ : Function.Injective θ) (s : Fin n) :
    (k3bP θ s).eval ((θ s : ℝ) : ℂ) ≠ 0 := by
  rw [k3bP, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro t ht
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h
  exact (Finset.ne_of_mem_erase ht) (hθ (Complex.ofReal_injective h)).symm

theorem aeval_tensorAction_comm (hE : IsGlRep E) (p : ℂ[X]) (a b : Fin n) (f : Fin n → M) :
    aeval (eeV E) p (tensV E a b f) = tensV E a b (aeval (eeV E) p f) := by
  have h : eeV E * tensV E a b = tensV E a b * eeV E := by
    refine LinearMap.ext fun g => ?_
    exact (tensorAction_comm_euler hE a b g).symm
  exact LinearMap.congr_fun (aeval_mul_commute h p) f

theorem eigenTensorSpace_stable (hE : IsGlRep E) (a b : Fin n) {θ : ℝ} {f : Fin n → M}
    (hf : f ∈ Xs (eeV E) (genSub E V) θ) : tensV E a b f ∈ Xs (eeV E) (genSub E V) θ := by
  rw [mem_eigenTensorSpace_gen_iff] at hf ⊢
  refine ⟨tensorAction_mem_generated hf.1 a b, ?_⟩
  rw [← tensorAction_comm_euler hE, hf.2, map_smul]

theorem generated_eigenspace_annihilate {N : Type*} [AddCommGroup N] [Module ℂ N] (EN : Fin n → Fin n → Module.End ℂ N)
    (φ : (Fin n → M) →ₗ[ℂ] N)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensV E a b f) = EN a b (φ f))
    (T : Module.End ℂ (Fin n → M)) (hT : ∀ a b f, T (tensV E a b f) = tensV E a b (T f))
    (hTG : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → ∀ c, T f c ∈ genSub E V)
    (hz : ∀ u : Fin n → M, (∀ c, u c ∈ V) → φ (T u) = 0) {f : Fin n → M}
    (hf : f ∈ genSub (tensV E) (Submodule.pi Set.univ fun _ => V)) : φ (T f) = 0 := by
  let Z : Submodule ℂ (Fin n → M) :=
    Submodule.pi Set.univ (fun _ => genSub E V) ⊓ LinearMap.ker (φ ∘ₗ T)
  have hZ : ∀ g, g ∈ Z ↔ (∀ c, g c ∈ genSub E V) ∧ φ (T g) = 0 := fun g => by
    simp [Z, Submodule.mem_pi]
  have hle : genSub (tensV E) (Submodule.pi Set.univ fun _ => V) ≤ Z := by
    refine sInf_le ⟨fun u hu => (hZ u).2 ⟨fun c => le_generatedSubmodule (hu c (Set.mem_univ c)),
      hz u fun c => hu c (Set.mem_univ c)⟩, ?_⟩
    intro a b g hg
    rw [hZ] at hg ⊢
    refine ⟨tensorAction_mem_generated hg.1 a b, ?_⟩
    rw [hT, hφ a b _ (hTG g hg.1), hg.2, map_zero]
  exact ((hZ f).1 (hle hf)).2

theorem casimir_map_intertwiner {N : Type*} [AddCommGroup N] [Module ℂ N]
    (EN : Fin n → Fin n → Module.End ℂ N) (φ : (Fin n → M) →ₗ[ℂ] N)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensV E a b f) = EN a b (φ f))
    {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) : casimir EN (φ f) = φ (casimir (tensV E) f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hφ a b _ (tensorAction_mem_generated hf b a), hφ b a _ hf]

end Xs

theorem casimirValue_add_single (lam : Fin n → ℝ) (s : Fin n) :
    casVal (lam + Pi.single s 1) = casVal lam + n + 2 * thV lam s := by
  simp only [casVal, nsq, dot, thV, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem lowestKType_add_single (ε : Fin n → Bool) (lam : Fin n → ℝ) (s : Fin n) :
    lowK ε (lam + Pi.single s 1) = lowK ε lam + Pi.single s 1 := by
  unfold lowK; abel

theorem lowestKType_shift_inv (ε : Fin n → Bool) (ν : Fin n → ℝ) : lowK ε (ν + rhoC ε - rhoN ε) = ν := by
  unfold lowK; abel

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RealSmulCj
section
noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
  {ε : Fin n → Bool}

def sdd (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) : Cj H →L[ℂ] Cj H :=
  opCj (σ (sub g))

theorem urep_sdd {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (UJset (ε ∘ Fin.rev)) (sdd σ) := by
  obtain ⟨⟨h1, hm⟩, hn, hc⟩ := hσ
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold sdd; rw [sub_one, h1]; rfl
  · intro a ha b hb; unfold sdd; rw [sub_mul, hm _ (inUJ_sub ha) _ (inUJ_sub hb)]; rfl
  · intro g hg v; exact hn _ (inUJ_sub hg) (ofCj v)
  · intro v
    have hcs : Continuous (sub : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      continuous_id.matrix_submatrix _ _
    exact (hc (ofCj v)).comp hcs.continuousOn (fun g hg => inUJ_sub hg)

theorem smul_ofD (c : ℂ) (u : D) : c • ofD u = ofD (conj c • u) := by
  rw [ofD_smul]; simp

theorem sum_rev_swap {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    ∑ a, ∑ b, F a b = ∑ a, ∑ b, F (Fin.rev b) (Fin.rev a) := by
  rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Fin.revPerm]
  rfl

theorem actM_Edd {E : Fin n → Fin n → Module.End ℂ D} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG (ε ∘ Fin.rev) X) (u : D) : actM (Edd ε E) X (ofD u) = ofD (actM E (sub X) u) := by
  unfold actM
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Edd_ofD, smul_ofD, ofD_sum]
  rw [sum_rev_swap]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.rev_rev, sub_apply, smul_smul]
  congr 2
  have he := inG_entry hX (Fin.rev b) (Fin.rev a)
  simp only [Function.comp_apply, Fin.rev_rev] at he
  rw [he]
  unfold sg
  simp only [Fin.rev_rev]
  cases ε a <;> cases ε b <;> simp

theorem real_smul_cj (r : ℝ) (x : Cj H) : r • x = toCj (r • ofCj x) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ) r (ofCj x),
    ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace.smul_def, RCLike.conj_ofReal]

def toCjR : H →L[ℝ] Cj H where
  toFun := toCj
  map_add' _ _ := rfl
  map_smul' r x := (real_smul_cj r (toCj x)).symm
  cont := continuous_id

theorem derived_sdd {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
    (hD : IsDerivedOn ε σ D E) : IsDerivedOn (ε ∘ Fin.rev) (sdd σ) (cjSub D) (Edd ε E) := by
  refine ⟨glRep_Edd ε hD.glRep, ?_, ?_⟩
  · intro k hk v hv
    exact hD.kStable (sub k) (K_sub hk) (ofCj v) hv
  · intro X hX v
    have h3 := hD.deriv (sub X) (inG_sub hX) (toD v)
    have h4 := (toCjR (H := H)).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) h3
    have hv : v = ofD (toD v) := rfl
    rw [hv, actM_Edd hX]
    convert (preTransparency := .reducible) h4 using 1
    · funext t
      simp only [sdd, Function.comp_apply, ← exp_sub, sub_smul]
      rfl
    · rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal
end
end

