module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.AtTLemmas

@[expose] public section

open Module

noncomputable section

namespace Formalism.L2.Col

namespace RamFun

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, CommGroup (G i)]
  [∀ i, Fintype (G i)] {M : Type} [AddCommGroup M] [Module K M]


variable (K M) in
def trl (b : ∀ i, G i) : Module.End K ((∀ i, G i) → M) := LinearMap.funLeft K M fun c => b * c

theorem trl_apply (b : ∀ i, G i) (F : (∀ i, G i) → M) (c : ∀ i, G i) : trl K M b F c = F (b * c) := rfl

theorem trl_one : trl K M (1 : ∀ i, G i) = 1 := by
  refine LinearMap.ext fun F => funext fun c => ?_
  show F (1 * c) = F c
  rw [one_mul]

theorem trl_mul (b b' : ∀ i, G i) : trl K M b * trl K M b' = trl K M (b * b') := by
  refine LinearMap.ext fun F => funext fun c => ?_
  show F (b' * (b * c)) = F (b * b' * c)
  congr 1
  rw [mul_left_comm, mul_assoc]

theorem trl_comm (b b' : ∀ i, G i) : Commute (trl K M b) (trl K M b') := by
  show trl K M b * trl K M b' = trl K M b' * trl K M b
  rw [trl_mul, trl_mul, mul_comm]


variable (K M) in
def nmF (i : ι) : Module.End K ((∀ i, G i) → M) := ∑ g : G i, trl K M (Pi.mulSingle i g)


variable (K M G) in
def ramFun : Submodule K ((∀ i, G i) → M) := ⨅ i, LinearMap.ker (nmF K M (G := G) i)


variable (K M G) in
def offAlg (i : ι) : Submodule K (Module.End K ((∀ i, G i) → M)) :=
  Submodule.span K {x | ∃ b : ∀ i, G i, b i = 1 ∧ x = trl K M b}

theorem one_mem_offAlg (i : ι) : (1 : Module.End K ((∀ i, G i) → M)) ∈ offAlg K G M i := by
  have h : trl K M (1 : ∀ i, G i) ∈ offAlg K G M i := Submodule.subset_span ⟨1, rfl, rfl⟩
  rwa [trl_one] at h

theorem mul_mem_offAlg (i : ι) {x y : Module.End K ((∀ i, G i) → M)} (hx : x ∈ offAlg K G M i)
    (hy : y ∈ offAlg K G M i) : x * y ∈ offAlg K G M i := by
  unfold offAlg at *
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨b, hb, rfl⟩ := hx'
      obtain ⟨b', hb', rfl⟩ := hy'
      exact Submodule.subset_span ⟨b * b', by rw [Pi.mul_apply, hb, hb', one_mul], trl_mul b b'⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

theorem nmF_mem_offAlg {i j : ι} (h : j ≠ i) : nmF K M (G := G) j ∈ offAlg K G M i := by
  unfold nmF
  exact Submodule.sum_mem _ fun g _ =>
    Submodule.subset_span ⟨Pi.mulSingle j g, Pi.mulSingle_eq_of_ne h.symm g, rfl⟩

theorem nmF_comm_trl (i : ι) (b : ∀ i, G i) : Commute (nmF K M (G := G) i) (trl K M b) :=
  Commute.sum_left _ _ _ fun _ _ => trl_comm _ _

theorem nmF_comm (i j : ι) : Commute (nmF K M (G := G) i) (nmF K M (G := G) j) :=
  Commute.sum_left _ _ _ fun _ _ => (nmF_comm_trl j _).symm

theorem nmF_sq (i : ι) : nmF K M (G := G) i * nmF K M i = (Fintype.card (G i) : K) • nmF K M i := by
  have key : ∀ g : G i, nmF K M (G := G) i * trl K M (Pi.mulSingle i g) = nmF K M i := by
    intro g
    show (∑ h : G i, trl K M (Pi.mulSingle i h)) * trl K M (Pi.mulSingle i g) =
      ∑ h : G i, trl K M (Pi.mulSingle i h)
    rw [Finset.sum_mul]
    simp_rw [trl_mul, ← Pi.mulSingle_mul]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun _ => rfl
  calc nmF K M (G := G) i * nmF K M i = ∑ g : G i, nmF K M (G := G) i * trl K M (Pi.mulSingle i g) := by
        rw [← Finset.mul_sum]; rfl
    _ = ∑ _g : G i, nmF K M (G := G) i := Finset.sum_congr rfl fun g _ => key g
    _ = (Fintype.card (G i) : K) • nmF K M i := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K]

section Trace

variable [FiniteDimensional K M]

theorem trace_trl {b : ∀ i, G i} (hb : b ≠ 1) : LinearMap.trace K _ (trl K M b) = 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basis fun _ : (∀ i, G i) => Module.finBasis K M), Matrix.trace]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨c, k⟩ := p
  have hc : b * c ≠ c := fun h => hb (mul_right_cancel (h.trans (one_mul c).symm))
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr, trl_apply]
  rw [Pi.single_eq_of_ne hc]
  simp

theorem trace_mul_offAlg {i : ι} {g : G i} (hg : g ≠ 1) {x : Module.End K ((∀ i, G i) → M)}
    (hx : x ∈ offAlg K G M i) : LinearMap.trace K _ (trl K M (Pi.mulSingle i g) * x) = 0 := by
  unfold offAlg at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [trl_mul]
    refine trace_trl fun h => hg ?_
    have := congrFun h i
    simpa [hb] using this
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add (f := _), hx, hy, add_zero]
  | smul a x _ hx => rw [mul_smul_comm, map_smul, hx, smul_zero]

theorem trace_nmF_mul {i : ι} {x : Module.End K ((∀ i, G i) → M)} (hx : x ∈ offAlg K G M i) :
    LinearMap.trace K _ (nmF K M i * x) = LinearMap.trace K _ x := by
  show LinearMap.trace K _ ((∑ g : G i, trl K M (Pi.mulSingle i g)) * x) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, Finset.sum_eq_single (1 : G i)]
  · rw [Pi.mulSingle_one, trl_one, one_mul]
  · intro g _ hg
    exact trace_mul_offAlg hg hx
  · intro h
    exact absurd (Finset.mem_univ _) h

end Trace

end RamFun

namespace RamFun

section Proj

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
  [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] {M : Type} [AddCommGroup M] [Module K M]


variable (K M G) in
def eF (i : ι) : Module.End K ((∀ i, G i) → M) := 1 - ((Fintype.card (G i) : K)⁻¹) • nmF K M i

theorem card_ne (i : ι) : (Fintype.card (G i) : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem nmF_mul_eF (i : ι) : nmF K M i * eF K G M i = 0 := by
  unfold eF
  rw [mul_sub, mul_one, mul_smul_comm, nmF_sq, smul_smul, inv_mul_cancel₀ (card_ne (K := K) (G := G) i),
    one_smul, sub_self]

theorem eF_mem_offAlg {i j : ι} (h : j ≠ i) : eF K G M j ∈ offAlg K G M i :=
  Submodule.sub_mem _ (one_mem_offAlg i) (Submodule.smul_mem _ _ (nmF_mem_offAlg h))

theorem nmF_comm_eF (i j : ι) : Commute (nmF K M (G := G) i) (eF K G M j) :=
  (Commute.one_right _).sub_right ((nmF_comm i j).smul_right _)


variable (K M G) in
def eL (l : List ι) : Module.End K ((∀ i, G i) → M) := (l.map (eF K G M)).prod

theorem eL_mem_offAlg {i : ι} {l : List ι} (h : i ∉ l) : eL K G M l ∈ offAlg K G M i := by
  induction l with
  | nil =>
    simp only [eL, List.map_nil, List.prod_nil]
    exact one_mem_offAlg i
  | cons a l ih =>
    rw [List.mem_cons, not_or] at h
    simp only [eL, List.map_cons, List.prod_cons] at ih ⊢
    exact mul_mem_offAlg i (eF_mem_offAlg (Ne.symm h.1)) (ih h.2)

theorem nmF_mul_eL {i : ι} {l : List ι} (h : i ∈ l) : nmF K M i * eL K G M l = 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [eL, List.map_cons, List.prod_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h'
    · rw [← mul_assoc, nmF_mul_eF, zero_mul]
    · rw [← mul_assoc, (nmF_comm_eF i a).eq, mul_assoc, ih h', mul_zero]

theorem eL_fix {F : (∀ i, G i) → M} (hF : F ∈ ramFun K G M) (l : List ι) : eL K G M l F = F := by
  have h1 : ∀ j, eF K G M j F = F := by
    intro j
    have h0 : nmF K M j F = 0 := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hF j)
    simp [eF, h0]
  induction l with
  | nil => simp [eL]
  | cons a l ih =>
    simp only [eL, List.map_cons, List.prod_cons] at ih ⊢
    show eF K G M a ((List.map (eF K G M) l).prod F) = F
    rw [ih, h1]

variable [FiniteDimensional K M]

theorem trace_eL {l : List ι} (hl : l.Nodup) :
    LinearMap.trace K _ (eL K G M l) =
      (l.map fun i => (1 - (Fintype.card (G i) : K)⁻¹)).prod * LinearMap.trace K ((∀ i, G i) → M) 1 := by
  induction l with
  | nil => simp [eL]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hx : eL K G M l ∈ offAlg K G M a := eL_mem_offAlg hl.1
    have e : eL K G M (a :: l) = eF K G M a * eL K G M l := by simp [eL]
    rw [e, eF, sub_mul, one_mul, smul_mul_assoc, map_sub, map_smul, trace_nmF_mul hx, ih hl.2,
      List.map_cons, List.prod_cons, smul_eq_mul]
    ring

theorem isProj_eL : LinearMap.IsProj (ramFun K G M) (eL K G M Finset.univ.toList) := by
  refine ⟨?_, fun F hF => eL_fix hF _⟩
  refine fun F => (Submodule.mem_iInf _).2 fun i => ?_
  show nmF K M i (eL K G M Finset.univ.toList F) = 0
  rw [← mul_apply_eq_comp, nmF_mul_eL (Finset.mem_toList.2 (Finset.mem_univ i))]
  rfl

theorem finrank_ramFun : finrank K (ramFun K G M) = finrank K M * ∏ i, (Fintype.card (G i) - 1) := by
  have h := (isProj_eL (K := K) (G := G) (M := M)).trace
  rw [trace_eL (Finset.nodup_toList _), LinearMap.trace_one, Finset.prod_map_toList] at h
  have hV : finrank K ((∀ i, G i) → M) = (∏ i, Fintype.card (G i)) * finrank K M := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_pi, smul_eq_mul]
  have hc : ∀ i, ((Fintype.card (G i) - 1 : ℕ) : K) =
      (Fintype.card (G i) : K) * (1 - (Fintype.card (G i) : K)⁻¹) := by
    intro i
    rw [Nat.cast_sub (Fintype.card_pos : 1 ≤ Fintype.card (G i)), Nat.cast_one, mul_sub, mul_one,
      mul_inv_cancel₀ (card_ne (K := K) (G := G) i)]
  rw [hV] at h
  apply Nat.cast_injective (R := K)
  rw [← h]
  simp only [Nat.cast_mul, Nat.cast_prod]
  rw [Finset.prod_congr rfl fun i _ => hc i, Finset.prod_mul_distrib]
  ring

end Proj

end RamFun

section ColsRank

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)




end ColsRank

end Formalism.L2.Col
