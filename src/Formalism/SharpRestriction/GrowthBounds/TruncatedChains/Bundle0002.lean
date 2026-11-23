module

public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RaisingKillOfInterface
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pp_append (E : GLOps n K V) (mu : Fin n → ℤ) (l1 l2 : List (Fin n × Fin n)) (T : ℕ) (x : V) :
    pp E mu (l1 ++ l2) T x = pp E mu l1 T (pp E mu l2 T x) := by
  simp only [pp, List.map_append, List.prod_append, Module.End.mul_apply]

theorem pp_cons (E : GLOps n K V) (mu : Fin n → ℤ) (ab : Fin n × Fin n) (l : List (Fin n × Fin n)) (T : ℕ) (x : V) :
    pp E mu (ab :: l) T x = ppFac E mu ab.1 ab.2 T (pp E mu l T x) := by
  simp only [pp, List.map_cons, List.prod_cons, Module.End.mul_apply]

end

private theorem mem_weightSp_iff_forall_diag {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (ν : Fin n → ℤ) (y : V) :
    y ∈ weightSp E ν ↔ ∀ c, E c c y = (ν c : K) • y := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero]
  first
  | simp only [Module.End.one_apply]
  | simp only [LinearMap.one_apply]

private theorem glRep_apply_mem_weightSp_shift {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (ν : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E ν) :
    E a b y ∈ weightSp E (fun c => ν c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_weightSp_iff_forall_diag] at hy ⊢
  intro c
  have h := congrArg (fun f : Module.End K V => f y) (hE.1 c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hy c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a
  · subst hca
    by_cases hcb : c = b
    · subst hcb
      simp only [eq_self_iff_true, if_true]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul])
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [eq_self_iff_true, if_true, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul]; abel)
  · by_cases hcb : c = b
    · subst hcb
      simp only [eq_self_iff_true, if_true, if_neg hca, LinearMap.zero_apply, zero_sub]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul]; abel)
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [if_neg hca, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero, zero_add]
      push_cast
      first
      | module
      | simp

private theorem glRep_pow_apply_mem_weightSp_shift {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (k : ℕ) (ν : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E ν) :
    (E a b ^ k) y ∈ weightSp E
      (fun c => ν c + (k : ℤ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  induction k generalizing ν y with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h1 := ih _ _ (glRep_apply_mem_weightSp_shift E hE a b ν y hy)
    convert h1 using 2
    funext c
    push_cast
    ring

private theorem ppFac_apply_mem_weightSp_of_mem {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (a b : Fin n) (T : ℕ) (ν : Fin n → ℤ)
    (y : V) (hy : y ∈ weightSp E ν) : ppFac E mu a b T y ∈ weightSp E ν := by
  unfold ppFac
  first
  | rw [LinearMap.sum_apply]
  | rw [LinearMap.coe_sum, Finset.sum_apply]
  | rw [LinearMap.coe_fn_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  simp only [divPowE, LinearMap.smul_apply, Module.End.mul_apply, map_smul]
  refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))
  have h1 := glRep_pow_apply_mem_weightSp_shift E hE a b k ν y hy
  have h2 := glRep_pow_apply_mem_weightSp_shift E hE b a k _ _ h1
  convert h2 using 2
  funext c
  ring

private theorem pp_apply_mem_weightSp_of_mem {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (l : List (Fin n × Fin n)) (T : ℕ)
    (ν : Fin n → ℤ) (y : V) (hy : y ∈ weightSp E ν) : pp E mu l T y ∈ weightSp E ν := by
  induction l with
  | nil => simpa [pp] using hy
  | cons ab l ih =>
    rw [pp_cons]
    exact ppFac_apply_mem_weightSp_of_mem E hE mu ab.1 ab.2 T ν _ ih

theorem pp_step (hC : RestComm) (hY : RestYB) {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ)
    (hmu : ∀ a b : Fin n, a < b → 1 ≤ mu a - mu b + ((b : ℤ) - (a : ℤ))) (T : ℕ) (hT : Module.finrank K V ≤ T)
    {l l' : List (Fin n × Fin n)} (h : Step n l l') (x : V) (hx : x ∈ weightSp E mu) :
    pp E mu l T x = pp E mu l' T x := by
  cases h with
  | swap l1 l2 a b c d hac had hbc hbd =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    exact LinearMap.congr_fun (hC K V n E hE a b c d hac had hbc hbd _ _ T).eq _
  | braid l1 l2 a b c hab hbc =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    have h1 := hmu a b hab
    have h2 := hmu b c hbc
    have h3 := hmu a c (hab.trans hbc)
    have hab2 : (a : ℕ) < b := hab
    have hbc2 : (b : ℕ) < c := hbc
    have e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat =
        (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat := by
      omega
    rw [hu]
    exact hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne
      mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)
  | braid' l1 l2 a b c hab hbc =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    have h1 := hmu a b hab
    have h2 := hmu b c hbc
    have h3 := hmu a c (hab.trans hbc)
    have hab2 : (a : ℕ) < b := hab
    have hbc2 : (b : ℕ) < c := hbc
    have e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat =
        (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat := by
      omega
    rw [hu]
    exact (hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne
      mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)).symm

theorem raising_kill_of_interface (hN : RestConn) (hC : RestComm) (hY : RestYB) (hK : RestKill) : SimpleRaisingKillsExtremalProjector := by
  intro K V _ _ _ _ _ n E hE mu hmu ord hord T hT x hx a b hab
  obtain ⟨l, hl⟩ := hN n ord hord a b hab
  have key : ∀ l', Relation.ReflTransGen (Step n) ord l' → pp E mu ord T x = pp E mu l' T x := by
    intro l' hl'
    induction hl' with
    | refl => rfl
    | tail _ hs ih => rw [ih, pp_step hC hY E hE mu hmu T hT hs x hx]
  have hlt : a < b := by
    rw [Fin.lt_iff_val_lt_val]
    omega
  have h1 := hmu a b hlt
  have hba : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = 1 := by omega
  have key2 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + 1 := by
    rw [Int.toNat_of_nonneg (by linarith)]
    linarith
  rw [key _ hl, pp_cons, ppFac_eq]
  exact hK K V n E hE a b hlt.ne mu _ key2 T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l T mu x hx)

end Formalism.MainNotions.G.ExtremalProjector
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPairOf
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem comm_of_disj {E : GLOps n K V} (hE : IsGLRep E) {a b c d : Fin n} (h1 : b ≠ c) (h2 : d ≠ a) :
    Commute (E a b) (E c d) := by
  have := hE.1 a b c d
  rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at this
  exact this

theorem divPow_comm {E : GLOps n K V} {a b c d : Fin n} (h : Commute (E a b) (E c d)) (j k : ℕ) :
    Commute (divPowE E a b j) (divPowE E c d k) := by
  unfold divPowE
  exact ((h.pow_pow j k).smul_left _).smul_right _

theorem pf_comm {E : GLOps n K V} (hE : IsGLRep E) {a b c d : Fin n} (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c)
    (h4 : b ≠ d) (s s' T : ℕ) : Commute (pf E a b s T) (pf E c d s' T) := by
  unfold pf
  refine Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ => ?_
  refine (Commute.smul_left ?_ _).smul_right _
  have c1 : Commute (E b a) (E d c) := comm_of_disj hE h2 h3.symm
  have c2 : Commute (E b a) (E c d) := comm_of_disj hE h1 h4.symm
  have c3 : Commute (E a b) (E d c) := comm_of_disj hE h4 h1.symm
  have c4 : Commute (E a b) (E c d) := comm_of_disj hE h3 h2.symm
  exact Commute.mul_left (Commute.mul_right (divPow_comm c1 j k) (divPow_comm c2 j k))
    (Commute.mul_right (divPow_comm c3 j k) (divPow_comm c4 j k))

theorem dual_mem (E : GLOps n K V) (ν : Fin n → ℤ) (x : V) :
    x ∈ weightSp (dualOps E) (-ν) ↔ x ∈ weightSp E ν := by
  rw [mem_weightSpace_iff_diagonal_eigen, mem_weightSpace_iff_diagonal_eigen]
  refine forall_congr' fun a => ?_
  simp only [dualOps, LinearMap.neg_apply, Pi.neg_apply, Int.cast_neg, neg_smul, neg_inj]

theorem dual_rep {E : GLOps n K V} (hE : IsGLRep E) : IsGLRep (dualOps E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    have := hE.1 b a d c
    simp only [dualOps, neg_mul_neg]
    rw [this, if_congr (eq_comm (a := a) (b := d)) rfl rfl, if_congr (eq_comm (a := c) (b := b)) rfl rfl]
    split_ifs <;> abel
  · intro x
    obtain ⟨W, h1, h2, h3⟩ := hE.2.1 x
    exact ⟨W, h1, h2, fun a b y hy => by
      simp only [dualOps, LinearMap.neg_apply]
      exact W.neg_mem (h3 b a y hy)⟩
  · rw [eq_top_iff, ← hE.2.2]
    refine iSup_le fun ν => le_iSup_of_le (-ν) fun x hx => (dual_mem E ν x).2 hx

theorem divPow_dual (E : GLOps n K V) (x y : Fin n) (k : ℕ) :
    divPowE (dualOps E) x y k = (-1 : K) ^ k • divPowE E y x k := by
  simp only [divPowE, dualOps]
  rw [show -E y x = (-1 : K) • E y x by simp, smul_pow, smul_comm]

theorem pf_dual (E : GLOps n K V) (x y : Fin n) (c T : ℕ) : pf (dualOps E) x y c T = pf E y x c T := by
  unfold pf
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [divPow_dual, divPow_dual, smul_mul_smul_comm, ← mul_pow]
  simp

end

theorem restComm : RestComm := fun _ _ _ _ _ _ _ hE _ _ _ _ h1 h2 h3 h4 s s' T => pf_comm hE h1 h2 h3 h4 s s' T

theorem restPair'_of (h : RestPair) : RestPair' := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν t u hu T hT w hw
  have := h K V n (dualOps E) (dual_rep hE) c b a hbc.symm hac.symm hab.symm (-ν) t u
    (by simp only [Pi.neg_apply]; omega) T hT w ((dual_mem E ν w).2 hw)
  simp only [pf_dual] at this
  simp only [dualOps, LinearMap.neg_apply, map_neg, neg_inj] at this
  exact this

theorem ybat_symm (sg ta : ℕ) (h : YBat sg ta) : YBat ta sg := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx
  have := h K V n (dualOps E) (dual_rep hE) c b a hbc.symm hac.symm hab.symm (-ν) t s
    (by simp only [Pi.neg_apply]; omega) (by simp only [Pi.neg_apply]; omega) T hT x ((dual_mem E ν x).2 hx)
  simp only [pf_dual] at this
  rw [add_comm t s] at this
  exact this.symm

end Formalism.MainNotions.G.ExtremalProjector
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestTruncOfNil
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {n : ℕ} {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem pf_apply (E : GLOps n K V) (a b : Fin n) (c T : ℕ) (x : V) :
    pf E a b c T x = ∑ k ∈ Finset.range (T + 1),
      ((-1 : K) ^ k / ((Nat.choose (c + k) k : ℕ) : K)) •
        (((k.factorial : K)⁻¹) • ((E b a) ^ k) (((k.factorial : K)⁻¹) • ((E a b) ^ k) x)) := by
  unfold pf
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [divPowE, Module.End.mul_apply]

theorem pow_mem_stable (f : Module.End K W) (S : Submodule K W) (h : ∀ w ∈ S, f w ∈ S) (k : ℕ) (w : W)
    (hw : w ∈ S) : (f ^ k) w ∈ S := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact h _ ih

theorem pf_mem (A : GLOps n K W) (S : Submodule K W) (x y : Fin n) (h1 : ∀ w ∈ S, A x y w ∈ S)
    (h2 : ∀ w ∈ S, A y x w ∈ S) (c T : ℕ) (w : W) (hw : w ∈ S) : pf A x y c T w ∈ S := by
  rw [pf_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (pow_mem_stable _ S h2 k _ (Submodule.smul_mem _ _ (pow_mem_stable _ S h1 k w hw))))

theorem pow_intertw (f : Module.End K W) (g : Module.End K V) (π : W →ₗ[K] V) (S : Submodule K W)
    (hS : ∀ w ∈ S, f w ∈ S) (h : ∀ w ∈ S, π (f w) = g (π w)) (k : ℕ) (w : W) (hw : w ∈ S) :
    π ((f ^ k) w) = (g ^ k) (π w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      h _ (pow_mem_stable f S hS k w hw), ih]

theorem pf_intertw (A : GLOps n K W) (E : GLOps n K V) (π : W →ₗ[K] V) (S : Submodule K W) (x y : Fin n)
    (hS : ∀ w ∈ S, A x y w ∈ S) (h1 : ∀ w ∈ S, π (A x y w) = E x y (π w)) (h2 : ∀ w, π (A y x w) = E y x (π w))
    (c T : ℕ) (w : W) (hw : w ∈ S) : π (pf A x y c T w) = pf E x y c T (π w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pf_apply, pf_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, pow_intertw (A y x) (E y x) π ⊤ (fun _ _ => Submodule.mem_top)
    (fun w _ => h2 w) k _ Submodule.mem_top, map_smul, pow_intertw (A x y) (E x y) π S hS h1 k w hw]

theorem pf_wt {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (ν : Fin n → ℤ) (a b : Fin n) (c T : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : pf E a b c T x ∈ weightSp E ν := by
  have hpow : ∀ (a' b' : Fin n) (k : ℕ) (μ : Fin n → ℤ) (y : V), y ∈ weightSp E μ →
      (E a' b' ^ k) y ∈ weightSp E (μ + k • rootW a' b') := by
    intro a' b' k
    induction k with
    | zero => intro μ y hy; simpa using hy
    | succ k ih =>
      intro μ y hy
      rw [pow_succ', Module.End.mul_apply]
      have := hs a' b' _ _ (ih μ y hy)
      convert this using 2
      rw [succ_nsmul, add_assoc]
  have hr : rootW a b + rootW b a = 0 := by
    unfold rootW
    abel
  rw [pf_apply]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
  have h1 := hpow b a k _ _ (Submodule.smul_mem _ ((k.factorial : K)⁻¹) (hpow a b k ν x hx))
  have he : ν + k • rootW a b + k • rootW b a = ν := by
    rw [add_assoc, ← smul_add, hr, smul_zero, add_zero]
  rw [he] at h1
  exact h1

theorem pf_sub (E : GLOps n K V) (a b : Fin n) (c T : ℕ) (x : V) :
    pf E a b c T x - x ∈ LinearMap.range (E b a) := by
  rw [pf_apply, Finset.sum_range_succ', add_sub_assoc]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => ?_) ?_
  · refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    rw [pow_succ', Module.End.mul_apply]
    exact LinearMap.mem_range_self _ _
  · simp

end Gen

section Tens

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def tensOps (E : GLOps n K V) : GLOps n K (Fin n → V) := fun x y =>
  LinearMap.pi fun i => E x y ∘ₗ (LinearMap.proj i : (Fin n → V) →ₗ[K] V) +
    if i = x then (LinearMap.proj y : (Fin n → V) →ₗ[K] V) else 0

theorem tensOps_apply (E : GLOps n K V) (x y : Fin n) (w : Fin n → V) (i : Fin n) :
    tensOps E x y w i = E x y (w i) + if i = x then w y else 0 := by
  by_cases h : i = x <;> simp [tensOps, h]

theorem tens_rel {E : GLOps n K V} (hE : IsGLRep E) (a b c d : Fin n) :
    tensOps E a b * tensOps E c d - tensOps E c d * tensOps E a b =
      (if b = c then tensOps E a d else 0) - (if d = a then tensOps E c b else 0) := by
  refine LinearMap.ext fun w => funext fun i => ?_
  have hc := LinearMap.congr_fun (hE.1 a b c d) (w i)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, tensOps_apply, map_add (f := _)]
  split_ifs at hc ⊢ <;> subst_vars <;>
    (try simp only [tensOps_apply, LinearMap.zero_apply, Pi.zero_apply, map_zero, add_zero, zero_add,
      sub_zero, LinearMap.sub_apply] at hc ⊢) <;>
    (try split_ifs at hc ⊢) <;> (try subst_vars) <;>
    first
    | abel1
    | (rw [sub_eq_iff_eq_add] at hc; rw [hc]; abel1)
    | skip
  all_goals done

theorem tens_single_wt (E : GLOps n K V) (ν : Fin n → ℤ) (i : Fin n) (x : V) (hx : x ∈ weightSp E ν) :
    (Pi.single i x : Fin n → V) ∈ weightSp (tensOps E) (ν + Pi.single i 1) := by
  unfold weightSp at hx ⊢
  rw [Submodule.mem_iInf] at hx ⊢
  intro a
  have ha := hx a
  rw [LinearMap.mem_ker] at ha ⊢
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at ha ⊢
  funext j
  rw [tensOps_apply]
  by_cases hj : j = i
  · subst hj
    by_cases hja : j = a
    · subst hja
      simp [ha, add_smul]
    · simp [ha, hja, Ne.symm hja]
  · by_cases hja : j = a
    · subst hja
      simp [hj]
    · simp [hj, hja]

theorem tens_isGLRep [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) : IsGLRep (tensOps E) := by
  refine ⟨fun a b c d => tens_rel hE a b c d,
    fun x => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hw : w i ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ mu : Fin n → ℤ, weightSp E mu) ≤
      (⨆ mu : Fin n → ℤ, weightSp (tensOps E) mu).comap (LinearMap.single K (fun _ : Fin n => V) i) :=
    iSup_le fun mu y hy => Submodule.mem_iSup_of_mem (mu + Pi.single i 1) (tens_single_wt E mu i y hy)
  exact hle hw

end Tens

end Formalism.MainNotions.G.ExtremalProjector
end
end

