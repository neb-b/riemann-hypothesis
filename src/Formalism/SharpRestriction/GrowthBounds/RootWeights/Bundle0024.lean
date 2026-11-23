module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0011
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0023
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantInjectiveOfCyclic

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.FiltrationAdjointStable
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem pow_apply_mem_weightSp_add_smul_rootW {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (a b : Fin n) (k : ℕ)
    (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    ((E a b) ^ k) x ∈ weightSp E (ν + (k : ℤ) • rootW a b) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have e : ν + ((k + 1 : ℕ) : ℤ) • rootW a b = (ν + (k : ℤ) • rootW a b) + rootW a b := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rw [e, pow_succ']
    exact hs a b _ _ ih

theorem projector_factor_preserves_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (mu ν : Fin n → ℤ) (a b : Fin n) (T : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : ppFac E mu a b T x ∈ weightSp E ν := by
  have key : ∀ k : ℕ, (divPowE E b a k * divPowE E a b k) x ∈ weightSp E ν := by
    intro k
    have h1 := pow_apply_mem_weightSp_add_smul_rootW hs a b k ν x hx
    have h2 := pow_apply_mem_weightSp_add_smul_rootW hs b a k _ _ h1
    have e : ν + (k : ℤ) • rootW a b + (k : ℤ) • rootW b a = ν := by
      funext c
      simp only [rootW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [e] at h2
    show divPowE E b a k (divPowE E a b k x) ∈ weightSp E ν
    simp only [divPowE, LinearMap.smul_apply, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ h2)
  simp only [ppFac, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (key k)

theorem extremal_projector_preserves_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (mu ν : Fin n → ℤ) (ord : List (Fin n × Fin n)) (T : ℕ)
    (x : V) (hx : x ∈ weightSp E ν) : pp E mu ord T x ∈ weightSp E ν := by
  induction ord with
  | nil => simpa [pp] using hx
  | cons ab ord ih =>
    simp only [pp, List.map_cons, List.prod_cons] at ih ⊢
    exact projector_factor_preserves_weight hs mu ν ab.1 ab.2 T _ ih

theorem divided_power_kills_kernel (E : GLOps n K V) (a b : Fin n) (k : ℕ) (hk : k ≠ 0) (x : V) (h : E a b x = 0) :
    divPowE E a b k x = 0 := by
  cases k with
  | zero => exact absurd rfl hk
  | succ j =>
    have hm : ∀ (f g : Module.End K V) (y : V), (f * g) y = f (g y) := fun _ _ _ => rfl
    simp only [divPowE, LinearMap.smul_apply]
    rw [pow_succ, hm, h, map_zero, smul_zero]

theorem projector_factor_fixes_kernel (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) (T : ℕ) (x : V) (h : E a b x = 0) :
    ppFac E mu a b T x = x := by
  have hz : ∀ k : ℕ, (divPowE E b a (k + 1) * divPowE E a b (k + 1)) x = 0 := by
    intro k
    show divPowE E b a (k + 1) (divPowE E a b (k + 1) x) = 0
    rw [divided_power_kills_kernel E a b (k + 1) (Nat.succ_ne_zero k) x h, map_zero]
  simp only [ppFac, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_range_succ']
  simp only [hz, smul_zero, Finset.sum_const_zero, zero_add]
  simp [divPowE]

theorem extremal_projector_fixes_hwv (E : GLOps n K V) (mu : Fin n → ℤ) (ord : List (Fin n × Fin n)) (T : ℕ) (x : V)
    (h : ∀ ab ∈ ord, E ab.1 ab.2 x = 0) : pp E mu ord T x = x := by
  have hm : ∀ (f g : Module.End K V) (y : V), (f * g) y = f (g y) := fun _ _ _ => rfl
  induction ord with
  | nil => simp [pp]
  | cons ab ord ih =>
    have ih' := ih (fun ab' hab' => h ab' (by simp [hab']))
    simp only [pp, List.map_cons, List.prod_cons] at ih' ⊢
    rw [hm, ih']
    exact projector_factor_fixes_kernel E mu ab.1 ab.2 T x (h ab (by simp))

theorem lowering_operator_mem_nMinus (E : GLOps n K V) {a b : Fin n} (hab : b < a) (w : V) : E a b w ∈ nMinus E := by
  unfold nMinus
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem hab (LinearMap.mem_range_self _ _)))

theorem projector_factor_sub_mem_nMinus (E : GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n} (hab : a < b) (T : ℕ) (x : V) :
    ppFac E mu a b T x - x ∈ nMinus E := by
  have hm : ∀ (f g : Module.End K V) (y : V), (f * g) y = f (g y) := fun _ _ _ => rfl
  have hterm : ∀ i : ℕ, (divPowE E b a (i + 1) * divPowE E a b (i + 1)) x ∈ nMinus E := by
    intro i
    rw [hm]
    simp only [divPowE, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    rw [pow_succ' (E b a) i, hm]
    exact lowering_operator_mem_nMinus E hab _
  have fin : ∀ y z : V, y ∈ nMinus E → z = x → y + z - x ∈ nMinus E := by
    intro y z hy hz
    subst hz
    simpa using hy
  simp only [ppFac, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_range_succ']
  exact fin _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hterm i)) (by simp [divPowE])

theorem extremal_projector_sub_mem_nMinus (E : GLOps n K V) (mu : Fin n → ℤ) (ord : List (Fin n × Fin n)) (T : ℕ) (x : V)
    (h : ∀ ab ∈ ord, ab.1 < ab.2) : pp E mu ord T x - x ∈ nMinus E := by
  induction ord with
  | nil => simp [pp]
  | cons ab ord ih =>
    have ih' := ih (fun ab' hab' => h ab' (by simp [hab']))
    have hab : ab.1 < ab.2 := h ab (by simp)
    simp only [pp, List.map_cons, List.prod_cons] at ih' ⊢
    have key : ∀ y : V, ppFac E mu ab.1 ab.2 T y - y ∈ nMinus E → y - x ∈ nMinus E →
        ppFac E mu ab.1 ab.2 T y - x ∈ nMinus E := by
      intro y h1 h2
      have h3 := Submodule.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at h3
    exact key _ (projector_factor_sub_mem_nMinus E mu hab T _) ih'

theorem simple_raising_kill_all_raising {E : GLOps n K V} (hE : IsGLRep E) (y : V)
    (h : ∀ a b : Fin n, a.val + 1 = b.val → E a b y = 0) :
    ∀ (d : ℕ) (a b : Fin n), a.val + d + 1 = b.val → E a b y = 0 := by
  intro d
  induction d with
  | zero =>
    intro a b hab
    exact h a b (by omega)
  | succ d ih =>
    intro a b hab
    have hb := b.isLt
    have hc : a.val + d + 1 < n := by omega
    obtain ⟨c, hcv⟩ : ∃ c : Fin n, c.val = a.val + d + 1 := ⟨⟨a.val + d + 1, hc⟩, rfl⟩
    have h1 : E a c y = 0 := ih a c hcv.symm
    have h2 : E c b y = 0 := h c b (by omega)
    have hba : b ≠ a := by
      intro e
      rw [e] at hab
      omega
    have hcomm : E a c (E c b y) - E c b (E a c y) =
        ((if c = c then E a b else 0) - (if b = a then E c c else 0)) y :=
      LinearMap.congr_fun (hE.1 a c c b) y
    rw [h1, h2, map_zero, map_zero, sub_zero, if_pos rfl, if_neg hba, sub_zero] at hcomm
    exact hcomm.symm

end

theorem hwv_mem_nMinus_eq_zero (D : Formalism.BasicNotions.D7) {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E mu) (hr : ∀ a b : Fin n, a < b → E a b y = 0) (hn : y ∈ nMinus E) : y = 0 := by
  by_contra hne
  have hXst : IsStableUnderOperators E (isoSub E mu) := fun a b x hx => isotypic_stable_under_gl_operator E mu a b x hx
  have hXle : isoSub E mu ≤ cr_WS E (weightsBelow mu) := by
    refine le_trans (Submodule.span_mono ?_) (isotypic_component_le_lower_weights E hE.1 ⊤ mu)
    rintro x ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, Submodule.mem_top, hv, rfl⟩
  have hyX : y ∈ isoSub E mu :=
    Submodule.subset_span ⟨1, Submonoid.one_mem _, y, ⟨hne, hy, hr⟩, rfl⟩
  obtain ⟨X', hc, hX'⟩ := cr_compl E hE.1 hE.2.2 (isoSub E mu) hXst
  have hle : nMinus E ≤ (cr_WS E (cr_Low mu) ⊓ isoSub E mu) ⊔ X' := by
    unfold nMinus
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ isoSub E mu ⊔ X' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup ⟨cr_lower E hE.1 mu a b hab (hXle hp), hXst a b p hp⟩ (hX' a b q hq)
  obtain ⟨s, hs, x', hx', hsum⟩ := Submodule.mem_sup.1 (hle hn)
  have hx'X : x' ∈ isoSub E mu := by
    have h := (isoSub E mu).sub_mem hyX hs.2
    rwa [← hsum, add_sub_cancel_left] at h
  have hx0 : x' = 0 := Submodule.disjoint_def.1 hc.disjoint x' hx'X hx'
  rw [hx0, add_zero] at hsum
  have hmem := cr_WS_mem E (hsum ▸ hs.1) hy hne
  have h0 := hmem.2
  simp [weightHeight'] at h0

def SimpleRaisingKillsExtremalProjector : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ mu : Fin n → ℤ,
      (∀ a b : Fin n, a < b → 1 ≤ mu a - mu b + ((b : ℤ) - (a : ℤ))) →
      ∀ ord, NormalOrder n ord → ∀ T : ℕ, Module.finrank K V ≤ T →
        ∀ x ∈ weightSp E mu, ∀ a b : Fin n, a.val + 1 = b.val → E a b (pp E mu ord T x) = 0

private theorem operatorsShiftWeightsByRoots_of_isGLRep {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) : OperatorsShiftWeightsByRoots E := by
  have h1y : ∀ y : V, (1 : Module.End K V) y = y := fun _ => rfl
  intro a b ν x hx
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, h1y, sub_eq_zero] at hx ⊢
  intro c
  have claim : ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x =
      ((rootW a b c : ℤ) : K) • E a b x := by
    by_cases h1 : c = a <;> by_cases h2 : b = c
    · subst h1; subst h2; simp [rootW]
    · subst h1; simp [rootW, h2, Ne.symm h2]
    · subst h2; simp [rootW, h1]
    · simp [rootW, h1, h2, Ne.symm h1, Ne.symm h2]
  have hc : E c c (E a b x) - E a b (E c c x) =
      ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x :=
    LinearMap.congr_fun (hE.1 c c a b) x
  rw [hx c, map_smul, claim, sub_eq_iff_eq_add] at hc
  rw [hc, Pi.add_apply, Int.cast_add, add_smul]
  exact add_comm _ _

theorem sizes_bound_of_log_estimates (D : Formalism.BasicNotions.D7) (h : SimpleRaisingKillsExtremalProjector) : adm5 D := by
  intro K V _ _ _ _ _ n E hE mu hmu ord hord T hT
  have hs : OperatorsShiftWeightsByRoots E := operatorsShiftWeightsByRoots_of_isGLRep E hE
  have hlt : ∀ ab ∈ ord, ab.1 < ab.2 := by
    unfold NormalOrder at hord
    exact hord.2.1
  have hwt : ∀ x ∈ weightSp E mu, pp E mu ord T x ∈ weightSp E mu :=
    fun x hx => extremal_projector_preserves_weight hs mu mu ord T x hx
  refine ⟨hwt, ?_, ?_⟩
  · intro x hx hn
    have hsimple : ∀ a b : Fin n, a.val + 1 = b.val → E a b (pp E mu ord T x) = 0 :=
      h K V n E hE mu hmu ord hord T hT x hx
    have hall : ∀ a b : Fin n, a < b → E a b (pp E mu ord T x) = 0 := by
      intro a b hab
      have hab' : a.val < b.val := hab
      exact simple_raising_kill_all_raising hE _ hsimple (b.val - a.val - 1) a b (by omega)
    have hyn : pp E mu ord T x ∈ nMinus E := by
      have h2 := Submodule.add_mem _ (extremal_projector_sub_mem_nMinus E mu ord T x hlt) hn
      rwa [sub_add_cancel] at h2
    exact hwv_mem_nMinus_eq_zero D E hE mu _ (hwt x hx) hall hyn
  · intro x hx hr
    exact extremal_projector_fixes_hwv E mu ord T x (fun ab hab => hr ab.1 ab.2 (hlt ab hab))

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.HeisenbergDividedPowerExpansion
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem weighted_sum_shift_recombine {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (c c' r : ℕ → K) (B : ℕ → M) (k : ℕ)
    (h0 : c' 0 = c 0) (hs : ∀ j, j < k + 1 → c' (j + 1) = c (j + 1) + c j * r j) (hz : c (k + 1) = 0) :
    ∑ j ∈ range (k + 1), c j • (B j + r j • B (j + 1)) = ∑ j ∈ range (k + 2), c' j • B j := by
  rw [Finset.sum_range_succ' (fun j => c' j • B j), h0]
  have e1 : ∑ j ∈ range (k + 1), c' (j + 1) • B (j + 1) =
      ∑ j ∈ range (k + 1), (c (j + 1) • B (j + 1) + (c j * r j) • B (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j (Finset.mem_range.mp hj), add_smul]
  rw [e1, Finset.sum_add_distrib]
  have e2 : ∑ j ∈ range (k + 1), c j • (B j + r j • B (j + 1)) =
      ∑ j ∈ range (k + 1), c j • B j + ∑ j ∈ range (k + 1), (c j * r j) • B (j + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_add, smul_smul]
  rw [e2]
  have e3 : ∑ j ∈ range (k + 1), c j • B j =
      c 0 • B 0 + ∑ j ∈ range (k + 1), c (j + 1) • B (j + 1) := by
    rw [Finset.sum_range_succ (fun j => c (j + 1) • B (j + 1)), hz, zero_smul, add_zero,
      Finset.sum_range_succ' (fun j => c j • B j)]
    abel
  rw [e3]
  abel

section Heisenberg₂

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

theorem heisenberg_mul_pow_commutator {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (m : ℕ) :
    X * Y ^ m = Y ^ m * X + (m : K) • (Y ^ (m - 1) * Z) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : X * Y ^ (m + 1) = (X * Y ^ m) * Y := by rw [pow_succ, mul_assoc]
    have e2 : Y ^ (m - 1) * Z * Y = Y ^ (m - 1) * Y * Z := by rw [mul_assoc, hZY, ← mul_assoc]
    rw [e1, ih, add_mul, mul_assoc (Y ^ m) X Y, hZ, smul_mul_assoc, e2, mul_add, ← mul_assoc, ← pow_succ]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← pow_succ, Nat.sub_add_cancel hm]
      simp only [Nat.add_sub_cancel, Nat.cast_succ, add_smul, one_smul]
      abel

theorem heisenberg_pow_mul_pow_expansion {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (hZX : X * Z = Z * X) (k l : ℕ) :
    X ^ k * Y ^ l = ∑ j ∈ range (k + 1),
      (((k.choose j * l.descFactorial j : ℕ) : K)) • (Y ^ (l - j) * Z ^ j * X ^ (k - j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : ∀ j : ℕ, Commute X (Z ^ j) := fun j => Commute.pow_right (show Commute X Z from hZX) j
    have step : ∀ j ∈ range (k + 1),
        X * ((((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k - j))) =
        (((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j) +
          (((l - j : ℕ)) : K) • (Y ^ (l - (j + 1)) * Z ^ (j + 1) * X ^ (k + 1 - (j + 1)))) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_smul_comm]
      congr 1
      rw [← mul_assoc, ← mul_assoc, heisenberg_mul_pow_commutator (K := K) hZ hZY (l - j), add_mul, add_mul,
        smul_mul_assoc, smul_mul_assoc]
      congr 1
      · simp only [mul_assoc]
        rw [← mul_assoc X (Z ^ j), (hc j).eq, mul_assoc (Z ^ j), ← pow_succ',
          show k - j + 1 = k + 1 - j by omega]
      · congr 1
        rw [show l - (j + 1) = l - j - 1 by omega, show k + 1 - (j + 1) = k - j by omega,
          mul_assoc (Y ^ (l - j - 1)) Z, ← pow_succ']
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum, Finset.sum_congr rfl step]
    exact weighted_sum_shift_recombine (fun j => ((k.choose j * l.descFactorial j : ℕ) : K))
      (fun j => (((k + 1).choose j * l.descFactorial j : ℕ) : K)) (fun j => ((l - j : ℕ) : K))
      (fun j => Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j)) k (by simp)
      (fun j _ => by
        have e : (k + 1).choose (j + 1) * l.descFactorial (j + 1) =
            k.choose (j + 1) * l.descFactorial (j + 1) + k.choose j * l.descFactorial j * (l - j) := by
          rw [Nat.choose_succ_succ, Nat.descFactorial_succ]; ring
        rw [e]
        push_cast
        ring)
      (by simp [Nat.choose_succ_self])

def dividedPower (K : Type*) [Field K] {A : Type*} [Ring A] [Algebra K A] (X : A) (k : ℕ) : A := ((k.factorial : K)⁻¹) • X ^ k

theorem heisenberg_dividedPower_expansion {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (hZX : X * Z = Z * X) (k l : ℕ) :
    dividedPower K X k * dividedPower K Y l = ∑ j ∈ range (k + 1),
      if j ≤ l then dividedPower K Y (l - j) * dividedPower K Z j * dividedPower K X (k - j) else 0 := by
  unfold dividedPower
  rw [smul_mul_smul_comm, heisenberg_pow_mul_pow_expansion (K := K) hZ hZY hZX, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  split_ifs with hjl
  · rw [smul_smul, smul_mul_smul_comm, smul_mul_smul_comm]
    congr 1
    have h1 : ((k.factorial : ℕ) : K) = (k.choose j : K) * j.factorial * (k - j).factorial := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
    have h2 : ((l.factorial : ℕ) : K) = ((l - j).factorial : K) * l.descFactorial j := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hjl).symm
    have h3 : (k.choose j : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
    have h4 : (l.descFactorial j : K) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
    have h5 : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h6 : ((k - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h7 : ((l - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [h1, h2]
    push_cast
    field_simp
  · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

end Heisenberg₂

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.SchurInvariantProjectionTrace
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem exists_equivariant_cyclic_to_hwv (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (lam : Fin n → ℤ)
    (v0 v : V) (hv0 : IsHWV E lam v0) (hv : IsHWV E lam v) (hL : IsSubrepresentation E (cyclicSubmodule E v0)) :
    ∃ φ : cyclicSubmodule E v0 →ₗ[K] V, IsEquivariantMap (restrictRepresentation E _ hL) E φ ∧ φ ⟨v0, self_mem_cyclicSubmodule E v0⟩ = v := by
  have hP := prodRepresentation_isRep E E hE hE
  have hg : IsHWV (prodRepresentation E E) lam (v0, v) := by
    refine ⟨fun h => hv0.1 (congrArg Prod.fst h), (prod_mem_weightSpace_iff E E lam _).2 ⟨hv0.2.1, hv.2.1⟩, fun a b hab => ?_⟩
    rw [prodRepresentation_apply, hv0.2.2 a b hab, hv.2.2 a b hab]; rfl
  have hΓ := cyclicSubmodule_isSubrepresentation (prodRepresentation E E) (v0, v)
  have hEΓ := restrictRepresentation_isRep (prodRepresentation E E) hP _ hΓ
  have hg' := highest_vector_restrict (prodRepresentation E E) _ hΓ lam (v0, v) (self_mem_cyclicSubmodule _ _) hg
  have hcyc := cyclicSubmodule_restrict_eq_top (prodRepresentation E E) (v0, v) hΓ
  let F : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.fst K V V) ∘ₗ (Submodule.subtype _)
  let S2 : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.snd K V V) ∘ₗ (Submodule.subtype _)
  have hF : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E F := fun a b x => rfl
  have hS : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E S2 := fun a b x => rfl
  have hker := equivariant_injective_of_cyclic D h2 _ hEΓ E lam _ hg' hcyc F hF hv0.1
  have hinj : Function.Injective F := LinearMap.ker_eq_bot.1 hker
  have hrange : LinearMap.range F = cyclicSubmodule E v0 := by
    have := equivariant_map_cyclicSubmodule _ E F hF ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩
    rw [hcyc, Submodule.map_top] at this
    exact this
  have hmem : ∀ z, F z ∈ cyclicSubmodule E v0 := fun z => by rw [← hrange]; exact ⟨z, rfl⟩
  let e : cyclicSubmodule (prodRepresentation E E) (v0, v) ≃ₗ[K] cyclicSubmodule E v0 :=
    LinearEquiv.ofBijective (F.codRestrict _ hmem)
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => by
        have hy : (y : V) ∈ LinearMap.range F := by rw [hrange]; exact y.2
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, Subtype.ext hz⟩⟩
  have he : ∀ z, ((e z : cyclicSubmodule E v0) : V) = F z := fun z => rfl
  refine ⟨S2 ∘ₗ e.symm.toLinearMap, fun a b y => ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := e.surjective y
    have h1 : restrictRepresentation E _ hL a b (e z) = e (restrictRepresentation (prodRepresentation E E) _ hΓ a b z) := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply, e.symm_apply_apply]
    exact hS a b z
  · have h1 : (⟨v0, self_mem_cyclicSubmodule E v0⟩ : cyclicSubmodule E v0) = e ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩ := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply]
    rfl

def trivialRepresentation (n : ℕ) (K : Type) [Field K] : GLOps n K K := fun _ _ => 0

theorem trivialRepresentation_isRep (n : ℕ) (K : Type) [Field K] : IsGLRep (trivialRepresentation n K) := by
  refine ⟨?_, fun x => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩, ?_⟩
  · intro a b c d
    simp only [trivialRepresentation]
    split_ifs <;> simp
  · rw [eq_top_iff]
    intro x _
    exact Submodule.mem_iSup_of_mem 0 ((mem_weightSp_iff_diagonal_apply _ _ _).2 fun a => by simp [trivialRepresentation])

theorem trivialRep_invariant_projection (n : ℕ) (K : Type) [Field K] [CharZero K] : IsInvProj (trivialRepresentation n K) 1 := by
  refine ⟨fun x _ => rfl, fun mu hmu x hx => ?_⟩
  have hle : isoSub (trivialRepresentation n K) mu ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, _, v, hv, _⟩
    exfalso
    obtain ⟨i, hi⟩ : ∃ i, mu i ≠ 0 := by
      by_contra hcon
      exact hmu (funext fun i => by_contra fun h => hcon ⟨i, h⟩)
    have h1 := (mem_weightSp_iff_diagonal_apply _ mu v).1 hv.2.1 i
    simp only [trivialRepresentation, LinearMap.zero_apply] at h1
    rcases smul_eq_zero.1 h1.symm with h | h
    · exact hi (by exact_mod_cast h)
    · exact hv.1 h
  have := hle hx
  rw [Submodule.mem_bot] at this
  rw [this, map_zero]

theorem invariant_projection_equivariant (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V V' : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (E : GLOps n K V) (E' : GLOps n K V') (hE : IsGLRep E) (hE' : IsGLRep E')
    (P : Module.End K (V →ₗ[K] V')) (hP : IsInvProj (homRepresentation E E') P) (g : V →ₗ[K] V') : IsEquivariantMap E E' (P g) := by
  intro a b x
  have h := congrArg (fun f : V →ₗ[K] V' => f x)
    (invariant_projection_kills_operators D h2 n K _ (homRepresentation E E') (homRepresentation_isRep E E' hE hE') P hP g a b)
  simp only [homRepresentation_apply, LinearMap.zero_apply] at h
  exact (sub_eq_zero.1 h).symm

theorem schur_invariant_projection_trace (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K L : Type} [Field K] [CharZero K]
    [AddCommGroup L] [Module K L] [FiniteDimensional K L] (EL : GLOps n K L) (hEL : IsGLRep EL) (lam : Fin n → ℤ)
    (v0 : L) (hv0 : IsHWV EL lam v0) (hcyc : cyclicSubmodule EL v0 = ⊤)
    (P0 : Module.End K (L →ₗ[K] L)) (hP0 : IsInvProj (homRepresentation EL EL) P0) (g : L →ₗ[K] L) :
    (Module.finrank K L : K) • P0 g = (LinearMap.trace K L g) • (LinearMap.id : L →ₗ[K] L) := by
  have hψ := invariant_projection_equivariant D h2 EL EL hEL hEL P0 hP0 g
  have hw : P0 g v0 ∈ weightSp EL lam := by
    rw [mem_weightSp_iff_diagonal_apply]
    intro a
    rw [← hψ, (mem_weightSp_iff_diagonal_apply EL lam v0).1 hv0.2.1 a, map_smul]
  obtain ⟨c, hc⟩ := cyclic_highest_weightSpace_line EL hEL lam v0 hv0 (P0 g v0) (by rw [hcyc]; trivial) hw
  have hid : P0 g = c • (LinearMap.id : L →ₗ[K] L) := by
    have hT : IsEquivariantMap EL EL (P0 g - c • (LinearMap.id : L →ₗ[K] L)) := by
      intro a b x
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
      rw [hψ]
    have h0 : (P0 g - c • (LinearMap.id : L →ₗ[K] L)) v0 = 0 := by
      simp [hc]
    ext x
    have := equivariant_kills_cyclic_of_zero EL EL _ hT v0 h0 x (by rw [hcyc]; trivial)
    exact sub_eq_zero.1 this
  have htr : IsEquivariantMap (homRepresentation EL EL) (trivialRepresentation n K) (LinearMap.trace K L) := by
    intro a b f
    have : homRepresentation EL EL a b f = EL a b * f - f * EL a b := by
      ext x; simp
    rw [this, map_sub, LinearMap.trace_mul_comm, sub_self]
    rfl
  have h3 := equivariant_commutes_isotypic D h2 n K _ K (homRepresentation EL EL) (trivialRepresentation n K) (homRepresentation_isRep EL EL hEL hEL)
    (trivialRepresentation_isRep n K) (LinearMap.trace K L) htr P0 1 hP0 (trivialRep_invariant_projection n K) g
  rw [Module.End.one_apply, hid, map_smul, LinearMap.trace_id, smul_eq_mul] at h3
  rw [hid, smul_smul, ← h3, mul_comm]

end Formalism.MainNotions.G.GLWeightTheory
end
end

