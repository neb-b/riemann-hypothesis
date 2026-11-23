module

public import Formalism.PieriBlockIdeals.Bundle0006
public import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.PathEqOfContentSequence
section
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lca_content_lt {q : ℕ} (κ : Fin q → ℕ) (h : Antitone κ) {a b : Fin q} (hab : a < b) :
    (κ b : ℤ) - (b.val : ℤ) < (κ a : ℤ) - (a.val : ℤ) := by
  have h1 : κ b ≤ κ a := h hab.le
  have h2 : a.val < b.val := hab
  omega

theorem lca_content_inj {q : ℕ} (κ : Fin q → ℕ) (h : Antitone κ) {a b : Fin q}
    (e : (κ a : ℤ) - (a.val : ℤ) = (κ b : ℤ) - (b.val : ℤ)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lca_content_lt κ h hab; omega
  · exact hab
  · have := lca_content_lt κ h hab; omega

theorem path_eq_of_content_sequence {q n : ℕ} {lam2 tau tau' : Fin q → ℕ} {κ κ' : ℕ → Fin q → ℕ} {ρ ρ' : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (H' : IsPath n lam2 tau' κ' ρ') (m : ℕ) (hm : m ≤ n)
    (hc : ∀ j : Fin n, j.val < m → cseq κ ρ j = cseq κ' ρ' j) : ∀ l ≤ m, κ l = κ' l := by
  intro l
  induction l with
  | zero => intro _; rw [H.start, H'.start]
  | succ l ih =>
    intro hl
    have e := ih (by omega)
    have hln : l < n := by omega
    have h1 := hc ⟨l, hln⟩ (by show l < m; omega)
    have h2 := H.step ⟨l, hln⟩
    have h3 := H'.step ⟨l, hln⟩
    dsimp only [cseq] at h1 h2 h3
    rw [← e] at h1 h3
    have h4 : ρ ⟨l, hln⟩ = ρ' ⟨l, hln⟩ := lca_content_inj (κ l) (H.dom l (by omega)) h1
    rw [h2, h3, h4]

theorem lca_single_ne {q : ℕ} {r a : Fin q} (h : a ≠ r) (A : Fin q → ℕ) :
    (A + Pi.single r 1 : Fin q → ℕ) a = A a := by
  simp [Pi.single_apply, h]

theorem lca_single_eq {q : ℕ} (r : Fin q) (A : Fin q → ℕ) :
    (A + Pi.single r 1 : Fin q → ℕ) r = A r + 1 := by simp

theorem lca_rows_lt {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (hle : colSeq κ ρ j' ≤ colSeq κ ρ j) :
    ρ j < ρ j' ∧ colSeq κ ρ j' = κ j.val (ρ j') := by
  have hjn := j'.isLt
  have s1 := H.step j
  have d1 := H.dom (j.val + 1) (by omega)
  have hle' : κ (j.val + 1) (ρ j') ≤ κ j.val (ρ j) := by
    have := hle; unfold colSeq at this; rwa [hv] at this
  have hlt : ρ j < ρ j' := by
    by_contra hcon
    have hcon : ρ j' ≤ ρ j := not_lt.mp hcon
    have h3 := d1 hcon
    rw [s1] at h3 hle'
    rw [lca_single_eq] at h3
    omega
  refine ⟨hlt, ?_⟩
  unfold colSeq; rw [hv, s1, lca_single_ne hlt.ne']

theorem lca_swap {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (hlt : colSeq κ ρ j' < colSeq κ ρ j) :
    2 ≤ cseq κ ρ j - cseq κ ρ j' ∧
      ∃ κ' : ℕ → Fin q → ℕ, IsPath n lam2 tau κ' (ρ ∘ Equiv.swap j j') ∧
        cseq κ' (ρ ∘ Equiv.swap j j') = cseq κ ρ ∘ Equiv.swap j j' ∧
        colSeq κ' (ρ ∘ Equiv.swap j j') = colSeq κ ρ ∘ Equiv.swap j j' := by
  obtain ⟨hr, hc⟩ := lca_rows_lt H j j' hv hlt.le
  have hjn := j'.isLt
  have s1 := H.step j
  have s2 := H.step j'
  rw [hv] at s2
  have d0 := H.dom j.val (by omega)
  have d2 := H.dom (j.val + 1 + 1) (by omega)
  have hA : κ j.val (ρ j') < κ j.val (ρ j) := by rw [← hc]; exact hlt
  have hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ) := by
    have := hc; unfold colSeq at this; unfold cseq; rw [this]
  have hr' : (ρ j).val < (ρ j').val := hr
  refine ⟨by rw [hc']; unfold cseq; omega, ?_⟩
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℕ → Fin q → ℕ,
      ∀ l, κ' l = if l = j.val + 1 then κ j.val + Pi.single (ρ j') 1 else κ l := ⟨_, fun _ => rfl⟩
  have k1 : κ' (j.val + 1) = κ j.val + Pi.single (ρ j') 1 := by rw [hκ', if_pos rfl]
  have k2 : ∀ l, l ≠ j.val + 1 → κ' l = κ l := fun l h => by rw [hκ', if_neg h]
  have anti : Antitone (κ j.val + Pi.single (ρ j') 1) := by
    intro a b hab
    by_cases hb : b = ρ j'
    · by_cases ha : a = ρ j'
      · rw [ha, hb]
      · rw [hb, lca_single_eq, lca_single_ne ha]
        have hab' : a < ρ j' := lt_of_le_of_ne (hb ▸ hab) ha
        by_cases har : a ≤ ρ j
        · have := d0 har; omega
        · have har : ρ j < a := not_le.mp har
          have h5 := d2 hab'.le
          rw [s2, s1] at h5
          rw [lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha, lca_single_ne har.ne'] at h5
          exact h5
    · rw [lca_single_ne hb]
      calc κ j.val b ≤ κ j.val a := d0 hab
        _ ≤ (κ j.val + Pi.single (ρ j') 1 : Fin q → ℕ) a := by simp [Pi.add_apply]
  have hcol : colSeq κ' (ρ ∘ Equiv.swap j j') = colSeq κ ρ ∘ Equiv.swap j j' := by
    funext l
    by_cases h1 : l = j
    · rw [h1]
      simp only [colSeq, Function.comp, Equiv.swap_apply_left]
      rw [k2 j.val (by omega), hv, s1, lca_single_ne hr.ne']
    · by_cases h2 : l = j'
      · rw [h2]
        simp only [colSeq, Function.comp, Equiv.swap_apply_right]
        rw [hv, k1, lca_single_ne hr.ne]
      · have h4 : l.val ≠ j.val + 1 := fun h => h2 (Fin.ext (h.trans hv.symm))
        simp only [colSeq, Function.comp]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ h4]
  refine ⟨κ', ⟨?_, ?_, ?_, ?_⟩, ?_, hcol⟩
  · rw [k2 0 (by omega), H.start]
  · intro l
    by_cases h1 : l = j
    · rw [h1]
      simp only [Function.comp, Equiv.swap_apply_left]
      rw [k1, k2 j.val (by omega)]
    · by_cases h2 : l = j'
      · rw [h2]
        simp only [Function.comp, Equiv.swap_apply_right]
        rw [hv, k1, k2 (j.val + 1 + 1) (by omega), s2, s1]
        exact add_right_comm _ _ _
      · have h3 : l.val ≠ j.val := fun h => h1 (Fin.ext h)
        have h4 : l.val ≠ j.val + 1 := fun h => h2 (Fin.ext (h.trans hv.symm))
        simp only [Function.comp]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ (by omega), k2 _ h4]
        exact H.step l
  · rw [k2 n (by omega), H.stop]
  · intro l hl
    by_cases h : l = j.val + 1
    · rw [h, k1]; exact anti
    · rw [k2 l h]; exact H.dom l hl
  · funext l
    have := congrFun hcol l
    simp only [colSeq, cseq, Function.comp] at this ⊢
    rw [this]

theorem swap_path_exists : SwapPath := by
  intro q n lam2 tau κ ρ H j hj hlt
  exact lca_swap H j ⟨j.val + 1, hj⟩ rfl hlt

theorem lca_same {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (heq : colSeq κ ρ j' = colSeq κ ρ j) :
    cseq κ ρ j' = cseq κ ρ j - 1 ∧ ¬ IsContentSeq lam2 (cseq κ ρ ∘ Equiv.swap j j') := by
  obtain ⟨hr, hc⟩ := lca_rows_lt H j j' hv heq.le
  have hjn := j'.isLt
  have s1 := H.step j
  have s2 := H.step j'
  rw [hv] at s2
  have d0 := H.dom j.val (by omega)
  have d2 := H.dom (j.val + 1 + 1) (by omega)
  have hA : κ j.val (ρ j') = κ j.val (ρ j) := by rw [← hc]; exact heq
  have hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ) := by
    have := hc; unfold colSeq at this; unfold cseq; rw [this]
  have hr' : (ρ j).val < (ρ j').val := hr
  constructor
  · have hrow : (ρ j').val = (ρ j).val + 1 := by
      by_contra hcon
      have hq := (ρ j').isLt
      obtain ⟨a, ha⟩ : ∃ a : Fin q, a.val = (ρ j).val + 1 := ⟨⟨(ρ j).val + 1, by omega⟩, rfl⟩
      have ha1 : ρ j < a := by show (ρ j).val < a.val; omega
      have ha2 : a < ρ j' := by show a.val < (ρ j').val; omega
      have h5 := d2 ha2.le
      rw [s2, s1] at h5
      rw [lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha2.ne, lca_single_ne ha1.ne'] at h5
      have h6 := d0 ha1.le
      omega
    rw [hc']; unfold cseq; omega
  · rintro ⟨tau', κ', ρ', H', hcs⟩
    have hpre : ∀ i : Fin n, i.val < j.val → cseq κ ρ i = cseq κ' ρ' i := by
      intro i hi
      have h := congrFun hcs i
      have h1 : i ≠ j := fun h => by rw [h] at hi; omega
      have h2 : i ≠ j' := fun h => by rw [h] at hi; omega
      simp only [Function.comp] at h
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at h
      exact h.symm
    have e : κ j.val = κ' j.val := path_eq_of_content_sequence H H' j.val (by omega) hpre j.val le_rfl
    have h1 := congrFun hcs j
    simp only [Function.comp, Equiv.swap_apply_left] at h1
    rw [hc'] at h1
    unfold cseq at h1
    rw [← e] at h1
    have h2 : ρ' j = ρ j' := lca_content_inj _ d0 h1
    have h3 := H'.dom (j.val + 1) (by omega) hr.le
    rw [H'.step j, ← e, h2, lca_single_eq, lca_single_ne hr.ne] at h3
    omega

theorem same_column : SameCol := by
  intro q n lam2 tau κ ρ H j hj heq
  exact lca_same H j ⟨j.val + 1, hj⟩ rfl heq

end Formalism.CohomologicalDescent.LC
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.PermutationWeightInvariant
section
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lc_c_filter_succ {A : Type*} [AddCommMonoid A] {n : ℕ} (f : Fin n → A) (l : ℕ) (hl : l < n) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l + 1), f i =
      f ⟨l, hl⟩ + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), f i := by
  have hfil : (Finset.univ.filter (fun i : Fin n => i.val < l + 1)) =
      insert (⟨l, hl⟩ : Fin n) (Finset.univ.filter (fun i : Fin n => i.val < l)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hfil, Finset.sum_insert (by simp)]

theorem lc_c_filter_zero {A : Type*} [AddCommMonoid A] {n : ℕ} (f : Fin n → A) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < 0), f i = 0 := by
  have : (Finset.univ.filter (fun i : Fin n => i.val < 0)) = ∅ := by
    ext i; simp
  rw [this, Finset.sum_empty]

theorem lc_c_casVal_step {q : ℕ} (κ : Fin q → ℕ) (r : Fin q) :
    casVal (κ + Pi.single r 1) - casVal κ - (q : ℤ) = 2 * ((κ r : ℤ) - (r.val : ℤ)) := by
  have h2 := casimir_content_holds q (fun b => (κ b : ℤ)) r
  unfold casVal
  simp only [Pi.add_apply, Pi.single_apply, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact h2

theorem lc_c_casVal_path {q n : ℕ} (lam2 : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q) (h0 : κ 0 = lam2)
    (hs : ∀ j : Fin n, κ (j.val + 1) = κ j.val + Pi.single (ρ j) 1) : ∀ l ≤ n,
    casVal (κ l) = casVal lam2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), (2 * cseq κ ρ i + (q : ℤ)) := by
  intro l
  induction l with
  | zero => intro _; rw [lc_c_filter_zero, add_zero, h0]
  | succ l ih =>
    intro hl
    have hl' : l < n := hl
    rw [lc_c_filter_succ _ l hl']
    have h1 := lc_c_casVal_step (κ l) (ρ ⟨l, hl'⟩)
    have h2 := hs ⟨l, hl'⟩
    simp only at h2
    rw [← h2] at h1
    have h3 := ih hl'.le
    simp only [cseq] at h3 ⊢
    linarith

theorem lc_c_eig {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {A T : Module.End K V} (h : Commute T A)
    {z : V} {a : K} (hz : A z = a • z) : A (T z) = a • T z := by
  have := LinearMap.congr_fun h.eq z
  simp only [Module.End.mul_apply] at this
  rw [← this, hz, map_smul]

theorem lc_c_Dpart0 {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P]
    {n : ℕ} (EM : R → R → Module.End k M) (b b' : R) :
    (Dpart k EM 0 b b' : Module.End k (Tens R P M n)) = onM k (EM b b') := by
  simp [Dpart]

theorem commute_casimir_zero {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P]
    [Fintype R] {n : ℕ} (EM : R → R → Module.End k M) (T : Module.End k (Tens R P M n))
    (h0 : ∀ a b, Commute T (onM k (EM a b))) : Commute T (Cas k EM 0) := by
  unfold Cas
  simp only [lc_c_Dpart0]
  exact Commute.sum_right _ _ _ fun b _ => Commute.sum_right _ _ _ fun b' _ => (h0 _ _).mul_right (h0 _ _)

theorem casimir_from_x : CasFromX := by
  intro K P M q _ _ _ _ EM n lam2 c z hz l
  induction l with
  | zero =>
    intro _
    rw [lc_c_filter_zero, add_zero]
    exact hz.1
  | succ l ih =>
    intro hl
    have hl' : l < n := hl
    have h1 := congrArg (fun T : Module.End K (Tens (Fin q) P M n) => T z)
      (casimir_jucys_murphy_holds K (Fin q) P M EM n ⟨l, hl'⟩)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      Fintype.card_fin] at h1
    rw [lc_c_filter_succ _ l hl']
    rw [ih hl'.le, hz.2 ⟨l, hl'⟩, ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, smul_smul, ← add_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem weight_iff_condition : WtIff := by
  intro K P M q _ _ _ _ _ EM n lam2 κ ρ h0 hs z
  constructor
  · intro hz
    refine ⟨?_, fun j => ?_⟩
    · have := hz 0 (Nat.zero_le _)
      rwa [h0] at this
    · exact (path_eigen_holds K P M q EM n κ ρ hs z hz).1 j
  · intro hz j hj
    rw [casimir_from_x K P M q EM n lam2 _ z hz j hj, lc_c_casVal_path lam2 κ ρ h0 hs j hj]

theorem permutation_weight_invariant : PermXWt := by
  intro K P M q _ _ _ _ EM n lam2 c z σ hz
  refine ⟨?_, fun j => ?_⟩
  · exact lc_c_eig (commute_casimir_zero EM _ fun a b => permFirst_commute_onModule K σ _) hz.1
  · exact lc_c_eig (commute_jucysMurphy_of_commute K EM _ (fun a b => permFirst_commute_onModule K σ _)
      (fun i a b => permFirst_commute_unitSecond K σ i a b) j) (hz.2 j)

theorem to_symmetric_y_x : ToSymYX := by
  intro K R P M _ _ _ _ _ _ _ n σ z
  rw [← toSym_perm_eq (k := K) (permX K σ⁻¹ z) σ]
  congr 1
  funext g
  simp [permTensor_apply_comp, permFirst_apply, permSecond_apply]

theorem lc_c_ss {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ} (a b : Fin n) :
    (permY k (Equiv.swap a b) * permY k (Equiv.swap a b) : Module.End k (Tens R P M n)) = 1 := by
  rw [← permOnTensor_mul, Equiv.swap_mul_self, permSecond_one]

theorem exchange' : Exchange := by
  intro K P M q _ _ _ _ _ EM n lam2 c z j hj hz hne
  set j' : Fin n := ⟨j.val + 1, hj⟩ with hj'
  set s : Module.End K (Tens (Fin q) P M n) := permY K (Equiv.swap j j') with hs
  have hH := hecke_relations_hold K (Fin q) P M EM n j hj
  have h1 : s * xJM K EM j = xJM K EM j' * s - 1 := hH.1
  have hss : s * s = 1 := lc_c_ss j j'
  have h2 : xJM K EM j * s = s * xJM K EM j' - 1 := by
    calc xJM K EM j * s = (s * s) * xJM K EM j * s := by rw [hss, one_mul]
      _ = s * (s * xJM K EM j) * s := by simp only [mul_assoc]
      _ = s * (xJM K EM j' * s - 1) * s := by rw [h1]
      _ = s * xJM K EM j' * (s * s) - s * s := by noncomm_ring
      _ = s * xJM K EM j' - 1 := by rw [hss, mul_one]
  have e1 : xJM K EM j' (s z) = ((c j : ℤ) : K) • s z + z := by
    have := LinearMap.congr_fun h1 z
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this
    rw [hz.2 j, map_smul] at this
    rw [this]; abel
  have e2 : xJM K EM j (s z) = ((c j' : ℤ) : K) • s z - z := by
    have := LinearMap.congr_fun h2 z
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this
    rw [hz.2 j', map_smul] at this
    exact this
  have hd : (((c j - c j' : ℤ) : ℤ) : K) ≠ 0 := Int.cast_ne_zero.2 (sub_ne_zero.2 hne)
  set b : K := (((c j - c j' : ℤ) : ℤ) : K)⁻¹ with hbdef
  have hb : b * (((c j : ℤ) : K) - ((c j' : ℤ) : K)) = 1 := by
    rw [← Int.cast_sub]; exact inv_mul_cancel₀ hd
  have hjj' : j ≠ j' := by
    intro e; have := congrArg Fin.val e; simp [hj'] at this
  refine ⟨?_, fun l => ?_⟩
  · rw [map_add (f := _), map_smul, hz.1, lc_c_eig (commute_casimir_zero EM s fun a b => permSecond_commute_onModule K _ _) hz.1]
    module
  · by_cases hl : l = j
    · subst hl
      rw [Function.comp_apply, Equiv.swap_apply_left, map_add (f := _), map_smul, e2, hz.2 l]
      have e : b * ((c l : ℤ) : K) - 1 = ((c j' : ℤ) : K) * b := by linear_combination hb
      calc _ = ((c j' : ℤ) : K) • s z + (b * ((c l : ℤ) : K) - 1) • z := by module
        _ = _ := by rw [e]; module
    · by_cases hl' : l = j'
      · rw [hl', Function.comp_apply, Equiv.swap_apply_right, map_add (f := _), map_smul, e1, hz.2 j']
        have e : 1 + b * ((c j' : ℤ) : K) = ((c j : ℤ) : K) * b := by linear_combination (-1 : K) * hb
        calc _ = ((c j : ℤ) : K) • s z + (1 + b * ((c j' : ℤ) : K)) • z := by module
          _ = _ := by rw [e]; module
      · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hl hl', map_add (f := _), map_smul, hz.2 l,
          lc_c_eig (hH.2 l hl hl') (hz.2 l)]
        module

theorem good_swap_exists : GoodSwap := by
  intro K P M q _ _ _ _ _ _ EM n lam2 c j hj hd hgood z hz
  have hne : c j ≠ c ⟨j.val + 1, hj⟩ := by intro e; rw [e] at hd; omega
  have hz' := exchange' K P M q EM n lam2 c z j hj hz hne
  set j' : Fin n := ⟨j.val + 1, hj⟩ with hj'
  set s : Module.End K (Tens (Fin q) P M n) := permY K (Equiv.swap j j') with hs
  set b : K := (((c j - c j' : ℤ) : ℤ) : K)⁻¹ with hbdef
  set z' := s z + b • z with hz'def
  have hss : s * s = 1 := lc_c_ss j j'
  have t1 : toSym K z' = 0 := hgood z' hz'
  have t2 : toSym K (s z') = 0 := by
    rw [hs, to_symmetric_y_x K (Fin q) P M n (Equiv.swap j j') z']
    exact hgood _ (permutation_weight_invariant K P M q EM n lam2 _ z' _ hz')
  have hssz : s (s z) = z := by
    have := LinearMap.congr_fun hss z
    simpa using this
  have e : s z' - b • z' = (1 - b * b) • z := by
    rw [hz'def, map_add (f := _), map_smul, hssz]
    module
  have t3 : (1 - b * b) • toSym K z = 0 := by
    rw [← map_smul, ← e, map_sub, map_smul, t1, t2]; simp
  have hD : (((c j - c j' : ℤ) : ℤ) : K) ≠ 0 := Int.cast_ne_zero.2 (sub_ne_zero.2 hne)
  have hb : b * (((c j - c j' : ℤ) : ℤ) : K) = 1 := inv_mul_cancel₀ hD
  have hbb : 1 - b * b ≠ 0 := by
    intro h0
    have h1 : (((c j - c j' : ℤ) : ℤ) : K) * (((c j - c j' : ℤ) : ℤ) : K) = 1 := by
      linear_combination ((((c j - c j' : ℤ) : ℤ) : K) * (((c j - c j' : ℤ) : ℤ) : K)) * h0 +
        (b * (((c j - c j' : ℤ) : ℤ) : K) + 1) * hb
    have h2 : (c j - c j') * (c j - c j') = 1 := by exact_mod_cast h1
    nlinarith
  exact (smul_eq_zero.1 t3).resolve_left hbb

theorem NoWt_of (h : NoTuple) : NoWt := by
  intro K P M q _ _ _ _ _ EM n lam2 hp c z hz hc
  let TT : Set (Fin (n + 1) → K) := {t | ∃ (tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q),
    IsPath n lam2 tau κ ρ ∧ ∀ j : Fin (n + 1), t j = ((casVal (κ j.val) : ℤ) : K)}
  let E : Set (Tens (Fin q) P M n) := ⋃ tau : Fin q → ℕ, {z | ∃ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q),
    IsPath n lam2 tau κ ρ ∧ ∀ j ≤ n, Cas K EM j z = ((casVal (κ j) : ℤ) : K) • z}
  have hE : Submodule.span K E = ⊤ := by
    rw [← hp, Submodule.span_iUnion]; rfl
  let T0 : ℕ → ℤ := fun l => casVal lam2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), (2 * c i + (q : ℤ))
  refine h K (Tens (Fin q) P M n) (Fin (n + 1)) (fun j => Cas K EM j.val) TT E ?_ z (by rw [hE]; trivial)
    (fun j => ((T0 j.val : ℤ) : K)) ?_ ?_
  · intro e he
    obtain ⟨tau, κ, ρ, hpath, hcas⟩ := Set.mem_iUnion.1 he
    exact ⟨fun j => ((casVal (κ j.val) : ℤ) : K), ⟨tau, κ, ρ, hpath, fun _ => rfl⟩,
      fun j => hcas j.val (Nat.lt_succ_iff.1 j.2)⟩
  · rintro ⟨tau, κ, ρ, hpath, ht⟩
    apply hc
    refine ⟨tau, κ, ρ, hpath, ?_⟩
    have hT : ∀ l ≤ n, T0 l = casVal (κ l) := by
      intro l hl
      have : ((T0 l : ℤ) : K) = ((casVal (κ l) : ℤ) : K) := ht ⟨l, Nat.lt_succ_iff.2 hl⟩
      exact Int.cast_injective this
    funext i
    have a1 := hT i.val i.2.le
    have a2 := hT (i.val + 1) i.2
    rw [lc_c_casVal_path lam2 κ ρ hpath.start hpath.step _ i.2.le] at a1
    rw [lc_c_casVal_path lam2 κ ρ hpath.start hpath.step _ i.2] at a2
    simp only [T0] at a1 a2
    rw [lc_c_filter_succ _ i.val i.2, lc_c_filter_succ _ i.val i.2] at a2
    simp only [Fin.eta] at a2
    linarith
  · intro j
    exact casimir_from_x K P M q EM n lam2 c z hz j.val (Nat.lt_succ_iff.1 j.2)

theorem AntiStep_of (h : NoTuple) : AntiStep := by
  intro K P M q _ _ _ _ _ EM n lam2 hp c z j hj hz hc hn
  have hne : c j ≠ c ⟨j.val + 1, hj⟩ := by rw [hc]; omega
  have hz' := exchange' K P M q EM n lam2 c z j hj hz hne
  have h0 := NoWt_of h K P M q EM n lam2 hp _ _ hz' hn
  have h1 : c j - c ⟨j.val + 1, hj⟩ = 1 := by rw [hc]; ring
  rw [h1] at h0
  simp only [Int.cast_one, inv_one, one_smul] at h0
  exact eq_neg_of_add_eq_zero_left h0

end Formalism.CohomologicalDescent.LC
end

