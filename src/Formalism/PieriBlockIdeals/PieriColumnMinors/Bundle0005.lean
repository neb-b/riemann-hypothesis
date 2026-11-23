module

public import Formalism.PieriBlockIdeals.Bundle0006
public import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.AntitoneShapes
section
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lcb_transp {K R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] {n : ℕ} (i p : ℕ) (u : Tens R P M n)
    (h : ∀ (j : Fin n) (hj : j.val + 1 < n), i ≤ j.val → j.val < i + p →
      permY K (Equiv.swap j ⟨j.val + 1, hj⟩) u = - u) :
    ∀ (d : ℕ) (a b : Fin n), i ≤ a.val → b.val = a.val + d + 1 → b.val ≤ i + p →
      permY K (Equiv.swap a b) u = - u := by
  intro d
  induction d with
  | zero =>
    intro a b ha hb hbp
    have hj : a.val + 1 < n := by have := b.isLt; omega
    have hb' : b = ⟨a.val + 1, hj⟩ := Fin.ext (by simpa using hb)
    rw [hb']; exact h a hj ha (by omega)
  | succ d ih =>
    intro a b ha hb hbp
    have hc : a.val + d + 1 < n := by have := b.isLt; omega
    have hcb : (⟨a.val + d + 1, hc⟩ : Fin n).val + 1 < n := by have := b.isLt; simp only; omega
    have hb' : b = ⟨(⟨a.val + d + 1, hc⟩ : Fin n).val + 1, hcb⟩ := Fin.ext (by simp only; omega)
    have h1 : permY K (Equiv.swap a ⟨a.val + d + 1, hc⟩) u = - u := ih a ⟨a.val + d + 1, hc⟩ ha rfl (by simp only; omega)
    have h2 : permY K (Equiv.swap ⟨a.val + d + 1, hc⟩ b) u = - u := by
      rw [hb']; exact h ⟨a.val + d + 1, hc⟩ hcb (by simp only; omega) (by simp only; omega)
    have hac : a ≠ ⟨a.val + d + 1, hc⟩ := by
      intro e; have := congrArg Fin.val e; simp only at this; omega
    have hab : a ≠ b := by
      intro e; have := congrArg Fin.val e; omega
    have e : Equiv.swap a b = Equiv.swap ⟨a.val + d + 1, hc⟩ b * Equiv.swap a ⟨a.val + d + 1, hc⟩ *
        Equiv.swap ⟨a.val + d + 1, hc⟩ b := by
      rw [Equiv.swap_mul_swap_mul_swap hac hab, Equiv.swap_comm]
    rw [e, permOnTensor_mul, permOnTensor_mul]
    simp only [Module.End.mul_apply, h1, h2, map_neg, neg_neg]

theorem antitone_shapes : Anti := by
  intro K R P M _ _ _ _ _ _ _ _ n i hi u h
  classical
  have htr := lcb_transp (K := K) i (Fintype.card P) u h
  have hex : ∀ x : Fin n → P, ∃ ab : Fin n × Fin n, i ≤ ab.1.val ∧ ab.1.val < ab.2.val ∧
      ab.2.val ≤ i + Fintype.card P ∧ x ab.1 = x ab.2 := by
    intro x
    have hcard : Fintype.card P < Fintype.card (Fin (Fintype.card P + 1)) := by simp
    obtain ⟨s, t, hst, hx⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun s : Fin (Fintype.card P + 1) => x ⟨i + s.val, by have := s.isLt; omega⟩) hcard
    have hs := s.isLt
    have ht := t.isLt
    have hst' : s.val ≠ t.val := fun e => hst (Fin.ext e)
    rcases lt_or_gt_of_ne hst' with hlt | hlt
    · exact ⟨(⟨i + s.val, by omega⟩, ⟨i + t.val, by omega⟩), by simp only; omega, by simp only; omega,
        by simp only; omega, hx⟩
    · exact ⟨(⟨i + t.val, by omega⟩, ⟨i + s.val, by omega⟩), by simp only; omega, by simp only; omega,
        by simp only; omega, hx.symm⟩
  choose pr hpr using hex
  funext m
  rw [toSym_apply_sum_fiber]
  let xs : (Fin n → R × P) → Fin n → P := fun g s => (g s).2
  let inv : (Fin n → R × P) → (Fin n → R × P) := fun g => g ∘ Equiv.swap (pr (xs g)).1 (pr (xs g)).2
  have hxs : ∀ g, xs (inv g) = xs g := by
    intro g; funext s
    obtain ⟨_, _, _, h4⟩ := hpr (xs g)
    show (g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).2 = (g s).2
    by_cases hs1 : s = (pr (xs g)).1
    · rw [hs1, Equiv.swap_apply_left]; exact h4.symm
    · by_cases hs2 : s = (pr (xs g)).2
      · rw [hs2, Equiv.swap_apply_right]; exact h4
      · rw [Equiv.swap_apply_of_ne_of_ne hs1 hs2]
  have hu : ∀ g, u g + u (inv g) = 0 := by
    intro g
    obtain ⟨h1, h2, h3, h4⟩ := hpr (xs g)
    have key := congrFun (htr ((pr (xs g)).2.val - (pr (xs g)).1.val - 1) (pr (xs g)).1 (pr (xs g)).2 h1
      (by omega) h3) g
    rw [permSecond_apply] at key
    have e : (fun s => ((g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).1, (g s).2)) = inv g := by
      funext s
      have := congrFun (hxs g) s
      exact Prod.ext rfl this.symm
    rw [e] at key
    rw [key]; simp
  show _ = (0 : M)
  refine Finset.sum_involution (fun g _ => inv g) ?_ ?_ ?_ ?_
  · intro g _; exact hu g
  · intro g _ hne heq
    apply hne
    have h0 := hu g
    rw [heq] at h0
    have h2 : (2 : K) • u g = 0 := by rw [two_smul]; exact h0
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    show cont (g ∘ _) = m
    rw [content_comp_perm_eq]; exact hg
  · intro g _
    show (inv g) ∘ Equiv.swap (pr (xs (inv g))).1 (pr (xs (inv g))).2 = g
    rw [hxs g]
    funext s
    simp [inv]

theorem lcb_mono {n : ℕ} (col : Fin n → ℕ) (h : ∀ (j : Fin n) (hj : j.val + 1 < n), col j ≤ col ⟨j.val + 1, hj⟩) :
    ∀ (d : ℕ) (a b : Fin n), b.val = a.val + d → col a ≤ col b := by
  intro d
  induction d with
  | zero => intro a b hb; have : a = b := Fin.ext (by omega); rw [this]
  | succ d ih =>
    intro a b hb
    have hc : a.val + d < n := by have := b.isLt; omega
    have hc' : (⟨a.val + d, hc⟩ : Fin n).val + 1 < n := by have := b.isLt; simp only; omega
    have hb' : b = ⟨(⟨a.val + d, hc⟩ : Fin n).val + 1, hc'⟩ := Fin.ext (by simp only; omega)
    calc col a ≤ col ⟨a.val + d, hc⟩ := ih a _ rfl
      _ ≤ col b := by rw [hb']; exact h _ hc'

theorem lcb_ivt {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (hp : IsPath n lam2 tau κ ρ) (a : Fin q) (j0 : ℕ) (h0 : lam2 a ≤ j0) :
    ∀ m ≤ n, j0 < κ m a → ∃ l : Fin n, ρ l = a ∧ κ l.val a = j0 := by
  intro m
  induction m with
  | zero => intro _ h; rw [hp.start] at h; omega
  | succ m ih =>
    intro hm h
    by_cases h' : j0 < κ m a
    · exact ih (by omega) h'
    · have hs := hp.step ⟨m, by omega⟩
      have hs' : κ (m + 1) a = κ m a + (Pi.single (ρ ⟨m, by omega⟩) 1 : Fin q → ℕ) a := by
        have := congrFun hs a; simpa using this
      by_cases hr : ρ ⟨m, by omega⟩ = a
      · refine ⟨⟨m, by omega⟩, hr, ?_⟩
        rw [hr, Pi.single_eq_same] at hs'
        simp only; omega
      · rw [Pi.single_eq_of_ne (Ne.symm hr)] at hs'
        omega

theorem monotone_run : MonoRun := by
  intro q n lam2 tau κ ρ hp hmono p j0 hlen
  classical
  unfold LD.colLen at hlen
  set S : Finset (Fin n) := Finset.univ.filter (fun l => colSeq κ ρ l = j0) with hS
  have hmem : ∀ l, l ∈ S ↔ colSeq κ ρ l = j0 := by
    intro l; simp [hS]
  have hsub : (Finset.univ.filter fun a : Fin q => lam2 a ≤ j0 ∧ j0 < tau a) ⊆ S.image ρ := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨l, hl1, hl2⟩ := lcb_ivt hp a j0 ha.1 n le_rfl (by rw [hp.stop]; exact ha.2)
    refine Finset.mem_image.mpr ⟨l, ?_, hl1⟩
    rw [hmem]
    unfold colSeq
    rw [hl1]; exact hl2
  have hcard : p < S.card := by
    calc p < _ := hlen
      _ ≤ (S.image ρ).card := Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hi : colSeq κ ρ (S.min' hne) = j0 := (hmem _).mp (Finset.min'_mem S hne)
  have hi' : colSeq κ ρ (S.max' hne) = j0 := (hmem _).mp (Finset.max'_mem S hne)
  have hIcc : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := fun l hl =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le S l hl, Finset.le_max' S l hl⟩
  have hc2 : S.card ≤ (S.max' hne).val + 1 - (S.min' hne).val := by
    have := Finset.card_le_card hIcc
    rwa [Fin.card_Icc] at this
  refine ⟨(S.min' hne).val, by have := (S.max' hne).isLt; omega, fun l h1 h2 => ?_⟩
  have m1 := lcb_mono _ hmono (l.val - (S.min' hne).val) (S.min' hne) l (by omega)
  have m2 := lcb_mono _ hmono ((S.max' hne).val - l.val) l (S.max' hne) (by omega)
  omega

end Formalism.CohomologicalDescent.LC
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.FsDivMem
section
namespace Formalism.CohomologicalDescent.LR

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.Symmetrization

theorem lrd_core {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℚ V]
    (φ : ι → Module.End ℚ V) (hφ : ∀ a b, Commute (φ a) (φ b)) (L : AddSubgroup V)
    (hL : ∀ (v : ι) (k : ℕ), ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • ((φ v) ^ k) x ∈ L) :
    ∀ (M : Multiset ι), ∀ x ∈ L,
      (((∏ v, (Multiset.count v M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x ∈ L := by
  suffices key : ∀ n : ℕ, ∀ M : Multiset ι, Multiset.card M = n → ∀ x ∈ L,
      (((∏ v, (Multiset.count v M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x ∈ L by
    intro M
    exact key _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hn x hx
    by_cases hM : M = 0
    · subst hM
      simp [hx]
    obtain ⟨v, hv⟩ := Multiset.exists_mem_of_ne_zero hM

    set c := Multiset.count v M with hc
    set M' := M.filter (fun w => ¬ w = v) with hM'
    have hsplit : M = Multiset.replicate c v + M' := by
      rw [hM', hc, ← Multiset.filter_eq' M v, Multiset.filter_add_not]
    have hc0 : 0 < c := Multiset.count_pos.mpr hv
    have hcard : Multiset.card M' < n := by
      have e := congrArg Multiset.card hsplit
      rw [Multiset.card_add, Multiset.card_replicate] at e
      omega
    have hperm : M.toList.Perm (List.replicate c v ++ M'.toList) := by
      have e : (M.toList : Multiset ι) = ((List.replicate c v ++ M'.toList : List ι) : Multiset ι) := by
        rw [Multiset.coe_toList, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_replicate]
        exact hsplit
      exact Multiset.coe_eq_coe.mp e
    have hpw : (M.toList.map φ).Pairwise Commute :=
      List.pairwise_map.mpr (List.pairwise_of_forall fun a b => hφ a b)
    have hprod : (M.toList.map φ).prod = φ v ^ c * (M'.toList.map φ).prod := by
      rw [(hperm.map φ).prod_eq' hpw]
      simp [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]

    have hcnt : ∀ w ∈ Finset.univ.erase v, Multiset.count w M' = Multiset.count w M := by
      intro w hw
      exact Multiset.count_filter_of_pos (Finset.ne_of_mem_erase hw)
    have hcv : Multiset.count v M' = 0 := Multiset.count_filter_of_neg (fun h => h rfl)
    have hfact : (∏ w, (Multiset.count w M).factorial : ℕ) =
        c.factorial * ∏ w, (Multiset.count w M').factorial := by
      rw [← Finset.mul_prod_erase Finset.univ (fun w => (Multiset.count w M).factorial) (Finset.mem_univ v),
        ← Finset.mul_prod_erase Finset.univ (fun w => (Multiset.count w M').factorial) (Finset.mem_univ v),
        hcv, Nat.factorial_zero, one_mul]
      congr 1
      exact Finset.prod_congr rfl fun w hw => by rw [hcnt w hw]
    have hrest := ih _ (hn ▸ hcard) M' rfl x hx
    have e : (((∏ w, (Multiset.count w M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x =
        ((c.factorial : ℚ)⁻¹) • (φ v ^ c)
          ((((∏ w, (Multiset.count w M').factorial : ℕ) : ℚ)⁻¹) • (M'.toList.map φ).prod x) := by
      rw [hprod, hfact, Module.End.mul_apply, map_smul, smul_smul, Nat.cast_mul, mul_inv]
    rw [e]
    exact hL v c _ hrest

theorem Fs_div_mem {V P R : Type} [AddCommGroup V] [Module ℚ V] [DecidableEq P] [DecidableEq R] [Fintype P]
    [Fintype R] (S : Symmetrization.HidaSetting ℚ V P R) (L : AddSubgroup V)
    (hL : ∀ (v : R × P) (k : ℕ), ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • ((S.f v) ^ k) x ∈ L) {n : ℕ}
    (m : Sym (R × P) n) : ∀ x ∈ L, ((Symmetrization.mfact m : ℚ)⁻¹) • S.Fs m x ∈ L := by
  have hcomm : ∀ a b : R × P, Commute (S.f a) (S.f b) := by
    intro a b
    have h := S.comm (Sum.inr a.1) (Sum.inl a.2) (Sum.inr b.1) (Sum.inl b.2)
    simp only [reduceCtorEq, if_false, sub_zero] at h
    exact sub_eq_zero.mp h
  intro x hx
  exact lrd_core S.f hcomm L hL m.1 x hx

end Formalism.CohomologicalDescent.LR
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.MeasureSwapInvariant
section
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem no_bad_tuple : NoTuple := by
  intro K V J _ _ _ T TT E hE v hv t0 ht0 hv0
  classical
  choose! tt htt1 htt2 using hE
  obtain ⟨f, t, htE, -, hsum⟩ := (Submodule.mem_span_iff_exists_finset_subset).1 hv
  clear hv
  induction t using Finset.induction_on generalizing f v with
  | empty => simpa using hsum.symm
  | insert e0 t' he0 ih =>
    have he0E : e0 ∈ E := htE (by simp)
    have hne : tt e0 ≠ t0 := fun h => ht0 (h ▸ htt1 e0 he0E)
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have h1 : (t0 j - tt e0 j) • v = ∑ a ∈ t', (f a * (tt a j - tt e0 j)) • a := by
      have h3 : T j v - tt e0 j • v = ∑ a ∈ insert e0 t', f a • (T j a - tt e0 j • a) := by
        rw [← hsum]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intros
        rw [smul_comm]
      rw [sub_smul, ← hv0 j, h3, Finset.sum_insert he0, htt2 e0 he0E j, sub_self, smul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro a ha
      rw [htt2 a (htE (by simp [ha])) j, ← sub_smul, smul_smul]
    have h2 := ih ((t0 j - tt e0 j) • v) (fun i => by rw [map_smul, hv0 i, smul_comm])
      (fun a => f a * (tt a j - tt e0 j)) (fun a ha => htE (by simp at ha ⊢; exact Or.inr ha)) h1.symm
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hj))

theorem measure_swap_invariant : MeasSwap := by
  intro n col j hj hlt
  set b : Fin n := ⟨j.val + 1, hj⟩ with hb
  have hjb : j ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [hb] at this
  have hsplit : ∀ F : Fin n → ℕ, ∑ l, F l = F j + (F b + ∑ l ∈ (Finset.univ.erase j).erase b, F l) := by
    intro F
    rw [Finset.add_sum_erase _ F (by simp [hjb.symm]), Finset.add_sum_erase _ F (by simp)]
  unfold meas
  rw [hsplit, hsplit (fun l => (n - l.val) * col l)]
  have hrest : ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * (col ∘ Equiv.swap j b) l =
      ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * col l := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hl.2 hl.1]
  rw [hrest]
  simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  obtain ⟨w, hw⟩ : ∃ w, n - b.val = w := ⟨_, rfl⟩
  have hw' : n - j.val = w + 1 := by
    have : b.val = j.val + 1 := rfl
    omega
  rw [hw, hw']
  nlinarith

theorem ColumnsFromPieri_of (hSwap : SwapPath) (hSame : SameCol) (hMeas : MeasSwap) (hMono : MonoRun)
    (hWt : WtIff) (hGood : GoodSwap) (hAntiStep : AntiStep) (hAnti : Anti) : ColumnsFromPieri := by
  intro K P M q _ _ _ _ _ _ EM n lam2 hp tau ⟨b, j0, hj0, hcol⟩ z hz
  have key : ∀ N : ℕ, ∀ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
      meas (colSeq κ ρ) = N → ∀ z : Tens (Fin q) P M n, IsWt K EM lam2 (cseq κ ρ) z → toSym K z = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro κ ρ hpath hN z hz
      by_cases hdesc : ∃ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ ⟨j.val + 1, hj⟩ < colSeq κ ρ j
      · obtain ⟨j, hj, hlt⟩ := hdesc
        obtain ⟨h2, κ', hpath', hc', hcol'⟩ := hSwap q n lam2 tau κ ρ hpath j hj hlt
        refine hGood K P M q EM n lam2 (cseq κ ρ) j hj h2 ?_ z hz
        intro z' hz'
        rw [← hc'] at hz'
        refine ih _ ?_ κ' _ hpath' rfl z' hz'
        rw [hcol', ← hN]
        exact hMeas n _ j hj hlt
      · push Not at hdesc
        obtain ⟨i, hi, hrun⟩ := hMono q n lam2 tau κ ρ hpath hdesc (Fintype.card P) j0 hcol
        refine hAnti K (Fin q) P M n i hi z ?_
        intro j hj h1 h2
        have hc : colSeq κ ρ ⟨j.val + 1, hj⟩ = colSeq κ ρ j := by
          rw [hrun j h1 (by omega), hrun ⟨j.val + 1, hj⟩ (by simp only []; omega) (by simp only []; omega)]
        obtain ⟨ha, hb⟩ := hSame q n lam2 tau κ ρ hpath j hj hc
        exact hAntiStep K P M q EM n lam2 hp _ z j hj hz ha hb
  have hle : PathSpace K (P := P) EM n lam2 tau ≤ LinearMap.ker (toSym K) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨κ, ρ, hpath, hy⟩
    exact LinearMap.mem_ker.2 (key _ κ ρ hpath rfl y ((hWt K P M q EM n lam2 κ ρ hpath.start hpath.step y).1 hy))
  exact LinearMap.mem_ker.1 (hle hz)

end Formalism.CohomologicalDescent.LC
end

