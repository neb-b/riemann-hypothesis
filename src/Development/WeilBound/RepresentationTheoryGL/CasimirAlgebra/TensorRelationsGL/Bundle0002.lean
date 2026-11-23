module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PChainA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ChainP

section gen
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem intCast_comp (f : V →ₗ[ℂ] W) (z : ℤ) :
    f ∘ₗ ((z : Module.End ℂ V)) = ((z : Module.End ℂ W)) ∘ₗ f := by
  refine LinearMap.ext fun v => ?_
  simp [Module.End.intCast_apply]

theorem ofFn_comp (f : V →ₗ[ℂ] W) {t : ℕ} (A : Fin t → Module.End ℂ V) (B : Fin t → Module.End ℂ W)
    (h : ∀ k, f ∘ₗ A k = B k ∘ₗ f) : f ∘ₗ (List.ofFn A).prod = (List.ofFn B).prod ∘ₗ f := by
  induction t with
  | zero => refine LinearMap.ext fun v => ?_; simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc,
      ih (fun k => A k.succ) (fun k => B k.succ) (fun k => h _), LinearMap.comp_assoc]

theorem qdet_comp {n : ℕ} (f : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b, f ∘ₗ E a b = F a b ∘ₗ f) (u : ℂ) :
    f ∘ₗ qdet E u = qdet F u ∘ₗ f := by
  unfold qdet qminor
  have key : ∀ σ : Equiv.Perm (Fin n), f ∘ₗ (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ V) *
      (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod) =
      (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) *
      (List.ofFn fun k : Fin n => Tm F (u - (k : ℂ)) (id (σ k)) (id k)).prod) ∘ₗ f := fun σ => by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, intCast_comp,
    LinearMap.comp_assoc, ofFn_comp f _ _ (fun k => ?_), LinearMap.comp_assoc]
    simp only [Tm]
    rw [LinearMap.comp_add, LinearMap.add_comp, h]
    congr 1
    split_ifs
    · refine LinearMap.ext fun v => ?_; simp
    · simp
  refine LinearMap.ext fun v => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun σ _ => LinearMap.congr_fun (key σ) v

theorem listSub_comp (f : V →ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : f ∘ₗ A = B ∘ₗ f)
    (L : List ℂ) :
    f ∘ₗ (L.map fun r => A - algebraMap ℂ _ r).prod = (L.map fun r => B - algebraMap ℂ _ r).prod ∘ₗ f := by
  have key : ∀ r : ℂ, f ∘ₗ (A - algebraMap ℂ _ r) = (B - algebraMap ℂ _ r) ∘ₗ f := by
    intro r
    ext v
    have hv := LinearMap.congr_fun h v
    simp only [LinearMap.comp_apply] at hv
    simp [hv]
  induction L with
  | nil =>
    ext v
    simp
  | cons r L ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, key r,
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

theorem listSub_commute (A T : Module.End ℂ V) (h : Commute A T) (L : List ℂ) :
    Commute (L.map fun r => A - algebraMap ℂ _ r).prod T := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  exact h.sub_left (Algebra.commutes r T)

theorem listSub_pairwise (A : Module.End ℂ V) (L : List ℂ) :
    (L.map fun r => A - algebraMap ℂ _ r).Pairwise Commute := by
  rw [List.pairwise_map]
  exact List.pairwise_of_forall fun r s =>
    ((Commute.refl A).sub_left (Algebra.commutes r A)).sub_right (Algebra.commutes s _).symm

theorem listSub_kill (A : Module.End ℂ V) {n : ℕ} (l : Fin n → ℂ) (c : Fin n)
    (h0 : (List.ofFn fun k => A - algebraMap ℂ _ (l k)).prod = 0) :
    (((List.ofFn l).erase (l c)).map fun r => A - algebraMap ℂ _ r).prod * (A - algebraMap ℂ _ (l c)) = 0 := by
  have hm : l c ∈ List.ofFn l := by simp
  have h1 : ((List.ofFn l).map fun r => A - algebraMap ℂ (Module.End ℂ V) r).prod = 0 := by
    rw [List.map_ofFn]
    exact h0
  rw [((List.perm_cons_erase hm).map _).prod_eq' (listSub_pairwise A _), List.map_cons,
    List.prod_cons] at h1
  rw [(listSub_commute A _ ((Commute.refl A).sub_right (Algebra.commutes _ A).symm) _).eq]
  exact h1

theorem adjoin_commute {A : Type} [Ring A] [Algebra ℂ A] (s : Set A) (T : A) (hs : ∀ x ∈ s, Commute x T) :
    ∀ g ∈ Algebra.adjoin ℂ s, Commute g T := by
  intro g hg
  have hle : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {T} :=
    Algebra.adjoin_le fun x hx => by
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hs x hx).symm.eq
  have h2 := hle hg
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact (h2 T (Set.mem_singleton T)).symm

end gen

end ChainP

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAntiB
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def npairs {m : ℕ} (col : Fin m → ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin m × Fin m => x.1 < x.2 ∧ col x.1 = col x.2).card

def ColInj {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) : Prop :=
  ∀ p q, col p = col q → I p = I q → p = q

def rk {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) (p : Fin m) : ℕ :=
  (Finset.univ.filter fun q => col q = col p ∧ I p < I q).card

theorem rk_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) (p : Fin m) : rk col I p ≤ (top : ℕ) - I p := by
  unfold rk
  have h1 : (Finset.univ.filter fun q => col q = col p ∧ I p < I q).card ≤ (Finset.Ioi (I p)).card := by
    apply Finset.card_le_card_of_injOn I
    · intro q hq
      simp at hq ⊢
      exact hq.2
    · intro q hq q' hq' hqq
      simp at hq hq'
      exact hI q q' (hq.1.trans hq'.1.symm) hqq
  rw [Fin.card_Ioi] at h1
  omega

theorem sum_rk {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) (hI : ColInj col I) :
    ∑ p, rk col I p = npairs col := by
  have e1 : ∑ p, rk col I p = (Finset.univ.filter fun x : Fin m × Fin m => col x.2 = col x.1 ∧ I x.1 < I x.2).card := by
    unfold rk
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [e1]
  unfold npairs
  apply Finset.card_bij' (fun x _ => if x.1 < x.2 then x else x.swap) (fun y _ => if I y.1 < I y.2 then y else y.swap)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_cases h : x.1 < x.2
    · simp [h, hx.2]
    · have h' : ¬ I x.2 < I x.1 := not_lt.mpr hx.2.le
      simp [h, h']
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    by_cases h : I y.1 < I y.2
    · simp [h, hy.1]
    · have h' : ¬ y.2 < y.1 := not_lt.mpr hy.1.le
      simp [h, h']
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hne : x.1 ≠ x.2 := fun h => by rw [h] at hx; exact lt_irrefl _ hx.2
    split_ifs with h
    · exact ⟨h, hx.1.symm⟩
    · try simp only [Prod.fst_swap, Prod.snd_swap]
      refine ⟨?_, hx.1⟩
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd h' h
      · exact h'
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hne : I y.1 ≠ I y.2 := fun h => (ne_of_lt hy.1) (hI _ _ hy.2 h)
    split_ifs with h
    · exact ⟨hy.2.symm, h⟩
    · try simp only [Prod.fst_swap, Prod.snd_swap]
      exact ⟨hy.2, lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)⟩

theorem npairs_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) : npairs col ≤ ∑ p, ((top : ℕ) - I p) := by
  rw [← sum_rk col I hI]
  exact Finset.sum_le_sum fun p _ => rk_le col top htop I hI p

theorem eq_of_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (b I : Fin m → Fin n)
    (hb : IsTab col b) (hI : ColInj col I) (h : ∑ p, ((top : ℕ) - I p) ≤ npairs col) :
    ∃ σ ∈ colG col, I = b ∘ σ := by
  classical
  have heq : ∀ p, rk col I p = (top : ℕ) - I p := by
    have hs : ∑ p, rk col I p = ∑ p, ((top : ℕ) - I p) :=
      le_antisymm (by rw [sum_rk col I hI]; exact npairs_le col top htop I hI) (by rw [sum_rk col I hI]; exact h)
    intro p
    exact (Finset.sum_eq_sum_iff_of_le (fun p _ => rk_le col top htop I hI p)).mp hs p (Finset.mem_univ p)
  have hex : ∀ p, ∃ q, col q = col p ∧ b q = I p := by
    intro p
    have hA : (top : ℕ) - I p + 1 ≤ (Finset.univ.filter fun q => col q = col p).card := by
      rw [← heq p]
      unfold rk
      rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun q => col q = col p ∧ I p < I q) (a := p) (by simp)]
      apply Finset.card_le_card
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rcases hq with rfl | hq
      · rfl
      · exact hq.1
    by_cases hb0 : ∃ q, col q = col p ∧ b q ≤ I p
    · obtain ⟨q0, hq0c, hq0b⟩ := hb0
      rcases lt_or_eq_of_le hq0b with hlt | heq'
      · obtain ⟨q, hqc, hqb⟩ := hb.2 q0 (I p) hlt
        exact ⟨q, hqc.trans hq0c, hqb⟩
      · exact ⟨q0, hq0c, heq'⟩
    · push_neg at hb0
      exfalso
      have hB : (Finset.univ.filter fun q => col q = col p).card ≤ (Finset.Ioi (I p)).card := by
        apply Finset.card_le_card_of_injOn b
        · intro q hq
          simp at hq ⊢
          exact hb0 q hq
        · intro q hq q' hq' hqq
          simp at hq hq'
          exact hb.1 q q' (hq.trans hq'.symm) hqq
      rw [Fin.card_Ioi] at hB
      have := (I p).isLt
      omega
  choose σf hσc hσb using hex
  have hinj : Function.Injective σf := by
    intro p p' hpp
    have hc : col p = col p' := by rw [← hσc p, ← hσc p', hpp]
    have hi : I p = I p' := by rw [← hσb p, ← hσb p', hpp]
    exact hI p p' hc hi
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective σf (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_, ?_⟩
  · simp [colG, σ, hσc]
  · funext p
    simp [σ, hσb]

end ColumnAntisymmetry

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAntiC
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem split {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (col : Fin m → ℕ) (hmono : Monotone col)
    (hc : ∀ i j : Fin m, Commute (xJ E i) (xJ E j))
    (hP : ∀ i j : Fin m, (i : ℕ) + 1 = j →
      xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 ∧
      ∀ k : Fin m, k ≠ i → k ≠ j → Commute (xJ E k) (pm (Equiv.swap i j)))
    (i j : Fin m) (hij : (i : ℕ) + 1 = j) (hcol : col i = col j) :
    ∃ R : Module.End ℂ (TV n M (Fin m)), colD E col = (xJ E i - xJ E j + 1) * R ∧
      R * pm (Equiv.swap i j) = pm (Equiv.swap i j) * R := by
  set s : Module.End ℂ (TV n M (Fin m)) := pm (Equiv.swap i j) with hs_def
  have hs2 : s * s = 1 := by rw [hs_def, ← pm_mul, Equiv.swap_mul_self, pm_one]
  obtain ⟨h1, h2⟩ := hP i j hij
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hlt : i < j := by
    rw [Fin.lt_iff_val_lt_val]
    omega
  have h3 : s * xJ E j = xJ E i * s + 1 := by
    calc s * xJ E j = s * (xJ E j * s) * s := by simp only [mul_assoc, hs2, mul_one]
      _ = s * (s * xJ E i + 1) * s := by rw [h1]
      _ = xJ E i * s + 1 := by
        rw [mul_add, add_mul, ← mul_assoc s s, hs2, one_mul, mul_one, hs2]
  have e1 : Commute (xJ E i + xJ E j) s := by
    show (xJ E i + xJ E j) * s = s * (xJ E i + xJ E j)
    rw [add_mul, mul_add, h1, h3]
    abel
  have e2 : Commute (xJ E i * xJ E j) s := by
    show xJ E i * xJ E j * s = s * (xJ E i * xJ E j)
    rw [mul_assoc, h1, (hc i j).eq, ← mul_assoc, h3]
    noncomm_ring
  have hsym : ∀ c, Commute c s → Commute c (xJ E i) →
      Commute ((xJ E i + c) * (xJ E j + c)) s := by
    intro c hcs hci
    have hexp : (xJ E i + c) * (xJ E j + c) =
        xJ E i * xJ E j + c * (xJ E i + xJ E j) + c * c := by
      rw [add_mul, mul_add, mul_add, mul_add, ← hci.eq]
      abel
    rw [hexp]
    exact (e2.add_left (hcs.mul_left e1)).add_left (hcs.mul_left hcs)
  have hsym2 : ∀ c, Commute c s → Commute c (xJ E i) →
      Commute ((c - xJ E i) * (c - xJ E j)) s := by
    intro c hcs hci
    have hh := hsym (-c) hcs.neg_left hci.neg_left
    rwa [show (c - xJ E i) * (c - xJ E j) = (xJ E i + -c) * (xJ E j + -c) by noncomm_ring]
  let S : Set (Module.End ℂ (TV n M (Fin m))) := Set.range (xJ E)
  have hcomm : S.Pairwise Commute := by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ _
    exact hc k l
  let _ : IsMulCommutative (Algebra.adjoin ℂ S) := Algebra.isMulCommutative_adjoin ℂ hcomm
  let _ : CommRing (Algebra.adjoin ℂ S) :=
    open scoped IsMulCommutative in inferInstance
  let x' : Fin m → Algebra.adjoin ℂ S := fun k => ⟨xJ E k, Algebra.subset_adjoin ⟨k, rfl⟩⟩
  let F : Fin m → Fin m → Algebra.adjoin ℂ S := fun p q =>
    if p < q ∧ col p = col q then x' p - x' q + 1 else 1
  have hF : ∀ p q, ((F p q : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) =
      if p < q ∧ col p = col q then xJ E p - xJ E q + 1 else 1 := by
    intro p q
    simp only [F]
    split_ifs <;> rfl
  have hcoe_mul : ∀ a b : Algebra.adjoin ℂ S,
      ((a * b : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) = a * b := fun a b => rfl
  have hcoe_one : ((1 : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) = 1 := rfl
  have hlist : ∀ l : List (Algebra.adjoin ℂ S),
      ((l.prod : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) =
        (l.map Subtype.val).prod := by
    intro l
    induction l with
    | nil => exact hcoe_one
    | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, hcoe_mul, ih]
  have hcolD : colD E col = ((∏ q, ∏ p, F p q : Algebra.adjoin ℂ S) : Module.End ℂ _) := by
    simp only [colD, ← List.prod_ofFn, hlist, List.map_ofFn, Function.comp_def, hF]
  have hjmem : j ∈ (Finset.univ : Finset (Fin m)).erase i :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hsplit : ∀ g : Fin m → Algebra.adjoin ℂ S,
      ∏ q, g q = g i * g j * ∏ q ∈ (Finset.univ.erase i).erase j, g q := by
    intro g
    rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ g hjmem, mul_assoc]
  have hmemO : ∀ p, p ∈ (Finset.univ.erase i).erase j → p ≠ i ∧ p ≠ j := by
    intro p hp
    simp only [Finset.mem_erase] at hp
    exact ⟨hp.2.1, hp.1⟩
  have Fii : F i i = 1 := by simp [F]
  have Fjj : F j j = 1 := by simp [F]
  have Fji : F j i = 1 := by
    simp only [F]
    rw [if_neg]
    rintro ⟨h, -⟩
    exact absurd (lt_trans h hlt) (lt_irrefl _)
  have hPeq : ∏ q, ∏ p, F p q = F i j *
      ((∏ p ∈ (Finset.univ.erase i).erase j, F p i * F p j) *
        (∏ q ∈ (Finset.univ.erase i).erase j, F i q * F j q) *
        ∏ q ∈ (Finset.univ.erase i).erase j, ∏ p ∈ (Finset.univ.erase i).erase j, F p q) := by
    simp only [hsplit, Fii, Fjj, Fji, one_mul, mul_one, Finset.prod_mul_distrib]
    ring
  refine ⟨(((∏ p ∈ (Finset.univ.erase i).erase j, F p i * F p j) *
        (∏ q ∈ (Finset.univ.erase i).erase j, F i q * F j q) *
        ∏ q ∈ (Finset.univ.erase i).erase j, ∏ p ∈ (Finset.univ.erase i).erase j, F p q :
          Algebra.adjoin ℂ S) : Module.End ℂ _), ?_, ?_⟩
  · rw [hcolD, hPeq, hcoe_mul, hF, if_pos ⟨hlt, hcol⟩]
  · have hmul : ∀ a b : Algebra.adjoin ℂ S,
        Commute (a : Module.End ℂ (TV n M (Fin m))) s →
        Commute (b : Module.End ℂ (TV n M (Fin m))) s →
        Commute ((a * b : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) s := by
      intro a b ha hb
      rw [hcoe_mul]
      exact ha.mul_left hb
    have hone : Commute ((1 : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) s := by
      rw [hcoe_one]
      exact Commute.one_left s
    have hA : Commute (((∏ p ∈ (Finset.univ.erase i).erase j, F p i * F p j :
        Algebra.adjoin ℂ S)) : Module.End ℂ (TV n M (Fin m))) s := by
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro p hp
      obtain ⟨hpi, hpj⟩ := hmemO p hp
      have hpi' : (p : ℕ) ≠ i := fun h => hpi (Fin.ext h)
      show Commute ((F p i : Module.End ℂ (TV n M (Fin m))) * (F p j : Module.End ℂ _)) s
      rw [hF, hF]
      by_cases hq : p < i ∧ col p = col i
      · rw [if_pos hq, if_pos ⟨lt_trans hq.1 hlt, hq.2.trans hcol⟩,
          show xJ E p - xJ E i + 1 = (xJ E p + 1) - xJ E i by abel,
          show xJ E p - xJ E j + 1 = (xJ E p + 1) - xJ E j by abel]
        exact hsym2 _ ((h2 p hpi hpj).add_left (Commute.one_left s))
          ((hc p i).add_left (Commute.one_left _))
      · have hn : ¬ (p < j ∧ col p = col j) := by
          rintro ⟨h, h'⟩
          apply hq
          refine ⟨?_, h'.trans hcol.symm⟩
          rw [Fin.lt_iff_val_lt_val] at h ⊢
          omega
        rw [if_neg hq, if_neg hn, mul_one]
        exact Commute.one_left s
    have hB : Commute (((∏ q ∈ (Finset.univ.erase i).erase j, F i q * F j q :
        Algebra.adjoin ℂ S)) : Module.End ℂ (TV n M (Fin m))) s := by
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro q hq
      obtain ⟨hqi, hqj⟩ := hmemO q hq
      have hqj' : (q : ℕ) ≠ j := fun h => hqj (Fin.ext h)
      show Commute ((F i q : Module.End ℂ (TV n M (Fin m))) * (F j q : Module.End ℂ _)) s
      rw [hF, hF]
      by_cases hq' : i < q ∧ col i = col q
      · have hjq : j < q := by
          have := hq'.1
          rw [Fin.lt_iff_val_lt_val] at this ⊢
          omega
        rw [if_pos hq', if_pos ⟨hjq, hcol.symm.trans hq'.2⟩,
          show xJ E i - xJ E q + 1 = xJ E i + (1 - xJ E q) by abel,
          show xJ E j - xJ E q + 1 = xJ E j + (1 - xJ E q) by abel]
        exact hsym _ ((Commute.one_left s).sub_left (h2 q hqi hqj))
          ((Commute.one_left _).sub_left (hc q i))
      · have hn : ¬ (j < q ∧ col j = col q) := by
          rintro ⟨h, h'⟩
          apply hq'
          refine ⟨?_, hcol.trans h'⟩
          rw [Fin.lt_iff_val_lt_val] at h ⊢
          omega
        rw [if_neg hq', if_neg hn, mul_one]
        exact Commute.one_left s
    have hC : Commute (((∏ q ∈ (Finset.univ.erase i).erase j,
        ∏ p ∈ (Finset.univ.erase i).erase j, F p q :
        Algebra.adjoin ℂ S)) : Module.End ℂ (TV n M (Fin m))) s := by
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro q hq
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro p hp
      obtain ⟨hqi, hqj⟩ := hmemO q hq
      obtain ⟨hpi, hpj⟩ := hmemO p hp
      show Commute (F p q : Module.End ℂ (TV n M (Fin m))) s
      rw [hF]
      split_ifs
      · exact ((h2 p hpi hpj).sub_left (h2 q hqi hqj)).add_left (Commute.one_left s)
      · exact Commute.one_left s
    exact (hmul _ _ (hmul _ _ hA hB) hC).eq

end ColumnAntisymmetry

end PositivityTheory.Rg.Cz

end
end

