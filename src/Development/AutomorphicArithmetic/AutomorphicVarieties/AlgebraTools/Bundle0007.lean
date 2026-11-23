module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0026

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem swap_lt {n : ℕ} {a c : Fin n} (h : a.val + 1 = c.val) {x y : Fin n} (hxy : x < y)
    (hne : ¬ (x = a ∧ y = c)) : swap a c x < swap a c y := by
  have key : ∀ z : Fin n, (swap a c z).val = if z.val = a.val then c.val else if z.val = c.val then a.val else z.val := by
    intro z
    rw [swap_apply_def]
    by_cases h1 : z = a
    · subst h1
      simp
    · by_cases h2 : z = c
      · subst h2
        have h1' : z.val ≠ a.val := fun e => h1 (Fin.ext e)
        simp [h1, h1']
      · have h1' : z.val ≠ a.val := fun e => h1 (Fin.ext e)
        have h2' : z.val ≠ c.val := fun e => h2 (Fin.ext e)
        simp [h1, h2, h1', h2']
  rw [Fin.lt_def, key, key]
  rw [Fin.lt_def] at hxy
  have hne' : ¬ (x.val = a.val ∧ y.val = c.val) := fun e => hne ⟨Fin.ext e.1, Fin.ext e.2⟩
  split_ifs <;> omega

private theorem mem_invSet {n : ℕ} (w : Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ invSet w ↔ p.1 < p.2 ∧ w⁻¹ p.2 < w⁻¹ p.1 := by
  simp [invSet, pairs]

private theorem eq_one_of_strictMono {n : ℕ} (w : Perm (Fin n)) (h : StrictMono w) : w = 1 := by
  exact Equiv.ext fun x => congrFun h.eq_id x

private theorem invSet_rev (n : ℕ) : invSet (Fin.revPerm : Perm (Fin n)) = pairs n := by
  ext ⟨x, y⟩
  rw [mem_invSet]
  have hinv : ∀ z : Fin n, (Fin.revPerm : Perm (Fin n))⁻¹ z = z.rev := by
    intro z
    rw [Perm.inv_eq_iff_eq, Fin.revPerm_apply, Fin.rev_rev]
  simp only [hinv, Fin.rev_lt_rev]
  simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem UpperTheory.V.AlgebraTools.hkInv :
    ∀ n : ℕ, (∀ (a c : Fin n), a.val + 1 = c.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ c →
        invSet (swap a c * w) = insert (a, c) ((invSet w).image fun p => (swap a c p.1, swap a c p.2)) ∧
        (a, c) ∉ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) ∧ invN (swap a c * w) = invN w + 1) ∧
      (∀ w : Perm (Fin n), w ≠ 1 → ∃ a c : Fin n, a.val + 1 = c.val ∧ w⁻¹ c < w⁻¹ a) ∧
      invSet (1 : Perm (Fin n)) = ∅ ∧ invSet (Fin.revPerm : Perm (Fin n)) = pairs n ∧
      (∀ w : Perm (Fin n), w ≠ Fin.revPerm → invN w < invN (Fin.revPerm : Perm (Fin n))) := by
  intro n
  refine ⟨?_, ?_, ?_, invSet_rev n, ?_⟩
  · intro a c hac w hw
    have hlt : a < c := by
      rw [Fin.lt_def]
      omega
    have hff : ∀ p : Fin n × Fin n, (swap a c (swap a c p.1), swap a c (swap a c p.2)) = p := by
      intro p
      simp
    have hmemimg : ∀ q : Fin n × Fin n, q ∈ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) ↔
        (swap a c q.1, swap a c q.2) ∈ invSet w := by
      intro q
      rw [Finset.mem_image]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rwa [hff]
      · intro hq
        exact ⟨_, hq, hff q⟩
    have hnot : (a, c) ∉ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) := by
      rw [hmemimg, mem_invSet]
      simp only [swap_apply_left, swap_apply_right]
      exact fun h => absurd h.1 (lt_asymm hlt)
    have heq : invSet (swap a c * w) = insert (a, c) ((invSet w).image (fun p => (swap a c p.1, swap a c p.2))) := by
      ext ⟨x, y⟩
      rw [Finset.mem_insert, hmemimg, mem_invSet, mem_invSet]
      simp only [mul_inv_rev, swap_inv, Perm.mul_apply, Prod.mk.injEq]
      by_cases hp : x = a ∧ y = c
      · obtain ⟨rfl, rfl⟩ := hp
        simp only [swap_apply_left, swap_apply_right]
        exact ⟨fun _ => Or.inl (by simp), fun _ => ⟨hlt, hw⟩⟩
      · constructor
        · rintro ⟨hxy, hA⟩
          exact Or.inr ⟨swap_lt hac hxy hp, hA⟩
        · rintro (h | ⟨hs, hA⟩)
          · exact absurd h hp
          · refine ⟨?_, hA⟩
            rcases lt_trichotomy x y with h | h | h
            · exact h
            · subst h
              exact absurd hs (lt_irrefl _)
            · by_cases hq : y = a ∧ x = c
              · obtain ⟨rfl, rfl⟩ := hq
                simp only [swap_apply_left, swap_apply_right] at hA
                exact absurd hA (lt_asymm hw)
              · exact absurd (swap_lt hac h hq) (lt_asymm hs)
    refine ⟨heq, hnot, ?_⟩
    unfold invN
    rw [heq, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective]
    intro p q hpq
    have := congrArg (fun r : Fin n × Fin n => (swap a c r.1, swap a c r.2)) hpq
    simp only [hff] at this
    exact this
  · intro w hw
    by_contra hcon
    push_neg at hcon
    apply hw
    have hadj : ∀ a c : Fin n, a.val + 1 = c.val → w⁻¹ a < w⁻¹ c := by
      intro a c h
      refine lt_of_le_of_ne (hcon a c h) ?_
      intro h'
      have := w⁻¹.injective h'
      rw [this] at h
      omega
    have key : ∀ k : ℕ, ∀ i j : Fin n, j.val = i.val + k + 1 → w⁻¹ i < w⁻¹ j := by
      intro k
      induction k with
      | zero =>
        intro i j h
        exact hadj i j (by omega)
      | succ k ih =>
        intro i j h
        have hj := j.isLt
        have hm : i.val + k + 1 < n := by omega
        exact lt_trans (ih i ⟨i.val + k + 1, hm⟩ rfl) (hadj _ _ (by show i.val + k + 1 + 1 = j.val; omega))
    have hsm : StrictMono ⇑(w⁻¹) := by
      intro i j hij
      rw [Fin.lt_def] at hij
      exact key (j.val - i.val - 1) i j (by omega)
    exact inv_eq_one.mp (eq_one_of_strictMono _ hsm)
  · apply Finset.eq_empty_of_forall_notMem
    intro p hp
    rw [mem_invSet] at hp
    simp only [inv_one, Perm.one_apply] at hp
    exact lt_asymm hp.1 hp.2
  · intro w hw
    unfold invN
    rw [invSet_rev]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hset
    apply hw
    have hall : ∀ i j : Fin n, i < j → w⁻¹ j < w⁻¹ i := by
      intro i j hij
      have hm : (i, j) ∈ invSet w := by
        rw [hset]
        simp [pairs, hij]
      exact ((mem_invSet w _).mp hm).2
    have hsm : StrictMono ⇑(w⁻¹ * (Fin.revPerm : Perm (Fin n))) := by
      intro i j hij
      simp only [Perm.mul_apply, Fin.revPerm_apply]
      exact hall _ _ (Fin.rev_lt_rev.mpr hij)
    have h1 := eq_one_of_strictMono _ hsm
    rw [mul_eq_one_iff_eq_inv] at h1
    exact inv_inj.mp h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FiniteHomOfTopFG
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem fgHom_mem_of_closed {G : Type} [Group G] [TopologicalSpace G] {s : Set G}
    (hs : TopGen s) (E : Subgroup G) (hE : IsClosed (E : Set G)) (hsE : s ⊆ E) (g : G) : g ∈ E := by
  have h1 : (Subgroup.closure s : Set G) ⊆ E := (Subgroup.closure_le E).2 hsE
  have h2 : closure (Subgroup.closure s : Set G) ⊆ E := closure_minimal h1 hE
  exact h2 (hs g)

private theorem fgHom_part1 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : TopFG G) (Z : Type) [Group Z] [Finite Z] :
    {f : G →* Z | IsOpen (f.ker : Set G)}.Finite := by
  obtain ⟨s, hsf, hs⟩ := hG
  haveI : Finite s := hsf.to_subtype
  refine Set.Finite.of_finite_image (f := fun f : G →* Z => fun x : s => f x) (Set.toFinite _) ?_
  intro f hf f' hf' h
  have hle : f.ker ⊓ f'.ker ≤ f.eqLocus f' := by
    intro x hx
    have h1 : f x = 1 := hx.1
    have h2 : f' x = 1 := hx.2
    show f x = f' x
    rw [h1, h2]
  have hop : IsOpen ((f.ker ⊓ f'.ker : Subgroup G) : Set G) := IsOpen.inter hf hf'
  have hcl : IsClosed (f.eqLocus f' : Set G) :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono hle hop)
  ext g
  exact fgHom_mem_of_closed hs _ hcl (fun x hx => congrFun h ⟨x, hx⟩) g

private theorem fgHom_part2 {G : Type} [Group G] [TopologicalSpace G]
    (hG : TopFG G) (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction G M] :
    {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + g • c h}.Finite := by
  obtain ⟨s, hsf, hs⟩ := hG
  haveI : Finite s := hsf.to_subtype
  refine Set.Finite.of_finite_image (f := fun c : G → M => fun x : s => c x) (Set.toFinite _) ?_
  intro c hc c' hc' h
  have one : ∀ d : G → M, (∀ g h, d (g * h) = d g + g • d h) → d 1 = 0 := by
    intro d hd
    have := hd 1 1
    rw [one_mul, one_smul] at this
    exact left_eq_add.1 this
  let E : Subgroup G :=
    { carrier := {g | c g = c' g}
      mul_mem' := by
        intro a b ha hb
        have ha' : c a = c' a := ha
        have hb' : c b = c' b := hb
        show c (a * b) = c' (a * b)
        rw [hc.2, hc'.2, ha', hb']
      one_mem' := by
        show c 1 = c' 1
        rw [one c hc.2, one c' hc'.2]
      inv_mem' := by
        intro a ha
        have ha' : c a = c' a := ha
        show c a⁻¹ = c' a⁻¹
        have h1 := hc.2 a a⁻¹
        have h2 := hc'.2 a a⁻¹
        rw [mul_inv_cancel, one c hc.2] at h1
        rw [mul_inv_cancel, one c' hc'.2, ← ha'] at h2
        exact MulAction.injective a (add_left_cancel (h1.symm.trans h2)) }
  have hcl : IsClosed (E : Set G) := by
    have := (hc.1.prodMk hc'.1) {p : M × M | p.1 ≠ p.2}
    rw [← isOpen_compl_iff]
    exact this
  funext g
  exact fgHom_mem_of_closed hs E hcl (fun x hx => congrFun h ⟨x, hx⟩) g

private theorem fgHom_part3 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : TopFG G) (n : ℕ) (hn : n ≠ 0) :
    {H : Subgroup G | IsOpen (H : Set G) ∧ H.index = n}.Finite := by
  have h1 := (fgHom_part1 hG (Equiv.Perm (Fin n))).prod (Set.finite_univ (α := Fin n))
  refine (h1.image fun p => (MulAction.stabilizer (Equiv.Perm (Fin n)) p.2).comap p.1).subset ?_
  rintro H ⟨hH, hi⟩
  haveI : H.FiniteIndex := ⟨hi ▸ hn⟩
  have e : (G ⧸ H) ≃ Fin n := Finite.equivFinOfCardEq hi
  refine ⟨(e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H)), e ((1 : G) : G ⧸ H)),
    ⟨?_, trivial⟩, ?_⟩
  · have hop : IsOpen (H.normalCore : Set G) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _
        (Subgroup.normalCore_isClosed H (Subgroup.isClosed_of_isOpen H hH))
    refine Subgroup.isOpen_mono ?_ hop
    intro g hg
    rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg, map_one]
  · ext g
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    have : (e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))) g • e ((1 : G) : G ⧸ H)
        = e ((g : G) : G ⧸ H) := by
      simp [Equiv.Perm.smul_def]
    rw [this, e.injective.eq_iff, eq_comm, QuotientGroup.eq, inv_one, one_mul]

theorem UpperTheory.V.AlgebraTools.finite_hom_of_topFG :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], TopFG G →
      (∀ (Z : Type) [Group Z] [Finite Z], {f : G →* Z | IsOpen (f.ker : Set G)}.Finite) ∧
      (∀ (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction G M], (∀ m : M, IsLocallyConstant fun g : G => g • m) →
        {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + g • c h}.Finite) ∧
      (∀ n : ℕ, n ≠ 0 → {H : Subgroup G | IsOpen (H : Set G) ∧ H.index = n}.Finite) := by
  intro G _ _ _ hG
  exact ⟨fun Z _ _ => fgHom_part1 hG Z, fun M _ _ _ _ => fgHom_part2 hG M,
    fun n hn => fgHom_part3 hG n hn⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FlagCharsUnique
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem exists_invariant_flag_mod_l {R : Type} [CommRing R] {n : ℕ} (P P' V : Matrix (Fin n) (Fin n) R)
    (hP : ∀ i j, j < i → P i j = 0) (hP' : ∀ i j, j < i → P' i j = 0)
    (hu : ∀ i j, j < i → IsUnit (P i i - P' j j)) (hE : P * V = V * P') :
    ∀ i j, j < i → V i j = 0 := by
  have key : ∀ j i : Fin n, j < i → V i j = 0 := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ihj =>
      intro i
      induction i using WellFoundedGT.induction with
      | ind i ihi =>
        intro hji
        have h := congrFun (congrFun hE i) j
        rw [Matrix.mul_apply, Matrix.mul_apply] at h
        have hL : ∑ k, P i k * V k j = P i i * V i j := by
          refine Finset.sum_eq_single i ?_ (by simp)
          intro k _ hk
          rcases lt_or_gt_of_ne hk with h1 | h1
          · rw [hP i k h1, zero_mul]
          · rw [ihi k h1 (hji.trans h1), mul_zero]
        have hR : ∑ k, V i k * P' k j = V i j * P' j j := by
          refine Finset.sum_eq_single j ?_ (by simp)
          intro k _ hk
          rcases lt_or_gt_of_ne hk with h1 | h1
          · rw [ihj k h1 i (h1.trans hji), zero_mul]
          · rw [hP' k j h1, mul_zero]
        rw [hL, hR] at h
        have h0 : (P i i - P' j j) * V i j = 0 := by
          linear_combination h
        exact ((hu i j hji).mul_right_eq_zero).1 h0
  intro i j h
  exact key j i h

private theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) :
    (A * B) i i = A i i * B i i :=
  _root_.UpperTheory.Reformulated.B.S8.diag_mul A B hA hB i

theorem UpperTheory.V.AlgebraTools.flag_chars_unique :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Group Γ] {n : ℕ} (r : Γ →* GL (Fin n) R) (ψ ψ' : Fin n → Γ →* Rˣ) (g g' : GL (Fin n) R), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp ((Units.coeHom R).comp (ψ i))) → (∀ i s, residue R (ψ i s) = residue R (ψ' i s)) → (∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g * r s * g⁻¹ : GL (Fin n) R) i i = (ψ i s : R)) → (∀ s, (∀ i j, j < i → (g' * r s * g'⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g' * r s * g'⁻¹ : GL (Fin n) R) i i = (ψ' i s : R)) → ψ = ψ' ∧ ∀ i j, j < i → (g * g'⁻¹ : GL (Fin n) R) i j = 0 := by
  intro R Γ _ _ _ n r ψ ψ' g g' hn hinj hres h1 h2
  obtain ⟨z, hz⟩ := UpperTheory.V.AlgebraTools.sep_chars (fun i => (Units.coeHom R).comp (ψ i)) hn hinj
  have hcomm : ∀ s, ((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      ((g' * r s * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    intro s
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have key : ∀ w : MonoidAlgebra R Γ, ∃ P P' : Matrix (Fin n) (Fin n) R,
      (∀ i j, j < i → P i j = 0) ∧ (∀ i j, j < i → P' i j = 0) ∧
      P * ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
        ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * P' ∧
      (∀ i, P i i = MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) w) ∧
      (∀ i, residue R (P' i i) = residue R (P i i)) := by
    intro w
    induction w using MonoidAlgebra.induction_on with
    | of s =>
      refine ⟨_, _, (h1 s).1, (h2 s).1, hcomm s, fun i => ?_, fun i => ?_⟩
      · rw [MonoidAlgebra.lift_of]; exact (h1 s).2 i
      · rw [(h1 s).2 i, (h2 s).2 i, hres]
    | add a b ha hb =>
      obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := ha
      obtain ⟨Q, Q', b1, b2, b3, b4, b5⟩ := hb
      refine ⟨P + Q, P' + Q', fun i j h => ?_, fun i j h => ?_, ?_, fun i => ?_, fun i => ?_⟩
      · rw [Matrix.add_apply, a1 i j h, b1 i j h, add_zero]
      · rw [Matrix.add_apply, a2 i j h, b2 i j h, add_zero]
      · rw [add_mul, mul_add, a3, b3]
      · rw [Matrix.add_apply, map_add (f := _), a4, b4]
      · rw [Matrix.add_apply, Matrix.add_apply, map_add (f := _), map_add (f := _), a5, b5]
    | smul c a ha =>
      obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := ha
      refine ⟨c • P, c • P', fun i j h => ?_, fun i j h => ?_, ?_, fun i => ?_, fun i => ?_⟩
      · rw [Matrix.smul_apply, a1 i j h, smul_zero]
      · rw [Matrix.smul_apply, a2 i j h, smul_zero]
      · rw [Matrix.smul_mul, Matrix.mul_smul, a3]
      · rw [Matrix.smul_apply, map_smul, a4]
      · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, a5]
  obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := key z
  have hV := exists_invariant_flag_mod_l P P' _ a1 a2 (fun i j h => by
    have hu := hz i j h.ne'
    rw [← a4, ← a4, ← residue_ne_zero_iff_isUnit, map_sub] at hu
    rw [← residue_ne_zero_iff_isUnit, map_sub, a5]
    exact hu) a3
  refine ⟨?_, hV⟩
  have hdet : IsUnit (((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  rw [Matrix.det_of_upperTriangular (fun i j h => hV i j h)] at hdet
  funext i
  ext s
  have hu : IsUnit (((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i) :=
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem
      (fun k => ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) k k) (Finset.mem_univ i)) hdet
  have h := congrFun (congrFun (hcomm s) i) i
  rw [diag_mul _ _ (h1 s).1 hV, diag_mul _ _ hV (h2 s).1, (h1 s).2 i, (h2 s).2 i, mul_comm] at h
  exact hu.mul_left_cancel h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.GenExt
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_surj_over_finite :
    ∀ (P Γ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [TotallyDisconnectedSpace P] [Group Γ] (r h : ℕ) (x : Fin (r + h) → P) (γ : Fin r → Γ) (π : P →* Γ), TopGen (Set.range x) →
      (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (y : Fin (r + h) → G), ∃ f : P →* G, Continuous f ∧ ∀ i, f (x i) = y i) →
      Function.Surjective γ → IsOpen (π.ker : Set P) → (∀ i, π (x (Fin.castAdd h i)) = γ i) → (∀ i, π (x (Fin.natAdd r i)) = 1) →
      ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (q : G →* Γ), IsOpen (q.ker : Set G) → ∀ g : Fin r → G, (∀ i, q (g i) = γ i) →
        (∃ z : Fin h → q.ker, TopGen (Set.range z)) →
        ∃ f : P →* G, Continuous f ∧ Function.Surjective f ∧ q.comp f = π ∧ ∀ i, f (x (Fin.castAdd h i)) = g i := by
  intro P Γ _ _ _ _ _ _ r h x γ π hden huniv hγ hπo hπl hπr G _ _ _ _ _ q hqo g hg hz
  obtain ⟨z, hzd⟩ := hz
  obtain ⟨f, hf, hfx⟩ := huniv G (Fin.append g (fun j => (z j : G)))
  have hfl : ∀ i, f (x (Fin.castAdd h i)) = g i := fun i => by
    rw [hfx, Fin.append_left]
  have hfr : ∀ j, f (x (Fin.natAdd r j)) = z j := fun j => by
    rw [hfx, Fin.append_right]
  refine ⟨f, hf, ?_, ?_, hfl⟩
  · haveI : T2Space G := inferInstance
    have hRc : IsClosed (Set.range f) := (isCompact_range hf).isClosed
    have hker : ∀ k : q.ker, (k : G) ∈ Set.range f := by
      let S : Set q.ker := Subtype.val ⁻¹' Set.range f
      have hSc : IsClosed S := hRc.preimage continuous_subtype_val
      have hsub : ((Subgroup.closure (Set.range z) : Subgroup q.ker) : Set q.ker) ⊆ S := by
        have : Subgroup.closure (Set.range z) ≤ f.range.comap q.ker.subtype := by
          rw [Subgroup.closure_le]
          rintro _ ⟨j, rfl⟩
          exact ⟨x (Fin.natAdd r j), hfr j⟩
        intro a ha
        exact this ha
      have hdS : Dense S := hzd.mono hsub
      intro k
      have : k ∈ S := by
        rw [← hSc.closure_eq, hdS.closure_eq]
        trivial
      exact this
    intro a
    obtain ⟨i, hi⟩ := hγ (q a)
    have hmem : (g i)⁻¹ * a ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hg i, hi, inv_mul_cancel]
    obtain ⟨p1, hp1⟩ := hker ⟨_, hmem⟩
    refine ⟨x (Fin.castAdd h i) * p1, ?_⟩
    rw [map_mul, hfl, hp1]
    simp
  · set φ := q.comp f with hφ
    have hgen : Set.EqOn φ π (Set.range x) := by
      rintro _ ⟨k, rfl⟩
      induction k using Fin.addCases with
      | left i => simp [hφ, hfl, hg, hπl]
      | right j =>
        simp only [hφ, MonoidHom.comp_apply, hfr, hπr]
        exact (z j).2
    have hcl : Set.EqOn φ π (Subgroup.closure (Set.range x)) := MonoidHom.eqOn_closure hgen
    have hφo : IsOpen (φ.ker : Set P) := by
      have : (φ.ker : Set P) = f ⁻¹' (q.ker : Set G) := by
        ext a
        simp [hφ]
      rw [this]
      exact hqo.preimage hf
    ext p
    let V : Set P := (fun a => p⁻¹ * a) ⁻¹' ((π.ker : Set P) ∩ (φ.ker : Set P))
    have hVo : IsOpen V := (hπo.inter hφo).preimage (continuous_const.mul continuous_id)
    have hpV : p ∈ V := by
      simp [V]
    obtain ⟨d, ⟨hd1, hd2⟩, hdD⟩ := hden.inter_open_nonempty V hVo ⟨p, hpV⟩
    have e1 : π (p⁻¹ * d) = 1 := hd1
    have e2 : φ (p⁻¹ * d) = 1 := hd2
    rw [map_mul, map_inv, inv_mul_eq_one] at e1 e2
    rw [e2, hcl hdD, ← e1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDualEx
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem exists_lt_apply {n : ℕ} (w : Perm (Fin n)) (hw : w ≠ 1) : ∃ i, i < w i := by
  by_contra h
  push_neg at h
  apply hw
  have hs : ∑ i, (w i).val = ∑ i : Fin n, i.val := Equiv.sum_comp w (fun i => i.val)
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (w i).val ≤ i.val := fun i _ => h i
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  exact Equiv.ext fun i => Fin.ext (by simpa using heq i (Finset.mem_univ _))

theorem UpperTheory.V.AlgebraTools.hkDualEx :
    ∀ (R : Type) [CommRing R] (n : ℕ), ∃ (ι : Type) (_ : Fintype ι) (a b : ι → MvPolynomial (Fin n) R), IsDual a b := by
  intro R _ n
  refine ⟨Finset (Fin n × Fin n), inferInstance,
    fun t => if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0,
    fun t => ∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R), ?_⟩
  intro w
  have hsum : ∑ t : Finset (Fin n × Fin n), (if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0) *
      rename w (∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R)) =
      ∏ p ∈ pairs n, ((X p.2 : MvPolynomial (Fin n) R) + -X (w p.1)) := by
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun t : Finset (Fin n × Fin n) => t ⊆ pairs n) = (pairs n).powerset := by
      ext t
      simp
    rw [hf, Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [map_prod, rename_X]
  refine hsum.trans ?_
  split_ifs with h1
  · subst h1
    rw [De]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [sub_eq_add_neg]
  · obtain ⟨i, hi⟩ := exists_lt_apply w h1
    apply Finset.prod_eq_zero (i := (i, w i))
    · simp [pairs, hi]
    · simp
end

