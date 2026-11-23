module

public import Formalism.GradedWeylDivisibility.FinalD

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BideterminantAntidiagEvalWeightUnitSupport
section
open MvPolynomial Formalism.GradedWeylDivisibility

theorem UpperTheory.bideterminant_antidiag_eval_weight_unit_support :
    ∀ (R : Type) [CommRing R] (n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n), (∀ x : Matrix (Fin n) (Fin n) R, (∀ i j, j < i → x i j = 0) → eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (rowAct R x.transpose (bideterminant R sz hsz I)) = (∏ i, x i i ^ shapeDeg sz (Fin.rev i)) * eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I)) ∧ ((∀ k p, (I k p : ℕ) + sz k = n + p) → IsUnit (eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I))) ∧ ((∀ k, StrictMono (I k)) → eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I) ≠ 0 → ∀ k p, (I k p : ℕ) + sz k = n + p) := by
  intro R _ n K sz hsz I
  have hrev : ∀ {s : ℕ} (hs : s ≤ n) (a : Fin n) (r : Fin s),
      a = Fin.rev (Fin.castLE hs r) ↔ (a : ℕ) + r + 1 = n := by
    intro s hs a r
    rw [Fin.ext_iff, Fin.val_rev, Fin.coe_castLE]
    have := a.isLt
    have := r.isLt
    omega
  have key : ∀ φ : MvPolynomial (Fin n × Fin n) R →+* R, φ (bideterminant R sz hsz I) =
      ∏ k, (Matrix.of fun p q : Fin (sz k) => φ (X (I k p, Fin.castLE (hsz k) q))).det := by
    intro φ
    simp only [bideterminant, initMinor, map_prod, RingHom.map_det]
    rfl
  have hE : eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I)
      = ∏ k, (Matrix.of fun p q : Fin (sz k) => if (I k p : ℕ) + q + 1 = n then (1 : R) else 0).det := by
    rw [key]
    congr 1
    ext k
    congr 1
    ext p q
    simp [hrev]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hR : eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0)
        (rowAct R x.transpose (bideterminant R sz hsz I)) =
        ∏ k, (Matrix.of fun p q : Fin (sz k) => x (Fin.rev (Fin.castLE (hsz k) q)) (I k p)).det := by
      refine (key ((eval fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0).comp
        (rowAct R x.transpose).toRingHom)).trans ?_
      congr 1
      ext k
      congr 1
      ext p q
      simp [rowAct, Matrix.transpose_apply, mul_ite, Finset.sum_ite_eq']
    have hk : ∀ (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n),
        (Matrix.of fun p q : Fin s => x (Fin.rev (Fin.castLE hs q)) (J p)).det =
        (Matrix.of fun p q : Fin s => if (J p : ℕ) + q + 1 = n then (1 : R) else 0).det *
          ∏ q : Fin s, x (Fin.rev (Fin.castLE hs q)) (Fin.rev (Fin.castLE hs q)) := by
      intro s hs J
      have hU : (Matrix.of fun r q : Fin s =>
          x (Fin.rev (Fin.castLE hs q)) (Fin.rev (Fin.castLE hs r))).IsUpperTriangular := by
        intro r q hqr
        simp only [id, Matrix.of_apply] at hqr ⊢
        apply hx
        rw [Fin.lt_iff_val_lt_val] at hqr ⊢
        simp only [Fin.val_rev, Fin.coe_castLE]
        have := r.isLt
        omega
      have hdU := Matrix.det_of_upperTriangular hU
      simp only [Matrix.of_apply] at hdU
      rw [← hdU, ← Matrix.det_mul]
      congr 1
      ext p q
      simp only [Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
      have hJ := (J p).isLt
      have hq := q.isLt
      by_cases h : (J p : ℕ) + s < n
      · rw [Finset.sum_eq_zero]
        · apply hx
          rw [Fin.lt_iff_val_lt_val]
          simp only [Fin.val_rev, Fin.coe_castLE]
          omega
        · intro r _
          rw [if_neg]
          have := r.isLt
          omega
      · rw [Finset.sum_eq_single (⟨n - 1 - (J p : ℕ), by omega⟩ : Fin s)]
        · rw [if_pos (by simp only; omega)]
          congr 1
          ext
          simp only [Fin.val_rev, Fin.coe_castLE]
          omega
        · intro b _ hb
          rw [if_neg]
          intro h'
          apply hb
          ext
          simp only
          omega
        · intro h'
          exact absurd (Finset.mem_univ _) h'
    have hreg : ∀ k, ∏ q : Fin (sz k), x (Fin.rev (Fin.castLE (hsz k) q)) (Fin.rev (Fin.castLE (hsz k) q))
        = ∏ i : Fin n, if ((Fin.rev i : Fin n) : ℕ) < sz k then x i i else 1 := by
      intro k
      rw [← Finset.prod_filter]
      refine Finset.prod_bij (fun q _ => Fin.rev (Fin.castLE (hsz k) q)) ?_ ?_ ?_ ?_
      · intro q _
        simp
        have := q.isLt
        have := hsz k
        omega
      · intro a _ b _ h
        simpa using h
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        refine ⟨⟨(Fin.rev b : ℕ), hb⟩, Finset.mem_univ _, ?_⟩
        ext
        simp only [Fin.val_rev, Fin.coe_castLE]
        have := b.isLt
        omega
      · intro q _
        rfl
    rw [hR, hE, Finset.prod_congr rfl (fun k _ => hk (sz k) (hsz k) (I k)),
      Finset.prod_mul_distrib, mul_comm]
    congr 1
    rw [Finset.prod_congr rfl (fun k _ => hreg k), Finset.prod_comm]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rfl
  · intro hI
    rw [hE]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro k _
    have hP : (Matrix.of fun p q : Fin (sz k) => if (I k p : ℕ) + q + 1 = n then (1 : R) else 0)
        = (Fin.revPerm).permMatrix R := by
      ext p q
      have h1 := hI k p
      have h2 := p.isLt
      have h3 := q.isLt
      have h4 := hsz k
      have hiff : ((I k p : ℕ) + q + 1 = n) ↔ q ∈ (Fin.revPerm : Equiv.Perm (Fin (sz k))).toPEquiv p := by
        simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply,
          Fin.ext_iff, Fin.val_rev]
        constructor <;> intro <;> omega
      rw [Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      exact if_congr hiff rfl rfl
    rw [hP, Matrix.det_permutation]
    exact (Units.isUnit _).map (Int.castRingHom R)
  · intro hmono hne k p
    rw [hE] at hne
    have hdet : (Matrix.of fun p q : Fin (sz k) =>
        if (I k p : ℕ) + q + 1 = n then (1 : R) else 0).det ≠ 0 :=
      fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ k) h0)
    have hlow : ∀ p : Fin (sz k), n ≤ (I k p : ℕ) + sz k := by
      intro p
      by_contra hlt
      push_neg at hlt
      apply hdet
      apply Matrix.det_eq_zero_of_row_eq_zero p
      intro q
      simp only [Matrix.of_apply]
      rw [if_neg]
      have := q.isLt
      omega
    have hA : ∀ d : ℕ, ∀ a b : Fin (sz k), (b : ℕ) = a + d → (I k a : ℕ) + d ≤ I k b := by
      intro d
      induction d with
      | zero =>
        intro a b h
        have : a = b := Fin.ext (by omega)
        subst this
        simp
      | succ d ih =>
        intro a b h
        have hb' : (a : ℕ) + d < sz k := by
          have := b.isLt
          omega
        have h1 := ih a ⟨a + d, hb'⟩ rfl
        have h2 : I k ⟨a + d, hb'⟩ < I k b := hmono k (by rw [Fin.lt_iff_val_lt_val]; simp only; omega)
        rw [Fin.lt_iff_val_lt_val] at h2
        omega
    have hs : 0 < sz k := by
      have := p.isLt
      omega
    have h0 := hA p ⟨0, hs⟩ p (by simp)
    have hl := hlow ⟨0, hs⟩
    have h1 := hA (sz k - 1 - p) p ⟨sz k - 1, by omega⟩ (by simp only; have := p.isLt; omega)
    have := (I k ⟨sz k - 1, by omega⟩).isLt
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BideterminantRowWeightDominance
section
open MvPolynomial Formalism.GradedWeylDivisibility

private theorem sum_ite_eq_of_shifted_index {n m : ℕ} (g : Fin m → Fin n) (hg : ∀ p, (g p : ℕ) = n - m + p)
    (hm : m ≤ n) (i : Fin n) :
    (∑ p : Fin m, if g p = i then 1 else 0 : ℕ) = if n - m ≤ (i : ℕ) then 1 else 0 := by
  by_cases h : n - m ≤ (i : ℕ)
  · rw [if_pos h, Finset.sum_eq_single (⟨i - (n - m), by have := i.isLt; omega⟩ : Fin m)]
    · rw [if_pos]
      ext
      rw [hg]
      show n - m + ((i : ℕ) - (n - m)) = (i : ℕ)
      omega
    · intro p _ hp
      rw [if_neg]
      intro he
      apply hp
      ext
      have := hg p
      rw [he] at this
      show (p : ℕ) = (i : ℕ) - (n - m)
      omega
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    intro he
    apply h
    have := hg p
    rw [he] at this
    omega

private theorem sum_ite_pair_castLE_eq_of_shifted_index {n m : ℕ} (hm : m ≤ n) (g : Fin m → Fin n)
    (hg : ∀ p, (g p : ℕ) = n - m + p) (i j : Fin n) :
    (∑ p : Fin m, if (g p, Fin.castLE hm p) = (i, j) then 1 else 0 : ℕ)
      = if m + (i : ℕ) = n + j then 1 else 0 := by
  by_cases h : m + (i : ℕ) = n + j
  · rw [if_pos h, Finset.sum_eq_single (⟨j, by have := i.isLt; omega⟩ : Fin m)]
    · rw [if_pos]
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
      · show ((g _ : Fin n) : ℕ) = (i : ℕ)
        rw [hg]
        show n - m + (j : ℕ) = (i : ℕ)
        omega
      · simp
    · intro p _ hp
      rw [if_neg]
      intro he
      apply hp
      ext
      have := congrArg (fun x => (x.2 : ℕ)) he
      simp only [Fin.coe_castLE] at this
      show (p : ℕ) = (j : ℕ)
      exact this
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    intro he
    apply h
    have h1 := congrArg (fun x => (x.1 : ℕ)) he
    have h2 := congrArg (fun x => (x.2 : ℕ)) he
    simp only [Fin.coe_castLE] at h1 h2
    rw [hg] at h1
    have := p.isLt
    omega

private theorem strictMono_apply_add_le {n m : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (p : Fin m) :
    (f p : ℕ) + m ≤ n + p := by
  have h1 := Finset.card_le_card_of_injOn f (s := Finset.Ici p) (t := Finset.Ici (f p))
    (by
      intro q hq
      simp only [Finset.coe_Ici, Set.mem_Ici, Finset.mem_Ici] at hq ⊢
      exact hf.monotone hq)
    (fun a _ b _ h => hf.injective h)
  simp only [Fin.card_Ici] at h1
  have := p.isLt
  have := (f p).isLt
  omega

private theorem sum_mul_count_eq_sum_sum_apply {n K : ℕ} (sz : Fin K → ℕ) (f : ∀ k, Fin (sz k) → Fin n)
    (a : Fin n → ℤ) :
    ∑ i, a i * ((∑ k, ∑ p : Fin (sz k), if f k p = i then 1 else 0 : ℕ) : ℤ)
      = ∑ k, ∑ p, a (f k p) := by
  push_cast
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

private theorem rowWt_bidetExp_eq_count {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (i : Fin n) :
    rowWt (bidetExp sz hsz I) i = ∑ k, ∑ p : Fin (sz k), if I k p = i then 1 else 0 := by
  simp only [rowWt, rowDeg, bidetExp, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Prod.mk.injEq]
  by_cases h : I k p = i
  · simp [h]
  · simp [h]

private theorem shapeDeg_rev_eq_count_of_shifted {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (J : ∀ k, Fin (sz k) → Fin n) (hJ : ∀ k p, (J k p : ℕ) = n - sz k + p) (i : Fin n) :
    shapeDeg sz (Fin.rev i) = ∑ k, ∑ p : Fin (sz k), if J k p = i then 1 else 0 := by
  rw [Finset.sum_congr rfl fun k _ => sum_ite_eq_of_shifted_index (J k) (hJ k) (hsz k) i, shapeDeg,
    Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.val_rev]
  have := i.isLt
  by_cases h : n - sz k ≤ (i : ℕ)
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

private theorem bidetExp_apply_eq_card_of_canonical {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (hcan : ∀ k p, (I k p : ℕ) + sz k = n + p) (i j : Fin n) :
    bidetExp sz hsz I (i, j) = (Finset.univ.filter fun k => sz k + (i : ℕ) = n + j).card := by
  simp only [bidetExp, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_ite_pair_castLE_eq_of_shifted_index (hsz k) (I k) (fun p => by have := hcan k p; have := hsz k; omega) i j

private theorem card_lt_eq_card_eq_succ_add_card_succ_lt {K : ℕ} (s : Fin K → ℕ) (t : ℕ) :
    (Finset.univ.filter fun k => t < s k).card
      = (Finset.univ.filter fun k => s k = t + 1).card
        + (Finset.univ.filter fun k => t + 1 < s k).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> omega

theorem UpperTheory.bideterminant_row_weight_dominance :
    ∀ (n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n), (∀ k, StrictMono (I k)) → (∀ a : Fin n → ℤ, Antitone a → ∑ i, a i * (shapeDeg sz (Fin.rev i) : ℤ) ≤ ∑ i, a i * (rowWt (bidetExp sz hsz I) i : ℤ)) ∧ (∑ i : Fin n, ((n : ℤ) - 1 - (i : ℕ)) * (rowWt (bidetExp sz hsz I) i : ℤ) ≤ ∑ i : Fin n, ((n : ℤ) - 1 - (i : ℕ)) * (shapeDeg sz (Fin.rev i) : ℤ) → ∀ k p, (I k p : ℕ) + sz k = n + p) ∧ ((∀ k p, (I k p : ℕ) + sz k = n + p) → (∀ i, rowWt (bidetExp sz hsz I) i = shapeDeg sz (Fin.rev i)) ∧ ∀ (K' : ℕ) (sz' : Fin K' → ℕ) (hsz' : ∀ k, sz' k ≤ n) (I' : ∀ k, Fin (sz' k) → Fin n), (∀ k p, (I' k p : ℕ) + sz' k = n + p) → (shapeDeg sz' : Fin n → ℕ) = shapeDeg sz → bidetExp sz' hsz' I' = bidetExp sz hsz I) := by
  intro n K sz hsz I hI
  obtain ⟨J, hJ⟩ : ∃ J : ∀ k, Fin (sz k) → Fin n, ∀ k p, (J k p : ℕ) = n - sz k + p :=
    ⟨fun k p => ⟨n - sz k + p, by have := p.isLt; have := hsz k; omega⟩, fun _ _ => rfl⟩
  have hrow := rowWt_bidetExp_eq_count sz hsz I
  have hsh := shapeDeg_rev_eq_count_of_shifted sz hsz J hJ
  have hle : ∀ k p, (I k p : ℕ) + sz k ≤ n + p := fun k p => strictMono_apply_add_le (I k) (hI k) p
  have hws : ∀ a : Fin n → ℤ, ∑ i, a i * (shapeDeg sz (Fin.rev i) : ℤ) = ∑ k, ∑ p, a (J k p) := by
    intro a
    simp only [hsh]
    exact sum_mul_count_eq_sum_sum_apply sz J a
  have hwr : ∀ a : Fin n → ℤ,
      ∑ i, a i * (rowWt (bidetExp sz hsz I) i : ℤ) = ∑ k, ∑ p, a (I k p) := by
    intro a
    simp only [hrow]
    exact sum_mul_count_eq_sum_sum_apply sz I a
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [hws, hwr]
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun p _ => ha ?_
    rw [Fin.le_iff_val_le_val, hJ]
    have := hle k p
    have := hsz k
    omega
  · intro h k p
    have e1 := hws (fun i : Fin n => (n : ℤ) - 1 - ((i : ℕ) : ℤ))
    have e2 := hwr (fun i : Fin n => (n : ℤ) - 1 - ((i : ℕ) : ℤ))
    beta_reduce at e1 e2
    rw [e1, e2] at h
    by_contra hne
    refine absurd h (not_le.2 ?_)
    apply Finset.sum_lt_sum
    · intro k' _
      apply Finset.sum_le_sum
      intro p' _
      have := hle k' p'
      have := hJ k' p'
      have := hsz k'
      omega
    · refine ⟨k, Finset.mem_univ _, Finset.sum_lt_sum (fun p' _ => ?_) ⟨p, Finset.mem_univ _, ?_⟩⟩
      · have := hle k p'
        have := hJ k p'
        have := hsz k
        omega
      · have := hle k p
        have := hJ k p
        have := hsz k
        omega
  · intro hcan
    have hIJ : I = J := by
      funext k p
      ext
      rw [hJ]
      have := hcan k p
      have := hsz k
      omega
    refine ⟨fun i => by rw [hrow i, hsh i, hIJ], ?_⟩
    intro K' sz' hsz' I' hcan' hshape
    ext x
    obtain ⟨i, j⟩ := x
    rw [bidetExp_apply_eq_card_of_canonical sz' hsz' I' hcan' i j, bidetExp_apply_eq_card_of_canonical sz hsz I hcan i j]
    have hc : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz' k).card
        = (Finset.univ.filter fun k => t < sz k).card := by
      intro t
      by_cases ht : t < n
      · have := congrFun hshape ⟨t, ht⟩
        simpa only [shapeDeg, Fin.val_mk] using this
      · have e1 : (Finset.univ.filter fun k => t < sz' k) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun k _ => by have := hsz' k; omega
        have e2 : (Finset.univ.filter fun k => t < sz k) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun k _ => by have := hsz k; omega
        rw [e1, e2, Finset.card_empty, Finset.card_empty]
    have e1 : (Finset.univ.filter fun k => sz' k + (i : ℕ) = n + j)
        = Finset.univ.filter fun k => sz' k = (n + j - i - 1) + 1 :=
      Finset.filter_congr fun k _ => by have := i.isLt; omega
    have e2 : (Finset.univ.filter fun k => sz k + (i : ℕ) = n + j)
        = Finset.univ.filter fun k => sz k = (n + j - i - 1) + 1 :=
      Finset.filter_congr fun k _ => by have := i.isLt; omega
    rw [e1, e2]
    have h1 := card_lt_eq_card_eq_succ_add_card_succ_lt sz' (n + j - i - 1)
    have h2 := card_lt_eq_card_eq_succ_add_card_succ_lt sz (n + j - i - 1)
    have h3 := hc (n + j - i - 1)
    have h4 := hc (n + j - i - 1 + 1)
    omega
end

