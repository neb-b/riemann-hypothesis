module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0011

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AllowedLettersOfLateRows
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem detPl_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ)
    (s : Set (ℤ × Fin r)) (h : ∀ a b, (X.row j x a, b) ∈ s) : X.detPl R j x ∈ supported R s := by
  unfold Dat.detPl
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (prod_mem fun i _ => ?_) _
  rw [Matrix.of_apply]
  exact (MvPolynomial.X_mem_supported).2 (h _ _)

theorem DlSeg_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (j : ℤ)
    (s : Set (ℤ × Fin r)) (h : ∀ x ∈ X.toLate j, ∀ a b, (X.row j x a, b) ∈ s) : X.DlSeg p K R j ∈ supported R s := by
  unfold Dat.DlSeg
  exact prod_mem fun x hx => pow_mem (detPl_supported R X j x s (h x hx)) _

theorem ellP_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (s : Set (ℤ × Fin r)) (h : ∀ x ∈ X.toLate j, ∀ b, (x, b) ∈ s) :
    X.ellP K R j e ∈ supported R s := by
  unfold Dat.ellP
  exact prod_mem fun x hx => prod_mem fun c _ => pow_mem ((MvPolynomial.X_mem_supported).2 (h x hx c)) _

theorem ellN_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (s : Set (ℤ × Fin K)) (h : ∀ x ∈ X.toLate j, ∀ b, (x, b) ∈ s) :
    X.ellN K R j e ∈ supported R s := by
  unfold Dat.ellN
  exact prod_mem fun x hx => prod_mem fun c _ => pow_mem ((MvPolynomial.X_mem_supported).2 (h x hx c)) _

theorem allowed_letters_of_late_rows (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ) (hRow : LateIndexInjective) : ProductAllowedLetters C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hW
  classical
  have hX := hW.hX
  haveI : Fact p.Prime := ⟨hX.prime⟩
  have hlet : ∀ i : Fin (segN X.F j), segE X.F j i ∈ X.F.letters j := fun i =>
    ((X.F.letters j).orderIsoOfFin rfl i).2
  have hren : ∀ {k : ℕ} (P : MvPolynomial (Fin (segN X.F j) × Fin k) (FF O)) (s : Set (ℤ × Fin k)),
      (∀ v ∈ P.vars, (segE X.F j v.1, v.2) ∈ s) → segRen X.F j (FF O) k P ∈ supported (FF O) s := by
    intro k P s hs
    rw [MvPolynomial.mem_supported]
    intro v hv
    unfold segRen at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ P hv)
    exact hs w hw
  obtain ⟨b', b'', ⟨P1, hP1⟩, ⟨P2, hP2⟩, hcond⟩ := hW.hq
  refine ⟨?_, ?_⟩
  · unfold Dat.Aw
    refine mul_mem (mul_mem (pow_mem (hren _ _ fun v _ => hlet v.1) _) ?_) ?_
    · exact ellP_supported (FF O) X K j e _ fun x hx c => (Finset.mem_filter.1 hx).1
    · exact DlSeg_supported (FF O) X p K j _ fun x hx a c => ((hRow p n' r K X hX j x hx).2 a).1
  · unfold Dat.Gw
    have hA := (hA3 p O S (segN X.F j) K (segLL X.F j) b'' (fun i => q.2 i.succ (lastIdx K))
      (fun i => q.2 i.succ 0)).2
    have hPol : Psi (FF O) q.2 I'' ∈ Pol (FF O) K b'' :=
      ((Set.ext_iff.1 hA _).2 (Submodule.subset_span ⟨P2, I'', by rw [hP2]; exact hW.hI'',
        fun i => by rw [hP2]; exact ⟨le_rfl, le_rfl⟩, by rw [hP2]⟩)).1
    have hseg : segRen X.F j (FF O) K (Psi (FF O) q.2 I'') ∈
        supported (FF O) {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1} := by
      refine hren _ _ fun v hv => ⟨hlet v.1, fun hWv => ?_⟩
      obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars_iff_mem_support _).1 hv
      have hb0 : b'' v.1 = 0 := (hcond v.1).1 hWv
      have hsum : multideg m v.1 = b'' v.1 := ((MvPolynomial.mem_restrictSupport_iff _).1 hPol) hm v.1
      rw [hb0] at hsum
      have h0 : m (v.1, v.2) = 0 := Finset.sum_eq_zero_iff.1 hsum v.2 (Finset.mem_univ _)
      exact (Finsupp.mem_support_iff.1 hvm) h0
    refine mul_mem (pow_mem hseg _) ?_
    exact ellN_supported (FF O) X K j e _ fun x hx c =>
      ⟨(Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩

def DegAt {R : Type} [CommRing R] {ι : Type} {n : ℕ} (x : ι) (d : ℕ) (P : MvPolynomial (ι × Fin n) R) : Prop :=
  ∀ m ∈ P.support, multideg m x = d

section DegAt

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι}

theorem degAt_mul {d d' : ℕ} {P Q : MvPolynomial (ι × Fin n) R} (hP : DegAt x d P) (hQ : DegAt x d' Q) :
    DegAt x (d + d') (P * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hm)
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) (hP a ha) (hQ b hb)

theorem degAt_one : DegAt x 0 (1 : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have h0 : m = 0 := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm hne)])
  subst h0
  simp [multideg]

theorem degAt_pow {d : ℕ} {P : MvPolynomial (ι × Fin n) R} (hP : DegAt x d P) (k : ℕ) : DegAt x (k * d) (P ^ k) := by
  induction k with
  | zero => rw [pow_zero, zero_mul]; exact degAt_one
  | succ k ih => rw [pow_succ, add_mul, one_mul]; exact degAt_mul ih hP

theorem degAt_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ι × Fin n) R) (d : κ → ℕ)
    (h : ∀ i ∈ s, DegAt x (d i) (f i)) : DegAt x (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact degAt_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact degAt_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem degAt_X [DecidableEq ι] (v : ι × Fin n) : DegAt x (if v.1 = x then 1 else 0) (X v : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have h0 : Finsupp.single v 1 = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_X', if_neg hne])
  subst h0
  obtain ⟨a, c0⟩ := v
  by_cases ha : a = x
  · subst ha
    simp [multideg, Finsupp.single_apply, Prod.ext_iff]
  · simp [multideg, Finsupp.single_apply, Prod.ext_iff, ha]

theorem degAt_of_supported {P : MvPolynomial (ι × Fin n) R} (s : Set (ι × Fin n)) (hP : P ∈ supported R s)
    (hs : ∀ v ∈ s, v.1 ≠ x) : DegAt x 0 P := by
  intro m hm
  rw [MvPolynomial.mem_supported] at hP
  show ∑ c, m (x, c) = 0
  refine Finset.sum_eq_zero fun c _ => ?_
  by_contra hne
  have hv : (x, c) ∈ P.vars := (MvPolynomial.mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 hne⟩
  exact hs _ (hP hv) rfl

end DegAt

theorem degAt_segRen {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ) {n : ℕ}
    {b : Fin (segN F j) → ℕ} {A : MvPolynomial (Fin (segN F j) × Fin n) R} (hA : A ∈ Pol R n b) (i : Fin (segN F j)) :
    DegAt (segE F j i) (b i) (segRen F j R n A) := by
  classical
  have hinj : Function.Injective (fun v : Fin (segN F j) × Fin n => (segE F j v.1, v.2)) := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [Prod.mk.injEq] at h
    have ha : a = a' := ((F.letters j).orderIsoOfFin rfl).injective (Subtype.ext (by exact h.1))
    rw [ha, h.2]
  intro m hm
  unfold segRen at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h0 := ((MvPolynomial.mem_restrictSupport_iff _).1 hA) hm0
  show ∑ c, (Finsupp.mapDomain _ m0) (segE F j i, c) = b i
  rw [← h0 i]
  exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hinj m0 (i, c)

theorem ordDeg_prod {R : Type} [CommRing R] {r K : ℕ} {x : ℤ} {dA dG : ℕ} {A : MvPolynomial (ℤ × Fin r) R}
    {G : MvPolynomial (ℤ × Fin K) R} (hA : ¬ Even x → DegAt x dA A) (hG : Even x → DegAt x dG G) :
    ∀ mm ∈ (plEmb R r K A * nmEmb R r K G).support, ordDeg mm x = if Even x then dG else dA := by
  classical
  intro mm hmm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hmm)
  have hi1 : Function.Injective (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) := by
    rintro ⟨u1, u2⟩ ⟨w1, w2⟩ h
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    rw [h.1, h.2]
  have hi2 : Function.Injective (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) := by
    rintro ⟨u1, u2⟩ ⟨w1, w2⟩ h
    simp only [Prod.mk.injEq, Fin.natAdd_inj] at h
    rw [h.1, h.2]
  unfold plEmb at ha
  unfold nmEmb at hb
  rw [MvPolynomial.support_rename_of_injective hi1, Finset.mem_image] at ha
  rw [MvPolynomial.support_rename_of_injective hi2, Finset.mem_image] at hb
  obtain ⟨a0, ha0, rfl⟩ := ha
  obtain ⟨b0, hb0, rfl⟩ := hb
  unfold ordDeg
  split_ifs with hx
  · have h1 : ∀ c : Fin K, (Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) a0)
        (x, Fin.natAdd r c) = 0 := fun c => by
      refine Finsupp.mapDomain_notin_range _ _ ?_
      rintro ⟨⟨y, d⟩, h⟩
      simp only [Prod.mk.injEq] at h
      have := congrArg Fin.val h.2
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, h1, Finset.sum_const_zero, zero_add]
    rw [← hG hx b0 hb0]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hi2 b0 (x, c)
  · have h1 : ∀ c : Fin r, (Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) b0)
        (x, Fin.castAdd K c) = 0 := fun c => by
      refine Finsupp.mapDomain_notin_range _ _ ?_
      rintro ⟨⟨y, d⟩, h⟩
      simp only [Prod.mk.injEq] at h
      have := congrArg Fin.val h.2
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, h1, Finset.sum_const_zero, add_zero]
    rw [← hA hx a0 ha0]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hi1 a0 (x, c)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DomOfStripDown
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

theorem glueT_lt (t : ℕ) (be : ℤ) (τ : Fin (K + t) → ℤ) (m : Fin (r + K)) (h : m.val < r - t) :
    glueT t be τ m = be := by
  unfold glueT; rw [dite_eq_left h]

theorem glueT_ge (t : ℕ) (ht : t ≤ r) (be : ℤ) (τ : Fin (K + t) → ℤ) (m : Fin (r + K)) (h : r - t ≤ m.val) :
    glueT t be τ m = τ ⟨m.val - (r - t), by have := m.2; omega⟩ := by
  unfold glueT; rw [dite_eq_right (by omega), dite_eq_left]

theorem dom_of_strip_up {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) (hν : Dominant ν) : Dominant μ := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with he | hlt
  · rw [he]
  · have hm1 : (m'.val - 1) + 1 < n := by have := m'.2; have : m.val < m'.val := hlt; omega
    have h2 := h.2.1 ⟨m'.val - 1, by have := m'.2; omega⟩ hm1
    have hme : (⟨(m'.val - 1) + 1, hm1⟩ : Fin n) = m' := Fin.ext (by simp only; have : m.val < m'.val := hlt; omega)
    rw [hme] at h2
    have h3 : ν ⟨m'.val - 1, by have := m'.2; omega⟩ ≤ ν m :=
      hν (by rw [Fin.le_def]; simp only; have : m.val < m'.val := hlt; omega)
    exact le_trans h2 (le_trans h3 (h.1 m))

theorem dom_of_strip_down {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip μ ν b) (hν : Dominant ν) : Dominant μ := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with he | hlt
  · rw [he]
  · have hlt' : m.val < m'.val := hlt
    have hm1 : m.val + 1 < n := by have := m'.2; omega
    have h2 := h.2.1 m hm1
    have h3 : ν m' ≤ ν ⟨m.val + 1, hm1⟩ := hν (by rw [Fin.le_def]; simp only; omega)
    exact le_trans (h.1 m') (le_trans h3 h2)

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
theorem tau_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (H : HypT N n0 r K LL B od bb a La p)
    (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (t s : ℕ) (hst : s + t = N) (_ht : t ≤ r) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (K + t) (tailT t (μ0 ⟨s, by omega⟩)) := by
  intro t
  induction t with
  | zero =>
    intro s hst _ μ0 hv
    have hsN : s = N := by omega
    subst hsN
    have hμ : μ0 ∈ SP (r := r) (K := K) LL n0 B := (sp_iff H μ0).2 hv
    have hA : Af hfin s μ0 = (finite_St (tanPart μ0)).toFinset.image (fun I => (μ0, I)) := by
      ext q
      unfold Af
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image]
      constructor
      · rintro ⟨⟨_, h2⟩, h3'⟩
        have hq : q.1 = μ0 := funext fun t => h3' t (by have := t.2; omega)
        exact ⟨q.2, by rw [← hq]; exact h2, Prod.ext hq.symm rfl⟩
      · rintro ⟨I, hI, rfl⟩
        exact ⟨⟨hμ, hI⟩, fun t _ => rfl⟩
    have hdom : Dominant (pEnd (tanPart μ0)) := by
      intro x y hxy
      exact hv.2.1 (Fin.last s) (by simp) (by rw [Fin.le_def] at hxy ⊢; simp; omega)
    rw [hA, Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).2), ← Set.ncard_eq_toFinset_card _ (finite_St (tanPart μ0)),
      wt_eq D h3 _ hdom]
    show stCount K _ = stCount K _
    congr 1
    funext l
    have := tailT_apply (r := r) (K := K) 0 (Nat.zero_le r) (μ0 ⟨s, by omega⟩) l
    rw [show (tailT 0 (μ0 ⟨s, by omega⟩) : Fin (K + 0) → ℤ) l = _ from this]
    unfold pEnd tanPart
    congr 1
  | succ t ih =>
    intro s hst ht μ0 hv
    have hs : s < N := by omega
    have hN := H.hN
    have hn0 : n0 ≤ s := by omega
    have hla : ∀ m, μ0 (⟨s, hs⟩ : Fin N).castSucc m ≤ (beA n0 B : ℤ) := fun m => vp_le hv s (by omega) le_rfl m
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    generalize hlaeq : μ0 (⟨s, hs⟩ : Fin N).castSucc = la at hla hlad
    have hheads : ∀ m : Fin (r + K), m.val + 1 < r - t → la m = (beA n0 B : ℤ) := by
      intro m hm
      have hs1 : s - 1 < N := by omega
      have h1 := ((hv.2.2 ⟨s - 1, hs1⟩ (by simp only; omega)).2 (by simp only; omega)).2 m (by simp only; omega)
      have he : (⟨s - 1, hs1⟩ : Fin N).succ = (⟨s, hs⟩ : Fin N).castSucc := Fin.ext (by simp; omega)
      rw [he, hlaeq] at h1
      exact h1
    have hν : ∀ l : Fin (K + t + 1), (tailT (t + 1) la : Fin (K + t + 1) → ℤ) l =
        la ⟨(r - (t + 1)) + l.val, by have := l.2; omega⟩ := fun l => tailT_apply (t + 1) ht la l
    have hνdom : Dominant (tailT (t + 1) la : Fin (K + t + 1) → ℤ) := by
      intro x y hxy
      rw [hν, hν]
      exact hlad (by rw [Fin.le_def] at hxy ⊢; simp only; omega)
    set ν : Fin (K + t + 1) → ℤ := tailT (t + 1) la with hνdef
    set T := Fintype.piFinset (fun l : Fin (K + t) => Finset.Icc (ν l.succ) (ν l.castSucc)) with hT
    have hτ : ∀ τ ∈ T, ∀ l : Fin (K + t), ν l.succ ≤ τ l ∧ τ l ≤ ν l.castSucc := by
      intro τ hτ l
      rw [hT, Fintype.mem_piFinset] at hτ
      exact Finset.mem_Icc.mp (hτ l)
    have hinj : Set.InjOn (glueT (r := r) t (beA n0 B : ℤ)) (T : Set (Fin (K + t) → ℤ)) := by
      intro τ _ τ' _ h
      rw [← tailT_glueT (r := r) t (by omega) (beA n0 B : ℤ) τ, h, tailT_glueT (r := r) t (by omega)]
    have hE : ∀ q ∈ Af hfin s μ0, q.1 (⟨s, hs⟩ : Fin N).succ ∈ T.image (glueT (r := r) t (beA n0 B : ℤ)) := by
      intro q hq
      obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
      rw [hlaeq] at hstq
      obtain ⟨⟨d, hS⟩, hh⟩ := hstq.2 hn0
      generalize q.1 (⟨s, hs⟩ : Fin N).succ = la' at hS hh
      rw [Finset.mem_image]
      refine ⟨tailT t la', ?_, ?_⟩
      · rw [hT, Fintype.mem_piFinset]
        intro l
        have hl := l.2
        rw [Finset.mem_Icc, hν, hν, tailT_apply t (by omega)]
        constructor
        · have := hS.1 ⟨(r - t) + l.val, by omega⟩
          have he : (⟨(r - (t + 1)) + (l.succ : Fin (K + t + 1)).val, by simp; omega⟩ : Fin (r + K)) =
              ⟨(r - t) + l.val, by omega⟩ := Fin.ext (by simp; omega)
          rw [he]; exact this
        · have := hS.2.1 ⟨(r - (t + 1)) + l.val, by omega⟩ (by simp only; omega)
          have he : (⟨(r - (t + 1)) + l.val + 1, by omega⟩ : Fin (r + K)) = ⟨(r - t) + l.val, by omega⟩ :=
            Fin.ext (by simp only; omega)
          rw [he] at this
          exact this
      · funext m
        by_cases hm : m.val < r - t
        · rw [glueT_lt t _ _ m hm, hh m (by simp only; omega)]
        · rw [glueT_ge t (by omega) _ _ m (by omega), tailT_apply t (by omega)]
          congr 1
          exact Fin.ext (by simp only; omega)
    have hterm : ∀ τ ∈ T, (Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ
        (glueT (r := r) t (beA n0 B : ℤ) τ))).card = stCount (K + t) τ := by
      intro τ hτT
      have hb := hτ τ hτT
      have hτanti : ∀ l l' : Fin (K + t), l ≤ l' → τ l' ≤ τ l := by
        intro l l' hll
        rcases eq_or_lt_of_le hll with he | hlt
        · rw [he]
        · have h1 := (hb l').2
          have h2 := (hb l).1
          have h3 : ν l'.castSucc ≤ ν l.succ := hνdom (by rw [Fin.le_def]; simp; exact hlt)
          linarith
      have hτbe : ∀ l : Fin (K + t), τ l ≤ (beA n0 B : ℤ) := by
        intro l
        refine le_trans (hb l).2 ?_
        rw [hν]; exact hla _
      have hd' : Dominant (glueT (r := r) t (beA n0 B : ℤ) τ) := by
        intro m m' hmm
        have hmm' : m.val ≤ m'.val := hmm
        by_cases h1 : m'.val < r - t
        · rw [glueT_lt t _ _ m' h1, glueT_lt t _ _ m (by omega)]
        · rw [glueT_ge t (by omega) _ _ m' (by omega)]
          by_cases h2 : m.val < r - t
          · rw [glueT_lt t _ _ m h2]; exact hτbe _
          · rw [glueT_ge t (by omega) _ _ m (by omega)]
            exact hτanti _ _ (by rw [Fin.le_def]; simp only; omega)
      have hS1 : ∀ x, la x ≤ glueT (r := r) t (beA n0 B : ℤ) τ x := by
        intro x
        by_cases h1 : x.val < r - t
        · rw [glueT_lt t _ _ x h1]; exact hla x
        · rw [glueT_ge t (by omega) _ _ x (by omega)]
          have h2 := (hb ⟨x.val - (r - t), by have := x.2; omega⟩).1
          rw [hν] at h2
          have he : (⟨(r - (t + 1)) + ((⟨x.val - (r - t), by have := x.2; omega⟩ : Fin (K + t)).succ :
              Fin (K + t + 1)).val, by have := x.2; simp; omega⟩ : Fin (r + K)) = x := Fin.ext (by simp; omega)
          rw [he] at h2
          exact h2
      have hst' : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) (glueT (r := r) t (beA n0 B : ℤ) τ) := by
        rw [hlaeq]
        refine ⟨fun h => absurd h (by simp only; omega), fun _ => ⟨⟨(∑ x, (glueT (r := r) t (beA n0 B : ℤ) τ x - la x)).toNat,
          hS1, ?_, ?_⟩, fun m hm => glueT_lt t _ _ m (by simp only at hm; omega)⟩⟩
        · intro x hx
          by_cases h1 : x.val + 1 < r - t
          · rw [glueT_lt t _ _ _ (by simp only; exact h1), hheads x h1]
          · rw [glueT_ge t (by omega) _ _ _ (by simp only; omega)]
            have h2 := (hb ⟨x.val + 1 - (r - t), by have := x.2; omega⟩).2
            rw [hν] at h2
            have he : (⟨(r - (t + 1)) + ((⟨x.val + 1 - (r - t), by have := x.2; omega⟩ : Fin (K + t)).castSucc :
                Fin (K + t + 1)).val, by have := x.2; simp; omega⟩ : Fin (r + K)) = x := Fin.ext (by simp; omega)
            rw [he] at h2
            exact h2
        · exact (Int.toNat_of_nonneg (Finset.sum_nonneg fun x _ => sub_nonneg.mpr (hS1 x))).symm
      have hv' := vp_update hs hv _ hd' hst'
      rw [ih (s + 1) (by omega) (by omega) _ hv']
      congr 1
      show tailT t (Function.update μ0 (⟨s, hs⟩ : Fin N).succ (glueT (r := r) t (beA n0 B : ℤ) τ)
        (⟨s, hs⟩ : Fin N).succ) = τ
      rw [Function.update_self, tailT_glueT t (by omega)]
    rw [Af_card_sum hfin s hs μ0 _ hE, Finset.sum_image hinj, Finset.sum_congr rfl hterm]
    have h4' := h4 (K + t) ν hνdom
    show _ = stCount (K + t + 1) (tailT (t + 1) (μ0 (⟨s, hs⟩ : Fin N).castSucc))
    rw [hlaeq]
    exact h4'.symm

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

