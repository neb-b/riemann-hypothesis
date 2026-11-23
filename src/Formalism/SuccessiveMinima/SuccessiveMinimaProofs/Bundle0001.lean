module

public import Formalism.SuccessiveMinima.DefsMink

@[expose] public section

-- bundled from Formalism.SuccessiveMinima.SuccessiveMinimaProofs.AdaptedBasis
section
open Module Submodule

noncomputable section

namespace Formalism.FN.AdaptedBasisExistence

theorem exists_nsmul_mem_span {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type} [Fintype ι]
    (B : Basis ι ℝ E) (hB : ∀ i, B i ∈ L) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, N • x ∈ span ℤ (Set.range B) := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hKL : span ℤ (Set.range B) ≤ L := by
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    exact hB i
  have hdisc : IsDiscrete (L : Set E) := IsDiscrete.mk (inferInstance : DiscreteTopology L)
  haveI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hclosed : IsClosed (L : Set E) := (L.toAddSubgroup).isClosed_of_discreteTopology
  have hfin : (ZSpan.fundamentalDomain B ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed hdisc (ZSpan.fundamentalDomain_isBounded B) hclosed
  obtain ⟨S, hS⟩ : ∃ S : Finset E, ∀ y, y ∈ S ↔ y ∈ ZSpan.fundamentalDomain B ∩ (L : Set E) :=
    ⟨hfin.toFinset, fun y => hfin.mem_toFinset⟩
  refine ⟨S.card.factorial, Nat.factorial_pos _, fun x hx => ?_⟩
  have hmem : ∀ k : ℕ, ZSpan.fract B (k • x) ∈ S := by
    intro k
    rw [hS]
    refine ⟨ZSpan.fract_mem_fundamentalDomain B _, ?_⟩
    rw [ZSpan.fract_apply]
    exact L.sub_mem (nsmul_mem hx k) (hKL (ZSpan.floor B (k • x)).2)
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (S.card + 1) => (⟨ZSpan.fract B ((k : ℕ) • x), hmem k⟩ : S)) (by simp)
  have heq' : ZSpan.fract B ((a : ℕ) • x) = ZSpan.fract B ((b : ℕ) • x) :=
    congrArg Subtype.val heq
  rw [ZSpan.fract_eq_fract] at heq'
  have hab' : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  have key : ∃ k : ℕ, 0 < k ∧ k ≤ S.card ∧ k • x ∈ span ℤ (Set.range B) := by
    rcases lt_or_gt_of_ne hab' with h | h
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt h
      refine ⟨c + 1, Nat.succ_pos _, by omega, ?_⟩
      have e : -((a : ℕ) • x) + (b : ℕ) • x = (c + 1) • x := by
        rw [hc, add_assoc, add_nsmul]
        abel
      rw [← e]
      exact heq'
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt h
      refine ⟨c + 1, Nat.succ_pos _, by omega, ?_⟩
      have e : -(-((a : ℕ) • x) + (b : ℕ) • x) = (c + 1) • x := by
        rw [hc, add_assoc, add_nsmul]
        abel
      rw [← e]
      exact neg_mem heq'
  obtain ⟨k, hk0, hkS, hkx⟩ := key
  obtain ⟨d, hd⟩ := Nat.dvd_factorial hk0 hkS
  rw [hd, mul_comm, ← smul_smul]
  exact nsmul_mem hkx d

end Formalism.FN.AdaptedBasisExistence

namespace Formalism.FN.AdaptedBasisExistence


set_option maxHeartbeats 800000 in
theorem adapted_basis_exists : AdaptedBasis := by
  delta Formalism.FN.AdaptedBasis
  intro E _ _ _ L _ _ v hv hvL
  classical
  have hsp0 : ⊤ ≤ span ℝ (Set.range v) :=
    (hv.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)).ge
  let B : Basis (Fin (finrank ℝ E)) ℝ E := Basis.mk hv hsp0
  have hBv : ∀ i, B i = v i := fun i => congrFun (Basis.coe_mk hv hsp0) i
  obtain ⟨N, hN, hNL⟩ := exists_nsmul_mem_span L B (fun i => by rw [hBv]; exact hvL i)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hint : ∀ x ∈ L, ∀ k, ∃ z : ℤ, (N : ℝ) * B.repr x k = z := by
    intro x hx k
    obtain ⟨z, hz⟩ := (Basis.mem_span_iff_repr_mem ℤ B (N • x)).mp (hNL x hx) k
    have hz' : (z : ℝ) = (N : ℝ) * B.repr x k := by simpa using hz
    exact ⟨z, hz'.symm⟩
  have hP : ∀ j : Fin (finrank ℝ E), ∃ m : ℕ, 0 < m ∧ ∃ x, (x ∈ L ∧ ∀ k, j < k → B.repr x k = 0) ∧
      (N : ℝ) * B.repr x j = m := by
    intro j
    refine ⟨N, hN, v j, ⟨hvL j, fun k hk => ?_⟩, ?_⟩
    · rw [← hBv, B.repr_self, Finsupp.single_apply, if_neg (ne_of_lt hk)]
    · rw [← hBv, B.repr_self, Finsupp.single_apply, if_pos rfl, mul_one]
  have hm := fun j => Nat.find_spec (hP j)
  have hmin := fun j (r : ℕ) (hr : r < Nat.find (hP j)) => Nat.find_min (hP j) hr
  choose b hbG hbj using fun j => (hm j).2
  have hdiv : ∀ j x, (x ∈ L ∧ ∀ k, j < k → B.repr x k = 0) →
      ∃ q : ℤ, B.repr x j = q * B.repr (b j) j := by
    intro j x hx
    obtain ⟨z, hz⟩ := hint x hx.1 j
    have hmpos : 0 < (Nat.find (hP j) : ℤ) := by exact_mod_cast (hm j).1
    have hr0 : 0 ≤ z % (Nat.find (hP j) : ℤ) := Int.emod_nonneg _ hmpos.ne'
    have hrlt : z % (Nat.find (hP j) : ℤ) < Nat.find (hP j) := Int.emod_lt_of_pos _ hmpos
    have hcast : ((z % (Nat.find (hP j) : ℤ) : ℤ) : ℝ) =
        (z : ℝ) - ((z / (Nat.find (hP j) : ℤ) : ℤ) : ℝ) * (Nat.find (hP j) : ℝ) := by
      have h := congrArg (fun t : ℤ => (t : ℝ)) (Int.ediv_mul_add_emod z (Nat.find (hP j) : ℤ))
      push_cast at h
      linarith
    by_cases hr : z % (Nat.find (hP j) : ℤ) = 0
    · refine ⟨z / (Nat.find (hP j) : ℤ), ?_⟩
      apply mul_left_cancel₀ hN'
      rw [hz, mul_left_comm, hbj]
      rw [hr] at hcast
      push_cast at hcast
      linarith
    · exfalso
      have hrpos : 0 < z % (Nat.find (hP j) : ℤ) := lt_of_le_of_ne hr0 (Ne.symm hr)
      have e : ∀ k, B.repr (x - (z / (Nat.find (hP j) : ℤ)) • b j) k =
          B.repr x k - ((z / (Nat.find (hP j) : ℤ) : ℤ) : ℝ) * B.repr (b j) k := by
        intro k
        simp
      refine hmin j (z % (Nat.find (hP j) : ℤ)).toNat (by omega)
        ⟨by omega, x - (z / (Nat.find (hP j) : ℤ)) • b j,
          ⟨L.sub_mem hx.1 (L.smul_mem _ (hbG j).1), fun k hk => ?_⟩, ?_⟩
      · rw [e, hx.2 k hk, (hbG j).2 k hk, mul_zero, sub_zero]
      · rw [e, mul_sub, mul_left_comm, hbj, hz]
        have h2 : (((z % (Nat.find (hP j) : ℤ)).toNat : ℕ) : ℝ) =
            ((z % (Nat.find (hP j) : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hr0
        rw [h2, hcast]
  have hspan : ∀ r : ℕ, ∀ x ∈ L, (∀ k : Fin (finrank ℝ E), r ≤ k.val → B.repr x k = 0) →
      x ∈ span ℤ (b '' {k | k.val < r}) := by
    intro r
    induction r with
    | zero =>
      intro x _ h0
      have hx0 : x = 0 := B.repr.injective (by ext k; simp [h0 k (Nat.zero_le _)])
      rw [hx0]
      exact zero_mem _
    | succ r ih =>
      intro x hx h
      by_cases hr : r < finrank ℝ E
      · obtain ⟨q, hq⟩ := hdiv ⟨r, hr⟩ x ⟨hx, fun k hk => h k (by rw [Fin.lt_def] at hk; exact hk)⟩
        have e : ∀ k, B.repr (x - q • b ⟨r, hr⟩) k = B.repr x k - (q : ℝ) * B.repr (b ⟨r, hr⟩) k := by
          intro k
          simp
        have hy : x - q • b ⟨r, hr⟩ ∈ span ℤ (b '' {k | k.val < r}) := by
          refine ih _ (L.sub_mem hx (L.smul_mem q (hbG _).1)) fun k hk => ?_
          rw [e]
          rcases Nat.lt_or_ge r k.val with hk' | hk'
          · rw [h k hk', (hbG _).2 k (by rw [Fin.lt_def]; exact hk'), mul_zero, sub_zero]
          · have hkr : k = ⟨r, hr⟩ := Fin.ext (show k.val = r by omega)
            rw [hkr, hq, sub_self]
        have hb_mem : b ⟨r, hr⟩ ∈ span ℤ (b '' {k | k.val < r + 1}) :=
          subset_span ⟨⟨r, hr⟩, by simp, rfl⟩
        have hmono : span ℤ (b '' {k | k.val < r}) ≤ span ℤ (b '' {k | k.val < r + 1}) :=
          span_mono (Set.image_mono fun k (hk : k.val < r) => show k.val < r + 1 by omega)
        have hsum := add_mem (hmono hy) (smul_mem _ q hb_mem)
        rwa [sub_add_cancel] at hsum
      · have hmono : span ℤ (b '' {k | k.val < r}) ≤ span ℤ (b '' {k | k.val < r + 1}) :=
          span_mono (Set.image_mono fun k (hk : k.val < r) => show k.val < r + 1 by omega)
        exact hmono (ih x hx fun k hk => absurd k.isLt (by omega))
  have hbL : ∀ j, b j ∈ L := fun j => (hbG j).1
  have hall : ∀ x ∈ L, x ∈ span ℤ (Set.range b) := fun x hx =>
    span_mono (Set.image_subset_range _ _)
      (hspan (finrank ℝ E) x hx fun k hk => absurd k.isLt (by omega))
  let b' : Fin (finrank ℝ E) → L := fun j => ⟨b j, hbL j⟩
  have hsp : ⊤ ≤ span ℤ (Set.range b') := by
    rintro x -
    have h2 := hall x x.2
    have h3 : Set.range b = L.subtype '' Set.range b' := by
      rw [← Set.range_comp]
      rfl
    rw [h3, ← Submodule.map_span, Submodule.mem_map] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    rwa [← Subtype.ext hyx]
  have hliR : LinearIndependent ℝ b := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (Fintype.card_fin _)
    refine le_trans hsp0 (span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    exact span_le_restrictScalars ℤ ℝ _ (hall _ (hvL i))
  have hliZ : LinearIndependent ℤ b' :=
    LinearIndependent.of_comp L.subtype (hliR.restrict_scalars' ℤ)
  refine ⟨Basis.mk hliZ hsp, fun j => ?_⟩
  simp only [Basis.coe_mk]
  change span ℝ (b '' {k | k ≤ j}) = span ℝ (v '' {k | k ≤ j})
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [Set.mem_setOf_eq] at hk
    have hvB : v '' {k | k ≤ j} = B '' {k | k ≤ j} := Set.image_congr fun i _ => (hBv i).symm
    rw [SetLike.mem_coe, hvB, B.mem_span_image]
    intro i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    by_contra hij
    rw [Set.mem_setOf_eq, not_le] at hij
    exact hi ((hbG k).2 i (lt_of_le_of_lt hk hij))
  · rw [span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [Set.mem_setOf_eq] at hi
    have hvi := hspan (j.val + 1) (v i) (hvL i) fun k hk => by
      rw [← hBv, B.repr_self, Finsupp.single_apply, if_neg]
      intro hik
      rw [hik, Fin.le_def] at hi
      omega
    have hsub : {k : Fin (finrank ℝ E) | k.val < j.val + 1} ⊆ {k | k ≤ j} := by
      intro k hk
      simp only [Set.mem_setOf_eq] at hk ⊢
      rw [Fin.le_def]
      omega
    exact span_le_restrictScalars ℤ ℝ _ (span_mono (Set.image_mono hsub) hvi)

end Formalism.FN.AdaptedBasisExistence

theorem Formalism.FN.existsAdaptedBasis : Formalism.FN.AdaptedBasis := Formalism.FN.AdaptedBasisExistence.adapted_basis_exists
end
end

-- bundled from Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjLevel
section
open MeasureTheory Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

lemma measurableSet_boxJ (n j : ℕ) : MeasurableSet (boxJ n j) := by
  have h : boxJ n j = ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < j),
      ({u : Fin n → ℝ | 0 ≤ u i} ∩ {u | u i < 1}) := by
    ext u; simp [boxJ]
  rw [h]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem partialBoxVolumeMonotoneStep : GjLevel := by
  intro n j A hj hA hinj
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin n, (jj : ℕ) = j := ⟨⟨j, hj⟩, rfl⟩
  let ej : Fin n → ℝ := Pi.single jj 1
  have ej_apply : ∀ i, ej i = if i = jj then 1 else 0 := fun i => by simp [ej, Pi.single_apply]
  have hcoord : ∀ (y : Fin n → ℝ) (m : ℤ) (i : Fin n),
      (y + (m : ℝ) • ej) i = if i = jj then y i + m else y i := by
    intro y m i
    simp only [Pi.add_apply, Pi.smul_apply, ej_apply, smul_eq_mul]
    split_ifs <;> ring

  let S : Set (Fin n → ℝ) := boxJ n j ∩ (A + latJ n j)
  let P : ℤ → Set (Fin n → ℝ) := fun m => S ∩ {x | ⌊x jj⌋ = m}
  let Q : ℤ → Set (Fin n → ℝ) := fun m => (fun y => y + (m : ℝ) • ej) ⁻¹' P m
  have hSm : MeasurableSet S := (measurableSet_boxJ n j).inter (hA.add_right (t := latJ n j)).measurableSet
  have hPm : ∀ m, MeasurableSet (P m) := fun m =>
    hSm.inter ((Int.measurable_floor.comp (measurable_pi_apply jj)) (measurableSet_singleton m))
  have hQm : ∀ m, MeasurableSet (Q m) := fun m => (measurable_id.add_const _) (hPm m)
  have hvol : ∀ m, volume (Q m) = volume (P m) := fun m =>
    measure_preimage_add_right volume _ (P m)
  have hsub : ∀ m, Q m ⊆ boxJ n (j + 1) ∩ (A + latJ n (j + 1)) := by
    intro m y hy
    obtain ⟨⟨hbox, hAk⟩, hfl⟩ := hy
    have hfl' : ⌊(y + (m : ℝ) • ej) jj⌋ = m := hfl
    rw [hcoord, if_pos rfl, Int.floor_add_intCast] at hfl'
    have h0 : ⌊y jj⌋ = 0 := by omega
    have hyj := Int.floor_eq_zero_iff.1 h0
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases hij : i = jj
      · subst hij; exact ⟨hyj.1, hyj.2⟩
      · have hlt : (i : ℕ) < j :=
          lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) (fun h => hij (Fin.ext (h.trans hjj.symm)))
        have hb : 0 ≤ (y + (m : ℝ) • ej) i ∧ (y + (m : ℝ) • ej) i < 1 := hbox i hlt
        rw [hcoord, if_neg hij] at hb
        exact hb
    · obtain ⟨a, ha, k, hk, hak0⟩ := hAk
      have hak : a + k = y + (m : ℝ) • ej := hak0
      refine Set.mem_add.2 ⟨a, ha, k - (m : ℝ) • ej, ⟨?_, ?_⟩, ?_⟩
      · intro i
        obtain ⟨z, hz⟩ := hk.1 i
        refine ⟨z - (if i = jj then m else 0), ?_⟩
        simp only [Pi.sub_apply, Pi.smul_apply, ej_apply, smul_eq_mul, hz]
        split_ifs <;> push_cast <;> ring
      · intro i hi
        have hne : i ≠ jj := fun h => by rw [h, hjj] at hi; omega
        simp [hk.2 i (by omega), ej_apply, hne]
      · rw [← add_sub_assoc, hak, add_sub_cancel_right]
  have hdisj : Pairwise (Function.onFun Disjoint Q) := by
    intro m m' hmm'
    rw [Function.onFun, Set.disjoint_left]
    intro y hy hy'
    obtain ⟨⟨_, hAk⟩, _⟩ := hy
    obtain ⟨⟨_, hAk'⟩, _⟩ := hy'
    obtain ⟨a, ha, k, hk, hak0⟩ := hAk
    obtain ⟨a', ha', k', hk', hak0'⟩ := hAk'
    have hak : a + k = y + (m : ℝ) • ej := hak0
    have hak' : a' + k' = y + (m' : ℝ) • ej := hak0'
    have hint : ∀ i, ∃ z : ℤ, a i - a' i = z := by
      intro i
      obtain ⟨z, hz⟩ := hk.1 i
      obtain ⟨z', hz'⟩ := hk'.1 i
      have e1 := congrFun hak i
      have e2 := congrFun hak' i
      rw [Pi.add_apply, hcoord] at e1 e2
      split_ifs at e1 e2
      · exact ⟨m - m' - z + z', by push_cast; linarith⟩
      · exact ⟨-z + z', by push_cast; linarith⟩
    have hjeq := hinj a ha a' ha' hint jj hjj.ge
    have hk0 : k jj = 0 := hk.2 jj hjj.ge
    have hk0' : k' jj = 0 := hk'.2 jj hjj.ge
    have e1 := congrFun hak jj
    have e2 := congrFun hak' jj
    rw [Pi.add_apply, hcoord, if_pos rfl, hk0, add_zero] at e1
    rw [Pi.add_apply, hcoord, if_pos rfl, hk0', add_zero] at e2
    apply hmm'
    exact_mod_cast (by linarith : (m : ℝ) = m')
  have hcover : S ⊆ ⋃ m : ℤ, P m := fun x hx => Set.mem_iUnion.2 ⟨⌊x jj⌋, hx, rfl⟩
  calc Gj n j A = volume S := rfl
    _ ≤ volume (⋃ m : ℤ, P m) := measure_mono hcover
    _ ≤ ∑' m, volume (P m) := measure_iUnion_le _
    _ = ∑' m, volume (Q m) := tsum_congr fun m => (hvol m).symm
    _ = volume (⋃ m, Q m) := (measure_iUnion hdisj hQm).symm
    _ ≤ volume (boxJ n (j + 1) ∩ (A + latJ n (j + 1))) := measure_mono (Set.iUnion_subset hsub)
    _ = Gj n (j + 1) A := rfl

end Formalism.FN
end
end

-- bundled from Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MeasureEqCovolumeMulVolumeImage
section
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

theorem measure_eq_covolume_mul_volume_image {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type} [Fintype ι] (b : Basis ι ℤ L) (S : Set E) :
    μ S = ENNReal.ofReal (ZLattice.covolume L μ) *
      volume ((b.ofZLatticeBasis ℝ L).equivFun '' S) := by
  set B := b.ofZLatticeBasis ℝ L with hB
  let f : E ≃ᵐ (ι → ℝ) := B.equivFunL.toHomeomorph.toMeasurableEquiv
  have hf : (f : E → ι → ℝ) = B.equivFun := rfl
  have : (μ.map f).IsAddHaarMeasure := B.equivFunL.isAddHaarMeasure_map μ
  have huniq := MeasureTheory.Measure.isAddLeftInvariant_eq_smul (μ.map f) volume
  obtain ⟨c, hc⟩ : ∃ c, c = MeasureTheory.Measure.addHaarScalarFactor (μ.map f) volume := ⟨_, rfl⟩
  rw [← hc] at huniq
  have himg : ∀ T : Set E, μ T = c * volume (B.equivFun '' T) := by
    intro T
    have h1 : μ T = μ.map f (f '' T) := by
      rw [MeasurableEquiv.map_apply, Set.preimage_image_eq T f.injective]
    rw [h1, huniq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hf]
  have hD : (B.equivFun : E → ι → ℝ) '' ZSpan.fundamentalDomain B =
      Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1 := by
    have h : ZSpan.fundamentalDomain B =
        (B.equivFun : E → ι → ℝ) ⁻¹' (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) := by
      ext x
      simp [ZSpan.mem_fundamentalDomain, Set.mem_pi]
    rw [h, Set.image_preimage_eq _ B.equivFun.surjective]
  have hvol : volume (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]
    simp
  have hcov : c = ENNReal.ofReal (ZLattice.covolume L μ) := by
    have h := himg (ZSpan.fundamentalDomain B)
    rw [hD, hvol, mul_one] at h
    rw [← h, ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ),
      measureReal_def, ENNReal.ofReal_toReal]
    exact (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded B)).ne
  rw [himg S, hcov]

theorem minkowskiIIUpper_of (hc : MinkCore) (hs : SuccMinFacts) (ha : AdaptedBasis) :
    MinkowskiIIUpper := by
  intro E _ _ _ _ _ μ _ L _ _ K hKc hKconv hKsymm hK0
  obtain ⟨v, hvli, hvL, hvK, hpos, hmono, hspan⟩ := hs L K hKc hKconv hKsymm hK0
  obtain ⟨b, hb⟩ := ha L v hvli hvL
  set B := b.ofZLatticeBasis ℝ L with hB
  have hBfun : ∀ i, B i = (b i : E) := fun i => by simp [hB]
  set lam : Fin (finrank ℝ E) → ℝ := fun i => succMin L K ((i : ℕ) + 1) with hlam
  have hneg : ∀ a ∈ interior K, -a ∈ interior K := by
    intro a ha'
    have hU : IsOpen ((fun x : E => -x) ⁻¹' interior K) := isOpen_interior.preimage continuous_neg
    have hsub : (fun x : E => -x) ⁻¹' interior K ⊆ K := fun x hx => by
      simpa using hKsymm _ (interior_subset hx)
    exact interior_maximal hsub hU (by simpa using ha')
  have hCo : IsOpen (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    B.equivFunL.toHomeomorph.isOpenMap _ (isOpen_interior.smul₀ (by norm_num))
  have hCc : Convex ℝ (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    (hKconv.interior.smul (1 / 2 : ℝ)).linear_image B.equivFun.toLinearMap
  have hCs : ∀ x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K),
      -x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Set.mem_smul_set] at hw
    obtain ⟨a, ha', rfl⟩ := hw
    exact ⟨(1 / 2 : ℝ) • -a, Set.smul_mem_smul_set (hneg a ha'), by rw [smul_neg, map_neg]⟩
  have hCb : Bornology.IsBounded (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    B.equivFunL.lipschitzWith.isBounded_image ((hKc.isBounded.subset interior_subset).smul₀ _)
  have key := hc (finrank ℝ E) (B.equivFun '' ((1 / 2 : ℝ) • interior K)) lam hCo hCc hCs hCb
    hpos hmono (by
      intro j x hx y hy hint i hji
      rw [Set.mem_smul_set] at hx hy
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hx
      obtain ⟨_, ⟨w', hw', rfl⟩, rfl⟩ := hy
      rw [Set.mem_smul_set] at hw hw'
      obtain ⟨a, ha', rfl⟩ := hw
      obtain ⟨a', ha'', rfl⟩ := hw'
      obtain ⟨u, hu⟩ : ∃ u, u = lam j • ((1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a') := ⟨_, rfl⟩
      have heu : B.equivFun u =
          lam j • B.equivFun ((1 / 2 : ℝ) • a) - lam j • B.equivFun ((1 / 2 : ℝ) • a') := by
        rw [hu, map_smul B.equivFun (lam j), map_sub, smul_sub]
      have hrepr : ∀ i, B.repr u i =
          (lam j • B.equivFun ((1 / 2 : ℝ) • a)) i - (lam j • B.equivFun ((1 / 2 : ℝ) • a')) i := by
        intro i
        have h := congrFun heu i
        rw [B.equivFun_apply] at h
        exact h
      have huL : u ∈ L := by
        rw [← B.sum_repr u]
        refine sum_mem fun i _ => ?_
        obtain ⟨m, hm⟩ := hint i
        rw [hrepr i, hm, hBfun i]
        rw [Int.cast_smul_eq_zsmul ℝ m]
        exact L.smul_mem m (b i).2
      have hmid : (1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a' ∈ interior K := by
        rw [sub_eq_add_neg, ← smul_neg]
        exact hKconv.interior ha' (hneg a' ha'') (by norm_num) (by norm_num) (by norm_num)
      have hmem : u ∈ Submodule.span ℝ (v '' {k | k < j}) :=
        hspan j u huL (by rw [hu]; exact Set.smul_mem_smul_set hmid)
      have hsub : Submodule.span ℝ (v '' {k | k < j}) ≤ Submodule.span ℝ (B '' {k | k < j}) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        have h1 : v k ∈ Submodule.span ℝ (v '' {k' | k' ≤ k}) :=
          Submodule.subset_span ⟨k, le_refl k, rfl⟩
        rw [← hb k] at h1
        refine Submodule.span_mono ?_ h1
        rintro _ ⟨k', hk', rfl⟩
        exact ⟨k', show k' < j from lt_of_le_of_lt hk' hk, hBfun k'⟩
      have hsupp := (B.mem_span_image).mp (hsub hmem)
      have hz : B.repr u i = 0 := by
        by_contra h
        exact absurd (hsupp (Finsupp.mem_support_iff.mpr h)) (not_lt.mpr hji)
      have h0 := hrepr i
      rw [hz] at h0
      exact sub_eq_zero.mp h0.symm)
  have hthm := measure_eq_covolume_mul_volume_image μ L b ((1 / 2 : ℝ) • interior K)
  rw [← hB] at hthm
  have hhalf : μ ((1 / 2 : ℝ) • interior K) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ finrank ℝ E) * μ (interior K) := by
    rw [Measure.addHaar_smul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ finrank ℝ E)]
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hIfin : μ (interior K) < ⊤ := lt_of_le_of_lt (measure_mono interior_subset) hKfin
  have hKle : μ K ≤ μ (interior K) := by
    calc μ K ≤ μ (interior K ∪ frontier K) := by
          apply measure_mono
          intro x hx
          rw [← closure_eq_interior_union_frontier]
          exact subset_closure hx
      _ ≤ μ (interior K) + μ (frontier K) := measure_union_le _ _
      _ = μ (interior K) := by rw [hKconv.addHaar_frontier μ, add_zero]
  have hP : 0 ≤ ∏ i, lam i := Finset.prod_nonneg fun i _ => (hpos i).le
  have hc0 : 0 ≤ ZLattice.covolume L μ := (ZLattice.covolume_pos L μ).le
  have e1 : (μ ((1 / 2 : ℝ) • interior K)).toReal =
      ZLattice.covolume L μ * (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal := by
    rw [hthm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]
  have e2 : (μ ((1 / 2 : ℝ) • interior K)).toReal =
      (1 / 2 : ℝ) ^ finrank ℝ E * (μ (interior K)).toReal := by
    rw [hhalf, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have e3 : (μ (interior K)).toReal = 2 ^ finrank ℝ E * (ZLattice.covolume L μ *
      (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal) := by
    have h2 : (2 : ℝ) ^ finrank ℝ E * (1 / 2 : ℝ) ^ finrank ℝ E = 1 := by
      rw [← mul_pow]
      norm_num
    calc (μ (interior K)).toReal
        = 2 ^ finrank ℝ E * ((1 / 2 : ℝ) ^ finrank ℝ E * (μ (interior K)).toReal) := by
          rw [← mul_assoc, h2, one_mul]
      _ = _ := by rw [← e2, e1]
  have hK' : μ.real K ≤ (μ (interior K)).toReal := ENNReal.toReal_mono hIfin.ne hKle
  calc μ.real K * ∏ i, lam i ≤ (μ (interior K)).toReal * ∏ i, lam i :=
        mul_le_mul_of_nonneg_right hK' hP
    _ = 2 ^ finrank ℝ E * ZLattice.covolume L μ *
        ((volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal * ∏ i, lam i) := by
          rw [e3]
          ring
    _ ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ * 1 :=
        mul_le_mul_of_nonneg_left key (mul_nonneg (by positivity) hc0)
    _ = _ := mul_one _

end Formalism.FN
end
end

