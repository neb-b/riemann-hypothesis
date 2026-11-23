module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LinClosedOfAdic

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsMemPowerSeriesCharRatiosNotIsOfFinOrder
section
open IsLocalRing Polynomial Matrix UpperTheory.V

private lemma power_series_unit_eq_one_of_torsion (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [CharP K l]
    (y : (PowerSeries K)ˣ) (m : ℕ) (hm : m ≠ 0)
    (hc : PowerSeries.constantCoeff (y : PowerSeries K) = 1) (hy : y ^ m = 1) : y = 1 := by
  have : CharP (PowerSeries K) l :=
    charP_of_injective_ringHom (f := PowerSeries.C) PowerSeries.C_injective l
  apply Units.ext
  refine UpperTheory.V.Pr.T.oneUnitTF l (y : PowerSeries K) m hm ?_ ?_
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp [hc]
  · rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]

theorem UpperTheory.V.Ws.exists_mem_powerSeries_char_ratios_not_isOfFinOrder :
    ∀ (l : ℕ) [Fact l.Prime] (H K : Type) [Group H] [Field K] [Finite K] [CharP K l] (n : ℕ)
      (ψ : Fin n → H →* (PowerSeries K)ˣ) (N : Subgroup H),
      (∀ i j, i ≠ j → ∃ g ∈ N, PowerSeries.constantCoeff (ψ i g : PowerSeries K) = PowerSeries.constantCoeff (ψ j g : PowerSeries K) ∧
        ψ i g ≠ ψ j g) → ∃ g ∈ N, ∀ i j, i ≠ j → ¬ IsOfFinOrder (ψ i g / ψ j g) := by
  intro l _ H K _ _ _ _ n ψ N h
  classical
  have := Fintype.ofFinite K
  have hpos : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hunit : ∀ y : (PowerSeries K)ˣ, PowerSeries.constantCoeff (y : PowerSeries K) ≠ 0 := fun y =>
    (y.isUnit.map PowerSeries.constantCoeff).ne_zero
  have key := UpperTheory.V.Pr.commonFree N (PowerSeries K)ˣ {p : Fin n × Fin n // p.1 ≠ p.2}
    (fun p => (ψ p.1.1 / ψ p.1.2).comp N.subtype) (Fintype.card K - 1) hpos ?_ ?_
  · obtain ⟨g, hg⟩ := key
    refine ⟨g, g.2, fun i j hij hf => ?_⟩
    obtain ⟨m, hm, he⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    exact hg ⟨(i, j), hij⟩ m hm (by simpa using he)
  · intro p g m hm he
    refine power_series_unit_eq_one_of_torsion l K _ m hm.ne' ?_ ?_
    · rw [Units.val_pow_eq_pow_val, map_pow]
      exact FiniteField.pow_card_sub_one_eq_one _ (hunit _)
    · rw [← pow_mul, mul_comm, pow_mul, he, one_pow]
  · intro p
    obtain ⟨g, hg, hc, hne⟩ := h p.1.1 p.1.2 p.2
    refine ⟨⟨g, hg⟩, fun he => hne ?_⟩
    have h1 : ψ p.1.1 g / ψ p.1.2 g = 1 := by
      refine power_series_unit_eq_one_of_torsion l K _ _ hpos.ne' ?_ (by simpa using he)
      have h2 : (ψ p.1.1 g / ψ p.1.2 g) * ψ p.1.2 g = ψ p.1.1 g := div_mul_cancel _ _
      have h3 := congrArg (fun y : (PowerSeries K)ˣ => PowerSeries.constantCoeff (y : PowerSeries K)) h2
      simp only [Units.val_mul, map_mul] at h3
      rw [hc] at h3
      exact mul_right_cancel₀ (hunit (ψ p.1.2 g)) (h3.trans (one_mul _).symm)
    exact div_eq_one.1 h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsSignTwistCharEqOfCharpolyTwistInvariant
section
open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem charpoly_neg_roots_neg {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin n → R)
    (h : M.charpoly = ∏ i, (X - C (a i))) : (-M).charpoly = ∏ i, (X - C (-a i)) := by
  have h1 : (-M).charmatrix = -((compRingHom (-X : R[X])).mapMatrix M.charmatrix) := by
    ext i j : 1
    by_cases e : i = j
    · subst e
      simp [Matrix.charmatrix_apply_eq]
      ring
    · simp [Matrix.charmatrix_apply_ne _ _ _ e]
  have h2 := congrArg (compRingHom (-X : R[X])) h
  rw [Matrix.charpoly, RingHom.map_det, map_prod] at h2
  rw [Matrix.charpoly, h1, Matrix.det_neg, h2]
  have h3 : (-1 : R[X]) ^ Fintype.card (Fin n) = ∏ _i : Fin n, (-1 : R[X]) := by
    rw [Finset.prod_const, Finset.card_univ]
  rw [h3, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp
  ring

theorem UpperTheory.V.Ws.exists_sign_twist_char_eq_of_charpoly_twist_invariant :
    ∀ (K k k' B G : Type) [Field K] [Field k] [Field k'] [CommRing B] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) B)
      (j : B →+* K) (φ : B →+* k') (ι : k →+* k') (χ : Fin n → G →* kˣ) (η : G →* ℤˣ), Function.Injective j →
      (∀ g, (r g).charpoly.map φ = ∏ i, (X - C (ι (χ i g)))) →
      (∀ g, ((r g).map j).charpoly = ((((η g : ℤˣ) : ℤ) : K) • (r g).map j).charpoly) →
      ∀ i, ∃ i', W.pushCh (Int.castRingHom k) η * χ i = χ i' := by
  intro K k k' B G _ _ _ _ _ n r j φ ι χ η hj h1 h2 i
  have key : ∀ g, Pr.chPoly χ g = Pr.chPoly (fun i => W.pushCh (Int.castRingHom k) η * χ i) g := by
    intro g
    have hv : ∀ i, (((W.pushCh (Int.castRingHom k) η * χ i) g : kˣ) : k) = (((η g : ℤˣ) : ℤ) : k) * (χ i g : k) := by
      intro i
      rfl
    unfold Pr.chPoly
    simp only [hv]
    rcases Int.units_eq_one_or (η g) with e | e
    · simp only [e, Units.val_one, Int.cast_one, one_mul]
    · have h3 : (r g).charpoly = (-r g).charpoly := by
        apply Polynomial.map_injective j hj
        rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, h2 g, e]
        congr 1
        ext a b
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, Matrix.smul_apply, Matrix.map_apply,
          Matrix.neg_apply, map_neg, smul_eq_mul, neg_mul, one_mul]
      have h4 : ((r g).map φ).charpoly = ∏ i, (X - C (ι (χ i g))) := by rw [Matrix.charpoly_map, h1 g]
      have h5 := charpoly_neg_roots_neg _ _ h4
      have h6 : -((r g).map φ) = (-r g).map φ := by
        ext a b
        simp only [Matrix.map_apply, Matrix.neg_apply, map_neg]
      rw [h6, Matrix.charpoly_map, ← h3, h1 g] at h5
      apply Polynomial.map_injective ι ι.injective
      simp only [Polynomial.map_prod, e, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_neg, map_neg] at h5 ⊢
      exact h5
  obtain ⟨σ, hσ⟩ := Pr.charPerm G k n _ _ key
  exact ⟨σ i, hσ i⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsStabilizerIndexDvdOfNotIrreducibleRestrict
section
open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_stabilizer_index_dvd_of_not_irreducible_restriction :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) K), U3.MatIrr ⊤ r →
      ∀ N : Subgroup G, commutator G ≤ N → (∃ u ∈ N, (r u).charpoly.Separable) → ¬ U3.MatIrr N r →
      ∃ (W : Submodule K (Fin n → K)) (S : Subgroup G), W ≠ ⊥ ∧ W ≠ ⊤ ∧ N ≤ S ∧ (∀ g, g ∈ S ↔ ∀ v ∈ W, r g *ᵥ v ∈ W) ∧
        S.index ∣ n := by
  intro K G _ _ _ n r hirr N hN hu hnot
  classical
  obtain ⟨u, huN, hsep⟩ := hu
  have hconj : ∀ g h : G, h ∈ N → g⁻¹ * h * g ∈ N := by
    intro g h hh
    have hc : h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹ ∈ N :=
      hN (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have e : g⁻¹ * h * g = h * (h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹) := by
      group
    rw [e]
    exact N.mul_mem hh hc
  have hr1 : ∀ g : G, r g * r g⁻¹ = 1 := by
    intro g
    rw [← map_mul, mul_inv_cancel, map_one]
  have hr2 : ∀ g : G, r g⁻¹ * r g = 1 := by
    intro g
    rw [← map_mul, inv_mul_cancel, map_one]
  let Inv : Submodule K (Fin n → K) → Prop := fun X => ∀ g ∈ N, ∀ v ∈ X, r g *ᵥ v ∈ X
  let tr : G → Submodule K (Fin n → K) → Submodule K (Fin n → K) :=
    fun g X => X.map (Matrix.toLin' (r g))
  have mem_tr : ∀ g X v, v ∈ tr g X ↔ r g⁻¹ *ᵥ v ∈ X := by
    intro g X v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
      exact hx
    · intro hv
      refine Submodule.mem_map.2 ⟨_, hv, ?_⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]
  have tr_inv : ∀ g X, Inv X → Inv (tr g X) := by
    intro g X hX h hh v hv
    rw [mem_tr] at hv ⊢
    have e : r g⁻¹ *ᵥ (r h *ᵥ v) = r (g⁻¹ * h * g) *ᵥ (r g⁻¹ *ᵥ v) := by
      simp only [Matrix.mulVec_mulVec, map_mul, mul_assoc, hr1, mul_one]
    rw [e]
    exact hX _ (hconj g h hh) _ hv
  have htr_mul : ∀ g h X, tr (g * h) X = tr g (tr h X) := by
    intro g h X
    ext v
    rw [mem_tr, mem_tr, mem_tr, _root_.mul_inv_rev, map_mul, ← Matrix.mulVec_mulVec]
  have htr_one : ∀ X, tr 1 X = X := by
    intro X
    ext v
    rw [mem_tr, inv_one, map_one, Matrix.one_mulVec]
  obtain ⟨b, hb⟩ := Ws.invariant_submodule_eq_span_eigenbasis_of_separable K n (r u) hsep
  have hspan : ∀ X, Inv X → X = Submodule.span K (b '' {i | b i ∈ X}) :=
    fun X hX => hb X (hX u huN)
  have hrank : ∀ X, Inv X → Module.finrank K X = {i | b i ∈ X}.ncard := by
    intro X hX
    have e := hspan X hX
    calc Module.finrank K X = Module.finrank K (Submodule.span K (b '' {i | b i ∈ X})) := by
          rw [← e]
      _ = {i | b i ∈ X}.ncard := by
          have hli := b.linearIndependent.comp
            (Subtype.val : {i // i ∈ {i | b i ∈ X}} → Fin n) Subtype.val_injective
          rw [Set.image_eq_range]
          rw [finrank_span_eq_card (R := K) (b := fun x : {i // i ∈ {i | b i ∈ X}} => b x) hli,
            ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  obtain ⟨W0, hW0i, hW0b, hW0t⟩ : ∃ W, Inv W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
    unfold U3.MatIrr at hnot
    push_neg at hnot
    exact hnot
  have hex : ∃ k, ∃ X, Inv X ∧ X ≠ ⊥ ∧ Module.finrank K X = k := ⟨_, W0, hW0i, hW0b, rfl⟩
  obtain ⟨W, hWi, hWb, hWk⟩ := Nat.find_spec hex
  have hmin : ∀ X, Inv X → X ≠ ⊥ → Module.finrank K W ≤ Module.finrank K X := by
    intro X hX hXb
    rw [hWk]
    exact Nat.find_min' hex ⟨X, hX, hXb, rfl⟩
  have hWt : W ≠ ⊤ := by
    intro h
    have h1 := hmin W0 hW0i hW0b
    have h2 := Submodule.finrank_lt hW0t
    rw [h, finrank_top] at h1
    omega
  have tr_ne : ∀ g X, X ≠ ⊥ → tr g X ≠ ⊥ := by
    intro g X hX h
    apply hX
    rw [eq_bot_iff]
    intro v hv
    have hm : r g *ᵥ v ∈ tr g X := by
      rw [mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
      exact hv
    rw [h, Submodule.mem_bot] at hm
    have e := congrArg (fun w => r g⁻¹ *ᵥ w) hm
    simp only [Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec, Matrix.mulVec_zero] at e
    rw [e]
    exact Submodule.zero_mem _
  have trW_rank : ∀ g, Module.finrank K (tr g W) = Module.finrank K W := fun g =>
    le_antisymm (Submodule.finrank_map_le _ _) (hmin _ (tr_inv g W hWi) (tr_ne g W hWb))
  have key : ∀ g, (∀ v ∈ W, r g *ᵥ v ∈ W) → tr g W = W := by
    intro g hg
    apply Submodule.eq_of_le_of_finrank_le
    · intro v hv
      rw [mem_tr] at hv
      have e : v = r g *ᵥ (r g⁻¹ *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]
      rw [e]
      exact hg _ hv
    · rw [trW_rank]
  let S : Subgroup G :=
    { carrier := {g | tr g W = W}
      mul_mem' := by
        intro a c ha hc
        simp only [Set.mem_setOf_eq] at ha hc ⊢
        rw [htr_mul, hc, ha]
      one_mem' := htr_one W
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← htr_mul, inv_mul_cancel, htr_one] }
  have hS : ∀ g, g ∈ S ↔ ∀ v ∈ W, r g *ᵥ v ∈ W := by
    intro g
    constructor
    · intro hg v hv
      have hm : r g *ᵥ v ∈ tr g W := by
        rw [mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
        exact hv
      have hg' : tr g W = W := hg
      rw [hg'] at hm
      exact hm
    · exact key g
  refine ⟨W, S, hWb, hWt, fun g hg => (hS g).2 (hWi g hg), hS, ?_⟩
  have huniq : ∀ g1 g2 i, b i ∈ tr g1 W → b i ∈ tr g2 W → tr g1 W = tr g2 W := by
    intro g1 g2 i h1 h2
    have hI : Inv (tr g1 W ⊓ tr g2 W) := fun h hh v hv =>
      ⟨tr_inv g1 W hWi h hh v hv.1, tr_inv g2 W hWi h hh v hv.2⟩
    have hne : tr g1 W ⊓ tr g2 W ≠ ⊥ := by
      intro h
      have hm : b i ∈ tr g1 W ⊓ tr g2 W := ⟨h1, h2⟩
      rw [h, Submodule.mem_bot] at hm
      exact b.ne_zero i hm
    have hm := hmin _ hI hne
    have e1 : tr g1 W ⊓ tr g2 W = tr g1 W :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [trW_rank]; exact hm)
    have e2 : tr g1 W ⊓ tr g2 W = tr g2 W :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [trW_rank]; exact hm)
    exact e1.symm.trans e2
  have hcover : ∀ i, ∃ g, b i ∈ tr g W := by
    by_contra hc
    push_neg at hc
    obtain ⟨i, hi⟩ := hc
    have hUi : ∀ g ∈ (⊤ : Subgroup G), ∀ v ∈ ⨆ h, tr h W, r g *ᵥ v ∈ ⨆ h, tr h W := by
      intro g _ v hv
      refine Submodule.iSup_induction (fun h => tr h W)
        (motive := fun v => r g *ᵥ v ∈ ⨆ h, tr h W) hv ?_ ?_ ?_
      · intro h x hx
        refine Submodule.mem_iSup_of_mem (g * h) ?_
        rw [htr_mul, mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
        exact hx
      · show r g *ᵥ 0 ∈ ⨆ h, tr h W
        rw [Matrix.mulVec_zero]
        exact Submodule.zero_mem _
      · intro x y hx hy
        show r g *ᵥ (x + y) ∈ ⨆ h, tr h W
        rw [Matrix.mulVec_add]
        exact add_mem hx hy
    have hU := hirr _ hUi
    have hUb : (⨆ h, tr h W) ≠ ⊥ := by
      intro h
      apply hWb
      rw [eq_bot_iff, ← h]
      have := le_iSup (fun h => tr h W) 1
      rw [htr_one] at this
      exact this
    have hUt := hU.resolve_left hUb
    have hbi : b i ∈ ⨆ h, tr h W := by
      rw [hUt]
      exact Submodule.mem_top
    have hz : ∀ v ∈ ⨆ h, tr h W, b.repr v i = 0 := by
      intro v hv
      refine Submodule.iSup_induction (fun h => tr h W)
        (motive := fun v => b.repr v i = 0) hv ?_ ?_ ?_
      · intro g x hx
        have hx' : x ∈ tr g W := hx
        rw [hspan _ (tr_inv g W hWi), Module.Basis.mem_span_image] at hx'
        by_contra h0
        exact hi g (hx' (Finsupp.mem_support_iff.2 h0))
      · simp
      · intro x y hx hy
        simp only [map_add (f := _), Finsupp.add_apply]
        rw [hx, hy, add_zero]
    have := hz _ hbi
    simp at this
  let T : G ⧸ S → Set (Fin n) := fun q => {i | b i ∈ tr q.out W}
  have hT1 : ∀ q, (T q).ncard = Module.finrank K W := by
    intro q
    rw [← trW_rank q.out, hrank _ (tr_inv _ W hWi)]
  have hT2 : ∀ i, ∃! q, i ∈ T q := by
    intro i
    obtain ⟨g, hg⟩ := hcover i
    refine ⟨(g : G ⧸ S), ?_, ?_⟩
    · show b i ∈ tr (g : G ⧸ S).out W
      obtain ⟨a, ha⟩ : ∃ a, a = (g : G ⧸ S).out := ⟨_, rfl⟩
      rw [← ha]
      have hm : a⁻¹ * g ∈ S := by
        rw [ha]
        exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : G ⧸ S))
      have hm' : tr (a⁻¹ * g) W = W := hm
      have e : tr (a * (a⁻¹ * g)) W = tr a W := by
        rw [htr_mul, hm']
      rw [mul_inv_cancel_left] at e
      rw [← e]
      exact hg
    · intro q hq
      have e := huniq _ _ i hq hg
      have hm : q.out⁻¹ * g ∈ S := by
        show tr _ W = W
        rw [htr_mul, ← e, ← htr_mul, inv_mul_cancel, htr_one]
      exact (QuotientGroup.out_eq' q).symm.trans (QuotientGroup.eq.mpr hm)
  have hc := Ws.card_dvd_of_partition_equal_size (Fin n) (G ⧸ S) T (Module.finrank K W) hT1 hT2
  have hn : Nat.card (Fin n) = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)
  rw [hn] at hc
  exact hc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.IsClosedZeroLocusMvPolynomialEvalAdicContinuous
section
open IsLocalRing Polynomial Matrix UpperTheory.V

open Filter Topology in
theorem UpperTheory.V.Ws.isClosed_zeroLocus_mvPolynomial_eval_adicContinuous :
    ∀ (G A κ ι : Type) [TopologicalSpace G] [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [Field κ]
      (j : A →+* κ), Function.Injective j → ∀ a : ι → G → A, (∀ s, Alg.AdicCont (maximalIdeal A) (a s)) →
      ∀ f : MvPolynomial ι κ, IsClosed {g | MvPolynomial.eval (fun s => j (a s g)) f = 0} := by
  intro G A κ ι _ _ _ _ _ _ j _ a ha f
  classical
  letI : Algebra A κ := j.toAlgebra
  let L : (f.support → A) →ₗ[A] κ :=
    { toFun := fun v => ∑ d : f.support, f.coeff d.1 * j (v d)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        change ∑ d : f.support, f.coeff d.1 * j (c * x d) = j c * ∑ d : f.support, f.coeff d.1 * j (x d)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [map_mul]; ring }
  let m : G → f.support → A := fun g d => ∏ i ∈ d.1.support, a i g ^ d.1 i
  have hL : ∀ g, L (m g) = MvPolynomial.eval (fun s => j (a s g)) f := fun g => by
    rw [MvPolynomial.eval_eq, ← Finset.sum_coe_sort]
    change ∑ d : f.support, f.coeff d.1 * j (m g d) = _
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [m, map_prod, map_pow]
  let K := LinearMap.ker L
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := (f.support → A) ⧸ K) (maximalIdeal A)
    (maximalIdeal.isMaximal A).ne_top
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : K.mkQ (m x) ≠ 0 := fun h => hx (by
    have h2 : L (m x) = 0 := (Submodule.Quotient.mk_eq_zero K).1 h
    rw [hL] at h2
    exact h2)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, K.mkQ (m x) ∉ (maximalIdeal A ^ N • ⊤ : Submodule A ((f.support → A) ⧸ K)) := by
    by_contra h
    push Not at h
    apply hx'
    rw [← Submodule.mem_bot A, ← hK]
    exact (Submodule.mem_iInf _).2 h
  have hev : ∀ᶠ y in 𝓝 x, ∀ d, m x d - m y d ∈ maximalIdeal A ^ N := by
    rw [eventually_all]; intro d
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i ∈ d.1.support,
        Ideal.Quotient.mk (maximalIdeal A ^ N) (a i y) = Ideal.Quotient.mk (maximalIdeal A ^ N) (a i x) := by
      rw [eventually_all_finset]; intro i _
      exact (ha i N).eventually_eq x
    filter_upwards [h1] with y hy
    refine Ideal.Quotient.eq.1 ?_
    simp only [m, map_prod, map_pow]
    exact Finset.prod_congr rfl fun i hi => by rw [hy i hi]
  filter_upwards [hev] with y hy hy0
  apply hN
  have h0 : K.mkQ (m y) = 0 := (Submodule.Quotient.mk_eq_zero K).2 (by
    change L (m y) = 0
    rw [hL]; exact hy0)
  have h1 : K.mkQ (m x) = K.mkQ (m x - m y) := by rw [map_sub, h0, sub_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, pi_eq_sum_univ' (m x - m y), map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem_smul (hy s) Submodule.mem_top
end

