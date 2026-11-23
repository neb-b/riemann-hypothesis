module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushPFa
section
noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)] {K' : Type} [Fintype K'] {ι' : K' → Type}
  [∀ b, Fintype (ι' b)]

theorem ne_of_arith {Ω : Type} [Field Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

theorem arith_of_isPt [Nonempty K] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsPt ℚ y d) :
    IsArithVar (mCoordIdeal y) (d + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : ‹Algebra ℚ Ω› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  choose c hc using h1
  have hF : fnField ℚ y ≤ IntermediateField.adjoin ℚ (coneRatios y c) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨k, i⟩, ⟨k', j⟩, e, rfl⟩
    obtain rfl : k = k' := e
    have : y ⟨k, i⟩ / y ⟨k, j⟩ = (y ⟨k, i⟩ / y ⟨k, c k⟩) / (y ⟨k, j⟩ / y ⟨k, c k⟩) := by
      rw [div_div_div_cancel_right₀ (hc k)]
    rw [SetLike.mem_coe, this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, rfl⟩)
  have hA : Algebra.IsAlgebraic (Algebra.adjoin ℚ (fnField ℚ y : Set Ω)) Ω := by
    have e : Algebra.adjoin ℚ (fnField ℚ y : Set Ω) = (fnField ℚ y).toSubalgebra := Algebra.adjoin_eq (fnField ℚ y).toSubalgebra
    rw [e]
    exact inferInstanceAs (Algebra.IsAlgebraic (fnField ℚ y) Ω)
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := ℚ) (fnField ℚ y : Set Ω)
  have hc' : Cardinal.mk t = d := hb.cardinalMk_eq_trdeg.trans h3
  obtain ⟨e⟩ : Nonempty (Fin d ≃ t) := Cardinal.eq.1 (by simp [hc'])
  have hb' := hb.comp_equiv e
  have := hb'.isAlgebraic_field
  exact CoordConeArithVar.proof IntDomainDim.full K ι Ω y c d _ inferInstance hc hb'.1 (fun i => hF (ht (e i).2))
    fun r _ => Algebra.IsAlgebraic.isAlgebraic r

theorem mem_of_birational {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω) {y : (Σ b, ι b) → Ω₁} (hb : Birational y)
    (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) (F : Subfield Ω) (hF : ∀ k j j', i (y ⟨k, j⟩) / i (y ⟨k, j'⟩) ∈ F) (s : Ω₁) : i s ∈ F := by
  choose c hc using hne
  have key : ∀ (g : MRing ι) (d : K → ℕ), IsMultiHomog g d → i (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) ∈ F := by
    intro g d hg
    have h1 : aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
      have h := congrArg (eval fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap_of_isMultiHomog y hg)
      have h' : (eval fun k => (y ⟨k, c k⟩)⁻¹).comp (mConeMap y : MRing ι →+* MvPolynomial K Ω₁) =
          ((aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] Ω₁) : MRing ι →+* Ω₁) := by
        refine ringHom_ext (fun c => by simp) fun p => ?_
        simp [mConeMap, div_eq_mul_inv]
      have h'' := DFunLike.congr_fun h' g
      simp only [RingHom.comp_apply, RingHom.coe_coe] at h''
      rw [← h'', h, map_mul, eval_C]
      simp [div_eq_mul_inv]
    rw [h1]
    clear h1 hg
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simpa using add_mem hf hg
    | mul_X f p hf => simpa using mul_mem hf (hF p.1 p.2 (c p.1))
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hb s
  have hp : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have : s = (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) / (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k) := by
    rw [div_div_div_cancel_right₀ hp, e, mul_div_cancel_right₀ _ h0]
  rw [this, map_div₀]
  exact div_mem (key g d hg) (key h d hh)

variable {Ω₁ : Type} [Field Ω₁] [Algebra ℚ Ω₁] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra Ω₁ Ω]

theorem fnField_join {y : (Σ b, ι b) → Ω₁} (y' : (Σ b, ι' b) → Ω) (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) :
    (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')).toSubfield = (fnField Ω₁ y').toSubfield := by
  apply le_antisymm
  · rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨q, rfl⟩ | ⟨⟨k | k, j⟩, ⟨k', j'⟩, e, rfl⟩)
    · simp
    · obtain rfl : Sum.inl k = k' := e
      exact div_mem ((fnField Ω₁ y').algebraMap_mem _) ((fnField Ω₁ y').algebraMap_mem _)
    · obtain rfl : Sum.inr k = k' := e
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, ⟨k, j'⟩, rfl, rfl⟩
  · rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨s, rfl⟩ | ⟨⟨k, j⟩, ⟨k', j'⟩, e, rfl⟩)
    · refine mem_of_birational _ hb hne _ (fun k j j' => ?_) s
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨.inl k, j⟩, ⟨.inl k, j'⟩, rfl, rfl⟩
    · obtain rfl : k = k' := e
      exact IntermediateField.subset_adjoin _ _ ⟨⟨.inr k, j⟩, ⟨.inr k, j'⟩, rfl, rfl⟩

theorem finrank_join {y : (Σ b, ι b) → Ω₁} (y' : (Σ b, ι' b) → Ω) (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) :
    Module.finrank (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')) Ω = Module.finrank (fnField Ω₁ y') Ω := by
  show Module.finrank (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')).toSubfield Ω =
    Module.finrank (fnField Ω₁ y').toSubfield Ω
  rw [fnField_join y' hb hne]

theorem isPt_join {y : (Σ b, ι b) → Ω₁} {y' : (Σ b, ι' b) → Ω} {n r : ℕ} (hb : Birational y)
    (ha : IsArithVar (mCoordIdeal y) (n + 1)) (h : IsPt Ω₁ y' r) :
    IsPt ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y') (n + r) := by
  have hne := ne_of_arith ha
  refine ⟨?_, ?_, ?_⟩
  · rintro (k | k)
    · obtain ⟨j, hj⟩ := hne k
      exact ⟨j, (map_ne_zero (algebraMap Ω₁ Ω)).2 hj⟩
    · exact h.1 k
  · have := h.2.1
    exact Module.finite_of_finrank_pos (by rw [finrank_join y' hb hne]; exact Module.finrank_pos)
  · have h1 := FnFieldTrdeg.full K ι Ω₁ y n hb ha
    have : CharZero Ω₁ := algebraRat.charZero Ω₁
    have : IsScalarTower ℤ ℚ Ω₁ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : IsScalarTower ℚ Ω₁ Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have h2 := trdeg_add_eq ℤ ℚ (A := Ω₁)
    rw [trdeg_eq_zero, zero_add, h1] at h2
    rw [← trdeg_add_eq ℚ Ω₁ (A := Ω), h2, h.2.2, Nat.cast_add]

end SheetDecomposition.PF
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushPFb
section
noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial

theorem ker_baseChange {k B K σ Φ Φ' : Type} [Field k] [CommRing B] [Algebra k B] [Field Φ] [Field Φ']
    [Algebra (MvPolynomial K k) Φ] [IsFractionRing (MvPolynomial K k) Φ] (a : k →+* Φ)
    (ha : ∀ c, a c = algebraMap (MvPolynomial K k) Φ (C c)) (ν : MvPolynomial K B →+* Φ') (hν : Function.Injective ν)
    (L : Φ →+* Φ') (hL : ∀ r, L (algebraMap (MvPolynomial K k) Φ r) = ν (map (algebraMap k B) r))
    (ψ : MvPolynomial σ k →ₐ[k] B) :
    RingHom.ker (eval₂Hom L fun s => ν (C (ψ (X s)))) = (RingHom.ker ψ).map (map a) := by
  classical
  obtain ⟨Θ, hΘ⟩ : ∃ f : MvPolynomial σ Φ →+* Φ', f = eval₂Hom L fun s => ν (C (ψ (X s))) :=
    ⟨_, rfl⟩
  suffices main : RingHom.ker Θ = (RingHom.ker ψ).map (map a) by
    subst hΘ
    exact main
  have hΘC : ∀ f : Φ, Θ (C f) = L f := fun f => by rw [hΘ, eval₂Hom_C]
  have hΘX : ∀ s : σ, Θ (X s) = ν (C (ψ (X s))) := fun s => by rw [hΘ, eval₂Hom_X']
  obtain ⟨α, hα⟩ : ∃ f : MvPolynomial K (MvPolynomial σ k) →+* MvPolynomial σ Φ,
      f = eval₂Hom (map a) fun i => C (algebraMap (MvPolynomial K k) Φ (X i)) := ⟨_, rfl⟩
  have hαC : ∀ p : MvPolynomial σ k, α (C p) = map a p := fun p => by rw [hα, eval₂Hom_C]
  have hαX : ∀ i : K, α (X i) = C (algebraMap (MvPolynomial K k) Φ (X i)) := fun i => by
    rw [hα, eval₂Hom_X']
  have hΘa : ∀ p : MvPolynomial σ k, Θ (map a p) = ν (C (ψ p)) := by
    have h : Θ.comp (map a) =
        ν.comp ((C : B →+* MvPolynomial K B).comp (ψ : MvPolynomial σ k →+* B)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, map_C, hΘC, ha, hL, RingHom.coe_coe, algHom_C]
      · intro s
        simp only [RingHom.comp_apply, map_X, hΘX, RingHom.coe_coe]
    intro p
    exact DFunLike.congr_fun h p
  have hΘα : ∀ Q, Θ (α Q) = ν (map (ψ : MvPolynomial σ k →+* B) Q) := by
    have h : Θ.comp α = ν.comp (map (ψ : MvPolynomial σ k →+* B)) := by
      apply MvPolynomial.ringHom_ext
      · intro p
        simp only [RingHom.comp_apply, hαC, hΘa, map_C, RingHom.coe_coe]
      · intro i
        simp only [RingHom.comp_apply, hαX, hΘC, hL, map_X]
    intro Q
    exact DFunLike.congr_fun h Q
  have hαmapC : ∀ p : MvPolynomial K k, α (map (C : k →+* MvPolynomial σ k) p) =
      C (algebraMap (MvPolynomial K k) Φ p) := by
    have h : α.comp (map (C : k →+* MvPolynomial σ k)) =
        (C : Φ →+* MvPolynomial σ Φ).comp (algebraMap (MvPolynomial K k) Φ) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, map_C, hαC, ha]
      · intro i
        simp only [RingHom.comp_apply, map_X, hαX]
    intro p
    exact DFunLike.congr_fun h p
  have hCmem : ∀ q : MvPolynomial K k, C (algebraMap (MvPolynomial K k) Φ q) ∈ α.range :=
    fun q => RingHom.mem_range.mpr ⟨_, hαmapC q⟩
  have hXmem : ∀ s : σ, (X s : MvPolynomial σ Φ) ∈ α.range := fun s =>
    RingHom.mem_range.mpr ⟨C (X s), by rw [hαC, map_X]⟩
  have hden : ∀ P : MvPolynomial σ Φ, ∃ q : MvPolynomial K k, q ≠ 0 ∧
      C (algebraMap (MvPolynomial K k) Φ q) * P ∈ α.range := by
    intro P
    refine MvPolynomial.induction_on (motive := fun P => ∃ q : MvPolynomial K k, q ≠ 0 ∧
      C (algebraMap (MvPolynomial K k) Φ q) * P ∈ α.range) P ?_ ?_ ?_
    · intro f
      try dsimp only
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial K k) f
      refine ⟨q, nonZeroDivisors.ne_zero hq, ?_⟩
      rw [← C_mul, mul_div_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq)]
      exact hCmem p
    · intro P₁ P₂ h₁ h₂
      try dsimp only at h₁ h₂ ⊢
      obtain ⟨q₁, hq₁, h₁⟩ := h₁
      obtain ⟨q₂, hq₂, h₂⟩ := h₂
      refine ⟨q₁ * q₂, mul_ne_zero hq₁ hq₂, ?_⟩
      have e : C (algebraMap (MvPolynomial K k) Φ (q₁ * q₂)) * (P₁ + P₂) =
          C (algebraMap (MvPolynomial K k) Φ q₂) * (C (algebraMap (MvPolynomial K k) Φ q₁) * P₁) +
            C (algebraMap (MvPolynomial K k) Φ q₁) * (C (algebraMap (MvPolynomial K k) Φ q₂) * P₂) := by
        rw [map_mul, C_mul]
        ring
      rw [e]
      exact add_mem (mul_mem (hCmem q₂) h₁) (mul_mem (hCmem q₁) h₂)
    · intro P s h
      try dsimp only at h ⊢
      obtain ⟨q, hq, h⟩ := h
      refine ⟨q, hq, ?_⟩
      rw [← mul_assoc]
      exact mul_mem h (hXmem s)
  apply le_antisymm
  · intro P hP
    rw [RingHom.mem_ker] at hP
    obtain ⟨q, hq, hmem⟩ := hden P
    obtain ⟨Q, hQ⟩ := RingHom.mem_range.mp hmem
    have hQ0 : map (ψ : MvPolynomial σ k →+* B) Q = 0 := by
      apply hν
      rw [map_zero, ← hΘα, hQ, map_mul, hP, mul_zero]
    have hJ : α Q ∈ (RingHom.ker ψ).map (map a) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Q.as_sum, map_sum]
      refine Ideal.sum_mem _ fun v _ => ?_
      rw [monomial_eq, map_mul, hαC]
      refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker]
      have hv := congrArg (AddMonoidAlgebra.coeff · v) hQ0
      rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hv
      exact hv
    have hqne : algebraMap (MvPolynomial K k) Φ q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hq)
    have hP' : P = C (algebraMap (MvPolynomial K k) Φ q)⁻¹ * α Q := by
      rw [hQ, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hqne, C_1, one_mul]
    rw [hP']
    exact Ideal.mul_mem_left _ _ hJ
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_comap, RingHom.mem_ker, hΘa, hp, map_zero, map_zero]

end SheetDecomposition.PF
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestA
section
noncomputable section

namespace SheetDecomposition

open MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

section Relabel

variable {Ψ Ψ' : Type} [Fintype Ψ] [DecidableEq Ψ] [Fintype Ψ'] [DecidableEq Ψ'] {N : ℕ} (e : Ψ ≃ Ψ')

theorem degFl_rename (F : RP Ψ N) : degFl (rename (e.prodCongr (Equiv.refl (Fin N))) F : RP Ψ' N) = degFl F := by
  unfold degFl
  have hd : dimFl Ψ' N = dimFl Ψ N := by
    unfold dimFl
    rw [Fintype.card_congr e]
  rw [hd, ← (Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))).sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hp : permExp ((Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))) σ) =
      Finsupp.mapDomain (e.prodCongr (Equiv.refl (Fin N))) (permExp σ) := by
    ext ⟨τ', i⟩
    rw [Finsupp.mapDomain_equiv_apply]
    simp [permExp]
  rw [hp, coeff_rename_mapDomain _ (e.prodCongr (Equiv.refl (Fin N))).injective]
  congr 1
  exact Equiv.prod_comp e.symm (fun τ => ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ))

theorem rename_muSmall (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (muSmall j : RP Ψ N) : RP Ψ' N) = muSmall j := by
  unfold muSmall
  split_ifs
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [pkLow, map_neg, map_sum, map_pow, rename_X, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.refl_apply]
      congr 1
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem rename_fibClass (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (fibClass j : RP Ψ N) : RP Ψ' N) = fibClass j := by
  unfold fibClass
  simp only [map_prod, map_sub, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

end Relabel

theorem testRelabel : TestRelabel := by
  intro Ψ _ _ N j
  unfold testDeg
  rw [← degFl_rename (Fintype.equivFin Ψ), map_mul, map_pow, rename_muSmall, rename_fibClass]
  simp [dimX]

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {p q : ℕ}

theorem count_pairs : Fintype.card Ψ * p * q + Fintype.card (PairIx Ψ p q) = dimFl Ψ (p + q) := by
  classical
  have hL : (Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).card =
      (p + q) * (p + q - 1) / 2 := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_range_id,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have hC : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
      fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)).card = p * q := by
    have e : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
        fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)) =
        (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p) ×ˢ
          (Finset.univ.filter fun b : Fin (p + q) => ¬ (b : ℕ) < p) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Fin.lt_iff_val_lt_val]
      omega
    have h1 : (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p).card = p := by
      rw [Fin.card_filter_val_lt]
      omega
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (p + q))))
      (fun a : Fin (p + q) => (a : ℕ) < p)
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    rw [e, Finset.card_product, h1]
    congr 1
    omega
  have hS : Fintype.card {ab : Fin (p + q) × Fin (p + q) // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)} +
      p * q = (p + q) * (p + q - 1) / 2 := by
    rw [Fintype.card_subtype, ← hL, ← hC, ← Finset.filter_filter]
    exact Finset.card_filter_add_card_filter_not _
  rw [Fintype.card_prod]
  unfold dimFl
  rw [← hS]
  ring

def muCoef (Ψ : Type) (p q : ℕ) : Ψ × Fin (p + q) → ℤ := fun x => if p ≤ (x.2 : ℕ) then 1 else 0

def fibCoef (t : PairIx Ψ p q) : Ψ × Fin (p + q) → ℤ := fun x =>
  (if x = (t.1, t.2.1.2) then 1 else 0) - if x = (t.1, t.2.1.1) then 1 else 0

theorem sum_muCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) :
    ∑ r, muCoef Ψ p q r • x r = ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (p + q) => p ≤ (i : ℕ)), x (τ, i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [muCoef]
  split_ifs <;> simp

theorem sum_fibCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) (t : PairIx Ψ p q) :
    ∑ r, fibCoef t r • x r = x (t.1, t.2.1.2) - x (t.1, t.2.1.1) := by
  simp [fibCoef, sub_smul, Finset.sum_sub_distrib, ite_smul]

theorem test_factor {n r : ℕ} (e : Fin r ≃ PairIx Ψ p q) (hq : q ≤ p) (hn : n = Fintype.card Ψ * p * q) :
    (muSmall p ^ dimX Ψ (p + q) p * fibClass p : RP Ψ (p + q)) =
      ∏ j : Fin (n + r), ∑ x, Fin.append (fun _ : Fin n => muCoef Ψ p q) (fun j => fibCoef (e j)) j x • X x := by
  have hN : p + q - p ≤ p := by omega
  have hmu : (muSmall p : RP Ψ (p + q)) = ∑ x, muCoef Ψ p q x • (X x : RP Ψ (p + q)) := by
    rw [sum_muCoef (X : Ψ × Fin (p + q) → RP Ψ (p + q))]
    unfold muSmall
    rw [if_pos hN]
  have hdim : dimX Ψ (p + q) p = n := by
    unfold dimX
    rw [hn, Nat.add_sub_cancel_left]
    ring
  have hfib : (fibClass p : RP Ψ (p + q)) = ∏ i : Fin r, ∑ x, fibCoef (e i) x • (X x : RP Ψ (p + q)) := by
    simp only [sum_fibCoef]
    rw [Fintype.prod_equiv e _ (fun t : PairIx Ψ p q => (X (t.1, t.2.1.2) - X (t.1, t.2.1.1) : RP Ψ (p + q)))
      (fun _ => rfl)]
    unfold fibClass
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_subtype_eq_prod_filter, Finset.subtype_univ]
    try rfl
  rw [Fin.prod_univ_add, hmu, hdim, hfib]
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SheetDecomposition
end
end

