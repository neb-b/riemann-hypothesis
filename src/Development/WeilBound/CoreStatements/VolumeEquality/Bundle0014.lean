module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushNumEq
section
noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)]

theorem inum_eq_zero_of_valEq_zero (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a : Fin d → K → ℤ) (i : Fin d) (h : ValEq k z (a i) z 0) : inum k z a = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := i.pos; omega⟩
  have key : inum k z a = inum k z (a ∘ Equiv.swap i (Fin.last n)) := by
    unfold inum NumbersDVR.intNum
    rw [FieldNumbers.mixedDiff_comp_perm]
  rw [key, ← Fin.snoc_init_self (a ∘ Equiv.swap i (Fin.last n))]
  apply h3 k Ω K ι z n _ _ hz ht
  show ValEq k z (a (Equiv.swap i (Fin.last n) (Fin.last n))) z 0
  rw [Equiv.swap_apply_right]
  exact h

theorem inum_update (h1 : PtDim) (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a : Fin d → K → ℤ) (i : Fin d) (b : K → ℤ) (h : ValEq k z b z (a i)) : inum k z (Function.update a i b) = inum k z a := by
  classical
  obtain ⟨hprime, hdim, -⟩ := h1 k Ω K ι z d hz
  have hadd := FieldNumbers.IntNumAdd.full k K ι (NumbersDVR.pointIdeal k z) hprime.multiHomog hprime.relevant d hdim
    a i (b - a i) (a i)
  rw [sub_add_cancel, Function.update_eq_self] at hadd
  have hz0 : inum k z (Function.update a i (b - a i)) = 0 := by
    apply inum_eq_zero_of_valEq_zero h3 hz ht _ i
    rw [Function.update_self]
    obtain ⟨ρ, hρ, hO⟩ := h
    refine ⟨ρ, hρ, fun O hk => ?_⟩
    have e := hO O hk
    have hne : ∀ c : K, (Finset.univ.sup fun j : ι c => O.valuation (z ⟨c, j⟩)) ≠ 0 := by
      intro c h0
      obtain ⟨j, hj⟩ := hz.1 c
      have hle : O.valuation (z ⟨c, j⟩) ≤ 0 :=
        h0 ▸ Finset.le_sup (f := fun j : ι c => O.valuation (z ⟨c, j⟩)) (Finset.mem_univ j)
      exact hj ((Valuation.zero_iff _).mp (le_antisymm hle zero_le'))
    have hv : vdeg O z (b - a i) * vdeg O z (a i) = vdeg O z b := by
      unfold vdeg
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [Pi.sub_apply, ← zpow_add₀ (hne c), sub_add_cancel]
    have hne' : vdeg O z (a i) ≠ 0 := by
      unfold vdeg
      exact Finset.prod_ne_zero_iff.mpr fun c _ => zpow_ne_zero _ (hne c)
    have h0 : vdeg O z (0 : K → ℤ) = 1 := by
      unfold vdeg
      simp
    rw [h0, mul_one]
    apply mul_right_cancel₀ hne'
    rw [hv, e]
  unfold inum at hz0 ⊢
  convert hadd using 1
  rw [hz0, zero_add]

theorem inum_congr (h1 : PtDim) (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a a' : Fin d → K → ℤ) (h : ∀ j, ValEq k z (a j) z (a' j)) : inum k z a = inum k z a' := by
  classical
  have key : ∀ s : Finset (Fin d), inum k z (fun j => if j ∈ s then a' j else a j) = inum k z a := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi ih
      rw [← ih]
      have e : (fun j => if j ∈ insert i s then a' j else a j) =
          Function.update (fun j => if j ∈ s then a' j else a j) i (a' i) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [hj]
      rw [e]
      apply inum_update h1 h3 hz ht
      simpa [hi] using (h i).symm
  simpa using (key Finset.univ).symm

theorem fnField_le_join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) : fnField k y ≤ fnField k (joinPt y y') := by
  unfold fnField
  rw [IntermediateField.adjoin_le_iff]
  rintro t ⟨p, q, hpq, rfl⟩
  apply IntermediateField.subset_adjoin
  exact ⟨⟨Sum.inl p.1, p.2⟩, ⟨Sum.inl q.1, q.2⟩, congrArg Sum.inl hpq, rfl⟩

theorem finite_of_le {F F' : IntermediateField k Ω} (h : F ≤ F') [FiniteDimensional F Ω] : FiniteDimensional F' Ω := by
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F F' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite F F' Ω

theorem IsPt.join_inl {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d) (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) :
    IsPt k (joinPt y y') d := by
  obtain ⟨h0, hf, ht⟩ := h
  refine ⟨?_, ?_, ht⟩
  · rintro (b | b)
    · exact h0 b
    · exact h' b
  · haveI := hf
    exact finite_of_le (fnField_le_join_inl (k := k) y y')

theorem num_join_inl (h2 : NumPull) {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d)
    (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) (a : Fin d → K → ℤ) : num k (joinPt y y') (fun j => Sum.elim (a j) 0) = num k y a := by
  have hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inl : K → K ⊕ K')
      (fun p : (Σ b, ι b) => (⟨Sum.inl p.1, p.2⟩ : Σ b, Sum.elim ι ι' b)) := by
    refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
    · intro p q hpq
      obtain ⟨b, i⟩ := p
      obtain ⟨b', i'⟩ := q
      cases hpq
      rfl
    · rintro ⟨b, i⟩ ⟨c, rfl⟩
      exact ⟨⟨c, i⟩, rfl⟩
  have hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inl : K → K ⊕ K') (a j) = Sum.elim (a j) (0 : K' → ℤ) := by
    intro j
    funext x
    cases x with
    | inl c => exact Sum.inl_injective.extend_apply (a j) 0 c
    | inr c =>
      show Function.extend Sum.inl (a j) 0 (Sum.inr c) = 0
      rw [Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]
      rfl
  have := h2 k Ω K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl _ (joinPt y y') d a hv (h.join_inl h') h
  simp only [hp] at this
  exact this

theorem num_join_inr (h2 : NumPull) {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d) (h' : IsPt k y' d)
    (a : Fin d → K' → ℤ) : num k (joinPt y y') (fun j => Sum.elim 0 (a j)) = num k y' a := by
  have hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inr : K' → K ⊕ K')
      (fun p : (Σ b, ι' b) => (⟨Sum.inr p.1, p.2⟩ : Σ b, Sum.elim ι ι' b)) := by
    refine ⟨Sum.inr_injective, ?_, fun _ => rfl, ?_⟩
    · intro p q hpq
      obtain ⟨b, i⟩ := p
      obtain ⟨b', i'⟩ := q
      cases hpq
      rfl
    · rintro ⟨b, i⟩ ⟨c, rfl⟩
      exact ⟨⟨c, i⟩, rfl⟩
  have hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inr : K' → K ⊕ K') (a j) = Sum.elim (0 : K → ℤ) (a j) := by
    intro j
    funext x
    cases x with
    | inr c => exact Sum.inr_injective.extend_apply (a j) 0 c
    | inl c =>
      show Function.extend Sum.inr (a j) 0 (Sum.inl c) = 0
      rw [Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]
      rfl
  have := h2 k Ω K' ι' (K ⊕ K') (Sum.elim ι ι') Sum.inr _ (joinPt y y') d a hv (h.join_inl h'.1) h'
  simp only [hp] at this
  exact this

theorem exists_top (y : (Σ b, ι b) → Ω) [FiniteDimensional (fnField k y) Ω] :
    ∃ (m : ℕ) (w : (Σ _ : Unit, Option (Fin m)) → Ω), (∀ b, ∃ i, w ⟨b, i⟩ ≠ 0) ∧ fnField k (joinPt y w) = ⊤ := by
  let B := Module.finBasis (fnField k y) Ω
  refine ⟨_, fun x => x.2.elim 1 B, fun _ => ⟨none, one_ne_zero⟩, eq_top_iff.2 fun t _ => ?_⟩
  rw [← B.sum_repr t]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  refine mul_mem (fnField_le_join_inl y _ (B.repr t i).2) (IntermediateField.subset_adjoin _ _ ?_)
  exact ⟨⟨.inr (), some i⟩, ⟨.inr (), none⟩, rfl, (div_one _).symm⟩

theorem numEq : PtDim → NumPull → UnitZero → NumEq := by
  intro h1 h2 h3 k _ Ω _ _ K _ ι _ K' _ ι' _ y y' d a a' hy hy' h
  have hj := hy.join_inl hy'.1
  haveI := hj.2.1
  obtain ⟨m, w, hw, ht⟩ := exists_top (k := k) (joinPt y y')
  rw [← num_join_inl h2 hy hy'.1, ← num_join_inr h2 hy hy', ← num_join_inl h2 hj hw, ← num_join_inl h2 hj hw]
  unfold num
  congr 1
  refine inum_congr h1 h3 (hj.join_inl hw) ht _ _ fun j => ?_
  exact ((ValEq.join_inl _ w _).trans (ValEq.join_inl y y' _)).trans
    ((h j).trans ((ValEq.join_inl _ w _).trans (ValEq.join_inr y y' _)).symm)

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushPFc
section
noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal intNum pointConeMap)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)] {K' : Type} [Fintype K'] {ι' : K' → Type}
  [∀ b, Fintype (ι' b)]

def blkE (K K' : Type) : K' ≃ FibreBlock (Sum.inl : K → K ⊕ K') where
  toFun k := ⟨.inr k, by simp⟩
  invFun
    | ⟨.inl k, h⟩ => absurd ⟨k, rfl⟩ h
    | ⟨.inr k, _⟩ => k
  left_inv _ := rfl
  right_inv
    | ⟨.inl k, h⟩ => absurd ⟨k, rfl⟩ h
    | ⟨.inr _, _⟩ => rfl

def varE (ι : K → Type) (ι' : K' → Type) :
    (Σ b, ι' b) ≃ Σ b : FibreBlock (Sum.inl : K → K ⊕ K'), fibreIdx (Sum.elim ι ι') Sum.inl b where
  toFun p := ⟨⟨.inr p.1, by simp⟩, p.2⟩
  invFun
    | ⟨⟨.inl k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨.inr k, _⟩, i⟩ => ⟨k, i⟩
  left_inv _ := rfl
  right_inv
    | ⟨⟨.inl k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨.inr _, _⟩, _⟩ => rfl

variable {Ω₁ : Type} [Field Ω₁] {Ω : Type} [Field Ω] [Algebra Ω₁ Ω]

theorem image_join (y : (Σ b, ι b) → Ω₁) (y' : (Σ b, ι' b) → Ω) :
    imageZ inlV (mCoordIdeal (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')) = mCoordIdeal y := by
  have key : ∀ f, mConeMap (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y') (rename inlV f) =
      rename Sum.inl (MvPolynomial.map (algebraMap Ω₁ Ω) (mConeMap y f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp]
      simp [mConeMap, inlV, joinPt]
  ext f
  simp only [imageZ, Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
  rw [show (rename inlV).toRingHom f = rename inlV f from rfl, key]
  constructor
  · intro h
    apply MvPolynomial.map_injective _ (algebraMap Ω₁ Ω).injective
    apply MvPolynomial.rename_injective _ Sum.inl_injective
    rw [h, map_zero, map_zero]
  · intro h
    rw [h, map_zero, map_zero]

theorem ker_aeval_cone {Φ : Type} [Field Φ] (y : (Σ b, ι b) → Ω) (ν : MvPolynomial K Ω →+* Φ) (hν : Function.Injective ν) :
    RingHom.ker (aeval (fun p : Σ b, ι b => ν (C (y p) * X p.1)) : MRing ι →ₐ[ℤ] Φ) = mCoordIdeal y := by
  have key : ∀ f : MRing ι, (aeval (fun p : Σ b, ι b => ν (C (y p) * X p.1)) : MRing ι →ₐ[ℤ] Φ) f =
      ν (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      rw [map_mul, hp, map_mul (mConeMap y), map_mul ν, aeval_X]
      congr 1
      simp [mConeMap]
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker]
  rw [key]
  constructor
  · intro h
    apply hν
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

theorem gen_cone {Φ : Type} [Field Φ] [Algebra (MvPolynomial K Ω₁) Φ] [IsFractionRing (MvPolynomial K Ω₁) Φ]
    {y : (Σ b, ι b) → Ω₁} (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) (c : Φ) :
    ∃ f g : MRing ι, aeval (fun p : Σ b, ι b => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1)) g ≠ 0 ∧
      c = aeval (fun p : Σ b, ι b => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1)) f /
        aeval (fun p : Σ b, ι b => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1)) g := by
  set φ : MRing ι →ₐ[ℤ] Φ :=
    aeval (fun p : Σ b, ι b => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1)) with hφ
  have key : ∀ f : MRing ι, φ f = algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [hφ, mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      rw [map_mul, hp, map_mul (mConeMap y), map_mul (algebraMap _ Φ), hφ, aeval_X]
      congr 1
      simp [mConeMap]
  have hinj : Function.Injective (algebraMap (MvPolynomial K Ω₁) Φ) := IsFractionRing.injective _ _
  set S := Subfield.closure (Set.range φ) with hS
  have hmem : ∀ f, algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y f) ∈ S := by
    intro f
    rw [← key]
    exact Subfield.subset_closure ⟨f, rfl⟩
  have hC : ∀ s : Ω₁, algebraMap (MvPolynomial K Ω₁) Φ (C s) ∈ S := by
    intro s
    obtain ⟨d, g, h, hg, hh, hne0, heq⟩ := hb s
    have eg := ConeTrdeg.mConeMap_of_isMultiHomog y hg
    have eh := ConeTrdeg.mConeMap_of_isMultiHomog y hh
    have hM : (∏ k : K, (X k : MvPolynomial K Ω₁) ^ d k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (X_ne_zero k))
    have hCne : (C (aeval y h) : MvPolynomial K Ω₁) ≠ 0 := by
      rw [Ne, MvPolynomial.C_eq_zero]
      exact hne0
    have hden : algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y h) ≠ 0 := by
      rw [eh]
      intro h0
      have := hinj (h0.trans (map_zero _).symm)
      exact mul_ne_zero hCne hM this
    have : algebraMap (MvPolynomial K Ω₁) Φ (C s) =
        algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y g) / algebraMap (MvPolynomial K Ω₁) Φ (mConeMap y h) := by
      rw [eq_div_iff hden, ← map_mul, eg, eh, heq]
      congr 1
      rw [map_mul]
      ring
    rw [this]
    exact div_mem (hmem g) (hmem h)
  have hX : ∀ k : K, algebraMap (MvPolynomial K Ω₁) Φ (X k) ∈ S := by
    intro k
    obtain ⟨j, hj⟩ := hne k
    have e1 : (X k : MvPolynomial K Ω₁) = C (y ⟨k, j⟩)⁻¹ * mConeMap y (X ⟨k, j⟩) := by
      simp only [mConeMap, aeval_X]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hj, map_one, one_mul]
    rw [e1, map_mul]
    exact mul_mem (hC _) (hmem _)
  have hall : ∀ a : MvPolynomial K Ω₁, algebraMap (MvPolynomial K Ω₁) Φ a ∈ S := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C s => exact hC s
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p n hp => rw [map_mul]; exact mul_mem hp (hX n)
  have hc : c ∈ S := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial K Ω₁) c
    exact div_mem (hall a) (hall b)
  have hsub : Subring.closure (Set.range φ) ≤ φ.toRingHom.range :=
    Subring.closure_le.mpr (by
      rintro _ ⟨f, rfl⟩
      exact ⟨f, rfl⟩)
  obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.mp hc
  obtain ⟨f, rfl⟩ := hsub hu
  obtain ⟨g, rfl⟩ := hsub hv
  by_cases hg0 : φ.toRingHom g = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [← huv, hg0, div_zero, map_zero, zero_div]
  · exact ⟨f, g, hg0, huv.symm⟩

open Classical in
theorem exists_genFibre {y : (Σ b, ι b) → Ω₁} (y' : (Σ b, ι' b) → Ω) (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) :
    ∃ G : GenFibre inlV (mCoordIdeal (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')), ∀ (r : ℕ) (N : Fin r → K' → ℤ),
      intNum G.Φ (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inl G) (fun j => fibreDeg Sum.inl (Sum.elim (0 : K → ℤ) (N j))) = inum Ω₁ y' N := by
  let B := MvPolynomial K' Ω
  let Φ := FractionRing (MvPolynomial K Ω₁)
  let Φ' := FractionRing (MvPolynomial K B)
  let ν : MvPolynomial K B →+* Φ' := algebraMap _ _
  have hν : Function.Injective ν := IsFractionRing.injective _ _
  let e := sumRingEquiv Ω K K'
  let ν' : MvPolynomial (K ⊕ K') Ω →+* Φ' := ν.comp e.toRingHom
  have hν' : Function.Injective ν' := hν.comp e.injective
  have hg : Function.Injective (ν.comp (MvPolynomial.map (algebraMap Ω₁ B))) :=
    hν.comp (MvPolynomial.map_injective _ (algebraMap Ω₁ B).injective)
  let L : Φ →+* Φ' := IsFractionRing.lift hg
  letI alg : Algebra Φ Φ' := L.toAlgebra
  haveI : ∀ b, Fintype (Sum.elim ι ι' b) := fun b => by
    cases b <;> dsimp <;> infer_instance
  have he : ∀ (c : Ω) (q : Σ b, Sum.elim ι ι' b), e (C c * X q.1) =
      match q with
      | ⟨Sum.inl k, _⟩ => C (C c) * X k
      | ⟨Sum.inr k, _⟩ => C (C c * X k) := by
    rintro c ⟨(k | k), i⟩ <;> simp [e, sumRingEquiv_C, sumRingEquiv_X_inl, sumRingEquiv_X_inr]
  let ψ := pointConeMap Ω₁ y'
  have ha : ∀ c : Ω₁, algebraMap Ω₁ Φ c = algebraMap (MvPolynomial K Ω₁) Φ (C c) := by
    intro c
    rw [IsScalarTower.algebraMap_apply Ω₁ (MvPolynomial K Ω₁) Φ, MvPolynomial.algebraMap_eq]
  have hL : ∀ r, L (algebraMap (MvPolynomial K Ω₁) Φ r) = ν (MvPolynomial.map (algebraMap Ω₁ B) r) := by
    intro r
    exact IsFractionRing.lift_algebraMap hg r
  have hbc := ker_baseChange (algebraMap Ω₁ Φ) ha ν hν L hL ψ
  refine ⟨⟨Φ, Φ', fun p => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1),
    fun q => ν' (C (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y' q) * X q.1), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [image_join]
    exact ker_aeval_cone y (algebraMap (MvPolynomial K Ω₁) Φ) (IsFractionRing.injective _ _)
  · exact gen_cone hb hne
  · exact ker_aeval_cone _ ν' hν'
  · intro p
    rw [RingHom.algebraMap_toAlgebra]
    show ν (e _) = L _
    rw [IsFractionRing.lift_algebraMap, he]
    simp [inlV, joinPt, ν]
    rfl
  · intro r N
    have hdeg : (fun j => fibreDeg Sum.inl (Sum.elim (0 : K → ℤ) (N j))) = fun j => N j ∘ (blkE K K').symm := by
      funext j b
      obtain ⟨(k | k), h⟩ := b
      · exact absurd ⟨k, rfl⟩ h
      · rfl
    rw [hdeg]
    dsimp only
    rw [← FieldNumbers.RenameIntNum.full Φ K' (FibreBlock (Sum.inl : K → K ⊕ K')) ι'
      (fibreIdx (Sum.elim ι ι') Sum.inl) (blkE K K') (varE ι ι') (fun v => rfl)]
    have hmap : ∀ P : Ideal (NumbersDVR.MRing ι' Ω₁),
        intNum Φ (Ideal.map (MvPolynomial.map (algebraMap Ω₁ Φ)) P) N = intNum Ω₁ P N := by
      intro P
      unfold intNum
      congr 2
      funext m
      exact FieldNumbers.hilbFn_map P m
    refine Eq.trans ?_ (hmap (RingHom.ker ψ))
    rw [← hbc]
    congr 1
    ext f
    simp only [Ideal.mem_comap, ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, MvPolynomial.aeval_rename]
    rw [MvPolynomial.aeval_eq_eval₂Hom]
    congr! 3
    funext s
    obtain ⟨k, i⟩ := s
    have h1 := he (y' ⟨k, i⟩) ⟨Sum.inr k, i⟩
    simp only [Function.comp_apply, varE, Equiv.coe_fn_mk, ν', RingHom.comp_apply, joinPt]
    show ν (e (C (y' ⟨k, i⟩) * X (Sum.inr k))) = _
    rw [h1]
    simp [ψ, pointConeMap]

end SheetDecomposition.PF
end
end

