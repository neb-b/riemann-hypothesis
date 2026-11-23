module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsOpenImmersionIsStandardSmoothOfRelativeD
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [Algebra K B] (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K B]
    (p : Ideal B) [p.IsPrime] (hp : ∀ q : Ideal B, q.IsPrime → q ≤ p → q = p) :
    Algebra.EssFiniteType K p.ResidueField ∧ Algebra.trdeg K p.ResidueField = d := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K B
  letI : Algebra (MvPolynomial (Fin d) K) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) B := hg
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Algebra.FiniteType K B := .trans (S := MvPolynomial (Fin d) K) inferInstance inferInstance
  refine ⟨.comp K B _, ?_⟩
  obtain ⟨q, hqp, hq, hqo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal (MvPolynomial (Fin d) K))) (q := p.under (MvPolynomial (Fin d) K)) p bot_le
  obtain rfl := hp q hq hqp
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro a ha
    rw [IsScalarTower.algebraMap_apply _ B, Ideal.algebraMap_residueField_eq_zero] at ha
    have : a ∈ q.under (MvPolynomial (Fin d) K) := ha
    rwa [← hqo.over] at this
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) q.ResidueField := by
    let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin d) K)) q
    have : Module.Finite (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField q.ResidueField :=
      inferInstance
    have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K)
        (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (Fin d) K))
    exact Algebra.IsAlgebraic.trans _ (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField _
  rw [← trdeg_add_eq K (MvPolynomial (Fin d) K), MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero]
  simp

theorem exists_isOpenImmersion_isStandardSmoothOfRelativeDimension {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) :
    ∃ (B : CommRingCat.{0}) (φ : CommRingCat.of K ⟶ B) (j : Spec B ⟶ X) (_ : IsOpenImmersion j)
      (y : Spec B), j y = x ∧ j ≫ f = Spec.map φ ∧
        φ.hom.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨A, j, hj, ⟨y, rfl⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
  have h : SmoothOfRelativeDimension (0 + d) (j ≫ f) := inferInstance
  rw [zero_add, ← hφ] at h
  obtain ⟨s, hs, h'⟩ := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).1 h
  obtain ⟨t, ht, hty⟩ : ∃ t ∈ s, t ∉ y.asIdeal := by
    by_contra hne
    push Not at hne
    exact y.isPrime.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hne))
  obtain ⟨z, hz⟩ : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ t]
    exact hty
  refine ⟨.of (Localization.Away t), φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away t)),
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) ≫ j, inferInstance, z,
    ?_, ?_, h' t ht⟩
  · rw [← hz]; rfl
  · rw [Category.assoc, ← hφ, Spec.map_comp]

theorem residueField_fg_trdeg_of_smoothOfRelativeDimension {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) (hx : ∀ y : X, y ⤳ x → y = x) :
    letI : Algebra K (X.residueField x) :=
      (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    (⊤ : IntermediateField K (X.residueField x)).FG ∧ Algebra.trdeg K (X.residueField x) = d := by
  obtain ⟨B, φ, j, hj, y, rfl, hjf, hφ⟩ :=
    exists_isOpenImmersion_isStandardSmoothOfRelativeDimension f d hf x
  letI : Algebra K (X.residueField (j y)) :=
    (Spec.preimage (X.fromSpecResidueField (j y) ≫ f)).hom.toAlgebra
  letI : Algebra K B := φ.hom.toAlgebra
  haveI : y.asIdeal.IsPrime := y.isPrime
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d K B := hφ
  obtain ⟨h1, h2⟩ := residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension (K := K) d
    y.asIdeal (fun q hq hqy => by
      have hs : (⟨q, hq⟩ : PrimeSpectrum B) ⤳ y := (PrimeSpectrum.le_iff_specializes _ _).mp hqy
      have := j.isOpenEmbedding.injective (hx _ (hs.map j.continuous))
      exact congrArg PrimeSpectrum.asIdeal this)
  let e : X.residueField (j y) ≅ CommRingCat.of y.asIdeal.ResidueField :=
    asIso (j.residueFieldMap y) ≪≫ Scheme.Spec.residueFieldIso B y
  have he : Spec.preimage (X.fromSpecResidueField (j y) ≫ f) ≫ e.hom =
      φ ≫ CommRingCat.ofHom (algebraMap B y.asIdeal.ResidueField) := by
    rw [← Spec.map_inj, ← cancel_epi (Spec.map (Scheme.Spec.residueFieldIso B y).inv)]
    simp only [e, Iso.trans_hom, asIso_hom, Spec.map_comp, Spec.map_preimage, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, hjf]
    rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  let e' : X.residueField (j y) ≃ₐ[K] y.asIdeal.ResidueField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a => congr($(he).hom a) }
  refine ⟨IntermediateField.fg_top_iff.mpr ?_, ?_⟩
  · exact Algebra.EssFiniteType.of_surjective e'.symm.toAlgHom e'.symm.surjective
  · rw [e'.trdeg_eq, h2]

theorem residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ), SmoothOfRelativeDimension d f → ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X), letI : Algebra K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) := (Spec.preimage (X.fromSpecResidueField (hZ.1 : IsIrreducible Z).genericPoint ≫ f)).hom.toAlgebra; (⊤ : IntermediateField K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint)).FG ∧ Algebra.trdeg K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) = d := by
  intro K _ X f d hf Z hZ
  refine residueField_fg_trdeg_of_smoothOfRelativeDimension f d hf _ fun y hy => ?_
  have hg := (hZ.1 : IsIrreducible Z).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z hZ)
  have h1 : Z ⊆ closure {y} := by
    rw [← hg.def]
    exact specializes_iff_closure_subset.mp hy
  have h2 : closure {y} ⊆ Z := hZ.2 isIrreducible_singleton.closure h1
  exact (hy.antisymm (hg.specializes (h2 (subset_closure rfl)))).eq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsLowerMulUpperOfLeadingMinors
section
namespace GlobalTheory

open Matrix

section Cell
variable {R : Type} [CommRing R]

theorem det_eq_one_of_lower_unitriangular {r : ℕ} (l : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j h => h0 i j h)]
  simp [h1]

theorem exists_lower_mul_upper_of_leading_minors (r : ℕ) (h : Matrix (Fin r) (Fin r) R)
    (hm : ∀ k (hk : k ≤ r), IsUnit (h.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∃ l b : Matrix (Fin r) (Fin r) R, (∀ i j : Fin r, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧
      b.BlockTriangular id ∧ h = l * b := by
  induction r with
  | zero => exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩
  | succ r ih =>
    obtain ⟨L, B, hL0, hL1, hB, hA⟩ := ih (h.submatrix Fin.castSucc Fin.castSucc)
      (fun k hk => hm k (hk.trans (Nat.le_succ r)))
    have hLd : L.det = 1 := det_eq_one_of_lower_unitriangular L hL0 hL1
    have hAu : IsUnit (h.submatrix Fin.castSucc Fin.castSucc).det := hm r (Nat.le_succ r)
    have hBu : IsUnit B.det := by
      rw [hA, Matrix.det_mul, hLd, one_mul] at hAu; exact hAu
    have hLu : IsUnit L.det := by rw [hLd]; exact isUnit_one
    set x : Fin r → R := (fun j => h (Fin.last r) j.castSucc) ᵥ* B⁻¹ with hx
    set y : Fin r → R := L⁻¹ *ᵥ (fun i => h i.castSucc (Fin.last r)) with hy
    have hxB : x ᵥ* B = fun j => h (Fin.last r) j.castSucc := by
      rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hBu, Matrix.vecMul_one]
    have hLy : L *ᵥ y = fun i => h i.castSucc (Fin.last r) := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hLu, Matrix.one_mulVec]
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) 1 x j)
        (fun i => Fin.lastCases (motive := fun _ => R) 0 (L i) j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) (h (Fin.last r) (Fin.last r) - x ⬝ᵥ y) (fun _ => 0) j)
        (fun i => Fin.lastCases (motive := fun _ => R) (y i) (B i) j) i, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hL0 i j (by simpa using hij)
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hL1 i
    · intro i j hij
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last i))
      | cast j =>
        induction i using Fin.lastCases with
        | last => simp
        | cast i => simpa using hB (i := i) (j := j) (by simpa using hij)
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [dotProduct]
        | cast j => simpa [Matrix.vecMul, dotProduct] using (congrFun hxB j).symm
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa [Matrix.mulVec, dotProduct] using (congrFun hLy i).symm
        | cast j => simpa [Matrix.mul_apply] using congrFun (congrFun hA i) j

theorem eq_one_of_lower_unitriangular_eq_mul {r : ℕ} (l l' c : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1)
    (h0' : ∀ i j : Fin r, i < j → l' i j = 0) (h1' : ∀ i, l' i i = 1)
    (hc : c.BlockTriangular id) (h : l = l' * c) : c = 1 := by
  have key : ∀ i : Fin r, ∀ j, c i j = (1 : Matrix (Fin r) (Fin r) R) i j := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro j
      rcases lt_or_ge j i with hji | hij
      · rw [hc hji, Matrix.one_apply_ne hji.ne']
      · have e : l i j = c i j := by
          rw [h, Matrix.mul_apply, Finset.sum_eq_single i, h1', one_mul]
          · intro k _ hk
            rcases lt_or_gt_of_ne hk with hk | hk
            · rw [ih k hk, Matrix.one_apply_ne (hk.trans_le hij).ne, mul_zero]
            · rw [h0' i k hk, zero_mul]
          · simp
        rw [← e]
        rcases hij.eq_or_lt with rfl | hij
        · simp [h1]
        · rw [h0 i j hij, Matrix.one_apply_ne hij.ne]
  ext i j
  exact key i j

theorem isUnit_det_of_upper_of_isUnit_diag {r : ℕ} (b : Matrix (Fin r) (Fin r) R)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) : IsUnit b.det := by
  rw [Matrix.det_of_upperTriangular hb]
  exact IsUnit.prod_iff.2 fun i _ => hu i

end Cell

theorem cell_coordinates_exists_unique :
    ∀ (R : Type) [CommRing R] (n r : ℕ) (ι : Fin r ↪ Fin n) (g : Matrix (Fin n) (Fin r) R), ((∀ k (hk : k ≤ r), IsUnit (g.submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk)).det) ↔ ∃ (u : Matrix (Fin n) (Fin r) R) (b : Matrix (Fin r) (Fin r) R), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ g = u * b) ∧ ∀ (u u' : Matrix (Fin n) (Fin r) R) (b b' : Matrix (Fin r) (Fin r) R), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) → (∀ i j : Fin r, i < j → u' (ι i) j = 0) ∧ (∀ i : Fin r, u' (ι i) i = 1) → b.BlockTriangular id → b'.BlockTriangular id → (∀ i, IsUnit (b i i)) → u * b = u' * b' → u = u' ∧ b = b' := by
  intro R _ n r ι g
  refine ⟨⟨fun hm => ?_, ?_⟩, ?_⟩
  · obtain ⟨l, b, hl0, hl1, hb, hh⟩ :=
      exists_lower_mul_upper_of_leading_minors r (g.submatrix ι id) hm
    have hbu : IsUnit b.det := by
      have h1 : IsUnit (g.submatrix ι id).det := hm r le_rfl
      rwa [hh, Matrix.det_mul, det_eq_one_of_lower_unitriangular l hl0 hl1, one_mul] at h1
    have hu : ∀ i j, (g * b⁻¹) (ι i) j = l i j := by
      intro i j
      have : l = g.submatrix ι id * b⁻¹ := by
        rw [hh, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hbu, Matrix.mul_one]
      rw [this]; simp [Matrix.mul_apply]
    refine ⟨g * b⁻¹, b, fun i j hij => by rw [hu, hl0 i j hij], fun i => by rw [hu, hl1], hb, ?_, ?_⟩
    · intro i
      rw [Matrix.det_of_upperTriangular hb] at hbu
      exact IsUnit.prod_iff.1 hbu i (Finset.mem_univ _)
    · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbu, Matrix.mul_one]
  · rintro ⟨u, b, hu0, hu1, hb, hbu, rfl⟩ k hk
    have e : (u * b).submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk) =
        u.submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk) *
          b.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      symm
      refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)
      intro m hm
      have hkm : k ≤ m.val := by
        by_contra hlt
        exact hm ⟨⟨m.val, not_le.1 hlt⟩, rfl⟩
      have : Fin.castLE hk j < m := by
        rw [Fin.lt_def]; exact lt_of_lt_of_le j.2 hkm
      have h0 : b m (Fin.castLE hk j) = 0 := hb this
      rw [h0, mul_zero]
    rw [e, Matrix.det_mul, det_eq_one_of_lower_unitriangular, one_mul]
    · exact isUnit_det_of_upper_of_isUnit_diag _ (fun i j hij => hb hij) (fun i => hbu _)
    · intro i j hij; exact hu0 _ _ hij
    · intro i; exact hu1 _
  · rintro u u' b b' ⟨hu0, hu1⟩ ⟨hu0', hu1'⟩ hb hb' hbu h
    have hd := isUnit_det_of_upper_of_isUnit_diag b hb hbu
    have hu : u = u' * (b' * b⁻¹) := by
      rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    have hbi : b⁻¹.BlockTriangular id := by
      let _ := Matrix.invertibleOfIsUnitDet b hd
      exact Matrix.blockTriangular_inv_of_blockTriangular hb
    have hc : b' * b⁻¹ = 1 := by
      refine eq_one_of_lower_unitriangular_eq_mul (u.submatrix ι id) (u'.submatrix ι id) _
        hu0 hu1 hu0' hu1' (hb'.mul hbi) ?_
      ext i j
      rw [Matrix.submatrix_apply, hu]; simp [Matrix.mul_apply]
    refine ⟨by rw [hu, hc, Matrix.mul_one], ?_⟩
    calc b = b' * b⁻¹ * b := by rw [hc, Matrix.one_mul]
      _ = b' := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSubfieldValuationClosure
section
namespace GlobalTheory


open Topology Filter in
theorem exists_subfield_valuation_closure :
    ∀ (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (S : Subfield U),
      ∃ S' : Subfield U, ∀ u, u ∈ S' ↔
        ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ s ∈ S, v (u - s) < γ := by
  intro U _ v S
  refine ⟨{ carrier := {u | ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ s ∈ S, v (u - s) < γ}
            zero_mem' := ?hz, one_mem' := ?ho, add_mem' := ?ha, neg_mem' := ?hn, mul_mem' := ?hm,
            inv_mem' := ?hi }, fun _ => Iff.rfl⟩
  case hz =>
    intro γ hγ
    exact ⟨0, S.zero_mem, by rw [sub_self, map_zero]; exact zero_lt_iff.2 hγ⟩
  case ho =>
    intro γ hγ
    exact ⟨1, S.one_mem, by rw [sub_self, map_zero]; exact zero_lt_iff.2 hγ⟩
  case ha =>

    intro a b ha hb γ hγ
    obtain ⟨s, hs, hs'⟩ := ha γ hγ
    obtain ⟨t, ht, ht'⟩ := hb γ hγ
    refine ⟨s + t, S.add_mem hs ht, ?_⟩
    rw [show a + b - (s + t) = (a - s) + (b - t) by ring]
    exact v.map_add_lt hs' ht'
  case hn =>
    intro a ha γ hγ
    obtain ⟨s, hs, hs'⟩ := ha γ hγ
    refine ⟨-s, S.neg_mem hs, ?_⟩
    rw [show -a - -s = -(a - s) by ring, Valuation.map_neg]
    exact hs'
  case hm =>

    intro a b ha hb γ hγ
    obtain ⟨M, haM, hbM, hM1⟩ : ∃ M : WithZero (Multiplicative ℤ), v a ≤ M ∧ v b ≤ M ∧ 1 ≤ M :=
      ⟨max (max (v a) (v b)) 1, le_trans (le_max_left _ _) (le_max_left _ _),
        le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
    have hM0 : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hM1)
    obtain ⟨δ, hδ0, hδγ, hδ1⟩ : ∃ δ : WithZero (Multiplicative ℤ), δ ≠ 0 ∧ δ ≤ γ * M⁻¹ ∧ δ ≤ 1 := by
      refine ⟨min (γ * M⁻¹) 1, ?_, min_le_left _ _, min_le_right _ _⟩
      rcases le_total (γ * M⁻¹) 1 with h | h
      · rw [min_eq_left h]; exact mul_ne_zero hγ (inv_ne_zero hM0)
      · rw [min_eq_right h]; exact one_ne_zero
    obtain ⟨s, hs, hs'⟩ := ha δ hδ0
    obtain ⟨t, ht, ht'⟩ := hb δ hδ0
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have hMδ : M * δ ≤ γ := by
      calc M * δ ≤ M * (γ * M⁻¹) := mul_le_mul_right hδγ M
        _ = γ := by rw [mul_comm γ, ← mul_assoc, mul_inv_cancel₀ hM0, one_mul]
    have hvt : v t ≤ M := by
      rw [show t = b - (b - t) by ring]
      exact v.map_sub_le hbM (le_trans (le_of_lt ht') (le_trans hδ1 hM1))
    rw [show a * b - s * t = a * (b - t) + (a - s) * t by ring]
    refine v.map_add_lt ?_ ?_
    · rw [v.map_mul]
      calc v a * v (b - t) ≤ M * v (b - t) := mul_le_mul_left haM _
        _ < M * δ := mul_lt_mul_of_pos_left ht' (zero_lt_iff.2 hM0)
        _ ≤ γ := hMδ
    · rw [v.map_mul]
      calc v (a - s) * v t ≤ v (a - s) * M := mul_le_mul_right hvt _
        _ < δ * M := mul_lt_mul_of_pos_right hs' (zero_lt_iff.2 hM0)
        _ = M * δ := mul_comm _ _
        _ ≤ γ := hMδ
  case hi =>

    intro a ha γ hγ
    by_cases h0 : a = 0
    · subst h0
      rw [inv_zero]
      exact ⟨0, S.zero_mem, by rw [sub_self, map_zero]; exact zero_lt_iff.2 hγ⟩
    have hva : v a ≠ 0 := (v.ne_zero_iff).2 h0
    obtain ⟨δ, hδ0, hδa, hδγ⟩ :
        ∃ δ : WithZero (Multiplicative ℤ), δ ≠ 0 ∧ δ ≤ v a ∧ δ ≤ γ * (v a * v a) := by
      refine ⟨min (v a) (γ * (v a * v a)), ?_, min_le_left _ _, min_le_right _ _⟩
      rcases le_total (v a) (γ * (v a * v a)) with h | h
      · rw [min_eq_left h]; exact hva
      · rw [min_eq_right h]; exact mul_ne_zero hγ (mul_ne_zero hva hva)
    obtain ⟨s, hs, hs'⟩ := ha δ hδ0
    have hvs : v s = v a :=
      v.map_eq_of_sub_lt (by rw [v.map_sub_swap]; exact lt_of_lt_of_le hs' hδa)
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, map_zero] at hvs
      exact hva hvs.symm
    refine ⟨s⁻¹, S.inv_mem hs, ?_⟩
    have key : a⁻¹ - s⁻¹ = (s - a) * (a⁻¹ * s⁻¹) := by
      rw [sub_mul, mul_left_comm, mul_inv_cancel₀ hs0, mul_one, ← mul_assoc,
        mul_inv_cancel₀ h0, one_mul]
    rw [key, v.map_mul, v.map_mul, v.map_inv, v.map_inv, hvs, v.map_sub_swap]
    have hpos : 0 < (v a)⁻¹ * (v a)⁻¹ :=
      zero_lt_iff.2 (mul_ne_zero (inv_ne_zero hva) (inv_ne_zero hva))
    calc v (a - s) * ((v a)⁻¹ * (v a)⁻¹) < γ * (v a * v a) * ((v a)⁻¹ * (v a)⁻¹) :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le hs' hδγ) hpos
      _ = γ := by rw [mul_assoc, ← mul_inv, mul_inv_cancel₀ (mul_ne_zero hva hva), mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringLeDominatingOfFractionFiel
section
open IsLocalRing

namespace GlobalTheory

def compositeValuationSubring {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) : ValuationSubring L where
  toSubring := (V.toSubring.comap (residue W)).map W.subtype
  mem_or_inv_mem' := by
    intro x
    by_cases hx : x ∈ W
    · by_cases hx' : x⁻¹ ∈ W
      · rcases eq_or_ne x 0 with rfl | hx0
        · exact Or.inl (Subring.zero_mem _)
        have hmul : residue W ⟨x, hx⟩ * residue W ⟨x⁻¹, hx'⟩ = 1 := by
          rw [← map_mul, ← map_one (residue W)]
          congr 1
          exact Subtype.ext (mul_inv_cancel₀ hx0)
        rcases V.mem_or_inv_mem (residue W ⟨x, hx⟩) with h | h
        · exact Or.inl ⟨⟨x, hx⟩, h, rfl⟩
        · refine Or.inr ⟨⟨x⁻¹, hx'⟩, ?_, rfl⟩
          rw [← eq_inv_of_mul_eq_one_right hmul] at h
          exact h
      · refine Or.inl ⟨⟨x, hx⟩, ?_, rfl⟩
        have hm : (⟨x, hx⟩ : W) ∈ maximalIdeal W := by
          rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
          exact Or.inr hx'
        have h0 : residue W ⟨x, hx⟩ = 0 := (residue_eq_zero_iff _).2 hm
        change residue W ⟨x, hx⟩ ∈ V
        rw [h0]
        exact V.zero_mem
    · have hx' : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hx
      refine Or.inr ⟨⟨x⁻¹, hx'⟩, ?_, rfl⟩
      have hm : (⟨x⁻¹, hx'⟩ : W) ∈ maximalIdeal W := by
        rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
        exact Or.inr (by simpa using hx)
      have h0 : residue W ⟨x⁻¹, hx'⟩ = 0 := (residue_eq_zero_iff _).2 hm
      change residue W ⟨x⁻¹, hx'⟩ ∈ V
      rw [h0]
      exact V.zero_mem

theorem mem_compositeValuationSubring {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) (x : L) :
    x ∈ compositeValuationSubring W V ↔ ∃ h : x ∈ W, residue W ⟨x, h⟩ ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hV⟩
    exact ⟨⟨x, h⟩, hV, rfl⟩

theorem compositeValuationSubring_le {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) : compositeValuationSubring W V ≤ W :=
  fun x hx => ((mem_compositeValuationSubring W V x).1 hx).1

theorem exists_valuationSubring_le_dominating {O L : Type*} [CommRing O] [IsLocalRing O]
    [Field L] (g : O →+* L) (W : ValuationSubring L) (hg : ∀ x, g x ∈ W) :
    ∃ W' : ValuationSubring L, W' ≤ W ∧ (∀ x : O, g x ∈ W') ∧
      ∀ x ∈ maximalIdeal O, g x ∈ W'.nonunits := by
  let g' : O →+* W := g.codRestrict W.toSubring hg
  let f : O →+* ResidueField W := (residue W).comp g'
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨compositeValuationSubring W V, compositeValuationSubring_le W V, fun x =>
    (mem_compositeValuationSubring W V _).2 ⟨hg x, hV x⟩, fun x hx => ?_⟩
  rw [ValuationSubring.mem_nonunits_iff_or]
  rcases eq_or_ne (g x) 0 with h0 | h0
  · exact Or.inl h0
  refine Or.inr fun hinv => ?_
  obtain ⟨h, hres⟩ := (mem_compositeValuationSubring W V _).1 hinv
  have hmul : f x * residue W ⟨(g x)⁻¹, h⟩ = 1 := by
    change residue W (g' x) * _ = 1
    rw [← map_mul, ← map_one (residue W)]
    congr 1
    exact Subtype.ext (mul_inv_cancel₀ h0)
  have hu : IsUnit (f.codRestrict V.toSubring hV x) :=
    isUnit_iff_exists_inv.2 ⟨⟨_, hres⟩, Subtype.ext hmul⟩
  exact (mem_maximalIdeal x).1 hx (hloc.1 x hu)

theorem exists_valuationSubring_le_dominating_of_fractionField :
    ∀ (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
      [Algebra O F] [IsFractionRing O F] [Field L] (ι : F →+* L) (W : ValuationSubring L),
      (∀ x, ι x ∈ W) → ∃ W' : ValuationSubring L, W' ≤ W ∧
        (∀ x : O, ι (algebraMap O F x) ∈ W') ∧
        ∀ x ∈ IsLocalRing.maximalIdeal O, ι (algebraMap O F x) ∈ W'.nonunits := by
  intro O F L _ _ _ _ _ _ _ ι W hW
  exact exists_valuationSubring_le_dominating (ι.comp (algebraMap O F)) W fun x => hW _

end GlobalTheory
end

