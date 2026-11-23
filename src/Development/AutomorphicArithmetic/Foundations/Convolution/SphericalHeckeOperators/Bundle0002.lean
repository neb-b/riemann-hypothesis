module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoVol
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem meas_union {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (A I J : Subgroup G) (t : G)
    (hJ : ∀ x, x ∈ J ↔ t⁻¹ * x * t ∈ I) (hI : MeasurableSet (I : Set G))
    [Finite (A ⧸ J.subgroupOf A)] :
    μ {g | ∃ x ∈ A, ∃ y ∈ I, g = x * t * y} = J.relIndex A * μ (I : Set G) := by
  classical
  let S : A ⧸ J.subgroupOf A → Set G := fun q => (fun g => ((q.out : G) * t)⁻¹ * g) ⁻¹' (I : Set G)
  have hU : {g | ∃ x ∈ A, ∃ y ∈ I, g = x * t * y} = ⋃ q, S q := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, S, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      refine ⟨((⟨x, hx⟩ : A) : A ⧸ J.subgroupOf A), ?_⟩
      have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨x, hx⟩ : A) : A ⧸ J.subgroupOf A))
      rw [Subgroup.mem_subgroupOf, hJ] at h
      have := I.mul_mem h hy
      simpa [mul_assoc] using this
    · rintro ⟨q, hq⟩
      exact ⟨q.out, q.out.2, _, hq, by group⟩
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro p q hpq
    refine Set.disjoint_left.2 fun g hp hq => hpq ?_
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, hJ]
    have := I.mul_mem hp (I.inv_mem hq)
    simpa [mul_assoc] using this
  rw [hU, measure_iUnion hd (fun q => measurable_const_mul _ hI)]
  simp only [S, measure_preimage_mul]
  rw [ENNReal.tsum_const, Subgroup.relIndex, Subgroup.index, ENat.card_eq_coe_natCard]
  simp

private theorem index_modular {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [LocallyCompactSpace B] [T2Space B] (A J : Subgroup B) (t : B) (hAc : IsCompact (A : Set B)) (hAo : IsOpen (A : Set B))
    (hJ : ∀ x, x ∈ J ↔ t⁻¹ * x * t ∈ A) (hJA : J ≤ A) :
    Measure.modularCharacter t * J.relIndex A = 1 := by
  borelize B
  let ν : Measure B := Measure.haar
  have hJs : (J : Set B) = (fun g => t⁻¹ * g) ⁻¹' ((fun g => g * t) ⁻¹' (A : Set B)) := by
    ext x; exact hJ x
  have hJo : IsOpen (J : Set B) := by
    rw [hJs]; exact (hAo.preimage (by fun_prop)).preimage (by fun_prop)
  have : CompactSpace A := isCompact_iff_compactSpace.1 hAc
  have : Finite (A ⧸ J.subgroupOf A) :=
    Subgroup.quotient_finite_of_isOpen _ (hJo.preimage continuous_subtype_val)
  have h1 := meas_union ν A J J 1 (by simp) hJo.measurableSet
  have h2 : {g | ∃ x ∈ A, ∃ y ∈ J, g = x * 1 * y} = (A : Set B) := by
    ext g
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact A.mul_mem (by simpa using hx) (hJA hy)
    · intro hg
      exact ⟨g, hg, 1, J.one_mem, by simp⟩
  have h3 : ν (J : Set B) = Measure.modularCharacter t * ν (A : Set B) := by
    rw [hJs, measure_preimage_mul, ← Measure.map_apply (measurable_mul_const t) hAo.measurableSet,
      Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure _ ν hAc.closure,
      ← Measure.modularCharacterFun_eq_haarScalarFactor]
    rfl
  rw [h2, h3, ← mul_assoc] at h1
  have h0 : ν (A : Set B) ≠ 0 := hAo.measure_ne_zero ν ⟨1, A.one_mem⟩
  have h4 : (J.relIndex A : ENNReal) * Measure.modularCharacter t = 1 := by
    apply (ENNReal.mul_left_inj h0 hAc.measure_lt_top.ne).1
    rw [← h1, one_mul]
  rw [mul_comm] at h4
  exact_mod_cast h4

private theorem meas_dcoset {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (B I : Subgroup G)
    [LocallyCompactSpace B] (hB : IsClosed (B : Set G)) (hIc : IsCompact (I : Set G)) (hIo : IsOpen (I : Set G))
    (t : B) (h1 : ∀ x ∈ B, x ∈ I → (t : G) * x * (t : G)⁻¹ ∈ I)
    (h2 : ∀ k ∈ I, ∃ x ∈ B, x ∈ I ∧ ∃ z, (t : G)⁻¹ * z * t ∈ I ∧ k = x * z) :
    Measure.modularCharacter t * μ {g | ∃ x ∈ I, ∃ y ∈ I, g = x * t * y} = μ (I : Set G) := by
  let J : Subgroup G := I.comap (MulAut.conj (t : G)⁻¹).toMonoidHom
  have hJ : ∀ x, x ∈ J ↔ (t : G)⁻¹ * x * t ∈ I := fun x => by simp [J]
  have hJo : IsOpen (J : Set G) := by
    have : (J : Set G) = (fun x => (t : G)⁻¹ * x * t) ⁻¹' (I : Set G) := Set.ext hJ
    rw [this]; exact hIo.preimage (by fun_prop)
  have hAc : IsCompact ((I ⊓ B : Subgroup G) : Set G) := hIc.inter_right hB
  have : CompactSpace (I ⊓ B : Subgroup G) := isCompact_iff_compactSpace.1 hAc
  have : Finite ((I ⊓ B : Subgroup G) ⧸ J.subgroupOf (I ⊓ B)) :=
    Subgroup.quotient_finite_of_isOpen _ (hJo.preimage continuous_subtype_val)
  have e1 := meas_union μ (I ⊓ B) I J t hJ hIo.measurableSet
  have e2 : {g | ∃ x ∈ I, ∃ y ∈ I, g = x * t * y} = {g | ∃ x ∈ I ⊓ B, ∃ y ∈ I, g = x * t * y} := by
    ext g
    constructor
    · rintro ⟨k, hk, y, hy, rfl⟩
      obtain ⟨x, hxB, hxI, z, hz, rfl⟩ := h2 k hk
      exact ⟨x, ⟨hxI, hxB⟩, _, I.mul_mem hz hy, by group⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx.1, y, hy, rfl⟩
  have e3 := index_modular (I.subgroupOf B) (J.subgroupOf B) t
    (hB.isClosedEmbedding_subtypeVal.isCompact_preimage hIc) (hIo.preimage continuous_subtype_val)
    (fun x => by rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hJ]; rfl)
    (fun x hx => by
      rw [Subgroup.mem_subgroupOf, hJ] at hx
      have := h1 _ (B.mul_mem (B.mul_mem (B.inv_mem t.2) x.2) t.2) hx
      rw [Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using this)
  have e4 : (J.subgroupOf B).relIndex (I.subgroupOf B) = J.relIndex (I ⊓ B) := by
    rw [← Subgroup.inf_subgroupOf_right I B, Subgroup.relIndex_subgroupOf inf_le_right]
  rw [e4] at e3
  rw [e2, e1, ← mul_assoc]
  have e5 : (Measure.modularCharacter t : ENNReal) * (J.relIndex (I ⊓ B) : ENNReal) = 1 := by
    exact_mod_cast e3
  rw [e5, one_mul]

private theorem conj_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    (a : Fin n → ℤ) {g : GL (Fin n) F} (hg : g ∈ iwahori F n)
    (h : ∀ i j, a i < a j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    torusPow F n a * g * (torusPow F n a)⁻¹ ∈ iwahori F n := by
  have he : ∀ i j, ((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) F) i j := by
    intro i j
    rw [← torusPow_neg, Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, Matrix.mul_diagonal,
      Matrix.diagonal_mul, sub_eq_add_neg, zpow_add₀ (GLnLocal.uniformizer_ne_zero F), Pi.neg_apply]
    ring
  have hle : ∀ i j, ValuativeRel.valuation F
      (((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) ≤
      ValuativeRel.valuation F ((g : Matrix (Fin n) (Fin n) F) i j) := by
    intro i j
    rw [he]
    rcases lt_or_ge (a i) (a j) with hij | hij
    · rw [h i j hij, mul_zero]
    · obtain ⟨d, hd⟩ : ∃ d : ℕ, a i - a j = d := ⟨(a i - a j).toNat, by omega⟩
      rw [hd, zpow_natCast, map_mul, map_pow]
      simpa [mul_comm] using mul_le_of_le_one_right' (a := ValuativeRel.valuation F ((g : Matrix (Fin n) (Fin n) F) i j)) (pow_le_one' (GLnLocal.valuation_uniformizer_lt_one F).le d)
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hg
  refine (mem_iwahori_iff F n).2 ⟨fun i j => (hle i j).trans (h1 i j),
    fun i j hij => (hle i j).trans_lt (h2 i j hij), fun i => ?_⟩
  rw [he, sub_self, zpow_zero, one_mul, h3]

theorem UpperTheory.ConvolutionTheory.H.dcoVol :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (a : Fin n → ℤ), Antitone a →
      halfModulus F a ^ 2 * (μ.real (dco F a) : ℂ) = (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) := by
  intro F _ _ _ _ n _ _ μ _ a ha
  have key := meas_dcoset μ (blockUpper F n (id : Fin n → Fin n)) (iwahori F n) (Measures.isClosed_blockUpper F n _)
    (isCompact_iwahori F n) (isOpen_iwahori F n) (torusBorel F n a)
    (fun x hxB hxI => conj_mem a hxI fun i j hij =>
      (mem_blockUpper F n).1 hxB (lt_of_not_ge fun h => (ha h).not_gt hij))
    (fun k hk => by
      obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
        Parabolic.iwahori_iwahoriFactorization' (β := (id : Fin n → Fin n)) monotone_id k hk
      refine ⟨x * y, mul_mem (Parabolic.unipotentRadical_le_blockUpper hx.2)
        (Parabolic.levi_le_blockUpper hy.2), mul_mem hx.1 hy.1, z, ?_, rfl⟩
      have := conj_mem (-a) hz.1 fun i j hij =>
        (Parabolic.mem_oppositeUnipotentRadical.1 hz.2).1 i j
          (lt_of_not_ge fun h => (ha h).not_gt (neg_lt_neg_iff.1 hij))
      rwa [torusPow_neg, inv_inv] at this)
  have h2 : halfModulus F a ^ 2 = ((Measure.modularCharacter (torusBorel F n a) : ℝ) : ℂ) := by
    rw [halfModulus_eq, modularCharacter_torusBorel, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, sqrtQ_sq]
    push_cast
    rfl
  rw [h2, measureReal_def, measureReal_def, ← key, ENNReal.toReal_mul, ENNReal.coe_toReal, Complex.ofReal_mul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.GapDom
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem mem_supp_monomial {n : ℕ} {a b : Fin n → ℤ}
    (h : a ∈ (monomial b : LaurentRing n).coeff.support) : a = b := by
  rw [AddMonoidAlgebra.coeff_single] at h
  simpa using Finsupp.support_single_subset h

private theorem card_touch_le {n : ℕ} (T : Finset (Fin n × Fin n)) (hT : T ⊆ pairs n) (j : Fin n) :
    (T.filter fun p => p.1 = j ∨ p.2 = j).card ≤ n := by
  have := Finset.card_le_card_of_injOn (s := T.filter fun p => p.1 = j ∨ p.2 = j) (t := Finset.univ)
    (fun p : Fin n × Fin n => if p.1 = j then p.2 else p.1) (fun _ _ => by simp) (by
      rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : a < b := by simpa [pairs] using hT hp.1
      have h2 : c < d := by simpa [pairs] using hT hq.1
      have h3 := hp.2
      have h4 := hq.2
      simp only at h h3 h4
      simp only [Prod.mk.injEq]
      split_ifs at h <;> omega)
  simpa using this

private def Bd {n : ℕ} (T : Finset (Fin n × Fin n)) (e : Fin n → ℤ) : Prop :=
  ∀ j, 0 ≤ e j ∧ e j ≤ ((T.filter fun p => p.1 = j ∨ p.2 = j).card : ℤ)

private theorem bd_insert {n : ℕ} {T : Finset (Fin n × Fin n)} {p : Fin n × Fin n} (hp : p ∉ T)
    {e : Fin n → ℤ} (he : Bd T e) {k : Fin n} (hk : k = p.1 ∨ k = p.2) :
    Bd (insert p T) (Pi.single k 1 + e) := by
  intro j
  obtain ⟨h0, h1⟩ := he j
  rw [Finset.filter_insert]
  by_cases hj : j = k
  · subst hj
    rw [if_pos (by tauto), Finset.card_insert_of_notMem (by simp [hp])]
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast
    omega
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hj]
    split_ifs
    · rw [Finset.card_insert_of_notMem (by simp [hp])]
      push_cast
      omega
    · omega

private theorem bd_sum {n : ℕ} (f : Fin n × Fin n → Fin n) (hf : ∀ p, f p = p.1 ∨ f p = p.2)
    (T : Finset (Fin n × Fin n)) : Bd T (∑ p ∈ T, Pi.single (f p) 1) := by
  induction T using Finset.induction_on with
  | empty => intro j; simp
  | insert p T hp ih => rw [Finset.sum_insert hp]; exact bd_insert hp ih (hf p)

private theorem bd_prod {n : ℕ} (t : ℂ) (T : Finset (Fin n × Fin n)) :
    ∀ a ∈ (∏ p ∈ T, (varL p.1 - t • varL p.2) : LaurentRing n).coeff.support, Bd T a := by
  induction T using Finset.induction_on with
  | empty =>
    intro a ha
    rw [Finset.prod_empty] at ha
    have : a = 0 := mem_supp_monomial (b := 0) ha
    subst this
    intro j; simp
  | insert p T hp ih =>
    intro a ha
    rw [Finset.prod_insert hp] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)
    rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul] at hb
    rcases Finset.mem_union.1 (Finsupp.support_sub hb) with hb | hb
    · rw [mem_supp_monomial hb]; exact bd_insert hp (ih c hc) (Or.inl rfl)
    · rw [mem_supp_monomial (Finsupp.support_smul hb)]; exact bd_insert hp (ih c hc) (Or.inr rfl)

private theorem anti_of_bd {n : ℕ} {ν e : Fin n → ℤ} (hν : Gap n ν) {T : Finset (Fin n × Fin n)}
    (hT : T ⊆ pairs n) (he : Bd T e) : Antitone (ν + e) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · have h1 := hν i j hij
    have h2 := (he i).1
    have h3 := (he j).2
    have h4 := card_touch_le T hT j
    simp only [Pi.add_apply]
    omega

theorem UpperTheory.ConvolutionTheory.H.gapDom :
    ∀ (n : ℕ) (ν : Fin n → ℤ), Gap n ν → (∀ S ∈ (pairs n).powerset, Antitone (ν + eL S) ∧ Antitone (ν + eR S)) ∧
      (∀ t : ℂ, Dom (monomial ν * dPol n t)) ∧ ∀ a, Antitone a → Gap n (a + ν) := by
  intro n ν hν
  refine ⟨fun S hS => ⟨?_, ?_⟩, fun t a ha => ?_, fun a ha i j hij => ?_⟩
  · exact anti_of_bd hν (Finset.mem_powerset.1 hS) (bd_sum Prod.fst (fun _ => Or.inl rfl) S)
  · exact anti_of_bd hν Finset.sdiff_subset (bd_sum Prod.snd (fun _ => Or.inr rfl) _)
  · obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)
    rw [mem_supp_monomial hb]
    exact anti_of_bd hν subset_rfl (bd_prod t _ c hc)
  · have h1 := hν i j hij
    have h2 := ha hij.le
    simp only [Pi.add_apply]
    omega
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.HlEval
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem he_single {n : ℕ} (i : Fin n) (m : ℤ) (w : Fin n → ℂˣ) : monomialChar (Pi.single i m : Fin n → ℤ) w = (w i : ℂ) ^ m := by
  rw [monomialChar_apply, Finset.prod_eq_single i] <;> simp +contextual [Pi.single_apply]

private theorem he_d {n : ℕ} (w : Fin n → ℂˣ) : evalAt w (dPol n 1) = ∏ p ∈ pairs n, ((w p.1 : ℂ) - w p.2) := by
  rw [dPol, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, one_smul, evalAt_single, evalAt_single, he_single, he_single]
  simp

private theorem he_det {n : ℕ} (w : Fin n → ℂˣ) :
    evalAt w (dPol n 1) = (Matrix.projVandermonde (fun _ => (1 : ℂ)) fun i => (w i : ℂ)).det := by
  rw [he_d, Matrix.det_projVandermonde, Finset.prod_sigma', pairs]
  refine Finset.prod_nbij' (fun p => ⟨p.1, p.2⟩) (fun p => (p.1, p.2)) ?_ ?_ ?_ ?_ ?_ <;> simp

private theorem he_alt {n : ℕ} (w : Fin n → ℂˣ) : evalAt w (alternant (staircase n)) = evalAt w (dPol n 1) := by
  rw [he_det, alternant_eq_det, AlgHom.map_det]
  congr 1
  ext a b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, monomial, evalAt_single, he_single, one_mul,
    Matrix.projVandermonde_apply, one_pow]
  rw [← zpow_natCast]
  congr 1
  have := b.2
  simp only [staircase, Fin.val_rev]
  omega

private theorem he_sgn {n : ℕ} (w : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) :
    evalAt (w ∘ σ) (dPol n 1) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt w (dPol n 1) := by
  rw [he_det, he_det, ← Matrix.det_permute]
  rfl

theorem UpperTheory.ConvolutionTheory.H.hlEval :
    ∀ (n : ℕ) (t : ℂ) (z : Fin n → ℂˣ), Function.Injective z → ∀ a : Fin n → ℤ,
      (∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n 1) ≠ 0) ∧
      evalAt z (hlR t a) = ∑ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n t) / evalAt (z ∘ σ) (dPol n 1) * monomialChar a (z ∘ σ) := by
  intro n t z hz a
  have hne : ∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n 1) ≠ 0 := fun σ => by
    rw [he_d]
    refine Finset.prod_ne_zero_iff.2 fun p hp => sub_ne_zero.2 fun h => ?_
    have h1 : p.1 < p.2 := by simpa [pairs] using hp
    exact h1.ne (σ.injective (hz (Units.ext h)))
  refine ⟨hne, ?_⟩
  have h1 := congrArg (evalAt z) (alternant_mul_altQuot (monomial a * hlFactor n t))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, he_alt, antisymm_apply, map_sum] at h1
  have h0 : evalAt z (dPol n 1) ≠ 0 := hne 1
  refine mul_left_cancel₀ h0 (h1.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h2 := he_sgn z σ
  have h3 := hne σ
  rw [Units.smul_def, map_zsmul, evalAt_permAct, map_mul, monomial, evalAt_single, one_mul, zsmul_eq_mul]
  have h4 : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h5 : evalAt z (dPol n 1) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt (z ∘ σ) (dPol n 1) := by
    rw [h2, ← mul_assoc, h4, one_mul]
  rw [h5]
  change _ * (_ * evalAt (z ∘ σ) (dPol n t)) = _
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.MemSuppMono
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem UpperTheory.ConvolutionTheory.H.mem_supp_mono {n : ℕ} {a c : Fin n → ℤ} {q : LaurentRing n}
    (h : c ∈ (monomial a * q).coeff.support) : -a + c ∈ q.coeff.support := by
  rw [Finsupp.mem_support_iff] at h ⊢
  have e : (monomial a * q).coeff c = 1 * q.coeff (-a + c) :=
    AddMonoidAlgebra.coeff_single_mul_apply q 1 a c
  rw [e, one_mul] at h
  exact h

private theorem UpperTheory.ConvolutionTheory.H.gap_strict {n : ℕ} (B : Finset (Fin n → ℤ)) :
    ∃ m : ℕ, ∀ a : Fin n → ℤ, Gap m a → ∀ b ∈ B, StrictAnti (a + b) := by
  classical
  set M : ℕ := ∑ b ∈ B, ∑ i, (b i).natAbs with hM
  have hb : ∀ b ∈ B, ∀ i, (b i).natAbs ≤ M := fun b hb i =>
    (Finset.single_le_sum (f := fun i => (b i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun b : Fin n → ℤ => ∑ i, (b i).natAbs)
        (fun _ _ => Nat.zero_le _) hb)
  refine ⟨2 * M + 1, fun a ha b hbB i j hij => ?_⟩
  have h1 := ha i j hij
  have h2 := hb b hbB i
  have h3 := hb b hbB j
  simp only [Pi.add_apply]
  push_cast at h1
  omega

private theorem UpperTheory.ConvolutionTheory.H.Gap.mono {n : ℕ} {m m' : ℕ} (h : m ≤ m') {a : Fin n → ℤ}
    (ha : Gap m' a) : Gap m a := fun i j hij => by
  have := ha i j hij
  have h' : (m : ℤ) ≤ m' := by exact_mod_cast h
  omega

private theorem UpperTheory.ConvolutionTheory.H.Gap.scale {n : ℕ} {m l : ℕ} (hl : 1 ≤ l) {a : Fin n → ℤ}
    (ha : Gap m a) : Gap m ((l : ℤ) • a) := fun i j hij => by
  have h := ha i j hij
  have h' : (1 : ℤ) ≤ l := by exact_mod_cast hl
  have hm : (0 : ℤ) ≤ m := by positivity
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith

private theorem UpperTheory.ConvolutionTheory.H.bc_monomial {n : ℕ} (l : ℕ) (a : Fin n → ℤ) :
    bc l (monomial a) = monomial ((l : ℤ) • a) := by
  simp only [bc, AddMonoidAlgebra.mapDomainAlgHom_apply, monomial, AddMonoidAlgebra.mapDomain_single]
  rfl

private theorem UpperTheory.ConvolutionTheory.H.monomial_pow {n : ℕ} (l : ℕ) (a : Fin n → ℤ) :
    monomial ((l : ℤ) • a) = monomial a ^ l := by
  induction l with
  | zero => simp [monomial, AddMonoidAlgebra.one_def]
  | succ k ih =>
    rw [pow_succ, ← ih, ← monomial_add]
    congr 1
    push_cast
    rw [add_smul, one_smul]

private noncomputable def UpperTheory.ConvolutionTheory.H.cof (n l : ℕ) (t : ℂ) : LaurentRing n :=
  ∏ p ∈ pairs n, ∑ k ∈ Finset.range l, varL p.1 ^ k * (t • varL p.2) ^ (l - 1 - k)

private theorem UpperTheory.ConvolutionTheory.H.bc_dPol (n l : ℕ) (t : ℂ) :
    bc l (dPol n (t ^ l)) = dPol n t * cof n l t := by
  simp only [dPol, cof, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, map_smul, mul_comm, geom_sum₂_mul, smul_pow]
  simp only [varL, bc_monomial, monomial_pow]

theorem UpperTheory.ConvolutionTheory.H.depth :
    ∀ (n l : ℕ), 1 ≤ l → ∀ (t : ℂ) (P : Finset (LaurentRing n)) (ν ν' : Fin n → ℤ), ∃ m : ℕ, ∀ a : Fin n → ℤ, Gap m a → ∀ p ∈ P,
      SDom (monomial a * dPol n (t ^ l) * p) ∧
      (∃ r, Dom r ∧ monomial a * dPol n (t ^ l) * p = monomial ν * dPol n (t ^ l) * r) ∧
      ∃ r', Dom r' ∧ bc l (monomial a * dPol n (t ^ l) * p) = monomial ν' * dPol n t * r' := by
  classical
  intro n l hl t P ν ν'
  obtain ⟨m₁, h₁⟩ := gap_strict (P.biUnion fun p => (dPol n (t ^ l) * p).coeff.support)
  obtain ⟨m₂, h₂⟩ := gap_strict (P.biUnion fun p => p.coeff.support.image (· - ν))
  obtain ⟨m₃, h₃⟩ := gap_strict
    (P.biUnion fun p => (cof n l t * bc l p).coeff.support.image (· - ν'))
  refine ⟨m₁ + m₂ + m₃, fun a ha p hp => ⟨?_, ⟨monomial (a - ν) * p, ?_, ?_⟩,
    ⟨monomial ((l : ℤ) • a - ν') * (cof n l t * bc l p), ?_, ?_⟩⟩⟩
  · intro c hc
    rw [mul_assoc] at hc
    have hb := mem_supp_mono hc
    have := h₁ a (Gap.mono (by omega) ha) (-a + c)
      (Finset.mem_biUnion.2 ⟨p, hp, hb⟩)
    simpa using this
  · intro c hc
    have hb := mem_supp_mono hc
    have := h₂ a (Gap.mono (by omega) ha) (-(a - ν) + c - ν)
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)
    have e : a + (-(a - ν) + c - ν) = c := by abel
    rw [e] at this
    exact this.antitone
  · have e : monomial a = monomial ν * monomial (a - ν) := by
      rw [← monomial_add]; congr 1; abel
    rw [e]; ring
  · intro c hc
    have hb := mem_supp_mono hc
    have := h₃ ((l : ℤ) • a) (Gap.scale hl (Gap.mono (by omega) ha))
      (-((l : ℤ) • a - ν') + c - ν')
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)
    have e : (l : ℤ) • a + (-((l : ℤ) • a - ν') + c - ν') = c := by abel
    rw [e] at this
    exact this.antitone
  · have e : monomial ((l : ℤ) • a) = monomial ν' * monomial ((l : ℤ) • a - ν') := by
      rw [← monomial_add]; congr 1; abel
    rw [map_mul, map_mul, bc_monomial, bc_dPol, e]; ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymAlg
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

theorem UpperTheory.ConvolutionTheory.H.symAlg :
    ∀ (n l : ℕ) (y : LaurentRing n),
      symSum y ∈ symmetricLaurent (n := n) ∧ bc l (symSum y) = symSum (bc l y) ∧
      (∀ p ∈ symmetricLaurent (n := n), symSum (y * p) = symSum y * p) ∧
      (y ∈ symmetricLaurent (n := n) → bc l y ∈ symmetricLaurent (n := n)) ∧
      ∀ z : Fin n → ℂˣ, evalAt z (bc l y) = evalAt (z ^ l) y := by
  intro n l y
  have hb : ∀ (a : Fin n → ℤ) (c : ℂ), bc l (AddMonoidAlgebra.single a c : LaurentRing n) = AddMonoidAlgebra.single ((l : ℤ) • a) c := by
    intro a c
    simp [bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]
  have hc : ∀ (σ : Equiv.Perm (Fin n)) (y : LaurentRing n), bc l (permAct σ y) = permAct σ (bc l y) := fun σ y => by
    have : (bc l).comp (permAct σ) = (permAct σ).comp (bc (n := n) l) :=
      AddMonoidAlgebra.algHom_ext (fun a => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, permAct_single, hb, hb, permAct_single]; rfl) (Subsingleton.elim _ _)
    exact AlgHom.congr_fun this y
  refine ⟨fun τ => ?_, ?_, fun p hp => ?_, fun hy σ => ?_, fun z => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [symSum, map_sum]
      simp only [permAct_permAct]
      exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [symSum, symSum, map_sum]
      exact Finset.sum_congr rfl fun σ _ => hc σ y
  · rw [symSum, symSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by rw [map_mul, hp σ]
  · rw [← hc, hy σ]
  · have : (evalAt z).comp (bc l) = evalAt (z ^ l) :=
      AddMonoidAlgebra.algHom_ext (fun a => by
        rw [AlgHom.comp_apply, hb, evalAt_single, evalAt_single, monomialChar_apply, monomialChar_apply]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, zpow_mul, zpow_natCast, Pi.pow_apply]) (Subsingleton.elim _ _)
    exact AlgHom.congr_fun this y
end

