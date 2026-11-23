module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SumCount
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sumCount :
    ∀ (R D M : Type) [CommRing R] [Group D] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R D M) (b : AddSubgroup M) (Z : AddSubgroup (D → M)), Finite Z → (∀ y ∈ b, (fun g => ρ g y - y) ∈ Z) → Finite ((Bl ρ).toAddSubgroup ⊔ Z : AddSubgroup (D → M)) ∧ Nat.card ((Bl ρ).toAddSubgroup ⊔ Z : AddSubgroup (D → M)) * Nat.card b ≤ Nat.card M * Nat.card Z := by
  intro R D M _ _ _ _ _ ρ b Z hZ hb
  let d : M →ₗ[R] (D → M) := LinearMap.pi fun g => ρ g - LinearMap.id
  have hd : ∀ y, d y = fun g => ρ g y - y := fun y => rfl
  let φ : M × Z →+ (D → M) := d.toAddMonoidHom.coprod Z.subtype
  have hφ : ∀ p : M × Z, φ p = d p.1 + p.2 := fun p => rfl
  have hr : φ.range = (Bl ρ).toAddSubgroup ⊔ Z := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hφ]
      exact AddSubgroup.add_mem_sup (show d p.1 ∈ (Bl ρ).toAddSubgroup from ⟨p.1, rfl⟩) p.2.2
    · refine sup_le ?_ ?_
      · rintro _ ⟨y, rfl⟩
        exact ⟨(y, 0), by rw [hφ]; exact add_zero _⟩
      · intro z hz
        exact ⟨(0, ⟨z, hz⟩), by rw [hφ]; simp⟩
  rw [← hr]
  have hfin : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  refine ⟨hfin, ?_⟩
  have h1 : Nat.card (M × Z) = Nat.card φ.range * Nat.card φ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
  have h2 : Nat.card b ≤ Nat.card φ.ker := by
    let ι : b → φ.ker := fun y => ⟨(y.1, -⟨fun g => ρ g y.1 - y.1, hb y.1 y.2⟩), by
      rw [AddMonoidHom.mem_ker, hφ, hd]
      exact add_neg_cancel _⟩
    refine Nat.card_le_card_of_injective ι fun y y' h => ?_
    exact Subtype.ext (congrArg (fun p : φ.ker => p.1.1) h)
  rw [← Nat.card_prod M Z, h1]
  exact Nat.mul_le_mul_left _ h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SumDegF
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sumDegF :
    ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F], ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, locDeg v.1 = Module.finrank ℚ F := by
  intro l _ F _ _
  classical
  have hl : l.Prime := Fact.out
  let p : Ideal ℤ := Ideal.span {(l : ℤ)}
  haveI hpmax : p.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hp0 : p ≠ ⊥ := by
    simp only [p, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hl.ne_zero
  let e1 : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} ≃
      {v : HeightOneSpectrum (𝓞 F) // v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 F)) p} :=
    Equiv.subtypeEquivRight (fun v => by
      rw [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
        map_natCast])
  let e := e1.trans (HeightOneSpectrum.equivPrimesOver (𝓞 F) hp0)
  have h1 : ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, locDeg v.1
      = ∑ᶠ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [← finsum_comp_equiv e]
    rfl
  rw [h1, finsum_eq_sum_of_fintype, Ideal.sum_ramification_inertia_eq_finrank,
    NumberField.RingOfIntegers.rank]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.TyCard
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem tc_perm {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (w : GL (Fin n) R) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, w (σ i) i ≠ 0 := by
  by_contra h
  push Not at h
  have hd : (w : Matrix (Fin n) (Fin n) R).det = 0 := by
    rw [Matrix.det_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    obtain ⟨i, hi⟩ := h σ
    have hp : ∏ j, (w : Matrix (Fin n) (Fin n) R) (σ j) j = 0 :=
      Finset.prod_eq_zero (f := fun j => (w : Matrix (Fin n) (Fin n) R) (σ j) j) (Finset.mem_univ i) hi
    rw [hp, smul_zero]
  have hu : IsUnit (w : Matrix (Fin n) (Fin n) R).det := (Matrix.isUnit_iff_isUnit_det _).1 w.isUnit
  exact hu.ne_zero hd

private theorem tc_inv {R : Type} [CommRing R] {n : ℕ} (w : GL (Fin n) R) (b t : Fin n → Bool)
    (h : ∀ i j, b i ≠ t j → w i j = 0) (i j : Fin n) (e : t i ≠ b j) : (w⁻¹ : GL (Fin n) R) i j = 0 := by
  classical
  set M : Matrix (Fin n) (Fin n) R := (w : Matrix (Fin n) (Fin n) R) with hM
  set N : Matrix (Fin n) (Fin n) R := ((w⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hN
  let Dt : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if t k then 1 else 0
  let Db : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if b k then 1 else 0
  have hc : M * Dt = Db * M := by
    ext p q
    simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hpq : b p = t q
    · rw [hpq]; ring
    · rw [show M p q = 0 from h p q hpq]; simp
  have hNM : N * M = 1 := Units.inv_mul w
  have hMN : M * N = 1 := Units.mul_inv w
  have key : Dt * N = N * Db := by
    calc Dt * N = N * M * Dt * N := by rw [hNM, Matrix.one_mul]
      _ = N * (M * Dt) * N := by simp only [Matrix.mul_assoc]
      _ = N * (Db * M) * N := by rw [hc]
      _ = N * Db * (M * N) := by simp only [Matrix.mul_assoc]
      _ = N * Db := by rw [hMN, Matrix.mul_one]
  have hij := congrFun (congrFun key i) j
  simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  cases hti : t i <;> cases hbj : b j <;> simp [hti, hbj] at hij e ⊢ <;>
    first | exact hij | exact hij.symm

private theorem tc_same {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card =
      (Finset.univ.filter fun i => t i = true).card.choose 2 +
        (Finset.univ.filter fun i => ¬ t i = true).card.choose 2 := by
  classical
  have hU : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2) =
      ((Finset.univ.filter fun i => t i = true) ×ˢ (Finset.univ.filter fun i => t i = true)).filter
          (fun p => p.1 < p.2) ∪
        ((Finset.univ.filter fun i => ¬ t i = true) ×ˢ
          (Finset.univ.filter fun i => ¬ t i = true)).filter (fun p => p.1 < p.2) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product]
    cases t x <;> cases t y <;> simp
  rw [hU, Finset.card_union_of_disjoint, Finset.card_product_filter_lt,
    Finset.card_product_filter_lt]
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at h1 h2
  exact h2.1.1 h1.1.1

private theorem tc_diff {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card =
      (Finset.univ.filter fun i => t i = true).card *
        (Finset.univ.filter fun i => ¬ t i = true).card := by
  classical
  have hsplit : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact h2.2.2 h1.2.2
  have htot : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card = n.choose 2 := by
    simpa using Fintype.card_product_filter_lt (α := Fin n)
  have hcard : (Finset.univ.filter fun i => t i = true).card +
      (Finset.univ.filter fun i => ¬ t i = true).card = n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hch : ∀ a b : ℕ, (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
    intro a b
    induction b with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ', Nat.choose_succ_succ' k, Nat.choose_one_right,
        Nat.choose_one_right, ih]
      ring
  have hh := hch (Finset.univ.filter fun i => t i = true).card
    (Finset.univ.filter fun i => ¬ t i = true).card
  rw [hcard] at hh
  rw [htot, tc_same t] at hsplit
  linarith

theorem UpperTheory.V.Pa.tyCard :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (v : F.Vl) (g : ℕ), (Finset.univ.filter fun i => x.ty v i = true).card = x.a ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 = x.ty v p.2).card + g * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = nu n x.a g ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = x.a * (n - x.a) ∧ ∀ i j : Fin n, x.ty v i ≠ decide ((j : ℕ) < x.a) → ((x.w v)⁻¹ : GL (Fin n) x.A) i j = 0 := by
  intro l _ F n x v g
  classical
  obtain ⟨σ, hσ⟩ := tc_perm (x.w v)
  have hty : ∀ j, x.ty v j = decide (((σ j : Fin n) : ℕ) < x.a) := by
    intro j
    by_contra hne
    exact hσ j (x.w_blk v (σ j) j (Ne.symm hne))
  have hT : (Finset.univ.filter fun i => x.ty v i = true).card = x.a := by
    rw [← Fintype.card_subtype, ← Fintype.card_fin_lt_of_le x.a_le]
    refine Fintype.card_congr (Equiv.subtypeEquiv σ fun j => ?_)
    rw [hty j]
    simp
  have hF : (Finset.univ.filter fun i => ¬ x.ty v i = true).card = n - x.a := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => x.ty v i = true)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [tc_same, tc_diff, hT, hF]
    simp [nu]
  · rw [tc_diff, hT, hF]
  · intro i j e
    exact tc_inv (x.w v) (fun k => decide ((k : ℕ) < x.a)) (x.ty v)
      (fun p q hpq => x.w_blk v p q hpq) i j e
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.UnrLoc
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ul_cop (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (n : ℕ) :
    (Nat.card (Fin n → kˣ)).Coprime l := by
  classical
  haveI := Fintype.ofFinite k
  have hl : l.Prime := Fact.out
  obtain ⟨m, -, hm⟩ := FiniteField.card k l
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_units, hm]
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
  intro hd
  have h1 : l ∣ l ^ (m : ℕ) := dvd_pow_self l m.ne_zero
  have h2 : 1 ≤ l ^ (m : ℕ) := Nat.one_le_pow _ _ hl.pos
  have h3 := Nat.dvd_sub h1 hd
  rw [Nat.sub_sub_self h2] at h3
  exact hl.one_lt.ne' (Nat.dvd_one.mp h3)

private theorem ul_ker {G C : Type} [Group G] [Group C] {n : ℕ} (f : Fin n → G →* C) :
    (MonoidHom.pi f).ker = ⨅ i, (f i).ker := by
  ext g
  simp [MonoidHom.mem_ker, Subgroup.mem_iInf, funext_iff]

theorem UpperTheory.V.Pa.unrLoc :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), ∀ u, UnrCount l ((locOf r).Gu u) ((locOf r).Ju u) := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r u
  haveI : CharP (IsLocalRing.ResidueField O) l := IsCoef.char
  haveI : Finite (IsLocalRing.ResidueField O) := IsCoef.finite
  unfold locOf
  dsimp only
  have key : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v →
      UnrCount l (Dec (F := L) A) ((Ine A).subgroupOf (Dec (F := L) A) ⊓
        ⨅ i, ((r.chib i).comp (V0.pr.comp (Dec (F := L) A).subtype)).ker) := by
    intro A v hv
    let χ := MonoidHom.pi (fun i => (r.chib i).comp (V0.pr.comp (Dec (F := L) A).subtype))
    have hker : χ.ker = ⨅ i, ((r.chib i).comp (V0.pr.comp (Dec (F := L) A).subtype)).ker := ul_ker _
    have hopen : IsOpen (χ.ker : Set (Dec (F := L) A)) := by
      rw [hker, Subgroup.coe_iInf]
      refine isOpen_iInter_of_finite fun i => ?_
      exact (r.chib_open i).preimage ((V0.pr_cont continuous_resP).comp continuous_subtype_val)
    have h := unrBare l L Ω A v _ χ hv hopen (ul_cop l _ n)
    rwa [hker] at h
  exact key _ _ (s.hw _)
end

