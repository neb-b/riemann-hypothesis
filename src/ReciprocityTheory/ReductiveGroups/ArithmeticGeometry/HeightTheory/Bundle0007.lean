module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import ReciprocityTheory.SemistableReduction.Bundle0006
public import Mathlib
public import ReciprocityTheory.SemistableReduction.Bundle0001
public import ReciprocityTheory.SemistableReduction.Bundle0008
public import ReciprocityTheory.SemistableReduction.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraicIndependentResidueOfIsUnit
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

theorem mem_valuationRing {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) (x : E) :
    x ∈ vRing v ↔ 0 ≤ v x :=
  (Valuation.mem_valuationSubring_iff (v : Valuation E (Multiplicative (WithTop ℤ)ᵒᵈ)) x).trans Iff.rfl

theorem algebraicIndependent_residue_of_isUnit {A R E : Type} [CommRing A] [Field R] [Field E] (V : ValuationSubring E)
    [Algebra R (IsLocalRing.ResidueField V)] (φ : A →+* V) (ψ : A →+* R)
    (hψ : Function.Surjective ψ)
    (hc : ∀ a, algebraMap R (IsLocalRing.ResidueField V) (ψ a) = IsLocalRing.residue V (φ a))
    {τ : Type} (t : τ → V) (h : ∀ q : MvPolynomial τ A, q.map ψ ≠ 0 → IsUnit (eval₂ φ t q)) :
    AlgebraicIndependent R (fun j => IsLocalRing.residue V (t j)) := by
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hne
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective ψ hψ P
  have hu := (h q hne).map (IsLocalRing.residue V)
  have key : IsLocalRing.residue V (eval₂ φ t q) =
      MvPolynomial.aeval (fun j => IsLocalRing.residue V (t j)) (q.map ψ) := by
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    exact RingHom.ext fun a => (hc a).symm
  rw [key, hP] at hu
  exact not_isUnit_zero hu

theorem trdeg_residue_le {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D : ℕ)
    (hD : Algebra.trdeg K Ω = D) (v : AddValuation Ω (WithTop ℤ))
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = 0) (a0 : Ω) (ha0 : a0 ≠ 0) (hva0 : v a0 ≠ 0) :
    @Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
      (IsLocalRing.ResidueField (vRing v)) _ _ (resAlg (F := K) v) ≤ ((D - 1 : ℕ) : Cardinal) := by
  set V := vRing v with hV
  set k := IsLocalRing.ResidueField (V.comap (algebraMap K Ω)) with hk
  set κ := IsLocalRing.ResidueField V with hκ
  letI inst : Algebra k κ := resAlg (F := K) v
  have hKV : ∀ a : K, algebraMap K Ω a ∈ V := by
    intro a
    rw [hV, mem_valuationRing]
    by_cases ha : a = 0
    · rw [ha, map_zero, AddValuation.map_zero]
      exact le_top
    · exact le_of_eq (hK a ha).symm
  let jK : K →+* V := (algebraMap K Ω).codRestrict V hKV
  let jW : K →+* V.comap (algebraMap K Ω) :=
    (RingHom.id K).codRestrict (V.comap (algebraMap K Ω)) fun a => ValuationSubring.mem_comap.mpr (hKV a)
  let ιK : K →+* k := (IsLocalRing.residue _).comp jW
  have hcompat : ∀ a : K, algebraMap k κ (ιK a) = IsLocalRing.residue V (jK a) := by
    intro a
    show IsLocalRing.ResidueField.map (comapIncl V (algebraMap K Ω)) (IsLocalRing.residue _ (jW a)) = _
    rw [IsLocalRing.ResidueField.map_residue]
    rfl
  have hle : Algebra.trdeg k κ ≤ D := by
    have h := ReciprocityTheory.MultiplicativeHeights.residueTrdegLe K Ω V
    rw [hD] at h
    exact h
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Algebra.trdeg k κ = r :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt hle Cardinal.natCast_lt_aleph0)
  haveI : FaithfulSMul k κ :=
    (faithfulSMul_iff_algebraMap_injective k κ).mpr (algebraMap k κ).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k κ
  have hsr : Cardinal.mk s = r := by rw [hs.cardinalMk_eq_trdeg, hr]
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hsr
  let ρ : Fin r → κ := fun i => (e.symm i : κ)
  have hρ : AlgebraicIndependent k ρ := hs.1.comp e.symm e.symm.injective
  choose tV htV using fun i => IsLocalRing.residue_surjective (R := V) (ρ i)
  let t : Fin r → Ω := fun i => (tV i : Ω)
  let ψ : MvPolynomial (Fin r) K →+* V := MvPolynomial.eval₂Hom jK tV
  have hψ : ∀ p, (ψ p : Ω) = MvPolynomial.aeval t p := by
    intro p
    show V.subtype (MvPolynomial.eval₂ jK tV p) = _
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def]
    congr 1
  have hres : ∀ p, IsLocalRing.residue V (ψ p) = MvPolynomial.aeval ρ (p.map ιK) := by
    intro p
    show IsLocalRing.residue V (MvPolynomial.eval₂ jK tV p) = _
    have hf : (IsLocalRing.residue V).comp jK = (algebraMap k κ).comp ιK :=
      RingHom.ext fun a => (hcompat a).symm
    have hg : (fun i => IsLocalRing.residue V (tV i)) = ρ := funext htV
    rw [MvPolynomial.hom_eval₂, hf, hg, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  have hG : ∀ p : MvPolynomial (Fin r) K, p ≠ 0 → v (MvPolynomial.aeval t p) = 0 := by
    intro p hp
    have hne : MvPolynomial.aeval ρ (p.map ιK) ≠ 0 := by
      intro h0
      apply hp
      apply MvPolynomial.map_injective ιK ιK.injective
      rw [map_zero]
      exact (algebraicIndependent_iff.mp hρ) _ h0
    rw [← hres] at hne
    have hu := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne
    rw [← hψ]
    obtain ⟨u, hu'⟩ := hu
    have hmul : (ψ p : Ω) * ((↑u⁻¹ : V) : Ω) = 1 := by
      have h1 := u.mul_inv
      rw [hu'] at h1
      exact congrArg Subtype.val h1
    have hsum : v (ψ p : Ω) + v ((↑u⁻¹ : V) : Ω) = 0 := by
      rw [← AddValuation.map_mul, hmul, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg ((mem_valuationRing v _).mp (ψ p).2)
      ((mem_valuationRing v _).mp (↑u⁻¹ : V).2)).mp hsum).1
  have ht : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra hne
    have h1 := hG p hne
    rw [hp, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : WithTop ℤ) = v a0 :=
    WithTop.ne_top_iff_exists.mp (by rw [Ne, AddValuation.top_iff]; exact ha0)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hva0 hm.symm
  have htr : Transcendental (Algebra.adjoin K (Set.range t)) a0 := by
    rintro ⟨q, hq0, hq⟩
    have hcv : ∀ j, q.coeff j ≠ 0 → v ((q.coeff j : Ω)) = 0 := by
      intro j hj
      have hmem : (q.coeff j : Ω) ∈ (MvPolynomial.aeval (R := K) t).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval K t]
        exact (q.coeff j).2
      obtain ⟨p, hp⟩ := hmem
      have hp0 : p ≠ 0 := by
        rintro rfl
        apply hj
        apply Subtype.ext
        rw [← hp, map_zero]
        rfl
      rw [← hp]
      exact hG p hp0
    rw [Polynomial.aeval_eq_sum_range] at hq
    obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image q.support (fun j => (j : ℤ) * m)
      (Polynomial.nonempty_support_iff.mpr hq0)
    have hj0S : j0 ∈ Finset.range (q.natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp j0 hj0))
    have hterm : ∀ j, q.coeff j ≠ 0 → v (q.coeff j • a0 ^ j) = (((j : ℤ) * m : ℤ) : WithTop ℤ) := by
      intro j hj
      rw [Algebra.smul_def, AddValuation.map_mul, AddValuation.map_pow, ← hm]
      have e1 : algebraMap (Algebra.adjoin K (Set.range t)) Ω (q.coeff j) = (q.coeff j : Ω) := rfl
      rw [e1, hcv j hj, zero_add, ← WithTop.coe_nsmul, nsmul_eq_mul]
    have hg : v (q.coeff j0 • a0 ^ j0) = (((j0 : ℤ) * m : ℤ) : WithTop ℤ) :=
      hterm j0 (Polynomial.mem_support_iff.mp hj0)
    have hrest : v (q.coeff j0 • a0 ^ j0) <
        v (∑ j ∈ (Finset.range (q.natDegree + 1)).erase j0, q.coeff j • a0 ^ j) := by
      rw [hg]
      apply AddValuation.map_lt_sum _ WithTop.coe_ne_top
      intro j hj
      by_cases hc : q.coeff j = 0
      · rw [hc, zero_smul, AddValuation.map_zero]
        exact WithTop.coe_lt_top _
      · rw [hterm j hc, WithTop.coe_lt_coe]
        have hne : j ≠ j0 := Finset.ne_of_mem_erase hj
        have hle := hmin j (Polynomial.mem_support_iff.mpr hc)
        have hneq : (j0 : ℤ) * m ≠ (j : ℤ) * m := by
          intro h
          apply hne
          exact_mod_cast (mul_right_cancel₀ hm0 h).symm
        exact lt_of_le_of_ne hle hneq
    rw [← Finset.add_sum_erase _ _ hj0S] at hq
    have h2 := AddValuation.map_add_eq_of_lt_left v hrest
    rw [hq, AddValuation.map_zero, hg] at h2
    exact WithTop.top_ne_coe h2
  have hind : AlgebraicIndependent K (fun o : Option (Fin r) => o.elim a0 t) :=
    AlgebraicIndependent.option_iff.mpr ⟨ht, htr⟩
  have hcardle := hind.cardinalMk_le_trdeg
  rw [hD, Cardinal.mk_option, Cardinal.mk_fintype, Fintype.card_fin] at hcardle
  have hrD : r + 1 ≤ D := by exact_mod_cast hcardle
  have hfin : Algebra.trdeg k κ ≤ ((D - 1 : ℕ) : Cardinal) := by
    rw [hr]
    exact_mod_cast (by omega : r ≤ D - 1)
  exact hfin

theorem trdeg_eq_of_card {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E] [Algebra E C]
    [Algebra F C] {σ τ : Type} [Fintype σ] [Fintype τ] (tb : σ → C)
    (ub : τ → C) (hu : AlgebraicIndependent F ub)
    (hmem : ∀ j, ub j ∈ Algebra.adjoin E (Set.range tb)) (n : ℕ)
    (hE : Algebra.trdeg F E ≤ n) (hcard : Fintype.card τ = Fintype.card σ + n)
    (hT : ∀ x : F, algebraMap F C x = algebraMap E C (algebraMap F E x)) :
    Algebra.trdeg F E = n ∧ AlgebraicIndependent E tb := by
  haveI : IsScalarTower F E C := IsScalarTower.of_algebraMap_eq hT
  have h1 := ReciprocityTheory.MultiplicativeHeights.gauss_card_le_trdeg_add tb ub hu hmem
  have h2 := ReciprocityTheory.MultiplicativeHeights.gauss_trdeg_adjoin_le (E := E) tb
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Algebra.trdeg F E = a :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt hE Cardinal.natCast_lt_aleph0)
  rw [Cardinal.mk_fintype] at h2
  obtain ⟨b, hb⟩ : ∃ b : ℕ, Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) = b :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt h2 Cardinal.natCast_lt_aleph0)
  rw [Cardinal.mk_fintype, hcard, ha, hb] at h1
  rw [ha] at hE
  rw [hb] at h2
  have h1' : Fintype.card σ + n ≤ a + b := by exact_mod_cast h1
  have hE' : a ≤ n := by exact_mod_cast hE
  have h2' : b ≤ Fintype.card σ := by exact_mod_cast h2
  have han : a = n := by omega
  have hbs : b = Fintype.card σ := by omega
  refine ⟨by rw [ha, han], ReciprocityTheory.MultiplicativeHeights.gauss_indep_of_le_trdeg tb ?_⟩
  rw [hb, hbs, Cardinal.mk_fintype]

theorem isUnit_of_val_eq_zero' {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {z : E}
    (h : z ∈ vRing v) (hz : v z = 0) : IsUnit (⟨z, h⟩ : vRing v) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hz
    exact WithTop.top_ne_coe hz
  have hinv : z⁻¹ ∈ vRing v := by
    rw [mem_valuationRing, AddValuation.map_inv, hz, neg_zero]
  exact IsUnit.of_mul_eq_one (⟨z⁻¹, hinv⟩ : vRing v) (Subtype.ext (mul_inv_cancel₀ hz0))

theorem val_eq_zero_of_isUnit' {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {z : E}
    (h : z ∈ vRing v) (hu : IsUnit (⟨z, h⟩ : vRing v)) : v z = 0 := by
  obtain ⟨u, hu⟩ := hu
  have hmul : z * ((↑u⁻¹ : vRing v) : E) = 1 := by
    have h1 := u.mul_inv
    rw [hu] at h1
    exact congrArg Subtype.val h1
  have hsum : v z + v ((↑u⁻¹ : vRing v) : E) = 0 := by
    rw [← AddValuation.map_mul, hmul, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg ((mem_valuationRing v z).mp h)
    ((mem_valuationRing v _).mp (↑u⁻¹ : vRing v).2)).mp hsum).1

theorem scalarRatio_eq {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  have he : ∃ b : Ω, f = b • g := ⟨a, h⟩
  rw [ratio, dite_eq_left he]
  exact smul_left_injective Ω hg (he.choose_spec.symm.trans h)

theorem genericImage_base {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (i : Fin (D + 1)) :
    sImg j₀ x (i, j₀) = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
      (if i = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (x k)) := by
  rw [sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]

theorem genericImage_succAbove {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (i : Fin (D + 1)) (k : Fin N) :
    sImg j₀ x (i, j₀.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (MvPolynomial.X (Sum.inr (i, k))) := by
  rw [sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CastAddNeNatAdd
section
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB

open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights

section MH

variable {R : Type*} [CommSemiring R] {B n : ℕ}

theorem isMH_zero (a : Fin B → ℕ) : IsMultiHomogeneous a (0 : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs; simp at hs

theorem isMH_C (r : R) : IsMultiHomogeneous (0 : Fin B → ℕ) (C r : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs b
  rw [mem_support_iff, coeff_C] at hs
  have : (0 : Fin B × Fin n →₀ ℕ) = s := by
    by_contra h; exact hs (if_neg h)
  subst this; simp

theorem isMH_add {a : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous a g) : IsMultiHomogeneous a (f + g) := by
  classical
  intro s hs
  rcases Finset.mem_union.1 (support_add hs) with h | h
  exacts [hf s h, hg s h]

theorem isMH_mul_X {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (a + Pi.single i 1) (f * X (i, j)) := by
  classical
  intro s hs b
  rw [support_mul_X, Finset.mem_map] at hs
  obtain ⟨s', hs', rfl⟩ := hs
  simp only [addRightEmbedding_apply, Finsupp.add_apply, Finset.sum_add_distrib, hf s' hs' b,
    Pi.add_apply]
  congr 1
  by_cases hb : b = i
  · subst hb; simp [Finsupp.single_apply]
  · simp [hb]

end MH

theorem countable_mvPoly {σ R : Type*} [Countable σ] [CommSemiring R] [Countable R] :
    Countable (MvPolynomial σ R) := by
  classical
  refine Function.Surjective.countable (f := fun f : (σ →₀ ℕ) →₀ R => f.sum fun m a => monomial m a) ?_
  intro p
  refine ⟨Finsupp.onFinset p.support (fun m => AddMonoidAlgebra.coeff p m) (fun m hm => mem_support_iff.2 hm), ?_⟩
  dsimp only
  rw [Finsupp.onFinset_sum _ (fun m => by simp)]
  exact (MvPolynomial.as_sum p).symm

variable {K : Type} [Field K] {D N : ℕ}

noncomputable def hImg (p : Fin (D + 1) × Fin (N + 1)) :
    MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) :=
  Fin.cases (motive := fun _ => Fin (N + 1) → MvPolynomial (Fin (N + 1 + D))
      (MvPolynomial (Fin D × Fin (N + 1)) K))
    (fun j => X (Fin.castAdd D j)) (fun i j => X (Fin.natAdd (N + 1) i) * C (X (i, j))) p.1 p.2

@[simp] theorem hImg_zero (j : Fin (N + 1)) :
    hImg (K := K) (D := D) ((0 : Fin (D + 1)), j) = X (Fin.castAdd D j) := by
  simp [hImg]

@[simp] theorem hImg_succ (i : Fin D) (j : Fin (N + 1)) :
    hImg (K := K) (i.succ, j) = X (Fin.natAdd (N + 1) i) * C (X (i, j)) := by
  simp [hImg]

noncomputable def homog : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →ₐ[K]
    MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) :=
  aeval hImg

noncomputable def back : MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) →+*
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
  eval₂Hom (rename fun p : Fin D × Fin (N + 1) => (p.1.succ, p.2)).toRingHom
    (Fin.addCases (fun j => X (0, j)) (fun _ => 1))

theorem back_homog (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) : back (homog q) = q := by
  have : (back (K := K) (D := D) (N := N)).comp (homog (K := K)).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [back, homog, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, j⟩
      cases i using Fin.cases with
      | zero => simp [back, homog]
      | succ i => simp [back, homog]
  exact congrArg (fun f => f q) this

theorem homog_injective : Function.Injective (homog (K := K) (D := D) (N := N)) :=
  Function.LeftInverse.injective back_homog

theorem castAdd_ne_natAdd (j : Fin (N + 1)) (i : Fin D) : Fin.castAdd D j ≠ Fin.natAdd (N + 1) i := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem homog_coeff_isMH (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    ∀ γ : Fin (N + 1 + D) →₀ ℕ,
    IsMultiHomogeneous (fun i => γ (Fin.natAdd (N + 1) i)) (AddMonoidAlgebra.coeff (homog q) γ) := by
  classical
  induction q using MvPolynomial.induction_on
  · rename_i a
    intro γ
    rw [show homog (C a) = C (C a) from by simp [homog, MvPolynomial.algebraMap_eq], coeff_C]
    split_ifs with h
    · subst h
      intro s hs b
      simpa using isMH_C (B := D) (n := N + 1) a s hs b
    · exact isMH_zero _
  · rename_i p q hp hq
    intro γ
    rw [map_add (f := _), MvPolynomial.coeff_add]; exact isMH_add (hp γ) (hq γ)
  · rename_i p v hp
    intro γ
    obtain ⟨i, j⟩ := v
    rw [map_mul, show homog (X (i, j)) = hImg (K := K) (i, j) from aeval_X _ _]
    cases i using Fin.cases with
    | zero =>
      rw [hImg_zero, coeff_mul_X']
      split_ifs with h
      · have := hp (γ - Finsupp.single (Fin.castAdd D j) 1)
        convert this using 2 with b
        simp [castAdd_ne_natAdd j b]
      · exact isMH_zero _
    | succ i =>
      rw [hImg_succ, ← mul_assoc, mul_comm _ (C (X (i, j))), coeff_C_mul, coeff_mul_X']
      split_ifs with h
      · rw [mul_comm]
        have := isMH_mul_X (hp (γ - Finsupp.single (Fin.natAdd (N + 1) i) 1)) i j
        convert this using 1
        funext b
        have hpos : 1 ≤ γ (Fin.natAdd (N + 1) i) := by
          rw [Finsupp.mem_support_iff] at h; omega
        by_cases hb : b = i
        · subst hb; simp [Finsupp.single_apply]; omega
        · simp [Finsupp.single_apply, Pi.single_apply, hb, Ne.symm hb]
      · rw [mul_zero]; exact isMH_zero _

noncomputable def psi (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ) :
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →+* MvPolynomial (Fin (N + 1 + D)) ℂ :=
  (MvPolynomial.map (eval₂Hom sg tt)).comp (homog (K := K)).toRingHom

noncomputable def gpt (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) :
    Fin (D + 1) × Fin (N + 1) → ℂ :=
  fun p => Fin.cases (motive := fun _ => Fin (N + 1) → ℂ) (fun j => y (Fin.castAdd D j))
    (fun i j => y (Fin.natAdd (N + 1) i) * tt (i, j)) p.1 p.2

@[simp] theorem gpt_zero (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) (j : Fin (N + 1)) :
    gpt tt y (0, j) = y (Fin.castAdd D j) := by simp [gpt]

@[simp] theorem gpt_succ (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) (i : Fin D)
    (j : Fin (N + 1)) : gpt tt y (i.succ, j) = y (Fin.natAdd (N + 1) i) * tt (i, j) := by simp [gpt]

theorem eval_psi (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ)
    (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    eval y (psi sg tt q) = eval₂ sg (gpt tt y) q := by
  have : (eval y).comp (psi sg tt) = eval₂Hom sg (gpt tt y) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [psi, homog, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, j⟩
      cases i using Fin.cases with
      | zero => simp [psi, homog]
      | succ i => simp [psi, homog]
  exact congrArg (fun f => f q) this

theorem psi_injective (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ)
    (hG : ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg tt p ≠ 0) :
    Function.Injective (psi sg tt) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro q hq
  apply homog_injective (K := K) (D := D) (N := N)
  rw [map_zero]
  refine MvPolynomial.ext _ _ fun γ => ?_
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hne
  have h0 : AddMonoidAlgebra.coeff (psi sg tt q) γ = 0 := by rw [hq]; simp
  rw [psi, RingHom.comp_apply, coeff_map] at h0
  exact hG _ _ (homog_coeff_isMH q γ) hne (by simpa using h0)

theorem ae_gen (sg : K →+* ℂ) [Countable K] :
    ∀ᵐ z ∂(blockSphereProb D (N + 1)), ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg (blockPoint z) p ≠ 0 := by
  have := countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)
  rw [ae_all_iff]; intro a
  rw [ae_all_iff]; intro p
  by_cases hp : IsMultiHomogeneous a p ∧ p ≠ 0
  · have hm : IsMultiHomogeneous a (MvPolynomial.map sg p) :=
      fun s hs => hp.1 s (support_map_subset _ _ hs)
    have hm0 : MvPolynomial.map sg p ≠ 0 := fun h0 =>
      hp.2 (map_injective sg sg.injective (by rw [h0, map_zero]))
    filter_upwards [ae_blockSphere_eval_ne_zero D (N + 1) a _ hm0 hm] with z hz _ _
    rwa [eval_map] at hz
  · exact Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp

theorem exists_gen (sg : K →+* ℂ) [Countable K] (tt : Fin D × Fin (N + 1) → ℂ)
    (hG : ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg tt p ≠ 0)
    (Q : MvPolynomial (Fin (N + 1 + D)) ℂ) (hQ : Q ≠ 0) :
    ∃ y : Fin (N + 1 + D) → ℂ, eval y Q ≠ 0 ∧
      ∀ q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, q ≠ 0 → eval₂ sg (gpt tt y) q ≠ 0 := by
  have := countable_mvPoly (σ := Fin (D + 1) × Fin (N + 1)) (R := K)
  have h1 := ae_eval_ne_zero_of_ne_zero_fin _ Q hQ
  have h2 : ∀ᵐ y ∂(volume : Measure (Fin (N + 1 + D) → ℂ)),
      ∀ q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, q ≠ 0 → eval y (psi sg tt q) ≠ 0 := by
    rw [ae_all_iff]; intro q
    by_cases hq : q = 0
    · exact Filter.Eventually.of_forall fun y h => absurd hq h
    · have hq' : psi sg tt q ≠ 0 := fun h0 => hq (psi_injective sg tt hG (by rw [h0, map_zero]))
      filter_upwards [ae_eval_ne_zero_of_ne_zero_fin _ _ hq'] with y hy _ using hy
  have : (ae (volume : Measure (Fin (N + 1 + D) → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  exact ⟨y, hy1, fun q hq => by rw [← eval_psi]; exact hy2 q hq⟩

end ReciprocityTheory.ChartRestriction.G.T0.NPB
end

