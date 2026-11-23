module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LinearIndependentAdjoinOfTranscendental
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace TranscRatioDeg

open Polynomial

theorem transcendental_subfieldClosure {E : Type*} [Field E] {ι : Type*} (u : ι → E) (t : E)
    (ht : Transcendental (Algebra.adjoin ℤ (Set.range u)) t) :
    Transcendental (Subfield.closure (Set.range u)) t := by
  have hR : ∀ x, x ∈ Algebra.adjoin ℤ (Set.range u) ↔ x ∈ Subring.closure (Set.range u) := fun x => by
    rw [Algebra.adjoin_int]; rfl
  set R := Algebra.adjoin ℤ (Set.range u)
  set Q := Subfield.closure (Set.range u)
  have hmem : ∀ x : R, (x : E) ∈ Q := fun x => Subfield.subring_closure_le _ ((hR x).1 x.2)
  let _ : Algebra R Q := RingHom.toAlgebra
    { toFun := fun x => ⟨x.1, hmem x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have : IsScalarTower R Q E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul R Q := (faithfulSMul_iff_algebraMap_injective R Q).2
    (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have : IsFractionRing R Q := IsFractionRing.of_field R Q (fun z => by
    obtain ⟨y, hy, z', hz', h⟩ := Subfield.mem_closure_iff.1 z.2
    exact ⟨⟨y, (hR y).2 hy⟩, ⟨z', (hR z').2 hz'⟩, Subtype.ext (by rw [Subfield.coe_div]; exact h.symm)⟩)
  intro halg
  exact ht ((IsFractionRing.isAlgebraic_iff R Q E).2 halg)

theorem transcendental_of_subfield {E : Type*} [Field E] {S : Type*} [CommRing S] [Algebra S E]
    (Q : Subfield E) (h : ∀ x : S, algebraMap S E x ∈ Q) (hinj : Function.Injective (algebraMap S E))
    {t : E} (ht : Transcendental Q t) : Transcendental S t := by
  rintro ⟨p, hp0, hp⟩
  let φ : S →+* Q := (algebraMap S E).codRestrict Q h
  have hφ : Function.Injective φ := fun a b hab => hinj (congrArg Subtype.val hab :)
  refine ht ⟨p.map φ, (Polynomial.map_ne_zero_iff hφ).2 hp0, ?_⟩
  rw [aeval_def, eval₂_map]
  exact hp


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem linearIndependent_adjoin_of_transcendental {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) {κ : Type*} {b : κ → A}
    (hb : LinearIndependent K b) :
    LinearIndependent (IntermediateField.adjoin K {t}) (A.val ∘ b) :=
  open scoped IntermediateField.algebraAdjoinAdjoin in by
  letI : Algebra (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K {t})).toAlgebra
  letI : FaithfulSMul (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
      Subtype.ext (by simpa using congrArg (fun x : IntermediateField.adjoin K {t} => (x : E)) h)
  letI : IsFractionRing (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) :=
    IsFractionRing.of_field _ _ fun ⟨_, h⟩ =>
      have ⟨x, hx, y, hy, eq⟩ := IntermediateField.mem_adjoin_iff_div.mp h
      ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext eq⟩
  letI : IsScalarTower (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine (LinearIndependent.iff_fractionRing (Algebra.adjoin K {t})
    (IntermediateField.adjoin K {t})).1 ?_
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hp : ∀ j, ∃ p : K[X], aeval t p = (g j : E) := fun j => by
    have h : (g j : E) ∈ (aeval t : K[X] →ₐ[K] E).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact (g j).2
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hp⟩
  choose p hp using hp
  have hsum : ∑ j ∈ s, aeval t (p j) * (b j : E) = 0 := by
    simpa [hp, Subalgebra.smul_def] using hg
  let P : A[X] := ∑ j ∈ s, C (b j) * (p j).map (algebraMap K A)
  have hP : aeval t P = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_sum, map_mul, aeval_C, aeval_map_algebraMap]
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  have hP0 : P = 0 := by
    by_contra hne
    exact ht ⟨P, hne, hP⟩
  have hcoeff : ∀ n, ∑ j ∈ s, (p j).coeff n • b j = 0 := by
    intro n
    have := congrArg (fun q => q.coeff n) hP0
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hpi : p i = 0 := by
    ext n
    exact linearIndependent_iff'.1 hb s (fun j => (p j).coeff n) (hcoeff n) i hi
  apply Subtype.ext
  rw [← hp i, hpi, map_zero]
  rfl

theorem finrank_adjoin_eq_of_transcendental {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) :
    Module.finrank (IntermediateField.adjoin K {t})
      (IntermediateField.adjoin (IntermediateField.adjoin K {t}) (A : Set E)) = Module.finrank K A := by
  set L := IntermediateField.adjoin K {t}
  let a := Module.Free.chooseBasis K A
  have hind : LinearIndependent L (A.val ∘ a) :=
    linearIndependent_adjoin_of_transcendental A ht a.linearIndependent
  by_cases hfin : Module.Finite K A
  · have H : A.LinearDisjoint L := IntermediateField.LinearDisjoint.of_basis_left a hind
    have hr := H.adjoin_rank_eq_rank_left_of_isAlgebraic_left
    exact congrArg Cardinal.toNat hr
  · rw [Module.finrank_of_not_finite hfin]
    set M := IntermediateField.adjoin L (A : Set E)
    letI : Module.Free L M := Module.Free.of_divisionRing L M
    refine Module.finrank_of_not_finite (M := M) ?_
    intro hfin'
    apply hfin
    let f : Module.Free.ChooseBasisIndex K A → M :=
      fun k => ⟨A.val (a k), IntermediateField.subset_adjoin L _ (a k).2⟩
    have hf : LinearIndependent L f := LinearIndependent.of_comp M.val.toLinearMap hind
    have : Finite (Module.Free.ChooseBasisIndex K A) := hf.finite
    exact Module.Finite.of_basis a

theorem finrank_adjoin_congr {E Φ L : Type*} [Field E] [Field Φ] [Field L] [Algebra Φ E] [Algebra L E]
    {S T : Set E} (h : (algebraMap Φ E).fieldRange = (algebraMap L E).fieldRange)
    (hST : Subfield.closure (Set.range (algebraMap Φ E) ∪ S) =
      Subfield.closure (Set.range (algebraMap L E) ∪ T)) :
    Module.finrank Φ (IntermediateField.adjoin Φ S) = Module.finrank L (IntermediateField.adjoin L T) := by
  let i : Φ ≃+* L := ((algebraMap Φ E).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr h)).trans
    (algebraMap L E).rangeRestrictFieldEquiv.symm
  have hi : ∀ r, algebraMap L E (i r) = algebraMap Φ E r := fun r => by
    simp only [i, RingEquiv.trans_apply, RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    rfl
  have hmem : ∀ x : E, x ∈ IntermediateField.adjoin Φ S ↔ x ∈ IntermediateField.adjoin L T := fun x => by
    rw [← IntermediateField.mem_toSubfield, ← IntermediateField.mem_toSubfield,
      IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, hST]
  let j : IntermediateField.adjoin Φ S ≃+ IntermediateField.adjoin L T :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩, invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  have hr := rank_eq_of_equiv_equiv i j i.bijective (fun r m => Subtype.ext (by
    simp only [j, AddEquiv.coe_mk, Equiv.coe_fn_mk, Algebra.smul_def]
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul]
    exact congrArg (· * (m : E)) (hi r).symm))
  exact congrArg Cardinal.toNat hr

end TranscRatioDeg

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartSup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set

noncomputable section

def ChartSupBound.Statement : Prop :=
  ∀ (D : ℕ) (V K : Set (Fin D → ℂ)) (ψ ν : (Fin D → ℂ) → ℝ), IsOpen V → IsCompact K → K ⊆ V →
    ContDiffOn ℝ 2 ψ V → ContinuousOn ν V → (∀ z ∈ V, 0 < ν z) →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ F : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ F V → ∀ w ∈ K,
      ENNReal.ofReal (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w)) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ D) *
          ∫⁻ z in V, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(n : ℝ) * ψ z) * ν z)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexMinimalPrimesContract
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def ComplexMinimalPrimesContract.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    ∀ Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
      Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsDescend
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

def ConstantsDescend.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (R T : Subalgebra ℤ Ω), R.FG → Module.Finite ℤ T →
    (∀ w w' : ↥(R ⊔ T) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom) →
    ∃ m : ℕ, 1 ≤ m ∧ ∀ t ∈ T, (m : Ω) * t ∈ R

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDoubleComplexVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

def DoubleComplexVanish.Statement : Prop :=
  ∀ (C : ℕ → ℕ → Type) [∀ p n, AddCommGroup (C p n)] (P : ∀ p n, AddSubgroup (C p n))
    (δ : ∀ p n, C p n →+ C p (n + 1)) (κ : ∀ p n, C (p + 1) n →+ C p n) (R : ℕ),
    (∀ p n, ∀ x ∈ P p n, δ p n x ∈ P p (n + 1)) →
    (∀ p n, ∀ x ∈ P (p + 1) n, κ p n x ∈ P p n) →
    (∀ p n, ∀ x ∈ P p n, δ p (n + 1) (δ p n x) = 0) →
    (∀ p n, ∀ x ∈ P (p + 1) n, δ p n (κ p n x) = κ p (n + 1) (δ (p + 1) n x)) →
    (∀ p n, ∀ x ∈ P (p + 2) n, κ p n (κ (p + 1) n x) = 0) →
    (∀ n, ∀ x ∈ P 0 n, ∃ y ∈ P 1 n, κ 0 n y = x) →
    (∀ p n, ∀ x ∈ P (p + 1) n, κ p n x = 0 → ∃ y ∈ P (p + 2) n, κ (p + 1) n y = x) →
    (∀ p n, R < p → ∀ x ∈ P p n, x = 0) →
    (∀ p, 1 ≤ p → p ≤ R → ∀ n, ∀ x ∈ P p (n + 1), δ p (n + 1) x = 0 → ∃ y ∈ P p n, δ p n y = x) →
    ∀ n, ∀ x ∈ P 0 (n + 1), δ 0 (n + 1) x = 0 → ∃ y ∈ P 0 n, δ 0 n y = x

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFiniteSeparatingModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def FiniteSeparatingModel.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)) (f : MvPolynomial σ ℚ) (x : σ → ℂ),
    P.IsPrime → f ∉ P → (∀ g ∈ P, aeval x g = 0) →
    ∃ (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ) (u : MvPolynomial σ ℚ)
      (G : Polynomial (MvPolynomial (Fin e) ℚ)) (c D : MvPolynomial (Fin e) ℚ),
      G.Monic ∧ c ≠ 0 ∧ D ≠ 0 ∧
      (∀ i : σ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ), p.Monic ∧
        ∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
          p.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (z i) = 0) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        G.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (aeval z u) = 0) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        aeval (fun j => aeval z (ℓ j)) c ≠ 0 → aeval z f ≠ 0) ∧
      (∀ (y : Fin e → ℂ) (t : ℂ), aeval y D ≠ 0 → G.eval₂ (aeval y).toRingHom t = 0 →
        ∃ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) ∧ (fun j => aeval z (ℓ j)) = y ∧ aeval z u = t) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        (fun j => aeval z (ℓ j)) = (fun j => aeval x (ℓ j)) → aeval z u = aeval x u → z = x)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIndependentModBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def IndependentModBaseChange.Statement : Prop :=
  ∀ (σ : Type) (P : Ideal (MvPolynomial σ ℤ)) (r : ℕ) (g : Fin r → MvPolynomial σ ℤ),
    LinearIndependent ℤ (fun i => Ideal.Quotient.mk P (g i)) →
    LinearIndependent ℂ (fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ)))
      (MvPolynomial.map (Int.castRingHom ℂ) (g i)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedTopAlgebra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

def MixedTopAlgebra.Statement : Prop :=
  ∀ (d : ℕ) (m : ℕ → ℝ), 2 ≤ d → (∀ i, 1 ≤ i → i ≤ d → 0 ≤ m i) → 0 < m d →
    (∀ q p : ℕ, 1 ≤ q → 1 ≤ p →
      0 < ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (q : ℝ) ^ (d - i) * (p : ℝ) ^ i * m i →
      0 ≤ ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * (q : ℝ) ^ (d - 1 - i) * (p : ℝ) ^ i * m i) →
    0 ≤ m 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNoetherProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def NoetherProjection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)), P ≠ ⊤ →
    ∃ (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ),
      (∀ q : MvPolynomial (Fin e) ℚ, aeval ℓ q ∈ P → q = 0) ∧
      ∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
        p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonnegAtZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter

def PolyNonnegAtZero.Statement : Prop :=
  ∀ (d : ℕ) (p : Polynomial ℝ) (c : ℝ), 0 < c →
    (∀ t : ℚ, 0 < t → 0 < p.eval (t : ℝ) → c * (t : ℝ) ^ d ≤ p.eval (t : ℝ)) →
    (∀ᶠ t in atTop, 0 < p.eval t) → 0 ≤ p.eval 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonvanishDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def PolyNonvanishDense.Statement : Prop :=
  ∀ (e : ℕ) (D : MvPolynomial (Fin e) ℚ), D ≠ 0 → Dense {y : Fin e → ℂ | aeval y D ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolySandwich
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def PolySandwich.Statement : Prop :=
  ∀ (D c : ℕ) (p q : Polynomial ℚ), q.natDegree ≤ D →
    (∀ᶠ n : ℕ in Filter.atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ) ∧ q.eval (n : ℚ) ≤ p.eval ((n : ℚ) + c)) →
    p.natDegree ≤ D ∧ p.coeff D = q.coeff D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

