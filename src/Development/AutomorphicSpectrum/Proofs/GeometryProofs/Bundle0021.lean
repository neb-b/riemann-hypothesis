module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ValAtRestrict

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicElementHomogRelation
section
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AlgPoly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem form_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem form_one : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h0
  · subst h0
    simp
  · exact absurd rfl hm

theorem form_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem form_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem form_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm

theorem form_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  exact form_add hf (form_neg hg)

theorem form_sum {σ : Type*} (s : Finset σ) (f : σ → MRing ι) {a : K → ℕ}
    (hf : ∀ x ∈ s, IsMultiHomog (f x) a) : IsMultiHomog (∑ x ∈ s, f x) a := by
  exact Finset.sum_induction f (fun p => IsMultiHomog p a) (fun _ _ h1 h2 => form_add h1 h2)
    (form_zero a) hf

theorem form_natCast_mul {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f * (n : MRing ι)) a := by
  induction n with
  | zero => simpa using form_zero a
  | succ n ih =>
    rw [Nat.cast_succ, mul_add, mul_one]
    exact form_add ih hf

theorem cone_form (y : (Σ k, ι k) → Ω) {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) :
    mConeMap y h = MvPolynomial.C (aeval y h) * ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
  classical
  have key : ∀ v ∈ h.support, mConeMap y (monomial v (AddMonoidAlgebra.coeff h v)) =
      MvPolynomial.C (aeval y (monomial v (AddMonoidAlgebra.coeff h v))) * ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
    intro v hv
    have hX : (v.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e) = ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]
      exact Finset.prod_congr rfl fun k _ => by simp only [Finset.prod_pow_eq_pow_sum, hh v hv k]
    have h1 : (v.prod fun p e => (MvPolynomial.C (y p) * X p.1 : MvPolynomial K Ω) ^ e) =
        MvPolynomial.C (v.prod fun p e => y p ^ e) * v.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e := by
      rw [map_finsuppProd, ← Finsupp.prod_mul]
      exact Finsupp.prod_congr fun p _ => by simp only [mul_pow, map_pow]
    show (aeval fun p => MvPolynomial.C (y p) * (X p.1 : MvPolynomial K Ω)) (monomial v (AddMonoidAlgebra.coeff h v)) = _
    simp only [MvPolynomial.aeval_monomial]
    rw [h1, hX, map_mul]
    simp only [algebraMap_int_eq, eq_intCast, Int.coe_castRingHom, map_intCast]
    ring
  rw [h.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl key

theorem mem_of_aeval_eq_zero {y : (Σ k, ι k) → Ω} {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d)
    (h0 : aeval y h = 0) : h ∈ mCoordIdeal y := by
  show h ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, cone_form y hh, h0, map_zero, zero_mul]

theorem notMem_of_aeval_ne_zero {y : (Σ k, ι k) → Ω} {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d)
    (h0 : aeval y h ≠ 0) : h ∉ mCoordIdeal y := by
  intro hmem
  change h ∈ RingHom.ker (mConeMap y) at hmem
  rw [RingHom.mem_ker, cone_form y hh] at hmem
  rcases mul_eq_zero.1 hmem with h1 | h1
  · exact h0 (MvPolynomial.C_eq_zero.1 h1)
  · exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h1

theorem common_denominator {y : (Σ k, ι k) → Ω} (hy : Birational y) (s : Finset Ω) :
    ∃ (b : K → ℕ) (H : MRing ι), IsMultiHomog H b ∧ aeval y H ≠ 0 ∧
      ∀ x ∈ s, ∃ g : MRing ι, IsMultiHomog g b ∧ aeval y g = x * aeval y H := by
  classical
  refine Finset.induction_on s ⟨0, 1, form_one, by simp, fun x hx => by simp at hx⟩ ?_
  intro x s _ ih
  obtain ⟨b, H, hH, hH0, hg⟩ := ih
  obtain ⟨d, g, h, hgd, hhd, hh0, hgh⟩ := hy x
  refine ⟨b + d, H * h, form_mul hH hhd, by rw [map_mul]; exact mul_ne_zero hH0 hh0, fun z hz => ?_⟩
  rcases Finset.mem_insert.1 hz with rfl | hz
  · exact ⟨H * g, form_mul hH hgd, by rw [map_mul, map_mul, hgh]; ring⟩
  · obtain ⟨g', hg', hg'e⟩ := hg z hz
    exact ⟨g' * h, form_mul hg' hhd, by rw [map_mul, map_mul, hg'e]; ring⟩

theorem lift_poly {y : (Σ k, ι k) → Ω} {b : K → ℕ} {H : MRing ι} (P : Polynomial Ω)
    (hP : ∀ j, j ∈ P.support → ∃ g : MRing ι, IsMultiHomog g b ∧ aeval y g = P.coeff j * aeval y H) :
    ∃ L : Polynomial (MRing ι), (∀ j, IsMultiHomog (L.coeff j) b) ∧
      L.map (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom = Polynomial.C (aeval y H) * P := by
  classical
  choose! g hg using hP
  refine ⟨∑ j ∈ P.support, Polynomial.monomial j (g j), fun j => ?_, ?_⟩
  · rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq']
    split_ifs with hj
    · exact (hg j hj).1
    · exact form_zero b
  · ext n
    simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply,
      Finset.sum_ite_eq', Polynomial.coeff_C_mul]
    split_ifs with hn
    · exact ((hg n hn).2).trans (mul_comm _ _)
    · have hc : P.coeff n = 0 := by simpa using hn
      rw [map_zero, hc, mul_zero]

theorem sum_derivative (q : Polynomial ℂ) (n : ℕ) (hn : q.natDegree ≤ n) (τ : ℂ) :
    ∑ j ∈ Finset.range (n + 1), (j : ℂ) * q.coeff j * τ ^ (j - 1) = (Polynomial.derivative q).eval τ := by
  rw [Polynomial.derivative_eval, Polynomial.sum_over_range' _ (fun _ => by simp) (n + 1) (Nat.lt_succ_of_le hn)]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sum_eval (q : Polynomial ℂ) (n : ℕ) (hn : q.natDegree ≤ n) (τ : ℂ) :
    ∑ j ∈ Finset.range (n + 1), q.coeff j * τ ^ j = q.eval τ := by
  exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hn) τ).symm

def evalAt (w : (Σ k, ι k) → ℂ) : MRing ι →+* ℂ :=
  (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ))

theorem evalAt_apply (w : (Σ k, ι k) → ℂ) (f : MRing ι) :
    evalAt w f = eval w (map (Int.castRingHom ℂ) f) := rfl

theorem core {Ω' : Type} [Field Ω'] {y : (Σ k, ι k) → Ω} (hy : Birational y) (i : Ω →+* Ω') (α : Ω')
    (m : Polynomial Ω) (hsep : IsCoprime m (Polynomial.derivative m)) (hroot : Polynomial.eval₂ i α m = 0) :
    ∃ (n : ℕ) (c : ℕ → MRing ι) (a : K → ℕ) (G : MRing ι) (b : K → ℕ),
      (∀ j, IsMultiHomog (c j) a) ∧ IsMultiHomog G b ∧ G ∉ mCoordIdeal y ∧
      (∑ j ∈ Finset.range (n + 1), i (aeval y (c j)) * α ^ j = 0) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), eval w (map (Int.castRingHom ℂ) G) ≠ 0 → ∀ τ : ℂ,
        ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ j = 0 →
        ∑ j ∈ Finset.range (n + 1), (j : ℂ) * eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ (j - 1) ≠ 0 := by
  classical
  obtain ⟨u, v, huv⟩ := hsep
  obtain ⟨b, H, hH, hH0, hg⟩ := common_denominator hy
    (m.support.image m.coeff ∪ u.support.image u.coeff ∪ v.support.image v.coeff)
  obtain ⟨M, hMh, hMm⟩ := lift_poly (y := y) (H := H) m (fun j hj => hg _
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj))))
  obtain ⟨U, hUh, hUm⟩ := lift_poly (y := y) (H := H) u (fun j hj => hg _
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))))
  obtain ⟨V, hVh, hVm⟩ := lift_poly (y := y) (H := H) v (fun j hj => hg _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)))
  have hDh : ∀ j, IsMultiHomog ((Polynomial.derivative M).coeff j) b := fun j => by
    rw [Polynomial.coeff_derivative]
    exact_mod_cast form_natCast_mul (hMh (j + 1)) (j + 1)
  have hEh : ∀ j, IsMultiHomog ((U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).coeff j)
      (b + b) := by
    intro j
    rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul,
      Polynomial.coeff_C]
    refine form_sub (form_add (form_sum _ _ fun x _ => form_mul (hUh _) (hMh _))
      (form_sum _ _ fun x _ => form_mul (hVh _) (hDh _))) ?_
    split_ifs
    · exact form_mul hH hH
    · exact form_zero _
  have hEm : (U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).map
      (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, Polynomial.map_C, hUm, hVm, hMm, Polynomial.derivative_C_mul]
    simp only [map_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    linear_combination (Polynomial.C (aeval y H) * Polynomial.C (aeval y H)) * huv
  have hEmem : ∀ j, (U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).coeff j ∈
      mCoordIdeal y := by
    intro j
    refine mem_of_aeval_eq_zero (hEh j) ?_
    have h2 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j) hEm
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
    exact h2
  refine ⟨M.natDegree, fun j => M.coeff j, b, H, b, hMh, hH, notMem_of_aeval_ne_zero hH hH0, ?_, ?_⟩
  · have hdeg : (M.map (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom).natDegree < M.natDegree + 1 :=
      Nat.lt_succ_of_le Polynomial.natDegree_map_le
    have h1 := Polynomial.eval₂_eq_sum_range' i hdeg α
    simp only [Polynomial.coeff_map] at h1
    rw [hMm, Polynomial.eval₂_mul, Polynomial.eval₂_C, hroot, mul_zero] at h1
    exact h1.symm
  · intro w hw hG τ hτ hder
    have key : ∀ j, eval w (map (Int.castRingHom ℂ)
        ((U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).coeff j)) = 0 :=
      fun j => hw.2 _ (hEmem j)
    have hE0 : (U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).map (evalAt w) = 0 := by
      ext j
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, evalAt_apply]
      exact key j
    rw [Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, Polynomial.map_C] at hE0
    have hMe : (M.map (evalAt w)).eval τ = 0 := by
      rw [← sum_eval (M.map (evalAt w)) M.natDegree Polynomial.natDegree_map_le τ]
      simpa only [Polynomial.coeff_map, evalAt_apply] using hτ
    have hDe : (Polynomial.derivative (M.map (evalAt w))).eval τ = 0 := by
      rw [← sum_derivative (M.map (evalAt w)) M.natDegree Polynomial.natDegree_map_le τ]
      simpa only [Polynomial.coeff_map, evalAt_apply] using hder
    have h3 := congrArg (Polynomial.eval τ) hE0
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hMe,
      hDe, mul_zero, add_zero, zero_sub, Polynomial.eval_zero, neg_eq_zero, map_mul] at h3
    have hGH : evalAt w H ≠ 0 := by
      rw [evalAt_apply]
      exact hG
    exact hGH (mul_self_eq_zero.1 h3)

theorem algebraic_form_poly : ∀ (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (Ω₀ Ω : Type)
    [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (i : Ω₀ →+* Ω) (α : Ω), Birational y₀ →
    (letI := i.toAlgebra; IsAlgebraic Ω₀ α) →
    ∃ (n : ℕ) (c : ℕ → MRing J₀) (a : K₀ → ℕ) (G : MRing J₀) (b : K₀ → ℕ),
      (∀ j, IsMultiHomog (c j) a) ∧ IsMultiHomog G b ∧ G ∉ mCoordIdeal y₀ ∧
      (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * α ^ j = 0) ∧
      ∀ w ∈ mcPts (mCoordIdeal y₀), eval w (map (Int.castRingHom ℂ) G) ≠ 0 → ∀ τ : ℂ,
        ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ j = 0 →
        ∑ j ∈ Finset.range (n + 1), (j : ℂ) * eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ (j - 1) ≠ 0 := by
  intro K₀ _ J₀ _ Ω₀ Ω _ _ _ y₀ i α hy hα
  letI := i.toAlgebra
  haveI : CharZero Ω₀ := RingHom.charZero i
  have hα' : IsAlgebraic Ω₀ α := hα
  have hint : IsIntegral Ω₀ α := hα'.isIntegral
  have hsep : (minpoly Ω₀ α).Separable := (minpoly.irreducible hint).separable
  have hroot : Polynomial.eval₂ i α (minpoly Ω₀ α) = 0 := by
    have h := minpoly.aeval Ω₀ α
    rwa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] at h
  exact core hy i α (minpoly Ω₀ α) hsep hroot

end GlobalTheory.CompanionTheory.Ar.AlgPoly
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHomStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_comap_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (T' : Type) [CommGroup T'] [Finite T'] (Γ' : QFGroup R T') (a : Γ.G ⟶ Γ'.G) (α : T →* T'), (∀ t, Γ.pt t ≫ a = Γ'.pt (α t)) → ∀ f ∈ Γ'.btOrder ⊤, (fun t => f (α t)) ∈ Γ.btOrder ⊤ := by
  intro R _ _ T _ _ Γ T' _ _ Γ' a α ha f hf
  let Φ : (T' → R) →ₐ[R] (T → R) :=
    { toFun := fun f t => f (α t)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hle : Γ'.btOrder ⊤ ≤ (Γ.btOrder ⊤).comap Φ := by
    refine Algebra.adjoin_le fun f hf => ?_
    refine Algebra.subset_adjoin fun t g _ => ?_
    obtain ⟨U, hU, s, hs⟩ := hf (α t) (a.left g) trivial
    refine ⟨a.left ⁻¹ᵁ U, hU, (a.left.app U).hom s, fun x h => ?_⟩
    have hx : (Γ.pt x).left ≫ a.left = (Γ'.pt (α x)).left := by
      rw [← ha x, Over.comp_left]
    have h' : ⊤ ≤ (Γ'.pt (α x)).left ⁻¹ᵁ U := by
      rw [← hx]
      exact h
    have hval : valAt (Γ.pt x).left (a.left ⁻¹ᵁ U) h ((a.left.app U).hom s) =
        valAt (Γ'.pt (α x)).left U h' s := by
      simp only [valAt, ← hx, Scheme.Hom.comp_appLE]
      rfl
    change valAt (Γ.pt x).left (a.left ⁻¹ᵁ U) h ((a.left.app U).hom s) =
      algebraMap R (FractionRing R) (f (α (t * x)))
    rw [hval, map_mul]
    exact hs (α x) h'
  exact hle hf
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeNormMembership
section
open ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.ChartVal

theorem isIntegral_of_forall_valuationSubring {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (hf : Function.Injective (algebraMap R Ω)) (a : Ω)
    (H : ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap R Ω r ∈ V) → a ∈ V) : IsIntegral R a := by
  classical
  by_contra hna
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hna isIntegral_zero
  set B : Subring Ω := (Algebra.adjoin R {a⁻¹}).toSubring with hB
  have hbA : a⁻¹ ∈ B := Algebra.subset_adjoin rfl
  have hnu : ¬ IsUnit (⟨a⁻¹, hbA⟩ : B) := by
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : a⁻¹ * (w : Ω) = 1 := congrArg Subtype.val hw
    have hwa : (w : Ω) = a := by
      calc (w : Ω) = a * (a⁻¹ * w) := by rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
        _ = a := by rw [h1, mul_one]
    have haA : a ∈ Algebra.adjoin R {a⁻¹} := by
      have hw2 := w.2
      rw [hwa] at hw2
      exact hw2
    apply hna
    rw [Algebra.adjoin_singleton_eq_range_aeval] at haA
    obtain ⟨p, hp⟩ := (AlgHom.mem_range _).mp haA
    rw [Polynomial.aeval_def] at hp
    letI : Invertible a⁻¹ := invertibleOfNonzero (inv_ne_zero ha0)
    have key := Polynomial.eval₂_reverse_mul_pow (algebraMap R Ω) a⁻¹ p
    rw [invOf_eq_inv, inv_inv, hp] at key
    have hdeg : p.reverse.degree < ↑(p.natDegree + 1) := by
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      exact_mod_cast Nat.lt_succ_of_le (Polynomial.reverse_natDegree_le p)
    refine (show ∃ q : Polynomial R, q.Monic ∧ Polynomial.eval₂ (algebraMap R Ω) a q = 0 from
      ⟨Polynomial.X ^ (p.natDegree + 1) - p.reverse, Polynomial.monic_X_pow_sub hdeg, ?_⟩)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, sub_eq_zero]
    calc a ^ (p.natDegree + 1) = a * a ^ p.natDegree := pow_succ' a _
      _ = Polynomial.eval₂ (algebraMap R Ω) a p.reverse * a⁻¹ ^ p.natDegree * a ^ p.natDegree := by
          rw [key]
      _ = Polynomial.eval₂ (algebraMap R Ω) a p.reverse := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ ha0, one_pow, mul_one]
  obtain ⟨P, hP, hxP⟩ := Ideal.exists_le_maximal (Ideal.span {(⟨a⁻¹, hbA⟩ : B)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact hnu)
  haveI := hP.isPrime
  have hx : (⟨a⁻¹, hbA⟩ : B) ∈ P := hxP (Ideal.mem_span_singleton_self _)
  have hg : ∀ y : P.primeCompl, IsUnit (B.subtype (y : B)) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h => (show (y : B) ∉ P from y.2) ?_
    have hy0 : (y : B) = 0 := Subtype.ext h
    rw [hy0]
    exact P.zero_mem
  let f := IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hg
  have hfl : ∀ z : B, f (algebraMap B (Localization.AtPrime P) z) = z := fun z =>
    IsLocalization.lift_eq hg z
  have hfinj : Function.Injective f := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have h' := congrArg f h
      rw [hfl, hfl] at h'
      exact h'
    · intro h
      have hxy : x = y := Subtype.ext h
      rw [hxy]
  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range f)
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV
  have hmemL : ∀ z : B, (z : Ω) ∈ (LocalSubring.range f).toSubring := by
    intro z
    first
      | exact (show (z : Ω) ∈ Set.range f from ⟨_, hfl z⟩)
      | (rw [LocalSubring.range_toSubring]; exact ⟨_, hfl z⟩)
  have haV : a ∈ V := H V fun r => hle (hmemL ⟨algebraMap R Ω r, Subalgebra.algebraMap_mem _ r⟩)
  let xL : (LocalSubring.range f).toSubring := ⟨a⁻¹, hmemL ⟨a⁻¹, hbA⟩⟩
  have hunitV : IsUnit (Subring.inclusion hle xL) :=
    isUnit_iff_exists_inv.mpr ⟨⟨a, haV⟩, Subtype.ext (inv_mul_cancel₀ ha0)⟩
  have hunitL : IsUnit xL := by
    first
      | exact isUnit_of_map_unit (Subring.inclusion hle) xL hunitV
      | exact IsUnit.of_map (Subring.inclusion hle) xL hunitV
  obtain ⟨w, hw⟩ := hunitL.exists_right_inv
  have hw2 : (w : Ω) ∈ Set.range f := w.2
  obtain ⟨s, hs⟩ := hw2
  have h1 : f (algebraMap B (Localization.AtPrime P) ⟨a⁻¹, hbA⟩ * s) = f 1 := by
    rw [map_mul, hfl, hs, map_one]
    exact congrArg Subtype.val hw
  have hu : IsUnit (algebraMap B (Localization.AtPrime P) ⟨a⁻¹, hbA⟩) :=
    isUnit_iff_exists_inv.mpr ⟨s, hfinj h1⟩
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P] at hu
  exact hu hx

theorem mem_chartLatNm_of_forall_valuationSubring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (q : ℕ) (x : Ω),
    (∀ (c : (k : K) → ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ W : ValuationSubring Ω,
      (∀ p, y p / y ⟨p.1, c p.1⟩ ∈ W) → x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q ∈ W) →
    x * u ^ q ∈ chartLatNm y a q := by
  intro K _ ι _ Ω _ y a u q x H c hc
  have e : x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) =
      x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q := by
    rw [mul_pow, ← Finset.prod_pow, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  show x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) ∈ integralClosure (chartRingZ y c) Ω
  rw [e, mem_integralClosure_iff]
  refine isIntegral_of_forall_valuationSubring Subtype.val_injective _ fun V hV => H c hc V fun p => ?_
  exact hV ⟨_, Algebra.subset_adjoin ⟨p, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.ChartVal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenComponentMapCompatStatement
section
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_component_map_compat : ∀ (k k' V V' O : Type) [Field k] [Field k'] [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k' V'] [CommRing O] (κ : k →+* k') (j : V →+ V'), (∀ (c : k) x, j (c • x) = κ c • j x) → ∀ (ρ : O →+* Module.End k V) (ρ' : O →+* Module.End k' V'), (∀ a x, ρ' a (j x) = j (ρ a x)) → ∀ (σ : O →+* k) (x : V), eigComp ρ σ x ≠ 0 → eigComp ρ' (κ.comp σ) (j x) = j (eigComp ρ σ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigMap.eigComp_map | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigMap.eigComp_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigMap.eigComp_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReversedDualBasis
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.DualRev

theorem dotDualRevBasis (Ω : Type) [Field Ω] (r : ℕ) (w : Module.Basis (Fin r) Ω (Fin r → Ω)) :
    ∃ v : Module.Basis (Fin r) Ω (Fin r → Ω), ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
  classical
  set v : Fin r → Fin r → Ω := fun j t => w.dualBasis (Fin.rev j) (fun s => if t = s then 1 else 0) with hv
  have key : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
    intro i j
    have h1 : w i ⬝ᵥ v j = w.dualBasis (Fin.rev j) (w i) := by
      rw [LinearMap.pi_apply_eq_sum_univ (w.dualBasis (Fin.rev j)) (w i)]
      simp [dotProduct, hv, smul_eq_mul]
    rw [h1, Module.Basis.dualBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hli : LinearIndependent Ω v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j0
    have := congrArg (fun x => w (Fin.rev j0) ⬝ᵥ x) hg
    simp only [dotProduct_sum, dotProduct_smul, key, smul_eq_mul, dotProduct_zero] at this
    simpa [Fin.rev_inj, eq_comm] using this
  have hcard : Fintype.card (Fin r) = Module.finrank Ω (Fin r → Ω) := by
    rw [Fintype.card_fin, Module.finrank_fin_fun]
  by_cases hr : r = 0
  · subst hr
    exact ⟨w, fun i => i.elim0⟩
  haveI : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
  intro i j
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact key i j

end GlobalTheory.CompanionTheory.Ar.DualRev
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_centre_local_hom : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (R : Type) [CommRing R] [IsLocalRing R] (φ : regAt ξ p →+* R), IsLocalHom φ → ∃! z : Spec (CommRingCat.of R) ⟶ X, centre z = p.1 ∧ ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local | exact GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_unique_point_of_local <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenLeClosedFibre
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isFinite_open_le_of_closedFibre_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' :=
  @PositivityTheory.HtPt.Unc.finite_le

end GlobalTheory.CompanionTheory.Ar.BT
end

