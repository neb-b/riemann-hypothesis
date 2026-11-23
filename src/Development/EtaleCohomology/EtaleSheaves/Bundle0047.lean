module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0038
public import Development.EtaleCohomology.EtaleSheaves.LeafRepCut
public import Development.EtaleCohomology.EtaleSheaves.Bundle0039

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LIdemLiftPf
section
noncomputable section

namespace LateralTheory.E.LIdemLiftPf

open Polynomial

def IdemLiftFin (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def FactLift (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (g : A[X]), g.Monic → ∀ n m : ℕ, g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
    ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧
      P.map (Ideal.Quotient.mk I) = X ^ n ∧ Q.map (Ideal.Quotient.mk I) = (X - 1) ^ m

def LFact : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], FactLift A I

def LFinOfFact : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ →
  FactLift A I → IdemLiftFin A I

def LRed : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), IdemLiftFin A I →
  LateralTheory.E.LChartPf.IdemLiftInt A I

theorem idem_of_mul_eq_zero {B : Type} [CommRing B] (x y : B) (hxy : x * y = 0) (hu : IsUnit (x + y)) :
    IsIdempotentElem (x * hu.unit⁻¹) := by
  have hx : x * x = x * (x + y) := by rw [mul_add, hxy, add_zero]
  have h1 : (x + y) * (hu.unit⁻¹ : Bˣ) = 1 := hu.mul_val_inv
  unfold IsIdempotentElem
  calc x * ↑hu.unit⁻¹ * (x * ↑hu.unit⁻¹) = x * x * (↑hu.unit⁻¹ * ↑hu.unit⁻¹) := by ring
    _ = x * ((x + y) * ↑hu.unit⁻¹) * ↑hu.unit⁻¹ := by rw [hx]; ring
    _ = x * ↑hu.unit⁻¹ := by rw [h1, mul_one]

theorem lRed : LRed := by
  intro A _ I hfin B _ _ _ ε hε
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ε
  have hb : b * b - b ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]
  rw [Ideal.map, Submodule.mem_span_set'] at hb
  obtain ⟨n, f, g, hfg⟩ := hb
  choose a ha hag using fun i => (g i).2
  let C : Subalgebra A B := Algebra.adjoin A (insert b (Set.range f))
  have hC : Module.Finite A C := by
    have := Algebra.finite_adjoin_of_finite_of_isIntegral (R := A) (s := insert b (Set.range f))
      ((Set.finite_range f).insert b) (fun x _ => Algebra.IsIntegral.isIntegral x)
    exact this
  have hbC : b ∈ C := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hfC : ∀ i, f i ∈ C := fun i => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  let bC : C := ⟨b, hbC⟩
  have hmem : bC * bC - bC ∈ I.map (algebraMap A C) := by
    have : bC * bC - bC = ∑ i, (⟨f i, hfC i⟩ : C) * algebraMap A C (a i) := by
      apply Subtype.ext
      simp only [bC, Subalgebra.coe_sub, Subalgebra.coe_mul, ← hfg, smul_eq_mul]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hag i]
    rw [this]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))
  have hidC : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A C)) bC) := by
    unfold IsIdempotentElem
    rw [← map_mul, Ideal.Quotient.eq]; exact hmem
  obtain ⟨e, he, hee⟩ := hfin C _ hidC
  refine ⟨(e : B), ?_, ?_⟩
  · unfold IsIdempotentElem; exact congrArg Subtype.val he.eq
  · rw [Ideal.Quotient.eq] at hee ⊢
    have := Ideal.mem_map_of_mem (C.val : C →ₐ[A] B).toRingHom hee
    rw [Ideal.map_map] at this
    simpa [bC] using this

theorem exists_monic_of_idem_mod {A : Type} [CommRing A] (I : Ideal A) (B : Type) [CommRing B] [Algebra A B]
    [Module.Finite A B] (b : B) (hb : b * b - b ∈ I.map (algebraMap A B)) :
    ∃ (g : A[X]) (d : ℕ), g.Monic ∧ aeval b g = 0 ∧
      g.map (Ideal.Quotient.mk I) = X ^ (d + 1) * (X - 1) ^ (d + 1) := by
  let φ : Module.End A B := LinearMap.mulLeft A (b * b - b)
  have hφ : LinearMap.range φ ≤ I • (⊤ : Submodule A B) := by
    rintro _ ⟨y, rfl⟩
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right _ _ hb
  obtain ⟨p, hpm, -, hpc, hpφ⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A φ I hφ
  have hp0 : aeval (b * b - b) p = 0 := by
    have hφ' : φ = Algebra.lmul A B (b * b - b) := rfl
    rw [hφ', Polynomial.aeval_algHom_apply] at hpφ
    simpa using congrArg (fun ψ : Module.End A B => ψ 1) hpφ
  have hpmap : p.map (Ideal.Quotient.mk I) = X ^ p.natDegree := by
    ext k
    rw [coeff_map, coeff_X_pow]
    split_ifs with hk
    · subst hk; rw [hpm.coeff_natDegree, map_one]
    · rcases lt_or_gt_of_ne hk with h | h
      · rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_le_self (by omega) (hpc k)
      · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
  rcases subsingleton_or_nontrivial A with hA | hA
  · have h10 : (1 : B) = 0 := by rw [← map_one (algebraMap A B), Subsingleton.elim (1 : A) 0, map_zero]
    have : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
    have h10' : (1 : A ⧸ I) = 0 := by rw [← map_one (Ideal.Quotient.mk I), Subsingleton.elim (1 : A) 0, map_zero]
    have : Subsingleton (A ⧸ I) := subsingleton_of_zero_eq_one h10'.symm
    exact ⟨p, 0, hpm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hqm : (X * X - X : A[X]).Monic := by
    rw [show (X * X - X : A[X]) = X ^ 2 - X by ring]
    exact monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by norm_num : 1 < 2))
  have hq : (X * X - X : A[X]).natDegree = 2 := by
    rw [show (X * X - X : A[X]) = X ^ 2 - X by ring]
    compute_degree!
  refine ⟨p.comp (X * X - X) * (X * X - X), p.natDegree, (hpm.comp hqm (by omega)).mul hqm, ?_, ?_⟩
  · rw [map_mul, aeval_comp]; simp [hp0]
  · simp only [Polynomial.map_mul, map_comp, hpmap, X_pow_comp, Polynomial.map_sub, map_X]
    rw [show (X * X - X : (A ⧸ I)[X]) = X * (X - 1) by ring, mul_pow]
    ring

theorem aeval_sub_mem_of_map_eq {A : Type} [CommRing A] (I : Ideal A) {B : Type} [CommRing B] [Algebra A B]
    (f f' : A[X]) (h : f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I)) (b : B) :
    aeval b f - aeval b f' ∈ I.map (algebraMap A B) := by
  have h1 : f - f' ∈ Ideal.map (C : A →+* A[X]) I := by
    rw [← Ideal.mk_ker (I := I), ← Polynomial.ker_mapRingHom, RingHom.mem_ker, map_sub]
    simp only [coe_mapRingHom, h, sub_self]
  have h2 := Ideal.mem_map_of_mem (aeval b).toRingHom h1
  rw [Ideal.map_map] at h2
  have h3 : (aeval b).toRingHom.comp (C : A →+* A[X]) = algebraMap A B := by ext; simp
  rw [h3] at h2
  simpa using h2

theorem isUnit_one_add_of_finite {A : Type} [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    {B : Type} [CommRing B] [Algebra A B] [Module.Finite A B] (s : B)
    (hs : s - 1 ∈ I.map (algebraMap A B)) : IsUnit s := by
  have key : (⊤ : Submodule A B) ≤ (Ideal.span {s}).restrictScalars A := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI ?_
    intro y _
    have hy : y = s * y - (s - 1) * y := by ring
    rw [hy]
    refine Submodule.sub_mem_sup (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) ?_
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right _ _ hs
  have h1 : (1 : B) ∈ Ideal.span {s} := key Submodule.mem_top
  rw [Ideal.mem_span_singleton] at h1
  exact isUnit_of_dvd_one h1

theorem lFinOfFact : LFinOfFact := by
  intro A _ I hI hF B _ _ _ ε hε
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ε
  set π := Ideal.Quotient.mk (I.map (algebraMap A B))
  have hb : b * b - b ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]
  obtain ⟨g, d, hgm, hgb, hgmap⟩ := exists_monic_of_idem_mod I B b hb
  obtain ⟨P, Q, -, -, hPQ, hP, hQ⟩ := hF g hgm _ _ hgmap
  have hcop : IsCoprime (X ^ (d + 1) : (A ⧸ I)[X]) ((X - 1) ^ (d + 1)) :=
    (show IsCoprime (X : (A ⧸ I)[X]) (X - 1) from ⟨1, -1, by ring⟩).pow
  obtain ⟨u0, v0, huv0⟩ := hcop
  obtain ⟨u, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective u0
  obtain ⟨v, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective v0
  have hπ : ∀ f f' : A[X], f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I) →
      π (aeval b f) = π (aeval b f') := fun f f' h =>
    Ideal.Quotient.eq.2 (aeval_sub_mem_of_map_eq I f f' h b)
  have hPb : π (aeval b P) = π b ^ (d + 1) := by
    rw [hπ P (X ^ (d + 1)) (by rw [hP]; simp)]; simp
  have hQb : π (aeval b Q) = (π b - 1) ^ (d + 1) := by
    rw [hπ Q ((X - 1) ^ (d + 1)) (by rw [hQ]; simp)]; simp
  have hUb : π (aeval b (u * P)) + π (aeval b (v * Q)) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _), hπ (u * P + v * Q) 1 (by simp [Polynomial.map_add (f := _), Polynomial.map_mul, hP, hQ, huv0])]
    simp
  set x := aeval b (u * P)
  set y := aeval b (v * Q)
  have hxy : x * y = 0 := by
    simp only [x, y, ← map_mul]
    rw [show u * P * (v * Q) = u * v * g by rw [hPQ]; ring, map_mul, hgb, mul_zero]
  have hs : (x + y) - 1 ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), hUb, map_one, sub_self]
  have hu := isUnit_one_add_of_finite I hI (x + y) hs
  refine ⟨x * hu.unit⁻¹, idem_of_mul_eq_zero x y hxy hu, ?_⟩
  have hinv : π (hu.unit⁻¹ : Bˣ) = 1 := by
    have h1 : π (x + y) * π (hu.unit⁻¹ : Bˣ) = 1 := by rw [← map_mul, hu.mul_val_inv, map_one]
    rwa [map_add, hUb, one_mul] at h1
  have he : π b * π b = π b := hε.eq
  have hx : π x = π b := by
    have e1 : π x * (1 - π b) = 0 := by
      simp only [x, map_mul, hPb]
      rw [pow_succ, mul_assoc, mul_assoc, mul_sub, mul_one, he, sub_self, mul_zero, mul_zero]
    have e2 : π y * π b = 0 := by
      simp only [y, map_mul, hQb]
      rw [pow_succ, mul_assoc, mul_assoc, sub_mul, he, one_mul, sub_self, mul_zero, mul_zero]
    have e3 : π x = π x * π b := by linear_combination e1
    rw [e3]; linear_combination (π b) * hUb - e2
  rw [map_mul, hinv, mul_one, hx]

theorem LIdemLift_of (h1 : LFact) : LateralTheory.E.LChartPf.LIdemLift := by
  intro A _ I _
  exact lRed A I (lFinOfFact A I (by simpa only [Ideal.jacobson_bot] using (HenselianRing.jac (R := A) (I := I))) (h1 A I))

end LateralTheory.E.LIdemLiftPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafBaseChangeFieldPf
section
noncomputable section
open Polynomial IntermediateField

namespace LateralTheory.E.LeafBaseChangeFieldPf

def ratMap (F G : Type) [Field F] [Field G] [Algebra F G] : RatFunc F →+* RatFunc G :=
  RatFunc.liftRingHom ((algebraMap G[X] (RatFunc G)).comp (Polynomial.mapRingHom (algebraMap F G))) (show
      nonZeroDivisors F[X] ≤ Submonoid.comap ((algebraMap G[X] (RatFunc G)).comp
        (Polynomial.mapRingHom (algebraMap F G))) (nonZeroDivisors (RatFunc G)) from by
    intro p hp
    rw [Submonoid.mem_comap]
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom]
    intro h
    apply hp0
    have h1 := RatFunc.algebraMap_injective G (h.trans (map_zero _).symm)
    exact (Polynomial.map_eq_zero_iff (algebraMap F G).injective).1 h1)

lemma ratMap_algebraMap (F G : Type) [Field F] [Field G] [Algebra F G] (f : F) :
    ratMap F G (algebraMap F (RatFunc F) f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
  have e1 : algebraMap F (RatFunc F) f = algebraMap F[X] (RatFunc F) (C f) / algebraMap F[X] (RatFunc F) 1 := by
    rw [map_one, div_one, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [e1, ratMap, RatFunc.liftRingHom_apply_div]
  simp [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

lemma mem_adjoin_of_ratFunc {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] (x : RatFunc G) :
    algebraMap (RatFunc G) L x ∈ G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := by
  have key : ∀ p : G[X], algebraMap (RatFunc G) L (algebraMap G[X] (RatFunc G) p) =
      aeval (algebraMap (RatFunc G) L RatFunc.X) p := by
    intro p
    rw [aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]
  rw [← RatFunc.num_div_denom x, map_div₀, key, key]
  exact div_mem (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))
    (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))

lemma transc_X_image {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] : Transcendental G (algebraMap (RatFunc G) L RatFunc.X) := by
  rw [transcendental_iff_injective]
  intro p q h
  rw [aeval_algebraMap_apply, aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap,
    RatFunc.aeval_X_left_eq_algebraMap] at h
  exact RatFunc.algebraMap_injective G ((algebraMap (RatFunc G) L).injective h)

lemma finite_over_adjoin {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] [Module.Finite (RatFunc G) L] :
    FiniteDimensional G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L := by
  let c : RatFunc G →+* G⟮algebraMap (RatFunc G) L RatFunc.X⟯ :=
    (algebraMap (RatFunc G) L).codRestrict _ mem_adjoin_of_ratFunc
  letI : Algebra (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := c.toAlgebra
  haveI : IsScalarTower (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact Module.Finite.of_restrictScalars_finite (RatFunc G) _ L

end LateralTheory.E.LeafBaseChangeFieldPf

open LateralTheory.E.LeafBaseChangeFieldPf in
theorem LateralTheory.E.LeafBaseChangeFieldPf.LeafBaseChangeField_of : LateralTheory.E.LeafCurveVCut.LeafBaseChangeField := by
  intro F G K _ _ _ _ _ t ht hfin
  let e := RatFunc.algEquivOfTranscendental t ht
  let h : F⟮t⟯ →+* RatFunc G := (ratMap F G).comp e.symm.toRingHom
  letI : Algebra F⟮t⟯ (RatFunc G) := h.toAlgebra
  haveI : Nontrivial (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ h.injective
      (algebraMap F⟮t⟯ K).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct F⟮t⟯ (RatFunc G) K)
  letI : Field (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Module.Finite.base_change F⟮t⟯ (RatFunc G) K
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (RatFunc G) M).toLinearMap Ideal.Quotient.mk_surjective
  haveI : IsScalarTower G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := inferInstance
  refine ⟨TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M, inferInstance, inferInstance,
    algebraMap (RatFunc G) _ RatFunc.X,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight (R := F⟮t⟯) (A := RatFunc G) (B := K)).toRingHom,
    transc_X_image, finite_over_adjoin, ?_⟩
  ext f
  have h1 : h (algebraMap F F⟮t⟯ f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
    show ratMap F G (e.symm (algebraMap F F⟮t⟯ f)) = _
    rw [AlgEquiv.commutes]
    exact ratMap_algebraMap F G f
  rw [RingHom.comp_apply, RingHom.comp_apply, IsScalarTower.algebraMap_apply F F⟮t⟯ K, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes, IsScalarTower.algebraMap_apply F⟮t⟯ (RatFunc G)]
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M), ← h1]
  rfl
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafConsPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafConsPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves

def LeafLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1),
  ∃ (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L),
    Rep q i p ι K0 l0 ∧ Rep q i (g1 ≫ p) ι K1 l1 ∧ Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 ∧ RepB q i ι L lL ∧
    MorRep q i p g1 ι l0 l1 f ∧ MorRep q i (g1 ≫ p) g2 ι l1 l2 g ∧ MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ

def LeafGlob : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
  (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
  (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L),
  Rep q i p ι K0 l0 → Rep q i (g1 ≫ p) ι K1 l1 → Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 → RepB q i ι L lL →
  MorRep q i p g1 ι l0 l1 f → MorRep q i (g1 ≫ p) g2 ι l1 l2 g → MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ →
  ∃ (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj L)),
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (shiftFunctor _ n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (shiftFunctor _ n).map ℓ)

theorem LeafCons_of (hL : LeafLoc) (hG : LeafGlob) : LateralTheory.E.EtaleTopologySheaves.LeafCons := by
  intro q _ i B W Y0 Y1 Y2 ι _ p g1 g2
  obtain ⟨K0, K1, K2, L, f, g, ℓ, l0, l1, l2, lL, r0, r1, r2, rL, mf, mg, mℓ⟩ := hL q i ι p g1 g2
  obtain ⟨e0, e2, eL, h1, h2, h3, h4⟩ :=
    hG q i ι p g1 g2 K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  exact ⟨K0, K1, K2, L, f, g, ℓ, l0, l1, l2, lL, e0, e2, eL, r0, r1, r2, rL, mf, mg, mℓ, h1, h2, h3, h4⟩

end LateralTheory.E.LeafConsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafConsPfA
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafConsPfA
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

theorem HK_pull_mk (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) (z : Cocycle L (res R F) n) :
    HK.pull R f F n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom f) z (zero_add n)) := rfl

theorem HK_pull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (y : HK R M F n) : HK.pull R (f ≫ g) F n y = HK.pull R f F n (HK.pull R g F n y) := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  rw [HK_pull_mk, HK_pull_mk, HK_pull_mk]
  congr 1
  apply Cocycle.ext
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem HK_pull_id (R : Type) [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ)
    (y : HK R K F n) : HK.pull R (𝟙 K) F n y = y := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  rw [HK_pull_mk]
  congr 1
  apply Cocycle.ext
  simp [zcomp]

theorem map_congr {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂} (ha : a = a') (hb : b = b')
    (c : φ₁ ≫ b = a ≫ φ₂) (c' : φ₁ ≫ b' = a' ≫ φ₂) :
    mappingCone.map φ₁ φ₂ a b c = mappingCone.map φ₁ φ₂ a' b' c' := by
  subst ha hb; rfl

theorem rmap_congr (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') {u u2 : U' ⟶ U} {e e2 : E' ⟶ E}
    (hu : u = u2) (he : e = e2) (c : f' ≫ e = u ≫ f) (c2 : f' ≫ e2 = u2 ≫ f) :
    rmap R f f' u e c = rmap R f f' u2 e2 c2 := by
  subst hu he; rfl

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (c'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) c'' = rmap R f' f'' u' e' c' ≫ rmap R f f' u e c := by
  unfold rmap
  exact (map_congr _ _ ((chains R).map_comp _ _) ((chains R).map_comp _ _) _ _).trans
    (mappingCone.map_comp _ _ _ _ _ _ _ _ _)

theorem rmap_id (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (c : f ≫ 𝟙 E = 𝟙 U ≫ f) :
    rmap R f f (𝟙 U) (𝟙 E) c = 𝟙 _ := by
  unfold rmap
  exact (map_congr _ _ ((chains R).map_id _) ((chains R).map_id _) _ _).trans (mappingCone.map_id _)

theorem rpl_comp (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (c'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (n : ℤ) (y) :
    rpl q i f f'' (u' ≫ u) (e' ≫ e) c'' n y = rpl q i f' f'' u' e' c' n (rpl q i f f' u e c n y) := by
  simp only [rpl, rpull]
  rw [← HK_pull_comp, ← rmap_comp _ _ _ _ _ _ _ _ _ _ (by simp only [← Functor.map_comp, c'', Category.assoc])]
  congr 1

theorem rpl_id (q : ℕ) (i : ℤ) {U E : Scheme.{0}} (f : U ⟶ E) (c : f ≫ 𝟙 E = 𝟙 U ≫ f) (n : ℤ) (y) :
    rpl q i f f (𝟙 U) (𝟙 E) c n y = y := by
  simp only [rpl, rpull]
  rw [rmap_congr _ _ _ (sch.map_id _) (sch.map_id _) _ (by simp), rmap_id, HK_pull_id]

theorem rpl_bij (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (c : f' ≫ e = u ≫ f) [IsIso u] [IsIso e] (n : ℤ) : Function.Bijective (rpl q i f f' u e c n) := by
  have c2 : f ≫ inv e = inv u ≫ f' := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine Function.bijective_iff_has_inverse.2 ⟨rpl q i f' f (inv u) (inv e) c2 n, fun y => ?_, fun y => ?_⟩
  · rw [← rpl_comp q i f f' f u e (inv u) (inv e) c c2 (by simp), ]
    simp only [IsIso.inv_hom_id]
    exact rpl_id q i f _ n y
  · rw [← rpl_comp q i f' f f' (inv u) (inv e) u e c2 c (by simp)]
    simp only [IsIso.hom_inv_id]
    exact rpl_id q i f' _ n y

end LateralTheory.E.LeafConsPfA
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDescendVCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafDescendVCut

abbrev toR {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) : Sp Ω ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (algebraMap R Ω))

abbrev incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

def Chain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) {C0 C1 C2 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0)
    (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) : Prop :=
  IsProper q ∧ SmoothOfRelativeDimension 1 q ∧ IsProper (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
  IsProper (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧ γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2

def LeafDescendChain : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 → ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1),
    IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2

def LeafDescendMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0), IsProper q → IsPullback v0 c0 q (toR R) → ∀ (e : C0 ⟶ X),
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∃ (R' : Subalgebra k Ω) (hR : R ≤ R'), R'.FG ∧ ∀ (E0 : Scheme.{0}) (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0)
      (w0 : C0 ⟶ E0), IsPullback r q' q (incl hR) → IsPullback w0 c0 q' (toR R') → w0 ≫ r = v0 →
      ∃ f : E0 ⟶ X, w0 ≫ f = e ∧ f ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))

def LeafBaseChange : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r : E0 ⟶ D0), Chain R' c0 γ1 γ2 q' e1 e2 w0 w1 w2 ∧ IsPullback r q' q (incl hR) ∧
      w0 ≫ r = v0

def LeafIrred : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), IsCurve c0 →
    SmoothOfRelativeDimension 1 q → IsPullback v0 c0 q (toR R) → IrreducibleSpace D0

def LeafDimBound : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R), SmoothOfRelativeDimension 1 q →
    topologicalKrullDim D0 ≤ ringKrullDim R + 1

theorem goal_of (hA : LeafDescendChain) (hB : LeafDescendMap) (hC : LeafBaseChange) (hI : LeafIrred)
    (hD : LeafDimBound) : LateralTheory.E.LeafSpreadVCut.LeafDescendV := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, v0, v1, v2, hch⟩ := hA k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨R', hRR', hR', hM⟩ := hB k p Ω R hR c0 q v0 hch.1 hch.2.2.2.2.2.2.1 e he
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r, hch', hr, hw⟩ :=
    hC k Ω R R' hRR' c0 γ1 γ2 q d1 d2 v0 v1 v2 hch
  obtain ⟨f, hf1, hf2⟩ := hM E0 q' r w0 hr hch'.2.2.2.2.2.2.1 hw
  obtain ⟨pq, sq, pq1, sq1, pq2, sq2, P0, P1, P2, c1, c2⟩ := hch'
  exact ⟨R', hR', E0, E1, E2, q', e1, e2, f, w0, w1, w2, pq, sq, pq1, sq1, pq2, sq2, hf2,
    hI k Ω R' hR' c0 q' w0 hc0 sq P0, hD k Ω R' hR' q' sq, P0, P1, P2, c1, c2, hf1⟩

end LateralTheory.E.LeafDescendVCut

end
end

