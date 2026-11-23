module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArithFrobeniusAbsGalois
section
namespace GlobalTheory

open IsLocalRing


open IsLocalRing in
theorem _root_.GlobalTheory.exists_arithFrobenius_absGalois (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (hfin : Finite (IsLocalRing.ResidueField V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [IsLocalRing (integralClosure V Ω)] : ∃ φ : Ω ≃ₐ[K] Ω, ∀ x : integralClosure V Ω, ∃ y : integralClosure V Ω, (y : Ω) = φ x ∧ y - x ^ Nat.card (IsLocalRing.ResidueField V) ∈ IsLocalRing.maximalIdeal (integralClosure V Ω) := by
  classical
  haveI : Algebra.IsIntegral K Ω := inferInstance
  letI : TopologicalSpace (integralClosure V Ω) := ⊥
  haveI : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  haveI : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen_of_isIntegral (K := K) (L := Ω) (x : Ω) using 2
    ext g
    simp [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  haveI : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    refine ⟨fun x hx => ?_⟩
    have hmem : (x : Ω) ∈ IntermediateField.fixedField (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) := by
      rintro ⟨g, -⟩
      exact congrArg Subtype.val (hx g)
    rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hx2 : IsIntegral V (x : Ω) := x.2
    rw [← hk] at hx2
    have hint : IsIntegral V k :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom V K Ω) (algebraMap K Ω).injective).mp hx2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨v, Subtype.ext ?_⟩
    simp [IsScalarTower.algebraMap_apply V K Ω, hv, hk]
  haveI : (maximalIdeal (integralClosure V Ω)).LiesOver (maximalIdeal V) := by
    refine ⟨(IsLocalRing.eq_maximalIdeal ?_).symm⟩
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V)
      (maximalIdeal (integralClosure V Ω))
  letI : Fintype (V ⧸ maximalIdeal V) := @Fintype.ofFinite _ hfin
  letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  letI : Field (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) :=
    Ideal.Quotient.field _
  haveI : Algebra.IsIntegral (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := inferInstance
  haveI : Algebra.IsAlgebraic (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := Algebra.IsIntegral.isAlgebraic
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) (maximalIdeal (integralClosure V Ω))
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  refine ⟨g.1, fun x => ⟨g.1 • x, rfl, ?_⟩⟩
  rw [← Ideal.Quotient.eq]
  have h := congrArg (fun e => e (Ideal.Quotient.mk (maximalIdeal (integralClosure V Ω)) x)) hg
  simp only [Ideal.Quotient.stabilizerHom_apply, FiniteField.frobeniusAlgEquivOfAlgebraic_apply] at h
  rw [Fintype.card_eq_nat_card] at h
  rw [map_pow]
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedToIdempotents
section
open Module

namespace GlobalTheory.ZH

open Module in
private lemma mulVec_column_of_orthogonal_idempotents {R J C : Type} [CommRing R] [Fintype J]
    [DecidableEq C] (e : C → Matrix J J R)
    (he : ∀ c c', e c * e c' = if c = c' then e c else 0) (d c : C) (s : J) :
    (e d).mulVec (fun j => e c j s) = if d = c then (fun j => e c j s) else 0 := by
  ext i
  have h := congrFun (congrFun (he d c) i) s
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct]
  rw [h]
  split_ifs with hdc
  · subst hdc; rfl
  · rfl


open Module in
theorem _root_.GlobalTheory.ZH.exists_basis_adapted_to_idempotents :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (J C : Type) [Fintype J] [DecidableEq J] [Fintype C]
      [DecidableEq C] (e : C → Matrix J J O),
      (∀ c c', e c * e c' = if c = c' then e c else 0) → ∑ c, e c = 1 →
      ∃ (κ : J → C) (col : J → J),
        IsUnit (Matrix.det (Matrix.of fun i j => e (κ i) j (col i))) ∧
        ∀ c, Submodule.span O (Set.range fun i => fun j => e c j i) =
          Submodule.span O {v | ∃ i, κ i = c ∧ v = fun j => e c j (col i)} := by
  intro O _ _ J C _ _ _ _ e he hsum
  classical
  let f : Matrix J J O →+* Matrix J J (IsLocalRing.ResidueField O) :=
    (IsLocalRing.residue O).mapMatrix
  let E : C → Matrix J J (IsLocalRing.ResidueField O) := fun c => f (e c)
  have hE : ∀ c c', E c * E c' = if c = c' then E c else 0 := by
    intro c c'
    simp only [E, ← map_mul, he]
    split_ifs <;> simp
  have hEsum : ∑ c, E c = 1 := by simp only [E, ← map_sum, hsum, map_one]
  let w : C → J → (J → IsLocalRing.ResidueField O) := fun c s j => E c j s
  choose T a ha hsp hli using fun c => exists_linearIndependent' (IsLocalRing.ResidueField O) (w c)
  haveI : ∀ c, Fintype (T c) := fun c => Fintype.ofInjective (a c) (ha c)
  let W : (Σ c, T c) → (J → IsLocalRing.ResidueField O) := fun p => w p.1 (a p.1 p.2)
  have hWli : LinearIndependent (IsLocalRing.ResidueField O) W := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    obtain ⟨d, t⟩ := p
    have h1 := congrArg (Matrix.mulVecLin (E d)) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, Matrix.mulVecLin_apply, W, w,
      mulVec_column_of_orthogonal_idempotents E hE, Fintype.sum_sigma, smul_ite, smul_zero] at h1
    rw [Finset.sum_eq_single d (fun c _ hc => by simp [Ne.symm hc]) (by simp)] at h1
    simp only [if_pos rfl] at h1
    exact Fintype.linearIndependent_iff.mp (hli d) (fun t => g ⟨d, t⟩) h1 t
  have hWsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range W) := by
    rw [← (Pi.basisFun (IsLocalRing.ResidueField O) J).span_eq, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    have hs : Pi.basisFun (IsLocalRing.ResidueField O) J s = ∑ c, w c s := by
      ext j
      have := congrFun (congrFun hEsum j) s
      simp only [Matrix.sum_apply, Matrix.one_apply] at this
      simp [w, Finset.sum_apply, this, Pi.single_apply]
    rw [hs]
    refine Submodule.sum_mem _ fun c _ => ?_
    have h2 : w c s ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range (w c ∘ a c)) := by
      rw [hsp c]; exact Submodule.subset_span ⟨s, rfl⟩
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨c, t⟩, rfl⟩
  let b := Basis.mk hWli hWsp
  have hcard : Fintype.card J = Fintype.card (Σ c, T c) := by
    rw [← Module.finrank_fintype_fun_eq_card (IsLocalRing.ResidueField O),
      Module.finrank_eq_card_basis b]
  let σ : J ≃ (Σ c, T c) := Fintype.equivOfCardEq hcard
  let M : Matrix J J O := Matrix.of fun i j => e (σ i).1 j (a (σ i).1 (σ i).2)
  have hdet : IsUnit M.det := by
    rw [← isUnit_map_iff (IsLocalRing.residue O), RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
    exact hWli.comp σ σ.injective
  refine ⟨fun i => (σ i).1, fun i => a (σ i).1 (σ i).2, hdet, fun c => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    show (fun j => e c j s) ∈ Submodule.span O _
    have hfix : (e c).mulVec (fun j => e c j s) = fun j => e c j s := by
      simpa using mulVec_column_of_orthogonal_idempotents e he c c s
    have h3 : (fun j => e c j s) = Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
    have h4 : (fun j => e c j s) =
        ∑ i, (Matrix.vecMul (fun j => e c j s) M⁻¹) i • (e c).mulVec (M i) := by
      calc (fun j => e c j s) = (e c).mulVec (fun j => e c j s) := hfix.symm
        _ = (e c).mulVec (Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M) := by rw [← h3]
        _ = _ := by
          rw [Matrix.vecMul_eq_sum]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]
    rw [h4]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h5 : (e c).mulVec (M i) = if c = (σ i).1 then M i else 0 :=
      mulVec_column_of_orthogonal_idempotents e he c (σ i).1 _
    rw [h5]
    split_ifs with h
    · exact Submodule.subset_span ⟨i, h.symm, by subst h; rfl⟩
    · exact zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact Submodule.subset_span ⟨a (σ i).1 (σ i).2, rfl⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfIsIntegralImage
section
open scoped BigOperators

namespace GlobalTheory

theorem exists_mul_eq_natCast_of_isIntegral_int {S : Type*} [CommRing S] [IsDomain S]
    {y : S} (hy : IsIntegral ℤ y) (hy0 : y ≠ 0) :
    ∃ (t : S) (n : ℕ), 0 < n ∧ y * t = n := by
  obtain ⟨m, hm, t, ht⟩ :=
    hy.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hy0)
  have ht' : (m : S) = y * t := by simpa using ht
  refine ⟨(m.sign : S) * t, m.natAbs, Int.natAbs_pos.mpr hm, ?_⟩
  have h1 : ((m.natAbs : ℤ) : S) = ((m.sign * m : ℤ) : S) := by
    rw [Int.sign_mul_self_eq_natAbs]
  have h2 : (m.natAbs : S) = (m.sign : S) * (m : S) := by
    rw [← Int.cast_mul, ← h1, Int.cast_natCast]
  rw [h2, ht']; ring

theorem exists_field_of_isIntegral_image :
    ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ := by
  intro R _ φ hφ
  let S := R ⧸ RingHom.ker φ
  have hinj : Function.Injective (RingHom.kerLift φ) := RingHom.kerLift_injective φ
  haveI : IsDomain S := hinj.isDomain (RingHom.kerLift φ)
  haveI : CharZero S := (RingHom.kerLift φ).charZero
  have hint : ∀ y : S, @IsIntegral ℤ S _ _ (Ring.toIntAlgebra S) y := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← isIntegral_algHom_iff (RingHom.kerLift φ).toIntAlgHom hinj]
    exact hφ r
  haveI : CharZero (FractionRing S) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S))
  refine ⟨FractionRing S, inferInstance, inferInstance,
    (algebraMap S (FractionRing S)).comp (Ideal.Quotient.mk _), ?_, ?_⟩
  · intro x
    obtain ⟨a, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨t, n, hn, ht⟩ := exists_mul_eq_natCast_of_isIntegral_int (hint y) hy0
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (a * t)
    refine ⟨r, n, hn, ?_⟩
    have hy' : algebraMap S (FractionRing S) y ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr hy0
    have hn' : (n : FractionRing S) =
        algebraMap S (FractionRing S) y * algebraMap S (FractionRing S) t := by
      rw [← map_mul, ht, map_natCast]
    rw [RingHom.comp_apply, hr, hn', map_mul]
    field_simp
  · intro A _ _ χ hχ
    let ψ : S →+* A := Ideal.Quotient.lift (RingHom.ker φ) χ (fun r hr => hχ r hr)
    have hu : ∀ y : nonZeroDivisors S, IsUnit (ψ y) := by
      intro y
      obtain ⟨t, n, hn, ht⟩ :=
        exists_mul_eq_natCast_of_isIntegral_int (hint y) (nonZeroDivisors.ne_zero y.2)
      have hnu : IsUnit (n : A) := by
        have : IsUnit (n : ℚ) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
        simpa using this.map (algebraMap ℚ A)
      have : ψ y * ψ t = n := by rw [← map_mul, ht, map_natCast]
      exact isUnit_of_mul_isUnit_left (this ▸ hnu)
    refine ⟨IsLocalization.lift (M := nonZeroDivisors S) (S := FractionRing S) hu, ?_⟩
    ext r
    simp only [RingHom.comp_apply, IsLocalization.lift_eq]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalAdjoinAlgebraic
section
namespace GlobalTheory

theorem exists_extend_of_ringEquiv_of_isAlgebraic {K L M F : Type} [Field K] [Field L] [Field M] [Field F]
    [IsAlgClosed F] [Algebra L M] [Algebra.IsAlgebraic L M] (φ : K ≃+* L) (g : K →+* F) :
    ∃ g' : M →+* F, g'.comp ((algebraMap L M).comp φ.toRingHom) = g := by
  letI : Algebra L F := (g.comp φ.symm.toRingHom).toAlgebra
  let g' : M →ₐ[L] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨g'.toRingHom, RingHom.ext fun x => ?_⟩
  change g' (algebraMap L _ (φ x)) = g x
  rw [g'.commutes]
  change g (φ.symm (φ x)) = g x
  rw [φ.symm_apply_apply]

theorem exists_finite_normal_adjoin_algebraic :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
      (s : AlgebraicClosure (FractionRing R)),
      ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂)
        (h' : FractionRing R →+* FractionRing R₂)
        (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)),
        Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧
        (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧
        (∃ s₂, e s₂ = s) ∧
        ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F),
          ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by
  intro R _ _ _ _ _ s
  have : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  let L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R)) :=
    IntermediateField.adjoin (FractionRing R) {s}
  have : FiniteDimensional (FractionRing R) L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  have : Algebra.IsSeparable (FractionRing R) L := inferInstance
  have hfin : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)
  have hfr : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) L
  let φ : FractionRing (integralClosure R L) ≃+* L :=
    (FractionRing.algEquiv (integralClosure R L) L).toRingEquiv
  have hφ : ∀ x : integralClosure R L,
      φ (algebraMap (integralClosure R L) _ x) = algebraMap (integralClosure R L) L x :=
    fun x => (FractionRing.algEquiv (integralClosure R L) L).commutes x
  refine ⟨integralClosure R L, inferInstance, inferInstance, algebraMap R _,
    φ.symm.toRingHom.comp (algebraMap (FractionRing R) L),
    (algebraMap L (AlgebraicClosure (FractionRing R))).comp φ.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : algebraMap R L a = algebraMap R L b := by
      rw [IsScalarTower.algebraMap_apply R (integralClosure R L) L,
        IsScalarTower.algebraMap_apply R (integralClosure R L) L b, hab]
    rw [IsScalarTower.algebraMap_apply R (FractionRing R) L,
      IsScalarTower.algebraMap_apply R (FractionRing R) L b] at h1
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) L).injective h1)
  · exact RingHom.finite_algebraMap.2 hfin
  · exact (isIntegrallyClosed_iff_isIntegrallyClosedIn L).2 inferInstance
  · intro r
    apply φ.injective
    rw [hφ, ← IsScalarTower.algebraMap_apply R (integralClosure R L) L,
      IsScalarTower.algebraMap_apply R (FractionRing R) L]
    exact φ.apply_symm_apply _
  · refine RingHom.ext fun x => ?_
    change algebraMap L _ (φ (φ.symm (algebraMap (FractionRing R) L x))) = _
    rw [φ.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
  · refine ⟨φ.symm ⟨s, IntermediateField.mem_adjoin_simple_self _ s⟩, ?_⟩
    change algebraMap L _ (φ (φ.symm _)) = _
    rw [φ.apply_symm_apply]
    rfl
  · intro F _ _ g
    have : Algebra.IsAlgebraic L (AlgebraicClosure (FractionRing R)) :=
      Algebra.IsAlgebraic.tower_top (K := FractionRing R) L
    exact exists_extend_of_ringEquiv_of_isAlgebraic φ g

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsForallNeZeroOfCountableAnalytic
section
open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem exists_forall_ne_zero_of_countable_analytic :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (U : Set E),
      IsOpen U → IsPreconnected U → U.Nonempty → ∀ (ι : Type) [Countable ι] (f : ι → E → ℂ),
      (∀ i, AnalyticOnNhd ℂ (f i) U) → (∀ i, ∃ x ∈ U, f i x ≠ 0) →
      ∃ x ∈ U, ∀ i, f i x ≠ 0 := by
  intro E _ _ _ U hU hc hne ι _ f hf hnz
  let S : ι → Set E := fun i => (U ∩ f i ⁻¹' ({0}ᶜ)) ∪ (closure U)ᶜ
  have hopen : ∀ i, IsOpen (S i) := fun i =>
    ((hf i).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union
      isClosed_closure.isOpen_compl
  have hdense : ∀ i, Dense (S i) := by
    intro i
    rw [dense_iff_inter_open]
    intro V hV hVne
    by_cases hVU : (V ∩ U).Nonempty
    · obtain ⟨z, hzV, hzU⟩ := hVU
      by_contra hcon
      have hzero : ∀ y ∈ V ∩ U, f i y = 0 := by
        intro y hy
        by_contra hy0
        exact hcon ⟨y, hy.1, Or.inl ⟨hy.2, hy0⟩⟩
      have hev : f i =ᶠ[nhds z] 0 := by
        filter_upwards [(hV.inter hU).mem_nhds ⟨hzV, hzU⟩] with y hy
        exact hzero y hy
      have hall := (hf i).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU hev
      obtain ⟨x, hxU, hx⟩ := hnz i
      exact hx (hall hxU)
    · obtain ⟨z, hzV⟩ := hVne
      refine ⟨z, hzV, Or.inr ?_⟩
      intro hz
      exact hVU (mem_closure_iff.1 hz V hV hzV)
  have hD : Dense (⋂ i, S i) := dense_iInter_of_isOpen hopen hdense
  obtain ⟨x, hxU, hx⟩ := hD.inter_open_nonempty U hU hne
  refine ⟨x, hxU, fun i => ?_⟩
  rcases Set.mem_iInter.1 hx i with h | h
  · exact h.2
  · exact absurd (subset_closure hxU) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormLimitIdeal
section
namespace GlobalTheory.Degen

open MvPolynomial

theorem exists_form_limit_ideal (R : Type) [CommRing R] (I : Ideal R) (hI : IsAdicComplete I R)
    (σ : Type) [Finite σ] (K : ℕ → Ideal (MvPolynomial σ R)) (t : ℕ)
    (hK : ∀ e F, F.IsHomogeneous t → F ∈ K (e + 1) → F ∈ K e)
    (ha : ∀ e, ∀ a ∈ I ^ (e + 1), MvPolynomial.C a ∈ K e)
    (hs : ∀ e F, F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial σ R, G.IsHomogeneous t ∧
      (∀ d, AddMonoidAlgebra.coeff G d ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1))
    (e : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous t) (hFe : F ∈ K e) :
    ∃ F₁ : MvPolynomial σ R, F₁.IsHomogeneous t ∧ (∀ e', F₁ ∈ K e') ∧
      ∀ d, AddMonoidAlgebra.coeff (F - F₁) d ∈ I ^ (e + 1) := by
  classical
  have hdesc : ∀ (P : MvPolynomial σ R), P.IsHomogeneous t → ∀ m k, P ∈ K (m + k) → P ∈ K m := by
    intro P hP m k
    induction k with
    | zero => exact id
    | succ k ih => exact fun h => ih (hK _ _ hP h)
  have hcoef : ∀ (j : ℕ) (P : MvPolynomial σ R), (∀ d, AddMonoidAlgebra.coeff P d ∈ I ^ (j + 1)) → P ∈ K j := by
    intro j P hP
    rw [P.as_sum]
    refine Ideal.sum_mem _ fun d _ => ?_
    have : (monomial d (AddMonoidAlgebra.coeff P d) : MvPolynomial σ R) = C (AddMonoidAlgebra.coeff P d) * monomial d 1 := by
      rw [C_mul_monomial, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (ha _ _ (hP d))
  choose G hG1 hG2 hG3 using hs
  let s : (n : ℕ) → {P : MvPolynomial σ R // P.IsHomogeneous t ∧ P ∈ K (e + n)} := fun n =>
    Nat.rec (motive := fun n => {P : MvPolynomial σ R // P.IsHomogeneous t ∧ P ∈ K (e + n)})
      ⟨F, hF, hFe⟩
      (fun n z => ⟨z.1 - G (e + n) z.1 z.2.1 z.2.2, z.2.1.sub (hG1 _ _ _ _), hG3 _ _ _ _⟩) n
  have hs0 : (s 0).1 = F := rfl
  have hsn : ∀ n, (s (n + 1)).1 = (s n).1 - G (e + n) (s n).1 (s n).2.1 (s n).2.2 :=
    fun n => rfl
  have hd : ∀ d m n, m ≤ n → AddMonoidAlgebra.coeff (s m).1 d - AddMonoidAlgebra.coeff (s n).1 d ∈ I ^ (e + m + 1) := by
    intro d m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hsn, coeff_sub, ← sub_add]
      exact Ideal.add_mem _ ih
        (Ideal.pow_le_pow_right (by omega) (hG2 (e + n) (s n).1 (s n).2.1 (s n).2.2 d))
  have hmem : ∀ (n : ℕ) (z : R), z ∈ (I ^ n • ⊤ : Submodule R R) ↔ z ∈ I ^ n := by
    intro n z
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hlim : ∀ d, ∃ L : R, ∀ m, AddMonoidAlgebra.coeff (s m).1 d - L ∈ I ^ (e + m + 1) := by
    intro d
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := R) hI.toIsPrecomplete
      (f := fun n => AddMonoidAlgebra.coeff (s n).1 d) (by
        intro m n hmn
        rw [SModEq.sub_mem, hmem]
        exact Ideal.pow_le_pow_right (by omega) (hd d m n hmn))
    refine ⟨L, fun m => ?_⟩
    have h := hL (e + m + 1)
    rw [SModEq.sub_mem, hmem] at h
    have h2 := Ideal.add_mem _ (hd d m (e + m + 1) (by omega)) h
    simpa using h2
  choose L hL using hlim
  have hfin : {d : σ →₀ ℕ | d.degree = t}.Finite :=
    (Finsupp.finite_of_degree_le t).subset fun d hd => le_of_eq hd
  let F₁ : MvPolynomial σ R := ∑ d ∈ hfin.toFinset, monomial d (L d)
  have hF₁ : F₁.IsHomogeneous t :=
    IsHomogeneous.sum _ _ _ fun d hd => isHomogeneous_monomial _ (by simpa using hd)
  have hc : ∀ m d, AddMonoidAlgebra.coeff ((s m).1 - F₁) d ∈ I ^ (e + m + 1) := by
    intro m d
    by_cases hdt : d.degree = t
    · have : AddMonoidAlgebra.coeff F₁ d = L d := by
        simp only [F₁, coeff_sum, coeff_monomial]
        rw [Finset.sum_ite_eq']
        simp [hdt]
      rw [coeff_sub, this]
      exact hL d m
    · rw [((s m).2.1.sub hF₁).coeff_eq_zero hdt]
      exact Ideal.zero_mem _
  refine ⟨F₁, hF₁, fun m => hdesc _ hF₁ m e ?_, hc 0⟩
  rw [add_comm m e]
  have h := Ideal.sub_mem _ (s m).2.2 (hcoef _ _ (hc m))
  simpa using h

end GlobalTheory.Degen
end

