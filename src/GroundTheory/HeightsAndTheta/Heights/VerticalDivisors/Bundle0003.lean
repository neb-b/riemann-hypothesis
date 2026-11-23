module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartTorsion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace ChartTorsion

variable {D : Type} [CommRing D] {n : ℕ} (k : ℕ) (P : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

abbrev Base := Localization.Away (Ideal.Quotient.mk P (X j))

def toBase : MvPolynomial (Fin n) D →+* Base P j :=
  (algebraMap (MvPolynomial (Fin n) D ⧸ P) (Base P j)).comp (Ideal.Quotient.mk P)

def solve (i : Fin k) (m : Fin n) : MvPolynomial (Fin k × Fin n) (Base P j) :=
  if m = j then
    -(C (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X j))) *
      ∑ l ∈ Finset.univ.erase j, C (toBase P j (X l)) * X (i, l))
  else X (i, m)

def toChart : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D →+* MvPolynomial (Fin k × Fin n) (Base P j) :=
  eval₂Hom (C.comp ((toBase P j).comp C))
    (Sum.elim (fun m => C (toBase P j (X m))) (fun im => solve k P j im.1 im.2))

theorem toChart_rename (p : MvPolynomial (Fin n) D) :
    toChart k P j (rename Sum.inl p) = C (toBase P j p) := by
  induction p using MvPolynomial.induction_on with
  | C d => simp [toChart]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p m hp => simp only [map_mul, hp, rename_X]; simp [toChart]

theorem incIdeal_le_ker : incIdeal P k ≤ RingHom.ker (toChart k P j) := by
  refine sup_le (Ideal.map_le_iff_le_comap.2 fun p hp => ?_)
    (Ideal.span_le.2 (Set.range_subset_iff.2 fun i => ?_))
  · show toChart k P j (rename Sum.inl p) = 0
    rw [toChart_rename]
    simp [toBase, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · show toChart k P j _ = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hs : ∀ l ∈ Finset.univ.erase j,
        toChart k P j (X (Sum.inr (i, l))) * toChart k P j (X (Sum.inl l)) =
          C (toBase P j (X l)) * X (i, l) := by
      intro l hl
      simp [toChart, solve, Finset.ne_of_mem_erase hl, mul_comm]
    rw [Finset.sum_congr rfl hs]
    have h1 : C (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X j))) * C (toBase P j (X j)) =
        (1 : MvPolynomial (Fin k × Fin n) (Base P j)) := by
      rw [← C_mul, mul_comm, toBase, RingHom.comp_apply, IsLocalization.Away.mul_invSelf, C_1]
    simp only [toChart, eval₂Hom_X', Sum.elim_inl, Sum.elim_inr, solve, ↓reduceIte]
    linear_combination (-(∑ l ∈ Finset.univ.erase j, C (toBase P j (X l)) * X (i, l))) * h1

abbrev Loc := Localization.Away (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))

def toLoc : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D →+* Loc k P j :=
  (algebraMap _ (Loc k P j)).comp (Ideal.Quotient.mk (incIdeal P k))

theorem toLoc_mem {g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D} (hg : g ∈ incIdeal P k) :
    toLoc k P j g = 0 := by
  simp [toLoc, Ideal.Quotient.eq_zero_iff_mem.2 hg]

def quotToLoc : MvPolynomial (Fin n) D ⧸ P →+* Loc k P j :=
  Ideal.Quotient.lift P ((toLoc k P j).comp (rename Sum.inl).toRingHom) fun _ hp =>
    toLoc_mem k P j (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))

theorem quotToLoc_mk (p : MvPolynomial (Fin n) D) :
    quotToLoc k P j (Ideal.Quotient.mk P p) = toLoc k P j (rename Sum.inl p) := rfl

theorem isUnit_quotToLoc : IsUnit (quotToLoc k P j (Ideal.Quotient.mk P (X j))) := by
  rw [quotToLoc_mk, rename_X]
  exact IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))

def baseToLoc : Base P j →+* Loc k P j :=
  IsLocalization.Away.lift _ (isUnit_quotToLoc k P j)

theorem baseToLoc_toBase (p : MvPolynomial (Fin n) D) :
    baseToLoc k P j (toBase P j p) = toLoc k P j (rename Sum.inl p) := by
  simp [baseToLoc, toBase, quotToLoc_mk]

def back : MvPolynomial (Fin k × Fin n) (Base P j) →+* Loc k P j :=
  eval₂Hom (baseToLoc k P j) fun im => toLoc k P j (X (Sum.inr im))

theorem back_toChart (g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D) :
    back k P j (toChart k P j g) = toLoc k P j g := by
  suffices h : (back k P j).comp (toChart k P j) = toLoc k P j from congrArg (· g) h
  apply MvPolynomial.ringHom_ext
  · intro d
    have := baseToLoc_toBase k P j (C d)
    simpa [back, toChart] using this
  · rintro (m | ⟨i, m⟩)
    · have := baseToLoc_toBase k P j (X m)
      simpa [back, toChart] using this
    · by_cases hm : m = j
      · subst hm
        have hinc : toLoc k P m (∑ l, X (Sum.inr (i, l)) * X (Sum.inl l)) = 0 :=
          toLoc_mem k P m (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), map_add (f := _), map_sum] at hinc
        have hinv : baseToLoc k P m (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X m))) *
            toLoc k P m (X (Sum.inl m)) = 1 := by
          have e := baseToLoc_toBase k P m (X m)
          rw [rename_X] at e
          rw [← e, toBase, RingHom.comp_apply, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf,
            map_one]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [RingHom.comp_apply, toChart, eval₂Hom_X', Sum.elim_inr, solve, ↓reduceIte,
          back, map_neg, map_mul, map_sum, eval₂Hom_C, eval₂Hom_X', baseToLoc_toBase, rename_X]
        simp only [map_mul] at hinc
        set u := toLoc k P m (X (Sum.inr (i, m)))
        set xm := toLoc k P m (X (Sum.inl m))
        set inv := baseToLoc k P m (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X m)))
        have hS : ∑ l ∈ Finset.univ.erase m, toLoc k P m (X (Sum.inl l)) *
              toLoc k P m (X (Sum.inr (i, l))) =
            ∑ l ∈ Finset.univ.erase m, toLoc k P m (X (Sum.inr (i, l))) *
              toLoc k P m (X (Sum.inl l)) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        rw [hS]
        linear_combination (-inv) * hinc + u * hinv
      · simp [back, toChart, solve, hm]

end ChartTorsion


open ChartTorsion in
theorem ChartTorsion.proof : ChartTorsion.Statement := by
  intro D _ _ n k P hP hPD c g hc hcg j
  by_cases hj : (X j : MvPolynomial (Fin n) D) ∈ P
  · refine ⟨1, Ideal.mul_mem_right _ _ (Ideal.mem_sup_left ?_)⟩
    simpa using Ideal.mem_map_of_mem (rename (R := D) (Sum.inl (β := Fin k × Fin n))) hj
  have hx : Ideal.Quotient.mk P (X j) ≠ 0 := fun h => hj (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hle : Submonoid.powers (Ideal.Quotient.mk P (X j)) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hx
  have : IsDomain (Base P j) := IsLocalization.isDomain_localization hle
  have hcz : toChart k P j (C c) ≠ 0 := by
    simp only [toChart, eval₂Hom_C, RingHom.comp_apply, ne_eq, C_eq_zero, toBase]
    rw [map_eq_zero_iff _ (IsLocalization.injective (Base P j) hle)]
    intro h
    exact hc (hPD c (Ideal.Quotient.eq_zero_iff_mem.1 h))
  have hg0 : toChart k P j g = 0 := by
    have h := incIdeal_le_ker k P j hcg
    rw [RingHom.mem_ker, map_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hcz
  have hl : toLoc k P j g = 0 := by
    rw [← back_toChart, hg0, map_zero]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))) _ _).1 hl
  refine ⟨N, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  simpa [map_mul, map_pow] using hN

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PCodimOnePrimeAvoid
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open GroundTheory.Arith.Abelian.Jacobian

theorem CodimOnePrimeAvoid.proof : CodimOnePrimeAvoid.Statement := by
  intro k B _ _ _ _ _ h hh hdim
  let Bh := Localization.Away h
  have hle : Submonoid.powers h ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hh
  have : IsDomain Bh := IsLocalization.isDomain_localization hle
  have : Algebra.FinitePresentation B Bh := IsLocalization.Away.finitePresentation (S := Bh) h
  have : Algebra.FiniteType B Bh := inferInstance
  have : Algebra.FiniteType k Bh := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have : IsNoetherianRing Bh := Algebra.FiniteType.isNoetherianRing k Bh
  let K := FractionRing B
  have hu : ∀ y : Submonoid.powers h, IsUnit (algebraMap B K y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective B K)).2
      (nonZeroDivisors.ne_zero (hle y.2)))
  let _ : Algebra Bh K := (IsLocalization.lift (M := Submonoid.powers h) (S := Bh) hu).toAlgebra
  have : IsScalarTower B Bh K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := Submonoid.powers h) (S := Bh) hu x).symm
  have : IsScalarTower k Bh K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply k B K, IsScalarTower.algebraMap_apply k B Bh,
      ← IsScalarTower.algebraMap_apply B Bh K]
  have : IsFractionRing Bh K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers h) Bh K
  have hdimh : ringKrullDim Bh = ringKrullDim B := by
    rw [ringKrullDim_eq_trdeg_fractionRing k K, ringKrullDim_eq_trdeg_fractionRing k K]
  have hnf : ¬ IsField Bh := fun hf => by
    have h0 := ringKrullDim_eq_zero_of_isField hf
    rw [hdimh] at h0
    rw [h0] at hdim
    exact absurd hdim (by decide)
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 hnf
  obtain ⟨x, hxp, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem p).2 hxp)
  have hqp : q.IsPrime := hq.isPrime
  have hxq : x ∈ q := (Ideal.span_singleton_le_iff_mem q).1 hq.1.2
  have hq1 : q.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    exact hx0 hxq
  refine ⟨q.comap (algebraMap B Bh), hqp.comap _, fun hhN => hqp.ne_top ?_, ?_⟩
  · exact Ideal.eq_top_of_isUnit_mem _ hhN (IsLocalization.Away.algebraMap_isUnit h)
  · have hN := IsLocalization.height_under (Submonoid.powers h) q
    rw [hq1] at hN
    have := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient k (q.comap (algebraMap B Bh))
    rw [Ideal.under] at hN
    rw [hN] at this
    rw [← this, add_comm]
    rfl

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreCompDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

section Residue

variable {O : Type} [CommRing O] [IsDedekindDomain O] {n : ℕ} (v : HeightOneSpectrum O)
  (W : Ideal (MvPolynomial (Fin n) O))

noncomputable def quotientResidueEquiv (hW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W) :
    (MvPolynomial (Fin n) O ⧸ W) ≃+*
      (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸
        W.map (MvPolynomial.map (algebraMap O v.asIdeal.ResidueField))) :=
  let φ : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) v.asIdeal.ResidueField :=
    MvPolynomial.map (algebraMap O v.asIdeal.ResidueField)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hψ : Function.Surjective ((Ideal.Quotient.mk (W.map φ)).comp φ) :=
    Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ((Ideal.Quotient.mk (W.map φ)).comp φ) = W := by
    have : RingHom.ker φ = Ideal.map C v.asIdeal := by
      rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, this, sup_eq_left.mpr hW]
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)

theorem exists_ringKrullDim_quotient_eq_nat (hWp : W.IsPrime)
    (hW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W) :
    ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) O ⧸ W) = m := by
  let φ : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) v.asIdeal.ResidueField :=
    MvPolynomial.map (algebraMap O v.asIdeal.ResidueField)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hkerW : RingHom.ker φ ≤ W := by
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
    exact hW
  have : (W.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hkerW
  obtain ⟨m, hm, -⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := v.asIdeal.ResidueField) (A := MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸ W.map φ)
  exact ⟨m, (ringKrullDim_eq_of_ringEquiv (quotientResidueEquiv v W hW)).trans hm⟩

end Residue

theorem FibreCompDim.proof (hBase : FibreClosedComponent.Statement) (hCut : FibreCut.Statement)
    (hDrop : GenericFibreDrop.Statement) : FibreCompDim.Statement := by
  intro O _ _ F _ _ _ n P W v hP hPC hW
  have key : ∀ (m : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)), P.IsPrime →
      P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) = m →
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) =
        ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro P W hP hPC hW hm
    by_cases hmax : W.IsMaximal
    · rw [hBase O F n P W v hP hPC hW hmax]
      let _ := Ideal.Quotient.field W
      exact ringKrullDim_eq_zero_of_field _
    · obtain ⟨P', W', f, hfP, hP', hP'C, hW', hdim⟩ := hCut O n P W v hP hPC hW hmax
      have : W'.IsPrime := hW'.1.1
      have : P'.IsPrime := hP'.1.1
      obtain ⟨m', hm'⟩ := exists_ringKrullDim_quotient_eq_nat v W' hW'.1.1
        (le_sup_right.trans hW'.1.2)
      have hmm : m' + 1 = m := by
        rw [hm', hm] at hdim
        exact_mod_cast hdim
      rw [hDrop O F n P P' f hP hP'C hfP hP', ← ih m' (by omega) P' W' hP'.1.1 hP'C hW' hm', hdim]
  have : W.IsPrime := hW.1.1
  obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq_nat v W hW.1.1 (le_sup_right.trans hW.1.2)
  rw [← ringKrullDim_eq_of_ringEquiv (quotientResidueEquiv v W (le_sup_right.trans hW.1.2))]
  exact key m P W hP hPC hW hm

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

theorem not_lt_of_mem_minimalPrimes_sup_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P W Q : Ideal R} {f : R} [P.IsPrime] [W.IsPrime] (hPW : P < W)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : ¬ W < Q := by
  intro hWQ
  have : Q.IsPrime := hQ.isPrime
  have hPQ : P ≤ Q := le_sup_left.trans hQ.le
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ
  have hπ : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hWm : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPW.le)
  have hQm : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPQ)
  have hinj : ∀ {I J : Ideal R}, P ≤ I → P ≤ J →
      I.map (Ideal.Quotient.mk P) = J.map (Ideal.Quotient.mk P) → I = J := by
    intro I J hI hJ h
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h
    rwa [Ideal.comap_map_of_surjective' _ hπ, Ideal.comap_map_of_surjective' _ hπ, hker,
      sup_eq_left.mpr hI, sup_eq_left.mpr hJ] at this
  have hlt1 : (⊥ : Ideal (R ⧸ P)) < W.map (Ideal.Quotient.mk P) := by
    refine bot_lt_iff_ne_bot.mpr fun h => hPW.ne ?_
    exact hinj le_rfl hPW.le (by rw [h, Ideal.map_quotient_self])
  have hlt2 : W.map (Ideal.Quotient.mk P) < Q.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne (Ideal.map_mono hWQ.le) fun h => hWQ.ne (hinj hPW.le hPQ h)
  have a := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt1
  have b := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt2
  rw [Ideal.height_bot] at a
  have c : (W.map (Ideal.Quotient.mk P)).height < 1 := lt_of_lt_of_le b h1
  rw [Order.lt_one_iff] at c
  rw [c] at a
  exact lt_irrefl _ a

theorem FibreCut.proof (hAvoid : CodimOnePrimeAvoid.Statement) : FibreCut.Statement := by
  intro O _ _ n P W v hP hPC hW hWmax
  classical
  set vX : Ideal (MvPolynomial (Fin n) O) :=
    Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal with hvX
  have hWp : W.IsPrime := hW.isPrime
  have hPW : P ≤ W := le_sup_left.trans hW.le
  have hvW : vX ≤ W := le_sup_right.trans hW.le
  have hfin := (P ⊔ vX).finite_minimalPrimes_of_isNoetherianRing

  obtain ⟨h, hhQ, hhW⟩ : ∃ h, (∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≠ W → h ∈ Q) ∧ h ∉ W := by
    have hnot : ¬ (hfin.toFinset.erase W).inf id ≤ W := by
      rw [hWp.inf_le']
      rintro ⟨Q, hQs, hQW⟩
      obtain ⟨hQW', hQ⟩ := Finset.mem_erase.mp hQs
      rw [Set.Finite.mem_toFinset] at hQ
      exact hQW' (le_antisymm hQW (hW.2 ⟨hQ.isPrime, hQ.le⟩ hQW))
    obtain ⟨h, hh, hhW⟩ := SetLike.not_le_iff_exists.mp hnot
    exact ⟨h, fun Q hQ hQW => Finset.inf_le (f := id)
      (Finset.mem_erase.mpr ⟨hQW, hfin.mem_toFinset.mpr hQ⟩) hh, hhW⟩

  have hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hWC : W.comap (C : O →+* MvPolynomial (Fin n) O) = v.asIdeal :=
    (hvmax.eq_of_le (Ideal.comap_ne_top _ hWp.ne_top) (Ideal.map_le_iff_le_comap.mp hvW)).symm
  have : W.LiesOver v.asIdeal := ⟨hWC.symm⟩
  let _ : Field (O ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hBnf : ¬ IsField (MvPolynomial (Fin n) O ⧸ W) :=
    fun hf => hWmax (Ideal.Quotient.maximal_of_isField W hf)
  obtain ⟨I, hIbot, hItop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp hBnf
  have hdim1 : 1 ≤ ringKrullDim (MvPolynomial (Fin n) O ⧸ W) := by
    have : Nontrivial (_ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop.ne
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le I hIbot.ne'
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := (MvPolynomial (Fin n) O ⧸ W) ⧸ I)
    calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
      _ ≤ ringKrullDim ((MvPolynomial (Fin n) O ⧸ W) ⧸ I) + 1 := add_le_add h0 le_rfl
      _ ≤ _ := h2
  obtain ⟨N₀, hN₀, hhN₀, hdimN₀⟩ := hAvoid (O ⧸ v.asIdeal) (MvPolynomial (Fin n) O ⧸ W)
    (Ideal.Quotient.mk W h) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]) hdim1

  set φ : MvPolynomial (Fin n) O →+* (MvPolynomial (Fin n) O ⧸ W) ⧸ N₀ :=
    (Ideal.Quotient.mk N₀).comp (Ideal.Quotient.mk W) with hφ
  have hφs : Function.Surjective φ :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  set N := RingHom.ker φ with hNdef
  have hNp : N.IsPrime := RingHom.ker_isPrime φ
  have hmemN : ∀ a, a ∈ N ↔ Ideal.Quotient.mk W a ∈ N₀ := fun a => by
    simp [N, φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hWN : W ≤ N := fun a ha => (hmemN a).mpr (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact N₀.zero_mem)
  have hhN : h ∉ N := fun hh => hhN₀ ((hmemN h).mp hh)
  have hdimN : ringKrullDim (MvPolynomial (Fin n) O ⧸ N) + 1 =
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) := by
    rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφs)]
    exact hdimN₀
  have hNW : ¬ N ≤ W := by
    intro hle
    have hN₀bot : N₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (hle ((hmemN a).mpr hx)))
    subst hN₀bot
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at hdimN₀
    obtain ⟨m, hm, -⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
      (k := O ⧸ v.asIdeal) (A := MvPolynomial (Fin n) O ⧸ W)
    rw [hm] at hdimN₀
    have : ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞) := by push_cast; exact hdimN₀
    have : m + 1 = m := by exact_mod_cast this
    omega

  have hNQ : ∀ Q ∈ (P ⊔ vX).minimalPrimes, ¬ N ≤ Q := fun Q hQ hle =>
    hNW (hle.trans (hQ.2 ⟨hWp, hW.le⟩ (hWN.trans hle)))
  obtain ⟨f, hfN, hfQ⟩ : ∃ f ∈ N, ∀ Q ∈ (P ⊔ vX).minimalPrimes, f ∉ Q := by
    have hns : ¬ ((N : Set (MvPolynomial (Fin n) O)) ⊆
        ⋃ Q ∈ (↑hfin.toFinset : Set (Ideal (MvPolynomial (Fin n) O))), ((id Q : Ideal _) : Set _)) := by
      rw [Ideal.subset_union_prime (f := id) ⊥ ⊥
        (fun Q hQ _ _ => (hfin.mem_toFinset.mp hQ).isPrime)]
      rintro ⟨Q, hQ, hle⟩
      exact hNQ Q (hfin.mem_toFinset.mp hQ) hle
    obtain ⟨f, hfN, hf⟩ := Set.not_subset.mp hns
    refine ⟨f, hfN, fun Q hQ hfQ => hf ?_⟩
    exact Set.mem_biUnion (Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hQ)) hfQ
  have hfW : f ∉ W := hfQ W hW
  have hfP : f ∉ P := fun hf => hfW (hPW hf)

  have hPfN : P ⊔ Ideal.span {f} ≤ N :=
    sup_le (hPW.trans hWN) ((Ideal.span_singleton_le_iff_mem _).mpr hfN)
  obtain ⟨P', hP', hP'N⟩ := Ideal.exists_minimalPrimes_le hPfN
  have hP'p : P'.IsPrime := hP'.isPrime
  have hPP' : P ≤ P' := le_sup_left.trans hP'.le
  have hfP' : f ∈ P' := hP'.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hQN : ∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≤ N → Q = W := fun Q hQ hle => by
    by_contra hne
    exact hhN (hle (hhQ Q hQ hne))
  have hPltW : P < W := lt_of_le_of_ne hPW fun hPW' => v.ne_bot (by
    rw [eq_bot_iff, ← hPC, hPW']
    exact Ideal.map_le_iff_le_comap.mp hvW)
  have hvP' : ¬ vX ≤ P' := by
    intro hle
    obtain ⟨Q, hQ, hQP'⟩ := Ideal.exists_minimalPrimes_le (sup_le hPP' hle)
    rw [hQN Q hQ (hQP'.trans hP'N)] at hQP'
    rcases hQP'.lt_or_eq with hlt | heq
    · exact not_lt_of_mem_minimalPrimes_sup_span hPltW hP' hlt
    · exact hfW (heq ▸ hfP')
  have hP'C : P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ := by
    by_contra hne
    have hmax : (P'.comap (C : O →+* MvPolynomial (Fin n) O)).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hne
    have heq : P'.comap (C : O →+* MvPolynomial (Fin n) O) = N.comap C :=
      hmax.eq_of_le (Ideal.comap_ne_top _ hNp.ne_top) (Ideal.comap_mono hP'N)
    apply hvP'
    rw [hvX, Ideal.map_le_iff_le_comap, heq]
    exact Ideal.map_le_iff_le_comap.mp (hvW.trans hWN)

  obtain ⟨W', hW', hW'N⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hP'N (hvW.trans hWN) : P' ⊔ vX ≤ N)
  have : W'.IsPrime := hW'.isPrime
  have hWW' : W ≤ W' := by
    obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le
      (sup_le (hPP'.trans (le_sup_left.trans hW'.le)) (le_sup_right.trans hW'.le) : P ⊔ vX ≤ W')
    rw [← hQN Q hQ (hQW'.trans hW'N)]
    exact hQW'
  have hfW' : f ∈ W' := hW'.le (Ideal.mem_sup_left hfP')
  refine ⟨P', W', f, hfP, hP', hP'C, hW', le_antisymm ?_ ?_⟩
  · have hne : W'.map (Ideal.Quotient.mk W) ≠ ⊥ := by
      intro hb
      apply hfW
      have hm : Ideal.Quotient.mk W f ∈ W'.map (Ideal.Quotient.mk W) := Ideal.mem_map_of_mem _ hfW'
      rw [hb, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hm
      exact hm
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne
    rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hWW')] at h2
  · rw [← hdimN]
    exact add_le_add (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW'N)
      (Ideal.Quotient.factor_surjective hW'N)) le_rfl

end GroundTheory.Heights₂.Heights.Vertical
end

