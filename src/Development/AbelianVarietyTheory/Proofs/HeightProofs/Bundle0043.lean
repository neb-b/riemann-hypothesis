module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompleteSplittingCompositumDegreeOnePrime
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.SplitCompositum

theorem ncard_over_congr {K M M' : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field M']
    [NumberField M'] [Algebra K M] [Algebra K M'] (e : M ≃ₐ[K] M') (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {Q : HeightOneSpectrum (𝓞 M') | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M')) = 𝔭.asIdeal}.ncard =
      {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard := by
  classical
  let φ : 𝓞 M ≃+* 𝓞 M' := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
  have hφ : ∀ x : 𝓞 K, φ (algebraMap (𝓞 K) (𝓞 M) x) = algebraMap (𝓞 K) (𝓞 M') x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    show e (algebraMap (𝓞 M) M (algebraMap (𝓞 K) (𝓞 M) x)) = algebraMap (𝓞 M') M' (algebraMap (𝓞 K) (𝓞 M') x)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) K M, IsScalarTower.algebraMap_apply (𝓞 K) K M']
    exact e.commutes _
  have hcomp : ∀ I : Ideal (𝓞 M'),
      (I.comap φ).comap (algebraMap (𝓞 K) (𝓞 M)) = I.comap (algebraMap (𝓞 K) (𝓞 M')) := by
    intro I
    ext x
    simp only [Ideal.mem_comap]
    rw [hφ]
  refine Set.ncard_congr (fun Q _ => (⟨Q.asIdeal.comap φ, Ideal.comap_isPrime φ Q.asIdeal, fun h => Q.ne_bot (by
      have h' := congrArg (Ideal.map φ) h
      rwa [Ideal.map_comap_of_surjective φ φ.surjective, Ideal.map_bot] at h')⟩ : HeightOneSpectrum (𝓞 M)))
    ?_ ?_ ?_
  · intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ ⊢
    rw [hcomp, hQ]
  · intro Q₁ Q₂ _ _ h
    apply HeightOneSpectrum.ext
    have h' := congrArg HeightOneSpectrum.asIdeal h
    exact Ideal.comap_injective_of_surjective φ φ.surjective h'
  · intro Q hQ
    refine ⟨⟨Q.asIdeal.comap φ.symm, Ideal.comap_isPrime φ.symm Q.asIdeal, fun h => Q.ne_bot (by
      have h' := congrArg (Ideal.map φ.symm) h
      rwa [Ideal.map_comap_of_surjective φ.symm φ.symm.surjective, Ideal.map_bot] at h')⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq] at hQ ⊢
      rw [← hQ, ← hcomp]
      congr 1
      ext x
      simp [Ideal.mem_comap]
    · apply HeightOneSpectrum.ext
      ext x
      simp [Ideal.mem_comap]

theorem ncard_eq_finrank_of_generated (K L M M' : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field M'] [NumberField M'] [Algebra K L] [Algebra K M] [Algebra L M'] [Algebra K M']
    [IsScalarTower K L M'] (f : M →ₐ[K] M')
    (hgen : ∀ (N : Type) [Field N] [Algebra L N] (g g' : M' →ₐ[L] N), (∀ x, g (f x) = g' (f x)) → g = g')
    (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : HeightOneSpectrum (𝓞 L))
    (hover : 𝔓.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal)
    (hnorm : Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal)
    (hsplit : {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard =
      Module.finrank K M) :
    {Q : HeightOneSpectrum (𝓞 M') | Q.asIdeal.comap (algebraMap (𝓞 L) (𝓞 M')) = 𝔓.asIdeal}.ncard =
      Module.finrank L M' := by
  classical
  haveI : IsGalois K (AlgebraicClosure M') := IsAlgClosure.isGalois K _
  set N : IntermediateField K (AlgebraicClosure M') :=
    IntermediateField.normalClosure K M' (AlgebraicClosure M') with hN
  haveI : FiniteDimensional K N := normalClosure.is_finiteDimensional K M' (AlgebraicClosure M')
  haveI : IsGalois K N := IsGalois.normalClosure K M' (AlgebraicClosure M')
  haveI : IsScalarTower ℚ K N := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_ratCast (algebraMap ℚ N), eq_ratCast (algebraMap ℚ K), map_ratCast])
  haveI : FiniteDimensional ℚ N := Module.Finite.trans K N
  haveI : NumberField N := NumberField.mk
  letI : Algebra L N := ((algebraMap M' N).comp (algebraMap L M')).toAlgebra
  haveI : IsScalarTower L M' N := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap K N x = algebraMap M' N (algebraMap L M' (algebraMap K L x))
    rw [← IsScalarTower.algebraMap_apply K L M', ← IsScalarTower.algebraMap_apply K M' N])
  haveI : IsGalois L N := IsGalois.tower_top_of_isGalois K L N
  let ι : M' →ₐ[L] N := IsScalarTower.toAlgHom L M' N
  let g : M →ₐ[K] N := (IsScalarTower.toAlgHom K M' N).comp f
  have h1 : {Q : HeightOneSpectrum (𝓞 g.fieldRange) |
      Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 g.fieldRange)) = 𝔭.asIdeal}.ncard =
      Module.finrank K g.fieldRange := by
    rw [ncard_over_congr g.equivFieldRange 𝔭, hsplit]
    exact g.equivFieldRange.toLinearEquiv.finrank_eq
  have hfix1 := GlobalTheory.T.frobenius_fixes_of_splitsCompletely_intermediate K N g.fieldRange 𝔭 h1
  have hfix2 : ∀ σ : N ≃ₐ[L] N, GlobalTheory.NT.IsFrob N 𝔓 σ → ∀ x ∈ ι.fieldRange, σ x = x := by
    intro σ hσ
    have hK : GlobalTheory.NT.IsFrob N 𝔭 (σ.restrictScalars K) := by
      obtain ⟨P, hP, hPo, hx⟩ := hσ
      refine ⟨P, hP, ⟨?_⟩, ?_⟩
      · rw [← hover, hPo.over, Ideal.under, Ideal.under, Ideal.comap_comap,
          ← IsScalarTower.algebraMap_eq]
      · intro x
        rw [← hnorm]
        exact hx x
    have hM1 := hfix1 (σ.restrictScalars K) hK
    have hg : (σ.toAlgHom.comp ι) = ι := hgen N _ _ (fun x => by
      have := hM1 (g x) ⟨x, rfl⟩
      exact this)
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun h : M' →ₐ[L] N => h y) hg
  have h2 := GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix L N ι.fieldRange 𝔓 hfix2
  rw [← ncard_over_congr ι.equivFieldRange 𝔓, h2]
  exact ι.equivFieldRange.toLinearEquiv.finrank_eq.symm

theorem ncard_eq_finrank_adjoin : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] (h : K ≤ L) (S : Set ℂ) [NumberField (IntermediateField.adjoin K S)] [NumberField (IntermediateField.adjoin L S)] (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : HeightOneSpectrum (𝓞 L)), 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) = 𝔭.asIdeal → Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin K S)) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 (IntermediateField.adjoin K S))) = 𝔭.asIdeal}.ncard = Module.finrank K (IntermediateField.adjoin K S) → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin L S)) | Q.asIdeal.comap (algebraMap (𝓞 L) (𝓞 (IntermediateField.adjoin L S))) = 𝔓.asIdeal}.ncard = Module.finrank L (IntermediateField.adjoin L S) := by
  intro K L _ _ h S _ _ 𝔭 𝔓 hover hnorm hsplit
  letI : Algebra K L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  letI : Algebra K (IntermediateField.adjoin L S) :=
    ((algebraMap L (IntermediateField.adjoin L S)).comp (algebraMap K L)).toAlgebra
  haveI : IsScalarTower K L (IntermediateField.adjoin L S) := IsScalarTower.of_algebraMap_eq' rfl
  have hle : IntermediateField.adjoin K S ≤ (IntermediateField.adjoin L S).restrictScalars K :=
    IntermediateField.adjoin_le_iff.mpr (fun z hz => IntermediateField.subset_adjoin L S hz)
  let f : IntermediateField.adjoin K S →ₐ[K] IntermediateField.adjoin L S :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hgen : ∀ (N : Type) [Field N] [Algebra L N] (g g' : IntermediateField.adjoin L S →ₐ[L] N),
      (∀ x, g (f x) = g' (f x)) → g = g' := by
    intro N _ _ g g' hgg
    apply IntermediateField.adjoin_algHom_ext
    intro x hx
    exact hgg ⟨x, IntermediateField.subset_adjoin K S hx⟩
  have hover' : 𝔓.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal := by
    rw [← hover]
    rfl
  exact ncard_eq_finrank_of_generated K L (IntermediateField.adjoin K S) (IntermediateField.adjoin L S) f hgen
    𝔭 𝔓 hover' hnorm hsplit

end GlobalTheory.SplitCompositum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebra
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.TypeSum.CasBasis
variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_lieSet_iff_entry {X : Mx n} : X ∈ lieSet ε ↔
    ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0 := by
  simp only [lieSet, Set.mem_setOf_eq, inG, Jm]
  rw [← Matrix.ext_iff]
  simp [mul_diagonal, diagonal_mul, conjTranspose_apply]

theorem smul_unitE_diag_mem (a : Fin n) {c : ℂ} (hc : star c = -c) : c • unitE a a ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_sub_mem_same {a b : Fin n} (h : ε a = ε b) {c : ℂ} (hc : star c = c) :
    c • (unitE a b - unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_add_mem_same {a b : Fin n} (h : ε a = ε b) {c : ℂ} (hc : star c = -c) :
    c • (unitE a b + unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_add_mem_opp {a b : Fin n} (h : ε a ≠ ε b) {c : ℂ} (hc : star c = c) :
    c • (unitE a b + unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_sub_mem_opp {a b : Fin n} (h : ε a ≠ ε b) {c : ℂ} (hc : star c = -c) :
    c • (unitE a b - unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

theorem star_invSqrtTwo_mul_I : star (invSqrtTwo * Complex.I) = -(invSqrtTwo * Complex.I) := by
  simp [invSqrtTwo]

theorem kList_mem_lieSet {X : Mx n} (hX : X ∈ kList ε) : X ∈ lieSet ε := by
  simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hX
  rcases hX with ⟨a, -, rfl⟩ | ⟨p, hp, hX⟩
  · exact smul_unitE_diag_mem a (by simp [Complex.star_def])
  · have hs : ε p.1 = ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    rcases hX with rfl | rfl
    · exact smul_unitE_sub_mem_same hs star_invSqrtTwo
    · exact smul_unitE_add_mem_same hs star_invSqrtTwo_mul_I

theorem pList_mem_lieSet {X : Mx n} (hX : X ∈ pList ε) : X ∈ lieSet ε := by
  simp only [pList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hX
  obtain ⟨p, hp, hX⟩ := hX
  have hs : ε p.1 ≠ ε p.2 := by
    simp [pairs] at hp
    exact hp.2.2
  rcases hX with rfl | rfl
  · exact smul_unitE_add_mem_opp hs star_invSqrtTwo
  · exact smul_unitE_sub_mem_opp hs star_invSqrtTwo_mul_I

theorem bases_mem_lieSet : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε) ∧ ∀ b, pB ε b ∈ lieSet ε :=
  fun _ _ => ⟨fun i => kList_mem_lieSet (List.get_mem _ i), fun b => pList_mem_lieSet (List.get_mem _ b)⟩

end GlobalTheory.TypeSum.CasBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceHermitianOrthonormalBasisMulEqIte
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis.PB

variable {n : ℕ}

theorem tr_unit (a b c d : Fin n) :
    trace (unitE a b * unitE c d) = if b = c ∧ d = a then 1 else 0 := by
  by_cases hbc : b = c
  · subst hbc
    rw [unitE, unitE, Matrix.single_mul_single_same, one_mul]
    by_cases hda : d = a
    · subst hda; simp [Matrix.trace_single_eq_same]
    · rw [Matrix.trace_single_eq_of_ne (h := Ne.symm hda)]; simp [hda]
  · rw [unitE, unitE, Matrix.single_mul_single_of_ne _ _ _ _ hbc]; simp [hbc]

theorem sq_inv : invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  rw [invSqrtTwo, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

def B (X Y : Mx n) : ℝ := (trace (X * Y)).re

theorem B_comm (X Y : Mx n) : B X Y = B Y X := by
  simp only [B, Matrix.trace_mul_comm X Y]

def f (p : Fin n × Fin n) : List (Mx n) :=
  [invSqrtTwo • (unitE p.1 p.2 + unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 - unitE p.2 p.1)]

theorem pList_eq (ε : Fin n → Bool) : pList ε = (pairs ε false).flatMap f := rfl

theorem mem_pairs' {ε : Fin n → Bool} {p : Fin n × Fin n} (h : p ∈ pairs ε false) : p.1 < p.2 := by
  simp only [pairs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

theorem nodup_pairs (ε : Fin n → Bool) : (pairs ε false).Nodup :=
  (List.Nodup.product (List.nodup_finRange n) (List.nodup_finRange n)).filter _

theorem norm_one {a b : Fin n} (hab : a < b) : ∀ X ∈ f (a, b), B X X = 1 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  intro X hX
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_add, add_mul, Matrix.trace_add, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, sq_inv, smul_eq_mul]
    norm_num
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, Matrix.trace_sub, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
    have : invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = -(1 / 2 : ℂ) := by
      rw [show invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = invSqrtTwo * invSqrtTwo * (Complex.I * Complex.I) by ring,
        sq_inv, Complex.I_mul_I]; ring
    rw [this]; norm_num

theorem within {a b : Fin n} (hab : a < b) : (f (a, b)).Pairwise fun X Y => B X Y = 0 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  simp only [f, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, add_mul, Matrix.trace_sub, Matrix.trace_add, tr_unit,
    h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  simp

theorem across {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hne : (a, b) ≠ (c, d)) :
    ∀ X ∈ f (a, b), ∀ Y ∈ f (c, d), B X Y = 0 := by
  have e1 : ¬ (b = c ∧ d = a) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  have e2 : ¬ (b = d ∧ c = a) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e3 : ¬ (a = c ∧ d = b) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e4 : ¬ (a = d ∧ c = b) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  intro X hX Y hY
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX hY
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, mul_add, add_mul, Matrix.trace_sub,
    Matrix.trace_add, tr_unit, e1, e2, e3, e4, if_false, sub_zero, add_zero, smul_zero, Complex.zero_re]

theorem pairwise_pList (ε : Fin n → Bool) : (pList ε).Pairwise fun X Y => B X Y = 0 := by
  rw [pList_eq, List.pairwise_flatMap]
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨a, b⟩ := p
    exact within (mem_pairs' hp)
  · refine (nodup_pairs ε).imp_of_mem fun {p q} hp hq hne => ?_
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    exact across (mem_pairs' hp) (mem_pairs' hq) hne

theorem norm_pList (ε : Fin n → Bool) : ∀ X ∈ pList ε, B X X = 1 := by
  intro X hX
  rw [pList_eq, List.mem_flatMap] at hX
  obtain ⟨⟨a, b⟩, hp, hX⟩ := hX
  exact norm_one (mem_pairs' hp) X hX

end GlobalTheory.TypeSum.CasBasis.PB

namespace GlobalTheory.TypeSum.CasBasis

theorem pB_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length),
    (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := by
  intro n ε a b
  have hpw := List.pairwise_iff_get.1 (PB.pairwise_pList ε)
  show PB.B (pB ε a) (pB ε b) = _
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg h.ne]; exact hpw a b h
  · rw [if_pos rfl]; exact PB.norm_pList ε _ (List.get_mem _ _)
  · rw [if_neg h.ne', PB.B_comm]; exact hpw b a h

end GlobalTheory.TypeSum.CasBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceSkewHermitianMulHermitianOrthonormalBasis
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

namespace GlobalTheory.TypeSum.CasBasis

theorem unitE_apply_eq_zero_of_sign {n : ℕ} {ε : Fin n → Bool} {i j a b : Fin n}
    (h : (ε i = ε j) ≠ (ε a = ε b)) : unitE i j a b = 0 := by
  rw [unitE, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h rfl

theorem kList_entry_zero {n : ℕ} {ε : Fin n → Bool} {X : Mx n} (hX : X ∈ kList ε) {a b : Fin n}
    (hab : ε a ≠ ε b) : X a b = 0 := by
  unfold kList at hX
  rcases List.mem_append.1 hX with h | h
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 h
    have h1 : unitE c c a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab])
    simp only [Matrix.smul_apply, h1, smul_zero]
  · obtain ⟨p, hp, hX⟩ := List.mem_flatMap.1 h
    have hpe : ε p.1 = ε p.2 := by
      have := (List.mem_filter.1 hp).2
      simp at this
      exact this.2
    have h1 : unitE p.1 p.2 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    have h2 : unitE p.2 p.1 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem pList_entry_zero {n : ℕ} {ε : Fin n → Bool} {Y : Mx n} (hY : Y ∈ pList ε) {a b : Fin n}
    (hab : ε a = ε b) : Y a b = 0 := by
  unfold pList at hY
  obtain ⟨p, hp, hY⟩ := List.mem_flatMap.1 hY
  have hpe : ε p.1 ≠ ε p.2 := by
    have := (List.mem_filter.1 hp).2
    simp at this
    exact this.2
  have h1 : unitE p.1 p.2 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
  have h2 : unitE p.2 p.1 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, Ne.symm hpe])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
  rcases hY with rfl | rfl <;>
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem re_trace_kB_mul_pB : ∀ (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length),
    (trace (kB ε i * pB ε b)).re = 0 := by
  intro n ε i b
  have hX : kB ε i ∈ kList ε := List.get_mem _ _
  have hY : pB ε b ∈ pList ε := List.get_mem _ _
  have : trace (kB ε i * pB ε b) = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ε a = ε c
    · rw [pList_entry_zero hY h.symm, mul_zero]
    · rw [kList_entry_zero hX h, zero_mul]
  rw [this, Complex.zero_re]

end GlobalTheory.TypeSum.CasBasis
end

