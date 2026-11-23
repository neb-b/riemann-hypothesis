module

public import Mathlib
public import GroundTheory.PAdicHodge.Bundle0001
public import GroundTheory.PAdicHodge.BdRSeries
public import GroundTheory.PowerSubgroups.CountableNeighbourhoods.Bundle0001
public import GroundTheory.PAdicHodge.GaloisOnCp

@[expose] public section

-- bundled from GroundTheory.PAdicHodge.HighIndexSingleZeroOne
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

structure AnnulusRing (I : Set ℝ) where

@[ext]
structure Robba where

  coeff : ℤ → K
  exists_convergesAt' : ∃ r < 1, ∀ ρ, r ≤ ρ → ρ < 1 → 0 < ρ → ConvergesAt coeff ρ

variable {K}

namespace AnnulusRing

variable {I : Set ℝ}

variable [hI : Fact (∃ ρ ∈ I, 0 < ρ)]

end AnnulusRing

namespace Robba

end Robba

namespace AnnulusRing

variable {r : ℝ} [Fact (r < 1)]

end AnnulusRing

namespace Robba

end Robba

namespace Laurent

end Laurent

namespace Robba

end Robba

namespace Laurent

end Laurent

namespace Robba

end Robba

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.LogMul
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.PowerSeries

section Formal

theorem exp_subst_log : (exp ℚ).subst (log ℚ) = (1 + X : ℚ⟦X⟧) :=
  PowerSeries.subst_exp_log ℚ

end Formal

section Nilpotent

variable {S : Type*} [CommRing S] [Algebra ℚ S]

theorem truncEval_pow_eq_zero {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧}
    (hg : constantCoeff g = 0) : (truncEval s hs g) ^ n = 0 := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.2 hg
  rw [← map_pow, mul_pow, map_mul, map_pow, truncEval_X, hs, zero_mul]

theorem truncEval_subst {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0)
    (f : ℚ⟦X⟧) :
    truncEval s hs (f.subst g) = truncEval (truncEval s hs g) (truncEval_pow_eq_zero hs hg) f := by
  have hS := HasSubst.of_constantCoeff_zero' hg
  have key := truncEval_unique ((truncEval s hs).comp (substAlgHom hS)) (truncEval s hs g)
    (truncEval_pow_eq_zero hs hg) (by rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hS])
  rw [← key, AlgHom.comp_apply, coe_substAlgHom]

theorem truncEval_exp {n : ℕ} {s : S} (hs : s ^ n = 0) :
    truncEval s hs (exp ℚ) = IsNilpotent.exp s := by
  rw [truncEval_eq_sum, IsNilpotent.exp_eq_sum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_exp, Algebra.smul_def, one_div]
  simp

theorem isNilpotent_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent (truncEval s hs (log ℚ)) :=
  ⟨n, truncEval_pow_eq_zero hs constantCoeff_log⟩

theorem exp_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent.exp (truncEval s hs (log ℚ)) = 1 + s := by
  rw [← truncEval_exp (truncEval_pow_eq_zero hs constantCoeff_log),
    ← truncEval_subst hs (g := log ℚ) constantCoeff_log,
    exp_subst_log, map_add, map_one, truncEval_X]

theorem eq_zero_of_exp_eq_one {c : S} (hc : IsNilpotent c) (h : IsNilpotent.exp c = 1) : c = 0 := by
  obtain ⟨k, hk⟩ := hc
  set w : S := ∑ i ∈ Finset.range k, ((i + 1).factorial : ℚ)⁻¹ • c ^ i with hw
  have hexp : IsNilpotent.exp c = 1 + c * w := by
    rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ',
      hw, Finset.mul_sum]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, pow_succ, mul_comm c]
  have hw1 : IsUnit w := by
    rcases k with _ | k
    · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hk.symm)
      exact isUnit_of_subsingleton w
    · have hsplit : w = 1 + c * ∑ i ∈ Finset.range k, ((i + 2).factorial : ℚ)⁻¹ • c ^ i := by
        rw [hw, Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, pow_succ, mul_comm c]
      rw [hsplit]
      exact IsNilpotent.isUnit_one_add ⟨k + 1, by rw [mul_pow, hk, zero_mul]⟩
  have h0 : c * w = 0 := by
    have := hexp.symm.trans h
    rwa [add_eq_left] at this
  simpa using (hw1.mul_left_eq_zero).1 h0

theorem eq_of_exp_eq {a b : S} (ha : IsNilpotent a) (hb : IsNilpotent b)
    (h : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hnb : IsNilpotent (-b) := hb.neg
  have h1 : IsNilpotent.exp (a + -b) = 1 := by
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) ha hnb, h,
      IsNilpotent.exp_mul_exp_neg_self hb]
  have h2 := eq_zero_of_exp_eq_one (Commute.isNilpotent_add (Commute.all _ _) ha hnb) h1
  rw [← sub_eq_add_neg, sub_eq_zero] at h2
  exact h2

theorem truncEval_log_mul {l m n : ℕ} {x y z : S} (hx : x ^ l = 0) (hy : y ^ m = 0)
    (hz : z ^ n = 0) (hxyz : 1 + z = (1 + x) * (1 + y)) :
    truncEval z hz (log ℚ) = truncEval x hx (log ℚ) + truncEval y hy (log ℚ) := by
  have hnx := isNilpotent_truncEval_log hx
  have hny := isNilpotent_truncEval_log hy
  apply eq_of_exp_eq (isNilpotent_truncEval_log hz) (Commute.isNilpotent_add (Commute.all _ _) hnx hny)
  rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hny, exp_truncEval_log,
    exp_truncEval_log, exp_truncEval_log, hxyz]

end Nilpotent

section Complete

variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]

theorem mk_seriesEval_eq_truncEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (seriesEval I z hz f) =
      truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n) f :=
  IsAdicComplete.mk_liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle) n f

theorem logOnePlus_mul {x y z : B} (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I)
    (hxyz : 1 + z = (1 + x) * (1 + y)) :
    logOnePlus I z hz = logOnePlus I x hx + logOnePlus I y hy := by
  refine eq_of_forall_sub_mem_pow I fun n => ?_
  rw [← Ideal.Quotient.eq, map_add (f := _), logOnePlus, logOnePlus, logOnePlus,
    mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval]
  exact truncEval_log_mul _ _ _ (by rw [← map_one (Ideal.Quotient.mk (I ^ n)), ← map_add (f := _), hxyz,
    map_mul, map_add, map_add, map_one])

end Complete

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.SlopeCauchyBinet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Matrix Finset Equiv

abbrev KSubset (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n := s.1.orderEmbOfFin s.2

theorem KSubset.range_emb {n k : ℕ} (s : KSubset n k) : Set.range s.emb = (s.1 : Set (Fin n)) :=
  Finset.range_orderEmbOfFin _ _

variable {R : Type*} [CommRing R]

section CauchyBinet

variable {k n : ℕ}

private theorem det_mul_eq_sum_fun (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ p : Fin k → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id, sum_mul, prod_mul_distrib, mul_assoc]
  rw [Finset.sum_comm]

theorem det_mul_eq_sum_minors (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det := by
  classical
  set F : (Fin k → Fin n) → R := fun p => (A.submatrix id p).det * ∏ i, B (p i) i with hF
  have hzero : ∀ p, ¬ Function.Injective p → F p = 0 := by
    intro p hp
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hp
      obtain ⟨i, j, h, hne⟩ := hp
      exact ⟨i, j, h, hne⟩
    simp only [hF]
    rw [det_zero_of_column_eq hne (fun r => by simp [hij]), zero_mul]
  have hterm : ∀ (s : KSubset n k) (σ : Perm (Fin k)),
      F (s.emb ∘ σ) = (A.submatrix id s.emb).det * (Perm.sign σ * ∏ i, B (s.emb (σ i)) i) := by
    intro s σ
    simp only [hF]
    have : A.submatrix id (s.emb ∘ σ) = (A.submatrix id s.emb).submatrix id σ := rfl
    rw [this, det_permute']
    simp only [Function.comp_apply]
    ring
  have hs : ∀ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det =
      ∑ σ : Perm (Fin k), F (s.emb ∘ σ) := by
    intro s
    simp only [hterm, ← mul_sum]
    congr 1
    rw [det_apply']
    rfl
  have hprod := Fintype.sum_prod_type (fun x : KSubset n k × Perm (Fin k) => F (x.1.emb ∘ x.2))
  simp only at hprod
  rw [det_mul_eq_sum_fun, Finset.sum_congr rfl (fun s _ => hs s)]
  change ∑ p, F p = _
  rw [← hprod, ← Finset.sum_filter_of_ne (p := Function.Injective) (fun p _ h => by
      by_contra hp; exact h (hzero p hp))]
  symm
  refine Finset.sum_bij (fun x _ => x.1.emb ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.1.emb.injective.comp x.2.injective
  · rintro ⟨s, σ⟩ _ ⟨t, τ⟩ _ h
    simp only at h
    have hst : s = t := by
      apply Subtype.ext
      have h1 : Set.range (s.emb ∘ σ) = Set.range (t.emb ∘ τ) := by rw [h]
      rw [Set.range_comp, Set.range_comp, σ.range_eq_univ, τ.range_eq_univ, Set.image_univ,
        Set.image_univ, KSubset.range_emb, KSubset.range_emb] at h1
      exact_mod_cast h1
    subst hst
    have : σ = τ := by
      ext i
      have := congrFun h i
      simp only [Function.comp_apply] at this
      exact congrArg Fin.val (s.emb.injective this)
    rw [this]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hcard : (Finset.univ.image p).card = k := by
      rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin]
    let s : KSubset n k := ⟨Finset.univ.image p, hcard⟩
    have hex : ∀ i, ∃ j, s.emb j = p i := by
      intro i
      have : p i ∈ (s.1 : Set (Fin n)) := by simp [s]
      rw [← KSubset.range_emb] at this
      exact this
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro i j hij
      apply hp
      rw [← hf i, ← hf j, hij]
    let σ : Perm (Fin k) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
    refine ⟨(s, σ), Finset.mem_univ _, ?_⟩
    funext i
    exact hf i
  · intro x _
    rfl

end CauchyBinet

section Minors

variable {m n k : ℕ}

def maxMinor (B : Matrix (Fin n) (Fin k) R) (s : KSubset n k) : R :=
  (B.submatrix s.emb id).det

end Minors

section Independence

variable {n k : ℕ}

theorem linearIndependent_col_iff_mulVec_eq_zero (B : Matrix (Fin n) (Fin k) R) :
    LinearIndependent R B.col ↔ ∀ v, B *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  have key : ∀ v : Fin k → R, ∑ j, v j • B.col j = B *ᵥ v := by
    intro v; ext i; simp [mulVec, dotProduct, Finset.sum_apply, col, mul_comm]
  constructor
  · intro h v hv
    funext j
    exact h v (by rw [key, hv]) j
  · intro h g hg j
    have := h g (by rw [← key, hg])
    exact congrFun this j

theorem exists_maxMinor_ne_zero_of_linearIndependent [IsDomain R]
    (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 :=
  _root_.GroundTheory.Variant₂.N1.exists_maxMinor_ne_zero_of_linearIndependent_alt B hB

end Independence

end GroundTheory.PAdicHodge
end

-- bundled from GroundTheory.PAdicHodge.TateCpTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open UniformSpace

variable {p : ℕ} [Fact p.Prime]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem algebraMap_intermediateField_cp (k : K) :
    algebraMap K ℂ_[p] k = ((k : PadicAlgCl p) : ℂ_[p]) := rfl

theorem gal_smul_algebraMap_intermediateField (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • algebraMap K ℂ_[p] k = algebraMap K ℂ_[p] k :=
  gal_smul_coe_of_mem σ k

theorem gal_smul_smul_intermediateField (σ : Gal(PadicAlgCl p/K)) (k : K) (x : ℂ_[p]) :
    σ • (k • x) = k • (σ • x) := by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', gal_smul_algebraMap_intermediateField]

noncomputable def cycloChar : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut Gal(PadicAlgCl p/K) (PadicAlgCl p))

theorem continuous_cycloChar : Continuous (cycloChar K) :=
  cyclotomicCharacter.continuous p K (PadicAlgCl p)

theorem cycloChar_spec (σ : Gal(PadicAlgCl p/K)) {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ p ^ n = 1) :
    σ ζ = ζ ^ ((cycloChar K σ : ℤ_[p]).toZModPow n).val :=
  cyclotomicCharacter.spec p (MulSemiringAction.toRingAut Gal(PadicAlgCl p/K) (PadicAlgCl p) σ) ζ hζ

noncomputable def twistScalar (j : ℤ) (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] :=
  algebraMap ℚ_[p] ℂ_[p] (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])

theorem twistScalar_one (j : ℤ) : twistScalar K j 1 = 1 := by
  simp [twistScalar]

theorem twistScalar_mul (j : ℤ) (σ τ : Gal(PadicAlgCl p/K)) :
    twistScalar K j (σ * τ) = twistScalar K j σ * twistScalar K j τ := by
  simp only [twistScalar, map_mul, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem twistScalar_zero (σ : Gal(PadicAlgCl p/K)) : twistScalar K 0 σ = 1 := by
  simp [twistScalar]

theorem gal_smul_twistScalar (j : ℤ) (σ τ : Gal(PadicAlgCl p/K)) :
    σ • twistScalar K j τ = twistScalar K j τ :=
  gal_smul_algebraMap σ _

noncomputable def cpTwistMap (j : ℤ) (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] →L[K] ℂ_[p] where
  toFun x := twistScalar K j σ * (σ • x)
  map_add' x y := by rw [smul_add, mul_add]
  map_smul' k x := by
    rw [gal_smul_smul_intermediateField, RingHom.id_apply, mul_smul_comm]
  cont := continuous_const.mul (continuous_const_smul σ)

theorem cpTwistMap_apply (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    cpTwistMap K j σ x = twistScalar K j σ * (σ • x) := rfl

noncomputable def cpTwistRep (j : ℤ) : ContRepresentation K Gal(PadicAlgCl p/K) ℂ_[p] :=
  .ofMonoidHom
    { toFun := cpTwistMap K j
      map_one' := by
        ext x
        simp [cpTwistMap_apply, twistScalar_one]
      map_mul' := fun σ τ => by
        ext x
        change cpTwistMap K j (σ * τ) x = cpTwistMap K j σ (cpTwistMap K j τ x)
        simp only [cpTwistMap_apply, twistScalar_mul, smul_mul', gal_smul_twistScalar, mul_smul]
        ring }

theorem cpTwistRep_apply (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    cpTwistRep K j σ x = twistScalar K j σ * (σ • x) := rfl

end GroundTheory.PAdicHodge
end

