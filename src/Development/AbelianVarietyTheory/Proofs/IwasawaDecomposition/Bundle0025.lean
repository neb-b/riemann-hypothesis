module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsQuasiFinitePolynomialMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamGeoEqFormula
section
namespace GlobalTheory.LowestKType

open Formalism.IndefR.IndefiniteWeightData Formalism.IndefR.IndefiniteWeightData.WeightData

variable {D : WeightData}

lemma r_eq (h : D.Hyp) : D.r = D.p + D.q := by
  obtain ⟨hk, hj, hjm, -⟩ := h
  unfold WeightData.r WeightData.p WeightData.q
  omega

lemma nV_eq (h : D.Hyp) : D.nV = D.p + D.q + D.t := by
  unfold WeightData.nV
  rw [r_eq h]

lemma nV_cast (h : D.Hyp) : (D.nV : ℚ) = D.p + D.q + D.t := by
  rw [nV_eq h]; push_cast; ring

lemma lam_tail (h : D.Hyp) (c : ℕ) : D.lam (D.p + c) = -D.b (D.j + c) := by
  obtain ⟨hk, hj, hjm, -⟩ := h
  unfold WeightData.lam WeightData.p
  rw [if_neg (by omega)]
  congr 2
  omega

lemma lam_step (h : D.Hyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.r) :
    (D.lam (i + 1) : ℚ) + 1 ≤ D.lam i := by
  have : D.lam (i + 1) + 1 ≤ D.lam i := h.2.2.2.2.2.1 i h1 h2
  exact_mod_cast this

lemma aMinus_rev (c : ℕ) (hc : c ≤ D.q + 1) :
    D.aMinus (D.q + 1 - c) = ((D.b (D.j + c) : ℚ) - D.e) + (1 - (D.t : ℚ) - 2 * (c : ℚ)) / 2 := by
  have : D.q + 1 - (D.q + 1 - c) = c := by omega
  unfold WeightData.aMinus
  rw [this]

lemma exists_half_r (h : D.Hyp) : ∃ u : ℕ, (D.q : ℚ) = 2 * u + 1 - D.p := by
  obtain ⟨u, hu⟩ := h.2.2.2.1
  rw [r_eq h] at hu
  have : (D.p : ℚ) + D.q = 2 * u + 1 := by exact_mod_cast hu
  exact ⟨u, by linarith⟩

lemma weightData_t_odd (h : D.Hyp) : ∃ w : ℕ, (D.t : ℚ) = 2 * w + 1 := by
  obtain ⟨u, hu⟩ := h.2.2.2.2.1
  exact ⟨u, by exact_mod_cast hu⟩

lemma aPlus_int (h : D.Hyp) (i : ℕ) : ∃ z : ℤ, D.aPlus i = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  obtain ⟨w, hw⟩ := weightData_t_odd h
  refine ⟨D.lam i + D.e - w - 1 + i - D.p, ?_⟩
  unfold WeightData.aPlus
  rw [nV_cast h, hu, hw]
  push_cast
  ring

lemma aMinus_int (h : D.Hyp) (s : ℕ) : ∃ z : ℤ, D.aMinus s = z := by
  obtain ⟨w, hw⟩ := weightData_t_odd h
  refine ⟨D.b (D.j + (D.q + 1 - s)) - D.e - w - ((D.q + 1 - s : ℕ) : ℤ), ?_⟩
  unfold WeightData.aMinus
  generalize D.q + 1 - s = c
  rw [hw]
  push_cast
  ring

lemma theta_param (h : D.Hyp) (i : ℕ) (h2 : i ≤ D.nV) :
    D.thetaWt i + ((D.p : ℚ) - D.q) / 2 - D.e + D.rhoNV i = D.uSideTarget i := by
  rw [nV_eq h] at h2
  unfold WeightData.thetaWt WeightData.rhoNV WeightData.uSideTarget
  by_cases hi : i ≤ D.p
  · simp only [if_pos hi]
    unfold WeightData.aPlus
    ring
  · by_cases hi' : i ≤ D.p + D.t
    · simp only [if_neg hi, if_pos hi']
      rw [nV_cast h]
      ring
    · obtain ⟨c, rfl⟩ : ∃ c, i = D.p + D.t + c := ⟨i - D.p - D.t, by omega⟩
      have e1 : D.p + D.t + c - D.p - D.t = c := by omega
      simp only [if_neg hi, if_neg hi', e1]
      rw [aMinus_rev c (by omega), nV_cast h]
      push_cast
      ring

lemma lamPrime_param (h : D.Hyp) (i : ℕ) (h2 : i ≤ D.nV) :
    D.lamPrime i + D.rhoNV i = D.uSideTarget i - 1 / 2 := by
  rw [← theta_param h i h2]
  unfold WeightData.lamPrime WeightData.dTau
  ring

lemma dTau_int (h : D.Hyp) : ∃ z : ℤ, D.dTau = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  refine ⟨D.p - u - 1 - D.e, ?_⟩
  unfold WeightData.dTau
  rw [hu]; push_cast; ring

lemma target_step (h : D.Hyp) (hg : D.GapHyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.nV) :
    D.uSideTarget (i + 1) + 1 ≤ D.uSideTarget i := by
  have hr := r_eq h
  rw [nV_eq h] at h2
  have ht : 1 ≤ D.t := h.2.2.2.2.1.pos
  unfold WeightData.uSideTarget
  rcases lt_trichotomy i D.p with hi | hi | hi
  · have a1 : i ≤ D.p := by omega
    have a2 : i + 1 ≤ D.p := by omega
    simp only [if_pos a1, if_pos a2]
    exact lam_step h i h1 (by omega)
  · subst hi
    have a2 : ¬ D.p + 1 ≤ D.p := by omega
    have a3 : D.p + 1 ≤ D.p + D.t := by omega
    have h4 := lam_tail h 0
    simp only [add_zero] at h4
    simp only [if_pos (le_refl D.p), if_neg a2, if_pos a3]
    rw [h4]
    have := hg.1
    push_cast
    linarith
  · have a1 : ¬ i ≤ D.p := by omega
    have a2 : ¬ i + 1 ≤ D.p := by omega
    simp only [if_neg a1, if_neg a2]
    rcases lt_trichotomy i (D.p + D.t) with hi' | hi' | hi'
    · have a3 : i ≤ D.p + D.t := by omega
      have a4 : i + 1 ≤ D.p + D.t := by omega
      simp only [if_pos a3, if_pos a4]
      push_cast
      linarith
    · subst hi'
      have a4 : ¬ D.p + D.t + 1 ≤ D.p + D.t := by omega
      have e1 : D.p + D.t + 1 - D.p - D.t = 1 := by omega
      have hq : D.q = D.m - D.j := rfl
      have := hg.2 (by omega)
      simp only [if_pos (le_refl (D.p + D.t)), if_neg a4, e1]
      push_cast
      linarith
    · have a3 : ¬ i ≤ D.p + D.t := by omega
      have a4 : ¬ i + 1 ≤ D.p + D.t := by omega
      simp only [if_neg a3, if_neg a4]
      obtain ⟨c, rfl⟩ : ∃ c, i = D.p + D.t + c := ⟨i - D.p - D.t, by omega⟩
      have e1 : D.p + D.t + c - D.p - D.t = c := by omega
      have e2 : D.p + D.t + c + 1 - D.p - D.t = c + 1 := by omega
      have h3 := lam_step h (D.p + c) (by omega) (by omega)
      rw [add_assoc, lam_tail h, lam_tail h] at h3
      rw [e1, e2]
      push_cast at h3
      linarith

theorem thetaSide : ThetaSideStatement := by
  intro D h hg
  refine ⟨fun i _ h2 => theta_param h i h2, fun i _ h2 => lamPrime_param h i h2, dTau_int h,
    ?_, ?_, ?_⟩
  · intro i _ _
    obtain ⟨d, hd⟩ := dTau_int h
    unfold WeightData.lamPrime WeightData.thetaWt
    rw [hd]
    split_ifs
    · obtain ⟨z, hz⟩ := aPlus_int h i
      exact ⟨z + d, by rw [hz]; push_cast; ring⟩
    · exact ⟨d, by ring⟩
    · obtain ⟨z, hz⟩ := aMinus_int h (D.q + 1 - (i - D.p - D.t))
      exact ⟨-z + d, by rw [hz]; push_cast; ring⟩
  · intro i h1 h2
    have h3 := target_step h hg i h1 h2
    have h4 := lamPrime_param h i h2.le
    have h5 := lamPrime_param h (i + 1) h2
    unfold WeightData.rhoNV at h4 h5
    push_cast at h5
    linarith
  · intro i h1 h2
    have h3 := target_step h hg i h1 h2
    rw [lamPrime_param h i h2.le, lamPrime_param h (i + 1) h2]
    linarith

end GlobalTheory.LowestKType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeElementaryDivisors
section
open IsDedekindDomain NumberField

namespace GlobalTheory.LatticeMinuscule

open Matrix

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}

open IsDedekindDomain NumberField in
open Matrix in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ} in
theorem _root_.GlobalTheory.LatticeMinuscule.lattice_elementary_divisors (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (Λ : Submodule R (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (a a' : Matrix (Fin n) (Fin n) K)
    (haa : a * a' = 1) (h1 : ∀ y ∈ Λ, a.mulVec y ∈ Λ)
    (h2 : ∀ y ∈ Λ, ∃ z ∈ Λ, algebraMap R K ϖ • y = a.mulVec z) (u : Rˣ)
    (hdet : a.det = algebraMap R K ϖ ^ k * algebraMap R K (u : R)) :
    ∃ B : Matrix (Fin n) (Fin n) K,
      (∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B.mulVec (fun i => algebraMap R K (z i))) ∧
      (∀ y, (∃ x ∈ Λ, y = a'.mulVec x) ↔ ∃ z : Fin n → R, y = B.mulVec (fun i =>
        algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖ0 : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  haveI : Module.Finite R Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free R Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R Λ
  have hli : LinearIndependent K (fun i => (b i : Fin n → K)) :=
    (LinearIndependent.iff_fractionRing R K).mp
      (b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ))
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R Λ) = n := by
    have hspan : ⊤ ≤ Submodule.span K (Set.range fun i => (b i : Fin n → K)) := by
      rw [← hsp, Submodule.span_le]
      intro x hx
      rw [← show ((⟨x, hx⟩ : Λ) : Fin n → K) = x from rfl, ← b.sum_repr ⟨x, hx⟩,
        Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, ← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  let b' := b.reindex (Fintype.equivFinOfCardEq hcard)
  let B0 : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (b' j : Fin n → K) i
  have key : ∀ z : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      ((b'.equivFun.symm z : Λ) : Fin n → K) := by
    intro z; ext i
    simp [B0, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Submodule.coe_sum,
      Finset.sum_apply, Algebra.smul_def, mul_comm]
  have memL : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B0 *ᵥ (fun i => algebraMap R K (z i)) := by
    intro y; constructor
    · intro hy; refine ⟨b'.equivFun ⟨y, hy⟩, ?_⟩; rw [key, LinearEquiv.symm_apply_apply]
    · rintro ⟨z, rfl⟩; rw [key]; exact Subtype.prop _
  have keyinj : ∀ z w : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      B0 *ᵥ (fun i => algebraMap R K (w i)) → z = w := by
    intro z w h; rw [key, key] at h; exact b'.equivFun.symm.injective (Subtype.coe_injective h)
  have hmap : ∀ (N : Matrix (Fin n) (Fin n) R) (z : Fin n → R),
      N.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (z i)) =
        fun i => algebraMap R K ((N *ᵥ z) i) := by
    intro N z; funext i; exact (RingHom.map_mulVec (algebraMap R K) N z i).symm
  have h1' : ∀ j, ∃ z : Fin n → R,
      a *ᵥ (b' j : Fin n → K) = B0 *ᵥ (fun i => algebraMap R K (z i)) :=
    fun j => (memL _).1 (h1 _ (b' j).2)
  choose zM hzM using h1'
  let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM j i
  have haB : a * B0 = B0 * M.map (algebraMap R K) := by
    ext i j
    have := congrFun (hzM j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, B0, M] using this
  have h2' : ∀ j, ∃ z : Fin n → R, algebraMap R K ϖ • (b' j : Fin n → K) =
      a *ᵥ (B0 *ᵥ (fun i => algebraMap R K (z i))) := by
    intro j
    obtain ⟨x, hx, hxe⟩ := h2 _ (b' j).2
    obtain ⟨z, rfl⟩ := (memL x).1 hx
    exact ⟨z, hxe⟩
  choose zM' hzM' using h2'
  let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM' j i
  have hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    have h := hzM' j
    rw [Matrix.mulVec_mulVec, haB, ← Matrix.mulVec_mulVec, hmap] at h
    have hl : algebraMap R K ϖ • (b' j : Fin n → K) =
        B0 *ᵥ (fun i => algebraMap R K ((ϖ • Pi.single j (1 : R) : Fin n → R) i)) := by
      rw [key, map_smul, Module.Basis.equivFun_symm_apply]
      simp [Pi.single_apply, algebraMap_smul]
    have h3 := congrFun (keyinj _ _ (hl.symm.trans h)) i
    rw [show (M * M') i j = (M *ᵥ zM' j) i from rfl, ← h3]
    simp [Matrix.one_apply, Pi.single_apply]
  have hsurj : Function.Surjective B0.mulVec := by
    intro y
    have hy : y ∈ Submodule.span K (Λ : Set (Fin n → K)) := hsp ▸ Submodule.mem_top
    have hle : Submodule.span K (Λ : Set (Fin n → K)) ≤ LinearMap.range (Matrix.mulVecLin B0) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hle hy
    exact ⟨w, hw⟩
  have hB0 : B0.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B0).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)).ne_zero
  have hdetM : Associated M.det (ϖ ^ k) := by
    have h := congrArg Matrix.det haB
    have hdm : (M.map (algebraMap R K)).det = algebraMap R K M.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, hdet, hdm, ← map_pow, ← map_mul] at h
    have h' := hinj (mul_left_cancel₀ hB0 h)
    exact ⟨u⁻¹, by rw [← h', mul_assoc, Units.mul_inv, mul_one]⟩
  obtain ⟨P, Q, hP, hQ, hMQ⟩ :=
    _root_.GlobalTheory.SmithBetween.smith_between R ϖ hϖ n k hk M M' hMM hdetM
  have haa' : a' * a = 1 := mul_eq_one_comm.mp haa
  have hE : ∀ z : Fin n → R, a *ᵥ ((B0 * Q.map (algebraMap R K)) *ᵥ (fun i =>
      algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) =
        B0 *ᵥ (fun i => algebraMap R K ((P *ᵥ z) i)) := by
    intro z
    have hdw : ((Matrix.diagonal fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ).map
        (algebraMap R K)) *ᵥ (fun i =>
          algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i)) =
        fun i => algebraMap R K (z i) := by
      rw [Matrix.diagonal_map (map_zero _)]
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hi : i.1 < n - k <;> simp [hi, hϖ0]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, haB, Matrix.mul_assoc, ← Matrix.map_mul, hMQ,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdw, hmap]
  refine ⟨B0 * Q.map (algebraMap R K), fun y => ?_, fun y => ?_⟩
  · rw [memL]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Q⁻¹ *ᵥ z, ?_⟩
      rw [← Matrix.mulVec_mulVec, hmap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hQ,
        Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      exact ⟨Q *ᵥ z, by rw [← Matrix.mulVec_mulVec, hmap]⟩
  · constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      refine ⟨P⁻¹ *ᵥ z, ?_⟩
      have h := hE (P⁻¹ *ᵥ z)
      have hz : P *ᵥ (P⁻¹ *ᵥ z) = z := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
      rw [hz] at h
      rw [← h, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      refine ⟨_, (memL _).2 ⟨P *ᵥ z, rfl⟩, ?_⟩
      rw [← hE z, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]

end GlobalTheory.LatticeMinuscule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalLocalIsLocalisationOfFiniteOverPolynomialA
section
open IsLocalRing

namespace GlobalTheory.QFNN

theorem integralClosure_of_fractions (P A : Type) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CharZero P] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Algebra P A] [Algebra.EssFiniteType P A]
    (hinj : Function.Injective (algebraMap P A))
    (hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b) :
    Module.Finite P (integralClosure P A) ∧ IsIntegrallyClosed (integralClosure P A) ∧
      Function.Injective (algebraMap P (integralClosure P A)) ∧
      IsLocalization.AtPrime A
        ((maximalIdeal A).comap (algebraMap (integralClosure P A) A)) := by
  let K := FractionRing A
  let F := FractionRing P
  let B := integralClosure P A
  have hιinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hPK : Function.Injective (algebraMap P K) := by
    rw [IsScalarTower.algebraMap_eq P A K]
    exact hιinj.comp hinj
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr hPK
  letI : Algebra F K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P F K := FractionRing.isScalarTower_liftAlgebra P K

  have halgA : ∀ a : A, IsAlgebraic P (algebraMap A K a) := by
    intro a
    obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
    have ht0 : algebraMap A K t ≠ 0 := by
      simpa using (map_ne_zero_iff _ hιinj).mpr hu.ne_zero
    have : algebraMap A K a = algebraMap A K b * (algebraMap A K t)⁻¹ := by
      rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    rw [this]
    exact (hb.algebraMap (B := K)).isAlgebraic.mul (ht.algebraMap (B := K)).isAlgebraic.inv
  haveI hPKalg : Algebra.IsAlgebraic P K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, s, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [div_eq_mul_inv]
    exact (halgA a).mul (halgA s).inv
  haveI : Algebra.IsAlgebraic F K := (IsFractionRing.comap_isAlgebraic_iff (A := P) (K := F)).mp hPKalg
  haveI : Algebra.EssFiniteType A K := .of_isLocalization K (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType P K := .comp P A K
  haveI : Algebra.EssFiniteType F K := .of_comp P F K
  haveI : FiniteDimensional F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective P F)
  haveI hic : IsIntegralClosure B P K :=
    { algebraMap_injective := hιinj.comp Subtype.val_injective
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := A))
          have ha : IsIntegral P a := (isIntegral_algebraMap_iff (A := A) (B := K)).mp hx
          exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact (y.2.algebraMap (B := K)) }
  haveI hfrac : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension P F K B
  refine ⟨IsIntegralClosure.finite P F K B, ?_, ?_, ?_⟩
  · refine (isIntegrallyClosed_iff K).mpr ?_
    intro x hx
    have hxP : IsIntegral P x := isIntegral_trans x hx
    exact (IsIntegralClosure.isIntegral_iff (A := B)).mp hxP
  · intro x y h
    exact hinj (congrArg Subtype.val h)
  · have hne : ∀ b : B, b ∈ ((maximalIdeal A).comap (algebraMap B A)).primeCompl →
        IsUnit (algebraMap B A b) := by
      intro b hb
      by_contra hu
      exact hb ((mem_maximalIdeal _).mpr hu)
    refine ⟨fun y => hne y.1 y.2, fun a => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
      refine ⟨(⟨b, hb⟩, ⟨⟨t, ht⟩, ?_⟩), hab⟩
      intro hmem
      exact (mem_maximalIdeal _).mp hmem hu
    · have : x = y := Subtype.val_injective h
      rw [this]

end GlobalTheory.QFNN

theorem GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B)
      (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B)
      (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime),
      Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  intro A _ _ _ _ _ hess
  obtain ⟨S₀, M, hft, hlocM⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ A).mp hess
  let 𝔮 : Ideal S₀ := (maximalIdeal A).comap (algebraMap S₀ A)
  haveI h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  have hunit : ∀ s : S₀, s ∉ 𝔮 → IsUnit (algebraMap S₀ A s) := by
    intro s hs
    by_contra hu
    exact hs ((mem_maximalIdeal _).mpr hu)
  have hM : M ≤ 𝔮.primeCompl := by
    intro m hm hmem
    exact (mem_maximalIdeal _).mp hmem (IsLocalization.map_units A ⟨m, hm⟩)
  haveI hat : IsLocalization 𝔮.primeCompl A :=
    IsLocalization.of_le M _ hM (fun s hs => hunit s hs)
  haveI : CharZero S₀ := (algebraMap S₀ A).charZero
  obtain ⟨r, y, hy, hqf⟩ := _root_.GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt S₀ 𝔮
  let P := MvPolynomial (Fin r) ℤ
  letI algPS : Algebra P S₀ := (MvPolynomial.aeval y : P →ₐ[ℤ] S₀).toRingHom.toAlgebra
  letI algPA : Algebra P A := ((algebraMap S₀ A).comp (algebraMap P S₀)).toAlgebra
  haveI : IsScalarTower P S₀ A := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ P S₀ := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsScalarTower ℤ P A := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType P S₀ := .of_restrictScalars_finiteType ℤ P S₀
  haveI : Algebra.EssFiniteType P A := .of_comp ℤ P A
  have hinj : Function.Injective (algebraMap P A) :=
    (Subtype.val_injective : Function.Injective (algebraMap S₀ A)).comp
      ((algebraicIndependent_iff_injective_aeval).mp hy)
  have hzmp : Algebra.ZariskisMainProperty P 𝔮 := Algebra.ZariskisMainProperty.of_finiteType 𝔮
  obtain ⟨ρ, hρq, hρ, H⟩ := Algebra.zariskisMainProperty_iff.mp hzmp
  have hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b := by
    intro a
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj 𝔮.primeCompl a
    obtain ⟨m₁, h₁⟩ := H x
    obtain ⟨m₂, h₂⟩ := H s
    have hb : IsIntegral P (ρ ^ (m₁ + m₂) * x) := by
      have : ρ ^ (m₁ + m₂) * x = ρ ^ m₂ * (ρ ^ m₁ * x) := by ring
      rw [this]
      exact (hρ.pow _).mul h₁
    have ht : IsIntegral P (ρ ^ (m₁ + m₂) * (s : S₀)) := by
      have : ρ ^ (m₁ + m₂) * (s : S₀) = ρ ^ m₁ * (ρ ^ m₂ * (s : S₀)) := by ring
      rw [this]
      exact (hρ.pow _).mul h₂
    refine ⟨_, _, hb.algebraMap (B := A), ht.algebraMap (B := A), hunit _ ?_, ?_⟩
    · exact h𝔮.mul_notMem (fun h => hρq (h𝔮.mem_of_pow_mem _ h)) s.2
    · simp only [map_mul, map_pow]
      rw [← hxs]
      ring
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.QFNN.integralClosure_of_fractions P A hinj hloc
  exact ⟨r, integralClosure P A, inferInstance, inferInstance, h2, inferInstance, h1, inferInstance,
    _, Ideal.comap_isPrime _ _, h3, h4⟩
end

