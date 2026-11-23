module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvaluesOfNewton
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDiagOfLower
section
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.IwahoriRoots

open IsDedekindDomain

section Val

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
  [Algebra O E] [IsFractionRing O E]

theorem valuation_unif (ϖ : O) (hϖ : Irreducible ϖ) :
    (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E ϖ) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)

theorem valuation_of_isUnit {u : O} (hu : IsUnit u) :
    (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E u) = 1 := by
  obtain ⟨u, rfl⟩ := hu
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  set v := IsDiscreteValuationRing.maximalIdeal O
  have h1 := v.intValuation_le_one (u : O)
  have h2 := v.intValuation_le_one ((u⁻¹ : Oˣ) : O)
  have h3 : v.intValuation (u : O) * v.intValuation ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = v.intValuation (u : O) * v.intValuation ((u⁻¹ : Oˣ) : O) := h3.symm
    _ ≤ v.intValuation (u : O) * 1 := by gcongr
    _ = v.intValuation (u : O) := mul_one _

end Val

theorem isUnit_diag_of_lower {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (x : GL (Fin n) O)
    (hx : ∀ i j, j < i → (x : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O)
    (i : Fin n) : IsUnit ((x : Matrix (Fin n) (Fin n) O) i i) := by
  have h1 : ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).BlockTriangular id := by
    intro a b hab
    simp only [Matrix.map_apply]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (hx a b hab)
  have h2 : IsUnit ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).det := by
    have e : ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).det =
        IsLocalRing.residue O (x : Matrix (Fin n) (Fin n) O).det := (RingHom.map_det _ _).symm
    rw [e]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).map _
  rw [Matrix.det_of_upperTriangular h1] at h2
  have h3 := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) h2
  simp only [Matrix.map_apply] at h3
  exact isUnit_of_map_unit (IsLocalRing.residue O) _ h3

theorem iwahori_roots : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O), Irreducible ϖ →
    ∀ (n : ℕ) (a : Fin n → ℤ), StrictAnti a → ∀ x y : GL (Fin n) O,
    (∀ i j, j < i → (x : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O) →
    (∀ i j, j < i → (y : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O) →
    ∃ r : Fin n → E, (∀ i, r i ≠ 0 ∧ val O (r i) = a i) ∧
      ((x : Matrix (Fin n) (Fin n) O).map (algebraMap O E) *
        Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) *
        (y : Matrix (Fin n) (Fin n) O).map (algebraMap O E)).charpoly = ∏ i, (X - C (r i)) := by
  intro O _ _ _ _ E _ _ _ _ ϖ hϖ n a ha x y hx hy
  have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hm : ϖ ∈ IsLocalRing.maximalIdeal O := by rw [hspan]; exact Ideal.mem_span_singleton_self ϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) O := by rw [← hspan]; infer_instance
  have hinj : Function.Injective (algebraMap O E) := IsFractionRing.injective O E
  have hϖ0 : algebraMap O E ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨N, hNa⟩ : ∃ N : ℤ, ∀ i, N ≤ a i := by
    obtain ⟨N, hN⟩ := (Set.finite_range a).bddBelow
    exact ⟨N, fun i => hN ⟨i, rfl⟩⟩
  let b : Fin n → ℕ := fun i => (a i - N).toNat
  have hab : ∀ i, a i = N + b i := fun i => by
    have := hNa i
    simp only [b]
    omega
  have hb : StrictAnti b := fun i j h => by
    have := ha h
    rw [hab, hab] at this
    omega
  have hdvd : ∀ z : O, z ∈ IsLocalRing.maximalIdeal O → ϖ ∣ z := fun z hz => by
    rw [hspan] at hz
    exact Ideal.mem_span_singleton.1 hz
  set G : Matrix (Fin n) (Fin n) O :=
    (x : Matrix (Fin n) (Fin n) O) * Matrix.diagonal (fun i => ϖ ^ b i) * y with hG
  have hroot := GlobalTheory.IwahoriEigen.exists_root_of_coeff ϖ hm hb G.charpoly
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) (fun j hj => by
      have := GlobalTheory.IwahoriNewtonTest.intersectionNumber_baseChange O ϖ hm n b hb x y (isUnit_diag_of_lower x hx)
        (isUnit_diag_of_lower y hy) (fun i j h => hdvd _ (hx i j h)) (fun i j h => hdvd _ (hy i j h))
        (n - j) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hj] at this)
  choose z hz hzr using hroot
  set M : Matrix (Fin n) (Fin n) E := (x : Matrix (Fin n) (Fin n) O).map (algebraMap O E) *
    Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) *
    (y : Matrix (Fin n) (Fin n) O).map (algebraMap O E) with hM
  have hMG : M = algebraMap O E ϖ ^ N • G.map (algebraMap O E) := by
    have : Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) =
        algebraMap O E ϖ ^ N • (Matrix.diagonal (fun i => ϖ ^ b i)).map (algebraMap O E) := by
      rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_smul]
      congr 1
      funext i
      rw [hab, zpow_add₀ hϖ0]
      simp
    rw [hM, this, hG, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul]
  let r : Fin n → E := fun i => algebraMap O E ϖ ^ N * algebraMap O E (ϖ ^ b i * z i)
  have hr0 : ∀ i, r i ≠ 0 := fun i =>
    mul_ne_zero (zpow_ne_zero _ hϖ0) ((map_ne_zero_iff _ hinj).2
      (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) (hz i).ne_zero))
  have hv : ∀ i, (IsDiscreteValuationRing.maximalIdeal O).valuation E (r i) =
      WithZero.exp (-(a i)) := fun i => by
    simp only [r, map_mul, map_pow, map_zpow₀, valuation_unif ϖ hϖ, valuation_of_isUnit (hz i), mul_one]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, hab]
    congr 1
    simp
    ring
  have hval : ∀ i, val O (r i) = a i := fun i => by
    simp only [val, hv i, WithZero.log_exp, neg_neg]
  have hrinj : Function.Injective r := fun i j h => by
    have h1 := hval i
    rw [h, hval j] at h1
    exact ha.injective h1.symm
  have hrt : ∀ i, M.charpoly.IsRoot (r i) := fun i => by
    have h1 : ((G.map (algebraMap O E)).charpoly).IsRoot (algebraMap O E (ϖ ^ b i * z i)) := by
      rw [Matrix.charpoly_map]
      exact Polynomial.IsRoot.map (algebraMap O E) (hzr i)
    rw [IsRoot.def, Matrix.eval_charpoly] at h1 ⊢
    have : Matrix.scalar (Fin n) (r i) - M = algebraMap O E ϖ ^ N •
        (Matrix.scalar (Fin n) (algebraMap O E (ϖ ^ b i * z i)) - G.map (algebraMap O E)) := by
      rw [hMG, smul_sub]
      congr 1
      rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
      rfl
    rw [this, Matrix.det_smul, h1, mul_zero]
  refine ⟨r, fun i => ⟨hr0 i, hval i⟩, ?_⟩
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C _ _) M.charpoly_monic ?_ ?_
  · exact Finset.prod_dvd_of_coprime
      (fun i _ j _ h => pairwise_coprime_X_sub_C hrinj h) fun i _ => dvd_iff_isRoot.2 (hrt i)
  · rw [Matrix.charpoly_natDegree_eq_dim, natDegree_finsetProd_X_sub_C_eq_card]
    simp

end GlobalTheory.IwahoriRoots
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieLatticeProdComapInlAndMapSnd
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.LinPair

theorem exists_smul_mem_of_mem_span (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] (M : Submodule K.O V) {x : V} (hx : x ∈ Submodule.span K.E (M : Set V)) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.ClearDenominatorsIntegral.main
  | exact _root_.GlobalTheory.ClearDenominatorsIntegral.main
  | (apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClearDenominatorsIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClearDenominatorsIntegral.main ..)

end GlobalTheory.UnitLemma.LinPair

open GlobalTheory.UnitLemma.LinPair in
theorem GlobalTheory.UnitLemma.InvAlg.lin_fst_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)),
    M ∈ (B₁.prod B₂).Lin →
    M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  intro K B₁ B₂ M hM
  obtain ⟨⟨hfg, hspan⟩, hg, hσ⟩ := hM
  have hg' : ∀ y ∈ M, ((B₁.g * y.1, B₂.g * y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hg y hy
  have hσ' : ∀ y ∈ M, ((B₁.σ y.1, B₂.σ y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hσ y hy
  replace hspan : Submodule.span K.E (M : Set (B₁.A × B₂.A)) = ⊤ := hspan
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩⟩
  ·
    apply Submodule.fg_of_fg_map_injective (LinearMap.inl K.O B₁.A B₂.A) LinearMap.inl_injective
    exact isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian M hfg) _ (Submodule.map_comap_le _ _)
  · rw [Submodule.eq_top_iff']
    intro y
    have hy : (y, (0 : B₂.A)) ∈ Submodule.span K.E (M : Set (B₁.A × B₂.A)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨d, hd, hdy⟩ := exists_smul_mem_of_mem_span K M hy
    have hdE : algebraMap K.O K.E d ≠ 0 := by
      rw [Ne, ← (algebraMap K.O K.E).map_zero]
      exact fun h => hd (IsFractionRing.injective K.O K.E h)
    have hmem : d • y ∈ M.comap (LinearMap.inl K.O B₁.A B₂.A) := by
      simpa [Submodule.mem_comap] using hdy
    refine (Submodule.smul_mem_iff _ hdE).mp ?_
    rw [algebraMap_smul]
    exact Submodule.subset_span hmem
  · intro y hy
    have := hg' _ hy
    simpa [Submodule.mem_comap] using this
  · intro y hy
    have := hσ' _ hy
    simpa [Submodule.mem_comap] using this
  · rw [Submodule.map_coe]
    have : ⇑(LinearMap.snd K.O B₁.A B₂.A) = ⇑(LinearMap.snd K.E B₁.A B₂.A) := rfl
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact LinearMap.snd_surjective
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hg' m hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hσ' m hm, rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
section
noncomputable section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.LiftCoker

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem map_mem_A (f : O⟦X⟧) : PowerSeries.map (algebraMap O K) f ∈ A O K := by
  rw [← coe_equivA]
  exact (equivA O K f).2


variable (O K) in
def colon {ι κ : Type} [Fintype ι] (G : Matrix κ ι K⟦X⟧) : Ideal O⟦X⟧ where
  carrier := {α | ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) →
    ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧ PowerSeries.map (algebraMap O K) α • w = G *ᵥ m}
  add_mem' {α β} hα hβ w hw := by
    obtain ⟨m, hm, h⟩ := hα w hw
    obtain ⟨m', hm', h'⟩ := hβ w hw
    exact ⟨m + m', fun j => add_mem (hm j) (hm' j), by rw [map_add (f := _), add_smul, h, h', Matrix.mulVec_add]⟩
  zero_mem' w _ := ⟨0, fun _ => zero_mem _, by simp⟩
  smul_mem' c α hα w hw := by
    obtain ⟨m, hm, h⟩ := hα w hw
    refine ⟨PowerSeries.map (algebraMap O K) c • m, fun j => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (map_mem_A c) (hm j)
    · rw [smul_eq_mul, map_mul, mul_smul, h, Matrix.mulVec_smul]

theorem mem_colon {ι κ : Type} [Fintype ι] {G : Matrix κ ι K⟦X⟧} {α : O⟦X⟧} :
    α ∈ colon O K G ↔ ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) →
      ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧ PowerSeries.map (algebraMap O K) α • w = G *ᵥ m := Iff.rfl

end GlobalTheory.LiftCoker
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommuteOfCommuteSeparableCharpoly
section
open Matrix Polynomial

namespace GlobalTheory.CommSep

theorem commute_aeval_of_commute {E : Type} [Field E] {r : ℕ} {m A : Matrix (Fin r) (Fin r) E}
    (h : Commute m A) (p : E[X]) : Commute m (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial k a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (h.pow_right k).smul_right a

theorem aeval_mulVec_eq_krylov {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (v c : Fin r → E) :
    aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) *ᵥ v = GlobalTheory.ClassParam.krylov A v *ᵥ c := by
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.ClassParam.krylov, map_sum, aeval_monomial, Matrix.sum_mulVec,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eq_aeval_of_commute_of_separable {E : Type} [Field E] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) E) (hs : A.charpoly.Separable) (n : Matrix (Fin r) (Fin r) E)
    (hn : n * A = A * n) : ∃ q : E[X], n = aeval A q := by
  classical
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field A hs
  set K := GlobalTheory.ClassParam.krylov A v with hK
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.2 hv
  let c := K⁻¹ *ᵥ (n *ᵥ v)
  refine ⟨∑ j : Fin r, monomial (j : ℕ) (c j), ?_⟩
  set p := aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) with hp
  have hpv : p *ᵥ v = n *ᵥ v := by
    rw [hp, aeval_mulVec_eq_krylov, ← hK]
    simp only [c, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul]
  have hpA : Commute p A := (commute_aeval_of_commute (Commute.refl A) _).symm
  have hnA : Commute n A := hn
  have hcol : n * K = p * K := by
    ext i j
    have e1 : ∀ M : Matrix (Fin r) (Fin r) E, Commute M A →
        (M * K) i j = (A ^ (j : ℕ) *ᵥ (M *ᵥ v)) i := by
      intro M hM
      have : (M * K) i j = (M *ᵥ (A ^ (j : ℕ) *ᵥ v)) i := by
        simp [hK, GlobalTheory.ClassParam.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hM.pow_right _).eq]
    rw [e1 n hnA, e1 p hpA, hpv]
  have := congrArg (· * K⁻¹) hcol
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu] using this

theorem commute_of_commute_separable : ∀ (E : Type) [Field E] (r : ℕ)
    (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E,
    m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by
  intro E _ r A₀ hs m n hm hn
  obtain ⟨q, rfl⟩ := eq_aeval_of_commute_of_separable A₀ hs n hn
  exact (commute_aeval_of_commute (m := m) hm q).eq

end GlobalTheory.CommSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeAlgebraMapOfStarEq
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.JR

theorem Unram.mem_range_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  intro F E _ _ _ _ h y hy
  haveI := h.charZero
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨b, d, hb0, hs, -, -⟩ := Unram.exists_basis_antifixed F E
  have hsum := b.sum_repr y
  rw [Fin.sum_univ_two, hb0] at hsum
  set a := b.repr y 0
  set c := b.repr y 1
  have hst : star y = a • (1 : E) - c • b 1 := by
    rw [← hsum]
    simp only [Algebra.smul_def, star_add, star_mul', h.star_fix, hs, star_one]
    ring
  have h2 : (2 : E) * (c • b 1) = 0 := by linear_combination hsum + hst - hy
  have hc : c • b 1 = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  refine ⟨a, ?_⟩
  rw [← hsum, hc, add_zero, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinear
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

theorem integrable_mixedModel_partialFourier_integrand {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] {r : ℕ} (μ : Measure F) [μ.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (hψ : IsLocallyConstant (fun x => ψ x))
    (f : Gl r F → ℂ) (hf : IsTest f) (Y : Gl r F) :
    Integrable (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1))
      (Measure.pi fun _ : Fin r => μ) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : Continuous (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1)) := by
    refine Continuous.mul ?_ ?_
    · exact hf.1.continuous.comp (by fun_prop)
    · exact hψ.continuous.comp (by fun_prop)
  refine hc.integrable_of_hasCompactSupport ?_
  have hK : IsCompact ((fun Z : Gl r F => Z.2.1) '' tsupport f) := hf.2.isCompact.image (by fun_prop)
  refine HasCompactSupport.intro hK ?_
  intro b hb
  have : (Y.1, b, Y.2.2.1, Y.2.2.2) ∉ tsupport f := fun h => hb ⟨_, h, rfl⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end GlobalTheory.JR.WeilMix

theorem GlobalTheory.JR.WeilMix.ptrB_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  intro F E _ _ _ _ hU r M ψ hψ c f f' hf hf'
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  have hlc : IsLocallyConstant (fun x => ψ x) := ((_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).1
  funext Y
  have h1 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f hf Y
  have h2 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f' hf' Y
  simp only [WeilMix.ptrB, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [integral_add (h1.const_mul c) h2, integral_const_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelWeylElementEqPartialFourier
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  intro F E _ _ _ _ hU r M ψ hψ f hf
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hψc : Continuous (fun x => ψ x) := ((_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).1.continuous
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  have hw : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  simp only [WeilMix.negB, WeilMix.ptrB, WeilMix.rowAct, WeilMix.rowMap, fourG, hw]
  simp
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  set G : (Fin r → F) → ℂ := fun x => (∫ b', f (A, b', x, l) * ψ (b' ⬝ᵥ c) ∂μ) * ψ (x ⬝ᵥ b) with hG
  set H : (Fin r → F) → (Fin r → F) → ℂ := fun x b' => f (A, b', x, l) * ψ (b' ⬝ᵥ c) * ψ (x ⬝ᵥ b) with hH
  have hHc : Continuous (Function.uncurry H) := by
    have h1 : Continuous (fun p : (Fin r → F) × (Fin r → F) => f (A, p.2, p.1, l)) :=
      hf.1.continuous.comp (by fun_prop)
    have h2 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.2 ⬝ᵥ c)) :=
      hψc.comp (continuous_snd.dotProduct continuous_const)
    have h3 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.1 ⬝ᵥ b)) :=
      hψc.comp (continuous_fst.dotProduct continuous_const)
    exact (h1.mul h2).mul h3
  have hHs : HasCompactSupport (Function.uncurry H) := by
    refine HasCompactSupport.intro ((hf.2.isCompact).image
      (show Continuous (fun Y : Gl r F => (Y.2.2.1, Y.2.1)) by fun_prop)) ?_
    intro p hp
    by_contra hne
    apply hp
    refine ⟨(A, p.2, p.1, l), subset_tsupport _ ?_, rfl⟩
    intro h0
    apply hne
    simp [Function.uncurry, H, h0]
  have hint : Integrable (Function.uncurry H) (μ.prod μ) := hHc.integrable_of_hasCompactSupport hHs
  calc _ = ∫ x, G (-x) ∂μ := by
        congr 1; funext x; simp only [G, neg_dotProduct, neg_neg]; rfl
    _ = ∫ x, G x ∂μ := integral_neg_eq_self G μ
    _ = ∫ x, ∫ b', H x b' ∂μ ∂μ := by
        congr 1; funext x; simp only [G, H]; rw [integral_mul_const]
    _ = ∫ b', ∫ x, H x b' ∂μ ∂μ := integral_integral_swap hint
    _ = _ := by
        congr 1; funext b'; congr 1; funext x
        simp only [H]
        rw [mul_assoc, ← AddChar.map_add_eq_mul, dotProduct_comm b' c, add_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedRowCoefficientMatricesDetNormStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedRowCoefficientMatrices_det_norm : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F), ϖ ≠ 0 → ∀ lam π : Fin h → F, (∀ j, lam j ≠ 0) → (∀ j, π j ≠ 0) → Antitone (fun j => ‖lam j‖) → Orth p lam → ∀ L U : ℕ, ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  first | exact @GlobalTheory.PMonE.coefB_det | exact GlobalTheory.PMonE.coefB_det | (intros; apply GlobalTheory.PMonE.coefB_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumCardSubspaces
section
open scoped BigOperators

namespace GlobalTheory.GaussSubspace

theorem sum_card_subspaces :
    ∀ (k : Type) [Field k] [Finite k] (m : ℕ) (A : Type) [CommRing A] (Y : A), ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ j * (Nat.card k : A) ^ (j * (j - 1) / 2) * (Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W = j} : A) * Y ^ j = ∏ i ∈ Finset.range m, (1 - (Nat.card k : A) ^ i * Y) := by
  intro k _ _ m A _ Y
  rw [← GlobalTheory.GaussCount.gauss_formula (Nat.card k) A Y m]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := GlobalTheory.GaussCount.subspaceCount k (Fin m → k) j
  rw [Module.finrank_fin_fun] at h
  rw [h]

end GlobalTheory.GaussSubspace
end

