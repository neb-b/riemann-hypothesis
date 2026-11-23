module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsEquiv
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.splitsEquiv_of :
    SplitsOfEquiv := by
  intro R S B _ _ _ _ _ I e
  let z : I → (S →ₐ[R] B) := fun i =>
    (((Pi.evalAlgHom B (fun _ => B) i).comp e.toAlgHom).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  refine ⟨z, ?_⟩
  have h : ∀ x, splitMap z x = e x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul b s =>
      funext i
      have hb : b ⊗ₜ[R] s = b • ((1 : B) ⊗ₜ[R] s) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [splitMap_tmul, hb, map_smul, Pi.smul_apply, smul_eq_mul]
      rfl
  have hf : (splitMap z : B ⊗[R] S → (I → B)) = e := funext h
  unfold Splits
  rw [hf]
  exact e.bijective
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsField
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem exists_forall_algHom_pi_eq_apply_of_finite {K P : Type} [Field K] [Finite P] (ψ : (P → K) →ₐ[K] K) :
    ∃ p, ∀ x, ψ x = x p := by
  classical
  have hex : ∃ p, ψ (Pi.single p 1) ≠ 0 := by
    by_contra h
    push_neg at h
    have := Fintype.ofFinite P
    have h1 : (1 : P → K) = ∑ p, Pi.single p 1 := by
      simpa using (Finset.univ_sum_single (1 : P → K)).symm
    have h2 : ψ 1 = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum]
      simp [h]
    simp at h2
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, fun x => ?_⟩
  have hid : ψ (Pi.single p 1) = 1 := by
    have h2 : ψ (Pi.single p 1) * ψ (Pi.single p 1) = ψ (Pi.single p 1) := by
      rw [← map_mul]
      congr 1
      ext i
      by_cases h : i = p <;> simp [Pi.single_apply, h]
    exact (mul_left_inj' hp).1 (h2.trans (one_mul _).symm)
  have hx : x * Pi.single p 1 = algebraMap K (P → K) (x p) * Pi.single p 1 := by
    ext i
    by_cases h : i = p <;> simp [Pi.single_apply, h]
  have h3 := congrArg ψ hx
  rw [map_mul, map_mul, AlgHom.commutes, hid] at h3
  simpa using h3

theorem UpperTheory.Gal.crystallineComparison.splitsField_of :
    SplitsField := by
  intro R S K _ _ _ _ _ _ hE
  classical
  have hfin : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  haveI : IsArtinianRing (K ⊗[R] S) := isArtinian_of_tower K inferInstance
  haveI : Finite (PrimeSpectrum (K ⊗[R] S)) := inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S)
  let F := splitMap (R := R) (S := S) (B := K) (I := S →ₐ[R] K) (fun z => z)
  let L : (S →ₐ[R] K) → ((K ⊗[R] S) →ₐ[K] K) := fun ψ => (Pi.evalAlgHom K (fun _ => K) ψ).comp F
  have hL : ∀ ψ x, L ψ x = F x ψ := fun _ _ => rfl
  have hLs : ∀ ψ (s : S), L ψ (1 ⊗ₜ s) = ψ s := by
    intro ψ s
    simp [L, F, splitMap]
  choose q hq using fun ψ => exists_forall_algHom_pi_eq_apply_of_finite ((L ψ).comp e.symm.toAlgHom)
  have hLe : ∀ ψ x, L ψ x = e x (q ψ) := by
    intro ψ x
    simpa using hq ψ (e x)
  have qinj : Function.Injective q := by
    intro ψ1 ψ2 h
    ext s
    rw [← hLs, ← hLs, hLe, hLe, h]
  have hsec : ∀ p, ∃ ψ, q ψ = p := by
    intro p
    let g : (K ⊗[R] S) →ₐ[K] K := (Pi.evalAlgHom K (fun _ => K) p).comp e.toAlgHom
    let ψ : S →ₐ[R] K := (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
    have hg : L ψ = g := by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · ext s
        simp [hLs, ψ]
    refine ⟨ψ, ?_⟩
    have h1 := hLe ψ (e.symm (Pi.single p 1))
    rw [hg] at h1
    simp only [g, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe,
      AlgEquiv.apply_symm_apply, Pi.evalAlgHom_apply] at h1
    by_contra hne
    simp [Pi.single_apply, hne] at h1
  refine ⟨Finite.of_injective q qinj, ?_⟩
  show Function.Bijective F
  constructor
  · intro x y h
    apply e.injective
    funext p
    obtain ⟨ψ, rfl⟩ := hsec p
    rw [← hLe, ← hLe, hL, hL, h]
  · intro v
    refine ⟨e.symm (Function.extend q v 0), ?_⟩
    funext ψ
    rw [← hL, hLe, e.apply_symm_apply, qinj.extend_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PTelescope
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem telescope_core {P : Type} (q n : ℕ) (F : P → P) (T A : ℕ → Multiset P)
    (h0 : T 0 = A 0)
    (hs : ∀ j, j < n → T (j + 1) = (A j).map F + q ^ (j + 1) • A (j + 1)) (m : ℕ) (hm : m ≤ n) :
    (Even m →
      ∑ j ∈ Finset.range (m + 1), (if Even j then q ^ (j.choose 2) else 0) • (T j).map F^[n - j] =
        ∑ j ∈ Finset.range (m + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T j).map F^[n - j] +
          q ^ ((m + 1).choose 2) • (A m).map F^[n - m]) ∧
    (¬ Even m →
      ∑ j ∈ Finset.range (m + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T j).map F^[n - j] =
        ∑ j ∈ Finset.range (m + 1), (if Even j then q ^ (j.choose 2) else 0) • (T j).map F^[n - j] +
          q ^ ((m + 1).choose 2) • (A m).map F^[n - m]) := by
  induction m with
  | zero =>
    refine ⟨fun _ => ?_, fun h => absurd ⟨0, rfl⟩ h⟩
    simp [h0]
  | succ m ih =>
    have hmn : m < n := hm
    obtain ⟨ihE, ihO⟩ := ih (by omega)
    have key : (T (m + 1)).map F^[n - (m + 1)] =
        (A m).map F^[n - m] + q ^ (m + 1) • (A (m + 1)).map F^[n - (m + 1)] := by
      rw [hs m hmn, Multiset.map_add (f := _), Multiset.map_nsmul, Multiset.map_map]
      congr 2
      have e : n - m = (n - (m + 1)) + 1 := by omega
      rw [e, Function.iterate_succ]
    have hc : (m + 1 + 1).choose 2 = (m + 1).choose 2 + (m + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    simp only [Finset.sum_range_succ _ (m + 1), key, hc, pow_add, smul_add, mul_smul]
    rcases Nat.even_or_odd m with he | ho
    · have hne : ¬ Even (m + 1) := Nat.not_even_iff_odd.mpr he.add_one
      simp only [hne, if_false, zero_smul, add_zero, if_true]
      refine ⟨fun h => h.elim, fun _ => ?_⟩
      rw [ihE he]
      abel
    · have hne : ¬ Even m := Nat.not_even_iff_odd.mpr ho
      have hev : Even (m + 1) := ho.add_one
      simp only [hev, if_false, zero_smul, add_zero, if_true]
      refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
      rw [ihO hne]
      abel

theorem UpperTheory.Gal.crystallineComparison.telescope_of :
    Telescope := by
  intro q n P F T A hAn h0 hs
  let T' : ℕ → Multiset P := fun j => if h : j < n + 1 then T ⟨j, h⟩ else 0
  have hT : ∀ j : Fin (n + 1), T j = T' j := fun j => by
    simp only [T', dif_pos j.isLt, Fin.eta]
  have h0' : T' 0 = A 0 := by simpa [T'] using h0
  have hs' : ∀ j, j < n → T' (j + 1) = (A j).map F + q ^ (j + 1) • A (j + 1) := by
    intro j hj
    have hh := hs ⟨j, hj⟩
    simpa [T', hj, Fin.succ] using hh
  have hE : ∑ j : Fin (n + 1), wEv q j • (T j).map F^[n - j] =
      ∑ j ∈ Finset.range (n + 1), (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j] := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j]
    rfl
  have hO : ∑ j : Fin (n + 1), wOd q j • (T j).map F^[n - j] =
      ∑ j ∈ Finset.range (n + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j] := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j]
    rfl
  obtain ⟨h1, h2⟩ := telescope_core q n F T' A h0' hs' n le_rfl
  rw [hE, hO]
  by_cases he : Even n
  · rw [h1 he]
    simp [hAn]
  · rw [h2 he]
    simp [hAn]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PValLift
section
noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem valLift_of : ValLift := by
  intro R _ l hl 𝔭 _
  classical
  obtain ⟨q, hq, hq𝔭⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := 𝔭) bot_le
  have hlq : l ∉ q := fun h =>
    Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) h hl
  haveI : q.IsPrime := hq.1.1
  let K := AlgebraicClosure (FractionRing (R ⧸ q))
  let ι : R →+* K := (algebraMap (FractionRing (R ⧸ q)) K).comp
    ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q))
  have hι : ∀ r, ι r = 0 ↔ r ∈ q := by
    intro r
    constructor
    · intro h
      have h1 : algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r) = 0 :=
        (map_eq_zero (algebraMap (FractionRing (R ⧸ q)) K)).mp h
      exact Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.to_map_eq_zero_iff.mp h1)
    · intro h
      simp [ι, Ideal.Quotient.eq_zero_iff_mem.mpr h]
  have hunit : ∀ s : 𝔭.primeCompl, IsUnit (ι s) := fun s =>
    isUnit_iff_ne_zero.mpr (fun h => s.2 (hq𝔭 ((hι s).mp h)))
  let φ : Localization.AtPrime 𝔭 →+* K := IsLocalization.lift (M := 𝔭.primeCompl) hunit
  have hφ : ∀ r, φ (algebraMap R _ r) = ι r := fun r => IsLocalization.lift_eq hunit r
  obtain ⟨B, hsub, hloc⟩ := (LocalSubring.range φ).exists_le_valuationSubring
  have hmemL : ∀ x, φ x ∈ (LocalSubring.range φ).toSubring := fun x => by
    rw [LocalSubring.range_toSubring]; exact ⟨x, rfl⟩
  let ψ' : Localization.AtPrime 𝔭 →+* B := φ.codRestrict B (fun x => hsub (hmemL x))
  let ψ : R →+* B := ψ'.comp (algebraMap R (Localization.AtPrime 𝔭))
  have hψ : ∀ r, (ψ r : K) = ι r := fun r => hφ r
  haveI : IsAlgClosed (FractionRing B) :=
    IsAlgClosed.of_ringEquiv K _ (FractionRing.algEquiv B K).symm.toRingEquiv
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, ψ.toAlgebra, ?_, ?_⟩
  · intro h
    change ψ l = 0 at h
    apply hlq
    rw [← hι, ← hψ, h, ZeroMemClass.coe_zero]
  · ext r
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    change ¬ IsUnit (ψ r) ↔ r ∈ 𝔭
    constructor
    · intro h
      by_contra hr
      exact h ((IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨r, hr⟩ : 𝔭.primeCompl)).map ψ')
    · intro hr hu
      have hxm : algebraMap R (Localization.AtPrime 𝔭) r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 r).mpr hr
      let y : (LocalSubring.range φ).toSubring :=
        ⟨φ (algebraMap R (Localization.AtPrime 𝔭) r), hmemL _⟩
      have hy : IsUnit y := hloc.map_nonunit y hu
      obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hy
      obtain ⟨w, hw⟩ : ∃ w, φ w = z := (LocalSubring.range_toSubring φ).le z.2
      have h1 : φ (algebraMap R (Localization.AtPrime 𝔭) r) * (z : K) = 1 := congrArg Subtype.val hz
      have hker : algebraMap R (Localization.AtPrime 𝔭) r * w - 1 ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, RingHom.map_sub, map_mul, map_one, hw, h1, sub_self]
      have hkerle : RingHom.ker φ ≤ IsLocalRing.maximalIdeal _ :=
        IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
      have h1m : (1 : Localization.AtPrime 𝔭) ∈ IsLocalRing.maximalIdeal _ := by
        have hs := Ideal.sub_mem _ (Ideal.mul_mem_right w _ hxm) (hkerle hker)
        simpa using hs
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)

end UpperTheory.Gal.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PValLocal
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem UpperTheory.Gal.crystallineComparison.one_not_mem {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime) :
    (1 : B) ∉ 𝔪 :=
  fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 h)

private theorem UpperTheory.Gal.crystallineComparison.good_or {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime) (e : B) :
    e ∉ 𝔪 ∨ 1 - e ∉ 𝔪 := by
  by_contra h
  push_neg at h
  exact one_not_mem h𝔪 (by simpa using 𝔪.add_mem h.1 h.2)

private theorem UpperTheory.Gal.crystallineComparison.mul_not_mem {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime)
    {a b : B} (ha : a ∉ 𝔪) (hb : b ∉ 𝔪) : a * b ∉ 𝔪 :=
  fun h => (h𝔪.mem_or_mem h).elim ha hb

private theorem UpperTheory.Gal.crystallineComparison.dvd_st {B : Type} [CommRing B] {a b e : B} (e' : B) (h : a ∣ e * b) :
    a ∣ e' * e * b := by
  rw [mul_assoc]
  exact Dvd.dvd.mul_left h e'

private theorem UpperTheory.Gal.crystallineComparison.good_combine {B ι : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime)
    (s : Finset ι) (Q : ι → B → Prop) (st : ∀ i e e', Q i e → Q i (e' * e))
    (ex : ∀ i ∈ s, ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ Q i e) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ ∀ i ∈ s, Q i e := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, IsIdempotentElem.one, one_not_mem h𝔪, by simp⟩
  | insert a s ha ih =>
    obtain ⟨e, he, hem, hQ⟩ := ih fun i hi => ex i (Finset.mem_insert_of_mem hi)
    obtain ⟨e', he', hem', hQ'⟩ := ex a (Finset.mem_insert_self a s)
    refine ⟨e' * e, he'.mul he, mul_not_mem h𝔪 hem' hem, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [mul_comm]
      exact st _ _ _ hQ'
    · exact st _ _ _ (hQ i hi)

private theorem UpperTheory.Gal.crystallineComparison.power_good {B : Type} [CommRing B] {ϖ : B} (hv : ValLike ϖ) {𝔪 : Ideal B}
    (h𝔪 : 𝔪.IsPrime) (d : B) (m : ℕ) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ (d ∣ e * ϖ ^ m ∨ ϖ ^ m ∣ e * d) := by
  obtain ⟨e, he, h1, h2⟩ := hv d (ϖ ^ m) ⟨m, Ideal.subset_span (by simp)⟩
  rcases good_or h𝔪 e with g | g
  · exact ⟨e, he, g, Or.inr h1⟩
  · exact ⟨1 - e, he.one_sub, g, Or.inl h2⟩

private theorem UpperTheory.Gal.crystallineComparison.pair_good {B : Type} [CommRing B] {ϖ : B} (hv : ValLike ϖ) {𝔪 : Ideal B}
    (h𝔪 : 𝔪.IsPrime) (M : ℕ) (d d' : B) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧
      ((∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ d ∣ e₀ * ϖ ^ M) → d ∣ e * d' ∨ d' ∣ e * d) := by
  by_cases h : ∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ d ∣ e₀ * ϖ ^ M
  · obtain ⟨e₀, h0, hm0, c, hc⟩ := h
    have h0' : e₀ * e₀ = e₀ := h0
    obtain ⟨f, hfd⟩ : ∃ f : B, f = e₀ * d + (1 - e₀) := ⟨_, rfl⟩
    have hf : e₀ * f = e₀ * d := by
      rw [hfd]
      linear_combination (d - 1) * h0'
    have hmem : ϖ ^ M ∈ Ideal.span {f, d'} := by
      have hP : ϖ ^ M = (e₀ * c + (1 - e₀) * ϖ ^ M) * f := by
        rw [hfd]
        linear_combination (-(c * d - c - d * ϖ ^ M + 2 * ϖ ^ M)) * h0' + e₀ * hc
      rw [hP]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    obtain ⟨e₁, h1, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hv f d' ⟨M, hmem⟩
    have A : d' ∣ (e₀ * e₁) * d := ⟨e₀ * a, by linear_combination e₀ * ha - e₁ * hf⟩
    have C : d ∣ (e₀ * (1 - e₁)) * d' := ⟨e₀ * b, by linear_combination e₀ * hb + b * hf⟩
    rcases good_or h𝔪 e₁ with g | g
    · exact ⟨e₀ * e₁, h0.mul h1, mul_not_mem h𝔪 hm0 g, fun _ => Or.inr A⟩
    · exact ⟨e₀ * (1 - e₁), h0.mul h1.one_sub, mul_not_mem h𝔪 hm0 g, fun _ => Or.inl C⟩
  · exact ⟨1, IsIdempotentElem.one, one_not_mem h𝔪, fun h' => absurd h' h⟩

theorem UpperTheory.Gal.crystallineComparison.valLocal_of :
    ValLocal := by
  intro B _ ϖ hv 𝔪 h𝔪 D M
  obtain ⟨e₁, i₁, g₁, q₁⟩ := good_combine h𝔪 (D ×ˢ Finset.range (M + 1))
    (fun p e => p.1 ∣ e * ϖ ^ p.2 ∨ ϖ ^ p.2 ∣ e * p.1)
    (fun p e e' h => h.elim (fun h => Or.inl (dvd_st e' h)) (fun h => Or.inr (dvd_st e' h)))
    (fun p _ => power_good hv h𝔪 p.1 p.2)
  obtain ⟨e₂, i₂, g₂, q₂⟩ := good_combine h𝔪 (D ×ˢ D)
    (fun p e => (∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ p.1 ∣ e₀ * ϖ ^ M) →
      p.1 ∣ e * p.2 ∨ p.2 ∣ e * p.1)
    (fun p e e' h h' => (h h').elim (fun h => Or.inl (dvd_st e' h)) (fun h => Or.inr (dvd_st e' h)))
    (fun p _ => pair_good hv h𝔪 M p.1 p.2)
  refine ⟨e₂ * e₁, i₂.mul i₁, mul_not_mem h𝔪 g₂ g₁, ?_, ?_⟩
  · intro d hd m hm
    have := q₁ (d, m) (Finset.mk_mem_product hd (Finset.mem_range.2 (Nat.lt_succ_of_le hm)))
    exact this.elim (fun h => Or.inl (dvd_st e₂ h)) (fun h => Or.inr (dvd_st e₂ h))
  · intro d hd d' hd' hdv
    have := q₂ (d, d') (Finset.mk_mem_product hd hd') ⟨e₂ * e₁, i₂.mul i₁, mul_not_mem h𝔪 g₂ g₁, hdv⟩
    rw [mul_comm e₂ e₁]
    exact this.elim (fun h => Or.inl (dvd_st e₁ h)) (fun h => Or.inr (dvd_st e₁ h))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PValPts
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.valPts_of :
    ValPts := by
  intro R S V _ _ _ _ _ _ _ _
  have hinj : Function.Injective (IsScalarTower.toAlgHom R V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  constructor
  · intro z z' h
    ext s
    apply hinj
    simpa only [AlgHom.comp_apply] using AlgHom.congr_fun h s
  · intro φ
    have hmem : ∀ s, φ s ∈ (IsScalarTower.toAlgHom R V (FractionRing V)).range := by
      intro s
      have h1 : IsIntegral R (φ s) := (Algebra.IsIntegral.isIntegral s).map φ
      have h2 : IsIntegral V (φ s) := h1.tower_top
      obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
      exact (AlgHom.mem_range _).2 ⟨v, hv⟩
    let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R V (FractionRing V)) hinj
    refine ⟨e.symm.toAlgHom.comp (φ.codRestrict _ hmem), ?_⟩
    ext s
    have h := e.apply_symm_apply ⟨φ s, hmem s⟩
    exact congrArg Subtype.val h
end

