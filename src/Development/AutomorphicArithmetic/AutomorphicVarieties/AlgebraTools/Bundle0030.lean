module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBruhatKO
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetLocus
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.le_of_detIdeal_le :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ Z : Ideal P, Z.IsPrime → relIdeal z m ≤ Z → (∃ j, m j ∉ Z) →
      ringKrullDim P ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) →
      ∀ Q : Ideal P, Q.IsPrime → detIdeal z m ≤ Q → Z ≤ Q := by
  intro P _ _ ι _ _ z m hc Z hZ hrel hm hdim Q hQ hdet
  have hdZ : detIdeal z m ≤ Z := det_mem_of_rel P ι z m Z hZ hrel hm
  by_cases hne : Nonempty ι
  swap
  · exfalso
    have : IsEmpty ι := not_nonempty_iff.1 hne
    apply hQ.ne_top
    rw [eq_top_iff]
    refine le_trans ?_ hdet
    simp [detIdeal, Matrix.det_isEmpty]
  obtain ⟨K, hK, hKdet, hKmin⟩ := exists_least_prime_detIdeal P ι z m hc hne
  haveI := hK
  haveI := hZ
  refine le_trans ?_ (hKmin Q hQ hdet)
  have hKZ : K ≤ Z := hKmin Z hZ hdZ
  by_contra hnot
  obtain ⟨x, hxZ, hxK⟩ := Set.not_subset.1 hnot
  have hrK : relIdeal z m ≤ K :=
    le_trans (le_sup_left : relIdeal z m ≤ relIdeal z m ⊔ Ideal.span {z.det}) hKdet
  have h1 : ringKrullDim (P ⧸ Z) + 1 ≤ ringKrullDim (P ⧸ K) := by
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hKZ)
      (Ideal.Quotient.factor_surjective hKZ) (r := Ideal.Quotient.mk K x) ?_ ?_
    · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    · simpa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using hxZ
  have h2 : ringKrullDim (P ⧸ K) ≤ ringKrullDim (P ⧸ relIdeal z m) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hrK) (Ideal.Quotient.factor_surjective hrK)
  have h3 := dim_relIdeal_le P ι z m hc
  have hfin : ringKrullDim (P ⧸ Z) < ⊤ := lt_of_le_of_lt (ringKrullDim_quotient_le Z) ringKrullDim_lt_top
  have hbot : ringKrullDim (P ⧸ Z) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
  have h12 := h1.trans h2
  have key : ringKrullDim (P ⧸ Z) + 1 + (Fintype.card ι : ℕ) ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) := by
    refine le_trans ?_ (h3.trans hdim)
    gcongr
  generalize ringKrullDim (P ⧸ Z) = d at key hfin hbot
  generalize Fintype.card ι = c at key
  induction d using WithBot.recBotCoe with
  | bot => exact hbot rfl
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => simp at hfin
    | coe d =>
      norm_cast at key
      omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermUnit
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hk_one {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) : hk ρ I 1 = 1 :=
  (hkNorm A G M ρ I 1 hI (one_mem _)).2.1

theorem UpperTheory.V.AlgebraTools.permUnit :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (w : Equiv.Perm (Fin n)), IsUnit (resCard k : A) → IsUnit (hk ρ (iwC k n C) (pm k n w)) := by
  intro k _ _ _ _ n C A M _ _ _ ρ w hq
  have hI : HeckePair (iwC k n C) := (heckePairIwC k n C).1
  induction h : invLen w generalizing w with
  | zero =>
    rw [(lenStep n w).2.1 h, map_one, hk_one ρ _ hI]
    exact isUnit_one
  | succ m ih =>
    have hw : w ≠ 1 := by
      rintro rfl
      have h0 : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
        unfold invLen
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro p _ ⟨h1, h2⟩
        exact lt_asymm h1 h2
      omega
    obtain ⟨i, j, hij, hlt⟩ := (lenStep n w).2.2 hw
    have hlen := ((lenStep n w).1 i j hij).2 hlt
    have hlt' : (Equiv.swap i j * w)⁻¹ i < (Equiv.swap i j * w)⁻¹ j := by
      simpa [_root_.mul_inv_rev, Equiv.swap_inv] using hlt
    have hm := permMul k n C A M ρ (Equiv.swap i j * w) i j hij hlt'
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at hm
    rw [← hm]
    exact ((simpleQuad k n C A M ρ i j hij).1 hq).mul (ih _ (by omega))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSphEq
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

private theorem hk_fixed {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) (hI : HeckePair I) {x : G} (hx : x ∈ K)
    (v : fixd ρ I) (hv : (v : M) ∈ fixd ρ K) :
    hk ρ I x v = (((MulAction.orbit I (x : G ⧸ I)).ncard : ℕ) : A) • v := by
  have hF : (MulAction.orbit I (x : G ⧸ I)).Finite := hI x
  ext
  change (hk2 ρ I I x v : M) = _
  rw [(hkApply A G M ρ I I x hF).1 v, dc,
    finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ I => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ hF,
    LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => (v : M))]
  · rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hF, Submodule.coe_smul, Nat.cast_smul_eq_nsmul]
  · intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨a, ha⟩ := hq
    have ha' : (((a : G) * x : G) : G ⧸ I) = (q.out : G) := by
      rw [QuotientGroup.out_eq']
      exact ha
    have h1 := mul_mem (mul_mem (h a.2) hx) (h (QuotientGroup.eq.1 ha'))
    rw [mul_inv_cancel_left] at h1
    exact hv _ h1

private theorem sum_ncard {G : Type} [Group G] {I K : Subgroup G} (h : I ≤ K) (hI : HeckePair I) {ι : Type}
    [Fintype ι] (w : ι → G) (hw : ∀ i, w i ∈ K) (hu : ∀ g ∈ K, ∃! i, ∃ a ∈ I, ∃ b ∈ I, g = a * w i * b) :
    ∑ i, (MulAction.orbit I (w i : G ⧸ I)).ncard = I.relIndex K := by
  obtain ⟨-, h1, h2⟩ := hkTrace ℤ G ℤ (Representation.trivial ℤ G ℤ) I K h ι w hI hw hu
  let v : fixd (Representation.trivial ℤ G ℤ) K := ⟨1, fun _ _ => rfl⟩
  have h3 := LinearMap.congr_fun h1 (inc _ h v)
  rw [LinearMap.comp_apply, h2, LinearMap.sum_apply,
    Finset.sum_congr rfl fun i _ => hk_fixed _ h hI (hw i) (inc _ h v) v.2, ← Finset.sum_smul, map_smul] at h3
  have h4 : (∑ i, (((MulAction.orbit I (w i : G ⧸ I)).ncard : ℕ) : ℤ)) * 1 = (I.relIndex K : ℤ) * 1 :=
    congrArg Subtype.val h3
  rw [mul_one, mul_one] at h4
  exact_mod_cast h4

private theorem invLen_one (n : ℕ) : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
  rw [invLen, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun p _ h => lt_asymm h.1 h.2

theorem UpperTheory.V.AlgebraTools.sphEq :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), IsSMulRegular M ((iwC k n ⊤).relIndex (KO k (Fin n)) : A) → ∀ v : fixd ρ (iwC k n ⊤), (v : M) ∈ fixd ρ (KO k (Fin n)) ↔ ∀ i j : Fin n, (j : ℕ) = i + 1 → hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j)) v = (resCard k : A) • v := by
  intro k _ _ _ _ n A M _ _ _ ρ hreg v
  have hI := (heckePairIwC k n ⊤).1
  have he : iwC k n ⊤ = iwahori k (Fin n) := (memIwC k n ⊤).2.1
  have hle : iwC k n ⊤ ≤ KO k (Fin n) := he ▸ iwahori_le_KO k (Fin n)
  obtain ⟨hw, hu⟩ := bruhatKO k n
  rw [← he] at hu
  constructor
  · intro hv i j hij
    have h2 := ((lenStep n 1).1 i j hij).1 (by
      show i < j
      rw [Fin.lt_def]; omega)
    rw [mul_one, invLen_one] at h2
    rw [hk_fixed ρ hle hI (hw _) v hv, permCard, h2, zero_add, pow_one]
  · intro hs
    have key : ∀ (m : ℕ) (w : Equiv.Perm (Fin n)), invLen w = m →
        hk ρ (iwC k n ⊤) (pm k n w) v = ((resCard k : A) ^ m) • v := by
      intro m
      induction m with
      | zero =>
        intro w hm
        rw [(lenStep n w).2.1 hm, map_one, (hkNorm A _ M ρ _ 1 hI (one_mem _)).2.1, pow_zero, one_smul]
        rfl
      | succ m ih =>
        intro w hm
        have hw1 : w ≠ 1 := by
          rintro rfl
          rw [invLen_one] at hm
          omega
        obtain ⟨i, j, hij, hlt⟩ := (lenStep n w).2.2 hw1
        have hl := ((lenStep n w).1 i j hij).2 hlt
        have hp := permMul k n ⊤ A M ρ (Equiv.swap i j * w) i j hij (by simpa using hlt)
        rw [Equiv.swap_mul_self_mul] at hp
        rw [← hp, Module.End.mul_apply, ih _ (by omega), map_smul, hs i j hij, smul_smul, pow_succ]
    have h1 := LinearMap.congr_fun (hkTrace A _ M ρ _ _ hle _ (fun w => pm k n w) hI hw hu).2.1 v
    have h2 := sum_ncard hle hI (fun w => pm k n w) hw hu
    simp only [permCard] at h2
    rw [LinearMap.sum_apply, Finset.sum_congr rfl fun w _ => key _ w rfl, ← Finset.sum_smul] at h1
    have h3 : ((iwC k n ⊤).relIndex (KO k (Fin n)) : A) • (v : M) = (trc ρ (KO k (Fin n)) (iwC k n ⊤) v : M) := by
      rw [← h2, Nat.cast_sum]
      simp only [Nat.cast_pow]
      exact congrArg Subtype.val h1
    intro g hg
    apply hreg
    show _ • ρ g v = _ • (v : M)
    rw [← map_smul, h3]
    exact (trc ρ (KO k (Fin n)) (iwC k n ⊤) v).2 g hg
end

