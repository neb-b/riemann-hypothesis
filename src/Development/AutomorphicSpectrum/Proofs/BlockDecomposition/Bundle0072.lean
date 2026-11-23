module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0052
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedUnitCoefficientRoot
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.UnitRoot

open Polynomial

theorem coeff_prod_mem {S : Type} [CommRing S] (m : Ideal S) (s : Multiset S)
    (h : ∀ b ∈ s, b ∈ m) :
    ∀ k < Multiset.card s, ((s.map fun b => (X : S[X]) - C b).prod).coeff k ∈ m := by
  induction s using Multiset.induction_on with
  | empty => intro k hk; simp at hk
  | cons a s ih =>
    intro k hk
    have ha : a ∈ m := h a (Multiset.mem_cons_self a s)
    have ih' := ih fun b hb => h b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.prod_cons, sub_mul]
    rw [Multiset.card_cons] at hk
    cases k with
    | zero =>
      simp only [coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]
      exact m.neg_mem (m.mul_mem_right _ ha)
    | succ k =>
      simp only [coeff_sub, coeff_X_mul, coeff_C_mul]
      exact m.sub_mem (ih' k (by omega)) (m.mul_mem_right _ ha)

theorem exists_root : ∀ {S : Type} [CommRing S] , Aic (S := S) →
    (∀ a b : S, IsUnit (a + b) → IsUnit a ∨ IsUnit b) →
    ∀ (Q : Polynomial S) (i : ℕ), Q.coeff 0 = 1 → 0 < i → IsUnit (Q.coeff i) →
      ∃ y, Q.eval y = 0 := by
  intro S _ hA hL Q i h0 hi hu
  rcases subsingleton_or_nontrivial S with hs | hn
  · exact ⟨0, Subsingleton.elim _ _⟩
  haveI : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add hL
  have htd : Q.natTrailingDegree = 0 :=
    Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [h0]; exact one_ne_zero))
  have hmon : Q.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, h0]
  have hdeg : Q.reverse.natDegree = Q.natDegree := by
    rw [reverse_natDegree, htd]; rfl
  have hid : i ≤ Q.natDegree := le_natDegree_of_ne_zero hu.ne_zero
  obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA _ hmon
  have hcard : Multiset.card s = Q.natDegree := by
    rw [← hdeg, hs, natDegree_multiset_prod_X_sub_C_eq_card]
  have hcoeff : Q.reverse.coeff (Q.natDegree - i) = Q.coeff i := by
    rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
    congr 1
    omega
  by_cases hex : ∃ b ∈ s, IsUnit b
  · obtain ⟨b, hbs, hb⟩ := hex
    have hroot : Q.reverse.eval b = 0 := by
      have hdvd : (X : S[X]) - C b ∣ Q.reverse := by
        rw [hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
      exact dvd_iff_isRoot.mp hdvd
    obtain ⟨u, rfl⟩ := hb
    refine ⟨((u⁻¹ : Sˣ) : S), ?_⟩
    letI : Invertible ((u⁻¹ : Sˣ) : S) := (u⁻¹).invertible
    have key := eval₂_reverse_mul_pow (RingHom.id S) ((u⁻¹ : Sˣ) : S) Q
    have hinv : ⅟((u⁻¹ : Sˣ) : S) = (u : S) := by simp
    rw [hinv, eval₂_id, eval₂_id, hroot, zero_mul] at key
    exact key.symm
  · exfalso
    have hall : ∀ b ∈ s, b ∈ IsLocalRing.maximalIdeal S := fun b hb =>
      (IsLocalRing.mem_maximalIdeal b).mpr fun hbu => hex ⟨b, hb, hbu⟩
    have hmem := coeff_prod_mem (IsLocalRing.maximalIdeal S) s hall (Q.natDegree - i)
      (by omega)
    rw [← hs, hcoeff] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

end GlobalTheory.CompanionTheory.UnitRoot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorIntersectionCardStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_intersection_card : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ I L : Submodule (ZMod n) X, Nat.card ↥((⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x))) * Nat.card ↥I * Nat.card ↥L = Nat.card X * Nat.card ↥(I ⊓ L) := by
  first | exact @GlobalTheory.CompanionTheory.PairCount.card_annihilator_inf | exact GlobalTheory.CompanionTheory.PairCount.card_annihilator_inf | (intros; apply GlobalTheory.CompanionTheory.PairCount.card_annihilator_inf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianLimitLiftOfCompatible
section
open CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.ArtinTower

universe w

theorem coset_chain {W : Type} [CommRing W] {M : Type w} [AddCommGroup M] [Module W M]
    [IsArtinian W M] (K : ℕ → Submodule W M) (hK : ∀ k, K (k + 1) ≤ K k) (c : ℕ → M)
    (hc : ∀ k, c (k + 1) - c k ∈ K k) : ∃ x, ∀ k, x - c k ∈ K k := by
  have hanti : Antitone K := antitone_nat_of_succ_le hK
  obtain ⟨m, hm⟩ := IsArtinian.monotone_stabilizes
    (⟨fun k => OrderDual.toDual (K k), hanti.dual_right⟩ : ℕ →o (Submodule W M)ᵒᵈ)
  have hdiff : ∀ k j, c (k + j) - c k ∈ K k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : c (k + j + 1) - c (k + j) ∈ K k := hanti (Nat.le_add_right k j) (hc (k + j))
      have h2 := add_mem h1 ih
      rw [sub_add_sub_cancel] at h2
      exact h2
  refine ⟨c m, fun k => ?_⟩
  rcases le_total k m with hkm | hmk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
    exact hdiff k j
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
    have hKeq : K m = K (m + j) := hm (m + j) (Nat.le_add_right m j)
    rw [← hKeq]
    have h3 := neg_mem (hdiff m j)
    rw [neg_sub] at h3
    exact h3

section
variable {W : Type} [CommRing W] (S : Sys.{w} W) (N : ∀ n, Submodule W (S.M n))
  (y : ∀ n, S.M n)

noncomputable def imgSub : ℕ → ∀ n, Submodule W (S.M n)
  | 0, n => N n
  | k + 1, n => (imgSub k (n + 1)).map (S.r n)

noncomputable def imgPt : ℕ → ∀ n, S.M n
  | 0, n => y n
  | k + 1, n => S.r n (imgPt k (n + 1))

def stable (n : ℕ) : Set (S.M n) := {x | ∀ k, x - imgPt S y k n ∈ imgSub S N k n}

variable {S N y}

theorem imgSub_succ_le (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) :
    ∀ k n, imgSub S N (k + 1) n ≤ imgSub S N k n := by
  intro k
  induction k with
  | zero =>
    intro n
    show Submodule.map (S.r n) (N (n + 1)) ≤ N n
    exact Submodule.map_le_iff_le_comap.mpr (fun u hu => hN n u hu)
  | succ k ih =>
    intro n
    show Submodule.map (S.r n) (imgSub S N (k + 1) (n + 1)) ≤
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    exact Submodule.map_mono (ih (n + 1))

theorem imgPt_step (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) :
    ∀ k n, imgPt S y (k + 1) n - imgPt S y k n ∈ imgSub S N k n := by
  intro k
  induction k with
  | zero => intro n; exact hy n
  | succ k ih =>
    intro n
    show S.r n (imgPt S y (k + 1) (n + 1)) - S.r n (imgPt S y k (n + 1)) ∈
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    rw [← map_sub]
    exact Submodule.mem_map_of_mem (ih (n + 1))

theorem stable_nonempty (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) (n : ℕ) [IsArtinian W (S.M n)] :
    ∃ x, x ∈ stable S N y n := by
  obtain ⟨x, hx⟩ := coset_chain (fun k => imgSub S N k n) (fun k => imgSub_succ_le hN k n)
    (fun k => imgPt S y k n) (fun k => imgPt_step hy k n)
  exact ⟨x, hx⟩

theorem stable_surj (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) {n : ℕ} [IsArtinian W (S.M (n + 1))]
    {x : S.M n} (hx : x ∈ stable S N y n) :
    ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := by
  have hxk : ∀ k, x - imgPt S y k n ∈ imgSub S N k n := hx
  have hA : ∀ k, ∃ u : S.M (n + 1),
      S.r n u = x ∧ u - imgPt S y k (n + 1) ∈ imgSub S N k (n + 1) := by
    intro k
    have h1 : x - imgPt S y (k + 1) n ∈ Submodule.map (S.r n) (imgSub S N k (n + 1)) :=
      hxk (k + 1)
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp h1
    refine ⟨v + imgPt S y k (n + 1), ?_, ?_⟩
    · rw [map_add (f := _), hve]
      show x - S.r n (imgPt S y k (n + 1)) + S.r n (imgPt S y k (n + 1)) = x
      exact sub_add_cancel _ _
    · rw [add_sub_cancel_right]
      exact hv
  choose c hc1 hc2 using hA
  have hKanti : ∀ k, LinearMap.ker (S.r n) ⊓ imgSub S N (k + 1) (n + 1) ≤
      LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) :=
    fun k => inf_le_inf_left _ (imgSub_succ_le hN k (n + 1))
  have hstep : ∀ k, c (k + 1) - c k ∈ LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) := by
    intro k
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hc1, hc1, sub_self]
    · have e : c (k + 1) - c k = (c (k + 1) - imgPt S y (k + 1) (n + 1)) +
          (imgPt S y (k + 1) (n + 1) - imgPt S y k (n + 1)) - (c k - imgPt S y k (n + 1)) := by
        abel
      rw [e]
      exact sub_mem (add_mem (imgSub_succ_le hN k (n + 1) (hc2 (k + 1)))
        (imgPt_step hy k (n + 1))) (hc2 k)
  obtain ⟨x', hx'⟩ := coset_chain (fun k => LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1))
    hKanti c hstep
  refine ⟨x', fun k => ?_, ?_⟩
  · have e : x' - imgPt S y k (n + 1) = (x' - c k) + (c k - imgPt S y k (n + 1)) := by abel
    rw [e]
    exact add_mem (Submodule.mem_inf.mp (hx' k)).2 (hc2 k)
  · have h0 := (Submodule.mem_inf.mp (hx' 0)).1
    rw [LinearMap.mem_ker, map_sub, hc1, sub_eq_zero] at h0
    exact h0

end

theorem exists_compatible : ∀ (W : Type) [CommRing W] (S : Sys.{1} W),
    (∀ n, IsArtinian W (S.M n)) → ∀ (N : ∀ n, Submodule W (S.M n)) (y : ∀ n, S.M n),
    (∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) → (∀ n, S.r n (y (n + 1)) - y n ∈ N n) →
    ∃ z : S.lim, ∀ n, z.1 n - y n ∈ N n := by
  intro W _ S hA N y hN hy
  have h0 : ∃ x, x ∈ stable S N y 0 := by
    haveI := hA 0
    exact stable_nonempty hN hy 0
  have hs : ∀ n (x : S.M n), x ∈ stable S N y n →
      ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := fun n x hx => by
    haveI := hA (n + 1)
    exact stable_surj hN hy hx
  let f : ∀ n, {x : S.M n // x ∈ stable S N y n} := fun n =>
    Nat.rec (motive := fun n => {x : S.M n // x ∈ stable S N y n})
      ⟨h0.choose, h0.choose_spec⟩
      (fun n p => ⟨(hs n p.1 p.2).choose, (hs n p.1 p.2).choose_spec.1⟩) n
  have hf : ∀ n, S.r n (f (n + 1)).1 = (f n).1 := fun n =>
    (hs n (f n).1 (f n).2).choose_spec.2
  refine ⟨⟨fun n => (f n).1, ?_⟩, fun n => (f n).2 0⟩
  unfold CrystallineSemistableComparison.Sys.lim
  exact fun n => hf n

end GlobalTheory.CompanionTheory.ArtinTower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariantRightTranslationStatement
section
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_invariant_right_translation : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := by
  first | exact @GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | exact GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | (intros; apply GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageOverMaximalCompactResidue
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.Jp.AvgRes

theorem avg_of_surjective {G H : Type*} [Group G] [Group H] (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)] (r : G →* H)
    (hr : Function.Surjective r) (hN : N ≤ r.ker) (f : H → ℂ) :
    (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, f (r (Quotient.out u)) = (∑ᶠ g, f g) / (Nat.card H : ℂ) := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set φ : G ⧸ N →* H := QuotientGroup.lift N r hN with hφdef
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨g, rfl⟩ := hr h
    exact ⟨(g : G ⧸ N), QuotientGroup.lift_mk N hN g⟩
  haveI : Finite H := Finite.of_surjective φ hφ
  haveI : Fintype H := Fintype.ofFinite _
  have hout : ∀ u : G ⧸ N, r (Quotient.out u) = φ u := by
    intro u
    conv_rhs => rw [← Quotient.out_eq u]
    exact (QuotientGroup.lift_mk N hN _).symm
  simp_rw [hout]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_comp f φ,
    Finset.image_univ_of_surjective hφ]
  set c := (Finset.univ.filter fun u : G ⧸ N => φ u = 1).card with hc
  have hfib : ∀ b : H, (Finset.univ.filter fun u : G ⧸ N => φ u = b).card = c := fun b =>
    MonoidHom.card_fiber_eq_of_mem_range φ (hφ b) (hφ 1)
  have hcard : Fintype.card (G ⧸ N) = Fintype.card H * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_image φ Finset.univ,
      Finset.image_univ_of_surjective hφ]
    simp [hfib]
  have hc0 : (c : ℂ) ≠ 0 := by
    rw [hc]
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, by simp⟩)
  have hH : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp_rw [hfib]
  rw [← Finset.smul_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard,
    nsmul_eq_mul]
  push_cast
  field_simp

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem resK_surjective (n : ℕ) : Function.Surjective (resK (n := n) (O := O)) := by
  intro M
  classical
  have hs := IsLocalRing.residue_surjective (R := O)
  let A : Matrix (Ix n) (Ix n) O :=
    (M : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)).map (Function.surjInv hs)
  have hA : (IsLocalRing.residue O).mapMatrix A = (M : Matrix (Ix n) (Ix n) _) := by
    ext i j
    exact Function.surjInv_eq hs _
  have hdet : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hA]
    exact (Matrix.isUnits_det_units M).ne_zero
  refine ⟨Matrix.nonsingInvUnit A hdet, ?_⟩
  ext i j
  exact Function.surjInv_eq hs _

theorem level_square_congruence_le_reduction_ker (n : ℕ) {ϖ : O} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) :
    Gam2 (n := n) ϖ ≤ (resK (n := n) (O := O)).ker := by
  intro g hg
  have hg' := MonoidHom.mem_ker.mp hg
  rw [MonoidHom.mem_ker]
  have hle : Ideal.span {ϖ ^ 2} ≤ IsLocalRing.maximalIdeal O :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_of_mem _ hϖ 2 two_pos))
  ext i j
  have h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((g : Matrix (Ix n) (Ix n) O) i j) =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 : Matrix (Ix n) (Ix n) O) i j) := by
    have h0 := congrArg
      (fun x : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => (x : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j) hg'
    change Ideal.Quotient.mk _ ((g : Matrix (Ix n) (Ix n) O) i j) =
      (1 : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 := Ideal.Quotient.eq.mpr (hle (Ideal.Quotient.eq.mp h1))
  change IsLocalRing.residue O ((g : Matrix (Ix n) (Ix n) O) i j) =
    (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j
  rw [show (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j =
      IsLocalRing.residue O ((1 : Matrix (Ix n) (Ix n) O) i j) by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp]
  exact h2

theorem avgK_res : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ f : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ,
      avgK ϖ (fun κ => f (resK κ)) = sumG f / (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
  intro O _ _ _ _ n ϖ hϖ f
  have hm : ϖ ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  haveI : (Gam2 (n := n) ϖ).Normal := MonoidHom.normal_ker _
  haveI : Finite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) := GlobalTheory.CompanionTheory.Jp.Unif.finite_quotient_level_square_congruence n hϖ
  exact avg_of_surjective (Gam2 ϖ) resK (resK_surjective n) (level_square_congruence_le_reduction_ker n hm) f

end GlobalTheory.CompanionTheory.Jp.AvgRes

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianMatricesModPow
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem exists_trace_one {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (h : IsUnrQuad R σ ϖ q ε) : ∃ u θ : R, IsUnit (u - σ u) ∧ θ + σ θ = 1 := by
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hσ : σ (u - σ u) = -(u - σ u) := by rw [map_sub, h.inv]; ring
  have hsv : σ v = -v := by
    have h1 : σ (u - σ u) * σ v = 1 := by rw [← map_mul, hv, map_one]
    rw [hσ] at h1
    have h2 : (u - σ u) * (σ v + v) = 0 := by linear_combination (-1 : R) * h1 + hv
    have h3 : v * ((u - σ u) * (σ v + v)) = 0 := by rw [h2, mul_zero]
    rw [← mul_assoc, mul_comm v, hv, one_mul] at h3
    linear_combination h3
  refine ⟨u, u * v, hu, ?_⟩
  rw [map_mul, hsv]
  linear_combination hv

theorem hermMod_eq {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (h : IsUnrQuad R σ ϖ q ε) (n k : ℕ) :
    hermMod σ ϖ n k = {H | ∀ a b, barσ σ ϖ h.fix_ϖ k (H b a) = H a b} := by
  ext H
  simp only [PositivityTheory.PfSWUS.Loc.hermMod, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, hh, rfl⟩ a b
    have hab := congrFun (congrFun hh a) b
    simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply] at hab
    simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, barσ_mk]
    rw [hab]
  · intro hH
    obtain ⟨-, θ, -, hθ⟩ := exists_trace_one h
    choose lift hlift using fun a b => Ideal.Quotient.mk_surjective (H a b)
    refine ⟨Matrix.of fun a b => θ * lift a b + σ (θ * lift b a), ?_, ?_⟩
    · ext a b
      simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_add (f := _),
        h.inv]
      ring
    · ext a b
      have e1 : Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (σ (lift b a)) = barσ σ ϖ h.fix_ϖ k (H b a) := by
        rw [← hlift b a, barσ_mk]
      have hθ' : Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) θ + Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (σ θ) = 1 := by
        rw [← map_add (f := _), hθ, map_one]
      simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, Matrix.of_apply, map_add (f := _), map_mul, hlift]
      rw [e1, hH a b]
      linear_combination (H a b) * hθ'

theorem card_hermMod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ n k : ℕ, Nat.card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by
  intro R _ σ ϖ q ε h n k
  rw [hermMod_eq h n k]
  have hcard := _root_.GlobalTheory.CompanionTheory.UnrDens.card_quot_lev R σ ϖ q ε h k
  have hq : 1 < q := h.one_lt
  haveI : Finite (R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  obtain ⟨u, hu, -⟩ := h.basis
  have hinv : ∀ x, barσ σ ϖ h.fix_ϖ k (barσ σ ϖ h.fix_ϖ k x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [barσ_mk, barσ_mk, h.inv]
  have hω : IsUnit (Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) u -
      barσ σ ϖ h.fix_ϖ k (Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) u)) := by
    rw [barσ_mk, ← map_sub]
    exact hu.map _
  have key := GlobalTheory.GramCount.card_hermitian_dvd_sq (barσ σ ϖ h.fix_ϖ k) hinv _ hω 1 (map_one _) n
  have e2 : Nat.card {x : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k // (1 : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) ∣ x} = q ^ (2 * k) := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => one_dvd x)
  apply Nat.pow_left_injective two_ne_zero
  show _ ^ 2 = _ ^ 2
  calc Nat.card ↥{H : Matrix (Fin n) (Fin n) (R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) |
          ∀ a b, barσ σ ϖ h.fix_ϖ k (H b a) = H a b} ^ 2
      = Nat.card {H : Fin n → Fin n → R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k //
          (∀ a b : Fin n, barσ σ ϖ h.fix_ϖ k (H b a) = H a b) ∧
            ∀ a b : Fin n, (1 : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) ∣ H a b} ^ 2 := by
        congr 1
        exact Nat.card_congr
          { toFun := fun H => ⟨H.1, H.2, fun _ _ => one_dvd _⟩
            invFun := fun H => ⟨H.1, H.2.1⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    _ = Nat.card {x : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k // (1 : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) ∣ x} ^ (n * n) := key
    _ = (q ^ (k * n ^ 2)) ^ 2 := by
        rw [e2, ← pow_mul, ← pow_mul]
        ring_nf

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankCompletionSymmetryStatement
section
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_rank_completion_symmetry : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ), ρ ≤ n →
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | exact GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | (intros; apply GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardTwoAffineHyperplanesStatement
section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_two_affine_hyperplanes : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k), a ≠ 0 → (∀ s : k, b ≠ s • a) →
  Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_two_equations | exact GlobalTheory.CompanionTheory.GapOpCount.card_two_equations | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_two_equations <;> assumption)
end

