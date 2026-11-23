module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0009
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAll
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem intersection_combLine_expansion : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin d → J → ℤ), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (fun k => combLine ℓ (n k)) = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) :=
  @RootFieldNumerics.intersection_multilinear_expansion

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumTermDiscreteValuation
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ), Q.IsHomogeneous (d + 1 - k) → (∀ i, (Hs i).IsHomogeneous (d - k)) → (k = d + 1 → ∀ i, Hs i = 0) → ∀ T : LocPair ι O (Ψ × Fin N), T.IsVert P ϖ → FlagChernComparison P d p j φ T → PowerSumsVanish P d (fun i : Fin N => T.x' (τ, i)) → T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) = cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ * Q) [] := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP p Ψ _ _ N j φ k hk1 hkd τ Q Hs hQ hHs hH0 T hT hM hPS
  obtain ⟨hadd, hsmul, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.locPair_val_linear O K ι (Ψ × Fin N) T P
  have hB : T.val P (fun i => (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) = 0 := by
    rcases Nat.lt_or_ge k (d + 1) with hlt | hge
    · exact _root_.GlobalTheory.CompanionTheory.Ar.Num.val_psum_mul_eq_zero O ϖ hϖ K ι P d hP (Ψ × Fin N) T hT N (fun a => (τ, a)) hPS k (d - k) hk1
        (by omega) Hs hHs
    · have hk : k = d + 1 := by omega
      have h0 := hsmul 0 (fun _ => 0)
      simp only [mul_zero, zero_mul] at h0
      have hfun : (fun i => (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) =
          (fun _ => (0 : MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ)) := by
        funext i
        rw [hH0 hk i, mul_zero]
      rw [hfun]
      exact h0
  have hA : T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i),
        rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a)))
          (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q) =
      cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ * Q) [] := by
    rw [_root_.GlobalTheory.CompanionTheory.Ar.Num.val_psumExpansion_mul O K ι (Ψ × Fin N) T P N k (fun a => (τ, a)) (rename Sum.inl Q),
      support_rename_of_injective Sum.inl_injective,
      Finset.sum_image (Finsupp.mapDomain_injective Sum.inl_injective).injOn,
      _root_.GlobalTheory.CompanionTheory.Ar.Num.cycNum_mul O K ι (Ψ × Fin N) (divCycle P (C (p : O))) T.x (bracket j φ p k τ) Q []]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hcl : classList (Sum.elim T.x T.x') (Finsupp.mapDomain Sum.inl μ) = classList T.x μ := by
      have hm : Finsupp.toMultiset (Finsupp.mapDomain (Sum.inl : Ψ × Fin N → (Ψ × Fin N) ⊕ (Ψ × Fin N)) μ) =
          (Finsupp.toMultiset μ).map Sum.inl := (Finsupp.toMultiset_map μ Sum.inl).symm
      unfold classList
      rw [hm, Multiset.map_map]
      rfl
    have hdeg : (classList T.x μ).length + k = d + 1 := by
      have h1 : (classList T.x μ).length = d + 1 - k := by
        have h2 := hQ (mem_support_iff.mp hμ)
        unfold classList
        rw [Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
        rw [Finsupp.weight_apply] at h2
        exact (by simpa using h2 : (μ.sum fun _ c => c) = d + 1 - k)
      omega
    rw [coeff_rename_mapDomain _ Sum.inl_injective, hcl, List.append_nil, hM τ k hk1 _ hdeg]
  exact (hadd _ _).trans (by rw [hA, hB, add_zero])
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ResidueModelAtPrime
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem mem_of_residue_map_mem_specialIdeal {K : Type} [DecidableEq K] {ι : K → Type} {O : Type}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {W : Ideal (MRing ι O)}
    (hW : (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O) ≤ W) {f : MRing ι O}
    (hf : MvPolynomial.map (IsLocalRing.residue O) f ∈ specialIdeal W) : f ∈ W := by
  obtain ⟨g, hg, hgf⟩ := (Ideal.mem_map_iff_of_surjective _
    (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective)).1 hf
  have hker : f - g ∈ W := by
    apply hW
    rw [MvPolynomial.mem_map_C_iff]
    intro d
    rw [← IsLocalRing.residue_eq_zero_iff]
    have h := congrArg (AddMonoidAlgebra.coeff · d) hgf
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at h
    rw [MvPolynomial.coeff_sub, map_sub, h, sub_self]
  have := W.add_mem hker hg
  simpa using this

theorem map_mem_pointIdeal {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {A O : Type} [CommRing A] [CommRing O] [Algebra A O] [Algebra A Ω]
    [Algebra O Ω] [IsScalarTower A O Ω] {f : MRing ι A} (hf : f ∈ pointIdeal A y) :
    MvPolynomial.map (algebraMap A O) f ∈ pointIdeal O y := by
  rw [pointIdeal, RingHom.mem_ker] at hf ⊢
  rw [← hf]
  simp only [pointConeMap]
  exact MvPolynomial.aeval_map_algebraMap _ _ _

theorem isMultiHomog_map {K : Type} [DecidableEq K] {ι : K → Type} {R S : Type} [CommRing R]
    [CommRing S] (φ : R →+* S) {G : MRing ι R} {b : K → ℕ} (hG : IsMultiHomog G b) :
    IsMultiHomog (MvPolynomial.map φ G) b := by
  intro d hd
  apply hG
  intro h0
  apply hd
  rw [MvPolynomial.coeff_map, h0, map_zero]

theorem intNumL_zmod_eq_residueDegree_mul_vNumL : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], HasConstants ℤ A y → ∀ (p : ℕ) [Fact p.Prime] (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], (p : A) ∈ m → ∀ fd : ℕ, Nat.card (A ⧸ m) = p ^ fd → ∀ W' : Ideal (MRing ι O), W'.IsPrime → IsMultiHomogIdeal W' → pointIdeal O y ≤ W' → (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O) ≤ W' → ∀ l : List (K → ℤ), intNumL (ZMod p) (extTo (ZMod p) (W'.comap (MvPolynomial.map (Int.castRingHom O)))) l = (fd : ℤ) * vNumL W' l := by
  intro K _ _ ι _ Ω _ y A _ _ _ _ hconst p _ m _ O _ _ _ _ _ _ _ hpm fd hcard W' hWp hWh hpt hϖ l
  have hmne : m ≠ ⊥ := by
    intro h
    apply IsDiscreteValuationRing.not_a_field O
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m O, h, Ideal.map_bot]
  haveI hmax : m.IsMaximal := Ideal.IsPrime.isMaximal ‹_› hmne
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal m O
  have hsurj : ∀ x : IsLocalRing.ResidueField O, ∃ a : A,
      IsLocalRing.residue O (algebraMap A O a) = x := by
    intro x
    obtain ⟨q, hq⟩ := e.surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨a, ?_⟩
    rw [← hq]
    exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk m O a).symm
  have hcardκ : Nat.card (IsLocalRing.ResidueField O) = p ^ fd :=
    (Nat.card_congr e.toEquiv).symm.trans hcard
  have hp0 : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    have h1 : algebraMap A O (p : A) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff O m _).2 hpm
    have h2 := (IsLocalRing.residue_eq_zero_iff _).2 h1
    simpa using h2
  haveI hchar : CharP (IsLocalRing.ResidueField O) p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (ringChar.dvd hp0) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h ▸ ringChar.charP _
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField O) := ZMod.algebra _ p
  haveI hfin : Finite (IsLocalRing.ResidueField O) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardκ]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  haveI : FiniteDimensional (ZMod p) (IsLocalRing.ResidueField O) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) (IsLocalRing.ResidueField O) = fd := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := IsLocalRing.ResidueField O)
    rw [hcardκ, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  have hhom : (algebraMap (ZMod p) (IsLocalRing.ResidueField O)).comp
      (Int.castRingHom (ZMod p)) = (IsLocalRing.residue O).comp (Int.castRingHom O) :=
    Subsingleton.elim _ _
  have hmm : ∀ g : MRing ι ℤ,
      MvPolynomial.map (algebraMap (ZMod p) (IsLocalRing.ResidueField O))
        (MvPolynomial.map (Int.castRingHom (ZMod p)) g) =
      MvPolynomial.map (IsLocalRing.residue O) (MvPolynomial.map (Int.castRingHom O) g) := by
    intro g
    rw [MvPolynomial.map_map, MvPolynomial.map_map, hhom]
  have hcomap : (specialIdeal W').comap
      (MvPolynomial.map (algebraMap (ZMod p) (IsLocalRing.ResidueField O))) =
      extTo (ZMod p) (W'.comap (MvPolynomial.map (Int.castRingHom O))) := by
    have hs : Function.Surjective
        (MvPolynomial.map (σ := (Σ k, ι k)) (Int.castRingHom (ZMod p))) :=
      MvPolynomial.map_surjective _ (ZMod.ringHom_surjective _)
    ext g
    obtain ⟨g0, rfl⟩ := hs g
    rw [Ideal.mem_comap, hmm, extTo]
    constructor
    · intro h
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.2 (mem_of_residue_map_mem_specialIdeal hϖ h))
    · intro h
      obtain ⟨g1, hg1, hg⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 h
      rw [← hmm, ← hg, hmm]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.1 hg1)
  have hsu : ∀ (c : ∀ k, ι k) (a : IsLocalRing.ResidueField O), ∃ (n : ℕ)
      (G : MRing ι (ZMod p)), IsMultiHomog G (fun _ => n) ∧
      C a * (∏ k, X ⟨k, c k⟩) ^ n -
        MvPolynomial.map (algebraMap (ZMod p) (IsLocalRing.ResidueField O)) G ∈
        specialIdeal W' := by
    intro c a
    obtain ⟨a0, rfl⟩ := hsurj a
    obtain ⟨n, G, hG, hmem⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.const_mul_chartMonomial_pow_form K ι Ω y A hconst c a0
    refine ⟨n, MvPolynomial.map (Int.castRingHom (ZMod p)) G, isMultiHomog_map _ hG, ?_⟩
    have h1 := hpt (map_mem_pointIdeal (O := O) hmem)
    have h2 : MvPolynomial.map (IsLocalRing.residue O) _ ∈ specialIdeal W' :=
      Ideal.mem_map_of_mem _ h1
    rw [hmm]
    have hG' : MvPolynomial.map (IsLocalRing.residue O) (MvPolynomial.map (algebraMap A O)
        (MvPolynomial.map (Int.castRingHom A) G)) =
        MvPolynomial.map (IsLocalRing.residue O) (MvPolynomial.map (Int.castRingHom O) G) := by
      simp only [MvPolynomial.map_map]
      exact congrArg (fun φ : ℤ →+* IsLocalRing.ResidueField O => MvPolynomial.map φ G)
        (Subsingleton.elim _ _)
    simpa [hG'] using h2
  have key := _root_.GlobalTheory.CompanionTheory.Ar.Num.intNumL_subfield_constants K ι (ZMod p) (IsLocalRing.ResidueField O) (specialIdeal W')
    (SpecialIdealMultiHomog.full O K ι W' hWh) hsu l
  rw [hcomap, hfr] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerSymmetryLimitCompat
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Top.PermInv

theorem exists_word_multiset {α : Type} (s : Multiset α) :
    ∃ w : Fin (Multiset.card s) → α, ∑ k, ({w k} : Multiset α) = s := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨Fin.elim0, by simp⟩
  | cons a s ih =>
    obtain ⟨w, hw⟩ := ih
    rw [Multiset.card_cons]
    refine ⟨Fin.cons a w, ?_⟩
    rw [Fin.sum_univ_succ]
    simp [hw, Multiset.singleton_add]

theorem degree_eq_card {α : Type} (μ : α →₀ ℕ) : μ.degree = Multiset.card (Finsupp.toMultiset μ) := by
  rw [Finsupp.card_toMultiset]
  rfl

theorem exists_word {α : Type} (μ : α →₀ ℕ) (d : ℕ) (h : μ.degree = d) :
    ∃ w : Fin d → α, ∑ k, Finsupp.single (w k) 1 = μ := by
  subst h
  have hc : Multiset.card (Finsupp.toMultiset μ) = μ.degree := (degree_eq_card μ).symm
  obtain ⟨w, hw⟩ := exists_word_multiset (Finsupp.toMultiset μ)
  refine ⟨fun k => w (Fin.cast hc.symm k), ?_⟩
  classical
  have H : Finsupp.toMultiset (∑ k, Finsupp.single (w (Fin.cast hc.symm k)) 1) = Finsupp.toMultiset μ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    exact (Fintype.sum_equiv (finCongr hc.symm) _ _ (fun k => rfl)).trans hw
  simpa [Finsupp.toMultiset_toFinsupp] using congrArg Multiset.toFinsupp H

theorem degree_mapDomain {α β : Type} (f : α → β) (μ : α →₀ ℕ) :
    (Finsupp.mapDomain f μ).degree = μ.degree := by
  rw [degree_eq_card, degree_eq_card, ← Finsupp.toMultiset_map, Multiset.card_map]

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem arMono_word (M : RootModel Ψ N) (II : IntersectionSystem) (hII : IsIntersectionSystem II) (t : ℝ)
    (w : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    M.arMono II t (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1)) =
      II _ _ M.P _ (fun j => M.x t (w j)) / (M.δ : ℝ) := by
  have e : Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1) =
      ∑ k, Finsupp.single (some (w k)) (1 : ℕ) := by
    simp [Finsupp.mapDomain_finsetSum]
  obtain ⟨hdeg, -, -, hv⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.monoLines_monomial_word II hII M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) (fun k => some (w k))
    M.arith (by rintro (_ | r); exacts [M.A_smooth, M.x_smooth t r])
  have hnone : (∑ k, Finsupp.single (some (w k)) (1 : ℕ) : Option (Ψ × Fin N) →₀ ℕ) none = 0 := by
    simp [Finsupp.finsetSum_apply]
  rw [e, RootModel.arMono, if_pos hdeg, hnone, pow_zero, mul_one, hv]
  rfl

end GlobalTheory.CompanionTheory.Ar.Top.PermInv

namespace GlobalTheory.CompanionTheory.Ar.Top.PermInv

theorem limUnder_arMono_perm {Ψ : Type} [Fintype Ψ] {N : ℕ} (M M' : RootModel Ψ N) (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) (hM : M.Converges II) (hM' : M'.Converges II) (σ : Equiv.Perm Ψ)
    (hlim : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M.P _ (fun j => M.x t (σ (w j).1, (w j).2)) /
      (M.δ : ℝ) - II _ _ M'.P _ (fun j => M'.x t (w j)) / (M'.δ : ℝ)) (𝓝[>] 0) (𝓝 0))
    (μ : Ψ × Fin N →₀ ℕ) :
    (limUnder (𝓝[>] (0 : ℝ)) fun t => M.arMono II t
        (Finsupp.mapDomain some (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) μ))) =
      limUnder (𝓝[>] (0 : ℝ)) fun t => M'.arMono II t (Finsupp.mapDomain some μ) := by
  by_cases hd : μ.degree = dimFl Ψ N + 1
  · obtain ⟨w, rfl⟩ := exists_word μ _ hd
    have e : Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1) =
        ∑ k, Finsupp.single (σ (w k).1, (w k).2) (1 : ℕ) := by
      simp [Finsupp.mapDomain_finsetSum]
    have hf : (fun t => M.arMono II t (Finsupp.mapDomain some
        (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1)))) =
        fun t => II _ _ M.P _ (fun j => M.x t (σ (w j).1, (w j).2)) / (M.δ : ℝ) := by
      funext t
      rw [e]
      exact arMono_word M II hII t (fun k => (σ (w k).1, (w k).2))
    have hg : (fun t => M'.arMono II t (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1))) =
        fun t => II _ _ M'.P _ (fun j => M'.x t (w j)) / (M'.δ : ℝ) := by
      funext t
      exact arMono_word M' II hII t w
    obtain ⟨L1, h1⟩ := hM (Finsupp.mapDomain some
        (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1)))
    obtain ⟨L2, h2⟩ := hM' (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1))
    rw [h1.limUnder_eq, h2.limUnder_eq]
    rw [hf] at h1
    rw [hg] at h2
    exact sub_eq_zero.1 (tendsto_nhds_unique (h1.sub h2) (hlim w))
  · have h0 : ∀ (K : RootModel Ψ N) (m : Ψ × Fin N →₀ ℕ), m.degree = μ.degree →
        (fun t => K.arMono II t (Finsupp.mapDomain some m)) = fun _ => 0 := by
      intro K m hm
      funext t
      rw [RootModel.arMono, if_neg (by rw [degree_mapDomain, hm]; exact hd)]
    rw [h0 M _ (degree_mapDomain _ μ), h0 M' μ rfl]

theorem propA_of_limits : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : GlobalTheory.CompanionTheory.Ar.Top.RootTower Ψ N)
    (II : IntersectionSystem) (Γ : Subgroup (Equiv.Perm Ψ)), T.Conv II → (∀ τ τ' : Ψ, ∃ s ∈ Γ, s τ = τ') →
    (∀ s ∈ Γ, ∀ B : ℕ, 2 ≤ B → ∃ π : Equiv.Perm T.Comp, ∀ (c : T.Comp)
      (w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N),
      Tendsto (fun t => II _ _ (T.M B c).P _ (fun j => (T.M B c).x t (s (w j).1, (w j).2)) / (T.M B c).δ -
        II _ _ (T.M B (π c)).P _ (fun j => (T.M B (π c)).x t (w j)) / (T.M B (π c)).δ) (𝓝[>] 0) (𝓝 0)) →
    IsIntersectionSystem II → T.PropA II := by
  intro Ψ _ _ N T II Γ hC htr hlim hII
  refine ⟨Γ, htr, fun σ hσ B hB F => ?_⟩
  obtain ⟨π, hπ⟩ := hlim σ hσ B hB
  have hb : ∀ (m : Option (Ψ × Fin N) →₀ ℕ) (a : ℝ),
      (monomial m a : RPA Ψ N) = a • (basisMonomials (Option (Ψ × Fin N)) ℝ) m := by
    intro m a
    simp [coe_basisMonomials, smul_monomial]
  have hmono : ∀ (c : T.Comp) (μ : Ψ × Fin N →₀ ℕ) (a : ℝ),
      T.PPc II B c (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) (monomial μ a)) =
        T.PPc II B (π c) (monomial μ a) := by
    intro c μ a
    simp only [RootTower.PPc, toA, rename_monomial]
    rw [hb, hb, map_smul, map_smul, RootModel.PP, RootModel.PP, Module.Basis.constr_basis,
      Module.Basis.constr_basis,
      limUnder_arMono_perm (T.M B c) (T.M B (π c)) II hII (hC B c) (hC B (π c)) σ (hπ c) μ]
  have hsum : ∀ (c : T.Comp) (f : RP Ψ N →ₐ[ℝ] RP Ψ N),
      T.PPc II B c (f F) = ∑ μ ∈ F.support, T.PPc II B c (f (monomial μ (F.coeff μ))) := by
    intro c f
    conv_lhs => rw [F.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RootTower.PPc, toA, map_sum]
  calc T.PPt II B (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F)
      = ∑ c, ∑ μ ∈ F.support, T.PPc II B (π c) (monomial μ (F.coeff μ)) := by
        unfold RootTower.PPt
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hsum c (rename (fun x : Ψ × Fin N => (σ x.1, x.2)))]
        exact Finset.sum_congr rfl fun μ _ => hmono c μ _
    _ = ∑ c, ∑ μ ∈ F.support, T.PPc II B c (monomial μ (F.coeff μ)) :=
        Equiv.sum_comp π (fun c => ∑ μ ∈ F.support, T.PPc II B c (monomial μ (F.coeff μ)))
    _ = T.PPt II B F := by
        unfold RootTower.PPt
        refine Finset.sum_congr rfl fun c _ => ?_
        have := hsum c (AlgHom.id ℝ (RP Ψ N))
        simpa using this.symm

end GlobalTheory.CompanionTheory.Ar.Top.PermInv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremB
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem thmB_functional : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh :=
  @RootFieldNumerics.antisymmetry_tower_theorem

end GlobalTheory.CompanionTheory.Ar.Top
end

