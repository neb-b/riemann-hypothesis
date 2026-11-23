module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineBundleModelDegree
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DBlock
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDeterminantBound

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementA
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.Cocycle

section Generic

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
  [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]

theorem sameGeneric_self (E : ChartBundle O (mseg x) N V) : SameGeneric O x E E :=
  fun _ _ => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
    fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩

theorem sameGeneric_flip {E E' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E') :
    SameGeneric O x E' E :=
  fun s hs => ⟨(h s hs).2, (h s hs).1⟩

theorem sameGeneric_comp {E E' E'' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E')
    (h' : SameGeneric O x E' E'') : SameGeneric O x E E'' := by
  have step : ∀ {A B C : ChartBundle O (mseg x) N V} (s : ∀ k, ι k),
      (∀ v ∈ A.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B.lat s) →
      (∀ v ∈ B.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ C.lat s) →
      ∀ v ∈ A.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ C.lat s := by
    intro A B C s hAB hBC v hv
    obtain ⟨c, hc, hcv⟩ := hAB v hv
    obtain ⟨c', hc', hcv'⟩ := hBC _ hcv
    exact ⟨c' * c, mul_ne_zero hc' hc, by rwa [map_mul, mul_smul]⟩
  exact fun s hs => ⟨step s (h s hs).1 (h' s hs).1, step s (h' s hs).2 (h s hs).2⟩

end Generic

theorem length_classList {K : Type} {q m : ℕ} (cls : Fin q → K → ℤ) {Q : MvPolynomial (Fin q) ℤ}
    (hQ : Q.IsHomogeneous m) {μ : Fin q →₀ ℕ} (hμ : μ ∈ Q.support) :
    (classList cls μ).length = m := by
  have h := hQ (mem_support_iff.1 hμ)
  rw [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset, ← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Ba.Statement.{0,0,0} O Ω ι := by
  intro O _ _ _ Ω _ _ K _ ι _
  classical
  intro x d N V _ _ E E' E'' hM h1 h2 k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h13 : SameGeneric O x E E'' := sameGeneric_comp h1 h2
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hMB, hbir, hEB⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.CommonFlag.main O Ω K ι x d hM N 2 V ![E, E', E''] (by
      intro j
      fin_cases j
      · exact sameGeneric_self E
      · exact h1
      · exact h13)
  have hM' : IsModelOver (pointIdeal O (joinCoord x z)) d :=
    ((GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O _ d).1 hMB).2
  have p0 : IsPull O x z E (EB 0) := (hEB 0).1
  have p1 : IsPull O x z E' (EB 1) := (hEB 1).1
  have p2 : IsPull O x z E'' (EB 2) := (hEB 2).1
  have fr : ∀ j, IsFlagFrame (joinCoord x z) (EB j) w (b j) := fun j => (hEB j).2
  have tri : ∀ i j : Fin N, i < j → w.repr (w i) j = 0 := by
    intro i j hij
    simp [Module.Basis.repr_self, Finsupp.single_apply, ne_of_lt hij]
  have pair : ∀ i j, SameGeneric O (joinCoord x z) (EB i) (EB j) →
      SameGenericFibre ϖ (EB i) (EB j) ∧ ∃ f g : Fin N → MRing (Sum.elim ι ι') O,
        IsFlagPair ϖ (joinCoord x z) (EB i) (EB j) w w (b i) (b j) f g := fun i j hs =>
    _root_.GlobalTheory.CompanionTheory.Ar.FlagPairOfFrames.main O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hM' N V (EB i) (EB j) hs
      w w (b i) (b j) (fr i) (fr j) tri
  have s01 := (_root_.GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) p0 p1).2.1 h1
  have s12 := (_root_.GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E' E'' K' ι' z (EB 1) (EB 2) p1 p2).2.1 h2
  have s02 := (_root_.GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E'' K' ι' z (EB 0) (EB 2) p0 p2).2.1 h13
  obtain ⟨g01, f01, d01, c01⟩ := pair 0 1 s01
  obtain ⟨g12, f12, d12, c12⟩ := pair 1 2 s12
  obtain ⟨-, f02, d02, c02⟩ := pair 0 2 s02
  obtain ⟨-, f10, d10, c10⟩ := pair 1 0 (sameGeneric_flip s01)
  have num : ∀ {A B : ChartBundle O (mseg x) N V} (i j : Fin 3) (f g : Fin N → MRing (Sum.elim ι ι') O),
      SameGeneric O x A B → IsPull O x z A (EB i) → IsPull O x z B (EB j) →
      IsFlagPair ϖ (joinCoord x z) (EB i) (EB j) w w (b i) (b j) f g →
      ck O x d N A B k L Q = ∑ μ ∈ Q.support, Q.coeff μ *
        pairNum (pointIdeal O (joinCoord x z)) (b i) (b j) f g (psumExpansion N k)
          (classList (fun j => pullDeg (K' := K') (L j)) μ) := by
    intro A B i j f g hs pi pj hf
    exact (GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hM N V A B hs K' ι' z hMB hbir (EB i) (EB j) pi pj
      w w (b i) (b j) f g hf).1 k hk1 hk2 q L Q hQ
  have coc := fun μ (hμ : μ ∈ Q.support) =>
    _root_.GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed.pairCocycle O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) d hM' N V (EB 0) (EB 1) (EB 2)
      g01 g12 w w w (b 0) (b 1) (b 2) f01 d01 f12 d12 f02 d02 c01 c12 c02 k (psumExpansion N k)
      (psumExpansion N k) (psumExpansion N k) (isPairExpansion_psum N k) (isPairExpansion_psum N k)
      (isPairExpansion_psum N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)
      (by rw [length_classList _ hQ hμ]; omega)
  refine ⟨?_, ?_⟩
  · rw [num 0 2 f02 d02 h13 p0 p2 c02, num 0 1 f01 d01 h1 p0 p1 c01,
      num 1 2 f12 d12 h2 p1 p2 c12, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [(coc μ hμ).1, mul_add]
  · rw [num 1 0 f10 d10 (sameGeneric_flip h1) p1 p0 c10, num 0 1 f01 d01 h1 p0 p1 c01,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [(coc μ hμ).2 f10 d10 (psumExpansion N k) c10 (isPairExpansion_psum N k), mul_neg]

end GlobalTheory.CompanionTheory.Ar.Num.Cocycle
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementD
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.Constants

theorem cycEval_natCast_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (F : Ideal (MRing ι O) → ℤ) (P : Ideal (MRing ι O)) (c : MRing ι O) (n : ℕ) :
    cycEval F (fun W => (n : ℤ) * divCycle P c W) = (n : ℤ) * cycEval F (divCycle P c) := by
  unfold cycEval
  have hfin : (Function.support fun W => divCycle P c W * F W).Finite :=
    (ScalarQuotient.divCycle_support_finite P c).subset fun W hW => by
      rw [Function.mem_support] at hW ⊢
      exact fun h0 => hW (by rw [h0, zero_mul])
  rw [mul_finsum' _ _ hfin]
  exact finsum_congr fun W => by ring

theorem length_classList {K : Type} {q : ℕ} (cls : Fin q → K → ℤ) {Q : MvPolynomial (Fin q) ℤ} {e : ℕ}
    (hQ : Q.IsHomogeneous e) {μ : Fin q →₀ ℕ} (hμ : μ ∈ Q.support) :
    (classList cls μ).length = e := by
  have h := hQ (MvPolynomial.mem_support_iff.mp hμ)
  have h2 : Finsupp.degree μ = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact h
  rw [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  simpa [Finsupp.sum, Finsupp.degree_apply] using h2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Bd.Statement.{0,0,0} O Ω ι := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' g hg hmod hlat k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg hϖ
  have hsame : SameGeneric O x E E' := fun s hs =>
    ⟨fun v hv => ⟨_, hg, (hlat s hs _).2 ⟨v, hv, rfl⟩⟩, fun v hv => by
      obtain ⟨e, he, rfl⟩ := (hlat s hs v).1 hv
      exact ⟨_, hg, E.stable s _ (Subalgebra.algebraMap_mem _ _) _
        (E.stable s _ (Subalgebra.algebraMap_mem _ _) _ he)⟩⟩
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hJ, hbir, hall⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.CommonFlag.main O Ω K ι x d hmod N 1 V ![E, E'] (by
      intro j
      fin_cases j
      · exact fun s hs => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
          fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
      · exact hsame)
  have p0 : IsPull O x z E (EB 0) := (hall 0).1
  have p1 : IsPull O x z E' (EB 1) := (hall 1).1
  have hpull := _root_.GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) p0 p1
  have hsameJ := hpull.2.1 hsame
  have hscJ := hpull.2.2 _ hlat
  have hmodJ : IsModelOver (pointIdeal O (joinCoord x z)) d :=
    ((BundleExamples.isModelOver_iff O _ d).1 hJ).2
  obtain ⟨-, f, f', hpair⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagPairOfFrames.main O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hmodJ N V
    (EB 0) (EB 1) hsameJ w w (b 0) (b 1) (hall 0).2 (hall 1).2 (fun i j hij => by
      simp [Module.Basis.repr_self, hij.ne])
  have hnum := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hmod N V E E' hsame K' ι' z hJ hbir (EB 0) (EB 1) p0 p1
    w w (b 0) (b 1) f f' hpair
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have : d - (k - 1) = d + 1 - k := by omega
    rwa [this]
  have hroot := hnum.2 (k - 1) (psum (Fin N) ℤ (k - 1)) (psum_isSymmetric _ _ _)
    (isHomogeneous_psum N (k - 1)) (by omega) q L Q hQ'
  have hP : (pointIdeal O (joinCoord x z)).IsPrime := hmodJ.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing (Sum.elim ι ι') O) ∉ pointIdeal O (joinCoord x z) := by
    intro a ha hmem
    have h1 : a ∈ (pointIdeal O (joinCoord x z)).comap (C : O →+* MRing (Sum.elim ι ι') O) := hmem
    rw [hmodJ.noTorsion] at h1
    exact ha (Ideal.mem_bot.mp h1)
  have hdiv : ∀ (v : Oˣ) (m : ℕ),
      rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ((v : O) * ϖ ^ m) =
        (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ := by
    intro v m
    rw [hroot _ (mul_ne_zero v.ne_zero (pow_ne_zero _ hϖ.ne_zero)), hroot _ hϖ.ne_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [ScalarQuotient.divCycle_const _ hC hϖ.ne_zero v m, cycEval_natCast_mul]
    ring
  refine ⟨?_, ?_⟩
  · rw [hnum.1 k hk1 hk2 q L Q hQ, hdiv, hroot _ hϖ.ne_zero, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [_root_.GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) d hmodJ N V (EB 0) (EB 1) n u
      hscJ w w (b 0) (b 1) f f' hpair k (psumExpansion N k) (isPairExpansion_psum N k) _
      (by rw [length_classList _ hQ hμ]; omega)]
    ring
  · intro m n' h w' hw' hm hEq
    obtain ⟨W, rfl⟩ := hw'
    by_cases h0 : h = 0
    · subst h0
      have hn' : n' = 0 := by
        by_contra hne
        rw [zero_pow hne, mul_zero] at hEq
        exact pow_ne_zero m hg hEq
      subst hn'
      have hnm : n * m = 0 := by
        refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) W _ _ ?_
        rw [pow_zero, mul_one] at hEq ⊢
        rw [Units.val_pow_eq_pow_val, pow_mul, ← mul_pow, hEq]
      have hn0 : n = 0 := by
        rcases Nat.mul_eq_zero.mp hnm with h | h
        · exact h
        · omega
      subst hn0
      rw [hdiv u 0]
      simp
    · obtain ⟨a, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
      have hnm : n * m = a * n' := by
        refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) (W * v ^ n') _ _ ?_
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        rw [pow_mul, pow_mul, ← mul_pow, hEq, mul_pow, mul_assoc]
      have hnm' : (n : ℤ) * m = a * n' := by exact_mod_cast hnm
      rw [hdiv u n, hdiv v a]
      linear_combination rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ * hnm'

end GlobalTheory.CompanionTheory.Ar.Num.Constants
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineBundleChartGenericComparison
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.CkLinePow

section Lists

variable {K : Type*} {σ : Type*}

theorem headAdd_zsmul {A : List (K → ℤ) → ℤ} (hA : HeadAdd A) (m : ℤ) (u : K → ℤ)
    (l : List (K → ℤ)) : A ((m • u) :: l) = m * A (u :: l) := by
  let φ : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun v => A (v :: l)) fun v w => hA v w l
  exact map_zsmul φ m u

theorem map_zsmul_append {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A) (m : ℤ)
    (l r : List (K → ℤ)) : A (l.map (m • ·) ++ r) = m ^ l.length * A (l ++ r) := by
  induction l generalizing r with
  | nil => simp
  | cons u l ih =>
    rw [List.map_cons, List.cons_append, headAdd_zsmul hA,
      hp _ _ (List.perm_middle (a := u) (l₁ := l.map (m • ·)) (l₂ := r)).symm, ih,
      hp _ _ (List.perm_middle (a := u) (l₁ := l) (l₂ := r)), List.length_cons, List.cons_append]
    ring

theorem length_classList (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ}
    (hH : H.IsHomogeneous n) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = n := by
  have h1 := hH (mem_support_iff.mp hμ)
  rw [← h1]
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply]
  simp [Finsupp.sum]

theorem polyVal_zsmul {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A) (m : ℤ)
    (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ} (hH : H.IsHomogeneous n) :
    polyVal A (fun s => m • cls s) H = m ^ n * polyVal A cls H := by
  unfold polyVal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hperm : (classList (fun s => m • cls s) μ).Perm ((classList cls μ).map (m • ·) ++ []) := by
    unfold classList
    rw [List.append_nil, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Multiset.coe_toList, Multiset.map_map]
    rfl
  rw [hp _ _ hperm, map_zsmul_append hp hA, length_classList cls hH hμ, List.append_nil]
  ring

end Lists

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isVerticalDivisor_swap {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) : IsVerticalDivisor P ϖ (-b) g f := by
  refine {
    degrees := ?_
    num_not_mem := hD.den_not_mem
    den_not_mem := hD.num_not_mem
    vertical := ?_
    unit_off_special := ?_ }
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨bg, bf, hg, hf, ?_⟩
    rw [← hb]
    funext k
    simp
  · intro W hW
    apply hD.vertical W
    intro h
    apply hW
    unfold ratDiv at h ⊢
    linarith
  · intro W hW hPW hrel hϖ
    obtain ⟨u, v, hu, hv, h⟩ := hD.unit_off_special W hW hPW hrel hϖ
    refine ⟨v, u, hv, hu, ?_⟩
    rw [← neg_sub]
    exact P.neg_mem h

theorem exists_zpow {Ω : Type} [Field Ω] (φ : MRing ι O →+* Ω) {P : Ideal (MRing ι O)} [P.IsPrime]
    {ϖ : O} {b : K → ℤ} {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g) {u : Ω} (hu : u ≠ 0)
    (hfg : φ f * u = φ g) (m : ℤ) :
    ∃ F G : MRing ι O, IsVerticalDivisor P ϖ (m • b) F G ∧ φ F * u ^ m = φ G ∧
      ∀ W, ratDiv P F G W = m * ratDiv P f g W := by
  induction m using Int.induction_on with
  | zero =>
    refine ⟨1, 1, ?_, by simp, fun W => by simp [ratDiv]⟩
    rw [zero_smul]
    exact isVerticalDivisor_one ϖ P
  | succ n ih =>
    obtain ⟨F, G, hFG, hv, hr⟩ := ih
    refine ⟨F * f, G * g, ?_, ?_, fun W => ?_⟩
    · rw [add_smul, one_smul]
      exact isVerticalDivisor_mul hFG hD
    · rw [zpow_add_one₀ hu, map_mul, map_mul, ← hv, ← hfg]
      ring
    · rw [ratDiv_mul hFG.num_not_mem hFG.den_not_mem hD.num_not_mem hD.den_not_mem, Pi.add_apply,
        hr]
      ring
  | pred n ih =>
    obtain ⟨F, G, hFG, hv, hr⟩ := ih
    refine ⟨F * g, G * f, ?_, ?_, fun W => ?_⟩
    · rw [sub_smul, one_smul, sub_eq_add_neg]
      exact isVerticalDivisor_mul hFG (isVerticalDivisor_swap hD)
    · rw [zpow_sub_one₀ hu, map_mul, map_mul, ← hv, ← hfg]
      field_simp
    · rw [ratDiv_mul hFG.num_not_mem hFG.den_not_mem hD.den_not_mem hD.num_not_mem, Pi.add_apply,
        hr]
      unfold ratDiv
      ring

theorem pairNum_scale {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ}
    (hP : IsModelOver P d) {a b : K → ℤ} {f g F G : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (m : ℤ) (hr : ∀ W, ratDiv P F G W = m * ratDiv P f g W)
    {k : ℕ} (hk : 1 ≤ k) {Q : List (K → ℤ)} (hQ : Q.length + k = d + 1) :
    pairNum P (fun _ : Fin 1 => m • a) (fun _ => 0) (fun _ => F) (fun _ => G)
        (psumExpansion 1 k) Q =
      m ^ k * pairNum P (fun _ : Fin 1 => a) (fun _ => 0) (fun _ => f) (fun _ => g)
        (psumExpansion 1 k) Q := by
  unfold pairNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hH := isHomogeneous_psumExpansion 1 k i
  have hn : k - 1 + Q.length = d := by omega
  have hcls : (Sum.elim (fun _ : Fin 1 => m • a) (fun _ : Fin 1 => (0 : K → ℤ))) =
      fun s => m • (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => (0 : K → ℤ))) s := by
    funext s
    cases s <;> simp
  unfold cycEval
  rw [mul_finsum]
  refine finsum_congr fun W => ?_
  beta_reduce
  rw [hr W]
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  rw [classNum_eq_polyVal _ hH hn, classNum_eq_polyVal _ hH hn, hcls,
    polyVal_zsmul (listNum_perm W Q d) (listNum_headAdd IntNumAddFirst.full hϖ hP hD hW Q) m _ hH]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (A T Am : ChartBundle O (mseg x) 1 Ω) (u : Ω) (a : K → ℤ) (m : ℤ), u ≠ 0 → IsLine O x u a A.lat → IsLine O x 1 0 T.lat → SameGeneric O x A T → IsLine O x (u ^ m) (m • a) Am.lat → SameGeneric O x Am T ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d 1 Am T k L Q = m ^ k * ck O x d 1 A T k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM A T Am u a m hu hA hT hS hAm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hW⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
  have hW' : GroundTheory.Heights₂.Heights.NumbersDVR.IsModelOver (pointIdeal O x) d := hW
  have hS' := (BundleExamples.sameGeneric_iff hϖ x A T).mp hS
  obtain ⟨f, g, hD, hfg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.VertDiv.commensurable_vertical O Ω K ι x ϖ hϖ d hW' a 0 u⁻¹ (inv_ne_zero hu) (by
    intro s hs
    obtain ⟨h1, h2⟩ := hS' s hs
    constructor
    · obtain ⟨n, hn⟩ := h1 _ ((hA s hs _).2 ⟨1, one_mem _, rfl⟩)
      obtain ⟨r, hr, e⟩ := (hT s hs _).1 hn
      refine ⟨n, r, hr, ?_⟩
      rw [smul_eq_mul] at e
      apply mul_left_cancel₀ hu
      field_simp
      linear_combination e
    · obtain ⟨n, hn⟩ := h2 _ ((hT s hs _).2 ⟨1, one_mem _, rfl⟩)
      obtain ⟨r, hr, e⟩ := (hA s hs _).1 hn
      refine ⟨n, r, hr, ?_⟩
      rw [smul_eq_mul] at e
      apply mul_left_cancel₀ hu
      field_simp
      linear_combination e)
  have hfg' : aeval x f * u = aeval x g := by
    rw [hfg]
    field_simp
  have : (pointIdeal O x).IsPrime := hW'.multiProj.isPrime
  obtain ⟨F, G, hFG, hv, hr⟩ := exists_zpow
    (aeval x : MRing ι O →ₐ[O] Ω).toRingHom hD hu hfg' m
  have hFG' : IsVerticalDivisor (pointIdeal O x) ϖ (m • a - 0) F G := by
    simpa using hFG
  obtain ⟨hs1, h1⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.LineCk.main O Ω K ι x ϖ hϖ d hM Am T (u ^ m) 1 (m • a) 0 hAm hT F G hFG'
    (by rw [mul_one]; exact hv)
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.LineCk.main O Ω K ι x ϖ hϖ d hM A T u 1 a 0 hA hT f g hD
    (by rw [mul_one]; exact hfg')
  refine ⟨hs1, fun k hk1 hk2 q L Q hQ => ?_⟩
  rw [h1 k hk1 hk2 q L Q hQ, h2 k hk1 hk2 q L Q hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [pairNum_scale hϖ hW' hD m hr hk1
    (by rw [length_classList L hQ hμ]; omega)]
  ring

end GlobalTheory.CompanionTheory.Ar.CkLinePow
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNorm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem orthogonalBlock_gram_det_log_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (gramE D (x ∘ Sum.inr)).det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inr)).det‖ = -(q : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) :=
  @PositivityTheory.Xgf.local_basis_gram_det_log_norm

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDeterminantBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_basis_gram_determinant_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes), p + q = D.p + D.q → ∃ x : Fin p ⊕ Fin q → D.La, IsLocBasis (𝓞 E) ℓ x ∧ (gramE D (x ∘ Sum.inl)).det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inl)).det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.LocR.exists_locBasis_first_unimodular | exact GlobalTheory.CompanionTheory.Ar.Fl.LocR.exists_locBasis_first_unimodular | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.LocR.exists_locBasis_first_unimodular <;> assumption)
end

