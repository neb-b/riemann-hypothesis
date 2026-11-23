module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturation
section
open MvPolynomial Filter

namespace GlobalTheory

namespace SatHilb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι K : Type*} [Field K]

end SatHilb

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma homogeneousComponent_add_X_pow_mul {K : Type} [Field K] {N : ℕ} (j : Fin N) (m n : ℕ)
    (g : MvPolynomial (Fin N) K) :
    homogeneousComponent (n + m) (X j ^ m * g) = X j ^ m * homogeneousComponent n g := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← sum_homogeneousComponent g, Finset.mul_sum, map_sum]
  have hterm : ∀ i, homogeneousComponent (n + m) (X j ^ m * homogeneousComponent i g) =
      if n + m = m + i then X j ^ m * homogeneousComponent i g else 0 := fun i =>
    homogeneousComponent_of_mem
      (((isHomogeneous_X_pow j m).mul (homogeneousComponent_isHomogeneous i g)))
  simp_rw [hterm]
  rw [Finset.sum_eq_single n]
  · simp [add_comm]
  · intro i _ hi
    rw [if_neg (by omega)]
  · intro hn
    rw [Finset.mem_range, not_lt] at hn
    rw [homogeneousComponent_eq_zero n g (by omega), mul_zero, ite_self]

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma homogeneousComponent_mem_of_isPrime_of_X_pow_saturation {K : Type} [Field K] {N : ℕ}
    {I Q : Ideal (MvPolynomial (Fin N) K)}
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) (hQ : Q.IsPrime) (hIQ : I ≤ Q)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    ∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q := by
  by_cases hX : ∀ j, X j ∈ Q
  · have hspan : Ideal.span (X '' Set.univ) ≤ Q := by
      rw [Ideal.span_le]
      rintro _ ⟨j, -, rfl⟩
      exact hX j
    intro g hg n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hsub : g - C (AddMonoidAlgebra.coeff g 0) ∈ Q := by
        apply hspan
        rw [mem_ideal_span_X_image]
        intro e he
        have he0 : e ≠ 0 := by
          rintro rfl
          simp at he
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
        exact ⟨i, Set.mem_univ _, hi⟩
      rw [homogeneousComponent_zero]
      have := Q.sub_mem hg hsub
      simpa using this
    · apply hspan
      rw [mem_ideal_span_X_image]
      intro e he
      rw [mem_support_iff, coeff_homogeneousComponent] at he
      have hdeg : e.degree = n := by
        by_contra hne
        exact he (if_neg hne)
      have he0 : e ≠ 0 := by
        rintro rfl
        simp at hdeg
        omega
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
      exact ⟨i, Set.mem_univ _, hi⟩
  · push_neg at hX
    obtain ⟨j, hj⟩ := hX
    intro g hg n
    obtain ⟨m, hm⟩ := hs g hg j
    have hmem := hIQ (hI _ hm (n + m))
    rw [homogeneousComponent_add_X_pow_mul] at hmem
    rcases hQ.mem_or_mem hmem with h | h
    · exact absurd (hQ.mem_of_pow_mem m h) hj
    · exact h

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma exists_homogeneous_mem_of_X_pow_mul_mem_of_homogeneous {K : Type} [Field K] {N : ℕ}
    {I Q : Ideal (MvPolynomial (Fin N) K)}
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    ∃ L : ℕ, ∀ n ≥ L, ∀ h ∈ Q, h ∈ homogeneousSubmodule (Fin N) K n → h ∈ I := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian Q : Q.FG)
  choose! mexp hmexp using hs
  set M := G.sup fun g => Finset.univ.sup (mexp g)
  set D := G.sup totalDegree
  set B := N * M + 1
  have hkey : ∀ g ∈ G, ∀ e : Fin N →₀ ℕ, B ≤ (e.sum fun _ k => k) → ∀ a : K,
      monomial e a * g ∈ I := by
    intro g hgG e he a
    have hgQ : g ∈ Q := hG ▸ Submodule.subset_span hgG
    have hj : ∃ j, M ≤ e j := by
      by_contra hne
      push_neg at hne
      have hsum : (e.sum fun _ k => k) ≤ N * M := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        calc ∑ j, e j ≤ ∑ _j : Fin N, M := Finset.sum_le_sum fun j _ => (hne j).le
          _ = N * M := by simp
      omega
    obtain ⟨j, hjM⟩ := hj
    have hle : mexp g j ≤ e j :=
      le_trans (le_trans (Finset.le_sup (f := mexp g) (Finset.mem_univ j))
        (Finset.le_sup (f := fun g => Finset.univ.sup (mexp g)) hgG)) hjM
    have hsingle : Finsupp.single j (mexp g j) ≤ e := by
      rw [Finsupp.single_le_iff]
      exact hle
    have hsplit : monomial e a =
        monomial (e - Finsupp.single j (mexp g j)) a * X j ^ mexp g j := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, tsub_add_cancel_of_le hsingle]
    rw [hsplit, mul_assoc]
    exact I.mul_mem_left _ (hmexp g hgQ j)
  refine ⟨B + D, fun n hn h hQ hh => ?_⟩
  have hhn : h = homogeneousComponent n h := by
    rw [homogeneousComponent_of_mem hh, if_pos rfl]
  rw [← hG] at hQ
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hQ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hhn, ← hf, map_sum]
  refine I.sum_mem fun g hgG => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [smul_eq_mul, as_sum (f g), Finset.sum_mul, map_sum]
  refine I.sum_mem fun e _ => ?_
  by_cases hdeg : B ≤ (e.sum fun _ k => k)
  · exact hI _ (hkey g hgG e hdeg _) n
  · rw [homogeneousComponent_eq_zero]
    · exact I.zero_mem
    · have h1 := totalDegree_mul (monomial e (AddMonoidAlgebra.coeff (f g) e)) g
      have h2 := totalDegree_monomial_le e (AddMonoidAlgebra.coeff (f g) e)
      have h3 : g.totalDegree ≤ D := Finset.le_sup (f := totalDegree) hgG
      have h4 : (e.sum fun _ => id) = (e.sum fun _ k => k) := rfl
      omega

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma coe_decompose_homogeneousSubmodule_eq_homogeneousComponent {K : Type} [Field K] {N : ℕ}
    (g : MvPolynomial (Fin N) K) (n : ℕ) :
    ((DirectSum.decompose (homogeneousSubmodule (Fin N) K) g n : MvPolynomial (Fin N) K)) =
      homogeneousComponent n g := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_eq_single n]
  · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g)
  · intro i _ hi
    exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) hi
  · intro hn
    rw [Finset.mem_range, not_lt] at hn
    rw [DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g),
      homogeneousComponent_eq_zero n g (by omega)]

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma isHomogeneous_of_forall_homogeneousComponent_mem {K : Type} [Field K] {N : ℕ}
    {I : Ideal (MvPolynomial (Fin N) K)} (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) I := by
  intro n g hg
  rw [coe_decompose_homogeneousSubmodule_eq_homogeneousComponent]
  exact hI g hg n


open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem _root_.GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq (K : Type) [Field K] (N : ℕ)
    (I Q : Ideal (MvPolynomial (Fin N) K))
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) (hQ : Q.IsPrime) (hIQ : I ≤ Q)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    (∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q) ∧
      _root_.GlobalTheory.idealHilbertPoly Q = _root_.GlobalTheory.idealHilbertPoly I := by
  have hQh := homogeneousComponent_mem_of_isPrime_of_X_pow_saturation hI hQ hIQ hs
  refine ⟨hQh, ?_⟩
  obtain ⟨L, hL⟩ := exists_homogeneous_mem_of_X_pow_mul_mem_of_homogeneous hI hs
  have hIh := isHomogeneous_of_forall_homogeneousComponent_mem hI
  have hQh' := isHomogeneous_of_forall_homogeneousComponent_mem hQh
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (((_root_.GlobalTheory.eventually_finrank_quotPiece hQh').and
      (_root_.GlobalTheory.eventually_finrank_quotPiece hIh)).and (eventually_ge_atTop L))
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n0 + n : ℕ) : ℚ))
    (fun a b hab => by simpa using hab) fun n => ?_
  obtain ⟨⟨hq, hi⟩, hLn⟩ := hn0 (n0 + n) (by omega)
  show Polynomial.eval _ _ = Polynomial.eval _ _
  rw [← hq, ← hi]
  have hint : Submodule.restrictScalars K Q ⊓ homogeneousSubmodule (Fin N) K (n0 + n) =
      Submodule.restrictScalars K I ⊓ homogeneousSubmodule (Fin N) K (n0 + n) := by
    apply le_antisymm
    · intro h hh
      rw [Submodule.mem_inf] at hh ⊢
      exact ⟨hL (n0 + n) hLn h hh.1 hh.2, hh.2⟩
    · intro h hh
      rw [Submodule.mem_inf] at hh ⊢
      exact ⟨hIQ hh.1, hh.2⟩
  have e1 := _root_.GlobalTheory.finrank_quotPiece_add Q (n0 + n)
  have e2 := _root_.GlobalTheory.finrank_quotPiece_add I (n0 + n)
  rw [hint] at e1
  congr 1
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotM
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ExtPrime


open MvPolynomial Filter in
open scoped ENNReal in
theorem _root_.GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L]
    [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L]
    [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K))
    (hP : P.IsPrime) :
    (P.map (MvPolynomial.map (algebraMap K L) :
      MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).IsPrime ∧
    ((∃ j, X j ∉ P) →
      (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
        MvPolynomial (Fin N) L) ∉
      P.map (MvPolynomial.map (algebraMap K L) :
        MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
  classical
  haveI := hP
  let e := (commAlgEquiv K (Fin N) (Fin N)).toRingEquiv
  let ι : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K) :=
    MvPolynomial.map (algebraMap K (MvPolynomial (Fin N) K))
  let π : MvPolynomial (Fin N) (MvPolynomial (Fin N) K) →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K ⧸ P) :=
    (MvPolynomial.map (Ideal.Quotient.mk P)).comp e.toRingHom
  have heι : ∀ p, e (ι p) = C p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [e, ι, commAlgEquiv_C]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
    | mul_X p i hp => rw [map_mul, map_mul, hp, map_X]; simp [e, commAlgEquiv_X]
  have hQ : P.map ι = RingHom.ker π := by
    ext b
    rw [RingHom.mem_ker]
    have hb : b = e.symm (e b) := (e.symm_apply_apply b).symm
    constructor
    · intro hb'
      have h1 : P.map ι ≤ RingHom.ker π := by
        rw [Ideal.map_le_iff_le_comap]
        intro p hp
        rw [Ideal.mem_comap, RingHom.mem_ker]
        show MvPolynomial.map (Ideal.Quotient.mk P) (e (ι p)) = 0
        rw [heι p, map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
      exact h1 hb'
    · intro hb'
      have hmem : e b ∈ Ideal.map C P := by
        have hk : Ideal.map (C : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) P =
            RingHom.ker (MvPolynomial.map (σ := Fin N) (Ideal.Quotient.mk P)) := by
          rw [MvPolynomial.ker_map, Ideal.mk_ker]
        rw [hk, RingHom.mem_ker]
        exact hb'
      rw [hb]
      have h2 : Ideal.map e.symm (Ideal.map C P) ≤ P.map ι := by
        rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro p hp
        have h4 : e.symm (C p) = ι p := by
          rw [← heι p]; exact e.symm_apply_apply _
        have h3 : e.symm (C p) ∈ P.map ι := by
          rw [h4]; exact Ideal.mem_map_of_mem ι hp
        exact h3
      exact h2 (Ideal.mem_map_of_mem _ hmem)
  have hQprime : (P.map ι).IsPrime := by rw [hQ]; exact RingHom.ker_isPrime π
  letI : Algebra (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L) :=
    (MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)).toAlgebra
  let Mₛ : Submonoid (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) :=
    Submonoid.map (C : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K))
      (nonZeroDivisors (MvPolynomial (Fin N) K))
  haveI hloc : IsLocalization Mₛ (MvPolynomial (Fin N) L) :=
    MvPolynomial.isLocalization (nonZeroDivisors (MvPolynomial (Fin N) K)) L
  have hdisj : Disjoint (Mₛ : Set (MvPolynomial (Fin N) (MvPolynomial (Fin N) K))) ↑(P.map ι) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    rw [SetLike.mem_coe, hQ, RingHom.mem_ker] at hrQ
    have hπ : π (C r) = MvPolynomial.map (algebraMap K (MvPolynomial (Fin N) K ⧸ P)) r := by
      simp only [π, RingHom.coe_comp, Function.comp_apply]
      rw [show e.toRingHom (C r) = MvPolynomial.map C r from commAlgEquiv_C (R := K) (S₁ := Fin N) r,
        MvPolynomial.map_map]
      rfl
    rw [hπ] at hrQ
    have hinj := MvPolynomial.map_injective (σ := Fin N) _
      (algebraMap K (MvPolynomial (Fin N) K ⧸ P)).injective
    have hr0 : r = 0 := hinj (by rw [hrQ, map_zero])
    exact nonZeroDivisors.ne_zero hr hr0
  have hcomp : (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) =
      (algebraMap (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L)).comp ι := by
    refine RingHom.ext fun p => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, ι, RingHom.algebraMap_toAlgebra, MvPolynomial.map_map]
    rw [← IsScalarTower.algebraMap_eq]
  have hmapeq : P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) =
      (P.map ι).map (algebraMap (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L)) := by
    rw [hcomp, Ideal.map_map]
  rw [hmapeq]
  refine ⟨IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hQprime hdisj, ?_⟩
  rintro ⟨j, hj⟩ hG
  let G₀ : MvPolynomial (Fin N) (MvPolynomial (Fin N) K) := ∑ i : Fin N, C (X i) * X i
  have hG₀ : algebraMap _ (MvPolynomial (Fin N) L) G₀ =
      ∑ i : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X i)) * X i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [G₀, RingHom.algebraMap_toAlgebra, map_sum]
  rw [← hG₀] at hG
  have hG₀Q : G₀ ∈ P.map ι := by
    have h := IsLocalization.under_map_of_isPrime_disjoint _ (MvPolynomial (Fin N) L) hQprime hdisj
    rw [← h]
    exact hG
  rw [hQ, RingHom.mem_ker] at hG₀Q
  have hπG : π G₀ = ∑ i : Fin N, X i * C (Ideal.Quotient.mk P (X i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [π, G₀, RingHom.coe_comp, Function.comp_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show e.toRingHom (C (X i)) = X i from commAlgEquiv_C_X (R := K) (S₁ := Fin N) i,
      show e.toRingHom (X i) = C (X i) from commAlgEquiv_X (R := K) (S₂ := Fin N) i, map_X, map_C]
  rw [hπG] at hG₀Q
  have hcoeff := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single j 1)) hG₀Q
  simp only [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  simp_rw [mul_comm (X _), coeff_C_mul, coeff_X, Finsupp.single_left_inj one_ne_zero] at hcoeff
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hcoeff
  exact hj (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)

end GlobalTheory.ExtPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureSumZero
section
noncomputable section

open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrodTheta

variable {F : Type} [Field F] [NumberField F]

def HasTheta {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) (f : W → ℂ) : Prop :=
  ∀ x, HasSum (fun ξ : κ → F => co.rho ψ x Φ fun i => algebraMap F (AF F) (ξ i)) (f x)

def IsPureSum {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (φ₀ : (κ → Fv F v₁) → ℂ) (Φ : (κ → AF F) → ℂ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
    Φ = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in cofinite, φ k v = vac v) ∧
      ∀ k, φ k v₁ = φ₀

theorem isPureSum_zero {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ)
    (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (φ₀ : (κ → Fv F v₁) → ℂ) : IsPureSum vac v₁ φ₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0⟩

theorem IsPureSum.smul {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ) (c : ℂ) :
    IsPureSum vac v₁ φ₀ (c • Φ) := by
  obtain ⟨m, f, φ, rfl, h1, h2, h3⟩ := h
  refine ⟨m, fun k => c • f k, φ, ?_, h1, h2, h3⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  ring

theorem IsPureSum.add {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ Ψ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ)
    (h' : IsPureSum vac v₁ φ₀ Ψ) : IsPureSum vac v₁ φ₀ (Φ + Ψ) := by
  first
  | exact @_root_.GlobalTheory.ClosingLemmaThird.main
  | exact _root_.GlobalTheory.ClosingLemmaThird.main
  | (apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosingLemmaThird.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosingLemmaThird.main ..)

theorem IsPureSum.sum {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {ι : Type} (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ k ∈ s, IsPureSum vac v₁ φ₀ (Φ k)) : IsPureSum vac v₁ φ₀ (∑ k ∈ s, Φ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPureSum_zero vac v₁ φ₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

section Theta

variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
  (co : Darboux B κ) (ψ : AddChar (AF F) ℂ)

theorem rho_smul (x : W) (c : ℂ) (Φ : (κ → AF F) → ℂ) : co.rho ψ x (c • Φ) = c • co.rho ψ x Φ := by
  funext y
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem hasTheta_zero : HasTheta co ψ 0 0 := fun x => by
  have : co.rho ψ x 0 = 0 := by simpa using rho_smul co ψ x 0 0
  simpa [this] using (hasSum_zero : HasSum (fun _ : κ → F => (0 : ℂ)) 0)

variable {co ψ}

theorem HasTheta.smul {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (c : ℂ) :
    HasTheta co ψ (c • Φ) (c • f) := fun x => by
  rw [rho_smul]
  exact (h x).mul_left c

theorem HasTheta.add {Φ Ψ : (κ → AF F) → ℂ} {f g : W → ℂ} (h : HasTheta co ψ Φ f) (h' : HasTheta co ψ Ψ g) :
    HasTheta co ψ (Φ + Ψ) (f + g) := by
  intro x
  have h0 := (h x).add (h' x)
  simpa only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, mul_add] using h0

theorem HasTheta.sum {ι : Type} (s : Finset ι) {Φ : ι → (κ → AF F) → ℂ} {f : ι → W → ℂ}
    (h : ∀ k ∈ s, HasTheta co ψ (Φ k) (f k)) : HasTheta co ψ (∑ k ∈ s, Φ k) (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasTheta_zero co ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem HasTheta.thetaSum_eq {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (x : W) :
    thetaSum F (co.rho ψ x Φ) = f x :=
  (h x).tsum_eq

end Theta

end GlobalTheory.SchrodTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeLeKFiniteVectorsFiniteDimensional
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.kTypeInKFinite : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → S ≤ D ∧ FiniteDimensional ℂ (S.comap D.subtype) ∧ KStab ε E (S.comap D.subtype) ∧ (∀ ν : Fin n → ℝ, ∀ x ∈ S.comap D.subtype, x ≠ 0 → KHighest ε E ν x → ν = μ) := by
  intro n ε H _ _ σ D E hH hU hI hK μ S hS
  have hSD : S ≤ D := fun v hv => (hK.mem v).2 ⟨S, hS.1, hv, hS.2.1⟩
  haveI : FiniteDimensional ℂ S := hS.1
  have hmap : (S.comap D.subtype).map D.subtype = S := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hSD
  haveI hFD : FiniteDimensional ℂ (S.comap D.subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSD).symm
  have hStab : KStab ε E (S.comap D.subtype) := by
    rw [_root_.GlobalTheory.KFinStab.kStab_iff_kStableOn n ε H σ D E hH hU hI hK _ hFD, hmap]; exact hS.2.1
  have hinj := Submodule.map_injective_of_injective (f := D.subtype) Subtype.val_injective
  have hirr : ∀ L' ≤ S.comap D.subtype, KStab ε E L' → L' = ⊥ ∨ L' = S.comap D.subtype := by
    intro L' hL' hst
    haveI : FiniteDimensional ℂ L' := Submodule.finiteDimensional_of_le hL'
    have hK' := (_root_.GlobalTheory.KFinStab.kStab_iff_kStableOn n ε H σ D E hH hU hI hK L' inferInstance).1 hst
    have hle : L'.map D.subtype ≤ S := hmap ▸ Submodule.map_mono hL'
    rcases hS.2.2.1 _ hle hK' with h | h
    · left; apply hinj; rw [h, Submodule.map_bot]
    · right; apply hinj; rw [h, hmap]
  obtain ⟨v, hv0, hvS, hvh⟩ := hK.hw μ S hS
  have hKR : KRel ε E := fun a b c d _ _ => hK.gl a b c d
  have hKU : KUnit ε E := fun a b h x y => by rw [hK.unit a b x y]; simp [Formalism.REAL.sgn, h]
  refine ⟨hSD, hFD, hStab, ?_⟩
  exact _root_.GlobalTheory.HDUniq.khighest_weight_unique n ε D E hKR hKU _ hFD hStab hirr μ v hvS hv0 hvh
end

