module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem leadIdeal_isHomogeneous (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    (leadIdeal J).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, (mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous _ _)⟩)

theorem linIdeal_isHomogeneous {d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    (linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X ℂ j).C_mul (A i j)))⟩)

theorem linIdeal_cons {k : ℕ} (A : Matrix (Fin k) (Fin n) ℂ) (B : Matrix (Fin 1) (Fin n) ℂ) :
    linIdeal (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) = linIdeal A ⊔ linIdeal B := by
  have h : linPoly (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) =
      Fin.cons (linPoly B 0) (linPoly A) := by
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  have hB : Set.range (linPoly B) = {linPoly B 0} := by
    rw [Set.range_unique]
    rfl
  rw [linIdeal, linIdeal, linIdeal, h, Fin.range_cons, hB, Set.insert_eq, Ideal.span_union, sup_comm]

theorem ConeAvoidsExists.proof (hlead : LeadIdealDim.Statement) (hcut : LinearFormCut.Statement)
    (hpow : HomogDimZeroPow.Statement) : ConeAvoidsExists.Statement := by
  intro n d J _ hd
  have key : ∀ k, k ≤ d → ∃ A : Matrix (Fin k) (Fin n) ℂ,
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (leadIdeal J ⊔ linIdeal A)) ≤
        ((d - k : ℕ) : WithBot ℕ∞) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, ?_⟩
      have h0 : linIdeal (0 : Matrix (Fin 0) (Fin n) ℂ) = ⊥ := by
        rw [linIdeal, Set.range_eq_empty, Ideal.span_empty]
      rw [h0, sup_bot_eq, Nat.sub_zero, ← hd]
      exact hlead n J
    | succ k ih =>
      intro hk
      obtain ⟨A, hA⟩ := ih (by omega)
      have hdk : d - k = (d - (k + 1)) + 1 := by omega
      rw [hdk] at hA
      obtain ⟨B, hB⟩ := hcut n _ _ hA
      refine ⟨Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ), ?_⟩
      rw [linIdeal_cons, ← sup_assoc]
      exact hB
  obtain ⟨A, hA⟩ := key d le_rfl
  rw [Nat.sub_self, Nat.cast_zero] at hA
  obtain ⟨N, hN⟩ := hpow n _ ((leadIdeal_isHomogeneous J).sup (linIdeal_isHomogeneous A)) hA
  exact ⟨A, N, hN⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem homogeneousComponent_mul_of_isHomogeneous_right {σ : Type*} (a g : MvPolynomial σ ℂ)
    {e : ℕ} (hg : g.IsHomogeneous e) (k : ℕ) :
    homogeneousComponent k (a * g) = if e ≤ k then homogeneousComponent (k - e) a * g else 0 := by
  have hd : ∀ (p : MvPolynomial σ ℂ) (i : ℕ),
      (DirectSum.decompose (homogeneousSubmodule σ ℂ) p i : MvPolynomial σ ℂ) =
        homogeneousComponent i p := fun p i => decomposition.decompose'_apply p i
  have h := DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ ℂ) k (a := a)
    ((mem_homogeneousSubmodule e g).2 hg)
  simpa only [hd] using h

theorem isHomogeneous_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (j : Fin d) :
    (linPoly A j).IsHomogeneous 1 := by
  have : linPoly A j ∈ homogeneousSubmodule (Fin n) ℂ 1 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X ℂ i))
  exact (mem_homogeneousSubmodule 1 _).1 this

theorem ConeAvoidsFinite.proof : ConeAvoidsFinite.Statement := by
  intro n d N J A hcone
  letI alg : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := alg.toModule
  show Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
  classical
  let gen : Finset (MvPolynomial (Fin n) ℂ ⧸ J) := Finset.univ.image fun f : Fin n → Fin N =>
    Ideal.Quotient.mk J (monomial (Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)) 1)
  let M := Submodule.span (MvPolynomial (Fin d) ℂ) (gen : Set (MvPolynomial (Fin n) ℂ ⧸ J))
  set_option synthInstance.maxHeartbeats 100000 in
  have hsmul : ∀ (s : MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin n) ℂ),
      Ideal.Quotient.mk J p ∈ M → Ideal.Quotient.mk J (pullback A s * p) ∈ M := by
    intro s p hp
    have : Ideal.Quotient.mk J (pullback A s * p) = s • Ideal.Quotient.mk J p := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul]; rfl
    rw [this]; exact M.smul_mem s hp
  have hsum : ∀ {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin n) ℂ),
      (∀ i ∈ s, Ideal.Quotient.mk J (q i) ∈ M) → Ideal.Quotient.mk J (∑ i ∈ s, q i) ∈ M :=
    fun s q h => by rw [map_sum]; exact M.sum_mem h
  have hmain : ∀ k (q : MvPolynomial (Fin n) ℂ), q.IsHomogeneous k → Ideal.Quotient.mk J q ∈ M := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>

    have key : ∀ (b x : MvPolynomial (Fin n) ℂ),
        x ∈ leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)) ∪ Set.range (linPoly A) →
        Ideal.Quotient.mk J (homogeneousComponent k (b * x)) ∈ M := by
      rintro b x (⟨f, hf, rfl⟩ | ⟨j, rfl⟩)
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b (leadForm f) (e := f.totalDegree)
          (homogeneousComponent_isHomogeneous f.totalDegree f)]
        split_ifs with hek
        · have hs := sum_homogeneousComponent f
          rw [Finset.sum_range_succ] at hs
          have hf' : leadForm f = f - ∑ i ∈ Finset.range f.totalDegree, homogeneousComponent i f := by
            rw [leadForm]; linear_combination hs
          rw [hf', mul_sub, map_sub, Finset.mul_sum,
            Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left _ hf), zero_sub]
          refine M.neg_mem (hsum _ _ fun i hi => ih _ ?_ _
            ((homogeneousComponent_isHomogeneous _ _).mul (homogeneousComponent_isHomogeneous _ _)))
          have := Finset.mem_range.1 hi; omega
        · simp
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b _ (isHomogeneous_linPoly A j)]
        split_ifs with hk
        · have hl : linPoly A j = pullback A (X j) := by simp [pullback]
          rw [mul_comm, hl]
          exact hsmul _ _ (ih _ (by omega) _ (homogeneousComponent_isHomogeneous _ _))
        · simp

    intro q hq
    rw [q.as_sum]
    refine hsum _ _ fun s hs => ?_
    have hdeg : s.degree = k := by
      have := hq (mem_support_iff.mp hs)
      rw [Finsupp.degree_eq_weight_one]; exact this
    have hCs : monomial s (AddMonoidAlgebra.coeff q s) = pullback A (C (AddMonoidAlgebra.coeff q s)) * monomial s 1 := by
      simp [pullback, C_mul_monomial]
    rw [hCs]
    refine hsmul _ _ ?_
    by_cases hlow : ∀ i, s i < N
    · refine Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨fun i => ⟨s i, hlow i⟩, Finset.mem_univ _, ?_⟩))
      congr 2; ext i; simp
    simp only [not_forall, not_lt] at hlow
    obtain ⟨i, hi⟩ := hlow

    have hmem : monomial s (1 : ℂ) ∈ leadIdeal J ⊔ linIdeal A := by
      apply hcone
      have hsplit : monomial s (1 : ℂ) = X i ^ N * monomial (s - Finsupp.single i N) 1 := by
        rw [← monomial_single_add, add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hi)]
      rw [hsplit]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (show X i ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) N)
    rw [leadIdeal, linIdeal, ← Ideal.span_union] at hmem
    obtain ⟨r, a, g, hag⟩ := Submodule.mem_span_set'.1 hmem
    have hm : monomial s (1 : ℂ) = homogeneousComponent k (∑ t, a t • (g t : MvPolynomial (Fin n) ℂ)) := by
      rw [hag, homogeneousComponent_eq_self (isHomogeneous_monomial _ hdeg)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, map_sum]
    exact hsum _ _ fun t _ => by rw [smul_eq_mul]; exact key _ _ (g t).2
  have htop : M = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sum_homogeneousComponent p]
    exact hsum _ _ fun i _ => hmain i _ (homogeneousComponent_isHomogeneous i p)
  exact ⟨⟨gen, htop⟩⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n d : ℕ}

theorem isHomogeneous_leadIdeal_sup_linIdeal (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    (leadIdeal J ⊔ linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  refine Ideal.IsHomogeneous.sup (Ideal.homogeneous_span _ _ ?_) (Ideal.homogeneous_span _ _ ?_)
  · rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, homogeneousComponent_mem _ _⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)⟩

theorem monomial_mem_originIdeal_pow {N : ℕ} {m : Fin n →₀ ℕ} (hm : m.degree = N) :
    monomial m (1 : ℂ) ∈ originIdeal n ^ N := by
  have hprod : ∏ i ∈ m.support, (X i : MvPolynomial (Fin n) ℂ) ^ m i = ∏ i, X i ^ m i :=
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by simp [Finsupp.notMem_support_iff.1 hi]
  rw [← prod_X_pow_eq_monomial, hprod, ← hm, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow
    (show (X i : MvPolynomial (Fin n) ℂ) ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) _

theorem originIdeal_pow_le_span (N : ℕ) :
    originIdeal n ^ N ≤
      Ideal.span {p | ∃ m : Fin n →₀ ℕ, m.degree = N ∧ monomial m (1 : ℂ) = p} := by
  induction N with
  | zero => simp only [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
            exact Ideal.subset_span ⟨0, by simp, by simp⟩
  | succ N ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [originIdeal, Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨m, hm, rfl⟩, _, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨m + Finsupp.single i 1, by simp [hm], by simp [X, monomial_mul]⟩

theorem originIdeal_pow_le {N : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (h : ∀ m : Fin n →₀ ℕ, m.degree = N → monomial m (1 : ℂ) ∈ I) : originIdeal n ^ N ≤ I := by
  refine (originIdeal_pow_le_span N).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact h m hm

theorem isZariskiOpen_of_local {U : Set (Matrix (Fin d) (Fin n) ℂ)}
    (H : ∀ A₀ ∈ U, ∃ p : MvPolynomial (Fin d × Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => A₀ ij.1 ij.2) p ≠ 0 ∧
        ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U) :
    IsZariskiOpen U := by
  refine ⟨{p | ∀ A : Matrix (Fin d) (Fin n) ℂ,
    eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U}, ?_⟩
  ext A
  constructor
  · intro hA
    obtain ⟨p, hp, hpU⟩ := H A hA
    exact ⟨p, hpU, hp⟩
  · rintro ⟨p, hpU, hp⟩
    exact hpU A hp

theorem ConeAvoidsOpen.proof : ConeAvoidsOpen.Statement := by
  intro n d N J
  classical
  refine isZariskiOpen_of_local fun A₀ hA₀ => ?_
  set V := Finset.finsuppAntidiag (Finset.univ : Finset (Fin n)) N
  have hV : ∀ m : Fin n →₀ ℕ, m ∈ V ↔ m.degree = N := fun m => by
    simp [V, Finsupp.degree_eq_sum]
  have hrep : ∀ m : V, ∃ a ∈ leadIdeal J, ∃ h : Fin d → MvPolynomial (Fin n) ℂ,
      a + ∑ j, h j * linPoly A₀ j = monomial (m : Fin n →₀ ℕ) 1 := by
    intro m
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.1 (hA₀ (monomial_mem_originIdeal_pow ((hV m).1 m.2)))
    obtain ⟨h, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
    exact ⟨a, ha, h, hab⟩
  choose a ha h hah using hrep
  let T : Matrix (Fin d) (Fin n) ℂ → V → MvPolynomial (Fin n) ℂ :=
    fun A m => a m + ∑ j, h m j * linPoly A j
  let P : Matrix V V (MvPolynomial (Fin d × Fin n) ℂ) := fun m' m =>
    C (AddMonoidAlgebra.coeff (a m) (m' : Fin n →₀ ℕ)) +
      ∑ j, ∑ k, C (AddMonoidAlgebra.coeff (h m j * X k) (m' : Fin n →₀ ℕ)) * X (j, k)
  have hP : ∀ (A : Matrix (Fin d) (Fin n) ℂ) (m' m : V),
      (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P m' m =
        AddMonoidAlgebra.coeff (T A m) (m' : Fin n →₀ ℕ) := by
    intro A m' m
    show eval _ (P m' m) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, T, linPoly, map_add (f := _), map_sum, map_mul, eval_C, eval_X, MvPolynomial.coeff_add, coeff_sum,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, coeff_C_mul, mul_comm]
  refine ⟨P.det, ?_, fun A hA => ?_⟩
  · rw [RingHom.map_det]
    have h1 : (eval fun ij : Fin d × Fin n => A₀ ij.1 ij.2).mapMatrix P = 1 := by
      ext m' m
      rw [hP, Matrix.one_apply]
      simp only [T, hah, coeff_monomial, Subtype.ext_iff, eq_comm]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  · rw [RingHom.map_det] at hA
    set M := (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P
    have hMT : ∀ m' m : V, M m' m = AddMonoidAlgebra.coeff (T A m) (m' : Fin n →₀ ℕ) := hP A
    have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hA)
    have hI : ∀ m, T A m ∈ leadIdeal J ⊔ linIdeal A := fun m =>
      Submodule.add_mem_sup (ha m) (Ideal.mem_span_range_iff_exists_fun.2 ⟨h m, rfl⟩)
    have hhom := isHomogeneous_leadIdeal_sup_linIdeal J A
    refine originIdeal_pow_le fun m hm => ?_
    have key : monomial m (1 : ℂ) =
        ∑ m'' : V, C (M⁻¹ m'' ⟨m, (hV m).2 hm⟩) * homogeneousComponent N (T A m'') := by
      ext s
      simp only [coeff_sum, coeff_C_mul, coeff_homogeneousComponent, coeff_monomial]
      by_cases hs : s.degree = N
      · have e := congr_fun (congr_fun hinv ⟨s, (hV s).2 hs⟩) ⟨m, (hV m).2 hm⟩
        simp only [Matrix.mul_apply, hMT, Matrix.one_apply, Subtype.ext_iff] at e
        simp only [hs, if_true]
        simp_rw [mul_comm (M⁻¹ _ _)]
        rw [e]
        by_cases hsm : s = m
        · simp [hsm]
        · simp [hsm, Ne.symm hsm]
      · simp only [hs, if_false, mul_zero, Finset.sum_const_zero]
        rw [if_neg]
        rintro rfl
        exact hs hm
    rw [key]
    exact Ideal.sum_mem _ fun m'' _ =>
      Ideal.mul_mem_left _ _ (homogeneousComponent_mem_of_mem hhom (hI m'') N)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCotangentBasisInPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem CotangentBasisInPrime.proof : CotangentBasisInPrime.Statement := by
  intro T _ _ P _

  let g : P → maximalIdeal (Localization.AtPrime P) := fun x =>
    ⟨algebraMap T _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P (x : T)).2 x.2⟩
  let v : P → CotangentSpace (Localization.AtPrime P) := fun x => (maximalIdeal _).toCotangent (g x)
  have hspan : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range v) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := (maximalIdeal (Localization.AtPrime P)).toCotangent_surjective z
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective P.primeCompl (y : Localization.AtPrime P)
    simp only at hxs
    have hx : x ∈ P :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P x s).1 (hxs ▸ y.2)
    have hy : y = IsLocalization.mk' (Localization.AtPrime P) (1 : T) s • g ⟨x, hx⟩ := by
      ext
      simp only [g, Submodule.coe_smul, smul_eq_mul, ← hxs]
      rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
    rw [hy, map_smul, ← algebraMap_smul (ResidueField (Localization.AtPrime P))]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' (ResidueField (Localization.AtPrime P)) v
  have : Finite κ := hli.finite_of_isNoetherian
  let e := Finite.equivFin κ
  let w := (v ∘ a) ∘ e.symm
  have hliw : LinearIndependent (ResidueField (Localization.AtPrime P)) w :=
    hli.comp e.symm e.symm.injective
  have hspw : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) = ⊤ := by
    rw [show Set.range w = Set.range (v ∘ a) from e.symm.surjective.range_comp _, hsp, hspan]
  let G : Fin (Nat.card κ) → maximalIdeal (Localization.AtPrime P) := fun i => g (a (e.symm i))
  have hsum : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      (maximalIdeal _).toCotangent (∑ i, c i • G i) = ∑ i, residue _ (c i) • w i := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← ResidueField.algebraMap_eq, algebraMap_smul]
    rfl
  have hcoe : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      ((∑ i, c i • G i : maximalIdeal (Localization.AtPrime P)) : Localization.AtPrime P) =
        ∑ i, c i * algebraMap T _ (a (e.symm i) : T) := by
    intro c
    simp [G, g]
  refine ⟨Nat.card κ, fun i => (a (e.symm i) : T), fun i => (a (e.symm i)).2, ?_, ?_⟩
  · intro y hy
    have hz : (maximalIdeal _).toCotangent ⟨y, hy⟩ ∈
        Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) := by
      rw [hspw]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    choose c' hc' using fun i => residue_surjective (R := Localization.AtPrime P) (c i)
    have hdiff : (maximalIdeal _).toCotangent (⟨y, hy⟩ - ∑ i, c' i • G i) = 0 := by
      rw [map_sub, hsum, ← hc]
      simp [hc']
    rw [Ideal.toCotangent_eq_zero, Submodule.coe_sub, hcoe] at hdiff
    rw [show y = (y - ∑ i, c' i * algebraMap T _ (a (e.symm i) : T)) +
        ∑ i, c' i * algebraMap T _ (a (e.symm i) : T) by ring]
    refine add_mem (Ideal.mem_sup_right hdiff) (Ideal.mem_sup_left (Ideal.sum_mem _ fun i _ => ?_))
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro c hc i
    have h0 : (maximalIdeal _).toCotangent (∑ i, c i • G i) = 0 := by
      rw [Ideal.toCotangent_eq_zero, hcoe]; exact hc
    rw [hsum] at h0
    exact (residue_eq_zero_iff _).1 (Fintype.linearIndependent_iff.1 hliw _ h0 i)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDerivationAdicCompletion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open AdicCompletion

variable {R : Type} [CommRing R] (I : Ideal R) (D : Derivation ℤ R R)

theorem derivation_mem_pow_of_mem_pow_succ {n : ℕ} {r : R} (hr : r ∈ I ^ (n + 1)) : D r ∈ I ^ n :=
  by apply _root_.UpperTheory.Reformulated.B.Qn11.derivation_mem_pow_of_mem_pow_succ <;> assumption

theorem pow_smul_top_eq (n : ℕ) : (I ^ n • ⊤ : Ideal R) = I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

noncomputable def derivQuot (n : ℕ) :
    R ⧸ (I ^ (n + 1) • ⊤ : Ideal R) →+ R ⧸ (I ^ n • ⊤ : Ideal R) :=
  QuotientAddGroup.lift (I ^ (n + 1) • ⊤ : Ideal R).toAddSubgroup
    ((Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R)).toAddMonoidHom.comp (D : R →ₗ[ℤ] R).toAddMonoidHom)
    (fun r hr => by
      change r ∈ (I ^ (n + 1) • ⊤ : Ideal R) at hr
      rw [AddMonoidHom.mem_ker]
      change Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_smul_top_eq]
      rw [pow_smul_top_eq] at hr
      exact derivation_mem_pow_of_mem_pow_succ I D hr)

theorem derivQuot_mk (n : ℕ) (r : R) :
    derivQuot I D n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D r) := rfl

theorem exists_rep_succ (x : AdicCompletion I R) (n : ℕ) :
    ∃ a : R, x.val (n + 1) = Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) a ∧
      x.val n = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
  refine ⟨a, ha.symm, ?_⟩
  rw [← x.property (Nat.le_succ n), ← ha]
  rfl

noncomputable def derivCompletionAdd : AdicCompletion I R →+ AdicCompletion I R where
  toFun x := ⟨fun n => derivQuot I D n (x.val (n + 1)), fun {m n} hmn => by
    change transitionMap I R hmn (derivQuot I D n (x.val (n + 1))) = derivQuot I D m (x.val (m + 1))
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
    have hm : x.val (m + 1) = Ideal.Quotient.mk (I ^ (m + 1) • ⊤ : Ideal R) a := by
      rw [← x.property (Nat.succ_le_succ hmn), ← ha]
      rfl
    rw [hm, ← ha, derivQuot_mk, derivQuot_mk]
    rfl⟩
  map_zero' := AdicCompletion.ext fun n => map_zero (derivQuot I D n)
  map_add' x y := AdicCompletion.ext fun n => map_add (derivQuot I D n) _ _

noncomputable def derivCompletion : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R) :=
  Derivation.mk' (derivCompletionAdd I D).toIntLinearMap (fun a b => by
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨p, hp1, hp0⟩ := exists_rep_succ I a n
    obtain ⟨q, hq1, hq0⟩ := exists_rep_succ I b n
    change derivQuot I D n ((a * b).val (n + 1)) =
      a.val n * derivQuot I D n (b.val (n + 1)) + b.val n * derivQuot I D n (a.val (n + 1))
    rw [val_mul, hp1, hq1, hp0, hq0, ← map_mul, derivQuot_mk, derivQuot_mk, derivQuot_mk, D.leibniz,
      smul_eq_mul (α := R), smul_eq_mul (α := R), map_add, map_mul, map_mul])

theorem DerivationAdicCompletion.proof : DerivationAdicCompletion.Statement := by
  intro R _ I D
  refine ⟨derivCompletion I D, fun r => AdicCompletion.ext fun n => ?_⟩
  rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

