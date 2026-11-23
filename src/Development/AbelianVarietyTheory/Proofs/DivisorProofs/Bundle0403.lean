module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexPointNormLtOfNotIsUnit
section
open Polynomial Filter Topology

namespace GlobalTheory

namespace SmallPoint

theorem exists_extend_of_ker_le {R B Ω : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.IsIntegral R B] [Field Ω] [IsAlgClosed Ω]
    (φ : R →+* Ω) (h : RingHom.ker (algebraMap R B) ≤ RingHom.ker φ) :
    ∃ ψ : B →+* Ω, ψ.comp (algebraMap R B) = φ := by
  haveI := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker φ) ⊥ h
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker φ) Ω := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) Ω := FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) (B ⧸ Q) := FaithfulSMul.to_isTorsionFree _ _
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker φ) (B ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := R)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (B ⧸ Q) →ₐ[R ⧸ RingHom.ker φ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨σ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩
  exact (σ.commutes (Ideal.Quotient.mk _ r)).trans (RingHom.kerLift_mk φ r)

theorem exists_extend_apply_eq {R B Ω : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    [Field Ω] [IsAlgClosed Ω] (ψ : R →+* Ω) (u : B) (t : Ω)
    (ht : (minpoly R u).eval₂ ψ t = 0) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap R B) = ψ ∧ φ u = t := by
  letI : Algebra R[X] B := (aeval u : R[X] →ₐ[R] B).toRingHom.toAlgebra
  haveI : IsScalarTower R R[X] B :=
    IsScalarTower.of_algebraMap_eq fun x => ((aeval u : R[X] →ₐ[R] B).commutes x).symm
  haveI : Algebra.IsIntegral R[X] B := Algebra.IsIntegral.tower_top (R := R)
  obtain ⟨φ, hφ⟩ := exists_extend_of_ker_le (B := B) (eval₂RingHom ψ t) (fun f hf => by
    obtain ⟨g, rfl⟩ := minpoly.isIntegrallyClosed_dvd
      (Algebra.IsIntegral.isIntegral (R := R) u) (p := f) hf
    rw [RingHom.mem_ker, map_mul, coe_eval₂RingHom, ht, zero_mul])
  have h : ∀ f : R[X], φ (aeval u f) = f.eval₂ ψ t := fun f => DFunLike.congr_fun hφ f
  refine ⟨φ, RingHom.ext fun r => ?_, ?_⟩
  · simpa using h (C r)
  · simpa using h X

theorem exists_root_norm_lt {F : ℂ[X]} (hF : F.Monic) {ε : ℝ} (hε : 0 < ε)
    (h : ‖F.coeff 0‖ < ε ^ F.natDegree) : ∃ t, F.IsRoot t ∧ ‖t‖ < ε := by
  first
  | exact @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | (apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt ..)

theorem exists_eventually_norm_le {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (Ψ : R →+* ℂ[X]) {b : B} (hb : IsIntegral R b) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝 (0 : ℂ), ∀ φ : B →+* ℂ,
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ → ‖φ b‖ ≤ M := by
  obtain ⟨G, hG, hGb⟩ := hb
  have h1 : ∀ i : ℕ, ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ (G.coeff i)).eval s‖ < ‖(Ψ (G.coeff i)).eval 0‖ + 1 := fun i =>
    ((Ψ (G.coeff i)).continuous.norm.tendsto 0).eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖ + 1) + 1, ?_⟩
  filter_upwards [(Finset.range G.natDegree).eventually_all.2 fun i _ => h1 i] with s hs φ hφ
  have hm : (G.map ((evalRingHom s).comp Ψ)).Monic := hG.map _
  have hr : (G.map ((evalRingHom s).comp Ψ)).IsRoot (φ b) := by
    rw [IsRoot, eval_map, ← hφ, ← hom_eval₂, hGb, map_zero]
  have h2 := hr.norm_lt_cauchyBound hm.ne_zero
  rw [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hG.natDegree_map] at h2
  have h3 : ((Finset.range G.natDegree).sup
      (fun i => ‖(G.map ((evalRingHom s).comp Ψ)).coeff i‖₊) : NNReal) ≤
      ∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖₊ + 1) := by
    refine Finset.sup_le fun i hi => ?_
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ‖(Ψ (G.coeff i)).eval 0‖₊ + 1) (fun _ _ => zero_le) hi)
    rw [coeff_map]
    exact_mod_cast (hs i hi).le
  have h4 := h2.le.trans (add_le_add_left h3 1)
  have h5 := NNReal.coe_le_coe.2 h4
  push_cast at h5
  exact h5

theorem exists_small_of_curve {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    (Ψ : R →+* ℂ[X]) (p : B →+* ℂ) (hp : p.comp (algebraMap R B) = (evalRingHom 0).comp Ψ)
    {n : ℕ} (w : Fin n → B) {u : B} (hu : p u = 0) {r : R} (hr : Ψ r ≠ 0) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ (s : ℂ) (φ : B →+* ℂ),
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ ∧ (Ψ r).eval s ≠ 0 ∧ ‖φ u‖ < ε ∧
        ∀ i, ‖φ (w i)‖ ≤ M := by
  choose M hM using fun i => exists_eventually_norm_le Ψ
    (Algebra.IsIntegral.isIntegral (R := R) (w i))
  refine ⟨∑ i, |M i|, fun ε hε => ?_⟩
  have hint := Algebra.IsIntegral.isIntegral (R := R) u
  have hF := minpoly.monic hint
  have h0 : (Ψ ((minpoly R u).coeff 0)).eval 0 = 0 := by
    have h := congrArg p (minpoly.aeval R u)
    rw [aeval_def, hom_eval₂, hu, eval₂_at_zero, hp, p.map_zero] at h
    exact h
  have h1 : ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ ((minpoly R u).coeff 0)).eval s‖ < ε ^ (minpoly R u).natDegree :=
    ((Ψ _).continuous.norm.tendsto 0).eventually (gt_mem_nhds (by
      simp only [h0, norm_zero]
      positivity))
  have h2 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ¬ (Ψ r).IsRoot s :=
    nhdsNE_le_cofinite _ (eventually_cofinite.2 (by
      simpa using (Ψ r).finite_setOf_isRoot hr))
  obtain ⟨s, hs2, hs1, hs3⟩ := (h2.and
    ((h1.and (eventually_all.2 hM)).filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨t, ht, htε⟩ := exists_root_norm_lt (hF.map ((evalRingHom s).comp Ψ)) hε (by
    rw [coeff_map, hF.natDegree_map]
    exact hs1)
  obtain ⟨φ, hφ, hφu⟩ := exists_extend_apply_eq ((evalRingHom s).comp Ψ) u t (by
    rwa [IsRoot, eval_map] at ht)
  refine ⟨s, φ, hφ, hs2, hφu ▸ htε, fun i => (hs3 i φ hφ).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

end SmallPoint

theorem exists_complex_point_norm_lt_of_not_isUnit :
    ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
      (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 →
      ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧
        ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by
  intro K B _ _ _ _ _ σ n w u q hu hq
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K B
  letI := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) K) B := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Nontrivial (B ⧸ Ideal.span {u}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨p₀, hp₀⟩ := exists_ringHom_extend_of_finiteType K (B ⧸ Ideal.span {u}) ℂ σ
  let p : B →+* ℂ := p₀.comp (Ideal.Quotient.mk _)
  have hpu : p u = 0 := by
    change p₀ (Ideal.Quotient.mk _ u) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self u), map_zero]
  obtain ⟨r, hr, c, hc⟩ :=
    (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) K) q).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hq)
  obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, MvPolynomial.eval z (MvPolynomial.map σ r) ≠ 0 := by
    by_contra! h
    exact hr (MvPolynomial.map_injective σ σ.injective
      (MvPolynomial.funext (by simpa using h)))
  let Ψ : MvPolynomial (Fin d) K →+* ℂ[X] := MvPolynomial.eval₂Hom (C.comp σ)
    fun j => C (p (g (MvPolynomial.X j))) + X * C (z j - p (g (MvPolynomial.X j)))
  have hΨ0 : p.comp (algebraMap (MvPolynomial (Fin d) K) B) = (evalRingHom 0).comp Ψ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · have : p (g (MvPolynomial.C a)) = σ a := by
        rw [MvPolynomial.algHom_C]
        exact hp₀ a
      exact this.trans (by simp [Ψ])
    · simp [Ψ]
      rfl
  have hΨ1 : (evalRingHom 1).comp Ψ = (MvPolynomial.eval z).comp (MvPolynomial.map σ) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_) <;> simp [Ψ]
  have hΨr : Ψ r ≠ 0 := fun h => hz (by
    have := DFunLike.congr_fun hΨ1 r
    simpa [h] using this.symm)
  obtain ⟨M, hM⟩ := SmallPoint.exists_small_of_curve Ψ p hΨ0 w hpu hΨr
  refine ⟨M, fun ε hε => ?_⟩
  obtain ⟨s, φ, hφ, h1, h2, h3⟩ := hM ε hε
  refine ⟨φ, RingHom.ext fun a => ?_, fun h => h1 ?_, h2, h3⟩
  · have := DFunLike.congr_fun hφ (MvPolynomial.C a)
    rw [RingHom.comp_apply, ← MvPolynomial.algHom_C g]
    exact this.trans (by simp [Ψ])
  · have := DFunLike.congr_fun hφ r
    rw [RingHom.comp_apply, hc, map_mul, h, zero_mul] at this
    exact this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPos
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscRep
variable {R : Type} [CommRing R]

def asum (m : ℕ) : ℤ := ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ)

theorem asum_succ (k : ℕ) : asum (k + 1) = asum k + (-1) ^ (k + 1) := by
  rw [asum, Fin.sum_univ_castSucc]
  simp [asum]

theorem asum_even (m : ℕ) : asum m = if Even m then 1 else 0 := by
  induction m with
  | zero => simp [asum]
  | succ k ih =>
    rw [asum_succ, ih]
    rcases Nat.even_or_odd k with h | h
    · have h' : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', (h.add_one).neg_one_pow]
    · have h' : Even (k + 1) := h.add_one
      have h'' : ¬ Even k := Nat.not_even_iff_odd.mpr h
      simp [h', h'', h'.neg_one_pow]

variable (R) in
abbrev C (F : PSh) : ChainComplex (Shv R) ℕ := (chainsN R).obj (disc.obj F)

theorem C_d (F : PSh) (p : ℕ) :
    (C R F).d (p + 1) p = (asum (p + 1)) • (𝟙 ((free R).obj F) : (C R F).X (p + 1) ⟶ (C R F).X p) := by
  rw [show (C R F).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((disc.obj F).δ i) from
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p]
  simp only [asum, Finset.sum_smul, SimplicialObject.δ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (disc.obj F).map (SimplexCategory.δ i).op = 𝟙 F from rfl]
  exact congrArg (fun f => (-1 : ℤ) ^ (i : ℕ) • f) ((free R).map_id F)

def idX (F : PSh) (i j : ℕ) : (C R F).X i ⟶ (C R F).X j := 𝟙 ((free R).obj F)

theorem idX_comp (F : PSh) (i j k : ℕ) : idX (R := R) F i j ≫ idX F j k = idX F i k := Category.id_comp _

theorem C_d' (F : PSh) (p : ℕ) : (C R F).d (p + 1) p = (asum (p + 1)) • idX F (p + 1) p := C_d F p

def piC (F : PSh) : C R F ⟶ C R F where
  f i := if i = 0 then 𝟙 _ else 0
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [if_neg (Nat.succ_ne_zero j), zero_comp, C_d']
    rcases j with _ | j
    · rw [asum_even, if_neg (by decide), zero_smul, zero_comp]
    · rw [if_neg (Nat.succ_ne_zero j), comp_zero]

def htpC (F : PSh) : Homotopy (𝟙 (C R F)) (piC F) where
  hom i j := if i + 1 = j ∧ Odd i then idX F i j else 0
  zero i j w := by
    rw [if_neg]
    rintro ⟨h, -⟩
    exact w h
  comm i := by
    rcases i with _ | k
    · rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, C_d']
      simp [piC, asum_even]
    · rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, C_d', C_d']
      simp only [piC, if_neg (Nat.succ_ne_zero k), add_zero, true_and, asum_even]
      rcases Nat.even_or_odd k with h | h
      · have h1 : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using h
        have h2 : Even (k + 1 + 1) := h1 |> fun _ => (h.add_one).add_one
        have h3 : Odd (k + 1) := h.add_one
        have h4 : ¬ Odd k := Nat.not_odd_iff_even.mpr h
        simp only [h1, h2, h3, h4, if_true, if_false, one_smul, zero_smul, comp_zero, zero_comp, zero_add, idX_comp]
        rfl
      · have h1 : Even (k + 1) := h.add_one
        have h3 : ¬ Odd (k + 1) := Nat.not_odd_iff_even.mpr h1
        simp only [h1, h, h3, if_true, if_false, one_smul, comp_zero, zero_comp, add_zero, idX_comp]
        rfl

def piZ (F : PSh) : (chains R).obj (disc.obj F) ⟶ (chains R).obj (disc.obj F) :=
  HomologicalComplex.extendMap (piC F) ComplexShape.embeddingDownNat

def htpZ (F : PSh) : Homotopy (𝟙 ((chains R).obj (disc.obj F))) (piZ F) :=
  (Homotopy.ofEq (HomologicalComplex.extendMap_id (C R F) ComplexShape.embeddingDownNat).symm).trans
    ((htpC F).extend ComplexShape.embeddingDownNat)

theorem piZ_f (F : PSh) (p : ℕ) (hp : 0 < p) : (piZ (R := R) F).f (-(p : ℤ)) = 0 := by
  have h1 := HomologicalComplex.extendMap_f (piC (R := R) F) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl
  simp only [piC, if_neg hp.ne', zero_comp, comp_zero] at h1
  exact h1

end GlobalTheory.EtC.DiscRep


open GlobalTheory.EtC.DiscRep in
theorem GlobalTheory.EtC.discRep : ∀ (R : Type) [CommRing R] (F : PSh) (I : Cx R) (n : ℤ)
    (x : CohomologyClass ((chains R).obj (disc.obj F)) I n), ∃ α : Cocycle ((chains R).obj (disc.obj F)) I n,
      CohomologyClass.mk α = x ∧ ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0 := by
  intro R _ F I n x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  refine ⟨zcomp (Cocycle.ofHom (piZ F)) α (zero_add n), ?_, ?_⟩
  · rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨-(n.negOnePow • (Cochain.ofHomotopy (htpZ F)).comp α.1 (by omega)), ?_⟩
    rw [δ_neg, δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
    ext p q hpq
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]
  · intro p hp s h
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) _ _ s (add_zero _) h, piZ_f F p hp]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndependentBasisCoprime
section
open NumberField

namespace GlobalTheory.CoprimeBasis

theorem isTorsionFree_of_addTorsionFree {F : Type} [Field F] [NumberField F]
    (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [IsAddTorsionFree M] :
    Module.IsTorsionFree (𝓞 F) M where
  isSMulRegular r hr x y hxy := by
    have hxy' : r • x = r • y := hxy
    have hr0 : r ≠ 0 := hr.ne_zero
    have hn : Ideal.absNorm (Ideal.span {r}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hr0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
    have h1 : (Ideal.absNorm (Ideal.span {r})) • (x - y) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 F), ← hb, mul_smul, smul_sub, hxy', sub_self, smul_zero]
    haveI : HasUniqueDiv M := by
      refine ⟨fun {n} hn => ?_⟩
      intro x y h
      have h' : (n : ℤ) • x = (n : ℤ) • y := by exact_mod_cast h
      have hz : (n : ℤ) • (x - y) = 0 := by rw [zsmul_sub, h', sub_self]
      have hdiff : x - y = 0 := by simpa [hn] using hz
      exact sub_eq_zero.mp hdiff
    exact sub_eq_zero.1 (nsmul_right_injective hn (h1.trans (nsmul_zero _).symm))

theorem isCoprime_of_mem_primeTo {R : Type} [CommRing R] {s d : R}
    (hs : s ∈ GlobalTheory.Mass.primeTo d) : IsCoprime s d := by
  by_cases hI : Ideal.span {s, d} = ⊤
  · obtain ⟨a, b, h⟩ := Ideal.mem_span_pair.1 ((Ideal.eq_top_iff_one _).1 hI)
    exact ⟨a, b, h⟩
  · obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hI
    exact absurd (hle (Ideal.subset_span (by simp))) (hs P hP (hle (Ideal.subset_span (by simp))))

theorem exists_coprime_basis : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (N : ℕ), 2 ≤ N → ∃ (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x ∧ ∃ c : 𝓞 F, c ≠ 0 ∧ IsCoprime c (N : 𝓞 F) ∧ ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x) := by
  intro F _ _ M _ _ _ _ N hN
  classical
  let S : Submonoid (𝓞 F) := GlobalTheory.Mass.primeTo (N : 𝓞 F)
  have hSle : S ≤ nonZeroDivisors (𝓞 F) := GlobalTheory.Mass.SemiBasis.primeTo_le hN
  haveI : Module.IsTorsionFree (𝓞 F) M := isTorsionFree_of_addTorsionFree M
  haveI : Module.Finite (𝓞 F) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) M
  haveI : IsDomain (Localization S) := IsLocalization.isDomain_localization hSle
  haveI : IsPrincipalIdealRing (Localization S) := by
    haveI := GlobalTheory.Mass.SemiBasis.isPID (K := F) hN
    have hA : GlobalTheory.Mass.SemiBasis.A F hN =
        Localization.subalgebra.ofField F (GlobalTheory.Mass.primeTo (N : 𝓞 F))
          (GlobalTheory.Mass.SemiBasis.primeTo_le hN) := by
      apply Subalgebra.ext
      intro x
      rfl
    haveI : IsLocalization S (GlobalTheory.Mass.SemiBasis.A F hN) := by
      rw [hA]
      exact Localization.subalgebra.isLocalization_ofField (A := 𝓞 F) (K := F)
        (S := GlobalTheory.Mass.primeTo (N : 𝓞 F))
        (hS := GlobalTheory.Mass.SemiBasis.primeTo_le hN)
    exact IsPrincipalIdealRing.of_surjective
      (IsLocalization.algEquiv S (GlobalTheory.Mass.SemiBasis.A F hN) (Localization S)).toRingHom
      (IsLocalization.algEquiv S (GlobalTheory.Mass.SemiBasis.A F hN) (Localization S)).surjective
  haveI : Module.Finite (Localization S) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := Localization S) (M := LocalizedModule S M)
  have hb : ∀ i, ∃ (m : M) (s : S), b i = LocalizedModule.mk m s := fun i => by
    exact LocalizedModule.induction_on (β := fun y => ∃ (m : M) (s : S), y = LocalizedModule.mk m s)
      (fun m s => ⟨m, s, rfl⟩) (b i)
  choose x s hxs using hb
  have key : ∀ i, (s i : 𝓞 F) • b i = LocalizedModule.mk (x i) 1 := by
    intro i
    rw [hxs i, LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel]
  refine ⟨r, x, ?_, ?_⟩
  · let u : Fin r → (Localization S)ˣ := fun i => (IsLocalization.map_units (Localization S) (s i)).unit
    have hu : LinearIndependent (Localization S) (u • ⇑b) := b.linearIndependent.units_smul u
    have hfx : (u • ⇑b) = LocalizedModule.mkLinearMap S M ∘ x := by
      funext i
      simp only [Pi.smul_apply', Function.comp_apply, LocalizedModule.mkLinearMap_apply, ← key i]
      rw [Units.smul_def, IsUnit.unit_spec, algebraMap_smul]
    rw [hfx] at hu
    have hinj : Function.Injective fun a : 𝓞 F => a • (1 : Localization S) := by
      intro a a' h
      simp only [Algebra.smul_def, mul_one] at h
      exact IsLocalization.injective (Localization S) hSle h
    exact (hu.restrict_scalars hinj).of_comp _
  · set P : Submodule (𝓞 F) M := Submodule.span (𝓞 F) (Set.range x) with hP
    have hloc : ∀ y : LocalizedModule S M, ∃ t : S, ∃ m' ∈ P, (t : 𝓞 F) • y = LocalizedModule.mk m' 1 := by
      intro y
      have hy : y ∈ Submodule.span (Localization S) (Set.range b) := by rw [b.span_eq]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact ⟨s i, x i, Submodule.subset_span ⟨i, rfl⟩, key i⟩
      | zero => exact ⟨1, 0, P.zero_mem, by simp [LocalizedModule.zero_mk]⟩
      | add y z _ _ hy hz =>
        obtain ⟨t, m, hm, h⟩ := hy
        obtain ⟨t', m', hm', h'⟩ := hz
        refine ⟨t * t', (t' : 𝓞 F) • m + (t : 𝓞 F) • m', P.add_mem (P.smul_mem _ hm) (P.smul_mem _ hm'), ?_⟩
        calc ((t * t' : S) : 𝓞 F) • (y + z) = (t' : 𝓞 F) • ((t : 𝓞 F) • y) + (t : 𝓞 F) • ((t' : 𝓞 F) • z) := by
              rw [Submonoid.coe_mul, smul_add, smul_smul, smul_smul, mul_comm (t' : 𝓞 F)]
          _ = _ := by
              rw [h, h', LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_add_mk]
              simp
      | smul a y _ hy =>
        obtain ⟨t, m, hm, h⟩ := hy
        obtain ⟨⟨r0, u⟩, hr⟩ := IsLocalization.surj S a
        have hua : (u : 𝓞 F) • a = algebraMap (𝓞 F) (Localization S) r0 := by
          rw [Algebra.smul_def, mul_comm]; exact hr
        refine ⟨u * t, r0 • m, P.smul_mem r0 hm, ?_⟩
        calc ((u * t : S) : 𝓞 F) • (a • y) = ((u : 𝓞 F) • a) • ((t : 𝓞 F) • y) := by
              rw [Submonoid.coe_mul, mul_smul, smul_comm (t : 𝓞 F) a y, smul_assoc]
          _ = LocalizedModule.mk (r0 • m) 1 := by
              rw [hua, h, algebraMap_smul, LocalizedModule.smul'_mk]
    have hgen : ∀ m : M, ∃ t : S, (t : 𝓞 F) • m ∈ P := by
      intro m
      obtain ⟨t, m', hm', h⟩ := hloc (LocalizedModule.mk m 1)
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h
      obtain ⟨u, hu⟩ := h
      simp only [one_smul, Submonoid.smul_def] at hu
      refine ⟨u * t, ?_⟩
      rw [Submonoid.coe_mul, mul_smul, hu]
      exact P.smul_mem _ hm'
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := 𝓞 F) (M := M)
    choose t ht using fun j => hgen (g j)
    refine ⟨((∏ j, t j : S) : 𝓞 F), ?_, ?_, ?_⟩
    · exact nonZeroDivisors.ne_zero (hSle (∏ j, t j).2)
    · exact isCoprime_of_mem_primeTo (∏ j, t j).2
    · intro m
      have hle : Submodule.span (𝓞 F) (Set.range g) ≤
          P.comap (LinearMap.lsmul (𝓞 F) M ((∏ j, t j : S) : 𝓞 F)) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show ((∏ j, t j : S) : 𝓞 F) • g j ∈ P
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Submonoid.coe_mul, mul_smul]
        exact P.smul_mem _ (ht j)
      rw [hg] at hle
      exact hle Submodule.mem_top

end GlobalTheory.CoprimeBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroClosureEtaleAtStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_closureEtaleAt_alt : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt) | (exact GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt) | (intros; apply GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafHomLinearMapsSheafCurryEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv : ∀ (R : Type) [CommRing R] (J : Shv R), ∃ e : ∀ (X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)), (X ⟶ (homSh J).obj (op M)) ≃ (M →ₗ[ULift.{1} R] (X ⟶ J)), (∀ (X : Shv R) (M N : ModuleCat.{1} (ULift.{1} R)) (p : M ⟶ N) (f : X ⟶ (homSh J).obj (op N)), e X M (f ≫ (homSh J).map p.op) = (e X N f) ∘ₗ p.hom) ∧ (∀ (X Y : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (i : X ⟶ Y) (f : Y ⟶ (homSh J).obj (op M)), e X M (i ≫ f) = (Linear.leftComp (ULift.{1} R) J i) ∘ₗ (e Y M f)) := by
  first | (exact @GlobalTheory.EtC.homSh_curry) | (exact GlobalTheory.EtC.homSh_curry) | (intros; apply GlobalTheory.EtC.homSh_curry  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSumSquaresRightDerivPowDifferentialOperatoStatement
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sumSquaresRightDeriv_pow_differentialOperator : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ k : ℕ, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ξ : E d, symb (2 * k) a x ξ = (((∑ i, (∑ j, c (b i) j x * ξ j) ^ 2) ^ k : ℝ) : ℂ)) ∧ ∀ f : h.smoothFuns (F := ℂ), ∀ x ∈ Metric.ball (0 : E d) r, (((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f : G → ℂ) (h.expG (coordEquiv b (x))) = apOp (2 * k) a (fun y => (f : G → ℂ) (h.expG (coordEquiv b (y)))) x := by
  first | exact @GlobalTheory.HCA.exists_apOp_sumSq_pow | exact GlobalTheory.HCA.exists_apOp_sumSq_pow | (intros; apply GlobalTheory.HCA.exists_apOp_sumSq_pow <;> assumption)
end

