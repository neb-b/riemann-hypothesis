module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0234
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0232
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.LocalAtPlace
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.TiedAInvOfTheta
public import GroundTheory.PAdicHodge.BCrisEigen
public import GroundTheory.PAdicHodge.BCrisRegularSenTate
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0233

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBcOfNe
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ChartBc

theorem chart_bc_of_ne : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) (hp : p ≠ 0) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) {V : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d),
    letI := σ.toAlgebra
    letI := c.D.i.toAlgebra
    ∃ (c' : Chart γ' p q κ' V d) (e : c.D ⟶ (m.mor p).functor.obj c'.D), (∀ i, e.φ (c.t i) = c'.t i) ∧
      (FlatT c.D → FlatT c'.D) ∧
      ∃ f : R' ⊗[R] c.D.B ≃+* c'.D.B, (∀ r, f (r ⊗ₜ 1) = c'.D.i r) ∧ ∀ x, f (1 ⊗ₜ x) = e.φ x := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m hp hu hg V d c
  exact chart_bc m hu hg (fun h => absurd h hp) c

end GlobalTheory.CompanionTheory.ChartBc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_is_good : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d), c.Good := by
  first | exact @GlobalTheory.CompanionTheory.ChartMaps.good | exact GlobalTheory.CompanionTheory.ChartMaps.good | (intros; apply GlobalTheory.CompanionTheory.ChartMaps.good <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SaGen

structure PlaceMap (F K : Type) [Field F] [NumberField F] [Field K] [Algebra F K] [TopologicalSpace K] where

  proj : AF F →ₐ[F] K

  inj : K →ₙₐ[F] AF F
  proj_inj : ∀ x, proj (inj x) = x
  inj_proj : ∀ a, inj (proj a) = inj 1 * a
  cont_proj : Continuous proj
  cont_inj : Continuous inj

section Inhabitants

variable {F : Type} [Field F] [NumberField F]

theorem adele_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext h1 h2

theorem finAdele_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  RestrictedProduct.ext _ _ h

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

theorem continuous_singleV' (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem evalV_singleV_eq (v w : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (f : ∀ u, Fv F u → Fv F u)
    (h0 : ∀ u, f u 0 = 0) :
    f w (evalV F w (singleV F v y)) = evalV F w (singleV F v (f v y)) := by
  by_cases h : w = v
  · subst h
    rw [StrongApprox.evalV_single_same, StrongApprox.evalV_single_same]
  · rw [StrongApprox.evalV_single_ne h, StrongApprox.evalV_single_ne h, h0]

def placeMapFin (v : HeightOneSpectrum (𝓞 F)) : PlaceMap F (Fv F v) where
  proj := (evalV F v).comp (sndA F)
  inj :=
    { toFun := fun y => pairA F 0 (singleV F v y)
      map_smul' := by
        intro c y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_smul, fstA_pairA, fstA_pairA, smul_zero]
        · rw [map_smul, sndA_pairA, sndA_pairA, map_smul]
          exact (evalV_singleV_eq v w y (fun u t => c • t) (fun u => smul_zero c)).symm ▸ rfl
      map_zero' := by
        refine adele_ext rfl (finAdele_ext fun w => ?_)
        rw [sndA_pairA, map_zero, map_zero]
        by_cases h : w = v
        · subst h
          rw [StrongApprox.evalV_single_same]
        · rw [StrongApprox.evalV_single_ne h]
      map_add' := by
        intro x y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA, add_zero]
        · rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA, map_add (f := _)]
          by_cases h : w = v
          · subst h
            simp only [StrongApprox.evalV_single_same]
          · simp only [StrongApprox.evalV_single_ne h, add_zero]
      map_mul' := by
        intro x y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_mul, fstA_pairA, fstA_pairA, fstA_pairA, mul_zero]
        · rw [map_mul, sndA_pairA, sndA_pairA, sndA_pairA, map_mul]
          by_cases h : w = v
          · subst h
            simp only [StrongApprox.evalV_single_same]
          · simp only [StrongApprox.evalV_single_ne h, mul_zero] }
  proj_inj := fun x => StrongApprox.evalV_single_same v x
  inj_proj := by
    intro a
    refine adele_ext ?_ (finAdele_ext fun w => ?_)
    · change (0 : Ainf F) = fstA F (pairA F 0 (singleV F v 1) * a)
      rw [map_mul, fstA_pairA, zero_mul]
    · change evalV F w (singleV F v (evalV F v (sndA F a))) = evalV F w (sndA F (pairA F 0 (singleV F v 1) * a))
      rw [map_mul, map_mul, sndA_pairA]
      by_cases h : w = v
      · subst h
        simp only [StrongApprox.evalV_single_same, one_mul]
      · simp only [StrongApprox.evalV_single_ne h, zero_mul]
  cont_proj := StrongApprox.continuous_evalV v
  cont_inj := continuous_const.prodMk (continuous_singleV' v)


open Classical in
def singleI (w : InfinitePlace F) (y : w.Completion) : Ainf F :=
  (Pi.single (M := fun u : InfinitePlace F => u.Completion) w y : ∀ u : InfinitePlace F, u.Completion)

open Classical in
theorem singleI_self (w : InfinitePlace F) (y : w.Completion) : (singleI w y : ∀ u : InfinitePlace F, u.Completion) w = y :=
  Pi.single_eq_same (M := fun u : InfinitePlace F => u.Completion) w y

open Classical in
theorem singleI_ne {w u : InfinitePlace F} (h : u ≠ w) (y : w.Completion) :
    (singleI w y : ∀ u : InfinitePlace F, u.Completion) u = 0 :=
  Pi.single_eq_of_ne (M := fun u : InfinitePlace F => u.Completion) h y

theorem ainf_ext {x y : Ainf F} (h : ∀ u, (x : ∀ u : InfinitePlace F, u.Completion) u = (y : ∀ u : InfinitePlace F, u.Completion) u) : x = y :=
  funext h


open Classical in
def placeMapInf (w : InfinitePlace F) : PlaceMap F w.Completion where
  proj := (Pi.evalAlgHom F (fun u : InfinitePlace F => u.Completion) w).comp (fstA F)
  inj :=
    { toFun := fun y => pairA F (singleI w y) 0
      map_smul' := by
        intro c y
        refine adele_ext ?_ ?_
        · rw [map_smul, fstA_pairA, fstA_pairA]
          exact Pi.single_smul (f := fun u : InfinitePlace F => u.Completion) w c y
        · rw [map_smul, sndA_pairA, sndA_pairA, smul_zero]
      map_zero' := by
        refine adele_ext ?_ rfl
        rw [fstA_pairA, map_zero]
        exact Pi.single_zero (M := fun u : InfinitePlace F => u.Completion) w
      map_add' := by
        intro x y
        refine adele_ext ?_ ?_
        · rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA]
          exact Pi.single_add (f := fun u : InfinitePlace F => u.Completion) w x y
        · rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA, add_zero]
      map_mul' := by
        intro x y
        refine adele_ext ?_ ?_
        · rw [map_mul, fstA_pairA, fstA_pairA, fstA_pairA]
          exact Pi.single_mul (α := fun u : InfinitePlace F => u.Completion) w x y
        · rw [map_mul, sndA_pairA, sndA_pairA, sndA_pairA, mul_zero] }
  proj_inj := fun x => singleI_self w x
  inj_proj := by
    intro a
    refine adele_ext ?_ ?_
    · change singleI w (fstA F a w) = fstA F (pairA F (singleI w 1) 0 * a)
      rw [map_mul, fstA_pairA]
      refine ainf_ext fun u => ?_
      change (singleI w (fstA F a w) : ∀ u : InfinitePlace F, u.Completion) u =
        (singleI w 1 : ∀ u : InfinitePlace F, u.Completion) u * fstA F a u
      by_cases h : u = w
      · subst h
        rw [singleI_self, singleI_self, one_mul]
      · rw [singleI_ne h, singleI_ne h, zero_mul]
    · change (0 : Af F) = sndA F (pairA F (singleI w 1) 0 * a)
      rw [map_mul, sndA_pairA, zero_mul]
  cont_proj := (continuous_apply w).comp continuous_fst
  cont_inj := (continuous_single w).prodMk continuous_const

end Inhabitants

section Ring

variable {R : Type} [CommRing R] {M : ℕ}

end Ring

section Lift

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def iB (P : PlaceMap F K) : K ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map { toFun := P.inj, map_add' := map_add _, map_smul' := map_smul _ } LinearMap.id

end Lift

section Iso

variable {F E : Type} [Field F] [Field E] [Algebra F E]

end Iso

end GlobalTheory.CompanionTheory.SaGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementProperties
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.EpsFacts

variable {l : ℕ} [Fact l.Prime]

theorem geom_sum_eq_zero {R : Type*} [CommRing R] [IsDomain R] {z : R} {m : ℕ} (h : z ^ m = 1) (h1 : z ≠ 1) :
    ∑ i ∈ Finset.range m, z ^ i = 0 := by
  have e := mul_geom_sum z m
  rw [h, sub_self] at e
  exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 h1)

theorem pow_chain {M : Type*} [Monoid M] {m : ℕ} (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ m = e k) (k j : ℕ) :
    e (k + j) ^ m ^ j = e k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ m j, mul_comm, pow_mul, ← add_assoc, hs, ih]

theorem prim_chain {M : Type*} [CommMonoid M] (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ l = e k) (h0 : e 0 = 1)
    (h1 : e 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (e m) (l ^ m) := by
  cases m with
  | zero => simpa [h0] using IsPrimitiveRoot.one
  | succ k =>
    have a : e (k + 1) ^ l ^ k = e 1 := by
      have := pow_chain e hs 1 k
      rwa [add_comm 1 k] at this
    have b : e (k + 1) ^ l ^ (k + 1) = 1 := by
      have := pow_chain e hs 0 (k + 1)
      rwa [zero_add, h0] at this
    have o : orderOf (e (k + 1)) = l ^ (k + 1) :=
      orderOf_eq_prime_pow (by rw [a]; exact h1) b
    exact o ▸ IsPrimitiveRoot.orderOf _

theorem coeff_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] (a : R) (ha : ¬ IsUnit (a - 1)) (i : ℕ) :
    ¬ IsUnit ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) := by
  have h1 : IsLocalRing.residue R a = 1 := by
    have : IsLocalRing.residue R (a - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 ha)
    rwa [map_sub, map_one, sub_eq_zero] at this
  have h2 : WittVector.map (IsLocalRing.residue R) (WittVector.teichmuller l a - 1 : WittVector l R) = 0 := by
    rw [map_sub, map_one, WittVector.map_teichmuller, h1, map_one, sub_self]
  have h3 : IsLocalRing.residue R ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) = 0 := by
    rw [← WittVector.map_coeff, h2, WittVector.zero_coeff]
  exact (IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3)

variable (l) in
theorem isLocalRing_oc : IsLocalRing (OC l) := ValuationRing.isLocalRing (OC l)

variable (l) in
theorem isLocalRing_ob : IsLocalRing (Ob l) :=
  haveI := isLocalRing_oc l
  GlobalTheory.preTilt_isLocalRing l (OC l)

variable (l) in
theorem pFlat_not_isUnit : ¬ IsUnit (pFlat l) := fun h => by
  have h1 : IsUnit (theta0 l (WittVector.teichmuller l (pFlat l))) := (h.map (WittVector.teichmuller l)).map (theta0 l)
  rw [WittVector.fontaineTheta_teichmuller, untilt_pFlat] at h1
  exact (inferInstance : Fact (¬ IsUnit (l : OC l))).out h1

theorem integral_prime_dvd_epsilon_zero_sub_one (ε : Eps l) : pFlat l ∣ ((ε.e 0 : Ob l) - 1) := by
  have h := ((RL.sharp_cong (base l)).2.1 (ε.e 0 : Ob l) 1).1 (by
    have h0 : (base l).sharp (ε.e 0 : Ob l) = 1 := ε.sharp_e (base l)
    rw [h0, map_one, sub_self]
    exact zero_mem _)
  exact Ideal.mem_span_singleton.1 h

theorem epsilon_one_sub_one_not_isUnit (ε : Eps l) : ¬ IsUnit ((ε.e 1 : Ob l) - 1) := fun h => by
  haveI : CharP (Ob l) l := inferInstance
  have h1 : IsUnit (((ε.e 1 : Ob l) - 1) ^ l) := h.pow l
  have e : (ε.e 1 : Ob l) ^ l = ε.e 0 := by
    have := congrArg Units.val (ε.succ 0)
    rwa [Units.val_pow_eq_pow_val] at this
  rw [sub_pow_char, e, one_pow] at h1
  exact pFlat_not_isUnit l (isUnit_of_dvd_unit (integral_prime_dvd_epsilon_zero_sub_one ε) h1)

theorem theta_e_succ (ε : Eps l) (k : ℕ) :
    theta0 l (WittVector.teichmuller l (ε.e (k + 1) : Ob l)) ^ l = theta0 l (WittVector.teichmuller l (ε.e k : Ob l)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]

theorem qk_succ (ε : Eps l) (k : ℕ) : ε.qk (k + 1) ^ l = ε.qk k := by
  rw [Eps.qk, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ, Eps.qk]

theorem sum_mem_ker (ε : Eps l) :
    ∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i ∈ RingHom.ker (theta0 l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [RingHom.mem_ker, map_sum]
  simp only [map_pow]
  exact geom_sum_eq_zero ((theta_e_succ ε 0).trans ε.one) ε.prim

theorem cris_sum_mem (ε : Eps l) (A : PAlg l) (n : ℕ) :
    A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1 := by
  have e : ∑ i ∈ Finset.range l, ε.qk 1 ^ i =
      algebraMap (Ainf l) (Acris l) (∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, Eps.qk]
  have h := sum_mem_ker ε
  rw [ker_theta0] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  rw [e, cris_algebraMap, ← hc, map_mul, map_mul]
  change _ * A.toAcr n A.xi ∈ _
  rw [toAcr_xi]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, le_rfl, rfl⟩)

theorem mu_eq (ε : Eps l) : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i := by
  rw [mul_geom_sum, qk_succ ε 0, Eps.μ]

theorem eps_facts : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) := by
  intro l _ ε
  haveI := isLocalRing_ob l
  exact ⟨fun i => coeff_not_isUnit _ (epsilon_one_sub_one_not_isUnit ε) i, qk_succ ε, cris_sum_mem ε, mu_eq ε,
    prim_chain (fun m => theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (theta_e_succ ε) ε.one ε.prim⟩

end GlobalTheory.CompanionTheory.EpsFacts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.CompanionTheory.LTPer

section Abs

variable {B : Type} [CommRing B]

def ltIter (ϖ : B) (q n : ℕ) : B → B := (fun x => ϖ * x + x ^ q)^[n]

def Near (S : Subring B) (ϖ : B) (J : Ideal B) (m : ℕ) (x : B) : Prop :=
  ∃ s ∈ S, x - ϖ ^ m * s ∈ J

structure PerEnv (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) : Prop where
  top : F 0 = ⊤
  anti : ∀ k, F (k + 1) ≤ F k
  mul_le : ∀ a b, F a * F b ≤ F (a + b)
  sep : ∀ x, (∀ k, x ∈ F k) → x = 0
  complete : ∀ x : ℕ → B, (∀ k, x (k + 1) - x k ∈ F k) → ∃ t, ∀ k, t - x k ∈ F k
  unit : IsUnit ϖ
  mem : ϖ ∈ S
  sumS : ∀ s : ℕ → B, (∀ n, s n ∈ S) → ∃ r ∈ S, ∀ N, ∃ a ∈ S,
    r - ∑ n ∈ Finset.range N, ϖ ^ n * s n = ϖ ^ N * a
  closed : ∀ k, ∀ x ∈ S, (∀ m, Near S ϖ (F k) m x) → x ∈ F k

def Tends (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) (x : ℕ → B) (t : B) : Prop :=
  ∀ k, ∃ c : ℕ, ∀ m, ∃ N, ∀ n ≥ N, Near S ϖ (F k) m (ϖ ^ c * (x n - t))

def EvalMod {R : Type} [CommRing R] (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) (h : R →+* B)
    (φ : PowerSeries R) (y r : B) (m : ℕ) : Prop :=
  ∀ k, ∃ D, ∀ D' ≥ D, Near S ϖ (F k) m
    ((∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * y ^ i) - r)

end Abs

section Conc

variable (l : ℕ) [Fact l.Prime]

open scoped Formalism.Per6

abbrev Tl : Type := PreTilt ↥(GroundTheory.PAdicHodge.normInteger ℂ_[l]) l

abbrev Wl : Type := WittVector l (Tl l)

def wB : Wl l →+* Formalism.Per6.BdRp l :=
  GroundTheory.PAdicHodge.wittToBDeRhamPlus ↥(GroundTheory.PAdicHodge.normInteger ℂ_[l]) l

def tch (x : Tl l) : Formalism.Per6.BdRp l := wB l (WittVector.teichmuller l x)

def rB : Om l →+* Formalism.Per6.BdRp l := (GroundTheory.PAdicHodge.algClToBdR l).toRingHom

def thB : Formalism.Per6.BdRp l →+* ℂ_[l] := (GroundTheory.PAdicHodge.thetaAlgHom l).toRingHom

def FB (k : ℕ) : Ideal (Formalism.Per6.BdRp l) := RingHom.ker (thB l) ^ k

variable {l}

def actB (g : GQ l) : Formalism.Per6.BdRp l →+* Formalism.Per6.BdRp l := MulSemiringAction.toRingHom _ _ (Formalism.Per6.toBot g)

def actT (g : GQ l) : Tl l →+* Tl l :=
  GroundTheory.PAdicHodge.preTiltMap l (GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) : ℂ_[l] →+* ℂ_[l])
    (GroundTheory.PAdicHodge.AInf.norm_galCp_toRingHom (Formalism.Per6.toBot g))

abbrev qOf {K : FinExt l} (π : ↥(OL K)) : ℕ := Nat.card (↥(OL K) ⧸ Ideal.span {π})

def oB (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) : ↥(OL K) →+* Formalism.Per6.BdRp l :=
  (rB l).comp ((μ : ↥K.1 →+* Om l).comp (algebraMap ↥(OL K) ↥K.1))

def LTData (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l) : Prop :=
  Irreducible π ∧ z 0 = 0 ∧ z 1 ≠ 0 ∧
    (∀ n, z (n + 1) ^ Nat.card (↥(OL K) ⧸ Ideal.span {π}) +
      (((π : ↥K.1) : Om l)) * z (n + 1) = z n) ∧
    ∀ (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
      ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) →
      PowerSeries.subst φ (GlobalTheory.CompanionTheory.LTHodge.ltSeries π) = PowerSeries.subst (GlobalTheory.CompanionTheory.LTHodge.ltSeries π) φ →
      ∀ n, HasSum (fun k : ℕ => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k)
        ((g : GQ l) (z n))

def PrePer (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (t : Formalism.Per6.BdRp l) : Prop :=
  t ≠ 0 ∧ (∀ (g : GQ l) (hg : g ∈ GK K), (∀ x : ↥K.1, g (μ x) = μ x) →
      actB g t = rB l (μ ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * t) ∧
    (μ = K.1.val → thB l t = 0)

end Conc

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftToThickeningStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_to_thickening : ∀ {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1) {κ : O →+* b.R ⧸ b.I} (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R)) (T : Thick (F.cr b ht κ)), ∃ g : s.R →+* T.B ⧸ T.J, (∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D), Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r) ∧ F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2 ∧ ∀ u : Fin d → T.B, (∀ k, Ideal.Quotient.mk T.J (u k) = g (s.T k)) → ∃! c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  first | exact @GlobalTheory.CompanionTheory.ThickHom.main | exact GlobalTheory.CompanionTheory.ThickHom.main | (intros; apply GlobalTheory.CompanionTheory.ThickHom.main <;> assumption)
end

