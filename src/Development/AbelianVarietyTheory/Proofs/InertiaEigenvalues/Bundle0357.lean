module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffMemOfToLamMem
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.LowCoeff

def genChar {T ι : Type} [CommMonoid T] [Fintype ι] (n : ℕ) [NeZero n] (u : ι → T) (hu : ∀ q, u q ^ n = 1) :
    Multiplicative (ι → ZMod n) →* T where
  toFun g := ∏ q, u q ^ (g.toAdd q).val
  map_one' := by simp
  map_mul' g h := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add]

open Classical in
theorem genChar_single {T ι : Type} [CommMonoid T] [Fintype ι] (n : ℕ) [NeZero n] [Fact (1 < n)] (u : ι → T)
    (hu : ∀ q, u q ^ n = 1) (q : ι) : genChar n u hu (Multiplicative.ofAdd (Pi.single q 1)) = u q := by
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod n) : ι → ZMod n) p).val = u q
  rw [Finset.prod_eq_single q]
  · simp [ZMod.val_one]
  · intro p _ hp
    simp [Pi.single_eq_of_ne hp]
  · simp

theorem coeff_mem_of_toLam_mem : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (I : Ideal (X.O0 i)), 0 < nu X i → nu X i + 1 ≤ M → (X.l i : X.O0 i) ^ (nu X i + 1) ∈ I → ∀ F : MvPolynomial ι (X.O0 i), toLam X i M ι F ∈ I.map (algebraMap (X.O0 i) (abelian₂ X i M ι)) → ∀ m : ι →₀ ℕ, m.degree < X.l i ^ (M - nu X i - 1) → F.coeff m ∈ I := by
  intro D N X i M ι _ I _ hM h4 F hF m hm
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  let J : Ideal (MvPolynomial ι (X.O0 i)) :=
    I.map (MvPolynomial.C : X.O0 i →+* MvPolynomial ι (X.O0 i)) ⊔ MvPolynomial.idealOfVars ι (X.O0 i) ^ (X.l i ^ (M - nu X i - 1))
  let π : MvPolynomial ι (X.O0 i) →ₐ[X.O0 i] (MvPolynomial ι (X.O0 i) ⧸ J) := Ideal.Quotient.mkₐ (X.O0 i) J
  have hI : ∀ a ∈ I, algebraMap (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) a = 0 := by
    intro a ha
    rw [← π.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
  have h4' : ((X.l i : ℕ) : MvPolynomial ι (X.O0 i) ⧸ J) ^ (nu X i + 1) = 0 := by
    have := hI _ h4
    rwa [map_pow, map_natCast] at this
  have h1 : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : Fact (1 < X.l i ^ M) := ⟨h1⟩
  haveI : NeZero (X.l i ^ M) := ⟨by omega⟩
  have hu : ∀ q, (1 + π (MvPolynomial.X q)) ^ (X.l i ^ M) = 1 := by
    intro q
    refine KStar.Tree.one_add_pow_prime_pow_eq_one hp h4' hM ?_
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_right (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self q)) _))
  let L := MonoidAlgebra.lift (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) (Del X i M ι)
    (genChar (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu)
  have hc : L.comp (toLam X i M ι) = π := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one, MonoidAlgebra.lift_of]
    have := genChar_single (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu q
    rw [sub_eq_iff_eq_add']
    convert this
  have hker : I.map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ≤ RingHom.ker L := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, L.commutes]
    exact hI a ha
  have hFJ : F ∈ J := by
    have h0 : L (toLam X i M ι F) = 0 := hker hF
    have : π F = 0 := by rw [← hc]; exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hFJ
  have hb0 : b.coeff m = 0 := (MvPolynomial.mem_pow_idealOfVars_iff' _ b).1 hb m hm
  rw [MvPolynomial.coeff_add, hb0, add_zero]
  exact MvPolynomial.mem_map_C_iff.1 ha m

end GlobalTheory.StepTwo.LowCoeff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokEquivOfExact
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.MatKerCokernel

section
variable {R : Type} [CommRing R] {a : ℕ}

abbrev Cok (Φ : Matrix (Fin a) (Fin a) R) : Type :=
  (Fin a → R) ⧸ LinearMap.range Φ.transpose.mulVecLin

def univ (Φ : Matrix (Fin a) (Fin a) R) (c : Fin a) : Cok Φ :=
  (LinearMap.range Φ.transpose.mulVecLin).mkQ (Pi.single c 1)

theorem matAct_apply' {B : Type} [AddCommGroup B] [Module R B] (Φ : Matrix (Fin a) (Fin a) R)
    (u : Fin a → B) (i : Fin a) : matAct Φ u i = ∑ j, Φ i j • u j := rfl

theorem mk_eq_sum (Φ : Matrix (Fin a) (Fin a) R) (y : Fin a → R) :
    (LinearMap.range Φ.transpose.mulVecLin).mkQ y = ∑ c, y c • univ Φ c := by
  have hy : y = ∑ c, y c • (Pi.single c 1 : Fin a → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, univ]

theorem univ_ker (Φ : Matrix (Fin a) (Fin a) R) : matAct Φ (univ Φ) = 0 := by
  funext i
  rw [matAct_apply', Pi.zero_apply]
  have h := mk_eq_sum Φ (fun j => Φ i j)
  beta_reduce at h
  rw [← h, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  refine ⟨Pi.single i 1, ?_⟩
  ext j
  simp

theorem map_ker {B B' : Type} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (Φ : Matrix (Fin a) (Fin a) R) (f : B →ₗ[R] B') (u : Fin a → B) (hu : matAct Φ u = 0) :
    matAct Φ (fun c => f (u c)) = 0 := by
  funext i
  have h := congrFun hu i
  rw [matAct_apply', Pi.zero_apply] at h
  rw [matAct_apply', Pi.zero_apply]
  calc ∑ j, Φ i j • f (u j) = f (∑ j, Φ i j • u j) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_smul]
    _ = 0 := by rw [h, map_zero]

theorem exists_lift {B : Type} [AddCommGroup B] [Module R B]
    (Φ : Matrix (Fin a) (Fin a) R) (b : Fin a → B) (hb : matAct Φ b = 0) :
    ∃ f : Cok Φ →ₗ[R] B, ∀ c, f (univ Φ c) = b c := by
  obtain ⟨g, hg⟩ : ∃ g : (Fin a → R) →ₗ[R] B, ∀ y, g y = ∑ c, y c • b c :=
    ⟨∑ c, (LinearMap.proj c).smulRight (b c), fun y => by simp [LinearMap.sum_apply]⟩
  have key : ∀ j, ∑ c, Φ j c • b c = 0 := fun j => by
    have h := congrFun hb j
    rw [matAct_apply', Pi.zero_apply] at h
    exact h
  have hle : LinearMap.range Φ.transpose.mulVecLin ≤ LinearMap.ker g := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, hg]
    calc ∑ c, (Φ.transpose.mulVecLin z) c • b c
        = ∑ c, ∑ j, z j • Φ j c • b c := by
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
            Finset.sum_smul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_comm, mul_smul]
      _ = ∑ j, z j • ∑ c, Φ j c • b c := by
          rw [Finset.sum_comm]
          simp only [Finset.smul_sum]
      _ = 0 := by simp [key]
  refine ⟨(LinearMap.range Φ.transpose.mulVecLin).liftQ g hle, fun c => ?_⟩
  rw [univ, Submodule.mkQ_apply, Submodule.liftQ_apply, hg]
  simp [Pi.single_apply]

theorem hom_ext {B : Type} [AddCommGroup B] [Module R B]
    (Φ : Matrix (Fin a) (Fin a) R) (f g : Cok Φ →ₗ[R] B)
    (h : ∀ c, f (univ Φ c) = g (univ Φ c)) : f = g := by
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun y => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, mk_eq_sum, map_sum, map_smul, h]

end

theorem cok_equiv_of_exact : ∀ (R : Type) [CommRing R] (a a' k : ℕ) (Φ : Matrix (Fin a) (Fin a) R) (Φ' : Matrix (Fin a') (Fin a') R) (x : R) (rel : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B], (Fin a → B) → (Fin a' → B) → Prop) (t : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B], (Fin a' → B) → Fin k → B), (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u u' : Fin a → B) (w : Fin a' → B), matAct Φ u = 0 → matAct Φ u' = 0 → rel B u w → rel B u' w → u = u') → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B) (w w' : Fin a' → B), matAct Φ' w = 0 → matAct Φ' w' = 0 → rel B u w → rel B u w' → w = w') → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B), matAct Φ u = 0 → ∃ w : Fin a' → B, matAct Φ' w = 0 ∧ rel B u w ∧ t B w = 0) → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (w : Fin a' → B), matAct Φ' w = 0 → t B w = 0 → ∃ u : Fin a → B, matAct Φ u = 0 ∧ rel B u w) → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (w : Fin a' → B), matAct Φ' w = 0 → ∀ j, x • t B w j = 0) → (∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (u : Fin a → B) (w : Fin a' → B), matAct Φ u = 0 → matAct Φ' w = 0 → rel B u w → rel B' (fun c => f (u c)) (fun c => f (w c))) → (∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (w : Fin a' → B), matAct Φ' w = 0 → t B' (fun c => f (w c)) = fun j => f (t B w j)) → ∃ v : Fin k → ((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin), (∀ j, x • v j = 0) ∧ Nonempty ((((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin) ⧸ Submodule.span R (Set.range v)) ≃ₗ[R] ((Fin a → R) ⧸ LinearMap.range Φ.transpose.mulVecLin)) := by
  intro R _ a a' k Φ Φ' x rel t H1 H2 H3 H4 H5 H6 H7

  let _ : TopologicalSpace (Cok Φ) := ⊥
  have : DiscreteTopology (Cok Φ) := ⟨rfl⟩
  let _ : TopologicalSpace (Cok Φ') := ⊥
  have : DiscreteTopology (Cok Φ') := ⟨rfl⟩

  obtain ⟨v, hv⟩ : ∃ v : Fin k → Cok Φ', v = t (Cok Φ') (univ Φ') := ⟨_, rfl⟩
  refine ⟨v, fun j => by rw [hv]; exact H5 _ _ (univ_ker Φ') j, ?_⟩
  obtain ⟨S, hS⟩ : ∃ S : Submodule R (Cok Φ'), S = Submodule.span R (Set.range v) := ⟨_, rfl⟩
  rw [← hS]
  let _ : TopologicalSpace (Cok Φ' ⧸ S) := ⊥
  have : DiscreteTopology (Cok Φ' ⧸ S) := ⟨rfl⟩

  have hw0 : matAct Φ' (fun c => S.mkQ (univ Φ' c)) = 0 := map_ker Φ' S.mkQ (univ Φ') (univ_ker Φ')
  have ht0 : t (Cok Φ' ⧸ S) (fun c => S.mkQ (univ Φ' c)) = 0 := by
    rw [H7 (Cok Φ') (Cok Φ' ⧸ S) S.mkQ (univ Φ') (univ_ker Φ'), ← hv]
    funext j
    simp only [Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    rw [hS]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨u0, hu0, hr0⟩ := H4 _ _ hw0 ht0
  obtain ⟨φ, hφ⟩ := exists_lift Φ u0 hu0

  obtain ⟨w1, hw1, hr1, ht1⟩ := H3 (Cok Φ) (univ Φ) (univ_ker Φ)
  obtain ⟨ψ0, hψ0⟩ := exists_lift Φ' w1 hw1
  have hψ0v : S ≤ LinearMap.ker ψ0 := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hv]
    have h := H7 (Cok Φ') (Cok Φ) ψ0 (univ Φ') (univ_ker Φ')
    rw [show (fun c => ψ0 (univ Φ' c)) = w1 from funext hψ0, ht1] at h
    exact (congrFun h j).symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Cok Φ' ⧸ S) →ₗ[R] Cok Φ, ∀ c, ψ (S.mkQ (univ Φ' c)) = w1 c :=
    ⟨S.liftQ ψ0 hψ0v, fun c => by rw [Submodule.mkQ_apply, Submodule.liftQ_apply, hψ0]⟩

  have e1 : ψ.comp φ = LinearMap.id := by
    apply hom_ext Φ
    intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hφ]
    have hk : matAct Φ (fun c => ψ (u0 c)) = 0 := map_ker Φ ψ u0 hu0
    have hr := H6 (Cok Φ' ⧸ S) (Cok Φ) ψ u0 (fun c => S.mkQ (univ Φ' c)) hu0 hw0 hr0
    simp only [hψ] at hr
    exact congrFun (H1 (Cok Φ) _ _ w1 hk (univ_ker Φ) hr hr1) c
  have e2 : φ.comp ψ = LinearMap.id := by
    apply Submodule.linearMap_qext
    apply hom_ext Φ'
    intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hψ]
    have hk : matAct Φ' (fun c => φ (w1 c)) = 0 := map_ker Φ' φ w1 hw1
    have hr := H6 (Cok Φ) (Cok Φ' ⧸ S) φ (univ Φ) w1 (univ_ker Φ) hw1 hr1
    simp only [hφ] at hr
    exact congrFun (H2 _ u0 _ _ hk hw0 hr hr0) c
  exact ⟨LinearEquiv.ofLinearMap ψ φ e1 e2⟩

end GlobalTheory.MatKerCokernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcreteProjectorEqOrthogonalProjection
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin Formalism.DivisionValues

noncomputable section

namespace GlobalTheory.EtaJoin

section Gen

variable {K : Type} [Field K] [StarRing K] {n d : ℕ}

theorem hform_eq_dot (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H.mulVec y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply, Pi.star_apply]; ring

theorem hform_orthProj (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (h : IsOrthProj H E Pr) (u : Fin d → K) (x : Fin n → K) :
    hform H (E.mulVec u) (x - E.mulVec (Pr.mulVec x)) = 0 := by
  have e : x - E.mulVec (Pr.mulVec x) = (1 - E * Pr).mulVec x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  rw [hform_eq_dot, e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h.2, Matrix.zero_mulVec, dotProduct_zero]

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (J : (Fin n → K) →ₛₗ[σ] W)

theorem semi_expand (y : Fin n → K) : J y = ∑ i, σ (y i) • J (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (y i) : Fin n → K) = y i • Pi.single i 1 := by
    ext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [this, LinearMap.map_smulₛₗ]

theorem semi_injective (hli : LinearIndependent ℂ fun i => J (Pi.single i 1)) : Function.Injective J := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand σ J y] at hy
  have h0 := (Fintype.linearIndependent_iff.1 hli) (fun i => σ (y i)) hy
  funext i
  exact σ.injective (by rw [h0 i]; simp)

theorem semi_mulVec_mem (E : Matrix (Fin n) (Fin d) K) (c : Fin d → K) :
    J (E.mulVec c) ∈ Submodule.span ℂ (Set.range fun k => J (E.mulVec (Pi.single k 1))) := by
  have e : E.mulVec c = ∑ k, c k • E.mulVec (Pi.single k 1) := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mulVec_smul]
    congr 1
    ext a; by_cases ha : a = k
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Gen

end GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

section Gen2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {σ : K →+* ℂ} {V : Type} [AddCommGroup V] [Module K V]

theorem tied_orthProj (e : (Fin n → K) ≃ₗ[K] V) (jV : V →ₛₗ[σ] W) (H Eop : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hF : FormsTie σ (jV.comp e.toLinearMap) H Eop op) (Z : Submodule ℂ W)
    (hZ : Z = Submodule.span ℂ (Set.range fun k => jV (e (E.mulVec (Pi.single k 1))))) :
    Function.Injective (e.toLinearMap ∘ₗ E.mulVecLin) ∧ Z.comap jV = LinearMap.range (e.toLinearMap ∘ₗ E.mulVecLin) ∧
      ∀ x, e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) ∈ (Zᗮ).comap jV := by
  have hin : ∀ x y, inner ℂ (jV (e x)) (jV (e y)) = σ (hform H x y) := hF.inner
  have hJinj : Function.Injective fun x => jV (e x) := fun a b h => semi_injective σ (jV.comp e.toLinearMap) hF.li h
  have hgen : ∀ c, jV (e (E.mulVec c)) ∈ Z := by
    intro c; rw [hZ]; exact semi_mulVec_mem σ (jV.comp e.toLinearMap) E c
  have horth : ∀ x, jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Zᗮ := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [hZ] at hu
    induction hu using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      show inner ℂ (jV (e (E.mulVec (Pi.single k 1)))) _ = 0
      rw [hin, hform_orthProj _ _ _ hP, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have hEinj : Function.Injective E.mulVec := by
    intro a b hab
    have := congrArg Pr.mulVec hab
    simp only [Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · exact e.injective.comp hEinj
  · ext y
    constructor
    · intro hy
      rw [Submodule.mem_comap] at hy
      obtain ⟨x, rfl⟩ := e.surjective y
      have hw1 : jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Z := by
        rw [map_sub, map_sub]; exact Submodule.sub_mem _ hy (hgen _)
      have hw0 : jV (e (x - E.mulVec (Pr.mulVec x))) = 0 :=
        inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (horth x) _ hw1)
      have hw : x = E.mulVec (Pr.mulVec x) := by
        refine sub_eq_zero.1 (hJinj ?_)
        simp only [map_zero]; exact hw0
      exact ⟨Pr.mulVec x, by simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]; rw [← hw]⟩
    · rintro ⟨c, rfl⟩
      exact hgen c
  · intro x
    rw [Submodule.mem_comap]
    have e1 : e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) = e (x - E.mulVec (Pr.mulVec x)) := by
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe, map_sub]
    rw [e1]; exact horth x

end Gen2

theorem concreteProj_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t) :=
    BlockDat.lf_l_proj (Z := Zs.Zl i t) hB
  exact tied_orthProj (eMt i t) (D.what₂.jMt (tup t) ((i : ℕ) + 1)) _ _ _ _ _ hP hF _ hZ

end GlobalTheory.EtaJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPull
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

def Layer.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {a d' : ℕ} {L₀ : FinExt l}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} {ρ' : Γ →* GL (Fin d') ℤ_[l]} (Y : Layer L₀ Cl ρ') :
    Layer L₀ ((fun ρ => ρ.comp j) '' Cl) (ρ'.comp j) where
  m := Y.m
  rep k := (Y.rep k).comp j
  mem k := ⟨Y.rep k, Y.mem k, rfl⟩
  L := Y.L
  le := Y.le
  rep_mem k g := Y.rep_mem k (j g)
  b := Y.b
  b_mem := Y.b_mem
  indep := Y.indep
  span := Y.span
  e := Y.e
  reads k := ⟨fun g => (Y.reads k).equi (j g), (Y.reads k).one⟩
  c := Y.c

def Tower.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {d : ℕ}
    {ρ : Γ →* GL (Fin d) ℤ_[l]} (T : Tower ρ) : Tower (ρ.comp j) where
  d' := T.d'
  ρ' n := (T.ρ' n).comp j
  Pi := T.Pi
  onto n := ⟨fun g => (T.onto n).equi (j g), (T.onto n).surj⟩
  f := T.f
  f_equi n g := T.f_equi n (j g)
  f_Pi := T.f_Pi

def Cover.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ]
    (j : Δ →* Γ) (hj : Continuous j) {a : ℕ} {L₀ : FinExt l} {r : Γ →* GL (Fin a) (Om l)}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} (C : Cover L₀ r Cl) :
    Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl) where
  d := C.d
  ρ := C.ρ.comp j
  cont := C.cont.comp hj
  b := C.b
  e := C.e
  reads := ⟨fun g => C.reads.equi (j g), C.reads.one⟩
  tw := C.tw.pull j
  cont' n := (C.cont' n).comp hj
  lay n := (C.lay n).pull j
  unit := C.unit
  trace := C.trace

theorem cover_pull : ∀ (l : ℕ) [Fact l.Prime] (Γ Δ : Type) [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ] (j : Δ →* Γ), Continuous j → ∀ (a : ℕ) (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))), Cover L₀ r Cl → Nonempty (Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl)) :=
  by
  intro _ _ _ _ _ _ _ _ j hj _ _ _ _ C
  exact ⟨C.pull j hj⟩

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFilteredDeRhamComparisonStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_filtered_deRham_comparison : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (a : ℤ), ∀ y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a, ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) (k i) ∧ b i ∈ (P.PD K).Fil (a - k i)) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  first | exact @GlobalTheory.SeedFil.crys_filtered | exact GlobalTheory.SeedFil.crys_filtered | (intros; apply GlobalTheory.SeedFil.crys_filtered <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportVal
section
noncomputable section

namespace GlobalTheory.Pass.CutEq

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem main : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i),
    PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  intro D i Xs π
  have h : ccAt (D.nd.T i) (cutLocus i Xs) π = GlobalTheory.Cut.ccOff i Xs π := by
    unfold ccAt GlobalTheory.Cut.ccOff Ideal.map
    congr 1
    ext a
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨f.1, f.2, fun x hx hZ => ?_, rfl⟩
      have := congrFun (RingHom.mem_ker.1 hf) ⟨x, by simp [cutLocus, hx, hZ]⟩
      exact this
    · rintro ⟨f, hf, h0, rfl⟩
      refine ⟨⟨f, hf⟩, RingHom.mem_ker.2 (funext fun y => ?_), rfl⟩
      have hy := y.2
      simp only [cutLocus, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hy
      exact h0 y.1 hy.2 hy.1
  unfold vccCut GlobalTheory.Cut.vccOff
  rw [h]

end GlobalTheory.Pass.CutEq
end
end

