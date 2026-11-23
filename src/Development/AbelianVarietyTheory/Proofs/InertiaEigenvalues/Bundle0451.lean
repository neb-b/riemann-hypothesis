module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.AnnihilatorMulRelativeDifferent
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsBasisEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.HerrExtClass


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 4000000 in
theorem herr_extension_class_formula : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass Formalism.MainNotions.RamifiedCoefficientChains.adm16
  intro l _ K s LL h
  show Formalism.MainNotions.RamifiedCoefficientChains.HerrExt ((HW l).W K s LL h)
  have hA := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have hU := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  obtain ⟨e, e₀, hspan, hT, hj, hN, hEE, hφ, hγ, htf⟩ := hU
  refine ⟨e, (e₀ : ((HW l).W K s LL h).one.V), ?_, ?_, ?_⟩
  · exact ⟨by rw [hN]; exact Submodule.subset_span rfl, hN, hEE, hφ, hγ, hT⟩
  · intro T Tp ι π κ hκ hcoc x c hx w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)) := ⟨_, Formalism.MainNotions.DeltaInvariantLattices.resFun_Z1T _ T _ hcκ⟩
    have hc : ∀ g : ↥((HW l).W K s LL h).GKs, ι.f ((cr : ↥((HW l).W K s LL h).GKs → T.V) g) = Tp.ρ (g : ↥(GK K)) (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ (g : ↥(GK K)))
      have e2 := ((Tp.ρ (g : ↥(GK K))).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Formalism.MainNotions.DeltaInvariantLattices.resFun, LinearMap.funLeft_apply, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ (g : ↥(GK K))) t) t
    have key := GlobalTheory.Cyc.dict_ext_Ks D HW F hA l K s LL h T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK Formalism.MainNotions.DeltaInvariantLattices.res
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
  · intro _ hp2 T Tp ι π κ hκ hcoc x c hx hδ w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles T.L) := ⟨_, hcκ⟩
    have hc : ∀ g : ↥(GK K), ι.f ((cr : ↥(GK K) → T.V) g) = Tp.ρ g (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ g)
      have e2 := ((Tp.ρ g).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ g) t) t
    have hi : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) = 2 → ∃ i : ↥K.1, i ^ 2 = -1 :=
      fun h2' => absurd h2' hp2
    have key := GlobalTheory.ExtDict.dict_K D HW F hA l K s LL h hi T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he hδ w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK
    rw [← Submodule.Quotient.mk_smul]
    rfl

end GlobalTheory.HerrExtClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrPartAEveryRecord
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.HerrFull

theorem herr_part_a_every_record :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
      Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F :=
  fun D HW F => herr_a_and_natural D HW F

end GlobalTheory.HerrFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Hilbert90MatrixCoboundaryCharPFiniteLevel
section
namespace GlobalTheory.UnramifiedHilbertNinety

open GlobalTheory.UnramifiedCrys

theorem exists_mem_multilinear_ne_zero {R V ι : Type} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (f : (ι → V) →ₘₗ[R] R) (S : Set V)
    (hS : ∀ l : V →ₗ[R] R, (∀ s ∈ S, l s = 0) → l = 0) (v₀ : ι → V) (h₀ : f v₀ ≠ 0) :
    ∃ v : ι → V, (∀ i, v i ∈ S) ∧ f v ≠ 0 := by
  have key : ∀ T : Finset ι, ∃ v : ι → V, (∀ i ∈ T, v i ∈ S) ∧ f v ≠ 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨v₀, by simp, h₀⟩
    | insert a T ha ih =>
      obtain ⟨v, hv, hf⟩ := ih
      obtain ⟨s, hs, hne⟩ : ∃ s ∈ S, f (Function.update v a s) ≠ 0 := by
        by_contra hc
        push Not at hc
        have h1 := hS (f.toLinearMap v a) hc
        have h2 := LinearMap.congr_fun h1 (v a)
        rw [MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h2
        exact hf h2
      refine ⟨Function.update v a s, fun i hi => ?_, hne⟩
      by_cases hia : i = a
      · subst hia
        rwa [Function.update_self]
      · rw [Function.update_of_ne hia]
        exact hv i ((Finset.mem_insert.1 hi).resolve_left hia)
  obtain ⟨v, hv, hf⟩ := key Finset.univ
  exact ⟨v, fun i => hv i (Finset.mem_univ i), hf⟩

theorem exists_matrix_coboundary (p : ℕ) [hp : Fact p.Prime] (G : Type) [Group G] (R : Type)
    [CommRing R] [IsDomain R] [CharP R p] (ρ : G →* (R ≃+* R)) (m : ℕ) (hm : 0 < m)
    (hfin : Finite (G ⧸ fixer ρ p m)) (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) R)
    (hρ : ∀ g h i j, ρ g (M h i j) = M h i j) (hM : ∀ h i j, M h i j ^ p ^ m = M h i j)
    (hMN : ∀ g ∈ fixer ρ p m, M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) R, IsUnit W.det ∧ (∀ i j, W i j ^ p ^ m = W i j) ∧
      ∀ g, M g * W.map (ρ g) = W := by
  classical
  set N := fixer ρ p m with hN
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let χ : G ⧸ N → (fixedPow p R m →* R) := fun x =>
    (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype
  have hχ : Function.Injective χ := by
    intro x x' h
    rw [← x.out_eq, ← x'.out_eq]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    intro y hy
    have h1 : ρ x.out y = ρ x'.out y := DFunLike.congr_fun h ⟨y, hy⟩
    rw [map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      RingAut.one_apply]
  have hli := (linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ
  have hsum : ∀ (f : G → R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
      ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out := by
    intro f hf g
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (g * x.out)
    have : MulAction.toPerm g x = QuotientGroup.mk (g * x.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← x.out_eq]
      rfl
    rw [this, hn, hf _ _ n.2]
  let S : Set (Fin r → R) := {v | (∀ i, v i ^ p ^ m = v i) ∧
    ∀ g i, ∑ k, M g i k * ρ g (v k) = v i}
  have hb : ∀ (θ : fixedPow p R m) (j : Fin r),
      (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) ∈ S := by
    intro θ j
    have hθm : (θ : R) ^ p ^ m = θ := θ.2
    refine ⟨fun i => ?_, fun g i => ?_⟩
    · rw [sum_pow_char_pow]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_pow, ← map_pow, hθm, hM]
    · have h2 := hsum (fun g => ρ g θ * M g i j) (fun g n hn => by
        simp only [map_mul, RingAut.mul_apply, hn θ hθm, hMN n hn, mul_one]) g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.mul_sum]
      rw [← h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [map_mul, RingAut.mul_apply, Matrix.mul_apply, hρ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
  have hS : ∀ l : (Fin r → R) →ₗ[R] R, (∀ s ∈ S, l s = 0) → l = 0 := by
    intro l hl
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    have h1 := Fintype.linearIndependent_iff.1 hli (fun x => l (fun i => M x.out i j)) (by
      funext θ
      simp only [Finset.sum_apply, Function.comp, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      have h3 : (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) =
          ∑ x : G ⧸ N, ρ x.out θ • (fun i => M x.out i j) := by
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h4 := hl _ (hb θ j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h3, map_sum] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl) (QuotientGroup.mk 1)
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (1 : G)
    simp only [hn, one_mul, hMN n n.2] at h1
    have h5 : (fun i => (1 : Matrix (Fin r) (Fin r) R) i j) = Pi.single j 1 := by
      funext i
      rw [Matrix.one_apply, Pi.single_apply]
    rw [h5] at h1
    simpa using h1
  obtain ⟨v, hv, hf⟩ := exists_mem_multilinear_ne_zero
    (Matrix.detRowAlternating (n := Fin r) (R := R)).toMultilinearMap S hS
    (1 : Matrix (Fin r) (Fin r) R) (by
      change (1 : Matrix (Fin r) (Fin r) R).det ≠ 0
      rw [Matrix.det_one]
      exact one_ne_zero)
  have hf' : ((Matrix.of v).transpose).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hf
  have hW : ∀ i j, (Matrix.of v).transpose i j ^ p ^ m = (Matrix.of v).transpose i j :=
    fun i j => (hv j).1 i
  refine ⟨(Matrix.of v).transpose, ?_, hW, fun g => ?_⟩
  · set t := ((Matrix.of v).transpose).det with ht
    have htq : t ^ p ^ m = t := by
      rw [← iterateFrobenius_def, ht, RingHom.map_det]
      congr 1
      ext i j
      exact hW i j
    have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
    have hu : t ^ (p ^ m - 2) * t = 1 := by
      apply mul_right_cancel₀ hf'
      rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
    exact IsUnit.of_mul_eq_one_right _ hu
  · ext i j
    exact (hv j).2 g i

end GlobalTheory.UnramifiedHilbertNinety
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkFrobOfAttached
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.HkFrobProof

theorem eval_charpolyRev_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b
  by_cases h : a = b <;> simp [h] <;> ring

theorem coeff_charpolyRev_map {n : ℕ} {R : Type} [CommRing R] (f : R →+* ℂ) (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    f (M.charpolyRev.coeff k) = (M.map f).charpolyRev.coeff k := by
  rw [← Polynomial.coeff_map]
  apply congrArg (fun p : ℂ[X] => p.coeff k)
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 1
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_smul_inv {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (h : M * A = 1) (β : Multiset ℂ)
    (hβ : (0 : ℂ) ∉ β) (hA : A.charpoly = (β.map fun a => (X : ℂ[X]) - C a).prod) (c : ℂ) :
    (c • M).charpolyRev = (β.map fun a => (1 : ℂ[X]) - C (c * a⁻¹) * X).prod := by
  have ev : ∀ y : ℂ, (y • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = (β.map fun a => y - a).prod := by
    intro y
    have := congrArg (Polynomial.eval y) hA
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at this
    simpa using this
  apply Polynomial.funext
  intro z
  rw [eval_charpolyRev_eq, eval_multiset_prod, Multiset.map_map]
  have h0 := ev 0
  have h1 := ev (z * c)
  have hne : (β.map fun a => (0 : ℂ) - a).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hm
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 hm
    have : a = 0 := by simpa using ha0
    exact hβ (this ▸ ha)
  apply mul_right_cancel₀ hne
  rw [← Multiset.prod_map_mul]
  conv_lhs => rw [← h0, ← Matrix.det_mul]
  have e : (1 - z • c • M) * ((0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A) = (z * c) • 1 - A := by
    rw [zero_smul, zero_sub, mul_neg, sub_mul, one_mul, smul_smul, Matrix.smul_mul, h, neg_sub]
  rw [e, h1]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := fun h => hβ (h ▸ ha)
  simp only [Function.comp, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)))

end GlobalTheory.TripleGal.HkFrobProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamilyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_basis_of_adapted_invariant_family : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  first | (exact @GlobalTheory.HodgeAt.hodge_of_adapted) | (exact GlobalTheory.HodgeAt.hodge_of_adapted) | (intros; apply GlobalTheory.HodgeAt.hodge_of_adapted  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeCrystallineSequences
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

noncomputable section

namespace GlobalTheory.HodgeCrysSeq

theorem hodgeExact_at (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) : Formalism.MainNotions.WachCoordinates.HodgeExact (P.PD K) ↥LL.1 ↥(OL LL) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T₁ T₂ F h1 _ hF τ a hj
    have hs : Function.Surjective F.f := by
      have hr : LinearMap.range F.f = ⊤ := by
        rw [eq_top_iff, ← T₂.L.span, Submodule.span_le]
        intro y hy
        obtain ⟨x, -, rfl⟩ := hF y hy
        exact ⟨x, rfl⟩
      exact LinearMap.range_eq_top.1 hr
    have hst : ∀ g, LinearMap.ker F.f ≤ (LinearMap.ker F.f).comap (T₁.ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, F.equiv, LinearMap.mem_ker.1 hv, map_zero]
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h1.2.2.2).1
    have := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI hT K LL (LinearMap.ker F.f)
      (T₁.ρ.subrepresentation (LinearMap.ker F.f) hst) T₁.V T₁.ρ T₂.V T₂.ρ
      (LinearMap.ker F.f).subtype F.f (fun _ _ => rfl) F.equiv (LinearMap.ker F.f).injective_subtype hs
      (Submodule.range_subtype _) hdr
    exact (this.2.2 τ a).2.2.2 (Or.inr hj)
  · intro T₀ T₁ T₂ ι π hS h1
    obtain ⟨hi, hs, -, hk, -⟩ := hS
    have c0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hi
      h1.2.2.2
    have c2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hs
      h1.2.2.2).1
    have hr : LinearMap.range ι.f = LinearMap.ker π.f := by
      ext x
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      exact (hk x).symm
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h1.2.2.2).1
    have := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f
      ι.equiv π.equiv hi hs hr hdr
    exact ⟨⟨inferInstance, inferInstance, T₀.cont, c0⟩, ⟨inferInstance, inferInstance, T₂.cont, c2⟩,
      fun τ a => (this.2.2 τ a).2.2⟩
  · intro T hT' τ a hj
    exact (GlobalTheory.TrivCrys.triv_crys_jump_zero l P AI hT K LL T.V T.ρ hT').2 τ a hj

theorem hodge_crystalline_sequences : ∀ D : D7, Formalism.MainNotions.WachCoordinates.adm14 D := by
  intro D l _ K LL
  exact hodgeExact_at l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory.HodgeCrysSeq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizEqXiRed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem horiz_eq_xi_red : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (v : Vec K a ι), P.conn v = 0 → v = P.xi (red v) := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ P v hv
  have hn : P.nabla v = 0 := by
    rw [BK.PhiMod.conn_apply] at hv
    exact (smul_right_injective _ PowerSeries.X_ne_zero) (hv.trans (smul_zero _).symm)
  set w := P.xiExt.symm v with hw
  have hvw : v = P.xiExt w := by rw [hw, LinearEquiv.apply_symm_apply]
  have hd : BK.derV w = 0 := by
    rw [hvw, BK.PhiMod.nabla_xiExt, ← map_zero P.xiExt] at hn
    exact P.xiExt.injective hn
  have hnz : ∀ m : ℕ, ((m : K) + 1) ≠ 0 := by
    intro m h
    have h2 : algebraMap ℚ_[l] K ((m : ℚ_[l]) + 1) = 0 := by
      rw [map_add (f := _), map_natCast, map_one]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective] at h2
    exact Nat.cast_add_one_ne_zero m h2
  have hc : w = BK.cst (red w) := by
    funext τ i
    ext n
    rcases n with _ | m
    · simp [BK.cst_apply, red_apply]
    · have h1 := congrArg (fun f => PowerSeries.coeff m (f τ i)) hd
      simp only [BK.derV_apply, PowerSeries.coeff_derivative] at h1
      rw [BK.cst_apply, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero m)]
      have h3 : PowerSeries.coeff (m + 1) (w τ i) * ((m : K) + 1) = 0 := by simpa using h1
      exact (mul_eq_zero.1 h3).resolve_right (hnz m)
  calc v = P.xiExt w := hvw
    _ = P.xiExt (BK.cst (red w)) := by rw [← hc]
    _ = P.xi (red v) := by rw [BK.PhiMod.xi_apply, hvw, BK.PhiMod.red_xiExt]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostImagQuadraticIsGaloisUnitsPmOne
section
open NumberField

namespace GlobalTheory.HostQuadUnits

theorem four_lt_d (D : Formalism.BasicNotions.D7) : 4 < D.host.d := by
  have h := D.host.hyp.2.2.2.1
  omega

theorem isGalois_and_units (D : Formalism.BasicNotions.D7) :
    IsGalois ℚ D.host.K ∧ ∀ u : (𝓞 D.host.K)ˣ, u = 1 ∨ u = -1 := by
  have h2 : Module.finrank ℚ D.host.K = 2 := Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D
  refine ⟨?_, fun u => ?_⟩
  · haveI : Algebra.IsQuadraticExtension ℚ D.host.K := ⟨h2⟩
    infer_instance
  · let σ : D.host.K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := D.host.K)).toRingHom
    exact GlobalTheory.QuadraticZeta.unit_eq h2 (Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.discr_K D) σ (four_lt_d D) u

theorem main : ∀ D : Formalism.BasicNotions.D7, IsGalois ℚ D.host.K ∧ ∀ u : (𝓞 D.host.K)ˣ, u = 1 ∨ u = -1 :=
  isGalois_and_units

end GlobalTheory.HostQuadUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDualityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invIso_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.InvIso := by
  first | exact @GlobalTheory.InvColim.inv_iso | exact GlobalTheory.InvColim.inv_iso | (intros; apply GlobalTheory.InvColim.inv_iso <;> assumption)
end

