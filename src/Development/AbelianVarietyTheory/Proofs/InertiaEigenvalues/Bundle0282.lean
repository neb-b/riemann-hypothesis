module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfIsIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
open scoped Formalism.Per

namespace GlobalTheory.ExpImage.EmbFil

theorem mem_range_of_isIntegral {F Ω L B : Type*} [Field F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
    [CommRing L] [Algebra F L] [CommRing B] [IsDomain B] [Algebra F B] [Algebra Ω B]
    [IsScalarTower F Ω B] (ι : L →ₐ[F] B) {x : L} (hx : IsIntegral F x) :
    ∃ a : Ω, algebraMap Ω B a = ι x :=
  IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := integralClosure Ω B) |>.2
    ⟨ι x, (hx.map ι).tower_top⟩ |>.imp fun _ h => congrArg Subtype.val h

theorem algebraMap_mem_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (T : LocTied l P AI) (a : Om l) : algebraMap (Om l) P.R.BdR a ∈ GlobalTheory.ExpImage.FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om a
  obtain ⟨-, hone, -⟩ := GlobalTheory.MemLoc.filD_laws l
  refine (T.fil _ 0 _).2 ?_
  have := Submodule.smul_mem _ y hone
  rwa [Algebra.smul_def, mul_one, ← h1] at this

theorem emb_mem_fil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (LL : FinExt l) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥LL.1),
      ι x ∈ GlobalTheory.ExpImage.FilB P 0 := by
  intro l _ P AI T LL ι x
  have := (GlobalTheory.Per.TiedField.tied_field l P AI T).1.isDomain
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨a, ha⟩ := mem_range_of_isIntegral (Ω := Om l) ι (IsIntegral.of_finite ℚ_[l] x)
  rw [← ha]
  exact algebraMap_mem_zero T a

end GlobalTheory.ExpImage.EmbFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.WachFree

theorem mem_X_smul_of_projective {D M : Type} [CommRing D] [IsDomain D] [AddCommGroup M]
    [Module D⟦X⟧ M] [Module.Projective D⟦X⟧ M] (c : D) (hc : c ≠ 0) (x y : M)
    (h : (C c : D⟦X⟧) • x = (X : D⟦X⟧) • y) : ∃ z : M, x = (X : D⟦X⟧) • z := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective D⟦X⟧ M›
  have hs' : ∀ m, Finsupp.linearCombination D⟦X⟧ id (s m) = m := fun m => LinearMap.congr_fun hs m
  have hd : ∀ m, (X : D⟦X⟧) ∣ s x m := by
    intro m
    have h1 := congrArg (fun w => constantCoeff (s w m)) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, constantCoeff_C,
      constantCoeff_X, zero_mul] at h1
    exact X_dvd_iff.mpr ((mul_eq_zero.mp h1).resolve_left hc)
  have : x ∈ LinearMap.range ((X : D⟦X⟧) • (LinearMap.id : M →ₗ[D⟦X⟧] M)) := by
    rw [← hs' x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    obtain ⟨d, hd⟩ := hd m
    exact ⟨d • m, by rw [hd, mul_smul]; rfl⟩
  obtain ⟨z, hz⟩ := this
  exact ⟨z, by simpa using hz.symm⟩

theorem free_of_regular {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular M (X : O⟦X⟧))
    (h : ∀ x y : M, (C c : O⟦X⟧) • x = (X : O⟦X⟧) • y → ∃ z : M, x = (X : O⟦X⟧) • z) :
    Module.Free O⟦X⟧ M := by
  haveI : Module.FinitePresentation O⟦X⟧ M := Module.finitePresentation_of_finite _ _
  have hker : Ideal.span {(X : O⟦X⟧)} = RingHom.ker (constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, X_dvd_iff]
  let e : (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) ≃+* O :=
    (Ideal.quotEquivOfEq hker).trans
      (RingHom.quotientKerEquivOfSurjective (f := constantCoeff (R := O))
        fun a => ⟨C a, by simp⟩)
  haveI : IsDomain (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) := e.toMulEquiv.isDomain
  haveI : IsPrincipalIdealRing (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
  have hpow : ∀ (k : ℕ) (x y : M), (C (c ^ k) : O⟦X⟧) • x = (X : O⟦X⟧) • y →
      ∃ z : M, x = (X : O⟦X⟧) • z := by
    intro k
    induction k with
    | zero => intro x y hxy; exact ⟨y, by simpa using hxy⟩
    | succ k ih =>
      intro x y hxy
      rw [pow_succ, map_mul, mul_smul] at hxy
      obtain ⟨z, hz⟩ := ih _ _ hxy
      exact h _ _ hz
  have hdvd : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ c ^ k := by
    intro a ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    obtain ⟨j, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    have hj : j ≠ 0 := by
      rintro rfl
      exact hc' (by simp)
    refine ⟨k, ?_⟩
    rw [Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd (Dvd.dvd.mul_left (dvd_pow_self _ hj) _) _
  haveI := Module.Finite.of_restrictScalars_finite O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)})
    (QuotSMulTop (X : O⟦X⟧) M)
  haveI : Module.IsTorsionFree (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) (QuotSMulTop (X : O⟦X⟧) M) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    by_cases hr : constantCoeff r = 0
    · left
      rw [Ideal.Quotient.eq_zero_iff_mem, hker]
      exact hr
    right
    have h1 : (Submodule.Quotient.mk (r • m) : QuotSMulTop (X : O⟦X⟧) M) = 0 := hrm
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
    obtain ⟨y, -, hy⟩ := h1
    obtain ⟨k, b, hb⟩ := hdvd _ hr
    obtain ⟨d, hd⟩ : (X : O⟦X⟧) ∣ C (c ^ k) - C b * r := by
      rw [X_dvd_iff]
      simp [hb, mul_comm]
    obtain ⟨z, hz⟩ := hpow k m (d • m + (C b : O⟦X⟧) • y) (by
      rw [smul_add, smul_comm (X : O⟦X⟧) (C b : O⟦X⟧) y, hy, smul_smul, smul_smul, ← hd, ← add_smul,
        sub_add_cancel])
    exact ⟨z, trivial, hz.symm⟩
  refine (Module.free_quotSMulTop_iff_free O⟦X⟧ M ?_ hX).mp inferInstance
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, isUnit_iff_constantCoeff]
  simp

theorem finrank_fibre {ι R N : Type} [DecidableEq ι] [CommRing R] [IsLocalRing R] [AddCommGroup N]
    [Module (ι → R) N] [Module.Finite (ι → R) N] [Module.Flat (ι → R) N] (i : ι) :
    ∃ r : ℕ, ∀ (S : Type) [CommRing S] [Nontrivial S] [Algebra (ι → R) S],
      algebraMap (ι → R) S (Pi.single i 1) = 1 → Module.finrank S (S ⊗[ι → R] N) = r := by
  letI : Algebra (ι → R) R := (Pi.evalRingHom (fun _ : ι => R) i).toAlgebra
  haveI : Module.Free R (R ⊗[ι → R] N) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.finrank R (R ⊗[ι → R] N), fun S _ _ _ hS => ?_⟩
  letI : Algebra R S := ((algebraMap (ι → R) S).comp (Pi.constRingHom ι R)).toAlgebra
  haveI : IsScalarTower (ι → R) R S := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap (ι → R) S a = algebraMap (ι → R) S (fun _ => a i)
    have : a * Pi.single i 1 = (fun _ => a i) * Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    have h2 := congrArg (algebraMap (ι → R) S) this
    rwa [map_mul, map_mul, hS, mul_one, mul_one] at h2
  rw [← (AlgebraTensorModule.cancelBaseChange (ι → R) R S S N).finrank_eq,
    Module.finrank_baseChange]

theorem basis_of_baseChange {ι R N E D : Type} [Finite ι] [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module (ι → R) N] [Module.Finite (ι → R) N] [Module R N]
    [IsScalarTower R (ι → R) N] [Module.Flat R N] [CommRing E] [Algebra (ι → R) E]
    (hE : Function.Injective (algebraMap (ι → R) E)) [AddCommGroup D] [Module E D]
    [Module (ι → R) D] [IsScalarTower (ι → R) E D] [Module.Free E D] (f : N →ₗ[ι → R] D)
    (hf : IsBaseChange E f) : Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → R) N) := by
  classical
  haveI := Fintype.ofFinite ι
  haveI : Module.Flat (ι → R) N := Algebra.FormallyUnramified.flat_of_restrictScalars R (ι → R) N
  haveI : Finite (MaximalSpectrum (ι → R)) := by
    haveI := (Algebra.QuasiFinite.finite_primesOver (S := ι → R)
      (IsLocalRing.maximalIdeal R)).to_subtype
    refine Finite.of_injective (fun n : MaximalSpectrum (ι → R) =>
      (⟨n.asIdeal, n.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
        (@Ideal.isMaximal_comap_of_isIntegral_of_isMaximal R _ _ _ _
          (algebraMap_isIntegral_iff.mpr inferInstance) n.asIdeal n.isMaximal)).symm⟩⟩ :
        (IsLocalRing.maximalIdeal R).primesOver (ι → R))) fun a b hab => ?_
    exact MaximalSpectrum.ext (congrArg Subtype.val hab)
  refine Module.nonempty_basis_of_flat_of_finrank_eq _ _ _ fun P => ?_
  haveI := P.isMaximal
  have hee : ∀ i : ι, (Pi.single i 1 : ι → R) * (Pi.single i 1 - 1) = 0 := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  obtain ⟨i, hi⟩ : ∃ i : ι, (Pi.single i 1 : ι → R) ∉ P.asIdeal := by
    by_contra hcon
    push Not at hcon
    apply P.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← Finset.univ_sum_single (1 : ι → R)]
    exact Ideal.sum_mem _ fun j _ => hcon j
  have hi' : (Pi.single i 1 - 1 : ι → R) ∈ P.asIdeal :=
    (P.isMaximal.isPrime.mem_or_mem (by rw [hee i]; exact Ideal.zero_mem _)).resolve_left hi
  obtain ⟨r, hr⟩ := finrank_fibre (R := R) (N := N) i
  rw [hr ((ι → R) ⧸ P.asIdeal) (by
    rw [Ideal.Quotient.algebraMap_eq, ← map_one (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq]
    exact hi')]
  let I : Ideal E := Ideal.span {algebraMap (ι → R) E (Pi.single i 1 - 1)}
  haveI : Nontrivial (E ⧸ I) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro hI
    rw [Ideal.span_singleton_eq_top] at hI
    apply hi
    have : algebraMap (ι → R) E (Pi.single i 1) = 0 := by
      rw [← hI.mul_left_eq_zero, ← map_mul, hee, map_zero]
    rw [hE (this.trans (map_zero _).symm)]
    exact Ideal.zero_mem _
  haveI : Nontrivial E := (algebraMap E (E ⧸ I)).domain_nontrivial
  rw [← hr (E ⧸ I) (by
    rw [IsScalarTower.algebraMap_apply (ι → R) E (E ⧸ I), Ideal.Quotient.algebraMap_eq,
      ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)),
    ← (AlgebraTensorModule.cancelBaseChange (ι → R) E (E ⧸ I) (E ⧸ I) N).finrank_eq,
    (AlgebraTensorModule.congr (LinearEquiv.refl (E ⧸ I) (E ⧸ I)) hf.equiv).finrank_eq,
    Module.finrank_baseChange]

theorem basis_of_regular {ι O N E D : Type} [Finite ι] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup N] [Module (ι → O⟦X⟧) N] [Module.Finite (ι → O⟦X⟧) N]
    [CommRing E] [Algebra (ι → O⟦X⟧) E]
    (hE : Function.Injective (algebraMap (ι → O⟦X⟧) E)) [AddCommGroup D] [Module E D]
    [Module (ι → O⟦X⟧) D] [IsScalarTower (ι → O⟦X⟧) E D] [Module.Free E D]
    (f : N →ₗ[ι → O⟦X⟧] D) (hf : IsBaseChange E f) (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular N (fun _ => X : ι → O⟦X⟧))
    (h : ∀ x y : N, (fun _ => C c : ι → O⟦X⟧) • x = (fun _ => X : ι → O⟦X⟧) • y →
      ∃ z : N, x = (fun _ => X : ι → O⟦X⟧) • z) :
    Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → O⟦X⟧) N) := by
  letI : Module O⟦X⟧ N := Module.compHom _ (algebraMap O⟦X⟧ (ι → O⟦X⟧))
  haveI : IsScalarTower O⟦X⟧ (ι → O⟦X⟧) N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite O⟦X⟧ N := Module.Finite.trans (ι → O⟦X⟧) _
  haveI : Module.Free O⟦X⟧ N := free_of_regular c hc hc' hX h
  exact basis_of_baseChange hE f hf


set_option maxHeartbeats 1600000 in
theorem wach_free {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys (P.PD K) T.ρ) :
    Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T))
      (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K s LL h).N T)) := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T
  generalize H.W K s LL h = W at hproj ⊢
  obtain ⟨hfree, hrk⟩ := W.DD_free T
  rw [← hrk]
  haveI : Module.Finite (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(W.N T) :=
    Module.Finite.iff_fg.mpr (W.N_fg T)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  refine basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (O := ↥(OL LL))
    (N := ↥(W.N T)) (E := W.EE) (D := W.DD T) W.EE_inj (W.N T).subtype (W.N_base T hT)
    ((l : ℕ) : ↥(OL LL)) hl0 hl ?_ ?_
  · intro x y hxy
    have h1 : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (x : W.DD T) =
        (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (y : W.DD T) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  · intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) =
        fun _ => C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X = fun _ => X := by
      funext i
      simp [zlA]
    obtain ⟨z, hz⟩ := @mem_X_smul_of_projective ℤ_[l] ↥(W.N T) _ _ _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))) hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) x y (by
        change zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) • x =
          zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • y
        rw [e1, e2]
        exact hxy)
    refine ⟨z, ?_⟩
    change x = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • z at hz
    rw [e2] at hz
    exact hz

end GlobalTheory.WachFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTensorSemistablePeriodRingSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem monSt_surjective_onto {l : ℕ} [Fact l.Prime] (P : LocPrime l) :
    Function.Surjective (monSt P) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | monomial n a =>
    have hn : ((n + 1 : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    refine ⟨-Polynomial.monomial (n + 1) (((n + 1 : ℕ) : ℚ_[l])⁻¹ • a), ?_⟩
    rw [map_neg, monSt_apply, neg_neg, Polynomial.derivative_monomial, Nat.add_sub_cancel,
      ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem monV_surjective_onto :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V],
      Function.Surjective (monV P ℚ_[l] V) := by
  intro l _ P V _ _ x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul v b =>
    obtain ⟨c, rfl⟩ := monSt_surjective_onto P b
    exact ⟨v ⊗ₜ c, monV_tmul P v c⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatLogFloorExpLe
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

open NumberField IsDedekindDomain Module in
private lemma natLog_mul_log_two_le_log_of_le {l m : ℕ} {C : ℝ} (hl : 2 ≤ l) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ C) : (Nat.log l m : ℝ) * Real.log 2 ≤ Real.log C := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using Real.log_nonneg hC
  have h1 : Nat.log l m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hl
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 : ℝ) ^ Nat.log l m ≤ C :=
    calc (2 : ℝ) ^ Nat.log l m ≤ 2 ^ Nat.log 2 m := pow_le_pow_right₀ (by norm_num) h1
      _ ≤ m := by exact_mod_cast h2
      _ ≤ C := hm
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

open NumberField IsDedekindDomain Module in
private lemma natLog_le_add_two_mul_of_le_two_pow_mul_exp {l m k : ℕ} {L : ℝ} (hl : 2 ≤ l) (hL : 0 ≤ L)
    (hm : (m : ℝ) ≤ 2 ^ k * Real.exp L) : (Nat.log l m : ℝ) ≤ k + 2 * L := by
  have hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)
  have h := natLog_mul_log_two_le_log_of_le hl hC hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_contra hcon
  push_neg at hcon
  have : ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L := by linarith
  nlinarith


open NumberField IsDedekindDomain Module in
theorem _root_.GlobalTheory.HubLoc.cBnum_le_thirty : ∀ (l t N : ℕ) (L : ℝ), 2 ≤ l → 1 ≤ t → 1 ≤ N →
    1 ≤ L → (_root_.GlobalTheory.HubLoc.cBnum l ⌊2 * Real.exp L⌋₊ t N : ℝ) ≤ 30 * t * N * L := by
  intro l t N L hl ht hN hL
  have hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L :=
    Nat.floor_le (by positivity)
  have hm : ((2 * ⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 ^ 2 * Real.exp L := by
    push_cast
    nlinarith
  have hK := natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm
  unfold _root_.GlobalTheory.HubLoc.cBnum
  push_cast at hK ⊢
  set K : ℝ := (Nat.log l (2 * ⌊2 * Real.exp L⌋₊) : ℝ)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have htN : (1 : ℝ) ≤ t * N := one_le_mul_of_one_le_of_one_le ht' hN'
  have htNL : (1 : ℝ) ≤ t * N * L := one_le_mul_of_one_le_of_one_le htN hL
  have hL1 : L ≤ t * N * L := by nlinarith
  have ht1 : (t : ℝ) ≤ t * N * L := by nlinarith
  have hA : (t : ℝ) * N * K ≤ t * N * (2 + 2 * L) := by
    apply mul_le_mul_of_nonneg_left hK; positivity
  nlinarith

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitCont
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst

namespace GlobalTheory.LTChar

variable {l : ℕ} [Fact l.Prime]

theorem orbit_cont (y : ℂ_[l]) : Continuous fun g : GQ l => Formalism.Per.σC g y := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨z, hz⟩ : ∃ z : Om l, dist y (z : ℂ_[l]) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  let F := adjExt (z : Om l)
  haveI := F.2
  have hH : IsOpen ((F.1.fixingSubgroup : Subgroup (GQ l)) : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isOpen F.1
  have hU : IsOpen {g : GQ l | g₀⁻¹ * g ∈ F.1.fixingSubgroup} :=
    hH.preimage (continuous_const.mul continuous_id)
  have hg₀ : g₀ ∈ {g : GQ l | g₀⁻¹ * g ∈ F.1.fixingSubgroup} := by
    simp only [Set.mem_setOf_eq, inv_mul_cancel]
    exact Subgroup.one_mem _
  filter_upwards [hU.mem_nhds hg₀] with g hg
  have hgz : g z = g₀ z := by
    have h := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg z (mem_adjExt z)
    rw [AlgEquiv.mul_apply] at h
    have h' := congrArg g₀ h
    rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h'
  have e : Formalism.Per.σC g y - Formalism.Per.σC g₀ y =
      Formalism.Per.σC g (y - z) + Formalism.Per.σC g₀ ((z : ℂ_[l]) - y) := by
    rw [map_sub, map_sub, GlobalTheory.RingBasics.σC_coe, GlobalTheory.RingBasics.σC_coe, hgz]
    ring
  rw [dist_eq_norm, e]
  calc _ ≤ ‖Formalism.Per.σC g (y - z)‖ + ‖Formalism.Per.σC g₀ ((z : ℂ_[l]) - y)‖ := norm_add_le _ _
    _ = ‖y - z‖ + ‖y - z‖ := by rw [GlobalTheory.RingBasics.norm_σC, GlobalTheory.RingBasics.norm_σC, norm_sub_rev (z : ℂ_[l]) y]
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.LTChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParOfTwist
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem pointPar_of_twist (D : D7) (hT : TwistInv D) (hc : D.naut.csd D.naut.etaT)
    (hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ)) : PointPar D := by
  intro i x π hx
  obtain ⟨P, -, hB⟩ := hx
  have hp : (⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ : Formalism.BasicNotions.Part D.naut.CG) ∈
      twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
    List.mem_cons_self
  obtain ⟨h1, -, h2⟩ := hB.1 _ hp
  refine ⟨?_, (D.naut.ralg_def π).2 fun τ => ?_⟩
  · have := D.naut.csd_tw _ _ hc h2
    rwa [hT.2 _ π h1] at this
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (D.naut.infG_card D.naut.etaTinv τ)
  obtain ⟨k0, hk0⟩ := hz τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hW : (D.naut.infWt i τ).Nodup ∧
      ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    rw [D.nbc.embAV_inf i P]
    exact D.nbc.infW_alg _ _ τ
  have hle : (D.naut.infG π τ).map (· + s) ≤ D.naut.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ, ← D.naut.infG_tw π _ τ s hs]
    simp [isoInf, twistIso]
  refine ⟨Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle hW.1), fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  refine ⟨k - k0, ?_⟩
  rw [Ranks.nV] at hk
  push_cast at hk hk0 ⊢
  linear_combination hk - hk0

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonSubExpMemHodgeFiltrationStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmullerEpsilon_sub_exp_mem_hodgeFiltration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ M : ℕ, io AI (WittVector.teichmuller l AI.ε) - ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.TaylorEps.eps_sub_exp | exact GlobalTheory.ExpImage.TaylorEps.eps_sub_exp | (intros; apply GlobalTheory.ExpImage.TaylorEps.eps_sub_exp <;> assumption)
end

