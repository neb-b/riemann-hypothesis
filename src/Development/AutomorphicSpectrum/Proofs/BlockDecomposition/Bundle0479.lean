module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHolds
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLargePrimeInRayClass
section
open NumberField IsDedekindDomain Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.DegOneRay

variable {F : Type} [Field F] [NumberField F]

theorem finite_realEmb : Finite (F →+* ℝ) :=
  Finite.of_injective (fun σ : F →+* ℝ => (Complex.ofRealHom.comp σ : F →+* ℂ)) fun σ τ h => by
    ext x
    exact Complex.ofReal_injective (congrArg (fun f : F →+* ℂ => f x) h)

theorem exists_totPos_inv {𝔣 : Ideal (𝓞 F)} (hf : 𝔣 ≠ ⊥) {u : 𝓞 F} (hu : IsCoprime (Ideal.span {u}) 𝔣) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ d * u - 1 ∈ 𝔣 ∧ ∀ σ : F →+* ℝ, 0 < σ (d : F) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hu
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have hc : c * u - 1 ∈ 𝔣 := by
    have : c * u - 1 = -j := by rw [← hij]; ring
    rw [this]; exact 𝔣.neg_mem hj
  set N : ℕ := Ideal.absNorm 𝔣 with hN
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by simpa [hN, Ideal.absNorm_eq_zero_iff] using hf)
  have hNm : ((N : ℕ) : 𝓞 F) ∈ 𝔣 := Ideal.absNorm_mem 𝔣
  have : Finite (F →+* ℝ) := finite_realEmb
  obtain ⟨b, hb⟩ := (Set.finite_range fun σ : F →+* ℝ => -σ (c : F)).bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt b
  have key : ∀ m : ℕ, M ≤ m → ((c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 ∈ 𝔣 ∧
      ∀ σ : F →+* ℝ, 0 < σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F)) := by
    intro m hm
    refine ⟨?_, fun σ => ?_⟩
    · have : (c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 = (c * u - 1) + (N : 𝓞 F) * ((m : 𝓞 F) * u) := by ring
      rw [this]
      exact 𝔣.add_mem hc (𝔣.mul_mem_right _ hNm)
    · have h1 : -σ (c : F) ≤ b := hb ⟨σ, rfl⟩
      have h2 : (M : ℝ) ≤ m := by exact_mod_cast hm
      have h3 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have e : σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F) = σ (c : F) + (m : ℝ) * (N : ℝ) := by
        push_cast
        simp
      rw [e]
      nlinarith
  by_cases h0 : c + (M : 𝓞 F) * (N : 𝓞 F) = 0
  · refine ⟨c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F), ?_, (key _ (Nat.le_succ M)).1, (key _ (Nat.le_succ M)).2⟩
    have : c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F) = (N : 𝓞 F) := by
      push_cast
      linear_combination h0
    rw [this]
    exact_mod_cast hN0.ne'
  · exact ⟨_, h0, (key M le_rfl).1, (key M le_rfl).2⟩

theorem rayRel_of_rayPair {𝔣 𝔠 𝔞 : Ideal (𝓞 F)} (hf : 𝔣 ≠ ⊥) {α β : 𝓞 F} (hr : GlobalTheory.NT.RayPair 𝔣 α β)
    (h : Ideal.span {β} * 𝔠 = Ideal.span {α} * 𝔞) : RayRel F 𝔣 𝔠 𝔞 := by
  obtain ⟨ha, hb, ha', hb', hab, hpos⟩ := hr
  have hb2 : IsCoprime (Ideal.span {β * β}) 𝔣 := by
    rw [← Ideal.span_singleton_mul_span_singleton]; exact hb'.mul_left hb'
  obtain ⟨d, hd0, hd, hdp⟩ := exists_totPos_inv hf hb2
  refine ⟨d * (β * β), d * (α * β), mul_ne_zero hd0 (mul_ne_zero hb hb),
    mul_ne_zero hd0 (mul_ne_zero ha hb), hd, ?_, fun σ => ?_, ?_⟩
  · have : d * (α * β) - 1 = (d * β) * (α - β) + (d * (β * β) - 1) := by ring
    rw [this]
    exact 𝔣.add_mem (𝔣.mul_mem_left _ hab) hd
  · have hbK : (β : F) ≠ 0 := by exact_mod_cast hb
    have hσb : σ (β : F) ≠ 0 := (map_ne_zero σ).2 hbK
    have e1 : σ ((d * (β * β) : 𝓞 F) : F) = σ (d : F) * (σ (β : F) * σ (β : F)) := by
      push_cast; simp
    have e2 : σ ((d * (α * β) : 𝓞 F) : F) = σ (d : F) * (σ (α : F) * σ (β : F)) := by
      push_cast; simp
    rw [e1, e2]
    exact ⟨mul_pos (hdp σ) (mul_self_pos.2 hσb), mul_pos (hdp σ) (hpos σ)⟩
  · calc Ideal.span {d * (β * β)} * 𝔠 = Ideal.span {d * β} * (Ideal.span {β} * 𝔠) := by
          rw [← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton, mul_assoc d]
      _ = Ideal.span {d * β} * (Ideal.span {α} * 𝔞) := by rw [h]
      _ = Ideal.span {d * (α * β)} * 𝔞 := by
          rw [← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton,
            show d * β * α = d * (α * β) by ring]

theorem finite_excluded (𝔣 : Ideal (𝓞 F)) (hf : 𝔣 ≠ ⊥) (W : Finset (𝓞 F)) (B : ℕ) (hW : ∀ x ∈ W, x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣 ∨ Ideal.absNorm v.asIdeal ≤ B ∨ ∃ x ∈ W, x ∈ v.asIdeal}.Finite := by
  have h1 : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣}.Finite := Ideal.finite_factors hf
  have h2 : {v : HeightOneSpectrum (𝓞 F) | Ideal.absNorm v.asIdeal ≤ B}.Finite := by
    have h : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B}.Finite := by
      have : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B} =
          ⋃ n ∈ Finset.range (B + 1), {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
        ext I; simp [Nat.lt_succ_iff]
      rw [this]
      exact Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => Ideal.finite_setOfPred_absNorm_eq n
    exact (h.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
      (fun v _ w _ e => HeightOneSpectrum.ext e))
  have h3 : {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal}.Finite := by
    have : {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal} =
        ⋃ x ∈ W, {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {x}} := by
      ext v
      simp [Ideal.dvd_span_singleton]
    rw [this]
    refine Set.Finite.biUnion W.finite_toSet fun x hx => Ideal.finite_factors ?_
    simpa using hW x hx
  exact (h1.union (h2.union h3)).subset fun v hv => by
    rcases hv with h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]

theorem exists_degree_one_frobenius_prime {Ω : Type} [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω)
    [FiniteDimensional F L] [IsGalois F L] (g : L ≃ₐ[F] L) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g := by
  obtain ⟨v, hv, hd, A, hA, -, σ, hσ, hg⟩ := GlobalTheory.Published.chebotarevDegreeOne' F Ω L g S hS
  refine ⟨v, hv, hd, ?_⟩
  have h := GlobalTheory.RayFromArtin.isFrob_restrict (K := F) (Ω := Ω) L hA hσ
  rwa [hg] at h

theorem exists_degOne_isFrob_of_closure (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {L : Type} [Field L]
    [NumberField L] [Algebra F L] [IsGalois F L] (g : L ≃ₐ[F] L) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite ℚ F L
  let i : L →ₐ[F] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : L ≃ₐ[F] i.fieldRange := AlgEquiv.ofInjectiveField i
  have : IsGalois F i.fieldRange := IsGalois.of_algEquiv e
  have : FiniteDimensional F i.fieldRange := e.toLinearEquiv.finiteDimensional
  obtain ⟨v, hv, hd, h⟩ := exists_degree_one_frobenius_prime i.fieldRange (e.autCongr g) S hS
  exact ⟨v, hv, hd, (GlobalTheory.Mem.Fld.isFrob_congr e v g).1 h⟩

theorem exists_degOne_isFrob {L : Type} [Field L] [NumberField L] [Algebra F L] [IsGalois F L] (g : L ≃ₐ[F] L)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g :=
  exists_degOne_isFrob_of_closure (AlgebraicClosure F) g S hS

theorem exists_degOne_prime_in_rayClass : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    CoprimeTo F 𝔣 𝔞 → ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ CoprimeTo F 𝔣 𝔠 ∧
      RayRel F 𝔣 𝔠 𝔞 ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  intro F _ _ 𝔣 𝔞 hf ha W B hW
  obtain ⟨ha0, hac⟩ := ha
  obtain ⟨L, _, _, _, hab, Art, hArt⟩ := (GlobalTheory.Published.rayClassFieldSt_iff_artinIso.1
    (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt GlobalTheory.CompanionTheory.Hypotheses₂.globalArtinReciprocity)) F 𝔣 hf
  have hc : IsCoprime 𝔞 𝔣 := Ideal.isCoprime_iff_sup_eq.2 hac
  obtain ⟨J, hJ⟩ := GlobalTheory.RayFieldCompare.exists_integral 𝔣 𝔞 ha0 hc
  obtain ⟨v, hv, hd, hfr⟩ := exists_degOne_isFrob (Art (QuotientGroup.mk J)) _ (finite_excluded 𝔣 hf W B hW)
  simp only [Set.mem_setOf_eq, not_or, not_exists, not_and] at hv
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have heq : (QuotientGroup.mk J : GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.RayClassGroup 𝔣) = GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeClass 𝔣 v hv1 :=
    Art.injective (GlobalTheory.RayFieldCompare.isFrob_unique L (hArt v hv1).1 hfr (hArt v hv1).2)
  obtain ⟨x, ⟨α, β, hr, hx⟩, hxJ⟩ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 heq)
  have e1 : J.1 * toPrincipalIdeal (𝓞 F) F x = (GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeElt 𝔣 v hv1).1 := by
    rw [hxJ, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have e2 : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) =
      (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) := by
    have h := congrArg Units.val e1
    rw [Units.val_mul, hJ, coe_toPrincipalIdeal] at h
    exact h
  have hα : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hx]
  have e3 : Ideal.span {β} * v.asIdeal = Ideal.span {α} * 𝔞 := by
    refine FractionalIdeal.coeIdeal_injective (K := F) ?_
    change ((Ideal.span {β} * v.asIdeal : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      ((Ideal.span {α} * 𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, ← e2]
    change FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F) * _ =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) * _
    rw [hα]
    ring
  refine ⟨v.asIdeal, v.isPrime, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd,
    not_le.1 hv2, ⟨v.ne_bot, ?_⟩, rayRel_of_rayPair hf hr e3, fun y hy hy' => hv3 y hy hy'⟩
  by_contra hne
  exact hv1 (Ideal.dvd_iff_le.2 ((v.isMaximal.eq_of_le hne le_sup_left).symm ▸ le_sup_right))

end GlobalTheory.CompanionTheory.DegOneRay
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOne
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def hsq (x : Lie E a) : ℝ :=
  ∑ i, ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2

theorem hsq_nonneg (x : Lie E a) : 0 ≤ hsq x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem sq_le_hsq (x : Lie E a) (i j : Fin a) (w : InfinitePlace E) :
    ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x := by
  have h1 : ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ w)
  have h2 : ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)
  have h3 : ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x :=
    Finset.single_le_sum (f := fun i => ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  exact h1.trans (h2.trans h3)

theorem hsq_oneL : hsq (oneL E a) = 0 := by
  simp [hsq, oneL, toL]

theorem dist_oneL_lt {x : Lie E a} {δ : ℝ} (hδ : 0 < δ) (h : hsq x < δ ^ 2) : dist x (oneL E a) < δ := by
  refine (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2 fun j => (dist_pi_lt_iff hδ).2 fun w => ?_
  have h1 := (sq_le_hsq x i j w).trans_lt h
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le h1

theorem contDiff_hsq : ContDiff ℝ ∞ (hsq : Lie E a → ℝ) := by
  unfold hsq
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun w _ => ContDiff.norm_sq ℝ ?_
  change ContDiff ℝ ∞ fun x : Lie E a => x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w
  fun_prop

theorem ofReal_hsq (x : Lie E a) :
    (hsq x : ℂ) = ∑ w, Matrix.trace ((Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) *
      star (Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E))) w := by
  simp only [hsq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans ?_ Finset.sum_comm
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => rfl

theorem hsq_conj (k : Kinf E a) (x : Lie E a) : hsq (toL (k.1 * Matrix.of x * star k.1)) = hsq x := by
  apply Complex.ofReal_injective
  rw [ofReal_hsq, ofReal_hsq]
  have hk : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have hk' : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of x - 1 with hY
  have e1 : (Matrix.of (toL (k.1 * Matrix.of x * star k.1)) - 1 : Matrix (Fin a) (Fin a) (Cinf E)) = k.1 * Y * star k.1 := by
    rw [hY, mul_sub, sub_mul, mul_one, hk]
    rfl
  have e2 : Matrix.trace ((k.1 * Y * star k.1) * star (k.1 * Y * star k.1)) = Matrix.trace (Y * star Y) := by
    have : (k.1 * Y * star k.1) * star (k.1 * Y * star k.1) = k.1 * ((Y * star Y) * star k.1) := by
      simp only [star_mul, star_star]
      calc k.1 * Y * star k.1 * (k.1 * (star Y * star k.1))
          = k.1 * Y * (star k.1 * k.1) * (star Y * star k.1) := by simp only [mul_assoc]
        _ = k.1 * ((Y * star Y) * star k.1) := by rw [hk']; simp only [mul_one, mul_assoc]
    rw [this, Matrix.trace_mul_comm, mul_assoc, hk', mul_one]
  rw [e1, e2]

end GlobalTheory.CompanionTheory.SmoothRep

namespace GlobalTheory.CompanionTheory.SmoothRep


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem val_image_mem_nhds_one {E : Type} [Field E] [NumberField E] {a : ℕ} {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 1) :
    (Units.val '' N) ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
  letI : NormedAddCommGroup (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap.image_mem_nhds hN

theorem exists_bump_conjInv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (N : Set (GL (Fin a) (Cinf E))), N ∈ 𝓝 1 → ∃ β₀ : Lie E a → ℝ, 0 ≤ β₀ ∧ 0 < β₀ (oneL E a) ∧
      IsTest (fun x => (β₀ x : ℂ)) ∧ ConjInv (fun x => (β₀ x : ℂ)) ∧ ∀ x, β₀ x ≠ 0 → ∃ y ∈ N, toL y.val = x := by
  intro E _ _ _ a N hN
  have h := val_image_mem_nhds_one hN
  have e : (toL '' (Units.val '' N) : Set (Lie E a)) = Units.val '' N := Set.image_id _
  have hV : (toL '' (Units.val '' N) : Set (Lie E a)) ∈ 𝓝 (oneL E a) := by
    rw [e]; exact h
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1 hV
  have hδ2 : 0 < δ ^ 2 := by positivity
  let f : ContDiffBump (0 : ℝ) := ⟨δ ^ 2 / 4, δ ^ 2 / 2, by positivity, by linarith⟩
  have hsupp : ∀ x : Lie E a, f (hsq x) ≠ 0 → hsq x < δ ^ 2 / 2 := fun x hx => by
    have : hsq x ∈ Function.support f := hx
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hsq_nonneg x)] at this
    exact this
  have hmem : ∀ x : Lie E a, hsq x ≤ δ ^ 2 / 2 → ∃ y ∈ N, toL y.val = x := fun x hx => by
    have : x ∈ Metric.ball (oneL E a) δ := dist_oneL_lt hδ (by linarith)
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hb this
    exact ⟨y, hy, rfl⟩
  have hKc : IsClosed {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    isClosed_le contDiff_hsq.continuous continuous_const
  have hts : tsupport (fun x => (f (hsq x) : ℂ)) ⊆ {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    closure_minimal (fun x hx => (hsupp x (fun h0 => hx (by simp [h0]))).le) hKc
  have hKb : {x : Lie E a | hsq x ≤ δ ^ 2 / 2} ⊆ Metric.closedBall (oneL E a) δ := fun x hx =>
    (dist_oneL_lt hδ (by simp only [Set.mem_setOf_eq] at hx; linarith)).le
  refine ⟨fun x => f (hsq x), fun x => f.nonneg, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show 0 < f (hsq (oneL E a))
    rw [hsq_oneL]
    exact f.pos_of_mem_ball (Metric.mem_ball_self f.rOut_pos)
  · exact Complex.ofRealCLM.contDiff.comp (f.contDiff.comp contDiff_hsq)
  · exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hts.trans hKb)
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hmem x (hts hx)
    exact y.isUnit
  · intro k x
    show (f (hsq (toL (k.1 * Matrix.of x * star k.1))) : ℂ) = f (hsq x)
    rw [hsq_conj]
  · exact fun x hx => hmem x (hsupp x hx).le

end GlobalTheory.CompanionTheory.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralCongruenceInvariant
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem gramQ_mul_right (D : D7) (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    gramQ V (x * a) = (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * gramQ V x * a := by
  have hm : (x * a).map (D.sp.cm.sig : D.host.E → D.host.E) =
      x.map (D.sp.cm.sig : D.host.E → D.host.E) * a.map (D.sp.cm.sig : D.host.E → D.host.E) :=
    Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
  unfold gramQ
  rw [hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

def congrEquiv (D : D7) (V : HSp D) {r : ℕ} (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E)
    (ha : a.det ≠ 0) :
    {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = (congrH a β).1} :=
  have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hi : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
  have hi' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hu
  have hu' : IsUnit (a⁻¹).det := by
    have := congrArg Matrix.det hi
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at this)
  have hc : ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
      (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have hm : (a * a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) =
        a.map (D.sp.cm.sig : D.host.E → D.host.E) * (a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) :=
      Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [← hm, hi, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  { toFun := fun x => ⟨x.1 * a, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a x.1 hu]
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]; rfl⟩
    invFun := fun x => ⟨x.1 * a⁻¹, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a⁻¹ x.1 hu']
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]
      change ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
        ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a) * a⁻¹ = β.1
      calc _ = (((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
              (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ) * β.1 * (a * a⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = β.1 := by rw [hc, hi, Matrix.one_mul, Matrix.mul_one]⟩
    left_inv := fun x => Subtype.ext (by
      change x.1 * a * a⁻¹ = x.1
      rw [Matrix.mul_assoc, hi, Matrix.mul_one])
    right_inv := fun x => Subtype.ext (by
      change x.1 * a⁻¹ * a = x.1
      rw [Matrix.mul_assoc, hi', Matrix.mul_one]) }

theorem ifrB_congrH : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (r : ℕ) (φ : Mx D V.rank r → ℂ) (β : HermE D r)
    (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    IfrB V ν φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) = IfrB V ν (pull a φ) β := by
  intro D V ν r φ β a ha
  have key : (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = (congrH a β).1},
        φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) =
      (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = β.1},
        pull a φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) := by
    funext h
    rw [← (congrEquiv D V β a ha).tsum_eq]
    refine tsum_congr fun x => ?_
    have hm : (x.1 * a).map (incA D) = HMul.hMul (x.1.map (incA D)) (a.map (incA D)) :=
      Matrix.map_mul (f := incA D)
    change φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((x.1 * a).map (incA D))) =
      φ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D))) (a.map (incA D)))
    rw [hm, Matrix.mul_assoc]
  unfold IfrB
  rw [key]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProduct
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.HaarSplit


open GroundTheory.Automorphic.Reduction in
theorem map_prod_eq_smul (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ha : 0 < a)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ := by
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph E a ha
  have hfun : (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e := by
    funext p
    exact (he p.1 p.2).symm
  rw [hfun]
  set m : Measure (GA E a) := Measure.map e (ν.prod volume) with hm
  have hemeas : Measurable e := e.continuous.measurable
  have hinv : m.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨y, s⟩, rfl⟩ := e.surjective g
    have hcomp : (fun x => e (y, s) * x) ∘ e = e ∘ Prod.map (fun x => y * x) (fun t => s + t) := by
      funext p
      obtain ⟨x, t⟩ := p
      simp only [Function.comp, Prod.map, he]
      rw [splitCentre_add, Subgroup.coe_mul]
      rw [mul_assoc, mul_assoc, ← mul_assoc (y : GA E a), ← splitCentre_comm, mul_assoc]
    have hpres : MeasurePreserving (Prod.map (fun x : normOneGL (K := E) (n := a) => y * x) (fun t : ℝ => s + t))
        (ν.prod volume) (ν.prod volume) :=
      (measurePreserving_mul_left ν y).prod (measurePreserving_add_left volume s)
    rw [hm, Measure.map_map (by fun_prop) hemeas, hcomp, ← Measure.map_map hemeas hpres.measurable, hpres.map_eq]
  have hfin : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    change Measure.map e.toMeasurableEquiv (ν.prod volume) K < ⊤
    rw [e.toMeasurableEquiv.map_apply]
    exact (e.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
  have hopen : m.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  have hhaar : m.IsHaarMeasure := { }
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure m μ
  refine ⟨(Measure.haarScalarFactor m μ : NNReal), ENNReal.coe_ne_zero.2 hc.ne', ENNReal.coe_ne_top, ?_⟩
  exact Measure.isMulLeftInvariant_eq_smul m μ

end GlobalTheory.CompanionTheory.HaarSplit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKFiniteStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_k_finite : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : GlobalTheory.CompanionTheory.ModelS.SmF n, F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev → ∃ S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n), FiniteDimensional ℂ S ∧ F ∈ S ∧ ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite | exact GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite | (intros; apply GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHoldsStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_pg_rank_zero_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG0 k := by
  first | exact @GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds | exact GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds | (intros; apply GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds <;> assumption)
end

