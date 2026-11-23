module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0241
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0242
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdicSumExists
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.PowerSeriesSum

theorem adic_sum_exists {W : Type} [CommRing W] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (N : ℕ) (hN : 0 < N) (b : ℕ → W) :
    ∃ L : W, ∀ M, ∃ c : W,
      L - ∑ n ∈ Finset.range M, (p : W) ^ (n / N) * b n = (p : W) ^ (M / N) * c := by
  set I : Ideal W := Ideal.span {(p : W)} with hI
  set g : ℕ → W := fun M => ∑ n ∈ Finset.range M, (p : W) ^ (n / N) * b n with hg
  have key : ∀ e M₁ M₂, e * N ≤ M₁ → M₁ ≤ M₂ → g M₂ - g M₁ ∈ I ^ e := by
    intro e M₁ M₂ h₁ h₂
    simp only [hg]
    rw [← Finset.sum_Ico_eq_sub _ h₂]
    refine Ideal.sum_mem _ fun n hn => ?_
    have hn' : e ≤ n / N := (Nat.le_div_iff_mul_le hN).2 (h₁.trans (Finset.mem_Ico.1 hn).1)
    exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hn'
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := W) inferInstance
    (f := fun k => g (k * N)) (by
      intro m n hmn
      rw [SModEq.sub_mem]
      simp only [smul_eq_mul, Ideal.mul_top]
      have := key m (m * N) (n * N) le_rfl (Nat.mul_le_mul_right N hmn)
      have h2 := (I ^ m).neg_mem this
      simpa using h2)
  refine ⟨L, fun M => ?_⟩
  have h₁ : L - g (M / N * N) ∈ I ^ (M / N) := by
    have := hL (M / N)
    rw [SModEq.sub_mem] at this
    simp only [smul_eq_mul, Ideal.mul_top] at this
    have h2 := (I ^ (M / N)).neg_mem this
    simpa using h2
  have h₂ : g M - g (M / N * N) ∈ I ^ (M / N) := key _ _ _ le_rfl (Nat.div_mul_le_self M N)
  have h₃ : L - g M ∈ I ^ (M / N) := by
    have := (I ^ (M / N)).sub_mem h₁ h₂
    simpa using this
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h₃
  obtain ⟨c, hc⟩ := h₃
  exact ⟨c, by rw [mul_comm, hc]⟩

theorem sum_exists {W B : Type} [CommRing W] [CommRing B] (w : W →+* B) (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (S : Subring B) (T : Finset B)
    (hw : ∀ a, w a ∈ S) (hT : ∀ t ∈ T, t ∈ S)
    (hgen : ∀ s ∈ S, ∃ a : B → W, s = ∑ t ∈ T, t * w (a t))
    (ϖ y : B) (N : ℕ) (hN : 0 < N) (hϖ : ϖ ∈ S) (hy : y ∈ S) (hN' : ϖ ^ N = (p : B) * y)
    (s : ℕ → B) (hs : ∀ n, s n ∈ S) :
    ∃ r ∈ S, ∀ M, ∃ c ∈ S,
      r - ∑ n ∈ Finset.range M, ϖ ^ n * s n = (p : B) ^ (M / N) * c := by
  have hu : ∀ n, ϖ ^ (n % N) * y ^ (n / N) * s n ∈ S := fun n =>
    S.mul_mem (S.mul_mem (S.pow_mem hϖ _) (S.pow_mem hy _)) (hs n)
  choose a ha using fun n => hgen _ (hu n)
  have hpow : ∀ n, ϖ ^ n * s n = (p : B) ^ (n / N) * ∑ t ∈ T, t * w (a n t) := by
    intro n
    rw [← ha n]
    have hϖn : ϖ ^ n = ((p : B) ^ (n / N) * y ^ (n / N)) * ϖ ^ (n % N) := by
      have h0 : ϖ ^ n = ϖ ^ (N * (n / N) + n % N) := by rw [Nat.div_add_mod]
      rw [h0, pow_add, pow_mul, hN', mul_pow]
    rw [hϖn]
    ring
  choose α hα using fun t => adic_sum_exists (W := W) p N hN (fun n => a n t)
  choose c hc using fun t M => hα t M
  refine ⟨∑ t ∈ T, t * w (α t), S.sum_mem fun t ht => S.mul_mem (hT t ht) (hw _), fun M => ?_⟩
  refine ⟨∑ t ∈ T, t * w (c t M), S.sum_mem fun t ht => S.mul_mem (hT t ht) (hw _), ?_⟩
  have hterm : ∀ t, w (α t) = ∑ n ∈ Finset.range M, (p : B) ^ (n / N) * w (a n t)
      + (p : B) ^ (M / N) * w (c t M) := by
    intro t
    have h := congrArg w (hc t M)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_pow, map_natCast] at h
    rw [← h]; ring
  simp only [hpow, hterm, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hswap : ∑ n ∈ Finset.range M, ∑ t ∈ T, (p : B) ^ (n / N) * (t * w (a n t))
      = ∑ t ∈ T, ∑ n ∈ Finset.range M, t * ((p : B) ^ (n / N) * w (a n t)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun n _ => by ring
  rw [hswap, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem sum_with_tails {W B : Type} [CommRing W] [CommRing B] (w : W →+* B) (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (S : Subring B) (T : Finset B) :
    (∀ a, w a ∈ S) → (∀ t ∈ T, t ∈ S) → (∀ s ∈ S, ∃ a : B → W, s = ∑ t ∈ T, t * w (a t)) →
    (∀ x, (∀ m : ℕ, ∃ s ∈ S, x = (p : B) ^ m * s) → x = 0) →
    ∀ (ϖ y : B) (N : ℕ), 0 < N → ϖ ∈ S → y ∈ S → ϖ ^ N = (p : B) * y →
    ∀ s : ℕ → B, (∀ n, s n ∈ S) → ∃ r ∈ S, ∀ M, ∃ a ∈ S,
      r - ∑ n ∈ Finset.range M, ϖ ^ n * s n = ϖ ^ M * a := by
  intro hw hT hgen hsep ϖ y N hN hϖ hy hN' s hs
  obtain ⟨r, hrS, hr⟩ := sum_exists w p S T hw hT hgen ϖ y N hN hϖ hy hN' s hs
  refine ⟨r, hrS, fun M => ?_⟩
  obtain ⟨rM, hrMS, hrM⟩ := sum_exists w p S T hw hT hgen ϖ y N hN hϖ hy hN'
    (fun n => s (M + n)) (fun n => hs _)
  refine ⟨rM, hrMS, ?_⟩
  have hd : r - ∑ n ∈ Finset.range M, ϖ ^ n * s n - ϖ ^ M * rM = 0 := by
    refine hsep _ fun m => ?_
    obtain ⟨c₁, hc₁S, hc₁⟩ := hr (M + N * m)
    obtain ⟨c₂, hc₂S, hc₂⟩ := hrM (N * m)
    have hdiv₁ : (M + N * m) / N = M / N + m := Nat.add_mul_div_left _ _ hN
    have hdiv₂ : (N * m) / N = m := Nat.mul_div_cancel_left _ hN
    rw [hdiv₁] at hc₁
    rw [hdiv₂] at hc₂
    refine ⟨(p : B) ^ (M / N) * c₁ - ϖ ^ M * c₂,
      S.sub_mem (S.mul_mem (S.pow_mem (natCast_mem S p) _) hc₁S)
        (S.mul_mem (S.pow_mem hϖ _) hc₂S), ?_⟩
    rw [Finset.sum_range_add] at hc₁
    have e₁ : r = ∑ n ∈ Finset.range M, ϖ ^ n * s n
        + ∑ n ∈ Finset.range (N * m), ϖ ^ (M + n) * s (M + n)
        + (p : B) ^ (M / N + m) * c₁ := by rw [← hc₁]; ring
    have e₂ : rM = ∑ n ∈ Finset.range (N * m), ϖ ^ n * s (M + n) + (p : B) ^ m * c₂ := by
      rw [← hc₂]; ring
    have e₃ : ∑ n ∈ Finset.range (N * m), ϖ ^ (M + n) * s (M + n)
        = ϖ ^ M * ∑ n ∈ Finset.range (N * m), ϖ ^ n * s (M + n) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e₁, e₂, e₃]
    ring
  exact sub_eq_zero.1 hd

end GlobalTheory.CompanionTheory.LTPer.PowerSeriesSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineRestrictionFunctionsNaturality
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

namespace GlobalTheory.CompanionTheory.GE.FormalShift

attribute [local instance] algebraOfOver

theorem restrict_idealPow_lift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; (∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a)) → ∀ (G : Z.Modules) [G.IsQuasicoherent] (m : ℕ), ∃ g : (idealPow I G m).restrict (φ ⁻¹ᵁ V).ι ⟶ idealPow (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m, g ≫ idealPowι (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m = (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) := by
  intro A _ _ I X Z _ _ φ V hV _
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  intro hcomp G _ m
  haveI : (G.restrict (φ ⁻¹ᵁ V).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have hf : (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) ≫
      cokernel.π (idealSumMap (G.restrict (φ ⁻¹ᵁ V).ι)
        (Ideal.map (toFunctions (A := A) V) I ^ m)) = 0 := by
    refine hom_eq_zero_of_affineOpens _ fun U s ↦ ?_
    have hU : IsAffineOpen (U : (φ ⁻¹ᵁ V).toScheme.Opens) := U.2
    have hU' : IsAffineOpen ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) :=
      hU.image_of_isOpenImmersion _
    have h1 : (idealPowι I G m).app ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) s ∈
        (Ideal.map (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m) • ⊤ :
          Submodule _ _) :=
      (Set.ext_iff.1 (range_idealPowι_app I G hU' m) _).1 ⟨s, rfl⟩
    have hJ : ∀ a ∈ Ideal.map
        (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m),
        ((φ ⁻¹ᵁ V).ι.appIso (U : (φ ⁻¹ᵁ V).toScheme.Opens)).hom a ∈
          Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) := by
      intro a ha
      have h := Ideal.mem_map_of_mem ((φ ⁻¹ᵁ V).ι.appIso (U : (φ ⁻¹ᵁ V).toScheme.Opens)).hom.hom ha
      rw [Ideal.map_map] at h
      rw [← Ideal.map_pow, Ideal.map_map]
      convert h using 2
      ext r
      exact (hcomp U r).symm
    have h2 : ∀ x ∈ (Ideal.map
        (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m) • ⊤ :
          Submodule Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))),
        (G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv x ∈
          (Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) • ⊤ :
              Submodule Γ((φ ⁻¹ᵁ V).toScheme, (U : (φ ⁻¹ᵁ V).toScheme.Opens))
                Γ(G.restrict (φ ⁻¹ᵁ V).ι, (U : (φ ⁻¹ᵁ V).toScheme.Opens))) := by
      intro x hx
      refine Submodule.smul_induction_on
        (p := fun x ↦ (G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv x ∈
          (Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) • ⊤ :
              Submodule Γ((φ ⁻¹ᵁ V).toScheme, (U : (φ ⁻¹ᵁ V).toScheme.Opens))
                Γ(G.restrict (φ ⁻¹ᵁ V).ι, (U : (φ ⁻¹ᵁ V).toScheme.Opens)))) hx ?_ ?_
      · intro a ha y _
        show _ ∈ _
        rw [Scheme.Modules.smul_restrictAppIso_inv_apply]
        exact Submodule.smul_mem_smul (hJ a ha) Submodule.mem_top
      · intro y z hy hz
        show _ ∈ _
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hy hz
    obtain ⟨y, hy⟩ := (Set.ext_iff.1 (range_idealPowι_app
      (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) hU m) _).2 (h2 _ h1)
    change (cokernel.π (idealSumMap (G.restrict (φ ⁻¹ᵁ V).ι)
        (Ideal.map (toFunctions (A := A) V) I ^ m))).app (U : (φ ⁻¹ᵁ V).toScheme.Opens)
      ((G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv
        ((idealPowι I G m).app ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) s)) = 0
    rw [← hy, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, kernel.condition,
      Scheme.Modules.Hom.zero_app]
    rfl
  exact ⟨kernel.lift _ _ hf, kernel.lift_ι _ _ _⟩

end GlobalTheory.CompanionTheory.GE.FormalShift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartTensorBaseCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_tensor_base_compat : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (eO (1 ⊗ₜ f))) →
      (∀ f, ev cA.D cA.inV f = Ideal.Quotient.mk _ (eA (1 ⊗ₜ f))) →
      ∃ e₀ : cO.D ⟶ ((nmO γ q).mor 0).obj cA.D, ∀ f, e₀.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := by
  first | exact @GlobalTheory.CompanionTheory.BcMor.chart_mor | exact GlobalTheory.CompanionTheory.BcMor.chart_mor | (intros; apply GlobalTheory.CompanionTheory.BcMor.chart_mor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

variable {X Z : Scheme.{0}}

theorem pushforward_map_smulHom_appTop (φ : Z ⟶ X) (H : Z.Modules) (r : Γ(X, ⊤)) :
    (Scheme.Modules.pushforward φ).map (GroundTheory.Arith.SchemeCoh.smulHom H (φ.appTop r)) =
      GroundTheory.Arith.SchemeCoh.smulHom ((Scheme.Modules.pushforward φ).obj H) r := by
  ext U x
  rw [GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.QCoh.pushforward_smul]
  refine (GroundTheory.Arith.SchemeCoh.smulHom_app_apply H (φ.appTop r) (φ ⁻¹ᵁ U) x).trans ?_
  congr 1
  unfold GroundTheory.Arith.SchemeCoh.restrictTop
  have h := φ.naturality (homOfLE (le_top : U ≤ ⊤)).op
  have h2 := congrArg (fun g => CommRingCat.Hom.hom g r) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2.symm

theorem pullback_map_smulHom_appTop (φ : Z ⟶ X) (E : X.Modules) (a : Γ(X, ⊤)) :
    (Scheme.Modules.pullback φ).map (GroundTheory.Arith.SchemeCoh.smulHom E a) =
      GroundTheory.Arith.SchemeCoh.smulHom _ (φ.appTop a) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_smulHom_appTop]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality _).symm.trans
    (GroundTheory.Arith.SchemeCoh.smulHom_comp _ _)

theorem pullback_map_comp_eq_zero_iff (φ : Z ⟶ X) {D E : X.Modules} {Q : Z.Modules} (f : D ⟶ E)
    (q : (Scheme.Modules.pullback φ).obj E ⟶ Q) :
    (Scheme.Modules.pullback φ).map f ≫ q = 0 ↔
      f ≫ (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E Q q = 0 := by
  rw [← Adjunction.homEquiv_naturality_left]
  constructor
  · intro h
    rw [h, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
  · intro h
    apply ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv D Q).injective
    rw [h, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

theorem appTop_algebraMap [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (a : A) :
    φ.appTop (algebraMap A Γ(X, ⊤) a) = algebraMap A Γ(Z, ⊤) a := by
  unfold GroundTheory.Arith.SchemeCoh.algebraOfOver GroundTheory.Arith.SchemeCoh.overAlgebra
  simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  rw [← hφ, Scheme.Hom.comp_appTop]
  rfl

theorem exists_smulHom_eq_comp_idealSumMap [X.Over (Spec (.of A))] (F : X.Modules) (J : Ideal A) {a : A}
    (ha : a ∈ J) : ∃ L : F ⟶ (⨁ fun _ : Fin (idealGenNum J) => F),
      GroundTheory.Arith.SchemeCoh.smulHom F (algebraMap A Γ(X, ⊤) a) = L ≫ idealSumMap F J := by
  rw [← GroundTheory.Arith.SchemeCoh.span_idealGen J] at ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ha
  refine ⟨biproduct.lift fun k => GroundTheory.Arith.SchemeCoh.smulHom F (algebraMap A Γ(X, ⊤) (c k)), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GroundTheory.Arith.SchemeCoh.idealSumMap, biproduct.lift_desc, ← hc, map_sum,
    GroundTheory.Arith.SchemeCoh.smulHom_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, map_mul, GroundTheory.Arith.SchemeCoh.smulHom_comp_smulHom]

theorem arrow_comp_cokernel_eq_zero {C : X.Modules} {D T : Subobject C} (h : D ≤ T) :
    D.arrow ≫ cokernel.π T.arrow = 0 := by
  rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, Limits.comp_zero]

theorem pullback_idealPowι_comp_eq_zero [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (E : X.Modules) (n : ℕ)
    {T : Subobject ((Scheme.Modules.pullback φ).obj E)}
    (hT : powSub I ((Scheme.Modules.pullback φ).obj E) n ≤ T) :
    (Scheme.Modules.pullback φ).map (idealPowι I E n) ≫ cokernel.π T.arrow = 0 := by
  have h0 : kernel.ι (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap
      ((Scheme.Modules.pullback φ).obj E) (I ^ n))) ≫ cokernel.π T.arrow = 0 := by
    change GroundTheory.Arith.SchemeCoh.idealPowι I ((Scheme.Modules.pullback φ).obj E) n ≫
      cokernel.π T.arrow = 0
    have e := Subobject.underlyingIso_arrow
      (GroundTheory.Arith.SchemeCoh.idealPowι I ((Scheme.Modules.pullback φ).obj E) n)
    have e2 : (Subobject.mk (GroundTheory.Arith.SchemeCoh.idealPowι I ((Scheme.Modules.pullback φ).obj E)
        n)).arrow ≫ cokernel.π T.arrow = 0 := arrow_comp_cokernel_eq_zero hT
    rw [← e, Category.assoc, e2, Limits.comp_zero]
  have hz : GroundTheory.Arith.SchemeCoh.idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ n) ≫
      cokernel.π T.arrow = 0 := by
    rw [← kernel.lift_ι (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap _ (I ^ n)))
      (GroundTheory.Arith.SchemeCoh.idealSumMap _ (I ^ n)) (cokernel.condition _), Category.assoc, h0,
      Limits.comp_zero]
  have key : GroundTheory.Arith.SchemeCoh.idealSumMap E (I ^ n) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _ (cokernel.π T.arrow) = 0 := by
    rw [GroundTheory.Arith.SchemeCoh.idealSumMap]
    apply biproduct.hom_ext'
    intro k
    rw [biproduct.ι_desc_assoc, Limits.comp_zero, ← Adjunction.homEquiv_naturality_left,
      pullback_map_smulHom_appTop, appTop_algebraMap φ hφ]
    obtain ⟨L, hL⟩ := exists_smulHom_eq_comp_idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ n)
      (GroundTheory.Arith.SchemeCoh.idealGen_mem (I ^ n) k)
    rw [hL, Category.assoc, hz, Limits.comp_zero, Adjunction.homEquiv_unit, Functor.map_zero,
      Limits.comp_zero]
  rw [pullback_map_comp_eq_zero_iff]
  rw [show GroundTheory.Arith.SchemeCoh.idealPowι I E n =
      kernel.ι (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap E (I ^ n))) from rfl,
    ← cokernel.π_desc (GroundTheory.Arith.SchemeCoh.idealSumMap E (I ^ n)) _ key, kernel.condition_assoc,
    Limits.zero_comp]

private theorem isQuasicoherent_imageSubobject_of_isQuasicoherent {W : Scheme.{0}} {M N : W.Modules} (f : M ⟶ N)
    (T : Subobject N) (hT : T = imageSubobject f) :
    SheafOfModules.IsQuasicoherent M ∧ SheafOfModules.IsQuasicoherent N →
      SheafOfModules.IsQuasicoherent (Subobject.underlying.obj T) := by
  subst hT
  have e := (imageSubobjectIso f).symm
  intro h
  exact @GlobalTheory.QCoh.isQuasicoherent_of_iso _ _ _ e (@GlobalTheory.QCoh.isQuasicoherent_image _ _ _ f h.1 h.2)

theorem closedSys_pullSys {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))]
    [IsLocallyNoetherian X] (φ : Z ⟶ X) (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)))
    {E : X.Modules} (hE : IsCoherent E) {S : ℕ → Subobject E} (hS : ClosedSys I E S) :
    ClosedSys I ((Scheme.Modules.pullback φ).obj E) (pullSys I φ E S) := by
  have hle : ∀ e, S (e + 1) ≤ S e := fun e => by
    rw [hS.succ e]
    exact le_sup_left
  unfold GlobalTheory.CompanionTheory.GE.pullSys
  refine ⟨fun e => ?_, fun e => le_sup_right, fun e => ?_⟩
  · have hpb : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pullback φ).obj E) :=
      @GlobalTheory.QCoh.isQuasicoherent_pullback _ _ φ E hE.1
    exact (GlobalTheory.CompanionTheory.GE.supsecs hpb _ _
      (isQuasicoherent_imageSubobject_of_isQuasicoherent ((Scheme.Modules.pullback φ).map (S e).arrow) _ rfl
        ⟨@GlobalTheory.QCoh.isQuasicoherent_pullback _ _ φ _ (hS.qcoh e), hpb⟩)
      ((@closedSys_pow A _ _ I _ _ ((Scheme.Modules.pullback φ).obj E) hpb).qcoh e)).1
  · apply le_antisymm
    · refine sup_le ?_ le_sup_right
      generalize hT : (imageSubobject ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow) ⊔
          powSub I ((Scheme.Modules.pullback φ).obj E) (e + 1 + 1)) ⊔
          powSub I ((Scheme.Modules.pullback φ).obj E) (e + 1) = T
      have hT1 : imageSubobject ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow) ≤ T := by
        rw [← hT]
        exact le_sup_left.trans le_sup_left
      have hT2 : powSub I ((Scheme.Modules.pullback φ).obj E) (e + 1) ≤ T := by
        rw [← hT]
        exact le_sup_right
      have hK : S e ≤ kernelSubobject ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _
          (cokernel.π T.arrow)) := by
        rw [hS.succ e]
        refine sup_le (le_kernelSubobject _ _ ?_) (le_kernelSubobject _ _ ?_)
        · refine (pullback_map_comp_eq_zero_iff φ _ _).1 ?_
          have e1 := imageSubobject_arrow_comp ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow)
          refine (congrArg (· ≫ cokernel.π T.arrow) e1).symm.trans ?_
          rw [Category.assoc, arrow_comp_cokernel_eq_zero hT1, Limits.comp_zero]
        · have e2 := (pullback_map_comp_eq_zero_iff φ _ _).1
            (pullback_idealPowι_comp_eq_zero I φ hφ E (e + 1) hT2)
          have e3 := Subobject.underlyingIso_hom_comp_eq_mk
            (GroundTheory.Arith.SchemeCoh.idealPowι I E (e + 1))
          exact (congrArg (· ≫ _) e3.symm).trans
            ((Category.assoc _ _ _).trans (by rw [e2]; exact Limits.comp_zero))
      have hz : (S e).arrow ≫ (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _
          (cokernel.π T.arrow) = 0 := by
        rw [← Subobject.ofLE_arrow hK, Category.assoc, kernelSubobject_arrow_comp, Limits.comp_zero]
      exact imageSubobject_le _ (Abelian.monoLift _ _ ((pullback_map_comp_eq_zero_iff φ _ _).2 hz))
        (Abelian.monoLift_comp _ _ _)
    · have him : imageSubobject ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow) ≤
          imageSubobject ((Scheme.Modules.pullback φ).map (S e).arrow) := by
        rw [← Subobject.ofLE_arrow (hle e), Functor.map_comp]
        exact imageSubobject_comp_le _ _
      exact sup_le (sup_le (him.trans le_sup_left)
        ((powSub_succ_le I _ (e + 1)).trans le_sup_right)) le_sup_right

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_subobject_coherent : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {E : X.Modules}, IsCoherent E → ∀ D : Subobject E, (D : X.Modules).IsQuasicoherent → IsCoherent (D : X.Modules) := by
  first | exact @GlobalTheory.CompanionTheory.GE.isCoherent_subobject | exact GlobalTheory.CompanionTheory.GE.isCoherent_subobject | (intros; apply GlobalTheory.CompanionTheory.GE.isCoherent_subobject <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLift
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.CLiftEx

theorem thick_isNilpotent {b : Base} {L : b.Fun} (T : Thick L) (x : T.B) (hx : x ∈ T.J) :
    IsNilpotent x := by
  by_cases hp : b.p = 0
  · obtain ⟨k, hk⟩ := T.adm.2 hp
    refine ⟨k, ?_⟩
    simpa [hk] using Ideal.pow_mem_pow hx k
  · obtain ⟨k, hk⟩ := T.adm.1 hp
    refine ⟨b.p * k, ?_⟩
    have hfac : ((b.p.factorial : ℕ) : T.B) = (b.p : T.B) * ((b.p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, ← T.δ.factorial_mul_dpow_eq_pow hx, hfac, mul_assoc, mul_pow, hk, zero_mul]

theorem unit_lift {B : Type} [CommRing B] (J : Ideal B) (hJ : ∀ x ∈ J, IsNilpotent x) (u : (B ⧸ J)ˣ) :
    ∃ w : Bˣ, Ideal.Quotient.mk J (w : B) = (u : B ⧸ J) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ J)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (B ⧸ J)ˣ) : B ⧸ J)
  have hmem : a * c - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hc, Units.mul_inv, map_one, sub_self]
  have hunit : IsUnit (a * c) := by
    have h1 := (hJ _ hmem).isUnit_one_add
    have h2 : (1 : B) + (a * c - 1) = a * c := by ring
    rwa [h2] at h1
  obtain ⟨w, hw⟩ := isUnit_of_mul_isUnit_left hunit
  exact ⟨w, by rw [hw, ha]⟩

theorem nonempty_cLift : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X),
    (∀ T, ∃ p : Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y, p ≫ D.f = B.thPt (G.obj T)) → Nonempty (B.CLift G D) := by
  intro O _ X q b ht κ C _ G D h
  classical
  choose p hp using h
  refine ⟨⟨p, hp, fun {T T'} φ =>
    if h : (B.thSp (G.map φ) ≫ p T) ≫ D.f = p T' ≫ D.f then
      (unit_lift (G.obj T').J (fun x hx => thick_isNilpotent (G.obj T') x hx)
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom.toMonoidHom
          (D.u (B.thSp (G.map φ) ≫ p T) (p T') h))).choose
    else 1, fun {T T'} φ h => ?_⟩⟩
  rw [dite_eq_left h]
  exact (unit_lift (G.obj T').J (fun x hx => thick_isNilpotent (G.obj T') x hx)
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom.toMonoidHom
      (D.u (B.thSp (G.map φ) ≫ p T) (p T') h))).choose_spec

end GlobalTheory.CompanionTheory.CLiftEx
end

