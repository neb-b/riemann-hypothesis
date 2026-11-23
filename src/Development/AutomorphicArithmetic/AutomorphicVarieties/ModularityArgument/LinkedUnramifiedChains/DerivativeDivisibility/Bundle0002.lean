module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.Bundle0001
public import Mathlib.RingTheory.DedekindDomain.Different

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CondField
section
open Polynomial

namespace UpperTheory.V.J

private theorem cond_field {Λ L : Type} [CommRing Λ] [IsDomain Λ] [IsIntegrallyClosed Λ] [CharZero Λ]
    [Field L] [Algebra (FractionRing Λ) L] [Algebra Λ L] [IsScalarTower Λ (FractionRing Λ) L]
    [FiniteDimensional (FractionRing Λ) L] (g : Λ[X]) (hm : g.Monic)
    (hi : Irreducible (g.map (algebraMap Λ (FractionRing Λ)))) (r : L) (hr : aeval r g = 0)
    (hgen : Algebra.adjoin (FractionRing Λ) {r} = ⊤) (α : L) (hα : IsIntegral Λ α) :
    ∃ W : Λ[X], aeval r (derivative g) * α = aeval r W := by
  have hrA : IsIntegral Λ r := ⟨g, hm, by rwa [aeval_def] at hr⟩
  have hmin : minpoly (FractionRing Λ) r = g.map (algebraMap Λ (FractionRing Λ)) :=
    (minpoly.eq_of_irreducible_of_monic hi (by rw [aeval_map_algebraMap]; exact hr) (hm.map _)).symm
  have hd : aeval r (derivative (minpoly (FractionRing Λ) r)) = aeval r (derivative g) := by
    rw [hmin, derivative_map, aeval_map_algebraMap]
  have hd0 : aeval r (derivative g) ≠ 0 := by
    rw [← hd]
    exact (Algebra.IsSeparable.isSeparable (FractionRing Λ) r).aeval_derivative_ne_zero
      (minpoly.aeval _ r)
  have hmem : α ∈ (Algebra.traceForm (FractionRing Λ) L).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin Λ {r})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [Algebra.traceForm_apply]
    have hyi : IsIntegral Λ y := (mem_integralClosure_iff Λ L).1 (adjoin_le_integralClosure hrA hy)
    have := Algebra.isIntegral_trace (L := FractionRing Λ) (hα.mul hyi)
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    rw [Submodule.mem_one]
    exact ⟨c, hc⟩
  rw [traceForm_dualSubmodule_adjoin Λ (FractionRing Λ) hgen hrA, hd,
    Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨b, hb, hbα⟩ := hmem
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hb
  obtain ⟨W, rfl⟩ := hb
  refine ⟨W, ?_⟩
  rw [← hbα, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]

private theorem cond_core {Λ B : Type} [CommRing Λ] [IsDomain Λ] [IsIntegrallyClosed Λ] [CharZero Λ]
    [CommRing B] (φ : Λ →+* B) (Q : Ideal B) (hQ : Q.IsPrime) (t : B) (g : Λ[X]) (hm : g.Monic)
    (hi : Irreducible (g.map (algebraMap Λ (FractionRing Λ))))
    (hq : ∀ q : Λ[X], q.eval₂ φ t ∈ Q ↔ g ∣ q) (hc : ∀ c : Λ, c ≠ 0 → φ c ∉ Q)
    (a : B) (c : Λ) (hc0 : c ≠ 0) (P : Λ[X]) (haP : φ c * a - P.eval₂ φ t ∈ Q)
    (q : Λ[X]) (hqm : q.Monic) (hqa : q.eval₂ φ a ∈ Q) :
    ∃ W : Λ[X], (derivative g).eval₂ φ t * a - W.eval₂ φ t ∈ Q := by
  haveI := hQ
  haveI : Fact (Irreducible (g.map (algebraMap Λ (FractionRing Λ)))) := ⟨hi⟩
  have hne : g.map (algebraMap Λ (FractionRing Λ)) ≠ 0 := (hm.map _).ne_zero
  haveI : FiniteDimensional (FractionRing Λ) (AdjoinRoot (g.map (algebraMap Λ (FractionRing Λ)))) :=
    (AdjoinRoot.powerBasis hne).finite
  let ι : Λ →+* FractionRing (B ⧸ Q) :=
    (algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q))).comp ((Ideal.Quotient.mk Q).comp φ)
  have h0 : Function.Injective ((Ideal.Quotient.mk Q).comp φ) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    exact hc x hx0 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  have hι : Function.Injective ι := (IsFractionRing.injective (B ⧸ Q) (FractionRing (B ⧸ Q))).comp h0
  letI : Algebra Λ (FractionRing (B ⧸ Q)) := ι.toAlgebra
  let tF : FractionRing (B ⧸ Q) := algebraMap (B ⧸ Q) _ (Ideal.Quotient.mk Q t)
  have hevx : ∀ (x : B) (p : Λ[X]), aeval (algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q))
      (Ideal.Quotient.mk Q x)) p =
      algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q (p.eval₂ φ x)) := by
    intro x p
    rw [aeval_def, hom_eval₂, hom_eval₂]
    rfl
  have hev : ∀ p : Λ[X], aeval tF p =
      algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q (p.eval₂ φ t)) := hevx t
  let κ : FractionRing Λ →+* FractionRing (B ⧸ Q) := IsFractionRing.lift hι
  have hκ : ∀ c : Λ, κ (algebraMap Λ (FractionRing Λ) c) = ι c := fun c =>
    IsFractionRing.lift_algebraMap hι c
  have hroot : (g.map (algebraMap Λ (FractionRing Λ))).eval₂ κ tF = 0 := by
    rw [eval₂_map]
    have hk : κ.comp (algebraMap Λ (FractionRing Λ)) = algebraMap Λ (FractionRing (B ⧸ Q)) :=
      RingHom.ext hκ
    rw [hk, ← aeval_def, hev, Ideal.Quotient.eq_zero_iff_mem.2 ((hq g).2 dvd_rfl), map_zero]
  let θ : AdjoinRoot (g.map (algebraMap Λ (FractionRing Λ))) →ₐ[Λ] FractionRing (B ⧸ Q) :=
    { AdjoinRoot.lift κ tF hroot with
      commutes' := fun c => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [IsScalarTower.algebraMap_apply Λ (FractionRing Λ), AdjoinRoot.algebraMap_eq,
          AdjoinRoot.lift_of, hκ]
        rfl }
  have hθr : θ (AdjoinRoot.root _) = tF := AdjoinRoot.lift_root hroot
  have hθinj : Function.Injective θ := θ.toRingHom.injective
  have hθp : ∀ p : Λ[X], θ (aeval (AdjoinRoot.root _) p) =
      algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q (p.eval₂ φ t)) := by
    intro p
    rw [← Polynomial.aeval_algHom_apply, hθr, hev]
  let α : AdjoinRoot (g.map (algebraMap Λ (FractionRing Λ))) :=
    aeval (AdjoinRoot.root _) P * (algebraMap Λ _ c)⁻¹
  have hιc : ι c ≠ 0 := by
    rw [ne_eq, ← map_zero ι]
    exact fun h => hc0 (hι h)
  have hca : ι c * algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q a) =
      algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q (P.eval₂ φ t)) := by
    have h1 : Ideal.Quotient.mk Q (φ c * a) = Ideal.Quotient.mk Q (P.eval₂ φ t) :=
      Ideal.Quotient.eq.2 haP
    rw [map_mul] at h1
    rw [← h1, map_mul]
    rfl
  have hθα : θ α = algebraMap (B ⧸ Q) (FractionRing (B ⧸ Q)) (Ideal.Quotient.mk Q a) := by
    simp only [α, map_mul, map_inv₀, hθp, AlgHom.commutes]
    rw [← hca, RingHom.algebraMap_toAlgebra, mul_comm (ι c), mul_assoc, mul_inv_cancel₀ hιc, mul_one]
  have hαint : IsIntegral Λ α := by
    rw [← isIntegral_algHom_iff θ hθinj, hθα]
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, hevx, Ideal.Quotient.eq_zero_iff_mem.2 hqa, map_zero]
  have hr : aeval (AdjoinRoot.root (g.map (algebraMap Λ (FractionRing Λ)))) g = 0 := by
    rw [← aeval_map_algebraMap (FractionRing Λ), AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  obtain ⟨W, hW⟩ := cond_field g hm hi (AdjoinRoot.root _) hr AdjoinRoot.adjoinRoot_eq_top α hαint
  refine ⟨W, ?_⟩
  have h2 := congrArg θ hW
  rw [map_mul, hθp, hθα, hθp, ← map_mul, ← map_mul] at h2
  exact Ideal.Quotient.eq.1 (IsFractionRing.injective (B ⧸ Q) (FractionRing (B ⧸ Q)) h2)

end UpperTheory.V.J

theorem UpperTheory.V.J.cond :
    UpperTheory.V.J.Cond := by
  intro O Λ B _ _ _ _ _ _ _ _ lam J t s g h i a
  obtain ⟨hp, hq, hc⟩ := UpperTheory.V.J.cmpPrime O Λ B lam J t s g h i
  have hJ : J ≤ UpperTheory.V.J.cmp lam J t g i := fun x hx => by
    simp only [UpperTheory.V.J.cmp, Submodule.mem_colon_singleton]
    exact J.mul_mem_right _ hx
  obtain ⟨c, hc0, P, hP⟩ := h.prim a
  obtain ⟨q, hqm, hqa⟩ := h.int a
  exact UpperTheory.V.J.cond_core (lam : Λ →+* B) _ hp t (g i) (h.monic i) (h.irr i) (hq) hc a c hc0 P
    (hJ hP) q hqm (hJ hqa)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LyOver
section
open Polynomial

private theorem ext_injective {R S K : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Field K]
    [IsAlgClosed K] (f : R →+* S) (hi : Function.Injective f) (hf : f.IsIntegral) (φ : R →+* K)
    (hφ : Function.Injective φ) : ∃ ψ : S →+* K, ψ.comp f = φ := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R K := φ.toAlgebra
  haveI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.2 hi
  haveI : Module.IsTorsionFree R K := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  haveI : Algebra.IsAlgebraic R S := Algebra.IsIntegral.isAlgebraic
  let e : S →ₐ[R] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨e.toRingHom, RingHom.ext fun r => e.commutes r⟩

private theorem ext_integral {R S K : Type} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    (f : R →+* S) (hf : f.IsIntegral) (φ : R →+* K) (h : RingHom.ker f ≤ RingHom.ker φ) :
    ∃ ψ : S →+* K, ψ.comp f = φ := by
  letI : Algebra R S := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) ⊥ (by
    intro r hr
    apply h
    rw [RingHom.mem_ker]
    exact Ideal.mem_bot.1 (Ideal.mem_comap.1 hr))
  have hQc' : Q.comap f = RingHom.ker φ := hQc
  let φ' : R ⧸ Q.comap f →+* K := Ideal.Quotient.lift _ φ (fun a ha => by
    rw [hQc'] at ha
    exact ha)
  have hφ' : Function.Injective φ' := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc']
    exact hx
  obtain ⟨ψ, hψ⟩ := ext_injective (Ideal.quotientMap Q f le_rfl) Ideal.quotientMap_injective
    (RingHom.IsIntegral.quotient f hf) φ' hφ'
  refine ⟨ψ.comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  have := congrArg (fun g => g (Ideal.Quotient.mk _ r)) hψ
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk] at this ⊢
  exact this.trans (Ideal.Quotient.lift_mk _ _ _)

theorem UpperTheory.V.J.lyOver :
    UpperTheory.V.J.LyOver := by
  intro O Λ B K _ _ _ _ _ _ _ _ _ lam J t s g hC p z i hz
  obtain ⟨hprime, hdiv, hnot⟩ := UpperTheory.V.J.cmpPrime O Λ B lam J t s g hC i
  set Q := UpperTheory.V.J.cmp lam J t g i with hQdef
  have hJQ : J ≤ Q := by
    intro a ha
    rw [hQdef, UpperTheory.V.J.cmp, Submodule.mem_colon]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    simpa [smul_eq_mul] using J.mul_mem_right _ ha
  let f : Λ[X] →+* B ⧸ Q := (Ideal.Quotient.mk Q).comp (eval₂RingHom (lam : Λ →+* B) t)
  have hfC : f.comp C = (Ideal.Quotient.mk Q).comp (lam : Λ →+* B) := by
    ext c
    simp [f]
  have hint : f.IsIntegral := by
    apply RingHom.IsIntegral.tower_top C f
    rw [hfC]
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, hqm, hq⟩ := hC.int b
    refine ⟨q, hqm, ?_⟩
    rw [← hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hJQ hq
  let φ : Λ[X] →+* K := eval₂RingHom (p : Λ →+* K) z
  have hker : RingHom.ker f ≤ RingHom.ker φ := by
    intro q hq
    rw [RingHom.mem_ker] at hq ⊢
    have hq' : eval₂ (lam : Λ →+* B) t q ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [f] using hq
    obtain ⟨r, rfl⟩ := (hdiv q).1 hq'
    simp only [φ, coe_eval₂RingHom, eval₂_mul]
    rw [hz, zero_mul]
  obtain ⟨ψ, hψ⟩ := ext_integral f hint φ hker
  have hc : ∀ c, ψ (Ideal.Quotient.mk Q (lam c)) = p c := by
    intro c
    have := congrArg (fun h => h (C c)) hψ
    simpa [f, φ] using this
  have ht : ψ (Ideal.Quotient.mk Q t) = z := by
    have := congrArg (fun h => h X) hψ
    simpa [f, φ] using this
  refine ⟨{ toRingHom := ψ.comp (Ideal.Quotient.mk Q), commutes' := ?_ }, ?_, ?_, ?_⟩
  · intro o
    have := hc (algebraMap O Λ o)
    simpa using this
  · intro b hb
    rw [RingHom.mem_ker]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hb]
  · ext c
    simpa using hc c
  · simpa using ht
end

