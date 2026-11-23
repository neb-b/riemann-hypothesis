module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
section
open IsLocalRing Polynomial

namespace GlobalTheory.StrictHensel

theorem henselian_of_sections {R : Type} [CommRing R] [IsLocalRing R]
    (H : ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime],
      q.comap (algebraMap R A) = maximalIdeal R →
        ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) :
    HenselianLocalRing R := by
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  let P : StandardEtalePair R := ⟨f, hf, derivative f, 1, 0, 1, by simp⟩
  have e : ∀ p : R[X], aeval (residue R a₀) p = residue R (p.eval a₀) := fun p => by
    rw [← ResidueField.algebraMap_eq]; exact aeval_algebraMap_apply_eq_algebraMap_eval _ _
  have hP : P.HasMap (residue R a₀) := by
    refine ⟨?_, ?_⟩
    · change aeval (residue R a₀) f = 0
      rw [e]; exact (residue_eq_zero_iff _).mpr h₁
    · change IsUnit (aeval (residue R a₀) (derivative f))
      rw [e]; exact h₂.map (residue R)
  let ψ := P.lift (residue R a₀) hP
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hq : (RingHom.ker ψ).comap (algebraMap R P.Ring) = maximalIdeal R := by
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, ResidueField.algebraMap_eq,
      residue_eq_zero_iff]
  obtain ⟨s, hs⟩ := H P.Ring (RingHom.ker ψ) hq
  refine ⟨s P.X, ?_, ?_⟩
  · have h := (P.hasMap_X.map s).1
    simpa [P, IsRoot, coe_aeval_eq_eval] using h
  · have hmem : P.X - algebraMap R P.Ring a₀ ∈ RingHom.ker ψ := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, ResidueField.algebraMap_eq]
      simp [ψ]
    rw [← hs, Ideal.mem_comap] at hmem
    simpa using hmem

theorem isSepClosed_of_sections {R : Type} [CommRing R] [IsLocalRing R]
    (H : ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime],
      q.comap (algebraMap R A) = maximalIdeal R →
        ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) :
    IsSepClosed (ResidueField R) := by
  refine IsSepClosed.of_exists_root _ fun g hm hirr hsep => ?_
  obtain ⟨f, hf, -, hfm⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts g).2 (map_surjective _ residue_surjective g)) hm
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  let P : StandardEtalePair R := ⟨f, hfm, derivative f, 1, 0, 1, by simp⟩
  have e : ∀ p : R[X], aeval (AdjoinRoot.root g) p =
      AdjoinRoot.mk g (p.map (residue R)) := fun p => by
    rw [← AdjoinRoot.aeval_eq, ← ResidueField.algebraMap_eq, aeval_map_algebraMap]
  have hP : P.HasMap (AdjoinRoot.root g) := by
    refine ⟨?_, ?_⟩
    · change aeval (AdjoinRoot.root g) f = 0
      rw [e, hf, AdjoinRoot.mk_self]
    · change IsUnit (aeval (AdjoinRoot.root g) (derivative f))
      rw [e, ← derivative_map, hf, isUnit_iff_ne_zero, Ne, AdjoinRoot.mk_eq_zero]
      rintro ⟨c, hc⟩
      obtain ⟨a, b, hab⟩ := hsep
      exact hirr.not_isUnit (isUnit_of_dvd_one ⟨a + b * c, by rw [← hab, hc]; ring⟩)
  let ψ := P.lift (AdjoinRoot.root g) hP
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hq : (RingHom.ker ψ).comap (algebraMap R P.Ring) = maximalIdeal R := by
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R (ResidueField R) (AdjoinRoot g),
      map_eq_zero_iff _ (algebraMap (ResidueField R) (AdjoinRoot g)).injective,
      ResidueField.algebraMap_eq, residue_eq_zero_iff]
  obtain ⟨s, -⟩ := H P.Ring (RingHom.ker ψ) hq
  have ha : f.eval (s P.X) = 0 := by
    have h := (P.hasMap_X.map s).1
    simpa [P, coe_aeval_eq_eval] using h
  exact ⟨residue R (s P.X), by rw [← hf, eval_map, eval₂_hom, ha, map_zero]⟩

end GlobalTheory.StrictHensel

namespace GlobalTheory.StrictHensel

theorem sections_of_henselian_sepClosed {R : Type} [CommRing R] [IsLocalRing R]
    [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime]
    (hq : q.comap (algebraMap R A) = maximalIdeal R) :
    ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q := by
  let S := Localization.AtPrime q
  haveI : IsLocalHom (algebraMap R S) := ⟨fun r hr => by
    rw [IsScalarTower.algebraMap_apply R A S, IsLocalization.AtPrime.isUnit_to_map_iff S q] at hr
    exact (notMem_maximalIdeal).mp fun h => hr (by
      have : r ∈ q.comap (algebraMap R A) := hq ▸ h
      exact this)⟩
  haveI : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.comp R A S
  haveI : Algebra.EssFiniteType R S := Algebra.EssFiniteType.comp R A S
  have hsurj := IsSepClosed.algebraMap_surjective (ResidueField R) (ResidueField S)
  let e : ResidueField R ≃ₐ[ResidueField R] ResidueField S :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) ⟨fun a b h => (algebraMap (ResidueField R) (ResidueField S)).injective h, hsurj⟩
  let φ : A →ₐ[R] ResidueField R := ((e.symm.restrictScalars R).toAlgHom).comp
    ((IsScalarTower.toAlgHom R S (ResidueField S)).comp (IsScalarTower.toAlgHom R A S))
  obtain ⟨s, hs⟩ := (_root_.GlobalTheory.EtaleHensel.bijective_residue_comp R A R).2 φ
  refine ⟨s, ?_⟩
  ext x
  have hx := congrArg (fun ψ : A →ₐ[R] ResidueField R => ψ x) hs
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hx
  rw [Ideal.mem_comap, ← residue_eq_zero_iff, ← ResidueField.algebraMap_eq]
  change algebraMap R (ResidueField R) (s x) = 0 ↔ x ∈ q
  rw [hx]
  simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe,
    IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq]
  change e.symm (residue S (algebraMap A S x)) = 0 ↔ x ∈ q
  rw [map_eq_zero_iff _ e.symm.injective, residue_eq_zero_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff S q]

end GlobalTheory.StrictHensel

namespace GlobalTheory.StrictHensel

theorem strictlyHenselian_iff : ∀ (R : Type) [CommRing R] [IsLocalRing R],
    (∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime],
      q.comap (algebraMap R A) = maximalIdeal R →
        ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) ↔
      (HenselianLocalRing R ∧ IsSepClosed (ResidueField R)) := by
  intro R _ _
  refine ⟨fun H => ⟨henselian_of_sections H, isSepClosed_of_sections H⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  intro A _ _ _ q _ hq
  exact sections_of_henselian_sepClosed A q hq

end GlobalTheory.StrictHensel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar lamF upIdele)

namespace GlobalTheory.ToricTransport

def coordIn (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) : ℂ :=
  (C0 E d (2 * s) κ : ℂ) * T / Ω ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i)

def IsDatum {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I] (ι : K →+* ℂ)
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  UnramFin E ∧ IsCMType φ ∧ (∀ i, (φ i).comp (algebraMap K E) = ι) ∧ 1 ≤ s ∧ (∀ i, 1 ≤ κ i) ∧ IsBaseCond 𝔣 ∧ IsFinSetSplitPlacesCoprimeConductor 𝔣 Q ∧
    IsValChar φ s κ 𝔣 ∅ χ

def TwistedTransport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ),
    Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧
      (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
        (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
        ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T → IsAlgebraic ℚ (coordIn E d s κ Ω₀ T)) ∧
      ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ) (art : Ideles K →* Gab K Ω),
        j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
        ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ), (∀ x, j (σ x) = g (j x)) → IsSymbol art t σ →
        ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧
          ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
            (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
            ∀ (κ' : I → ℕ) (χ' : HChar E), IsConjWt φ g κ κ' → IsConjChar φ s κ' g χ χ' →
            ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T T' : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T →
              IsTwistedSum φ s κ' (condQ 𝔣 Q) χ' (conjChar g ψ) T' →
              g (coordIn E d s κ Ω₀ T) =
                coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ *
                  (lamF s χ' (upIdele K E t) * ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ))⁻¹ * T')

theorem coordIn_div (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d) (hs : 1 ≤ s) (κ : I → ℕ)
    {Ω : ℂ} (hΩ : Ω ≠ 0) (T T₀ : ℂ) : coordIn E d s κ Ω T / coordIn E d s κ Ω T₀ = T / T₀ := by
  have hC : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  rw [coordIn, coordIn, div_div_div_cancel_right₀ (pow_ne_zero _ hΩ), mul_div_mul_left _ _ hC]

end GlobalTheory.ToricTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceEndomorphismPreservesTorusWei
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.CoefTorusWeight

theorem coeff_aeval_scale {K σ : Type} [Field K] [Fintype σ] (c : σ → K) (F : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun v => (C (c v) * X v : MvPolynomial σ K)) F) m = (∏ v, c v ^ m v) * AddMonoidAlgebra.coeff F m := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : aeval (fun v => (C (c v) * X v : MvPolynomial σ K)) (monomial u a)
        = monomial u ((∏ v, c v ^ u v) * a) := by
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), monomial_eq,
        Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, algebraMap_eq, C_mul]
      ring
    rw [h, coeff_monomial, coeff_monomial]
    split_ifs with hu
    · rw [hu]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem coeff_actP_diag {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (t : ι → Fin n → Kˣ) (F : Pol K ι n) (m : (ι × Fin n × Fin n) →₀ ℕ) :
    AddMonoidAlgebra.coeff (actP lam (fun τ => diagGL K n (t τ)) F) m
      = detTwK lam (fun τ => diagGL K n (t τ)) *
        ((∏ v : ι × Fin n × Fin n, (t v.1 v.2.1 : K) ^ m v) * AddMonoidAlgebra.coeff F m) := by
  classical
  have h : trAct (fun τ => diagGL K n (t τ))
      = aeval (fun v : ι × Fin n × Fin n => (C (t v.1 v.2.1 : K) * X v : Pol K ι n)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, diagGL, Matrix.diagonal_transpose]
    rw [Finset.sum_eq_single v.2.1]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · simp
  rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, coeff_smul, smul_eq_mul, h,
    coeff_aeval_scale]

theorem detTwK_ne_zero {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) : detTwK lam h ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Units.ne_zero _

theorem weight_preserved (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (g : Module.End K (VV K lam))
    (hg : ∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) (v : VV K lam)
    (hv : ∀ m ∈ (v : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) :
    ∀ m ∈ ((g v : VV K lam) : Pol K ι n).support, ∀ τ a,
      ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a := by
  classical
  intro m hm τ0 a0
  let u : Kˣ := Units.mk0 (2 : K) two_ne_zero
  let t : ι → Fin n → Kˣ := fun τ a => if τ = τ0 ∧ a = a0 then u else 1
  have hprod : ∀ m : (ι × Fin n × Fin n) →₀ ℕ,
      (∏ v : ι × Fin n × Fin n, (t v.1 v.2.1 : K) ^ m v) = 2 ^ (∑ s : Fin n, m (τ0, a0, s)) := by
    intro m
    rw [Fintype.prod_prod_type, Finset.prod_eq_single τ0, Fintype.prod_prod_type,
      Finset.prod_eq_single a0, ← Finset.prod_pow_eq_pow_sum]
    · simp [t, u]
    · intro b _ hb
      simp [t, hb]
    · simp
    · intro b _ hb
      simp [t, hb]
    · simp
  set h : ι → GL (Fin n) K := fun τ => diagGL K n (t τ) with hh
  have hco : ∀ (w : VV K lam) (m : (ι × Fin n × Fin n) →₀ ℕ),
      AddMonoidAlgebra.coeff ((rhoK lam h w : VV K lam) : Pol K ι n) m
        = detTwK lam h * (2 ^ (∑ s : Fin n, m (τ0, a0, s)) * AddMonoidAlgebra.coeff (w : Pol K ι n) m) := by
    intro w m
    rw [← hprod]
    exact coeff_actP_diag lam t w m
  have h1 : rhoK lam h v = (detTwK lam h * 2 ^ (lam τ0).natW a0) • v := by
    apply Subtype.ext
    ext m'
    rw [hco, Submodule.coe_smul, coeff_smul, smul_eq_mul, mul_assoc]
    by_cases hm' : m' ∈ (v : Pol K ι n).support
    · rw [hv m' hm']
    · rw [notMem_support_iff.mp hm']
      simp
  have h2 := hg h v
  rw [h1, map_smul] at h2
  have h3 := congrArg (fun w : VV K lam => AddMonoidAlgebra.coeff (w : Pol K ι n) m) h2
  simp only [hco, Submodule.coe_smul, coeff_smul, smul_eq_mul, mul_assoc] at h3
  have h4 := mul_right_cancel₀ (mem_support_iff.mp hm) (mul_left_cancel₀ (detTwK_ne_zero lam h) h3)
  have h5 : (2 : ℕ) ^ (lam τ0).natW a0 = 2 ^ (∑ s : Fin n, m (τ0, a0, s)) := by
    exact_mod_cast h4
  exact (Nat.pow_right_injective le_rfl h5).symm

end GlobalTheory.CoefTorusWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceLeSpanPureTensors
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem multilinear_mem_span_of_mem_span {K ι M N : Type} [Field K] [Fintype ι]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (m : (ι → M) →ₘₗ[K] N) (S : ι → Set M) (f : ι → M)
    (hf : ∀ τ, f τ ∈ Submodule.span K (S τ)) :
    m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
  classical
  have key : ∀ (s : Finset ι) (f : ι → M), (∀ τ, f τ ∈ Submodule.span K (S τ)) →
      (∀ τ, τ ∉ s → f τ ∈ S τ) →
      m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f _ h
      exact Submodule.subset_span ⟨f, fun τ => h τ (Finset.notMem_empty τ), rfl⟩
    | insert a s ha ih =>
      intro f h1 h2
      have hle : Submodule.span K (S a) ≤
          (Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g}).comap
            (m.toLinearMap f a) := by
        rw [Submodule.span_le]
        intro x hx
        rw [SetLike.mem_coe, Submodule.mem_comap, MultilinearMap.toLinearMap_apply]
        apply ih
        · intro τ
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact Submodule.subset_span hx
          · rw [Function.update_of_ne hτ]
            exact h1 τ
        · intro τ hτs
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact hx
          · rw [Function.update_of_ne hτ]
            exact h2 τ (by simp [hτ, hτs])
      have h := hle (h1 a)
      rw [Submodule.mem_comap, MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h
      exact h
  exact key Finset.univ f hf (fun τ h => absurd (Finset.mem_univ τ) h)

theorem coefSpace_le_span_pure_tensors (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K))
    (hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) :
    VV K lam ≤ Submodule.span K
      {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  classical
  let m : (ι → MvPolynomial (Fin n × Fin n) K) →ₘₗ[K]
      (MvPolynomial (ι × Fin n × Fin n) K) :=
    (MultilinearMap.mkPiAlgebra K ι (MvPolynomial (ι × Fin n × Fin n) K)).compLinearMap
      (fun τ => (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap)
  have hm : ∀ f, m f = ten f := fun f => rfl
  unfold VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro P ⟨F, hF, rfl⟩
  exact multilinear_mem_span_of_mem_span m S F (fun τ => hS τ (hF τ))

end GlobalTheory
end
end

