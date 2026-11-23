module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartMultihomogOrderAtPoint
section
noncomputable section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono

theorem exists_unit_mul_monomial_of_primes {m e : ℕ} (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hI : ∀ h ∈ I, eval t h = 0) [hreg : IsRegularLocalRing (locRing I t)]
    (hdim : ringKrullDim (locRing I t) = e) (r : Fin e → MvPolynomial (Fin m) ℂ) (J : Finset (Fin e))
    (hspan : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t))
    (hpr : ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t →
      (Dc ≤ 𝔮 ↔ ∃ i ∈ J, r i ∈ 𝔮))
    (g : MvPolynomial (Fin m) ℂ)
    (hg : ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → g ∈ 𝔮 → Dc ≤ 𝔮) :
    ∃ (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ J → mm i = 0) ∧
      algebraMap _ (locRing I t) g = u * ∏ i ∈ J, algebraMap _ (locRing I t) (r i) ^ mm i := by
  classical
  have hdom : IsDomain (locRing I t) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hKt : I ≤ ptIdeal t := fun h hh => RingHom.mem_ker.mpr (hI h hh)
  have hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      IsLocalRing.maximalIdeal (locRing I t) := by
    rw [hspan, maximalIdeal_locRing hKt]
  have hdim' : (e : WithBot ℕ∞) = ringKrullDim (locRing I t) := hdim.symm
  have hprime : ∀ i, Prime (algebraMap _ (locRing I t) (r i)) :=
    prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim'

  have hcontr : ∀ 𝔓 : Ideal (locRing I t), 𝔓.IsPrime →
      (𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t))).IsPrime ∧
      I ≤ 𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) ∧
      𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) ≤ ptIdeal t := by
    intro 𝔓 h𝔓
    refine ⟨Ideal.comap_isPrime _ _, ?_, ?_⟩
    · intro h hh
      rw [Ideal.mem_comap]
      have : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) h = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hh)
      rw [this]
      exact 𝔓.zero_mem
    · intro h hh
      rw [Ideal.mem_comap] at hh
      by_contra hne
      have hne' : eval t h ≠ 0 := fun h0 => hne (RingHom.mem_ker.mpr h0)
      have hu := (IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI h).mpr hne'
      exact h𝔓.ne_top (Ideal.eq_top_of_isUnit_mem _ hh hu)
  have hg0 : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) g ≠ 0 := by
    intro h0
    obtain ⟨h1, h2, h3⟩ := hcontr ⊥ Ideal.isPrime_bot
    have hgm : g ∈ (⊥ : Ideal (locRing I t)).comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) := by
      rw [Ideal.mem_comap, h0]; exact Ideal.zero_mem _
    obtain ⟨i, -, hi⟩ := (hpr _ h1 h2 h3).1 (hg _ h1 h2 h3 hgm)
    rw [Ideal.mem_comap, Ideal.mem_bot] at hi
    exact (hprime i).ne_zero hi
  have hrad : (∏ i ∈ J, algebraMap _ (locRing I t) (r i)) ∈
      (Ideal.span {algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) g}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro 𝔓 ⟨hle, h𝔓⟩
    obtain ⟨h1, h2, h3⟩ := hcontr 𝔓 h𝔓
    have hgm : g ∈ 𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) := by
      rw [Ideal.mem_comap]; exact hle (Ideal.mem_span_singleton_self _)
    obtain ⟨i, hiJ, hi⟩ := (hpr _ h1 h2 h3).1 (hg _ h1 h2 h3 hgm)
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hiJ) hi
  exact eq_unit_mul_monomial (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim' J hg0 hrad

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ideal_sup_le_of_mem (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (hP : IsMultiHomogIdeal P) (f : MvPolynomial (Σ k, ι k) ℂ)
    (hf : ∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D)
    (𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) (h𝔮 : 𝔮.IsPrime)
    (hI : SncRes.ideal P p ≤ 𝔮) (hg : bind₁ (SncRes.lift p) f ∈ 𝔮) :
    SncRes.ideal (P ⊔ D) p ≤ 𝔮 := by
  classical
  intro h hh
  have hvan : h ∈ vanishingIdeal ℂ (zeroLocus ℂ 𝔮) := by
    rw [mem_vanishingIdeal_iff]
    intro w hw
    have hw0 : ∀ c ∈ 𝔮, eval w c = 0 := fun c hc => by simpa using hw c hc
    let w' : (Σ k, ι k) → ℂ := w ∘ Fintype.equivFin (Σ k, ι k)
    have hpt : renPt w' = w := by
      funext j
      simp [renPt, w']
    have hren : ∀ x, eval w (renC (Σ k, ι k) x) = eval w' x := fun x => by
      rw [← eval_renC w' x, hpt]
    have hchart : ∀ c ∈ chartIdeal P p, eval w' c = 0 := fun c hc => by
      rw [← hren]
      have hs : (renR (Σ k, ι k)).symm (renC (Σ k, ι k) c) = c := (renR (Σ k, ι k)).symm_apply_apply c
      have hm : renC (Σ k, ι k) c ∈ SncRes.ideal P p := by
        unfold SncRes.ideal
        rw [mem_map_renR_iff, hs]
        exact hc
      exact hw0 _ (hI hm)
    obtain ⟨hcone, h1, -⟩ := conePts_of_chartIdeal hP p w' hchart
    have hlift : (fun q => eval w (SncRes.lift p q)) = w' := by
      funext q
      unfold SncRes.lift
      split_ifs with hq
      · obtain ⟨k, i⟩ := q
        simp only at hq
        subst hq
        simp [h1 k]
      · simp [w']
    have hfz : eval w' f = 0 := by
      have h2 : eval w (bind₁ (SncRes.lift p) f) = eval (fun q => eval w (SncRes.lift p q)) f :=
        eval₂Hom_bind₁ _ _ _ _
      rw [← hlift, ← h2]
      exact hw0 _ hg
    have hD := hf w' hcone hfz
    have hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval w') := by
      refine sup_le (sup_le (fun c hc => RingHom.mem_ker.mpr (hcone.2 c hc))
        (fun c hc => RingHom.mem_ker.mpr (hD.2 c hc))) ?_
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show eval w' _ = 0
      simp [h1 k]
    have h3 : eval w' ((renR (Σ k, ι k)).symm h) = 0 :=
      RingHom.mem_ker.mp (hle ((mem_map_renR_iff _ h).1 hh))
    have e1 : renC (Σ k, ι k) ((renR (Σ k, ι k)).symm h) = h := (renR (Σ k, ι k)).apply_symm_apply h
    show eval w h = 0
    rw [← e1, hren, h3]
  rwa [vanishingIdeal_zeroLocus_eq_radical, h𝔮.radical] at hvan

theorem exists_unit_mul_monomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → IsMultiHomog f a → (∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D) → ∃ (u : (locRing (SncRes.ideal P p) (renPt (affCoord p z)))ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ Jf → mm i = 0) ∧ algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (bind₁ (SncRes.lift p) f) = u * ∏ i ∈ Jf, algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r i) ^ mm i := by
  intro K _ ι _ P D e p z r Jf f a hP _ _ _ hI hreg hdim hspan hpr _ hf
  exact exists_unit_mul_monomial_of_primes (SncRes.ideal P p) (SncRes.ideal (P ⊔ D) p) _ hI hdim r Jf
    hspan hpr _ fun 𝔮 h𝔮 hle _ hg => ideal_sup_le_of_mem P D p hP f hf 𝔮 h𝔮 hle hg

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionTransitionPolynomial
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

theorem coord_image (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0} := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact renPt_zero (chartIdeal P p) (affCoord p (rep x))
      ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))
  · intro ht
    obtain ⟨w, hwd⟩ : ∃ w, w = t ∘ Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
    have hren : renPt w = t := by
      subst hwd
      funext l
      simp [renPt]
    have hw : ∀ h ∈ chartIdeal P p, eval w h = 0 := by
      intro h hh
      rw [← eval_renC w h, hren]
      exact ht _ (Ideal.mem_map_of_mem _ hh)
    obtain ⟨hc, h1, ha⟩ := conePts_of_chartIdeal hP p w hw
    let x : Pts P := ⟨proj w, w, hc, rfl⟩
    have ho : SameOrbit (rep x) w := sameOrbit_of_proj_eq (rep_mem x).1 hc.1 (proj_rep x)
    refine ⟨x, fun k => ?_, ?_⟩
    · obtain ⟨c, hcn, hcz⟩ := ho
      have hk : rep x ⟨k, p k⟩ = c k * w ⟨k, p k⟩ := congrFun hcz ⟨k, p k⟩
      rw [hk, h1 k, mul_one]
      exact hcn k
    · show renPt (affCoord p (rep x)) = t
      rw [affCoord_eq_of_sameOrbit p ho, ha, hren]

theorem coord_trans (p p' : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p ∩ src P p') :
    ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
      (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
      eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
        ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, e = Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
  have hev : ∀ (y : Pts P) (q : Σ k, ι k), eval (coord P p y) (X (e q)) = affCoord p (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  have hev' : ∀ (y : Pts P) (q : Σ k, ι k), coord P p' y (e q) = affCoord p' (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  refine ⟨∏ k, X (e ⟨k, p' k⟩),
    fun l => X l * ∏ k ∈ Finset.univ.erase (e.symm l).1, X (e ⟨k, p' k⟩), ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [hev]
    exact div_ne_zero (hx.2 k) (hx.1 k)
  · intro y hy _ l
    obtain ⟨r, rfl⟩ := e.surjective l
    have hprod := Finset.mul_prod_erase Finset.univ
      (fun k => affCoord p (rep y) ⟨k, p' k⟩) (Finset.mem_univ r.1)
    have hA : affCoord p' (rep y) r * affCoord p (rep y) ⟨r.1, p' r.1⟩ = affCoord p (rep y) r := by
      have h1 := hy.1 r.1
      have h2 := hy.2 r.1
      simp only [affCoord]
      field_simp
    simp only [map_prod, map_mul, hev, hev', Equiv.symm_apply_apply]
    rw [← hprod, ← mul_assoc, hA]

theorem chart_image_and_trans (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    (∀ p : (k : K) → ι k, coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0}) ∧
    ∀ p p' : (k : K) → ι k, ∀ x ∈ src P p ∩ src P p',
      ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
        (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
        eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
          ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) :=
  ⟨coord_image hP, fun p p' x hx => coord_trans p p' x hx⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SpanEqTopOfForallDotEqZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt IsLocalRing

variable {m : ℕ}

theorem span_eq_top_of_forall_dot_eq_zero (S : Set (Fin m → ℂ))
    (hS : ∀ v : Fin m → ℂ, (∀ w ∈ S, ∑ j, v j * w j = 0) → v = 0) :
    Submodule.span ℂ S = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hv : (fun j => f (fun k => if j = k then (1 : ℂ) else 0)) = 0 := by
    apply hS
    intro w hw
    have h1 : f w = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hw))
    rw [LinearMap.pi_apply_eq_sum_univ f w] at h1
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, mul_comm]
  apply hf0
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ f x, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := congrFun hv j
  simp only [Pi.zero_apply] at this
  rw [this, smul_zero]

theorem lin_mem_of_eval_eq_zero (t : Fin m → ℂ) (J : Ideal (MvPolynomial (Fin m) ℂ))
    (hJ : ptI t ^ 2 ≤ J) {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ J) (h0 : eval t a = 0) :
    ∑ i, C (gradP t a i) * (X i - C (t i)) ∈ J := by
  have h := hJ (ReciprocityTheory.AnForm.R.JacobianCriterionAlt.taylor t a)
  rw [h0, map_zero, sub_zero] at h
  have h2 := J.sub_mem ha h
  rwa [sub_sub_cancel] at h2

theorem ptI_le_of_span_grad_eq_top (t : Fin m → ℂ) (J : Ideal (MvPolynomial (Fin m) ℂ))
    (hJ : ptI t ^ 2 ≤ J) (A : Set (MvPolynomial (Fin m) ℂ)) (hAJ : A ⊆ J)
    (hA0 : ∀ a ∈ A, eval t a = 0) (hA : Submodule.span ℂ (gradP t '' A) = ⊤) :
    ptI t ≤ J := by
  let φ : (Fin m → ℂ) →ₗ[ℂ] MvPolynomial (Fin m) ℂ :=
    { toFun := fun v => ∑ i, C (v i) * (X i - C (t i))
      map_add' := fun v w => by
        simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum,
          MvPolynomial.smul_eq_C_mul, mul_assoc] }
  have hφ : ∀ v, φ v = ∑ i, C (v i) * (X i - C (t i)) := fun v => rfl
  have hspan : Submodule.span ℂ (gradP t '' A) ≤ Submodule.comap φ (J.restrictScalars ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, haA, rfl⟩
    show φ (gradP t a) ∈ J
    rw [hφ]
    exact lin_mem_of_eval_eq_zero t J hJ (hAJ haA) (hA0 a haA)
  have key : ∀ i, X i - C (t i) ∈ J := by
    intro i
    have hmem : (Pi.single i 1 : Fin m → ℂ) ∈ Submodule.comap φ (J.restrictScalars ℂ) :=
      hspan (by rw [hA]; exact Submodule.mem_top)
    have h2 : φ (Pi.single i 1) ∈ J := hmem
    rw [hφ, Finset.sum_eq_single i] at h2
    · simpa using h2
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ptIdeal_eq_span, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact key i

private theorem gradP_eq_eval_pderiv (t : Fin m → ℂ) (a : MvPolynomial (Fin m) ℂ) (j : Fin m) :
    gradP t a j = eval t (pderiv j a) := by
  induction a using MvPolynomial.induction_on
  next c =>
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, pderiv_C, map_zero, Pi.zero_apply]
  next p q hp hq =>
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, Pi.add_apply, hp, hq, map_add (f := _), map_add (f := _)]
  next p i hp =>
    have hX : gradP t (X i) = Pi.single i 1 := by
      have h2 : (X i : MvPolynomial (Fin m) ℂ) = (X i - C (t i)) + C (t i) := by ring
      rw [h2, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_lin,
        ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, add_zero]
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_mul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, hp, hX, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul,
      map_mul, eval_X]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]

theorem span_algebraMap_eq_map_ptIdeal (e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (r : Fin e → MvPolynomial (Fin m) ℂ) (hI : ∀ h ∈ I, eval t h = 0) (hr : ∀ l, eval t (r l) = 0)
    (hv : ∀ v : Fin m → ℂ, (∀ h ∈ I, ∑ j, v j * eval t (pderiv j h) = 0) →
      (∀ l, ∑ j, v j * eval t (pderiv j (r l)) = 0) → v = 0) :
    Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) := by
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian I t hI
  have hpt : ptI t = ptIdeal t := by
    ext a
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]
    unfold ptIdeal
    rw [RingHom.mem_ker]
  have hmemPt : ∀ a, eval t a = 0 → a ∈ ptIdeal t := fun a ha => by
    rw [← hpt, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]
    exact ha
  have hφ : ∀ a, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a =
      Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)
        (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t) a) := fun a => rfl
  have hI0 : ∀ a ∈ I, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a = 0 := by
    intro a ha
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  set N : Ideal (locRing I t) := Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l))
    with hN
  set M : Ideal (locRing I t) := Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) with hM
  have hNM : N ≤ M := by
    rw [hN, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact Ideal.mem_map_of_mem _ (hmemPt _ (hr l))
  have key : ptI t ≤ Ideal.comap (algebraMap _ (locRing I t)) (N ⊔ M ^ 2) := by
    refine ptI_le_of_span_grad_eq_top t _ ?_ ((I : Set (MvPolynomial (Fin m) ℂ)) ∪ Set.range r)
      ?_ ?_ ?_
    · intro a ha
      rw [Ideal.mem_comap]
      apply Ideal.mem_sup_right
      rw [hM, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (by rw [← hpt]; exact ha)
    · rintro a (ha | ⟨l, rfl⟩)
      · rw [SetLike.mem_coe, Ideal.mem_comap, hI0 a ha]
        exact Submodule.zero_mem _
      · rw [SetLike.mem_coe, Ideal.mem_comap]
        exact Ideal.mem_sup_left (Ideal.subset_span ⟨l, rfl⟩)
    · rintro a (ha | ⟨l, rfl⟩)
      · exact hI a ha
      · exact hr l
    · apply span_eq_top_of_forall_dot_eq_zero
      intro v hvS
      apply hv v
      · intro h hh
        have h3 := hvS _ ⟨h, Or.inl hh, rfl⟩
        simpa only [gradP_eq_eval_pderiv] using h3
      · intro l
        have h3 := hvS _ ⟨r l, Or.inr ⟨l, rfl⟩, rfl⟩
        simpa only [gradP_eq_eval_pderiv] using h3
  have hMle : M ≤ N ⊔ M ^ 2 := Ideal.map_le_iff_le_comap.mpr (hpt.symm.le.trans key)
  haveI := hloc
  haveI := hnoeth
  have hMtop : M ≠ ⊤ := by
    haveI : (ptIdeal t).IsPrime := ptIdeal_isPrime t
    intro htop
    have hmax : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t) =
        IsLocalRing.maximalIdeal (Localization.AtPrime (ptIdeal t)) :=
      Localization.AtPrime.map_eq_maximalIdeal
    have hMeq : M = Ideal.map
        (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I))
        (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t)) := by
      rw [hM, Ideal.map_map]
      exact congrArg (fun f => Ideal.map f (ptIdeal t)) (RingHom.ext fun a => rfl)
    have hc := Ideal.comap_map_of_surjective
      (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I))
      Ideal.Quotient.mk_surjective (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t))
    rw [← hMeq, htop, Ideal.comap_top] at hc
    have hb : Ideal.comap
        (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)) ⊥ ≤
        Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
      exact Ideal.map_mono (fun a ha => hmemPt a (hI a ha)) hx
    rw [sup_eq_left.mpr hb, hmax] at hc
    exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime (ptIdeal t))).ne_top hc.symm
  have hMj : M ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hMtop
  have hle : M ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian M) hMj ?_
    rw [Ideal.smul_eq_mul, ← pow_two]
    exact hMle
  exact le_antisymm hNM hle

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

