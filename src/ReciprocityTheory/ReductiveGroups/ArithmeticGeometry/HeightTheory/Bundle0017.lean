module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0014
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SacSuccAbove

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.EvTEqBlockPointOfMh
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem evT_eq_blockPoint_of_mh (sg : K →+* ℂ) (q : KTp K d.D d.N) (hq : q ≠ 0) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    ∃ g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ, g ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun i : Fin d.D => m i.succ) g ∧
      ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
  classical
  set φ : Fin d.D × Fin (d.N + 1) → TVar d.D d.N := fun p => (p.1.succ, p.2) with hφ
  have hφi : Function.Injective φ := fun p p' h => by
    simp only [hφ, Prod.mk.injEq] at h
    exact Prod.ext (Fin.succ_injective _ h.1) h.2
  have hvars : (q.vars : Set (TVar d.D d.N)) ⊆ Set.range φ := by
    intro v hv
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hv
    obtain ⟨s, hs, hsv⟩ := hv
    have h0 : v.1 ≠ 0 := by
      intro h0
      have h1 := hqm s hs 0
      rw [hm] at h1
      have hz := (Finset.sum_eq_zero_iff.1 h1) v.2 (Finset.mem_univ _)
      apply (Finsupp.mem_support_iff.1 hsv)
      have e : v = (0, v.2) := Prod.ext h0 rfl
      rw [e]; exact hz
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq.2 h0
    exact ⟨(i, v.2), Prod.ext hi rfl⟩
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q φ hφi hvars
  set g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ := MvPolynomial.map sg q' with hgdef
  have heval : ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
    intro z
    rw [← hq', evT, MvPolynomial.eval₂_rename, hgdef, MvPolynomial.eval_map]
    congr 1
  have hq'0 : q' ≠ 0 := by
    rintro rfl
    exact hq (by rw [← hq', map_zero])
  have hg0 : g ≠ 0 := by
    intro h0
    apply hq'0
    apply MvPolynomial.map_injective sg sg.injective
    rw [← hgdef, h0, map_zero]
  have hgm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun i : Fin d.D => m i.succ) g := by
    intro s hs b
    have hs' : s ∈ q'.support := MvPolynomial.support_map_subset _ _ hs
    have hsq : Finsupp.mapDomain φ s ∈ q.support := by
      rw [← hq', MvPolynomial.support_rename_of_injective hφi]
      exact Finset.mem_image_of_mem _ hs'
    show _ = m b.succ
    rw [← hqm _ hsq b.succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finsupp.mapDomain_apply_of_injective hφi s (b, j)).symm
  exact ⟨g, hg0, hgm, heval⟩

theorem logInt_evT_of_mh (sg : K →+* ℂ) (q : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    MeasureTheory.Integrable (fun z => Real.log ‖d.evT sg 0 (d.tOf z) q‖)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  by_cases hq : q = 0
  · subst hq
    simp [evT]
  · obtain ⟨g, hg, hgm, heq⟩ := d.evT_eq_blockPoint_of_mh sg q hq m hm hqm
    simp_rw [heq]
    exact ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable d.D (d.N + 1) _ g hg hgm

theorem integrable_log_norm_sub_log_norm (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    MeasureTheory.Integrable (fun z => Real.log ‖d.evT sg 0 (d.tOf z) a‖ -
      Real.log ‖d.evT sg 0 (d.tOf z) b‖) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  obtain ⟨-, -, m, hm0, hma, hmb⟩ := hab
  exact (d.logInt_evT_of_mh sg a m hm0 hma).sub (d.logInt_evT_of_mh sg b m hm0 hmb)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.EvalOneBilinearSubstitution
section
namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution

open MvPolynomial

variable {K : Type} [Field K] {D N : ℕ}

abbrev V (D N : ℕ) : Type := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)

noncomputable def ev1 : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => if v = Sum.inr 0 then 1 else X v

noncomputable def thetaS (sgn : K) : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => match v with
    | Sum.inl (a, j) => if a = 0 then X (Sum.inl (a, j))
        else X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j))
    | Sum.inr i => X (Sum.inr i)

private theorem thetaS_X_inr (sgn : K) (i : Fin (D + 2)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inr i)) = X (Sum.inr i) := by
  simp [thetaS]

private theorem thetaS_X_inl_zero (sgn : K) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (0, j))) = X (Sum.inl (0, j)) := by
  simp [thetaS]

private theorem thetaS_X_inl_of_ne_zero (sgn : K) {a : Fin (D + 2)} (ha : a ≠ 0) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (a, j))) =
      X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j)) := by
  simp [thetaS, ha]

theorem thetaS_comp (s t : K) (hst : s + t = 0) :
    (thetaS (D := D) (N := N) s).comp (thetaS t) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro (⟨a, j⟩ | i)
  · by_cases ha : a = 0
    · subst ha
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_zero]
    · have hC : (C s + C t : MvPolynomial (V D N) K) = 0 := by
        rw [← C_add, hst, C_0]
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_of_ne_zero _ ha, map_add (f := _), map_mul,
        thetaS_X_inr, thetaS_X_inl_zero, algHom_C, algebraMap_eq]
      linear_combination
        (X (Sum.inr a) * X (Sum.inl (0, j)) : MvPolynomial (V D N) K) * hC
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inr]

noncomputable def theta : MvPolynomial (V D N) K ≃ₐ[K] MvPolynomial (V D N) K :=
  AlgEquiv.ofAlgHom (thetaS (-1)) (thetaS 1) (thetaS_comp _ _ (by ring)) (thetaS_comp _ _ (by ring))

def iota (p : TVar D N) : V D N := Sum.inl (p.1.succ, p.2)

theorem iota_injective : Function.Injective (iota (D := D) (N := N)) := by
  rintro ⟨a, j⟩ ⟨b, k⟩ h
  simp only [iota, Sum.inl.injEq, Prod.mk.injEq, Fin.succ_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

private theorem ev1_X_inr_zero :
    ev1 (K := K) (D := D) (N := N) (X (Sum.inr 0)) = 1 := by
  simp [ev1]

private theorem ev1_X_of_ne_inr_zero {v : V D N} (hv : v ≠ Sum.inr 0) :
    ev1 (K := K) (X v) = X v := by
  simp [ev1, hv]

theorem evalOne_bilinearSubstitution (F : KTp K D N) : ev1 (bilinearSubstitution F) = theta (rename iota F) := by
  have key : (ev1 (K := K) (D := D) (N := N)).comp
      (aeval fun t : ReciprocityTheory.ChartRestriction.G.T0.TVar D N =>
        (X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2)) :
          MvPolynomial (V D N) K)) =
      (thetaS (-1)).comp (rename iota) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, j⟩
    have h1 : (Sum.inl (a.succ, j) : V D N) ≠ Sum.inr 0 := Sum.inl_ne_inr
    have h2 : (Sum.inr a.succ : V D N) ≠ Sum.inr 0 :=
      fun h => Fin.succ_ne_zero a (Sum.inr_injective h)
    have h3 : (Sum.inl (0, j) : V D N) ≠ Sum.inr 0 := Sum.inl_ne_inr
    simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, ev1_X_inr_zero, ev1_X_of_ne_inr_zero h1,
      ev1_X_of_ne_inr_zero h2, ev1_X_of_ne_inr_zero h3, rename_X, iota,
      thetaS_X_inl_of_ne_zero _ (Fin.succ_ne_zero a), map_neg, map_one]
    ring
  exact DFunLike.congr_fun key F

private theorem irreducible_rename_of_injective_height {α β : Type} [Fintype α] {f : α → β}
    (hf : Function.Injective f) {F : MvPolynomial α K} (hF : Irreducible F) :
    Irreducible (rename f F) := by
  have hP : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF
  have h1 : rename f F = rename ((↑) : Set.range f → β) (renameEquiv K (Equiv.ofInjective f hf) F) := by
    rw [renameEquiv_apply, rename_rename]
    congr 1
  have h2 : Prime (renameEquiv K (Equiv.ofInjective f hf) F) := (MulEquiv.prime_iff _).mpr hP
  rw [h1]
  exact ((prime_rename_iff (Set.range f)).mpr h2).irreducible

theorem irreducible_theta_rename (F : KTp K D N) (hF : Irreducible F) :
    Irreducible (theta (rename (iota (D := D) (N := N)) F)) :=
  (MulEquiv.irreducible_iff (theta (K := K) (D := D) (N := N))).mpr
    (irreducible_rename_of_injective_height iota_injective hF)

end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPtsB
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial MeasureTheory

theorem countable_numberField (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem ST_scale (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ) (y : Fin (d.N + 1 + d.D) → ℂ)
    (hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0) :
    d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t := by
  ext P
  simp only [ST, Set.mem_setOf_eq, NPB.gpt, Fin.cases_succ]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_eq_zero]
  simp [hy i]

theorem gpt_one (t : Fin d.D → Fin (d.N + 1) → ℂ) (t0 : Fin (d.N + 1) → ℂ) :
    NPB.gpt (fun q => t q.1 q.2) (Fin.addCases t0 (fun _ => (1 : ℂ))) =
      fun v : TVar d.D d.N => Fin.cases (motive := fun _ => ℂ) (t0 v.2) (fun i => t i v.2) v.1 := by
  funext v
  rcases v with ⟨a, j⟩
  refine Fin.cases ?_ (fun i => ?_) a <;> simp [NPB.gpt]

theorem fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    (d.ST c sg t).Finite ∧ (d.ST c sg t).ncard = d.delc c ∧
      (∀ g : Ω c, tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g))
        = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g) ∧
      tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) =
        ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
          ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
  letI iA : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI iB : Algebra (KTf K d.D d.N) ℂ := (tauPev sg _ hpt).toAlgebra
  obtain ⟨hfd, hrank⟩ := d.omS_finite hd h c
  haveI := hfd
  haveI : CharZero (KTf K d.D d.N) := inferInstance
  haveI : Algebra.IsIntegral (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsSeparable.of_integral _ _
  have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := by
    intro i h0
    apply hpt (MvPolynomial.X (i.succ, 0)) (MvPolynomial.X_ne_zero _)
    simp [NPB.gpt, h0]
  have hST : d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t :=
    d.ST_scale c sg t y hy
  obtain ⟨hinj, hrange⟩ := d.fibre_core (hd := hd) (h := h) (c := c) (sg := sg)
    (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt)
  rw [hST] at hrange
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hrange]
    exact Set.finite_range _
  · rw [← hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, AlgHom.card, hrank]
  · intro g
    have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ
      (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    exact h1
  · have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ (d.rationalBaseRow c)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    refine h1.trans (Finset.prod_congr rfl fun σ _ => ?_)
    have hσ : (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (d.KTtoS h c) = tauPev sg _ hpt :=
      RingHom.ext fun x => σ.commutes x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rationalBaseRow, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have he := d.emb_sH (h := h) (c := c) (sg := sg)
      (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt) (σ : OmS (Ω c) d.D d.N →+* ℂ) hσ
      (MvPolynomial.X (0, j))
    simp only [AlgHom.coe_toRingHom] at he
    rw [he]
    simp [NPB.gpt]

theorem norm_at_sg_B (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c ∧
      (∀ (g : Ω c) (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), g ≠ 0 → b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ∧
      (∀ (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          ∑ j, t0 j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have := countable_numberField K
  filter_upwards [NPB.ae_gen (K := K) (D := d.D) (N := d.N) sg] with z hz
  have hG : ∀ (a : Fin d.D → ℕ) (p : MvPolynomial (Fin d.D × Fin (d.N + 1)) K),
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a p → p ≠ 0 →
        eval₂ sg (fun q => d.tOf z q.1 q.2) p ≠ 0 := hz
  obtain ⟨y1, -, hpt1⟩ := NPB.exists_gen sg (fun q => d.tOf z q.1 q.2) hG 1 one_ne_zero
  obtain ⟨hfin, hcard, -, -⟩ := d.fib hd h c sg (d.tOf z) y1 hpt1
  refine ⟨hfin, hcard, ?_, ?_⟩
  · intro g a b t0 _ _ hab hbt
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a -
        C (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) *
          NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, hn, -⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn g, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    rw [div_eq_iff hbt]
    exact h2
  · intro a b t0 _ hab hbt
    let cX : MvPolynomial (Fin (d.N + 1 + d.D)) ℂ := ∏ P ∈ hfin.toFinset,
      ∑ j, X (Fin.castAdd d.D j) * C (P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)))
    have hcX : ∀ y, eval y cX = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
      intro y
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [cX, map_prod, map_sum, map_mul, eval_X, eval_C]
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a - cX * NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, -, hn⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    simp only [Fin.addCases_left] at h2
    rw [div_eq_iff hbt]
    exact h2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightKerScaledSubstitutionLeOne
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem height_ker_scaledSubstitution_le_one (hd : d.AxH 𝒜) (c : ι) : (RingHom.ker (d.scaledSubstitution c)).height ≤ 1 := by
  classical
  obtain ⟨J, hJ⟩ := hd.a1 c
  obtain ⟨δ, hδ⟩ := ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.exists_dual_derivations (K := K) (d.x c) J hJ
  have hy : d.affineCoord c (d.jc c) = 1 := scalarRatio_self (hd.w_base c)
  let ρ : Option (Fin d.D) → Fin (d.D + 2) := fun o =>
    (finSuccEquiv (d.D + 1)).symm (some ((finSuccEquiv d.D).symm o))
  have hρ : Function.Injective ρ := by
    intro o o' h
    simpa [ρ] using h
  have hind := algebraicIndependent_scaledForms (K := K) (d.affineCoord c) (d.jc c) hy J δ hδ ρ hρ
  let e : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2) ≃
      Option ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)) :=
    { toFun := fun x => match x with
        | Sum.inl p => some (Sum.inl p)
        | Sum.inr i => (finSuccEquiv (d.D + 1) i).map fun j => Sum.inr (finSuccEquiv d.D j)
      invFun := fun y => match y with
        | none => Sum.inr 0
        | some (Sum.inl p) => Sum.inl p
        | some (Sum.inr o) => Sum.inr (ρ o)
      left_inv := by
        rintro (p | i)
        · rfl
        · rcases h : finSuccEquiv (d.D + 1) i with _ | j <;>
          · have := (finSuccEquiv (d.D + 1)).symm_apply_apply i
            rw [h] at this
            simpa [h, ρ] using this
      right_inv := by
        rintro (_ | p | o)
        · simp
        · rfl
        · simp [ρ] }
  let g := (MvPolynomial.renameEquiv K e).trans
    (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)))
  let gr := g.toRingEquiv
  rw [← RingEquiv.height_comap gr.symm (RingHom.ker (d.scaledSubstitution c))]
  haveI hk : (RingHom.ker (d.scaledSubstitution c)).IsPrime := RingHom.ker_isPrime _
  haveI : (Ideal.comap gr.symm (RingHom.ker (d.scaledSubstitution c))).IsPrime := Ideal.comap_isPrime _ _
  refine ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot _ ?_
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker] at ha
  rw [Ideal.mem_bot]
  have h2 : (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm
      (Polynomial.C a) = MvPolynomial.rename some a := by
    rw [AlgEquiv.symm_apply_eq]
    exact (optionEquivLeft_rename_some' a).symm
  have h1 : gr.symm (Polynomial.C a) = MvPolynomial.rename (fun s => e.symm (some s)) a := by
    show (MvPolynomial.renameEquiv K e).symm ((MvPolynomial.optionEquivLeft K
      ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm (Polynomial.C a)) = _
    rw [h2, MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
    rfl
  rw [h1, scaledSubstitution_eq, MvPolynomial.aeval_rename] at ha
  have hfam : (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) ∘
      (fun s => e.symm (some s)) =
      Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun o => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (ρ o, j)) * MvPolynomial.C (d.affineCoord c j)) := by
    funext s
    rcases s with p | o <;> rfl
  rw [hfam] at ha
  exact (injective_iff_map_eq_zero _).mp hind a ha

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

