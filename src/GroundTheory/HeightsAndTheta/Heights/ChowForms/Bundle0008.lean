module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartFirstGroupPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

private def firstGroupVars (e n : ℕ) : Fin (e + 1) × Fin n ≃ Fin n ⊕ Fin e × Fin n where
  toFun ij := Fin.cases (motive := fun _ => Fin n ⊕ Fin e × Fin n) (Sum.inl ij.2)
    (fun i => Sum.inr (i, ij.2)) ij.1
  invFun := Sum.elim (fun m => (0, m)) (fun im => (im.1.succ, im.2))
  left_inv := by
    rintro ⟨i, m⟩
    cases i using Fin.cases <;> rfl
  right_inv := by
    rintro (m | ⟨i, m⟩) <;> rfl

private theorem firstGroup_eq {F : Type*} [Field F] {n e : ℕ} (g : MvPolynomial (Fin (e + 1) × Fin n) F) :
    firstGroup g = ((renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n))) g := by
  have h : (aeval (fun ij : Fin (e + 1) × Fin n =>
      Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
        (X ij.2) (fun i => C (X (i, ij.2))) ij.1) :
        MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] _) =
      ((renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n))).toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, m⟩
    cases i using Fin.cases <;> simp [firstGroupVars]
  exact DFunLike.congr_fun h g

theorem ChartFirstGroupPrime.proof (h₁ : IncIdealPrime.Statement) (h₂ : IncIdealBelow.Statement) :
    ChartFirstGroupPrime.Statement := by
  intro F _ n e I f p _ hI hf
  obtain ⟨hf0, hspan⟩ := isChowForm_iff.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  set Φ := (renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n)) with hΦ
  have hg : Prime (firstGroup f) := by
    rw [firstGroup_eq]
    exact (MulEquiv.prime_iff Φ).mpr hfp

  have hC : ∀ s : MvPolynomial (Fin e × Fin n) F,
      (C s : MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) =
        Φ (rename (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) s) := by
    intro s
    have hcomp : (firstGroupVars e n) ∘ (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) =
        Sum.inr := by
      funext im
      rfl
    rw [hΦ, AlgEquiv.trans_apply, renameEquiv_apply, rename_rename, hcomp]
    have := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr F (Fin n) (Fin e × Fin n)) s
    simp only [AlgHom.coe_comp, Function.comp_apply] at this
    exact (this.trans (by rw [IsScalarTower.coe_toAlgHom', algebraMap_eq])).symm
  have hdisj : Disjoint ((p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+*
      MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) : Submonoid _) : Set _)
      ((Ideal.span {firstGroup f} : Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) :
        Set (MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) := by
    rw [Set.disjoint_left]
    intro y hy hmem
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
    rw [SetLike.mem_coe, Ideal.mem_span_singleton, hC, firstGroup_eq, map_dvd_iff] at hmem
    have hvan := (hf.2 _).mpr hmem
    have hsI : s ∈ incIdeal I e := by
      rw [mem_incIdeal_iff]
      rintro v ⟨x, hx0, hxI, hxv⟩
      have := hvan (fun ij => Fin.cases (motive := fun _ => AlgebraicClosure F) 0 (fun i => v (i, ij.2)) ij.1)
        ⟨x, hx0, hxI, fun i => by
          cases i using Fin.cases with
          | zero => simp
          | succ i => simpa using hxv i⟩
      rwa [aeval_rename] at this
    rw [h₂ F n e I f hI hf, Ideal.mem_bot] at hsI
    exact hs (hsI ▸ p.zero_mem)
  letI := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := MvPolynomial (Fin e × Fin n) F)
    (S := Localization.AtPrime p)
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    (p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+*
      MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)))
    (MvPolynomial (Fin n) (Localization.AtPrime p)) _
    ((Ideal.span_singleton_prime hg.ne_zero).mpr hg) hdisj
  rw [Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] at hprime
  refine (Ideal.span_singleton_prime fun h => hg.ne_zero ?_).mp hprime
  exact map_injective _ (IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors)
    (h.trans (map_zero _).symm)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartIncDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartIncDomain

theorem aeval_smul_of_isHomogeneous {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (c : S) (x : σ → S) :
    aeval (c • x) p = c ^ d * aeval x p := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : ∑ i ∈ s.support, s i = d := by
    have := hp (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs']
  ring

theorem isHomogeneous_linForm {F : Type*} [CommRing F] {n : ℕ} (t : Fin n → F) :
    (linForm t).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X _ _).C_mul _

variable {F : Type} [Field F] {n : ℕ}

theorem aeval_genPt (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (g : MvPolynomial (Fin n) F) :
    aeval (genPt I) g =
      algebraMap (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))
        (Ideal.Quotient.mk I g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F ⧸ I)]
    rfl
  | add p q hp hq =>
    rw [map_add (aeval (genPt I)), (Ideal.Quotient.mk I).map_add, RingHom.map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X, genPt]

theorem ker_aeval_eta (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (hI : IsProjPrime I)
    (ht : linForm t ∉ I) :
    letI : I.IsPrime := hI.isPrime;
    RingHom.ker (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I) :
        MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I)) =
      I ⊔ Ideal.span {linForm t - 1} := by
  have := hI.isPrime
  set ξ := genPt I
  set τ := aeval ξ (linForm t)
  have hτ : τ ≠ 0 := by
    rw [show τ = _ from aeval_genPt I (linForm t), Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact ht
  have hhom : ∀ (p : MvPolynomial (Fin n) F) (d : ℕ), p.IsHomogeneous d →
      aeval (τ⁻¹ • ξ) p = τ⁻¹ ^ d * aeval ξ p := fun p d hp => aeval_smul_of_isHomogeneous hp _ _
  have hcomp : ∀ (g : MvPolynomial (Fin n) F), aeval (τ⁻¹ • ξ) g =
      ∑ d ∈ Finset.range (g.totalDegree + 1), τ⁻¹ ^ d * aeval ξ (homogeneousComponent d g) := by
    intro g
    conv_lhs => rw [← sum_homogeneousComponent g]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun d _ => hhom _ _ (homogeneousComponent_isHomogeneous d g)
  apply le_antisymm
  · intro g hg
    rw [RingHom.mem_ker] at hg
    set D := g.totalDegree
    set G := ∑ d ∈ Finset.range (D + 1), homogeneousComponent d g * linForm t ^ (D - d)
    have hGξ : aeval ξ G = τ ^ D * aeval (τ⁻¹ • ξ) g := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcomp, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdD : d ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
      rw [map_mul, map_pow, ← mul_assoc, mul_comm (aeval ξ _)]
      congr 1
      rw [← Nat.sub_add_cancel hdD, pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hτ, one_pow,
        mul_one, Nat.sub_add_cancel hdD]
    have hGI : G ∈ I := by
      have h0 : aeval ξ G = 0 := by
        rw [hGξ]
        have : (aeval (τ⁻¹ • ξ) : MvPolynomial (Fin n) F →ₐ[F] _) g = 0 := hg
        rw [this, mul_zero]
      rw [aeval_genPt, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
      exact h0
    set J := I ⊔ Ideal.span {linForm t - 1}
    have h1 : Ideal.Quotient.mk J (linForm t) = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    have hG : Ideal.Quotient.mk J G = Ideal.Quotient.mk J g := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [G, map_sum, map_mul, map_pow, h1, one_pow, mul_one]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, sum_homogeneousComponent]
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hG, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left hGI
  · refine sup_le ?_ ?_
    · intro g hg
      rw [RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) g = 0
      rw [hcomp]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [aeval_genPt, (Ideal.Quotient.eq_zero_iff_mem).mpr (hI.isHomog g hg d), map_zero, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) (linForm t - 1) = 0
      rw [map_sub, map_one, hhom _ 1 (isHomogeneous_linForm t), pow_one, inv_mul_cancel₀ hτ, sub_self]

theorem proof : ChartIncDomain.Statement := by
  intro F _ n e I t hI ht
  have := hI.isPrime
  set J := I ⊔ Ideal.span {linForm t - 1} with hJdef
  have hJ : J.IsPrime := by
    rw [hJdef, ← ker_aeval_eta I t hI ht]
    exact RingHom.ker_isPrime _

  set q : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F ⧸ J := Ideal.Quotient.mk J with hq
  set ζ : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (X m) with hζ
  set c : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (C (t m)) with hc'
  have hc : ∑ l, c l * ζ l = 1 := by
    have h1 : q (linForm t) = 1 := by
      rw [← sub_eq_zero, ← map_one q, ← map_sub, hq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, linForm, map_sum]
    simp only [map_mul, hζ, hc']

  set γ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) :=
    eval₂Hom (C.comp (q.comp C)) (Sum.elim (fun m => C (ζ m)) (genSubst ζ c)) with hγ
  have hγX : ∀ g, γ (rename Sum.inl g) = C (q g) := by
    intro g
    have : γ.comp (rename Sum.inl).toRingHom = C.comp q := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [hγ]
      · intro m; simp [hγ, hζ]
    exact RingHom.congr_fun this g
  have hker : chartIncIdeal I t e ≤ RingHom.ker γ := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [hγX, hq, (Ideal.Quotient.eq_zero_iff_mem).mpr hg, map_zero]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have hC : ∑ l, C (c l) * C (ζ l) = (1 : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← C_1, ← hc, map_sum]
        simp only [C_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hγ, coe_eval₂Hom, eval₂_X, Sum.elim_inl, Sum.elim_inr]
      simp only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one,
        sub_self]

  set γbar : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) :=
    Ideal.Quotient.lift (chartIncIdeal I t e) γ (fun a ha => RingHom.mem_ker.mp (hker ha)) with hγbar
  set χ : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e :=
    (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inl).toRingHom with hχ
  have hJX : ∀ a ∈ J, χ a = 0 := by
    intro a ha
    rw [hχ, RingHom.comp_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)

  set β : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) →+*
      MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e :=
    eval₂Hom (Ideal.Quotient.lift J χ hJX)
      (fun im => Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inr im))) with hβ
  have hβγ : β.comp γ = Ideal.Quotient.mk (chartIncIdeal I t e) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hβ, hγ, hq, hχ]
    · rintro (m | im)
      · simp [hβ, hγ, hζ, hq, hχ]
      · have h0 : Ideal.Quotient.mk (chartIncIdeal I t e)
            (∑ l, X (Sum.inr (im.1, l)) * X (Sum.inl l)) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.subset_span ⟨im.1, rfl⟩)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul] at h0
        simp [hβ, hγ, hζ, hc', hq, hχ, genSubst, h0]
  have hleft : ∀ x : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e, β (γbar x) = x := by
    intro x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := chartIncIdeal I t e) x
    rw [hγbar, Ideal.Quotient.lift_mk]
    exact RingHom.congr_fun hβγ g
  have hinj : Function.Injective γbar := Function.LeftInverse.injective hleft
  refine ⟨(hinj.isDomain γbar :), ?_⟩
  change RingHom.ker χ = J
  ext g
  constructor
  · intro hg
    rw [RingHom.mem_ker] at hg
    have h := hγX g
    have h' : γbar (χ g) = γ (rename Sum.inl g) := by
      rw [hγbar, hχ, RingHom.comp_apply]
      exact Ideal.Quotient.lift_mk _ _ _
    rw [← h', hg, map_zero, eq_comm, C_eq_zero, hq, Ideal.Quotient.eq_zero_iff_mem] at h
    exact h
  · intro hg
    exact hJX g hg

end ChartIncDomain

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartLocDomain

variable {F : Type} [Field F] {n : ℕ}

theorem aeval_mul_of_isHomogeneous {A : Type*} [CommRing A] [Algebra F A]
    {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) (c : A) (x : Fin n → A) :
    aeval (fun m => c * x m) g = c ^ d * aeval x g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.mp hs)
  simp only [aeval_monomial, mul_pow]
  rw [Finsupp.prod_mul, Finsupp.prod_pow, Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, ← hd,
    Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [smul_eq_mul, Pi.one_apply, mul_one]
  ring

theorem linForm_isHomogeneous (u : Fin n → F) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem linForm_not_mem_sup {I : Ideal (MvPolynomial (Fin n) F)} (hI : IsProjPrime I) {t u : Fin n → F}
    (ht : linForm t ∉ I) (hu : linForm u ∉ I) : linForm u ∉ I ⊔ Ideal.span {linForm t - 1} := by
  have := hI.isPrime
  set a : MvPolynomial (Fin n) F ⧸ I := Ideal.Quotient.mk I (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ I) A).comp (Ideal.Quotient.mkₐ F I)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    rw [← comp_aeval_apply]; simp
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {d : ℕ}, g.IsHomogeneous d → ψ g = v ^ d * φ g :=
    fun hg => by rw [← hφ]; exact aeval_mul_of_isHomogeneous hg _ _
  have hle : I ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [hhom (homogeneousComponent_isHomogeneous d g)]
      have : φ (homogeneousComponent d g) = 0 := by
        simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hI.isHomog g hg d)]
      rw [this, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
        hhom (linForm_isHomogeneous t), pow_one]
      have : φ (linForm t) = algebraMap _ A a := rfl
      rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  intro hmem
  have h0 : ψ (linForm u) = 0 := hle hmem
  rw [hhom (linForm_isHomogeneous u), pow_one] at h0
  have h1 : algebraMap _ A (Ideal.Quotient.mk I (linForm u)) = 0 :=
    calc algebraMap _ A (Ideal.Quotient.mk I (linForm u))
        = algebraMap _ A a * (v * φ (linForm u)) := by
          rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]; rfl
      _ = 0 := by rw [h0, mul_zero]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ I) A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  exact hu (Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h1.trans (map_zero _).symm)))

end ChartLocDomain

theorem ChartLocDomain.proof (h₁ : IncIdealBelow.Statement) (h₂ : ChartIncDomain.Statement)
    (h₃ : ChartKernel.Statement) : ChartLocDomain.Statement := by
  intro F _ n e I f t p _ hI hf ht
  obtain ⟨hdom, hker⟩ := h₂ F n e I t hI ht
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr (by rw [h₃ F n e I t hI ht, h₁ F n e I f hI hf])
  have hle : Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl ≤ nonZeroDivisors (ChartInc I t e) := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs ?_
    rw [hinj (h0.trans (map_zero _).symm)]
    exact p.zero_mem
  have : IsDomain (ChartLoc I t e p) := IsLocalization.isDomain_localization hle
  refine ⟨inferInstance, localizationAlgebra_injective (M := p.primeCompl) (S := ChartInc I t e)
    (Rₘ := Localization.AtPrime p) (Sₘ := ChartLoc I t e p) (hRS := hinj), fun u hu h0 => ?_⟩
  have hz : chartLin I t e u = 0 := IsLocalization.injective (ChartLoc I t e p) hle (h0.trans (map_zero _).symm)
  have hmem : linForm u ∈ RingHom.ker (chartX I t e) := hz
  rw [hker] at hmem
  exact ChartLocDomain.linForm_not_mem_sup hI ht hu hmem

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormMultiHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem chowFormMultiHomog : ChowFormMultiHomog.Statement :=
  fun _ _ _ _ _ _ hP hf => hf.exists_multiHomog hP

theorem ChowFormMultiHomog.proof (_h₁ : ProjNullstellensatz.Statement) :
    ChowFormMultiHomog.Statement :=
  chowFormMultiHomog

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartFirstGroupDvd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartFirstGroupDvd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I →
      (∑ m, X m * C (chartX I t e (X m))) ∣
        map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

