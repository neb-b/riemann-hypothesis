module

public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RingKrullDimQuotientOfMemAssociatedPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDimform
section
open IsLocalRing

private theorem height_map_mk_comap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (I : Ideal S) (hI : I = RingHom.ker φ) (J : Ideal T) :
    ((J.comap φ).map (Ideal.Quotient.mk I)).height = J.height := by
  subst hI
  have h : (J.comap φ).map (Ideal.Quotient.mk (RingHom.ker φ)) =
      J.comap (RingHom.quotientKerEquivOfSurjective hφ) := by
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk (RingHom.ker φ)) Ideal.Quotient.mk_surjective
      (J.comap (RingHom.quotientKerEquivOfSurjective hφ))]
    congr 1
  rw [h, RingEquiv.height_comap]

attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem height_ker_add {B C : Type} [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Algebra B C]
    [FaithfulSMul B C] (t N : ℕ) (ht : Algebra.trdeg B C = t) (g : MvPolynomial (Fin N) B →ₐ[B] C)
    (hg : Function.Surjective g) :
    ((RingHom.ker (g : MvPolynomial (Fin N) B →+* C)).height : WithBot ℕ∞) + t = N := by
  let K := FractionRing B
  let L := FractionRing C
  have hBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B C L]
    exact (IsFractionRing.injective C L).comp (FaithfulSMul.algebraMap_injective B C)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hBL
  letI : Algebra K L := FractionRing.liftAlgebra B L
  have : IsScalarTower B K L := FractionRing.isScalarTower_liftAlgebra B L
  let g' : MvPolynomial (Fin N) K →ₐ[K] L :=
    MvPolynomial.aeval fun i => algebraMap C L (g (MvPolynomial.X i))
  have hgg : ∀ x, g' (algebraMap (MvPolynomial (Fin N) B) (MvPolynomial (Fin N) K) x) = algebraMap C L (g x) := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C, MvPolynomial.algHom_C, MvPolynomial.algHom_C,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | mul_X a i ha =>
      simp only [map_mul, ha]
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_X]
      simp [g']
  have hL : IsLocalization ((nonZeroDivisors B).map (MvPolynomial.C (σ := Fin N))) (MvPolynomial (Fin N) K) :=
    MvPolynomial.isLocalization _ _
  have hp : (RingHom.ker g').IsPrime := RingHom.ker_isPrime g'
  have hc : (RingHom.ker g').comap (algebraMap (MvPolynomial (Fin N) B) (MvPolynomial (Fin N) K)) =
      RingHom.ker (g : MvPolynomial (Fin N) B →+* C) := by
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hgg]
    exact map_eq_zero_iff _ (IsFractionRing.injective C L)
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K N (RingHom.ker g')
  have h2 : ringKrullDim (MvPolynomial (Fin N) K ⧸ RingHom.ker g') = ringKrullDim g'.range :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange g').toRingEquiv
  have hft : Algebra.FiniteType K g'.range :=
    Algebra.FiniteType.of_surjective g'.rangeRestrict g'.rangeRestrict_surjective
  have h3 : Algebra.trdeg K g'.range = t := by
    have hmem : ∀ c : C, algebraMap C L c ∈ g'.range := fun c => by
      obtain ⟨x, rfl⟩ := hg c
      exact ⟨_, hgg x⟩
    let j : C →ₐ[B] g'.range.restrictScalars B :=
      (IsScalarTower.toAlgHom B C L).codRestrict (g'.range.restrictScalars B) hmem
    have hj : Function.Injective j := fun a b hab =>
      IsFractionRing.injective C L (congrArg Subtype.val hab)
    have a1 : Algebra.trdeg B C ≤ Algebra.trdeg B g'.range := trdeg_le_of_injective j hj
    have a2 : Algebra.trdeg B g'.range ≤ Algebra.trdeg B L :=
      trdeg_le_of_injective (g'.range.val.restrictScalars B) Subtype.val_injective
    have : Algebra.IsAlgebraic C L := IsLocalization.isAlgebraic L (nonZeroDivisors C)
    have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
    have a3 : Algebra.trdeg B L = Algebra.trdeg B C := by
      rw [← trdeg_add_eq B C (A := L), trdeg_eq_zero (R := C) (A := L), add_zero]
    have a4 : Algebra.trdeg B g'.range = Algebra.trdeg K g'.range := by
      have : FaithfulSMul K g'.range :=
        (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K g'.range).injective
      rw [← trdeg_add_eq B K (A := g'.range), trdeg_eq_zero (R := B) (A := K), zero_add]
    rw [← a4, ← ht]
    exact le_antisymm (a2.trans a3.le) a1
  rw [h2, ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field t h3,
    ← IsLocalization.height_under ((nonZeroDivisors B).map (MvPolynomial.C (σ := Fin N))) (RingHom.ker g'), Ideal.under_def, hc] at h1
  exact h1

theorem UpperTheory.V.CA.g_dimform :
    ∀ (B C : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing C] [IsDomain C] [Algebra B C] [FaithfulSMul B C]
      [Algebra.FiniteType B C] (t : ℕ), ReciprocityTheory.CA.IsCMQuot B → Algebra.trdeg B C = t →
        ∀ (𝔪 : Ideal C) [𝔪.IsMaximal], 𝔪.comap (algebraMap B C) = maximalIdeal B →
          (𝔪.height : WithBot ℕ∞) = ringKrullDim B + t := by
  intro B C _ _ _ _ _ _ _ hft t hB ht 𝔪 _ h𝔪
  obtain ⟨P, _, _, f, hP, hf⟩ := hB
  have := hP.1
  obtain ⟨N, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let F : MvPolynomial (Fin N) P →+* MvPolynomial (Fin N) B := MvPolynomial.map f
  have hF : Function.Surjective F := MvPolynomial.map_surjective f hf
  let G : MvPolynomial (Fin N) P →+* C := (g : MvPolynomial (Fin N) B →+* C).comp F
  have hG : Function.Surjective G := hg.comp hF
  have hGC : ∀ a : P, G (MvPolynomial.C a) = algebraMap B C (f a) := fun a => by
    simp [G, F]
  have : (𝔪.comap G).IsMaximal := Ideal.comap_isMaximal_of_surjective G hG
  have hc : (𝔪.comap G).comap MvPolynomial.C = maximalIdeal P := by
    have : (𝔪.comap G).comap MvPolynomial.C = (maximalIdeal B).comap f := by
      ext a
      rw [← h𝔪]
      simp only [Ideal.mem_comap, hGC]
    rw [this]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf)
  obtain ⟨hCM, e1⟩ := ReciprocityTheory.CA.isCM_localization_mvPolynomial hP N (𝔪.comap G) hc
  have : (RingHom.ker G).IsPrime := RingHom.ker_isPrime G
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have e2 := ReciprocityTheory.CA.height_eq_add_of_isCM_localization (𝔪.comap G) (RingHom.ker G) hCM
    (Ideal.ker_le_comap G)
  rw [height_map_mk_comap G hG _ rfl] at e2
  have : (RingHom.ker G).LiesOver (RingHom.ker f) := ⟨by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, MvPolynomial.algebraMap_eq, hGC]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective B C)).symm⟩
  have e3 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (RingHom.ker f) (RingHom.ker G)
  have hk : RingHom.ker G = (RingHom.ker (g : MvPolynomial (Fin N) B →+* C)).comap F := rfl
  have e4 := height_map_mk_comap F hF ((RingHom.ker f).map (algebraMap P (MvPolynomial (Fin N) P)))
    (by rw [MvPolynomial.algebraMap_eq]; exact (MvPolynomial.ker_map f).symm)
    (RingHom.ker (g : MvPolynomial (Fin N) B →+* C))
  rw [← hk] at e4
  rw [e4] at e3
  have e5 := height_ker_add t N ht g hg
  have e6 := hP.height_add_ringKrullDim_quotient (RingHom.ker f)
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf)] at e6
  have f1 : (RingHom.ker G).height ≠ ⊤ := Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  have key : (((RingHom.ker G).height : ℕ∞) : WithBot ℕ∞) + 𝔪.height =
      (((RingHom.ker G).height : ℕ∞) : WithBot ℕ∞) + (ringKrullDim B + t) := by
    rw [← WithBot.coe_add, ← e2, e1, ← e6, ← e5, e3, WithBot.coe_add]
    abel
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp f1
  rw [← hn] at key
  exact (ENat.WithBot.natCast_add_cancel).mp key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GKillsTr
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.g_kills_tr :
    ∀ {n h : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → MultFree χ h → 1 ≤ n → ∀ y : MonoidAlgebra B G, D.Kills y ↔ ∀ g : G, D.tr (MonoidAlgebra.single g 1 * y) = 0 := by
  intro n h B G _ _ _ _ _ _ _ _ _ _ D χ hc hred hmf hn y
  obtain ⟨DE, π, e, hpull, hgma, -, -, -, -, -⟩ := finE_gma D χ hc hred hmf ∅ (by simp)
  have hsurj : Function.Surjective (D.toQuot ∅) := RingCon.mkₐ_surjective _
  have htq : ∀ w, DE.tr (D.toQuot ∅ w) = D.tr w := by
    intro w
    rw [← (d_toDet D w).2.2.1]
    show (-1) ^ 1 * (DE.chi _).coeff (n - 1) = (-1) ^ 1 * (D.toDet.chi w).coeff (n - 1)
    rw [← hpull, (d_pull DE (D.toQuot ∅)).1 w]
  obtain ⟨t, ht⟩ := (d_tr D.toDet).1 hn
  rw [← (d_toDet D y).2.2.2, ← (d_ker _ y).1]
  constructor
  · intro hy g
    have hk : D.toQuot ∅ y ∈ DE.ker := by
      rw [← hpull] at hy
      exact ((d_pull DE _).2.2.2 hsurj).1 y hy
    rw [← htq, map_mul]
    exact (gma_kills DE e hn hgma _).1 hk _
  · intro H
    have hk : D.toQuot ∅ y ∈ DE.ker := by
      rw [gma_kills DE e hn hgma]
      intro q
      obtain ⟨w, rfl⟩ := hsurj q
      rw [← map_mul, htq, ← (d_toDet D _).2.2.1, ← ht]
      refine MonoidAlgebra.induction_on (motive := fun w => t (w * y) = 0) w ?_ ?_ ?_
      · intro m
        rw [ht, (d_toDet D _).2.2.1]
        exact H m
      · intro a b ha hb
        rw [add_mul, map_add (f := _), ha, hb, add_zero]
      · intro r a ha
        rw [smul_mul_assoc, map_smul, ha, smul_zero]
    rw [← hpull]
    exact (d_pull DE _).2.1 y hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KTypesBoundedFinite
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem exists_inverse_mod_maximal_pow {A : Type} [CommRing A] (x : Ideal A) [x.IsMaximal] (n : ℕ) (w : A)
    (hw : w ∉ x) : ∃ v : A, v * w - 1 ∈ x ^ n := by
  have hcop : Ideal.span {w} ⊔ x ^ n = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hM.isPrime
    have hxM : x ≤ M := Ideal.IsPrime.le_of_pow_le (le_trans le_sup_right hle)
    have hMx : x = M := Ideal.IsMaximal.eq_of_le ‹x.IsMaximal› hM.ne_top hxM
    apply hw
    rw [hMx]
    exact hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self w))
  have h1 : (1 : A) ∈ Ideal.span {w} ⊔ x ^ n := by
    rw [hcop]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨v, ?_⟩
  have e : v * w - 1 = -z := by
    rw [← hyz]
    ring
  rw [e]
  exact (x ^ n).neg_mem hz

private theorem isCplAt_of_localization_atPrime {A R' : Type} [CommRing A] [CommRing R'] [IsLocalRing R']
    (x : Ideal A) [x.IsMaximal] [Algebra (Localization.AtPrime x) R'] [Algebra A R']
    (hcomp : algebraMap A R' =
      (algebraMap (Localization.AtPrime x) R').comp (algebraMap A (Localization.AtPrime x)))
    (h : IsCplAt (maximalIdeal (Localization.AtPrime x)) R') : IsCplAt x R' := by
  have hmax : maximalIdeal (Localization.AtPrime x) = x.map (algebraMap A (Localization.AtPrime x)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hprim : ∀ n : ℕ, Ideal.comap (algebraMap A (Localization.AtPrime x))
      (x.map (algebraMap A (Localization.AtPrime x)) ^ n) = x ^ n := by
    intro n
    rw [← Ideal.map_pow]
    apply le_antisymm
    · intro a ha
      rw [Ideal.mem_comap, IsLocalization.mem_map_algebraMap_iff x.primeCompl] at ha
      obtain ⟨⟨y, t⟩, hyt⟩ := ha
      rw [← map_mul, IsLocalization.eq_iff_exists x.primeCompl] at hyt
      obtain ⟨c, hc⟩ := hyt
      have hw : (c : A) * t ∉ x := fun hm =>
        (Ideal.IsPrime.mem_or_mem inferInstance hm).elim c.2 t.2
      obtain ⟨v, hv⟩ := exists_inverse_mod_maximal_pow x n ((c : A) * t) hw
      have hca : (c : A) * t * a ∈ x ^ n := by
        have e1 : (c : A) * t * a = c * (a * t) := by ring
        rw [e1, hc]
        exact Ideal.mul_mem_left _ _ y.2
      have e2 : a = v * ((c : A) * t * a) - (v * ((c : A) * t) - 1) * a := by ring
      rw [e2]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hca) (Ideal.mul_mem_right _ _ hv)
    · exact Ideal.le_comap_map
  refine ⟨h.noeth, h.complete, ?_, ?_⟩
  · intro n
    rw [hcomp, ← Ideal.comap_comap, h.comap_pow n, hmax]
    exact hprim n
  · intro n r
    obtain ⟨a, ha⟩ := h.dense n r
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective x.primeCompl a
    obtain ⟨u, hu⟩ := exists_inverse_mod_maximal_pow x n (t : A) t.2
    refine ⟨s * u, ?_⟩
    have e : IsLocalization.mk' (Localization.AtPrime x) s t
        - algebraMap A (Localization.AtPrime x) (s * u) =
        algebraMap A (Localization.AtPrime x) (s * (1 - u * t)) *
          IsLocalization.mk' (Localization.AtPrime x) (1 : A) t := by
      have hsp := IsLocalization.mk'_spec (Localization.AtPrime x) (1 : A) t
      rw [IsLocalization.mk'_eq_mul_mk'_one s t]
      simp only [map_mul, map_sub, map_one] at hsp ⊢
      linear_combination (algebraMap A (Localization.AtPrime x) s *
        algebraMap A (Localization.AtPrime x) u) * hsp
    have hmem : s * (1 - u * t) ∈ x ^ n := by
      have e3 : s * (1 - u * t) = -(s * (u * t - 1)) := by ring
      rw [e3]
      exact neg_mem (Ideal.mul_mem_left _ _ hu)
    have hdiff : IsLocalization.mk' (Localization.AtPrime x) s t
        - algebraMap A (Localization.AtPrime x) (s * u) ∈
        maximalIdeal (Localization.AtPrime x) ^ n := by
      rw [e, hmax, ← Ideal.map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmem)
    have hm1 : (maximalIdeal (Localization.AtPrime x)).map
        (algebraMap (Localization.AtPrime x) R') ≤ maximalIdeal R' := by
      rw [Ideal.map_le_iff_le_comap]
      have h1 := h.comap_pow 1
      rw [pow_one, pow_one] at h1
      rw [h1]
    have hmapR : (maximalIdeal (Localization.AtPrime x) ^ n).map
        (algebraMap (Localization.AtPrime x) R') ≤ maximalIdeal R' ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hm1 n
    have h2 := hmapR (Ideal.mem_map_of_mem (algebraMap (Localization.AtPrime x) R') hdiff)
    rw [map_sub] at h2
    have h3 := (maximalIdeal R' ^ n).add_mem ha h2
    rw [hcomp, RingHom.comp_apply]
    convert h3 using 1
    ring

theorem UpperTheory.V.CA.c3d :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {B C R : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [CommRing C] [Algebra B C] [Algebra.FiniteType B C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCL O B → x.comap (algebraMap B C) = maximalIdeal B → IsCplAt x R → ∀ (p : Ideal C) [p.IsPrime], p ≤ x → ∀ q ∈ (p.map (algebraMap C R)).minimalPrimes, ringKrullDim (R ⧸ q) = dimAt x p ∧ q.comap (algebraMap C R) = p := by
  intro O _ _ _ _ B C R _ _ _ _ _ _ _ _ _ x _ hB hxB hR p _ hpx q hq
  haveI : IsNoetherianRing B := hB.noeth
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing B C
  have hcomapq : q.comap (algebraMap C R) = p := by
    have h := (c3a x hR).2.2.2.2 p q hq
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at h
    exact h
  refine ⟨le_antisymm ((c3c x hR).2 p q hcomapq.ge) ?_, hcomapq⟩
  obtain ⟨P0, _, _, f0, hcm, hf0⟩ := cl_cmquot O B hB
  haveI : IsNoetherianRing P0 := hcm.1
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType B C)
  let π : MvPolynomial (Fin n) P0 →+* C :=
    (g : MvPolynomial (Fin n) B →+* C).comp (MvPolynomial.map f0)
  have hπ : Function.Surjective π := by
    intro c
    obtain ⟨a, rfl⟩ := hg c
    obtain ⟨b, rfl⟩ := MvPolynomial.map_surjective (f := f0) hf0 a
    exact ⟨b, rfl⟩
  set xt : Ideal (MvPolynomial (Fin n) P0) := Ideal.comap π x with hxt
  haveI : xt.IsMaximal := Ideal.comap_isMaximal_of_surjective π hπ
  have hxtC : Ideal.comap MvPolynomial.C xt = maximalIdeal P0 := by
    have e : π.comp MvPolynomial.C = (algebraMap B C).comp f0 := by
      refine RingHom.ext fun a => ?_
      show g (MvPolynomial.map f0 (MvPolynomial.C a)) = algebraMap B C (f0 a)
      rw [MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    rw [hxt, Ideal.comap_comap, e, ← Ideal.comap_comap, hxB]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f0 hf0)
  obtain ⟨hScm, -⟩ := isCM_localization_mvPolynomial hcm n xt hxtC
  haveI : IsNoetherianRing (Localization.AtPrime xt) := hScm.1
  obtain ⟨d, hd, -⟩ := hScm.2
  obtain ⟨hloc, hcpl⟩ := cpl_is (Localization.AtPrime xt) (maximalIdeal (Localization.AtPrime xt))
  obtain ⟨-, hDR', hDSx, hdimR'⟩ := cpl_cm (Localization.AtPrime xt)
    (Cpl (maximalIdeal (Localization.AtPrime xt))) hcpl hScm
  haveI : IsNoetherianRing (Cpl (maximalIdeal (Localization.AtPrime xt))) := hcpl.noeth
  haveI : Module.Flat (Localization.AtPrime xt) (Cpl (maximalIdeal (Localization.AtPrime xt))) :=
    (c3a (maximalIdeal (Localization.AtPrime xt)) hcpl).1
  letI : Algebra (MvPolynomial (Fin n) P0) (Cpl (maximalIdeal (Localization.AtPrime xt))) :=
    ((algebraMap (Localization.AtPrime xt) (Cpl (maximalIdeal (Localization.AtPrime xt)))).comp
      (algebraMap (MvPolynomial (Fin n) P0) (Localization.AtPrime xt))).toAlgebra
  have hcplS : IsCplAt xt (Cpl (maximalIdeal (Localization.AtPrime xt))) := isCplAt_of_localization_atPrime xt rfl hcpl
  obtain ⟨F, hFs, hFc, hFk⟩ := cpl_quot xt hcplS C R π x hπ hxt.symm hR
  set pt : Ideal (MvPolynomial (Fin n) P0) := Ideal.comap π p with hpt
  haveI : pt.IsPrime := Ideal.comap_isPrime π p
  have hptxt : pt ≤ xt := Ideal.comap_mono hpx
  have hdisj : Disjoint (xt.primeCompl : Set (MvPolynomial (Fin n) P0)) (pt : Set _) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact ha (hptxt hb)
  set ps : Ideal (Localization.AtPrime xt) := pt.map (algebraMap _ (Localization.AtPrime xt)) with hps
  haveI : ps.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint xt.primeCompl _ pt inferInstance hdisj
  haveI : q.IsPrime := hq.1.1
  set Q' : Ideal (Cpl (maximalIdeal (Localization.AtPrime xt))) := Ideal.comap F q with hQ'
  haveI : Q'.IsPrime := Ideal.comap_isPrime F q
  have hkerle : RingHom.ker π ≤ pt := fun a ha => by
    rw [hpt, Ideal.mem_comap, RingHom.mem_ker.mp ha]
    exact p.zero_mem
  have hmapS : pt.map (algebraMap (MvPolynomial (Fin n) P0) (Cpl (maximalIdeal (Localization.AtPrime xt)))) =
      ps.map (algebraMap (Localization.AtPrime xt) (Cpl (maximalIdeal (Localization.AtPrime xt)))) := by
    rw [hps, Ideal.map_map]
    rfl
  have hFmap : (pt.map (algebraMap (MvPolynomial (Fin n) P0)
      (Cpl (maximalIdeal (Localization.AtPrime xt))))).map F = p.map (algebraMap C R) := by
    rw [Ideal.map_map, hFc, ← Ideal.map_map, hpt, Ideal.map_comap_of_surjective π hπ]
  have hQmin : Q' ∈ (ps.map (algebraMap (Localization.AtPrime xt)
      (Cpl (maximalIdeal (Localization.AtPrime xt))))).minimalPrimes := by
    rw [← hmapS]
    refine ⟨⟨inferInstance, ?_⟩, fun Q'' hQ'' hle => ?_⟩
    · exact Ideal.map_le_iff_le_comap.mp (hFmap ▸ hq.1.2)
    · obtain ⟨hQ''p, hQ''le⟩ := hQ''
      haveI := hQ''p
      have hkF : RingHom.ker F ≤ Q'' := by
        rw [hFk]
        exact le_trans (Ideal.map_mono hkerle) hQ''le
      haveI hmp : (Q''.map F).IsPrime := Ideal.map_isPrime_of_surjective hFs hkF
      have h1 : p.map (algebraMap C R) ≤ Q''.map F := by
        rw [← hFmap]
        exact Ideal.map_mono hQ''le
      have h2 : Q''.map F ≤ q := by
        calc Q''.map F ≤ Q'.map F := Ideal.map_mono hle
          _ = q := Ideal.map_comap_of_surjective F hFs q
      have h3 : q ≤ Q''.map F := hq.2 ⟨hmp, h1⟩ h2
      calc Q' = Ideal.comap F q := rfl
        _ ≤ Ideal.comap F (Q''.map F) := Ideal.comap_mono h3
        _ = Q'' := by
          rw [Ideal.comap_map_of_surjective F hFs, sup_eq_left]
          exact fun a ha => hkF ha
  obtain ⟨-, hdimeq⟩ := g_ratliff (Localization.AtPrime xt)
    (Cpl (maximalIdeal (Localization.AtPrime xt))) d hDSx hDR' hd (hdimR'.trans hd) ps Q' hQmin
  have hsurjq : Function.Surjective ((Ideal.Quotient.mk q).comp F) := fun z => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨r', rfl⟩ := hFs r
    exact ⟨r', rfl⟩
  have hkerq : RingHom.ker ((Ideal.Quotient.mk q).comp F) = Q' := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  have hiso : ringKrullDim (R ⧸ q) =
      ringKrullDim (Cpl (maximalIdeal (Localization.AtPrime xt)) ⧸ Q') := by
    rw [← ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurjq), hkerq]
  let φ := Localization.localRingHom xt x π hxt
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective x.primeCompl z
    obtain ⟨r', rfl⟩ := hπ r
    obtain ⟨s', hs'⟩ := hπ (s : C)
    have hs'p : s' ∈ xt.primeCompl := by
      intro h
      apply s.2
      have h' : π s' ∈ x := h
      rw [hs'] at h'
      exact h'
    refine ⟨IsLocalization.mk' (Localization.AtPrime xt) r' ⟨s', hs'p⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  have hφq : Function.Surjective
      ((Ideal.Quotient.mk (p.map (algebraMap C (Localization.AtPrime x)))).comp φ) := fun z => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨r', rfl⟩ := hφ r
    exact ⟨r', rfl⟩
  have hkerφ : ∀ a ∈ ps,
      ((Ideal.Quotient.mk (p.map (algebraMap C (Localization.AtPrime x)))).comp φ) a = 0 := by
    have hle : ps ≤ RingHom.ker
        ((Ideal.Quotient.mk (p.map (algebraMap C (Localization.AtPrime x)))).comp φ) := by
      rw [hps, Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, Localization.localRingHom_to_map,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hb
    exact fun a ha => hle ha
  have hfin := ringKrullDim_le_of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective ps hkerφ hφq)
  rw [hiso, hdimeq]
  exact hfin
end

