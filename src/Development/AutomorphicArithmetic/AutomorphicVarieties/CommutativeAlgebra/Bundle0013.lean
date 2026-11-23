module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0050

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.EigenMem
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem eigen_low {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S)
    (F : MvPowerSeries σ R →+* S) (hF : ∀ s, F (X s) ∈ m) (n : ℕ) (g : MvPowerSeries σ R)
    (hg : ∀ d : σ →₀ ℕ, d.degree < n → coeff d g = 0) : F g ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), F (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  have h := key (e g) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    have : truncTotal n g = 0 := by
      ext x
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hx
      · rw [hg x hx]; simp
      · simp
    rw [this]
    rfl)
  rwa [AlgEquiv.symm_apply_apply] at h

private theorem eigen_split {O σ X : Type} [CommRing O] [Finite σ] [AddCommGroup X] (wt : σ → X) (j : X)
    (n : ℕ) (g : MvPowerSeries σ O) : ∃ s : Finset X, j ∈ s ∧
      ∀ d : σ →₀ ℕ, d.degree < n → coeff d (g - ∑ i ∈ s, wcomp O wt i g) = 0 := by
  classical
  refine ⟨insert j ((truncTotal n g).support.image (Finsupp.weight wt)), Finset.mem_insert_self _ _,
    fun d hd => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra hne
    refine h (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ?_))
    rwa [MvPolynomial.mem_support_iff, coeff_truncTotal _ hd]

theorem UpperTheory.V.Alg.eigen_mem :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (x : R) (j : X),
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ), (∀ i, res O R' (t i) = 1) →
        (∀ s, f' (W.z s) = t (Multiplicative.ofAdd (W.wt s)) * f (W.z s)) → f' x = t (Multiplicative.ofAdd j) * f x) → x ∈ W.part j := by
  intro O _ _ _ _ X _ _ _ R _ _ hR W hz x j H
  classical
  obtain ⟨n, t0, ht1, hind⟩ := tchar O X
  haveI : IsCO O (MvPowerSeries (Fin n) R) := co_mvps O R (Fin n)
  let f : R →ₐ[O] MvPowerSeries (Fin n) R :=
    { (C : R →+* MvPowerSeries (Fin n) R) with commutes' := fun a => (MvPowerSeries.algebraMap_apply).symm }
  have hf : ∀ a, f a = C a := fun _ => rfl
  let t : Multiplicative X →* (MvPowerSeries (Fin n) R)ˣ :=
    (Units.map (MvPowerSeries.map (σ := Fin n) (algebraMap O R)).toMonoidHom).comp t0
  have ht : ∀ i, (t i : MvPowerSeries (Fin n) R) =
      MvPowerSeries.map (algebraMap O R) (t0 i : MvPowerSeries (Fin n) O) := fun _ => rfl
  have hres : ∀ i, res O (MvPowerSeries (Fin n) R) (t i) = 1 := fun i => by
    have h : (t i : MvPowerSeries (Fin n) R) - 1 ∈ maximalIdeal (MvPowerSeries (Fin n) R) := fun hu => by
      have h2 := isUnit_constantCoeff _ hu
      rw [map_sub, ht, constantCoeff_map, ht1, map_one, map_one, sub_self] at h2
      exact not_isUnit_zero h2
    have := (res_eq_zero_iff O _ _).2 h
    rwa [map_sub, map_one, sub_eq_zero] at this
  obtain ⟨f', hf', -⟩ := tact O X R W hz (MvPowerSeries (Fin n) R) f t
  have hx := H _ f f' t hres (fun s => hf' _ _ (W.z_mem s))
  obtain ⟨g, rfl⟩ := W.surj x
  suffices h : W.π (wcomp O W.wt j g) - W.π g = 0 by
    rw [sub_eq_zero] at h
    exact ⟨_, wcomp_mem O W.wt j g, h⟩
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  refine IsHausdorff.haus (I := maximalIdeal R) inferInstance _ fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨s, hjs, hs⟩ := eigen_split W.wt j N g
  have h1 := eigen_low ((maximalIdeal R).map (C : R →+* MvPowerSeries (Fin n) R))
    ((f'.comp W.π : MvPowerSeries W.σ O →ₐ[O] _) : MvPowerSeries W.σ O →+* _) (fun s => by
      show f' (W.z s) ∈ _
      rw [hf' _ _ (W.z_mem s)]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hz s))) N _ hs
  let q := Ideal.Quotient.mk (maximalIdeal R ^ N)
  have h2 : MvPowerSeries.map (σ := Fin n) q (f' (W.π (g - ∑ i ∈ s, wcomp O W.wt i g))) = 0 := by
    rw [← Ideal.map_pow] at h1
    refine (Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) : _ ≤ RingHom.ker (MvPowerSeries.map (σ := Fin n) q)) h1
    rw [Ideal.mem_comap, RingHom.mem_ker, map_C, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  have hq : ∀ i, MvPowerSeries.map (σ := Fin n) q (t i) =
      MvPowerSeries.map (algebraMap O (R ⧸ maximalIdeal R ^ N)) (t0 i : MvPowerSeries (Fin n) O) := fun i => by
    ext d
    rfl
  have h3 := hind (R ⧸ maximalIdeal R ^ N) s
    (fun i => q (W.π (wcomp O W.wt i g)) - if i = j then q (W.π g) else 0) (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sub, hx, map_sum, map_sum, Finset.sum_congr rfl
        (fun i _ => hf' i (W.π (wcomp O W.wt i g)) ⟨_, wcomp_mem O W.wt i g, rfl⟩), map_sub, map_sum] at h2
      simp only [map_mul, hq, hf, map_C] at h2
      simp only [map_sub, mul_sub, Finset.sum_sub_distrib, apply_ite C, map_zero, mul_ite, mul_zero,
        Finset.sum_ite_eq', if_pos hjs]
      rw [← neg_eq_zero, neg_sub]
      exact h2) j hjs
  simp only [if_true] at h3
  rwa [← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogOfStable
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem hos_expand {O S σ : Type} [CommRing O] [CommRing S] [Algebra O S] [Finite σ]
    (N : ℕ) (D : Finset (σ →₀ ℕ)) (hD : ∀ d, d ∈ D ↔ d.degree < N)
    (g : MvPowerSeries σ O →ₐ[O] S) (J : Ideal S) (hg : ∀ s, g (MvPowerSeries.X s) ∈ J) (hJ : J ^ N = ⊥)
    (y : MvPowerSeries σ O) :
    g y = ∑ d ∈ D, algebraMap O S (coeff d y) * d.prod fun s k => g (MvPowerSeries.X s) ^ k := by
  classical
  have h1 := GlobalTheory.algHom_sub_aeval_truncTotal_mem g hg N y
  rw [hJ, Ideal.mem_bot, sub_eq_zero] at h1
  rw [h1]
  have ht : truncTotal N y = ∑ d ∈ D, MvPolynomial.monomial d (coeff d y) := by
    ext d
    rw [MvPolynomial.coeff_sum, coeff_truncTotal_eq_ite]
    simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', hD]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ht, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.aeval_monomial]

private theorem hos_prod {S σ X : Type} [CommRing S] [AddCommGroup X] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (a : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun s k => ((t (Multiplicative.ofAdd (wt s)) : S) * a s) ^ k) =
      t (Multiplicative.ofAdd (Finsupp.weight wt d)) * d.prod fun s k => a s ^ k := by
  classical
  unfold Finsupp.prod
  simp only [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum, ofAdd_sum, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]

private theorem hos_art {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {S : Type} [CommRing S] [Algebra O S] [IsCO O S] {σ : Type} [Finite σ] (wt : σ → X)
    (p : MvPowerSeries σ O →ₐ[O] S) (N : ℕ) (hJ : maximalIdeal S ^ N = ⊥)
    (hp : ∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal S) (x : MvPowerSeries σ O)
    (H : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (i : S →ₐ[O] R')
      (t : Multiplicative X →* R'ˣ), (∀ j, res O R' (t j) = 1) →
      ∀ f' : MvPowerSeries σ O →ₐ[O] R',
        (∀ s, f' (MvPowerSeries.X s) = t (Multiplicative.ofAdd (wt s)) * i (p (MvPowerSeries.X s))) → f' x = 0)
    (j : X) : p (wcomp O wt j x) = 0 := by
  classical
  obtain ⟨n, t, ht1, ht2⟩ := tchar O X
  haveI : IsCO O (MvPowerSeries (Fin n) S) := co_mvps O S (Fin n)
  let i : S →ₐ[O] MvPowerSeries (Fin n) S := IsScalarTower.toAlgHom O S (MvPowerSeries (Fin n) S)
  have hi : ∀ a, i a = MvPowerSeries.C a := fun a => rfl
  let t' : Multiplicative X →* (MvPowerSeries (Fin n) S)ˣ :=
    (Units.map (MvPowerSeries.map (algebraMap O S)).toMonoidHom).comp t
  have ht' : ∀ k, res O (MvPowerSeries (Fin n) S) (t' k) = 1 := by
    intro k
    rw [← sub_eq_zero, ← map_one (res O (MvPowerSeries (Fin n) S)), ← map_sub, res_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    have hc : constantCoeff ((t' k : MvPowerSeries (Fin n) S) - 1) = 0 := by
      show constantCoeff (MvPowerSeries.map (algebraMap O S) (t k : MvPowerSeries (Fin n) O) - 1) = 0
      rw [map_sub, MvPowerSeries.constantCoeff_map, ht1, map_one, map_one, sub_self]
    rw [hc]
    exact not_isUnit_zero
  have hJm : Ideal.map i (maximalIdeal S) ≤ maximalIdeal (MvPowerSeries (Fin n) S) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    show i a ∈ maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, hi,
      MvPowerSeries.constantCoeff_C]
    exact (IsLocalRing.mem_maximalIdeal _).1 ha
  let e : σ → MvPowerSeries (Fin n) S := fun s =>
    (t' (Multiplicative.ofAdd (wt s)) : MvPowerSeries (Fin n) S) * i (p (MvPowerSeries.X s))
  have he : ∀ s, e s ∈ Ideal.map i (maximalIdeal S) := fun s =>
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hp s))
  haveI : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) S)) (MvPowerSeries (Fin n) S) :=
    IsCO.complete (O := O)
  let f' := GlobalTheory.mvEvalAdic O (maximalIdeal (MvPowerSeries (Fin n) S)) e (fun s => hJm (he s))
  have hf'X : ∀ s, f' (MvPowerSeries.X s) =
      t' (Multiplicative.ofAdd (wt s)) * i (p (MvPowerSeries.X s)) := fun s =>
    GlobalTheory.mvEvalAdic_X _ _ _ s
  have h0 : f' x = 0 := H _ i t' ht' f' hf'X
  have hJN : Ideal.map i (maximalIdeal S) ^ N = ⊥ := by
    rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have hf'J : ∀ s, f' (MvPowerSeries.X s) ∈ Ideal.map i (maximalIdeal S) := fun s => by
    rw [hf'X]
    exact he s
  let D : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_lt N).toFinset
  have hD : ∀ d, d ∈ D ↔ d.degree < N := fun d => by simp [D]
  have E1 := hos_expand N D hD f' (Ideal.map i (maximalIdeal S)) hf'J hJN x
  let T : (σ →₀ ℕ) → S := fun d =>
    algebraMap O S (coeff d x) * d.prod fun s k => p (MvPowerSeries.X s) ^ k
  have hT : ∀ k, p (wcomp O wt k x) = ∑ d ∈ D, if Finsupp.weight wt d = k then T d else 0 := by
    intro k
    rw [hos_expand N D hD p (maximalIdeal S) hp hJ]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coeff_wcomp]
    split_ifs <;> simp [T]
  have hE : f' x = ∑ d ∈ D,
      (t' (Multiplicative.ofAdd (Finsupp.weight wt d)) : MvPowerSeries (Fin n) S) * i (T d) := by
    rw [E1]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hf'X]
    have hp' := hos_prod wt t' (fun s => i (p (MvPowerSeries.X s))) d
    beta_reduce at hp'
    rw [hp']
    simp only [T, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]
    ring
  let s : Finset X := D.image (Finsupp.weight wt)
  have hz : ∀ k ∈ s, p (wcomp O wt k x) = 0 := by
    refine ht2 S s (fun k => p (wcomp O wt k x)) ?_
    calc _ = ∑ k ∈ s, (t' (Multiplicative.ofAdd k) : MvPowerSeries (Fin n) S) *
          i (p (wcomp O wt k x)) := Finset.sum_congr rfl fun k _ => by rw [hi]; rfl
      _ = ∑ k ∈ s, ∑ d ∈ D, if Finsupp.weight wt d = k then
          (t' (Multiplicative.ofAdd k) : MvPowerSeries (Fin n) S) * i (T d) else 0 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [hT, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          split_ifs <;> simp
      _ = ∑ d ∈ D, ∑ k ∈ s, if Finsupp.weight wt d = k then
          (t' (Multiplicative.ofAdd k) : MvPowerSeries (Fin n) S) * i (T d) else 0 :=
          Finset.sum_comm
      _ = f' x := by
          rw [hE]
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ hd)]
      _ = 0 := h0
  by_cases hj : j ∈ s
  · exact hz j hj
  · rw [hT]
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    intro h
    exact hj (h ▸ Finset.mem_image_of_mem _ hd)

theorem UpperTheory.V.Alg.homog_of_stable :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : Type) [Finite σ] (wt : σ → X) (π : MvPowerSeries σ O →ₐ[O] R), (∀ s, π (MvPowerSeries.X s) ∈ maximalIdeal R) →
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : MvPowerSeries σ O →ₐ[O] R') (t : Multiplicative X →* R'ˣ), (∀ j, res O R' (t j) = 1) → (∀ x, π x = 0 → f x = 0) →
        ∀ f' : MvPowerSeries σ O →ₐ[O] R', (∀ s, f' (MvPowerSeries.X s) = t (Multiplicative.ofAdd (wt s)) * f (MvPowerSeries.X s)) → ∀ x, π x = 0 → f' x = 0) →
      IsHomog O wt (RingHom.ker π) := by
  intro O _ _ _ _ X _ _ _ R _ _ _ σ _ wt π hπ hstab
  intro x hx j
  have hx' : π x = 0 := hx
  show π (wcomp O wt j x) = 0
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow (maximalIdeal R)
  intro N
  rw [sub_zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ N) ?_
  obtain ⟨I, hI⟩ : ∃ I : Ideal R, I = maximalIdeal R ^ (N + 1) := ⟨_, rfl⟩
  rw [← hI]
  have hIm : I ≤ maximalIdeal R := hI ▸ Ideal.pow_le_self (Nat.succ_ne_zero N)
  have hItop : I ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ hIm))
  haveI : Nontrivial (R ⧸ I) := by
    refine ⟨⟨0, 1, fun h => hItop ((Ideal.eq_top_iff_one _).2 ?_)⟩⟩
    rw [← map_one (Ideal.Quotient.mk I)] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h.symm
  let q : R →ₐ[O] R ⧸ I := Ideal.Quotient.mkₐ O I
  haveI : IsCO O (R ⧸ I) := co_quot O R (R ⧸ I) q (Ideal.Quotient.mkₐ_surjective O I)
  have hmap : ∀ r ∈ maximalIdeal R, q r ∈ maximalIdeal (R ⧸ I) := by
    intro r hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (R ⧸ I)ˣ) : R ⧸ I)
    have hrv : r * v - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
      show q r * _ = 1
      rw [← hu, Units.mul_inv]
    apply (maximalIdeal.isMaximal R).ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 := Ideal.sub_mem _ (Ideal.mul_mem_right v _ hr) (hIm hrv)
    simpa using h1
  have hle : maximalIdeal (R ⧸ I) ≤ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) := by
    intro y hy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.mem_map_of_mem
    by_contra hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
    exact (IsLocalRing.mem_maximalIdeal _).1 hy (hr.map _)
  have hJ : maximalIdeal (R ⧸ I) ^ (N + 1) = ⊥ := by
    rw [eq_bot_iff]
    calc maximalIdeal (R ⧸ I) ^ (N + 1)
        ≤ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) ^ (N + 1) := Ideal.pow_right_mono hle _
      _ = Ideal.map (Ideal.Quotient.mk I) I := by rw [← Ideal.map_pow, hI]
      _ = ⊥ := Ideal.map_quotient_self I
      _ ≤ ⊥ := le_rfl
  have hp : ∀ s, (q.comp π) (MvPowerSeries.X s) ∈ maximalIdeal (R ⧸ I) := fun s =>
    hmap _ (hπ s)
  have key := hos_art wt (q.comp π) (N + 1) hJ hp x
    (fun R' _ _ _ i t ht f' hf' =>
      hstab R' ((i.comp q).comp π) t ht (fun y hy => by simp [hy]) f' (fun s => (hf' s).trans rfl) x hx') j
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at key
  exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresNew
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pres_new_low {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S)
    (F : MvPowerSeries σ R →+* S) (hF : ∀ s, F (X s) ∈ m) (n : ℕ) (g : MvPowerSeries σ R) :
    F g - F (truncTotal n g : MvPolynomial σ R) ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), F (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  have h := key (e (g - (truncTotal n g : MvPolynomial σ R))) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    have : truncTotal n (g - ((truncTotal n g : MvPolynomial σ R) : MvPowerSeries σ R)) = 0 := by
      ext x
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hx
      · rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx]; simp
      · simp
    rw [this]
    rfl)
  rwa [AlgEquiv.symm_apply_apply, map_sub] at h

private theorem pres_new_coeff {O σ : Type} [CommRing O] [IsLocalRing O] (N : ℕ) :
    ∀ h ∈ maximalIdeal (MvPowerSeries σ O) ^ N, ∀ a : σ →₀ ℕ,
      coeff a h ∈ maximalIdeal O ^ (N - a.degree) :=
  _root_.UpperTheory.Reformulated.B.PreservedCoefficient.pres_new_coeff N

private theorem pres_new_wcomp {O σ X : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] (wt : σ → X)
    {i : X} (j : X) {h : MvPowerSeries σ O} (hh : h ∈ wtPart O wt i) :
    wcomp O wt j h = if i = j then h else 0 := by
  ext a
  rw [coeff_wcomp]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    split_ifs with h1
    · rfl
    · exact (hh a h1).symm
  · rw [if_neg hij]
    split_ifs with h1
    · rw [map_zero]
      exact hh a (h1 ▸ Ne.symm hij)
    · simp

private theorem pres_new_mono {O σ τ Y : Type} [CommRing O] [AddCommGroup Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s))
    (u : τ →₀ ℕ) : Φ (monomial u 1) ∈ wtPart O w (Finsupp.weight wt u) := by
  induction u using Finsupp.induction_linear with
  | zero => simpa using one_mem_wtPart O w
  | add u v hu hv =>
    have : (monomial (u + v) 1 : MvPowerSeries τ O) = monomial u 1 * monomial v 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [this, map_mul, map_add (f := _)]
    exact mul_mem_wtPart O w hu hv
  | single s n =>
    rw [← X_pow_eq, map_pow, Finsupp.weight_single]
    exact SetLike.pow_mem_graded n (hΦ s)

private theorem pres_new_poly {O σ τ Y : Type} [CommRing O] [AddCommGroup Y] [DecidableEq Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s)) (j : Y)
    (p : MvPolynomial τ O) : Φ (wcomp O wt j p) = wcomp O w j (Φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    have : ((MvPolynomial.monomial u c : MvPolynomial τ O) : MvPowerSeries τ O) = c • monomial u 1 := by
      rw [MvPolynomial.coe_monomial, ← map_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, map_smul, map_smul, pres_new_wcomp w j (pres_new_mono wt w Φ hΦ u),
      pres_new_wcomp wt j (h := monomial u 1) (pres_new_mono wt wt (AlgHom.id O _) (X_mem_wtPart O wt) u)]
    split_ifs <;> simp
  | add p q hp hq => simp only [MvPolynomial.coe_add, map_add (f := _), hp, hq]

private theorem pres_new_comm {O σ τ Y : Type} [CommRing O] [IsLocalRing O] [IsHausdorff (maximalIdeal O) O]
    [Finite τ] [AddCommGroup Y] [DecidableEq Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s))
    (hm : ∀ s, Φ (X s) ∈ maximalIdeal (MvPowerSeries σ O)) (j : Y)
    (g : MvPowerSeries τ O) : Φ (wcomp O wt j g) = wcomp O w j (Φ g) := by
  have hl := pres_new_low (maximalIdeal (MvPowerSeries σ O)) (Φ : MvPowerSeries τ O →+* MvPowerSeries σ O) hm
  ext a
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := maximalIdeal O) inferInstance _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have h1 := pres_new_coeff _ _ (hl (k + a.degree) g) a
  have h2 := pres_new_coeff _ _ (hl (k + a.degree) (wcomp O wt j g)) a
  have h3 : ((truncTotal (k + a.degree) (wcomp O wt j g) : MvPolynomial τ O) : MvPowerSeries τ O) =
      wcomp O wt j (truncTotal (k + a.degree) g : MvPolynomial τ O) := by
    ext b
    simp only [coeff_wcomp, MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite]
    split_ifs <;> rfl
  rw [h3] at h2
  simp only [RingHom.coe_coe, Nat.add_sub_cancel, map_sub] at h1 h2
  rw [pres_new_poly wt w Φ hΦ] at h2
  rw [coeff_wcomp] at h2 ⊢
  split_ifs at h2 ⊢
  · simpa using sub_mem h2 h1
  · exact h2

theorem UpperTheory.V.Alg.pres_new :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (τ : Type) [Fintype τ] (wt : τ → X) (z : τ → R), (∀ s, z s ∈ maximalIdeal R ∧ z s ∈ W.part (wt s)) →
      maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 →
      ∃ (W' : WPres O X R) (e : τ ≃ W'.σ), ∀ s, W'.z (e s) = z s ∧ W'.wt (e s) = wt s := by
  intro O _ _ _ _ Y _ _ _ _ R _ _ _ W _ τ _ wt z hz hgen
  haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O W.σ
  haveI : IsCO O (MvPowerSeries τ O) := co_mvps O O τ
  choose f hf hfz using fun s => (hz s).2
  have hfz' : ∀ s, W.π (f s) = z s := hfz
  have hfm : ∀ s, f s ∈ maximalIdeal (MvPowerSeries W.σ O) := fun s hu =>
    (hz s).1 (hfz' s ▸ hu.map W.π)
  obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := co_ev O O (MvPowerSeries W.σ O) τ (Algebra.ofId _ _) f hfm
  have hF : ∀ s, (W.π.comp Φ) (X s) = z s := fun s => by rw [AlgHom.comp_apply, hΦ, hfz']
  refine ⟨⟨τ, wt, W.π.comp Φ, ?_, ?_⟩, Equiv.refl _, fun s => ⟨hF s, rfl⟩⟩
  · refine co_surj O _ R _ (hgen.trans (sup_le_sup_right (sup_le ?_ ?_) _))
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      rw [← hF s]
      refine Ideal.mem_map_of_mem _ fun hu => ?_
      simpa using isUnit_constantCoeff _ hu
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, ← (W.π.comp Φ).commutes]
      refine Ideal.mem_map_of_mem _ fun hu => hc ?_
      simpa [MvPowerSeries.algebraMap_apply] using isUnit_constantCoeff _ hu
  · intro g hg j
    show W.π (Φ _) = 0
    rw [pres_new_comm wt W.wt Φ (fun s => hΦ s ▸ hf s) (fun s => hΦ s ▸ hfm s)]
    exact W.homog _ hg j
end

