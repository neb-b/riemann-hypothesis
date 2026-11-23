module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.AdSurj
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.adSurj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (n : ℕ) (g : UA L n), ∃ x : ∀ v : Pl (Lp L), Matrix (Fin n) (Fin n) (Lsq (Kv v) (cv v R.Δ)), (∀ v, star (x v) * x v = 1) ∧ (∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) (x v i j)) ∧ ∀ w, mL w g = (x (un w)).map (R.ρ _ w rfl) := by
  intro L _ _ _ R n g
  classical
  let G : Matrix (Fin n) (Fin n) (Ad L) := (g.1 : Matrix (Fin n) (Fin n) (Ad L))
  let A : Matrix (Fin n) (Fin n) (Af L) := G.map (pFin L)
  have hU : ∀ i j, ∑ k, cjF (L := L) (A k i) * A k j = (1 : Matrix (Fin n) (Fin n) (Af L)) i j := by
    have hG : Formalism.UG.cT (conjAd L) G * 1 * G = 1 := g.2
    have h1 := congrArg (pFin L).mapMatrix hG
    rw [map_one, map_mul, map_mul, map_one, Matrix.mul_one] at h1
    intro i j
    have h2 := congrFun (congrFun h1 i) j
    rw [Matrix.mul_apply] at h2
    exact h2
  have hx : ∀ v i j, ∃ x : Lsq (Kv v) (cv v R.Δ), ∀ w h, R.ρ v w h x = pLoc L w (A i j) :=
    fun v i j => R.ρ_surj v (A i j)
  choose x hx using hx
  refine ⟨fun v => Matrix.of (x v), ?_, ?_, ?_⟩
  · intro v
    ext1 i j
    rw [← sub_eq_zero]
    apply R.ρ_inj v
    intro w h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, Matrix.mul_apply, map_sum]
    have e1 : ∀ k, R.ρ v w h ((star (Matrix.of (x v))) i k * (Matrix.of (x v)) k j) =
        pLoc L w (cjF (L := L) (A k i) * A k j) := by
      intro k
      rw [map_mul, map_mul, Matrix.star_apply, Matrix.of_apply, Matrix.of_apply,
        R.ρ_star v _ _ (hx v k i) w h, hx v k j w h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun k _ => e1 k, ← map_sum, hU i j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  · have hfin : ∀ i j, {w : Plc L | pLoc L w (A i j) ∉ w.adicCompletionIntegers L}.Finite := by
      intro i j
      exact (A i j).2
    have hall : {w : Plc L | ∃ i j, pLoc L w (A i j) ∉ w.adicCompletionIntegers L}.Finite := by
      have : {w : Plc L | ∃ i j, pLoc L w (A i j) ∉ w.adicCompletionIntegers L} =
          ⋃ i, ⋃ j, {w : Plc L | pLoc L w (A i j) ∉ w.adicCompletionIntegers L} := by
        ext w; simp
      rw [this]
      exact Set.finite_iUnion fun i => Set.finite_iUnion fun j => hfin i j
    have hbad := hall.image (fun w : Plc L => un w)
    rw [Filter.eventually_cofinite]
    refine hbad.subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq, not_forall] at hv
    obtain ⟨i, j, hij⟩ := hv
    have : ¬ ∀ w h, R.ρ v w h (x v i j) ∈ w.adicCompletionIntegers L := fun h => hij ((R.ρ_int v _).2 h)
    simp only [not_forall] at this
    obtain ⟨w, h, hw⟩ := this
    exact ⟨w, ⟨i, j, by rwa [hx v i j w h] at hw⟩, h⟩
  · intro w
    refine Matrix.ext fun i j => ?_
    change mL w g i j = R.ρ _ w rfl (x (un w) i j)
    rw [hx (un w) i j w rfl]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.EvenVal
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.evenVal :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), Dict.Unr L → ∀ v : Pl (Lp L), EvenVal (Ov v) (cv v P.Δ) := by
  intro L _ _ _ P hU v
  have hval : ∀ x : Lp L, Valued.v (cv v x) = v.valuation (Lp L) x := fun x =>
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hδ : P.e QuadraticAlgebra.omega * P.e QuadraticAlgebra.omega = algebraMap (Lp L) L P.Δ := by
    rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero,
      P.e_alg]
  have hδ0 : P.e QuadraticAlgebra.omega ≠ 0 := by
    intro h0
    have h1 : (QuadraticAlgebra.omega : Lsq (Lp L) P.Δ) = 0 := P.e.injective (by rw [h0, map_zero])
    have h2 := congrArg QuadraticAlgebra.im h1
    simp at h2
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hQl.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQm.isPrime, hQ0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := hQl
  have hr : w.asIdeal.ramificationIdx (𝓞 (Lp L)) = 1 := by
    haveI := hU w
    haveI : w.asIdeal.IsPrime := w.isPrime
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 (Lp L)) (p := w.asIdeal)
  have hv := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v w P.Δ
  rw [hr, pow_one, ← hδ, map_mul] at hv
  have hw0 : w.valuation L (P.e QuadraticAlgebra.omega) ≠ 0 := by simpa using hδ0
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer (Lp L)
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  let t : Lp L := π ^ (-WithZero.log (w.valuation L (P.e QuadraticAlgebra.omega)))
  have ht0 : t ≠ 0 := zpow_ne_zero _ hπ0
  have ht : v.valuation (Lp L) t = w.valuation L (P.e QuadraticAlgebra.omega) := by
    simp only [t, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]
    exact WithZero.exp_log hw0
  have hu1 : Valued.v (cv v (P.Δ / t ^ 2)) = 1 := by
    rw [hval, map_div₀, map_pow, ht, hv, sq]
    exact div_self (mul_ne_zero hw0 hw0)
  have hu2 : Valued.v (cv v (P.Δ / t ^ 2)⁻¹) = 1 := by
    rw [hval, map_inv₀, ← hval, hu1, inv_one]
  have hne : P.Δ / t ^ 2 ≠ 0 := div_ne_zero (by
      intro h0
      apply hδ0
      exact mul_self_eq_zero.mp (by rw [hδ, h0, map_zero])) (pow_ne_zero _ ht0)
  refine ⟨⟨⟨cv v (P.Δ / t ^ 2), le_of_eq hu1⟩, ⟨cv v (P.Δ / t ^ 2)⁻¹, le_of_eq hu2⟩, ?_, ?_⟩,
    cv v t, (map_ne_zero (cv v)).2 ht0, ?_⟩
  · apply Subtype.ext
    show cv v (P.Δ / t ^ 2) * cv v (P.Δ / t ^ 2)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  · apply Subtype.ext
    show cv v (P.Δ / t ^ 2)⁻¹ * cv v (P.Δ / t ^ 2) = 1
    rw [← map_mul, inv_mul_cancel₀ hne, map_one]
  · show cv v P.Δ = cv v (P.Δ / t ^ 2) * cv v t ^ 2
    rw [← map_pow, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ ht0)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.ExistsUnitNormQuotientLift
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section H90

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K}

private theorem unit_of_norm (z : Lsq K Δ) (h : QuadraticAlgebra.norm z ≠ 0) :
    ∃ c : (Lsq K Δ)ˣ, (c : Lsq K Δ) = z ∧
      ((c⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) = algebraMap K (Lsq K Δ) (QuadraticAlgebra.norm z)⁻¹ * star z := by
  have h1 : z * (algebraMap K (Lsq K Δ) (QuadraticAlgebra.norm z)⁻¹ * star z) = 1 := by
    rw [mul_left_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← map_mul, inv_mul_cancel₀ h, map_one]
  exact ⟨⟨z, _, h1, by rw [mul_comm]; exact h1⟩, rfl, rfl⟩

private def starO : Lsq K Δ →ₐ[O] Lsq K Δ :=
  { starRingEnd (Lsq K Δ) with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ) r]
      change star (algebraMap K (Lsq K Δ) _) = _
      ext <;> simp }

private theorem int_star {z : Lsq K Δ} (h : IsIntegral O z) : IsIntegral O (star z) :=
  h.map (starO (O := O) (K := K) (Δ := Δ))

private theorem dich [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K] (h2 : IsUnit (2 : O))
    {u : Lsq K Δ} (hu : IsIntegral O u) :
    (∃ v : Oˣ, algebraMap O K v = 2 + 2 * u.re) ∨ (∃ v : Oˣ, algebraMap O K v = 2 - 2 * u.re) := by
  have ht : IsIntegral O (algebraMap K (Lsq K Δ) (2 * u.re)) := by
    have : algebraMap K (Lsq K Δ) (2 * u.re) = u + star u := by
      ext <;> simp <;> ring
    rw [this]
    exact hu.add (int_star hu)
  have ht' : IsIntegral O (2 * u.re) :=
    (isIntegral_algebraMap_iff ).1 ht
  haveI : IsDomain O := (IsFractionRing.injective O K).isDomain (algebraMap O K)
  obtain ⟨τ, hτ⟩ := IsIntegrallyClosed.isIntegral_iff.1 ht'
  have h4 : IsUnit ((2 + τ) + (2 - τ) : O) := by
    have : ((2 + τ) + (2 - τ) : O) = 2 * 2 := by ring
    rw [this]
    exact h2.mul h2
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h4 with h | h
  · left
    exact ⟨h.unit, by simp [hτ, map_ofNat]⟩
  · right
    exact ⟨h.unit, by simp [hτ, map_ofNat]⟩

private theorem int_omega {d : O} (hd : algebraMap O K d = Δ) :
    IsIntegral O (QuadraticAlgebra.omega : Lsq K Δ) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C d, Polynomial.monic_X_pow_sub_C d two_ne_zero, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
    IsScalarTower.algebraMap_apply O K (Lsq K Δ), hd, pow_two,
    QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext <;> simp

private theorem exists_unit_norm_quotient_lift (z u : Lsq K Δ) (hz : z = u * star z) (hn : QuadraticAlgebra.norm z ≠ 0)
    (hi : ∀ [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K], IsUnit (2 : O) →
      (∃ v : Oˣ, algebraMap O K v = Δ) → IsIntegral O u →
        IsIntegral O z ∧ ∃ v : Oˣ, algebraMap O K v = QuadraticAlgebra.norm z) :
    ∃ c : (Lsq K Δ)ˣ, (c : Lsq K Δ) = u * star (c : Lsq K Δ) ∧
      ∀ [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K], IsUnit (2 : O) →
        (∃ v : Oˣ, algebraMap O K v = Δ) → IsIntegral O u →
          IsIntegral O (c : Lsq K Δ) ∧ IsIntegral O ((c⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) := by
  obtain ⟨c, hc, hci⟩ := unit_of_norm z hn
  refine ⟨c, by rw [hc]; exact hz, ?_⟩
  intro _ _ _ h2 hΔ hu
  obtain ⟨hzi, v, hv⟩ := hi h2 hΔ hu
  refine ⟨by rw [hc]; exact hzi, ?_⟩
  rw [hci, ← hv, ← map_units_inv, ← IsScalarTower.algebraMap_apply]
  exact isIntegral_algebraMap.mul (int_star hzi)

private theorem ex_c (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) (u : Lsq K Δ) (hu : u * star u = 1) :
    ∃ c : (Lsq K Δ)ˣ, (c : Lsq K Δ) = u * star (c : Lsq K Δ) ∧
      ∀ [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K], IsUnit (2 : O) →
        (∃ v : Oˣ, algebraMap O K v = Δ) → IsIntegral O u →
          IsIntegral O (c : Lsq K Δ) ∧ IsIntegral O ((c⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) := by
  classical
  have r1 : (1 : Lsq K Δ).re = 1 := rfl
  have i1 : (1 : Lsq K Δ).im = 0 := rfl
  have hN1 : QuadraticAlgebra.norm u = 1 := by
    apply (algebraMap K (Lsq K Δ)).injective
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, hu, map_one]
  have hN := hN1
  rw [QuadraticAlgebra.norm_def] at hN
  by_cases hcase : (2 + 2 * u.re ≠ 0) ∧ ¬ ∃ v : Oˣ, algebraMap O K v = 2 - 2 * u.re
  · have hn : QuadraticAlgebra.norm (1 + u) = 2 + 2 * u.re := by
      rw [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, r1, i1]
      linear_combination hN
    apply exists_unit_norm_quotient_lift (1 + u) u (by rw [star_add, star_one, mul_add, hu]; ring) (by rw [hn]; exact hcase.1)
    intro _ _ _ h2' _ hi
    refine ⟨isIntegral_one.add hi, ?_⟩
    rcases dich h2' hi with ⟨v, hv⟩ | h
    · exact ⟨v, by rw [hn, hv]⟩
    · exact absurd h hcase.2
  · have hsω : star (QuadraticAlgebra.omega : Lsq K Δ) = -QuadraticAlgebra.omega := by
      ext <;> simp
    have hn : QuadraticAlgebra.norm ((1 - u) * QuadraticAlgebra.omega)
        = (2 - 2 * u.re) * (-Δ) := by
      rw [map_mul, QuadraticAlgebra.norm_def (1 - u), QuadraticAlgebra.norm_def QuadraticAlgebra.omega,
        QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, r1, i1, QuadraticAlgebra.omega_re,
        QuadraticAlgebra.omega_im]
      linear_combination (-Δ) * hN
    have hne : 2 - 2 * u.re ≠ 0 := by
      intro h0
      apply hcase
      refine ⟨fun h1 => h2 ?_, ?_⟩
      · have h4 : (2 : K) * 2 = 0 := by linear_combination h0 + h1
        exact mul_self_eq_zero.mp h4
      · rintro ⟨v, hv⟩
        rw [h0] at hv
        exact (v.isUnit.map (algebraMap O K)).ne_zero hv
    apply exists_unit_norm_quotient_lift ((1 - u) * QuadraticAlgebra.omega) u
      (by
        rw [star_mul', star_sub, star_one, hsω]
        linear_combination (-QuadraticAlgebra.omega) * hu)
      (by rw [hn]; exact mul_ne_zero hne (neg_ne_zero.mpr hΔ))
    intro _ _ _ h2' hΔ' hi
    obtain ⟨d, hd⟩ := hΔ'
    refine ⟨(isIntegral_one.sub hi).mul (int_omega hd), ?_⟩
    obtain ⟨w, hw⟩ : ∃ w : Oˣ, algebraMap O K w = 2 - 2 * u.re := by
      by_cases hB : ∃ w : Oˣ, algebraMap O K w = 2 - 2 * u.re
      · exact hB
      · have hA : 2 + 2 * u.re = 0 := by
          by_contra hA
          exact hcase ⟨hA, hB⟩
        refine ⟨h2'.unit * h2'.unit, ?_⟩
        rw [Units.val_mul, IsUnit.unit_spec, map_mul, map_ofNat]
        linear_combination hA
    exact ⟨-(w * d), by rw [hn, ← hw, ← hd]; simp⟩

private theorem mem_range (g : GL (Fin 2) (Lsq K Δ)) (h1 : ∀ i j, IsIntegral O (g.1 i j))
    (h2 : ∀ i j, IsIntegral O (g.inv i j)) :
    g ∈ (GeneralLinearGroup.map ((integralClosure O (Lsq K Δ)).val :
      integralClosure O (Lsq K Δ) →+* Lsq K Δ)).range := by
  let f : integralClosure O (Lsq K Δ) →+* Lsq K Δ := (integralClosure O (Lsq K Δ)).val
  let F := RingHom.mapMatrix (m := Fin 2) f
  let A : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) :=
    Matrix.of fun i j => ⟨g.1 i j, h1 i j⟩
  let B : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) :=
    Matrix.of fun i j => ⟨g.inv i j, h2 i j⟩
  have hA : F A = g.1 := Matrix.ext fun i j => rfl
  have hB : F B = g.inv := Matrix.ext fun i j => rfl
  have inj : Function.Injective F := fun M N e =>
    Matrix.map_injective Subtype.val_injective e
  have hAB : A * B = 1 := inj (by rw [map_mul, hA, hB, g.val_inv, map_one])
  have hBA : B * A = 1 := inj (by rw [map_mul, hA, hB, g.inv_val, map_one])
  refine MonoidHom.mem_range.mpr ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

private theorem conj_two {A : Type} [CommRing A] (m : Matrix (Fin 2) (Fin 2) A) :
    !![0, -1; 1, 0] * m * !![0, 1; -1, 0] = !![m 1 1, -m 1 0; -m 0 1, m 0 0] := by
  rw [Matrix.eta_fin_two m]
  simp [Matrix.mul_fin_two]

end H90

theorem UpperTheory.V.Z.Sym.Dict.Br.h90 :
    ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (Δ : K), (2 : K) ≠ 0 → Δ ≠ 0 → ∀ x : Matrix (Fin 2) (Fin 2) (Lsq K Δ), star x * x = 1 → ∃ (y : DX Δ) (c : (Lsq K Δ)ˣ), x = (c : Lsq K Δ) • mt y ∧ (x = 1 → y = 1) ∧ (∀ [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K], IsUnit (2 : O) → (∃ u : Oˣ, algebraMap O K u = Δ) → (∀ i j, IsIntegral O (x i j)) → y ∈ KD Δ O) := by
  intro O K _ _ _ Δ h2 hΔ x hx
  by_cases hx1 : x = 1
  · refine ⟨1, 1, ?_, fun _ => rfl, fun _ _ _ => one_mem _⟩
    subst hx1
    simp [Glob.mt]
  set u := x.det with hu_def
  have hxx : x * star x = 1 := mul_eq_one_comm.mp hx
  have hu : u * star u = 1 := by
    have e := congrArg Matrix.det hx
    rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose,
      Matrix.det_conjTranspose] at e
    rw [mul_comm]
    exact e
  obtain ⟨c, hc, hci⟩ := ex_c (O := O) h2 hΔ u hu
  set s : Lsq K Δ := ((c⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) with hs_def
  have hsc : s * c = 1 := Units.inv_mul c
  have hcs : (c : Lsq K Δ) * s = 1 := Units.mul_inv c
  have hss : star s = s * u := by
    have e2 : star s * star (c : Lsq K Δ) = 1 := by rw [← star_mul', hsc, star_one]
    linear_combination (-star s) * hsc + (u * s) * e2 + (star s * s) * hc
  have hM : u • star x = Matrix.adjugate x := by
    calc u • star x = star x * (u • 1) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = star x * (x * Matrix.adjugate x) := by rw [Matrix.mul_adjugate]
      _ = Matrix.adjugate x := by rw [← Matrix.mul_assoc, hx, Matrix.one_mul]
  have r : ∀ i j, u * star (x j i) = Matrix.adjugate x i j := fun i j => by
    have e := congrFun (congrFun hM i) j
    simpa [Matrix.star_apply] using e
  have r00 := r 0 0
  have r01 := r 0 1
  have r10 := r 1 0
  have r11 := r 1 1
  simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at r00 r01 r10 r11
  let Y : GL (Fin 2) (Lsq K Δ) :=
    ⟨s • x, (c : Lsq K Δ) • star x,
      by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hxx, hsc, one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx, hcs, one_smul]⟩
  have hY : Y ∈ DX Δ := by
    show GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) Y
      = MulEquiv.toMonoidHom (MulAut.conj (wJ Δ)⁻¹) Y
    apply Units.ext
    show (starRingEnd (Lsq K Δ)).mapMatrix (s • x) = !![0, -1; 1, 0] * (s • x) * !![0, 1; -1, 0]
    rw [conj_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show star (s * x 0 0) = s * x 1 1
      rw [star_mul']
      linear_combination (star (x 0 0)) * hss + s * r00
    · show star (s * x 0 1) = -(s * x 1 0)
      rw [star_mul']
      linear_combination (star (x 0 1)) * hss + s * r10
    · show star (s * x 1 0) = -(s * x 0 1)
      rw [star_mul']
      linear_combination (star (x 1 0)) * hss + s * r01
    · show star (s * x 1 1) = s * x 0 0
      rw [star_mul']
      linear_combination (star (x 1 1)) * hss + s * r11
  refine ⟨⟨Y, hY⟩, c, ?_, fun h => absurd h hx1, ?_⟩
  · show x = (c : Lsq K Δ) • (s • x)
    rw [smul_smul, hcs, one_smul]
  · intro _ _ _ h2' hΔ' hint
    have hui : IsIntegral O u := by
      rw [hu_def, Matrix.det_fin_two]
      exact ((hint 0 0).mul (hint 1 1)).sub ((hint 0 1).mul (hint 1 0))
    obtain ⟨hci1, hci2⟩ := hci h2' hΔ' hui
    rw [KD, Subgroup.mem_subgroupOf]
    exact mem_range Y (fun i j => hci2.mul (hint i j)) (fun i j => hci1.mul (int_star (hint j i)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.GlobEx
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.globEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], ∃ (Δ : Lp L) (e : Lsq (Lp L) Δ ≃+* L), (∀ x, e (star x) = IsCMField.complexConj L (e x)) ∧ (∀ a : Lp L, e (algebraMap _ _ a) = algebraMap (Lp L) L a) ∧ ∀ σ : Lp L →+* ℝ, σ Δ < 0 :=
  _root_.UpperTheory.Reformulated.B.Qh37.globEx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IntsOv
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mem_adicCompletionIntegers_iff_valuation_le_one (F : Type) [Field F] [NumberField F] (v : Pl F) (x : Kv v) :
    x ∈ v.adicCompletionIntegers F ↔ valuation (Kv v) x ≤ 1 := by
  rw [← (valuation (Kv v)).vle_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  change _ ↔ Valued.v x ≤ Valued.v (1 : Kv v)
  rw [map_one]

theorem UpperTheory.V.Z.Sym.Dict.Br.intsOv :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl F), Sig.IsInts (Kv v) (Ov v) ∧ ∀ x : Kv v, x ∈ v.adicCompletionIntegers F ↔ valuation (Kv v) x ≤ 1 := by
  intro F _ _ v
  refine ⟨⟨Subtype.val_injective, fun x => ?_⟩, mem_adicCompletionIntegers_iff_valuation_le_one F v⟩
  rw [← mem_adicCompletionIntegers_iff_valuation_le_one F v x]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.LocBase
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.locBase :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl F), IsFractionRing (Ov v) (Kv v) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (Ov v)) (Ov v) ∧ Finite (IsLocalRing.ResidueField (Ov v)) ∧ ((2 : 𝓞 F) ∉ v.asIdeal → IsUnit (2 : Ov v)) := by
  intro F _ _ v
  refine ⟨inferInstance, GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v,
    GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v, fun h => ?_⟩
  have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h
  rwa [map_ofNat] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.PhiEx
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.phiEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], ∃ φ : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → Kv v →+* Kw w, (∀ v w h, Continuous (φ v w h)) ∧ ∀ v w h (a : Lp L), φ v w h (cv v a) = algebraMap L (Kw w) (algebraMap (Lp L) L a) := by
  intro L _ _ _
  have hlo : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → w.asIdeal.LiesOver v.asIdeal := by
    intro v w h
    subst h
    exact ⟨rfl⟩
  refine ⟨fun v w h => @GroundTheory.Global.SemiLocal.completionMap _ _ _ _ _ _ _ v w (hlo v w h), ?_, ?_⟩
  · intro v w h
    exact @GroundTheory.Global.SemiLocal.continuous_completionMap _ _ _ _ _ _ _ v w (hlo v w h)
  · intro v w h a
    have e := @GroundTheory.Global.SemiLocal.completionMap_algebraMap _ _ _ _ _ _ _ v w (hlo v w h) a
    simp only [cv]
    rw [e]
    exact IsScalarTower.algebraMap_apply (Lp L) L _ a
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoGlob
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoGlob :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v w h (x : Lsq (Lp L) P.Δ), P.rho v w h (lmap (cv v) P.Δ x) = algebraMap L (Kw w) (P.e x) := by
  intro L _ _ _ P v w h x
  have hx : x = algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.re
      + algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.im * QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
  have lhs : P.rho v w h (lmap (cv v) P.Δ x)
      = P.φ v w h (cv v x.re) + P.φ v w h (cv v x.im) * P.rt w := rfl
  rw [lhs, P.φ_alg, P.φ_alg, Pre.rt]
  conv_rhs => rw [hx]
  rw [map_add (f := _), map_mul, P.e_alg, P.e_alg, map_add (f := _), map_mul]
end

