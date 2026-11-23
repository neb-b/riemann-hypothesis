module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOne
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

noncomputable section

namespace GlobalTheory.QNorm

theorem exists_mem_only (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ a ∈ v.asIdeal ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → a ∉ w.asIdeal := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) :=
    mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ h, pow_mem hv h⟩ = 1 := by
    have : (⟨v.asIdeal ^ h, pow_mem hv h⟩ : nonZeroDivisors (Ideal (𝓞 F))) =
        ⟨v.asIdeal, hv⟩ ^ h := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff _).1 h1
  have ha' : v.asIdeal ^ h = Ideal.span {a} := ha
  refine ⟨a, ?_, ?_, ?_⟩
  · rintro rfl
    have : v.asIdeal ^ h = ⊥ := by rw [ha']; simp
    exact pow_ne_zero h v.ne_bot this
  · exact Ideal.pow_le_self hpos (ha' ▸ Ideal.mem_span_singleton_self a)
  · intro w hw haw
    have hle : v.asIdeal ^ h ≤ w.asIdeal := by
      rw [ha']; exact (Ideal.span_singleton_le_iff_mem _).2 haw
    have := w.isPrime
    have h2 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le hle
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2).symm)

theorem sUnits_rank :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
      Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by
  intro F _ _ S
  classical
  have hunit : ∀ (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)),
      v.valuation F (algebraMap (𝓞 F) F u) = 1 := by
    intro u v
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hu
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu u.isUnit)
  let f0 : (𝓞 F)ˣ →* sUnits F S :=
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom).codRestrict _
      (fun u => (mem_sUnits F S _).2 fun v _ => hunit u v)
  let f : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive (sUnits F S) :=
    (MonoidHom.toAdditive f0).toIntLinearMap
  let g0 : Additive (sUnits F S) →+ (S → ℤ) :=
    AddMonoidHom.mk' (fun x v => WithZero.log
      ((v : HeightOneSpectrum (𝓞 F)).valuation F (((Additive.toMul x : sUnits F S) : Fˣ) : F))) (by
      intro a b
      funext v
      simp only [toMul_add, Subgroup.coe_mul, Units.val_mul, map_mul, Pi.add_apply]
      exact WithZero.log_mul (by simp) (by simp))
  let g := g0.toIntLinearMap
  have hker : LinearMap.ker g = LinearMap.range f := by
    apply le_antisymm
    · intro x hx
      set y : Fˣ := ((Additive.toMul x : sUnits F S) : Fˣ) with hy
      have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y : F) = 1 := by
        intro v
        by_cases hv : v ∈ S
        · have h : WithZero.log (v.valuation F (y : F)) = 0 :=
            congrFun (LinearMap.mem_ker.1 hx) ⟨v, hv⟩
          have hne : v.valuation F (y : F) ≠ 0 := by simp
          rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
        · exact (mem_sUnits F S _).1 (Additive.toMul x).2 v hv
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)
        (fun v => (hall v).le)
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)⁻¹
        (fun v => by rw [map_inv₀, hall v, inv_one])
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (𝓞 F) F
        rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ y.ne_zero]
      refine ⟨Additive.ofMul (Units.mkOfMulEqOne a b hab), ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      exact ha
    · rintro _ ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      funext v
      change WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F
        (algebraMap (𝓞 F) F (Additive.toMul u : (𝓞 F)ˣ))) = 0
      rw [hunit, WithZero.log_one]
  have hinj : Function.Injective f := by
    intro a b hab
    apply Additive.toMul.injective
    apply Units.ext
    apply IsFractionRing.injective (𝓞 F) F
    exact congrArg (fun x : Additive (sUnits F S) => (((Additive.toMul x : sUnits F S) : Fˣ) : F)) hab
  have hfin : Module.Finite ℤ (Additive (sUnits F S)) :=
    Module.Finite.iff_addGroup_fg.2 (GroupFG.iff_add_fg.1 (sUnits_fg F S))
  have hrange : Module.finrank ℤ (LinearMap.range g) = S.card := by
    apply le_antisymm
    · refine (Submodule.finrank_le _).trans ?_
      simp
    · have key : ∀ v : S, ∃ c : ℤ, c ≠ 0 ∧ Pi.single v c ∈ LinearMap.range g := by
        intro v
        obtain ⟨a, ha0, hav, haw⟩ := exists_mem_only F v
        have ha0' : algebraMap (𝓞 F) F a ≠ 0 := by simpa using ha0
        have hw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
            w.valuation F (algebraMap (𝓞 F) F a) = 1 := fun w hw =>
          (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (haw w hw)
        refine ⟨WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a)),
          ?_, Additive.ofMul ⟨Units.mk0 _ ha0', (mem_sUnits F S _).2 fun w hwS =>
            hw w (fun e => hwS (e ▸ v.2))⟩, ?_⟩
        · intro h0
          have hne : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) ≠ 0 := by
            simpa using ha0
          have h1 : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) = 1 := by
            rw [← WithZero.exp_log hne, h0, WithZero.exp_zero]
          exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 h1 hav
        · funext w
          change WithZero.log ((w : HeightOneSpectrum (𝓞 F)).valuation F
            (algebraMap (𝓞 F) F a)) = _
          by_cases hwv : w = v
          · subst hwv; simp
          · rw [Pi.single_eq_of_ne hwv, hw w (fun e => hwv (Subtype.ext e)), WithZero.log_one]
      choose c hc0 hc using key
      have hli : LinearIndependent ℤ (fun v : S => (⟨Pi.single v (c v), hc v⟩ : LinearMap.range g)) :=
        LinearIndependent.of_comp (LinearMap.range g).subtype
          (Pi.linearIndependent_single_of_ne_zero hc0)
      simpa using hli.fintype_card_le_finrank
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
  rw [g.quotKerEquivRange.finrank_eq, hrange, hker, LinearMap.finrank_range_of_inj hinj,
    NumberField.Units.finrank_eq, NumberField.Units.rank] at h1
  have h2 : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  omega

end GlobalTheory.QNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90BaseChange
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isUnit_of_forall_maximal {K A : Type} [Field K] [Infinite K] [CommRing A]
    [Algebra K A] [IsArtinianRing A] (Θ : A →ₗ[K] A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ c, Θ c ∉ 𝔪) : ∃ c, IsUnit (Θ c) := by
  classical
  have hfin := IsArtinianRing.setOf_isMaximal_finite A
  let s : Finset (Subspace K A) :=
    hfin.toFinset.image fun 𝔪 => (𝔪.restrictScalars K).comap Θ
  have hs : ⊤ ∉ s := by
    intro ht
    obtain ⟨𝔪, hm, he⟩ := Finset.mem_image.1 ht
    obtain ⟨c, hc⟩ := h 𝔪 (by simpa using hm)
    have : c ∈ (𝔪.restrictScalars K).comap Θ := by rw [he]; trivial
    exact hc this
  have hne := Subspace.biUnion_ne_univ_of_top_notMem hs
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
  refine ⟨c, ?_⟩
  by_contra hu
  obtain ⟨𝔪, hm, hle⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
  apply hc
  simp only [Set.mem_iUnion]
  exact ⟨_, Finset.mem_image.2 ⟨𝔪, by simpa using hm, rfl⟩, hle⟩

theorem hilbert90_baseChange : ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] (τ : E ≃ₐ[F] E) (m : ℕ), orderOf τ = m → ∀ x : K ⊗[F] E, ∏ i ∈ Finset.range m, (Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E))^[i] x = 1 → ∃ z : (K ⊗[F] E)ˣ, x * Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) z = z := by
  intro F E K _ _ _ _ _ _ _ τ m hm x hx
  classical
  set T := Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) with hT
  have hm0 : 0 < m := hm ▸ orderOf_pos τ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : IsArtinianRing (K ⊗[F] E) := IsArtinianRing.of_finite K _
  have hpow : ∀ (i : ℕ) (y : K ⊗[F] E), T^[i] y = (T ^ i) y := fun i y => by
    rw [AlgHom.coe_pow]
  have htm : ∀ (i : ℕ) (k : K) (c : E), (T ^ i) (k ⊗ₜ c) = k ⊗ₜ ((τ ^ i) c) := by
    intro i k c
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, ih, AlgEquiv.mul_apply]; simp [hT]
  have hTm : ∀ y, (T ^ m) y = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k c => rw [htm, ← hm, pow_orderOf_eq_one]; rfl
    | add a b ha hb => rw [map_add (f := _), ha, hb]
  simp only [hpow] at hx
  let a : ℕ → K ⊗[F] E := fun i => ∏ j ∈ Finset.range i, (T ^ j) x
  have ha : ∀ i, x * T (a i) = a (i + 1) := by
    intro i
    simp only [a, map_prod, Finset.prod_range_succ', pow_zero, AlgHom.one_apply, pow_succ',
      AlgHom.mul_apply]
    ring
  have ha0 : a 0 = 1 := by simp [a]
  have ham : a m = 1 := hx
  let Θ : K ⊗[F] E →ₗ[K] K ⊗[F] E :=
    ∑ i ∈ Finset.range m, (LinearMap.mulLeft K (a i)).comp (T ^ i).toLinearMap
  have hΘ : ∀ c, Θ c = ∑ i ∈ Finset.range m, a i * (T ^ i) c := by
    intro c
    simp [Θ, LinearMap.sum_apply]
  have hfix : ∀ c, x * T (Θ c) = Θ c := by
    intro c
    have h1 : x * T (Θ c) = ∑ i ∈ Finset.range m, a (i + 1) * (T ^ (i + 1)) c := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΘ, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← mul_assoc, ha, pow_succ', AlgHom.mul_apply]
    have h2 := Finset.sum_range_succ' (fun i => a i * (T ^ i) c) m
    rw [Finset.sum_range_succ, ham, ha0, hTm, pow_zero, AlgHom.one_apply] at h2
    rw [h1, hΘ]
    exact (add_right_cancel h2).symm
  obtain ⟨c, hc⟩ := exists_isUnit_of_forall_maximal Θ (fun 𝔪 h𝔪 => by
    by_contra hcon
    push_neg at hcon
    letI : Field ((K ⊗[F] E) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    let ι : E →+* (K ⊗[F] E) ⧸ 𝔪 :=
      (Ideal.Quotient.mk 𝔪).comp Algebra.TensorProduct.includeRight.toRingHom
    let φ : Fin m → (E →* (K ⊗[F] E) ⧸ 𝔪) := fun i =>
      ι.toMonoidHom.comp ((τ ^ (i : ℕ) : E ≃ₐ[F] E) : E →* E)
    have hφ : Function.Injective φ := by
      intro i j hij
      have : τ ^ (i : ℕ) = τ ^ (j : ℕ) := by
        ext c
        exact ι.injective (DFunLike.congr_fun hij c)
      exact Fin.ext (pow_injOn_Iio_orderOf (by simp [hm]) (by simp [hm]) this)
    have hli := (linearIndependent_monoidHom E ((K ⊗[F] E) ⧸ 𝔪)).comp φ hφ
    have := Fintype.linearIndependent_iff.1 hli (fun i => Ideal.Quotient.mk 𝔪 (a i)) (by
      ext c
      have h := Ideal.Quotient.eq_zero_iff_mem.2 (hcon (1 ⊗ₜ c))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΘ, map_sum, Finset.sum_range] at h
      simp only [htm, map_mul] at h
      rw [Finset.sum_apply]
      exact h) ⟨0, hm0⟩
    simp only [ha0, map_one] at this
    exact one_ne_zero this)
  exact ⟨hc.unit, hfix c⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexRangeKerIterateEndomorphism
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem card_ker_comp_eq {M : Type} [CommGroup M] (f g : M →* M) :
    Nat.card (f.comp g).ker = Nat.card g.ker * Nat.card (g.range.subgroupOf f.ker) := by
  have hle : g.ker ≤ (f.comp g).ker := by
    intro x hx
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx ⊢
    rw [hx, map_one]
  have h1 := Subgroup.card_mul_index (g.ker.subgroupOf (f.comp g).ker)
  have h2 : (g.ker.subgroupOf (f.comp g).ker).index = Nat.card ((f.comp g).ker.map g) :=
    Subgroup.relIndex_ker _ _
  have h3 : (f.comp g).ker.map g = g.range ⊓ f.ker := by
    rw [← MonoidHom.comap_ker, Subgroup.map_comap_eq]
  have h4 : Nat.card (g.range.subgroupOf f.ker) = Nat.card (g.range ⊓ f.ker : Subgroup M) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h1, h2, h3, h4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem index_range_comp_mul {M : Type} [CommGroup M] (f g : M →* M) :
    (f.comp g).range.index * Nat.card f.ker * Nat.card g.ker =
      f.range.index * g.range.index * Nat.card (f.comp g).ker := by
  have h1 : (f.comp g).range.index = (g.range ⊔ f.ker).index * f.range.index := by
    rw [MonoidHom.range_comp, Subgroup.index_map]
  have h2 : g.range.relIndex f.ker * (g.range ⊔ f.ker).index = g.range.index := by
    rw [← Subgroup.relIndex_sup_left, Subgroup.relIndex_mul_index le_sup_left]
  have h3 : Nat.card (g.range.subgroupOf f.ker) * g.range.relIndex f.ker = Nat.card f.ker :=
    Subgroup.card_mul_index _
  rw [h1, card_ker_comp_eq, ← h2, ← h3]
  ring

theorem index_range_ker_pow_succ_endomorphism {M : Type} [CommGroup M] (f : Monoid.End M)
    (hK : Nat.card (MonoidHom.ker f) ≠ 0) (k : ℕ) :
    Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) ≠ 0 ∧
    (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index * Nat.card (MonoidHom.ker f) ^ (k + 1) =
      (MonoidHom.range f).index ^ (k + 1) *
        Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) := by
  induction k with
  | zero => simpa using hK
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hc : (f ^ (k + 1 + 1) : Monoid.End M) = MonoidHom.comp f (f ^ (k + 1) : Monoid.End M) := by
      rw [pow_succ' f (k + 1)]; rfl
    rw [hc]
    constructor
    · refine (card_ker_comp_eq (M := M) f (f ^ (k + 1) : Monoid.End M)).trans_ne
        (mul_ne_zero ih1 ?_)
      have h3 := Subgroup.card_mul_index
        ((MonoidHom.range (f ^ (k + 1) : Monoid.End M)).subgroupOf (MonoidHom.ker f))
      intro h
      rw [h, zero_mul] at h3
      exact hK h3.symm
    · have h := index_range_comp_mul (M := M) f (f ^ (k + 1) : Monoid.End M)
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ih1)
      generalize (MonoidHom.comp f (f ^ (k + 1) : Monoid.End M)).range.index = A at *
      generalize Nat.card (MonoidHom.comp f (f ^ (k + 1) : Monoid.End M)).ker = B at *
      generalize (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index = C at *
      generalize Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) = D at *
      generalize Nat.card (MonoidHom.ker f) = K at *
      generalize (MonoidHom.range f).index = I at *
      calc A * K ^ (k + 1 + 1) * D = (A * K * D) * K ^ (k + 1) := by ring
        _ = I * B * (C * K ^ (k + 1)) := by rw [h]; ring
        _ = I ^ (k + 1 + 1) * B * D := by rw [ih2]; ring

theorem index_ker_iterate :
    ∀ (M : Type) [CommGroup M] (f : Monoid.End M) (k : ℕ), (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index ≠ 0 → Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) ≠ 0 → (MonoidHom.range f).index ≠ 0 ∧ Nat.card (MonoidHom.ker f) ≠ 0 ∧ (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index * Nat.card (MonoidHom.ker f) ^ (k + 1) = (MonoidHom.range f).index ^ (k + 1) * Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) := by
  intro M _ f k hI hK
  have hr : MonoidHom.range (f ^ (k + 1) : Monoid.End M) ≤ MonoidHom.range f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(f ^ k : Monoid.End M) x, by rw [pow_succ']; rfl⟩
  have hk : MonoidHom.ker f ≤ MonoidHom.ker (f ^ (k + 1) : Monoid.End M) := by
    intro x hx
    have hx' : f x = 1 := hx
    rw [pow_succ]
    change (f ^ k : Monoid.End M) (f x) = 1
    rw [hx', map_one]
  have hK' : Nat.card (MonoidHom.ker f) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hK (Subgroup.card_dvd_of_le hk)
  exact ⟨ne_zero_of_dvd_ne_zero hI (Subgroup.index_dvd_of_le hr), hK',
    (index_range_ker_pow_succ_endomorphism f hK' k).2⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_span_singleton_adicCompletionIntegers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {t : v.adicCompletionIntegers F}
    (ht : Valued.v (t : v.adicCompletion F) ≠ 0) (x : v.adicCompletionIntegers F) :
    x ∈ Ideal.span {t} ↔
      Valued.v (x : v.adicCompletion F) ≤ Valued.v (t : v.adicCompletion F) := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have ha : Valued.v (a : v.adicCompletion F) ≤ 1 := a.2
    change Valued.v ((a : v.adicCompletion F) * t) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' ha
  · intro hx
    have ht1 : (t : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h] at ht; simp at ht
    have hm : (x : v.adicCompletion F) / t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ (zero_lt_iff.2 ht)]
      exact hx
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    change (x : v.adicCompletion F) / t * t = x
    rw [div_mul_cancel₀ _ ht1]

theorem isAdicComplete_and_card_quotient_adicCompletionIntegers :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∀ t : v.adicCompletionIntegers F, Valued.v (t : v.adicCompletion F) < 1 → IsAdicComplete (Ideal.span {t}) (v.adicCompletionIntegers F)) ∧ ∀ (t : v.adicCompletionIntegers F) (e : ℕ), Valued.v (t : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) → Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {t}) = Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v
  refine ⟨fun t ht => ?_, fun t e ht => ?_⟩
  · refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion F) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) ?_
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
    · rw [Ne, Ideal.span_singleton_eq_top,
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact ht.ne
  · have ht0 : Valued.v (t : v.adicCompletion F) ≠ 0 := by rw [ht]; exact WithZero.exp_ne_zero
    let f : 𝓞 F →+* v.adicCompletionIntegers F ⧸ Ideal.span {t} :=
      (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
    have hs : Function.Surjective f := by
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨s, hs⟩ := Idele.exists_valued_sub_le v (a := (y : v.adicCompletion F)) y.2 e
      refine ⟨s, ?_⟩
      change Ideal.Quotient.mk _ _ = _
      rw [eq_comm, Ideal.Quotient.eq, mem_span_singleton_adicCompletionIntegers v ht0, ht]
      exact hs
    have hk : RingHom.ker f = v.asIdeal ^ e := by
      ext s
      rw [RingHom.mem_ker]
      change Ideal.Quotient.mk _ _ = _ ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton_adicCompletionIntegers v ht0, ht,
        HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    rw [← Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv, hk, ← map_pow,
      Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NcardPlacesOverEqOfPrimeDegree
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem ncard_places_over_eq_of_prime_degree :
    ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [IsGalois F E], p.Prime → Module.finrank F E = p →
      ∀ (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)), w ≠ w' →
        w.under (𝓞 F) = v → w'.under (𝓞 F) = v →
        Set.ncard {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} = p := by
  intro p F E _ _ _ _ _ _ hp hdeg v w w' hne hw hw'
  have : IsGaloisGroup (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ F E
  have hv := v.isMaximal
  have himg : (fun u : HeightOneSpectrum (𝓞 E) => u.asIdeal) ''
      {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} = v.asIdeal.primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : u.under (𝓞 F) = v := hu
      exact ⟨u.isPrime, ⟨by rw [← hu']; rfl⟩⟩
    · rintro ⟨hP, hPv⟩
      refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ?_, rfl⟩
      exact HeightOneSpectrum.ext hPv.over.symm
  have hcard : Set.ncard {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v}
      = (v.asIdeal.primesOver (𝓞 E)).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 E)
    (E ≃ₐ[F] E)
  rw [IsGalois.card_aut_eq_finrank, hdeg, ← hcard] at hf
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ hf) with h1 | h1
  · exfalso
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have h2 : w ∈ {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} := hw
    have h3 : w' ∈ {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} := hw'
    rw [ha] at h2 h3
    exact hne (h2.trans h3.symm)
  · exact h1

end GlobalTheory.CNorm
end

