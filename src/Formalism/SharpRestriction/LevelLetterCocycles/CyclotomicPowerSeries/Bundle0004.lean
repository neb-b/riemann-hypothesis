module

public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle0002
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EmultiplicityEqValuation

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.MapEvalRingHomOfPiFamily
section
noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

def ofPiFamily {LL ι : Type} [CommRing LL] (f : ι → PowerSeries LL) :
    PowerSeries (ι → LL) :=
  PowerSeries.mk fun n i => coeff n (f i)

theorem map_evalRingHom_ofPiFamily {LL ι : Type} [CommRing LL] (f : ι → PowerSeries LL) (i : ι) :
    PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) (ofPiFamily f) = f i := by
  ext n
  simp [ofPiFamily, PowerSeries.coeff_map, PowerSeries.coeff_mk]

theorem ext_evalRingHom {LL ι : Type} [CommRing LL] {F G : PowerSeries (ι → LL)}
    (h : ∀ i, PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F =
      PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) G) : F = G := by
  ext n i
  have h' : coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F) =
      coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) G) := by rw [h i]
  simpa [PowerSeries.coeff_map] using h'

def piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) : PowerSeries O →ₐ[O] PowerSeries (ι → LL) where
  toFun a := ofPiFamily fun i => ρ i a
  map_one' := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_mul' a b := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_zero' := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_add' a b := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  commutes' c := ext_evalRingHom fun i => by
    rw [map_evalRingHom_ofPiFamily, AlgHom.commutes]
    ext n
    simp [PowerSeries.algebraMap_apply, coeff_C]

theorem map_evalRingHom_piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) (i : ι) (a : PowerSeries O) :
    PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) (piAlgHom ρ a) = ρ i a := by
  first
    | exact map_evalRingHom_ofPiFamily (fun i => ρ i a) i
    | (simp only [piAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
       exact map_evalRingHom_ofPiFamily _ i)

theorem constantCoeff_piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) (i : ι) (a : PowerSeries O) :
    constantCoeff (piAlgHom ρ a) i = constantCoeff (ρ i a) := by
  rw [← map_evalRingHom_piAlgHom ρ i a, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
  rfl

theorem cyclotomic_comp_dvd {LL : Type} [Field LL] (n : ℕ) (hn : 0 < n) (ζ₀ : LL)
    (hζ₀ : IsPrimitiveRoot ζ₀ n) (r : Polynomial LL)
    (hr : ∀ ζ, IsPrimitiveRoot ζ n → r.eval (ζ - 1) = 0) :
    (Polynomial.cyclotomic n LL).comp (Polynomial.X + 1) ∣ r := by
  classical
  have hdiv : Polynomial.cyclotomic n LL ∣ r.comp (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ₀]
    apply Finset.prod_dvd_of_coprime
    · exact (Polynomial.pairwise_coprime_X_sub_C Function.injective_id).set_pairwise _
    · intro μ hμ
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_comp]
      simpa using hr μ ((mem_primitiveRoots hn).mp hμ)
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c.comp (Polynomial.X + 1), ?_⟩
  have hback : (r.comp (Polynomial.X - 1)).comp (Polynomial.X + 1) = r := by
    rw [Polynomial.comp_assoc]
    simp
  rw [← hback, hc, Polynomial.mul_comp]

private theorem derivative_exp_eq_exp' (A : Type) [Field A] [CharZero A] :
    derivative (PowerSeries.exp A) = PowerSeries.exp A :=
  PowerSeries.derivative_exp A

private theorem constantCoeff_exp_eq_one (A : Type) [Field A] [CharZero A] :
    constantCoeff (PowerSeries.exp A) = 1 := by
  first
    | simp
    | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_exp]; simp)

private theorem cyclotomic_comp_pow_dvd_of_X_pow_dvd {O LL : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field LL] [CharZero LL]
    [Algebra O LL] [IsFractionRing O LL] (n : ℕ) (hn : 0 < n) (ζ₀ : LL)
    (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hP : ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).IsDistinguishedAt (maximalIdeal O))
    (ρ : LL → (PowerSeries O →ₐ[O] PowerSeries LL))
    (hρ : ∀ ζ, IsPrimitiveRoot ζ n → 1 + ρ ζ X = C ζ * PowerSeries.exp LL)
    (k : ℕ) (a : PowerSeries O)
    (hk : ∀ ζ, IsPrimitiveRoot ζ n → (X : PowerSeries LL) ^ k ∣ ρ ζ a) :
    (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) ^ k ∣ a := by
  classical
  have hexp0 := constantCoeff_exp_eq_one LL
  have hcyc : ∀ z : PowerSeries LL, Polynomial.aeval z (Polynomial.cyclotomic n O) =
      Polynomial.aeval z (Polynomial.cyclotomic n LL) := by
    intro z
    first
      | rw [← Polynomial.map_cyclotomic n (algebraMap O LL), Polynomial.aeval_map_algebraMap]
      | rw [← Polynomial.map_cyclotomic_int n O, ← Polynomial.map_cyclotomic_int n LL,
          ← algebraMap_int_eq, ← algebraMap_int_eq, Polynomial.aeval_map_algebraMap,
          Polynomial.aeval_map_algebraMap]
  have hunit : ∀ ζ, IsPrimitiveRoot ζ n → ∃ w : (PowerSeries LL)ˣ,
      ρ ζ (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        (w : PowerSeries LL) * X := by
    intro ζ hζ
    have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic n LL) = 0 := by
      rw [Polynomial.coe_aeval_eq_eval]
      haveI : NeZero (n : LL) := ⟨by exact_mod_cast hn.ne'⟩
      first
        | exact Polynomial.isRoot_cyclotomic_iff.mpr hζ
        | exact Polynomial.isRoot_cyclotomic hn hζ
    obtain ⟨w, hw⟩ := cycloSimple LL LL n hn ζ (PowerSeries.exp LL) hroot hexp0
      (derivative_exp_eq_exp' LL)
    refine ⟨w, ?_⟩
    rw [algHom_coe_eq_aeval, Polynomial.aeval_comp]
    have h1 : Polynomial.aeval (ρ ζ X) (Polynomial.X + 1 : Polynomial O) =
        C ζ * PowerSeries.exp LL := by
      rw [map_add (f := _), Polynomial.aeval_X, map_one, add_comm]
      exact hρ ζ hζ
    rw [h1, hcyc]
    exact hw
  choose! w hw using hunit
  have hWu : IsUnit (ofPiFamily fun i : {ζ : LL // IsPrimitiveRoot ζ n} => (w i.1 : PowerSeries LL)) :=
    ((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).2.mpr fun i => by
      rw [map_evalRingHom_ofPiFamily]
      exact (w i.1).isUnit
  have hρP : piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1)
      (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        (hWu.unit : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) * X := by
    rw [IsUnit.unit_spec]
    apply ext_evalRingHom
    intro i
    rw [map_evalRingHom_piAlgHom, map_mul, map_evalRingHom_ofPiFamily, PowerSeries.map_X]
    exact hw i.1 i.2
  have hcc : ∀ i : {ζ : LL // IsPrimitiveRoot ζ n},
      constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) i = i.1 - 1 := by
    intro i
    rw [constantCoeff_piAlgHom]
    have h : constantCoeff (1 + ρ i.1 X) = constantCoeff (C i.1 * PowerSeries.exp LL) := by
      rw [hρ i.1 i.2]
    rw [map_add (f := _), map_one, map_mul, constantCoeff_C, hexp0, mul_one] at h
    linear_combination h
  have hroots : ∀ r : Polynomial LL,
      Polynomial.aeval (constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r = 0 →
        ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) ∣ r := by
    intro r hr
    have hmap : ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) =
        (Polynomial.cyclotomic n LL).comp (Polynomial.X + 1) := by
      rw [Polynomial.map_comp, Polynomial.map_cyclotomic, Polynomial.map_add (f := _), Polynomial.map_X,
        Polynomial.map_one]
    rw [hmap]
    apply cyclotomic_comp_dvd n hn ζ₀ hζ₀ r
    intro ζ hζ
    have h : (Polynomial.aeval (constantCoeff (piAlgHom
        (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ = 0 := by
      rw [hr]
      rfl
    rw [show (Polynomial.aeval (constantCoeff (piAlgHom
        (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ =
        Polynomial.aeval (constantCoeff (piAlgHom
          (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) ⟨ζ, hζ⟩) r from
        (Polynomial.aeval_algHom_apply (Pi.evalAlgHom LL (fun _ : {ζ : LL // IsPrimitiveRoot ζ n} => LL)
          ⟨ζ, hζ⟩) _ r).symm, hcc, Polynomial.coe_aeval_eq_eval] at h
    exact h
  have hXk : (X : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) ^ k ∣
      piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) a :=
    (((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).1 k).mpr fun i => by
      rw [map_evalRingHom_piAlgHom]
      exact hk i.1 i.2
  exact rhoCompl O LL ({ζ : LL // IsPrimitiveRoot ζ n} → LL) _ hP
    (piAlgHom fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) ⟨hWu.unit, hρP⟩ hroots k a hXk

theorem splitCompl : SplitComplStatement := by
  unfold SplitComplStatement
  intro O LL _ _ _ _ _ _ _ _ l s hl hlm hζ0 ρ hρ k a hk
  obtain ⟨ζ₀, hζ₀⟩ := hζ0
  exact cyclotomic_comp_pow_dvd_of_X_pow_dvd (l ^ (s + 1)) (pow_pos hl.pos _) ζ₀ hζ₀
    (cycloDist O l s hl hlm) ρ hρ k a hk

end LevelStatements.Lv
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PowValMemPrimitiveRoots
section
noncomputable section

namespace LevelStatements.Link

open PowerSeries

theorem pow_val_mem_primitiveRoots {LL : Type} [Field LL] (N : ℕ) (hN : 0 < N) (w : ZMod N)
    (hw : IsUnit w) {ξ : LL} (hξ : ξ ∈ primitiveRoots N LL) : ξ ^ w.val ∈ primitiveRoots N LL := by
  obtain ⟨u, rfl⟩ := hw
  rw [mem_primitiveRoots hN] at hξ ⊢
  exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)

theorem eq_of_pow_pred_eq_one {l : ℕ} [Fact l.Prime] (s : ℕ) (a b : ZMod (l ^ (s + 1)))
    (ha : a ^ (l - 1) = 1) (hb : b ^ (l - 1) = 1) (hab : (l : ZMod (l ^ (s + 1))) ∣ b - a) :
    b = a := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  set x := b - a with hx
  have hba : b = a + x := by rw [hx]; ring
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion
    (Polynomial.X ^ (l - 1) : Polynomial (ZMod (l ^ (s + 1)))) a x
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C] at hk
  rw [← hba, ha, hb] at hk
  have hlpow : (l : ZMod (l ^ (s + 1))) ^ (s + 1) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hxpow : x ^ (s + 1) = 0 := by
    obtain ⟨t, ht⟩ := hab
    rw [ht, mul_pow, hlpow, zero_mul]
  have hkx : IsNilpotent (k * x) := ⟨s + 1, by rw [mul_pow, hxpow, mul_zero]⟩
  have hl1 : IsUnit ((l - 1 : ℕ) : ZMod (l ^ (s + 1))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hinv : a * a ^ (l - 1 - 1) = 1 := by
    rw [← pow_succ', show l - 1 - 1 + 1 = l - 1 by omega, ha]
  have ha' : IsUnit a := ⟨⟨a, a ^ (l - 1 - 1), hinv, by rw [mul_comm]; exact hinv⟩, rfl⟩
  have hU : IsUnit (((l - 1 : ℕ) : ZMod (l ^ (s + 1))) * a ^ (l - 1 - 1) + k * x) :=
    hkx.isUnit_add_left_of_commute (hl1.mul (ha'.pow _)) (Commute.all _ _)
  have hx0 : x * (((l - 1 : ℕ) : ZMod (l ^ (s + 1))) * a ^ (l - 1 - 1) + k * x) = 0 := by
    linear_combination (-1 : ZMod (l ^ (s + 1))) * hk
  have hx' : x = 0 := hU.mul_left_eq_zero.mp hx0
  exact sub_eq_zero.mp hx'

theorem exists_toZModPow_eq_of_pow_pred_eq_one {l : ℕ} [Fact l.Prime] {Δ : Type*} (om : Δ → ℤ_[l])
    (hom : ∀ j, om j ^ (l - 1) = 1)
    (hom' : ∀ a : ZMod l, a ≠ 0 → ∃ j, PadicInt.toZMod (om j) = a) (s : ℕ)
    (a : ZMod (l ^ (s + 1))) (ha : a ^ (l - 1) = 1) :
    ∃ j, PadicInt.toZModPow (s + 1) (om j) = a := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdvd : l ∣ l ^ (s + 1) := dvd_pow_self l (Nat.succ_ne_zero s)
  set π := ZMod.castHom hdvd (ZMod l) with hπ
  have hψ : π.comp (PadicInt.toZModPow (s + 1)) = (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    apply ZMod.ringHom_eq_of_ker_eq
    have m1 := RingHom.ker_isMaximal_of_surjective _
      (ZMod.ringHom_surjective (π.comp (PadicInt.toZModPow (s + 1))))
    have m2 := RingHom.ker_isMaximal_of_surjective _
      (ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[l] →+* ZMod l))
    rw [IsLocalRing.eq_maximalIdeal m1, IsLocalRing.eq_maximalIdeal m2]
  have key : ∀ y : ZMod (l ^ (s + 1)), π y = 0 → (l : ZMod (l ^ (s + 1))) ∣ y := by
    intro y hy
    rw [← ZMod.natCast_zmod_val y, map_natCast] at hy
    obtain ⟨t, ht⟩ := (CharP.cast_eq_zero_iff (ZMod l) l y.val).mp hy
    refine ⟨(t : ZMod (l ^ (s + 1))), ?_⟩
    rw [← ZMod.natCast_zmod_val y, ht, Nat.cast_mul]
  have ha0 : π a ≠ 0 := by
    intro h0
    have hpa : π a ^ (l - 1) = 1 := by rw [← map_pow, ha, map_one]
    rw [h0, zero_pow (by omega)] at hpa
    exact zero_ne_one hpa
  obtain ⟨j, hj⟩ := hom' (π a) ha0
  refine ⟨j, eq_of_pow_pred_eq_one s a _ ha ?_ ?_⟩
  · rw [← map_pow, hom j, map_one]
  · have hc : π (PadicInt.toZModPow (s + 1) (om j)) = PadicInt.toZMod (om j) :=
      RingHom.congr_fun hψ (om j)
    have hk : π (PadicInt.toZModPow (s + 1) (om j) - a) = 0 := by
      rw [map_sub, hc, hj, sub_self]
    exact key _ hk

theorem map_cyclotomic_comp {O LL : Type} [CommRing O] [Field LL] [CharZero LL] [Algebra O LL]
    (ρ : PowerSeries O →ₐ[O] PowerSeries LL) (ζ : LL) (hρ : 1 + ρ X = C ζ * exp LL) (m : ℕ) :
    ρ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
      Polynomial.aeval (C ζ * exp LL) (Polynomial.cyclotomic m LL) := by
  have key : ∀ p : Polynomial O, ρ (p : PowerSeries O) = Polynomial.aeval (ρ X) p := by
    intro p
    have h := Polynomial.algHom_ext (f := ρ.comp (Polynomial.coeToPowerSeries.algHom O))
      (g := Polynomial.aeval (ρ X)) (by simp)
    have hp := AlgHom.congr_fun h p
    simpa using hp
  rw [key, Polynomial.aeval_comp]
  have h1 : Polynomial.aeval (ρ X) (Polynomial.X + 1 : Polynomial O) = C ζ * exp LL := by
    rw [map_add (f := _), Polynomial.aeval_X, map_one, add_comm, hρ]
  rw [h1, ← Polynomial.map_cyclotomic m (algebraMap O LL), Polynomial.aeval_map_algebraMap]

end LevelStatements.Link
end
end

