module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0002
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0005
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionOfExpSpec
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair

namespace BiextensionSums

theorem map_lgF' {K0 K : Type} [Field K0] [Field K] (l : ℕ) (j : K0 →+* K) :
    PowerSeries.map j (lgF K0 l) = lgF K l := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold lgF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [map_inv₀, map_pow, map_natCast]
  · rw [map_zero]

theorem linSub_idM {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] :
    linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) = X := by
  funext x
  unfold linSub idM
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    rw [if_neg (Ne.symm hy)]
    simp
  · simp

theorem map_sumE {K0 K ι : Type} [Field K0] [Field K] [Fintype ι] {N0 N1 : ℕ} (j : K0 →+* K)
    (be : MvPowerSeries (Fin 2) K0) :
    map j (sumE (ι := ι) (N0 := N0) (N1 := N1) be) = sumE (map j be) := by
  unfold sumE
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_subst (hasSubst_of_constantCoeff_zero (by intro a; simp))]
  simp only [map_X]

theorem subst_neg' {K ι κ : Type} [Field K] {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f : MvPowerSeries ι K) : subst φ (-f) = -subst φ f := by
  rw [← coe_substAlgHom hφ, map_neg]

theorem subst_map_linEL {K0 K : Type} [NormedField K0] [NormedField K] {d N0 N1 : ℕ} [NeZero d]
    (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (c : K0) (a : Fin N0) (b : Fin N1)
    {g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K} (hg : HasSubst g)
    (hgE : ∀ y, subst g (entLog (K := K) l y) = X y) :
    subst g (map j (linEL σ c (fun s : ZMod d => entLog (K := K0) l (s, a, b)))) =
      ∑ s : ZMod d, if s.val % 2 = 0 then C (j (σ^[s.val] c)) * X (s, a, b) else 0 := by
  unfold linEL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, subst_sum hg]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [map_mul, map_C, Formalism.DworkPowerSeriesWeights.Transfer.map_entLog, subst_mul hg, subst_C, hgE]
  · rw [map_zero, subst_zero' hg]

theorem subst_map_linOL {K0 K : Type} [NormedField K0] [NormedField K] {d N0 N1 : ℕ} [NeZero d]
    (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (c : K0) (a : Fin N0) (b : Fin N1)
    {g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K} (hg : HasSubst g)
    (hgE : ∀ y, subst g (entLog (K := K) l y) = X y) :
    subst g (map j (linOL σ c (fun s : ZMod d => entLog (K := K0) l (s, a, b)))) =
      ∑ s : ZMod d, if s.val % 2 = 0 then 0 else C (j (σ^[s.val] c)) * X (s, a, b) := by
  unfold linOL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, subst_sum hg]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [map_zero, subst_zero' hg]
  · rw [map_mul, map_C, Formalism.DworkPowerSeriesWeights.Transfer.map_entLog, subst_mul hg, subst_C, hgE]

end BiextensionSums

open BiextensionSums

theorem biextension_of_exp_spec (hE : ExpSpec) (hP : BiextensionPointsIntegral) : B0 := by
  intro K0 K _ _ _ _ _ _ l d N0 N1 _ σ j hU hj h2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hTr ζ hζ
    U0 Φ hU0 hΦ0 hΦ
  have hl : 2 ≤ l := hU.1.two_le
  obtain ⟨Xt, hX, hlog, hS⟩ := hP K0 l d N0 N1 σ hU h2 hd F hF be0 hF1 hF2 ι om oms hOw hTr ζ hζ
  have hR := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (ZV d N0 N1)
  have hs0 : HasSubst Xt := hasSubst_of_constantCoeff_zero fun x => (hX x).1
  obtain ⟨Xp, hXp⟩ : ∃ Xp : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries (ZV d N0 N1) K,
      ∀ x, Xp x = map j (Xt x) := ⟨fun x => map j (Xt x), fun _ => rfl⟩
  have hXp' : (fun x => map j (Xt x)) = Xp := funext fun x => (hXp x).symm
  have h0 : ∀ x, constantCoeff (Xp x) = 0 := fun x => by
    rw [hXp, constantCoeff_map, (hX x).1, map_zero]
  have hi : ∀ x, Integral (Xp x) := fun x => by
    rw [hXp]
    exact Formalism.DworkPowerSeriesWeights.Transfer.integral_map j hj (hX x).2
  have hs : HasSubst Xp := hasSubst_of_constantCoeff_zero h0
  have hE0 : ∀ (a : Fin N0) (b : Fin N1) (s : ZMod d),
      constantCoeff (entLog (K := K0) l (s, a, b)) = 0 :=
    fun a b s => ((letter_shift K0 l d σ hU.1).2.2 N0 N1 a b s).1
  have hE1 : ∀ (a : Fin N0) (b : Fin N1) (s : ZMod d),
      constantCoeff (entLog (K := K) l (s, a, b)) = 0 :=
    fun a b s => ((letter_shift K l d (RingHom.id K) hU.1).2.2 N0 N1 a b s).1
  obtain ⟨bm, hbm⟩ : ∃ bm, bm = map j (beMean (d := d) l σ be0 om oms ζ) := ⟨_, rfl⟩
  obtain ⟨Bt, hBt⟩ : ∃ Bt : MvPowerSeries (ZV d N0 N1) K, Bt = ∑ ab : Fin N0 × Fin N1,
      subst (fun s => entLog (K := K) l (s, ab.1, ab.2)) bm := ⟨_, rfl⟩
  have hmapB : map j (∑ ab : Fin N0 × Fin N1, subst
      (fun s => entLog (K := K0) l (s, ab.1, ab.2)) (beMean (d := d) l σ be0 om oms ζ)) = Bt := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hBt]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [map_subst (hasSubst_of_constantCoeff_zero fun s => hE0 ab.1 ab.2 s), hbm]
    simp only [Formalism.DworkPowerSeriesWeights.Transfer.map_entLog]
  have hS' : Simeq Bt (subst Xp (sumE (map j be0))) := by
    have := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq K0 K _ j hj).1 _ _ hS
    rwa [hmapB, map_subst hs0, map_sumE, hXp'] at this
  have hΦ' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Bool × ι × Fin N0 × Fin N1)).2.2.2.2 _ Φ _ Xp h0 hi hΦ
  have hBΦ : Simeq Bt (subst Xp Φ) := hR.2.2.1 _ _ _ hS' (hR.2.1 _ _ hΦ')
  have hsΦ0 : constantCoeff (subst Xp Φ) = 0 := constantCoeff_subst_eq_zero hs h0 hΦ0
  have hBt0 : constantCoeff Bt = 0 := by
    have := hBΦ.1
    rwa [map_sub, hsΦ0, sub_zero] at this
  have hnB0 : constantCoeff (-Bt) = 0 := by rw [map_neg, hBt0, neg_zero]
  refine ⟨mvExp (Bt - subst Xp Φ) * subst Xp U0,
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hBΦ.2 (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' h0 hi hU0), ?_⟩
  intro g hg0 hgE
  have hg : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hx : ∀ x, subst g (Xp x) = xOfZ l j σ om oms x := by
    intro x
    have ha : constantCoeff (subst g (Xp x)) = 0 := constantCoeff_subst_eq_zero hg hg0 (h0 x)
    have hlg : PowerSeries.subst (subst g (Xp x)) (lgF K l) =
        subst g (map j (PowerSeries.subst (Xt x) (lgF K0 l))) := by
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX x).1), map_lgF',
        ← hXp, subst_subst1 hg (PowerSeries.HasSubst.of_constantCoeff_zero (h0 x))]
    rw [← exp_log hE hl ha, hlg, hlog]
    unfold xOfZ
    congr 1
    split_ifs
    · exact subst_map_linEL l j σ _ _ _ hg hgE
    · exact subst_map_linOL l j σ _ _ _ hg hgE
  have hmain : subst Xp (mvExp (-Φ) * U0) =
      mvExp (-Bt) * (mvExp (Bt - subst Xp Φ) * subst Xp U0) := by
    rw [subst_mul hs, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hs (by rw [map_neg, hΦ0, neg_zero]),
      ← mul_assoc, ← mvExp_add hnB0 hBΦ.1, subst_neg' hs]
    congr 2
    ring
  have hgB : subst g Bt = bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) bm := by
    unfold bSum
    rw [linSub_idM, hBt, subst_sum hg]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun s => hE1 ab.1 ab.2 s) hg]
    simp only [hgE]
  have hxf : xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms = fun x => subst g (Xp x) :=
    funext fun x => (hx x).symm
  unfold thetaInZ thetaZ
  rw [linSub_idM, subst_self, id, ← hbm, ← hgB, hxf, ← subst_comp_subst_apply hs hg, hmain,
    subst_mul hg, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hg hnB0, subst_neg' hg, neg_smul, one_smul, mul_comm]

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FrobeniusOnRingA
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

variable (l : ℕ) [Fact l.Prime]

def muSub : Submonoid ℂ_[l] where
  carrier := muPrime l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.mp h), by simp⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases (Fact.out : l.Prime).dvd_mul.mp h with h | h
      exacts [hln h, hlm h]
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]

def evK (k : ℕ) : MonoidAlgebra ℤ (muSub l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muSub l) ((muSub l).subtype.comp (powMonoidHom k))

lemma evK_of (k : ℕ) (g : muSub l) :
    evK l k (MonoidAlgebra.of ℤ (muSub l) g) = (g : ℂ_[l]) ^ k := by
  simp [evK]

lemma evK_mem (k : ℕ) (r : MonoidAlgebra ℤ (muSub l)) : evK l k r ∈ ringA l := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    rw [evK_of]
    exact Subring.pow_mem _ (Subring.subset_closure g.2) k
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Subring.add_mem _ hx hy
  | smul a x hx =>
    rw [zsmul_eq_mul, map_mul, map_intCast]
    exact Subring.mul_mem _ (intCast_mem _ a) hx

lemma eval_pow_coprime {K : Type*} [Field K] [CharZero K] {n k : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (hcop : Nat.Coprime k n) (P : Polynomial ℤ)
    (h : P.eval₂ (Int.castRingHom K) ζ = 0) : P.eval₂ (Int.castRingHom K) (ζ ^ k) = 0 := by
  have h1 : Polynomial.aeval ζ P = 0 := by
    rw [Polynomial.aeval_def]
    exact h
  have hd : minpoly ℤ ζ ∣ P := minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hn) h1
  rw [hζ.minpoly_eq_pow_coprime hcop] at hd
  obtain ⟨Q, rfl⟩ := hd
  have h2 : Polynomial.aeval (ζ ^ k) (minpoly ℤ (ζ ^ k)) = 0 := minpoly.aeval _ _
  rw [Polynomial.aeval_def] at h2
  rw [Polynomial.eval₂_mul]
  exact mul_eq_zero_of_left h2 _

lemma exists_poly (r : MonoidAlgebra ℤ (muSub l)) :
    ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ∀ m : ℕ, n ∣ m → 0 < m → ∀ ζ : ℂ_[l], IsPrimitiveRoot ζ m →
      ∃ P : Polynomial ℤ, ∀ k : ℕ, P.eval₂ (Int.castRingHom ℂ_[l]) (ζ ^ k) = evK l k r := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    obtain ⟨n, hn, hln, hg⟩ := g.2
    refine ⟨n, hn, hln, fun m hnm hm ζ hζ => ?_⟩
    have hgm : (g : ℂ_[l]) ^ m = 1 := by
      obtain ⟨c, rfl⟩ := hnm
      rw [pow_mul, hg, one_pow]
    have : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hgm
    refine ⟨Polynomial.X ^ i, fun k => ?_⟩
    rw [evK_of, ← hi, Polynomial.eval₂_pow, Polynomial.eval₂_X, ← pow_mul, ← pow_mul, mul_comm]
  | add x y hx hy =>
    obtain ⟨n, hn, hln, hP⟩ := hx
    obtain ⟨n', hn', hln', hP'⟩ := hy
    refine ⟨n * n', Nat.mul_pos hn hn', fun h => ?_, fun m hnm hm ζ hζ => ?_⟩
    · rcases (Fact.out : l.Prime).dvd_mul.mp h with h | h
      exacts [hln h, hln' h]
    · obtain ⟨P, hP⟩ := hP m (dvd_trans (dvd_mul_right _ _) hnm) hm ζ hζ
      obtain ⟨P', hP'⟩ := hP' m (dvd_trans (dvd_mul_left _ _) hnm) hm ζ hζ
      exact ⟨P + P', fun k => by rw [Polynomial.eval₂_add, map_add (f := _), hP, hP']⟩
  | smul a x hx =>
    obtain ⟨n, hn, hln, hP⟩ := hx
    refine ⟨n, hn, hln, fun m hnm hm ζ hζ => ?_⟩
    obtain ⟨P, hP⟩ := hP m hnm hm ζ hζ
    exact ⟨Polynomial.C a * P, fun k => by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hP, zsmul_eq_mul, map_mul, map_intCast, eq_intCast]⟩

lemma evK_ker (r : MonoidAlgebra ℤ (muSub l)) (h : evK l 1 r = 0) : evK l l r = 0 := by
  obtain ⟨n, hn, hln, hP⟩ := exists_poly l r
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n : ℂ_[l]) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] n
  obtain ⟨P, hP⟩ := hP n dvd_rfl hn ζ hζ
  have h1 : P.eval₂ (Int.castRingHom ℂ_[l]) ζ = 0 := by
    have := hP 1
    rw [pow_one] at this
    rw [this, h]
  have hcop : Nat.Coprime l n := ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hln
  rw [← hP l]
  exact eval_pow_coprime hζ hn hcop P h1

def evA (k : ℕ) : MonoidAlgebra ℤ (muSub l) →+* ringA l :=
  (evK l k).toRingHom.codRestrict (ringA l) (evK_mem l k)

lemma evA_coe (k : ℕ) (r : MonoidAlgebra ℤ (muSub l)) : ((evA l k r : ringA l) : ℂ_[l]) = evK l k r := rfl

lemma evA_of (k : ℕ) (g : muSub l) :
    evA l k (MonoidAlgebra.of ℤ (muSub l) g) = (⟨g, Subring.subset_closure g.2⟩ : ringA l) ^ k := by
  apply Subtype.ext
  rw [evA_coe, evK_of]
  rfl

lemma evA_surj : Function.Surjective (evA l 1) := by
  have hle : ringA l ≤ (evK l 1).toRingHom.range := by
    refine Subring.closure_le.mpr fun g hg => ?_
    refine ⟨MonoidAlgebra.of ℤ (muSub l) ⟨g, hg⟩, ?_⟩
    change evK l 1 _ = g
    rw [evK_of, pow_one]
  rintro ⟨x, hx⟩
  obtain ⟨r, hr⟩ := hle hx
  exact ⟨r, Subtype.ext hr⟩

lemma evA_ker : RingHom.ker (evA l 1) ≤ RingHom.ker (evA l l) := by
  intro r hr
  rw [RingHom.mem_ker] at hr ⊢
  apply Subtype.ext
  rw [evA_coe]
  exact evK_ker l r (by rw [← evA_coe, hr]; rfl)

lemma int_fermat (a : ℤ) : ∃ c : ℤ, a - a ^ l = (l : ℤ) * c := by
  have : ((a - a ^ l : ℤ) : ZMod l) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

lemma evA_congr (r : MonoidAlgebra ℤ (muSub l)) :
    ∃ y : ringA l, evA l l r - evA l 1 r ^ l = (l : ringA l) * y := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    refine ⟨0, ?_⟩
    rw [evA_of, evA_of, pow_one, sub_self, mul_zero]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    obtain ⟨w, hw⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (evA l 1 x) (evA l 1 y)
    refine ⟨u + v - evA l 1 x * evA l 1 y * w, ?_⟩
    rw [map_add (f := _), map_add (f := _), hw]
    linear_combination hu + hv
  | smul a x hx =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨c, hc⟩ := int_fermat l a
    have hc' : (a : ringA l) - (a : ringA l) ^ l = (l : ringA l) * (c : ringA l) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ringA l) hc
    refine ⟨(a : ringA l) * u + (c : ringA l) * evA l 1 x ^ l, ?_⟩
    rw [zsmul_eq_mul, map_mul, map_mul, map_intCast, map_intCast, mul_pow]
    linear_combination (a : ringA l) * hu + (evA l 1 x ^ l) * hc'

theorem frobenius_on_ring_a : FrobA := by
  intro l _
  refine ⟨(evA l 1).liftOfSurjective (evA_surj l) ⟨evA l l, evA_ker l⟩, fun ζ hζ => ?_, fun x => ?_⟩
  · have h1 : evA l 1 (MonoidAlgebra.of ℤ (muSub l) ⟨ζ, hζ⟩) = ζ := by
      rw [evA_of, pow_one]
    conv_lhs => rw [← h1]
    rw [RingHom.liftOfSurjective_comp_apply]
    change evA l l _ = _
    rw [evA_of]
  · obtain ⟨r, rfl⟩ := evA_surj l x
    rw [RingHom.liftOfSurjective_comp_apply]
    exact evA_congr l r

end Formalism.L2.Th1.D
end
end

