module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.SmulBasisMemHatIff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionLatticeSeparatedComplete
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Complete

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

noncomputable def comb {m : ℕ} (e : Fin m → Fin n → E) :
    (Fin m → FiniteAdeleRing (𝓞 F) F) →+ (Fin n → RA F E) where
  toFun a := ∑ i, fun j => a i ⊗ₜ[F] e i j
  map_zero' := by funext j; simp
  map_add' a b := by funext j; simp [TensorProduct.add_tmul, Finset.sum_add_distrib]

end

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem comb_apply_eq_sum_tmul {m : ℕ} (e : Fin m → Fin n → E)
    (a : Fin m → FiniteAdeleRing (𝓞 F) F) :
    _root_.GlobalTheory.AdLat.Complete.comb e a = ∑ k, fun j => a k ⊗ₜ[F] e k j := rfl

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem exists_integral_comb_of_mem_hat {m : ℕ} {e : Fin m → Fin n → E}
    {L : Set (Fin n → E)} (he : ∀ x ∈ L, ∃ c : Fin m → ℤ, ∑ k, c k • e k = x)
    {w : Fin n → _root_.GlobalTheory.AdLat.RA F E} (hw : w ∈ _root_.GlobalTheory.AdLat.hat F L) :
    ∃ a : Fin m → FiniteAdeleRing (𝓞 F) F, (∀ k v, a k v ∈ v.adicCompletionIntegers F) ∧
      w = _root_.GlobalTheory.AdLat.Complete.comb e a := by
  unfold _root_.GlobalTheory.AdLat.hat at hw
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨c, rfl⟩ := he x hx
    refine ⟨fun k => c k • a, fun k v => zsmul_mem (ha v) _, ?_⟩
    funext j
    simp only [comb_apply_eq_sum_tmul, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Int.cast_smul_eq_zsmul F, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      Int.cast_smul_eq_zsmul]
  | zero =>
    refine ⟨0, fun k v => zero_mem _, ?_⟩
    simp
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, fun k v => add_mem (ha k v) (hb k v), (map_add _ a b).symm⟩
  | neg x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨-a, fun k v => neg_mem (ha k v), (map_neg _ a).symm⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem eq_zero_of_forall_nsmul_mem_hat [FiniteDimensional F E] {m : ℕ}
    {e : Fin m → Fin n → E} {L : Set (Fin n → E)}
    (he : ∀ x ∈ L, ∃ c : Fin m → ℤ, ∑ k, c k • e k = x)
    (z : Fin n → _root_.GlobalTheory.AdLat.RA F E)
    (hz : ∀ N : ℕ, 0 < N → ∃ w ∈ _root_.GlobalTheory.AdLat.hat F L, z = N • w) : z = 0 := by
  classical
  set b := Module.finBasis F E
  set B := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F)) (S := F)
    Finset.univ (fun t : Fin m × Fin n × Fin (Module.finrank F E) => b.repr (e t.1 t.2.1) t.2.2)
  set δ : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d)
  have hδ : IsUnit δ :=
    (IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)).map
      (algebraMap F (FiniteAdeleRing (𝓞 F) F))
  have hint : ∀ w ∈ _root_.GlobalTheory.AdLat.hat F L, ∀ i ℓ v,
      (δ * B.repr (w i) ℓ) v ∈ v.adicCompletionIntegers F := by
    intro w hw i ℓ
    obtain ⟨a, ha, rfl⟩ := exists_integral_comb_of_mem_hat he hw
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [comb_apply_eq_sum_tmul, Finset.sum_apply, map_sum, Finsupp.coe_finsetSum,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_induction _ (fun y : FiniteAdeleRing (𝓞 F) F =>
      ∀ v, y v ∈ v.adicCompletionIntegers F) (fun x y hx hy v => add_mem (hx v) (hy v))
      (fun v => zero_mem _) fun k _ => ?_
    obtain ⟨r, hr⟩ := hd ⟨k, i, ℓ⟩ (Finset.mem_univ _)
    have hterm : δ * (a k * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr (e k i) ℓ)) =
        a k * algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r) := by
      rw [hr, Algebra.smul_def, map_mul]
      ring
    have hB : (B.repr (a k ⊗ₜ[F] e k i)) ℓ =
        a k * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr (e k i) ℓ) := by
      simp [B, Algebra.TensorProduct.basis_repr_tmul]
    rw [hB, hterm]
    intro v
    exact mul_mem (ha k v) ((_root_.GlobalTheory.AdLat.Model.integral_iff _).mpr ⟨r, rfl⟩ v)
  have hcoord : ∀ i ℓ, B.repr (z i) ℓ = 0 := by
    intro i ℓ
    refine (hδ.mul_right_eq_zero).mp ?_
    refine (_root_.GlobalTheory.AdLat.integral_finiteAdele_complete_separated F).1 _ fun N hN => ?_
    obtain ⟨w, hw, rfl⟩ := hz N hN
    refine ⟨δ * B.repr (w i) ℓ, hint w hw i ℓ, ?_⟩
    simp only [Pi.smul_apply, map_nsmul, Finsupp.smul_apply, mul_smul_comm]
  funext i
  refine B.repr.injective ?_
  ext ℓ
  simp [hcoord i ℓ]

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem comb_mem_hat_of_integral {m : ℕ} {e : Fin m → Fin n → E}
    {L : Set (Fin n → E)} (he : ∀ k, e k ∈ L) {a : Fin m → FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ k v, a k v ∈ v.adicCompletionIntegers F) :
    _root_.GlobalTheory.AdLat.Complete.comb e a ∈ _root_.GlobalTheory.AdLat.hat F L := by
  rw [comb_apply_eq_sum_tmul]
  refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ?_
  exact ⟨a k, ha k, e k, he k, rfl⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem exists_limit_in_hat_of_cauchy_nsmul {m : ℕ} {e : Fin m → Fin n → E}
    {L : Set (Fin n → E)} (he : ∀ x ∈ L, ∃ c : Fin m → ℤ, ∑ k, c k • e k = x)
    (hmem : ∀ k, e k ∈ L) (x : ℕ → (Fin n → _root_.GlobalTheory.AdLat.RA F E))
    (hx : ∀ N, x N ∈ _root_.GlobalTheory.AdLat.hat F L)
    (hstep : ∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ _root_.GlobalTheory.AdLat.hat F L,
      x (N * m) = x N + N • w) :
    ∃ z ∈ _root_.GlobalTheory.AdLat.hat F L, ∀ N : ℕ, 0 < N →
      ∃ w ∈ _root_.GlobalTheory.AdLat.hat F L, z = x N + N • w := by
  classical
  have hfact : ∀ t : ℕ, (t + 1 + 1).factorial = (t + 1).factorial * (t + 2) := fun t => by
    rw [Nat.factorial_succ (t + 1)]
    ring
  have hs : ∀ t : ℕ, ∃ c : Fin m → FiniteAdeleRing (𝓞 F) F,
      (∀ k v, c k v ∈ v.adicCompletionIntegers F) ∧
      x (t + 1 + 1).factorial = x (t + 1).factorial +
        (t + 1).factorial • _root_.GlobalTheory.AdLat.Complete.comb e c := by
    intro t
    obtain ⟨w, hw, hxw⟩ := hstep (t + 1).factorial (t + 2) (Nat.factorial_pos _) (by omega)
    obtain ⟨c, hc, rfl⟩ := exists_integral_comb_of_mem_hat he hw
    exact ⟨c, hc, by rw [hfact, hxw]⟩
  choose c hc hcx using hs
  obtain ⟨a₀, ha₀, hxa₀⟩ := exists_integral_comb_of_mem_hat he (hx (0 + 1).factorial)
  let A : ℕ → Fin m → FiniteAdeleRing (𝓞 F) F :=
    fun t => a₀ + ∑ j ∈ Finset.range t, (j + 1).factorial • c j
  have hA : ∀ t, _root_.GlobalTheory.AdLat.Complete.comb e (A t) = x (t + 1).factorial := by
    intro t
    induction t with
    | zero =>
      show _root_.GlobalTheory.AdLat.Complete.comb e
        (a₀ + ∑ j ∈ Finset.range 0, (j + 1).factorial • c j) = _
      rw [Finset.sum_range_zero, add_zero]
      exact hxa₀.symm
    | succ t ih =>
      show _root_.GlobalTheory.AdLat.Complete.comb e
        (a₀ + ∑ j ∈ Finset.range (t + 1), (j + 1).factorial • c j) = _
      rw [Finset.sum_range_succ, ← add_assoc, map_add (f := _),
        show a₀ + ∑ j ∈ Finset.range t, (j + 1).factorial • c j = A t from rfl, ih, map_nsmul,
        hcx t]
  have hAint : ∀ t k v, A t k v ∈ v.adicCompletionIntegers F := by
    intro t k
    simp only [A, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    intro v
    refine add_mem (ha₀ k v) ?_
    revert v
    refine Finset.sum_induction _ (fun y : FiniteAdeleRing (𝓞 F) F =>
      ∀ v, y v ∈ v.adicCompletionIntegers F) (fun y y' hy hy' v => add_mem (hy v) (hy' v))
      (fun v => zero_mem _) fun j _ v => ?_
    exact nsmul_mem (hc j k v) _
  have hcauchy : ∀ k, ∀ N m' : ℕ, 0 < N → 0 < m' → ∃ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ A (N * m') k = A N k + N • a := by
    intro k N m' hN hm'
    have hle : N ≤ N * m' := Nat.le_mul_of_pos_right _ hm'
    have hdvd : ∀ j ∈ Finset.Ico N (N * m'), N ∣ (j + 1).factorial := fun j hj =>
      Nat.dvd_factorial hN (by simp only [Finset.mem_Ico] at hj; omega)
    refine ⟨∑ j ∈ Finset.Ico N (N * m'), ((j + 1).factorial / N) • c j k, ?_, ?_⟩
    · refine Finset.sum_induction _ (fun y : FiniteAdeleRing (𝓞 F) F =>
        ∀ v, y v ∈ v.adicCompletionIntegers F) (fun y y' hy hy' v => add_mem (hy v) (hy' v))
        (fun v => zero_mem _) fun j _ v => ?_
      exact nsmul_mem (hc j k v) _
    · simp only [A, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
      rw [← Finset.sum_range_add_sum_Ico _ hle, add_assoc, Finset.smul_sum]
      congr 2
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [smul_smul, Nat.mul_div_cancel' (hdvd j hj)]
  choose y hy using fun k => (_root_.GlobalTheory.AdLat.integral_finiteAdele_complete_separated F).2
    (fun N => A N k) (fun N v => hAint N k v) (hcauchy k)
  have hyint : ∀ k v, y k v ∈ v.adicCompletionIntegers F := by
    intro k v
    obtain ⟨a, ha, h⟩ := hy k 1 one_pos
    rw [h]
    exact add_mem (hAint 1 k v) (nsmul_mem (ha v) 1)
  refine ⟨_root_.GlobalTheory.AdLat.Complete.comb e y,
    comb_mem_hat_of_integral hmem hyint, fun N hN => ?_⟩
  choose a ha hya using fun k => hy k N hN
  have hyA : y = A N + N • a := funext fun k => hya k
  have hdN : N ∣ (N + 1).factorial := Nat.dvd_factorial hN (by omega)
  obtain ⟨w, hw, hxw⟩ := hstep N ((N + 1).factorial / N) hN
    (Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) hdN) hN)
  rw [Nat.mul_div_cancel' hdN] at hxw
  refine ⟨w + _root_.GlobalTheory.AdLat.Complete.comb e a,
    add_mem hw (comb_mem_hat_of_integral hmem ha), ?_⟩
  rw [hyA, map_add (f := _), map_nsmul, hA, hxw, smul_add, add_assoc]


open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
theorem _root_.GlobalTheory.AdLat.Complete.hat_separated_complete : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ z : Fin n → _root_.GlobalTheory.AdLat.RA F E, (∀ N : ℕ, 0 < N →
      ∃ w ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), z = N • w) → z = 0) ∧
    ∀ x : ℕ → (Fin n → _root_.GlobalTheory.AdLat.RA F E),
      (∀ N, x N ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)))) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        x (N * m) = x N + N • w) →
      ∃ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), ∀ N : ℕ, 0 < N →
        ∃ w ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), z = x N + N • w := by
  intro F E _ _ _ _ _ n L hL
  obtain ⟨m, e, he⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (hL.restrictScalars (R := ℤ))
  have hgen : ∀ x ∈ (L : Set (Fin n → E)), ∃ c : Fin m → ℤ, ∑ k, c k • e k = x := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (Set.range e) := by
      rw [he]
      exact hx
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx'
  have hmem : ∀ k, e k ∈ (L : Set (Fin n → E)) := by
    intro k
    have hk : e k ∈ Submodule.span ℤ (Set.range e) := Submodule.subset_span ⟨k, rfl⟩
    rw [he] at hk
    exact hk
  exact ⟨eq_zero_of_forall_nsmul_mem_hat hgen,
    fun x hx hstep => exists_limit_in_hat_of_cauchy_nsmul hgen hmem x hx hstep⟩

end GlobalTheory.AdLat.Complete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KernelNoTorsion

theorem eq_of_isSchemeTheoreticallyDominant {X S Y Z : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    {a b : Y ⟶ X} (hab : a ≫ f = b ≫ f) (j : Z ⟶ Y) [IsSchemeTheoreticallyDominant j]
    (hj : j ≫ a = j ≫ b) : a = b := by
  have := GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated f hab
  have hk : (equalizer.ι a b).ker = ⊥ := by
    have h := Scheme.Hom.le_ker_comp (equalizer.lift j hj) (equalizer.ι a b)
    rw [equalizer.lift_ι, j.ker_eq_bot] at h
    exact le_bot_iff.mp h
  have : IsIso (equalizer.ι a b) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b), equalizer.condition]

theorem eq_of_generic (T K : Type) [CommRing T] [IsDomain T] [Field K] [Algebra T K]
    [IsFractionRing T K] {Y X : Over (Sp T)} [Flat Y.hom] [IsSeparated X.hom] {a b : Y ⟶ X}
    (h : (Over.pullback (spMap (algebraMap T K))).map a =
      (Over.pullback (spMap (algebraMap T K))).map b) : a = b := by
  have : IsDominant (spMap (algebraMap T K)) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap T K)).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  apply Over.OverMorphism.ext
  refine eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm)
    (pullback.fst Y.hom (spMap (algebraMap T K))) ?_
  have h' := congr(($h).left ≫ pullback.fst X.hom (spMap (algebraMap T K)))
  exact (pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))

theorem comp_mulN {S : Scheme.{0}} {Y G : Over S} [GrpObj G] (x : Y ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => rw [pow_zero, mulN, Hom.one_def, comp_toUnit_assoc]
  | succ n ih => rw [pow_succ, mulN, Hom.mul_def, comp_lift_assoc, ih, Category.comp_id]

noncomputable def torsionLift {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : Y ⟶ torsion G n :=
  pullback.lift x (toUnit Y) (by rw [comp_mulN, hx, Hom.one_def])

theorem torsionLift_ι {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : torsionLift x hx ≫ torsion.ι G n = x :=
  pullback.lift_fst _ _ _

theorem torsion_hom_ext {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ}
    {a b : Y ⟶ torsion G n} (h : a ≫ torsion.ι G n = b ≫ torsion.ι G n) : a = b :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem torsionι_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 := by
  rw [← comp_mulN, Hom.one_def]
  refine (pullback.condition).trans ?_
  congr 1
  exact toUnit_unique _ _

theorem eq_one_of_pow_eq_one_of_comp_eq_one :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] [IsCommMonObj Ga] [IsCommMonObj G] (p : Ga ⟶ G) (n : ℕ), IsMonHom p → IsSeparated Ga.hom → Etale (torsion Ga n).hom → Etale (torsion G n).hom → IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → ∀ (Y : Over (Sp T)) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ p = 1 → x = 1 := by
  intro T K _ _ _ _ _ _ Ga G _ _ _ _ p n hp hsep hA hB hiso Y x hx hxp
  have hq : (torsion.ι Ga n ≫ p) ^ n = 1 := by
    rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp]
  let q : torsion Ga n ⟶ torsion G n := torsionLift _ hq
  let e : torsion Ga n ⟶ torsion G n := torsionLift 1 (one_pow n)
  have hopen := GlobalTheory.isOpenImmersion_equalizer_ι_left_of_unramified q e
  have hflat : Flat (equalizer q e).hom := by
    rw [← Over.w (equalizer.ι q e)]
    infer_instance
  have h1 : (equalizer.ι q e ≫ torsion.ι Ga n) ≫ p = (1 : equalizer q e ⟶ Ga) ≫ p := by
    have := equalizer.condition q e =≫ torsion.ι G n
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one] at this
    rw [Category.assoc, this, MonObj.one_comp]
  have h2 : equalizer.ι q e ≫ torsion.ι Ga n = 1 := by
    apply eq_of_generic T K
    rw [← cancel_mono ((Over.pullback (spMap (algebraMap T K))).map p), ← Functor.map_comp,
      ← Functor.map_comp, h1]
  have h3 : torsionLift x hx ≫ q = torsionLift x hx ≫ e := by
    apply torsion_hom_ext
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one,
      ← Category.assoc, torsionLift_ι, hxp]
  rw [← torsionLift_ι x hx, ← equalizer.lift_ι (torsionLift x hx) h3, Category.assoc, h2,
    MonObj.comp_one]

end GlobalTheory.KernelNoTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology

namespace GlobalTheory

namespace RationalPoint

variable {k : Type} [Field k]

noncomputable def pt {X : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) : X.left :=
  y.left (IsLocalRing.closedPoint k)

theorem range_left_subset_iff {X : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) (Z : Set X.left) :
    Set.range y.left ⊆ Z ↔ pt y ∈ Z := by
  refine ⟨fun h => h ⟨_, rfl⟩, fun h => ?_⟩
  rintro _ ⟨a, rfl⟩
  have : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [this]
  exact h

theorem pt_comp {X Y : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) (f : X ⟶ Y) :
    pt (y ≫ f) = f.left (pt y) := rfl

@[reducible] noncomputable def zariski (X : Over (Sp k)) :
    TopologicalSpace (𝟙_ (Over (Sp k)) ⟶ X) :=
  TopologicalSpace.induced pt inferInstance

theorem continuous_comp {X Y : Over (Sp k)} (f : X ⟶ Y) :
    Continuous[zariski X, zariski Y] fun y => y ≫ f := by
  letI := zariski X
  letI := zariski Y
  exact continuous_induced_rng.2 (f.left.continuous.comp continuous_induced_dom)

theorem separatelyContinuousMul (B : Over (Sp k)) [GrpObj B] :
    @SeparatelyContinuousMul (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  have h : ∀ g y : 𝟙_ (Over (Sp k)) ⟶ B, y ≫ toUnit B ≫ g = g := fun g y => by
    rw [← Category.assoc, toUnit_unique (y ≫ toUnit B) (𝟙 _), Category.id_comp]
  refine ⟨fun {g} => ?_, fun {g} => ?_⟩
  · convert continuous_comp ((toUnit B ≫ g) * 𝟙 B) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]
  · convert continuous_comp (𝟙 B * (toUnit B ≫ g)) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]

theorem continuousInv (B : Over (Sp k)) [GrpObj B] :
    @ContinuousInv (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  refine ⟨?_⟩
  convert continuous_comp (𝟙 B)⁻¹ using 2 with y
  rw [GrpObj.comp_inv, Category.comp_id]

variable [IsAlgClosed k]

theorem isClosed_pt {X : Over (Sp k)} [LocallyOfFiniteType X.hom] (y : 𝟙_ (Over (Sp k)) ⟶ X) :
    IsClosed {pt y} :=
  (pointEquivClosedPoint X.hom ⟨y.left, Over.w y⟩).2

theorem pt_injective {X : Over (Sp k)} [LocallyOfFiniteType X.hom] :
    Function.Injective (pt : (𝟙_ (Over (Sp k)) ⟶ X) → X.left) := fun x y h =>
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq X.hom (Over.w x) (Over.w y) h)

theorem exists_pt_mem {X : Over (Sp k)} [LocallyOfFiniteType X.hom] {Z : Set X.left}
    (hZ : IsClosed Z) (hne : Z.Nonempty) : ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne hZ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc), ?_⟩
  have : pt (Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc) :
      𝟙_ (Over (Sp k)) ⟶ X) = c := pointOfClosedPoint_apply X.hom c hc _
  rwa [this]

theorem pt_mem_image_iff {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) {Z : Set X.left} (hZ : IsClosed Z)
    (y : 𝟙_ (Over (Sp k)) ⟶ Y) :
    pt y ∈ f.left '' Z ↔ ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z ∧ x ≫ f = y := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := exists_pt_mem (Z := Z ∩ f.left ⁻¹' {pt y})
      (hZ.inter ((isClosed_pt y).preimage f.left.continuous)) ⟨z, hz, hzy⟩
    exact ⟨x, hx, pt_injective hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨pt x, hx, rfl⟩


omit [IsAlgClosed k] in
theorem isConstructible_image_of_isClosed {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    {Z : Set X.left} (hZ : IsClosed Z) : IsConstructible (f.left '' Z) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian X.left := {}
  have : IsNoetherian Y.left := {}
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : LocallyOfFinitePresentation f.left := inferInstance
  have : QuasiCompact f.left := inferInstance
  refine f.left.isConstructible_image ?_
  exact ((TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl).of_compl

end RationalPoint


open RationalPoint in
theorem exists_isClosed_image_of_isClosed_subgroup :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G B : Over (Sp k)) [GrpObj G] [GrpObj B] (q : G ⟶ B), IsMonHom q → LocallyOfFiniteType G.hom → QuasiCompact G.hom → LocallyOfFiniteType B.hom → QuasiCompact B.hom → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → ∃ Z' : Set B.left, IsClosed Z' ∧ ∀ y : (𝟙_ (Over (Sp k)) ⟶ B), (∃ x ∈ C, x ≫ q = y) ↔ Set.range y.left ⊆ Z' := by
  intro k _ _ G B _ _ q _ _ _ _ _ C Z hZ hC
  letI := RationalPoint.zariski B
  haveI := RationalPoint.separatelyContinuousMul B
  haveI := RationalPoint.continuousInv B
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ B) :=
    MonoidHom.mk' (fun x => x ≫ q) fun x y => MonObj.mul_comp x y q
  have hcl : IsClosed (C.map φ : Set (𝟙_ (Over (Sp k)) ⟶ B)) := by
    refine isClosed_subgroup_of_eq_preimage_isConstructible _ (f := RationalPoint.pt)
      continuous_induced_dom (RationalPoint.isConstructible_image_of_isClosed q hZ) ?_
    ext y
    rw [Set.mem_preimage, RationalPoint.pt_mem_image_iff q hZ]
    simp only [← RationalPoint.range_left_subset_iff, ← hC]
    rfl
  obtain ⟨Z', hZ', h⟩ := isClosed_induced_iff.1 hcl
  refine ⟨Z', hZ', fun y => ?_⟩
  rw [RationalPoint.range_left_subset_iff, ← Set.mem_preimage, h]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSetStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_nsmul_adelicCompletionOfVectorSet : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); (∀ N : ℕ, 0 < N → IsOpen {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y}) ∧ ∀ W ∈ 𝓝 (0 : RA F E), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), N • y ∈ W := by
  exact @GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat
end

