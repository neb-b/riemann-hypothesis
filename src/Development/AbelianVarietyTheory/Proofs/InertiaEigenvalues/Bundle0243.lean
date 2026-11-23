module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import GroundTheory.PAdicHodge.TiltField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMap
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEstimateGaloisEigenvectorCLTate
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem tate_eigenvector_estimate : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l) (u : ℚ_[l]) (y : ℂ_[l]) (z : Om l) (N : ℕ) (e δ : ℝ), Per.σC γ y = algebraMap ℚ_[l] ℂ_[l] u * y → ‖u‖ = 1 → (γ ^ N) z = z → ‖y - (z : ℂ_[l])‖ ≤ e → ‖∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)‖ ≤ δ * ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ → 0 ≤ δ → ‖u ^ N - 1‖ * ‖y‖ ≤ max (‖u - 1‖ * e) (δ * e) := by
  intro l _ γ u y z N e δ hy hu hz he hT hδ
  have hca : ∀ c : ℚ_[l], ((algebraMap ℚ_[l] (Om l) c : Om l) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] c :=
    fun _ => rfl
  have hn : ∀ c : ℚ_[l], ‖algebraMap ℚ_[l] ℂ_[l] c‖ = ‖c‖ := fun c => by
    rw [← hca, PadicComplex.norm_extends, norm_algebraMap']
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  set U : ℂ_[l] := algebraMap ℚ_[l] ℂ_[l] u with hU
  have hv : ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ ≤ e := by
    rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul,
      hca, ← GlobalTheory.RingBasics.σC_coe]
    have h1 : Per.σC γ (z : ℂ_[l]) - U * (z : ℂ_[l])
        = U * (y - (z : ℂ_[l])) + -Per.σC γ (y - (z : ℂ_[l])) := by
      rw [map_sub, hy]; ring
    rw [← hU, h1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, hU, hn, hu, one_mul]; exact he
    · rw [norm_neg, GlobalTheory.RingBasics.norm_σC]; exact he
  have hpow : ∀ i : ℕ, Per.σC (γ ^ i) y = U ^ i * y := by
    intro i
    induction i with
    | zero => simp [GlobalTheory.RingBasics.σC_one]
    | succ i ih =>
      rw [pow_succ, GlobalTheory.RingBasics.σC_mul, hy, map_mul, hU, TateTwist.σC_algebraMap, ← hU, ih]
      ring
  have htel : ∑ i ∈ Finset.range N, (γ ^ i) (γ z) = ∑ i ∈ Finset.range N, (γ ^ i) z := by
    have h := Finset.sum_range_sub (fun i => (γ ^ i) z) N
    rw [Finset.sum_sub_distrib] at h
    simp only [hz, pow_zero, AlgEquiv.one_apply, sub_self, pow_succ, AlgEquiv.mul_apply] at h
    exact sub_eq_zero.1 h
  have hTv : ∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)
      = algebraMap ℚ_[l] (Om l) (1 - u) * ∑ i ∈ Finset.range N, (γ ^ i) z := by
    simp only [map_sub, map_mul, AlgEquiv.commutes, Finset.sum_sub_distrib, htel, map_one,
      ← Finset.mul_sum]
    ring
  set S : Om l := ∑ i ∈ Finset.range N, (γ ^ i) z with hS
  have hSc : (S : ℂ_[l]) = ∑ i ∈ Finset.range N, Per.σC (γ ^ i) (z : ℂ_[l]) := by
    simp only [GlobalTheory.RingBasics.σC_coe]
    exact map_sum (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l]) _ _
  have hB : ‖(U - 1) * (S : ℂ_[l])‖ ≤ δ * e := by
    have h2 : (U - 1) * (S : ℂ_[l]) = -((algebraMap ℚ_[l] (Om l) (1 - u) * S : Om l) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_mul, hca, map_sub, map_one, ← hU]; ring
    rw [h2, norm_neg, PadicComplex.norm_extends, ← hTv]
    exact hT.trans (mul_le_mul_of_nonneg_left hv hδ)
  have hA : ‖∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))‖ ≤ e :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg he0 fun i _ => by
      rw [GlobalTheory.RingBasics.norm_σC]; exact he
  have hmain : algebraMap ℚ_[l] ℂ_[l] (u ^ N - 1) * y
      = (U - 1) * (∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))) + (U - 1) * (S : ℂ_[l]) := by
    rw [hSc, ← mul_add, ← Finset.sum_add_distrib]
    simp only [map_sub, sub_add_cancel, hpow, map_pow, map_one, ← hU]
    rw [← Finset.sum_mul, ← mul_assoc, mul_geom_sum]
  rw [← hn, ← norm_mul, hmain]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ hB)
  have h3 : ‖U - 1‖ = ‖u - 1‖ := by rw [← hn, map_sub, map_one]
  rw [norm_mul, h3]
  exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfPow
section
open Polynomial

namespace GlobalTheory.GLq.LabelModel
theorem lift {F : Type} [Field F] {m M : ℕ} (hM : 0 < M) (hm : m ∣ M) {ξ ζ : F} (hξ : IsPrimitiveRoot ξ M)
    (hζ : IsPrimitiveRoot ζ m) : ∃ ξ' : F, IsPrimitiveRoot ξ' M ∧ ξ' ^ (M / m) = ζ := by
  obtain ⟨c, rfl⟩ := hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hM
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (m * c) := ⟨hM.ne'⟩
  have hη : IsPrimitiveRoot (ξ ^ c) m := hξ.pow hM (mul_comm _ _)
  obtain ⟨a, -, hac, ha⟩ := (hη.isPrimitiveRoot_iff).1 hζ
  obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective (n := m) (m := m * c) (Dvd.intro _ rfl) (ZMod.unitOfCoprime a hac)
  refine ⟨ξ ^ (U : ZMod (m * c)).val, hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime U), ?_⟩
  rw [Nat.mul_div_cancel_left _ hm0, ← pow_mul, mul_comm, pow_mul, ← ha]
  have h1 : (((U : ZMod (m * c)).val : ℕ) : ZMod m) = (a : ZMod m) := by
    have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hU
    simpa [ZMod.unitsMap_val] using this
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  rw [pow_eq_pow_mod _ hη.pow_eq_one, pow_eq_pow_mod a hη.pow_eq_one, h2]

variable (g : ℕ) [hg : Fact g.Prime]

theorem pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)

theorem dv {d e : ℕ} (h : d ∣ e) : g ^ d - 1 ∣ g ^ e - 1 := Nat.pow_sub_one_dvd_pow_sub_one g h

theorem exprim {d : ℕ} (hd : 0 < d) : ∃ ξ : Formalism.CyclotomicNorms.Fbar g, IsPrimitiveRoot ξ (g ^ d - 1) := by
  haveI : NeZero (((g ^ d - 1 : ℕ)) : Formalism.CyclotomicNorms.Fbar g) := ⟨by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hg.out.pos), Nat.cast_pow, CharP.cast_eq_zero (Formalism.CyclotomicNorms.Fbar g) g, zero_pow hd.ne']
    simp⟩
  haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _

theorem chain : ∃ z : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ n, IsPrimitiveRoot (z n) (g ^ n.factorial - 1) ∧
    z (n+1) ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
  have step : ∀ n (x : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)}),
      ∃ y : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ (n+1).factorial - 1)},
        y.1 ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = x.1 := by
    intro n x
    obtain ⟨ξ, hξ⟩ := exprim g (Nat.factorial_pos (n+1))
    obtain ⟨y, hy, hy'⟩ := lift (pos g (Nat.factorial_pos (n+1))) (dv g (Nat.factorial_dvd_factorial (Nat.le_succ n))) hξ x.2
    exact ⟨⟨y, hy⟩, hy'⟩
  choose f hf using step
  obtain ⟨x0, hx0⟩ := exprim g (Nat.factorial_pos 0)
  let s : ∀ n : ℕ, {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)} :=
    fun n => Nat.rec ⟨x0, hx0⟩ (fun n x => f n x) n
  exact ⟨fun n => (s n).1, fun n => ⟨(s n).2, hf n (s n)⟩⟩

theorem divmul {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (hb : 0 < b) : c / b * (b / a) = c / a := by
  obtain ⟨u, rfl⟩ := h1
  obtain ⟨v, rfl⟩ := h2
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  rw [Nat.mul_div_cancel_left _ hb, Nat.mul_div_cancel_left _ ha, mul_assoc, Nat.mul_div_cancel_left _ ha, mul_comm]

theorem gensys : ∃ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ d, 0 < d → IsPrimitiveRoot (ζ d) (g ^ d - 1) ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = ζ d := by
  obtain ⟨z, hz⟩ := chain g
  have hc : ∀ n k, z (n + k) ^ ((g ^ (n+k).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
    intro n k
    induction k with
    | zero => simp [Nat.div_self (pos g (Nat.factorial_pos n))]
    | succ k ih =>
      rw [← ih, ← (hz (n+k)).2, ← pow_mul, ← add_assoc,
        divmul (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right n k)))
          (dv g (Nat.factorial_dvd_factorial (Nat.le_succ _))) (pos g (Nat.factorial_pos _))]
  refine ⟨fun d => z d ^ ((g ^ d.factorial - 1) / (g ^ d - 1)), fun d hd => ⟨?_, fun d' hdd hd' => ?_⟩⟩
  · exact (hz d).1.pow (pos g (Nat.factorial_pos _)) (Nat.div_mul_cancel (dv g (Nat.dvd_factorial hd le_rfl))).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_dvd hd' hdd)
    beta_reduce
    rw [← hc d k, ← pow_mul, ← pow_mul,
      divmul (dv g hdd) (dv g (Nat.dvd_factorial hd' le_rfl)) (pos g hd'),
      divmul (dv g (Nat.dvd_factorial hd le_rfl)) (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right d k))) (pos g (Nat.factorial_pos _))]

theorem level (x : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) : ∃ d, 0 < d ∧ x ^ (g ^ d - 1) = 1 := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  let K := IntermediateField.adjoin (ZMod g) {x}
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ Module.finrank (ZMod g) K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have := FiniteField.pow_card_sub_one_eq_one y hy
  rw [hcard] at this
  exact ⟨_, Module.finrank_pos, by simpa [y] using congrArg Subtype.val this⟩

noncomputable def E (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((g ^ d - 1 : ℕ) : ℂ))

theorem E_prim {d : ℕ} (hd : 0 < d) : IsPrimitiveRoot (E g d) (g ^ d - 1) :=
  Complex.isPrimitiveRoot_exp _ (pos g hd).ne'

theorem E_pow {d d' : ℕ} (h : d ∣ d') (hd : 0 < d) (hd' : 0 < d') : E g d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = E g d := by
  obtain ⟨c, hc⟩ := dv g h
  have h1 := pos g hd
  have h2 := pos g hd'
  have hc0 : c ≠ 0 := by rintro rfl; omega
  unfold E
  rw [← Complex.exp_nat_mul, hc, Nat.mul_div_cancel_left _ h1]
  congr 1
  have : ((g ^ d - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h1.ne'
  have : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc0
  rw [Nat.cast_mul]
  field_simp

theorem prim_iff {R : Type} [CommMonoid R] {z : R} {m : ℕ} (h : IsPrimitiveRoot z m) (hm : 0 < m) (a b : ℕ) :
    z ^ a = z ^ b ↔ a ≡ b [MOD m] := by
  have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, h.pow_eq_one⟩
  rw [hf.pow_eq_pow_iff_modEq, ← h.eq_orderOf]

theorem inhab : Nonempty (LabelDatum g) := by
  classical
  obtain ⟨ζ, hζ⟩ := gensys g
  let R : Formalism.CyclotomicNorms.Fbar g → ℂ → Prop := fun x c => ∃ d, 0 < d ∧ ∃ j, x = ζ d ^ j ∧ c = E g d ^ j
  have common : ∀ x c y c', R x c → R y c' → ∃ d, 0 < d ∧ ∃ j j', x = ζ d ^ j ∧ c = E g d ^ j ∧ y = ζ d ^ j' ∧ c' = E g d ^ j' := by
    rintro x c y c' ⟨d, hd, j, rfl, rfl⟩ ⟨e, he, k, rfl, rfl⟩
    have hde := Nat.mul_pos hd he
    refine ⟨d * e, hde, (g ^ (d * e) - 1) / (g ^ d - 1) * j, (g ^ (d * e) - 1) / (g ^ e - 1) * k, ?_, ?_, ?_, ?_⟩
    · rw [pow_mul (ζ _), (hζ d hd).2 _ (Dvd.intro _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro _ rfl) hd hde]
    · rw [pow_mul (ζ _), (hζ e he).2 _ (Dvd.intro_left _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro_left _ rfl) he hde]
  have key : ∀ x c y c', R x c → R y c' → (x = y ↔ c = c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    rw [prim_iff (hζ d hd).1 (pos g hd), prim_iff (E_prim g hd) (pos g hd)]
  have mul : ∀ x c y c', R x c → R y c' → R (x * y) (c * c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    exact ⟨d, hd, j + j', (pow_add _ _ _).symm, (pow_add _ _ _).symm⟩
  have ex : ∀ x, x ≠ 0 → ∃ c, R x c := by
    intro x hx
    obtain ⟨d, hd, h⟩ := level g x hx
    haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
    obtain ⟨j, -, hj⟩ := (hζ d hd).1.eq_pow_of_pow_eq_one h
    exact ⟨_, d, hd, j, hj.symm, rfl⟩
  choose! t ht using ex
  let t' : Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if x = 0 then 0 else t x
  have ht' : ∀ x, x ≠ 0 → R x (t' x) := fun x hx => by simpa [t', hx] using ht x hx
  refine ⟨⟨⟨⟨t', ?_⟩, ?_⟩, ?_, ζ, fun d hd => (hζ d hd).1.eq_orderOf.symm,
    fun d e hd he => (hζ d hd).2 _ (Dvd.intro _ rfl) (Nat.mul_pos hd he)⟩⟩
  · exact (key _ _ _ _ (ht' 1 one_ne_zero) ⟨1, one_pos, 0, by simp, by simp⟩).1 rfl
  · intro x y
    by_cases hx : x = 0
    · simp [t', hx]
    by_cases hy : y = 0
    · simp [t', hy]
    exact (key _ _ _ _ (ht' _ (mul_ne_zero hx hy)) (mul _ _ _ _ (ht' x hx) (ht' y hy))).1 rfl
  · intro x y hx hy h
    exact (key _ _ _ _ (ht' x hx) (ht' y hy)).2 h

theorem thetaOf_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  have hp : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h1 := (prim_iff hp (pos g hd) _ _).1 h.choose_spec
  have h2 : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [thetaOf, dite_eq_left h, pow_eq_pow_mod _ h2, pow_eq_pow_mod n h2, h1]

end GlobalTheory.GLq.LabelModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltComplexPadicIsAlgClosedUnitBall
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GroundTheory.PAdicHodge

theorem tilt_isAlgClosed_and_unitBall : ∀ (l : ℕ) [Fact l.Prime],
    IsAlgClosed (FractionRing (PreTilt (normInteger ℂ_[l]) l)) ∧
      ∃ ι : Fl l →+* FractionRing (PreTilt (normInteger ℂ_[l]) l),
        (∀ x, tiltSharp (K := ℂ_[l]) (p := l) (ι x) = sh x) ∧
        (∀ z : FractionRing (PreTilt (normInteger ℂ_[l]) l), ‖z‖ ≤ 1 → ∃ x, ι x = z) := by
  intro l _
  obtain ⟨e, he⟩ := exists_flEquiv_untilt l
  have hC : IsAlgClosed (Formalism.BasicNotions.Loc.Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  refine ⟨?_, (algebraMap (PreTilt (normInteger ℂ_[l]) l) _).comp (e : Fl l →+* _), ?_, ?_⟩
  · let e' : Formalism.BasicNotions.Loc.Cb l ≃+* FractionRing (PreTilt (normInteger ℂ_[l]) l) :=
      IsFractionRing.ringEquivOfRingEquiv (A := Formalism.BasicNotions.Loc.OCb l) (B := PreTilt (normInteger ℂ_[l]) l) e
    exact IsAlgClosed.of_ringEquiv _ _ e'
  · intro x
    rw [RingHom.comp_apply, tiltSharp_algebraMap]
    exact he x
  · intro z hz
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hz
    exact ⟨e.symm a, by simp⟩

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltGaloisActionRootOfUnityCoprime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem σC_root_of_unity {m n : ℕ} {g : GQ l} (hm : 0 < m) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n)
    {x : ℂ_[l]} (hx : x ^ m = 1) : Per.σC g x = x ^ n := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have hζ' := hζ.map_of_injective (algebraMap (Om l) ℂ_[l]).injective
  obtain ⟨i, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hx
  have h1 : (ζ ^ i) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (ζ ^ i)) = algebraMap (Om l) ℂ_[l] (g (ζ ^ i)) :=
    GlobalTheory.RingBasics.σC_coe g (ζ ^ i)
  rw [← map_pow, h2, hg _ h1, map_pow]

theorem tilt_root_eq_one {c : Per.Fl l} {m : ℕ} (hlm : ¬ l ∣ m) (hc : c ^ m = 1)
    (h0 : PreTilt.coeff 0 c = 1) : c = 1 := by
  have : IsDomain (Per.Fl l) := inferInstance
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, c ^ i) * (c - 1) = 0 := by rw [geom_sum_mul, hc, sub_self]
  have h2 : (∑ i ∈ Finset.range m, c ^ i) = 0 :=
    (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (PreTilt.coeff (O := Per.OC l) (p := l) 0) h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_pow, h0, one_pow, Finset.sum_const, Finset.card_range, map_zero,
    nsmul_eq_mul, mul_one] at h3
  exact hlm ((CharP.cast_eq_zero_iff _ l m).1 h3)

theorem tilt_root_inj {a b : Per.Fl l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (ha : a ^ m = 1)
    (hb : b ^ m = 1) (h : a.untilt = b.untilt) : a = b := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hb' : b * b ^ k = 1 := by rw [← pow_succ', hb]
  have h0 : PreTilt.coeff 0 a = PreTilt.coeff 0 b := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, ← PreTilt.mk_untilt_eq_coeff_zero, h]
  have h1 : a * b ^ k = 1 := by
    refine tilt_root_eq_one hlm ?_ ?_
    · rw [mul_pow, ha, ← pow_mul, mul_comm k, pow_mul, hb, one_pow, one_mul]
    · rw [map_mul, h0, ← map_mul, hb', map_one]
  calc a = a * (b * b ^ k) := by rw [hb', mul_one]
    _ = (a * b ^ k) * b := by ring
    _ = b := by rw [h1, one_mul]

theorem σF_root_of_unity (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l) (hm : 0 < m)
    (hlm : ¬ l ∣ m) (he : e ^ m = 1) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n) :
    Per.σF g e = e ^ n := by
  refine tilt_root_inj hm hlm ?_ ?_ ?_
  · rw [← map_pow, he, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, he, one_pow]
  · rw [GlobalTheory.RingBasics.untilt_σF, map_pow]
    have h1 : e.untilt ^ m = 1 := by rw [← map_pow, he, map_one]
    have h2 : ((e.untilt : Per.OC l) : ℂ_[l]) ^ m = 1 := by
      simpa using congrArg Subtype.val h1
    exact Subtype.ext ((GlobalTheory.RingIface.sigO_coe l g _).trans
      ((σC_root_of_unity hm hg h2).trans (by simp)))

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMemAdjoin
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

theorem trace_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hT : T ^ (n + 1) = T) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    LinearMap.trace ℂ V T ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  haveI : NeZero n := ⟨hn⟩
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply Subalgebra.multiset_sum_mem
  intro μ hμ
  have hr : T.charpoly.IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
  have he : T.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).2 hr
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  have h1 := hv.pow_apply (n + 1)
  rw [hT, hv.apply_eq_smul] at h1
  have h2 : μ = μ ^ (n + 1) := smul_left_injective ℂ hv.2 h1
  by_cases h0 : μ = 0
  · rw [h0]; exact Subalgebra.zero_mem _
  · have h3 : μ ^ n = 1 := by
      rw [pow_succ] at h2
      exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h2.symm)
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h3
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _

theorem trace_lmul {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra ℂ Γ) :
    LinearMap.trace ℂ _ (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) = (Nat.card Γ : ℂ) * x.coeff 1 := by
  classical
  haveI := Fintype.ofFinite Γ
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis Γ ℂ), Matrix.trace]
  have : ∀ g : Γ, (LinearMap.toMatrix (MonoidAlgebra.basis Γ ℂ) (MonoidAlgebra.basis Γ ℂ)
      (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x)).diag g = x.coeff 1 := by
    intro g
    rw [Matrix.diag, LinearMap.toMatrix_apply]
    have hb : MonoidAlgebra.basis Γ ℂ g = MonoidAlgebra.single g 1 := by simp
    rw [hb]
    change (x * MonoidAlgebra.single g (1 : ℂ)).coeff g = _
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp
  rw [Finset.sum_congr rfl fun g _ => this g]
  simp

theorem centralIdemCoeff : CentralIdemCoeff := by
  intro Γ _ _ e he hc ζ hζ h
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ Γ) := Module.Finite.of_basis (MonoidAlgebra.basis Γ ℂ)
  set x : MonoidAlgebra ℂ Γ := MonoidAlgebra.single h⁻¹ (1 : ℂ) * e with hx
  have hcm : Commute (MonoidAlgebra.single h⁻¹ (1 : ℂ)) e := (hc _).symm
  have hid : IsIdempotentElem e := he
  have hp : x ^ (Nat.card Γ + 1) = x := by
    rw [hx, hcm.mul_pow, hid.pow_succ_eq, MonoidAlgebra.single_pow, one_pow, pow_succ,
      pow_card_eq_one', one_mul]
  have hT := trace_mem_adjoin (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) (n := Nat.card Γ)
    Nat.card_pos.ne' (by rw [← map_pow, hp]) hζ
  rw [trace_lmul, hx, MonoidAlgebra.coeff_single_mul_apply] at hT
  simpa using hT

end GlobalTheory.CentralIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMapStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tracePairing_injective_equivariant_levelMap : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]), (∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a) → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ g : ↥(GK K), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA _ hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → ∃ Ψ : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) →+ ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M, Function.Injective Ψ ∧ ∀ g y, Ψ (actQ LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y) = ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho g (Ψ y) := by
  first | exact @GlobalTheory.tracePairing_levelMap | exact GlobalTheory.tracePairing_levelMap | (intros; apply GlobalTheory.tracePairing_levelMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass.FamCont

theorem epsU_cont {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    Continuous fun g => ((epsU N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((epsU N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := R.rank_add_five_le
    rw [← Units.val_mul, N.chi_def i 2 (by omega) (by omega)]
    simp [Glob.epsO]
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

theorem stepCont : StepCont := by
  intro D i r hr x
  have hc := (hr x).1
  constructor
  · have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
      (D.nd.chi_cont i 1).comp continuous_inv
    refine (h1.smul hc).congr fun g => ?_
    simp [rTwO, twistM, rO]
  · have h1 := (D.nd.chi_cont i 1).mul (epsU_cont D.nd i)
    have h2 := (hc.comp continuous_inv).matrix_transpose
    refine (h1.smul h2).congr fun g => ?_
    rfl

end GlobalTheory.Pass.FamCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightLocalisationRegularAlgebraic
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem weight_localisation_regular_algebraic : ∀ (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* ℂ),
    (D.naut.infWt i τ).Nodup ∧ ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
  intro D i P τ
  rw [D.nbc.embAV_inf i P]
  exact D.nbc.infW_alg _ _ τ

end GlobalTheory
end

