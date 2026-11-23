module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeStructureOfAdaptedInvariantFamily
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.AdaptedHodge

variable {l : ℕ} [Fact l.Prime]

theorem xi_unit_fil (C : Core l) (ξ : Ainf l) (hξ : Ideal.span {ξ} = RingHom.ker (Per.θ l)) :
    ∃ u : (Per.BdR l)ˣ, (u : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ∧
      ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a →
        ∃ w : Per.BdRp l, x = ((u ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w := by
  have he := core_isEps l C
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l
  have h1 : xi C.ε ∈ Ideal.span {ξ} := by rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
  have h2 : ξ ∈ Ideal.span {xi C.ε} := by rw [← C.ker_theta, ← hξ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a0, ha0⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨b0, hb0⟩ := Ideal.mem_span_singleton'.1 h2
  have hX := TiedUnif.isUnit_xi he
  have key : aDp l a0 * aDp l b0 * aDp l (xi C.ε) = aDp l (xi C.ε) := by
    rw [← map_mul, ← map_mul, mul_assoc, hb0, ha0]
  have hab : aDp l a0 * aDp l b0 = 1 := by
    apply hinj
    rw [map_one]
    apply hX.mul_right_cancel
    rw [one_mul, ← map_mul, key]
  have hα : IsUnit (aDp l a0) := IsUnit.of_mul_eq_one _ hab
  have hXe : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi C.ε)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a0) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) := by
    rw [← map_mul, ← map_mul, ha0]
  have hu : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ)) :=
    isUnit_of_mul_isUnit_right (hXe ▸ hX)
  refine ⟨hu.unit, hu.unit_spec, fun a x hx => ?_⟩
  obtain ⟨w, rfl⟩ := (TiedUnif.mem_FilD_iff he a x).1 hx
  have hEq : hX.unit = hu.unit * Units.map (algebraMap (Per.BdRp l) (Per.BdR l) : Per.BdRp l →* Per.BdR l) hα.unit :=
    Units.ext (by simp [hXe, mul_comm])
  refine ⟨((hα.unit ^ a : (Per.BdRp l)ˣ) : Per.BdRp l) * w, ?_⟩
  rw [hEq, mul_zpow, ← map_zpow, Units.val_mul, map_mul, mul_assoc]
  rfl

end GlobalTheory.BKLim.AdaptedHodge

namespace GlobalTheory.BKLim

theorem hodge_of_adapted : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (x : Fin d → Fin d → P.R.BdR) (h : Fin d → ℤ), (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) → (∀ j i, x j i ∈ (P.PD K).Fil (h j)) → (∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) → ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • x j) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ i, (H.p i : ℤ) - H.q = h i := by
  intro l _ K P AI T C hfit ξ hξ d ρ x h hinv hfil hspan
  obtain ⟨u, hu, hF⟩ := AdaptedHodge.xi_unit_fil C ξ hξ
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l
  have hV : ∀ j i, ∃ w : Per.BdRp l, T.eD (x j i) = ((u ^ h j : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w :=
    fun j i => hF _ _ ((T.fil K _ _).1 (hfil j i))
  choose w hw using hV
  have h0 : ∀ i (k : Fin d), (Pi.single i (1 : P.R.BdR) : Fin d → P.R.BdR) k ∈ (P.PD K).Fil 0 := by
    intro i k
    rw [T.fil]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same, map_one, ← map_one (algebraMap (Per.BdRp l) (Per.BdR l))]
      exact TiedUnif.alg_mem_FilD_zero 1
    · rw [Pi.single_eq_of_ne hk, map_zero]
      exact zero_mem _
  choose c hc hsum using fun i => hspan (Pi.single i 1) (h0 i)
  have hW : ∀ i j, ∃ w' : Per.BdRp l, T.eD (c i j) = ((u ^ (-h j) : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w' :=
    fun i j => hF _ _ ((T.fil K _ _).1 (hc i j))
  choose w' hw' using hW
  have hq : ∀ j, 0 ≤ h j + ((∑ j, (h j).natAbs : ℕ) : ℤ) := by
    intro j
    have h1 : (h j).natAbs ≤ ∑ j, (h j).natAbs := Finset.single_le_sum (f := fun j => (h j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hcan : ∀ j, ((u ^ (-h j) : (Per.BdR l)ˣ) : Per.BdR l) * ((u ^ h j : (Per.BdR l)ˣ) : Per.BdR l) = 1 := by
    intro j
    rw [← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  have hVW : (Matrix.of fun i j => w j i) * (Matrix.of fun j i => w' i j) = 1 := by
    ext k i
    apply hinj
    have e1 := congrArg (fun y : Fin d → P.R.BdR => T.eD (y k)) (hsum i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at e1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp only [Matrix.of_apply, map_mul]
    have e2 : ∀ j, T.eD (c i j) * T.eD (x j k) = algebraMap (Per.BdRp l) (Per.BdR l) (w j k) * algebraMap (Per.BdRp l) (Per.BdR l) (w' i j) := by
      intro j
      rw [hw, hw']
      linear_combination (algebraMap (Per.BdRp l) (Per.BdR l) (w j k) * algebraMap (Per.BdRp l) (Per.BdR l) (w' i j)) * hcan j
    simp only [e2] at e1
    rw [← e1, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  have hz : ∀ z : ℤ_[l], T.eD (algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) =
      ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) (zOm l z) := by
    intro z
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, hfit.o]
    rfl
  refine ⟨{ V := Matrix.of fun i j => w j i
            unit := ⟨⟨_, _, hVW, _root_.mul_eq_one_comm.mp hVW⟩, rfl⟩
            p := fun j => (h j + ((∑ j, (h j).natAbs : ℕ) : ℤ)).toNat
            q := ∑ j, (h j).natAbs
            Q := Matrix.of fun i j => T.eD (x j i)
            Q_eq := ?_
            inv := ?_ }, ?_⟩
  · intro i j
    simp only [Matrix.of_apply]
    rw [hw, map_mul, map_pow, ← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← mul_assoc, ← Units.val_mul,
      ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_add, Int.toNat_of_nonneg (hq j), add_comm]
  · intro g _
    ext i j
    have e1 := congrArg (fun y : Fin d → P.R.BdR => T.eD (y i)) (hinv j g)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, T.actD, hz] at e1
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact e1
  · intro i
    simp only
    rw [Int.toNat_of_nonneg (hq i)]
    ring

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfFracInv
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedIndep

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]


omit [Field K₀] [Algebra Qp K₀] [Algebra K₀ B] [IsScalarTower Qp K₀ B] in
theorem comm_smul (b : B) (w : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (b • w) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b)
        (TensorProduct.comm Qp B V w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

end Generic

end GlobalTheory.Per.TiedIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralWittElementOfEvaluation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.HeightSInt
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem smod_iff {R : Type} [CommRing R] (p x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule R R)] ↔ p ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem l_ne_zero_WCb : ((l : ℕ) : WCb l) ≠ 0 := by
  intro h
  have := congrArg (fun x : WCb l => x.coeff 1) h
  simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
  exact one_ne_zero this

theorem l_mul_cancel {x y : WCb l} (h : (l : WCb l) * x = (l : WCb l) * y) : x = y :=
  mul_left_cancel₀ l_ne_zero_WCb h

theorem dvd_iff_coeff {a : ℕ} [NeZero a] (w : Wq l a) : (l : Wq l a) ∣ w ↔ w.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, WittVector.constantCoeff_apply]

theorem dec {a : ℕ} [NeZero a] (s : (Wq l a)⟦X⟧) :
    (∃ s', s = (l : (Wq l a)⟦X⟧) * s') ∨
      ∃ (j : ℕ) (t s' : (Wq l a)⟦X⟧), IsUnit t ∧ s = X ^ j * t + (l : (Wq l a)⟦X⟧) * s' := by
  classical
  have hl' : ((l : (Wq l a)⟦X⟧)) = C (l : Wq l a) := (map_natCast C l).symm
  by_cases h : ∀ k, (l : Wq l a) ∣ coeff k s
  · left
    choose d hd using h
    refine ⟨mk d, ?_⟩
    ext k
    rw [hl', coeff_C_mul, coeff_mk, ← hd]
  · right
    push_neg at h
    let j := Nat.find h
    have hj : ¬ (l : Wq l a) ∣ coeff j s := Nat.find_spec h
    have hlt : ∀ i < j, (l : Wq l a) ∣ coeff i s := fun i hi => by
      have := Nat.find_min h hi
      simpa using this
    let d : ℕ → Wq l a := fun i => if hd : (l : Wq l a) ∣ coeff i s then hd.choose else 0
    refine ⟨j, mk fun i => coeff (i + j) s, mk fun i => if i < j then d i else 0, ?_, ?_⟩
    · rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
      exact WittVector.isUnit_of_coeff_zero_ne_zero _ (fun h0 => hj ((dvd_iff_coeff _).2 h0))
    · refine PowerSeries.ext fun k => ?_
      rw [map_add (f := _), coeff_X_pow_mul', hl', coeff_C_mul]
      simp only [coeff_mk]
      by_cases hk : j ≤ k
      · rw [if_pos hk, if_neg (not_lt.2 hk), mul_zero, add_zero, Nat.sub_add_cancel hk]
      · have hk' : k < j := not_le.1 hk
        rw [if_neg hk, if_pos hk', zero_add]
        have hdk : (l : Wq l a) ∣ coeff k s := hlt k hk'
        simp only [d, dif_pos hdk]
        exact hdk.choose_spec

variable (bk : BK K)

def e0 : bk.S →+* OCb l := WittVector.constantCoeff.comp bk.ev

theorem reduction_X_eq_flat : e0 bk X = bk.flat := by
  simp [e0, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem reduction_l_mul_eq_zero (s : bk.S) : e0 bk ((l : bk.S) * s) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem reduction_decomposition (s : bk.S) : (∃ s', s = (l : bk.S) * s') ∨ ∃ (j : ℕ) (t : bk.S), IsUnit (e0 bk t) ∧
    ∃ s' : bk.S, s = X ^ j * t + (l : bk.S) * s' ∧ e0 bk s = bk.flat ^ j * e0 bk t := by
  rcases dec s with h | ⟨j, t, s', ht, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨j, t, ht.map _, s', h, ?_⟩
    rw [h, map_add (f := _), reduction_l_mul_eq_zero, add_zero, map_mul, map_pow, reduction_X_eq_flat]

theorem dvd_of_reduction_eq_zero {s : bk.S} (h : e0 bk s = 0) : ∃ s', s = (l : bk.S) * s' := by
  rcases reduction_decomposition bk s with h' | ⟨j, t, ht, s', -, he⟩
  · exact h'
  · rw [he] at h
    exact absurd h (mul_ne_zero (pow_ne_zero _ (FlatDisc.flat_ne_zero bk)) ht.ne_zero)

theorem exists_reduction_of_flat_pow {m : ℕ} {x : OCb l} {s : bk.S} (h : bk.flat ^ m * x = e0 bk s) : ∃ s₀ : bk.S, x = e0 bk s₀ := by
  have hf := FlatDisc.flat_ne_zero bk
  rcases reduction_decomposition bk s with ⟨s', rfl⟩ | ⟨j, t, ht, s', -, he⟩
  · rw [reduction_l_mul_eq_zero] at h
    exact ⟨0, by rw [map_zero]; exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hf)⟩
  · rw [he] at h
    by_cases hmj : m ≤ j
    · refine ⟨X ^ (j - m) * t, ?_⟩
      rw [map_mul, map_pow, reduction_X_eq_flat]
      refine mul_left_cancel₀ (pow_ne_zero m hf) ?_
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmj]
    · exfalso
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 hmj)
      have h2 : bk.flat ^ (k + 1) * x = e0 bk t := by
        refine mul_left_cancel₀ (pow_ne_zero j hf) ?_
        rw [← h, ← mul_assoc, ← pow_add]; ring_nf
      rw [← h2, pow_succ, mul_assoc, mul_comm, mul_assoc] at ht
      exact FlatDisc.not_isUnit_flat bk (isUnit_of_mul_isUnit_left ht)

theorem cc_evW (s : bk.S) : WittVector.constantCoeff (bk.evW s) = algebraMap (OCb l) (Cb l) (e0 bk s) := by
  simp [BK.evW, e0, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem cc_inclW (a : Ainf l) : WittVector.constantCoeff (inclW l a) = algebraMap (OCb l) (Cb l) (a.coeff 0) := by
  simp [inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem cc_l_mul (y : WCb l) : WittVector.constantCoeff ((l : WCb l) * y) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

end GlobalTheory.BSP.HeightSInt

namespace GlobalTheory.BSP.HeightSInt
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem mem_of_l_mul_mem {v : WCb l} (h : (l : WCb l) * v ∈ bk.OE) : v ∈ bk.OE := by
  intro n
  obtain ⟨m, s, y, hs⟩ := h (n + 1)
  have h0 : e0 bk s = 0 := by
    have := congrArg WittVector.constantCoeff hs
    rw [map_add (f := _), pow_succ', mul_assoc, cc_l_mul, add_zero, cc_evW, mul_left_comm, cc_l_mul] at this
    exact (IsFractionRing.injective (OCb l) (Cb l)) (by rw [← this, map_zero])
  obtain ⟨s', rfl⟩ := dvd_of_reduction_eq_zero bk h0
  refine ⟨m, s', y, l_mul_cancel ?_⟩
  rw [map_mul, map_natCast] at hs
  rw [mul_add, mul_left_comm, hs]; ring

theorem step {a : Ainf l} (h : inclW l a ∈ bk.OE) :
    ∃ (s₀ : bk.S) (a₁ : Ainf l), a = bk.ev s₀ + (l : Ainf l) * a₁ ∧ inclW l a₁ ∈ bk.OE := by
  obtain ⟨m, s, y, hs⟩ := h 1
  have h1 : bk.flat ^ m * a.coeff 0 = e0 bk s := by
    have := congrArg WittVector.constantCoeff hs
    rw [map_add (f := _), pow_one, cc_l_mul, add_zero, cc_evW, map_mul, map_pow, cc_evW, cc_inclW, reduction_X_eq_flat, ← map_pow,
      ← map_mul] at this
    exact IsFractionRing.injective (OCb l) (Cb l) this
  obtain ⟨s₀, hs₀⟩ := exists_reduction_of_flat_pow bk h1
  have h2 : a - bk.ev s₀ ∈ Ideal.span {(l : Ainf l)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, hs₀]
    simp [e0, WittVector.constantCoeff_apply]
  obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton.1 h2
  refine ⟨s₀, a₁, by rw [← ha₁]; ring, mem_of_l_mul_mem bk ?_⟩
  have : (l : WCb l) * inclW l a₁ = inclW l a - bk.evW s₀ := by
    rw [BK.evW, RingHom.comp_apply, ← map_sub, ha₁, map_mul, map_natCast]
  rw [this]
  exact sub_mem h (evW_mem bk s₀)

theorem exists_lim {a : ℕ} [NeZero a] (T : ℕ → (Wq l a)⟦X⟧)
    (hT : ∀ n, (l : (Wq l a)⟦X⟧) ^ n ∣ T (n + 1) - T n) :
    ∃ s : (Wq l a)⟦X⟧, ∀ n, (l : (Wq l a)⟦X⟧) ^ n ∣ T n - s := by
  classical
  have hl' : ∀ n, ((l : (Wq l a)⟦X⟧)) ^ n = C ((l : Wq l a) ^ n) := fun n => by
    rw [map_pow, map_natCast]
  have hmn : ∀ m k, (l : (Wq l a)⟦X⟧) ^ m ∣ T (m + k) - T m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have : T (m + (k + 1)) - T m = (T (m + k + 1) - T (m + k)) + (T (m + k) - T m) := by
        rw [← add_assoc]; ring
      rw [this]
      exact dvd_add ((pow_dvd_pow _ (Nat.le_add_right m k)).trans (hT (m + k))) ih
  have hc : ∀ i, ∃ L : Wq l a, ∀ n, (l : Wq l a) ^ n ∣ coeff i (T n) - L := by
    intro i
    have hpc : IsPrecomplete (Ideal.span {(l : Wq l a)}) (Wq l a) := inferInstance
    obtain ⟨L, hL⟩ := hpc.prec (f := fun n => coeff i (T n)) (fun {m n} hmn' => by
      rw [smod_iff]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn'
      obtain ⟨q, hq⟩ := hmn m k
      refine ⟨-coeff i q, ?_⟩
      have : T m - T (m + k) = -(T (m + k) - T m) := by ring
      rw [← map_sub, this, hq, hl', map_neg, coeff_C_mul]; ring)
    exact ⟨L, fun n => (smod_iff _ _ _ _).1 (hL n)⟩
  choose L hL using hc
  refine ⟨mk L, fun n => ?_⟩
  choose q hq using fun i => hL i n
  refine ⟨mk fun i => q i, PowerSeries.ext fun i => ?_⟩
  rw [map_sub, coeff_mk, hl', coeff_C_mul, coeff_mk, hq]

theorem main (w : WCb l) (hw : w ∈ bk.OE) (a : Ainf l) (ha : w = inclW l a) : ∃ s : bk.S, a = bk.ev s := by
  classical
  subst ha
  let P : Type := {a : Ainf l // inclW l a ∈ bk.OE}
  have hs : ∀ b : P, ∃ (s₀ : bk.S) (b₁ : P), b.1 = bk.ev s₀ + (l : Ainf l) * b₁.1 := fun b => by
    obtain ⟨s₀, a₁, h, h'⟩ := step bk b.2
    exact ⟨s₀, ⟨a₁, h'⟩, h⟩
  choose σ nx hσ using hs
  let A : ℕ → P := fun n => nx^[n] ⟨a, hw⟩
  have hA : ∀ n, A (n + 1) = nx (A n) := fun n => Function.iterate_succ_apply' nx n _
  let T : ℕ → bk.S := fun n => ∑ i ∈ Finset.range n, (l : bk.S) ^ i * σ (A i)
  have hTa : ∀ n, a = bk.ev (T n) + (l : Ainf l) ^ n * (A n).1 := by
    intro n
    induction n with
    | zero => simp [T, A]
    | succ n ih =>
      rw [ih, hσ (A n), ← hA n]
      simp only [T, Finset.sum_range_succ, map_add (f := _), map_mul, map_pow, map_natCast]
      ring
  obtain ⟨s, hs⟩ := exists_lim T (fun n => ⟨σ (A n), by simp [T, Finset.sum_range_succ]⟩)
  refine ⟨s, ?_⟩
  rw [← sub_eq_zero]
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(l : Ainf l)})).2 fun n => (smod_iff _ _ _ _).2 ?_
  obtain ⟨q, hq⟩ := hs n
  have : T n = s + (l : bk.S) ^ n * q := by rw [← hq]; ring
  refine ⟨bk.ev q + (A n).1, ?_⟩
  rw [sub_zero]
  conv_lhs => rw [hTa n]
  rw [this, map_add (f := _), map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.BSP.HeightSInt

theorem GlobalTheory.BSP.ainf_inter_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ w ∈ bk.OE, ∀ a : Ainf l,
    w = inclW l a → ∃ s : bk.S, a = bk.ev s :=
  fun _ _ _ bk w hw a ha => HeightSInt.main bk w hw a ha
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealEqOfNotLeMaximalMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem ideal_dual_symm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (x y : ↥I) : f x * (y : A) = f y * (x : A) := by
  have h : (x : A) • y = (y : A) • x := Subtype.ext (by simp [mul_comm])
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm (f x), ← this, mul_comm]

theorem invertible_ideal_eq_of_not_le_maximal_mul (A : Type) [CommRing A] (I N : Ideal A) :
    Module.Invertible A ↥I → N ≤ I → (∀ m : Ideal A, m.IsMaximal → ¬ N ≤ m * I) → N = I := by
  intro hI hNI hm

  set c : Ideal A := N.colon I with hc
  have key : ∀ (f : Module.Dual A ↥I) (n : ↥I), (n : A) ∈ N → f n ∈ c := by
    intro f n hn
    rw [hc, Submodule.mem_colon]
    intro p hp
    rw [smul_eq_mul, ideal_dual_symm I f n ⟨p, hp⟩]
    exact N.mul_mem_left _ hn
  have hcTop : c = ⊤ := by
    by_contra hne
    obtain ⟨m, hmax, hcm⟩ := Ideal.exists_le_maximal c hne
    apply hm m hmax
    intro n hn
    obtain ⟨t, ht⟩ := hI.bijective.2 1
    have hall : ∀ t : Module.Dual A ↥I ⊗[A] ↥I, contractLeft A ↥I t * n ∈ m * I := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        rw [contractLeft_apply, ideal_dual_symm I f x ⟨n, hNI hn⟩]
        exact Ideal.mul_mem_mul (hcm (key f ⟨n, hNI hn⟩ hn)) x.2
      | add s u hs hu => rw [map_add (f := _), add_mul]; exact Ideal.add_mem _ hs hu
    simpa [ht] using hall t
  apply le_antisymm hNI
  intro y hy
  have h1 : (1 : A) ∈ c := hcTop ▸ Submodule.mem_top
  rw [hc, Submodule.mem_colon] at h1
  simpa using h1 y hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalizedFractionSemilinearTransition
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrac_transition : ∀ (A A' : Type) [CommRing A] [CommRing A'] (k : A →+* A') (N : Type) [AddCommGroup N] [Module A N] (N' : Type) [AddCommGroup N'] [Module A' N'] (τ : N →ₛₗ[k] N') (t : A) (t' : A') (a : ℕ) (y : LocalizedModule (Submonoid.powers t) N) (y' : LocalizedModule (Submonoid.powers t') N') (z m : N) (z' n : N') (i j : ℕ), IsFrac t y z a → IsFrac t y m i → IsFrac t' y' z' a → IsFrac t' y' n j → t' ^ a • τ z = k t ^ a • z' → ∃ r : ℕ, (k t * t') ^ r • (t' ^ j • τ m - k t ^ i • n) = 0 := by
  intro A A' _ _ k N _ _ N' _ _ τ t t' a y y' z m z' n i j h1 h2 h3 h4 h5
  unfold IsFrac at h1 h2 h3 h4
  obtain ⟨⟨_, r₁, rfl⟩, e1⟩ := LocalizedModule.mk_eq.1 (h1.symm.trans h2)
  obtain ⟨⟨_, r₂, rfl⟩, e2⟩ := LocalizedModule.mk_eq.1 (h3.symm.trans h4)
  simp only [Submonoid.smul_def] at e1 e2
  have e3 := congrArg τ e1
  simp only [map_smulₛₗ, map_pow] at e3
  refine ⟨r₁ + r₂ + a, ?_⟩
  linear_combination (norm := skip) (-(k t ^ r₂ * t' ^ (r₁ + r₂ + a) * t' ^ j)) • e3
    + (k t ^ (r₂ + r₁ + i) * t' ^ (r₁ + r₂ + j)) • h5
    + (k t ^ (r₁ + r₂ + a + i) * t' ^ r₁) • e2
  match_scalars <;> ring

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelaxedResidualSelmerMemUnrelaxedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relaxedResidualSelmer_mem_unrelaxed : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), FirstHalf i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q → ∀ x : Z1 (red i K (Tgl i s)), cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → (∀ a, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))), x.1 σ = 0 ∧ x.1 (GlobalTheory.TwistDet.cConj X σ) = 0) → cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅ := by
  first | exact @GlobalTheory.ResUnr.unrelax | exact GlobalTheory.ResUnr.unrelax | (intros; apply GlobalTheory.ResUnr.unrelax <;> assumption)
end

