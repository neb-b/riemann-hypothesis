module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BalancedNonnegFormInPsdCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership

theorem toReal_mem_psdCone_of_nonneg : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O), CMOrd O bar → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X), β ∈ balForms bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := bar) (X := X) := by
  intro O _ _ _ _ bar _ X _ _ _ _ β hβ hp
  have h := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 (fun _ => β) (fun _ => 1)
    (fun _ => hβ) (fun _ y => hp y) (fun _ => zero_le_one)
  simpa using h

end GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimensionLabelBounded
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity

private theorem exists_int_ne_zero_eq_mul_of_ne_zero (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O]
    (s : O) (hs : s ≠ 0) : ∃ n : ℤ, n ≠ 0 ∧ ∃ o : O, o * s = (n : O) := by
  have hI : Ideal.comap (algebraMap ℤ O) (Ideal.span {s}) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hs (Ideal.mem_span_singleton_self s)
      (Algebra.IsIntegral.isIntegral s)
  obtain ⟨n, hn, hn0⟩ := (Submodule.ne_bot_iff _).mp hI
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hn)
  exact ⟨n, hn0, o, by rw [ho]; exact eq_intCast (algebraMap ℤ O) n⟩

private theorem isLocalizedModule_int_restrictScalars_mkLinearMap (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [Module.Finite ℤ O] (X : Type) [AddCommGroup X] [Module O X] :
    IsLocalizedModule (nonZeroDivisors ℤ)
      ((LocalizedModule.mkLinearMap (nonZeroDivisors O) X).restrictScalars ℤ) := by
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · rintro ⟨n, hn⟩
    rw [Module.End.isUnit_iff]
    have hn0 : (n : O) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hn)
    have hu : algebraMap O (FractionRing O) (n : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hn0)
    have key : ∀ v : LocalizedModule (nonZeroDivisors O) X,
        (algebraMap ℤ (Module.End ℤ (LocalizedModule (nonZeroDivisors O) X)) n) v =
          algebraMap O (FractionRing O) (n : O) • v := by
      intro v
      rw [Module.algebraMap_end_apply, algebraMap_smul, Int.cast_smul_eq_zsmul]
    constructor
    · intro a b h
      rw [key, key] at h
      have h2 := congrArg (fun w => (algebraMap O (FractionRing O) (n : O))⁻¹ • w) h
      simpa only [smul_smul, inv_mul_cancel₀ hu, one_smul] using h2
    · intro v
      exact ⟨(algebraMap O (FractionRing O) (n : O))⁻¹ • v, by
        rw [key, smul_smul, mul_inv_cancel₀ hu, one_smul]⟩
  · intro y
    refine LocalizedModule.induction_on (fun m s => ?_) y
    obtain ⟨n, hn0, o, ho⟩ := exists_int_ne_zero_eq_mul_of_ne_zero O s (nonZeroDivisors.ne_zero s.2)
    refine ⟨⟨o • m, ⟨n, mem_nonZeroDivisors_of_ne_zero hn0⟩⟩, ?_⟩
    simp only [Submonoid.smul_def, LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply]
    rw [← Int.cast_smul_eq_zsmul O, LocalizedModule.smul'_mk, ← ho, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, OneMemClass.coe_one, one_smul, mul_smul]
    exact smul_comm _ _ _
  · intro x₁ x₂ h
    simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
      LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    obtain ⟨n, hn0, o, ho⟩ := exists_int_ne_zero_eq_mul_of_ne_zero O u (nonZeroDivisors.ne_zero u.2)
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn0⟩, ?_⟩
    simp only [Submonoid.smul_def, OneMemClass.coe_one, one_smul] at hu ⊢
    rw [← Int.cast_smul_eq_zsmul O, ← Int.cast_smul_eq_zsmul O, ← ho, mul_smul, mul_smul, hu]

private theorem finrank_int_eq_mul_finrank (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [Module.Finite ℤ O] (X : Type) [AddCommGroup X] [Module O X] :
    Module.finrank ℤ X = Module.finrank ℤ O * Module.finrank O X := by
  haveI := isLocalizedModule_int_restrictScalars_mkLinearMap O X
  haveI : CharZero (FractionRing O) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))
  letI : Module ℚ (LocalizedModule (nonZeroDivisors O) X) :=
    Module.compHom _ (algebraMap ℚ (FractionRing O))
  haveI : IsScalarTower ℚ (FractionRing O) (LocalizedModule (nonZeroDivisors O) X) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have e1 : Module.finrank ℤ (LocalizedModule (nonZeroDivisors O) X) = Module.finrank ℤ X :=
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ)
      ((LocalizedModule.mkLinearMap (nonZeroDivisors O) X).restrictScalars ℤ) le_rfl
  have e2 : Module.finrank ℚ (LocalizedModule (nonZeroDivisors O) X) =
      Module.finrank ℤ (LocalizedModule (nonZeroDivisors O) X) :=
    IsFractionRing.finrank_right_eq ℤ ℚ _
  have e3 : Module.finrank ℚ (FractionRing O) *
      Module.finrank (FractionRing O) (LocalizedModule (nonZeroDivisors O) X) =
      Module.finrank ℚ (LocalizedModule (nonZeroDivisors O) X) :=
    Module.finrank_mul_finrank ℚ (FractionRing O) _
  haveI : @IsScalarTower ℤ ℚ (FractionRing O) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have e4 : Module.finrank ℚ (FractionRing O) = Module.finrank ℤ O :=
    IsFractionRing.finrank_eq ℤ ℚ O (FractionRing O)
  have e5 : Module.finrank (FractionRing O) (LocalizedModule (nonZeroDivisors O) X) =
      Module.finrank O (LocalizedModule (nonZeroDivisors O) X) :=
    IsFractionRing.finrank_right_eq O (FractionRing O) _
  have e6 : Module.finrank O (LocalizedModule (nonZeroDivisors O) X) = Module.finrank O X :=
    IsLocalizedModule.finrank_eq (nonZeroDivisors O)
      (LocalizedModule.mkLinearMap (nonZeroDivisors O) X) le_rfl
  rw [← e1, ← e2, ← e3, e4, e5, e6]

theorem finrank_int_eq_fraction_mul (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (K : Type) [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K]
    (X : Type) [AddCommGroup X] [Module O X] :
    Module.finrank ℤ X = Module.finrank ℚ K * Module.finrank O X := by
  rw [finrank_int_eq_mul_finrank O X, IsFractionRing.finrank_eq ℤ ℚ O K]

theorem finrank_int_eq_finrank_mul (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (X : Type) [AddCommGroup X] [Module O X] :
    Module.finrank ℤ X = Module.finrank ℤ O * Module.finrank O X := by
  have : CharZero (FractionRing O) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))
  have h := finrank_int_eq_fraction_mul O (FractionRing O) O
  rw [Module.finrank_self, mul_one] at h
  rw [finrank_int_eq_fraction_mul O (FractionRing O) X, h]

private theorem isTorsionFree_int_of_isTorsionFree (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    (Y : Type) [AddCommGroup Y] [Module O Y] [Module.IsTorsionFree O Y] :
    Module.IsTorsionFree ℤ Y :=
  Module.IsTorsionFree.comap (S := O) (fun r : ℤ => (r : O))
    (fun r hr => IsRegular.of_ne_zero (Int.cast_ne_zero.mpr hr.ne_zero))
    (fun r m => Int.cast_smul_eq_zsmul O r m)

theorem free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    {Y : Type} [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y] : Module.Free ℤ Y := by
  haveI : Module.Finite ℤ Y := Module.Finite.trans O Y
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective O Y)
  have hinj : Function.Injective s := fun a b h => by
    have ha := LinearMap.congr_fun hs a
    have hb := LinearMap.congr_fun hs b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [← ha, ← hb, h]
  haveI : Module.IsTorsionFree O Y :=
    Function.Injective.moduleIsTorsionFree s hinj (fun r m => s.map_smul r m)
  haveI : Module.IsTorsionFree ℤ Y := isTorsionFree_int_of_isTorsionFree O Y
  exact Module.free_of_finite_type_torsion_free'

theorem genRank_le_sq (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] (q : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) :
    genRank γ ≤ (q * Module.finrank ℤ O) ^ 2 := by
  haveI : Module.IsTorsionFree ℤ O := isTorsionFree_int_of_isTorsionFree O O
  haveI : Module.Free ℤ O := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  haveI : Module.Free ℤ X := free_int_of_projective O
  have hX' : Module.finrank ℤ X ≤ q * Module.finrank ℤ O := by
    rw [finrank_int_eq_finrank_mul O X, mul_comm]
    exact Nat.mul_le_mul_right _ hX
  show Module.finrank ℤ (Submodule.span ℤ (Set.range γ)) ≤ _
  calc Module.finrank ℤ (Submodule.span ℤ (Set.range γ))
      ≤ Module.finrank ℤ (LinearMap.BilinForm ℤ X) := Submodule.finrank_le _
    _ = Module.finrank ℤ X * Module.finrank ℤ X := by
      show Module.finrank ℤ (X →ₗ[ℤ] X →ₗ[ℤ] ℤ) = _
      rw [Module.finrank_linearMap, Module.finrank_linearMap, Module.finrank_self, mul_one]
    _ ≤ (q * Module.finrank ℤ O) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hX' hX'

private theorem nat_sInf_le_of_forall_le {s : Set ℕ} {N : ℕ} (h : ∀ k ∈ s, k ≤ N) : sInf s ≤ N := by
  rcases s.eq_empty_or_nonempty with hs | ⟨k, hk⟩
  · rw [hs, Nat.sInf_empty]
    exact Nat.zero_le _
  · exact (Nat.sInf_le hk).trans (h k hk)

theorem carrierDim_bounded : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  intro O _ _ _ _ bar _ q ψ lab hC
  refine ⟨(q * Module.finrank ℤ O) ^ 2, ?_⟩
  intro X _ _ _ _ hX β hβ hpos
  rw [hC X hX β hβ hpos]
  exact_mod_cast nat_sInf_le_of_forall_le (fun k hk => by
    obtain ⟨m, γ, -, -, rfl⟩ := hk
    exact genRank_le_sq O q X hX γ)

end GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CmOrdIntId
section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem cmOrd_int_id : CMOrd ℤ id := CMOrd.int

end GlobalTheory.CompanionTheory.Ar.Fan
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsNatCombOfToRealMemRcone
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_nat_comb_of_toReal_mem_rcone (X : Type) [AddCommGroup X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) (hβ : toReal β ∈ rcone γ) :
    ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i := by
  obtain ⟨t, ht0, ht⟩ := hβ
  let vec : X × X → Fin (m + 1) → ℤ := fun p =>
    Fin.snoc (α := fun _ => ℤ) (fun i => γ i p.1 p.2) (-(β p.1 p.2))
  obtain ⟨r, v, hreal, -⟩ :=
    GlobalTheory.MinkWeylReal.cone_orthant_fg (m + 1) ∅ (Set.range vec) Set.finite_empty
  let T : Fin (m + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) t 1
  have hpt : ∀ y z : X, (β y z : ℝ) = ∑ i, t i * (γ i y z : ℝ) := by
    intro y z
    have h := LinearMap.congr_fun (LinearMap.congr_fun ht y) z
    simpa [toReal, LinearMap.sum_apply] using h
  have hT : (∀ i, 0 ≤ T i) ∧ (∀ a ∈ (∅ : Set (Fin (m + 1) → ℤ)), ∑ i, (a i : ℝ) * T i ≤ 0) ∧
      (∀ b ∈ Set.range vec, ∑ i, (b i : ℝ) * T i = 0) := by
    refine ⟨fun i => ?_, fun a ha => absurd ha (Set.notMem_empty a), ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [T]
      · simpa [T] using ht0 j
    · rintro _ ⟨⟨y, z⟩, rfl⟩
      rw [Fin.sum_univ_castSucc]
      simp only [vec, T, Fin.snoc_castSucc, Fin.snoc_last]
      have h2 : ∑ x, ((γ x y z : ℤ) : ℝ) * t x = ∑ i, t i * (γ i y z : ℝ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      have h3 := hpt y z
      push_cast
      linarith
  obtain ⟨c, hc0, hTc⟩ := (hreal T).1 hT
  have hlast : (1 : ℝ) = ∑ k, c k * (v k (Fin.last m) : ℝ) := by
    have h := congrFun hTc (Fin.last m)
    simpa [T, Finset.sum_apply] using h
  have hex : ∃ k, 0 < v k (Fin.last m) := by
    by_contra hno
    push_neg at hno
    have : ∑ k, c k * (v k (Fin.last m) : ℝ) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have : v k (Fin.last m) = 0 := Nat.le_zero.1 (hno k)
        simp [this]
    rw [this] at hlast
    exact one_ne_zero hlast
  obtain ⟨k, hk⟩ := hex
  have hv := (hreal (fun i => (v k i : ℝ))).2
    ⟨Pi.single k 1, fun j => by
      by_cases h : j = k
      · subst h; simp
      · simp [Pi.single_eq_of_ne h], by
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp⟩
  refine ⟨v k (Fin.last m), fun i => v k i.castSucc, hk, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have h := hv.2.2 (vec (y, z)) ⟨(y, z), rfl⟩
  rw [Fin.sum_univ_castSucc] at h
  simp only [vec, Fin.snoc_castSucc, Fin.snoc_last] at h
  have h' : ∑ i, γ i y z * (v k i.castSucc : ℤ) + -(β y z) * (v k (Fin.last m) : ℤ) = 0 := by
    exact_mod_cast h
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul]
  push_cast
  have h2 : ∑ i, (v k i.castSucc : ℤ) * γ i y z = ∑ i, γ i y z * (v k i.castSucc : ℤ) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h2]
  linarith

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntEqZeroOfForallTwoPowDvd
section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem int_eq_zero_of_forall_two_pow_dvd (n : ℤ) (h : ∀ k : ℕ, (2 : ℤ) ^ k ∣ n) : n = 0 := by
  refine Int.eq_zero_of_abs_lt_dvd (h n.natAbs) ?_
  have h1 : n.natAbs < 2 ^ n.natAbs := Nat.lt_two_pow_self
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1

theorem exists_two_pow_smul_of_covers2 {X : Type} [AddCommGroup X] {ι : Type} {a : ι → X}
    (ha : Covers2 a) (d : X →+ X) (hd : ∀ i, d (a i) = 0) (k : ℕ) :
    ∀ y : X, ∃ z : X, d y = ((2 : ℤ) ^ k) • z := by
  induction k with
  | zero => exact fun y => ⟨d y, by simp⟩
  | succ k ih =>
    intro y
    obtain ⟨i, x, rfl⟩ := ha y
    obtain ⟨z, hz⟩ := ih x
    refine ⟨z, ?_⟩
    rw [map_add (f := _), map_add (f := _), hd, hz, zero_add, pow_succ, mul_smul, two_smul]
    simp only [two_smul, smul_add]

theorem addHom_eq_zero_of_covers2 {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {ι : Type} {a : ι → X} (ha : Covers2 a) (d : X →+ X) (hd : ∀ i, d (a i) = 0) : d = 0 := by
  ext y
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective (Finsupp.ext fun j => ?_)
  have : b.repr (d y) j = 0 := by
    refine int_eq_zero_of_forall_two_pow_dvd _ fun k => ?_
    obtain ⟨z, hz⟩ := exists_two_pow_smul_of_covers2 ha d hd k y
    exact ⟨b.repr z j, by rw [hz]; simp⟩
  simpa using this

theorem addHom_ext_of_covers2 {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {ι : Type} {a : ι → X} (ha : Covers2 a) {f g : X →+ X} (h : ∀ i, f (a i) = g (a i)) : f = g := by
  have := addHom_eq_zero_of_covers2 ha (f - g) (fun i => by simp [h i])
  exact sub_eq_zero.mp this

theorem finite_addHom_of_covers2 : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (ι : Type)
    [Finite ι] (a : ι → X), Covers2 a → ∀ F : Set X, F.Finite → {f : X →+ X | ∀ i, f (a i) ∈ F}.Finite := by
  intro X _ _ _ ι _ a ha F hF
  have hT : (Set.pi Set.univ fun _ : ι => F).Finite := Set.Finite.pi fun _ => hF
  refine Set.Finite.of_injOn (f := fun (f : X →+ X) (i : ι) => f (a i)) ?_ ?_ hT
  · exact fun f hf i _ => hf i
  · exact fun f _ g _ h => addHom_ext_of_covers2 ha fun i => congrFun h i

end GlobalTheory.CompanionTheory.Ar.Fan
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsMin2IffFinite
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem isMin2_iff_finite : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (y : X),
    (∀ i x, 0 ≤ u i x x) → ∃ F : Finset X, ∀ B ∈ rcone u,
      (IsMin2 B y ↔ ∀ x ∈ F, B y y ≤ B (y + (x + x)) (y + (x + x))) := by
  intro X _ m u y hu
  obtain ⟨F, hF⟩ := GlobalTheory.dickson_finite_below_every (ι := X) m fun x i => (u i (y + (x + x)) (y + (x + x))).toNat
  refine ⟨F, ?_⟩
  rintro B ⟨t, ht, rfl⟩
  refine ⟨fun h x _ => h x, fun h x => ?_⟩
  obtain ⟨x', hx', hle⟩ := hF x
  refine (h x' hx').trans ?_
  have hval : ∀ a : X, (∑ i, t i • toReal (u i)) a a = ∑ i, t i * (u i a a : ℝ) := fun a => by
    simp [LinearMap.sum_apply]
  simp only [hval]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
  have h1 := hle i
  have h2 := hu i (y + (x' + x'))
  have h3 := hu i (y + (x + x))
  simp only at h1
  exact_mod_cast (by omega : u i (y + (x' + x')) (y + (x' + x')) ≤ u i (y + (x + x)) (y + (x + x)))

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsPosDefAddAndMemPsdCone
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y] :
    Module.Finite ℤ Y ∧ Module.Free ℤ Y := by
  have hfin : Module.Finite ℤ Y := Module.Finite.trans O Y
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O Y)
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := Finsupp.linearCombination O id) (fun y => by
    simpa using LinearMap.congr_fun hs y)
  have htf : Module.IsTorsionFree ℤ Y := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n y h
    by_contra hc
    push_neg at hc
    have h1 : ((n : O)) • y = 0 := by rw [Int.cast_smul_eq_zsmul]; exact h
    have h2 : (n : O) • s y = 0 := by rw [← map_smul, h1, map_zero]
    have hy : s y ≠ 0 := fun h0 => hc.2 (hinj (by rw [h0, map_zero]))
    obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hy
    have h3 := DFunLike.congr_fun h2 a
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h3 ha
    exact (mul_ne_zero (Int.cast_ne_zero.2 hc.1) ha) h3
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

theorem sum_nonneg_of_isPosDef {Y ι : Type} [AddCommGroup Y] [Fintype ι] (b : Module.Basis ι ℤ Y)
    {B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ} (h : IsPosDef B) {n : ℕ} (y : Fin n → Y) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * B (y i) (y j) := by
  have hy : ∀ i j, B (y i) (y j) = ∑ k, ∑ l, (b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l) := fun i j => by
    conv_lhs => rw [← b.sum_repr (y i), ← b.sum_repr (y j)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have key : ∑ i, ∑ j, c i * c j * B (y i) (y j) = ∑ k, ∑ l, (∑ i, c i * (b.repr (y i) k : ℝ)) *
      (∑ i, c i * (b.repr (y i) l : ℝ)) * B (b k) (b l) := by
    symm
    simp only [hy, Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ k, ∑ l, ∑ i, ∑ j, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, ∑ i, ∑ j, ∑ l, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [key]
  by_cases hd : (fun k => ∑ i, c i * (b.repr (y i) k : ℝ)) = 0
  · have hd' : ∀ k, ∑ i, c i * (b.repr (y i) k : ℝ) = 0 := fun k => congrFun hd k
    simp [hd']
  · exact ((isPosDef_iff_basis b B).1 h _ hd).le

theorem sum_nonneg_of_mem_psdCone (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X))
    {n : ℕ} (x : Fin n → X) (c : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, c i * c j * B (x i) (x j) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, -, h1, h2⟩ := hB
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  obtain ⟨_, _⟩ := free_int_of_projective O X₁
  simp only [h2]
  exact sum_nonneg_of_isPosDef (Module.Free.chooseBasis ℤ X₁) h1 (fun i => r (x i)) c

theorem isPosDef_add_and_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hB : B ∈ psdCone (bar := bar) (X := X)) (hB₀ : B₀ ∈ realForms bar X) (h₀ : IsPosDef B₀) :
    IsPosDef (B + B₀) ∧ B + B₀ ∈ psdCone (bar := bar) (X := X) := by
  have hpos : IsPosDef (B + B₀) := fun n x hx c hc => by
    have h1 := sum_nonneg_of_mem_psdCone O hB x c
    have h2 := h₀ n x hx c hc
    have h3 : ∑ i, ∑ j, c i * c j * (B + B₀) (x i) (x j) =
        ∑ i, ∑ j, c i * c j * B (x i) (x j) + ∑ i, ∑ j, c i * c j * B₀ (x i) (x j) := by
      simp only [LinearMap.add_apply, mul_add, Finset.sum_add_distrib]
    rw [h3]
    exact add_pos_of_nonneg_of_pos h1 h2
  exact ⟨hpos, hpos.mem_psdCone (add_mem (mem_realForms_of_mem_psdCone hB) hB₀)⟩

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

