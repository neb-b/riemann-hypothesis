module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementarySublatticesOfIndexDegreesQBinomial
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']

namespace WDRep

theorem iso_sum_tensor (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    ((a.sum b).tensor c).Iso ((a.tensor c).sum (b.tensor c)) := by
  refine ⟨TensorProduct.prodLeft ℂ ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      obtain ⟨x₁, x₂⟩ := x
      simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      obtain ⟨x₁, x₂⟩ := x
      simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem iso_tw_tensor (a : WDRep h V) (c : WDRep h V') (s : ℝ) :
    ((a.tw s).tensor c).Iso ((a.tensor c).tw s) :=
  ⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_left], fun _ => rfl⟩

theorem iso_tensor_tw (a : WDRep h V) (c : WDRep h V') (s : ℝ) :
    (a.tensor (c.tw s)).Iso ((a.tensor c).tw s) :=
  ⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_right], fun _ => rfl⟩

theorem iso_tensor_assoc (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    ((a.tensor b).tensor c).Iso (a.tensor (b.tensor c)) := by
  refine ⟨TensorProduct.assoc ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp
      | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [tmul_add, add_tmul, add_assoc]
      | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]

theorem iso_zero_tensor (a : WDRep h V) (c : WDRep h V') [Subsingleton V] (b : WDRep h V'') [Subsingleton V''] :
    (a.tensor c).Iso b := by
  haveI : Subsingleton (V ⊗[ℂ] V') := by
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : V ⊗[ℂ] V', z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [key x, key y]
  exact ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem ρ_eq_one_of_line (c : WDRep h V') (hu : c.Unr) (hd : finrank ℂ V' = 1)
    (hroot : (c.ρ (frob h)).charpoly.IsRoot 1) (σ : Weil h) : c.ρ σ = 1 := by
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot).exists_hasEigenvector
  have hv1 : c.ρ (frob h) v = v := by simpa using hv.apply_eq_smul
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv.2).mp hd
  have hF : c.ρ (frob h) = 1 := LinearMap.ext fun u => by
    obtain ⟨t, rfl⟩ := hspan u
    simp [hv1]
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  have hz : ∀ n : ℤ, c.ρ (frob h ^ n) = 1 := fun n => by
    have h1 : c.ρ.toHomUnits (frob h) = 1 := Units.ext hF
    have h2 : c.ρ.toHomUnits (frob h ^ n) = 1 := by rw [map_zpow, h1, one_zpow]
    exact congrArg Units.val h2
  rw [hτ, map_mul, hz, hu.2 τ, one_mul]

theorem iso_tensor_line (a : WDRep h V) (c : WDRep h V') (hN : c.N = 0) (hd : finrank ℂ V' = 1)
    (hρ : ∀ σ, c.ρ σ = 1) : (a.tensor c).Iso a := by
  let f : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq V' ℂ (by simpa using hd)
  refine ⟨(TensorProduct.congr (.refl ℂ V) f).trans (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hρ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hN]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end WDRep

namespace WD

theorem lpChar_laws (a b c : WD h) (s : ℝ) :
    (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧
    (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧
    a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧
    (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧
    (WD.lpZero (h := h)).lpChar c = WD.lpZero (h := h) ∧
    (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) := by
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
  induction c using ind with
  | hP k c =>
  refine ⟨?_, ?_, ?_, ?_, ?_, fun hu hd he => ?_⟩
  · simp only [lpSum_mk, lpChar_mk]
    exact sound (a.iso_sum_tensor b c)
  · simp only [lpTw_mk, lpChar_mk]
    exact sound (a.iso_tw_tensor c s)
  · simp only [lpTw_mk, lpChar_mk]
    exact sound (a.iso_tensor_tw c s)
  · simp only [lpChar_mk]
    exact sound (a.iso_tensor_assoc b c)
  · simp only [lpZero, lpChar_mk]
    exact sound (WDRep.iso_zero_tensor _ c _)
  · rw [unr_mk] at hu
    rw [lpDim_mk] at hd
    rw [frobEig_mk] at he
    have hroot : (c.ρ (frob h)).charpoly.IsRoot 1 := by
      have h1 : (1 : ℂ) ∈ (c.ρ (frob h)).charpoly.roots := by rw [he]; simp
      exact (Polynomial.mem_roots'.mp h1).2
    rw [lpChar_mk]
    exact sound (a.iso_tensor_line c hu.1 hd (c.ρ_eq_one_of_line hu hd hroot))

end WD

theorem lpChar_laws_closed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h) (s : ℝ),
    (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧
    (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧
    a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧
    (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧
    (WD.lpZero (h := h)).lpChar c = WD.lpZero (h := h) ∧
    (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) :=
  fun _ _ _ _ _ _ _ _ _ _ a b c s => WD.lpChar_laws a b c s

end GlobalTheory.WeilDeligne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NcardSublatticesOfIndexPrimePowerLe
section
noncomputable section

open GlobalTheory.LatHecke

namespace GlobalTheory.SubIdxCount

noncomputable def hc (q : ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hc q r k * q ^ (r * (n - k))

theorem hc_zero_right (q r : ℕ) : hc q r 0 = 1 := by
  induction r with
  | zero => simp [hc]
  | succ r ih => simp [hc, ih]

theorem hc_le (q : ℕ) (hq : 1 ≤ q) (r n : ℕ) : hc q r n ≤ (n + 1) ^ r * (q ^ (r - 1)) ^ n := by
  induction r generalizing n with
  | zero => simp only [hc]; split_ifs <;> simp
  | succ r ih =>
    simp only [hc]
    calc ∑ k ∈ Finset.range (n + 1), hc q r k * q ^ (r * (n - k))
        ≤ ∑ k ∈ Finset.range (n + 1), (n + 1) ^ r * q ^ (r * n) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          calc hc q r k * q ^ (r * (n - k))
              ≤ ((k + 1) ^ r * (q ^ (r - 1)) ^ k) * q ^ (r * (n - k)) :=
                Nat.mul_le_mul_right _ (ih k)
            _ = (k + 1) ^ r * q ^ ((r - 1) * k + r * (n - k)) := by
                rw [← pow_mul, pow_add]; ring
            _ ≤ (n + 1) ^ r * q ^ (r * n) := by
                apply Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
                apply Nat.pow_le_pow_right hq
                have h1 : (r - 1) * k ≤ r * k := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
                have h2 : r * k + r * (n - k) = r * n := by
                  rw [← Nat.mul_add, Nat.add_sub_cancel' hk']
                omega
      _ = (n + 1) ^ (r + 1) * (q ^ (r + 1 - 1)) ^ n := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.add_sub_cancel, ← pow_mul,
            pow_succ]
          ring

theorem one_sub_mul_geom (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X) * PowerSeries.mk (fun n => c ^ n) = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n),
      pow_succ]
    ring

def polP (q r : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range r, (1 - Polynomial.C ((q : ℂ) ^ i) * Polynomial.X)

theorem polP_mul_hc (q r : ℕ) :
    (polP q r : PowerSeries ℂ) * PowerSeries.mk (fun n => (hc q r n : ℂ)) = 1 := by
  induction r with
  | zero =>
    ext n; simp [polP, hc, PowerSeries.coeff_one]
  | succ r ih =>
    have hmk : PowerSeries.mk (fun n => (hc q (r + 1) n : ℂ)) =
        PowerSeries.mk (fun n => (hc q r n : ℂ)) * PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n) := by
      ext n
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (PowerSeries.mk (fun n => (hc q r n : ℂ))) *
          PowerSeries.coeff j (PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n)))]
      simp [hc, pow_mul]
    rw [polP, Finset.prod_range_succ, Polynomial.coe_mul, ← polP, hmk]
    calc (polP q r : PowerSeries ℂ) * ((1 - Polynomial.C ((q : ℂ) ^ r) * Polynomial.X :
          Polynomial ℂ) : PowerSeries ℂ) * (PowerSeries.mk (fun n => (hc q r n : ℂ)) *
            PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n))
        = ((polP q r : PowerSeries ℂ) * PowerSeries.mk (fun n => (hc q r n : ℂ))) *
          (((1 - Polynomial.C ((q : ℂ) ^ r) * Polynomial.X : Polynomial ℂ) : PowerSeries ℂ) *
            PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n)) := by ring
      _ = 1 := by
        rw [ih, one_mul]
        rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
          Polynomial.coe_X]
        exact one_sub_mul_geom ((q : ℂ) ^ r)

theorem coeff_relation (q r n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (polP q r).coeff k * (hc q r (n - k) : ℂ) = 0 := by
  have h := congrArg (PowerSeries.coeff n) (polP_mul_hc q r)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (polP q r : PowerSeries ℂ) *
      PowerSeries.coeff j (PowerSeries.mk (fun n => (hc q r n : ℂ))))] at h
  simpa [PowerSeries.coeff_one, show n ≠ 0 by omega, Polynomial.coeff_coe] using h

end GlobalTheory.SubIdxCount

namespace GlobalTheory.SubIdxCount

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]

theorem elem_coeff (r : ℕ) (L : Lat O K r) (k : ℕ) :
    (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * ((subElem k L).ncard : ℂ) =
      (polP (qRes O) r).coeff k := by
  obtain ⟨-, -, hemp, hX⟩ := _root_.GlobalTheory.LatHecke.subElem_degrees O K r L
  have hQP : (∑ j ∈ Finset.range (r + 1), Polynomial.C ((-1 : ℂ) ^ j *
      (qRes O : ℂ) ^ (j * (j - 1) / 2) * ((subElem j L).ncard : ℂ)) * Polynomial.X ^ j) =
      polP (qRes O) r := by
    apply Polynomial.funext
    intro x
    rw [polP, Polynomial.eval_finsetSum, Polynomial.eval_prod]
    simpa using hX x
  rw [← hQP, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · have : r < k := by simp at hk; omega
    rw [hemp k this]; simp

theorem ncard_subIdx_eq (r : ℕ) : ∀ (n : ℕ) (L : Lat O K r),
    (subIdx n L).ncard = hc (qRes O) r n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [subIdx_zero, Set.ncard_singleton, hc_zero_right]
  have hid := _root_.GlobalTheory.HeckeSeries.heckeSeries_identity O K r ℂ (fun _ => (1 : ℂ)) n L hn
  have hall : ∀ (m : ℕ) (M : Lat O K r),
      heckeAll m (fun _ => (1 : ℂ)) M = ((subIdx m M).ncard : ℂ) := by
    intro m M
    rw [heckeAll_eq_sum, Set.ncard_eq_toFinset_card _ (subIdx_finite m M)]
    simp
  have hterm : ∀ k ∈ Finset.range n,
      ((-1 : ℂ) ^ (k + 1) * (qRes O : ℂ) ^ ((k + 1) * (k + 1 - 1) / 2)) •
        heckeElem (k + 1) (heckeAll (n - (k + 1)) (fun _ => (1 : ℂ))) L =
      (polP (qRes O) r).coeff (k + 1) * (hc (qRes O) r (n - (k + 1)) : ℂ) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hc' : heckeAll (n - (k + 1)) (fun (_ : Lat O K r) => (1 : ℂ)) =
        fun (_ : Lat O K r) => (hc (qRes O) r (n - (k + 1)) : ℂ) := by
      funext M; rw [hall, ih _ (by omega) M]
    rw [hc', heckeElem_eq_sum, Finset.sum_const, ← Set.ncard_eq_toFinset_card _
      (subElem_finite _ L), ← elem_coeff r L (k + 1), smul_eq_mul, nsmul_eq_mul]
    ring
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_range_succ'] at hid
  rw [hsum] at hid
  have hrel := coeff_relation (qRes O) r n hn
  rw [Finset.sum_range_succ'] at hrel
  have h0 := elem_coeff r L 0
  rw [subElem_zero, Set.ncard_singleton] at h0
  rw [heckeElem_zero, hall] at hid
  simp only [pow_zero, zero_mul, Nat.zero_div, Nat.cast_one, mul_one, Nat.sub_zero,
    one_smul] at hid h0
  rw [← h0, one_mul] at hrel
  have : ((subIdx n L).ncard : ℂ) = (hc (qRes O) r n : ℂ) := by
    linear_combination hid - hrel
  exact_mod_cast this

theorem ncard_subIdx_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (n : ℕ) (L : Lat O K r),
    ((subIdx n L).ncard : ℝ) ≤ ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
  intro O K _ _ _ _ _ _ _ r n L
  rw [ncard_subIdx_eq r n L]
  have h := hc_le (qRes O) (one_lt_qRes (O := O)).le r n
  exact_mod_cast h

end GlobalTheory.SubIdxCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataCrystallineAdmissible
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

namespace GlobalTheory

theorem length_H1fT_modPow_le : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ), Module.Finite LL (FiniteCohomology PD ρ) → ∀ n : ℕ, Module.length O (↥(latticeFiniteCocycles PD L) ⧸ ((latticeFiniteCocycles PD L).map ((((PD.p : ℕ) : O) ^ n) • (LinearMap.id : (G → V) →ₗ[O] (G → V))) ⊔ latticeCoboundaries L).comap (latticeFiniteCocycles PD L).subtype) ≤ (n : ℕ∞) * (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * lenOl PD (O := O) + Module.length O ↥(Representation.invariants (repD L)) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ _ _ _ V _ _ _ _ _ _ ρ _ _ _ L hfin n
  set Z := latticeFiniteCocycles PD L with hZdef
  set B' : Submodule O (G → V) := (B1 ρ).restrictScalars O with hB'
  set a : O := ((PD.p : ℕ) : O) ^ n with ha
  have hBB : latticeCoboundaries L ≤ B' := by
    rintro c ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hZT : ∀ c ∈ Z, ∀ g, c g ∈ L.T := by
    intro c hc g
    exact (Submodule.mem_pi.mp hc.1.2) g (Set.mem_univ g)
  have hZf : ∀ c ∈ Z, c ∈ finiteCocycles PD ρ := fun c hc => hc.2
  have h1 := _root_.GlobalTheory.length_quotient_smul_sup_le O (G → V) Z (latticeCoboundaries L) B' a hBB
  have h2 := GlobalTheory.T.length_integral_cocycles_rational_coboundaries_le L Z hZT

  let ψ0 : ↥Z →ₗ[O] ↥(finiteCocycles PD ρ) :=
    { toFun := fun c => ⟨c.1, hZf c.1 c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r c => rfl }
  let ψ : ↥Z →ₗ[O] FiniteCohomology PD ρ :=
    (((B1 ρ).comap (finiteCocycles PD ρ).subtype).mkQ.restrictScalars O).comp ψ0
  have hker : LinearMap.ker ψ = B'.comap Z.subtype := by
    ext c
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  let f := (B'.comap Z.subtype).liftQ ψ hker.ge
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have h3 := _root_.GlobalTheory.length_quotient_smul_range_le_finrank_mul O LL (FiniteCohomology PD ρ) _ f hf a
  have h4 := _root_.GlobalTheory.main O ((PD.p : ℕ) : O) n
  have hl : lenOl PD (O := O) = Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) := rfl
  calc _ ≤ _ := h1
    _ ≤ (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) +
          Module.length O ↥(Representation.invariants (repD L)) := add_le_add h3 h2
    _ ≤ (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * ((n : ℕ∞) * lenOl PD (O := O)) +
          Module.length O ↥(Representation.invariants (repD L)) := by
        rw [hl]; gcongr
    _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitByBaseChange
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splitBy_baseChange : ∀ {Z X V T : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)},
    GlobalTheory.EtC.Tr.SplitBy f y s → ∀ (w : T ⟶ V), GlobalTheory.EtC.Tr.SplitBy f (w ≫ y) (fun j => w ≫ s j) := by
  intro Z X V T f y m s ⟨hs, hiso⟩ w
  have hs' : ∀ j, (w ≫ s j) ≫ f = w ≫ y := fun j => by rw [Category.assoc, hs j]
  refine ⟨hs', ?_⟩

  let c : Cofan (fun _ : Fin m => V) :=
    Cofan.mk (pullback f y) (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp]))
  have hc : IsColimit c := by
    haveI : IsIso ((coproductIsCoproduct (fun _ : Fin m => V)).desc c) := hiso
    exact IsColimit.ofPointIso (coproductIsCoproduct (fun _ : Fin m => V))
  let c' : Cofan (fun _ : Fin m => T) :=
    Cofan.mk (pullback f (w ≫ y)) (fun j => pullback.lift (w ≫ s j) (𝟙 T) (by rw [hs' j, Category.id_comp]))
  let g : pullback f (w ≫ y) ⟶ pullback f y :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w) (by rw [pullback.condition, Category.assoc])
  have hg1 : g ≫ pullback.fst f y = pullback.fst f (w ≫ y) := pullback.lift_fst _ _ _
  have hg2 : g ≫ pullback.snd f y = pullback.snd f (w ≫ y) ≫ w := pullback.lift_snd _ _ _

  have hA : IsPullback (pullback.snd f (w ≫ y)) g w (pullback.snd f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst f y) (v₂₂ := y) (h₃₁ := f) ?_ hg2.symm
      (IsPullback.of_hasPullback f y).flip
    rw [hg1]
    exact (IsPullback.of_hasPullback f (w ≫ y)).flip
  let α : Discrete.functor (fun _ : Fin m => T) ⟶ Discrete.functor (fun _ : Fin m => V) :=
    Discrete.natTrans (fun _ => w)
  have hsq : ∀ j, w ≫ c.ι.app ⟨j⟩ = c'.ι.app ⟨j⟩ ≫ g := by
    intro j
    show w ≫ pullback.lift (s j) (𝟙 V) _ = pullback.lift (w ≫ s j) (𝟙 T) _ ≫ g
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hg1, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hg2, ← Category.assoc, pullback.lift_snd,
        Category.comp_id, Category.id_comp]
  have hcc : α ≫ c.ι = c'.ι ≫ (Functor.const _).map g := by
    ext ⟨j⟩
    exact hsq j
  have hpb : ∀ j, IsPullback (c'.ι.app j) (α.app j) g (c.ι.app j) := by
    rintro ⟨j⟩
    refine IsPullback.of_right (h₁₂ := pullback.snd f (w ≫ y)) (v₁₃ := w) (h₂₂ := pullback.snd f y) ?_ (hsq j).symm hA
    have e1 : c'.ι.app ⟨j⟩ ≫ pullback.snd f (w ≫ y) = 𝟙 T := pullback.lift_snd _ _ _
    have e2 : c.ι.app ⟨j⟩ ≫ pullback.snd f y = 𝟙 V := pullback.lift_snd _ _ _
    rw [e1, e2]
    show IsPullback (𝟙 T) w w (𝟙 V)
    exact IsPullback.id_horiz w
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts hc c' α g hcc
    (NatTrans.Equifibered.of_discrete _) hpb
  have : Sigma.desc (fun j => pullback.lift (w ≫ s j) (𝟙 T) (by rw [hs' j, Category.id_comp])) =
      ((coproductIsCoproduct (fun _ : Fin m => T)).coconePointUniqueUpToIso hc').hom := by
    apply Sigma.hom_ext; intro j
    rw [Sigma.ι_desc]
    exact ((coproductIsCoproduct (fun _ : Fin m => T)).comp_coconePointUniqueUpToIso_hom hc' ⟨j⟩).symm
  rw [this]
  infer_instance

end GlobalTheory.EtC.Tr
end

