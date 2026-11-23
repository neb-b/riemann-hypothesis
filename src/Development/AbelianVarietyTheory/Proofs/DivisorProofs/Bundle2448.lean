module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierMonomialMemRadicalExtendedMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1774
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemIndexZeroCoefficientApprox
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.UnitZero

theorem qW_nsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (N : ℕ) (ν : Fin s → X) : qW W β (fun u => N • ν u) = (N : ℤ) ^ 2 * qW W β ν := by
  simp only [qW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [← Nat.cast_smul_eq_nsmul ℤ N (ν u), ← Nat.cast_smul_eq_nsmul ℤ N (ν v), LinearMap.map_smul₂, LinearMap.map_smul,
    smul_eq_mul, smul_eq_mul]
  ring

theorem mono_nsmul {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] {V : Type} [CommRing V]
    (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (ν : Fin s → X) (hν : ∀ k, 0 ≤ qW W (δ k) ν) (N : ℕ) :
    mono W t δ (fun u => N • ν u) = mono W t δ ν ^ (N ^ 2) := by
  simp only [mono]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← pow_mul, qW_nsmul]
  congr 1
  have : (N : ℤ) ^ 2 * qW W (δ k) ν = (((qW W (δ k) ν).toNat * N ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg (hν k)]
    ring
  rw [this, Int.toNat_natCast]

theorem mem_of_forall_mem_pow_sup {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (I : Ideal V) (x : V)
    (h : ∀ j : ℕ, x ∈ maximalIdeal V ^ j ⊔ I) : x ∈ I := by
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (R := V) (M := V ⧸ I) (maximalIdeal V)
    (by simpa only [Ideal.jacobson_bot] using (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal V)))
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hx : Ideal.Quotient.mk I x ∈ ⨅ i : ℕ, maximalIdeal V ^ i • (⊤ : Submodule V (V ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro j
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h j)
    have : Ideal.Quotient.mk I (a + b) = a • Ideal.Quotient.mk I 1 := by
      rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hb, add_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_one,
        _root_.mul_one]
    rw [this]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  rw [hK] at hx
  exact (Submodule.mem_bot _).1 hx

theorem pow_mem_of_radical {V : Type} [CommRing V] (J : Ideal V) {m : ℕ} (t : Fin m → V) {Ix : Type}
    (a : Ix → Fin m → ℕ) (Z : Set Ix) (hrad : ∀ ν ∈ Z, (∏ k, t k ^ a ν k) ∈ J.radical) (e : ℕ) :
    ∃ n, ∀ ν ∈ Z, ∀ M, n ≤ M → (∏ k, t k ^ a ν k) ^ M ∈ J ^ e := by
  classical
  let P : (Fin m → Bool) → V := fun p => ∏ k, t k ^ (if p k then 1 else 0)
  let pat : Ix → Fin m → Bool := fun ν k => decide (0 < a ν k)
  have hdvd : ∀ ν, P (pat ν) ∣ ∏ k, t k ^ a ν k := fun ν =>
    Finset.prod_dvd_prod_of_dvd _ _ fun k _ => pow_dvd_pow _ (by
      by_cases h : 0 < a ν k <;> simp [pat, h] <;> omega)
  have hP : ∀ p, ∃ n, (∃ ν ∈ Z, pat ν = p) → P p ^ n ∈ J := by
    intro p
    by_cases hp : ∃ ν ∈ Z, pat ν = p
    · obtain ⟨ν, hν, rfl⟩ := hp
      have hK : (∏ k, t k ^ a ν k) ∣ P (pat ν) ^ (∑ k, a ν k) := by
        simp only [P]
        rw [← Finset.prod_pow]
        refine Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_
        rw [← pow_mul]
        refine pow_dvd_pow _ ?_
        by_cases h : 0 < a ν k
        · simp only [pat, h, decide_true, if_true, Nat.one_mul]
          exact Finset.single_le_sum (f := a ν) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        · simp only [pat, h, decide_false]
          simp only [Bool.false_eq_true, if_false, Nat.zero_mul]
          omega
      obtain ⟨c, hc⟩ := hK
      have h1 : P (pat ν) ^ (∑ k, a ν k) ∈ J.radical := by
        rw [hc]; exact Ideal.mul_mem_right _ _ (hrad ν hν)
      obtain ⟨n, hn⟩ := Ideal.mem_radical_of_pow_mem h1
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose nP hnP using hP
  refine ⟨(Finset.univ.sup nP) * e, fun ν hν M hM => ?_⟩
  have hle : nP (pat ν) * e ≤ M :=
    le_trans (Nat.mul_le_mul_right _ (Finset.le_sup (f := nP) (Finset.mem_univ _))) hM
  have h1 : P (pat ν) ^ (nP (pat ν) * e) ∈ J ^ e := by
    rw [pow_mul]; exact Ideal.pow_mem_pow (hnP _ ⟨ν, hν, rfl⟩) e
  have h2 : P (pat ν) ^ (nP (pat ν) * e) ∣ (∏ k, t k ^ a ν k) ^ M :=
    (pow_dvd_pow _ hle).trans (pow_dvd_pow_of_dvd (hdvd ν) M)
  obtain ⟨c, hc⟩ := h2
  rw [hc]; exact Ideal.mul_mem_right _ _ h1

end GlobalTheory.Poinc.Sep.UnitZero

namespace GlobalTheory.Poinc.Sep.UnitZero

theorem mem_orbit_zero {O : Type} [CommRing O] {X₀ X : Type} [AddCommGroup X₀] [Module O X₀] [AddCommGroup X]
    [Module O X] {N₁ N : ℕ} {k : X₀ →ₗ[ℤ] X} {Ix : Type} {mu : Ix → X} (h : mu ∈ orbit O N₁ N k (0 : Ix → X₀)) :
    ∀ i, ∃ w, mu i = N • w := by
  obtain ⟨gam, -, -, -, hmu⟩ := h
  intro i
  obtain ⟨w, hw⟩ := hmu i
  exact ⟨w, by simpa using hw⟩

theorem zero_mem_orbit {O : Type} [CommRing O] {X₀ X : Type} [AddCommGroup X₀] [Module O X₀] [AddCommGroup X]
    [Module O X] {N₁ N : ℕ} {k : X₀ →ₗ[ℤ] X} {Ix : Type} : (0 : Ix → X) ∈ orbit O N₁ N k (0 : Ix → X₀) :=
  ⟨LinearMap.id, fun c x => ⟨0, by simp⟩, by simp, fun x => ⟨0, by simp⟩, fun i => ⟨0, by simp⟩⟩

end GlobalTheory.Poinc.Sep.UnitZero

namespace GlobalTheory.Poinc.Sep

theorem coeffZero_approx : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ → Φ.Four N₁ → (∀ y y', Φ.m y ≠ 1 → Φ.m y' ≠ 1 → y = y') → ∀ (c₀ : Φ.Q) (e : ℕ), ∃ a : A, ∀ y, Φ.ev y a - Φ.u y 0 c₀ ∈ (maximalIdeal A ^ e).map (Φ.ev y) := by
  intro O _ bar q s W A _ _ Φ N₁ h3 hEx hLam hFour huniq c₀ e
  classical
  rcases isEmpty_or_nonempty Φ.Y with hY | ⟨⟨y₀⟩⟩
  · exact ⟨0, fun y => (IsEmpty.false y).elim⟩
  obtain ⟨cW, hcW, hqW⟩ := QWDom.qW_ge s W Φ.posW
  obtain ⟨C, hC⟩ := hLam
  have hnn : ∀ y (k : Fin (Φ.m y)) (ν : Fin s → Φ.X y), 0 ≤ qW W (Φ.δ y k) ν := fun y k ν =>
    GlobalTheory.Poinc.qW_nonneg Φ.posW (Φ.bal y k).1 (Φ.nonneg y k) ν
  have hspec : ∃ n : ℕ, ∀ y, Φ.m y ≠ 1 → ∀ ν : Fin s → Φ.X y, ν ≠ 0 → ∀ M, n ≤ M →
      mono W (Φ.t y) (Φ.δ y) ν ^ M ∈ (maximalIdeal A ^ e).map (Φ.ev y) := by
    by_cases h : ∃ y₁, Φ.m y₁ ≠ 1
    · obtain ⟨y₁, hy₁⟩ := h
      obtain ⟨n, hn⟩ := UnitZero.pow_mem_of_radical ((maximalIdeal A).map (Φ.ev y₁)) (Φ.t y₁)
        (fun ν k => (qW W (Φ.δ y₁ k) ν).toNat) {ν | ν ≠ 0}
        (fun ν hν => _root_.GlobalTheory.Poinc.RadQ.mono_mem_radical O bar q s W A Φ N₁ h3 hEx y₁ ν hν) e
      refine ⟨n, fun y hy => ?_⟩
      obtain rfl := huniq y y₁ hy hy₁
      intro ν hν M hM
      rw [Ideal.map_pow]
      exact hn ν hν M hM
    · exact ⟨0, fun y hy => (h ⟨y, hy⟩).elim⟩
  obtain ⟨n, hn⟩ := hspec
  obtain ⟨N, hN₀, -, k, -, -, hF⟩ := hFour y₀ (n + ⌈((e * C : ℕ) : ℝ) / cW⌉₊ + 1)
  obtain ⟨f, hf⟩ := hF 1 0 (fun _ => c₀) e
  refine ⟨f, fun y => ?_⟩
  have hN2 : N ≤ N ^ 2 := Nat.le_self_pow two_ne_zero N
  have hNc : ((e * C : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 * cW := by
    have h1 : ((e * C : ℕ) : ℝ) / cW ≤ (N : ℝ) ^ 2 := by
      refine (Nat.le_ceil _).trans ?_
      exact_mod_cast (show ⌈((e * C : ℕ) : ℝ) / cW⌉₊ ≤ N ^ 2 by omega)
    rwa [div_le_iff₀ hcW] at h1
  have hmono : ∀ ν : Fin s → Φ.X y, ν ≠ 0 →
      mono W (Φ.t y) (Φ.δ y) (fun v => N • ν v) ∈ (maximalIdeal A ^ e).map (Φ.ev y) := by
    intro ν hν
    by_cases hm : Φ.m y = 1
    · obtain ⟨v, hv⟩ := Function.ne_iff.1 hν
      obtain ⟨i, hi⟩ := Φ.pos y (ν v) hv
      obtain ⟨h, hh, hdiv⟩ := hC y hm i (ν v) hv
      have hexp : e * (C * (Φ.δ y i (ν v) (ν v)).toNat) ≤ (qW W (Φ.δ y i) (fun u => N • ν u)).toNat := by
        have hq := hqW (Φ.X y) (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) ν
        have hsum : Φ.δ y i (ν v) (ν v) ≤ ∑ u, Φ.δ y i (ν u) (ν u) :=
          Finset.single_le_sum (f := fun u => Φ.δ y i (ν u) (ν u)) (fun u _ => Φ.nonneg y i _) (Finset.mem_univ v)
        have hsumR : ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ) ≤ ((∑ u, Φ.δ y i (ν u) (ν u) : ℤ) : ℝ) := by exact_mod_cast hsum
        have hD0 : (0 : ℝ) ≤ ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ) := by exact_mod_cast hi.le
        have hR : ((e * C : ℕ) : ℝ) * ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ) ≤ (N : ℝ) ^ 2 * (qW W (Φ.δ y i) ν : ℝ) := by
          calc ((e * C : ℕ) : ℝ) * ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ)
              ≤ (N : ℝ) ^ 2 * cW * ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ) := mul_le_mul_of_nonneg_right hNc hD0
            _ = (N : ℝ) ^ 2 * (cW * ((Φ.δ y i (ν v) (ν v) : ℤ) : ℝ)) := by ring
            _ ≤ (N : ℝ) ^ 2 * (cW * ((∑ u, Φ.δ y i (ν u) (ν u) : ℤ) : ℝ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumR hcW.le) (by positivity)
            _ ≤ (N : ℝ) ^ 2 * (qW W (Φ.δ y i) ν : ℝ) := mul_le_mul_of_nonneg_left hq (by positivity)
        have hZ : ((e * C : ℕ) : ℤ) * Φ.δ y i (ν v) (ν v) ≤ (N : ℤ) ^ 2 * qW W (Φ.δ y i) ν := by exact_mod_cast hR
        have hpos : 0 ≤ (N : ℤ) ^ 2 * qW W (Φ.δ y i) ν := mul_nonneg (by positivity) (hnn y i ν)
        rw [UnitZero.qW_nsmul, ← Nat.cast_le (α := ℤ), Int.toNat_of_nonneg hpos]
        push_cast
        rw [Int.toNat_of_nonneg hi.le]
        push_cast at hZ
        linarith
      have h1 : Φ.ev y (h ^ e) ∈ (maximalIdeal A ^ e).map (Φ.ev y) := Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hh e)
      have h2 : Φ.ev y (h ^ e) ∣ mono W (Φ.t y) (Φ.δ y) (fun u => N • ν u) := by
        rw [map_pow]
        refine (pow_dvd_pow_of_dvd hdiv e).trans ?_
        rw [← pow_mul]
        refine (pow_dvd_pow _ ((Nat.mul_comm _ _).le.trans hexp)).trans ?_
        unfold mono
        exact Finset.dvd_prod_of_mem (fun k => Φ.t y k ^ (qW W (Φ.δ y k) (fun u => N • ν u)).toNat) (Finset.mem_univ i)
      obtain ⟨c, hc⟩ := h2
      rw [hc]; exact Ideal.mul_mem_right _ _ h1
    · rw [UnitZero.mono_nsmul W (Φ.t y) (Φ.δ y) ν (fun k => hnn y k ν) N]
      exact hn y hm ν hν _ (le_trans (by omega) hN2)
  have hterm : ∀ mu ∈ orbit O N₁ N (k y) (0 : Fin 1 × Fin s → Φ.X y₀), mu ≠ 0 →
      (∏ i : Fin 1, Φ.u y (fun v => mu (i, v)) c₀ * mono W (Φ.t y) (Φ.δ y) (fun v => mu (i, v))) ∈
        (maximalIdeal A ^ e).map (Φ.ev y) := by
    intro mu hmu hmu0
    choose w hw using UnitZero.mem_orbit_zero hmu
    have hν : (fun v => w (0, v)) ≠ 0 := by
      intro h0
      apply hmu0
      funext ⟨i, v⟩
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst hi0
      rw [hw, Pi.zero_apply]
      have := congrFun h0 v
      simp only [Pi.zero_apply] at this
      rw [this, smul_zero]
    rw [Fin.prod_univ_one]
    have : (fun v => mu (0, v)) = fun v => N • w (0, v) := funext fun v => hw _
    rw [this]
    exact Ideal.mul_mem_left _ _ (hmono _ hν)
  have hmem : ∀ j : ℕ, Φ.ev y f - Φ.u y 0 c₀ ∈ maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) := by
    intro j
    obtain ⟨S, hS, htail, hap⟩ := hf y (j + 1)
    have h0 : (0 : Fin 1 × Fin s → Φ.X y) ∈ S := by
      by_contra h0
      have := htail 0 UnitZero.zero_mem_orbit h0
      simp only [lin, qW, Pi.zero_apply, map_zero, LinearMap.zero_apply, mul_zero, Finset.sum_const_zero] at this
      omega
    rw [← Finset.add_sum_erase S _ h0] at hap
    have hz : (∏ i : Fin 1, Φ.u y (fun v => (0 : Fin 1 × Fin s → Φ.X y) (i, v)) c₀ *
        mono W (Φ.t y) (Φ.δ y) (fun v => (0 : Fin 1 × Fin s → Φ.X y) (i, v))) = Φ.u y 0 c₀ := by
      rw [Fin.prod_univ_one]
      show Φ.u y 0 c₀ * mono W (Φ.t y) (Φ.δ y) 0 = Φ.u y 0 c₀
      simp [mono, qW]
    rw [hz] at hap
    have hle : maximalIdeal (Φ.V y) ^ (j + 1) ⊔ (maximalIdeal A ^ e).map (Φ.ev y) ≤
        maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) :=
      sup_le_sup_right (Ideal.pow_le_pow_right (Nat.le_succ j)) _
    have key := Submodule.add_mem _ (hle hap)
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun mu hmu => hterm mu (hS (Finset.mem_of_mem_erase hmu))
        (Finset.ne_of_mem_erase hmu)))
    convert key using 1
    ring
  haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
  exact UnitZero.mem_of_forall_mem_pow_sup _ _ hmem

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCanonicalLiftPrimitiveHodge
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ),
      (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
      ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A) (c : primDR A) (x : G.RigExt),
        GlobalTheory.PtExt.IsCan t c x → G.rigToExt x = 0 → c ∈ PrimitiveSubmodule A := by
  intro p _ R _ N hN A _ hA G t c x hx h0
  have : IsCommMonObj A := hA.comm
  obtain ⟨d, z, w, hz, -, rfl⟩ := hx
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow]; exact hN

  have hmk : (Submodule.Quotient.mk z : G.VecExt) = 0 := h0
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1 hmk
  have hcob : d.coc N = cobOne R (G.A N) (B.1 N) := by
    rw [← hz N, ← hB]; rfl

  have hchiN : chi (p ^ N) d.g (G.A N) (t.y N) = 0 := by
    rw [← Dat.diagSum_coc R A p G t c d N hN, hcob]
    exact diagSum_cobOne_eq_zero p R G N hN (B.1 N)

  have hchi : ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt A D), y ^ (p ^ N) = 1 →
      chi (p ^ N) d.g D y = 0 := by
    intro D _ _ y hy
    obtain ⟨φ, rfl⟩ := t.surj N D y hy
    have h1 : t.y N ^ (p ^ N) = 1 := t.y_pow N
    have hn := chi_natural (p ^ N) R hq A (fv d.f) d.g d.add (G.A N) D φ (t.y N)
    rw [h1, hchiN, map_zero, sub_zero, sub_self] at hn
    exact hn
  have hcoc := (fv_isCoc_and_ev_eq R A d.f).1
  have hsym := isSymCoc_of_isAdd R A hA (fv d.f) d.g d.add
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  obtain ⟨k, hk⟩ := Descent.exists_isCob (p ^ N) R hq A (fv d.f) d.g hcoc d.add hsym hchi
    (fun D _ _ y ↦ PtCover.exists_faithfullyFlat_pow_eq R A hA (p ^ N) hpos D y)
  have hF := (mem_hodgeFiltration_iff_pointwiseCoboundary R A d.f).2 ⟨k, hk⟩
  rw [d.cl] at hF
  exact hF

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEquivariantDeRham
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbDatum

open GlobalTheory.ConjSeq

theorem frobDR_primPull (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (c : primDR B) :
    frobDR p R hR A (primPull (dp0 R) (𝟙 _) f c) = primPull (dp0 R) (𝟙 _) f (frobDR p R hR B c) := by
  have k := (frobMor p R hR B (cast_left p R hR B)).comp (homMor (dp0 R) (𝟙 _) f)
  exact (GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) f) (frobMor p R hR A (cast_left p R hR A)) k (fun _ ↦ rfl)
    (GlobalTheory.VB.frob_naturality p _ f.left _) c).trans
    (GrpMor.pull_pull (frobMor p R hR B (cast_left p R hR B)) (homMor (dp0 R) (𝟙 _) f) k (fun _ ↦ rfl) rfl c).symm

end GlobalTheory.AbDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActsTransitivelyFibresFlatBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalFibre

theorem exists_act_apply_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Finite → IsGal ρ →
    ∀ (Y X : Scheme.{0}) (p : Y ⟶ Sp R) (p' : X ⟶ Sp R') (β : X ⟶ Y), Flat p → IsPullback β p' p (spMap ρ) →
    ∀ (act : Gal ρ → (X ⟶ X)), (∀ σ, act σ ≫ p' = p' ≫ spMap (Gal.hom σ)) → (∀ σ, act σ ≫ β = β) →
    ∀ z₀ z : X, β z₀ = β z → ∃ σ : Gal ρ, act σ z₀ = z := by
  intro R R' _ _ ρ _ hG Y X p p' β hfl hpb act hact hactβ z₀ z hz
  have : Flat p := hfl
  let π : R →+* ρ.range := ρ.rangeRestrict
  have hπ : Function.Surjective π := ρ.rangeRestrict_surjective
  have hfac : spMap ρ = spMap (algebraMap ρ.range R') ≫ spMap π := by
    rw [← Spec.map_comp]; rfl
  have hsq : IsPullback (pullback.fst p (spMap π)) (pullback.snd p (spMap π)) p (spMap π) :=
    IsPullback.of_hasPullback _ _
  let p₀ : X ⟶ pullback p (spMap π) :=
    hsq.lift β (p' ≫ spMap (algebraMap ρ.range R')) (by rw [hpb.w, hfac, Category.assoc])
  have hp₀ : p₀ ≫ pullback.fst p (spMap π) = β := hsq.lift_fst _ _ _
  have hp₀' : p₀ ≫ pullback.snd p (spMap π) = p' ≫ spMap (algebraMap ρ.range R') := hsq.lift_snd _ _ _
  have outer : IsPullback (p₀ ≫ pullback.fst p (spMap π)) p' p (spMap (algebraMap ρ.range R') ≫ spMap π) := by
    rw [hp₀, ← hfac]; exact hpb
  have hpb₀ : IsPullback p₀ p' (Over.mk (pullback.snd p (spMap π))).hom (spMap (algebraMap ρ.range R')) :=
    IsPullback.of_right outer hp₀' hsq
  have hinj : Function.Injective (algebraMap ρ.range R') := Subtype.val_injective
  let toG : Gal (algebraMap ρ.range R') → Gal ρ := fun σ => ⟨σ.1, fun r => σ.2 (π r)⟩
  have hG₀ : IsGal (algebraMap ρ.range R') := by
    refine ⟨?_, fun x hx => ?_⟩
    · have : Finite (Gal ρ) := hG.1
      exact Finite.of_injective toG (fun a b h => Subtype.ext (show a.1 = b.1 from congrArg (fun s : Gal ρ => s.1) h))
    · have hx' : ∀ σ ∈ Gal ρ, σ x = x := fun σ hσ => by
        refine hx σ ?_
        rintro ⟨_, r, rfl⟩
        exact hσ r
      exact ⟨⟨x, hG.2 x hx'⟩, rfl⟩
  have hflat : Flat (Over.mk (pullback.snd p (spMap π))).hom := by
    change Flat (pullback.snd p (spMap π)); infer_instance
  have : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  have hz₀ : p₀ z₀ = p₀ z := by
    apply (pullback.fst p (spMap π)).isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp₀, hz]
  obtain ⟨σ', h, h₁, h₂, h₃⟩ := gal_transitive_on_fibres ρ.range R' hinj hG₀ (Over.mk (pullback.snd p (spMap π)))
    hflat X p₀ p' hpb₀ z₀ z hz₀
  refine ⟨toG σ', ?_⟩
  have he : act (toG σ') = h := by
    refine hpb.hom_ext ?_ ?_
    · rw [hactβ, ← hp₀, ← Category.assoc, h₁]
    · rw [hact, h₂]; rfl
  rw [he, h₃]

end GlobalTheory.Mum.GalFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFromPageEstimate
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem indefinitePoint_splitPartContent_eq_forcedContent (p : PtAt ex Csz) (C CH : ℝ) :
    Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent ((R2 p).num (F2 p) C CH) (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) := by
  intro w j
  rw [numOf_Fj_eq_ofRecord D L p.Del p.h0 p.hDel p.hh0]
  rfl

end Comparison₂

end GlobalTheory.BigOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

variable {X Z : Scheme.{0}} {k : ℕ}

def GermRatioAgree {L : LB X} (v v' : Z ⟶ X) (s₀ : H0 L k) (i i'' : Fin 1 → L.ι) (z : Z) : Prop :=
  v z ∈ secChart L i ∧ v' z ∈ secChart L i'' ∧
    IsUnit (secGerm v z s₀ i) ∧ IsUnit (secGerm v' z s₀ i'') ∧
    ∀ s₁ : H0 L k, secGerm v z s₁ i * secGerm v' z s₀ i'' = secGerm v z s₀ i * secGerm v' z s₁ i''

end GlobalTheory.Mum
end
end

