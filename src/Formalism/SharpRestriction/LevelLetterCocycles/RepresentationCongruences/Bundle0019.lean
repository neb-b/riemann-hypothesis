module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantLeRpowOfThreeLe
public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AcoordSumVecMul
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0014

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PhiSqPi0PowEqPi0LambdaSq
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace ArcLengthTwoLifting

theorem liftΔ [FiniteDimensional Qp LL] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x) (hinj : Function.Injective (algebraMap O LL))
    {T₁ T₂ : LocLat G Qp LL O} (hT₁ : IsCrys PD T₁.ρ) (F : LatHom T₁.L T₂.L) (c : ZMod n) (rr : ℕ)
    (hk : Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr)) (n₂ : W.DD T₂) (hn₂ : InFNc W T₂ c 1 n₂) :
    ∃ n₁, InFNc W T₁ c 1 n₁ ∧ W.map F n₁ = lA W ^ rr • n₂ := by
  classical
  obtain ⟨y₂, hy₂, hy₂c, rfl⟩ := hn₂
  rw [one_smul]
  have hy₂' : y₂ ∈ W.N T₂ ∧ ∀ δ ∈ W.DelF, W.γD T₂ δ y₂ = y₂ := hy₂
  have hNl : y₂ ∈ W.Nl T₂ c :=
    Submodule.mem_map.2 ⟨y₂, hy₂'.1, by rw [LinearMap.smul_apply, LinearMap.id_apply, hy₂c]⟩
  obtain ⟨x₁, hx₁, hx₁F⟩ := Submodule.mem_map.1 (hk y₂ hNl hy₂'.2)
  obtain ⟨z₁, hz₁N, hz₁⟩ := Submodule.mem_map.1 hx₁
  rw [LinearMap.smul_apply, LinearMap.id_apply] at hz₁
  have hx₁N : x₁ ∈ W.N T₁ := by rw [← hz₁]; exact (W.N T₁).smul_mem _ hz₁N
  have hx₁c : (letE c : LetA O n) • x₁ = x₁ := by
    rw [← hz₁, smul_smul, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self]
  have hx₁F' : W.map F x₁ = lA W ^ rr • y₂ := hx₁F
  obtain ⟨-, -, hU⟩ := lemG_units W hcase hP9 hT₁ hO hOv hinj
  set u : Oˣ := hU.unit with hu
  have hγl : ∀ (δ : W.Gam) (x : W.DD T₁),
      W.γD T₁ δ ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T₁ δ x := by
    intro δ x
    rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]
    congr 1
    exact GS.γA_letE W δ c
  set n₁ : W.DD T₁ := ((u⁻¹ : Oˣ) : O) • ∑ δ ∈ W.DelF, W.γD T₁ δ x₁ with hn₁
  refine ⟨n₁, ⟨n₁, ?_, ?_, (one_smul _ _).symm⟩, ?_⟩
  · show n₁ ∈ W.N T₁ ∧ ∀ δ ∈ W.DelF, W.γD T₁ δ n₁ = n₁
    refine ⟨?_, fun δ' hδ' => ?_⟩
    · rw [hn₁, ← algebraMap_smul (LetA O n)]
      exact (W.N T₁).smul_mem _ ((W.N T₁).sum_mem fun δ _ => W.N_Γ T₁ δ x₁ hx₁N)
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hn₁, map_smul, map_sum]
      congr 1
      refine Finset.sum_nbij' (δ' * ·) (δ'⁻¹ * ·) (fun g hg => TypesA.delF_mul W hδ' hg)
        (fun g hg => TypesA.delF_mul W (TypesA.delF_inv W hδ') hg) (fun g _ => by simp)
        (fun g _ => by simp) (fun g _ => ?_)
      rw [W.γD_mul]
  · rw [hn₁, smul_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← hγl, hx₁c]
  · have hγ₂ : ∀ δ ∈ W.DelF, W.γD T₂ δ (W.map F x₁) = lA W ^ rr • y₂ := by
      intro δ hδ
      rw [hx₁F', TypesA.lA_pow_smul, map_nsmul, hy₂'.2 δ hδ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hn₁, ← algebraMap_smul W.EE, map_smul, map_sum]
    simp only [W.map_γ]
    rw [Finset.sum_congr rfl hγ₂, Finset.sum_const, algebraMap_smul, ← Nat.cast_smul_eq_nsmul O, smul_smul]
    have : ((u⁻¹ : Oˣ) : O) * (W.DelF.card : O) = 1 := by
      rw [hu]
      exact hU.val_inv_mul
    rw [this, one_smul]

theorem dvO_single (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (k : Fin d) : dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  unfold dvO
  congr 1
  funext m
  by_cases h : m = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem dv_sum (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    {I : Type*} (s : Finset I) (a : I → LL) (c₀ : I → Fin d → LL) :
    dv W T e b (fun m => ∑ i ∈ s, a i * c₀ i m) = ∑ i ∈ s, a i • dv W T e b (c₀ i) := by
  unfold dv
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem dv_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (a : LL) (c₀ : Fin d → LL) : dv W T e b (fun m => a * c₀ m) = a • dv W T e b c₀ := by
  unfold dv
  simp only [Finset.smul_sum, smul_smul]

theorem coeff_p1_pow_top_isUnit {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {l : ℕ} [Fact l.Prime]
    (P : PhiData O l) (y : ℕ) : IsUnit (PowerSeries.coeff (l * y) (P.p 1 ^ y)) := by
  have hp := P.first_partial_unit_eq_exp
  obtain ⟨S, hS⟩ := sub_dvd_pow_sub_pow (P.p 1) (P.u * PowerSeries.X ^ l) y
  have hdiff : P.p 1 - P.u * PowerSeries.X ^ l = PowerSeries.C (l : O) * P.eps := by rw [hp]; ring
  rw [hdiff] at hS
  have hexp : P.p 1 ^ y = P.u ^ y * PowerSeries.X ^ (l * y) + PowerSeries.C (l : O) * (P.eps * S) := by
    rw [← mul_assoc, ← hS, mul_pow, ← pow_mul]; ring
  rw [hexp, map_add (f := _), PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff (l * y) (P.u ^ y * PowerSeries.X ^ (l * y)) =
      PowerSeries.constantCoeff (P.u ^ y) := by
    have := PowerSeries.coeff_mul_X_pow (P.u ^ y) (l * y) 0
    rw [zero_add, PowerSeries.coeff_zero_eq_constantCoeff] at this
    exact this
  rw [h0]
  have hu : IsUnit (PowerSeries.constantCoeff (P.u ^ y)) := (P.hu.pow y).map _
  by_contra hne
  have hm : PowerSeries.constantCoeff (P.u ^ y) + (l : O) * PowerSeries.coeff (l * y) (P.eps * S) ∈
      IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hne
  have hl : (l : O) * PowerSeries.coeff (l * y) (P.eps * S) ∈ IsLocalRing.maximalIdeal O :=
    Ideal.mul_mem_right _ _ P.hl
  have := (IsLocalRing.maximalIdeal O).sub_mem hm hl
  rw [add_sub_cancel_right] at this
  exact (IsLocalRing.mem_maximalIdeal _).1 this hu


open Formalism.MainNotions.UnusedSlot80.SatW in
theorem isUnit_ps [FiniteDimensional Qp LL] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (s : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (ps W s)) := by
  obtain ⟨hbij, hs, hp⟩ := hcase
  obtain ⟨hring, -⟩ := (hP9 T hT hs hp).2.2 (finrank_one_of_bij' hbij)
  obtain ⟨h3, h6⟩ := ring_clauses W hring
  exact isUnit_EE_of_UPi W (UPi_qpow W h3 h6 s)

theorem phi_sq_pi0_pow_eq_pi0_lambda_sq (W : LocWach PD LL O v n) (hR : GS.RD W) (Λ : LetA O n) (hΛ : Λ ∈ W.AΔ)
    (hΛu : IsUnit (algebraMap (LetA O n) W.EE (W.π₀ * Λ ^ 2))) (G₀ M : ℕ) (u : LetA O n) (hu : u ∈ W.AΔ)
    (hJ : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * G₀) M) = W.π₀ * Λ ^ 2 * u) :
    ∃ N : ℕ, ∃ w ∈ W.AΔ, ((W.φA ^ 2) W.π₀) ^ N = W.π₀ * Λ ^ 2 * w := by
  obtain ⟨h₀, hh₀⟩ := GS.φpow_π₀ (W := W) hR 0
  have h1 : W.φA W.π₀ = W.π₀ * qA W * h₀ := by simpa using hh₀
  have hJJ : Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * G₀) M = W.π₀ ^ M * qA W ^ (2 * G₀) := by
    simp only [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, Formalism.MainNotions.LiftingTheory.pk, pow_zero, AlgHom.one_apply]
    rfl
  have key : ((W.φA ^ 2) W.π₀) ^ (M + 2 * G₀) =
      W.π₀ * Λ ^ 2 * (u * W.φA (W.π₀ ^ (2 * G₀) * qA W ^ M * h₀ ^ (M + 2 * G₀))) := by
    rw [pow_two, AlgHom.mul_apply, h1, ← map_pow,
      show (W.π₀ * qA W * h₀) ^ (M + 2 * G₀) =
        Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * G₀) M * (W.π₀ ^ (2 * G₀) * qA W ^ M * h₀ ^ (M + 2 * G₀)) by rw [hJJ]; ring,
      map_mul, hJ]
    ring
  refine ⟨M + 2 * G₀, _, ?_, key⟩
  apply GS.quot_mem (W := W) (W.AΔ.mul_mem (TypesA.pi0_mem_ADelta W) (W.AΔ.pow_mem hΛ 2)) hΛu
  rw [← key]
  exact W.AΔ.pow_mem (GS.φpow_mem (W := W) 2 (TypesA.pi0_mem_ADelta W)) _

theorem dv_eq_sum_single (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (c₀ : Fin d → LL) : dv W T e b c₀ = ∑ m, c₀ m • dv W T e b (Pi.single m 1) := by
  unfold dv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp), Pi.single_eq_same,
    one_smul]

theorem filS_anti (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ}
    (h : u ≤ u') : FilS W T a s u' ≤ FilS W T a s u :=
  Submodule.map_mono (inf_le_inf_right _ (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h))

theorem sum_unit_inv {R : Type*} [CommRing R] {d₁ d : ℕ} (th : R) (hthu : IsUnit th) (G : Fin d₁ → R)
    (μ : Fin d₁ → Fin d → R) (k₀ : Fin d) (P : R)
    (hcr : ∀ j, ∑ m, G m * μ m j = if j = k₀ then P * th else 0) :
    ∀ j, ∑ m, (↑(hthu.unit⁻¹) * G m) * μ m j = if j = k₀ then P else 0 := by
  intro j
  have h1 : ∑ m, (↑(hthu.unit⁻¹) * G m) * μ m j = ↑(hthu.unit⁻¹) * ∑ m, G m * μ m j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [h1, hcr j]
  by_cases hj : j = k₀
  · rw [if_pos hj, if_pos hj]
    have := hthu.val_inv_mul
    linear_combination P * this
  · rw [if_neg hj, if_neg hj, mul_zero]

theorem crisMap_dvO (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (e : ℕ)
    {d₁ d : ℕ} (b₁ : Fin d₁ → W.DD T₁) (b : Fin d → W.DD T₂) (μ : Fin d₁ → Fin d → O)
    (hμ : ∀ m, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dv W T₁ e b₁ (Pi.single m 1)) = dvO W T₂ e b (μ m))
    (c₁ : Fin d₁ → O) (k₀ : Fin d) (P : O) (hSig : ∀ j, ∑ m, c₁ m * μ m j = if j = k₀ then P else 0) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ e b₁ c₁) = algebraMap O LL P • dv W T₂ e b (Pi.single k₀ 1) := by
  unfold dvO
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dv_eq_sum_single, map_sum]
  simp only [map_smul, hμ]
  unfold dvO
  rw [← dv_sum W T₂ e b Finset.univ (fun m => algebraMap O LL (c₁ m)) (fun m k => algebraMap O LL (μ m k)),
    ← dv_smul]
  congr 1
  funext k
  have h := congrArg (algebraMap O LL) (hSig k)
  simp only [map_sum, map_mul] at h
  by_cases hk : k = k₀
  · subst hk; simpa using h
  · simpa [hk, Pi.single_apply] using h

end ArcLengthTwoLifting

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PhiSqPi0PowPowerSeries
section
open scoped TensorProduct

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

namespace ArcLengthThreeFiltration

open PowerSeries

variable {W : LocWach PD LL O v n} (Br : PhiBridge W)

theorem ea_sub (a : ZMod n) (F F' : PowerSeries O) : ea Br a (F - F') = ea Br a F - ea Br a F' := by
  have h := ea_add Br a (F - F') F'
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem ea_mul_algO (a : ZMod n) (F : PowerSeries O) (x : O) :
    ea Br a F * algebraMap O W.EE x = ea Br a (F * C x) := by
  rw [mul_comm F, ea_C_mul, mul_comm]

theorem ea_mul_cst (a : ZMod n) (F G : PowerSeries O) :
    ea Br a F * algebraMap (LetA O n) W.EE (Br.cst G) = ea Br a (F * G) := by
  rw [mul_comm, cst_mul_ea, mul_comm G]

theorem ea_def (a : ZMod n) (F : PowerSeries O) :
    ea Br a F = algebraMap (LetA O n) W.EE (letE a * 1 * Br.cst F) := by
  unfold ea; rw [mul_one]

theorem inFr_one_ea (a : ZMod n) (G F : PowerSeries O) :
    InFr W a 1 (Br.cst G) (ea Br a F) :=
  ⟨Br.cst (G * F), Br.cst_mem _, by rw [cst_mul_ea, ea_def]⟩

theorem inId_two (a : ZMod n) (α : ℕ → ℤ) (g : W.EE) :
    InId W a 2 α g ↔ InFr W a (Br.cst (X ^ (α 0).toNat * Br.P.p 1 ^ (α 1).toNat))
      (Br.cst (X ^ (-(α 0)).toNat * Br.P.p 1 ^ (-(α 1)).toNat)) g := by
  unfold InId
  rw [prod_two_levels_eq_const Br, prod_two_levels_eq_const Br]

theorem pi0_eq_cst_X_sub_C_prime : W.π₀ = Br.cst (X - C ((PD.p : ℕ) : O)) := Br.π₀_eq

theorem phi_sq_pi0_pow_power_series (h G : ℕ) :
    ∃ N : ℕ, ∃ w ∈ W.AΔ, ((W.φA ^ 2) W.π₀) ^ N = W.π₀ * (Br.cst (X ^ h * Br.P.p 1 ^ G)) ^ 2 * w := by
  have hpF : Fact PD.p.Prime := ⟨PD.hp⟩
  have hl1 : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  set N := 2 * h + 2 * G + 1 with hN
  have hφ2 : (W.φA ^ 2) W.π₀ = Br.cst (Br.P.φ (Br.P.φ (X - C ((PD.p : ℕ) : O)))) := by
    rw [pow_two, AlgHom.mul_apply, pi0_eq_cst_X_sub_C_prime Br, Br.φA_cst, Br.φA_cst]
  have hφφ : Br.P.φ (Br.P.φ (X - C ((PD.p : ℕ) : O))) =
      Br.P.φ Br.P.u * Br.P.u * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) * Br.P.p 1 ^ (PD.p - 1) := by
    rw [Br.P.hφ0, map_mul, map_mul, map_pow, Br.P.hφ0]
    have : Br.P.φ X = Br.P.p 1 := rfl
    rw [this]; ring
  have e1 : (PD.p - 1) * N = 2 * h + ((PD.p - 1) * N - 2 * h) := by
    have : 2 * h ≤ (PD.p - 1) * N := by nlinarith
    omega
  have e2 : (PD.p - 1) * N = 2 * G + ((PD.p - 1) * N - 2 * G) := by
    have : 2 * G ≤ (PD.p - 1) * N := by nlinarith
    omega
  have e3 : N = 1 + (N - 1) := by omega
  refine ⟨N, Br.cst ((Br.P.φ Br.P.u * Br.P.u) ^ N * (X - C ((PD.p : ℕ) : O)) ^ (N - 1) *
      X ^ ((PD.p - 1) * N - 2 * h) * Br.P.p 1 ^ ((PD.p - 1) * N - 2 * G)), Br.cst_mem _, ?_⟩
  rw [hφ2, hφφ, pi0_eq_cst_X_sub_C_prime Br, ← Br.cst_pow, ← Br.cst_pow, ← Br.cst_mul, ← Br.cst_mul]
  congr 1
  have : (Br.P.φ Br.P.u * Br.P.u * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) * Br.P.p 1 ^ (PD.p - 1)) ^ N =
      (Br.P.φ Br.P.u * Br.P.u) ^ N * (X - C ((PD.p : ℕ) : O)) ^ N * X ^ ((PD.p - 1) * N) *
        Br.P.p 1 ^ ((PD.p - 1) * N) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  rw [this, show (X : PowerSeries O) ^ ((PD.p - 1) * N) = X ^ (2 * h) * X ^ ((PD.p - 1) * N - 2 * h) by
      rw [← pow_add, ← e1],
    show Br.P.p 1 ^ ((PD.p - 1) * N) = Br.P.p 1 ^ (2 * G) * Br.P.p 1 ^ ((PD.p - 1) * N - 2 * G) by
      rw [← pow_add, ← e2],
    show (X - C ((PD.p : ℕ) : O)) ^ N = (X - C ((PD.p : ℕ) : O)) * (X - C ((PD.p : ℕ) : O)) ^ (N - 1) by
      rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ N by omega)]]
  ring

theorem coeff_zero_of_coord (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (K h : ℕ)
    (Y D : PowerSeries O) (u : LetA O n) (hu : u ∈ W.AΔ)
    (hK : algebraMap (LetA O n) W.EE (letE a) * (lE W K * ea Br a D) =
      algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Br.cst (X ^ h * Y)) * u)) :
    ∀ j < h, coeff j D = 0 := by
  obtain ⟨U, hU⟩ := letE_mul_AΔ Br a hu
  have e1 : algebraMap (LetA O n) W.EE (letE a) * (lE W K * ea Br a D) =
      ea Br a (C (((PD.p : ℕ) : O) ^ K) * D) := by
    rw [ea_C_mul]; unfold ea
    simp only [lE, map_pow, map_natCast]
    rw [show (algebraMap (LetA O n) W.EE) (letE a) * (((PD.p : ℕ) : W.EE) ^ K *
        (algebraMap (LetA O n) W.EE) (letE a * Br.cst D)) = ((PD.p : ℕ) : W.EE) ^ K *
        (algebraMap (LetA O n) W.EE) ((letE a * letE a) * Br.cst D) by rw [map_mul, map_mul, map_mul]; ring,
      letE_mul_self]
  have e2 : algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Br.cst (X ^ h * Y)) * u) =
      ea Br a ((X - C ((PD.p : ℕ) : O)) * (X ^ h * Y) * U) := by
    unfold ea
    congr 1
    rw [show letE a * (W.π₀ * Br.cst (X ^ h * Y)) * u = (W.π₀ * Br.cst (X ^ h * Y)) * (letE a * u) by ring, hU,
      pi0_eq_cst_X_sub_C_prime Br, Br.cst_mul ((X - C ((PD.p : ℕ) : O)) * (X ^ h * Y)) U,
      Br.cst_mul (X - C ((PD.p : ℕ) : O)) (X ^ h * Y)]
    ring
  rw [e1, e2] at hK
  have hD := ea_inj Br a hK
  intro j hj
  have h1 := congrArg (coeff j) hD
  rw [coeff_C_mul, show (X - C ((PD.p : ℕ) : O)) * (X ^ h * Y) * U = X ^ h * ((X - C ((PD.p : ℕ) : O)) * Y * U) by ring,
    coeff_X_pow_mul', if_neg (by omega)] at h1
  have hpF : Fact PD.p.Prime := ⟨PD.hp⟩
  exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ Br.P.hl0)

theorem dvd_of_not_dvd {x y : O} (h : ¬ y ∣ x) : x ∣ y := by
  by_cases hx : x = 0
  · exact absurd (hx ▸ dvd_zero y) h
  by_cases hy : y = 0
  · exact hy ▸ dvd_zero x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨m', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rcases le_or_gt m m' with hm | hm
  · refine ⟨↑u⁻¹ * u' * ϖ ^ (m' - m), ?_⟩
    rw [show ϖ ^ m' = ϖ ^ m * ϖ ^ (m' - m) by rw [← pow_add, Nat.add_sub_cancel' hm]]
    have : (u : O) * ↑u⁻¹ = 1 := u.mul_inv
    linear_combination (-(↑u' * ϖ ^ m * ϖ ^ (m' - m))) * this
  · exfalso; apply h
    refine ⟨↑u'⁻¹ * u * ϖ ^ (m - m'), ?_⟩
    rw [show ϖ ^ m = ϖ ^ m' * ϖ ^ (m - m') by rw [← pow_add, Nat.add_sub_cancel' hm.le]]
    have : (u' : O) * ↑u'⁻¹ = 1 := u'.mul_inv
    linear_combination (-(↑u * ϖ ^ m' * ϖ ^ (m - m'))) * this

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

