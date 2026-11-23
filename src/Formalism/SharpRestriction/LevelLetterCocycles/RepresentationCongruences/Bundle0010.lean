module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CoefStepOf
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.SatW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem coef_step_of (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ)
    (hgpi0 : ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W))
    (hA2 : ∀ f ∈ W.AΔ, ∃ g ∈ W.AΔ, W.γA W.gam f - f = W.π₀ * qA W * g)
    (hA3 : ∀ k ≥ 1, ∃ g ∈ W.AΔ, W.γA W.gam (ps W k) = ps W k * (1 + W.π₀ * qA W * g))
    (hA4 : ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g)
    (hinj : Function.Injective (algebraMap O LL))
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1)
    (bi : ℕ) (s : W.EE) (s' : LetA O n) (hs' : s' ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k})
    (hs : algebraMap (LetA O n) W.EE (qA W ^ bi) * s = algebraMap (LetA O n) W.EE s')
    (j : ℕ) (hj : j ≤ bi) (g : LetA O n) (hg : g ∈ W.AΔ) :
    ∃ h ∈ W.AΔ, W.γE W.gam (algebraMap (LetA O n) W.EE (qA W ^ j * g) * s) -
        algebraMap (LetA O n) W.EE (qA W ^ j * g) * s =
      algebraMap (LetA O n) W.EE (W.π₀ * qA W ^ j *
        (algebraMap O (LetA O n) (cc ((bi : ℤ) - j)) * g + qA W * h)) * s := by
  obtain ⟨hbij, hs1, hp2⟩ := hcase
  have hfin : Module.finrank K₀ K = 1 := finrank_one_of_bij' hbij
  obtain ⟨-, -, h9c⟩ := hP9 T hT hs1 hp2
  obtain ⟨⟨hπΔ', -, ⟨wπ, hwπ⟩, -⟩, -⟩ := h9c hfin
  have hπ : W.π₀ ∈ W.AΔ := hπΔ'
  have hp1 : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  have hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0 := p_nzd_O W hinj
  have hQe : qA W = W.π₀ + ((PD.p : ℕ) : LetA O n) := rfl
  have hQΔ : qA W ∈ W.AΔ := by rw [hQe]; exact add_mem hπ (natCast_mem _ _)
  have hUπ : UPi PD.p W.π₀ := ⟨wπ, PD.p - 1, 0, by rw [hwπ, mul_zero, add_zero]⟩
  have hUQ : UPi PD.p (qA W) := ⟨wπ, PD.p - 1, 1, by rw [hQe, hwπ, mul_one]⟩
  have hEQ : IsUnit (algebraMap (LetA O n) W.EE (qA W)) := isUnit_EE_of_UPi W hUQ
  have hΓ : ∀ a : LetA O n, W.γE W.gam (algebraMap (LetA O n) W.EE a) =
      algebraMap (LetA O n) W.EE (W.γA W.gam a) := fun a => W.γE_ext W.gam a

  obtain ⟨g4, hg4, h4⟩ := hA4
  obtain ⟨Xc, hXc⟩ : ∃ X : LetA O n, X = algebraMap O (LetA O n) ((W.χΓ W.gam : Oˣ) : O) :=
    ⟨_, rfl⟩
  have hXcΔ : Xc ∈ W.AΔ := by rw [hXc]; exact Subalgebra.algebraMap_mem _ _
  obtain ⟨w, hw⟩ : ∃ w : LetA O n, w = Xc + qA W * g4 := ⟨_, rfl⟩
  have hwΔ : w ∈ W.AΔ := by rw [hw]; exact add_mem hXcΔ (mul_mem hQΔ hg4)
  have h4' : W.γA W.gam (qA W) = qA W * w := by
    rw [h4, hw, hXc, Algebra.smul_def]; ring
  obtain ⟨g5, hg5, h5⟩ := hA2 (qA W) hQΔ
  have hw1 : w = 1 + W.π₀ * g5 := by
    apply W.EE_inj
    apply hEQ.mul_left_cancel
    rw [← map_mul (algebraMap (LetA O n) W.EE), ← map_mul (algebraMap (LetA O n) W.EE)]
    exact congrArg (algebraMap (LetA O n) W.EE) (by linear_combination h5 - h4')

  have hmulw : w * (fun i => PowerSeries.invOfUnit (w i) 1) = 1 := funext fun i => by
    show w i * PowerSeries.invOfUnit (w i) 1 = 1
    refine PowerSeries.mul_invOfUnit (w i) 1 ?_
    rw [hw1, hwπ]
    simp [letπ, zero_pow hp1]
  have hwU : IsUnit w := ⟨⟨w, _, hmulw, by rw [mul_comm]; exact hmulw⟩, rfl⟩
  obtain ⟨wu, hwu⟩ := id hwU
  obtain ⟨wi, hwi⟩ : ∃ x : LetA O n, x = ((wu⁻¹ : (LetA O n)ˣ) : LetA O n) := ⟨_, rfl⟩
  have hwwi : w * wi = 1 := by rw [hwi, ← hwu]; exact wu.mul_inv
  have hwiΔ : wi ∈ W.AΔ := by
    have hwδ : ∀ δ ∈ W.DelF, W.γA δ w = w := hwΔ
    show ∀ δ ∈ W.DelF, W.γA δ wi = wi
    intro δ hδ
    apply hwU.mul_left_cancel
    calc w * W.γA δ wi = W.γA δ w * W.γA δ wi := by rw [hwδ δ hδ]
      _ = W.γA δ (w * wi) := (map_mul (W.γA δ) w wi).symm
      _ = w * wi := by rw [hwwi, map_one]

  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = bi - j := ⟨_, rfl⟩
  have hbi : bi = j + m := by omega
  have e' : -((bi : ℤ) - (j : ℤ)) = -((m : ℕ) : ℤ) := by rw [hm, Nat.cast_sub hj]
  have key : ((((W.χΓ W.gam) ^ m)⁻¹ : Oˣ) : O) = 1 - ((PD.p : ℕ) : O) * cc ((bi : ℤ) - j) := by
    have h0 := hcc ((bi : ℤ) - j)
    rw [e', zpow_neg, zpow_natCast] at h0
    linear_combination -h0
  have hc' : ((W.χΓ W.gam : Oˣ) : O) ^ m * (1 - ((PD.p : ℕ) : O) * cc ((bi : ℤ) - j)) = 1 := by
    rw [← key, ← Units.val_pow_eq_pow_val, Units.mul_inv]
  obtain ⟨C, hC⟩ : ∃ C : LetA O n, C = algebraMap O (LetA O n) (cc ((bi : ℤ) - j)) := ⟨_, rfl⟩
  have hCΔ : C ∈ W.AΔ := by rw [hC]; exact Subalgebra.algebraMap_mem _ _
  have hcA : Xc ^ m * (1 - ((PD.p : ℕ) : LetA O n) * C) = 1 := by
    have := congrArg (algebraMap O (LetA O n)) hc'
    simpa only [map_mul, map_sub, map_one, map_pow, map_natCast, ← hC, ← hXc] using this

  obtain ⟨R1, hR1d⟩ : ∃ R : LetA O n,
      R = (Finset.range m).sum (fun i => w ^ i * Xc ^ (m - 1 - i)) := ⟨_, rfl⟩
  obtain ⟨R2, hR2d⟩ : ∃ R : LetA O n, R = (Finset.range m).sum (fun i => w ^ i) := ⟨_, rfl⟩
  have hR1 : R1 * (w - Xc) = w ^ m - Xc ^ m := by rw [hR1d]; exact geom_sum₂_mul w Xc m
  have hR2 : R2 * (w - 1) = w ^ m - 1 := by rw [hR2d]; exact geom_sum_mul w m
  have hR1Δ : R1 ∈ W.AΔ := by
    rw [hR1d]; exact sum_mem fun i _ => mul_mem (pow_mem hwΔ _) (pow_mem hXcΔ _)
  have hR2Δ : R2 ∈ W.AΔ := by rw [hR2d]; exact sum_mem fun i _ => pow_mem hwΔ _
  obtain ⟨M, hMd⟩ : ∃ M : LetA O n, M = Xc ^ m * C + g4 * R1 * (1 + W.π₀ * C) := ⟨_, rfl⟩
  obtain ⟨N, hNd⟩ : ∃ N : LetA O n, N = g5 * R2 * (1 + W.π₀ * C) + C := ⟨_, rfl⟩
  have hQM : w ^ m * (1 + W.π₀ * C) = 1 + qA W * M := by
    linear_combination (-(1 + W.π₀ * C)) * hR1 + (R1 * (1 + W.π₀ * C)) * hw + hcA -
      (Xc ^ m * C) * hQe - qA W * hMd
  have hπN : w ^ m * (1 + W.π₀ * C) = 1 + W.π₀ * N := by
    linear_combination (-(1 + W.π₀ * C)) * hR2 + (R2 * (1 + W.π₀ * C)) * hw1 - W.π₀ * hNd
  have hpM : ((PD.p : ℕ) : LetA O n) ^ 1 * M = W.π₀ * (N - M) := by
    linear_combination hπN - hQM - M * hQe
  obtain ⟨Z, hZ⟩ := dvd_of_UPi hO hUπ 1 (N - M) M hpM
  have hMZ : M = W.π₀ * Z := by
    apply p_cancel hO
    linear_combination hpM + W.π₀ * hZ
  have hMΔ : M ∈ W.AΔ := by
    rw [hMd]
    exact add_mem (mul_mem (pow_mem hXcΔ _) hCΔ)
      (mul_mem (mul_mem hg4 hR1Δ) (add_mem (one_mem _) (mul_mem hπ hCΔ)))
  have hNΔ : N ∈ W.AΔ := by
    rw [hNd]
    exact add_mem (mul_mem (mul_mem hg5 hR2Δ) (add_mem (one_mem _) (mul_mem hπ hCΔ))) hCΔ
  have hZΔ : Z ∈ W.AΔ := mem_AΔ_of_p_pow W hO 1 (by rw [← hZ]; exact sub_mem hNΔ hMΔ)
  have hYM : w ^ m * (1 + W.π₀ * C) = 1 + qA W * (W.π₀ * Z) := by rw [← hMZ]; exact hQM

  let S : Submonoid (LetA O n) :=
    { carrier := {x | ∃ t ∈ W.AΔ, W.γA W.gam x = x * (1 + W.π₀ * qA W * t)}
      mul_mem' := by
        rintro a b ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        refine ⟨ta + tb + W.π₀ * qA W * ta * tb,
          add_mem (add_mem hta htb) (mul_mem (mul_mem (mul_mem hπ hQΔ) hta) htb), ?_⟩
        rw [map_mul (W.γA W.gam), ha, hb]; ring
      one_mem' := ⟨0, zero_mem _, by simp⟩ }
  have hsub : {x : LetA O n | ∃ k ≥ 1, x = ps W k} ⊆ (S : Set (LetA O n)) := by
    rintro x ⟨k, hk, rfl⟩
    exact hA3 k hk
  have hsS : s' ∈ S := Submonoid.closure_le.mpr hsub hs'
  obtain ⟨t, ht, hts⟩ := hsS

  have h1 := congrArg (W.γE W.gam) hs
  rw [map_mul (W.γE W.gam), hΓ, hΓ, hts, map_pow (W.γA W.gam), h4', mul_pow,
    map_mul (algebraMap (LetA O n) W.EE), map_mul (algebraMap (LetA O n) W.EE), ← hs] at h1
  have hu : IsUnit (algebraMap (LetA O n) W.EE (qA W ^ bi)) := by
    rw [map_pow]; exact hEQ.pow bi
  have h2' : algebraMap (LetA O n) W.EE (w ^ bi) * W.γE W.gam s =
      s * algebraMap (LetA O n) W.EE (1 + W.π₀ * qA W * t) := by
    apply hu.mul_left_cancel
    linear_combination h1
  have hEwb : algebraMap (LetA O n) W.EE w ^ bi * algebraMap (LetA O n) W.EE wi ^ bi = 1 := by
    rw [← mul_pow, ← map_mul, hwwi, map_one, one_pow]
  rw [map_pow] at h2'
  have hΓs : W.γE W.gam s = algebraMap (LetA O n) W.EE wi ^ bi *
      (s * algebraMap (LetA O n) W.EE (1 + W.π₀ * qA W * t)) := by
    linear_combination (algebraMap (LetA O n) W.EE wi ^ bi) * h2' - (W.γE W.gam s) * hEwb

  obtain ⟨g2, hg2, h2⟩ := hA2 g hg
  have hg' : W.γA W.gam g = g + W.π₀ * qA W * g2 := by linear_combination h2
  have hwj : w ^ j * wi ^ j = 1 := by rw [← mul_pow, hwwi, one_pow]
  have hwm1 : w ^ m * wi ^ m = 1 := by rw [← mul_pow, hwwi, one_pow]
  have hwbi : wi ^ bi = wi ^ j * wi ^ m := by rw [← pow_add, ← hbi]
  obtain ⟨h, hh⟩ : ∃ h : LetA O n,
      h = wi ^ m * (g2 + g * t + W.π₀ * qA W * g2 * t - g * Z) := ⟨_, rfl⟩
  have keyA : W.γA W.gam (qA W ^ j * g) * (wi ^ bi * (1 + W.π₀ * qA W * t)) =
      qA W ^ j * g + W.π₀ * qA W ^ j * (C * g + qA W * h) := by
    rw [map_mul (W.γA W.gam), map_pow (W.γA W.gam), h4', hg']
    linear_combination
      ((qA W * w) ^ j * (g + W.π₀ * qA W * g2) * (1 + W.π₀ * qA W * t)) * hwbi +
      (qA W ^ j * (g + W.π₀ * qA W * g2) * (1 + W.π₀ * qA W * t) * wi ^ m) * hwj -
      (qA W ^ j * g * wi ^ m) * hYM + (qA W ^ j * g * (1 + W.π₀ * C)) * hwm1 -
      (W.π₀ * qA W ^ j * qA W) * hh
  have hfin2 : W.γE W.gam (algebraMap (LetA O n) W.EE (qA W ^ j * g) * s) =
      algebraMap (LetA O n) W.EE (qA W ^ j * g + W.π₀ * qA W ^ j * (C * g + qA W * h)) * s := by
    rw [map_mul (W.γE W.gam), hΓ, hΓs, ← keyA]
    simp only [map_mul, map_pow]
    ring
  refine ⟨h, ?_, ?_⟩
  · rw [hh]
    exact mul_mem (pow_mem hwiΔ _) (sub_mem (add_mem (add_mem hg2 (mul_mem hg ht))
      (mul_mem (mul_mem (mul_mem hπ hQΔ) hg2) ht)) (mul_mem hg hZΔ))
  · rw [← hC, hfin2, map_add (f := _)]
    ring

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InFPOfMul
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.FrobeniusPowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace Formalism.MainNotions.N.Ln17.PCutBoundRep

variable (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem γ_smul (a : LetA O n) (x : W.DD T) : W.γ T (a • x) = W.γA W.gam a • W.γ T x :=
  GS.γD_smulA W T W.gam a x

theorem γA_lA (k : ℕ) : W.γA W.gam (lA W ^ k) = lA W ^ k := by
  simp only [lA, map_pow, map_natCast]

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem φpow_smulA (e : ℕ) (a : LetA O n) (x : W.DD T) :
    ((W.φD T) ^ e) (a • x) = (W.φA ^ e) a • ((W.φD T) ^ e) x := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih, φD_smulA, Module.End.mul_apply]
      <;> rfl

theorem γ_φpow (e : ℕ) (x : W.DD T) : W.γ T (((W.φD T) ^ e) x) = ((W.φD T) ^ e) (W.γ T x) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact (W.φγ_comm T W.gam _).symm

theorem γ_Δ {x : W.DD T} (h : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T δ (W.γ T x) = W.γ T x := by
  intro δ hδ
  show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x
  rw [← W.γD_mul, mul_comm, W.γD_mul, h δ hδ]

theorem γ_NΔ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {x : W.DD T} (hx : x ∈ W.NΔ T) :
    W.γ T x ∈ W.NΔ T := by
  have hx' : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx
  show W.γ T x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (W.γ T x) = W.γ T x
  exact ⟨(hP2 T hT).1 W.gam x hx'.1, γ_Δ W hx'.2⟩

theorem γ_NΔi (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (W.γ T x) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨γ_NΔ W hT hP2 h1, ?_⟩
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 h2
  refine Submodule.mem_map.2 ⟨W.γ T z, (hP2 T hT).1 W.gam z hz, ?_⟩
  rw [← hzx]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [γ_smul, GS.γA_letE]

theorem γ_Pp (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {e : ℕ} {y : W.DD T}
    (hy : y ∈ Pp W T c e) : W.γ T y ∈ Pp W T c e := by
  have key : Pp W T c e ≤ (Pp W T c e).comap (W.γ T).toAddMonoidHom := by
    unfold Pp
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    refine AddSubgroup.mem_comap.2 ?_
    show W.γ T (a • ((W.φD T) ^ e) x) ∈ _
    rw [γ_smul, γ_φpow]
    exact AddSubgroup.subset_closure ⟨_, GS.γA_mem W W.gam ha, _, γ_NΔi W hT hP2 hx, rfl⟩
  exact key hy

theorem γ_InFP (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {e : ℕ} {f : LetA O n}
    {x : W.DD T} (h : InFP W T c e f x) : InFP W T c e (W.γA W.gam f) (W.γ T x) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨W.γ T y, γ_Pp W hT hP2 hy, γ_smul W f y⟩

theorem inMultiple_zero {c : ZMod n} {e : ℕ} {f : LetA O n} : InFP W T c e f 0 :=
  ⟨0, (Pp W T c e).zero_mem, (smul_zero f).symm⟩

theorem inMultiple_sum {c : ZMod n} {e : ℕ} {f : LetA O n} {ι : Type} (s : Finset ι) (x : ι → W.DD T)
    (h : ∀ i ∈ s, InFP W T c e f (x i)) : InFP W T c e f (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact inMultiple_zero W
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨y, hy, hxy⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨y', hy', hxy'⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨y + y', (Pp W T c e).add_mem hy hy', by rw [hxy, hxy', smul_add]⟩

theorem InI_γ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T}
    (h : InI W T c w) : InI W T c (W.γ T w) := by
  obtain ⟨h1, h2, ⟨y, hy, hyc, hxy⟩⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  obtain ⟨u, hu, hγπ⟩ := hpi0
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • W.γ T w = W.γ T w
    rw [← GS.γA_letE W W.gam c, ← γ_smul, h1]
  · exact γ_Δ W h2
  · refine ⟨u • W.γ T y, TypesA.NΔ_smul W hu (γ_NΔ W hT hP2 hy), ?_, ?_⟩
    · rw [smul_comm, ← GS.γA_letE W W.gam c, ← γ_smul, hyc]
    · have : W.γ T (W.γ T w) - W.γ T w = W.γ T (W.γ T w - w) := by rw [map_sub]
      rw [this, hxy, γ_smul, hγπ, mul_smul]

theorem InI_smulA {c : ZMod n} {a : LetA O n} (ha : a ∈ W.AΔ) (ha' : W.γA W.gam a = a) {w : W.DD T}
    (h : InI W T c w) : InI W T c (a • w) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (a • w) = a • w
    rw [smul_comm, h1]
  · show ∀ δ ∈ W.DelF, W.γD T δ (a • w) = a • w
    intro δ hδ
    rw [GS.γD_smulA, ha δ hδ, h2 δ hδ]
  · have : W.γ T (a • w) - a • w = a • (W.γ T w - w) := by rw [γ_smul, ha', smul_sub]
    rw [this]
    exact TypesA.InFNc_smul W ha h3

theorem InI_smulO {c : ZMod n} (o : O) {w : W.DD T} (h : InI W T c w) : InI W T c (o • w) := by
  obtain ⟨h1, h2, y, hy, hyl, hyx⟩ := h
  refine ⟨?_, ?_, o • y, (W.NΔ T).smul_mem o hy, ?_, ?_⟩
  · unfold InLet at h1 ⊢
    rw [smul_comm, h1]
  · intro δ hδ
    rw [map_smul, h2 δ hδ]
  · rw [smul_comm, hyl]
  · rw [map_smul, ← smul_sub, hyx, smul_comm]

theorem InI_sum {c : ZMod n} {ι : Type} (s : Finset ι) (x : ι → W.DD T) (h : ∀ i ∈ s, InI W T c (x i)) :
    InI W T c (∑ i ∈ s, x i) := by
  classical
  have hadd : ∀ x y, InI W T c x → InI W T c y → InI W T c (x + y) := by
    rintro x y ⟨hx1, hx2, u, hu, hul, hux⟩ ⟨hy1, hy2, u', hu', hul', hux'⟩
    refine ⟨?_, ?_, u + u', (W.NΔ T).add_mem hu hu', ?_, ?_⟩
    · unfold InLet at hx1 hy1 ⊢
      rw [smul_add, hx1, hy1]
    · intro δ hδ
      rw [map_add (f := _), hx2 δ hδ, hy2 δ hδ]
    · rw [smul_add, hul, hul']
    · rw [map_add (f := _), add_sub_add_comm, hux, hux', smul_add]
  have hzero : InI W T c 0 := ⟨by unfold InLet; rw [smul_zero], fun δ _ => map_zero _, 0,
    (W.NΔ T).zero_mem, smul_zero _, by rw [map_zero, sub_zero, smul_zero]⟩
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hzero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hadd _ _ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem InI_iter (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T} (h : InI W T c w) (i : ℕ) :
    InI W T c ((W.γ T)^[i] w) := by
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Function.iterate_succ_apply']; exact InI_γ W hT hP2 hpi0 ih

theorem aeval_eq (P : Polynomial O) (x : W.DD T) :
    Polynomial.aeval (W.γ T) P x = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (W.γ T)^[i] x := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp [Module.End.pow_apply]

theorem aevalE_eq (P : Polynomial O) (f : W.EE) :
    Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P f =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (W.γE W.gam)^[i] f := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp [Module.End.pow_apply]

theorem InI_aeval (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T} (h : InI W T c w)
    (P : Polynomial O) : InI W T c (Polynomial.aeval (W.γ T) P w) := by
  rw [aeval_eq]
  exact InI_sum W _ _ fun i _ => InI_smulO W _ (InI_iter W hT hP2 hpi0 h i)

end Formalism.MainNotions.N.Ln17.PCutBoundRep
end
end

