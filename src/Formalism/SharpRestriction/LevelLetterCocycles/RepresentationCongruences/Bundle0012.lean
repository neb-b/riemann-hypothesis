module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0010

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.QALetterNe
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem phi_smul (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  show W.φD T (a • x) = (letφ W.φ₀ a) • W.φD T x
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]

variable {W} [IsDomain O] [FiniteDimensional Qp LL]

theorem π₀_letter_ne (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : W.π₀ j ≠ 0 := by
  obtain ⟨w, hw⟩ := hR.1
  intro h0
  have h1 : W.π₀ j = (w : LetA O n) j * PowerSeries.X ^ (PD.p - 1) := by
    rw [hw, Pi.mul_apply, Pi.pow_apply]
    rfl
  rw [h1] at h0
  have hu : IsUnit ((w : LetA O n) j) := w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) j)
  have hX : (PowerSeries.X : PowerSeries O) ^ (PD.p - 1) ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  exact hX (hu.mul_right_eq_zero.mp h0)

theorem cancel_π₀ (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) {x y : LetA O n} (h : W.π₀ * x = W.π₀ * y) : x = y := by
  funext j
  have h' := congrFun h j
  simp only [Pi.mul_apply] at h'
  exact mul_left_cancel₀ (π₀_letter_ne hR j) h'

theorem qA_letter_cc (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : constantCoeff (qA W j) = ((PD.p : ℕ) : O) := by
  obtain ⟨w, hw⟩ := hR.1
  have hp2 : 2 ≤ PD.p := PD.hp.two_le
  have h1 : qA W j = (w : LetA O n) j * PowerSeries.X ^ (PD.p - 1) + ((PD.p : ℕ) : PowerSeries O) := by
    show W.π₀ j + (lA W) j = _
    rw [hw, Pi.mul_apply, Pi.pow_apply]
    rfl
  rw [h1, map_add (f := _), map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero, zero_add,
    map_natCast]

theorem qA_letter_ne (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : qA W j ≠ 0 := by
  intro h
  have hc := qA_letter_cc hR j
  rw [h, map_zero] at hc
  have hv := W.v_l
  have h0 : ((PD.p : ℕ) : LL) = 0 := by
    rw [← map_natCast (algebraMap O LL), ← hc, map_zero]
  rw [h0, AddValuation.map_zero] at hv
  simp at hv

theorem w_mem (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) :
    ∃ w ∈ W.AΔ, IsUnit w ∧ W.φA W.π₀ = w * W.π₀ * qA W ^ (PD.p - 1) := by
  obtain ⟨w, hw⟩ := hR.2.1
  have hinv : ∀ g, g ∈ W.DelF → g⁻¹ ∈ W.DelF := by
    intro g hg
    obtain ⟨k, hk, hk'⟩ := (W.DelF_def g).1 hg
    exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hk', inv_one]⟩
  have hmul : ∀ a b, a ∈ W.DelF → b ∈ W.DelF → a * b ∈ W.DelF := by
    intro a b ha hb
    obtain ⟨k, hk, hk'⟩ := (W.DelF_def a).1 ha
    obtain ⟨m, hm, hm'⟩ := (W.DelF_def b).1 hb
    refine (W.DelF_def _).2 ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [mul_pow, pow_mul, hk', one_pow, one_mul, mul_comm k m, pow_mul, hm', one_pow]
  have hπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := by
    intro δ hδ
    funext i
    show W.γ₀ δ W.π₀₁ = W.π₀₁
    unfold Formalism.BasicNotions.LocWach.π₀₁
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sub, map_one, map_natCast, map_sum]
    congr 1
    have hsum : ∀ x ∈ W.DelF, W.γ₀ δ (W.γ₀ x (1 + PowerSeries.X)) = W.γ₀ (δ * x) (1 + PowerSeries.X) := by
      intro x _
      rw [map_mul, AlgHom.mul_apply]
    rw [Finset.sum_congr rfl hsum]
    refine Finset.sum_equiv (Equiv.mulLeft δ) (fun g => ?_) (fun g _ => rfl)
    constructor
    · intro hg
      exact hmul δ g hδ hg
    · intro hg
      have := hmul δ⁻¹ (δ * g) (hinv δ hδ) hg
      rwa [inv_mul_cancel_left] at this
  have hq : ∀ δ ∈ W.DelF, W.γA δ (qA W) = qA W := by
    intro δ hδ
    show W.γA δ (W.π₀ + lA W) = W.π₀ + lA W
    rw [map_add (f := _), hπ δ hδ]
    congr 1
    show W.γA δ ((PD.p : ℕ) : LetA O n) = ((PD.p : ℕ) : LetA O n)
    exact map_natCast _ _
  have hc : ∀ δ (a : LetA O n), W.γA δ (W.φA a) = W.φA (W.γA δ a) := by
    intro δ a
    funext i
    show W.γ₀ δ (W.φ₀ (a (i - 1))) = W.φ₀ (W.γ₀ δ (a (i - 1)))
    rw [W.γ₀_comm]
  refine ⟨w, ?_, w.isUnit, hw⟩
  show ∀ δ ∈ W.DelF, W.γA δ (w : LetA O n) = w
  intro δ hδ
  have e1 := congrArg (W.γA δ) hw
  rw [hc, hπ δ hδ, map_mul, map_mul, map_pow, hπ δ hδ, hq δ hδ, hw] at e1
  funext j
  have e2 := congrFun e1 j
  simp only [Pi.mul_apply, Pi.pow_apply] at e2
  have hne : W.π₀ j * qA W j ^ (PD.p - 1) ≠ 0 :=
    mul_ne_zero (π₀_letter_ne hR j) (pow_ne_zero _ (qA_letter_ne hR j))
  apply mul_left_cancel₀ hne
  linear_combination -e2

theorem coord_mod (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) {T : LocLat G Qp LL O} {i : ZMod n} {d : ℕ} {b : Fin d → W.DD T}
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    ∃ (c₀ : Fin d → O) (z : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T i z ∧
      x = Formalism.MainNotions.LiftingTheory.vecB W T b c₀ + W.π₀ • z := by
  obtain ⟨a, ⟨haA, hxa⟩, -⟩ := hb.2 x hx
  choose F hF using fun m => hR.2.2.2 (a m) (haA m).1
  have hs : HasSubst W.π₀₁ := HasSubst.of_constantCoeff_zero' (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀₁_cc hR)
  let c₀ : Fin d → O := fun m => constantCoeff (F m i)
  let g : Fin d → PowerSeries O := fun m => substAlgHom hs (mk fun k => coeff (k + 1) (F m i))
  let a' : Fin d → LetA O n := fun m => Pi.single i (g m)
  have hzero : ∀ m, ∀ j, j ≠ i → a m j = 0 := by
    intro m j hj
    have := congrFun (haA m).2 j
    simp only [Pi.mul_apply, letE, Pi.single_apply, hj, if_false, zero_mul] at this
    exact this.symm
  have key : ∀ m, a m = algebraMap O (LetA O n) (c₀ m) * letE i + W.π₀ * a' m := by
    intro m
    funext j
    by_cases hj : j = i
    · subst hj
      have e1 : a m j = substAlgHom hs (F m j) := by rw [hF m j, coe_substAlgHom]; rfl
      rw [e1]
      conv_lhs => rw [eq_shift_mul_X_add_const (F m j)]
      rw [map_add (f := _), map_mul, substAlgHom_X hs]
      have e2 : substAlgHom hs (C (constantCoeff (F m j))) = C (constantCoeff (F m j)) := by
        rw [coe_substAlgHom, subst_C]
        rfl
      rw [e2]
      show _ = (algebraMap O (LetA O n) (c₀ m)) j * (letE (O := O) j : LetA O n) j + W.π₀ j * a' m j
      have e3 : (algebraMap O (LetA O n) (c₀ m)) j = C (c₀ m) := rfl
      simp only [e3, letE, a', g, c₀, Pi.single_eq_same, mul_one]
      show _ = C (constantCoeff (F m j)) + W.π₀₁ * _
      ring
    · simp only [Pi.add_apply, Pi.mul_apply, letE, Pi.single_apply, hj, if_false, mul_zero, a', zero_add, hzero m j hj]
  have h1 : ∀ m, W.π₀ * a' m = a m - algebraMap O (LetA O n) (c₀ m) * letE i := by
    intro m
    rw [key m]
    ring
  refine ⟨c₀, ∑ m, a' m • b m, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Submodule.sum_mem _ fun m _ => (W.N T).smul_mem _ (hb.1 m).1.1
  · intro δ hδ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γD_smulA, (hb.1 m).1.2 δ hδ]
    congr 1
    apply cancel_π₀ hR
    calc W.π₀ * W.γA δ (a' m) = W.γA δ (W.π₀ * a' m) := by
          rw [map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀_mem W δ hδ]
      _ = W.γA δ (a m - algebraMap O (LetA O n) (c₀ m) * letE i) := by rw [h1]
      _ = a m - algebraMap O (LetA O n) (c₀ m) * letE i := by
          rw [map_sub, map_mul, (haA m).1 δ hδ, AlgHom.commutes, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_letE]
      _ = W.π₀ * a' m := (h1 m).symm
  · refine ⟨∑ m, a' m • b m, Submodule.sum_mem _ fun m _ => (W.N T).smul_mem _ (hb.1 m).1.1, ?_⟩
    show (letE i : LetA O n) • (∑ m, a' m • b m) = ∑ m, a' m • b m
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [letE, a']
    · simp [letE, a', hj]
  · rw [hxa]
    simp only [Formalism.MainNotions.LiftingTheory.vecB]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hlet : (letE i : LetA O n) • b m = b m := Formalism.MainNotions.N.FrobeniusPowerSeries.TypesD.nl_letter W (hb.1 m).2
    rw [key m, add_smul, mul_smul, hlet, algebraMap_smul, mul_smul]

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RepVVAeval
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

variable (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
  {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL}

theorem RepVV_smulA {a₀ : LetA O n} (ha₀ : a₀ ∈ W.AΔ) {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a₀ • x) (fun k => algebraMap (LetA O n) W.EE a₀ * f k) := by
  obtain ⟨κ, κ', Hh, a, hH, ha, y, hy, hxy⟩ := h
  refine ⟨κ, κ', Hh, fun k => a₀ * a k, hH, fun k => ⟨W.AΔ.mul_mem ha₀ (ha k).1, ?_⟩,
    a₀ • y, Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W ha₀ hy, ?_⟩
  · rw [map_mul, ← (ha k).2]
    ring
  · have hsum : ∑ k, (a₀ * a k) • ((W.φD T) ^ e) (Hh k) = a₀ • ∑ k, a k • ((W.φD T) ^ e) (Hh k) := by
      rw [Finset.smul_sum]
      simp only [smul_smul]
    rw [hsum]
    have e1 : lA W ^ κ' • (lA W ^ κ • Λ • a₀ • x - a₀ • ∑ k, a k • ((W.φD T) ^ e) (Hh k)) =
        a₀ • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) := by
      rw [smul_comm Λ a₀ x, smul_comm (lA W ^ κ) a₀, ← smul_sub, smul_comm (lA W ^ κ') a₀]
    rw [e1, hxy, smul_comm]

theorem RepVV_smulO (o : O) {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (o • x) (fun k => algebraMap O W.EE o * f k) := by
  have h1 := RepVV_smulA W (W.AΔ.algebraMap_mem o) h
  have hx : o • x = algebraMap O (LetA O n) o • x := (algebraMap_smul (LetA O n) o x).symm
  have hf : (fun k => algebraMap O W.EE o * f k) =
      fun k => algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) o) * f k := by
    funext k
    rw [← IsScalarTower.algebraMap_apply]
  rw [hx, hf]
  exact h1

theorem RepVV_zero {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol 0 (fun _ => 0) := by
  obtain ⟨κ, κ', Hh, a, hH, ha, y, hy, hxy⟩ := h
  refine ⟨κ, κ', Hh, fun _ => 0, hH, fun k => ⟨W.AΔ.zero_mem, by simp⟩,
    (0 : LetA O n) • y, Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W W.AΔ.zero_mem hy, by simp⟩

theorem RepVV_sum (h0 : RepVV W T c' e M Λ b sol 0 (fun _ => 0)) {ι : Type} (s : Finset ι)
    (x : ι → W.DD T) (f : ι → Fin d → W.EE) (h : ∀ i ∈ s, RepVV W T c' e M Λ b sol (x i) (f i)) :
    RepVV W T c' e M Λ b sol (∑ i ∈ s, x i) (fun k => ∑ i ∈ s, f i k) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using h0) ?_
  intro j s hj ih h
  have := Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.RepVV_add W (h j (Finset.mem_insert_self j s))
    (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  simpa [Finset.sum_insert hj] using this

theorem RepVV_γ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) (hb : IsHor W T c' b sol)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ)
    (hM : ∃ u ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ M = W.π₀ * Λ ^ 2 * u)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (W.γ T x) (fun k => W.γE W.gam (f k)) := by
  obtain ⟨κ, κ', Hh, a, hH, ha, y, hy, hxy⟩ := h
  obtain ⟨R, hR, R', hR', hRR', hΛR⟩ := hΛ
  obtain ⟨u, hu, hu'⟩ := hpi0
  obtain ⟨u₂, hu₂, hM'⟩ := hM
  have hγH : ∀ k, ∃ z, Formalism.MainNotions.LiftingTheory.InNΔi W T c' z ∧ W.γ T (Hh k) = Hh k + W.π₀ ^ M • z := by
    intro k
    obtain ⟨yy, hyy, hHk⟩ := hH k
    obtain ⟨z, hz, hzeq⟩ := (hb.2 k).1 M κ yy hyy
    refine ⟨z, hz, ?_⟩
    rw [hHk]
    rw [smul_zero, sub_zero, sub_eq_iff_eq_add] at hzeq
    rw [hzeq, add_comm]
  choose z hz hγz using hγH
  have hZ : ∑ k, W.γA W.gam (a k) • ((W.φA ^ e) (W.π₀ ^ M) • ((W.φD T) ^ e) (z k)) =
      (W.π₀ * Λ ^ 2) • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_pow, hM', smul_smul, smul_smul]
    congr 1
    ring
  have h1 := congrArg (W.γ T) hxy
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [γ_smul W, map_sub, map_sum, γA_lA W, γ_φpow W, hγz, map_add (f := _), φpow_smulA W, smul_add,
    Finset.sum_add_distrib, hΛR] at h1
  rw [hZ, map_mul, map_pow, hu', hΛR] at h1
  have hlA : lA W ∈ W.AΔ := by
    unfold lA
    exact W.AΔ.natCast_mem _
  refine ⟨κ, κ', Hh, fun k => R' * W.γA W.gam (a k), hH,
    fun k => ⟨W.AΔ.mul_mem hR' (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_mem W _ (ha k).1), ?_⟩,
    (R' * u * R ^ 2) • W.γ T y + lA W ^ κ' • R' • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k),
    AddSubgroup.add_mem _
      (Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W (W.AΔ.mul_mem (W.AΔ.mul_mem hR' hu) (W.AΔ.pow_mem hR 2))
        (γ_Pp W hT hP2 hy))
      (Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W (W.AΔ.pow_mem hlA κ')
        (Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W hR' (AddSubgroup.sum_mem _ fun k _ =>
          Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.Pp_smul W (W.AΔ.mul_mem (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_mem W _ (ha k).1) hu₂)
            (AddSubgroup.subset_closure ⟨1, W.AΔ.one_mem, z k, hz k, (one_smul _ _).symm⟩)))), ?_⟩
  · have h2 := congrArg (W.γE W.gam) (ha k).2
    rw [map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γE_ι W, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γE_ι W, hΛR, map_mul] at h2
    have h3 : algebraMap (LetA O n) W.EE R' * algebraMap (LetA O n) W.EE R = 1 := by
      rw [← map_mul, mul_comm, hRR', map_one]
    rw [map_mul, ← h2]
    linear_combination (-(algebraMap (LetA O n) W.EE Λ * W.γE W.gam (f k))) * h3
  · have hsH : ∑ k, (R' * W.γA W.gam (a k)) • ((W.φD T) ^ e) (Hh k) =
        R' • ∑ k, W.γA W.gam (a k) • ((W.φD T) ^ e) (Hh k) := by
      rw [Finset.smul_sum]
      simp only [smul_smul]
    have hΛ1 : lA W ^ κ • Λ • W.γ T x = lA W ^ κ • ((R' * R) * Λ) • W.γ T x := by
      rw [mul_comm R' R, hRR', one_mul]
    rw [hsH, hΛ1]
    calc _ = R' • (lA W ^ κ' • (lA W ^ κ • (R * Λ) • W.γ T x -
            (∑ k, W.γA W.gam (a k) • ((W.φD T) ^ e) (Hh k) +
              (W.π₀ * Λ ^ 2) • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k)))) +
          (W.π₀ * Λ ^ 2) • (lA W ^ κ' • R' • ∑ k, (W.γA W.gam (a k) * u₂) • ((W.φD T) ^ e) (z k)) := by
          simp only [smul_sub, smul_add, smul_smul]
          ring_nf
          abel
      _ = _ := by
          rw [h1]
          simp only [smul_add, smul_smul]
          ring_nf

theorem RepVV_iter (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) (hb : IsHor W T c' b sol)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ)
    (hM : ∃ u ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ M = W.π₀ * Λ ^ 2 * u)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) (i : ℕ) :
    RepVV W T c' e M Λ b sol ((W.γ T)^[i] x) (fun k => (W.γE W.gam)^[i] (f k)) := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    have := RepVV_γ W hT hP2 hpi0 hb hΛ hM ih
    simpa [Function.iterate_succ_apply'] using this

theorem RepVV_aeval (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) (hb : IsHor W T c' b sol)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ)
    (hM : ∃ u ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ M = W.π₀ * Λ ^ 2 * u)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) (P : Polynomial O) :
    RepVV W T c' e M Λ b sol (Polynomial.aeval (W.γ T) P x)
      (fun k => Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (f k)) := by
  rw [aeval_eq W P x]
  have hf : (fun k => Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (f k)) =
      fun k => ∑ i ∈ Finset.range (P.natDegree + 1),
        algebraMap O W.EE (P.coeff i) * (W.γE W.gam)^[i] (f k) := by
    funext k
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, Module.End.pow_apply, Algebra.smul_def]
    rfl
  rw [hf]
  exact RepVV_sum W (RepVV_zero W h) _ _ (fun i k => algebraMap O W.EE (P.coeff i) * (W.γE W.gam)^[i] (f k))
    fun i _ => RepVV_smulO W (P.coeff i) (RepVV_iter W hT hP2 hpi0 hb hΛ hM h i)

end Formalism.MainNotions.N.Ln17.PCutBoundRep
end
end

