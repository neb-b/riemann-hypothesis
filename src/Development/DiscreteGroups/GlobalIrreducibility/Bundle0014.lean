module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.DiscreteGroups.GlobalIrreducibility.EntriesOfMemUnipRad

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def DepthZeroInertiaBig : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (t : G E Ω), t ∈ Ine (F := E) A →
    Formalism.L2.NT.TameCoupled A κ t L.gen →
    ∀ n : ℕ, (n = 1 ∨ 16 * n ^ 2 < g) → ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)), (cls σ).IsCusp →
    ∀ (τ : FDRep ℂ (Gn g n)) (P : (ZMod g)[X]), IsCuspOf L P τ.character →
    GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
    (rc (cls σ)).inePol t = GlobalTheory.SerSys.TameGen.liftPoly L.teich P

theorem big_of_le_nV (D : Formalism.BasicNotions.D7) (k : Fin 2) {n : ℕ} (hn : n ≤ D.R.nV) : 16 * n ^ 2 < D.host.g k := by
  have hg : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := D.ntypes.g_cond k
  have hq := D.host.qd_big
  have ht : 0 < D.R.t := D.R.t_odd.pos
  have hr : 1 ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; have := D.R.two_le_m; omega
  have h2 : 2 ≤ D.host.g k := (D.host.g_prime k).two_le
  have hQ0 : 0 < D.host.QS := by
    rcases Nat.eq_zero_or_pos D.host.QS with h | h
    · rw [h] at hg; simp at hg; omega
    · exact h
  have h16 : 16 ≤ D.host.QS :=
    Nat.le_of_dvd hQ0 ((pow_dvd_pow 2 (m := 4) (by have := D.host.two_le_e; omega)).trans D.host.tower_dvd)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ D.host.g k - 1 := by
    have := Nat.mod_add_div (D.host.g k) (D.host.QS * D.host.q * D.host.d)
    rw [hg] at this
    exact ⟨D.host.g k / (D.host.QS * D.host.q * D.host.d), Nat.sub_eq_of_eq_add' this.symm⟩
  have hle := Nat.le_of_dvd (by omega) hdvd
  have hn' : n ≤ 4 * D.R.t * D.R.r + 1 := by
    unfold Formalism.BasicNotions.Ranks.nV at hn
    nlinarith
  have hq1 : n ≤ D.host.q := by omega
  have hd1 : n ≤ D.host.d := by omega
  have h5 : n * n ≤ D.host.q * D.host.d := Nat.mul_le_mul hq1 hd1
  have h6 : 16 * (D.host.q * D.host.d) ≤ D.host.QS * D.host.q * D.host.d := by
    rw [mul_assoc D.host.QS]
    exact Nat.mul_le_mul_right _ h16
  rw [sq]
  omega

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Filter Topology GlobalTheory.GLp GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}

theorem val_lt_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one, Valued.toNormedField.norm_lt_one_iff]

theorem val_le_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.le_one_iff_le_one, Valued.toNormedField.norm_le_one_iff]

variable {g : ℕ} [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
include hi

theorem norm_lt_of_lt {x : ℚ_[g]} (hx : ‖x‖ < 1) : ‖i x‖ < 1 := by
  have h1 : Tendsto (fun k : ℕ => x ^ k) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx
  have h0 : Tendsto i (𝓝 0) (𝓝 0) := by simpa using hi.tendsto 0
  have h2 : Tendsto (fun k : ℕ => ‖i x‖ ^ k) atTop (𝓝 0) := by
    have := (h0.comp h1).norm
    simpa [Function.comp_def, map_pow, norm_pow] using this
  by_contra hc
  rw [not_lt] at hc
  obtain ⟨k, hk⟩ := (h2.eventually (gt_mem_nhds one_pos)).exists
  exact absurd hk (not_lt.2 (one_le_pow₀ hc))

theorem norm_le_of_le {x : ℚ_[g]} (hx : ‖x‖ ≤ 1) : ‖i x‖ ≤ 1 :=
  GlobalTheory.TypeRec.Model.emb_le w g i.toRingHom hi x hx

theorem norm_lt_iff (x : ℚ_[g]) : ‖i x‖ < 1 ↔ ‖x‖ < 1 := by
  refine ⟨fun h => ?_, norm_lt_of_lt i hi⟩
  by_contra hc
  rw [not_lt] at hc
  have hx0 : x ≠ 0 := fun e => by rw [e, norm_zero] at hc; exact absurd hc (by norm_num)
  have h1 : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hc
  have h2 := norm_le_of_le i hi h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖i x‖ := norm_pos_iff.2 ((map_ne_zero i).2 hx0)
  have := (inv_le_one₀ hpos).1 h2
  exact absurd h (not_lt.2 this)

theorem norm_le_iff (x : ℚ_[g]) : ‖i x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun h => ?_, norm_le_of_le i hi⟩
  by_contra hc
  rw [not_le] at hc
  have hx0 : x ≠ 0 := fun e => by rw [e, norm_zero] at hc; exact absurd hc (by norm_num)
  have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := norm_lt_of_lt i hi h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖i x‖ := norm_pos_iff.2 ((map_ne_zero i).2 hx0)
  have := (inv_lt_one₀ hpos).1 h2
  exact absurd h (not_le.2 this)

theorem valuation_lt_iff (x : ℚ_[g]) : valuation (w.adicCompletion E) (i x) < 1 ↔ ‖x‖ < 1 :=
  (val_lt_iff _).trans (norm_lt_iff i hi x)

theorem valuation_le_iff (x : ℚ_[g]) : valuation (w.adicCompletion E) (i x) ≤ 1 ↔ ‖x‖ ≤ 1 :=
  (val_le_iff _).trans (norm_le_iff i hi x)


omit hi in
theorem exists_ker_red {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ_[g])
    (h : ∀ a b, ‖M a b - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b‖ < 1) :
    ∃ k : GL (Fin n) ℤ_[g], red g n k = 1 ∧ (inc g n k : Matrix (Fin n) (Fin n) ℚ_[g]) = M := by
  have hM : ∀ a b, ‖M a b‖ ≤ 1 := by
    intro a b
    have h1 := h a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq] at h1
      have := IsUltrametricDist.norm_add_le_max (M a a - 1) (1 : ℚ_[g])
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le h1.le le_rfl)
    · rw [Matrix.one_apply_ne hab, sub_zero] at h1
      exact h1.le
  let A : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b => ⟨M a b, hM a b⟩
  have hA : (PadicInt.toZMod (p := g)).mapMatrix A = 1 := by
    ext a b
    have hmem : A a b - (1 : Matrix (Fin n) (Fin n) ℤ_[g]) a b ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      have hc : ((A a b - (1 : Matrix (Fin n) (Fin n) ℤ_[g]) a b : ℤ_[g]) : ℚ_[g]) =
          M a b - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b := by
        rw [PadicInt.coe_sub]
        by_cases hab : a = b
        · subst hab; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, PadicInt.coe_one]
        · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, PadicInt.coe_zero]
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def, hc]
      exact h a b
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hmem]
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  have hd : IsUnit A.det := by
    by_contra hn
    have hk : A.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact mem_nonunits_iff.2 hn
    rw [RingHom.mem_ker, RingHom.map_det, hA, Matrix.det_one] at hk
    exact one_ne_zero hk
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hd
  refine ⟨u, Units.ext ?_, ?_⟩
  · show (PadicInt.toZMod (p := g)).mapMatrix (u : Matrix (Fin n) (Fin n) ℤ_[g]) = 1
    rw [hu, hA]
  · show (algebraMap ℤ_[g] ℚ_[g]).mapMatrix (u : Matrix (Fin n) (Fin n) ℤ_[g]) = M
    rw [hu]
    ext a b
    rfl

theorem map_mem_KOne {n : ℕ} (k : GL (Fin n) ℤ_[g]) (hk : red g n k = 1) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) ∈ KOne (w.adicCompletion E) (Fin n) := by
  rw [GlobalTheory.StepData.mem_KOne]
  intro a b
  have hk' : PadicInt.toZMod (k.val a b) = (1 : Matrix (Fin n) (Fin n) (ZMod g)) a b :=
    congrArg (fun x : GL (Fin n) (ZMod g) => (x : Matrix (Fin n) (Fin n) (ZMod g)) a b) hk
  have hn : ‖((k.val a b : ℤ_[g]) : ℚ_[g]) - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b‖ < 1 := by
    have hmem : k.val a b - (1 : Matrix (Fin n) (Fin n) ℤ_[g]) a b ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [RingHom.mem_ker, map_sub, hk']
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have hc : ((k.val a b - (1 : Matrix (Fin n) (Fin n) ℤ_[g]) a b : ℤ_[g]) : ℚ_[g]) =
        ((k.val a b : ℤ_[g]) : ℚ_[g]) - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b := by
      rw [PadicInt.coe_sub]
      by_cases hab : a = b
      · subst hab; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, PadicInt.coe_one]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, PadicInt.coe_zero]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def, hc] at hmem
    exact hmem
  have hv := (valuation_lt_iff i hi _).2 hn
  have e : ((Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k)).val - 1) a b =
      i (((k.val a b : ℤ_[g]) : ℚ_[g]) - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b) := by
    rw [Matrix.sub_apply, map_sub]
    refine congrArg₂ (· - ·) rfl ?_
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e]
  exact hv

theorem exists_of_mem_KOne {n : ℕ} {m : GL (Fin n) (w.adicCompletion E)}
    (hm : m ∈ KOne (w.adicCompletion E) (Fin n)) :
    ∃ k : GL (Fin n) ℤ_[g], red g n k = 1 ∧ Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) = m := by
  have h1 := GlobalTheory.StepData.mem_KOne.1 hm
  obtain ⟨k, hk, hk'⟩ := exists_ker_red (i.symm.toRingHom.mapMatrix m.val) (fun a b => by
    have e : (i.symm.toRingHom.mapMatrix m.val) a b - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b =
        i.symm ((m.val - 1) a b) := by
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab, map_sub]
    rw [e, ← valuation_lt_iff i hi, RingEquiv.apply_symm_apply]
    exact h1 a b)
  refine ⟨k, hk, Units.ext (Matrix.ext fun a b => ?_)⟩
  change i ((inc g n k : Matrix (Fin n) (Fin n) ℚ_[g]) a b) = m.val a b
  rw [hk']
  simp

end DiscreteGroups.sglob.DzIso
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.RankOneTopLeftZero
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem conj_colU (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (c : Fin n → k) :
    x⁻¹ * colU j c * x = colU j (colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  have hYX : Y * X = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYC : Y * colM j c = colM j (colMul j Y c) := by
    ext i b
    rw [Matrix.mul_apply, colM_apply]
    by_cases hb : b.val = j
    · simp only [colM_apply, hb, and_true]
      by_cases hi : i.val < j
      · rw [if_pos hi, colMul]
        exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun a _ => ?_
        split_ifs with ha
        · rw [hy i a (Or.inl (by omega)), one_apply_ne (by intro e; rw [e] at hi; omega), zero_mul]
        · rw [mul_zero]
    · simp [colM_apply, hb]
  have hCX : ∀ d : Fin n → k, colM j d * X = colM j d := by
    intro d
    ext i l
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · rw [hx _ l (Or.inl le_rfl)]
      by_cases hl : (⟨j, hj⟩ : Fin n) = l
      · rw [← hl, one_apply_eq, mul_one]
      · rw [one_apply_ne hl, mul_zero, colM_apply, if_neg (fun h => hl (Fin.ext h.2.symm))]
    · intro b _ hb
      rw [colM_apply, if_neg (fun h => hb (Fin.ext h.2)), zero_mul]
    · simp
  ext : 1
  rw [Units.val_mul, Units.val_mul, val_colU, val_colU, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hYX, hYC, hCX]

def i0 (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) : Fin n := ⟨j - 1, by omega⟩

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k)

def vrow : Fin n → k := fun l => if l.val < j then ξ l - (if l = i0 j hj hj1 then 1 else 0) else 0

def R1 : Matrix (Fin n) (Fin n) k := Matrix.of fun i l => if i = i0 j hj hj1 then vrow j hj hj1 ξ l else 0

theorem rankOne_mul_self : R1 j hj hj1 ξ * R1 j hj hj1 ξ = (vrow j hj hj1 ξ (i0 j hj hj1)) • R1 j hj hj1 ξ := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (i0 j hj hj1)]
  · simp only [R1, of_apply, Matrix.smul_apply, smul_eq_mul, if_true]
    split_ifs <;> ring
  · intro b _ hb; simp [R1, hb]
  · simp

theorem rowVector_at_index : vrow j hj hj1 ξ (i0 j hj hj1) = ξ (i0 j hj hj1) - 1 := by
  simp [vrow, i0, show j - 1 < j by omega]

theorem rankOne_top_left_zero : ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → R1 j hj hj1 ξ i l = 0 := by
  intro i l h
  simp only [R1, of_apply]
  split_ifs with hi
  · have : ¬ l.val < j := by rw [hi] at h; simp [i0] at h; omega
    simp [vrow, this]
  · rfl

end RankOne

end DiscreteGroups.sglob.LConvGenM
end
end

