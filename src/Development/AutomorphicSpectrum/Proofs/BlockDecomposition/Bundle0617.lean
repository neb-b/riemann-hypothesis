module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictGradedPullNatural
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCell
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem locSec_parab_mir_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) :
    LocSec (parab k (two (stdSum h))) (Mir k (i + t)) 1 := by
  set e := GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) with he
  obtain ⟨b, hbc, hb1, hbw⟩ := GlobalTheory.CompanionTheory.BZRes.exists_rowSec (k := k) (Fin.last (i + t))
  obtain ⟨W, hW⟩ : ∃ W : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k,
      ∀ u, W u = (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) :=
    ⟨fun u : GL (Fin (i + t + 1)) k => (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)),
      fun _ => rfl⟩
  have hWc : Continuous W := by
    have hWeq : W = fun u : GL (Fin (i + t + 1)) k => (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) :=
      funext hW
    rw [hWeq]
    exact continuous_pi fun j =>
      (Units.continuous_coe_inv (M := Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)).matrix_elem
        (Fin.last (i + t)) j
  have hone : (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
      GlobalTheory.BZMir.eLast k (i + t) := by
    funext j
    by_cases hj : j = Fin.last (i + t)
    · subst hj
      simp [GlobalTheory.BZMir.eLast]
    · simp [GlobalTheory.BZMir.eLast, Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]
  have hrow : ∀ q p : GL (Fin (i + t + 1)) k, p ∈ GlobalTheory.BZMir.Mir k (i + t) →
      (↑(q * p)⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
        (↑q⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) := by
    intro q p hp
    have hp' := (GlobalTheory.BZMir.mem_Mir_iff k p⁻¹).1 (Subgroup.inv_mem _ hp)
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply_eq_vecMul, hp']
    simp only [GlobalTheory.BZMir.eLast, Matrix.single_one_vecMul]
    rfl
  have hW1 : W 1 = Pi.single (Fin.last (i + t)) 1 := by
    rw [hW, inv_one, Units.val_one, hone]
    rfl
  have hbW : ContinuousAt (fun u => b (W u)) 1 := by
    refine ContinuousAt.comp (f := W) (g := b) ?_ hWc.continuousAt
    rw [hW1]
    exact hbc
  have hbW1 : b (W 1) = 1 := by rw [hW1, hb1]
  unfold GlobalTheory.CompanionTheory.BZRes.LocSec
  intro OQ hOQ OP hOP
  have h1 : (fun u => (b (W u))⁻¹) ⁻¹' OQ ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    hbW.inv.preimage_mem_nhds (by
      show OQ ∈ 𝓝 (b (W 1))⁻¹
      rw [hbW1, inv_one]
      exact hOQ)
  have h2 : (fun u => b (W u) * u) ⁻¹' OP ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    (hbW.mul continuousAt_id).preimage_mem_nhds (by
      show OP ∈ 𝓝 (b (W 1) * 1)
      rw [hbW1, mul_one]
      exact hOP)
  have h3 : (fun u => W u (Fin.last (i + t))) ⁻¹' {x | x ≠ 0} ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    ((continuous_apply _).comp hWc).continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds (by simp [hW1]))
  refine ⟨_, Filter.inter_mem h1 (Filter.inter_mem h2 h3), ?_⟩
  rintro u ⟨hu1, hu2, hu3⟩ hu
  unfold GlobalTheory.CompanionTheory.BZRes.dcos at hu
  obtain ⟨q, hq, p, hp, hqp⟩ := hu
  simp only [one_mul, mul_one] at hqp
  have hbw' := hbw (W u) hu3
  have hWu : W u = (↑q⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) := by
    rw [hW, hqp]
    exact hrow q p hp
  have hbQ : b (W u) ∈ GlobalTheory.SmGL.parab k e := by
    rw [GlobalTheory.SmGL.mem_parab_iff]
    rintro (_ | _) (_ | _) r c hlt
    all_goals first | exact absurd hlt (by decide) | skip
    rw [hbw']
    by_cases hr : e ⟨true, r⟩ = Fin.last (i + t)
    · rw [hr, Matrix.updateRow_self, hWu, ← hr]
      exact (GlobalTheory.SmGL.mem_parab_iff.1 (Subgroup.inv_mem _ hq)) true false r c hlt
    · rw [Matrix.updateRow_ne hr, Matrix.one_apply_ne]
      intro hrc
      exact absurd (e.injective hrc) (by simp)
  have hpP : b (W u) * u ∈ GlobalTheory.BZMir.Mir k (i + t) := by
    rw [GlobalTheory.BZMir.mem_Mir_iff, Units.val_mul, Matrix.mul_apply_eq_vecMul, hbw', Matrix.updateRow_self, hW,
      ← Matrix.mul_apply_eq_vecMul, Units.inv_mul, hone]
  refine ⟨(b (W u))⁻¹, Subgroup.inv_mem _ hbQ, hu1, b (W u) * u, hpP, hu2, ?_⟩
  simp

end GlobalTheory.CompanionTheory.BZRes

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionOpenCell
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem wPerm_last {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    wPerm h (stdSum h (Sum.inl (Fin.last i))) = Fin.last (i + t) := by
  have e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _
  rw [e, ePG_false_last]

theorem vecMul_wGL {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k))
      (wGL k h : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
  ext c
  rw [Matrix.single_one_vecMul]
  show (1 : Matrix _ _ k) (wPerm h (stdSum h (Sum.inl (Fin.last i)))) c = _
  rw [wPerm_last]
  simp [eLast, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem vecMul_wGL_inv {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (eLast k (i + t)) (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k) := by
  rw [← vecMul_wGL (k := k) h, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem mem_parab_of_row {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k)
    (y : Fin (i + t + 1) → k)
    (hg : (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix _ _ k).updateRow (stdSum h (Sum.inl (Fin.last i))) y) :
    g ∈ parab k (two (stdSum h)) := by
  rw [mem_parab_iff]
  intro a b x z hab
  have hab' : a = true ∧ b = false := by
    clear x z
    revert hab
    cases a <;> cases b <;> decide
  obtain ⟨rfl, rfl⟩ := hab'
  have hne : two (stdSum h) ⟨true, x⟩ ≠ stdSum h (Sum.inl (Fin.last i)) := by
    intro e
    have := (stdSum h).injective e
    simp at this
  have hne2 : two (stdSum h) ⟨true, x⟩ ≠ two (stdSum h) ⟨false, z⟩ := by
    intro e
    have := (two (stdSum h)).injective e
    simp at this
  rw [hg, Matrix.updateRow_ne hne, Matrix.one_apply_ne hne2]

theorem locSec_wGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1) : LocSec (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  intro OQ hOQ OP hOP
  set a₁ := stdSum h (Sum.inl (Fin.last i)) with ha₁
  set w := wGL k h with hw
  obtain ⟨b, hbc, hb1, hb⟩ := exists_rowSec (k := k) a₁
  let y : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k := fun u =>
    vecMul (eLast k (i + t)) (((w * u)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
  have hyc : Continuous y :=
    continuous_const.matrix_vecMul (Units.continuous_val.comp (continuous_const.mul continuous_id).inv)
  have hy1 : y 1 = Pi.single a₁ 1 := by
    simp only [y, mul_one]
    exact vecMul_wGL_inv h
  have hBc : ContinuousAt (fun u => b (y u)) 1 :=
    ContinuousAt.comp (f := y) (g := b) (by rw [hy1]; exact hbc) hyc.continuousAt
  have hB1 : b (y 1) = 1 := by rw [hy1, hb1]
  have hS : ContinuousAt (fun u => (b (y u))⁻¹) 1 := hBc.inv
  have hP : ContinuousAt (fun u => w⁻¹ * b (y u) * w * u) 1 :=
    ((continuousAt_const.mul hBc).mul continuousAt_const).mul continuousAt_id
  have hS' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), (b (y u))⁻¹ ∈ OQ :=
    hS.eventually_mem (by simpa [hB1] using hOQ)
  have hP' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), w⁻¹ * b (y u) * w * u ∈ OP :=
    hP.eventually_mem (by simpa [hB1] using hOP)
  have hne : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), y u a₁ ≠ 0 := by
    have : ContinuousAt (fun u => y u a₁) 1 := ((continuous_apply a₁).comp hyc).continuousAt
    exact this.eventually_ne (by rw [hy1]; simp)
  refine ⟨_, hS'.and (hP'.and hne), ?_⟩
  rintro u ⟨h1, h2, h3⟩ -
  have hBm := hb (y u) h3
  refine ⟨(b (y u))⁻¹, inv_mem (mem_parab_of_row h _ _ hBm), h1, w⁻¹ * b (y u) * w * u, ?_, h2, by group⟩
  show vecMul (eLast k (i + t)) _ = eLast k (i + t)
  have e1 : vecMul (vecMul (eLast k (i + t)) ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k))
      (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = y u := by
    rw [vecMul_wGL_inv h, hBm, Matrix.single_one_vecMul]
    exact Matrix.updateRow_self
  have e2 : vecMul (y u) ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
    simp only [y]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have e3 : ((w⁻¹ * b (y u) * w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
        (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
          ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [e3, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, e1, e2]

end GlobalTheory.CompanionTheory.BZRes

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistence
section
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField Ad3 Ad3.R
open GroundTheory.Global.RationalSymbol (prime unitAt)
open GroundTheory.Automorphic.GodementSection (adeleAt)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelbergQ

open DirichletHecke
open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

theorem mem_adicCompletionIntegers_of_ord_nonneg (v : Pl) {x : Qv v} (hx : x ≠ 0) (h : 0 ≤ ord x) :
    x ∈ v.adicCompletionIntegers ℚ := by
  have h1 : normalizedValuation (Qv v) x ≤ normalizedValuation (Qv v) 1 := by
    rw [map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 := normalizedValuation_le_iff.1 h1
  rw [map_one] at h2
  exact (mem_valuationInteger_iff v x).1 h2

theorem norm_padicRingEquiv_of_ord_eq_zero (v : Pl) (a : (Qv v)ˣ) (h : ord (a : Qv v) = 0) :
    ‖padicRingEquiv v (a : Qv v)‖ = 1 := by
  refine norm_padicRingEquiv_eq_one ((Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩)
  · exact mem_adicCompletionIntegers_of_ord_nonneg v a.ne_zero h.ge
  · refine mem_adicCompletionIntegers_of_ord_nonneg v (a⁻¹).ne_zero ?_
    rw [ord_units_inv, h]
    simp

theorem ofFinite_mem_positiveSubgroup (e : Afˣ) (h : ∀ v, ord (lf v e : Qv v) = 0) :
    IdeleGroup.ofFinite e ∈ RationalIdeles.positiveSubgroup := by
  refine mem_positiveSubgroup_of (fun w => norm_padicRingEquiv_of_ord_eq_zero w (lf w e) (h w)) ?_
  change 0 < ((RationalIdeles.realUnitsEquiv.toMulEquiv.toMonoidHom
    (IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite e)) : ℝˣ) : ℝ)
  rw [IdeleGroup.toInfinite_ofFinite, map_one, Units.val_one]
  exact one_pos

theorem toZModPow_eq_of_congr {N : ℕ} [NeZero N] (w : Pl) (x : Qv w) (u : ℤ_[prime w]) (n : ℤ)
    (hu : (u : ℚ_[prime w]) = padicRingEquiv w x)
    (hx : ((N : Qv w))⁻¹ * (x - n) ∈ 𝒪[Qv w]) :
    PadicInt.toZModPow (N.factorization (prime w)) u =
      ZMod.castHom (Nat.ordProj_dvd N (prime w)) _ (n : ZMod N) := by
  have hO := (mem_valuationInteger_iff w _).1 hx
  have hn : ‖padicRingEquiv w (((N : Qv w))⁻¹ * (x - n))‖ ≤ 1 :=
    (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).mapsTo hO)
  let z : ℤ_[prime w] := ⟨_, hn⟩
  have hN : ((N : ℕ) : ℚ_[prime w]) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hz : u = (n : ℤ_[prime w]) + (N : ℤ_[prime w]) * z := by
    apply PadicInt.ext
    have hzc : ((z : ℤ_[prime w]) : ℚ_[prime w]) = ((N : ℚ_[prime w]))⁻¹ * (padicRingEquiv w x - n) := by
      change padicRingEquiv w (((N : Qv w))⁻¹ * (x - n)) = _
      simp only [map_mul, map_inv₀, map_sub, map_natCast, map_intCast]
    rw [PadicInt.coe_add, PadicInt.coe_mul, hzc, hu]
    push_cast
    field_simp
    ring
  have h0 : ((N : ℕ) : ZMod (prime w ^ N.factorization (prime w))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.ordProj_dvd N (prime w))
  rw [hz, map_add (f := _), map_mul, map_natCast, map_intCast, map_intCast, h0, zero_mul, add_zero]

theorem heckeCharacter_ofFinite_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (d : Afˣ) (n : ℤ)
    (h0 : ∀ v, ord (lf v d : Qv v) = 0)
    (h1 : ∀ v, pOf v ∣ N → ((N : Qv v))⁻¹ * ((lf v d : Qv v) - n) ∈ 𝒪[Qv v]) :
    ((heckeCharacter χ).toIdele (IdeleGroup.ofFinite d) : ℂ) * χ (n : ZMod N) = 1 := by
  have hinv : ∀ v, ord (lf v d⁻¹ : Qv v) = 0 := fun v => by
    have : lf v d⁻¹ = (lf v d)⁻¹ := map_inv (Units.map (adeleAt v).toMonoidHom) d
    rw [this, ord_units_inv, h0 v]
    simp
  let y : RationalIdeles.positiveSubgroup :=
    ⟨IdeleGroup.ofFinite d⁻¹, ofFinite_mem_positiveSubgroup d⁻¹ hinv⟩
  have key : (heckeCharacter χ (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℂ) = χ (n : ZMod N) := by
    refine coe_heckeCharacter_mk_of_forall χ y fun w hw => ?_
    refine toZModPow_eq_of_congr w (lf w d : Qv w) _ n ?_ (h1 w ?_)
    · have hc := coe_unitAt y w
      have hy : (IdeleGroup.finiteProj w (y : IdeleGroup ℚ) : Qv w) = ((lf w d : Qv w))⁻¹ := by
        have : lf w d⁻¹ = (lf w d)⁻¹ := map_inv (Units.map (adeleAt w).toMonoidHom) d
        change ((lf w d⁻¹ : (Qv w)ˣ) : Qv w) = _
        rw [this, Units.val_inv_eq_inv_val]
      have hm : ((((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) *
          ((unitAt y w : ℤ_[prime w]) : ℚ_[prime w]) = 1 := by
        rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
      rw [hc, hy, map_inv₀] at hm
      have hne : padicRingEquiv w (lf w d : Qv w) ≠ 0 := (map_ne_zero _).2 (lf w d).ne_zero
      field_simp at hm
      exact hm
    · rw [show pOf w = prime w from absNorm_asIdeal w]
      exact hw
  rw [← key, HeckeCharacter.toIdele_apply, ← Circle.coe_mul, ← map_mul, ← map_mul, ← map_mul]
  simp [y]

theorem f0 : Ad3.R.B0 → Ad3.R.F0 := fun _ _ _ χ =>
  ⟨heckeCharacter χ, ⟨isOfFinOrder_heckeCharacter χ, fun d n h0 h1 =>
    heckeCharacter_ofFinite_mul χ d n h0 h1⟩⟩

end GlobalTheory.CompanionTheory.RankinSelbergQ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellInducingCharacter
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hpg_wGL_conj_apply {i t : ℕ} (h : (i + 1) + t = i + t + 1) (G : GL (Fin (i + t + 1)) k) (a b : Fin (i + t + 1)) :
    ((wGL k h * G * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) a b =
      (G : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (wPerm h a) (wPerm h b) := by
  have e : (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix id (wPerm h) := rfl
  have e' : ((wGL k h : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix (wPerm h) id := rfl
  rw [Units.val_mul, Units.val_mul, e, e']
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem hpg_wPerm_two {i t : ℕ} (h : (i + 1) + t = i + t + 1) (y : Σ x, Two (Fin (i + 1)) (Fin t) x) :
    wPerm h (two (stdSum h) y) = ePG i t y := by
  simp [wPerm]

theorem hpg_leviProj_wGL_conj {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : HPG k i t)
    (hq : wGL k h * ((g : Mir k (i + t)) : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (x : Bool) :
    leviProj k (two (stdSum h)) ⟨_, hq⟩ x = leviProj k (ePG i t) (hpgIncl k i t g) x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [leviProj_apply, leviProj_apply]
  show ((wGL k h * ((g : Mir k (i + t)) : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) _ _ = _
  rw [hpg_wGL_conj_apply, hpg_wPerm_two, hpg_wPerm_two]
  rfl

theorem open_orbit_twist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j : ℕ} (h : (i + 1) + (j + 1) = i + (j + 1) + 1) (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HPG k i (j + 1)) (hq : wGL k h * ((g : Mir k (i + (j + 1))) : GL (Fin (i + (j + 1) + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (v : ⨂[ℂ] x, TwoT V W x), ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g (tE V W v) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ v) := by
  intro k _ _ _ _ V W _ _ _ _ i j h π₁ π₂ g hq v
  have hf : leviProj k (two (stdSum h)) ⟨_, hq⟩ false = ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k) :=
    hpg_leviProj_wGL_conj h g hq false
  have ht : leviProj k (two (stdSum h)) ⟨_, hq⟩ true = (pgProj k i (j + 1) g).2 :=
    hpg_leviProj_wGL_conj h g hq true
  have hδ : (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) =
      (absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k)) : ℂ) *
      (absPow k (((-((i + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det (pgProj k i (j + 1) g).2) : ℂ) := by
    have e := deltaHalf_two (k := k) (a := Fin (i + 1)) (b := Fin (j + 1))
      (leviProj k (two (stdSum h)) ⟨_, hq⟩ false, leviProj k (two (stdSum h)) ⟨_, hq⟩ true)
    have e2 : leviTwo k (Fin (i + 1)) (Fin (j + 1))
        (leviProj k (two (stdSum h)) ⟨_, hq⟩ false, leviProj k (two (stdSum h)) ⟨_, hq⟩ true) =
        leviProj k (two (stdSum h)) ⟨_, hq⟩ := by
      funext x
      cases x <;> rfl
    rw [e2, hf, ht] at e
    rw [e, Units.val_mul]
    simp only [Fintype.card_fin]
    push_cast
    rfl
  have key : ∀ x : ∀ b, TwoT V W b, ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
      (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g
        (tE V W (PiTensorProduct.tprod ℂ x)) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    have hr : tE V W (sQ h π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) =
        (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) •
          (π₁ (leviProj k (two (stdSum h)) ⟨_, hq⟩ false) (x false) ⊗ₜ[ℂ]
            π₂ (leviProj k (two (stdSum h)) ⟨_, hq⟩ true) (x true)) := by
      show tE V W ((deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) •
        piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum h)) ⟨_, hq⟩) (PiTensorProduct.tprod ℂ x)) = _
      rw [piTensor_tprod, map_smul, Exponents.boolTensorEquiv_tprod]
      rfl
    rw [hr, hf, ht, hδ, Exponents.boolTensorEquiv_tprod]
    refine (extTensor_tmul _ _ _ (x false) (x true)).trans ?_
    show ((absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k)) : ℂ) •
        π₁ ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k) (x false)) ⊗ₜ[ℂ]
      ((absPow k (((-((i + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det (pgProj k i (j + 1) g).2) : ℂ) •
        π₂ (pgProj k i (j + 1) g).2 (x true)) = _
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm]
  let A : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W := ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
      (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g
  have hlin : A ∘ₗ (tE V W).toLinearMap = (tE V W).toLinearMap ∘ₗ sQ h π₁ π₂ ⟨_, hq⟩ :=
    PiTensorProduct.ext (MultilinearMap.ext fun x => key x)
  exact LinearMap.congr_fun hlin v

end GlobalTheory.CompanionTheory.BZRes

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductLanglandsSubquotientSegments
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.LProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLSeg_append {p q : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (Δ₁ : Fin p → Segment k)
    (Δ₂ : Fin q → Segment k) (h₁ : ∀ i, IsLSeg (Δ₁ i) (x i).rep) (h₂ : ∀ i, IsLSeg (Δ₂ i) (y i).rep)
    (i : Fin (p + q)) : IsLSeg (Fin.append Δ₁ Δ₂ i) (Fin.append x y i).rep := by
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left, Fin.append_left]; exact h₁ i
  | right i => rw [Fin.append_right, Fin.append_right]; exact h₂ i

theorem map_append {p q : ℕ} (Δ₁ : Fin p → Segment k) (Δ₂ : Fin q → Segment k) :
    Finset.univ.val.map (Fin.append Δ₁ Δ₂) = Finset.univ.val.map Δ₁ + Finset.univ.val.map Δ₂ := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_fin_append]
  rfl

theorem prod₂_isSubquotient_append {r t p q : ℕ} {U W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) U) (ρ : Representation ℂ (GL (Fin t) k) W)
    (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hd : ∑ i, (Fin.append x y i).1 = r + t) (h₁ : IsSubquotient σ (prodIrr x hx))
    (h₂ : IsSubquotient ρ (prodIrr y hy)) : IsSubquotient (prod₂ σ ρ) (prodIrr (Fin.append x y) hd) := by
  obtain ⟨F⟩ := GlobalTheory.T.product_irreducible_append_equiv k p q r t x y hx hy hd
  exact GlobalTheory.CompanionTheory.Ysupp.isSubquotient_of_prod₂_equiv (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)
    h₁ h₂ (Representation.Equiv.refl _) F

end GlobalTheory.CompanionTheory.LProd

theorem GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL (k := k)), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  intro k _ _ _ _ _ 𝔪 𝔫 a b ha hb
  obtain ⟨p, x, hx, ⟨Δ₁, hO₁, hL₁⟩, hc₁⟩ := ha
  obtain ⟨q, y, hy, ⟨Δ₂, hO₂, hL₂⟩, hc₂⟩ := hb
  have hd : ∑ i, (Fin.append x y i).1 = a.1 + b.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hx, hy]
  refine ⟨p + q, Fin.append x y, Fin.append Δ₁ Δ₂, hd, GlobalTheory.CompanionTheory.LProd.isLSeg_append x y Δ₁ Δ₂ hL₁ hL₂, ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LProd.map_append, hO₁.1, hO₂.1]
  · exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_append _ _ x y hx hy hd hc₁.isSubquotient hc₂.isSubquotient

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictGradedPullNaturalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_graded_pull_natural : ∀ (K : Type) [CommRing K], ∃ m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
    CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
      (RingHom.id K),
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n)) ∧
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q)
      (V : X.Opens) (W : Y.Opens) (h : V ≤ u ⁻¹ᵁ W) (hh : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q) (s a : ℕ)
      (hG : ∀ T, KS q s {V} T → KS p s {W} ((pullM u hu a).G.obj T))
      (hG' : ∀ T, KS (V.ι ≫ q) s {⊤} T → KS (W.ι ≫ p) s {⊤} ((pullM (u.resLE W V h) hh a).G.obj T)) (n : ℕ) x,
      (m q V s a).pull n ((morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').pull n x) =
        (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).pull n ((m p W s a).pull n x) := by
  first | exact @GlobalTheory.CompanionTheory.OpenThick.open_thick | exact GlobalTheory.CompanionTheory.OpenThick.open_thick | (intros; apply GlobalTheory.CompanionTheory.OpenThick.open_thick <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwinerStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_split_intertwiner : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL (k := k)) (hu : IsLSeg (segLow Δ a h0) u.rep) (hv : IsLSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N), ∃ f : (prodIrr ![u, v] hd).IntertwiningMap π, Function.Surjective f := by
  first | exact @GlobalTheory.CompanionTheory.SegQuotTwo.quottwo | exact GlobalTheory.CompanionTheory.SegQuotTwo.quottwo | (intros; apply GlobalTheory.CompanionTheory.SegQuotTwo.quottwo <;> assumption)
end

