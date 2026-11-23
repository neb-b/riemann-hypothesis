module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitEdgeClassKummerDlogCongruence
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoverTensorHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open scoped Matrix Kronecker

noncomputable section

namespace GlobalTheory

namespace FockEmb

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (fun a => if a.isLeft then (1 : ℂ) else -1) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem reindex_kron_J (p q r s : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Formalism.UG.Jpq p q ⊗ₖ Formalism.UG.Jpq r s) = Formalism.UG.Jpq (p * r + q * s) (p * s + q * r) := by
  rw [Jpq_eq_diagonal, Jpq_eq_diagonal, Jpq_eq_diagonal, Matrix.diagonal_kronecker_diagonal,
    Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨l, rfl⟩ := (lineEquiv p q r s).surjective x
  simp only [Function.comp, Equiv.symm_apply_apply, lineEquiv_isLeft]
  rcases l with ⟨a | a, c | c⟩ <;> simp [linePos]

def kronGL (p q r s : ℕ) :
    GL (Ix p q) ℂ × GL (Ix r s) ℂ →* GL (Ix (p * r + q * s) (p * s + q * r)) ℂ where
  toFun x := Units.map (Matrix.reindexAlgEquiv ℂ ℂ (lineEquiv p q r s)).toMonoidHom
    (Matrix.GeneralLinearGroup.kronecker x.1 x.2)
  map_one' := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.kronecker]
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.kronecker, Matrix.mul_kronecker_mul]

theorem kronGL_val {p q r s : ℕ} (g : GL (Ix p q) ℂ) (h : GL (Ix r s) ℂ) :
    ((kronGL p q r s (g, h) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) =
      Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
        ((g : Mat p q) ⊗ₖ (h : Mat r s)) := rfl

theorem mem_Upq_iff {p q : ℕ} (g : GL (Ix p q) ℂ) :
    g ∈ Formalism.UG.Upq p q ↔ (g : Mat p q)ᴴ * Formalism.UG.Jpq p q * (g : Mat p q) = Formalism.UG.Jpq p q :=
  Iff.rfl

theorem kronGL_mem {p q r s : ℕ} {g : GL (Ix p q) ℂ} {h : GL (Ix r s) ℂ}
    (hg : g ∈ Formalism.UG.Upq p q) (hh : h ∈ Formalism.UG.Upq r s) :
    kronGL p q r s (g, h) ∈ Formalism.UG.Upq (p * r + q * s) (p * s + q * r) := by
  rw [mem_Upq_iff] at *
  rw [kronGL_val, ← reindex_kron_J]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hg, hh]

theorem kronGL_det {p q r s : ℕ} (g : GL (Ix p q) ℂ) (h : GL (Ix r s) ℂ) :
    ((kronGL p q r s (g, h) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)).det =
      (g : Mat p q).det ^ (r + s) * (h : Mat r s).det ^ (p + q) := by
  rw [kronGL_val, Matrix.det_reindex_self, Matrix.det_kronecker]
  simp

end FockEmb


open FockEmb in
theorem exists_cover_tensor_hom :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), ∃ emb : T1.G × T2.G →* T0.G, (∀ g h, ((T0.cov (emb (g, h)) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) = Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Matrix.kroneckerMap (· * ·) ((T1.cov g : GL _ ℂ) : Mat p q) ((T2.cov h : GL _ ℂ) : Mat r s))) ∧ ∀ g h, T0.sq (emb (g, h)) = T1.sq g ^ (r + s) * T2.sq h ^ (p + q) := by
  intro p q r s T0 T1 T2
  have key : ∀ x : T1.G × T2.G, ∃! y : T0.G, T0.cov y = kronGL p q r s (T1.cov x.1, T2.cov x.2) ∧
      T0.sq y = T1.sq x.1 ^ (r + s) * T2.sq x.2 ^ (p + q) := by
    intro x
    apply T0.bij _ (kronGL_mem (T1.cov_mem _) (T2.cov_mem _))
    rw [kronGL_det, ← T1.sq_sq, ← T2.sq_sq]
    push_cast
    ring
  choose f hf huniq using key
  refine ⟨MonoidHom.mk' f ?_, fun g h => ?_, fun g h => (hf (g, h)).2⟩
  · intro x y
    symm
    apply huniq
    constructor
    · rw [map_mul, (hf x).1, (hf y).1, ← map_mul]
      simp
    · rw [map_mul, (hf x).2, (hf y).2]
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
      exact mul_mul_mul_comm _ _ _ _
  · show ((T0.cov (f (g, h)) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) = _
    rw [(hf (g, h)).1]
    rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TwoTorsionPt

theorem not_integral_half {N : ℕ} (hN : Odd N) {x : ℂ} (hx : IsIntegral ℤ x)
    (h : x + (starRingEnd ℂ) x = (N : ℂ) / 2) : False := by
  have h1 : IsIntegral ℤ ((starRingEnd ℂ) x) := hx.map (starRingEnd ℂ).toIntAlgHom
  have h2 : IsIntegral ℤ (algebraMap ℚ ℂ ((N : ℚ) / 2)) := by
    have : algebraMap ℚ ℂ ((N : ℚ) / 2) = (N : ℂ) / 2 := by simp
    rw [this, ← h]; exact hx.add h1
  have h3 : IsIntegral ℤ ((N : ℚ) / 2) :=
    (isIntegral_algebraMap_iff ).1 h2
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have h4 : (N : ℚ) = 2 * (m : ℚ) := by
    have : (m : ℚ) = (N : ℚ) / 2 := by simpa using hm
    rw [this]; ring
  have h5 : (N : ℤ) = 2 * m := by exact_mod_cast h4
  obtain ⟨k, hk⟩ := hN
  omega

theorem isTwoTorsionCMPoint_of_odd_multiple (D : D7) (Λ : AddSubgroup ℂ) {δ : ℂ} (hδ : δ ≠ 0) {N : ℕ} (hN : Odd N)
    (hmem : δ * N ∈ Λ) (hint : ∀ w ∈ Λ, ∃ x : ℂ, IsIntegral ℤ x ∧ w = δ * x) :
    GL3Theta.IsTwoTorsionPointUnkilled D Λ (δ * N / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · have : 2 * (δ * N / 2) = δ * N := by ring
    rw [this]; exact hmem
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine not_integral_half hN hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_add (f := _), map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine not_integral_half hN hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring

theorem lamOf_integral (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ w ∈ lamOf D cc δ, ∃ x : ℂ, IsIntegral ℤ x ∧ w = δ * x := by
  intro w hw
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, -, rfl⟩ := hw
    refine ⟨_, ?_, rfl⟩
    have h0 : IsIntegral ℤ (c : D.host.K) := c.2
    exact h0.map (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
  | zero => exact ⟨0, isIntegral_zero, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, hx.add hy, by ring⟩
  | neg a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨-x, hx.neg, by ring⟩

theorem norm_mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    δ * (Ideal.absNorm cc : ℕ) ∈ lamOf D cc δ := by
  refine AddSubgroup.subset_closure ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩
  simp

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) :
    Odd (Ideal.absNorm cc) :=
  Nat.coprime_two_right.1 (Nat.Coprime.coprime_mul_right_right h.1.2)

theorem delta_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) : δ ≠ 0 :=
  (_root_.GlobalTheory.CurveLattice.lattice_of_curve D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ h).2.1

theorem exists_lamOf {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) :
    ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 :=
  ⟨_, isTwoTorsionCMPoint_of_odd_multiple D _ (delta_ne h) (odd_norm h) (norm_mem_lamOf D cc δ) (lamOf_integral D cc δ)⟩

theorem exists_bar {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) (Λ : AddSubgroup ℂ)
    (hΛ : Λ.map (starRingEnd ℂ).toAddMonoidHom = lamOf D cc δ) :
    ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D Λ t0 := by
  have hδ : (starRingEnd ℂ) δ ≠ 0 := by simpa using delta_ne h
  refine ⟨_, isTwoTorsionCMPoint_of_odd_multiple D Λ hδ (odd_norm h) ?_ ?_⟩
  · have h1 := norm_mem_lamOf D cc δ
    rw [← hΛ] at h1
    obtain ⟨w, hw, e⟩ := h1
    have e1 : (starRingEnd ℂ) w = δ * (Ideal.absNorm cc : ℕ) := e
    have e2 : w = (starRingEnd ℂ) δ * (Ideal.absNorm cc : ℕ) := by
      rw [← Complex.conj_conj w, e1, map_mul, map_natCast]
    rw [← e2]; exact hw
  · intro w hw
    have h1 : (starRingEnd ℂ) w ∈ lamOf D cc δ := by
      rw [← hΛ]; exact ⟨w, hw, rfl⟩
    obtain ⟨x, hx, e⟩ := lamOf_integral D cc δ _ h1
    refine ⟨(starRingEnd ℂ) x, hx.map (starRingEnd ℂ).toIntAlgHom, ?_⟩
    rw [← Complex.conj_conj w, e, map_mul]

theorem exists_extension (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ (M' : IntermediateField ℚ ℂ) (ρ' : M' →ₐ[ℚ] ℂ), (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ M') ∧
      ∀ x ∈ M, x ∈ M' ∧ ρ' (TaylorLogMetric.liftM M' x) = ρ (TaylorLogMetric.liftM M x) := by
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := algebraicClosure M ℂ) ρ
  refine ⟨(algebraicClosure M ℂ).restrictScalars ℚ, φ, ?_, ?_⟩
  · intro x hx
    exact mem_algebraicClosure_iff.2 (hx.extendScalars (algebraMap ℚ M).injective)
  · intro x hx
    have hx' : x ∈ (algebraicClosure M ℂ).restrictScalars ℚ :=
      (algebraicClosure M ℂ).algebraMap_mem (⟨x, hx⟩ : M)
    refine ⟨hx', ?_⟩
    unfold TaylorLogMetric.liftM
    rw [dite_eq_left hx', dite_eq_left hx, ← hφ]
    rfl

theorem exists_point : ∀ D : D7, t0Ex D := by
  intro D cc δ hc
  refine ⟨exists_lamOf hc, ?_⟩
  intro M ρ h2 h3
  obtain ⟨M', ρ', halg, hext⟩ := exists_extension M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [(hext _ h2).2, (hext _ h3).2]
  rw [hl]
  have hD : DataIn D (tor0 D cc δ) M' := by
    refine ⟨fun τ x => halg _ ?_, (hext _ h2).1, (hext _ h3).1⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom
  obtain ⟨hfix, hbar, -⟩ := _root_.GlobalTheory.ThetaConj.useBar_holds D cc δ hc M' ρ' hD
  rcases hfix with hfix | hfix
  · obtain ⟨cc', δ', hc', -, e⟩ := _root_.GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M' ρ' hfix hD.2.1 hD.2.2 1 one_pos
    rw [e]
    exact exists_lamOf hc'
  · obtain ⟨cc', δ', hc', -, e⟩ :=
      _root_.GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M' (rhoBar M' ρ') hfix hD.2.1 hD.2.2 1 one_pos
    refine exists_bar hc' _ ?_
    rw [← e]
    exact (congrArg Tor.abelian₂ hbar).symm

end GlobalTheory.TwoTorsionPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvPhiSeriesSubNsmulEqDiv
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogShift

open MvPowerSeries

theorem expMv_phAt_sub_nsmul : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (h : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 → PowerSeries.constantCoeff h = 0 → MvPowerSeries.constantCoeff ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = 0 ∧ expMv ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = ((PowerSeries.subst h (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ n : PowerSeries ℂ_[p]) := by
  intro p _ g h n hE hh
  have exp_add {f g : MvPowerSeries Unit ℂ_[p]} (hf : constantCoeff f = 0)
      (hg : constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg,
      GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg
  have exp_zero : expMv (0 : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero
  have cc_ph : PowerSeries.constantCoeff g.ph = 0 := by
    have ht := (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).1
    show constantCoeff (-GL3Theta.logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0
    rw [map_neg, ht, neg_zero]
  have cc_phAt {y : MvPowerSeries Unit ℂ_[p]} (hy : constantCoeff y = 0) :
      constantCoeff (g.phAt y) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hy _ cc_ph
  have exp_sum {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries Unit ℂ_[p]}
      (hf : ∀ i, constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
    induction s using Finset.induction_on with
    | empty => simpa using exp_zero
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, exp_add (hf i) (by simp [map_sum, hf]), ih]
  have subst_exp {a : Unit → MvPowerSeries Unit ℂ_[p]} (ha : ∀ i, constantCoeff (a i) = 0)
      {f : MvPowerSeries Unit ℂ_[p]} (hf : constantCoeff f = 0) : subst a (expMv f) = expMv (subst a f) := by
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]
    rw [PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const hs]
    rfl
  have inv_ePhi1 {y : MvPowerSeries Unit ℂ_[p]} (hy : constantCoeff y = 0) :
      (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = expMv (g.phAt y) := by
    have hs : HasSubst (fun _ : Unit => y) := hasSubst_of_constantCoeff_zero fun _ => hy
    have ht := congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
    rw [subst_mul hs, subst_exp (f := -GL3Theta.logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) cc_ph, ← coe_substAlgHom hs (R := ℂ_[p]), map_one,
      coe_substAlgHom] at ht
    have h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0 := by
      rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]; exact one_ne_zero
    rw [MvPowerSeries.inv_eq_iff_mul_eq_one h1]
    exact ht
  have hh' : MvPowerSeries.constantCoeff (h : MvPowerSeries Unit ℂ_[p]) = 0 := hh
  have hX : MvPowerSeries.constantCoeff (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by
    simp [GL3Theta.Xv]
  have ha : MvPowerSeries.constantCoeff (g.phAt (h : MvPowerSeries Unit ℂ_[p])) = 0 :=
    cc_phAt hh'
  have hb : MvPowerSeries.constantCoeff (g.phAt (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p])) = 0 :=
    cc_phAt hX
  refine ⟨by simp [map_sub, map_mul, ha, hb], ?_⟩
  set b : MvPowerSeries Unit ℂ_[p] := g.phAt (GL3Theta.Xv ()) with hbdef
  set F : PowerSeries ℂ_[p] := ePhi1 g.lam g.abelian₂ g.C g.wq with hF

  have hbph : b = (g.ph : MvPowerSeries Unit ℂ_[p]) := by
    show PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.ph = g.ph
    rw [← PowerSeries.map_algebraMap_eq_subst_X]; simp

  have hbF : expMv b * (F : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [hbph]; exact (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
  have hnb : MvPowerSeries.constantCoeff (-b) = 0 := by simp [hb]

  have hneg : expMv (-b) = (F : MvPowerSeries Unit ℂ_[p]) := by
    have h0 : expMv b * expMv (-b) = 1 := by
      rw [← exp_add hb hnb, add_neg_cancel, exp_zero]
    calc expMv (-b) = expMv (-b) * (expMv b * (F : MvPowerSeries Unit ℂ_[p])) := by rw [hbF, mul_one]
      _ = (expMv b * expMv (-b)) * F := by ring
      _ = F := by rw [h0, one_mul]
  have hsum : (g.phAt (h : MvPowerSeries Unit ℂ_[p])) - MvPowerSeries.C (n : ℂ_[p]) * b =
      g.phAt (h : MvPowerSeries Unit ℂ_[p]) + ∑ _i ∈ Finset.range n, -b := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_eq_add_neg, ← neg_mul]
    congr 1
    rw [neg_mul, mul_neg]
    congr 1
  have hsum0 : MvPowerSeries.constantCoeff (∑ _i ∈ Finset.range n, -b) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp [hb]
  rw [hsum, exp_add ha hsum0,
    exp_sum _ (fun _ => hnb), Finset.prod_const, Finset.card_range, hneg,
    ← inv_ePhi1 hh']

end GlobalTheory.ExpLogShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixed
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertParity.FiniteOrder

theorem exists_prime_mem {R : Type*} [CommRing R] (P : Ideal R) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : R) ∈ P) : ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ (q : R) ∈ P := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
  | exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
  | (apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem ..)

theorem simple_case (D : D7) (S : Type) [AddCommGroup S] [Module (𝓞 D.host.E) S] [Finite S]
    [IsSimpleModule (𝓞 D.host.E) S] :
    Ev D (Nat.card S) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card S → InertQ D q) → sgn D (Nat.card S) = -1) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := 𝓞 D.host.E) (M := S)).1 ‹_›
  have hc : Nat.card S = Ideal.absNorm P := by
    rw [Nat.card_congr e.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Ideal.absNorm P ≠ 0 := hc ▸ Nat.card_pos.ne'
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.InertResidue.norm_prime D P hP
  rw [hc]
  refine ⟨h1, fun h => ?_⟩
  by_cases hs : D.host.conj • P = P
  · exact (h2 hs).1
  · obtain ⟨q, hq, hd, hm⟩ := exists_prime_mem P hP.isPrime _ h0 (Ideal.absNorm_mem P)
    exact absurd (h q hq hd) ((h3 hs).2 q hq hm)

theorem card_parity_sign_length_of_eq (D : D7) (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M],
    Nat.card M = n → Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) →
      sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ hn
    rcases subsingleton_or_nontrivial M with hM | hM
    · have h1 : Nat.card M = 1 := Nat.card_of_subsingleton (0 : M)
      rw [h1, Module.length_eq_zero]
      exact ⟨Ev.one, fun _ => by simp [sgn_one]⟩
    · obtain ⟨N, hN⟩ : ∃ N : Submodule (𝓞 D.host.E) M, IsCoatom N := by
        rcases eq_top_or_exists_le_coatom (⊥ : Submodule (𝓞 D.host.E) M) with h | ⟨N, hN, -⟩
        · exact absurd h bot_ne_top
        · exact ⟨N, hN⟩
      haveI : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
      haveI : IsSimpleModule (𝓞 D.host.E) (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
      haveI : Nontrivial (M ⧸ N) := IsSimpleModule.nontrivial (𝓞 D.host.E) (M ⧸ N)
      have hc : Nat.card M = Nat.card N * Nat.card (M ⧸ N) := Submodule.card_eq_card_quotient_mul_card N
      have hq : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
      have hp : 0 < Nat.card N := Nat.card_pos
      obtain ⟨a1, a2⟩ := ih (Nat.card N) (by rw [← hn, hc]; exact lt_mul_of_one_lt_right hp hq) N rfl
      obtain ⟨b1, b2⟩ := simple_case D (M ⧸ N)
      have hl : Module.length (𝓞 D.host.E) M =
          Module.length (𝓞 D.host.E) N + Module.length (𝓞 D.host.E) (M ⧸ N) :=
        Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
          (LinearMap.exact_subtype_mkQ N)
      have hfin : Module.length (𝓞 D.host.E) N ≠ ⊤ := Module.length_ne_top
      rw [hl, Module.length_eq_one (R := 𝓞 D.host.E) (M := M ⧸ N), ENat.toNat_add hfin (by simp), hc]
      refine ⟨a1.mul b1 hp.ne' (by omega), fun h => ?_⟩
      rw [sgn_mul a1 b1 hp.ne' (by omega), a2 fun q hq hd => h q hq (hd.mul_right _),
        b2 fun q hq hd => h q hq (hd.mul_left _), pow_add]
      simp

theorem ev_card_and_sgn_card : ∀ (D : D7) (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M], Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) → sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) :=
  fun D M _ _ _ => card_parity_sign_length_of_eq D _ M rfl

end GlobalTheory.InertParity.FiniteOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitEdgeClassKummerDlogCongruenceStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnit_edgeClass_kummer_dlog_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ cc : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n N c d : ℕ) (A₁ a₂ g B₁ b₂ h : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → b₂ ≡ N * h [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → (N : ℤ) ∣ b₂ → 1 ≤ n → n ≤ L → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → 1 < d → Nat.Coprime d (6 * N * p) →
    ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ B₁) →
  ∀ (F K Ω' : Type) [Field F] [Field K] [Field Ω'] [Algebra F K] [Algebra F Ω'] [Algebra K Ω'] [IsScalarTower F K Ω'] [IsAlgClosure K Ω'] [Normal F K]
    (e : K →+* X.K), (∀ y, e y ∈ KT X (p ^ L)) →
  ∀ (z a b : K) (ζ α β : Ω'), e z = algebraMap Ω X.K (zt ε p n) → ζ = algebraMap K Ω' z →
    e a = sgN X c N (N * p ^ L) (A₁, a₂) → e b = sgN X d N (N * p ^ L) (B₁, b₂) →
    α ^ (p ^ n) = algebraMap K Ω' a → β ^ (p ^ n) = algebraMap K Ω' b →
  ∀ (x y : (Ω' ≃ₐ[F] Ω') →* Multiplicative (ZMod (p ^ n))), (∀ t, (x t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ α t) → (∀ t, (y t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ β t) →
  ∀ η : (Ω' ≃ₐ[F] Ω') → ZMod (p ^ n), GlobalTheory.KEdge.CobOn (GlobalTheory.K4.geo F K Ω') x y η → IsLocallyConstant (fun t : GlobalTheory.K4.geo F K Ω' => η t) →
  ∃ ξ : ℚ → Ω, (∀ r, ξ r ∈ A) ∧ ∀ s : Ω ≃ₐ[ℚ] Ω, Stab A s → s (zt ε p L) = zt ε p L → (∀ f : F, X.gal s (e (algebraMap F K f)) = e (algebraMap F K f)) →
    ∀ σ : Ω' ≃ₐ[F] Ω', (∀ k k' : K, e k' = X.gal s (e k) → σ (algebraMap K Ω' k) = algebraMap K Ω' k') →
    ∀ (w : K) (φ : HahnSeries ℚ Ω) (t : ZMod (p ^ n)), GlobalTheory.K4.IsTopW ζ x y η σ w → IsDl X A p n ((p : ℚ) ^ L) (e w) φ →
      s (zt ε p (L + n)) = zt ε p n ^ t.val * zt ε p (L + n) →
      ∀ r : ℚ, CgA A p n ((p : Ω) ^ cc * φ.coeff r)
        (s.symm (ξ r) - ξ r - (p : Ω) ^ cc * ((A₁ * h - g * B₁ : ℤ) : Ω) * (t.val : Ω) *
          coefQ (p ^ L) (cmul (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂) (smF d 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) B₁ b₂)) r) := by
  first | exact @GlobalTheory.pair_edge_dlog | exact GlobalTheory.pair_edge_dlog | (intros; apply GlobalTheory.pair_edge_dlog <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumImageIntertwinerSelfDualPair
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ArchFree.firstBasisVectorLike

open GlobalTheory.VacuumMove

theorem isVacuum_thetaIntertwiner_selfDual : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  rintro D cc δ t0 hc ht a d L L' L₁ L₁' hL hL' hL₁ hL₁' G ⟨b, κ, hb, hκ, rfl⟩
  obtain ⟨μ, hμ, h⟩ := _root_.GlobalTheory.TripleIntertwiner.triple_constant D cc δ hc a d _ _ _ (Or.inl ⟨_, b, hb, rfl⟩) (Or.inr ⟨L, L', hL, hL', rfl⟩)
    (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) _ (pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ t0 hc ht b hb.1)
  refine ⟨b, κ * μ, hb, mod1All_mul hκ hμ, funext fun z => ?_⟩
  rw [Iop_mul, mul_assoc κ μ]
  exact congrArg (κ * ·) (congrFun h z)

end GlobalTheory.ArchFree.firstBasisVectorLike
end
end

