module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.DetMemOfEntries
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialOfSplitPlaceStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitStab

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_eq (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = dotProduct (fun i => σ (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_smul_left (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (fun i => a * x i) y = σ a * Formalism.UG.hform σ J x y := by
  simp only [hform_eq, dotProduct, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x (fun i => a * y i) = a * Formalism.UG.hform σ J x y := by
  have : (fun i => a * y i) = a • y := rfl
  rw [hform_eq, hform_eq, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform σ J x y := by
  have e : (fun i => σ (g.mulVec x i)) = Matrix.vecMul (fun i => σ (x i)) (Formalism.UG.cT σ g) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, mul_comm]
  rw [hform_eq, hform_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem stab_of_half (I : AddSubgroup A) (L : AddSubgroup (Fin n → A))
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, Formalism.UG.hform σ J z y ∈ I) {p : A}
    (hp : ∀ y ∈ L, (fun i => p * y i) ∈ L) (hq : ∀ y ∈ L, (fun i => σ p * y i) ∈ L)
    {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J)
    (hs : ∀ i j, (p + σ p) * (g - 1) i j = (g - 1) i j)
    (h1 : ∀ y ∈ L, (fun i => p * g.mulVec y i) ∈ L)
    (h2 : ∀ y ∈ L, ∃ z ∈ L, (fun i => p * y i) = fun i => p * g.mulVec z i) (y : Fin n → A) :
    y ∈ L ↔ g.mulVec y ∈ L := by
  have fwd : ∀ y ∈ L, g.mulVec y ∈ L := by
    intro y hy
    have hc : (fun i => σ p * g.mulVec y i) ∈ L := by
      refine (hL _).2 fun z hz => ?_
      obtain ⟨z', hz', e⟩ := h2 z hz
      rw [hform_smul_right, ← hform_smul_left, e, hform_smul_left, hform_mulVec σ J hg, ← hform_smul_right]
      exact (hL _).1 (hq y hy) z' hz'
    have hs' : (p + σ p) • (g - 1) = g - 1 := Matrix.ext hs
    have e : (p + σ p) • (g.mulVec y - y) = g.mulVec y - y := by
      have := congrArg (fun m => Matrix.mulVec m y) hs'
      simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using this
    have e2 : g.mulVec y = y + ((fun i => p * g.mulVec y i) + (fun i => σ p * g.mulVec y i) -
        (fun i => p * y i) - fun i => σ p * y i) := by
      funext i
      have := congrFun e i
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
      linear_combination -this
    rw [e2]
    exact add_mem hy (sub_mem (sub_mem (add_mem (h1 y hy) hc) (hp y hy)) (hq y hy))
  refine ⟨fwd y, fun hy => (hL _).2 fun z hz => ?_⟩
  rw [← hform_mulVec σ J hg]
  exact (hL _).1 hy _ (fwd z hz)

theorem supp_map {B : Type} [CommRing B] (φ : A →+* B) {f : A} {g : Matrix (Fin n) (Fin n) A}
    (hs : ∀ i j, f * (g - 1) i j = (g - 1) i j) (i j : Fin n) :
    φ f * (g.map φ - 1) i j = (g.map φ - 1) i j := by
  have e : (g.map φ - 1) i j = φ ((g - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, ← map_mul, hs]

end Alg

variable {D : D7}

theorem finPart_conj (x : Formalism.L2.Theta.AE D) :
    finPart D (cA D x) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem finMat_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) *
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram * finMat D.sp.cm.sig V.gram g =
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := by
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
      JR (AF D.host.F) V.gram := g.2
  have h2 := congrArg (fun m => Matrix.map m (finPart D)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (JR (AF D.host.F) V.gram).map (finPart D) = JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := rfl
  have e2 : (mt V g).map (finPart D) = finMat D.sp.cm.sig V.gram g := rfl
  have e3 : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (finPart D) =
      Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) := by
    ext i j
    exact finPart_conj _
  rwa [e1, e2, e3] at h2

theorem mem_ksph_of_split : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (g : GA D V), IsSplitIdem D e → Formalism.L2.Theta.SuppAt e V g → (∀ y ∈ LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec y a) ∈ LamHat V) → (∀ y ∈ LamHat V, ∃ z ∈ LamHat V, (fun a => finPart D e * y a) = fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec z a) → g ∈ KsphC V ∅ := by
  intro D V e g he hs h1 h2
  obtain ⟨hd, hm⟩ := GlobalTheory.LatDual.lamHat_selfDual_and_module V
  obtain ⟨i1, -, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
  have hp : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, i1])
  have hq : sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ← RingHom.map_mul, i1])
  refine ⟨?_, ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  · have h5 : infPart D (e + cA D e) = 0 := by
      rw [h4]
      exact TensorProduct.zero_tmul _ _
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h6 := congrArg (infPart D) (hs i j)
    rw [RingHom.map_mul, h5, zero_mul, Matrix.sub_apply, RingHom.map_sub] at h6
    have h7 : infPart D (mt V g i j) = infPart D ((1 : Matrix _ _ (Formalism.L2.Theta.AE D)) i j) :=
      sub_eq_zero.1 h6.symm
    refine h7.trans ?_
    rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact RingHom.map_one _
    · exact RingHom.map_zero _
  · refine stab_of_half (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)
      (JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram) (intAE D) (LamHat V) hd (p := finPart D e)
      (hm _ hp) (hm _ hq) (finMat_unitary V g) (fun i j => ?_) h1 h2
    rw [← finPart_conj, ← RingHom.map_add (f := _)]
    exact supp_map (finPart D) hs i j

end GlobalTheory.SplitStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOneOfTrace
section
noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.TraceNormCoordinates

theorem exists_coords (b : ℤ) (d : ℕ) (hd : 0 < d) {x : ℂ} (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) :
    ∃ p q : ℚ, x = (p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
  set s : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hs_def
  have hs : s * s = -(d : ℂ) := by
    have h2 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    calc s * s = (Complex.I * Complex.I) * (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) := by
          rw [hs_def]; ring
      _ = -(d : ℂ) := by rw [Complex.I_mul_I, h2]; ring
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨(b : ℚ) / 2, 1 / 2, ?_⟩
    simp only [PI.UnitDetRootDefs.cmTheta, hs_def]
    push_cast
    ring
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨p, q, rfl⟩ := ihx
    obtain ⟨p', q', rfl⟩ := ihy
    exact ⟨p + p', q + q', by push_cast; ring⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨p, q, rfl⟩ := ihx
    obtain ⟨p', q', rfl⟩ := ihy
    refine ⟨p * p' - d * q * q', p * q' + q * p', ?_⟩
    push_cast
    linear_combination (q : ℂ) * q' * hs
  | inv x _ ih =>
    obtain ⟨p, q, rfl⟩ := ih
    by_cases h0 : p = 0 ∧ q = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact ⟨0, 0, by simp⟩
    · have hN : p ^ 2 + d * q ^ 2 ≠ 0 := by
        intro hz
        apply h0
        have h1 : p ^ 2 = 0 := by nlinarith [sq_nonneg p, mul_nonneg hdq.le (sq_nonneg q)]
        have h2 : q ^ 2 = 0 := by nlinarith [sq_nonneg p, sq_nonneg q, mul_nonneg hdq.le (sq_nonneg q)]
        exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1, pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2⟩
      have hNc : ((p : ℂ) ^ 2 + (d : ℂ) * (q : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hN
      refine ⟨p / (p ^ 2 + d * q ^ 2), -q / (p ^ 2 + d * q ^ 2), ?_⟩
      apply inv_eq_of_mul_eq_one_right
      clear_value s
      have e : ((p : ℂ) + q * s) * (((p / (p ^ 2 + d * q ^ 2) : ℚ) : ℂ) + ((-q / (p ^ 2 + d * q ^ 2) : ℚ) : ℂ) * s)
          = ((p : ℂ) ^ 2 - (q : ℂ) ^ 2 * (s * s)) / ((p : ℂ) ^ 2 + (d : ℂ) * (q : ℂ) ^ 2) := by
        push_cast
        ring
      rw [e, hs, div_eq_one_iff_eq hNc]
      ring

theorem norm_le_one_of_trace {F : Type*} [NormedField F] [IsUltrametricDist F] {y y' : F}
    (h : y * y' = 1) (ht : ‖y + y'‖ ≤ 1) : ‖y‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hn : ‖y‖ * ‖y'‖ = 1 := by rw [← norm_mul, h, norm_one]
  have hy' : ‖y'‖ < ‖y‖ := by nlinarith [norm_nonneg y', norm_nonneg y]
  have hmax := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hy')
  rw [hmax, max_eq_left hy'.le] at ht
  linarith

theorem norm_eq_one {a : ℕ} {b c : ℤ} {d : ℕ} (hok : PI.UnitDetRootDefs.CmOK a b c d) (l : ℕ)
    [inst : Fact (Nat.Prime l)]
    (hT : ∀ T v : ℚ_[l], T ^ 2 + (d : ℚ_[l]) * v ^ 2 = 4 → ‖T‖ ≤ 1)
    (ι : ℂ ≃+* ℂ_[l]) {x : ℂ} (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) (h1 : x * conj x = 1) :
    ‖ι x‖ = 1 := by
  have hd : 0 < d := hok.2.2.2.pos
  obtain ⟨p, q, rfl⟩ := exists_coords b d hd hx
  set s : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hs_def
  have hs : s * s = -(d : ℂ) := by
    have h2 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    calc s * s = (Complex.I * Complex.I) * (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) := by
          rw [hs_def]; ring
      _ = -(d : ℂ) := by rw [Complex.I_mul_I, h2]; ring
  have hcs : conj s = -s := by simp [hs_def]
  have hconj : conj ((p : ℂ) + (q : ℂ) * s) = (p : ℂ) - (q : ℂ) * s := by
    rw [map_add (f := _), map_mul, hcs, map_ratCast, map_ratCast]; ring
  rw [hconj] at h1

  have hpq : (p ^ 2 + d * q ^ 2 : ℚ) = 1 := by
    have : (((p ^ 2 + d * q ^ 2 : ℚ)) : ℂ) = 1 := by
      push_cast
      linear_combination h1 + (q : ℂ) ^ 2 * hs
    exact_mod_cast this
  have hT' : ‖((2 * p : ℚ) : ℚ_[l])‖ ≤ 1 := by
    apply hT _ ((2 * q : ℚ) : ℚ_[l])
    have : ((2 * p) ^ 2 + d * (2 * q) ^ 2 : ℚ) = 4 := by linear_combination 4 * hpq
    exact_mod_cast congrArg (fun r : ℚ => (r : ℚ_[l])) this
  set y := ι ((p : ℂ) + (q : ℂ) * s)
  set y' := ι ((p : ℂ) - (q : ℂ) * s)
  have hyy : y * y' = 1 := by rw [← map_mul, h1, map_one]
  have hnr : ∀ r : ℚ, ‖(r : ℂ_[l])‖ = ‖(r : ℚ_[l])‖ := by
    intro r
    rw [← PadicComplex.norm_extends', map_ratCast, PadicComplex.coe_eq, map_ratCast]
  have hsum : y + y' = ((2 * p : ℚ) : ℂ_[l]) := by
    rw [← map_add (f := _)]
    have : (p : ℂ) + (q : ℂ) * s + ((p : ℂ) - (q : ℂ) * s) = ((2 * p : ℚ) : ℂ) := by push_cast; ring
    rw [this, map_ratCast]
  have htr : ‖y + y'‖ ≤ 1 := by rw [hsum, hnr]; exact hT'
  have hle : ‖y‖ ≤ 1 := norm_le_one_of_trace hyy htr
  have hle' : ‖y'‖ ≤ 1 := norm_le_one_of_trace (by rw [mul_comm]; exact hyy) (by rw [add_comm]; exact htr)
  have hn : ‖y‖ * ‖y'‖ = 1 := by rw [← norm_mul, hyy, norm_one]
  nlinarith [norm_nonneg y, norm_nonneg y']

end GlobalTheory.TraceNormCoordinates
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
section
noncomputable section

namespace GlobalTheory.ParamRep

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

theorem charpoly_smul_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) :
    (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod := by
  have h := (IsAlgClosed.splits (u • M).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _)
  rw [GlobalTheory.RowTie.EigTwist.roots_charpoly_smul_matrix] at h
  exact h

theorem charpoly_smul_of_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ)
    (L : Multiset ℂ) (h : M.charpoly = (L.map fun α => X - C α).prod) :
    (u • M).charpoly = ((L.map (· * u)).map fun α => X - C α).prod := by
  rw [charpoly_smul_eq_prod, h, roots_multiset_prod_X_sub_C]

theorem prod_Icc_eq_fin {M : Type*} [CommMonoid M] (F : ℕ → M) (t : ℕ) :
    ∏ c ∈ Finset.Icc 1 t, F c = ∏ c : Fin t, F ((c : ℕ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    Finset.prod_range]
  exact Finset.prod_congr rfl fun c _ => by rw [add_comm]

theorem charpoly_block {k : Type*} [CommRing k] {r t : ℕ} (M : Matrix (Fin r) (Fin r) k) (d : Fin t → k) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 (Matrix.diagonal d))).charpoly =
      M.charpoly * ∏ c, (X - C (d c)) := by
  rw [Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]
  congr 1
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_diagonal]

theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E q) : v ∉ placesOver E p := by
  intro hv'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h1 : (1 : 𝓞 E) ∈ v.asIdeal := by
    have e : (1 : 𝓞 E) = (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (q : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv') (v.asIdeal.mul_mem_left _ hv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem locG_tw_tw (hL : Formalism.MainNotions.SumRepresentations.At.TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) :
    A.locG (A.tw (A.tw π A.etaTinv) A.etaT) w = A.locG π w := by
  obtain ⟨h1, h2⟩ := A.etaTinv_def w
  have d1 := A.locG_dim A.etaTinv w
  have d2 := A.locG_dim A.etaT w
  have hu2 := A.etaT_unr w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ hu2).trans d2)
  have hc0 : c ≠ 0 := by
    have := A.frobEig_ne_zero _ hu2
    rw [hc] at this
    simpa [eq_comm] using this
  have hu := A.unr_char _ _ d2 h1 hu2
  have hf : A.frobEig (A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w)) = {1} := by
    rw [A.frobEig_char _ _ c h1 hu2 d2 hc, h2, hc]
    simp [hc0]
  have he : A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w) = A.lpUnr w {1} := by
    rw [A.unr_eq_lpUnr _ hu, hf]
  obtain ⟨-, -, -, e1, e2, -⟩ := hL w (A.locG π w) (A.locG π w) (A.locG A.etaTinv w) (A.locG A.etaT w) 0 d1 d2
  rw [A.locG_tw, A.locG_tw, e1, he, e2]

theorem hecke_split (i : N.Loc) (x : N.X i) (π : A.CG R.r) (P : A.AV i) (hP : A.ptV i P = some x)
    (hB : IsBCV N A i P (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv))
    {w : PlE H} (hw : SplitOut N i w) (hu : A.unr (A.locG (A.tw π A.etaTinv) w))
    {B : ValuationSubring N.Om} {σ : G H.E N.Om} (hBw : IsPlaceOver (F := H.E) B w)
    (hσ : IsFrob (F := H.E) B (normV w) σ) :
    (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) := by
  have e2 : (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := A.pt_loc i P x hP w hw
  have e3 := hB.2.2.2.1 w hw.1
  have s1 := galPol_speh N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w hu ((1 - (R.nV : ℝ)) / 2)
  have s2 := galPol_speh N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w (A.chi_mu i w hw).1
    ((1 - (R.nV : ℝ)) / 2)
  have e4 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w =
      A.lpSum (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w)
        (A.lpSum (spehLoc N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w) (A.lpZero w)) := rfl
  have e5 : ∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) =
      ∏ k ∈ Finset.range R.t, galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
        (((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hx : ((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2 =
        ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + (-(k : ℝ)) := by ring
    rw [hx, galPol_block N A i hw hBw hσ, add_comm 1 k, chi_apply N i k (Finset.mem_range.mp hk)]
    have hq := iota_eps N A i hw.2.1 hBw hσ
    have hinv : iotaO N A i ((((eps N i σ) ^ k)⁻¹ : (N.O i)ˣ) : N.O i) =
        ((normV w : ℕ) : ℂ) ^ (((-(k : ℝ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, ← hq,
        map_units_inv, Units.val_pow_eq_pow_val, map_pow]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Units.val_mul, map_mul, hinv]
  rw [e2, ← e3, e4, A.lpSum_zero, galPol_tw_sum N A _ _ s1.1 s2.1, s1.2, s2.2, e5]
  simp

theorem galPol_twist {w : PlE H} (π : A.CG R.r) (hu : A.unr (A.locG π w)) (u : ℂ)
    (hξ : A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {u}) :
    galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) =
      (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map (· * u)).map fun α => X - C α).prod := by
  obtain ⟨h1, -⟩ := A.etaTinv_def w
  have d1 := A.locG_dim A.etaTinv w
  obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ h1).trans d1)
  rw [A.frobEig_tw _ _ h1, hd, Multiset.map_singleton, Multiset.singleton_inj] at hξ
  unfold galPol
  rw [A.locG_tw, A.frobEig_tw _ _ (A.unr_char _ _ d1 hu h1), A.frobEig_char _ _ d hu h1 d1 hd,
    A.frobEig_tw _ _ hu]
  simp only [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => ?_)
  simp only [Function.comp]
  rw [← hξ]
  have hq : ((normV w : ℕ) : ℂ) ^ (((1 - (R.nV : ℝ)) / 2 : ℝ) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ (((1 - (R.r : ℝ)) / 2 : ℝ) : ℂ) *
        ((normV w : ℕ) : ℂ) ^ ((-(R.t : ℝ) / 2 : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ (normV_ne_zero w)]
    congr 1
    rw [Ranks.nV]
    push_cast
    ring
  rw [hq]
  congr 2
  ring

theorem map_smul_matrix {k l : Type*} [CommRing k] [CommRing l] {n : Type*} (f : k →+* l) (c : k)
    (M : Matrix n n k) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

section Twist

variable {Γ : Type} [Group Γ]

theorem coe_twGL {k : Type} [CommRing k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((χ g : kˣ) : k) • ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  show algebraMap k (Matrix (Fin n) (Fin n) k) ((χ g : kˣ) : k) * _ = _
  rw [← Algebra.smul_def]

theorem twGL_twGL_inv {k : Type} [CommRing k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    Formalism.MainNotions.SumRepresentations.At.twGL (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ⁻¹) χ = ρ := by
  ext g : 2
  rw [coe_twGL, coe_twGL, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel]
  simp

theorem mapRep_twGL {k l : Type} [CommRing k] [CommRing l] {n : ℕ} (f : k →+* l) (ρ : Γ →* GL (Fin n) k)
    (χ : Γ →* kˣ) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) =
      Formalism.MainNotions.SumRepresentations.At.twGL (mapRep f ρ) ((Units.map f.toMonoidHom).comp χ) := by
  ext g : 2
  rw [coe_twGL, mapRep_twGL_coe]
  rfl

theorem isSSRep_twGL {k : Type} [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) :
    IsSSRep (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) := by
  have key : ∀ W : Submodule k (Fin n → k), IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W ↔ IsInv ρ W := by
    intro W
    refine ⟨fun hW g v hv => ?_, fun hW g v hv => ?_⟩
    · have h1 := hW g v hv
      rw [coe_twGL, Matrix.smul_mulVec] at h1
      exact (W.smul_mem_iff (χ g).ne_zero).1 h1
    · rw [coe_twGL, Matrix.smul_mulVec]
      exact W.smul_mem _ (hW g v hv)
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((key W).1 hW)
  exact ⟨W', (key W').2 h1, h2⟩

end Twist

end GlobalTheory.ParamRep

section Final

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

end Final
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegralStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)), IsFrameAt V v h → ∀ g, (∀ w, w ≠ v → locMat hc V w g = 1) → (Stab hc V g ↔ h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range) := by
  first | exact @GlobalTheory.PlaceComp.StabLoc.stab_iff | exact GlobalTheory.PlaceComp.StabLoc.stab_iff | (intros; apply GlobalTheory.PlaceComp.StabLoc.stab_iff <;> assumption)
end

