module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlIntegralInvMulOfLatticeMapEq
section
namespace GlobalTheory.SplitHecke

open Matrix

section

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

theorem isInt_of_mem_span_basisFun {w : Fin r → K}
    (hw : w ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) (i : Fin r) :
    IsInt O (w i) := by
  show ∃ o : O, algebraMap O K o = w i
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hij : i = j
    · subst hij
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.basisFun_apply, Pi.single_apply, hij]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

theorem intM_inv_mul_of_map_le {a b : GL (Fin r) K}
    (hle : (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((a : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) ≤
      (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((b : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)) :
    IntM O (b⁻¹ * a).1 := by
  intro i j
  have hmem := Submodule.mem_map_of_mem
    (f := ((a : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)
    (Submodule.subset_span ⟨j, rfl⟩ :
      Pi.basisFun K (Fin r) j ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))))
  obtain ⟨w, hw, hwe⟩ := hle hmem
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hwe
  have hcol : ((b⁻¹ * a : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ Pi.basisFun K (Fin r) j = w := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hwe, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hentry : (b⁻¹ * a).1 i j = w i := by
    rw [← hcol]
    simp [Pi.basisFun_apply]
  rw [hentry]
  exact isInt_of_mem_span_basisFun hw i

end

theorem gInt_inv_mul_of_map_eq : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ)
    (h h' : GL (Fin r) K),
    (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) =
      (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((h' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) →
    GInt O (h⁻¹ * h') := by
  intro O K _ _ _ r h h' heq
  show IntM O (h⁻¹ * h').1 ∧ IntM O ((h⁻¹ * h')⁻¹).1
  refine ⟨intM_inv_mul_of_map_le heq.ge, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  exact intM_inv_mul_of_map_le heq.le

end GlobalTheory.SplitHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantEtaleBasisChangeByOEUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ChangeEtaleBasis.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  intro l _ K bk d ρ T0 Wm Wm' A0 A0' hT0 hA0 hA0' hfr hAA hW hW' hWW
  have hO := _root_.GlobalTheory.OEDvr.main l K bk
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → Wm.map (galW l (g : GQ l)) = Wm := by
    intro g hg
    exact Matrix.ext fun i j => by
      simp only [Matrix.map_apply]
      exact hO.2.2.2.2.2.1 g hg _ (hW i j)
  have hfrob : ∀ M : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → ∀ i j, M.map (frobW l) i j ∈ bk.OE := by
    intro M hM i j
    exact hO.2.2.2.2.2.2 _ (hM i j)
  have hmul : ∀ M N : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → (∀ i j, N i j ∈ bk.OE) → ∀ i j, (M * N) i j ∈ bk.OE := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ (fun k _ => Subring.mul_mem _ (hM i k) (hN k j))
  have hW'W : Wm' * Wm = 1 := mul_eq_one_comm.mp hWW
  refine ⟨?_, Wm' * A0 * Wm.map (frobW l), Wm'.map (frobW l) * A0' * Wm, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hmap : (T0 * Wm).map (galW l (g : GQ l)) = T0.map (galW l (g : GQ l)) * Wm.map (galW l (g : GQ l)) :=
      Matrix.map_mul (f := ((galW l (g : GQ l)) : WCb l →+* WCb l))
    rw [hmap, hgal g hg, ← Matrix.mul_assoc, hT0 g hg]
  · exact hmul _ _ (hmul _ _ hW' hA0) (hfrob _ hW)
  · exact hmul _ _ (hmul _ _ (hfrob _ hW') hA0') hW
  · have hmap : (T0 * Wm).map (frobW l) = T0.map (frobW l) * Wm.map (frobW l) :=
      Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
    rw [hmap, hfr]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wm Wm', hWW, Matrix.one_mul]
  · have hφ : Wm.map (frobW l) * Wm'.map (frobW l) = 1 := by
      have e : (Wm * Wm').map (frobW l) = Wm.map (frobW l) * Wm'.map (frobW l) :=
        Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
      rw [← e, hWW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    calc Wm' * A0 * Wm.map (frobW l) * (Wm'.map (frobW l) * A0' * Wm)
        = Wm' * A0 * (Wm.map (frobW l) * Wm'.map (frobW l)) * A0' * Wm := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hφ, Matrix.mul_one, Matrix.mul_assoc Wm', hAA, Matrix.mul_one, hW'W]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrIsIntegralInvInFieldFactor
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem idem_mul_aeval_idem_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (w : A) (p : R[X]) :
    f * aeval (f * w) p = f * aeval w p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), mul_add, mul_add, hp, hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, mul_pow]
    calc f * (algebraMap R A a * (f ^ n * w ^ n)) = algebraMap R A a * ((f * f ^ n) * w ^ n) := by ring
      _ = algebraMap R A a * (f * w ^ n) := by rw [← pow_succ', hf.pow_succ_eq]
      _ = f * (algebraMap R A a * w ^ n) := by ring

theorem isIntegral_idem_mul_of_quot {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (w : A)
    (h : IsIntegral R (Ideal.Quotient.mk (Ideal.span {1 - f}) w)) : IsIntegral R (f * w) := by
  obtain ⟨q, hq, hqw⟩ := h
  have h0 : aeval w q ∈ Ideal.span {1 - f} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← hqw, ← aeval_def]
    exact (aeval_algHom_apply (Ideal.Quotient.mkₐ R (Ideal.span {1 - f})) w q).symm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h0
  have h1 : f * aeval w q = 0 := by
    rw [hc, ← mul_assoc, mul_sub, mul_one, hf.eq, sub_self, zero_mul]
  refine ⟨X * q, monic_X.mul hq, ?_⟩
  rw [← aeval_def, map_mul, aeval_X, mul_assoc, mul_left_comm, idem_mul_aeval_idem_mul hf w q, h1, mul_zero]

theorem isIntegral_or_isIntegral_of_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f →
    (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f → IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := by
  intro K B f y z hf hinv hyz
  by_cases hf0 : f = 0
  · left; rw [hf0, zero_mul]; exact isIntegral_zero
  set I : Ideal B.A := Ideal.span {1 - f} with hI
  have hmk : ∀ a b : B.A, Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ ∃ c, a - b = (1 - f) * c := by
    intro a b
    rw [Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
    rfl
  have hf1 : Ideal.Quotient.mk I f = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), hmk]
    exact ⟨-1, by ring⟩
  have hfm : ∀ a : B.A, Ideal.Quotient.mk I (f * a) = Ideal.Quotient.mk I a := by
    intro a; rw [map_mul, hf1, one_mul]
  have hfield : IsField (B.A ⧸ I) := by
    refine ⟨⟨0, 1, fun h => hf0 ?_⟩, mul_comm, ?_⟩
    · obtain ⟨c, hc⟩ := (hmk 0 1).1 h
      have := congrArg (f * ·) hc
      simp only [mul_sub, mul_zero, mul_one, zero_sub] at this
      rw [← mul_assoc, mul_sub, mul_one, hf.eq, sub_self, zero_mul] at this
      simpa using this
    · intro a ha
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hfx : f * x ≠ 0 := by
        intro h0
        apply ha
        rw [← hfm x, h0, map_zero]
      obtain ⟨v, hv⟩ := hinv x hfx
      refine ⟨Ideal.Quotient.mk I v, ?_⟩
      rw [← map_mul, ← hfm (x * v), ← mul_assoc, hv, hf1]
  haveI : I.IsMaximal := Ideal.Quotient.maximal_of_isField I hfield
  letI : Field (B.A ⧸ I) := Ideal.Quotient.field I
  haveI : CharZero K.O :=
    ⟨fun m n h => Nat.cast_injective (R := K.E) (by simpa using congrArg (algebraMap K.O K.E) h)⟩
  let e : FractionRing K.O ≃ₐ[K.O] K.E := IsLocalization.algEquiv (nonZeroDivisors K.O) (FractionRing K.O) K.E
  letI : Algebra (FractionRing K.O) (B.A ⧸ I) :=
    ((algebraMap K.E (B.A ⧸ I)).comp (e : FractionRing K.O →+* K.E)).toAlgebra
  haveI : IsScalarTower K.O (FractionRing K.O) (B.A ⧸ I) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change _ = algebraMap K.E (B.A ⧸ I) (e (algebraMap K.O (FractionRing K.O) x))
    rw [AlgEquiv.commutes]
    first
      | exact IsScalarTower.algebraMap_apply K.O K.E (B.A ⧸ I) x
      | rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsIntegral (FractionRing K.O) (B.A ⧸ I) := by
    refine ⟨fun x => ?_⟩
    have hx : IsIntegral K.E x := Algebra.IsIntegral.isIntegral x
    have := IsIntegral.map_of_comp_eq (e.symm : K.E →+* FractionRing K.O) (RingHom.id (B.A ⧸ I)) ?_ hx
    · simpa using this
    · ext t
      change algebraMap K.E (B.A ⧸ I) (e (e.symm t)) = _
      simp
  have hinv' : Ideal.Quotient.mk I (f * z) = (Ideal.Quotient.mk I (f * y))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← hfm, show f * (f * z * (f * y)) = f * y * z * f * f by ring, hyz, hf.eq, hf.eq, hf1]
  rcases GlobalTheory.LN.isIntegral_or_isIntegral_inv K.O (B.A ⧸ I) (Ideal.Quotient.mk I (f * y)) with h | h
  · left
    have := isIntegral_idem_mul_of_quot hf (f * y) h
    rwa [← mul_assoc, hf.eq] at this
  · right
    rw [← hinv'] at h
    have := isIntegral_idem_mul_of_quot hf (f * z) h
    rwa [← mul_assoc, hf.eq] at this

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeApproximationMittagLeffler
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim


set_option maxHeartbeats 1000000 in
theorem mittagLeffler_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (tw.d' n) → bk.S, ∃ s' : Fin (tw.d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hT0 hR hRF n
  set I : Ideal (WCb l) := Ideal.span {(l : WCb l) ^ n} with hI
  let q : WCb l →+* WCb l ⧸ I := Ideal.Quotient.mk I
  have hq : ∀ w, (l : WCb l) ^ n ∣ w ↔ q w = 0 := fun w => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  have hmat : ∀ {a b : ℕ} (A B : Matrix (Fin a) (Fin b) (WCb l)), (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) →
      A.map q = B.map q := by
    intro a b A B h
    ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub]
    exact (hq _).1 (h i j)
  have hvec : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (WCb l)) (v : Fin b → WCb l),
      (fun i => q ((M *ᵥ v) i)) = M.map q *ᵥ fun j => q (v j) := fun M v => funext fun i => RingHom.map_mulVec q M v i
  obtain ⟨c, y, hcy⟩ := GlobalTheory.BKLim.flatPow_dvd_perPow_mod l K bk τ hτ (2 * N) n
  refine ⟨c, fun m hnm s => ?_⟩

  obtain ⟨Yn, Y'n, hYn, -⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N (tw.d' n) _ (F n)
  obtain ⟨Ym, Y'm, hYm, hYYm⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N (tw.d' m) _ (F m)
  obtain ⟨Sm, hSm⟩ := (tw.onto m).surj
  have hu : IsUnit (inclW l τ ^ N) := (_root_.GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1.pow N

  have hTY : (F m).T * Y'm.map (inclW l) = inclW l τ ^ N • (1 : Matrix _ _ (WCb l)) := by
    have h1 : (Ym * Y'm).map (inclW l) = (τ ^ (2 * N) • (1 : Matrix _ _ (Ainf l))).map (inclW l) := by rw [hYYm]
    rw [Matrix.map_mul, hYm] at h1
    have h2 : (τ ^ (2 * N) • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Ainf l))).map (inclW l) =
        inclW l τ ^ N • (inclW l τ ^ N • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (WCb l))) := by
      rw [smul_smul, ← pow_add, ← two_mul, ← map_pow]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [← hu.smul_left_cancel, ← Matrix.smul_mul, h1, h2]
  let qi : Ainf l →+* WCb l ⧸ I := q.comp (inclW l)
  have hv : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (Ainf l)) (v : Fin b → Ainf l),
      (fun i => qi ((M *ᵥ v) i)) = M.map qi *ᵥ fun j => qi (v j) := fun M v => funext fun i => RingHom.map_mulVec qi M v i
  have hzq : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ_[l]),
      (M.map (algebraMap ℤ_[l] (Ainf l))).map qi = (zW M).map q := fun M => by
    ext i j
    show q (inclW l (algebraMap ℤ_[l] (Ainf l) (M i j))) = q (algebraMap ℤ_[l] (WCb l) (M i j))
    congr 1
    exact (inclWA l).commutes _

  have F1 : T0.map q * (R n).map q = (zW (tw.Pi n)).map q * (F n).T.map q := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact (hmat _ _ fun i j => by rw [Matrix.sub_apply, dvd_sub_comm, ← Matrix.sub_apply]; exact hRF n i j)
  have F2 : T0.map q * (R m).map q = (zW (tw.Pi m)).map q * (F m).T.map q := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact (hmat _ _ fun i j => by
      rw [Matrix.sub_apply, dvd_sub_comm, ← Matrix.sub_apply]; exact dvd_trans (pow_dvd_pow _ hnm) (hRF m i j))
  have F3 : (zW (tw.Pi m)).map q * (zW Sm).map q = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_one q (map_zero q) (map_one q)]
    refine hmat _ _ fun i j => dvd_trans (pow_dvd_pow _ hnm) ?_
    have h := map_dvd (algebraMap ℤ_[l] (WCb l)) (hSm i j)
    rw [map_pow, map_natCast] at h
    convert h using 1
    rw [← Matrix.map_mul, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have F4 : Yn.map qi = qi τ ^ N • (F n).T.map q := by
    have : Yn.map qi = (Yn.map (inclW l)).map q := by ext i j; rfl
    rw [this, hYn]; ext i j; simp [qi]
  have F5 : (F m).T.map q * Y'm.map qi = qi τ ^ N • (1 : Matrix _ _ (WCb l ⧸ I)) := by
    have : Y'm.map qi = (Y'm.map (inclW l)).map q := by ext i j; rfl
    rw [this, ← Matrix.map_mul, hTY]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp [qi]
  have hXc : q (inclW l (bk.ev X ^ c)) = qi τ ^ (2 * N) * qi y := by
    have h0 : (l : WCb l) ^ n ∣ inclW l (bk.ev X ^ c - τ ^ (2 * N) * y) := by
      have := map_dvd (inclW l) hcy
      rwa [map_pow, map_natCast] at this
    have h := (hq _).1 h0
    rw [map_sub, map_sub, sub_eq_zero] at h
    rw [h]
    simp [qi]
  have F6 : (fun j => q (bk.evW (X ^ c * s j))) = (qi τ ^ (2 * N) * qi y) • fun j => qi (bk.ev (s j)) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, ← hXc]
    show q (inclW l (bk.ev (X ^ c * s j))) = q (inclW l (bk.ev X ^ c)) * q (inclW l (bk.ev (s j)))
    rw [map_mul, map_pow, map_mul, map_mul]

  set e : Fin (tw.d' n) → WCb l ⧸ I := fun j => qi (bk.ev (s j)) with he
  set zA := algebraMap ℤ_[l] (Ainf l) with hzA
  set w1 : Fin (tw.d' m) → Ainf l := (Sm.map zA) *ᵥ ((tw.Pi n).map zA *ᵥ (Yn *ᵥ fun j => bk.ev (s j))) with hw1
  set a : Fin (tw.d' m) → Ainf l := y • (Y'm *ᵥ w1) with ha
  have hqa : (fun j => q (inclW l (a j))) =
      qi y • (Y'm.map qi *ᵥ ((zW Sm).map q *ᵥ ((zW (tw.Pi n)).map q *ᵥ (Yn.map qi *ᵥ e)))) := by
    have h0 : (fun j => q (inclW l (a j))) = qi y • fun j => qi ((Y'm *ᵥ w1) j) := by
      funext j
      simp only [ha, Pi.smul_apply, smul_eq_mul, map_mul]
      rfl
    rw [h0, hv, hw1, hv, hv, hv, hzq, hzq]
  obtain ⟨T0i, hT0i⟩ := (hT0.map (RingHom.mapMatrix q)).exists_left_inv
  have hT0i' : T0i * T0.map q = 1 := hT0i
  have G : (R n).map q *ᵥ ((qi τ ^ (2 * N) * qi y) • e) =
      (R m).map q *ᵥ (qi y • (Y'm.map qi *ᵥ ((zW Sm).map q *ᵥ ((zW (tw.Pi n)).map q *ᵥ (Yn.map qi *ᵥ e))))) := by
    have canc : ∀ u v : Fin d → WCb l ⧸ I, T0.map q *ᵥ u = T0.map q *ᵥ v → u = v := fun u v h => by
      have := congrArg (fun x => T0i *ᵥ x) h
      simpa only [Matrix.mulVec_mulVec, hT0i', Matrix.one_mulVec] using this
    apply canc
    have L : T0.map q *ᵥ ((R n).map q *ᵥ ((qi τ ^ (2 * N) * qi y) • e)) =
        (qi τ ^ (2 * N) * qi y) • (((zW (tw.Pi n)).map q * (F n).T.map q) *ᵥ e) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, F1]
    have Rr : T0.map q *ᵥ ((R m).map q *ᵥ (qi y • (Y'm.map qi *ᵥ ((zW Sm).map q *ᵥ ((zW (tw.Pi n)).map q *ᵥ (Yn.map qi *ᵥ e)))))) =
        (qi y * qi τ ^ N * qi τ ^ N) • (((zW (tw.Pi n)).map q * (F n).T.map q) *ᵥ e) := by
      simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
      rw [F2, Matrix.mul_assoc ((zW (tw.Pi m)).map q), F5, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.smul_mul, F3, Matrix.one_mul, F4]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mulVec, smul_smul]
      first | rfl | (congr 1; ring)
    rw [L, Rr]
    congr 1
    ring
  have hev : ∀ t : bk.S, bk.evW t ∈ bk.OE := fun t => by
    intro k
    exact ⟨0, t, 0, by simp⟩
  have hxOE : ∀ i, (R n *ᵥ fun j => bk.evW (X ^ c * s j)) i ∈ bk.OE := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hR n i j) (hev _)
  obtain ⟨s', hs'⟩ := _root_.GlobalTheory.descentCoefficients l K bk d (tw.d' m) n (R m) (R n *ᵥ fun j => bk.evW (X ^ c * s j)) a (hR m) hxOE
    (fun i => by
      rw [hq, Pi.sub_apply, map_sub, sub_eq_zero]
      have h1 : q ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) i) =
          ((R n).map q *ᵥ fun j => q (bk.evW (X ^ c * s j))) i := congrFun (hvec (R n) fun j => bk.evW (X ^ c * s j)) i
      have h2 : q ((R m *ᵥ fun j => inclW l (a j)) i) = ((R m).map q *ᵥ fun j => q (inclW l (a j))) i :=
        congrFun (hvec (R m) fun j => inclW l (a j)) i
      rw [h1, h2, F6, hqa, G])
  exact ⟨s', hs'⟩

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorMemOEAndAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.BKLim.limvec_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v) := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hR hF v hv
  have hcl := _root_.GlobalTheory.OEStable.main l K bk
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have key : ∀ (k : ℕ) (z : WCb l), (l : WCb l) ^ k ∣ z ↔
      Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) z = 0 := fun k z => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun i => ?_, ?_⟩
  · apply hcl.2.1
    intro n
    obtain ⟨s', hs'⟩ := hv n
    refine ⟨(R n *ᵥ fun j => bk.evW (s' j)) i, ?_, hs' i⟩
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hR n i j) (hevW _)
  · have hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x :=
      fun x => (inclWA l).commutes x
    have hx : ∀ i k, ∃ a : Ainf l, (l : WCb l) ^ k ∣
        (l : WCb l) ^ 0 * (inclW l τ ^ N • (T0 *ᵥ v)) i - inclW l (1 * a) := by
      intro i k
      obtain ⟨s', hs'⟩ := hv k
      obtain ⟨Y, Y', hY, -⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N (tw.d' k) (fun g => (tw.ρ' k g).val) (F k)
      refine ⟨(((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i, ?_⟩
      set q := Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) with hq
      rw [key, pow_zero, one_mul, one_mul, map_sub, sub_eq_zero]
      have h1 : (fun i => q (v i)) = fun i => q ((R k *ᵥ fun j => bk.evW (s' j)) i) := funext fun i => by
        have := (key k _).1 (hs' i); rwa [Pi.sub_apply, map_sub, sub_eq_zero] at this
      have h2 : (zW (tw.Pi k) * (F k).T).map q = (T0 * R k).map q := by
        ext i j; have := (key k _).1 (hF k i j); rwa [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      have e1 : inclW l ((((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i) =
          (inclW l τ ^ N • ((zW (tw.Pi k) * (F k).T) *ᵥ fun j => bk.evW (s' j))) i := by
        rw [RingHom.map_mulVec, Matrix.map_mul, hY, Matrix.map_map]
        have : (tw.Pi k).map ((inclW l) ∘ (algebraMap ℤ_[l] (Ainf l))) = zW (tw.Pi k) := by
          ext a b; simp [zW, hinc]
        rw [this, Matrix.mul_smul, Matrix.smul_mulVec]
        rfl
      rw [e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
        RingHom.map_mulVec, RingHom.map_mulVec, h2, Matrix.map_mul, ← Matrix.mulVec_mulVec]
      have h1' : (⇑q ∘ v) = (R k).map q *ᵥ (⇑q ∘ fun j => bk.evW (s' j)) := funext fun j => by
        rw [Function.comp_apply, ← RingHom.map_mulVec]; exact congrFun h1 j
      rw [h1']
    refine ⟨fun i => Classical.choose (_root_.GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by simp) 0 _ (hx i)), funext fun i => ?_⟩
    have := Classical.choose_spec (_root_.GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by simp) 0 _ (hx i))
    rw [one_mul] at this
    exact this.symm
end

