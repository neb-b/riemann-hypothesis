module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdeal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_smul_top_eq {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) :
    (I ^ n • (⊤ : Submodule A A)) = I ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem mulVec_mem_of_mem {B : Type} [CommRing B] {d : ℕ} (E : Matrix (Fin d) (Fin d) B) (J : Ideal B)
    (v : Fin d → B) (hv : ∀ j, v j ∈ J) (i : Fin d) : E.mulVec v i ∈ J := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv j)

theorem lift_solution_of_step {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (hA : IsPrecomplete I A) (hB : IsHausdorff J B) {d : ℕ} (p q : A →+* B)
    (hp : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap p) (hq : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap q)
    (E : Matrix (Fin d) (Fin d) B)
    (step : ∀ (m : ℕ) (z : Fin d → A), (∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ m) →
      ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ m) ∧
        ∀ i, p (z' i) - E.mulVec (fun j => q (z' j)) i ∈ J ^ (m + 1))
    (z : Fin d → A) (hz : ∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ 1) :
    ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ 1) ∧
      (fun i => p (z' i)) = E.mulVec (fun j => q (z' j)) := by

  let res : (Fin d → A) → Fin d → B := fun w i => p (w i) - E.mulVec (fun j => q (w j)) i
  have hres_sub : ∀ (w w' : Fin d → A) (i : Fin d),
      res w i - res w' i = p (w i - w' i) - E.mulVec (fun j => q (w j - w' j)) i := by
    intro w w' i
    have : (fun j => q (w j - w' j)) = (fun j => q (w j)) - (fun j => q (w' j)) := by
      funext j; simp
    show p (w i) - E.mulVec (fun j => q (w j)) i - (p (w' i) - E.mulVec (fun j => q (w' j)) i) = _
    rw [this, Matrix.mulVec_sub, Pi.sub_apply, map_sub]
    ring

  have hseq : ∃ g : ℕ → (Fin d → A), g 0 = z ∧ (∀ k i, res (g k) i ∈ J ^ (k + 1)) ∧
      ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := by
    let G : (k : ℕ) → {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)} := fun k =>
      Nat.rec (motive := fun k => {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)}) ⟨z, hz⟩
        (fun k w => ⟨Classical.choose (step (k + 1) w.1 w.2),
          (Classical.choose_spec (step (k + 1) w.1 w.2)).2⟩) k
    refine ⟨fun k => (G k).1, rfl, fun k => (G k).2, fun k i => ?_⟩
    exact (Classical.choose_spec (step (k + 1) (G k).1 (G k).2)).1 i
  let g := Classical.choose hseq
  have hg0 : g 0 = z := (Classical.choose_spec hseq).1
  have hgres : ∀ k i, res (g k) i ∈ J ^ (k + 1) := (Classical.choose_spec hseq).2.1
  have hgd : ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := (Classical.choose_spec hseq).2.2

  have hcau : ∀ i {m n : ℕ}, m ≤ n → g n i - g m i ∈ I ^ m := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : g (n + 1) i - g n i ∈ I ^ m :=
        Ideal.pow_le_pow_right (by omega) (hgd n i)
      have := Ideal.add_mem _ h1 ih
      simpa using this

  have hlim : ∀ i, ∃ L : A, ∀ n, g n i - L ∈ I ^ n := by
    intro i
    have h := @IsPrecomplete.prec' A _ I A _ _ hA (fun k => g k i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, pow_smul_top_eq]
      have := hcau i hmn
      rw [← neg_mem_iff, neg_sub] at this
      exact this)
    refine ⟨Classical.choose h, fun n => ?_⟩
    have := Classical.choose_spec h n
    rw [SModEq.sub_mem, pow_smul_top_eq] at this
    exact this
  let z' : Fin d → A := fun i => Classical.choose (hlim i)
  have hz' : ∀ i n, g n i - z' i ∈ I ^ n := fun i => Classical.choose_spec (hlim i)
  refine ⟨z', fun i => ?_, ?_⟩
  · have h1 : g 1 i - z' i ∈ I ^ 1 := hz' i 1
    have h2 : g 1 i - g 0 i ∈ I ^ 1 := hgd 0 i
    rw [hg0] at h2
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  · funext i
    rw [← sub_eq_zero]
    refine hB.haus' _ fun k => ?_
    rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
    have hd : res (g k) i - res z' i ∈ J ^ k := by
      rw [hres_sub]
      refine Ideal.sub_mem _ (hp k (hz' i k)) ?_
      exact mulVec_mem_of_mem E _ _ (fun j => hq k (hz' j k)) i
    have hr : res (g k) i ∈ J ^ k := Ideal.pow_le_pow_right (by omega) (hgres k i)
    have := Ideal.sub_mem _ hr hd
    simpa [res] using this

theorem lift_solution (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hh : Cover h)
    (hpo : IsPO h h p q) (z : Fin d → C.A)
    (hz : ∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧
      (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) :=
  lift_solution_of_step (adI C) (adI D) C.complete.toIsPrecomplete D.complete.toIsHausdorff p.f q.f
    (adI_pow_le p) (adI_pow_le q) _ (_root_.GlobalTheory.BSP.lift_solution_succ l K bk d S B C D h f p q hh hpo) z hz

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.EquivKisin


set_option maxHeartbeats 1000000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N N' d d' : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Pre bk N d ρ) (F' : Pre bk N' d' ρ') (f : Matrix (Fin d') (Fin d) (ℤ_[l])), (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) (bk.S), F'.T * Y.map bk.evW = zW f * F.T := by
  intro l _ K bk τ hτ N N' d d' ρ ρ' F F' f hf
  obtain ⟨u, hu⟩ := F'.unit
  have cancel : ∀ M M' : Matrix (Fin d') (Fin d) (WCb l), F'.T * M = F'.T * M' → M = M' := by
    intro M M' h
    have h2 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) h
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  set Xm : Matrix (Fin d') (Fin d) (WCb l) := (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * (zW f * F.T) with hXm
  have hX : F'.T * Xm = zW f * F.T := by
    rw [hXm, ← hu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

  have hfix : ∀ g : ↥(GK K), bk.FixFlat g → Xm.map (galW l (g : GQ l)) = Xm := by
    intro g hg
    let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M :=
      fun M => Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have a1 : zW (ρ' g) * F'.T.map G = F'.T := F'.fix g hg
    have a2 : zW (ρ g) * F.T.map G = F.T := F.fix g hg
    change Xm.map G = Xm
    apply cancel
    have h1 := congrArg (fun M => M.map G) hX
    simp only [Matrix.map_mul, hzG] at h1
    calc F'.T * Xm.map G = zW (ρ' g) * (F'.T.map G * Xm.map G) := by
          rw [← Matrix.mul_assoc, a1]
      _ = zW (ρ' g * f) * F.T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * F.T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = F'.T * Xm := by rw [a2, hX]

  have hφ : bk.evW bk.E ^ N • (F'.A.map bk.evW * Xm.map (frobW l)) =
      bk.evW bk.E ^ N' • (Xm * F.A.map bk.evW) := by
    let Fr : WCb l →+* WCb l := (frobW l).toRingHom
    have hzF : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map Fr = zW M :=
      fun M => Matrix.ext fun i j => (frobW l).commutes _
    have b1 : bk.evW bk.E ^ N • F.T.map Fr = F.T * F.A.map bk.evW := F.φ
    have b2 : bk.evW bk.E ^ N' • F'.T.map Fr = F'.T * F'.A.map bk.evW := F'.φ
    change bk.evW bk.E ^ N • (F'.A.map bk.evW * Xm.map Fr) = bk.evW bk.E ^ N' • (Xm * F.A.map bk.evW)
    apply cancel
    have h1 := congrArg (fun M => M.map Fr) hX
    simp only [Matrix.map_mul, hzF] at h1
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← b2, Matrix.smul_mul, h1, smul_smul,
      ← Matrix.mul_assoc, hX, Matrix.mul_assoc, ← b1, Matrix.mul_smul, smul_smul, mul_comm]

  have hOE : ∀ i j, Xm i j ∈ bk.OE := by
    obtain ⟨w, hw, hew⟩ := (_root_.GlobalTheory.OEDvr.main l K bk).2.2.1 bk.E (GlobalTheory.BSP.EquivOE.not_dvd_E bk)
    have hA : F.A.map bk.evW * F.A'.map bk.evW =
        bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
      rw [← Matrix.map_mul, F.A_mul]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    have h1 : Xm = (w ^ (N' + 2 * N) * bk.evW bk.E ^ N) •
        (F'.A.map bk.evW * Xm.map (frobW l) * F.A'.map bk.evW) := by
      rw [mul_smul, ← Matrix.smul_mul, hφ, Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, smul_smul, mul_assoc, ← pow_add, ← mul_pow, mul_comm w, hew, one_pow, one_smul]
    intro i j
    refine _root_.GlobalTheory.BSP.invariant_phi_solution_mem_OE l K bk (Fin d' × Fin d) (fun p => Xm p.1 p.2)
      (fun p q => w ^ (N' + 2 * N) * bk.evW bk.E ^ N * bk.evW (F'.A q.1 p.1) * bk.evW (F.A' p.2 q.2))
      (fun p q => ?_) (fun q => ?_) (fun g h q => ?_) (i, j)
    · exact bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.pow_mem hw _)
        (bk.OE.pow_mem (GlobalTheory.BSP.EquivOE.evW_mem bk _) _)) (GlobalTheory.BSP.EquivOE.evW_mem bk _))
        (GlobalTheory.BSP.EquivOE.evW_mem bk _)
    · have h2 := congrFun (congrFun h1 q.1) q.2
      rw [h2, Fintype.sum_prod_type_right]
      simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
    · exact congrFun (congrFun (hfix g h) q.1) q.2

  obtain ⟨Y₁, Y₁', hY₁, hY₁'⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N' d' ρ' F'
  obtain ⟨Y₂, Y₂', hY₂, hY₂'⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N d ρ F
  set t : WCb l := inclW l τ with ht
  have hinv : t ^ N' • Y₁'.map (inclW l) = t ^ N' • (t ^ N' • (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l))) := by
    have e1 := congrArg (fun M => M.map (inclW l)) hY₁'
    simp only [Matrix.map_mul, hY₁] at e1
    have e2 : (τ ^ (2 * N') • (1 : Matrix (Fin d') (Fin d') (Ainf l))).map (inclW l) =
        (t ^ N' * t ^ N') • (1 : Matrix (Fin d') (Fin d') (WCb l)) := by
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply, ht, ← pow_add, two_mul]
    rw [e2, Matrix.smul_mul, ← hu] at e1
    have e3 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) e1
    simp only [Matrix.mul_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_one] at e3
    rw [e3, smul_smul]
  have hzf : (f.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW f := by
    exact Matrix.ext fun i j => (inclWA l).commutes (f i j)
  let x : Matrix (Fin d') (Fin d) (Ainf l) := τ ^ N' • (Y₁' * f.map (algebraMap ℤ_[l] (Ainf l)) * Y₂)
  have hx : x.map (inclW l) = inclW l τ ^ (2 * N' + N) • Xm := by
    have : x.map (inclW l) = t ^ N' • (Y₁'.map (inclW l) * zW f * (t ^ N • F.T)) := by
      have e : x.map (inclW l) = t ^ N' • ((Y₁' * f.map (algebraMap ℤ_[l] (Ainf l)) * Y₂).map (inclW l)) :=
        Matrix.ext fun i j => by simp only [x, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, ht]
      rw [e, Matrix.map_mul, Matrix.map_mul, hzf, hY₂]
    rw [this, ← Matrix.smul_mul, ← Matrix.smul_mul, hinv, hXm]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [← ht]
    congr 1
    ring
  obtain ⟨Y, hY⟩ := _root_.GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d' (2 * N' + N) Xm x hOE hx
  exact ⟨Y, by rw [hY, hX]⟩

end GlobalTheory.BKLim.EquivKisin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleOEBasisOfIsogenousLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EtBasis

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_ne_zero (x : ℤ_[l]) (hx : x ≠ 0) : algebraMap ℤ_[l] (WCb l) x ≠ 0 := by
  rw [PadicInt.unitCoeff_spec hx, map_mul, map_pow, map_natCast]
  exact mul_ne_zero ((PadicInt.unitCoeff hx).isUnit.map _).ne_zero
    (pow_ne_zero _ (WittVector.irreducible l).ne_zero)

theorem algebraMap_mem_OE {K : FinExt l} (bk : BK K) (x : ℤ_[l]) : algebraMap ℤ_[l] (WCb l) x ∈ bk.OE := by
  intro n
  obtain ⟨y, hy⟩ := (Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x))
  refine ⟨0, (PadicInt.appr x n : bk.S), algebraMap ℤ_[l] (WCb l) y, ?_⟩
  have : x = (PadicInt.appr x n : ℤ_[l]) + (l : ℤ_[l]) ^ n * y := by rw [mul_comm, hy]; ring
  have h2 := congrArg (algebraMap ℤ_[l] (WCb l)) this
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at h2
  rw [pow_zero, one_mul, h2, map_natCast]

theorem evW_mem_OE {K : FinExt l} (bk : BK K) (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem not_l_dvd_E {K : FinExt l} (bk : BK K) : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨t, ht⟩
  have h := congrArg (coeff bk.Ep.natDegree) ht
  rw [← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) h
  rw [map_mul, map_natCast, map_one, CharP.cast_eq_zero, zero_mul] at h2
  exact one_ne_zero h2

theorem adj_comm {d : ℕ} (f A B : Matrix (Fin d) (Fin d) ℤ_[l]) (hf : f.det ≠ 0) (h : f * B = A * f) :
    f.adjugate * A = B * f.adjugate := by
  have h1 : f.det • (f.adjugate * A) = f.det • (B * f.adjugate) := by
    calc f.det • (f.adjugate * A) = f.adjugate * A * (f * f.adjugate) := by
          rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
      _ = f.adjugate * (f * B) * f.adjugate := by rw [h]; simp only [Matrix.mul_assoc]
      _ = f.det • (B * f.adjugate) := by
          rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  exact smul_right_injective _ hf h1

end GlobalTheory.EtBasis

namespace GlobalTheory.EtBasis

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ'' : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (F : Pre bk N d ρ) (f : Matrix (Fin d) (Fin d) (ℤ_[l])), f.det ≠ 0 → (∀ g, IsUnit (ρ'' g)) →
    (∀ g, f * ρ'' g = ρ g * f) → ∃ T'' P : Matrix (Fin d) (Fin d) (WCb l), IsUnit T'' ∧ (∀ i j, P i j ∈ bk.OE) ∧
      zW f * T'' = F.T * P := by
  intro l _ K bk τ _ N d ρ ρ'' F f hf hρ'' hfρ
  obtain ⟨hsat1, -, hinvS, -, -, hgalOE, hfrobOE⟩ := _root_.GlobalTheory.OEDvr.main l K bk
  have hl0 : (l : WCb l) ≠ 0 := (WittVector.irreducible l).ne_zero
  have hzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], zW M = (algebraMap ℤ_[l] (WCb l)).mapMatrix M := fun _ => rfl
  have hzWmul : ∀ M M' : Matrix (Fin d) (Fin d) ℤ_[l], zW (M * M') = zW M * zW M' := fun M M' => by
    rw [hzW, hzW, hzW, map_mul]
  have hfadj : zW f * zW f.adjugate = algebraMap ℤ_[l] (WCb l) f.det • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← hzWmul, Matrix.mul_adjugate]
    ext i j
    by_cases h : i = j <;> simp [zW, h, Matrix.one_apply]
  have hTdet : F.T.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 F.unit).ne_zero
  have hdf : algebraMap ℤ_[l] (WCb l) f.det ≠ 0 := algebraMap_ne_zero _ hf
  set Y1 := zW f.adjugate * F.T with hY1
  have hY1det : Y1.det ≠ 0 := by
    rw [hY1, Matrix.det_mul, hzW, ← RingHom.map_det, Matrix.det_adjugate, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hdf) hTdet
  obtain ⟨m, P₀, Y', hP₀, hP₀det, hY', hlat, hsat⟩ := GlobalTheory.SatLattice.exists_lattice_basis l K bk d Y1 hY1det
  have hlm : (l : WCb l) ^ m ≠ 0 := pow_ne_zero _ hl0
  have hcancel : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (l : WCb l) ^ m • M = (l : WCb l) ^ m • M' → M = M' :=
    fun M M' h => Matrix.ext fun i j => mul_left_cancel₀ hlm (congrFun (congrFun h i) j)

  have hY'det : Y'.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hY'
    rw [Matrix.det_smul, h0, mul_zero, Matrix.det_mul] at this
    exact mul_ne_zero hY1det hP₀det this.symm

  obtain ⟨e, he, hEe⟩ := hinvS bk.E (not_l_dvd_E bk)
  have hφ : ∃ A'' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A'' i j ∈ bk.OE) ∧ Y'.map (frobW l) = Y' * A'' := by
    set B := e ^ N • F.A.map bk.evW with hB
    have hB_OE : ∀ i j, B i j ∈ bk.OE := fun i j => by
      simp only [hB, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem he N) (evW_mem_OE bk _)
    have hTφ : F.T.map (frobW l) = F.T * B := by
      have h := congrArg (fun M => e ^ N • M) F.φ
      have h1 : e ^ N * bk.evW bk.E ^ N = 1 := by rw [← mul_pow, mul_comm, hEe, one_pow]
      simp only [smul_smul, h1, one_smul] at h
      rw [h, hB, Matrix.mul_smul]
    have hfrobzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], (zW M).map (frobW l) = zW M := fun M => by
      exact Matrix.ext fun i j => (frobW l).commutes _
    have hmapmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l),
        (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
      fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
    have hY1φ : Y1.map (frobW l) = Y1 * B := by
      rw [hY1, hmapmul, hfrobzW, hTφ, Matrix.mul_assoc]
    set V := B * P₀.map (frobW l) with hV
    have hV_OE : ∀ i j, V i j ∈ bk.OE := fun i j => by
      simp only [hV, Matrix.mul_apply]
      exact bk.OE.sum_mem fun k _ => bk.OE.mul_mem (hB_OE i k) (hfrobOE _ (hP₀ k j))
    have hmain : (l : WCb l) ^ m • Y'.map (frobW l) = Y1 * V := by
      have h : ((l : WCb l) ^ m • Y').map (frobW l) = (Y1 * P₀).map (frobW l) := by rw [hY']
      rw [hmapmul, hY1φ] at h
      rw [hV, ← Matrix.mul_assoc, ← h]
      ext i j
      simp [map_mul, map_pow, map_natCast]
    have hcol : ∀ j, ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => V i j) = P₀ *ᵥ w := by
      intro j
      obtain ⟨w, hw, hvw⟩ := hlat (fun i => V i j) (fun i => hV_OE i j) m (fun i => by
        have : (Y1 *ᵥ fun i => V i j) i = (Y1 * V) i j := by
          simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
        rw [this, ← hmain, Matrix.smul_apply, smul_eq_mul]
        exact Dvd.intro _ rfl)
      exact ⟨w, hw, funext fun i => mul_left_cancel₀ hlm (congrFun hvw i)⟩
    choose w hw hvw using hcol
    refine ⟨Matrix.of fun i j => w j i, fun i j => hw j i, ?_⟩
    have hVP : V = P₀ * Matrix.of fun i j => w j i := by
      ext i j
      have := congrFun (hvw j) i
      simp only [Matrix.mulVec, dotProduct] at this
      simp [Matrix.mul_apply, this]
    apply hcancel
    rw [hmain, hVP, ← Matrix.mul_assoc, ← hY', Matrix.smul_mul]

  have hg : ∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧
      R * Y'.map (galW l (g : GQ l)) = Y' := by
    intro g hfix
    refine ⟨zW (ρ'' g), by rw [hzW]; exact (hρ'' g).map _, ?_⟩
    have hgmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (galW l (g : GQ l)) =
        M.map (galW l (g : GQ l)) * M'.map (galW l (g : GQ l)) :=
      fun M M' => Matrix.map_mul (f := (galW l (g : GQ l)).toRingEquiv.toRingHom)
    have hgzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], (zW M).map (galW l (g : GQ l)) = zW M := fun M => by
      exact Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have hgP : P₀.map (galW l (g : GQ l)) = P₀ := by
      exact Matrix.ext fun i j => hgalOE g hfix _ (hP₀ i j)
    have hcomm : zW (ρ'' g) * zW f.adjugate = zW f.adjugate * zW (ρ g) := by
      rw [← hzWmul, ← hzWmul, adj_comm f (ρ g) (ρ'' g) hf (hfρ g)]
    have h : ((l : WCb l) ^ m • Y').map (galW l (g : GQ l)) = (Y1 * P₀).map (galW l (g : GQ l)) := by rw [hY']
    rw [hgmul, hY1, hgmul, hgzW, hgP] at h
    have hs : ((l : WCb l) ^ m • Y').map (galW l (g : GQ l)) = (l : WCb l) ^ m • Y'.map (galW l (g : GQ l)) := by
      ext i j; simp
    apply hcancel
    rw [← Matrix.mul_smul, ← hs, h, hY', hY1]
    calc zW (ρ'' g) * (zW f.adjugate * F.T.map (galW l (g : GQ l)) * P₀)
        = zW (ρ'' g) * zW f.adjugate * F.T.map (galW l (g : GQ l)) * P₀ := by simp only [Matrix.mul_assoc]
      _ = zW f.adjugate * (zW (ρ g) * F.T.map (galW l (g : GQ l))) * P₀ := by
          rw [hcomm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [F.fix g hfix]
  obtain ⟨A'', hA'', hφ'⟩ := hφ
  have hunit : IsUnit Y' := GlobalTheory.SatInvUnit.isUnit_of_saturated l K bk d Y' A'' hY'det hA'' hφ' hg hsat
  set Ti := F.T⁻¹ with hTi'
  have hTi : Ti * F.T = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 F.unit)
  have hTTi : F.T * Ti = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 F.unit)
  refine ⟨Y', Ti * zW f * Y', hunit, fun i j => ?_, ?_⟩
  · have hP : (l : WCb l) ^ m • (Ti * zW f * Y') = algebraMap ℤ_[l] (WCb l) f.det • P₀ := by
      rw [← Matrix.mul_smul, hY', hY1]
      calc Ti * zW f * (zW f.adjugate * F.T * P₀) = Ti * (zW f * zW f.adjugate) * F.T * P₀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hfadj, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, hTi, Matrix.one_mul]
    have := congrFun (congrFun hP i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    refine GlobalTheory.SatLattice.sat_pow bk.OE hl0 hsat1 m _ ?_
    rw [this]
    exact bk.OE.mul_mem (algebraMap_mem_OE bk _) (hP₀ i j)
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hTTi, Matrix.one_mul]

end GlobalTheory.EtBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProof
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem fontaineBcris_of_tensorInj
    (h : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj) : GlobalTheory.Published.FontaineBcris :=
  GlobalTheory.Published.FontaineBcris.of_rest fun l _ C =>
    ⟨h l C, fun b h1 h2 => GlobalTheory.MemLoc.fundamental_exact l C b h1 h2,
      GlobalTheory.MemLoc.FundOnto.fundOnto l C, GlobalTheory.MemLoc.regular_of_tensorInj l C (h l C)⟩

theorem fontaineBcris : GlobalTheory.Published.FontaineBcris :=
  fontaineBcris_of_tensorInj _root_.GlobalTheory.MemLoc.TensorInj.tensorInj

end GlobalTheory.MemLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisHolds
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Published

theorem FontaineBcris.fund_holds (l : ℕ) [Fact l.Prime] (C : Core l) : C.Fund := by
  intro b h1 h2
  exact GlobalTheory.MemLoc.fundamental_exact l C b h1 h2

theorem FontaineBcris_holds : FontaineBcris :=
  FontaineBcris.of_rest fun l _ C =>
    ⟨_root_.GlobalTheory.MemLoc.TensorInj.tensorInj l C, FontaineBcris.fund_holds l C, GlobalTheory.MemLoc.FundOnto.fundOnto l C,
      _root_.GlobalTheory.MemLoc.regular_of_tensorInj l C (_root_.GlobalTheory.MemLoc.TensorInj.tensorInj l C)⟩

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemPPSetCongrStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ F ∈ PPSet t K e, frob2 φ₂ F ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, frob2 φ₂ F = F ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.FrobPP.frob_mem_PPSet_congr | exact GlobalTheory.CrysPrism.FrobPP.frob_mem_PPSet_congr | (intros; apply GlobalTheory.CrysPrism.FrobPP.frob_mem_PPSet_congr <;> assumption)
end

