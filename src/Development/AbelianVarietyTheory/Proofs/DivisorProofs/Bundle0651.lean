module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0628
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaPhiBranchOperator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomAgreeLocusClosedSubscheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem agreeLocus_factors_closedSubscheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) :=
  GlobalTheory.EndLoc.eqLocus_isClosedImmersion

end GlobalTheory.EndLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionCongrEqTransposeMul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CmpB

theorem blk_transpose {R : Type} [CommRing R] (d k : ℕ) (u v : R) :
    (blk d k u v).transpose = blk d k u v := Matrix.diagonal_transpose _

theorem tau_dvd_entry {R : Type} [CommRing R] (t : R) {m n h : Type} [Fintype n]
    (A : Matrix m n R) (Y : Matrix n h R) (hA : ∀ i j, t ∣ A i j) (i : m) (j : h) :
    t ∣ (A * Y) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (hA i l) _

theorem comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y Z : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U' → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z → (∀ i m, F.τ ∣ Z i m - Y i m) → Z = X.transpose * Y := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U U' X Y Z hU' hn1 hn2 hX hX1 hY hZ hZY
  set P := blk d k (p : F.B) 1 with hP

  have hT : P * U'.transpose * X.transpose = (X.map F.σ).transpose * P * U.transpose := by
    have := congrArg Matrix.transpose hX
    simp only [Matrix.transpose_mul, hP, blk_transpose] at this
    simpa only [Matrix.mul_assoc] using this
  have hΔ : (Z - X.transpose * Y).map F.σ = P * U'.transpose * (Z - X.transpose * Y) := by
    have e1 : (X.transpose * Y).map F.σ = P * U'.transpose * (X.transpose * Y) := by
      rw [Matrix.map_mul, Matrix.transpose_map, hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← hT, Matrix.mul_assoc (P * U'.transpose)]
    rw [Matrix.map_sub _ (map_sub F.σ), hZ, e1, Matrix.mul_sub]
  have hdiv : ∀ i m, F.τ ∣ (Z - X.transpose * Y) i m := by
    intro i m
    have e : Z - X.transpose * Y = (Z - Y) - (X.transpose - 1) * Y := by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, Matrix.sub_apply]
    refine dvd_sub (by simpa using hZY i m) (tau_dvd_entry _ _ _ (fun a b => ?_) i m)
    have h1 : (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) a b = (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) b a := by
      simp only [Matrix.one_apply, eq_comm]
    rw [Matrix.sub_apply, Matrix.transpose_apply, h1]
    exact hX1 b a
  have := (_root_.GlobalTheory.TauUniq.eq_zero_of_tau_dvd p C v O hv ε hε F d k h U' hU' hn1 hn2).1 _ hΔ hdiv
  exact (sub_eq_zero.1 this)

end GlobalTheory.CmpB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionMulCongrGmTranspose
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CmpG.comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (u l : F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B) (W : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → F.τ ∣ u - 1 → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → F.σ l = u * l → F.τ ∣ l - 1 → U * blk d k (p : F.B) 1 * Gm.transpose.map F.σ = (p : F.B) • Gm.transpose → U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W → (∀ i m, F.τ ∣ W i m - Gm m i) → X * W = l • Gm.transpose := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U U' X u l Gm W hU hN1 hN2 hu hX hXc hl hlc hG hW hWc
  classical
  haveI := ReciprocityTheory.PGsh.Ainf.O_local O hv
  obtain ⟨c, hc⟩ := hu
  have hue : u = 1 + F.τ * c := by rw [← hc]; ring
  set w : F.B := 1 - F.τ * c with hwdef
  have hwu : w * u = 1 := by rw [hue, hwdef]; linear_combination (-(c * c)) * F.τ_sq
  have hτ0 : F.θ F.τ = 0 := GlobalTheory.WinLift.theta_tau F hv hε
  have hθu : F.θ u = 1 := by rw [hue, map_add (f := _), map_one, map_mul, hτ0, zero_mul, add_zero]
  have hθw : F.θ w = 1 := by rw [hwdef, map_sub, map_one, map_mul, hτ0, zero_mul, sub_zero]
  have hwU : IsUnit w := ⟨⟨w, u, hwu, by rw [mul_comm]; exact hwu⟩, rfl⟩
  set P := blk d k (p : F.B) 1 with hP
  set D : Matrix (Fin d ⊕ Fin k) (Fin h) F.B := X * W - l • Gm.transpose with hDdef
  have hsm : (l • Gm.transpose).map F.σ = F.σ l • Gm.transpose.map F.σ :=
    Matrix.ext fun i j => by simp
  have hsub : D.map F.σ = (X * W).map F.σ - (l • Gm.transpose).map F.σ :=
    by rw [hDdef]; exact Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hD : U * P * D.map F.σ = ((p : F.B) * u) • D := by
    rw [hsub, Matrix.map_mul, hsm, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← hX,
      Matrix.mul_assoc, hW, hG, hl, Matrix.mul_smul, smul_smul, hDdef, smul_sub, smul_smul]
    congr 1
    rw [show u * l * (p : F.B) = p * u * l by ring]
  set U₁ := w • U with hU₁
  have hD1 : U₁ * P * D.map F.σ = (p : F.B) • D := by
    rw [hU₁, Matrix.smul_mul, Matrix.smul_mul, hD, smul_smul,
      show w * ((p : F.B) * u) = p by linear_combination (p : F.B) * hwu]
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).1 hU
  have hU₁u : IsUnit U₁ := by
    rw [Matrix.isUnit_iff_isUnit_det, hU₁, Matrix.det_smul]
    exact (hwU.pow _).mul hUdet
  have hinv : U₁.transpose⁻¹ = u • U.transpose⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hU₁, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hwu, one_smul,
      Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hUdet)]
  have hp : ¬IsUnit (p : O) := Fact.out
  have hN1' : IsNil F.θ F.σ (U₁.transpose⁻¹ * blk d k 1 (p : F.B)) := by
    refine GlobalTheory.WinLift.isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN1
    rw [hinv, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hθu, one_mul]
  have hN2' : IsNil F.θ F.σ (U₁ * P) := by
    refine GlobalTheory.WinLift.isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN2
    rw [hU₁, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hθw, one_mul]
  have key := (GlobalTheory.TauUniq.eq_zero_of_tau_dvd p C v O hv ε hε F d k h U₁ hU₁u hN1' hN2').2
  have hdec : D = (X - 1) * W + (W - Gm.transpose) - (l - 1) • Gm.transpose := by
    rw [hDdef, Matrix.sub_mul, Matrix.one_mul, sub_smul, one_smul]; abel
  have hτD : ∀ i m, F.τ ∣ D i m := by
    intro i m
    rw [hdec, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply]
    refine dvd_sub (dvd_add (Finset.dvd_sum fun j _ => ?_) (hWc i m)) (Dvd.dvd.mul_right hlc _)
    exact Dvd.dvd.mul_right (hXc i j) _
  have hD0 : D = 0 := by
    refine Matrix.ext fun i m => ?_
    have hcol := key (fun i => D i m) (funext fun i => by
      have := congrArg (fun M => M i m) hD1
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this) (fun i => hτD i m)
    exact congrFun hcol i
  exact sub_eq_zero.1 hD0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderiv
section
open Filter Topology

namespace GlobalTheory

open Filter Topology in
private lemma iteratedFDeriv_slice_eq_compContinuousLinearMap_inl {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (H : E × F → ℂ) {w : F}
    (hH : AnalyticAt ℂ H (0, w)) (k : ℕ) :
    iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 =
      (iteratedFDeriv ℂ k H (0, w)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl ℂ E F) := by
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  set s : Set (E × F) := (fun q ↦ q + (0, w)) ⁻¹' U with hs
  have hso : IsOpen s := hUo.preimage (continuous_id.add continuous_const)
  have h0s : (0 : E × F) ∈ s := by simpa [hs] using hwU
  have hf : AnalyticOnNhd ℂ (fun q : E × F ↦ H (q + (0, w))) s := fun q hq ↦
    (hU _ hq).comp (f := fun q : E × F ↦ q + (0, w)) (analyticAt_id.add analyticAt_const)
  have hslice : (fun z : E ↦ H (z, w)) =
      (fun q : E × F ↦ H (q + (0, w))) ∘ ContinuousLinearMap.inl ℂ E F := by
    ext z; simp
  have hpre : IsOpen (ContinuousLinearMap.inl ℂ E F ⁻¹' s) :=
    hso.preimage (ContinuousLinearMap.continuous _)
  have h0s' : ContinuousLinearMap.inl ℂ E F 0 ∈ s := by rw [map_zero]; exact h0s
  have h0pre : (0 : E) ∈ ContinuousLinearMap.inl ℂ E F ⁻¹' s := h0s'
  rw [hslice, ← iteratedFDerivWithin_of_isOpen k hpre h0pre,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right _ (hf.contDiffOn (n := k) hso.uniqueDiffOn)
      hso.uniqueDiffOn hpre.uniqueDiffOn h0s' le_rfl,
    iteratedFDerivWithin_of_isOpen k hso h0s', iteratedFDeriv_comp_add_right]
  simp

open Filter Topology in
private lemma fin_snoc_eq_cons_comp_finRotate {X : Type} {k : ℕ} (u : Fin k → X) (a : X) :
    (Fin.snoc u a : Fin (k + 1) → X) = Fin.cons a u ∘ finRotate (k + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp
  · simp


open Filter Topology in
theorem _root_.GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  intro E F _ _ _ _ _ _ H w₀ k v hH
  set u : Fin k → E × F := fun i ↦ (v i, 0) with hu
  have hev : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ H (0, w) :=
    ((continuous_const.prodMk continuous_id).tendsto w₀).eventually hH.eventually_analyticAt
  have heq : (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) =ᶠ[𝓝 w₀]
      fun w ↦ iteratedFDeriv ℂ k H (0, w) u :=
    hev.mono fun w hw ↦ by dsimp only; rw [iteratedFDeriv_slice_eq_compContinuousLinearMap_inl H hw k]; rfl
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  have hiter : AnalyticAt ℂ (iteratedFDeriv ℂ k H) (0, w₀) :=
    (AnalyticOnNhd.iteratedFDeriv_of_isOpen hU hUo k) _ hwU
  have hA : AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k H (0, w) u) w₀ :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).analyticAt _).comp
      (hiter.comp (f := fun w : F ↦ ((0 : E), w)) (analyticAt_const.prod analyticAt_id))
  refine ⟨hA.congr heq.symm, fun e ↦ ?_⟩
  have hD : HasFDerivAt (fun w ↦ iteratedFDeriv ℂ k H (0, w) u)
      ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).comp
        ((fderiv ℂ (iteratedFDeriv ℂ k H) (0, w₀)).comp (ContinuousLinearMap.inr ℂ E F))) w₀ :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).hasFDerivAt.comp w₀
      (hiter.differentiableAt.hasFDerivAt.comp w₀ (hasFDerivAt_prodMk_right (0 : E) w₀))
  have hG : AnalyticAt ℂ (fun y ↦ fderiv ℂ H y (0, e)) (0, w₀) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)).analyticAt _).comp hH.fderiv
  rw [heq.fderiv_eq, hD.fderiv, iteratedFDeriv_slice_eq_compContinuousLinearMap_inl _ hG k]
  have hcomp : (fun y ↦ fderiv ℂ H y (0, e)) =
      (ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)) ∘ fderiv ℂ H := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ (hH.fderiv.contDiffAt (n := k)) le_rfl]
  have hperm := (hH.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm (Fin.cons ((0 : E), e) u)
    (finRotate (k + 1))
  rw [← fin_snoc_eq_cons_comp_finRotate, iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_succ_apply_left] at hperm
  simpa [u] using hperm.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck

noncomputable section

namespace GlobalTheory.BrCompare

def rE (K : Type) [Field K] (n m : ℕ) (i j : Fin n) : Module.End K (MvPolynomial (Fin (n + 1) × Fin m) K) :=
  rowE K (n + 1) m i.castSucc j.castSucc

def rCap (K : Type) [Field K] (n m : ℕ) (u : ℤ) : Module.End K (MvPolynomial (Fin (n + 1) × Fin m) K) :=
  capDet (rE K n m) u

def lamN {n : ℕ} (lam : DomWeight (n + 1)) : Fin n → ℕ := fun i => lam.natW i.castSucc

def incl (K : Type) [Field K] (n : ℕ) :
    MvPolynomial (Fin (n + 1) × Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1) × Fin (n + 1)) K :=
  rename (Prod.map id Fin.castSucc)

def bfact {n : ℕ} (b : Fin n → ℕ) : ℕ := ∏ s, (b s).factorial

def coefOne (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ) (x : MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :
    MvPolynomial (Fin n × Fin n) K :=
  rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)
    (Formalism.L2.Col.Br.coefLast (rfl : n + 1 = n + 1) (fun _ : Unit => b)
      (rename (fun v : Fin (n + 1) × Fin (n + 1) => (((), v) : Unit × Fin (n + 1) × Fin (n + 1))) x))

def zList {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) : List ℤ :=
  (List.ofFn fun i : Fin n => (((GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.rangeSet lam sg i).erase (sg.w i)).toList).map fun v =>
    v - lam.w (Fin.last n) - (i.val : ℤ)).flatten

section Basic

variable {K : Type} [Field K]

theorem fockB_symm {σ : Type} (f g : MvPolynomial σ K) : fockB f g = fockB g f :=
  @fockSHerm K _ starRingOfComm _ g f

theorem fockB_X_mul {σ : Type} (v : σ) (f g : MvPolynomial σ K) : fockB (X v * f) g = fockB f (pderiv v g) := by
  classical
  exact @fockL_X_pderiv K _ starRingOfComm σ _ v f g

theorem fockB_rowE {r m : ℕ} (a b : Fin r) (f g : MvPolynomial (Fin r × Fin m) K) :
    fockB (rowE K r m a b f) g = fockB f (rowE K r m b a g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowE_apply, rowE_apply, ← fockBL_apply, ← fockBL_apply, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [fockBL_apply, fockBL_apply, fockB_X_mul, fockB_symm f, fockB_X_mul, fockB_symm]

theorem rE_rel (n m : ℕ) (i j k l : Fin n) :
    rE K n m i j * rE K n m k l - rE K n m k l * rE K n m i j =
      (if j = k then rE K n m i l else 0) - (if i = l then rE K n m k j else 0) := by
  have h := glRel_rowE K (n + 1) m i.castSucc j.castSucc k.castSucc l.castSucc
  simp only [Fin.castSucc_inj] at h
  simp only [rE, h, eq_comm (a := l)]

theorem end_two [CharZero K] {M : Type} [AddCommGroup M] [Module K M] (x : Module.End K M) (h : x + x = 0) : x = 0 := by
  rw [← two_smul K x] at h
  exact (smul_eq_zero.1 h).resolve_left two_ne_zero

theorem rE_comm_rCap [CharZero K] (n m : ℕ) (u : ℤ) (k l : Fin n) : Commute (rE K n m k l) (rCap K n m u) :=
  capDet_central _ u (rE_rel n m) end_two k l

theorem rCap_comm [CharZero K] (n m : ℕ) (u v : ℤ) : Commute (rCap K n m u) (rCap K n m v) :=
  capDet_commute_of _ v _ fun i j => (rE_comm_rCap n m u i j).symm

theorem rowE_mem {r m : ℕ} {ν : Fin m → ℕ} (a b : Fin r) {f : MvPolynomial (Fin r × Fin m) K}
    (hf : f ∈ dualWeyl K r m ν) : rowE K r m a b f ∈ dualWeyl K r m ν := by
  rw [(rowE_eq_rowDiv K r m a b f).1]
  exact rowDivStable K r m ν a b 1 f hf

theorem capDet_intertwine {M M' : Type} [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M'] {n : ℕ}
    (E : Fin n → Fin n → Module.End K M) (E' : Fin n → Fin n → Module.End K M') (φ : M →ₗ[K] M')
    (h : ∀ i j x, E' i j (φ x) = φ (E i j x)) (u : ℤ) (x : M) : capDet E' u (φ x) = φ (capDet E u x) := by
  have h1 : ∀ (k a i : Fin n) x, bmF E' u k a i (φ x) = φ (bmF E u k a i x) := by
    intro k a i x
    unfold bmF
    split_ifs
    · simp only [LinearMap.sub_apply, Module.End.intCast_apply, h, map_sub, map_zsmul]
    · simp [h]
  have h2 : ∀ (l : List (Fin n)) (α β : Fin n → Fin n) x, (l.map fun k => bmF E' u k (α k) (β k)).prod (φ x) =
      φ ((l.map fun k => bmF E u k (α k) (β k)).prod x) := by
    intro l α β x
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [capDet, bmPi, bmM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, List.ofFn_eq_map, h2]

theorem capDet_mem {M : Type} [AddCommGroup M] [Module K M] {n : ℕ} (E : Fin n → Fin n → Module.End K M)
    (W : Submodule K M) (h : ∀ i j, ∀ x ∈ W, E i j x ∈ W) (u : ℤ) {x : M} (hx : x ∈ W) : capDet E u x ∈ W := by
  have := capDet_intertwine (fun i j => (E i j).restrict (h i j)) E W.subtype (fun _ _ _ => rfl) u ⟨x, hx⟩
  rw [show x = W.subtype ⟨x, hx⟩ from rfl, this]
  exact Subtype.property _

theorem rE_emb (n : ℕ) (i j : Fin n) (f : MvPolynomial (Fin n × Fin n) K) :
    rE K n n i j (emb K n f) = emb K n (rowE K n n i j f) := by
  unfold rE
  induction f using MvPolynomial.induction_on with
  | C a => simp [emb, rowE_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    rw [map_mul, rowE_mul, rowE_mul, hp, map_add (f := _), map_mul, map_mul, bmF_emb_X, rowE_X, rowE_X]
    by_cases h : j = a <;> simp [h, bmF_emb_X]

theorem rE_zmon (n : ℕ) (i j : Fin n) (b : Fin n → ℕ) : rE K n n i j (zmon K n b) = 0 := by
  unfold rE zmon
  refine Finset.prod_induction _ (fun P => rowE K (n + 1) n i.castSucc j.castSucc P = 0) ?_ ?_ ?_
  · intro a b ha hb
    rw [rowE_mul, ha, hb]; simp
  · exact rowE_C K _ _ _ _ 1
  · intro s _
    induction b s with
    | zero => exact rowE_C K _ _ _ _ 1
    | succ k ih => rw [pow_succ, rowE_mul, ih, rowE_X, if_neg (Fin.castSucc_lt_last j).ne]; simp

theorem rE_lead (n : ℕ) (i j : Fin n) (b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    rE K n n i j (zmon K n b * emb K n f) = zmon K n b * emb K n (rowE K n n i j f) := by
  have h1 := rE_zmon (K := K) n i j b
  have h2 := rE_emb n i j f
  unfold rE at *
  rw [rowE_mul, h1, h2, zero_mul, zero_add]

theorem rCap_lead (n : ℕ) (u : ℤ) (b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    rCap K n n u (zmon K n b * emb K n f) = zmon K n b * emb K n (capDet (fun i j => rowE K n n i j) u f) :=
  capDet_intertwine (fun i j => rowE K n n i j) (rE K n n)
    (LinearMap.mulLeft K (zmon K n b) ∘ₗ (emb K n).toLinearMap) (fun i j x => rE_lead n i j b x) u f

theorem rowE_eq_deriv {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) K) :
    rowE K r m a b f = mkDerivation K (fun v : Fin r × Fin m =>
      if v.1 = b then (X (a, v.2) : MvPolynomial (Fin r × Fin m) K) else 0) f := by
  induction f using MvPolynomial.induction_on with
  | C c => rw [rowE_C, derivation_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    obtain ⟨c, s⟩ := v
    rw [rowE_mul, hp, Derivation.leibniz, mkDerivation_X, rowE_X]
    simp only [smul_eq_mul, eq_comm (a := b)]
    ring

theorem comp_comm_rE {B : Type} [AddCommMonoid B] [IsRightCancelAdd B] (n m : ℕ) (w : Fin (n + 1) × Fin m → B)
    (hw : ∀ (a a' : Fin n) s, w (a.castSucc, s) = w (a'.castSucc, s)) (β : B) (i j : Fin n) :
    Commute (weightedHomogeneousComponent w β : Module.End K (MvPolynomial (Fin (n + 1) × Fin m) K)) (rE K n m i j) := by
  refine commute_weightedComponent_of_monomial w _ (fun μ => ?_) β
  have h := bm_deriv_monomial_WH (R := K) w 0 (fun v : Fin (n + 1) × Fin m =>
      if v.1 = j.castSucc then (X (i.castSucc, v.2) : MvPolynomial (Fin (n + 1) × Fin m) K) else 0)
    (fun v => by
      split_ifs with hv
      · obtain ⟨a, s⟩ := v
        obtain rfl : a = j.castSucc := hv
        rw [add_zero, hw j i]
        exact isWeightedHomogeneous_X K w _
      · exact isWeightedHomogeneous_zero K w _) μ
  rwa [add_zero, ← rowE_eq_deriv] at h

theorem zcomp_comm_rE (n : ℕ) (β : Fin n → ℤ) (i j : Fin n) : Commute (zcomp K n β) (rE K n n i j) :=
  comp_comm_rE n n (zW n) (fun a a' s => by rw [bmF_zW_castSucc, bmF_zW_castSucc]) β i j

theorem lastcomp_comm_rE (n d : ℕ) (i j : Fin n) :
    Commute (weightedHomogeneousComponent (lastW n) d : Module.End K (BP K n)) (rE K n n i j) :=
  comp_comm_rE n n (lastW n) (fun a a' s => by rw [bmF_lastW_castSucc, bmF_lastW_castSucc]) d i j

theorem glOperatorFirstRows_mem_bmW {n d : ℕ} {lam : Fin n → ℕ} (i j : Fin n) {G : BP K n} (hG : G ∈ bmW K n lam d) :
    rE K n n i j G ∈ bmW K n lam d := by
  rw [bmK_mem_alt] at hG ⊢
  exact ⟨rowE_mem _ _ hG.1, bm_isWH_of_comm (lastW n) d _ (lastcomp_comm_rE n d i j) G hG.2⟩

theorem capelliDeterminantFirstRows_mem_bmW {n d : ℕ} {lam : Fin n → ℕ} (u : ℤ) {G : BP K n} (hG : G ∈ bmW K n lam d) :
    rCap K n n u G ∈ bmW K n lam d :=
  capDet_mem _ _ (fun i j _ hx => glOperatorFirstRows_mem_bmW i j hx) u hG

theorem zcomp_comm_rCap (n : ℕ) (β : Fin n → ℤ) (u : ℤ) : Commute (zcomp K n β) (rCap K n n u) :=
  capDet_commute_of _ u _ (zcomp_comm_rE n β)

theorem coeff_rowE_self {r m : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin m) K) (μ : Fin r × Fin m →₀ ℕ) :
    AddMonoidAlgebra.coeff (rowE K r m a a f) μ = (rowDeg μ a : K) * AddMonoidAlgebra.coeff f μ := by
  classical
  rw [rowE_apply, coeff_sum, rowDeg, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_X_mul']
  split_ifs with h
  · have h1 : Finsupp.single (a, s) 1 ≤ μ := by
      rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
    rw [coeff_pderiv, tsub_add_cancel_of_le h1, mul_comm]
    congr 1
    have h2 : 1 ≤ μ (a, s) := Finsupp.single_le_iff.1 h1
    simp [Nat.cast_sub h2]
  · rw [Finsupp.notMem_support_iff.1 h]; simp

theorem rowWeight_iff [CharZero K] {r m : ℕ} (ρ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin m) K) :
    IsWeightedHomogeneous (rowW r m) f ρ ↔ ∀ a, rowE K r m a a f = (ρ a : K) • f := by
  constructor
  · intro h a
    ext μ
    rw [coeff_rowE_self, coeff_smul, smul_eq_mul]
    by_cases h0 : AddMonoidAlgebra.coeff f μ = 0
    · simp [h0]
    · rw [← bm_weight_rowW, h h0]
  · intro h μ h0
    funext a
    have := congrArg (AddMonoidAlgebra.coeff · μ) (h a)
    rw [coeff_rowE_self, coeff_smul, smul_eq_mul] at this
    rw [bm_weight_rowW]
    exact_mod_cast mul_right_cancel₀ h0 this

theorem fockB_eq_zero {σ : Type} (f g : MvPolynomial σ K) (h : ∀ μ, AddMonoidAlgebra.coeff f μ ≠ 0 → AddMonoidAlgebra.coeff g μ = 0) : fockB f g = 0 :=
  Finset.sum_eq_zero fun μ hμ => by rw [h μ (mem_support_iff.1 hμ)]; simp

theorem fockB_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ K) :
    fockB (rename e f) (rename e g) = fockB f g := by
  classical
  induction f using MvPolynomial.induction_on generalizing g with
  | C a =>
    have h1 : ∀ {σ : Type} (g : MvPolynomial σ K), fockB (C a) g = a * constantCoeff g :=
      fun g => @fockL_C_left K _ starRingOfComm _ a g
    rw [rename_C, h1, h1, constantCoeff_rename]
  | add p q hp hq => simp only [← fockBL_apply, map_add (f := _), LinearMap.add_apply] at *; rw [hp, hq]
  | mul_X p v hp => rw [mul_comm, map_mul, rename_X, fockB_X_mul, fockB_X_mul, pderiv_rename he, hp]

theorem fockB_incl (n : ℕ) (f g : BP K n) : fockB (incl K n f) (incl K n g) = fockB f g :=
  fockB_rename (Function.injective_id.prodMap (Fin.castSucc_injective n)) f g

end Basic

end GlobalTheory.BrCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartEvNmulPowSelf
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem chart_ev_nmul_pow_self : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (i : Fin d), c.ev n (nmul c.μ (p ^ n) i) = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n i
  rw [GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c n (p ^ n) i, G.mulBy_pow_self n (c.x n i), c.aug n i, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondInjectiveGeomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clopenCond_injective_geom_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom) | (exact GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom) | (intros; apply GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom <;> assumption)
end

