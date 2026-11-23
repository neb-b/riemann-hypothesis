module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorsInvertibleBasisOverOEStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitVectors_invertible_basis_over_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)), (∀ n, ∃ R' : Matrix (Fin (d' n)) (Fin d) (WCb l), (∀ i j, R' i j ∈ bk.OE) ∧ ∀ i j, (l : WCb l) ^ n ∣ (R n * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ n i j, R n i j ∈ bk.OE) → ∃ V V' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, V i j ∈ bk.OE) ∧ (∀ i j, V' i j ∈ bk.OE) ∧ V * V' = 1 ∧ ∀ j k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ ((fun i => V i j) - R k *ᵥ fun a => bk.evW (s' a)) i := by
  first | (exact @GlobalTheory.LimVec.invertible_basis) | (exact GlobalTheory.LimVec.invertible_basis) | (intros; apply GlobalTheory.LimVec.invertible_basis  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletionFiltrationIffDeRhamFiltration
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR.CmpFil

theorem amulG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ∀ o o', ι' (o * o') = ι' o * ι' o') (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (x y : OD l O) (v : V ⊗[ℚ_[l]] R) : A (x * y) v = A x (A y v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add (f := _), hv, hw]
  | tmul v c =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [add_mul, map_add (f := _), AddMonoidHom.add_apply, hx, hx']
    | tmul o b =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
      | add y y' hy hy' => simp only [mul_add, map_add (f := _), AddMonoidHom.add_apply, hy, hy']
      | tmul o' b' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hA, hA, hA, map_mul, mul_assoc, h1, mul_smul]

theorem aoneG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ι' 1 = 1) (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (v : V ⊗[ℚ_[l]] R) : A 1 v = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add (f := _), hv, hw]
  | tmul v c => rw [Algebra.TensorProduct.one_def, hA, map_one, one_mul, h1, one_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem amulL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (x y : OD l ↥(OL LL)) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A (x * y) v = A x (A y v) :=
  amulG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) (fun _ _ => rfl) (GlobalTheory.BKGal.JumpDR.cD Td) A hA x y v

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem aoneL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A 1 v = v :=
  aoneG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) rfl (GlobalTheory.BKGal.JumpDR.cD Td) A hA v

set_option maxHeartbeats 1000000 in
theorem coreG {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {W : Type} [AddCommGroup W] (A : OD l O →+ (W →+ W)) (Fil : ℤ → W → Prop)
    (amul : ∀ x y v, A (x * y) v = A x (A y v)) (aone : ∀ v, A 1 v = v)
    (hbij : Function.Bijective (A (ϖ.iD t K (fun _ => Ehat O K l e))))
    (hS : ∀ (y : W) (j : ℤ), Fil j y ↔ Fil (j + 1) (A (ϖ.iD t K (fun _ => Ehat O K l e)) y))
    (gB : ι → W) (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e)
    (hy : ∀ τ j i, algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i))
    (f : ι → W) (hf1 : ∀ i, A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i) = ∑ j, A (ϖ.iD t K (fun τ => y τ j i)) (gB j))
    (hspan : ∀ v, Fil 0 v ↔ ∃ d : ι → OD l O, v = ∑ i, A (d i) (f i))
    (hind : ∀ d : ι → OD l O, ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0)
    {n : ℕ} (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (g : Fin n → W)
    (hC : ∀ (s' : Fin n → ZMod a → Ahat O K l e) (c : ZMod a → ι → Ahat O K l e), (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD t K (s' k)) (g k) = ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j))
    (hE1 : ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i)
    (j : ℤ) :
    GlobalTheory.BKGal.JumpDR.InEhat O K l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ Fil j (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
  classical
  have hbijN : ∀ N : ℕ, Function.Bijective (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) := by
    intro N
    induction N with
    | zero =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ 0)) = id := funext fun v => by rw [pow_zero]; exact aone v
      rw [h0]; exact Function.bijective_id
    | succ N ih =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1))) = ⇑(A (ϖ.iD t K (fun _ => Ehat O K l e))) ∘ ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) :=
        funext fun v => by rw [pow_succ', amul]; rfl
      rw [h0]; exact hbij.comp ih
  have hSh : ∀ (N : ℕ) (y : W) (j : ℤ), Fil j y ↔ Fil (j + N) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by
    intro N
    induction N with
    | zero => intro y j; rw [pow_zero, aone, Nat.cast_zero, add_zero]
    | succ N ih =>
      intro y j
      have e1 : (j + ((N + 1 : ℕ) : ℤ)) = (j + N) + 1 := by push_cast; ring
      have e2 : A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1)) y = A (ϖ.iD t K (fun _ => Ehat O K l e)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by rw [pow_succ', amul]
      rw [e1, e2]
      exact (ih y j).trans (hS _ _)
  have Fb : ∀ (d : ι → OD l O) (kk : ℕ), Fil kk (∑ i, A (d i) (f i)) ↔ ∀ i, d i ∈ Ideal.span {(ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk} := by
    intro d kk
    constructor
    · intro hd
      obtain ⟨v', hv'⟩ := (hbijN kk).2 (∑ i, A (d i) (f i))
      have h0 : Fil 0 v' := (hSh kk v' 0).2 (by rw [hv', zero_add]; exact hd)
      obtain ⟨z, rfl⟩ := (hspan v').1 h0
      have h4 : ∑ i, A (d i - (ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk * z i) (f i) = 0 := by
        simp only [map_sub, AddMonoidHom.sub_apply, Finset.sum_sub_distrib, amul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, hv', sub_self]
      intro i
      have h5 := hind _ h4 i
      rw [sub_eq_zero] at h5
      rw [h5]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hd
      choose z hz using fun i => Ideal.mem_span_singleton'.1 (hd i)
      have h6 : ∑ i, A (d i) (f i) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk) (∑ i, A (z i) (f i)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hz i, mul_comm, amul]
      have h7 := (hSh kk _ 0).1 ((hspan _).2 ⟨z, rfl⟩)
      rw [zero_add] at h7
      rw [h6]; exact h7
  have key : ∀ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), (∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
      A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) (∑ k, A (ϖ.iD t K (s k)) (g k)) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i) := by
    intro N x hx
    let s' : Fin n → ZMod a → Ahat O K l e := fun k => (fun _ => Ehat O K l e) ^ (N + β) * s k
    let c : ZMod a → ι → Ahat O K l e := fun τ j => ∑ i, y τ j i * x τ i
    have hw : ∀ τ i, GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N + β) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i
      simp only [GlobalTheory.BKGal.JumpDR.hsum, s', Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, Finset.mul_sum, mul_assoc]
    have hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i := by
      intro τ j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [c, map_sum, map_mul, hy, hx, hw]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hC' := hC s' c hc
    have h1 : ∑ k, A (ϖ.iD t K (s' k)) (g k) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + β)) (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [s', map_mul, map_pow]
      rw [amul]
    have h2' : ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) := by
      have h3 : ∀ j, (fun τ => c τ j) = ∑ i, (fun τ => x τ i) * (fun τ => y τ j i) := by
        intro j; funext τ; simp only [c, Finset.sum_apply, Pi.mul_apply, mul_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [h3, map_sum, AddMonoidHom.finsetSum_apply, map_mul, amul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hf1 i, map_sum]
    rw [h1, h2'] at hC'
    have h3 : ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← amul, ← amul, mul_comm]
    rw [h3, pow_add, mul_comm, amul] at hC'
    exact (hbijN β).1 hC'
  constructor
  · rintro ⟨N, hN, hx⟩
    choose x' hx' using hx
    have hkj : (((j + N).toNat : ℕ) : ℤ) = j + N := Int.toNat_of_nonneg hN
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ (j + N).toNat * x' τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; rw [← map_pow]; exact hx' τ i
    have hK := key N x hxx
    have hmem : Fil (((j + N).toNat : ℕ) : ℤ) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      refine (Fb _ _).2 fun i => ?_
      have h8 : (fun τ => x τ i) = (fun _ => Ehat O K l e) ^ (j + N).toNat * fun τ => x' τ i := by
        funext τ; simp only [x, Pi.mul_apply, Pi.pow_apply]
      rw [h8, map_mul, map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [← hK, hkj] at hmem
    exact (hSh N _ j).2 hmem
  · intro hF
    obtain ⟨N₁, x₁, hx₁⟩ := hE1
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ j.natAbs * x₁ τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N₁ + j.natAbs) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; simp only [x, map_mul, map_pow, hx₁, pow_add]; ring
    have hK := key _ x hxx
    have hN : 0 ≤ j + ((N₁ + j.natAbs : ℕ) : ℤ) := by push_cast; have := neg_abs_le j; omega
    have hkj : (((j + ((N₁ + j.natAbs : ℕ) : ℤ)).toNat : ℕ) : ℤ) = j + ((N₁ + j.natAbs : ℕ) : ℤ) := Int.toNat_of_nonneg hN
    have h1 := (hSh (N₁ + j.natAbs) _ j).1 hF
    rw [hK, ← hkj] at h1
    have h2 := (Fb _ _).1 h1
    refine ⟨N₁ + j.natAbs, hN, fun τ i => ?_⟩
    obtain ⟨z, hz⟩ := PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ _ _ (h2 i)
    refine ⟨z τ, ?_⟩
    have h9 := congrFun hz τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h9
    rw [← h9, map_pow]
    exact hxx τ i

end GlobalTheory.BKGal.JumpDR.CmpFil

open GlobalTheory.BKGal.JumpDR.CmpFil in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.BKGal.JumpDR.inEhat_iff_filV : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (j : ℤ), GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j := by
  intro hFont l _ a e _ _ ϖ LL _ _ h2 ι _ _ P T I jB Pl AI Td hcmp X hX A hA n s m j
  obtain ⟨hbij, hS⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td A hA
  obtain ⟨β, y, hy⟩ := _root_.GlobalTheory.BK.coordE_mxInv l a e ϖ LL ι P
  obtain ⟨f, hf1, hspan, hind⟩ := GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus hFont l a e ϖ LL h2 ι P T I jB Pl AI Td hcmp X hX A hA β y hy
  exact coreG (thetaW a LL) ϖ P A (fun j y => y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j)
    (amulL A hA) (aoneL A hA) hbij hS (fun j => X (jB (Pi.single j 1))) β y hy f hf1 hspan hind s m
    (fun k => X (jB (toBcris (thetaW a LL) ϖ P (m k))))
    (fun s' c h => GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates hFont l a e ϖ LL h2 ι P T jB Pl AI Td X hX A hA n s' m c h)
    (_root_.GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow l a e ϖ LL ι P n s m) j
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariantStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_translate_invariant : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ Φ : G → ℂ, Per Γ Φ → ∀ y : G, avg Γ (fun x => Φ (x + y)) = avg Γ Φ := by
  first | exact @GlobalTheory.CuspGeneric.avg_add_right | exact GlobalTheory.CuspGeneric.avg_add_right | (intros; apply GlobalTheory.CuspGeneric.avg_add_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFrames
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.FrameDom

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma emb_cc' (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.cc]
  exact IsCMField.complexEmbedding_complexConj E τ x

lemma gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma gm_eq {r : ℕ} (G G' : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ v w, herm G (γ.mulVec v) (γ.mulVec w) = herm G' v w) :
    G' = γᵀ * G * γ.map cc := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.single_apply, map_one, map_zero,
    mul_one, one_mul, mul_zero, zero_mul, ite_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.mulVec, dotProduct, apply_ite] at hij
  rw [← hij]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    ReciprocityTheory.ChartRestriction.G.FD.cc]
  rw [Finset.sum_comm]

omit [NumberField E] [IsCMField E] in
lemma det_map_ne {r : ℕ} (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ).2 ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

lemma gram_mul {r : ℕ} (G G' : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ v w, herm G (γ.mulVec v) (γ.mulVec w) = herm G' v w) (τ : E →+* ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G (γ.map τ * M) = gram τ G' M := by
  have h1 : (γ.map τ * M).map (starRingEnd ℂ) = (γ.map cc).map τ * M.map (starRingEnd ℂ) := by
    rw [Matrix.map_mul]
    congr 1
    ext a b
    simp only [Matrix.map_apply, emb_cc']
  have h2 : (γᵀ * G * γ.map cc).map τ = (γ.map τ)ᵀ * G.map τ * (γ.map cc).map τ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [gram_eq, gram_eq, gm_eq G G' γ h, h2, h1, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem mem_dom_of_isometry :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E), X.p0 = X'.p0 → (∀ τ, τ ∈ X.Ψ ↔ τ ∈ X'.Ψ) → (∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E).mulVec v) ((γ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X'.Gm v w) → ∀ (x : Frame X'.Ψ r) (x' : Frame X.Ψ r), x ∈ X'.dom → (∀ (τ : E →+* ℂ) (h₂ : τ ∈ X'.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ X.dom := by
  intro E _ _ _ r X X' γ hp hΨ hh x x' hx hmat
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.dom, ReciprocityTheory.ChartRestriction.G.FD.GG, Set.mem_ofPred_eq] at hx ⊢
  intro τ
  have h₂ : τ.1 ∈ X'.Ψ := (hΨ τ.1).1 τ.2
  obtain ⟨hdet, hpos⟩ := hx ⟨τ.1, h₂⟩
  have hm := hmat τ.1 h₂ τ.2
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero (det_map_ne τ.1 γ) hdet
  · have hd : dmin X.Gm x' τ i = dmin X'.Gm x ⟨τ.1, h₂⟩ i := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.dmin]
      rw [hm, gram_mul X.Gm X'.Gm (γ : Matrix (Fin r) (Fin r) E) hh]
    rw [hd, hp]
    exact hpos i

end GlobalTheory.FrameDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisations
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.DesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D := by
  intro hC D hT i _ _ r ρ π dc lenRow e' cB hr hA hπ
  obtain ⟨_, _, hG3, _, _, _, _, _, _, _, _, _, _, hDec, _⟩ := hA
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hDec
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.Proof.AbsoluteIrreducibilitySpan.absIrr_of_span hpos _ _ (fun _ => 1) (fun g => by rw [one_smul]; rfl) hG3.2.2
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, _⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS⟩

end GlobalTheory.DesignFromSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OrthogonalDesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  intro hC D hN9 hT i k hk hHG r ρ hr π hπ hd _
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hd
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hirr := (hN9 i hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) hpos _
      fun W hW => hirr W fun g _ x hx => hW g x hx
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, hg⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS, hg.2 ⟨k, hk⟩⟩

end GlobalTheory.OrthogonalDesignFromSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAinfLatticeFreeOverBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturatedAinfLattice_free_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (T0 V V' : Matrix (Fin d) (Fin d) (WCb l)) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T0 → (∀ i j, V i j ∈ bk.OE) → (∀ i j, V' i j ∈ bk.OE) → V * V' = 1 → Y1.map (inclW l) = inclW l τ ^ N • (T0 * V) → ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Wm Wm' : Matrix (Fin d) (Fin d) (WCb l)), IsUnit (Y.map (inclW l)) ∧ (∀ i j, Wm i j ∈ bk.OE) ∧ (∀ i j, Wm' i j ∈ bk.OE) ∧ Wm * Wm' = 1 ∧ Y.map (inclW l) = inclW l τ ^ N • (T0 * Wm) ∧ ∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  first | (exact @GlobalTheory.BKLim.SatLat.main) | (exact GlobalTheory.BKLim.SatLat.main) | (intros; apply GlobalTheory.BKLim.SatLat.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedMatrixCongruenceLiftSequenceStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_matrix_congruence_lift_sequence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (tw.d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v)) → ∀ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (T : Matrix (Fin d) (Fin d) (WCb l)), Y.map (inclW l) = inclW l τ ^ N • T → (∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∀ n, ∃ m, n ≤ m ∧ ∃ (Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S) (Q : Matrix (Fin (tw.d' m)) (Fin d) (Ainf l)), (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi m) * (F m).T - T * Rn.map bk.evW) i j) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (Rn.map bk.ev * Q).map (inclW l) - inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j := by
  first | (exact @GlobalTheory.BKLim.limit_basis_link_mod) | (exact GlobalTheory.BKLim.limit_basis_link_mod) | (intros; apply GlobalTheory.BKLim.limit_basis_link_mod  <;> assumption)
end

