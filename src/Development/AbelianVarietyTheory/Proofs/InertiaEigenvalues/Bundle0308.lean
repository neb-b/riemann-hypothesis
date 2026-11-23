module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPiPowEllOfNearPi
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl
section Gen
variable {O A R : Type} [CommRing O] [CommRing A] [CommRing R] [Algebra O R] {n : ℕ}

theorem letφ_smul_letE (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (o : O) (i : ZMod n) :
    letφ φ₀ (o • letE i : LetA O n) = o • letE (i + 1) := by
  rw [map_smul]
  congr 1
  funext k
  change φ₀ (letE i (k - 1)) = letE (i + 1) k
  by_cases hk : k = i + 1
  · subst hk
    simp [letE]
  · have : k - 1 ≠ i := fun h => hk (by rw [← h]; ring)
    simp [letE, hk, this]

theorem near_one_split [NeZero n] {ι : A →+* R} {p : ℕ} (j : LetA O n →ₐ[O] R)
    (hj : ∀ a, ∃ b, j a = ι b) (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (φR : R → R)
    (hφj : ∀ b, φR (j b) = j (letφ φ₀ b))
    (hφ : ∀ x, Near ι p (j letπ) 1 x → Near ι p (j letπ) 1 (φR x))
    (hO : ∀ o : O, Near ι p (j letπ) 1 (algebraMap O R o) → ∃ o' : O, o = (p : O) * o')
    (a : LetA O n) (ha : Near ι p (j letπ) 1 (j a)) :
    ∃ a1 a2 : LetA O n, a = letπ * a1 + (p : LetA O n) * a2 := by
  obtain ⟨a', ha'⟩ : ∃ a' : LetA O n,
      a = letπ * a' + fun i => PowerSeries.C (PowerSeries.constantCoeff (a i)) :=
    ⟨fun i => PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (a i),
      funext fun i => PowerSeries.eq_X_mul_shift_add_const (a i)⟩
  set c : LetA O n := fun i => PowerSeries.C (PowerSeries.constantCoeff (a i)) with hc
  have h1 : Near ι p (j letπ) 1 (j c) := by
    obtain ⟨b, hb⟩ := hj a'
    have h2 : j c = j a - j letπ ^ 1 * ι b := by
      rw [pow_one, ← hb, ← map_mul, ← map_sub]
      congr 1
      exact eq_sub_of_add_eq' ha'.symm
    rw [h2]
    exact ha.sub (Near.pow_mul 1 b)
  have h3 : ∀ i, ∃ o' : O, PowerSeries.constantCoeff (a i) = (p : O) * o' := by
    intro i
    set o := PowerSeries.constantCoeff (a i) with ho
    have h4 : Near ι p (j letπ) 1 (j (o • letE i)) := by
      obtain ⟨b, hb⟩ := hj (letE i)
      have h5 : (o • letE i : LetA O n) = letE i * c := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp [letE, hc, ho, PowerSeries.smul_eq_C_mul]
        · simp [letE, hk]
      rw [h5, map_mul, hb]
      exact h1.mul_ι b
    have h6 : ∀ k : ℕ, Near ι p (j letπ) 1 (j (o • letE (i + (k : ZMod n)))) := by
      intro k
      induction k with
      | zero => simpa using h4
      | succ k ih =>
        have := hφ _ ih
        rwa [hφj, letφ_smul_letE, add_assoc, ← Nat.cast_succ] at this
    have h7 : ∀ k : ZMod n, Near ι p (j letπ) 1 (j (o • letE k)) := by
      intro k
      have := h6 (k - i).val
      rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this
    apply hO
    have h8 : ∑ k : ZMod n, (letE k : LetA O n) = 1 := by
      funext k
      simp [letE, Finset.sum_apply, Pi.single_apply]
    have h9 : algebraMap O R o = ∑ k : ZMod n, j (o • letE k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← Finset.smul_sum, h8, map_smul, map_one, Algebra.algebraMap_eq_smul_one]
    rw [h9]
    exact Near.sum _ fun k _ => h7 k
  choose o' ho' using h3
  refine ⟨a', fun i => PowerSeries.C (o' i), ha'.trans ?_⟩
  congr 1
  funext i
  simp [hc, ho']

theorem near_split [NeZero n] {ι : A →+* R} {p : ℕ} {t : R} (j : LetA O n →ₐ[O] R)
    (hj : ∀ a, ∃ b, j a = ι b) (ht : j letπ = t) (hu : IsUnit t)
    (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (φR : R → R)
    (hφj : ∀ b, φR (j b) = j (letφ φ₀ b))
    (hφ : ∀ x, Near ι p t 1 x → Near ι p t 1 (φR x))
    (hO : ∀ o : O, Near ι p t 1 (algebraMap O R o) → ∃ o' : O, o = (p : O) * o')
    (m : ℕ) (a : LetA O n) (ha : Near ι p t m (j a)) :
    ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2 := by
  subst ht
  induction m with
  | zero => exact ⟨a, 0, by simp⟩
  | succ m ih =>
    obtain ⟨τ, hτ⟩ := hj letπ
    obtain ⟨a1, a2, h⟩ := ih (ha.mono hτ.symm (Nat.le_succ m))
    have h1 : j letπ ^ m * j a1 = j a - (p : R) * j a2 := by
      rw [h, map_add (f := _), map_mul, map_mul, map_pow, map_natCast, add_sub_cancel_right]
    have h2 : Near ι p (j letπ) (m + 1) (j letπ ^ m * j a1) := by
      rw [h1]
      exact ha.sub (Near.of_mul _ _)
    obtain ⟨b1, b2, hb⟩ := near_one_split j hj φ₀ φR hφj hφ hO a1 (h2.cancel hu)
    exact ⟨b1, letπ ^ m * b2 + a2, by rw [h, hb]; ring⟩
end Gen


set_option maxHeartbeats 1000000 in
theorem mem_pow_pi_of_nearPi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (m : ℕ) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), NearPi AI LL s m (inclR LL (E.tie.io a)) → ∃ a1 a2 : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a = letπ ^ m * a1 + (l : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) * a2 := by
  intro l _ P AI K s LL h W E m a ha
  obtain ⟨c1, -, c3, -⟩ := _root_.GlobalTheory.Decompl.ioE_compat l P AI K s LL h W E
  obtain ⟨-, -, p3, p4⟩ := GlobalTheory.DecomplFrob.frobenius_and_constants l P AI LL s
  have := (P.PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hu : IsUnit (piR AI LL s) := c3 ▸ W.EE_π.map E.tie.ioE
  refine near_split (ι := (inclR LL : RA LL →+* RW LL)) ((inclR LL).comp E.tie.io)
    (fun b => ⟨E.tie.io b, rfl⟩) ((E.tie.ioE_ext letπ).symm.trans c3) hu W.φ₀ (fun x => φRW LL x)
    (fun b => ?_) (p3 1) p4 m a ha
  have h1 := c1 (algebraMap _ W.EE b)
  exact (congrArg (fun x => φRW LL x) (E.tie.ioE_ext b)).symm.trans (h1.symm.trans
    ((congrArg (fun e => E.tie.ioE e) (W.φE_ext b)).trans (E.tie.ioE_ext _)))

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumns
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.ResR

open Matrix

variable {l : ℕ} [Fact l.Prime] {r : ℕ}

theorem resGL_mul_inv_map (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) :
    (resMat n ω).map f * (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map f = 1 := by
  have h : (resMat n ω) = ((resGL n ω hdet : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := rfl
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Units.mul_inv, map_one]

theorem resGL_inv_mul_map (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) :
    (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map f * (resMat n ω).map f = 1 := by
  have h : (resMat n ω) = ((resGL n ω hdet : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := rfl
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Units.inv_mul, map_one]

theorem resMat_mulVec_apply (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) (v : n × Fin r → S) (i : n) (m : Fin r) :
    ((resMat n ω).map f *ᵥ v) (i, m) = ∑ k, f (fr l m (ω k)) * v (i, k) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, resMat_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

theorem sum_fr_mul_eq_iter (hr : 0 < r) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hω : ∀ k, fr l r (ω k) = ω k)
    (a : n → P.R.B) (ha : ∀ i, P.φB^[r] (a i) = a i) (u : n × Fin r → P.R.B)
    (hu : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ u = fun j => P.φB^[j.2] (a j.1))
    (m : ℕ) (i : n) :
    ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m (ω k)) * u (i, k) = P.φB^[m] (a i) := by
  have h := congrFun hu (i, ⟨m % r, Nat.mod_lt _ hr⟩)
  rw [resMat_mulVec_apply] at h
  simp only [fr_mod (hω _)] at h
  rw [h]
  exact Function.IsPeriodicPt.iterate_mod_apply (ha i) m

theorem phi_fix_of_res (hr : 0 < r) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hω : ∀ k, fr l r (ω k) = ω k)
    (hdet : (frobMat ω).det ≠ 0)
    (a : n → P.R.B) (ha : ∀ i, P.φB^[r] (a i) = a i) (u : n × Fin r → P.R.B)
    (hu : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ u = fun j => P.φB^[j.2] (a j.1))
    (j : n × Fin r) : P.φB (u j) = u j := by
  set d : n × Fin r → P.R.B := fun j => P.φB (u j) - u j with hd
  have hz : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ d = 0 := by
    funext ⟨i, m⟩
    rw [resMat_mulVec_apply]
    have h1 := sum_fr_mul_eq_iter P hr ω hω a ha u hu (m + (r - 1)) i
    have h2 := sum_fr_mul_eq_iter P hr ω hω a ha u hu (m + (r - 1) + 1) i
    have e : m + (r - 1) + 1 = (m : ℕ) + r := by omega
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Function.iterate_succ_apply', ← h1, map_sum] at h2
    simp only [map_mul, phiB_algebraMap, ← fr_one, ← fr_add] at h2
    rw [show 1 + ((m : ℕ) + (r - 1)) = (m : ℕ) + r by omega, e] at h2
    simp only [fr_add, hω] at h2
    simp only [hd, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
    rw [h2, sub_self]
  have : d = 0 := by
    rw [← Matrix.one_mulVec d, ← resGL_inv_mul_map n ω hdet, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  exact sub_eq_zero.1 (congrFun this j)

def tzGL {N : Type} [Fintype N] [DecidableEq N] (e : N → ℤ) : GL N P.R.BdR where
  val := Matrix.diagonal fun j => tz P (e j)
  inv := Matrix.diagonal fun j => tz P (-e j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [← tz_add, tz_zero]
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp [← tz_add, tz_zero]

theorem iota_q_eq (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (U : Fin r → GL n P.R.BdR)
    (e : n × Fin r → ℤ) (A₀ : GL (n × Fin r) P.R.B) (W₀ : GL (n × Fin r) P.R.BdR)
    (hA : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) =
      (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR)) :
    ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.ιB *
      ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
        (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map P.ιB *
      (blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) =
      ((W₀⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
  set G : GL (n × Fin r) P.R.BdR := Units.map ((P.ιB : P.R.B →+* P.R.BdR).mapMatrix).toMonoidHom A₀ with hGdef
  set kp : GL (n × Fin r) P.R.BdR := Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+*
    Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom (resGL n ω hdet) with hkp
  have hG : G = kp⁻¹ * blockGL U * tzGL P e * W₀ := by
    apply Units.ext
    rw [hGdef]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Units.val_mul]
    rw [show (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (P.ιB : P.R.B →+* P.R.BdR) =
      (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) from rfl, hA]
    rfl
  have h1 : ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.ιB =
      ((G⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    rw [hGdef, ← map_inv, Units.coe_map]
    rfl
  have h2 : ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
        (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map P.ιB = ((kp⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    rw [hkp, ← map_inv, Units.coe_map, Matrix.map_map]
    ext i j
    simp [iota_kur]
  have h3 : (blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) =
      ((blockGL U * tzGL P e : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := rfl
  rw [h1, h2, Matrix.mul_assoc, h3, ← Units.val_mul, ← Units.val_mul, hG]
  congr 1
  group

theorem mem_span_colv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ), 0 < r → ∀ (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
    (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n]
    (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B),
    (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) →
    ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ →
    (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) →
    ∀ a : n → P.R.B, LatC P U x y a → a ∈ Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) := by
  intro l _ P r hr ω hω hdet n _ _ U x y A₀ hφ W₀ hW₀ hA a hLat
  obtain ⟨ha, hw⟩ := hLat
  choose w hw0 hwe using hw
  set pB : Matrix (n × Fin r) (n × Fin r) P.R.B := (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hpB
  set pI : Matrix (n × Fin r) (n × Fin r) P.R.B :=
    (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
      (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hpI
  set V : n × Fin r → P.R.B := fun j => P.φB^[j.2] (a j.1) with hV
  set u : n × Fin r → P.R.B := pI *ᵥ V with hu
  have hpu : pB *ᵥ u = V := by
    rw [hu, Matrix.mulVec_mulVec, hpB, hpI, resGL_mul_inv_map, Matrix.one_mulVec]
  set Ai : Matrix (n × Fin r) (n × Fin r) P.R.B := ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B)
    with hAi
  set q : n × Fin r → P.R.B := Ai *ᵥ u with hq

  have hAφ : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.φB = A₀ := Matrix.ext fun i j => hφ i j
  have hAiφ : Ai.map (P.φB : P.R.B →+* P.R.B) = Ai := by
    have h1 : Ai.map (P.φB : P.R.B →+* P.R.B) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) = 1 := by
      conv_lhs => rw [← hAφ]
      rw [show (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.φB =
          ((P.φB : P.R.B →+* P.R.B).mapMatrix (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B)) from rfl,
        show Ai.map (P.φB : P.R.B →+* P.R.B) = (P.φB : P.R.B →+* P.R.B).mapMatrix Ai from rfl, ← map_mul, hAi,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    calc Ai.map (P.φB : P.R.B →+* P.R.B)
        = Ai.map (P.φB : P.R.B →+* P.R.B) * ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) * Ai) := by
          rw [hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = Ai := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have huφ : ∀ j, P.φB (u j) = u j := phi_fix_of_res P hr ω hω hdet a ha u hpu
  have hqφ : ∀ c, P.φB (q c) = q c := by
    intro c
    have := RingHom.map_mulVec (P.φB : P.R.B →+* P.R.B) Ai u c
    rw [hAiφ] at this
    change P.φB (q c) = _ at this
    rw [this, hq]
    congr 1
    funext j
    exact huφ j

  set wt : n × Fin r → P.R.BdR := fun j => w j.2 j.1 with hwt
  have hιV : (fun j => P.ιB (V j)) = ((blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1)))) *ᵥ wt := by
    funext ⟨i, m⟩
    have h := congrFun (hwe m) i
    change P.ιB (P.φB^[m] (a i)) = _
    have hd : ∀ (v w : n × Fin r → P.R.BdR), Matrix.diagonal v *ᵥ w = fun j => v j * w j :=
      fun v w => funext (Matrix.mulVec_diagonal v w)
    have hd' : ∀ (v w : n → P.R.BdR), Matrix.diagonal v *ᵥ w = fun j => v j * w j :=
      fun v w => funext (Matrix.mulVec_diagonal v w)
    rw [show P.ιB (P.φB^[m] (a i)) = ev P m (a i) from rfl, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hd, hd']
    simp only [Matrix.mulVec, dotProduct, blockGL, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, hwt]
    rw [Finset.sum_comm, Finset.sum_eq_single m]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  have hιq : (fun c => P.ιB (q c)) = ((W₀⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *ᵥ wt := by
    funext c
    have e1 := RingHom.map_mulVec (P.ιB : P.R.B →+* P.R.BdR) Ai u c
    have e2 : (fun j => P.ιB (u j)) = (pI.map (P.ιB : P.R.B →+* P.R.BdR)) *ᵥ (fun j => P.ιB (V j)) := by
      funext j
      exact RingHom.map_mulVec (P.ιB : P.R.B →+* P.R.BdR) pI V j
    change P.ιB (q c) = _ at e1
    rw [e1]
    change (Ai.map P.ιB *ᵥ (fun j => P.ιB (u j))) c = _
    rw [e2, hιV, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [← iota_q_eq P ω hdet U (fun j : n × Fin r => eps x y (j.2, j.1)) A₀ W₀ hA]
    simp only [Matrix.mul_assoc]
    rfl
  have hqF : ∀ c, P.ιB (q c) ∈ Fil P 0 := by
    intro c
    rw [show P.ιB (q c) = (fun c => P.ιB (q c)) c from rfl, hιq]
    exact Fil_sum fun j _ => Fil_mul_left (hW₀.2 c j) (hw0 j.2 j.1)
  choose cq hcq using fun c => fund P (hqφ c) (hqF c)

  have hAq : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) *ᵥ q = u := by
    rw [hq, Matrix.mulVec_mulVec, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have haeq : a = ∑ c, cq c • colv P ω A₀ c := by
    funext i
    have h0 := sum_fr_mul_eq_iter P hr ω hω a ha u hpu 0 i
    simp only [fr_zero, Function.iterate_zero, id] at h0
    rw [← h0, ← hAq]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    simp only [Algebra.smul_def, hcq, colv, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [haeq]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))

end GlobalTheory.PMon.ResR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRing
section
namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc Filter Topology

theorem exists_padicInt_lim {l : ℕ} [Fact l.Prime] (z : ℕ → ℤ_[l])
    (h : ∀ n m, n ≤ m → ‖z n - z m‖ ≤ (l : ℝ) ^ (-(n : ℤ))) :
    ∃ y : ℤ_[l], ∀ n : ℕ, ∃ w : ℤ_[l], y - z n = (l : ℤ_[l]) ^ n * w := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Tendsto (fun n : ℕ => (l : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    simpa using this
  have hc : CauchySeq z :=
    cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by rw [dist_eq_norm]; exact h n m hnm) h0
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y, fun n => ?_⟩
  have h1 : ‖z n - y‖ ≤ (l : ℝ) ^ (-(n : ℤ)) :=
    le_of_tendsto ((tendsto_const_nhds.sub hy).norm)
      (eventually_atTop.2 ⟨n, fun m hm => h n m hm⟩)
  rw [norm_sub_rev, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at h1
  exact h1

theorem nearZ_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (hM : 1 ≤ M) (v : P.R.BdR)
    (hv : ∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) : NearZ P M v := by
  choose z hz using hv
  obtain ⟨y, hy⟩ := exists_padicInt_lim z (fun n m hnm => by
    have h1 := sub_mem (hz n) (Lat_anti AI hnm (hz m))
    rw [sub_sub_sub_cancel_right, ← map_sub] at h1
    exact GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM _ h1)
  refine ⟨y, GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI T M _ fun n => ?_⟩
  obtain ⟨w, hw⟩ := hy n
  have h2 := io_mem_Lat AI M n (algebraMap ℤ_[l] (Ainf l) w)
  rw [← map_natCast (algebraMap ℤ_[l] (Ainf l)), ← map_pow, ← map_mul, ← hw, io_zl AI T,
    PadicInt.coe_sub, map_sub] at h2
  have := add_mem h2 (hz n)
  rwa [sub_add_sub_cancel] at this

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntRingHomContinuousOfPadicCoeff
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory

theorem padicInt_ringHom_continuous_of_padicCoeff : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → ∀ φ : ℤ_[p] →+* O, Continuous φ := by
  intro p _ O _ _ _ _ hO φ
  haveI := hO.ring
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hO.adic).2 s hs
  have hball : Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) ∈ nhds (0 : ℤ_[p]) := by
    apply Metric.closedBall_mem_nhds
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  refine Filter.mem_map.mpr (Filter.mem_of_superset hball ?_)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow] at hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  apply hn
  show φ (a * (p : ℤ_[p]) ^ n) ∈ ((IsLocalRing.maximalIdeal O) ^ n : Ideal O)
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hO.p_mem n)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFinrankKs
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem padicValNat_finrank_Ks : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), (∀ m : ℕ, 0 < m → padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K m)) - padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K 1)) = m - 1) ∧ (K.1 ≤ Loc.MaximalUnramifiedExtension l → padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K 1)) - padicValNat l (finrank ℚ_[l] ↥K.1) = 0) := by
  intro l _ K
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : l - 1 ≠ 0 := by omega
  have hpow : ∀ n : ℕ, l ^ n ≠ 0 := fun n => pow_ne_zero n (by omega)

  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hle : Loc.K0 K ≤ K.1 := by unfold Loc.K0; exact inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  have hk0 : finrank ℚ_[l] ↥(Loc.K0 K) ≠ 0 := Module.finrank_pos.ne'
  refine ⟨fun m hm => ?_, fun hK => ?_⟩
  ·
    rw [finrank_Ks_eq l K m hm, finrank_Ks_eq l K 1 one_pos,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hk0 (Nat.mul_ne_zero (hpow _) hl1),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hk0 (Nat.mul_ne_zero (hpow _) hl1),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hpow _) hl1, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hpow _) hl1,
      (show ∀ n : ℕ, padicValNat l (l ^ n) = n from fun n => by simpa only [Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) n),
      (show ∀ n : ℕ, padicValNat l (l ^ n) = n from fun n => by simpa only [Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) n)]
    omega
  ·
    have heq : Loc.K0 K = K.1 := by unfold Loc.K0; exact inf_eq_left.mpr hK
    have hK1 : finrank ℚ_[l] ↥K.1 ≠ 0 := Module.finrank_pos.ne'
    have hv : padicValNat l (l - 1) = 0 :=
      by
        apply (Nat.padicValNat_def).trans
        exact padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    rw [finrank_Ks_eq l K 1 one_pos, heq, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hK1 (Nat.mul_ne_zero (hpow _) hl1),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hpow _) hl1, (show ∀ n : ℕ, padicValNat l (l ^ n) = n from fun n => by simpa only [Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) n), hv]
    omega

end GlobalTheory.HubLoc
end

