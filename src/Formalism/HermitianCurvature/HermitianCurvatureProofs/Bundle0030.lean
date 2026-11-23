module

public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0075
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
section
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

theorem pd_mono {a b : ℕ} (hab : a ≤ b) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

theorem pd_const (c : ℂ) (d : ℕ) : U.IsPolyDeg (N := N) d (fun _ => c) := by
  refine ⟨MvPolynomial.C c, ?_, fun g => ?_⟩
  · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  · simp

theorem pd_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => g i j) := by
  refine ⟨MvPolynomial.X (Sum.inl (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_star_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g i j)) := by
  refine ⟨MvPolynomial.X (Sum.inr (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g + Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_add]

theorem pd_mul {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg b Q) :
    U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_mul]

theorem pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_sub]

theorem pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 0 a
  | insert x s hx ih =>
    have h1 := pd_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert hx] using h1

theorem pd_prod {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg (s.card * a) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 1 0
  | insert x s hx ih =>
    have h1 := pd_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hc : (insert x s).card * a = a + s.card * a := by
      rw [Finset.card_insert_of_notMem hx]; ring
    rw [hc]
    simpa [Finset.prod_insert hx] using h1

theorem pd_det {l : ℕ} (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin l) (Fin l) ℂ)
    (h : ∀ a b, U.IsPolyDeg 1 (fun g => M g a b)) : U.IsPolyDeg l (fun g => (M g).det) := by
  have key : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin l))),
      U.IsPolyDeg l (fun g => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i) := by
    intro σ _
    have h1 := pd_mul (pd_const (N := N) ((Equiv.Perm.sign σ : ℤ) : ℂ) 0)
      (pd_prod (Finset.univ : Finset (Fin l)) (fun i _ => h (σ i) i))
    refine pd_mono ?_ h1
    simp
  have h2 := pd_sum _ key
  simpa [Matrix.det_apply'] using h2

end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

namespace Formalism.FourierDecayAlt.P

open PartialDerivativeAlgebra

theorem gram_function_last_minor : C6.GfDlast := by
  intro k r z z' hz hz' g ε hε
  unfold Gf at hε
  have h0 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) :=
    mul_nonneg (mul_nonneg hz hz') (Complex.normSq_nonneg _)
  linarith

private theorem isPolyDeg_one_mulVec_apply {M : ℕ} (v : Fin M → ℂ) (j : Fin M) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin M) (Fin M) ℂ => Matrix.mulVec g v j) := by
  have h := pd_sum (N := M) (Finset.univ : Finset (Fin M))
    (P := fun m g => g j m * v m) (a := 1 + 0)
    (fun m _ => pd_mul (pd_entry j m) (pd_const (v m) 0))
  simpa [Matrix.mulVec, dotProduct] using h

theorem zhat_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => Zhat k r z z' g a b) := by
  have hH : ∀ i, U.IsPolyDeg 1
      (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
        Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) := by
    intro i
    have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
      (P := fun j g => Hpk k r i j * Matrix.mulVec g (fvec k r z' b) j) (a := 0 + 1)
      (fun j _ => pd_mul (pd_const (Hpk k r i j) 0) (isPolyDeg_one_mulVec_apply _ j))
    simpa [Matrix.mulVec, dotProduct] using h
  have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
    (P := fun i g => star (fvec k r z a i) * Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) (a := 0 + 1)
    (fun i _ => pd_mul (pd_const _ 0) (hH i))
  simpa [Zhat, herm, dotProduct] using h

private theorem isPolyDeg_star' {M a : ℕ} {P : Matrix (Fin M) (Fin M) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · have hm : (map (starRingEnd ℂ) q).totalDegree ≤ q.totalDegree := by
      unfold totalDegree; exact Finset.sup_mono (support_map_subset _ _)
    exact (totalDegree_rename_le _ _).trans (hm.trans hq)
  · dsimp only
    rw [hP g, eval_rename, eval_map]
    change starRingEnd ℂ (eval₂ (RingHom.id ℂ) _ q) = _
    rw [eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem zhat_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => star (Zhat k r z z' g a b)) := by
  exact isPolyDeg_star' (zhat_pd k r z z' a b)

theorem minor_polynomial_property : C6.DminPoly := by
  intro k r z z' l
  exact pd_det (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))) (fun a b => zhat_pd k r z z' _ _)

theorem dmin_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg l.val (fun g => star (Dmin k r z z' g l)) := by
  exact isPolyDeg_star' (minor_polynomial_property k r z z' l)

theorem gram_function_polynomial : C6.GfPoly := by
  intro k r z z'
  have hL := pd_mul (minor_polynomial_property k r z z' (Fin.last (r + 1)))
    (dmin_star_pd k r z z' (Fin.last (r + 1)))
  have hR0 := pd_mul (minor_polynomial_property k r z z' ⟨r, by omega⟩)
    (dmin_star_pd k r z z' ⟨r, by omega⟩)
  have hR := pd_mul (pd_const (((Tz k r z * Tz k r z' : ℝ)) : ℂ) 0) hR0
  have hL' : U.IsPolyDeg (2 * r + 2) (fun g => Dmin k r z z' g (Fin.last (r + 1)) *
      star (Dmin k r z z' g (Fin.last (r + 1)))) :=
    pd_mono (by simp; omega) hL
  have hR' : U.IsPolyDeg (2 * r + 2) (fun g => ((Tz k r z * Tz k r z' : ℝ) : ℂ) *
      (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩))) :=
    pd_mono (by simp; omega) hR
  have h := pd_sub hL' hR'
  convert h using 2 with g
  simp only [Gf, Complex.ofReal_sub, Complex.ofReal_mul, Complex.star_def, Complex.mul_conj]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JDomBoundOfNnMaj
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NNMaj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * B.gN (B.sgs p g) ^ (-A) ≤ b p

def JDomBound : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p

def JDomMeas : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS

theorem jDom_of_parts : JDomMeas → JDomBound → Formalism.FourierDecayAlt.JF.JDom := fun hM hB k r Wp Wq _ _ _ _ _ _ D A m F hT hC =>
  ⟨hM k r Wp Wq D A m F hT hC, hB k r Wp Wq D A m F hT hC⟩

variable {k r : ℕ}

private theorem gv_mul_lemma (a b : Mat k r) (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma sL_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sL p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨⟨h11, -⟩, ⟨h12, -⟩, -, -⟩ := hp
  unfold sL
  exact gv_mul_lemma _ _ h12 h11

lemma sR_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sR p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨-, -, ⟨h21, -⟩, ⟨h22, -⟩⟩ := hp
  unfold sR
  exact gv_mul_lemma _ _ h22 h21

lemma pn_lr (p : SS k r) (u v : List (Mat k r)) :
    B4.pn (B4.lr (u.map (AdL p)) (v.map (AdR p))) =
      (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod := by
  simp [B4.pn, B4.lr, List.map_append, List.prod_append, List.map_map, Function.comp_def]

private theorem inLie_inv_mul_mul_of_mem_gv {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) : inLie k r (y⁻¹ * X * y) := by
  have hHH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by rw [← mul_assoc, hHH, one_mul]
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    simp only [mul_assoc] at hy' ⊢
    rw [hy', hHH]
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [hinv]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc,
      hHH, mul_one]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    rw [hinv]
    simp only [mul_assoc, hHH']
  show (y⁻¹ * X * y)ᴴ * Hpk k r + Hpk k r * (y⁻¹ * X * y) = 0
  rw [e1, e2, ← add_mul, ← mul_add, hX', mul_zero, zero_mul]

lemma allLie_ad {p : SS k r} (hL : sL p ∈ GV k r) (hR : sR p ∈ GV k r) {u v : List (Mat k r)}
    (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    B4.AllLie (B4.lr (u.map (AdL p)) (v.map (AdR p))) := by
  unfold B4.AllLie B4.lr AdL AdR
  intro x hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨_, ⟨X, hX, rfl⟩, rfl⟩ | ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  · exact inLie_inv_mul_mul_of_mem_gv hL (hu X hX).1
  · exact inLie_inv_mul_mul_of_mem_gv hR (hv X hX).1

theorem jDomBound_of_nnMaj : NNMaj → JDomBound := by
  intro hNN k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC K hK hKsub
  obtain ⟨c, hc⟩ := hCC
  obtain ⟨b, hbI, hb⟩ := hNN k r Wp Wq D A m hThr K hK hKsub
  refine ⟨fun p => c * b p, hbI.const_mul c, ?_⟩
  intro u v hu hv hl g hg
  filter_upwards [hb u v hu hv hl g hg, B7.ae_inSS D] with p hp hin
  have hgG : g ∈ GV k r := (hKsub hg).1
  have hsG : sgs p g ∈ GV k r := B7.sgs_mem D hin hgG
  have hN : 0 < gN (sgs p g) := B6.gN_pos hsG
  have hgA : 0 < gN (sgs p g) ^ A := Real.rpow_pos_of_pos hN A
  have hc0 : 0 ≤ c := by
    have h0 := hc.2 [] [] (by simp) (by simp) (by simp) g hgG
    exact le_trans (mul_nonneg (Real.rpow_pos_of_pos (B6.gN_pos hgG) A).le (norm_nonneg _)) h0
  have hall := allLie_ad (sL_mem hin) (sR_mem hin) hu hv
  have hlen : (B4.lr (u.map (AdL p)) (v.map (AdR p))).length ≤ m := by
    rw [B4.length_lr, List.length_map, List.length_map]; exact hl
  have hbd := B4.bound_scaled hc _ (B4.lrt_lr _ _) hall hlen _ hsG
  rw [← B4.dLR_eq, pn_lr] at hbd
  refine (B7.norm_rho_le D hin _ g).trans ?_
  have h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤
      ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * c) / gN (sgs p g) ^ A := by
    rw [le_div_iff₀ hgA]
    linarith [hbd]
  refine h1.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left hp hc0))
  rw [Real.rpow_neg hN.le]
  field_simp

end Formalism.FourierDecayAlt.P.JFxDs2
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
section
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem gnLower : GNLower := fun _ _ _ hg => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg

theorem ae_mem {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ g ∂μ, Matrix.of g ∈ U := by
  rw [ae_iff]
  exact h.conc

end Formalism.FourierDecayAlt.P.NormBallVolumes

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes

theorem matrix_coefficient_bound_by_norm : Formalism.FourierDecayAlt.B2.CCFromGN := by
  intro k r Wp Wq _ _ _ _ D A h F c _ hb
  have hae : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤ ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) := by
    filter_upwards [ae_mem D.haarG] with g hg
    have h1 := hb _ hg
    have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
    have hp : 0 < gN (Matrix.of g) ^ A := Real.rpow_pos_of_pos hpos A
    rw [← ENNReal.ofReal_mul (abs_nonneg c), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ hp]
    calc ‖F (Matrix.of g)‖ * gN (Matrix.of g) ^ A = gN (Matrix.of g) ^ A * ‖F (Matrix.of g)‖ := mul_comm _ _
      _ ≤ c := h1
      _ ≤ |c| := le_abs_self c
  calc (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g : Mt k r, ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG := lintegral_mono_ae hae
    _ = ENNReal.ofReal |c| * ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem matrix_coefficient_integrable_of_parts : Formalism.FourierDecayAlt.B2.AssembleCCInt := by
  intro h1 h2 k r Wp Wq _ _ _ _ D A hA
  exact h1 k r Wp Wq D A (h2 k r D.μG A D.haarG hA)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end Formalism.FourierDecayAlt.P.NormBallVolumes
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormLeIntegralFsv
section
open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

def isoQ : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun s := conj (Complex.I * s)
  invFun w := -Complex.I * conj w
  map_add' a b := by simp [mul_add]
  map_smul' c a := by
    simp only [RingHom.id_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  left_inv a := by
    simp only [map_mul, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp
  right_inv w := by
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp [Complex.I_sq]
  norm_map' s := by simp

theorem isoQ_apply (s : ℂ) : isoQ s = conj (Complex.I * s) := rfl

theorem fsv_smul (s u z : ℂ) : P5.fsv s u * z = 𝐞 (-⟪u, (π⁻¹ : ℝ) • isoQ s⟫) • z := by
  unfold P5.fsv
  simp [Circle.smul_def, isoQ_apply]
  left
  rw [Real.fourierChar_apply]
  congr 1
  have hπ : π ≠ 0 := Real.pi_ne_zero
  apply Complex.ext <;> simp <;> field_simp <;> ring

theorem norm_le_integral_fsv (φ : ℂ → ℂ) (hφ : Continuous φ) (hi : MeasureTheory.Integrable φ)
    (hΞ : MeasureTheory.Integrable (fun s : ℂ => ∫ t : ℂ, P5.fsv s t * φ t)) (t : ℂ) :
    ‖φ t‖ ≤ ∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖ := by
  have hc : (π⁻¹ : ℝ) ≠ 0 := inv_ne_zero Real.pi_ne_zero
  have hL : ∀ s : ℂ, (∫ u : ℂ, P5.fsv s u * φ u) = 𝓕 φ ((π⁻¹ : ℝ) • isoQ s) := by
    intro s
    rw [fourier_eq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => fsv_smul s u (φ u))
  have hmp : MeasurePreserving isoQ := isoQ.measurePreserving
  have hme : MeasurableEmbedding isoQ := isoQ.toHomeomorph.measurableEmbedding
  have hint1 : Integrable (fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) := by
    have h1 : Integrable ((fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) ∘ isoQ) := by
      have h2 := hΞ
      simp_rw [hL] at h2
      exact h2
    exact (hmp.integrable_comp_emb hme).mp h1
  have hint : Integrable (𝓕 φ) := by
    first
      | exact (integrable_comp_smul_iff volume (𝓕 φ) hc).mp hint1
      | exact (MeasureTheory.integrable_comp_smul_iff (volume : Measure ℂ) (𝓕 φ) hc).mp hint1
      | exact (Integrable.comp_smul_iff hc).mp hint1
  have hinv : 𝓕⁻ (𝓕 φ) t = φ t := by
    first
      | exact hi.fourier_inversion hint hφ.continuousAt
      | exact hi.fourierInv_fourier_eq hint hφ.continuousAt
      | exact hφ.fourierInv_fourier_eq hi hint t
      | exact Continuous.fourierInv_fourier_eq hφ hi hint t
      | exact hi.fourierInv_fourier hint hφ.continuousAt
      | exact hφ.fourierInv_fourier hi hint t
      | exact MeasureTheory.Integrable.fourier_inversion hi hint hφ.continuousAt
  have hb : ‖φ t‖ ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := by
    rw [← hinv]
    first
      | rw [fourierInv_eq]
      | rw [Real.fourierInv_eq]
      | rw [fourierInv_eq']
      | rw [fourierInv_eq_fourier_neg, fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext w
    first
      | exact Circle.norm_smul _ _
      | simp
  have e1 := hmp.integral_comp hme (fun s : ℂ => ‖𝓕 φ ((π⁻¹ : ℝ) • s)‖)
  have e2 := Measure.integral_comp_smul (volume : Measure ℂ) (fun w : ℂ => ‖𝓕 φ w‖) (π⁻¹ : ℝ)
  try dsimp only at e1
  try dsimp only at e2
  have heq : (∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖) =
      |((π⁻¹ : ℝ) ^ 2)⁻¹| • ∫ w : ℂ, ‖𝓕 φ w‖ := by
    simp_rw [hL]
    rw [e1, e2, Complex.finrank_real_complex]
  rw [heq, smul_eq_mul]
  have h0 : 0 ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := integral_nonneg fun _ => norm_nonneg _
  have hπ : 1 ≤ |((π⁻¹ : ℝ) ^ 2)⁻¹| := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  nlinarith

end Formalism.FourierDecayAlt.P.PBO
end
end

