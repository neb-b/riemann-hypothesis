module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlipUSymmCont
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.CompanionTheory.NegDS

variable {n : ℕ} {ε ε' : Fin n → Bool}

theorem sign_eq_iff (he : ∀ a, ε' a = !ε a) (a b : Fin n) : ε' a = ε' b ↔ ε a = ε b := by
  rw [he a, he b]
  cases ε a <;> cases ε b <;> simp

theorem Jm_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Jm ε' = -Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_neg]
  congr 1
  funext a
  rw [he a]
  cases ε a <;> simp

theorem UJset_flip (he : ∀ a, ε' a = !ε a) : Formalism.MainNotions.S.UJset ε' = Formalism.MainNotions.S.UJset ε := by
  ext g
  show Formalism.REAL.inUJ ε' g ↔ Formalism.REAL.inUJ ε g
  unfold Formalism.REAL.inUJ
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem Kset_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Kset ε' = Formalism.REAL.Kset ε := by
  ext g
  show g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε' = Formalism.REAL.Jm ε' * g ↔
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem rhoC_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoC ε' = Formalism.REAL.rhoC ε := by
  funext a
  simp only [Formalism.REAL.rhoC, sign_eq_iff he]

theorem rhoN_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoN ε' = Formalism.REAL.rhoN ε := by
  funext a
  simp only [Formalism.REAL.rhoN, ne_eq, sign_eq_iff he]

theorem lowK_flip (he : ∀ a, ε' a = !ε a) (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK ε' lam = Formalism.QuantumDeterminants.lowK ε lam := by
  unfold Formalism.QuantumDeterminants.lowK
  rw [rhoC_flip he, rhoN_flip he]

theorem vNormSq_flip (he : ∀ a, ε' a = !ε a) (μ : Fin n → ℝ) : Formalism.MainNotions.S.vNormSq ε' μ = Formalism.MainNotions.S.vNormSq ε μ := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [rhoC_flip he]

theorem cdom_flip (he : ∀ a, ε' a = !ε a) (μ Λ : Fin n → ℝ) : Formalism.MainNotions.S.CDom ε' μ Λ ↔ Formalism.MainNotions.S.CDom ε μ Λ := by
  simp only [Formalism.MainNotions.S.CDom, sign_eq_iff he]

section Rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kstable_flip (he : ∀ a, ε' a = !ε a) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKStableOn ε' σ S ↔ Formalism.MainNotions.S.IsKStableOn ε σ S := by
  simp only [Formalism.MainNotions.S.IsKStableOn, Kset_flip he]

theorem ktype_flip (he : ∀ a, ε' a = !ε a) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKTypeOf ε' σ Λ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ Λ S := by
  simp only [Formalism.MainNotions.S.IsKTypeOf, kstable_flip he, Kset_flip he, cdom_flip he]

end Rep

def flipU (he : ∀ a, ε' a = !ε a) : Formalism.REAL.UJ ε' ≃* Formalism.REAL.UJ ε where
  toFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).1 g.2⟩
  invFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).2 g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem flipU_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he) := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem flipU_symm_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he).symm := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem memLp_flip (he : ∀ a, ε' a = !ε a) {F : Formalism.REAL.UJ ε → ℂ} (hF : MemLp F 2 (Formalism.REAL.muG ε)) :
    MemLp (F ∘ flipU he) 2 (Formalism.REAL.muG ε') := by
  have hc := flipU_cont he
  have hcs := flipU_symm_cont he
  let eH : Formalism.REAL.UJ ε' ≃ₜ Formalism.REAL.UJ ε := ⟨(flipU he).toEquiv, hc, hcs⟩
  have hme : MeasurableEmbedding (flipU he) := eH.measurableEmbedding
  haveI : (Measure.map (flipU he) (Formalism.REAL.muG ε')).IsHaarMeasure :=
    (flipU he).isHaarMeasure_map (Formalism.REAL.muG ε') hc hcs
  have hmap : Measure.map (flipU he) (Formalism.REAL.muG ε') =
      MeasureTheory.Measure.haarScalarFactor (Measure.map (flipU he) (Formalism.REAL.muG ε')) (Formalism.REAL.muG ε) •
        Formalism.REAL.muG ε :=
    MeasureTheory.Measure.isMulLeftInvariant_eq_smul _ _
  rw [← hme.memLp_map_measure_iff, hmap, ENNReal.smul_def]
  exact hF.smul_measure ENNReal.coe_ne_top

theorem sqInt_flip {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (he : ∀ a, ε' a = !ε a) (h : Formalism.MainNotions.S.IsSqIntOn ε σ) : Formalism.MainNotions.S.IsSqIntOn ε' σ := by
  intro v w
  have e : Formalism.MainNotions.S.coefOn (ε := ε') σ v w = Formalism.MainNotions.S.coefOn (ε := ε) σ v w ∘ flipU he := by
    funext g
    rfl
  rw [e]
  exact memLp_flip he (h v w)

theorem isDS_flip : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS (fun a => !ε a) lam σ := by
  intro n H _ _ ε lam σ h
  have he : ∀ a, (fun a => !ε a) a = !ε a := fun _ => rfl
  unfold Formalism.MainNotions.S.IsDS at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, sqInt_flip he h5, ?_, ?_⟩
  · rw [UJset_flip he]
    exact h3
  · rw [UJset_flip he]
    exact h4
  · obtain ⟨S, hS⟩ := h6
    exact ⟨S, by rw [lowK_flip he, ktype_flip he]; exact hS⟩
  · intro μ S hS
    rw [lowK_flip he, vNormSq_flip he, vNormSq_flip he]
    exact h7 μ S ((ktype_flip he μ S).1 hS)

end GlobalTheory.CompanionTheory.NegDS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagConverse
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin.BdU

theorem gram_apply {L : Type} [CommRing L] (s : L →+* L) {a b c : Type} [Fintype a]
    (M : Matrix a b L) (H : Matrix a a L) (N : Matrix a c L) (i : b) (j : c) :
    (cT s M * H * N) i j = ∑ k, ∑ l, s (M k i) * H k l * N l j := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem cT_cT_self {L : Type} [CommRing L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {a b : Type}
    (M : Matrix a b L) : cT s (cT s M) = M := by
  ext i j
  simp [cT, hs]

theorem gram_bd {ι L : Type} [Fintype ι] [CommRing L] (s : L →+* L) (b : ι → ℤ)
    (G H : Matrix ι ι L) (hG : G.BlockTriangular b) (hH : ∀ u v, H u v ≠ 0 → b u + b v = 0)
    (hGH : cT s G * H * G = H) : cT s (bd b G) * H * bd b G = H := by
  ext i j
  have e := congrFun (congrFun hGH i) j
  rw [gram_apply] at e ⊢
  by_cases hij : b i + b j = 0
  · rw [← e]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [bd, Matrix.of_apply]
    by_cases hGki : G k i = 0
    · simp [hGki]
    by_cases hGlj : G l j = 0
    · simp [hGlj]
    by_cases hHkl : H k l = 0
    · simp [hHkl]
    have h1 := hH k l hHkl
    have h2 : ¬ b i < b k := fun hlt => hGki (hG hlt)
    have h3 : ¬ b j < b l := fun hlt => hGlj (hG hlt)
    have hk : b k = b i := by omega
    have hl : b l = b j := by omega
    simp [hk, hl]
  · have hHij : H i j = 0 := by
      by_contra hne
      exact hij (hH i j hne)
    rw [hHij]
    refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
    simp only [bd, Matrix.of_apply]
    by_cases hk : b k = b i
    · by_cases hl : b l = b j
      · have hHkl : H k l = 0 := by
          by_contra hne
          have := hH k l hne
          exact hij (by omega)
        simp [hHkl]
      · simp [hl]
    · simp [hk]

theorem levi_unitary {ι L : Type} [Fintype ι] [DecidableEq ι] [Field L] (s : L →+* L) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) L) (Q : Matrix (Fin n) ι L) (Qi : Matrix ι (Fin n) L) (b : ι → ℤ)
    (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hH : ∀ u v, (cT s Q * J * Q) u v ≠ 0 → b u + b v = 0)
    (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g) (hgJ : cT s g * J * g = J)
    (hB : (Qi * g * Q).BlockTriangular b) :
    IsUnit (Q * bd b (Qi * g * Q) * Qi) ∧
      cT s (Q * bd b (Qi * g * Q) * Qi) * J * (Q * bd b (Qi * g * Q) * Qi) = J := by
  have cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L),
      cT s (A * B) = cT s B * cT s A := by
    intro a b c _ A B
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have cT1 : cT s (1 : Matrix (Fin n) (Fin n) L) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]
  have hQQ : cT s Qi * cT s Q = 1 := by rw [← cTm, h2, cT1]
  have hGu : cT s (Qi * g * Q) * (cT s Q * J * Q) * (Qi * g * Q) = cT s Q * J * Q := by
    calc cT s (Qi * g * Q) * (cT s Q * J * Q) * (Qi * g * Q)
        = cT s Q * (cT s g * ((cT s Qi * cT s Q) * (J * ((Q * Qi) * (g * Q))))) := by
          rw [cTm, cTm]
          simp only [Matrix.mul_assoc]
      _ = cT s Q * ((cT s g * J * g) * Q) := by
          rw [hQQ, h2, Matrix.one_mul, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
      _ = cT s Q * J * Q := by rw [hgJ, Matrix.mul_assoc]
  have hbdu := gram_bd s b (Qi * g * Q) (cT s Q * J * Q) hB hH hGu
  obtain ⟨u, hu⟩ := hg
  have hGunit : IsUnit (Qi * g * Q) := by
    refine ⟨⟨Qi * g * Q, Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q, ?_, ?_⟩, rfl⟩
    · calc Qi * g * Q * (Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q) = Qi * (g * (Q * Qi) * (↑u⁻¹ : Matrix (Fin n) (Fin n) L)) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.mul_inv, Matrix.mul_one, h1]
    · calc Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q * (Qi * g * Q) = Qi * ((↑u⁻¹ : Matrix (Fin n) (Fin n) L) * (Q * Qi) * g) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.inv_mul, Matrix.mul_one, h1]
  have hbdtri : (bd b (Qi * g * Q)).BlockTriangular b := by
    intro i j hij
    simp only [bd, Matrix.of_apply]
    rw [if_neg (ne_of_gt hij)]
  have hdet : (bd b (Qi * g * Q)).det = (Qi * g * Q).det := by
    rw [hbdtri.det, hB.det]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    congr 1
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, bd]
    rw [if_pos (i.2.trans j.2.symm)]
  have hbdunit : IsUnit (bd b (Qi * g * Q)) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, ← Matrix.isUnit_iff_isUnit_det]
    exact hGunit
  obtain ⟨w, hw⟩ := hbdunit
  refine ⟨⟨⟨Q * (↑w : Matrix ι ι L) * Qi, Q * (↑w⁻¹ : Matrix ι ι L) * Qi, ?_, ?_⟩, ?_⟩, ?_⟩
  · calc Q * (↑w : Matrix ι ι L) * Qi * (Q * (↑w⁻¹ : Matrix ι ι L) * Qi) = Q * ((↑w : Matrix ι ι L) * (Qi * Q) * (↑w⁻¹ : Matrix ι ι L)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Units.mul_inv, Matrix.mul_one, h2]
  · calc Q * (↑w⁻¹ : Matrix ι ι L) * Qi * (Q * (↑w : Matrix ι ι L) * Qi) = Q * ((↑w⁻¹ : Matrix ι ι L) * (Qi * Q) * (↑w : Matrix ι ι L)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, h2]
  · show Q * (↑w : Matrix ι ι L) * Qi = Q * bd b (Qi * g * Q) * Qi
    rw [hw]
  · calc cT s (Q * bd b (Qi * g * Q) * Qi) * J * (Q * bd b (Qi * g * Q) * Qi)
        = cT s Qi * ((cT s (bd b (Qi * g * Q)) * (cT s Q * J * Q) * bd b (Qi * g * Q)) * Qi) := by
          rw [cTm, cTm]
          simp only [Matrix.mul_assoc]
      _ = cT s Qi * ((cT s Q * J * Q) * Qi) := by rw [hbdu]
      _ = (cT s Qi * cT s Q) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hQQ, h2, Matrix.one_mul, Matrix.mul_one]

theorem gram_frm_degree {L : Type} [Field L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {n r m : ℕ}
    (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L)
    (hJ : cT s J = J) (hXX : cT s X * J * X = 0) (hYY : cT s Y * J * Y = 0)
    (hXY : cT s X * J * Y = 1) (hXZ : cT s X * J * Z = 0) (hYZ : cT s Y * J * Z = 0)
    (S : Finset (Fin r)) (u v : Idx r m)
    (h : (cT s (frm X Z Y) * J * frm X Z Y) u v ≠ 0) : lev m S u + lev m S v = 0 := by
  have cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L),
      cT s (A * B) = cT s B * cT s A := by
    intro a b c _ A B
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have cT1 : cT s (1 : Matrix (Fin r) (Fin r) L) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]
  have cT0 : ∀ {a b : Type}, cT s (0 : Matrix a b L) = 0 := by
    intro a b
    unfold Formalism.UG.cT
    ext i j
    simp
  have hYX : cT s Y * J * X = 1 := by
    have e := congrArg (cT s) hXY
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT1, ← Matrix.mul_assoc] at e
    exact e
  have hZX : cT s Z * J * X = 0 := by
    have e := congrArg (cT s) hXZ
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc] at e
    exact e
  have hZY : cT s Z * J * Y = 0 := by
    have e := congrArg (cT s) hYZ
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc] at e
    exact e
  rcases u with i | i | i <;> rcases v with j | j | j
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inl j) = (cT s X * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXX] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inl j)) = (cT s X * J * Z) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXZ] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inr j)) = (cT s X * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXY] at h
    have hij : i = j := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hij
    show (cnt S i - (S.card : ℤ)) + ((S.card : ℤ) - cnt S i) = 0
    ring
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inl j) = (cT s Z * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hZX] at h
    simp at h
  · show (0 : ℤ) + 0 = 0
    rfl
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) = (cT s Z * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hZY] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inl j) = (cT s Y * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYX] at h
    have hij : i = j := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hij
    show ((S.card : ℤ) - cnt S i) + (cnt S i - (S.card : ℤ)) = 0
    ring
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = (cT s Y * J * Z) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYZ] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = (cT s Y * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYY] at h
    simp at h

theorem bd_unitary : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (Qi * g * frm X Z Y).BlockTriangular (lev m S) → IsUnit (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) ∧ cT s (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) * J * (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) = J := by
  intro L _ s hs n r m J X Y Z Qi hJ hXX hYY hXY hXZ hYZ h1 h2 S g hg hgJ hB
  exact levi_unitary s J (frm X Z Y) Qi (lev m S) h1 h2
    (fun u v h => gram_frm_degree s hs J X Y Z hJ hXX hYY hXY hXZ hYZ S u v h) g hg hgJ hB

end GlobalTheory.CompanionTheory.CFin.BdU

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Harmonic
section
namespace GlobalTheory.CompanionTheory.GKHarmonic

theorem harmonic : PositivityTheory.Rg.Cz.Harmonic := by
  intro E _ _ a M _ _ _ _ κ L hd q ω hc h0
  cases q with
  | zero => exact Or.inl ⟨ω, hc, hd 0 ω hc, h0⟩
  | succ q => exact Or.inr ⟨q, ω, hc, hd _ ω hc, fun η hη h => h0 (h.symm.trans (hd q η hη))⟩

end GlobalTheory.CompanionTheory.GKHarmonic
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBoundStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_of_norm_bound : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ ν : Fin n → ℤ, Antitone ν → DomLE (wtR ν) (m0 lam) → ∀ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) → ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (wtR ν (w a) - rhoV n (w a) + rhoV n a) ^ 2 → ν ∈ harmZ lam := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge | exact GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge | (intros; apply GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemConeStatement
section
open PositivityTheory.RgBcC.RealD (inCone)

theorem GlobalTheory.T.highest_weight_mem_cone :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (K : Fin n → Fin n → Module.End ℂ V),
      Formalism.REAL.GlRel K → ∀ lev : Fin n → ℕ, Monotone lev →
      ∀ (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ) (x : V),
        Formalism.REAL.KHighest (fun _ => true) K ν x →
        (∀ a b v, lev a = lev b → a ≠ b → ev (K a b v) = 0) →
        (∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) →
        (∃ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ev (T x) ≠ 0) →
        inCone lev (ν - μ) :=
  GlobalTheory.CompanionTheory.HighestCone.inCone_of_highest
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneTwistGloballyGenerated
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.SerreBpf


open GlobalTheory.QCoh GlobalTheory.Twist CechPic GlobalTheory.LB in
theorem eventually_basePointFree (Y : Var ℂ) (i : Fin (Y.N + 1))
    (hi : Y.ι (genericPoint Y.X) ∈ ProjSpace.chart ℂ Y.N i) (Δ : Y.Dv) :
    ∀ᶠ m : ℕ in Filter.atTop, ∃ (L : LB Y.X) (r : L.ι → Y.Fnˣ) (n : ℕ) (b : Fin n → L.Sec),
      L.IsLB ∧ Presents (Δ + m • Y.hyp hi) L r ∧ ⨆ j, nonzeroLocus (b j) = ⊤ := by
  have hA : GlobalTheory.IsAmpleLB Y.O1 := Y.isAmple_projective_O_one
  have hK : (GlobalTheory.Cartier.toLB (-Δ)).IsLB := GlobalTheory.Cartier.isLB_toLB _
  have hL0 : (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))).IsLB := GlobalTheory.CechPic.isLB_dual hK
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL0
  haveI := GlobalTheory.LB.isFiniteType_toMod hL0
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))) :=
    GlobalTheory.QCoh.IsFiniteQC.of_isFiniteType
  filter_upwards [hA.eventually_isGloballyGenerated_twist
    (GlobalTheory.LB.toMod (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))))] with m hm
  have hM : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb Y.isLineBundle_twistingSheafOne _ _
  have hN : (GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi)).IsLB := GlobalTheory.Cartier.isLB_toLB _
  have h1 : GlobalTheory.QCoh.IsGloballyGenerated
      (GlobalTheory.twist (GlobalTheory.twist (GlobalTheory.LB.unitMod Y.X) (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)) := by
    haveI : Epi (GlobalTheory.Twist.map (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
        (GlobalTheory.Twist.unitTwistIso (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))).inv) :=
      (GlobalTheory.Twist.epi_map_iff hM _).2 inferInstance
    exact hm.of_epi (GlobalTheory.Twist.map (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
      (GlobalTheory.Twist.unitTwistIso (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))).inv)
  have hiso : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
      ((GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi)).div (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))) := by
    rw [← GlobalTheory.CechPic.tens_eq_div, ← GlobalTheory.CechPic.cls_eq_iff hM (GlobalTheory.CechPic.isLB_tens hN hK),
      GlobalTheory.CechPic.cls_tens hN hK, GlobalTheory.CechPic.cls_lbPow Y.isLineBundle_twistingSheafOne, ← GlobalTheory.Cartier.toPic_apply,
      ← GlobalTheory.Cartier.toPic_apply, ← (Y.presents_hyp hi).toPic_eq, map_add, map_neg, map_nsmul]
    abel
  obtain ⟨e⟩ := GlobalTheory.Twist.nonempty_twistTwistIso (F := GlobalTheory.LB.unitMod Y.X) hL0 hM hN hiso
  have h2 : GlobalTheory.QCoh.IsGloballyGenerated (GlobalTheory.LB.toMod (GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi))) :=
    (GlobalTheory.QCoh.isGloballyGenerated_iff_of_iso (e ≪≫ GlobalTheory.Twist.unitTwistIso _)).1 h1
  obtain ⟨n, s, hs⟩ := ((GlobalTheory.isGloballyGenerated_toMod_iff hN).1 h2).exists_fin_succ
  exact ⟨_, _, n + 1, s, hN, GlobalTheory.Cartier.presents_toLB _, hs⟩

end GlobalTheory.CompanionTheory.SerreBpf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem exists_Qp_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (g : GL (Fin (i + t)) k), ∃ q : Qp k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), g = (q : GL (Fin (i + t)) k) * κ := by
  intro k _ _ _ _ i t g
  obtain ⟨u, l, w, hw, hg⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : i + t = i + t))) g
  refine ⟨⟨(u : GL (Fin (i + t)) k) * GlobalTheory.SmGL.leviEmb k _ l, ?_⟩, w, hw, hg⟩
  exact Subgroup.mul_mem _ (GlobalTheory.SmGL.unipRad_le_parab k _ u.2)
    (GlobalTheory.SmGL.leviEmb_mem_parab k _ l)

end GlobalTheory.CompanionTheory.BZPsiPG
end

