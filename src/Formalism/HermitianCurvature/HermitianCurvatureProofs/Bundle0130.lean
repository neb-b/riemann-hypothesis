module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0125
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0099
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0126
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0127
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GaXiSplit
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def rcAct {k p ρ : ℕ} (y : B.Mat k ρ) (x : U.RC k p ρ) : U.RC k p ρ := (fun v a => (y * Matrix.of x.1) v a, x.2)

def lhOf {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  U.wP σ * U.lowW σ v * (U.wP σ)⁻¹

def MMapEmbG : Prop := ∀ (k p ρ : ℕ) (Z : Matrix (Fin p) (Fin p) ℂ) (γ y₁ y₂ : B.Mat k ρ),
  U.mMap k p ρ Z (y₁ * γ * y₂) = U.embG k p ρ y₁ * U.mMap k p ρ Z γ * U.embG k p ρ y₂

def MMapLZU : Prop := ∀ (k p ρ : ℕ) (l Z u : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ), IsUnit l.det →
  U.mMap k p ρ (l * Z * u) γ = U.muP k p ρ (lᴴ)⁻¹ * U.mMap k p ρ Z γ * U.muP k p ρ u

def EmbGMuP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (q : Matrix (Fin p) (Fin p) ℂ),
  U.embG k p ρ y * U.muP k p ρ q = U.muP k p ρ q * U.embG k p ρ y

def EmbGRn : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (x : U.RC k p ρ), yᴴ * Hpk k ρ * y = Hpk k ρ →
  U.embG k p ρ y * U.Rn k p ρ x = U.Rn k p ρ (rcAct y x) * U.embG k p ρ y

def HeadHEq : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (v : U.LW σ → ℂ) (u : G.UT p → ℂ),
  U.headH σ d v u = lhOf σ v * U.hMat σ d * G.upper u ∧ G.IsLowerUni (lhOf σ v)

def ZjHZero : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : U.XiH p 0 σ) (Z : G.Mat 0),
  U.ZjH σ d η Z = U.headH σ d η.2.1 η.2.2

def GaXiSplit : Prop := ∀ (k p ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : U.Xi k p 0 ρ σ) (Z : G.Mat 0)
  (h ν h' ν' g : B.Mat k ρ), IsUnit h.det → IsUnit ν.det → h'ᴴ * Hpk k ρ * h' = Hpk k ρ →
  U.gaXi k ρ σ d ξ Z (h⁻¹ * ν⁻¹ * g * ν' * h') =
    (U.Rn k p ρ (-ξ.1.1) * U.muP k p ρ (lhOf σ ξ.2.2.1)ᴴ⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)) *
      U.mMap k p ρ (U.hMat σ d) g *
      (U.embG k p ρ ν' * U.muP k p ρ (G.upper ξ.2.2.2) * U.Rn k p ρ (rcAct h' ξ.1.2)) * U.embG k p ρ h'

def LeftMem : Prop := ∀ (k p ρ : ℕ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.RC k p ρ) (l : Matrix (Fin p) (Fin p) ℂ)
  (h ν : B.Mat k ρ), inWb k ρ z → G.IsLowerUni l → h ∈ UWset k ρ z → ν ∈ Nset k ρ →
  U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹) ∈ Sset k (p + ρ) (liftVec k p ρ z)

def PsiRight : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (ν' : B.Mat k ρ) (u : G.UT p → ℂ)
  (x : U.RC k p ρ), inWb k ρ z' → ν' ∈ Nset k ρ →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.embG k p ρ ν' * U.muP k p ρ (G.upper u) * U.Rn k p ρ x) =
    psi k ρ z' cStd ν' * psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u)) *
      psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiRnAct : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (h' : B.Mat k ρ) (x : U.RC k p ρ),
  inWb k ρ z' → h' ∈ UWset k ρ z' →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ (rcAct h' x)) = psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiMuP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (u : G.UT p → ℂ), inWb k ρ z' →
  star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u))) = G.psi U.betaU (U.supS (G.upper u))

def MuNLeft : Prop := ∀ (k p ρ : ℕ),
  D.muN k (p + ρ) = ((U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ))).map
    (fun x => Matrix.of.symm (U.embG k p ρ (Matrix.of x.2.2) * U.muP k p ρ (G.upper x.2.1) * U.Rn k p ρ x.1))

def RcActMP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ), ‖y.det‖ = 1 →
  MeasurePreserving (rcAct (p := p) y) (U.muRC k p ρ) (U.muRC k p ρ)

def RightMP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (μj : Measure (Mt k ρ)) (μ0' : Measure (Mt k (p + ρ))),
  B.IsHaarOn (UWset k ρ z') μj → μj Set.univ = 1 → μ0' = μj.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
  MeasurePreserving
    (fun y : (Mt k ρ × Mt k ρ) × (U.RC k p ρ × (G.UT p → ℂ)) =>
      (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl y.1.1,
        Matrix.of.symm (U.embG k p ρ (Matrix.of y.1.2) * U.muP k p ρ (G.upper y.2.2) *
          U.Rn k p ρ (rcAct (Matrix.of y.1.1) y.2.1))))
    ((μj.prod (D.muN k ρ)).prod ((U.muRC k p ρ).prod volume)) (μ0'.prod (D.muN k (p + ρ)))

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianInsertionVectorOrthogonal
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section SpacedProductLowerBound

variable {k : ℕ}

def pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) : Fin m :=
  ⟨if c < i.val then c else c - 1, by split_ifs <;> omega⟩

theorem succAbove_pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) :
    (i.succAbove (pidx m i c h)).val = c := by
  rw [succAbove_val]; unfold pidx; simp only; split_ifs <;> omega

theorem pidx_succAbove (m : ℕ) (i : Fin (m + 1)) (b : Fin m) (h : (i.succAbove b).val < m + 1 ∧ (i.succAbove b).val ≠ i.val) :
    pidx m i (i.succAbove b).val h = b := by
  ext; unfold pidx; simp only; rw [succAbove_val]; split_ifs <;> omega

theorem herm_add_smul_right {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w1 w2 : Fin n → ℂ) (a b : ℂ) :
    herm H v (a • w1 + b • w2) = star a * herm H v w1 + star b * herm H v w2 := by
  unfold herm
  simp [star_add, star_smul, add_dotProduct, smul_dotProduct]

def ViF (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ) : Fin (2 * (m + 1) + k + 1) → ℂ :=
  fun p => if p = esI k (m + 1) i then 1
    else if h : p.val < m + 1 ∧ p.val ≠ i.val then -star (Vc (pidx m i p.val h) (eI k (m + 1) i)) else 0

variable (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem insertion_vector_zero_off_index (p : Fin (2 * (m + 1) + k + 1)) (hp : m + 1 ≤ p.val) (hne : p ≠ esI k (m + 1) i) : ViF m i Vc p = 0 := by
  unfold ViF; rw [if_neg hne, dite_eq_right (by omega)]

theorem ViF_eI : ViF m i Vc (eI k (m + 1) i) = 0 := by
  unfold ViF
  rw [if_neg, dite_eq_right]
  · simp [eI]
  · intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega

theorem tau_eI (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (eI k (m + 1) c) = esI k (m + 1) c := by
  have := c.isLt
  ext; rw [tau_val, if_pos (by left; simp only [eI]; omega)]; simp only [eI, esI]

theorem tau_esI (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (esI k (m + 1) c) = eI k (m + 1) c := by
  have := c.isLt
  ext; rw [tau_val, if_pos (by right; simp only [esI]; omega)]; simp only [esI, eI]; omega

end SpacedProductLowerBound

section N2c

variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem sg_val' (q : Fin (2 * (m + 1) + k + 1)) : (NFOne.sg k (m + 1) q).val = 2 * (m + 1) + k - q.val := rfl

theorem ViF_alt (l : Fin (2 * (m + 1) + k + 1)) : ViF m i Vc l = 0 ∨ ViF m i Vc (WeylGroupFacts.tau k (m + 1) l) = 0 := by
  by_cases h1 : l = esI k (m + 1) i
  · right; rw [h1, tau_esI]; exact ViF_eI m i Vc
  by_cases h2 : l = eI k (m + 1) i
  · left; rw [h2]; exact ViF_eI m i Vc
  by_cases h3 : m + 1 ≤ l.val
  · left; exact insertion_vector_zero_off_index m i Vc l h3 h1
  · right
    apply insertion_vector_zero_off_index
    · rw [tau_val]; split_ifs <;> omega
    · intro h; apply h2
      have := congrArg (WeylGroupFacts.tau k (m + 1)) h
      rw [WeylGroupFacts.tau_tau, tau_esI] at this; exact this

theorem ViF_iso : herm (Hpk k (m + 1)) (ViF m i Vc) (ViF m i Vc) = 0 := by
  rw [herm_expand]
  apply Finset.sum_eq_zero
  intro l _
  rcases ViF_alt m i Vc l with h | h <;> simp [h]

theorem hermitian_insertion_vector_orthogonal (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (hz : inWb k (m + 1) z') :
    herm (Hpk k (m + 1)) z' (ViF m i Vc) = 0 := by
  rw [herm_expand]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
  · rw [insertion_vector_zero_off_index m i Vc l hW.1 (by intro h; rw [h] at hW; simp [esI] at hW; omega)]; simp
  · rw [hz (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp

theorem ViF_star (q : Fin (2 * (m + 1) + k + 1)) (hq : m + 1 + k < q.val) :
    ViF m i Vc q = if (NFOne.sg k (m + 1) q).val = i.val then 1 else 0 := by
  by_cases h : q = esI k (m + 1) i
  · rw [if_pos (by rw [sg_val', h]; simp [esI]; omega)]
    unfold ViF; rw [if_pos h]
  · rw [insertion_vector_zero_off_index m i Vc q (by omega) h, if_neg]
    intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; omega

theorem ViF_Vc (hVs : ∀ (b : Fin m) (q : Fin (2 * (m + 1) + k + 1)), m + 1 + k < q.val →
      Vc b q = if (NFOne.sg k (m + 1) q).val = (i.succAbove b).val then 1 else 0) (c' : Fin m) :
    herm (Hpk k (m + 1)) (ViF m i Vc) (Vc c') = 0 := by
  have hs := (i.succAbove c').isLt
  have hsi : (i.succAbove c').val ≠ i.val := fun h' => Fin.succAbove_ne i c' (Fin.ext h')
  rw [herm_expand, Finset.sum_eq_add (eI k (m + 1) i) (esI k (m + 1) (i.succAbove c'))]
  · rw [tau_eI, tau_esI]
    have e1 : ViF m i Vc (esI k (m + 1) i) = 1 := by unfold ViF; rw [if_pos rfl]
    have e2 : ViF m i Vc (eI k (m + 1) (i.succAbove c')) = -star (Vc c' (eI k (m + 1) i)) := by
      unfold ViF
      rw [if_neg (by intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega),
        dite_eq_left ⟨by simp only [eI]; omega, by simpa [eI] using hsi⟩]
      congr 3
      have := pidx_succAbove m i c' ⟨hs, hsi⟩
      simpa [eI] using this
    have e3 : Vc c' (esI k (m + 1) (i.succAbove c')) = 1 := by
      rw [hVs c' _ (by simp [esI]; omega), if_pos (by rw [sg_val']; simp [esI]; omega)]
    rw [e1, e2, e3, sgn_one _ (by simp [eI]; omega), sgn_one _ (by simp [esI]; omega)]
    simp
  · intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega
  · intro l _ hl
    by_cases hS : m + 1 + k < l.val
    · rw [hVs c' l hS, if_neg]
      · simp
      · intro h'; apply hl.2; ext; rw [sg_val'] at h'; simp [esI]; omega
    · by_cases hX : l.val < m + 1
      · rw [insertion_vector_zero_off_index m i Vc (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]
        · simp
        · intro h; apply hl.1
          have := congrArg (WeylGroupFacts.tau k (m + 1)) h
          rw [WeylGroupFacts.tau_tau, tau_esI] at this; exact this
      · have ht : WeylGroupFacts.tau k (m + 1) l = l := by ext; rw [tau_val]; split_ifs <;> omega
        rw [ht, insertion_vector_zero_off_index m i Vc l (by omega) (by intro h; rw [h] at hS; simp [esI] at hS; omega)]; simp
  · simp
  · simp

end N2c

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PairAtTAdjCpt
section
open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_eq_sum (A C : Wq →L[ℂ] Wp) :
    B.hsInner A C = ∑ m, ⟪C (stdOrthonormalBasis ℂ Wq m), A (stdOrthonormalBasis ℂ Wq m)⟫_ℂ := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply]

end HS

section Adj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_t_adj_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (hK : ∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
      ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (Y : ℂ) (a b : Fin 2)
    (h1 : ∀ m, Integrable (fun x : Mt P.k P.r =>
      ⟪(Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m),
        (X.t Y a b Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m)⟫_ℂ) μ)
    (h2 : ∀ m, Integrable (fun x : Mt P.k P.r =>
      ⟪(X.t (star Y) b a Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m),
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m)⟫_ℂ) μ) :
    pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c := by
  have hA := Formalism.FourierDecayAlt.P.actual_adjointness Wp Wq P z z' π π' hP X μ hμ Φ Ψ c hc hK Y a b
  simp only [pairAt, hsInner_eq_sum]
  rw [integral_finsetSum _ (fun m _ => h1 m), integral_finsetSum _ (fun m _ => h2 m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e := congrArg (starRingEnd ℂ) (hA (stdOrthonormalBasis ℂ Wq m))
  rw [← integral_conj, ← integral_conj] at e
  simp only [inner_conj_symm] at e
  exact e

end Adj

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.XepolNatDegree
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

section poly

theorem lag_weights (k : ℕ) : ∃ lam : Fin (k + 1) → ℂ, ∀ p : ℂ[X], p.natDegree ≤ k →
    ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1) := by
  classical
  let v : Fin (k + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin (k + 1))) := by
    intro a _ b _ hab
    have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := hab
    exact Fin.ext (by exact_mod_cast h')
  refine ⟨fun j => (Lagrange.basis Finset.univ v j).coeff (k - 1), ?_⟩
  intro p hp
  have hdeg : p.degree < (Finset.univ : Finset (Fin (k + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp) (by exact_mod_cast Nat.lt_succ_self k)
  conv_rhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.coeff_C_mul, mul_comm]

def xpol (P : M.Par) (ρ : M.Ty P) : ℂ[X] := ∏ i ∈ Finset.Icc 1 (P.k - 1), (X + C ((M.rho P ρ i : ℝ) : ℂ))

def xepol (P : M.Par) (l : ℕ) (ρ : M.Ty P) : ℂ[X] :=
  ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (X + C ((M.rho P ρ i : ℝ) : ℂ))

theorem xpol_eval (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : (xpol P ρ).eval Y = M.xC P ρ Y := by
  simp [xpol, M.xC, Polynomial.eval_prod]

theorem xepol_eval (P : M.Par) (l : ℕ) (ρ : M.Ty P) (Y : ℂ) : (xepol P l ρ).eval Y = M.xEx P {l} ρ Y := by
  simp [xepol, M.xEx, Polynomial.eval_prod]

theorem xpol_monic (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

theorem xpol_natDegree (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree = P.k - 1 := by
  unfold xpol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp [Polynomial.natDegree_X_add_C]

theorem xpol_coeff (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).coeff (P.k - 1) = 1 := by
  rw [← xpol_natDegree P ρ]
  exact (xpol_monic P ρ).coeff_natDegree

theorem xepol_natDegree (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    (xepol P l ρ).natDegree = P.k - 2 := by
  unfold xepol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]
  omega

end poly

section ring

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def fl (P : M.Par) (l : ℕ) (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ0 => if M.Up P l ρ0 ρ then 1 else 0

theorem up_func {l : ℕ} {ρ0 ρ ρ' : M.Ty P} (h1 : M.Up P l ρ0 ρ) (h2 : M.Up P l ρ0 ρ') : ρ = ρ' := by
  funext i
  apply Fin.ext
  rw [h1 i, h2 i]

theorem kap_decomp (d : Q.NFData P A) (g : M.Ty P → ℂ) : d.κ g = ∑ ρ0, g ρ0 • d.κ (dl ρ0) := by
  have h : g = ∑ ρ0, g ρ0 • dl ρ0 := by
    funext ρ
    simp [dl, Finset.sum_apply]
  conv_lhs => rw [h]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul]

theorem sum_dl (d : Q.NFData P A) : ∑ ρ, d.κ (dl ρ) = 1 := by
  have h : ∑ ρ, (dl ρ : M.Ty P → ℂ) = 1 := by
    funext x
    simp [dl, Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, h, map_one]

theorem dl_mul_kap (d : Q.NFData P A) (ρ : M.Ty P) (g : M.Ty P → ℂ) :
    d.κ (dl ρ) * d.κ g = g ρ • d.κ (dl ρ) := by
  have h : dl ρ * g = g ρ • dl ρ := by
    funext x
    by_cases hx : x = ρ
    · subst hx
      simp [dl]
    · simp [dl, hx]
  rw [← map_mul, h, map_smul]

theorem kap_comm (d : Q.NFData P A) (hR : d.Rel) (f : M.Ty P → ℂ) {g : A}
    (hg : g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : d.κ f * g = g * d.κ f := by
  have hm : g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs} := Or.inl (Or.inr hg)
  exact (hR.2.1 f g hm).eq

theorem fns_comm' (d : Q.NFData P A) {x y : A}
    (hx : x ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A))
    (hy : y ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : x * y = y * x :=
  d.L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem comb {k : ℕ} {lam : Fin (k + 1) → ℂ}
    (hlam : ∀ p : ℂ[X], p.natDegree ≤ k → ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1))
    (p : ℂ[X]) (hp : p.natDegree ≤ k) (O : A) :
    ∑ j : Fin (k + 1), lam j • (p.eval ((j : ℕ) : ℂ) • O) = p.coeff (k - 1) • O := by
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, hlam p hp]

theorem e10 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 1 0 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nab)) +
      ((xpol P ρ) * (X + C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζb)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ ρ0, (C (fl P l ρ ρ0) * xepol P l ρ0).eval Y • (d.SS l * d.κ (dl ρ0)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζbG : d.L.GG * d.L.ζb = d.L.ζb * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * d.L.ζb := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζb * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζb * (d.L.GG * d.L.GGi)) := by rw [hζbG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζb := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.l0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.l0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.l0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.weightedSumBis, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hc : d.κ (dl ρ) * d.SS l = d.SS l * d.κ (fl P l ρ) := by
      apply hR.2.2.2.1 l
      intro ρ0 ρ' hup
      by_cases h : ρ' = ρ
      · subst h
        simp [dl, fl, hup]
      · have hn : ¬ M.Up P l ρ0 ρ := fun h2 => h (up_func hup h2)
        simp [dl, fl, h, hn]
    rw [← mul_assoc, hc, mul_assoc, ← map_mul, kap_decomp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ0 _ => ?_)
    rw [mul_smul_comm]
    congr 1
    simp [Polynomial.eval_mul, Polynomial.eval_C, xepol_eval]

theorem e01 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 0 1 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nabs)) +
      ((xpol P ρ) * (X - C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζ)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (xepol P l ρ).eval Y • (d.κ (dl ρ) * star (d.SS l)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζG : d.L.GG * d.L.ζ = d.L.ζ * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * d.L.ζ := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζ * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζ * (d.L.GG * d.L.GGi)) := by rw [hζG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζ := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.m0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.m0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.m0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.S12, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← mul_assoc, dl_mul_kap]
    simp only [xepol_eval, smul_mul_assoc]

end ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

