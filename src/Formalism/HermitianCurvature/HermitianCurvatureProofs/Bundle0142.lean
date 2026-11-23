module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0138
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0139
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMTop
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

theorem vtop_rows (k r : ℕ) (s : Fin (k + 1)) : rowsNv k r (Fin.last r) s = rowsN k r (Fin.last r) s := by
  funext j
  apply Fin.ext
  simp [rowsNv, rowsN]

theorem mirror_residue_top_holds : JDRvTop := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have hm : Q.mdim k r (Fin.last r) = k + 1 := by simp [Q.mdim]
  have hpos : ∀ j, (Q.posL k r (Fin.last r) j).val = r + j.val := fun j => by
    simp [Q.posL]; omega
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  simp only [FNv, Q.resG, Q.QL, Q.grp, Q.tL, Pi.neg_apply, neg_neg]
  have e1 : Q.resG k r (Fin.last r) J c =
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
        (fun g' => J (Q.wCell k r (Fin.last r) c * g')) := rfl
  rw [e1, Formalism.FourierDecayAlt.P5.chatL_smulC, Pi.smul_apply]
  congr 1
  rw [top_chatL hm _ hpos]
  unfold NLv
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, vtop_rows, vtop_rows]
  congr 1
  have ez : Q.wCell k r (Fin.last r) c *ᵥ z = z := top_wlist_wb c _ z hz
  have eh : herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (wI k r s)) z =
      herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z := by
    rw [← Matrix.mulVec_mulVec]
    conv_lhs => rw [← ez]
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hW.1 _ _
  have es : Q.posL k r (Fin.last r) (Fin.cast hm.symm s) = wI k r s := by
    apply Fin.ext; simp [Q.posL, wI]; omega
  have et : Q.posL k r (Fin.last r) (Fin.cast hm.symm t) = wI k r t := by
    apply Fin.ext; simp [Q.posL, wI]; omega
  rw [eh]
  simp only [Q.ybv, Q.xv, fvec, es, et]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPCommPf
section
open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PCommPf

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq]

theorem isOpen_slice {Dc : (Fin r → ℂ) → Set (Q.Mx k r)}
    (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1}) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    IsOpen (Dc c) := by
  have h := ho.preimage (continuous_const.prodMk continuous_id : Continuous (fun g : Q.Mx k r => (c, g)))
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨hc, hg⟩, fun hg => hg.2⟩

theorem tL_crd_comm (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Q.Mx k r))
    (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1})
    (hΨ : Q.SmoothFam k r i {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} Ψ) (l : Fin r) (Y : ℂ) (a b : Fin 2)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r i) (hgD : g ∈ Dc c) :
    Q.crd (pOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pOp l) Ψ) c g ∧
    Q.crd (pbOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pbOp l) Ψ) c g := by
  have hO : IsOpen (Dc c) := isOpen_slice ho hc
  have hgG : g ∈ Q.Glev k r i ∩ Dc c := ⟨hg, hgD⟩
  have hx : ((c, g) : Qx8.XX k r) ∈ Qx8.UU Dc := ⟨hc, hgD⟩
  have hcd := Qx8.cd_tL (E := Wq →L[ℂ] Wp) (i := i) (U₀ := Qx8.UU Dc) ho z z' Y a b
  have hder : ∀ s s₂ : ℂ,
      s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g +
        s₂ • Qx8.dv (Pi.single l Complex.I) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g)) =
      Q.tL k r z z' i Y a b (fun g' => s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) Ψ c g' +
        s₂ • Qx8.dv (Pi.single l Complex.I) Ψ c g'))) g := by
    intro s s₂
    rw [hcd.comm _ Ψ hΨ (c, g) hx hg, hcd.comm _ Ψ hΨ (c, g) hx hg, smul_smul]
    have := Qx8.tl_comb (z := z) (z' := z') (i := i) Formalism.FourierDecayAlt.P.transfer_linear_local hO Y a b (s * (1 / 2)) s₂
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l 1) hΨ) hc)
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l Complex.I) hΨ) hc) hgG
    rw [← this]
    simp only [smul_smul]
  refine ⟨?_, ?_⟩
  · show pOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pOp l (fun c' => Ψ c' g') c) g
    have h := hder (c l) (-Complex.I)
    simp only [pOp, if_pos hc, wirt]
    simp only [Qx8.dv, neg_smul, ← sub_eq_add_neg] at h
    exact h
  · show pbOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pbOp l (fun c' => Ψ c' g') c) g
    have h := hder (star (c l)) Complex.I
    simp only [pbOp, if_pos hc, wirtBar]
    simp only [Qx8.dv] at h
    exact h

end PCommPf

theorem residue_projection_commutation : JDRPComm := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).1

theorem crd_pbOp_QL_last_comm :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Dc : (Fin r → ℂ) → Set (Q.Mx k r)) (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} →
    Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ →
    ∀ (l : Fin r) (Y : ℂ) (a b : Fin 2), ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
      Q.crd (Formalism.QuantumDeterminants.pbOp l) (Q.QL k r z z' (Fin.last r) Y a b Ψ) c g =
        Q.QL k r z z' (Fin.last r) Y a b (Q.crd (Formalism.QuantumDeterminants.pbOp l) Ψ) c g := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).2

end Formalism.FourierDecayAlt.P.CutMP

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvDefs
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

def alP (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (k + 1)) : ℂ :=
  ((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z'

def beM (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (t : Fin (k + 1)) : ℂ :=
  ((-1 : ℂ) ^ (t : ℕ)) * z' (wI k r t)

def RInvAlphaP : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (w m : B.Mat k r), inWb k r z' → w ∈ UWset k r z' → m ∈ Nset k r →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X : (Fin (r + k) → Fin (2 * r + k + 1)) → M),
      ∑ c ∈ jSetR k r, (∑ i : Fin (k + 1), alP k r z' i * ((m * w)⁻¹.submatrix c (rowsR k r i)).det) • X c =
        ((m * w)⁻¹).det • ∑ i : Fin (k + 1), alP k r z' i • X (rowsR k r i)

def RInvBetaP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g S : B.Mat k r), g ∈ B.GV k r → S ∈ B.GV k r →
    ∀ d : Fin (r + k) → Fin (2 * r + k + 1),
      ∑ J ∈ jSetR k r, beJ k r z g J * (S.submatrix J d).det = S.det * beJ k r z (g * S) d

def RInvBetaLeftP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h m g : B.Mat k r), inWb k r z → h ∈ UWset k r z → m ∈ Nset k r →
    g ∈ B.GV k r → ∀ J : Fin (r + k) → Fin (2 * r + k + 1), beJ k r z (h⁻¹ * m⁻¹ * g) J = beJ k r z g J

def RInvAlphaM : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g S : B.Mat k r), g ∈ B.GV k r → S ∈ B.GV k r →
    ∀ c : Fin (r + k) → Fin (2 * r + k + 1),
      ∑ J ∈ jSetR k r, alJ k r z g J * ((S⁻¹).submatrix c J).det = (S⁻¹).det * alJ k r z (g * S) c

def RInvAlphaLeftM : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h m g : B.Mat k r), inWb k r z → h ∈ UWset k r z → m ∈ Nset k r →
    g ∈ B.GV k r → ∀ J : Fin (r + k) → Fin (2 * r + k + 1), alJ k r z (h⁻¹ * m⁻¹ * g) J = alJ k r z g J

def RInvBetaM : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (w m : B.Mat k r), inWb k r z' → w ∈ UWset k r z' → m ∈ Nset k r →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X : (Fin (r + k) → Fin (2 * r + k + 1)) → M),
      ∑ d ∈ jSetR k r, (∑ t : Fin (k + 1), beM k r z' t * ((m * w).submatrix (colsV k r t) d).det) • X d =
        (m * w).det • ∑ t : Fin (k + 1), beM k r z' t • X (colsV k r t)

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
section
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def cc (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) : Fin (P.r - j) → ℂ :=
  fun l => consC t c (Fin.cast (by omega) l)

def gi (j : ℕ) (hj : j + 1 ≤ P.r) (g : Mx P.k (P.r - (j + 1))) : Mx P.k (P.r - j) :=
  D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g)

def GoodFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ t₀ : ℂ, t₀ ≠ 0 → ∀ γ₀ ∈ B.GV P.k (P.r - (j + 1)), ∃ (U : Set (ℂ × B.Mat P.k (P.r - (j + 1))))
      (f : ℂ × B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), IsOpen U ∧ (t₀, γ₀) ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ p ∈ U, p.2 ∈ B.GV P.k (P.r - (j + 1)) → G p.1 p.2 = f p) ∧
  ∀ K : Set ℂ, IsCompact K → (∀ t ∈ K, t ≠ 0) → ∃ C : Set (B.Mat P.k (P.r - (j + 1))), IsCompact C ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ K, ∀ γ, G t γ ≠ 0 → γ ∈ C ∧
      (γ ∈ B.GV P.k (P.r - (j + 1)) → ε ≤ Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ)

def famP (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) (v : ℂ) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ => fderiv ℝ (fun u : ℂ => G u γ) t v

def Rep (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
    (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def InC (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') : Prop :=
  ∃ G, GoodFam T j G ∧ Rep T j hj Ψ G

def sliceFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r) (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ =>
    ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
      (psi P.k (P.r - j) (T.bs j).z cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1) *
          star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2))) •
        F ((rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1)⁻¹ * mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ *
          rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2)
      ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1))))

end defs

def FamJFOK : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ t : ℂ, t ≠ 0 → JFOKCpt (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (G t)

def FamAlg : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → GoodFam T j G' → ∀ m : ℂ → ℂ, ContDiffOn ℝ ∞ m {t | t ≠ 0} →
      GoodFam T j (fun t γ => G t γ + G' t γ) ∧ GoodFam T j (fun t γ => m t • G t γ)

def FamDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ v : ℂ, GoodFam T j (famP j G v)

def RepLin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G → GoodFam T j G' →
    ∀ t : ℂ, t ≠ 0 → ∀ (a : ℂ), ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => G t γ + G' t γ)) x.1 x.2 =
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2 +
            resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G' t)) x.1 x.2 ∧
        resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => a • G t γ)) x.1 x.2 =
          a • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def FamJFDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z', ∀ v : ℂ,
      HasDerivAt (fun s : ℝ =>
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G (t + (s : ℂ) * v))) x.1 x.2)
        (resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v t)) x.1 x.2) 0

def CellTie : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (cc j hj t x.1, gi j hj x.2) ∈ DomR P.k (P.r - j) (T.bs j).z (T.bs j).z' ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ B.GV P.k (P.r - (j + 1)) ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'

def SliceFamGood : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
      GoodFam T j (sliceFam T j hj F)

def SliceFamJF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
    ∀ t : ℂ, t ≠ 0 → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
      γ ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' →
      B.JF (T.bs (j + 1)) (sliceFam T j hj F t) γ =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • B.JF (T.bs j) F (mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ)

def OpClosed : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (X : ActualOps P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (i : Fin 6)
      (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      InC T j hj Ψ → InC T j hj (X.op ⟨0, by omega⟩ i Ψ)

def BTlAdjoin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r), IsActualLevel X L →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (l : Fin r) (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S),
      (bTl L l w a b).1 ∈ Algebra.adjoin ℂ (Set.range (X.op l))

def UUiwScalar : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (S : Type) [Fintype S] [DecidableEq S] (s : ℂ)
    (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S), Wd.UUiw (A := A) s w a b ∈ (⊥ : Subalgebra ℂ A)

end Formalism.FourierDecayAlt.P.CutSH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportU
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

def LevTransportU : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)),
    ∃ Tw : D.LevTower P.k P.r Wp Wq, D.TowerNormalised Tw ∧
      Tw.base.z = z ∧ Tw.base.z' = z' ∧ Tw.base.π = π ∧ Tw.base.π' = π' ∧
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'))) (κ : ℝ),
      Di = Tw.bs i ∧ 0 < κ ∧ IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
      ∀ (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
      ∃ T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π',
        LevTrClauses P μ L st l0 i c Di μi Li sti T ∧
        ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (shiftCf i c''))

end Formalism.FourierDecayAlt.P.PTie
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfHaar
section
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieJ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem haar_prop {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : B.IsHaarOn U μ) (hν : B.IsHaarOn U ν) : ∃ c : ℝ≥0∞, ν = c • μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r U μ ν hU hμ hν.conc hν.left hν.finite_compact
  exact ⟨c, by rw [hc, ENNReal.smul_def]⟩

theorem sfinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) : SFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem jfScale : Formalism.FourierDecayAlt.P.PTie.JFScale := by
  intro k r Wp Wq _ _ _ _ Bs Bs' hz hz' hπ hπ'
  have hW := Bs.haarW
  have hW' := Bs.haarW'
  rw [hz] at hW
  rw [hz'] at hW'
  obtain ⟨a, ha⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z) Bs'.haarW hW
  obtain ⟨a', ha'⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z') Bs'.haarW' hW'
  obtain ⟨b, hb⟩ := haar_prop (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) Bs'.haarN Bs.haarN
  have := sfinite_of_haar Bs'.haarW
  have := sfinite_of_haar Bs'.haarW'
  have := sfinite_of_haar Bs'.haarN
  refine ⟨(((a * b) * (a' * b)).toReal : ℂ), fun F => ?_⟩
  funext g
  simp only [B.JF, Pi.smul_apply]
  rw [hz, hz', hπ, hπ', ha, ha', hb]
  unfold besselJ
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [integral_smul_measure, Complex.coe_smul]
  congr 2
  ring

end Formalism.FourierDecayAlt.P.PTieJ

namespace Formalism.FourierDecayAlt.P

theorem jacquet_scaling : Formalism.FourierDecayAlt.P.PTie.JFScale := PTieJ.jfScale

end Formalism.FourierDecayAlt.P
end
end

