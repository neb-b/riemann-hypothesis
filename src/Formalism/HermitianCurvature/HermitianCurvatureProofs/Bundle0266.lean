module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0255
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDJNice
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_orbital_niceness : RDJNice := by
  intro k r Wp Wq _ _ _ _ _ _ D F hF
  obtain ⟨ε, hε, hN⟩ := hF
  have h := Formalism.FourierDecayAlt.P.bessel_function_finite_class k r Wp Wq D F ε hε hN
  refine ⟨by rw [ffl_om_eq]; exact h, ?_⟩
  intro g₀ hg₀
  obtain ⟨U, F', hU, hgU, hc, he⟩ := h.1 g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg₀.1, hg₀.2⟩
  exact ⟨U, F', hU, hgU, by exact_mod_cast hc, fun g hg hgG => he g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG)⟩

end Formalism.FourierDecayAlt.P.CutSE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSCoordAdj
section
open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Mul

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rAdj_realMul (μ : Measure (Mt k r)) (W : Module.End ℂ (RadSp k r z z' π π')) (m : Mx k r → ℝ)
    (hW : ∀ (Φ : RadSp k r z z' π π'), ∀ x ∈ DomR k r z z',
      (W Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = ((m x.2 : ℝ) : ℂ) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) :
    RAdj μ (mkP W W) := by
  have hval : ∀ (Φ : RadSp k r z z' π π') (x : (Fin r → ℂ) × Mx k r),
      (W Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = ((m x.2 : ℝ) : ℂ) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    intro Φ x
    by_cases hx : x ∈ DomR k r z z'
    · exact hW Φ x hx
    · rw [Formalism.FourierDecayAlt.P5.radSp_zero_off (W Φ) hx, Formalism.FourierDecayAlt.P5.radSp_zero_off Φ hx, smul_zero]
  have htest : ∀ Ψ : RadSp k r z z' π π', RTest Ψ → RTest (W Ψ) := by
    rintro Ψ ⟨K, hK, hKD, h0⟩
    exact ⟨K, hK, hKD, fun x hx => by rw [hval, h0 x hx, smul_zero]⟩
  have hip : ∀ Φ Ψ : RadSp k r z z' π π', radIp μ (W Φ) Ψ = radIp μ Φ (W Ψ) := by
    intro Φ Ψ
    unfold radIp
    congr 1; funext c; congr 1; funext x
    have e1 := hval Φ (c, Matrix.of x)
    have e2 := hval Ψ (c, Matrix.of x)
    simp only at e1 e2
    rw [e1, e2, hsVec_smul_rd, hsVec_smul_rd, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  exact ⟨htest, htest, fun Φ Ψ _ => hip Φ Ψ, fun Φ Ψ _ => hip Φ Ψ⟩

end Mul

theorem spectral_function_adjoint : RDSFnAdj := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hGGi, -⟩ := hD.2.2.1
  rw [hGGi]
  refine rAdj_realMul μ (X.fn 5) (fun g => (GGl P.k P.r z z' g)⁻¹) fun Φ x hx => ?_
  rw [X.fn_apply 5 Φ x hx]
  simp [fnVal]

section MulC

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rAdj_mulPair (μ : Measure (Mt k r)) (W W' : Module.End ℂ (RadSp k r z z' π π')) (m : (Fin r → ℂ) → ℂ)
    (hW : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g = m c • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g)
    (hW' : ∀ (Φ : RadSp k r z z' π π') c g,
      (W' Φ : Fn k r (Wq →L[ℂ] Wp)) c g = conj (m c) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) :
    RAdj μ (mkP W W') ∧ RAdj μ (mkP W' W) := by
  have ht : ∀ (V : Module.End ℂ (RadSp k r z z' π π')) (m' : (Fin r → ℂ) → ℂ),
      (∀ (Φ : RadSp k r z z' π π') c g, (V Φ : Fn k r (Wq →L[ℂ] Wp)) c g = m' c • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) →
      ∀ Ψ, RTest Ψ → RTest (V Ψ) := by
    rintro V m' hV Ψ ⟨K, hK, hKD, h0⟩
    exact ⟨K, hK, hKD, fun x hx => by rw [hV, h0 x hx, smul_zero]⟩
  have h1 : ∀ Φ Ψ : RadSp k r z z' π π', radIp μ (W Φ) Ψ = radIp μ Φ (W' Ψ) := by
    intro Φ Ψ
    unfold radIp
    congr 1; funext c; congr 1; funext x
    rw [hW, hW', hsVec_smul_rd, hsVec_smul_rd, inner_smul_left, inner_smul_right]
  have h2 : ∀ Φ Ψ : RadSp k r z z' π π', radIp μ (W' Φ) Ψ = radIp μ Φ (W Ψ) := by
    intro Φ Ψ
    unfold radIp
    congr 1; funext c; congr 1; funext x
    rw [hW, hW', hsVec_smul_rd, hsVec_smul_rd, inner_smul_left, inner_smul_right, Complex.conj_conj]
  exact ⟨⟨ht W m hW, ht W' _ hW', fun Φ Ψ _ => h1 Φ Ψ, fun Φ Ψ _ => h2 Φ Ψ⟩,
    ⟨ht W' _ hW', ht W m hW, fun Φ Ψ _ => h2 Φ Ψ, fun Φ Ψ _ => h1 Φ Ψ⟩⟩

end MulC

def RDSPAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ l, RAdj μ (L.p l) ∧ RAdj μ (L.pb l)

theorem rDSCoordAdj_of_p (hp : RDSPAdj) : RDSCoordAdj := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr l
  obtain ⟨-, -, hc, hci, hcb, hcbi, -⟩ := hD.2.2.1
  obtain ⟨hpl, hpbl⟩ := hp Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr l
  have e : ∀ (i : Fin 6) (Φ : RadSp P.k P.r z z' π π') c g,
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = Formalism.QuantumDeterminants.opL l i (fun c' => (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g) c :=
    fun i Φ c g => by rw [X.op_apply]; rfl
  have C1 := rAdj_mulPair μ (X.op l 1) (X.op l 4) (fun c => c l) (fun Φ c g => by rw [e]; rfl)
    (fun Φ c g => by rw [e]; rfl)
  have C2 := rAdj_mulPair μ (X.op l 2) (X.op l 5) (fun c => (c l)⁻¹) (fun Φ c g => by rw [e]; rfl)
    (fun Φ c g => by rw [e]; simp [Formalism.QuantumDeterminants.opL, Formalism.QuantumDeterminants.cbiOp, map_inv₀])
  refine ⟨hpl, hpbl, ?_, ?_, ?_, ?_⟩
  · rw [hc]; exact C1.1
  · rw [hci]; exact C2.1
  · rw [hcb]; exact C1.2
  · rw [hcbi]; exact C2.2

section IpLin

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end IpLin

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA
section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

def RDSPolyProp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq), CutMP.PolyOp o κ Θ → B.Commutes D (B.GPos D) Θ → OpProp1 D Θ

def RDSAGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsPlace P D.z D.z' D.π D.π' → ∀ y : ℂ,
    ∃ Θ Θv : B.DiffOp P.k P.r Wp Wq, (∃ o κ : ℕ, CutMP.PolyOp o κ Θ) ∧ (∃ o κ : ℕ, CutMP.PolyOp o κ Θv) ∧
      B.Commutes D (B.GPos D) Θ ∧ B.Commutes D (B.GPos D) Θv ∧
      ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r D.z D.z' D.π D.π' 0 (JF.Om P.k P.r D.z D.z') →
        ∀ x ∈ DomR P.k P.r D.z D.z',
          resG P.k P.r (Fin.last P.r) (B.opApply Θ J) x.1 x.2 =
              CutMP.dMul (CutMP.drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (resG P.k P.r (Fin.last P.r) J)) x.1 x.2 ∧
            resG P.k P.r (Fin.last P.r) (B.opApply Θv J) x.1 x.2 =
              CutMP.dMul (CutMP.drbF P.r) (Q.crd (Q.cmp (CutMP.vABm P.r y P.r) 0) (resG P.k P.r (Fin.last P.r) J))
                x.1 x.2

def RDSARad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π')
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r), IsActualLevel X L →
    ∀ (y : ℂ) (Φ : RadSp P.k P.r z z' π π'),
      (((L.Ahat y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
          CutMP.dMul (CutMP.drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp))) ∧
        (((L.Ahatv y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
          CutMP.dMul (CutMP.drbF P.r) (Q.crd (Q.cmp (CutMP.vABm P.r y P.r) 0) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)))

def RDSALoc : Prop :=
  ∀ (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (y : ℂ) (f f' : (Fin r → ℂ) → E),
    (∀ c ∈ OmX r, f c = f' c) → ∀ c ∈ OmX r,
      (Q.vAB r y r).1 f c = (Q.vAB r y r).1 f' c ∧ (CutMP.vABm r y r).1 f c = (CutMP.vABm r y r).1 f' c

theorem rds_dMul_loc {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (hLoc : RDSALoc) (y : ℂ)
    (Φ Ψ : Fn k r E) (g : Mx k r) (hΦΨ : ∀ c ∈ OmX r, Φ c g = Ψ c g) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    CutMP.dMul (CutMP.drF r) (Q.crd (Q.cmp (Q.vAB r y r) 0) Φ) c g =
        CutMP.dMul (CutMP.drF r) (Q.crd (Q.cmp (Q.vAB r y r) 0) Ψ) c g ∧
      CutMP.dMul (CutMP.drbF r) (Q.crd (Q.cmp (CutMP.vABm r y r) 0) Φ) c g =
        CutMP.dMul (CutMP.drbF r) (Q.crd (Q.cmp (CutMP.vABm r y r) 0) Ψ) c g := by
  obtain ⟨h1, h2⟩ := hLoc r E y (fun c' => Φ c' g) (fun c' => Ψ c' g) (fun c' hc' => hΦΨ c' hc') c hc
  simp only [CutMP.dMul, Q.crd, Q.cmp, if_true]
  exact ⟨by rw [h1], by rw [h2]⟩

theorem rDSOpA_of_parts (hP : RDSPolyProp) (hG : RDSAGrp) (hR : RDSARad) (hLoc : RDSALoc) : RDSOpA := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' _ Y _ _ _ _
  subst hz hz' hπ hπ'
  obtain ⟨hPl, -, hL, -⟩ := hD
  obtain ⟨Θ, Θv, ⟨o, κ, hpo⟩, hpv, hc, hcv, hres⟩ := hG Wp Wq P D hPl Y
  refine ⟨Θ, hP P.k P.r Wp Wq D o κ Θ hpo hc, ?_⟩
  intro J hJ Φ hΦ x hx
  have e := congrFun (congrFun (hR Wp Wq P D.z D.z' D.π D.π' X L hL Y Φ).1 x.1) x.2
  refine ((hres J hJ x hx).1).trans (Eq.trans ?_ e.symm)
  obtain ⟨hc1, hg1, hG1⟩ := hx
  exact (rds_dMul_loc hLoc Y _ _ x.2
    (fun c' hc' => (hΦ (c', x.2) ⟨hc', hg1, hG1⟩).symm) x.1 hc1).1

theorem rDSOpAv_of_parts (hP : RDSPolyProp) (hG : RDSAGrp) (hR : RDSARad) (hLoc : RDSALoc) : RDSOpAv := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' _ Y _ _ _ _
  subst hz hz' hπ hπ'
  obtain ⟨hPl, -, hL, -⟩ := hD
  obtain ⟨Θ, Θv, hpa, ⟨o, κ, hpo⟩, hca, hc, hres⟩ := hG Wp Wq P D hPl (Y + 1)
  refine ⟨Θv, hP P.k P.r Wp Wq D o κ Θv hpo hc, ?_⟩
  intro J hJ Φ hΦ x hx
  have e := congrFun (congrFun (hR Wp Wq P D.z D.z' D.π D.π' X L hL (Y + 1) Φ).2 x.1) x.2
  refine ((hres J hJ x hx).2).trans (Eq.trans ?_ e.symm)
  obtain ⟨hc1, hg1, hG1⟩ := hx
  exact (rds_dMul_loc hLoc (Y + 1) _ _ x.2
    (fun c' hc' => (hΦ (c', x.2) ⟨hc', hg1, hG1⟩).symm) x.1 hc1).2

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpR
section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section comp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def dcomp (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) : B.DiffOp k r Wp Wq :=
  Θ.map fun T =>
    { coef := fun x => (T0.coef x).comp (T.coef x)
      coefAdj := fun x => (T.coefAdj x).comp (T0.coefAdj x)
      word := T.word
      word_lie := T.word_lie
      adj_id := fun x A B => by
        simp only [ContinuousLinearMap.comp_apply]
        rw [T0.adj_id, T.adj_id] }

theorem opApply_dcomp (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.opApply (dcomp T0 Θ) F g = T0.coef g (B.opApply Θ F g) := by
  unfold B.opApply dcomp
  rw [map_list_sum, List.map_map, List.map_map]
  rfl

def Good0 (D : B.RealPlaceData k r Wp Wq) (T0 : B.DTerm k r Wp Wq) : Prop :=
  T0.word = [] ∧ B.CkOn ⊤ (B.GPos D) T0.coef ∧ B.CkOn ⊤ (B.GPos D) T0.coefAdj ∧
    (∀ p, D.inSS p → ∀ g ∈ B.GPos D, ∀ A : Wq →L[ℂ] Wp,
      T0.coef g ((D.π (Matrix.of p.1.1)).comp (A.comp (D.π' (Matrix.of p.2.1)⁻¹))) =
        (D.π (Matrix.of p.1.1)).comp ((T0.coef (B.sgs p g) A).comp (D.π' (Matrix.of p.2.1)⁻¹))) ∧
    ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C d : ℝ, 0 ≤ d ∧ ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g →
        ‖B.dLR u v T0.coef g‖ ≤ C * B.gN g ^ d ∧ ‖B.dLR u v T0.coefAdj g‖ ≤ C * B.gN g ^ d

end comp

def RDSOpRGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (D : B.RealPlaceData k r Wp Wq)
    (Y σ : ℂ), ∃ Θ : B.DiffOp k r Wp Wq, OpProp1 D Θ ∧
      ∀ J : B.Mat k r → (Wq →L[ℂ] Wp), J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
        ∀ x ∈ DomR k r D.z D.z', resG k r (Fin.last r) (B.opApply Θ J) x.1 x.2 =
          σ • CutMP.rhGrp k r D.z D.z' Y (resG k r (Fin.last r) J) x.1 x.2

def RDSOpRvGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (D : B.RealPlaceData k r Wp Wq)
    (Y σ : ℂ), ∃ Θ : B.DiffOp k r Wp Wq, OpProp1 D Θ ∧
      ∀ J : B.Mat k r → (Wq →L[ℂ] Wp), J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
        ∀ x ∈ DomR k r D.z D.z', resG k r (Fin.last r) (B.opApply Θ J) x.1 x.2 =
          σ • CutMP.rhvGrp k r D.z D.z' Y (resG k r (Fin.last r) J) x.1 x.2

def RDSOpX : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Y : ℂ, Y ∈ st.inv → ∃ T0 : B.DTerm P.k P.r Wp Wq, Good0 D T0 ∧
      ∀ (Ψ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z',
        (((GiR L * st.xi Y).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          T0.coef (wCell P.k P.r (Fin.last P.r) x.1 * x.2) ((Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)

def RDSRhR : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → ∃ σ : ℂ, ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') →
      ∀ Φ : RadSp P.k P.r z z' π π',
        (∀ x ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) J x.1 x.2) →
        ∀ x ∈ DomR P.k P.r z z',
          (((RhR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
            σ • CutMP.rhGrp P.k P.r z z' Y (resG P.k P.r (Fin.last P.r) J) x.1 x.2

def RDSRhvR : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → ∃ σ : ℂ, ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') →
      ∀ Φ : RadSp P.k P.r z z' π π',
        (∀ x ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) J x.1 x.2) →
        ∀ x ∈ DomR P.k P.r z z',
          (((RhvR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
            σ • CutMP.rhvGrp P.k P.r z z' Y (resG P.k P.r (Fin.last P.r) J) x.1 x.2

def RDSComp0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (D : B.RealPlaceData k r Wp Wq)
    (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq), Good0 D T0 → OpProp1 D Θ → OpProp1 D (dcomp T0 Θ)

theorem rDSOpR_of_parts (hG : RDSOpRGrp) (hX : RDSOpX) (hR : RDSRhR) (hC : RDSComp0) : RDSOpR := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hY _ hY0 _
  obtain ⟨σ, hσ⟩ := hR Wp Wq P z z' π π' X μ L st l0 hD hl1 hl2 hr Y hY
  obtain ⟨T0, hT0, hT0e⟩ := hX Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hY0
  subst hz hz' hπ hπ'
  obtain ⟨Θ, hΘ, hΘe⟩ := hG Wp Wq P.k P.r D Y σ
  refine ⟨dcomp T0 Θ, hC Wp Wq P.k P.r D T0 Θ hT0 hΘ, ?_⟩
  intro J hJ Φ hΦ x hx
  have e1 : (((GiR L * st.xi Y * RhR L st Y).1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp))
      x.1 x.2 = (((GiR L * st.xi Y).1 ((RhR L st Y).1 Φ) : RadSp P.k P.r D.z D.z' D.π D.π') :
        Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, hT0e _ x hx, hσ J hJ Φ hΦ x hx, ← hΘe J hJ x hx]
  simp only [resG, opApply_dcomp, map_smul]

theorem rDSOpRv_of_parts (hG : RDSOpRvGrp) (hX : RDSOpX) (hR : RDSRhvR) (hC : RDSComp0) : RDSOpRv := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hY _ _ hY1
  have hY' : star (Y + 1) = Y + 1 := by rw [star_add, hY, star_one]
  obtain ⟨σ, hσ⟩ := hR Wp Wq P z z' π π' X μ L st l0 hD hl1 hl2 hr (Y + 1) hY'
  obtain ⟨T0, hT0, hT0e⟩ := hX Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr (Y + 1) hY1
  subst hz hz' hπ hπ'
  obtain ⟨Θ, hΘ, hΘe⟩ := hG Wp Wq P.k P.r D (Y + 1) σ
  refine ⟨dcomp T0 Θ, hC Wp Wq P.k P.r D T0 Θ hT0 hΘ, ?_⟩
  intro J hJ Φ hΦ x hx
  have e1 : (((GiR L * st.xi (Y + 1) * RhvR L st (Y + 1)).1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') :
      Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (((GiR L * st.xi (Y + 1)).1 ((RhvR L st (Y + 1)).1 Φ) :
        RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, hT0e _ x hx, hσ J hJ Φ hΦ x hx, ← hΘe J hJ x hx]
  simp only [resG, opApply_dcomp, map_smul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSSection
section
open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Gauge

variable {k r : ℕ}

def secGauge (k r : ℕ) (c : Fin r → ℂ) : ℂ := ∏ a : Fin r, ((‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ)

theorem secGauge_smooth : ContDiffOn ℝ ∞ (secGauge k r) (OmX r) := by
  unfold secGauge
  apply contDiffOn_prod
  intro a _ x hx
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => ‖c a‖) x :=
    (contDiffAt_norm ℝ (hx a)).comp x (contDiff_apply ℝ (fun _ => ℂ) a).contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt).comp x (h1.pow _)

theorem secGauge_ne {c : Fin r → ℂ} (hc : c ∈ OmX r) : secGauge k r c ≠ 0 := by
  unfold secGauge
  refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_)
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc a)))

theorem secGauge_inv_smooth : ContDiffOn ℝ ∞ (fun c => (secGauge k r c)⁻¹) (OmX r) := secGauge_smooth.inv (fun c hc => secGauge_ne hc)

theorem resG_last_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : Mx k r → E) (c : Fin r → ℂ)
    (g : Mx k r) : resG k r (Fin.last r) J c g = secGauge k r c • J (wCell k r (Fin.last r) c * g) := by
  unfold resG secGauge
  congr 1
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [if_pos (show (a : ℕ) < (Fin.last r : ℕ) from a.isLt)]

end Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem spectral_section_identity : RDSSection := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ Ψ _
  classical
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  obtain ⟨h0, hs, he⟩ := Ψ.2

  let Φf : Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g => (secGauge P.k P.r c)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g
  have hmem : Φf ∈ RadSp P.k P.r z z' π π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = 0
      rw [h0 x hx, smul_zero]
    · obtain ⟨U, F, hU, hxU, hF, hΨ⟩ := hs x₀ hx₀
      have hV : IsOpen {x : (Fin P.r → ℂ) × Mx P.k P.r | x.1 ∈ OmX P.r} :=
        (Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX P.r).preimage continuous_fst
      refine ⟨U ∩ {x | x.1 ∈ OmX P.r}, fun x => (secGauge P.k P.r x.1)⁻¹ • F x, hU.inter hV, ⟨hxU, hx₀.1⟩, ?_,
        fun x hx hxG => ?_⟩
      · have hg : ContDiffOn ℝ ∞ (fun x : (Fin P.r → ℂ) × Mx P.k P.r => (secGauge P.k P.r x.1)⁻¹)
            (U ∩ {x | x.1 ∈ OmX P.r}) :=
          secGauge_inv_smooth.comp contDiff_fst.contDiffOn fun x hx => hx.2
        exact hg.smul (hF.mono Set.inter_subset_left)
      · show (secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
        rw [hΨ x hx.1 hxG]
    · show (secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
        (π h).comp (((secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
      rw [he x hx h hh h' hh', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  obtain ⟨D₀, hD₀, K, hK, hKv⟩ :=
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_descent_holds Wp Wq P.k P.r z z' π π' hz hz' Φf hmem
  have hsub : ∀ g ∈ Q.Glev P.k P.r 0 ∩ Q.OmPlus P.k P.r z z', g ∈ D₀ := by
    intro g hg
    obtain ⟨n, hn, n', hn', c, hc, g₁, hg₁, hGG, hgeq⟩ :=
      Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_cover_holds P.k P.r z z' hz hz' g hg
    have hw := (hKv c hc g₁ hg₁ hGG).1
    have hwG : Q.wCell P.k P.r (Fin.last P.r) c * g₁ ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg₁)
    rw [hgeq]
    exact hD₀.2 _ ⟨hwG, hw⟩ n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n, hn, (Matrix.one_mul n).symm⟩ n'
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n', hn', (Matrix.one_mul n').symm⟩
  have hKO : K ∈ Q.FFl P.k P.r z z' π π' 0 (Q.OmPlus P.k P.r z z') := by
    obtain ⟨hs', hL, hRt, hW⟩ := hK
    exact ⟨fun g₀ hg₀ => hs' g₀ ⟨hg₀.1, hsub g₀ hg₀⟩, fun g hg n hn => hL g ⟨hg.1, hsub g hg⟩ n hn,
      fun g hg n hn => hRt g ⟨hg.1, hsub g hg⟩ n hn, fun g hg h hh h' hh' => hW g ⟨hg.1, hsub g hg⟩ h hh h' hh'⟩
  refine ⟨K, ?_, fun x hx => ?_⟩
  · rw [rdb_ffl_om_eq]; exact hKO
  · rw [resG_last_eq, (hKv x.1 hx.1 x.2 hx.2.1 hx.2.2).2]
    show _ = secGauge P.k P.r x.1 • ((secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
    rw [smul_smul, mul_inv_cancel₀ (secGauge_ne hx.1), one_smul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

