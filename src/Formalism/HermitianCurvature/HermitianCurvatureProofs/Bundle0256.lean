module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeib
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def wl (A B : ℂ) : ℂ →L[ℝ] ℂ := A • ContinuousLinearMap.id ℝ ℂ + B • Complex.conjCLE.toContinuousLinearMap

theorem wl_apply (A B h : ℂ) : wl A B h = A * h + B * conj h := rfl

section Slice

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wOp (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) : Module.End ℂ (RadSp k r z z' π π') :=
  (js.map (X.op l)).prod

def dT (X : ActualOps k r z z' π π') (l : Fin r) : Module.End ℂ (RadSp k r z z' π π') := X.op l 2 * X.op l 0

def dTb (X : ActualOps k r z z' π π') (l : Fin r) : Module.End ℂ (RadSp k r z z' π π') := X.op l 5 * X.op l 3

def SlDom (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (Φ : RadSp k r z z' π π') : Prop :=
  ∀ t0 : ℂ, t0 ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ ∃ F : Cf r l.succ → ℝ, Integrable F ∧
    ∀ t ∈ Metric.ball t0 ε, ∀ c' : Cf r l.succ,
      ‖wtI l.succ c' * pairAt μ Φ Φ (glue l.succ (Function.update c l t) c')‖ ≤ F c'

def SliceGood (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ)
    (Φ : RadSp k r z z' π π') : Prop :=
  Φ ∈ lcSub (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') ∧
    ∀ js : List (Fin 6), SlDom μ l c (wOp X l js Φ)

end Slice

def PairAtDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (l : Fin r), ∀ (Φ Ψ : RadSp k r z z' π π'),
    Φ ∈ lcSub (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') →
    Ψ ∈ lcSub (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') →
    ∀ c ∈ OmX r, ∀ (c' : Cf r l.succ) (t : ℂ), t ≠ 0 →
      HasFDerivAt (fun s => pairAt μ Φ Ψ (glue l.succ (Function.update c l s) c'))
        (wl (pairAt μ (dT X l Φ) Ψ (glue l.succ (Function.update c l t) c') +
              pairAt μ Φ (dTb X l Ψ) (glue l.succ (Function.update c l t) c'))
            (pairAt μ (dTb X l Φ) Ψ (glue l.succ (Function.update c l t) c') +
              pairAt μ Φ (dT X l Ψ) (glue l.succ (Function.update c l t) c'))) t

def OuterLeib : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (l : Fin r), ∀ (S : Type) [Fintype S] [DecidableEq S] (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ), c ∈ OmX r →
    (∀ b, SliceGood X μ l c (u b)) → (∀ b, SliceGood X μ l c (v b)) → ∀ t : ℂ, t ≠ 0 →
      HasFDerivAt (fun s => form μ l.succ u v (Function.update c l s))
        (wl (form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
              form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t))
            (form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
              form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t))) t

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERD
section
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Wave

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def wvG (z z' : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => fsv s (Dmin k r z z' g ⟨1, by omega⟩) • F g

variable [FiniteDimensional ℂ Wq]

def NiceAll (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ JC.NiceCoef D ε F

end Wave

def RDWave : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (hr : 0 < r) (ε : ℝ) (s : ℂ) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
    (JC.NiceCoef D ε G → JC.NiceCoef D ε (wvG D.z D.z' s G)) ∧
    ∀ y ∈ DomR k r D.z D.z', resG k r (Fin.last r) (B.JF D (wvG D.z D.z' s G)) y.1 y.2 =
      fsv s (y.1 ⟨0, hr⟩) • resG k r (Fin.last r) (B.JF D G) y.1 y.2

def RDBeta : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ : Measure (Mt k r)), B.IsHaarOn (Glev k r (Fin.last r)) μ →
    ∃ C1 : ℂ, C1 ≠ 0 ∧ ∀ (F H : B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Ψ : RadSp k r D.z D.z' D.π D.π'),
      (∀ (A : ℝ) (m : ℕ), B.InCC A m F) → (∀ (A : ℝ) (m : ℕ), B.InCC A m H) →
      (∀ y ∈ DomR k r D.z D.z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D F) y.1 y.2) →
      (∀ y ∈ DomR k r D.z D.z', (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D H) y.1 y.2) →
      ∀ c : Fin r → ℂ, LocFacts₂ μ 0 Φ Ψ c = C1 * B.beta D F H

def RDBdd : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F H : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ (A : ℝ) (m : ℕ), B.InCC A m F) → (∀ (A : ℝ) (m : ℕ), B.InCC A m H) →
    ∃ K : ℝ, ∀ s : ℂ, ‖B.beta D (wvG D.z D.z' s F) H‖ ≤ K

def RDHyp (Q : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], B.RealPlaceData k r Wp Wq → Prop) : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    Q P.k P.r Wp Wq D

def RDIdent : Prop :=
  RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∃ Θ : Fin 4 → (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp),
      (∀ j F, NiceAll D F → NiceAll D (Θ j F)) ∧
      ∀ (s : ℂ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' →
        s * B.beta D (wvG D.z D.z' s F) F' =
          B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F') - B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')

section Second

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def RDOpsProp (D : B.RealPlaceData k r Wp Wq) (Θ : Fin 4 → B.DiffOp k r Wp Wq) : Prop :=
  ∀ j, B.SmoothCoef (B.GPos D) (Θ j) ∧ B.Commutes D (B.GPos D) (Θ j) ∧
    (∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 ≤ d ∧ B.PolyCoef D ε d (B.opOrder (Θ j) + 5) (Θ j)) ∧
    ∀ F, NiceAll D F → NiceAll D (B.opApply (Θ j) F) ∧ NiceAll D (B.opAdj (Θ j) F)

end Second

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSESiteOpsC
section
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def SiteOpsWaveJC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (j : Fin 6), (j = 1 ∨ j = 4) →
    ∀ (Φ : RadSp P.k P.r z z' π π'), Φ ∈ waveJ P z z' π π' D l → X.op l j Φ ∈ waveJ P z z' π π' D l

namespace SiteC

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_mul_inv (Bs : B.RealPlaceData k r Wp Wq) (ι : B.Mat k r → ℂ)
    (hι : ∀ p : B.SS k r, Bs.inSS p → ∀ g, ι (B.sgs p g) = ι g) (G : B.Mat k r → (Wq →L[ℂ] Wp))
    (h : B.Mat k r) : B.JF Bs (fun g => ι g • G g) h = ι h • B.JF Bs G h := by
  unfold B.JF besselJ
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [B7.ae_inSS Bs] with p hp
  have hp' := hι p hp h
  simp only [B.sgs] at hp'
  simp only [hp', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm (ι h)]

theorem first_minor_double_coset_invariant (Bs : B.RealPlaceData k r Wp Wq) (p : B.SS k r) (hp : Bs.inSS p) (g : B.Mat k r) :
    Dmin k r Bs.z Bs.z' (B.sgs p g) ⟨1, by omega⟩ = Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩ :=
  Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _

private theorem dmin_one_eq_herm_mulVec_fvec {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Dmin k r z z' g ⟨1, by omega⟩ = herm (Hpk k r) (g *ᵥ fvec k r z' 0) (fvec k r z 0) := by
  unfold Dmin
  erw [Matrix.det_fin_one]
  rfl

theorem first_minor_good_function (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    Formalism.FourierDecayAlt.P.JCx2.mnGood Bs ε (fun g => Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩) := by
  refine JCx2.mn_good_congr (c := fun g => herm (Hpk k r) (g *ᵥ fvec k r Bs.z' 0) (fvec k r Bs.z 0)) ?_
    (JCx2.mn_good_herm _ _)
  intro g _
  rw [dmin_one_eq_herm_mulVec_fvec]

theorem first_minor_conj_good_function (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    Formalism.FourierDecayAlt.P.JCx2.mnGood Bs ε (fun g => star (Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩)) := by
  refine JCx2.mn_good_congr
    (c := fun g => (Complex.conjCLE.toContinuousLinearMap.comp
      (JCx2.mnLinHerm (k := k) (r := r) (fvec k r Bs.z' 0) (fvec k r Bs.z 0))) g) ?_
    (JCx2.mn_good_lin _)
  intro g _
  rw [dmin_one_eq_herm_mulVec_fvec]
  simp [JCx2.mnLinHerm]

private theorem wCell_succ_mulVec_bvec_eI_zero_eq_smul {k r : ℕ} (hr : 0 < r) (c : Fin r → ℂ) :
    ∀ (i : ℕ) (hi : i < r), wCell k r ⟨i + 1, by omega⟩ c *ᵥ bvec (eI k r ⟨0, hr⟩) =
      c ⟨0, hr⟩ • bvec (esI k r ⟨0, hr⟩) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have h := Qx6.wCell_succ (k := k) (⟨0, hr⟩ : Fin r) c
    simp only [Fin.succ_mk, Fin.castSucc_mk, Fin.mk_zero, Qx6.wCell_zero, one_mul] at h
    rw [h, Qx4.w1_mulVec_bvec_eI]
  | succ n ih =>
    intro hi
    have h := Qx6.wCell_succ (k := k) (⟨n + 1, hi⟩ : Fin r) c
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h
    have h1 : eI k r ⟨0, hr⟩ ≠ eI k r ⟨n + 1, hi⟩ := by
      simp [eI, Fin.ext_iff]
    have h2 : eI k r ⟨0, hr⟩ ≠ esI k r ⟨n + 1, hi⟩ := by
      simp [eI, esI, Fin.ext_iff]; omega
    rw [h, ← Matrix.mulVec_mulVec, Qx3.reflection_fixes_basis_vector _ _ h1 h2, ih (by omega)]

theorem first_minor_at_cell_eq_coefficient {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hr : 0 < r)
    (c : Fin r → ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, by omega⟩ = c ⟨0, hr⟩ := by
  rw [dmin_one_eq_herm_mulVec_fvec]
  have hf : ∀ w : Fin (2 * r + k + 1) → ℂ, fvec k r w 0 = bvec (eI k r ⟨0, hr⟩) := by
    intro w; simp [fvec, hr]
  rw [hf, hf, ← Matrix.mulVec_mulVec, (hg.2 ⟨0, hr⟩ (by simp; omega)).1]
  have h3 := wCell_succ_mulVec_bvec_eI_zero_eq_smul (k := k) hr c (r - 1) (by omega)
  have e : (⟨r - 1 + 1, by omega⟩ : Fin (r + 1)) = Fin.last r := by ext; simp; omega
  rw [e] at h3
  rw [h3]
  simp only [herm, bvec, eI, esI]
  simp
  rw [Matrix.mulVec_smul, Pi.smul_apply, Matrix.mulVec_single_one]
  simp [Hpk, hr]

end SiteC

open SiteC in
theorem site_operators_preserve_orbital : SiteOpsWaveJC := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D _ _ _ hz hz' hπ hπ' l hl j hj Φ hΦ
  subst hz hz' hπ hπ'
  have hr : 0 < P.r := by have := l.2; omega
  have hl' : l = ⟨0, hr⟩ := Fin.ext hl
  have key : ∀ Ψ, IsWaveJ P D.z D.z' D.π D.π' D l Ψ → IsWaveJ P D.z D.z' D.π D.π' D l (X.op l j Ψ) := by
    rintro Ψ ⟨hlc, s, ε, G, hε, hG, hΨ⟩
    rcases hj with rfl | rfl
    · refine ⟨?_, s, ε, fun g => Dmin P.k P.r D.z D.z' g ⟨1, by omega⟩ • G g, hε, first_minor_good_function D ε G hG, ?_⟩
      · intro c hc
        obtain ⟨U, hU, hcU, K, hK, hKs, hv⟩ := hlc c hc
        refine ⟨U, hU, hcU, K, hK, hKs, fun c' hc' g hg hgK => ?_⟩
        rw [X.op_apply]
        simp [crd, opL, cOp, hv c' hc' g hg hgK]
      · intro y hy
        rw [X.op_apply]
        simp only [crd, opL, cOp]
        rw [hΨ y hy]
        simp only [resG]
        rw [jf_mul_inv D _ (fun p hp g => BigCellZetaMinors.dmin_sgs D hp g _) G,
          first_minor_at_cell_eq_coefficient D.z_mem D.z'_mem hr y.1 hy.2.1, hl']
        simp only [smul_smul]
        ring_nf
    · refine ⟨?_, s, ε, fun g => star (Dmin P.k P.r D.z D.z' g ⟨1, by omega⟩) • G g, hε, first_minor_conj_good_function D ε G hG, ?_⟩
      · intro c hc
        obtain ⟨U, hU, hcU, K, hK, hKs, hv⟩ := hlc c hc
        refine ⟨U, hU, hcU, K, hK, hKs, fun c' hc' g hg hgK => ?_⟩
        rw [X.op_apply]
        simp [crd, opL, cbOp, hv c' hc' g hg hgK]
      · intro y hy
        rw [X.op_apply]
        simp only [crd, opL, cbOp]
        rw [hΨ y hy]
        simp only [resG]
        rw [jf_mul_inv D _ (fun p hp g => by rw [BigCellZetaMinors.dmin_sgs D hp g _]) G,
          first_minor_at_cell_eq_coefficient D.z_mem D.z'_mem hr y.1 hy.2.1, hl']
        simp only [smul_smul]
        ring_nf
  refine Submodule.span_induction (p := fun Φ _ => X.op l j Φ ∈ waveJ P D.z D.z' D.π D.π' D l) ?_ ?_ ?_ ?_ hΦ
  · intro x hx
    exact Submodule.subset_span (key x hx)
  · simp
  · intro x y _ _ hx hy
    rw [map_add (f := _)]
    exact add_mem hx hy
  · intro a x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

theorem site_multiplication_orbital : SiteMulWaveJ := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl Φ hΦ
  exact ⟨site_operators_preserve_orbital Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl 1 (Or.inl rfl) Φ hΦ,
    site_operators_preserve_orbital Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl 4 (Or.inr rfl) Φ hΦ⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWaveOut
section
open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S]
  [DecidableEq S]

theorem waveOut_pairAt_left (μ : Measure (Mt k r)) {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → ℂ}
    (hW : multiplicationOperator W (fun c _ => m c)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (W Φ) Ψ c = m c * pairAt μ Φ Ψ c := by
  unfold pairAt
  have e : ∀ g : Mt k r, B.hsInner ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) =
      m c * B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) := by
    intro g
    have h1 := hW Φ c (Matrix.of g)
    simp only at h1
    rw [h1, hsInner_smul_left']
  simp_rw [e]
  exact integral_const_mul _ _

theorem waveOut_pairAt_self (μ : Measure (Mt k r)) {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → ℂ}
    (hW : multiplicationOperator W (fun c _ => m c)) (hm : ∀ c, ‖m c‖ = 1) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (W Φ) (W Φ) c = pairAt μ Φ Φ c := by
  unfold pairAt
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have h1 := hW Φ c (Matrix.of g)
  simp only at h1
  show B.hsInner ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = _
  rw [h1, hsInner_smul_left', hsInner_smul_right', ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]
  simp

theorem waveOut_glue (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  unfold glue
  rw [dite_eq_right (by simp)]
  first
  | exact Function.update_self l t c
  | simp

theorem waveOut_dens (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) {W : Module.End ℂ (RadSp k r z z' π π')}
    (hW : multiplicationOperator W (fun c' _ => fsv s (c' l))) (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    Dens μ l (fun b => W (u b)) v c t = fsv s t * Dens μ l u v c t := by
  have e : (fun c' : Cf r l.succ => ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (W (u a)) (v a) (glue l.succ (Function.update c l t) c')) =
      fun c' => fsv s t * (((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l t) c')) := by
    funext c'
    have hp : ∀ a, pairAt μ (W (u a)) (v a) (glue l.succ (Function.update c l t) c') =
        fsv s t * pairAt μ (u a) (v a) (glue l.succ (Function.update c l t) c') := by
      intro a
      rw [waveOut_pairAt_left (m := fun c' => fsv s (c' l)) μ hW, waveOut_glue]
    simp only [hp, ← Finset.mul_sum]
    ring
  simp only [Dens, form]
  rw [e, integral_const_mul]
  ring

end Wave

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWdExpand
section
open Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem wdx_diff {n m : ℕ} {f : ℂ → ℂ} (hf : ContDiffOn ℝ n f {t | t ≠ 0}) (hm : m < n) {t : ℂ} (ht : t ≠ 0) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ m f) t := by
  have hs : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne
  have hd := hf.differentiableOn_iteratedFDerivWithin (by exact_mod_cast hm) hs.uniqueDiffOn
  have hdt : DifferentiableAt ℝ (iteratedFDerivWithin ℝ m f {t | t ≠ 0}) t :=
    (hd t ht).differentiableAt (hs.mem_nhds ht)
  exact hdt.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hs.mem_nhds ht)
    fun s hs' => (iteratedFDerivWithin_of_isOpen m hs hs').symm)

theorem wdx_hasFDerivAt_iter {m : ℕ} {f : ℂ → ℂ} {t : ℂ}
    (hd : DifferentiableAt ℝ (iteratedFDeriv ℝ m f) t) (w : Fin m → ℂ) :
    HasFDerivAt (fun s => iteratedFDeriv ℝ m f s w)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℂ) ℂ w).comp (fderiv ℝ (iteratedFDeriv ℝ m f) t)) t := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℂ) ℂ w).hasFDerivAt.comp t hd.hasFDerivAt

theorem wdx_step_eval {m : ℕ} {f : ℂ → ℂ} {t : ℂ} (h : ℂ) (w : Fin m → ℂ) :
    (fderiv ℝ (iteratedFDeriv ℝ m f) t h) w = iteratedFDeriv ℝ (m + 1) f t (Fin.cons h w) := by
  rw [iteratedFDeriv_succ_apply_left]
  simp

theorem word_expansion : WdExpand := by
  intro n f bs hlen hf
  induction bs with
  | nil =>
    refine ⟨1, fun _ => 1, fun _ => Fin.elim0, fun _ => by simp, fun t _ => ?_⟩
    simp [WD]
  | cons b bs ih =>
    have hlen' : bs.length ≤ n := by simp at hlen; omega
    have hlt : bs.length < n := by simp at hlen; omega
    obtain ⟨K, a, v, -, hv⟩ := ih hlen'
    have hs : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne
    have hder : ∀ t : ℂ, t ≠ 0 → ∀ h : ℂ, fderiv ℝ (WD bs f) t h =
        ∑ i, a i * iteratedFDeriv ℝ (bs.length + 1) f t (Fin.cons h (v i)) := by
      intro t ht h
      have heq : WD bs f =ᶠ[𝓝 t] fun s => ∑ i, a i * iteratedFDeriv ℝ bs.length f s (v i) :=
        Filter.eventuallyEq_of_mem (hs.mem_nhds ht) fun s hs' => hv s hs'
      have hd := wdx_diff hf hlt ht
      have hH : HasFDerivAt (fun s => ∑ i, a i * iteratedFDeriv ℝ bs.length f s (v i))
          (∑ i, a i • ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin bs.length => ℂ) ℂ (v i)).comp
            (fderiv ℝ (iteratedFDeriv ℝ bs.length f) t))) t := by
        first
          | exact HasFDerivAt.fun_sum fun i _ => (wdx_hasFDerivAt_iter hd (v i)).const_mul (a i)
          | (convert HasFDerivAt.sum (u := Finset.univ)
              (fun i _ => (wdx_hasFDerivAt_iter hd (v i)).const_mul (a i)) using 1
             ext s
             simp)
      rw [heq.fderiv_eq, hH.fderiv]
      simp [wdx_step_eval]
    refine ⟨K + K, Fin.append (fun i => (1 / 2 : ℂ) * a i)
        (fun i => (1 / 2 : ℂ) * ((if b then -Complex.I else Complex.I) * a i)),
      Fin.append (fun i => Fin.cons (1 : ℂ) (v i)) (fun i => Fin.cons Complex.I (v i)),
      fun h => by simp at h, fun t ht => ?_⟩
    show wirt b (WD bs f) t = ∑ i : Fin (K + K), _ * iteratedFDeriv ℝ (bs.length + 1) f t _
    unfold wirt
    rw [hder t ht, hder t ht, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, mul_add, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring

end Formalism.FourierDecayAlt.P.CutSE
end
end

