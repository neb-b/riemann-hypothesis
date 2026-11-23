module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0013

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeVIndep
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.DataInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7}

variable (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

def VIndepAt (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h₁ h₁' h₂ h₂', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₁ h₁' →
      IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₂ h₂' →
      (X.piU u h₁⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₁')) =
        (X.piU u h₂⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₂'))

end Formalism.L2.SG.Pf.Carrier
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.JointPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def OOQuot (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) → ∀ y : ∀ v, X.Vloc u' v,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.tensU u' y) =
      X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v))

def PlaceJ (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ (v : InfinitePlace X.B.I.F) (y : X.Vloc u' v),
      X.piLoc u v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v h⁻¹)
        ((haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
          Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))
          (X.piLoc u' v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v h') y)) =
      P.eP v
        (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
          Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
            (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p)))
          ((P.eQ v).symm y))

theorem jointTensor_of_steps (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : OOQuot X u u' νq νl) (hP : PlaceJ P sc i0 i0' νl) : P.JointTensor sc i0 i0' νq := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.JointTensor
  intro p w hpw hγ hG h h' hF x
  rw [X.tensU_equiv, hQ w hγ hG, X.tensU_equiv]
  · exact congrArg (fun f => X.tensU u f) (funext fun v => hP p w hpw hγ hG h h' hF v (x v))
  all_goals
    first
    | exact hF.2.1
    | (intro v y hy
       have h1 := hF.1 v y hy
       nth_rewrite 1 [← h1]
       rw [Matrix.mulVec_mulVec, Pi.inv_apply]
       simp only [uMat]
       rw [← Units.val_mul, ← MulMemClass.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Units.val_one,
         Matrix.one_mulVec])

end Formalism.L2.SG.Pf.Carrier.JointPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HermitianMatrixIdentities
section
noncomputable section

open Matrix Formalism.QuantumDeterminants

namespace Formalism.L2.SG.HermitianMatrixIdentities

variable {k r : ℕ}

theorem hpk_isUnit : IsUnit (Hpk k r).det := by
  exact Formalism.FourierDecayAlt.P.B2x5.isUnit_det_Hpk k r

theorem star_dot_conjT' {n m : Type*} [Fintype n] [Fintype m] (Q : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (Qᴴ *ᵥ y) = star (Q *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem herm_sum_left (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ) :
    herm H (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i * herm H (v i) w := by
  classical
  unfold herm
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mulVec_add, dotProduct_add, ih,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_sum_right (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (v : Fin (2 * r + k + 1) → ℂ) (w : ι → Fin (2 * r + k + 1) → ℂ) :
    herm H v (∑ i ∈ s, c i • w i) = ∑ i ∈ s, star (c i) * herm H v (w i) := by
  classical
  unfold herm
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, star_add, add_dotProduct, ih, star_smul,
    smul_dotProduct, smul_eq_mul]

private lemma isUnit_det_of_mem_UH_Hpk' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have hH := hpk_isUnit (k := k) (r := r)
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  have h3 : gᴴ.det * g.det * (Hpk k r).det = 1 * (Hpk k r).det := by linear_combination h2
  have h4 := mul_right_cancel₀ hH.ne_zero h3
  exact isUnit_iff_exists.mpr ⟨gᴴ.det, by rw [mul_comm]; exact h4, h4⟩

theorem herm_UH {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hρ : ρ ∈ UH (Hpk k r))
    (x y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (ρ *ᵥ x) y = herm (Hpk k r) x (ρ⁻¹ *ᵥ y) := by
  have hρ' : ρᴴ * Hpk k r * ρ = Hpk k r := hρ
  have hdet := isUnit_det_of_mem_UH_Hpk' hρ
  have hinv : (ρ⁻¹)ᴴ * ρᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one]
  have hkey : (ρ⁻¹)ᴴ * Hpk k r = Hpk k r * ρ := by
    calc (ρ⁻¹)ᴴ * Hpk k r = (ρ⁻¹)ᴴ * (ρᴴ * Hpk k r * ρ) := by rw [hρ']
      _ = ((ρ⁻¹)ᴴ * ρᴴ) * Hpk k r * ρ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * ρ := by rw [hinv, Matrix.one_mul]
  unfold herm
  rw [← star_dot_conjT' (ρ⁻¹) y (Hpk k r *ᵥ x)]
  simp only [Matrix.mulVec_mulVec, hkey]

private lemma mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.FourierDecayAlt.C2.StdZ k r z)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) (b : Fin (r + 1)) :
    m *ᵥ fvec k r z b = ∑ c, Formalism.FourierDecayAlt.C2.uMap k r z m c b • fvec k r z c := by
  have hF := Formalism.QuantumDeterminants.N_F hz.1 hm
  rw [Formalism.FourierDecayAlt.P.C2x5.uMap_eq hz m _ (Formalism.FourierDecayAlt.P.C2x5.colEq hF)]
  exact Formalism.FourierDecayAlt.P.C2x5.colEq hF b

theorem zhat_uMap {z z' : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.FourierDecayAlt.C2.StdZ k r z) (hz' : Formalism.FourierDecayAlt.C2.StdZ k r z')
    {δ ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hδ : δ ∈ UH (Hpk k r)) (hρ : ρ ∈ Nset k r)
    (hρ' : δ⁻¹ * ρ * δ ∈ Nset k r) :
    Zhat k r z z' δ * Formalism.FourierDecayAlt.C2.uMap k r z' (δ⁻¹ * ρ * δ) =
      (Formalism.FourierDecayAlt.C2.uMap k r z ρ⁻¹)ᴴ * Zhat k r z z' δ := by
  have hδd := isUnit_det_of_mem_UH_Hpk' hδ
  have hρU : ρ ∈ UH (Hpk k r) := hρ.1
  have hρi : ρ⁻¹ ∈ Nset k r := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hρ
  have hδs : δ * (δ⁻¹ * ρ * δ) = ρ * δ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hδd, Matrix.one_mul]
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]

  have e1 : ∑ c, Zhat k r z z' δ a c * Formalism.FourierDecayAlt.C2.uMap k r z' (δ⁻¹ * ρ * δ) c b =
      herm (Hpk k r) (δ *ᵥ ((δ⁻¹ * ρ * δ) *ᵥ fvec k r z' b)) (fvec k r z a) := by
    rw [mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset hz' hρ' b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rw [herm_sum_left]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Zhat]
    ring
  have e2 : ∑ c, (Formalism.FourierDecayAlt.C2.uMap k r z ρ⁻¹)ᴴ a c * Zhat k r z z' δ c b =
      herm (Hpk k r) (δ *ᵥ fvec k r z' b) (ρ⁻¹ *ᵥ fvec k r z a) := by
    rw [mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset hz hρi a, herm_sum_right]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Zhat, Matrix.conjTranspose_apply]
  rw [e1, e2, Matrix.mulVec_mulVec, hδs, ← Matrix.mulVec_mulVec, herm_UH hρU]

end Formalism.L2.SG.HermitianMatrixIdentities

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KernelOfEmbedding
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HS

variable {Wq Wp : Type*} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def cl (U : Wq ≃ₗᵢ[ℂ] Wq) : Wq →L[ℂ] Wq := U.toLinearIsometry.toContinuousLinearMap

theorem cl_apply (U : Wq ≃ₗᵢ[ℂ] Wq) (x : Wq) : cl U x = U x := rfl

theorem sum_inner_eq_trace {ι : Type*} [Fintype ι] (f : OrthonormalBasis ι ℂ Wq) (A B : Wq →L[ℂ] Wp) :
    ∑ i, inner ℂ (B (f i)) (A (f i)) =
      LinearMap.trace ℂ Wq (((ContinuousLinearMap.adjoint B).comp A : Wq →L[ℂ] Wq) : Wq →ₗ[ℂ] Wq) := by
  rw [LinearMap.trace_eq_sum_inner _ f]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem hsInner_comp_isom (A B : Wq →L[ℂ] Wp) (U : Wq ≃ₗᵢ[ℂ] Wq) :
    Formalism.MainNotions.S.hsInner (A.comp (cl U)) (B.comp (cl U)) = Formalism.MainNotions.S.hsInner A B := by
  unfold Formalism.MainNotions.S.hsInner
  calc ∑ i, inner ℂ ((B.comp (cl U)) (stdOrthonormalBasis ℂ Wq i)) ((A.comp (cl U)) (stdOrthonormalBasis ℂ Wq i))
      = ∑ i, inner ℂ (B (((stdOrthonormalBasis ℂ Wq).map U) i)) (A (((stdOrthonormalBasis ℂ Wq).map U) i)) := by
        simp [OrthonormalBasis.map_apply, cl_apply]
    _ = _ := sum_inner_eq_trace _ A B
    _ = ∑ i, inner ℂ (B (stdOrthonormalBasis ℂ Wq i)) (A (stdOrthonormalBasis ℂ Wq i)) :=
        (sum_inner_eq_trace _ A B).symm

theorem hsInner_smul_left (c : ℂ) (A B : Wq →L[ℂ] Wp) :
    Formalism.MainNotions.S.hsInner (c • A) B = c * Formalism.MainNotions.S.hsInner A B := by
  unfold Formalism.MainNotions.S.hsInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem hsInner_smul_right (c : ℂ) (A B : Wq →L[ℂ] Wp) :
    Formalism.MainNotions.S.hsInner A (c • B) = (starRingEnd ℂ) c * Formalism.MainNotions.S.hsInner A B := by
  unfold Formalism.MainNotions.S.hsInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

theorem hsInner_form (J₁ J₂ : Wq →L[ℂ] Wp) (c₁ c₂ : ℂ) (U₁ U₂ : Wq ≃ₗᵢ[ℂ] Wq) :
    Formalism.MainNotions.S.hsInner (c₁ • J₁.comp (cl U₁)) (c₂ • J₂.comp (cl U₂)) =
      c₁ * (starRingEnd ℂ) c₂ * Formalism.MainNotions.S.hsInner (J₁.comp (cl (U₂.symm.trans U₁))) J₂ := by
  have h : J₁.comp (cl U₁) = (J₁.comp (cl (U₂.symm.trans U₁))).comp (cl U₂) := by
    ext x
    simp [cl_apply]
  rw [hsInner_smul_left, hsInner_smul_right, h, hsInner_comp_isom]
  ring

theorem hsInner_eq_emb {Wq' Wp' : Type} [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] (A B : Wq' →L[ℂ] Wp') :
    Formalism.MainNotions.S.hsInner A B = inner ℂ (Formalism.L2.SG.PackageTie.hsEmb B) (Formalism.L2.SG.PackageTie.hsEmb A) := by
  unfold Formalism.MainNotions.S.hsInner
  simp [Formalism.L2.SG.PackageTie.hsEmb, PiLp.inner_apply]

end HS

section Stmt

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X)

abbrev amp {u u' : D.what₂.Word} (s : Formalism.L2.SG.PackageTie2.TT Y u u') : X.Vpi u' →L[ℂ] X.Vpi u :=
  ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s

abbrev row {u u' : D.what₂.Word} (s : Formalism.L2.SG.PackageTie2.TT Y u u') :=
  rowOf Y.TR (Y.cs u) (Y.cs u') s

def AmpCov : Prop :=
  ∀ (u u' : D.what₂.Word) (t : RT Y u u') (s s' : fib Y t),
    ∃ (c : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖c‖ = 1 ∧ amp Y s'.1 = c • (amp Y s.1).comp (cl U)

def PairAmpConst : Prop :=
  ∀ (u u' : D.what₂.Word) (t₁ t₂ : RT Y u u') (r r' : fib Y t₁ × fib Y t₂),
    row Y r.1.1 = row Y r.2.1 → row Y r'.1.1 = row Y r'.2.1 →
      Formalism.MainNotions.S.hsInner (amp Y r.1.1) (amp Y r.2.1) = Formalism.MainNotions.S.hsInner (amp Y r'.1.1) (amp Y r'.2.1)


variable {Y} in
def FibreCountEq (hF : FinX Y) : Prop :=
  ∀ (u u' : D.what₂.Word) (q : RP Y u u'),
    haveI := hF.fibFT q.1.1
    haveI := hF.fibFT q.1.2
    ∑ r : fib Y q.1.1 × fib Y q.1.2,
      (if row Y r.1.1 = row Y r.2.1 then Formalism.MainNotions.S.wRow D (X.Fu u') r.1.1.lam' else 0) = 1

end Stmt

section Val

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem wRow_nonneg {T : D.host.E} (F0 : Formalism.MainNotions.S.FlagG (Formalism.MainNotions.S.VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (Formalism.MainNotions.S.VS D).V) :
    0 ≤ Formalism.MainNotions.S.wRow D F0 Λ := by
  unfold Formalism.MainNotions.S.wRow; exact inv_nonneg.2 (Nat.cast_nonneg _)

theorem lam_eq_of_row {u u' : D.what₂.Word} {s₁ s₂ : Formalism.L2.SG.PackageTie2.TT Y u u'} (h : row Y s₁ = row Y s₂) :
    s₁.lam = s₂.lam ∧ s₁.lam' = s₂.lam' := by
  unfold row rowOf at h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact ⟨h.1, h.2.1⟩

theorem inner_vT {u u' : D.what₂.Word} (s₁ s₂ : Formalism.L2.SG.PackageTie2.TT Y u u') (h : row Y s₁ = row Y s₂) :
    inner ℂ (vT Y u u' s₂) (vT Y u u' s₁) =
      ((Formalism.MainNotions.S.wRow D (X.Fu u) s₁.lam * Formalism.MainNotions.S.wRow D (X.Fu u') s₁.lam' : ℝ) : ℂ) *
        Formalism.MainNotions.S.hsInner (amp Y s₁) (amp Y s₂) := by
  obtain ⟨hl, hl'⟩ := lam_eq_of_row h
  have hposition : ((⟨s₂.lam, s₂.mem⟩ : {Λ // Λ ∈ Y.what₂ u}), (⟨s₂.lam', s₂.mem'⟩ : {Λ' // Λ' ∈ Y.what₂ u'})) =
      (⟨s₁.lam, s₁.mem⟩, ⟨s₁.lam', s₁.mem'⟩) := by
    simp [hl, hl']
  have hwt : wt s₂ = wt s₁ := by unfold wt; rw [hl, hl']
  have hw2 : wt s₁ * wt s₁ = Formalism.MainNotions.S.wRow D (X.Fu u) s₁.lam * Formalism.MainNotions.S.wRow D (X.Fu u') s₁.lam' :=
    Real.mul_self_sqrt (mul_nonneg (wRow_nonneg _ _) (wRow_nonneg _ _))
  unfold vT vec
  rw [PiLp.inner_apply, Finset.sum_eq_single (⟨s₁.lam, s₁.mem⟩, ⟨s₁.lam', s₁.mem'⟩)]
  · simp only [if_true, hposition, hwt]
    rw [inner_smul_left, inner_smul_right, ← Formalism.L2.SG.Pf.KernelOfEmbedding.hsInner_eq_emb, ← hw2]
    simp only [Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  · intro b _ hb
    simp [hb]
  · intro hb; exact absurd (Finset.mem_univ _) hb

theorem pvR_eq (hF : FinX Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) {u u' : D.what₂.Word} (q : RP Y u u') :
    pvR hF u u' q = (Formalism.MainNotions.S.wRow D (X.Fu u) q.1.1.lam : ℂ) * Formalism.MainNotions.S.hsInner (amp Y q.l1) (amp Y q.l2) := by
  have key : ∀ r : fib Y q.1.1 × fib Y q.1.2,
      (if rowOf Y.TR (Y.cs u) (Y.cs u') r.1.1 = rowOf Y.TR (Y.cs u) (Y.cs u') r.2.1 then
        inner ℂ (vT Y u u' r.2.1) (vT Y u u' r.1.1) else 0) =
        (Formalism.MainNotions.S.wRow D (X.Fu u) q.1.1.lam : ℂ) * Formalism.MainNotions.S.hsInner (amp Y q.l1) (amp Y q.l2) *
          (((if row Y r.1.1 = row Y r.2.1 then Formalism.MainNotions.S.wRow D (X.Fu u') r.1.1.lam' else 0 : ℝ)) : ℂ) := by
    intro r
    by_cases hr : row Y r.1.1 = row Y r.2.1
    · have hlam : r.1.1.lam = q.1.1.lam := congrArg TermDef.Term.lam r.1.2
      have hc := hK u u' q.1.1 q.1.2 r (q.2.choose, q.2.choose_spec.choose) hr q.2.choose_spec.choose_spec
      rw [if_pos hr, if_pos hr, inner_vT _ _ hr, hc, hlam]
      simp only [RP.l1, RP.l2, Complex.ofReal_mul]
      ring
    · rw [if_neg hr, if_neg hr]
      simp
  unfold pvR
  rw [Finset.sum_congr rfl fun r _ => key r, ← Finset.mul_sum, ← Complex.ofReal_sum]
  have hn := hN u u' q
  rw [hn]
  simp

theorem pvR_form (hF : FinX Y) (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) {u u' : D.what₂.Word}
    (q : RP Y u u') (g₁ : fib Y q.1.1) (g₂ : fib Y q.1.2) :
    ∃ (c : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖c‖ = 1 ∧
      pvR hF u u' q = (Formalism.MainNotions.S.wRow D (X.Fu u) q.1.1.lam : ℂ) * c *
        Formalism.MainNotions.S.hsInner ((amp Y g₁.1).comp (cl U)) (amp Y g₂.1) := by
  obtain ⟨c₁, U₁, hc₁, h₁⟩ := hC u u' q.1.1 g₁ q.2.choose
  obtain ⟨c₂, U₂, hc₂, h₂⟩ := hC u u' q.1.2 g₂ q.2.choose_spec.choose
  refine ⟨c₁ * (starRingEnd ℂ) c₂, U₂.symm.trans U₁, by simp [hc₁, hc₂], ?_⟩
  rw [pvR_eq hF hK hN q]
  show _ * Formalism.MainNotions.S.hsInner (amp Y q.2.choose.1) (amp Y q.2.choose_spec.choose.1) = _
  rw [h₁, h₂, hsInner_form]
  ring

end Val

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OneBesselTor
section
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.L2.SG.Pf.OBT

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.FrameBoundFromBesselTorus

section Defs

variable {k r : ℕ}

def coefH (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) :
    Mx k r → (L.Wq →L[ℂ] L.Wp) :=
  fun x => P.comp ((L.σ x).comp Q)

def IsKFinPair (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) : Prop :=
  (∀ w, IsKFinHpk (k := k) (r := r) L.σ (Q w)) ∧
    (∀ x, IsKFinHpk (k := k) (r := r) L.σ (ContinuousLinearMap.adjoint P x))

def HasBData (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Λ : ℂ)
    (Φ : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Ψ : Mx k r → Measure (PairSp k r) → (L.Wq →L[ℂ] L.Wp)) : Prop :=
  (∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) →
      μᴴ * Hb k * μ = Hb k → L.J F (bigCell k r c μ) = Λ • Φ (bigCell k r c μ)) ∧
    (∀ (γ : Point ℂ (r + 1)) (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)),
      Gpt (Tz k r L.z) (Tz k r L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR →
      IsOrbQuot L g μR ν → OrbInt L F g ν = Λ • Ψ g ν)

end Defs

def RankOneTor (D : D7) (Cgf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (κ₀ : ℝ),
    0 < κ₀ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 +
        ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    ∃ (Φ : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
      (Ψ : Mx D.R.k D.R.rS → Measure (PairSp D.R.k D.R.rS) → (L.Wq →L[ℂ] L.Wp))
      (Λ₀ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℂ)
      (Λ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℝ → ℝ → ℂ),
      (∀ P Q, IsKFinPair L P Q → HasBData L (coefH L P Q) (Λ₀ P Q) Φ Ψ) ∧
      (∀ P Q (κ τ : ℝ), 0 < κ → 0 < τ → IsKFinPair L P Q →
        HasBData L (fun x => coefH L P Q (cj D.R.k D.R.rS κ τ x)) (Λ P Q κ τ) Φ Ψ) ∧
      (∀ (κ τ : ℝ), 0 < κ → 0 < τ → ∀ P Q, IsKFinPair L P Q → Λ₀ P Q ≠ 0 →
        ∃ P₁ Q₁, IsKFinPair L P₁ Q₁ ∧ Λ P₁ Q₁ κ τ ≠ 0)

section Zero

variable {k r : ℕ}

theorem isKFinHpk_zero (L : LocBessel k r) : IsKFinHpk (k := k) (r := r) L.σ (0 : L.Hs) := by
  exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx
    simp [hx]⟩

theorem J_zero (L : LocBessel k r) (g : Mx k r) : L.J (fun _ => 0) g = 0 := by
  simp [LocBessel.J, Formalism.QuantumDeterminants.besselJ]

theorem orbInt_zero (L : LocBessel k r) (g : Mx k r) (ν : Measure (PairSp k r)) :
    OrbInt L (fun _ => 0) g ν = 0 := by
  simp [OrbInt, besselIntg]

end Zero

theorem oneBesselTor_of_rankOne (D : D7) (Cgf : ℝ) (h : RankOneTor D Cgf) : OneBesselTor D Cgf := by
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hN hN' hε hgap hf
  obtain ⟨Φ, Ψ, Λ₀, Λ, h1, h2, h3⟩ := h L κ₀ hκ₀ hc hN hN' hε hgap
  obtain ⟨P, Q, hQ, hP, hfPQ⟩ := hf
  have hfeq : f = coefH L P Q := funext fun g => hfPQ g
  subst hfeq
  have hPQ : IsKFinPair L P Q := ⟨hQ, hP⟩
  by_cases h0 : Λ₀ P Q = 0
  · refine ⟨fun _ => 0, 1, one_ne_zero, ⟨0, 0, fun w => by simpa using isKFinHpk_zero L,
      fun x => by simpa using isKFinHpk_zero L, fun g => by simp⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      show L.J (fun _ => 0) _ = _
      rw [(h1 P Q hPQ).1 c μ hc0 hμ, h0, J_zero]
      simp
    · intro γ g μR ν hG hrep hst hroot hq
      show OrbInt L (fun _ => 0) g ν = _
      rw [(h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, h0, orbInt_zero]
      simp
  · obtain ⟨P₁, Q₁, hPQ₁, hΛ⟩ := h3 κ τ hκ hτ P Q hPQ h0
    refine ⟨coefH L P₁ Q₁, Λ P₁ Q₁ κ τ / Λ₀ P Q, div_ne_zero hΛ h0,
      ⟨P₁, Q₁, hPQ₁.1, hPQ₁.2, fun g => rfl⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).1 c μ hc0 hμ, (h1 P Q hPQ).1 c μ hc0 hμ, smul_smul,
        div_mul_cancel₀ _ h0]
    · intro γ g μR ν hG hrep hst hroot hq
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).2 γ g μR ν hG hrep hst hroot hq,
        (h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, smul_smul, div_mul_cancel₀ _ h0]

end Formalism.L2.SG.Pf.OBT
end
end

