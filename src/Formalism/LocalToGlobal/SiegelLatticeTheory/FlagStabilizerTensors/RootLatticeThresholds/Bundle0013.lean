module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TopLevelBesselOfHypothesis
public import Formalism.HermitianCurvature.Bundle0010

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BuiltPf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Built

open Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def chiStd (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem isCut0_chiStd : Formalism.FourierDecayAlt.C6.IsCut0 chiStd := by
  unfold Formalism.FourierDecayAlt.C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · show ContDiff ℝ _ (Real.smoothTransition ∘ fun x : ℝ => 2 * x - 1)
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

section tower

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def towerOf (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.LevTower k r Wp Wq :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose

theorem towerOf_base (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : (towerOf B h1 h2 h3).base = B :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.1

theorem towerOf_norm (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.TowerNormalised (towerOf B h1 h2 h3) :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.2

end tower

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

abbrev par (I : CarrierIn X u u') (v : Fin I.nf) : Formalism.FourierDecayAlt.M.Par := Formalism.FourierDecayAlt.D.parOf (sOf I) v

def sgOf {nf : ℕ} (G : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (pl : Fin nf ≃ InfinitePlace D.host.E)
    (T T' : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (v : Fin nf) : ℂ :=
  Formalism.FourierDecayAlt.M.sgn ⟨G.k, G.r, T, T', (G.place (pl v)).u de, (G.place (pl v)).u de'⟩ l

theorem sg_of (I : CarrierIn X u u')
    (h : I.sg = sgOf I.G I.pl ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) I.de I.de' (I.l + 1)) :
    ∀ v, I.sg v = Formalism.FourierDecayAlt.M.sgn (par I v) ((sOf I).l + 1) := by
  intro v
  rw [h]
  rfl

def ParNums (I : CarrierIn X u u') : Prop :=
  ∀ v, (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u i - (par I v).u 1 = n) ∧
    (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u' i - (par I v).u 1 = n) ∧
    ∀ i ∈ Finset.Icc 1 ((par I v).k - 1), (par I v).lo i ≤ (par I v).hi i

def Types (I : CarrierIn X u u') : Prop :=
  ∀ v, Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z (I.T v).base.π (par I v).u ∧
    Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z' (I.T v).base.π' (par I v).u'

def Frames (I : CarrierIn X u u') : Prop := ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame (I.T v).base (I.ν' v) (I.m₀ v)

def CoefCC (I : CarrierIn X u u') : Prop := ∀ v (m : ℕ), Formalism.FourierDecayAlt.B.InCC I.A₀ m (I.fc v)

def CoefCap (I : CarrierIn X u u') : Prop :=
  ∀ v (Y : ℝ), ∀ g ∈ Formalism.FourierDecayAlt.B.GV I.G.k I.G.r,
    Formalism.FourierDecayAlt.Q.CV I.G.k I.G.r (Y : ℂ) (I.fc v) g = (((sOf I).P v Y : ℝ) : ℂ) • I.fc v g

theorem isPlace_of (I : CarrierIn X u u') (hN : ParNums I) (hty : Types I) (v : Fin I.nf) :
    Formalism.FourierDecayAlt.Q.IsPlace (par I v) (I.T v).base.z (I.T v).base.z' (I.T v).base.π (I.T v).base.π' := by
  unfold Formalism.FourierDecayAlt.Q.IsPlace
  obtain ⟨h1, h2, h3⟩ := hN v
  obtain ⟨t1, t2⟩ := hty v
  obtain ⟨e1, e2⟩ := I.hT v
  have p1 := (I.T v).base.T_pos
  have p2 := (I.T v).base.T'_pos
  rw [e1] at p1
  rw [e2] at p2
  exact ⟨⟨(I.T v).base.k_pos, p1, p2, h1, h2, h3⟩, (I.T v).base.z_mem, (I.T v).base.z'_mem, e1, e2, t1, t2⟩

end Formalism.L2.SG.Pf.Built
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def IntNX (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : ℝ :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
            (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
              (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
    ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * (IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D))

def LocRep (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) : Prop :=
  (∀ v, Measurable (L v) ∧ ∀ cv, 0 ≤ L v cv) ∧
    ∀ c ∈ Good X u u', ∀ v, hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v (c v)

def PlaceEnergy (P : Parts X u u') (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  ∀ v, Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v)) ≠ ⊤ ∧
    ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) =
      ENNReal.ofReal (K v * (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal)

def ConstPin (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  (∀ v, 0 ≤ K v) ∧
    (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
              (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
                (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
      ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * ((∏ v, K v) / Formalism.L2.SG.MassDataConc.kapN D)) =
      (P.Gam0 ^ P.S.f)⁻¹

end Formalism.L2.SG.Pf.Carrier.EnergyPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2RightTranslationThm
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.WuBL

theorem l2RightTranslation_thm : L2RightTranslation := by
  classical
  intro k r z hz hT μG μS ν hG hS hq Vp _ W hWc hW0 hWS y hy
  obtain ⟨hGg, hSg, hSG, hRG, hRS⟩ := quotient_measure_unitary_group k r z hz hT
  have hset : PI.QuotientSetting (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (Formalism.QuantumDeterminants.Sset k r z) μG μS ν :=
    ⟨hGg, hSg, hSG, hG, hS, hRG μG hG, hRS μS hS, hq⟩
  let G : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}
  have hGc : IsClosed G := hGg.1.preimage continuous_id
  let F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ((‖W (Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2
  have hFG : F = G.piecewise F (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ G
    · simp [Set.piecewise, hx]
    · simp [Set.piecewise, hx, F, hW0 (Matrix.of x) hx]
  have hcont : ContinuousOn F G := by
    have hW' : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of x)) G :=
      hWc.comp continuous_id.continuousOn (fun x hx => hx)
    exact (ENNReal.continuous_pow 2).comp_continuousOn (ENNReal.continuous_coe.comp_continuousOn hW'.nnnorm)
  have hmeas : Measurable F := by
    rw [hFG]
    exact hcont.measurable_piecewise continuousOn_const hGc.measurableSet
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x : Formalism.QuantumDeterminants.Mt k r,
      Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      F (fun i j => (s * Matrix.of x) i j) = F x := by
    intro s hs x hx
    have h2 : ‖W (s * Matrix.of x)‖₊ = ‖W (Matrix.of x)‖₊ := NNReal.eq (hWS s hs (Matrix.of x) hx)
    change ((‖W (s * Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2 = _
    rw [h2]
  exact quotient_invariant (2 * r + k + 1) _ _ μG μS ν hset F hmeas hinv y hy

end Formalism.L2.SG.Pf.WuBL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocJEq

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

private theorem isUnit_y_det (τ : D.what₂.Tau) : IsUnit (C.y τ).det := by
  obtain ⟨hQiQ, hQQi, hH, -⟩ := C.isT τ
  have hJJ : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  generalize Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = J at hH hJJ
  have hHinv : (C.Qi τ * J * (C.Qi τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1 := by
    rw [← hH]
    calc C.Qi τ * J * (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * J * C.Q τ)
        = C.Qi τ * J * (C.Q τ * C.Qi τ)ᴴ * J * C.Q τ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hQQi, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_assoc (C.Qi τ), hJJ, Matrix.mul_one, hQiQ]
  have hy' : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have h1 : (C.Qi τ * J * (C.Qi τ)ᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) * C.y τ = 1 := by
    rw [Matrix.mul_assoc, hy', hHinv]
  exact Matrix.isUnit_det_of_left_inverse h1

private theorem conj_lemma_2 (τ : D.what₂.Tau) (w : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    C.Q τ * (C.Qi τ * w * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ = w := by
  obtain ⟨hQiQ, hQQi, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQQi, Matrix.one_mul, ← Matrix.mul_assoc (C.y τ)⁻¹ (C.y τ),
    Matrix.nonsing_inv_mul _ (isUnit_y_det C τ), Matrix.one_mul, hQQi, Matrix.mul_one]

private theorem Qi_mul_Q_conj_mul_y_inv_eq (τ : D.what₂.Tau) (x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    C.Qi τ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) * C.Q τ * (C.y τ)⁻¹ = Matrix.of x := by
  obtain ⟨hQiQ, hQQi, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Qi τ) (C.Q τ), hQiQ, Matrix.one_mul, ← Matrix.mul_assoc (C.Qi τ) (C.Q τ), hQiQ,
    Matrix.one_mul, Matrix.mul_nonsing_inv _ (isUnit_y_det C τ), Matrix.mul_one]

theorem mem_of_range (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (x : Set.range (Smap C τ γ)) :
    umat γ * (C.Q τ * Matrix.of x.1 * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := by
  obtain ⟨z, hz⟩ := x.2
  rw [← hz]
  unfold Smap
  simp only [Equiv.apply_symm_apply]
  rw [conj_lemma_2 C τ]
  unfold umat UJset
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.mul_inv_cancel_left]
  exact z.2

def smapInv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (x : Set.range (Smap C τ γ)) :
    Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) :=
  ujOf' (umat γ * (C.Q τ * Matrix.of x.1 * C.y τ * C.Qi τ)) (mem_of_range C τ γ x)

theorem smapInv_cont (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Continuous (smapInv C τ γ) := by
  unfold smapInv ujOf'
  apply Continuous.subtype_mk
  have hx : Continuous fun x : Set.range (Smap C τ γ) => (Matrix.of (x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · dsimp only [Function.comp_def]
    fun_prop
  · dsimp only [Units.inv_mk]
    fun_prop

theorem smap_measEmb (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : MeasurableEmbedding (Smap C τ γ) := by
  have hu : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => umat (γ⁻¹ * z) := by
    unfold umat
    exact Units.continuous_val.comp (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  have hc : Continuous (Smap C τ γ) := by
    have h2 : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹ :=
      ((continuous_const.matrix_mul hu).matrix_mul continuous_const).matrix_mul continuous_const
    exact h2
  refine MeasurableEmbedding.of_measurable_inverse_on_range hc.measurable ?_ (smapInv_cont C τ γ).measurable ?_
  · have hS : Set.range (Smap C τ γ) =
        {x | umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))} := by
      ext x
      constructor
      · intro hx
        exact mem_of_range C τ γ ⟨x, hx⟩
      · intro hx
        have hx' : umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := hx
        refine ⟨ujOf' _ hx', ?_⟩
        unfold Smap umat ujOf'
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mk, Units.inv_mul_cancel_left]
        rw [Qi_mul_Q_conj_mul_y_inv_eq C τ]
        simp
    rw [hS]
    apply IsClosed.measurableSet
    have hof : Continuous fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => Matrix.of x := continuous_id
    have hf : Continuous fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) :=
      continuous_const.matrix_mul (((continuous_const.matrix_mul hof).matrix_mul continuous_const).matrix_mul
        continuous_const)
    unfold UJset Formalism.REAL.inUJ
    exact isClosed_eq ((hf.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hf) continuous_const
  · intro z
    apply Subtype.ext
    apply Units.ext
    unfold smapInv ujOf' Set.rangeFactorization Smap
    simp only [Equiv.apply_symm_apply, Units.val_mk]
    rw [conj_lemma_2 C τ]
    unfold umat
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.mul_inv_cancel_left]

variable (hB : WuBessel C)

theorem integrand_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)))).smulRight
      ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z))) =
      sclOf hB u u' τ • Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
  rw [phi'_S, phi_S]
  unfold Formalism.L2.SG.TermOp.rk1
  have hc : (starRingEnd ℂ) (sclOf hB u u' τ) = sclOf hB u u' τ := by
    unfold sclOf
    exact Complex.conj_ofReal _
  change (innerSL ℂ (sclOf hB u u' τ • X.Wloc u' (vOf X τ) (γ⁻¹ * z))).smulRight
      (X.Wloc u (vOf X τ) z) =
    sclOf hB u u' τ • (innerSL ℂ (X.Wloc u' (vOf X τ) (γ⁻¹ * z))).smulRight (X.Wloc u (vOf X τ) z)
  rw [map_smulₛₗ, hc]
  ext v
  simp [smul_smul]

theorem rank_one_continuous {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] {T : Type*} [TopologicalSpace T] {a : T → V} {b : T → V'} (ha : Continuous a)
    (hb : Continuous b) : Continuous fun t => Formalism.L2.SG.TermOp.rk1 (a t) (b t) := by
  unfold Formalism.L2.SG.TermOp.rk1
  have h1 : Continuous fun t => innerSL ℂ (b t) := (innerSL ℂ).continuous.comp hb
  exact (ContinuousLinearMap.smulRightL ℂ V' V).continuous₂.comp₂ h1 ha

theorem integrand_aesm (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Smap C τ γ)) := by
  have hw : ∀ w : D.what₂.Word, Continuous (X.Wloc w (vOf X τ)) := fun w => by
    first
      | exact X.W.Wloc_cont w _
      | exact X.Wloc_cont w _
      | exact X.toWBlk.Wloc_cont w _
  rw [(smap_measEmb C τ γ).aestronglyMeasurable_map_iff]
  have he : (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) ∘ Smap C τ γ =
      fun z => sclOf hB u u' τ •
        Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
    funext z
    exact integrand_S C hB u u' τ γ z
  rw [he]
  apply Continuous.aestronglyMeasurable
  exact (rank_one_continuous (hw u) ((hw u').comp (continuous_const.mul continuous_id))).const_smul (sclOf hB u u' τ)

theorem locJ_map_eq' (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    (locS hB u u' τ).J (ν.map (Smap C τ γ)) (trG (C.Q τ) (C.Qi τ) γ) =
      ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) :=
  locJ_map_eq (C := C) (hB := hB) u u' τ γ ν (integrand_aesm (C := C) (hB := hB) u u' τ γ ν)

end Formalism.L2.SG.Pf.LocJEq
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TBBTie
section
noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.BigCellDensity
open scoped InnerProductSpace

def parOfL {k r : ℕ} (L : LocBessel k r) (u u' : ℕ → ℝ) : Formalism.FourierDecayAlt.M.Par :=
  ⟨k, r, Tz k r L.z, Tz k r L.z', u, u'⟩

def PlTie {k r : ℕ} (L : LocBessel k r) {u u' : ℕ → ℝ} (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq) : Prop :=
  p.T.base.z = L.z ∧ p.T.base.z' = L.z' ∧ p.T.base.π = L.π ∧ p.T.base.π' = L.π' ∧ p.T.base.μW = L.μW ∧
    p.T.base.μN = L.μN ∧ p.T.base.μW' = L.μW'

def WeightTie : Prop :=
  ∀ (k r : ℕ) (T T' : ℝ) (p : Point ℂ (r + 1)), 1 ≤ k →
    ptWeight k r T T' p = Formalism.FourierDecayAlt.TBB.nPt k r (T * T') (p.1.map Prod.swap)

def EnergyTie : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u u' : ℕ → ℝ)
    (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq), 1 ≤ k → L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → PlTie L p →
    IsKFinCoefH L.σ f → Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 f → IsSection k r L.z L.z' μsec →
    Formalism.FourierDecayAlt.TBB.jN2 p f ≤ ENNReal.ofReal (Real.pi ^ (2 * (2 * r + 2) ^ 2)) * jNorm2 L f μsec

def CoefCC1 (Cgc : ℝ) : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsKFinCoefH L.σ f →
    GapAtLeast L.ε L.lam (Cgc * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) →
    Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 f

theorem tieTopXk (k r : ℕ) (hk : 1 ≤ k) (L : LocBessel k r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData k r L.Wp L.Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat k r) :
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
      ∀ (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 F →
        0 < Gpt (Tz k r L.z) (Tz k r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        orbSq L F γ = ENNReal.ofReal (Real.pi ^ (2 * Formalism.MainNotions.BigCellDensity.pc r (γ.1.map Prod.snd)) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  exact topLevelBesselHypothesis k0 r L Ds ν' m₀

theorem pc_le (r : ℕ) (s : List ℕ) : Formalism.MainNotions.BigCellDensity.pc r s ≤ (r + 1) ^ 2 := by
  unfold Formalism.MainNotions.BigCellDensity.pc
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]

theorem exists_relrep {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (h : orbSq L F γ ≠ 0) : ∃ g, IsPtRep L γ g ∧ IsRelStab L g := by
  by_contra hne
  apply h
  unfold orbSq
  refine le_antisymm ?_ bot_le
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hg => ?_
  exact (hne ⟨g, hg.1, hg.2.1⟩).elim

theorem ew_top {P : Formalism.FourierDecayAlt.M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (F : Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : Formalism.FourierDecayAlt.C.LPt)
    (hγ : Formalism.FourierDecayAlt.D.IsLocPt γ (P.r + 1)) (hn : 0 ≤ Formalism.FourierDecayAlt.TBB.nPt P.k P.r (Formalism.FourierDecayAlt.TBB.TTp p) γ) :
    Formalism.FourierDecayAlt.TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ =
      Formalism.FourierDecayAlt.TBB.nPt P.k P.r (Formalism.FourierDecayAlt.TBB.TTp p) γ *
        (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ F γ) (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ F γ)).re := by
  unfold Formalism.FourierDecayAlt.TBB.Ew Formalism.FourierDecayAlt.TBB.NP Formalism.FourierDecayAlt.KB.Pl.RR Formalism.FourierDecayAlt.D.RRplace
  rw [dite_eq_left ⟨hγ, hγ⟩, dite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl]
  simp only [Formalism.FourierDecayAlt.TBB.normC, List.map_nil, List.prod_nil, div_one, Real.mul_self_sqrt hn,
    Complex.re_ofReal_mul]

theorem pointWeight_eq_blockWeight (k r : ℕ) (T T' GG : ℝ) (hk : 1 ≤ k) : ∀ (bs : List (ℂ × ℕ)) (a : ℕ),
    (∀ b ∈ bs, 1 ≤ b.2) → a + (bs.map Prod.snd).sum = r + 1 →
    (∀ x, bs.getLast? = some x → GG = Complex.normSq x.1 - T * T') →
    ptWeightFrom k r T T' a bs = Formalism.FourierDecayAlt.C.nAux k r GG (fun _ _ => 1) (a + 1) (bs.map Prod.swap)
  | [], a, _, _, _ => by simp [ptWeightFrom, Formalism.FourierDecayAlt.C.nAux]
  | (t, s) :: bs, a, hs, hsum, hlast => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    have hsum' : a + (s + (bs.map Prod.snd).sum) = r + 1 := by simpa using hsum
    have ih := pointWeight_eq_blockWeight k r T T' GG hk bs (a + s) (fun b hb => hs b (by simp [hb])) (by omega)
      (fun x hx => hlast x (by rw [List.getLast?_cons, hx]; rfl))
    simp only [ptWeightFrom, List.map_cons, Prod.swap_prod_mk, Formalism.FourierDecayAlt.C.nAux]
    rw [show a + 1 + s = a + s + 1 by omega, ← ih]
    congr 1
    have hindex : a + s + 1 - 1 = a + s := by omega
    have hcond : (a + s = r + 1 ∧ s = 1) ↔ (s = 1 ∧ a + 1 = r + 1) := by omega
    simp only [hindex, hcond]
    by_cases hc : s = 1 ∧ a + 1 = r + 1
    · simp only [ite_eq_left hc]
      have hbs : bs = [] := by
        cases bs with
        | nil => rfl
        | cons b bs' =>
          have := hs b (by simp)
          simp only [List.map_cons, List.sum_cons] at hsum'
          omega
      subst hbs
      rw [hlast (t, s) (by simp)]
    · simp only [ite_eq_right hc, one_mul]
      have hle : a + s ≤ r + 1 := by omega
      have hexp : (2 * (s : ℤ) * (Formalism.FourierDecayAlt.C.Mlev k r (a + s) + s - 3)) =
          ((2 * s * (Ml k r (a + s) + s - 3) : ℕ) : ℤ) := by
        unfold Formalism.FourierDecayAlt.C.Mlev Ml
        have h3 : 3 ≤ 2 * (r + 1 - (a + s)) + k + 1 + s := by omega
        push_cast [h3, Nat.sub_add_cancel hle]
        have e2 : ((r + 1 - (a + s) : ℕ) : ℤ) = (r : ℤ) + 1 - ((a + s : ℕ) : ℤ) := by omega
        rw [e2]
        push_cast
        ring
      rw [hexp, zpow_natCast]

theorem weightTie : WeightTie := by
  intro k r T T' p hk
  unfold ptWeight Formalism.FourierDecayAlt.TBB.nPt
  refine pointWeight_eq_blockWeight k r T T' _ hk p.1 0 (fun b hb => (p.2.1 b hb).2)
    (by rw [p.2.2, Nat.zero_add]) ?_
  intro x hx
  simp [Formalism.FourierDecayAlt.D.ptGG, Formalism.FourierDecayAlt.D.ptLast, List.getLast?_map, hx]

end Formalism.L2.SG.Pf.BesselExpansion
end
end

