module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0068
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0274
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
section
noncomputable section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace GlobalTheory.RowsOrb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def Wb : Submodule D.host.E (VS D).V where
  carrier := {v | ∀ a, (VS D).hT (X.eX a) v = 0 ∧ (VS D).hT (X.fY a) v = 0}
  add_mem' := by
    intro x y hx hy a
    exact ⟨by rw [map_add (f := _), (hx a).1, (hy a).1, add_zero], by rw [map_add (f := _), (hx a).2, (hy a).2, add_zero]⟩
  zero_mem' := fun a => ⟨map_zero _, map_zero _⟩
  smul_mem' := by
    intro c x hx a
    exact ⟨by rw [map_smul, (hx a).1, smul_zero], by rw [map_smul, (hx a).2, smul_zero]⟩

theorem mem_Wb (v : (VS D).V) : v ∈ Wb X ↔ ∀ a, (VS D).hT (X.eX a) v = 0 ∧ (VS D).hT (X.fY a) v = 0 := Iff.rfl

def hb : Wb X →ₗ⋆[D.host.E] Wb X →ₗ[D.host.E] D.host.E := GlobalTheory.Mass.hRes (VS D).hT (Wb X)

def zb (u : D.what₂.Word) : Wb X := ⟨X.zu u, fun a => X.zu_orth u a⟩

def Ub (u : D.what₂.Word) : Submodule D.host.E (Wb X) :=
  GlobalTheory.Mass.perp (hb X) (Submodule.span D.host.E {zb X u})

def hU (u : D.what₂.Word) : Ub X u →ₗ⋆[D.host.E] Ub X u →ₗ[D.host.E] D.host.E := GlobalTheory.Mass.hRes (hb X) (Ub X u)

def Lmap (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (Wb X) :=
  GlobalTheory.Mass.latIn (Wb X) (Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X)

abbrev Gz (u : D.what₂.Word) : Subgroup (Formalism.HermitianLatticesTheory.isom (hb X)) :=
  MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom (hb X)) (zb X u)

theorem hb_apply (x y : Wb X) : hb X x y = (VS D).hT (x : (VS D).V) (y : (VS D).V) := rfl

theorem zb_coe (u : D.what₂.Word) : ((zb X u : Wb X) : (VS D).V) = X.zu u := rfl

theorem hU_apply (u : D.what₂.Word) (x y : Ub X u) :
    hU X u x y = (VS D).hT ((x : Wb X) : (VS D).V) ((y : Wb X) : (VS D).V) := rfl

theorem mem_Ub (u : D.what₂.Word) (x : Wb X) : x ∈ Ub X u ↔ (VS D).hT (X.zu u) (x : (VS D).V) = 0 := by
  unfold Ub GlobalTheory.Mass.perp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro H
    exact H (zb X u) (Submodule.mem_span_singleton_self _)
  · intro H y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
    change _ • (VS D).hT (X.zu u) (x : (VS D).V) = 0
    rw [H, smul_zero]

theorem mem_Lmap (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Wb X) :
    w ∈ Lmap X u Λ ↔ (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl

end GlobalTheory.RowsOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.LatLoc

theorem isLattice_map {E V W : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (f : V ≃ₗ[E] W) (Λ : Submodule (𝓞 E) V) (h : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Λ.map ((f : V →ₗ[E] W).restrictScalars (𝓞 E))) := by
  exact Submodule.IsLattice.of_fg E (h.fg.map _)

variable {D : D7}

def cE (D : D7) : (VS D).V ≃ₗ[D.host.E] (Fin (nV D) → D.host.E) := (VS D).frame.equivFun

def cL (Λ : LV D) : Submodule (𝓞 D.host.E) (Fin (nV D) → D.host.E) :=
  Λ.map (((cE D) : (VS D).V →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))

theorem baseChange_eq (Z : LocDat D) (p : PlF D) (x : (VS D).V) : baseChange₂ D p x = (GlobalTheory.HL.placesOf Z).bc p (cE D x) := rfl

theorem localLattice_eq (Z : LocDat D) (p : PlF D) (Λ : LV D) : lattice₂ D Z.M p Λ = (GlobalTheory.HL.placesOf Z).lat p (cL Λ) := by
  unfold lattice₂ GlobalTheory.HL.Places.lat cL
  rw [Submodule.map_coe, Set.image_image]
  rfl

theorem cL_injective : Function.Injective (cL (D := D)) := by
  intro Λ₁ Λ₂ h
  have := congrArg (Submodule.comap (((cE D) : (VS D).V →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))) h
  unfold cL at this
  rwa [Submodule.comap_map_eq_of_injective (by exact (cE D).injective),
    Submodule.comap_map_eq_of_injective (by exact (cE D).injective)] at this

theorem std_finite (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) :
    {p | lattice₂ D Z.M p Λ ≠ Submodule.span ((GlobalTheory.HL.placesOf Z).L p).O
      (Set.range fun i => (Pi.single i 1 : Fin (nV D) → ((GlobalTheory.HL.placesOf Z).loc p).Ep))}.Finite := by
  have hc : Submodule.IsFullLattice D.host.E (cL Λ) := by
    refine { toIsLattice := isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E ((cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (cE D).surjective
  have := (_root_.GlobalTheory.HL.PlacesRec.lattice_local (GlobalTheory.HL.placesOf Z) (nV D) (cL Λ) hc).2.2
  simp only [localLattice_eq]
  exact this

theorem lattices_local_global : ∀ (D : D7) (Z : LocDat D), (∀ Λ₁ Λ₂ : LV D, Submodule.IsFullLattice D.host.E Λ₁ →
    Submodule.IsFullLattice D.host.E Λ₂ → {p | lattice₂ D Z.M p Λ₁ ≠ lattice₂ D Z.M p Λ₂}.Finite ∧
      ((∀ p, lattice₂ D Z.M p Λ₁ = lattice₂ D Z.M p Λ₂) → Λ₁ = Λ₂)) ∧
    ∀ (Λ₀ : LV D), Submodule.IsFullLattice D.host.E Λ₀ → ∀ Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p),
      (∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤) →
      {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite →
      ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ = Lp p := by
  intro D Z
  refine ⟨fun Λ₁ Λ₂ h₁ h₂ => ⟨?_, fun h => ?_⟩, fun Λ₀ h₀ Lp hL hfin => ?_⟩
  · refine ((std_finite Z Λ₁ h₁).union (std_finite Z Λ₂ h₂)).subset fun p hp => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hp (hc.1.trans hc.2.symm)
  · apply cL_injective
    have hc (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) :
        Submodule.IsFullLattice D.host.E (cL Λ) := by
      refine { toIsLattice := isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
      change Submodule.span D.host.E ((cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
      rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
      exact (cE D).surjective
    have r₁ := (_root_.GlobalTheory.HL.PlacesRec.lattice_local (GlobalTheory.HL.placesOf Z) (nV D) (cL Λ₁) (hc Λ₁ h₁)).1
    have r₂ := (_root_.GlobalTheory.HL.PlacesRec.lattice_local (GlobalTheory.HL.placesOf Z) (nV D) (cL Λ₂) (hc Λ₂ h₂)).1
    ext x
    rw [r₁, r₂]
    refine forall_congr' fun p => ?_
    rw [← localLattice_eq, ← localLattice_eq, h p]
  · obtain ⟨Γ, ⟨hΓ, hΓp⟩, -⟩ := _root_.GlobalTheory.HL.Glue.glue (GlobalTheory.HL.placesOf Z) (nV D) Lp (fun p => hL p)
      (((std_finite Z Λ₀ h₀).union hfin).subset fun p hp => by
        by_contra hc
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
        exact hp (hc.2.trans hc.1))
    refine ⟨Γ.map (((cE D).symm : (Fin (nV D) → D.host.E) →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E)),
      isLattice_map _ _ hΓ, fun p => ?_⟩
    rw [localLattice_eq, ← hΓp p]
    congr 1
    unfold cL
    rw [← Submodule.map_comp]
    convert Submodule.map_id Γ
    ext x
    simp

end GlobalTheory.Unfold.LatLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImageRationalOrthComplementUnitaryEqRationalStab
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold.RatPts

open GlobalTheory.RatDiscrete

theorem eq_map_of_resolution {E R : Type} [CommRing E] [CommRing R] (ι : E →+* R) {n m : ℕ}
    {x u : Fin n → E} {A : Matrix (Fin n) (Fin m) E} {A' : Matrix (Fin m) (Fin n) E}
    (h : vecMulVec x u + A * A' = 1) (M : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin m) (Fin m) E)
    (hx : M *ᵥ (fun i => ι (x i)) = fun i => ι (x i)) (hA : M * A.map ι = A.map ι * g.map ι) :
    M = (vecMulVec x u + A * g * A').map ι := by
  have h1 : (vecMulVec x u + A * A').map ι = 1 := by
    rw [h]; exact Matrix.map_one ι (map_zero ι) (map_one ι)
  have hvm : ∀ y w : Fin n → E, (vecMulVec y w).map ι = vecMulVec (fun i => ι (y i)) (fun i => ι (w i)) := by
    intro y w; ext i j; simp [vecMulVec_apply]
  have key : M * vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) =
      vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) := by
    ext i j
    have hi := congrFun hx i
    simp only [mulVec, dotProduct] at hi
    change (∑ k, M i k * (ι (x k) * ι (u j))) = ι (x i) * ι (u j)
    rw [← hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => (mul_assoc (M i k) (ι (x k)) (ι (u j))).symm
  calc M = M * (vecMulVec x u + A * A').map ι := by rw [h1, Matrix.mul_one]
    _ = (vecMulVec x u + A * g * A').map ι := by
      rw [Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hvm,
        Matrix.mul_add, key, ← Matrix.mul_assoc, hA]

theorem exists_isImage (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA, IsImage I γ a := by
  have hU : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
  have hG : ∀ v, ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
    intro v
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map (I.φ v)) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    exact (I.cm.cmUnram.2.1 (I.φ v) _).symm
  have hR : ∀ v, Formalism.REAL.inUJ (I.ε v)
      ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) := by
    intro v
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hdH : IsUnit (I.P v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
    unfold Formalism.REAL.inUJ
    rw [← I.P_spec v]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((I.P v)ᴴ)⁻¹ (I.P v)ᴴ, Matrix.nonsing_inv_mul _ hdH, Matrix.one_mul,
      ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG v]
  have hC : ∀ v (X Y : Matrix (Fin I.n) (Fin I.n) ℂ),
      ((I.P v)⁻¹ * X * I.P v) * ((I.P v)⁻¹ * Y * I.P v) = (I.P v)⁻¹ * (X * Y) * I.P v := by
    intro v X Y
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have hE : ∀ v (X : Matrix (Fin I.n) (Fin I.n) I.E) (Y : Matrix (Fin I.n) (Fin I.n) I.E), X * Y = 1 →
      ((I.P v)⁻¹ * X.map (I.φ v) * I.P v) * ((I.P v)⁻¹ * Y.map (I.φ v) * I.P v) = 1 := by
    intro v X Y hXY
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    rw [hC, ← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hd]
  let ι := Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)
  have hF : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι) *
      I.J.map ι * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι = I.J.map ι := by
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map ι) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [ι, Formalism.UG.cT, Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  let af : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := Units.map (RingHom.mapMatrix ι).toMonoidHom γ
  have haf : af ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    exact hF
  refine ⟨(fun v => ⟨⟨(I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      hE v _ _ (Units.mul_inv γ), hE v _ _ (Units.inv_mul γ)⟩, hR v⟩, ⟨af, haf⟩), fun v => rfl, rfl⟩

theorem isImage_embA {I : AutInst} (D : Sib I) {x u : Fin I.n → I.E} {A : Matrix (Fin I.n) (Fin D.n) I.E}
    {A' : Matrix (Fin D.n) (Fin I.n) I.E} (h : vecMulVec x u + A * A' = 1)
    {jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)} {jf : D.inst.Gf →* I.Gf}
    (hv : IsInfEmb D x A jv) (hf : IsFinEmb D x A jf) {γ : Matrix (Fin D.n) (Fin D.n) I.E} {g : D.inst.GA}
    (hg : IsImage D.inst γ g) : IsImage I (vecMulVec x u + A * γ * A') (embA D jv jf g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨fun v => ?_, ?_⟩
  · have hPu := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hDu := (Matrix.isUnit_iff_isUnit_det _).mp (D.P_unit v)
    obtain ⟨h1, h2⟩ := hv v (g.1 v)
    have hxv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (x i)) =
        fun i => I.φ v (x i) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      change I.P v *ᵥ (uMat (jv v (g.1 v)) *ᵥ infVec I v x) = _
      rw [h1, infVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    have key : I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v =
        A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
      calc I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v
          = I.P v * (uMat (jv v (g.1 v)) * ((I.P v)⁻¹ * A.map (I.φ v) * D.P v)) := by
            simp only [Matrix.mul_assoc]
        _ = I.P v * (((I.P v)⁻¹ * A.map (I.φ v) * D.P v) *
            ((D.P v)⁻¹ * γ.map (I.φ v) * D.P v)) :=
            congrArg (I.P v * ·) (h2.trans (congrArg (infMat D v A * ·) (hg1 v)))
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (D.P v) (D.P v)⁻¹, Matrix.mul_nonsing_inv _ hDu, Matrix.one_mul,
              ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    have hAv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) =
        A.map (I.φ v) * γ.map (I.φ v) := by
      calc (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v)
          = (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) * D.P v * (D.P v)⁻¹ := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v * (D.P v)⁻¹ := by rw [key]
        _ = A.map (I.φ v) * γ.map (I.φ v) := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
    have hM := eq_map_of_resolution (I.φ v) h (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) γ hxv hAv
    change uMat (jv v (g.1 v)) = _
    rw [← hM]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu,
      Matrix.one_mul]
  · change I.fmat (jf g.2) = _
    exact eq_map_of_resolution (Formalism.UG.inclE (F := I.F) (Af I.F)) h (I.fmat (jf g.2)) γ (hf g.2).1
      ((hf g.2).2.trans (congrArg (afMat I A * ·) hg2))

theorem inclE_injective (I : AutInst) :
    Function.Injective (Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)) := by
  have hnf : ¬ IsField (𝓞 I.F) := by
    exact NumberField.RingOfIntegers.not_isField I.F
  obtain ⟨p, hp0, hpp⟩ := Ring.not_isField_iff_exists_prime.mp hnf
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) := ⟨p, hpp, hp0⟩
  have : Nontrivial (Af I.F) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg (fun a : Af I.F => (a.1 v : v.adicCompletion I.F)) h)⟩⟩
  intro a b hab
  exact Algebra.TensorProduct.includeLeft_injective (R := I.F) (S := I.F) (A := I.E) (B := Af I.F)
    (RingHom.injective _) hab

end GlobalTheory.StabUnfold.RatPts

namespace GlobalTheory.StabUnfold

open GlobalTheory.RatDiscrete RatPts

theorem image_rational_eq_stab : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf), IsInfEmb D x A jv → IsFinEmb D x A jf → embA D jv jf '' D.inst.GFset = stabF I x := by
  intro I D s x A xf hP jv jf hv hf
  obtain ⟨hn, hβ, hxA, hAJ, -, -⟩ := hP
  have hJ : I.Jᴴ = I.J := by
    have hh := I.J_herm
    unfold Formalism.UG.IsHerm at hh
    ext i j
    have hij := congrFun (congrFun hh i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij
    rw [Matrix.conjTranspose_apply]
    exact hij
  have hβ0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hβ]; cases s <;> simp [GlobalTheory.GaussMean.sgn]
  obtain ⟨u, A', hA'A, hA'x, huA, hux, hres, hAJx⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ0 hxA hAJ
  obtain ⟨j, hjv, hjr⟩ := _root_.GlobalTheory.StabRing.exists_emb I.E (starRingEnd I.E) I.n D.n I.J D.J x u A A'
    (isUnit_iff_ne_zero.mpr hβ0) hxA hAJx hAJ hA'A hA'x huA hux hres
  ext y
  constructor
  · rintro ⟨g, ⟨γ, hγ, hg1, hg2⟩, rfl⟩
    have hIm := isImage_embA D hres hv hf (γ := (γ : Matrix (Fin D.n) (Fin D.n) I.E)) (g := g) ⟨hg1, hg2⟩
    have hj := hjv ⟨γ, hγ⟩
    refine ⟨⟨(j ⟨γ, hγ⟩ : GL (Fin I.n) I.E), (j ⟨γ, hγ⟩).2, ?_⟩, (hf g.2).1⟩
    change IsImage I _ _
    rw [hj]
    exact hIm
  · rintro ⟨⟨δ, hδ, hy1, hy2⟩, hyx⟩
    have h3 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x) i)) =
        fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i) := by
      rw [← GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.map_mulVec_incl, ← hy2]
      exact hyx
    have hδx : (δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x = x := by
      funext i
      exact inclE_injective I (congrFun h3 i)
    obtain ⟨γ₀, hγ₀⟩ := hjr ⟨δ, hδ⟩ hδx
    obtain ⟨g, hg⟩ := exists_isImage D.inst (γ₀ : GL (Fin D.n) I.E) γ₀.2
    refine ⟨g, ⟨(γ₀ : GL (Fin D.n) I.E), γ₀.2, hg.1, hg.2⟩, ?_⟩
    have hIm := isImage_embA D hres hv hf hg
    have hM : vecMulVec x u + A * ((γ₀ : GL (Fin D.n) I.E) : Matrix (Fin D.n) (Fin D.n) I.E) * A' =
        (δ : Matrix (Fin I.n) (Fin I.n) I.E) := by
      rw [← hjv γ₀, hγ₀]
    rw [hM] at hIm
    exact subsingleton_isImage I _ hIm ⟨hy1, hy2⟩

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnfoldKernel
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.AdelicUnfold

theorem unfold_smul {Γ X : Type} [Group Γ] [Countable Γ] [MulAction Γ X] [MeasurableSpace X]
    [MeasurableConstSMul Γ X] (μ : Measure X) [SMulInvariantMeasure Γ X μ] {s : Set X}
    (hs : IsFundamentalDomain Γ s μ) (f : X → ℂ) (hf : Integrable f μ) :
    IntegrableOn (fun z => ∑' γ : Γ, f (γ • z)) s μ ∧
      ∫ z, f z ∂μ = ∫ z in s, ∑' γ : Γ, f (γ • z) ∂μ := by
  classical
  have hmeas : ∀ γ : Γ, AEStronglyMeasurable (fun z => f (γ • z)) μ := fun γ =>
    hf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_smul γ μ)
  have hfin : ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ ≠ ⊤ := by
    rw [← hs.lintegral_eq_tsum'' (fun z => ‖f z‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  have hae : ∀ᵐ z ∂μ.restrict s, ∑' γ : Γ, ‖f (γ • z)‖ₑ < ⊤ := by
    apply ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).restrict.enorm)
    rw [lintegral_tsum fun γ => (hmeas γ).restrict.enorm]
    exact hfin
  have hsm : ∀ᵐ z ∂μ.restrict s, Summable fun γ : Γ => f (γ • z) := by
    filter_upwards [hae] with z hz
    exact Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.1 hz.ne)
  have hasm : AEStronglyMeasurable (fun z => ∑' γ : Γ, f (γ • z)) (μ.restrict s) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := (Filter.atTop : Filter (Finset Γ)))
      (f := fun t z => ∑ γ ∈ t, f (γ • z)) (fun t => ?_) ?_
    · convert Finset.aestronglyMeasurable_sum t (fun γ _ => (hmeas γ).restrict) using 1
      ext z
      simp [Finset.sum_apply]
    · filter_upwards [hsm] with z hz using hz.hasSum
  refine ⟨⟨hasm, ?_⟩, ?_⟩
  · calc ∫⁻ z in s, ‖∑' γ : Γ, f (γ • z)‖ₑ ∂μ ≤ ∫⁻ z in s, ∑' γ : Γ, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_mono fun z => enorm_tsum_le_tsum_enorm
      _ = ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_tsum fun γ => (hmeas γ).restrict.enorm
      _ < ⊤ := hfin.lt_top
  · rw [integral_tsum (fun γ => (hmeas γ).restrict) hfin]
    exact hs.integral_eq_tsum'' f hf

theorem measurePreserving_left (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (g : I.GA) : MeasurePreserving (fun z => g * z) (I.muA μf) (I.muA μf) := by
  unfold AutInst.muA
  have h0 : ∀ v, (muG (I.ε v)).IsMulLeftInvariant := fun v => inferInstance
  have h1 : (Measure.pi fun v => muG (I.ε v)).IsMulLeftInvariant := inferInstance
  have h2 : ((Measure.pi fun v => muG (I.ε v)).prod μf).IsMulLeftInvariant := inferInstance
  exact measurePreserving_mul_left _ g

theorem integral_unfold_kernel : ∀ (B : RowsAut) (φ F : B.I.GA → ℂ) (x : B.I.GA), (∀ᵐ z ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, F (γ * z) = F z) → Integrable (fun g => φ g * F (x * g)) (B.I.muA B.μf) → IntegrableOn (fun z => kern B.I φ x z * F z) B.fund (B.I.muA B.μf) ∧ ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z in B.fund, kern B.I φ x z * F z ∂(B.I.muA B.μf) := by
  intro B φ F x hF hint
  have := B.haar
  have := B.sf
  have hcount : Countable (GlobalTheory.RatDiscrete.ratSub B.I) := by
    have := (GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype
    exact this
  have : MeasurableConstSMul (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA :=
    ⟨fun γ => (measurePreserving_left B.I B.μf γ.1).measurable⟩
  have : SMulInvariantMeasure (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA (B.I.muA B.μf) :=
    ⟨fun γ A hA => (measurePreserving_left B.I B.μf γ.1).measure_preimage hA.nullMeasurableSet⟩
  have hfd : IsFundamentalDomain (GlobalTheory.RatDiscrete.ratSub B.I) B.fund (B.I.muA B.μf) :=
    GlobalTheory.RatDiscrete.isFundamentalDomain B.I B.μf B.fund B.fund_spec

  have hh : Integrable (fun z => φ (x⁻¹ * z) * F z) (B.I.muA B.μf) := by
    have := ((measurePreserving_left B.I B.μf x⁻¹).integrable_comp hint.aestronglyMeasurable).2 hint
    convert this using 1
    ext z
    simp [Function.comp, mul_inv_cancel_left]
  have hB : ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z, φ (x⁻¹ * z) * F z ∂(B.I.muA B.μf) := by
    have hmp := measurePreserving_left B.I B.μf x
    have e := integral_map hmp.measurable.aemeasurable
      (f := fun z => φ (x⁻¹ * z) * F z) (by rw [hmp.map_eq]; exact hh.aestronglyMeasurable)
    rw [hmp.map_eq] at e
    rw [e]
    congr 1
    ext g
    simp [inv_mul_cancel_left]

  have hD : (fun z => ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I, φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z))
      =ᵐ[(B.I.muA B.μf).restrict B.fund] fun z => kern B.I φ x z * F z := by
    filter_upwards [ae_restrict_of_ae (s := B.fund) hF] with z hz
    unfold kern
    have hγ : ∀ γ : GlobalTheory.RatDiscrete.ratSub B.I,
        φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z) = φ (x⁻¹ * γ.1 * z) * F z := fun γ => by
      rw [hz γ.1 γ.2, mul_assoc]
    rw [tsum_congr hγ, tsum_mul_right]
    rfl
  obtain ⟨hI, hE⟩ := unfold_smul (B.I.muA B.μf) hfd (fun z => φ (x⁻¹ * z) * F z) hh
  refine ⟨hI.congr hD, ?_⟩
  rw [hB, hE]
  exact integral_congr_ae hD

end GlobalTheory.AdelicUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySubgroupChartSurjectiveNearOriginStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySubgroupChart_surjective_near_origin : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < ρ → ∃ g : Formalism.REAL.UJ ε, uMat g - 1 ∈ A ∧ Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ ∧ (WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) = x := by
  first | exact @GlobalTheory.GaugeSubChartSurj.chart_surj | exact GlobalTheory.GaugeSubChartSurj.chart_surj | (intros; apply GlobalTheory.GaugeSubChartSurj.chart_surj <;> assumption)
end

