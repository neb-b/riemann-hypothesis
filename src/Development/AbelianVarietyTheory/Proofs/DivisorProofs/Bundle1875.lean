module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnfGroupContainsCongruenceUptoRootsOfUnity
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScal

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : Type := UG (cA σ) (dbl (incM F J))

def UDAt {R : Type} [Zero R] (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (ev : AF F → R) : Set (UD σ J) :=
  {p | At ev (((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1)}

def dsum {k : Type} [CommRing k] {d : ℕ} (c : GL (Fin d) k) : GL (Fin d ⊕ Fin d) k where
  val := Matrix.fromBlocks c.val 0 0 c.val
  inv := Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

def locMatD {σ : E →ₐ[F] E} {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (c : GL (Fin d) (Fv F v)) : UD σ J →* GL (Fin d ⊕ Fin d) (Fv F v) where
  toFun p := (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * dsum c
  map_one' := by simp
  map_mul' p q := by simp [mul_assoc]

abbrev DblCo (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) : Type :=
  Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d)

abbrev DblRep (σ : E →ₐ[F] E) {n d : ℕ} (W : Spc F E d) : Type :=
  UD σ W.J →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)

structure IsLinD {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (ψ : AddChar (AF F) ℂ) (dd : DblCo σ X W)
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ιd : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ)) :
    Prop where
  bij : Set.BijOn ιd (SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) : Set _)
    (SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) : Set _)
  trans : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 →
    ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      Acts (evFin F v) (dd.rho ψ u) φ φ₁ →
      ∀ Y, ιd φ₁ Y = ιd φ (Y + (b⁻¹).val * u.map (piW t) * ((dsum c)⁻¹).valᵀ)
  mult : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → u.map (piW t) = 0 →
    ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      Acts (evFin F v) (dd.rho ψ u) φ φ₁ →
      ∀ x : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
        ιd φ₁ ((b⁻¹).val * x.map (piW t) * ((dsum c)⁻¹).valᵀ) =
          ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u) * ιd φ ((b⁻¹).val * x.map (piW t) * ((dsum c)⁻¹).valᵀ)

def LocOps {σ : E →ₐ[F] E} {n d : ℕ} {W : Spc F E d} (omd : DblRep σ (n := n) W) (v : Pl (F := F)) : Prop :=
  ∀ p ∈ UDAt σ W.J (evFin F v), ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
    ∃ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ φ₁

def IsShapeD {σ : E →ₐ[F] E} {n d : ℕ} {W : Spc F E d} (omd : DblRep σ (n := n) W) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (c : GL (Fin d) (Fv F v))
    (ιd : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ))
    (cd : UD σ W.J → ℂ) : Prop :=
  ∀ p ∈ UDAt σ W.J (evFin F v), ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
    ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ φ₁ →
      ιd φ₁ = cd p • fun Y => ιd φ (Y * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val)

theorem exists_diag_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (h : UA σ J) :
    ∃ gd : UD σ J, ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      Matrix.fromBlocks (mat h) 0 0 1 := by
  let A : Matrix (Fin d) (Fin d) (AE F E) := mat h
  let Ai : Matrix (Fin d) (Fin d) (AE F E) := (((h : GL (Fin d) (AE F E))⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _)
  have h1 : A * Ai = 1 := (h : GL (Fin d) (AE F E)).mul_inv
  have h2 : Ai * A = 1 := (h : GL (Fin d) (AE F E)).inv_mul
  let G : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨Matrix.fromBlocks A 0 0 1, Matrix.fromBlocks Ai 0 0 1, by simp [fromBlocks_multiply, h1],
      by simp [fromBlocks_multiply, h2]⟩
  have hu : Aᵀ * incM F J * A.map (cA σ) = incM F J := h.2
  refine ⟨⟨G, ?_⟩, rfl⟩
  show (Matrix.fromBlocks A 0 0 1)ᵀ * dbl (incM F J) * (Matrix.fromBlocks A 0 0 1).map (cA σ) = dbl (incM F J)
  rw [fromBlocks_transpose, fromBlocks_map, dbl, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, transpose_one, Matrix.map_zero _ (map_zero (cA σ)), Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, hu]

theorem gdet_locMatD_diag {σ : E →ₐ[F] E} {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (c : GL (Fin d) (Fv F v)) (h : UA σ J) (gd : UD σ J)
    (hgd : ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      Matrix.fromBlocks (mat h) 0 0 1) :
    GlobalTheory.SplitFlip.gdet (locMatD t c gd) = GlobalTheory.SplitFlip.gdet (locMat t c h) := by
  apply Units.ext
  have e : (locMatD t c gd).val =
      Matrix.fromBlocks (locMat t c h).val 0 0 1 := by
    show ((dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) * (dsum c).val = _
    rw [hgd, locMat_val, fromBlocks_map]
    simp only [dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)),
      Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp [Units.mul_inv]
  simp only [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, e, det_fromBlocks_zero₂₁, det_one, mul_one]

def fixDiag {k : Type} [CommRing k] {d : ℕ} (A : GL (Fin d) k) : GL (Fin d ⊕ Fin d) k where
  val := Matrix.fromBlocks A.val (1 - A.val) 0 1
  inv := Matrix.fromBlocks (A⁻¹).val (1 - (A⁻¹).val) 0 1
  val_inv := by simp [fromBlocks_multiply, Matrix.mul_sub]
  inv_val := by simp [fromBlocks_multiply, Matrix.mul_sub]

theorem fixDiag_diag {k : Type} [CommRing k] {d : ℕ} (A : GL (Fin d) k) :
    ((fixDiag A).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) k) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) k) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) k) * (1 : Matrix (Fin d) (Fin d) k) := by
  simp only [fixDiag, diagCols, Matrix.mul_one]
  rw [← fromCols_fromRows_eq_fromBlocks, fromCols_mul_fromRows, fromRows_mul, fromRows_mul]
  ext (i | i) j <;> simp

theorem gdet_fixDiag {k : Type} [Field k] {d : ℕ} (A : GL (Fin d) k) :
    GlobalTheory.SplitFlip.gdet (fixDiag A) = GlobalTheory.SplitFlip.gdet A := by
  apply Units.ext
  simp [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, fixDiag, det_fromBlocks_zero₂₁]

theorem fromBlocks_sub_one {R : Type} [CommRing R] {d : ℕ} (A : Matrix (Fin d) (Fin d) R) :
    Matrix.fromBlocks A (0 : Matrix (Fin d) (Fin d) R) 0 (1 : Matrix (Fin d) (Fin d) R) - 1 =
      Matrix.fromBlocks (A - 1) (0 : Matrix (Fin d) (Fin d) R) 0 0 := by
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

end GlobalTheory.DblScal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.OrbitSep

section Lin

variable {X : Scheme.{0}} [IsIntegral X] {Γ : Type} [Group Γ]

def fnAct (ρ : Γ →* Aut X) (γ : Γ) : X.functionFieldˣ →* X.functionFieldˣ :=
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  Units.map (GlobalTheory.functionFieldMap (ρ γ).asIso.hom).toMonoidHom

def RatLin (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB) : Prop :=
  ∃ (D : CartierDiv X) (c : Γ → X.functionFieldˣ), cls (toLB D) (isLB_toLB D) = cls L hL ∧
    (∀ γ δ, c (γ * δ) = fnAct ρ δ (c γ) * c δ) ∧
    (∀ γ x g, D.IsEqn ((ρ γ).asIso.hom x) g → D.IsEqn x (fnAct ρ γ g * (c γ)⁻¹)) ∧
    ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * (c γ)⁻¹ * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Base

variable (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

abbrev X₀ : Scheme.{0} := (barComp Y Z).toScheme

abbrev s₀ : X₀ Y Z ⟶ Sp c.F := (barComp Y Z).ι ≫ Y.s

abbrev V₀ : Scheme.{0} := (Y.j ⁻¹ᵁ barComp Y Z).toScheme

abbrev i₀ : V₀ Y Z ⟶ Xo.XF c := (Y.j ⁻¹ᵁ barComp Y Z).ι

abbrev j₀ : V₀ Y Z ⟶ X₀ Y Z := Y.j ∣_ barComp Y Z


variable {Y} in
abbrev π₀ (X : FlagCover Y) (Z : Comp Xo c) : Y₀ X Z ⟶ X₀ Y Z := X.π ∣_ barComp Y Z


variable {Y} in
theorem π₀_s₀ (X : FlagCover Y) (Z : Comp Xo c) : π₀ X Z ≫ s₀ Y Z = str₀ X Z := by
  dsimp only [π₀, s₀, str₀, inc₀, flagStr]
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

theorem j₀_ι : j₀ Y Z ≫ (barComp Y Z).ι = i₀ Y Z ≫ Y.j :=
  morphismRestrict_ι _ _


variable {Y Z} in
def ActsBy {Γ : Type} [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ Y Z)) : Prop :=
  (∀ γ, (ρ γ).asIso.hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z) ∧
    ∀ (γ : Γ) (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v : Sp R ⟶ V₀ Y Z), v ≫ i₀ Y Z = ptF y →
      v ≫ (ρ γ).asIso.hom ≫ i₀ Y Z = ptF (move Xo c (ι γ)⁻¹ y)

end Base


variable (Dw) in
def kapBase : AllWt.Weight Dw := fun _ i => if (i : ℕ) < Dw.p then (Dw.q : ℤ) else -(Dw.p : ℤ)

def UnipAt (I : Ideal (𝓞 E)) (γ : LevelAut Dw l) : Prop :=
  ∃ m : ℕ, ∀ x : Dw.La, ((liftLa γ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)

def NeatPrime (I : Ideal (𝓞 E)) (g r : ℕ) : Prop :=
  g.Prime ∧ Ideal.absNorm I = g ∧ (g : 𝓞 E) ∉ I ^ 2 ∧ r + 1 < g

theorem gapGe_sub_kapBase (t : ℤ) (ht : ((Dw.p + Dw.q : ℕ) : ℤ) ≤ t) : GapGe 0 (t • hodgeWt Dw - kapBase Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [Pi.sub_apply, Pi.smul_apply, hodgeWt, GlobalTheory.CompHt.barWt, kapBase, smul_eq_mul]
  push_cast at ht ⊢
  split_ifs <;> omega

theorem gapGe_hodgeWt : GapGe 0 (hodgeWt Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [hodgeWt, GlobalTheory.CompHt.barWt]
  split_ifs <;> omega

end GlobalTheory.OrbitSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCompNonempty
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CovTop

theorem good_comp_nonempty : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Nonempty (Comp Y.d.Xo₂ Y.d.c₂) := by
  intro D T hT j hj Y e o _
  exact (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Y.d.Xo₂ Y.d.c₂
    (Inhab.rank_pos T.toCore hT.pins j hj)).1

end GlobalTheory.CovTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspData
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.CovData

theorem hasPrinc_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (Y.U σ))
      (Y.d.l₂.M * (D.host.g 0 * D.host.g 1 * Y.d.pd)) := by
  have hr : 0 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hN : 3 ≤ D.host.g 0 * D.host.g 1 * Y.d.pd := by
    have h0 := (D.host.g_prime 0).two_le
    have h1 := (D.host.g_prime 1).two_le
    have hp : 1 ≤ Y.d.pd := by rw [hG.pd]; exact Nat.one_le_pow _ _ (by norm_num)
    have : 4 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul h0 h1
    nlinarith
  intro k γ hγ hc
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) hG.lev.2 hr k γ hγ
    (fun x hx => by
      obtain ⟨y, hy, h⟩ := hc x hx
      refine ⟨((D.host.g 0 * D.host.g 1 * Y.d.pd : ℕ) : D.host.E) • y, ?_, ?_⟩
      · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
      · rw [h, smul_smul, ← Nat.cast_mul])
  obtain ⟨th, hrk, hth, hD⟩ := hG.dictU σ hσ
  have hmu : MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
    ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hG.unit σ hσ⟩
  have h1 := GlobalTheory.PrincCore.root_eq_one (D.sp.W j) hrk hr (Y.U σ).X (Y.dict σ) (fun _ => (1 : ℂ)) Y.Kf th hth hD
    hmu _ hN hG.levelK k γ γ' hγ'
    (fun x hx => by
      obtain ⟨y, hy, h⟩ := hc x hx
      refine ⟨((Y.d.l₂.M : ℕ) : D.host.E) • y, ?_, ?_⟩
      · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
      · rw [h, smul_smul, ← Nat.cast_mul, mul_comm])
    u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.CovData

namespace GlobalTheory.CovData

theorem exists_dataX_good : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ σ, GoodEmb Y.d.c₂ σ → ∀ k : (Y.U σ).Comp, ∃ (Xx : FD.DataX D.host.E D.R.r)
      (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), Xx.toData = (Y.U σ).X k ∧ 𝔄 ≠ 0 ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  intro D T j Y e o hG σ hσ k
  obtain ⟨hr, hm⟩ := hG.modelW σ hσ
  have hx1 : xiR D ≤ 1 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_le_half D).trans (by norm_num)
  have habs := hG.xiAbs σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) k
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((Y.U σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [(hm k).2, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
      ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
    exact h1
  have hA : D.host.AA ≠ 0 := by
    intro e0
    rw [e0] at hone
    simp at hone
  have hM : 0 < Y.d.l₂.M * (D.host.g 0 * D.host.g 1 * Y.d.pd) := by
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    have hp : 0 < Y.d.pd := by rw [hG.pd]; positivity
    have hl : 0 < Y.d.l₂.M := by have := Y.d.l₂.three_le; omega
    positivity
  obtain ⟨Xx, h1, -, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((Y.U σ).X k) D.host.AA D.host.AAbar
    (xiR D) _
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hasPrinc_good D T j Y e o hG σ hσ k)
  exact ⟨Xx, D.host.AA, h1, hA, h3⟩

end GlobalTheory.CovData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiAdditive
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.ConstDefCub

theorem isPullCubical_constPt : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq htan A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o m g hg1 hg2 hF
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    _root_.GlobalTheory.TangentConstLB.lbIso_tangent_const E H Dw l Xo c K y.x x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

end GlobalTheory.ConstDefCub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraTer
section
namespace GlobalTheory.LiftAndFactorization

open Formalism.L2.Pj

theorem exists_lift (T : CDVR) (x : T.Fr) (hx : x ≠ 0 → vV T.V x = 0) :
    ∃ b : T.V, algebraMap T.V T.Fr b = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have hne : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x ≠ 0 :=
    (Valuation.ne_zero_iff _).2 h0
  have hlog : WithZero.log ((IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x) = 0 := by
    have := hx h0
    unfold vV valV at this
    exact neg_eq_zero.1 this
  have := WithZero.exp_log hne
  rw [hlog, WithZero.exp_zero] at this
  exact this.ge

theorem exists_factor (T : CDVR) {F : Type} [Field F] (io : F →+* T.Fr)
    (h : ∀ a : F, a ≠ 0 → vV T.V (io a) = 0) :
    ∃ φ : F →+* T.V, (algebraMap T.V T.Fr).comp φ = io := by
  have key : ∀ a : F, ∃ b : T.V, algebraMap T.V T.Fr b = io a := fun a =>
    exists_lift T (io a) (fun ha => h a (fun h0 => ha (by rw [h0, map_zero])))
  choose f hf using key
  have inj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => inj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => inj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]) }, ?_⟩
  ext a
  exact hf a

end GlobalTheory.LiftAndFactorization
end

