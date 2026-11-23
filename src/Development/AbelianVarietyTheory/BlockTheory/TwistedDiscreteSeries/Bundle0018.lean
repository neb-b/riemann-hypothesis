module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory GlobalTheory.Doubling
open scoped TensorProduct ENNReal NNReal ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def schwartzA (θ : InfFam D) (m n : ℕ) : Submodule ℂ (Mx D m n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧
      φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))}

variable (A B : HSp D)

def cols (x y : WO A B) : WO (dblSp A) B := (Matrix.fromCols x y).submatrix id finSumFinEquiv.symm

def fstCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inl j)

def sndCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inr j)

def half (D : D7) : AE D := incA D (1 / 2)

def onX (x : WO A B) : WO (dblSp A) B := cols A B (half D • x) (half D • x)

def onY (y : WO A B) : WO (dblSp A) B := cols A B y (-y)

def xOf (w : WO (dblSp A) B) : WO A B := fstCols A B w + sndCols A B w

def yOf (w : WO (dblSp A) B) : WO A B := half D • (fstCols A B w - sndCols A B w)

variable {A B}

def thetaInt (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (μ : Measure (GA D B)) (𝓕 : Set (GA D B))
    (f₁ f₂ : WO A B → ℂ) (g₁ g₂ : GA D A) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ‖thetaKO om g₁ h f₁ * thetaKO om g₂ h f₂‖ₑ ∂μ

abbrev ht (V : HSp D) (g : GA D V) : ℝ≥0 := AdelicU.height D.sp.cm.sig V.gram g

variable (A B)

def InRange : Prop := 1 ≤ A.rank ∧ A.rank < B.rank ∧ (Cusp.wittIndex B = 0 ∨ A.rank + Cusp.wittIndex B < B.rank)

theorem half_add_half : half D + half D = 1 := by
  rw [half, ← map_add (f := _), add_halves, map_one]

theorem fstCols_cols (x y : WO A B) : fstCols A B (cols A B x y) = x := by
  ext i j; simp [fstCols, cols]

theorem sndCols_cols (x y : WO A B) : sndCols A B (cols A B x y) = y := by
  ext i j; simp only [sndCols, cols, Matrix.submatrix_apply, Equiv.symm_apply_apply]; rfl

theorem coords (x y : WO A B) : xOf A B (onX A B x) = x ∧ yOf A B (onX A B x) = 0 ∧
    xOf A B (onY A B y) = 0 ∧ yOf A B (onY A B y) = y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [xOf, yOf, onX, onY, fstCols_cols, sndCols_cols]
  · rw [← add_smul, half_add_half, one_smul]
  · simp
  · simp
  · rw [sub_neg_eq_add, smul_add, ← add_smul, half_add_half, one_smul]

end GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def heckeScalar (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : ℂ :=
  (((R.C.mu0 i).val P : ℂˣ) : ℂ) ^ (-(k : ℤ)) * ((Nat.card (kP P) : ℕ) : ℂ) ^ (-((k * (D.R.nV / 2) : ℕ) : ℤ))

def GoodPlace (P : Pl D.host.E) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) ∧ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

def IsCosetSys (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i))) : Prop :=
  ∃ α : GA D (Wc D i), IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def ReadAs (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) (heckeScalar R i P k) hL

def RationalHeckeAt (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : Prop :=
  ∃ hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL),
    (∀ Rc, IsCosetSys R i P k Rc → ReadAs R i P k Rc hL) ∧ ∀ x ∈ (R.FW i).WK, hL x ∈ (R.FW i).WK

def RationalHecke (i : Fin D.R.m) : Prop :=
  ∀ P : Pl D.host.E, GoodPlace R P → ∀ k : ℕ, k ≤ D.R.r → RationalHeckeAt R i P k

theorem readAs_iff (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) :
    ReadAs R i P k Rc hL ↔ ∀ x, (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (hL x)) =
      heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) x)) := Iff.rfl

theorem heckeScalar_zero (i : Fin D.R.m) (P : Pl D.host.E) : heckeScalar R i P 0 = 1 := by
  simp [heckeScalar]

end Local

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

end Comparison₂

end GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ContainsRayField {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (M : ℕ) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 L), ((M : ℕ) : 𝓞 L) ∉ 𝔓.asIdeal →
    ∃ (f : ℕ) (α : 𝓞 K),
      Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (𝔓.asIdeal.comap (RingOfIntegers.mapRingHom φ)) ^ f ∧
      (𝔓.asIdeal.comap (RingOfIntegers.mapRingHom φ)) ^ f = Ideal.span {α} ∧ ((M : ℕ) : 𝓞 K) ∣ α - 1

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Tuple

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


variable (D) in
def embK : D.host.K →+* D.what₂.LL := D.embE.comp (algebraMap D.host.K D.host.E)

def tupLevel (t : T0) : ℕ :=
  D.host.g 0 * D.host.g 1 * ∏ q ∈ (R.Q t).image (fun PP => Nat.card (kP PP)), q

def RatAt (i : Fin D.R.m) (ph : ℂ) (t : T0) : Prop :=
  ∀ x₀ : A.fam.amb.FL i t, ∃ y : Fin (R.nW i) → D.what₂.LL,
    (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = ph • R.thF i t (R.jV i t x₀) ∧
    ph • R.thG i t (R.jV i t x₀) =
      (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y)

theorem proj_clause (i : Fin D.R.m) (ph : ℂ) (t : T0) (hG : R.thP_thG)
    (hinj : Function.Injective (R.HW i (sg0 D A)).e)
    (hρ : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i _).e (actW R i _) (R.FW i).chi (R.FW i).ρ)
    (x : (R.HV i t).H) (y : Fin (R.nW i) → D.what₂.LL)
    (h : (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = ph • R.thF i t x) :
    ph • R.thG i t x = (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y) := by
  apply hinj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, hG i t x, ← map_smul, ← h, Arith.FormsL.eOp, LinearMap.sum_apply, map_sum, map_sum]
  have key : ∀ g : G, (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A)
      ((((idemOf A.X).coeff g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g) y)) =
      RealDat.eC (A := A) (sg0 D A) g • actW R i _ g ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y)) := by
    intro g
    rw [LinearMap.smul_apply, map_smulₛₗ, map_smul, hρ g y, smul_smul, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun g _ => key g]
  generalize (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = Φ
  ext v h
  simp [RealDat.eWf, gaL, actW, postOn, LinearMap.sum_apply, Finset.sum_apply]
  first | rfl | exact Finset.sum_congr rfl fun _ _ => rfl

end Tuple

end GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7}

def IsRealParam {m n k : ℕ} (L : (Fin k → ℝ) →+ Mx D m n) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

structure IsSchwartzBruhat {m n : ℕ} (φ : Mx D m n → ℂ) : Prop where

  level : ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, φ (x + u) = φ x

  supp : ∃ K : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, φ x ≠ 0 → x.map (finPart D) ∈ K

  schwartz : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), IsRealParam L → Function.Injective L →
    ∀ x, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = φ (x + L t)

end GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
section
namespace I195MixedCoordinates_a63f0715cbf334f1e52c5d7b

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_a63f0715cbf334f1e52c5d7b

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.MixModel
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {D : D7}

def halfMod {ρ : ℕ} (n : ℕ) (a : GL (Fin ρ) (AE D)) : ℝ :=
  ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : NNReal) : ℝ) ^ ((n : ℝ) / 2)

def starAdj (S T : HSp D) (x : WO S T) : Mx D S.rank T.rank :=
  incA D D.host.xi0 • (giA S ⬝ (adj x ⬝ gA T))

def ofAdj (S T : HSp D) (z : Mx D S.rank T.rank) : WO S T :=
  incA D (-D.host.xi0⁻¹) • (giA T ⬝ (adj z ⬝ gA S))

theorem starAdj_ofAdj (S T : HSp D) (z : Mx D S.rank T.rank) : starAdj S T (ofAdj S T z) = z := by
  rw [starAdj, ofAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv, one_smul, Matrix.mul_assoc, Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

structure FormulasS {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om₀ : GA D S₀ × GA D T →* Module.End ℂ (WO S₀ T → ℂ))
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) : Prop where

  target : ∀ (h : GA D T) (x : Mx D T.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 (om (1, h) f) x = om₀ (1, h) ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 f (mt T h⁻¹ ⬝ x))

  core : ∀ (g₀ : GA D S₀) (x : Mx D T.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 (om (d.emb0 g₀, 1) f) x = om₀ (g₀, 1) ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 f x)

  levi : ∀ (a : GL (Fin ρ) (AE D)) (x : Mx D T.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) x =
      ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (halfMod T.rank a : ℂ)) •
        (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 f (x ⬝ a.1)

  unip : ∀ (b : Mx D ρ S₀.rank) (x : Mx D T.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 (om (d.nB b, 1) f) x = heisO ψ S₀ T (x ⬝ b) ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 f x)

  centre : ∀ (c : skewA D ρ) (x : Mx D T.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 (om (d.nC c, 1) f) x =
      ψ (symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1))) • (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 f x

structure FormulasT {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (χS : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om₀ : GA D S × GA D T₀ →* Module.End ℂ (WO S T₀ → ℂ))
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) : Prop where

  source : ∀ (g : GA D S) (y : Mx D S.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 (om (g, 1) f) y = om₀ (g, 1) ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 f (mt S g⁻¹ ⬝ y))

  core : ∀ (h₀ : GA D T₀) (y : Mx D S.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 (om (1, d.emb0 h₀) f) y = om₀ (1, h₀) ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 f y)

  levi : ∀ (a : GL (Fin ρ) (AE D)) (y : Mx D S.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 (om (1, d.levi a) f) y =
      (((χS (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) * (halfMod S.rank a : ℂ)) •
        (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 f (y ⬝ a.1)

  unip : ∀ (b : Mx D ρ T₀.rank) (y : Mx D S.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 (om (1, d.nB b) f) y = heisO ψ S T₀ (ofAdj S T₀ (y ⬝ b)) ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 f y)

  centre : ∀ (c : skewA D ρ) (y : Mx D S.rank ρ),
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 (om (1, d.nC c) f) y = ψ (d.qT S c y) • (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 f y

def MixedSource (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (om₀ : GA D S₀ × GA D T →* Module.End ℂ (WO S₀ T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 →
    ∀ f, IsThetaFunO ψ S T f → FormulasS d ψ χT om om₀ μ 𝓕 f

def MixedTarget (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (om₀ : GA D S × GA D T₀ →* Module.End ℂ (WO S T₀ → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T₀ χS χT om₀ →
    ∀ (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)), IsCovolOne (ratMx D ρ S.rank) μ 𝓕 →
    ∀ f, IsThetaFunO ψ S T f → FormulasT d ψ χS om om₀ μ 𝓕 f

def MixedModelFormulas (D : D7) : Prop := MixedSource D ∧ MixedTarget D

def MixedValues (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)),
      IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ x, IsThetaFunO ψ S₀ T ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ μ 𝓕 f x)) ∧
    ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)),
      IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ y, IsThetaFunO ψ S T₀ ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 f y)

def gramSkew (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) : Mx D ρ ρ :=
  (-incA D D.host.xi0) • (adj x ⬝ (gA T ⬝ x))ᵀ

def CentralTerms (D : D7) : Prop :=
  (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    (∀ x : Mx D T.rank ρ, starAdj S T (d.extX T x) ⬝ x = d.jY ⬝ (gramSkew T x).map (cA D)) ∧
    (∀ (c : skewA D ρ) (x : Mx D T.rank ρ), symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1)) =
      -(algebraMap D.host.F (AF D.host.F) (1 / 2) *
        Algebra.trace (AF D.host.F) (AE D) ((gramSkew T x).map (cA D) ⬝ c.1).trace)) ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
      (∀ (x : Mx D T.rank ρ) (c c' : skewA D ρ), ψ (d.qS T (c + c') x) = ψ (d.qS T c x) * ψ (d.qS T c' x)) ∧
      (∀ x ∈ ratMx D T.rank ρ, ∀ c : skewA D ρ, c.1 ∈ ratMx D ρ ρ → ψ (d.qS T c x) = 1) ∧
      ∀ x ∈ ratMx D T.rank ρ, ∀ x' ∈ ratMx D T.rank ρ,
        (∀ c : skewA D ρ, ψ (d.qS T c x) = ψ (d.qS T c x')) ↔ gramSkew T x = gramSkew T x') ∧
  ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ),
    d.qT S c y = -(algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0⁻¹ • (adj y ⬝ (gA S ⬝ y))) ⬝ c.1).trace)

def HeisenbergTarget (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)),
      IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f →
        (∀ (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ), (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 (heisO ψ S T (d.incX S ξ) f) y =
          ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) • (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 f y) ∧
        (∀ (w₀ : WO S T₀) (y : Mx D S.rank ρ), (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 (heisO ψ S T (d.inc0 S w₀) f) y =
          heisO ψ S T₀ w₀ ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 f y)) ∧
        HasSum (fun y : Matrix (Fin S.rank) (Fin ρ) D.host.E => (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d) S ψ μ 𝓕 f (rat y) 0) (f 0)

theorem halfMod_pos {ρ : ℕ} (n : ℕ) (a : GL (Fin ρ) (AE D)) : 0 < halfMod n a := by
  refine Real.rpow_pos_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 fun h => ?_)) _
  have := (GlobalTheory.Doubling.absE D.host.F D.host.E).map_mul (Matrix.GeneralLinearGroup.det a)
    (Matrix.GeneralLinearGroup.det a)⁻¹
  rw [h, zero_mul, mul_inv_cancel, map_one] at this
  exact one_ne_zero this

theorem wittSmallProjection_wittNB_inv_mul_adjointInclusion {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (b : Mx D ρ T₀.rank) (y : Mx D S.rank ρ) :
    d.p0 ⬝ (mt T (d.nB b)⁻¹ ⬝ d.incAdj S y) = ofAdj S T₀ (y ⬝ b) := by
  rw [d.nB_inv, ← Matrix.mul_assoc, d.wittDecomp_projAnisotropic_unipotentMixed, HypDec.incAdj_apply, HypDec.incY_apply, ← Matrix.mul_assoc, Matrix.sub_mul,
    Matrix.mul_assoc _ d.pY, d.p0_jY, d.pY_jY, Matrix.mul_one, zero_sub, plus_neg, neg_neg, ofAdj, plus, adj_mul,
    Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KernelBound {D : D7} (V W : HSp D) (A d : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) →
      ∃ C : ℝ≥0, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
        IsWeilDatumO ψ V W χS χT ω →
        ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
          ∀ f ∈ thetaLevel ψ V W U, ∀ (g : GA D V) (h : GA D W),
            ‖thetaKO ω g h f‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f * ENNReal.ofReal ((height V g * height W h) ^ A)

def ThetaGrowth (D : D7) : Prop :=
  ∀ m n : ℕ, ∃ A d : ℕ, ∀ V W : HSp D, V.rank = m → W.rank = n → KernelBound V W A d

def ThetaGrowthUnif : Prop :=
  ∀ r N : ℕ, ∃ A d : ℕ, ∀ (D : D7) (V W : HSp D), Module.finrank ℚ D.host.F = r → V.rank * W.rank = N →
    KernelBound V W A d

theorem ThetaGrowthUnif.thetaGrowth (H : ThetaGrowthUnif) (D : D7) : ThetaGrowth D := fun m n =>
  (H _ (m * n)).imp fun _ h => h.imp fun _ h V W hV hW => h D V W rfl (by rw [hV, hW])

theorem KernelBound.real {D : D7} {V W : HSp D} {A d : ℕ} (H : KernelBound V W A d)
    (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {U : AddSubgroup (WO V W)}
    (hU : IsOpen (U : Set (WO V W))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
      IsWeilDatumO ψ V W χS χT ω →
      ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
        ∀ f ∈ thetaLevel ψ V W U, sobO ψ θ μ 𝓕 d f ≠ ∞ ∧ ∀ (g : GA D V) (h : GA D W),
          ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := by
  obtain ⟨C, hC⟩ := H ψ θ hθ U hU
  refine ⟨C, C.2, fun χS χT ω hω μ 𝓕 hμ f hf => ?_⟩
  have hs := sobO_ne_top hω.std hθ hμ.1 hμ.2.1 hf.1 d
  refine ⟨hs, fun g h => ?_⟩
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hs) ENNReal.ofReal_ne_top)
    (hC χS χT ω hω μ 𝓕 hμ f hf g h)
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (pow_nonneg (mul_pos (height_pos V g) (height_pos W h)).le A)] at this

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

end
end

