module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementArchimedeanMatrixForm
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SiegelTorusMat

theorem eq_of_scales {n q : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin q) ℂ}
    {P Q : Matrix (Fin q) (Fin n) ℂ} {d e : Fin q → ℂ} (hX : A * X = X * Matrix.diagonal d)
    (hY : A * Y = Y * Matrix.diagonal e) (hZ : A * (1 - X * P - Y * Q) = 1 - X * P - Y * Q) :
    A = 1 + X * Matrix.diagonal (fun i => d i - 1) * P + Y * Matrix.diagonal (fun i => e i - 1) * Q := by
  have h : ∀ a : Fin q → ℂ, Matrix.diagonal (fun i => a i - 1) = Matrix.diagonal a - 1 := fun a => by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, hY, Matrix.mul_one,
    sub_sub, sub_eq_iff_eq_add] at hZ
  rw [h, h, hZ]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

theorem inv_scales {n q : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hBA : B * A = 1) {X : Matrix (Fin n) (Fin q) ℂ}
    {d e : Fin q → ℂ} (hde : ∀ i, d i * e i = 1) (hX : A * X = X * Matrix.diagonal d) :
    B * X = X * Matrix.diagonal e := by
  have h : X * Matrix.diagonal d * Matrix.diagonal e = X := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [hde, Matrix.diagonal_one, Matrix.mul_one]
  conv_lhs => rw [← h, ← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBA, Matrix.one_mul]

theorem archMat_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E), GlobalTheory.SiegelSet.IsWittFrame σ J Xf Yf →
    ∀ (t : Fin q → ℝ), (∀ i, 0 < t i) → ∀ a : GAd σ J, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
                   (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
      GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
                   (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) := by
  intro F E _ _ _ _ _ σ h n J hJ q X Y hW t ht a ha w τ
  have cc : ∀ Z : Matrix (Fin n) (Fin q) E, Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Z) = Z :=
    fun Z => Matrix.ext fun i j => GlobalTheory.SiegelSet.sigma_sigma h _
  have hJ' : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 _ _
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ', Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have xx := hW.xx
  have yy := hW.yy
  have xy := hW.xy
  obtain ⟨hX, hY, hz⟩ := ha.2 w τ
  generalize Formalism.UG.cT (σ : E →+* E) Y * J = P at *
  generalize Formalism.UG.cT (σ : E →+* E) X * J = Q at *
  have hBA : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = A at *
  generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = B at *
  have hQ : Q * (1 - X * P - Y * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, xx, xy]; simp
  have hP : P * (1 - X * P - Y * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, yx, yy]; simp
  have hZ0 : A * (1 - X * P - Y * Q).map τ.1 = (1 - X * P - Y * Q).map τ.1 := by
    generalize (1 - X * P - Y * Q) = Z at *
    ext i j
    exact congrFun (hz (fun k => Z k j) (funext fun k => congrFun (congrFun hQ k) j)
      (funext fun k => congrFun (congrFun hP k) j)) i
  have hm : (1 - X * P - Y * Q).map τ.1 = 1 - X.map τ.1 * P.map τ.1 - Y.map τ.1 * Q.map τ.1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← RingHom.mapMatrix_apply, map_sub, map_sub, map_one]
    rfl
  rw [hm] at hZ0
  have ht' : ∀ i, ((t i : ℝ) : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (ht i).ne'
  refine ⟨eq_of_scales hX hY hZ0, eq_of_scales (inv_scales hBA (fun i => ?_) hX) (inv_scales hBA (fun i => ?_) hY) ?_⟩
  · rw [Complex.ofReal_inv, mul_inv_cancel₀ (ht' i)]
  · rw [Complex.ofReal_inv, inv_inv, inv_mul_cancel₀ (ht' i)]
  · conv_lhs => rw [← hZ0, ← Matrix.mul_assoc, hBA, Matrix.one_mul]

end GlobalTheory.SiegelTorusMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviTorus

open Matrix

variable {R : Type} [CommRing R] {n m : ℕ}

section
variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R)

theorem conj_mulVec (hJ : ∀ i j, c (J j i) = -J i j) (V : Fin n → R) (hc : ∀ r, c (c r) = r) :
    (fun i => c ((J *ᵥ fun k => c (V k)) i)) = -(V ᵥ* J) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, hc, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hJ k i]; ring

theorem conj_dot (a b : Fin n → R) : c (a ⬝ᵥ b) = (fun i => c (a i)) ⬝ᵥ (fun i => c (b i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, map_sum, map_mul]

theorem vmv_mulVec (u v w : Fin n → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

end

section Props

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R}
  (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j)
  (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0)
  (hXY : X ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 1)
include hc hJ hXY

theorem dot_yx : Y ⬝ᵥ J *ᵥ (fun i => c (X i)) = -1 := by
  rw [dotProduct_mulVec]
  have h := conj_mulVec c J hJ Y hc
  rw [show Y ᵥ* J = -(fun i => c ((J *ᵥ fun k => c (Y k)) i)) by rw [h, neg_neg]]
  rw [neg_dotProduct, ← conj_dot, dotProduct_comm (J *ᵥ _) X, hXY, map_one]


end Props

end GlobalTheory.LeviTorus

namespace GlobalTheory.LeviTorus

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, h]
  | add a b ha hb => simp [map_add (f := _), ha, hb]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem form_incl (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ incM F J *ᵥ (fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [form, incV, incM, cA_incl, dotProduct, mulVec, map_sum, map_mul]

theorem vecMul_incM (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin k) E) (y : Fin n → E) :
    (incM F J *ᵥ fun i => cA σ (incV F y i)) ᵥ* incM F A =
      fun j => inclR (F := F) (AF F) (form σ J (A *ᵥ Pi.single j 1) y) := by
  funext j
  rw [← form_incl]
  simp only [vecMul, dotProduct, incV, incM, Matrix.map_apply, mulVec_single_one]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; rfl

end GlobalTheory.LeviTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotFilTotSymKer
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem totFil_totSym_ker : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), ∀ a < X.T - X.D, totFil X s (a + 1) ≤ totFil X s a ∧ ∀ x : totFil X s a, totSym Co a x = 0 ↔ x.1 ∈ totFil X s (a + 1) := by
  intro K _ _ X s hs δ Co a ha
  obtain ⟨hle, hker⟩ := GlobalTheory.HSCore.filV_symV_ker K X s hs δ Co a ha
  refine ⟨Submodule.map_mono hle, fun x => ?_⟩
  let e := Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a)
  let y : filV X s a := e.symm x
  have hxy : e y = x := e.apply_symm_apply x
  have hx1 : x.1 = incl X X.T y.1 := by rw [← hxy]; rfl
  have : totSym Co a x = symV Co a y := rfl
  rw [this, hker y, hx1]
  constructor
  · intro h
    exact ⟨y.1, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [← incl_injective X X.T hzy]

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreePencilLineDiscriminantLeStatement
section
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalDegree_pencilLineDiscriminant_le : ∀ (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ ξ₀ ξ₁ : Fin N → F, (GlobalTheory.PencilDisc.disc δ (fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => MvPolynomial.C (ξ₀ j)) (fun j => MvPolynomial.C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  first | exact @GlobalTheory.PencilDiscDeg.totalDegree_disc_le | exact GlobalTheory.PencilDiscDeg.totalDegree_disc_le | (intros; apply GlobalTheory.PencilDiscDeg.totalDegree_disc_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
section
noncomputable section

namespace GlobalTheory.LeviLine

open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

def sf (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ (J *ᵥ fun i => c (v i))

variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

theorem sf_sub_left (u w v : Fin n → R) : sf c J (u - w) v = sf c J u v - sf c J w v := by
  simp [sf, sub_dotProduct]

theorem sf_smul_left (r : R) (u v : Fin n → R) : sf c J (r • u) v = r * sf c J u v := by
  simp [sf, smul_dotProduct]

theorem sf_sub_right (u v w : Fin n → R) : sf c J u (v - w) = sf c J u v - sf c J u w := by
  simp only [sf, Pi.sub_apply, map_sub]
  rw [show (fun i => c (v i) - c (w i)) = (fun i => c (v i)) - fun i => c (w i) from rfl, mulVec_sub, dotProduct_sub]

theorem sf_smul_right (r : R) (u v : Fin n → R) : sf c J u (r • v) = c r * sf c J u v := by
  simp only [sf, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => c r * c (v i)) = c r • fun i => c (v i) from rfl, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem vecMulVec_mulVec' (x a z : Fin n → R) : vecMulVec x a *ᵥ z = (a ⬝ᵥ z) • x := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sf_skew (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) (u v : Fin n → R) :
    sf c J u v = -c (sf c J v u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sf, dotProduct, mulVec, map_sum, map_mul, hc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem ext_form {A B : Matrix (Fin n) (Fin n) R} (h : ∀ u v : Fin n → R, u ⬝ᵥ A *ᵥ v = u ⬝ᵥ B *ᵥ v) : A = B := by
  ext i j
  simpa [mulVec_single_one, single_one_dotProduct] using h (Pi.single i 1) (Pi.single j 1)

theorem ext_mulVec {A B : Matrix (Fin n) (Fin n) R} (h : ∀ u : Fin n → R, A *ᵥ u = B *ᵥ u) : A = B :=
  ext_form fun u v => by rw [h]

variable {c J}

end GlobalTheory.LeviLine

namespace GlobalTheory.LeviLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open Matrix

theorem ext_mulVec_single {R : Type} [CommRing R] {m k : ℕ} {A B : Matrix (Fin m) (Fin k) R}
    (h : ∀ j, A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1) : A = B := by
  ext i j
  simpa [mulVec_single_one] using congrFun (h j) i

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigma_invol h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR]

end GlobalTheory.LeviLine

namespace GlobalTheory.LeviLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open Matrix

end GlobalTheory.LeviLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSec_sum_smul_bc {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {m : ℕ} (a : Fin m → ℂ)
    (P : Fin m → Frame X.Ψ r → ℂ) (hP : ∀ i, X.IsSec la (P i)) :
    X.IsSec la (fun x => ∑ i, a i * P i x) := by
  refine ⟨DifferentiableOn.fun_sum fun i _ => (hP i).1.const_mul _, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.1 x hx b hb]; ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.2 γ hγ x hx]; ring

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

open Classical in
theorem rdU_unfExt_of_isBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hBC : IsBC hle f' as fs) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) f' k x = ∑ i, σ' (as i) * rdU U (fs i) k x := by
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c' f' ((unfExt hle σ' hσ U).un k ⟨x, h⟩)) else 0) =
    ∑ i, σ' (as i) * (if h : x ∈ (U.X k).dom then toC (evR Xo c (fs i) (U.un k ⟨x, h⟩)) else 0)
  by_cases hx : x ∈ (U.X k).dom
  · simp only [dif_pos hx]
    exact @hBC (CAt σ') _ σ.toAlgebra σ'.toAlgebra hσ _
  · simp only [dif_neg hx, mul_zero, Finset.sum_const_zero]

theorem isUnf_unfExt (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) {U : Unf Xo c σ r} (hU : IsUnf U) : IsUnf (unfExt hle σ' hσ U) := by
  obtain rfl : σ = σ'.comp (incF c c' hle) := RingHom.ext fun a => (hσ a).symm
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hU
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  refine ⟨h1, h2, fun y => ?_, h4, fun a n hd f' hf' k => ?_, h6⟩
  · exact h3 (FrPt.res hle (S := CAt σ') hσ y)
  · obtain ⟨m, as, fs, hfs, hBC⟩ := (secBC_and_cuspBC E H Dw l Xo c c' hle).1 a n f' hf'
    have e : rdU (unfExt hle σ' hσ U) f' k = fun x => ∑ i, σ' (as i) * rdU U (fs i) k x :=
      funext fun x => rdU_unfExt_of_isBC hle σ' hσ U hBC k x
    rw [e]
    exact isSec_sum_smul_bc (U.X k) (laU U a n k) _ _ fun i => h5 a n hd _ (hfs i) k

theorem rdU_unfExt_smul_rulBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) (u : c'.F) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) (u • rulBC hle f) k x = σ' u * rdU U f k x := by
  rw [map_smulₛₗ]
  have e := rdU_unfExt_of_isBC hle σ' hσ U (GlobalTheory.FieldBCModel.isBC_rulBC hle hf.1) k x
  simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_fin_one, map_one, one_mul] at e
  rw [← e]
  rfl

end Gen

theorem cXiAt_covBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (n r : ℕ) (c c' : Coeff l) (hle : c.F ≤ c'.F) (V : HSp D) (hr : V.rank = r) (d : DeltaDat Xo c n) (u : c'.F)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ)
    (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (h : CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0) :
    CXiAt V hr c'.F.val.toRingHom (covBC hle d u) (covUnf hle d u U₂) dict₂ io x₀ xi ((u : ℂ) * c0) := by
  obtain ⟨h1, h2, g, e, F, ik, φ, th, h3, h4, h5⟩ := h
  refine ⟨isUnf_unfExt (le_covCoeff hle d) _ (fun _ => rfl) h1, h2, g, e, F, ik, φ, th, h3, h4, fun h γ hm => ?_⟩
  have e1 := rdU_unfExt_smul_rulBC (le_covCoeff hle d)
    (c'.F.val.toRingHom.comp ((covBC hle d u).eF.symm : (covBC hle d u).c₂.F →+* c'.F)) (fun _ => rfl) U₂
    (show (covCoeff hle d).F from u) hs (dict₂ h).1 (dict₂ h).2
  refine e1.trans ?_
  rw [h5 h γ hm, ← mul_assoc]
  rfl

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k) * M = 1 ∧ M * (1 + mat k) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
    ∃ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, ∃ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k = n * p := by
  first | exact @GlobalTheory.InertBigCell.inlD_bigCell | exact GlobalTheory.InertBigCell.inlD_bigCell | (intros; apply GlobalTheory.InertBigCell.inlD_bigCell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSymplecticFormFrameCoordinatesEqLocalTraceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_symplectic_form_frame_coordinates_eq_local_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) →
      ∀ (PV JS : GL (Fin n) L) (PW JT : GL (Fin d) L),
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι PV X.J →
        (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι PW W.J)ᵀ →
        ∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
            (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) := by
  first | exact @GlobalTheory.InertLocSymp.psi_symp_eq | exact GlobalTheory.InertLocSymp.psi_symp_eq | (intros; apply GlobalTheory.InertLocSymp.psi_symp_eq <;> assumption)
end

