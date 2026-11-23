module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace Opposite
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.VB
open GlobalTheory.Twist (resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear freeModule)

namespace GlobalTheory.OmegaGlobal

theorem map_bijective_of_isIso_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (R.map : (X ⟶ Y) → _) := by
  have h : (R.map : (X ⟶ Y) → _) = adj.homEquiv _ _ ∘ fun φ => adj.counit.app X ≫ φ := by
    funext φ
    simp [Adjunction.homEquiv_unit]
  rw [h]
  exact (adj.homEquiv _ _).bijective.comp
    ((asIso (adj.counit.app X)).homFromEquiv (Z := Y)).symm.bijective

section Frames

variable {X : Scheme.{0}} {F : X.Modules}

theorem isQuasicoherent_of_frames (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)),
    x ∈ U ∧ IsFrame e) : F.IsQuasicoherent := by
  choose U n e hx he using h
  refine QCoh.isQuasicoherent_of_restrict F (fun x => (U x).ι)
    (fun x => ⟨x, by simpa using hx x⟩) fun x => ?_
  have := (isVB_freeModule (U x).toScheme (Fin (n x))).isQuasicoherent
  exact QCoh.isQuasicoherent_of_iso ((isFrame_freeFrame _ _).iso
      ((isFrame_restrict_iff (U x).ι _).2 ((he x).res ((U x).ι_image_le ⊤))))

end Frames

variable {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G]

theorem fst_mul (x y : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫ (x.1 * y.1) =
    toUnit (specO O O) ≫ η[G] := by
  rw [comp_mul, x.2, y.2]
  exact _root_.mul_one (1 : specO O O ⟶ G)

theorem fst_scale (a : O) (x : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫
    (ptMap (dualScale a) ≫ x.1) = toUnit (specO O O) ≫ η[G] := by
  refine Eq.trans ?_ x.2
  rw [← Category.assoc]
  congr 1
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext y <;> simp [dualScale]

end GlobalTheory.OmegaGlobal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleTorusEllipticElementRealPlace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.RegularGamma

open Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
  (k : Type) [CommRing k] [Algebra F k]

abbrev pbL : PowerBasis E (Fld P) := AdjoinRoot.powerBasis P.2.2.1.ne_zero

def vec : Fin (pbL P).dim → k ⊗[F] Fld P := fun i => (1 : k) ⊗ₜ (pbL P).basis i

theorem smul_tmul' (a : k) (e : E) (b : k) (l : Fld P) :
    (a ⊗ₜ[F] e : k ⊗[F] E) • (b ⊗ₜ[F] l : k ⊗[F] Fld P) = (a * b) ⊗ₜ (algebraMap E (Fld P) e * l) := by
  rw [Algebra.smul_def]
  change (Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P))) (a ⊗ₜ[F] e) * _ = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rfl

theorem span_vec : Submodule.span (k ⊗[F] E) (Set.range (vec P k)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a l =>
    rw [← (pbL P).basis.sum_repr l, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : a ⊗ₜ[F] ((pbL P).basis.repr l i • (pbL P).basis i) =
        (a ⊗ₜ[F] (pbL P).basis.repr l i : k ⊗[F] E) • vec P k i := by
      rw [vec, smul_tmul', mul_one, Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem bijective_vec (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Function.Bijective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
  have hs : Function.Surjective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, span_vec]
  have hd : (pbL P).dim = r := (AdjoinRoot.powerBasis_dim _).trans P.2.2.2.1
  let ψ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin (pbL P).dim → k ⊗[F] E) :=
    φ.trans (LinearEquiv.funCongrLeft _ _ (finCongr hd))
  haveI : Module.Finite (k ⊗[F] E) (k ⊗[F] Fld P) := Module.Finite.equiv φ.symm
  have hi := OrzechProperty.injective_of_surjective_endomorphism
    ((Fintype.linearCombination (k ⊗[F] E) (vec P k)) ∘ₗ ψ.toLinearMap) (hs.comp ψ.surjective)
  refine ⟨fun y y' hyy => ?_, hs⟩
  obtain ⟨z, rfl⟩ := ψ.surjective y
  obtain ⟨z', rfl⟩ := ψ.surjective y'
  rw [hi hyy]

def bas (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Module.Basis (Fin (pbL P).dim) (k ⊗[F] E) (k ⊗[F] Fld P) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (bijective_vec P k φ)).symm

theorem bas_apply (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) (i : Fin (pbL P).dim) :
    bas P k φ i = vec P k i := by
  simp [bas, Module.Basis.coe_ofEquivFun]

theorem mul_vec (j : Fin (pbL P).dim) :
    ((1 : k) ⊗ₜ[F] alpha P) * vec P k j =
      ∑ i, (inclR (F := F) k (Algebra.leftMulMatrix (pbL P).basis (alpha P) i j)) • vec P k i := by
  have hinc : ∀ e : E, inclR (F := F) k e = (1 : k) ⊗ₜ[F] e := fun _ => rfl
  simp only [vec, hinc, smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.tmul_sum]
  congr 1
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', ← Algebra.smul_def]
  exact ((pbL P).basis.sum_repr _).symm

theorem charpoly_mul_alpha (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    haveI := Module.Free.of_basis (bas P k φ)
    haveI := Module.Finite.of_basis (bas P k φ)
    (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  rw [← LinearMap.charpoly_toMatrix _ (bas P k φ)]
  have hM : LinearMap.toMatrix (bas P k φ) (bas P k φ)
      (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)) =
      (Algebra.leftMulMatrix (pbL P).basis (alpha P)).map (inclR (F := F) k) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.mul_apply', bas_apply, mul_vec]
    simp_rw [← bas_apply P k φ]
    rw [Module.Basis.repr_sum_self]
    rfl
  rw [hM, Matrix.charpoly_map, show alpha P = (pbL P).gen from (AdjoinRoot.powerBasis_gen _).symm,
    charpoly_leftMulMatrix]
  exact congrArg _ (AdjoinRoot.minpoly_powerBasis_gen_of_monic P.2.1)

theorem charpoly_mulMat (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    (mulMat φ ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  change (LinearMap.toMatrix' (φ.conj (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)))).charpoly = _
  rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix, LinearEquiv.charpoly_conj,
    charpoly_mul_alpha P k φ]

variable {P k}

theorem gam_val {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : k ⊗[F] Fld P}
    {φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    ((gam h).1 : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = mulMat φ ((1 : k) ⊗ₜ[F] alpha P) := by
  change mulMat φ (torUnit _).1 = _
  congr 1
  change Matrix.det _ = _
  rw [Matrix.det_fin_one]
  rfl

end GlobalTheory.RegularGamma

namespace GlobalTheory.RegularGamma

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots

theorem isRegSS_gam {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ) : IsRegSS (matAt V ρ (gam h)) := by
  have hm : matAt V ρ (gam h) = (mulMat φ ((1 : (placeOf D ρ).Completion) ⊗ₜ alpha P)).map (infEmb (embOverOf D ρ)) := by
    rw [← gam_val h]
    rfl
  change (matAt V ρ (gam h)).charpoly.Separable
  rw [hm, Matrix.charpoly_map, charpoly_mulMat, Polynomial.map_map]
  exact (Irreducible.separable P.2.2.1).map

end GlobalTheory.RegularGamma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmMulRightOfIsCMExt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped NNReal Matrix Topology ContDiff
open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut.RightTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isRealLine_conj (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.UAut.RightTranslate


open GlobalTheory.UAut.RightTranslate in
theorem GlobalTheory.UAut.isSm_mul_right_of_isCMExt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ → ∀ (f : GlobalTheory.AdelicU.GAd σ J → ℂ) (a : GlobalTheory.AdelicU.GAd σ J), GlobalTheory.UAut.IsSm σ J f → GlobalTheory.UAut.IsSm σ J (fun x => f (x * a)) := by
  intro F E _ _ _ _ _ σ n J h f a hf
  intro k γ hγ g
  have hc : ∀ l : List (GAd σ J), (l.map fun x => a⁻¹ * x * a).prod = a⁻¹ * l.prod * a := fun l => by
    induction l with
    | nil => simp
    | cons x l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]; simp [mul_assoc]
  have e : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)) =
      fun t => f (g * a * (List.ofFn fun i => a⁻¹ * γ i (t i) * a).prod) := funext fun t => by
    rw [show (List.ofFn fun i => a⁻¹ * γ i (t i) * a) = (List.ofFn fun i => γ i (t i)).map fun x => a⁻¹ * x * a from by
      rw [List.map_ofFn]; rfl, hc]
    simp [mul_assoc]
  show ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)
  rw [e]
  exact hf k (fun i t => a⁻¹ * γ i t * a) (fun i => isRealLine_conj h (hγ i) a) (g * a)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothFunAndRightDerivEqLeftInvariantVectorField
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.GlVec

theorem isSmoothFun_and_rightDeriv_eq_vecF : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) ∧ ∀ X : glL E a, ContDiffOn ℝ ∞ (vecF E a (toL X.1) f) (invSet E a) ∧ (glH E a).rightDeriv X (fun y : glG E a => f (toL y.1.val)) = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  intro E _ _ _ a f hf
  let Tl : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a :=
    { toFun := fun x => toL x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap Tl
  have hT : ∀ x, T x = toL x := fun _ => rfl
  have hval : ∀ (g : glG E a) (Y : glL E a), ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val
      = (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E)) := by
    intro g Y; rfl
  have hsm : (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) := by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have hin : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) :=
      T.contDiff.comp (contDiff_const.mul ((GroundTheory.Automorphic.contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))
    have := hf.comp_contDiff hin (fun Y => by
      rw [hT, ← hval g Y]; exact val_mem_invSet _)
    have e : (fun Y : glL E a => f (toL ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val)) =
        f ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
          NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E))) := by
      funext Y; simp only [Function.comp_apply, hT, hval]
    rw [e]
    exact this
  refine ⟨hsm, fun X => ⟨?_, ?_⟩⟩
  · exact (hf.fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply (rmul (toL X.1)).contDiff.contDiffOn
  · funext y
    have h1 := IsExpLieAlgebra.hasDerivAt_rightDeriv (glH E a) hsm X y
    have hy : toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val ∈ invSet E a := val_mem_invSet _
    have hfd : HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val))
        (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val) :=
      ((hf.contDiffAt (isOpen_invSet.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have hc : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E)))))
        (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * (X : Matrix (Fin a) (Fin a) (Cinf E)))) 0 := by
      have h2 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)).const_mul
        (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    have hc' : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E))))) _ 0 := hc
    have h3 := (show HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val))
        (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp ((0:ℝ) • (X : Matrix (Fin a) (Fin a) (Cinf E))))) by
          simpa [hT] using hfd).comp_hasDerivAt (0 : ℝ) hc'
    exact h1.unique h3

end GlobalTheory.GlVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantLaplacianEqCasimirDecomposition
section
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LapSplit

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem Eop_conjugate (τ : E →+* ℂ) (i j : Fin a) :
    Eop (ComplexEmbedding.conjugate τ) i j =
      (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) + Complex.I • lieS E a i j (atEmb τ Complex.I)) := by
  have h : atEmb τ (starRingEnd ℂ Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq τ (starRingEnd ℂ Complex.I)]
    conv_rhs => rw [atEmb_eq τ Complex.I]
    simp
  simp only [Eop, atEmb_conj, map_one, h, map_neg, smul_neg, sub_neg_eq_add]

theorem sum_sum_eq_zero_of_swap {A : Type} [AddCommGroup A] [Module ℂ A] (f : Fin a → Fin a → A)
    (hf : ∀ i j, f i j + f j i = 0) : ∑ i, ∑ j, f i j = 0 := by
  have h2 : (2 : ℂ) • ∑ i, ∑ j, f i j = 0 := by
    rw [two_smul]
    conv_lhs => enter [2]; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun j _ => hf i j
  have := congrArg (fun x => (1 / 2 : ℂ) • x) h2
  simpa [smul_smul] using this

theorem lap_summand (τ : E →+* ℂ) :
    ∑ i : Fin a, ∑ j : Fin a, ((lieS E a i j (atEmb τ 1)) ^ 2 + (lieS E a i j (atEmb τ Complex.I)) ^ 2) =
      (2 : ℂ) • ∑ i : Fin a, ∑ j : Fin a, (1 / 4 : ℂ) •
        ((lieS E a i j (atEmb τ 1) - lieS E a j i (atEmb τ 1)) ^ 2 +
          (lieS E a i j (atEmb τ Complex.I) + lieS E a j i (atEmb τ Complex.I)) ^ 2) +
      (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) + (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ)) := by
  rw [← sub_eq_zero]
  simp only [Formalism.REAL.Cas, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply sum_sum_eq_zero_of_swap
  intro i j
  simp only [Eop_conjugate]
  simp only [Eop]
  set R1 := lieS E a i j (atEmb τ 1)
  set R2 := lieS E a j i (atEmb τ 1)
  set I1 := lieS E a i j (atEmb τ Complex.I)
  set I2 := lieS E a j i (atEmb τ Complex.I)
  simp only [sq, smul_add, smul_sub, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf

end GlobalTheory.LapSplit

namespace GlobalTheory.LapSplit

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem sum_cas_conjugate :
    ∑ τ : E →+* ℂ, Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ)) =
      ∑ τ : E →+* ℂ, Formalism.REAL.Cas (Eop (a := a) τ) := by
  let e : (E →+* ℂ) ≃ (E →+* ℂ) :=
    ⟨ComplexEmbedding.conjugate, ComplexEmbedding.conjugate, fun σ => star_star σ, fun σ => star_star σ⟩
  exact Equiv.sum_comp e (fun τ => Formalism.REAL.Cas (Eop (a := a) τ))

end GlobalTheory.LapSplit

namespace GlobalTheory.HCAlpha

theorem lapOp_eq_casKOp_add_cas (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    lapOp E a = (2 : ℂ) • casKOp E a + ∑ τ : E →+* ℂ, (4 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) := by
  have h4 : ∀ τ : E →+* ℂ, (4 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) =
      (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) + (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) := fun τ => by
    rw [← add_smul]; norm_num
  unfold lapOp casKOp
  rw [Finset.sum_congr rfl fun τ _ => GlobalTheory.LapSplit.lap_summand (a := a) τ]
  simp only [ Finset.sum_add_distrib, h4, ← Finset.smul_sum,
    GlobalTheory.LapSplit.sum_cas_conjugate]
  abel

end GlobalTheory.HCAlpha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelsStandardFramesConjugateStandardGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levels_standardFrames_conjugate_standardGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ (i : Fin D.R.m) {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → StdPsi hF PW → ∀ P : LevelP R.Pg D.R.r ℂ, ∃ h : Formalism.AUTREP.GAf D.host.E n, ∀ κ, PW.ψ κ ∈ levS _ (R.βW i) (R.datWp i P) → PY.ψ (h⁻¹ * κ * h) ∈ levS _ (R.βY 0) (R.dat0 P) ∧ levChi _ (R.βW i) (R.datWp i P) (PW.ψ κ) = levChi _ (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) := by
  first | exact @GlobalTheory.FrameMove.frame_move | exact GlobalTheory.FrameMove.frame_move | (intros; apply GlobalTheory.FrameMove.frame_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicArchimedeanEigenvectorStatement
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_archimedean_eigenvector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ q : GAd σ J, (∀ w : InfinitePlace F, ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J (projArch σ J w q)).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J (proj σ J v q)).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J q).1 * adMat F x = l.1 • adMat F x := by
  first | exact @GlobalTheory.LineGlue.exists_idele_smul_of_local_lines | exact GlobalTheory.LineGlue.exists_idele_smul_of_local_lines | (intros; apply GlobalTheory.LineGlue.exists_idele_smul_of_local_lines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydiStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc : ∀ {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)), IsCompact K → (∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  first | exact @GlobalTheory.GoodTop.integrableOn_poinVol | exact GlobalTheory.GoodTop.integrableOn_poinVol | (intros; apply GlobalTheory.GoodTop.integrableOn_poinVol <;> assumption)
end

