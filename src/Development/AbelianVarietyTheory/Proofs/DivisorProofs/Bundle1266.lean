module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslates
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicIdentification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Formalism.HarderNarasimhan.StatementPl
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefinitePairClassesFixedMinpolyDegreeOne
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseIntegralMatricesPreservingDoubledLa
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.LatticeStab

variable {A O : Type} [CommRing A] [CommRing O] (ι : O →ₙ+* A) {n : ℕ}

theorem map_mul_of_nonUnital {m : Type} [Fintype m] (G H : Matrix m m O) :
    (G * H).map ι = G.map ι * H.map ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum, map_mul]

theorem exists_matrix_of_keeps (P : Matrix (Fin n) (Fin n) A) (Λ : Set (Fin n → A))
    (hP : ι 1 • P = P)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A)
    (hM : ∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ) :
    ∃ G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O,
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  have h0 : (0 : Fin n → A) ∈ Λ :=
    (hΛ 0).2 ⟨0, by ext i; simp [Matrix.mulVec, dotProduct]⟩
  have hcol : ∀ k : Fin n, (fun r => P r k) ∈ Λ := by
    intro k
    refine (hΛ _).2 ⟨Pi.single k 1, ?_⟩
    ext r
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k]
    · have := congrFun (congrFun hP r) k
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      simp only [Pi.single_eq_same]
      rw [mul_comm]; exact this.symm
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  have hDcol : ∀ j, (fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inl ∈ Λ ∧
      (fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inr ∈ Λ := by
    intro j
    rcases j with k | k
    · have e1 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inl k)) ∘ Sum.inl = fun r => P r k := by
        ext r; simp
      have e2 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inl k)) ∘ Sum.inr = 0 := by
        ext r; simp
      rw [e1, e2]; exact ⟨hcol k, h0⟩
    · have e1 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inr k)) ∘ Sum.inl = 0 := by
        ext r; simp
      have e2 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inr k)) ∘ Sum.inr = fun r => P r k := by
        ext r; simp
      rw [e1, e2]; exact ⟨h0, hcol k⟩
  have ex : ∀ j, ∃ a b : Fin n → O,
      (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inl = P *ᵥ (fun i => ι (a i)) ∧
      (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inr = P *ᵥ (fun i => ι (b i)) := by
    intro j
    obtain ⟨h1, h2⟩ := hM _ (hDcol j).1 (hDcol j).2
    obtain ⟨a, ha⟩ := (hΛ _).1 h1
    obtain ⟨b, hb⟩ := (hΛ _).1 h2
    exact ⟨a, b, ha, hb⟩
  choose a b hab using ex
  refine ⟨Matrix.of fun i j => Sum.elim (a j) (b j) i, ?_⟩
  ext i j
  have hMD : (M * Matrix.fromBlocks P 0 0 P) i j = (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) i := rfl
  rw [hMD]
  rcases i with r | r
  · have := congrFun (hab j).1 r
    simp only [Function.comp] at this
    rw [this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  · have := congrFun (hab j).2 r
    simp only [Function.comp] at this
    rw [this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

end GlobalTheory.LatticeStab

theorem GlobalTheory.LatticeStab.matrix_in_diag_basis : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (n : ℕ) (P Q : Matrix (Fin n) (Fin n) A)
    (Λ : Set (Fin n → A)), Function.Injective ι → P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) A) →
    Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) A) → ι 1 • P = P → ι 1 • Q = Q →
    (∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A, M * M' = 1 →
    (∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inr ∈ Λ) →
    ∃ G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, G * G' = 1 ∧
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  intro A O _ _ ι n P Q Λ hinj _hPQ hQP hP _hQ hΛ M M' hMM' hM
  obtain ⟨G, hG⟩ := GlobalTheory.LatticeStab.exists_matrix_of_keeps ι P Λ hP hΛ M
    (fun z h1 h2 => ⟨(hM z h1 h2).1, (hM z h1 h2).2.1⟩)
  obtain ⟨G', hG'⟩ := GlobalTheory.LatticeStab.exists_matrix_of_keeps ι P Λ hP hΛ M'
    (fun z h1 h2 => ⟨(hM z h1 h2).2.2.1, (hM z h1 h2).2.2.2⟩)
  refine ⟨G, G', ?_, hG⟩
  have hDD : Matrix.fromBlocks P 0 0 P * (G * G').map ι = Matrix.fromBlocks P 0 0 P := by
    rw [GlobalTheory.LatticeStab.map_mul_of_nonUnital, ← Matrix.mul_assoc, ← hG, Matrix.mul_assoc, ← hG',
      ← Matrix.mul_assoc, hMM', Matrix.one_mul]
  have hQD : Matrix.fromBlocks Q 0 0 Q * Matrix.fromBlocks P 0 0 P =
      ι 1 • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_multiply]
    simp [hQP]
  have key : ι 1 • (G * G').map ι = ι 1 • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) := by
    have := congrArg (fun X => Matrix.fromBlocks Q 0 0 Q * X) hDD
    simp only [← Matrix.mul_assoc, hQD] at this
    rwa [Matrix.smul_mul, Matrix.one_mul] at this
  ext i j
  apply hinj
  have := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, one_mul] at this
  rw [this]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLagr

theorem exists_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
      ∃ Cy : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (Fv F v ⊗[F] E),
        IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) G.W.J) Cy := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw
  have hF := GlobalTheory.InertTensorField.isField_tensor_of_isInertAt F E σ B hT.base v w hvw
  obtain ⟨y, u, hu, hy⟩ := GlobalTheory.T.skewHermitian_det_eq_unit_mul_norm_at_inert F E σ B hT.base _ _ _ G.W hT.geo.hW hT.geo.even v w hvw hF
  obtain ⟨z, hz⟩ := GlobalTheory.T.unit_eq_norm_completionTensor_of_isInertAt F E σ B hT.base v w hvw hF u hu
  refine GlobalTheory.T.exists_lagrangian_skewHermitian_completionTensor F E σ hT.base.cm v hF (a + a') G.W.J hT.geo.even hT.geo.hW.skew
    (_root_.GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B _ _ _ G.W hT.geo.hW) ⟨z * y, ?_⟩
  rw [hy, hz, map_mul]
  ring

end GlobalTheory.InertLagr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinitStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, Polynomial.aeval (lapOp E a) p φ = 0 := by
  first | exact @GlobalTheory.GLPoly.exists_poly_formsGL | exact GlobalTheory.GLPoly.exists_poly_formsGL | (intros; apply GlobalTheory.GLPoly.exists_poly_formsGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerSectionNonzeroAtOrigin
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
noncomputable section

namespace GlobalTheory.Poinc.Origin
open GlobalTheory.UT.CoefBasic

theorem exists_sec_value_ne_zero : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ k : ℕ, 4 ≤ k → ∃ (t : SecA A F k) (c : F), c ≠ 0 ∧ ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val := by
  intro hL R _ _ A F _ _ ρ hρ k hk
  obtain ⟨M, s, hcov⟩ := (hL.1.ample _ A k hk).1 ⊤ (isAffineOpen_top _)
  obtain ⟨i', hi⟩ : ∃ i' : A.A.left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.A.left.topIso.inv, A.A.left.topIso.inv_hom_id⟩
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  let χ : (TFK (R := R) F).left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme :=
    (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ i'
  have hmem : χ z ∈ (⨆ j, nonzeroLocus (s j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨t, ht⟩ := exists_sec A.isLB (φ := fun _ : Fin k => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (k : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := A.L) (φ := fun _ : Fin k => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (TFK (R := R) F) A.A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
  obtain ⟨c, hc⟩ := ThetaSpan.exists_value A hρ (F := F) (k := k) t
  refine ⟨t, c, ?_, hc⟩
  rintro rfl
  obtain ⟨J, hJ⟩ := exists_good' A.isLB (Z := (TFK (R := R) F).left) z
  have h1 := hc z J hJ
  have h0 : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z 0) = 0 := by
    show cst (R := R) F z 0 = 0
    rw [cst_eq, map_zero]
  rw [h0, zero_mul] at h1
  have h2 : sA t (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left z J = sval (s j) χ z J :=
    (ht _ _ z J hJ).trans ((VVRank.sval_pullTo _ _ _ _ z hJ).trans (by simp only [χ, Category.assoc]))
  have hu : IsUnit (sval (s j) χ z J) :=
    (AmpleSpan.mem_nonzeroLocus_iff_gs (s j) χ z (hJ.mem (fun _ : Fin k => (A.A.hom ⁻¹ᵁ ⊤).ι) χ)).1 hj
  rw [← h2, h1] at hu
  exact not_isUnit_zero hu

end GlobalTheory.Poinc.Origin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalIsometriesInnerAutAdelicFrameIsometry
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.FinIsoLocal

theorem bij_of_frame {A : Type} [CommRing A] {m n : ℕ} (h : n = m) (j : Matrix (Fin m) (Fin n) A) (β : GL (Fin n) A)
    (M : GL (Fin m) A) (hj : j * β.val = M.val.submatrix id (Fin.cast h)) : Function.Bijective j.mulVec := by
  subst h
  have hj' : j = M.val * (β⁻¹).val := by
    have e : M.val.submatrix id (Fin.cast rfl) = M.val := by ext a b; rfl
    rw [e] at hj
    rw [← hj, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine GlobalTheory.FinAdIdent.bij_of_inv (j' := β.val * (M⁻¹).val) ?_ ?_
  · rw [hj', Matrix.mul_assoc, ← Matrix.mul_assoc (β⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [hj', Matrix.mul_assoc, ← Matrix.mul_assoc (M⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]

end GlobalTheory.FinIsoLocal

theorem GlobalTheory.FinIsoLocal.exists_local_inner : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (i : Fin D.R.m) (j : Matrix (Fin (Wc D i).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)), GlobalTheory.CuspMult.IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ → ∃ (jl : ∀ v, GLoc D.sp.cm.sig (Yc D 0).gram v ≃ₜ* GLoc D.sp.cm.sig (Wc D i).gram v) (Φ₀ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)) (b : GfC (Yc D 0)), (∀ v, IsLatticeConj (frameLat (Yc D 0)) (frameLat (Wc D i)) (jl v)) ∧ (∀ v g, Φ₀ (locFin (Yc D 0) v g) = locFin (Wc D i) v (jl v g)) ∧ ∀ g, Φ g = Φ₀ (b * g * b⁻¹) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i j Φ hΦ
  obtain ⟨h, u, hu, -⟩ := hΦ.frame
  have hbij := GlobalTheory.FinIsoLocal.bij_of_frame h j (R.βY 0) (R.βW i * intGL D.host.F D.host.E (Wc D i).rank u) hu
  have hIs : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom (Yc D 0) (Wc D i) (Formalism.L2.Herm.Af D.host.F) j := ⟨hbij, hΦ.isom⟩
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy (Yc D 0) (Wc D i) j Φ := hΦ.conj
  obtain ⟨β₀, hβ₀, -⟩ := _root_.GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat D (Yc D 0)
  obtain ⟨β₀', hβ₀', -⟩ := _root_.GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat D (Wc D i)
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.OnePlaceOver (D := D) (∅ : Set (Formalism.L2.DIV.Pl D.host.E)) := by
    intro PP hPP; exact absurd hPP (Set.notMem_empty PP)
  obtain ⟨j₀, hL, hM⟩ := GlobalTheory.FinAdIdent.globalIsometry D (Yc D 0) (Wc D i) h (frameLat (Yc D 0)) (frameLat (Wc D i))
    β₀ β₀' 1 1 hβ₀ hβ₀' ∅ hT
  obtain ⟨Φ₀, hC₀, -⟩ := GlobalTheory.FinAdIdent.inducedIso D (Yc D 0) (Wc D i) h (frameLat (Yc D 0)) (frameLat (Wc D i))
    β₀ β₀' 1 1 hβ₀ hβ₀' ∅ j₀ hL hM
  obtain ⟨jl, h1, h2⟩ := _root_.GlobalTheory.TwistPC.isom_locComponents D (Yc D 0) (Wc D i) j₀ Φ₀ hL hC₀
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.InnerTwist.conj_inner D (Yc D 0) (Wc D i) j j₀ Φ Φ₀ hIs hL.1 hC hC₀
  exact ⟨jl, Φ₀, b, h1, h2, hb⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalLiftSectionsOnClosedSubscheme
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open TopologicalSpace Opposite H0

theorem exists_local_lift_H0On : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (I : Y.IdealSheafData) (g : sectionsOnClosedSubscheme p B I) (y : Y), ∃ (W : Y.Opens) (_ : y ∈ W) (b : Vanishing.H0 p B W), ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ W) (j : (B.pull I.subschemeι).ι) (hj : z ∈ (B.pull I.subschemeι).U j), Vanishing.H0.germ j z (TopologicalSpace.Opens.mem_top z) hj g = (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) b) := by
  intro k _ Y p B hB I g y
  obtain ⟨i, hi⟩ := exists_chart hB y
  obtain ⟨W, hyW, hWi⟩ := exists_affine hi
  obtain ⟨J, rfl⟩ : ∃ J : (B.pull I.subschemeι).ι, J PUnit.unit = i := ⟨fun _ => i, rfl⟩
  have hJ (z : I.subscheme) (hz : I.subschemeι z ∈ W.1) : z ∈ (B.pull I.subschemeι).U J :=
    mem_pull.2 (hWi hz)
  have hle : I.subschemeι ⁻¹ᵁ W.1 ≤ ⊤ ⊓ (B.pull I.subschemeι).U J :=
    fun z hz => ⟨trivial, hJ z hz⟩
  obtain ⟨a, ha⟩ := I.subschemeι_app_surjective W (resG I.subscheme hle (g.loc J))
  let b : H0 p B W.1 := (LB.chartEquiv hB (J PUnit.unit) hWi).symm a
  have hb (x : Y) (hx : x ∈ W.1) : germ (J PUnit.unit) x hx (hWi hx) b = ger x hx a := by
    conv_rhs =>
      rw [← (LB.chartEquiv hB (J PUnit.unit) hWi).apply_symm_apply a, LB.chartEquiv_apply,
        ger_resG]
    rfl
  refine ⟨W.1, hyW, b, fun z hz j hj => ?_⟩
  have h0 : germ J z (Opens.mem_top z) (hJ z hz) g =
      (I.subschemeι.stalkMap z).hom (germ (J PUnit.unit) (I.subschemeι z) hz (hWi hz) b) := by
    rw [hb, germ_apply, ← ger_resG hle z hz, ← ha]
    exact (Scheme.Hom.germ_stalkMap_apply _ _ z hz a).symm
  rw [germ_change j J z _ hj (hJ z hz), h0,
    germ_change (j PUnit.unit) (J PUnit.unit) _ hz (mem_pull.1 hj) (hWi hz), map_mul,
    tr_pull B I.subschemeι z hj (hJ z hz), Units.coe_map]
  rfl

end GlobalTheory.Vanishing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxIdealSmulMemOfLtOfRelIndexNeZero
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero (F V : Type) [Field F] [NumberField F]
    [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
    (N₀ N : Submodule (𝓞 F) V) (hlt : N₀ < N)
    (hidx : N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0) :
    ∃ (u : V) (p : Ideal (𝓞 F)), p.IsMaximal ∧ u ∈ N ∧ u ∉ N₀ ∧ ∀ π ∈ p, π • u ∈ N₀ := by
  classical
  set P : Submodule (𝓞 F) N := N₀.comap N.subtype with hP
  have hPne : P ≠ ⊤ := by
    intro h
    obtain ⟨v, hvN, hvN₀⟩ := SetLike.exists_of_lt hlt
    have hv : (⟨v, hvN⟩ : N) ∈ P := h ▸ Submodule.mem_top
    exact hvN₀ hv
  haveI : Nontrivial (N ⧸ P) := Submodule.Quotient.nontrivial_iff.2 hPne
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty (𝓞 F) (N ⧸ P)
  obtain ⟨hprime, x, hx⟩ := (isAssociatedPrime_iff (R := 𝓞 F) (M := N ⧸ P)).1 hp
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P x
  have hmem : ∀ r : 𝓞 F, r ∈ p ↔ r • (y : V) ∈ N₀ := by
    intro r
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, hP, Submodule.mem_comap]
    rfl
  set n := N₀.toAddSubgroup.relIndex N.toAddSubgroup with hn
  have hkill : n • (y : V) ∈ N₀ := by
    have h := AddSubgroup.nsmul_index_mem (N₀.toAddSubgroup.addSubgroupOf N.toAddSubgroup)
      (⟨y.1, y.2⟩ : N.toAddSubgroup)
    exact AddSubgroup.mem_addSubgroupOf.1 h
  have hnp : ((n : ℕ) : 𝓞 F) ∈ p := by
    rw [hmem, Nat.cast_smul_eq_nsmul]
    exact hkill
  have hp0 : p ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hnp
    exact hidx (by exact_mod_cast hnp)
  refine ⟨(y : V), p, Ideal.IsPrime.isMaximal hprime hp0, y.2, ?_, fun π hπ => (hmem π).1 hπ⟩
  intro hy
  apply hprime.ne_top
  rw [eq_top_iff]
  intro r _
  rw [hmem]
  exact N₀.smul_mem r hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfPolarisedGenericFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

namespace GlobalTheory.ThetaDomain

theorem exists_sec_ne_zero_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) →
    ∃ (σ : LB.Sec t.PP.L) (k : t.PP.L.ι), σ.f k ≠ 0 := by
  intro E _ _ _ H R _ _ _ t hp
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨A, -, gen, -, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h₁ h₂ E H R t hp
  obtain ⟨O, hO, θ, hθ, -, nz⟩ := PushInv.pushInvertible_any h₂.secBaseChangeAny h₁.globalSectionsRank _ A
    (IsLocalRing.closedPoint (FractionRing R))
  obtain ⟨g, i, -, hi⟩ := nz _ hO
  obtain ⟨w, hw⟩ := LBIso.symm hL
  obtain ⟨s, hs⟩ := GlobalTheory.ThetaLocal.exists_sec_pull A.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom (jK R)))
    gen.hom.left w hw (O := A.A.hom ⁻¹ᵁ O) (fun z _ => by
      change A.A.hom (gen.hom.left z) ∈ O
      rwa [Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) (A.A.hom (gen.hom.left z))
        (IsLocalRing.closedPoint (FractionRing R))]) θ hθ
  have eg : gen.hom.left (gen.inv.left g) = g := congrArg (fun q : A.A ⟶ A.A => q.left g) gen.inv_hom_id
  obtain ⟨k, hk⟩ := hs (gen.inv.left g) i (by rw [eg]; exact hi)
  have hsk : s.f k ≠ 0 := fun e => by
    rw [e, Scheme.basicOpen_zero] at hk
    exact hk
  have := t.semi.separated
  have := t.semi.quasiCompact
  have : CompactSpace t.G.left := QuasiCompact.compactSpace_of_compactSpace t.G.hom
  have : QuasiSeparatedSpace t.G.left := quasiSeparatedSpace_of_quasiSeparated t.G.hom
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R (FractionRing R) (algebraMap R _)
    (RingHom.flat_algebraMap_iff.2 inferInstance) t.G.left t.G.hom _ _ _
    (IsPullback.of_hasPullback t.G.hom (jK R)) t.PP.L t.PP.isLB s
  by_contra hcon
  push Not at hcon
  refine hsk (fn_ext fun z hz => ?_)
  have hz' : pullback.fst t.G.hom (jK R) z ∈ t.PP.L.U (k PUnit.unit) := Set.mem_iInter.1 hz PUnit.unit
  rw [LBGerm.gs_zero _ z _ hz]
  refine (hu z (k PUnit.unit) hz').trans (Finset.sum_eq_zero fun i _ => ?_)
  rw [hcon, LBGerm.gs_zero _ z _ hz', mul_zero]

end GlobalTheory.ThetaDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonalStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧ diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  first | exact @GlobalTheory.SiegelTorusInf.exists_diag_infGL | exact GlobalTheory.SiegelTorusInf.exists_diag_infGL | (intros; apply GlobalTheory.SiegelTorusInf.exists_diag_infGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefinitePairClassesFixedMinpolyDegreeOneStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_definitePair_classes_fixed_minpoly_degree_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      ∀ P0 : Polynomial G.F, {q : GlobalTheory.LKDef.DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
        (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | (exact @GlobalTheory.LKDefFin.finite_classes_of_pol) | (exact GlobalTheory.LKDefFin.finite_classes_of_pol) | (intros; apply GlobalTheory.LKDefFin.finite_classes_of_pol <;> assumption)
end

