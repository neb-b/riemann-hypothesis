module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandInvariantsSymmetricOfDerivativeAdjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
open scoped Matrix

noncomputable section

namespace GlobalTheory.GelfSymm

open scoped Matrix

open GlobalTheory.Mem.RealTranslate (derEnd)
open GlobalTheory.RegSch (wordDer)

theorem prod_map_neg {R : Type} [Ring R] [Algebra ℂ R] :
    ∀ l : List R, (l.map fun a => -a).prod = (-1 : ℂ) ^ l.length • l.prod
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_neg l, List.prod_cons, List.length_cons, pow_succ,
      mul_smul_comm, neg_mul, mul_comm, mul_smul, neg_one_smul, smul_neg]

theorem sum_words_rev {R : Type} [Ring R] [Algebra ℂ R] {n : ℕ} (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] R)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (-(M * (Matrix.single (idx a) (idx (a + 1)) 1)ᵀ * M⁻¹))).reverse.prod =
    (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (Matrix.single (idx a) (idx (a + 1)) 1)).prod := by
  let ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Rᵐᵒᵖ := (MulOpposite.opLinearEquiv ℂ).toLinearMap ∘ₗ φ
  have h := congrArg MulOpposite.unop (GlobalTheory.RegSch.GelfCyc.sum_words ψ M hM k)
  have e : ∀ l : List R, (l.map MulOpposite.op).prod = MulOpposite.op l.reverse.prod := fun l => by
    rw [MulOpposite.op_list_prod, List.map_reverse, List.reverse_reverse]
  have e' : ∀ l : List R, (l.map MulOpposite.op).reverse.prod = MulOpposite.op l.prod := fun l =>
    (MulOpposite.op_list_prod l).symm
  have hψ : ∀ g : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ, (List.ofFn fun a => ψ (g a)) = (List.ofFn fun a => φ (g a)).map MulOpposite.op := by
    intro g; rw [List.map_ofFn]; rfl
  have hs : ∀ f : (Fin (k + 1) → Fin n) → R, ∑ i, MulOpposite.op (f i) = MulOpposite.op (∑ i, f i) :=
    fun f => (map_sum MulOpposite.opAddEquiv f _).symm
  simp only [hψ, e, e', hs, MulOpposite.unop_smul, MulOpposite.unop_op] at h
  exact h

end GlobalTheory.GelfSymm

namespace GlobalTheory.GelfSymm

open scoped Matrix
open GlobalTheory.Mem.RealTranslate (derEnd)
open GlobalTheory.RegSch (wordDer)

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem wordDer_append (τ : D.what₂.Tau) (l l' : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : GA D V → ℂ) :
    wordDer θ V τ (l ++ l') f = wordDer θ V τ l (wordDer θ V τ l' f) := by
  simp only [wordDer, List.foldr_append]

theorem wordDer_mem {τ : D.what₂.Tau} {A : Submodule ℂ (GA D V → ℂ)} (hA : ∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) {f : GA D V → ℂ} (hf : f ∈ A) : wordDer θ V τ l f ∈ A := by
  induction l with
  | nil => exact hf
  | cons Z l ih => exact hA Z _ ih

theorem adj_word {τ : D.what₂.Tau} {A : Submodule ℂ (GA D V → ℂ)} (hA : ∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A)
    (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ)
    (hb : ∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) =
      b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) :
    ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), ∀ x ∈ A, ∀ y ∈ A,
      b x (wordDer θ V τ l y) =
        b (wordDer θ V τ (l.reverse.map fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y
  | [], x, _, y, _ => rfl
  | Z :: l, x, hx, y, hy => by
    show b x (RderC θ V τ Z (wordDer θ V τ l y)) = _
    rw [hb Z x hx _ (wordDer_mem hA l hy), adj_word hA b hb l _ (hA _ _ hx) y hy, List.reverse_cons, List.map_append,
      wordDer_append]
    rfl

end GlobalTheory.GelfSymm


open GlobalTheory.Mem.RealTranslate (derEnd) in
open GlobalTheory.RegSch (wordDer) in
open GlobalTheory.GelfSymm in
theorem GlobalTheory.GelfSymm.gelf_symm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (A : Submodule ℂ (GA D V → ℂ)), A ≤ GlobalTheory.Mem.AutSpace.SmFun θ V →
    (∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A) → ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
    (∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) →
    ∀ k, ∀ x ∈ A, ∀ y ∈ A, b x (gelf θ V τ k y) = b (gelf θ V τ k x) y := by
  intro D θ V hθ τ A hAS hA b hb k x hx y hy
  have hu : IsUnit (gramAt D V τ).det := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hM : IsUnit ((gramAt D V τ)⁻¹).det := Matrix.isUnit_nonsing_inv_det_iff.2 hu
  let E : (Fin (k + 1) → Fin V.rank) → Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun idx a => Matrix.single (idx a) (idx (a + 1)) 1
  have hg : ∀ f, gelf θ V τ k f = ∑ idx, wordDer θ V τ (List.ofFn (E idx)) f := by
    intro f
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [wordDer, ← List.foldr_map (f := RderC θ V τ) (g := fun A acc => A acc), List.map_ofFn]
    rfl
  have hs : ∀ i j, (gramAt D V τ)⁻¹ * Matrix.conjTranspose (Matrix.single i j (1 : ℂ)) * gramAt D V τ =
      -(-((gramAt D V τ)⁻¹ * (Matrix.single i j (1 : ℂ))ᵀ * (gramAt D V τ)⁻¹⁻¹)) := by
    intro i j
    rw [neg_neg, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.conjTranspose_single, Matrix.transpose_single, star_one]
  have key : ∑ idx, (((List.ofFn (E idx)).reverse.map
        fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ)).prod =
      ∑ idx, ((List.ofFn (E idx)).map (derEnd hθ τ)).prod := by
    have h1 := sum_words_rev (derEnd hθ τ) (gramAt D V τ)⁻¹ hM k
    have e : ∀ idx, ((List.ofFn (E idx)).reverse.map
        fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ) =
        (List.ofFn fun a => derEnd hθ τ (-((gramAt D V τ)⁻¹ * (E idx a)ᵀ * (gramAt D V τ)⁻¹⁻¹))).reverse.map
          fun a => -a := by
      intro idx
      rw [List.map_map, List.map_reverse, List.map_reverse, List.map_ofFn, List.map_ofFn]
      congr 1
      congr 1
      funext a
      simp only [Function.comp_apply, ← map_neg, neg_neg]
      simpa only [E, neg_neg] using congrArg (derEnd hθ τ) (hs (idx a) (idx (a + 1)))
    simp only [e, prod_map_neg, List.length_reverse, List.length_ofFn, List.map_ofFn]
    rw [← Finset.smul_sum, h1, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
    rfl
  have hxS : x ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := hAS hx
  have wx : ∀ w, wordDer θ V τ w x = ((w.map (derEnd hθ τ)).prod ⟨x, hxS⟩).1 :=
    fun w => GlobalTheory.RegSch.GelfCyc.wordDer_eq hθ τ w ⟨x, hxS⟩
  have hgx : ∑ idx, wordDer θ V τ ((List.ofFn (E idx)).reverse.map
      fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x = gelf θ V τ k x := by
    rw [hg x]
    simp only [wx]
    rw [← Submodule.coe_sum, ← Submodule.coe_sum, ← LinearMap.sum_apply, ← LinearMap.sum_apply, key]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hg y, map_sum, ← hgx, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun idx _ => adj_word hA b hb _ x hx y hy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HomLatticeCosetIndicatorPrimePowersIntegralCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetIndCompare

variable {D : D7}

theorem frame_smul {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (a : AE D) (Y : Mx D m n) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((a • Y).map (toEAf D))) β.val =
      toEAf D a • HMul.hMul (HMul.hMul (β'⁻¹).val (Y.map (toEAf D))) β.val := by
  have : (a • Y).map (toEAf D) = toEAf D a • Y.map (toEAf D) := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [this]
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem frame_sub {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (Y Z : Mx D m n) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((Y - Z).map (toEAf D))) β.val =
      HMul.hMul (HMul.hMul (β'⁻¹).val (Y.map (toEAf D))) β.val -
        HMul.hMul (HMul.hMul (β'⁻¹).val (Z.map (toEAf D))) β.val := by
  rw [Matrix.map_sub _ (map_sub (toEAf D)), Matrix.mul_sub, Matrix.sub_mul]

theorem frame_incA {m n : ℕ} (y : Matrix (Fin m) (Fin n) D.host.E) :
    (y.map (incA D)).map (toEAf D) = y.map (eToEAf D) := by
  ext i j; rfl

theorem frame_mem_idS {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {β : GL (Fin n) (EAf D)} {β' : GL (Fin m) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') (I : Ideal (𝓞 D.host.E))
    {y : GlobalTheory.ChiGrid.homLat Λ Λ'} (hy : y ∈ (I • ⊤ : Submodule (𝓞 D.host.E) (GlobalTheory.ChiGrid.homLat Λ Λ'))) (i : Fin m)
    (j : Fin n) : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I,
      (t : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val ((y : Matrix (Fin m) (Fin n) D.host.E).map (eToEAf D))) β.val i j := by
  have h1 : (y : Matrix (Fin m) (Fin n) D.host.E) ∈ I • GlobalTheory.ChiGrid.homLat Λ Λ' := by
    have := Submodule.mem_map_of_mem (f := (GlobalTheory.ChiGrid.homLat Λ Λ').subtype) hy
    rwa [Submodule.map_smul'', Submodule.map_subtype_top] at this
  have h2 : (y : Matrix (Fin m) (Fin n) D.host.E).map (eToEAf D) ∈
      GlobalTheory.FunObj.HatFrame.genGrp D.host.F (I • GlobalTheory.ChiGrid.homLat Λ Λ') :=
    by
      unfold GlobalTheory.FunObj.HatFrame.genGrp
      apply AddSubgroup.subset_closure
      exact ⟨1, one_mem _, _, h1, by ext a b; rfl⟩
  exact GlobalTheory.FunObj.HatFrame.genGrp_le_frGrp hβ hβ' (H := GlobalTheory.ChiGrid.homLat Λ Λ') (fun _ hx => hx) I h2 i j

theorem frame_smul_incA {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (a : AE D)
    (y : Matrix (Fin m) (Fin n) D.host.E) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((a • y.map (incA D)).map (toEAf D))) β.val =
      toEAf D a • HMul.hMul (HMul.hMul (β'⁻¹).val (y.map (eToEAf D))) β.val := by
  rw [frame_smul, frame_incA]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem quot_iff (I : Ideal (𝓞 E)) (y : E ⊗[F] Formalism.L2.Herm.Af F) (r : 𝓞 E) :
    (∃ h : y ∈ Formalism.L2.Herm.intAf F E, Ideal.Quotient.mk (Formalism.L2.DIV.idS F I) ⟨y, h⟩ =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS F I) (Formalism.L2.DIV.oToS F E r)) ↔
    y ∈ Formalism.L2.Herm.intAf F E ∧ ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - Formalism.L2.DIV.oToS F E r := by
  constructor
  · rintro ⟨h, hq⟩
    exact ⟨h, _, Ideal.Quotient.eq.1 hq, rfl⟩
  · rintro ⟨h, t, ht, et⟩
    refine ⟨h, Ideal.Quotient.eq.2 ?_⟩
    have : (⟨y, h⟩ : Formalism.L2.Herm.intAf F E) - Formalism.L2.DIV.oToS F E r = t := Subtype.ext et.symm
    rw [this]; exact ht

theorem step_fwd {I : Ideal (𝓞 E)} {y N a s : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hq : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - N)
    (hv : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a - N)
    (hs : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - s) :
    ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - s * a := by
  obtain ⟨t1, h1, e1⟩ := hq
  obtain ⟨t2, h2, e2⟩ := hv
  obtain ⟨t3, h3, e3⟩ := hs
  refine ⟨t1 - t2 + t3 * ⟨a, ha⟩, add_mem (sub_mem h1 h2) (Ideal.mul_mem_right _ _ h3), ?_⟩
  simp only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, e1, e2, e3]
  ring

theorem step_bwd {I : Ideal (𝓞 E)} {y N a a' s : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hN : N ∈ Formalism.L2.Herm.intAf F E) (hsi : s ∈ Formalism.L2.Herm.intAf F E)
    (ht : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - s * a')
    (hu : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a' - a)
    (hv : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a - N)
    (hs : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - s) :
    y ∈ Formalism.L2.Herm.intAf F E ∧ ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - N := by
  obtain ⟨t1, h1, e1⟩ := ht
  obtain ⟨t2, h2, e2⟩ := hu
  obtain ⟨t3, h3, e3⟩ := hv
  obtain ⟨t4, h4, e4⟩ := hs
  have hy : y = ((t1 + ⟨s, hsi⟩ * t2 + ⟨s, hsi⟩ * ⟨a, ha⟩ : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
    simp only [Subring.coe_add, Subring.coe_mul, e1, e2]
    ring
  refine ⟨hy ▸ Subtype.property _, t1 + ⟨s, hsi⟩ * t2 - t4 * ⟨a, ha⟩ + t3,
    add_mem (sub_mem (add_mem h1 (Ideal.mul_mem_left _ _ h2)) (Ideal.mul_mem_right _ _ h4)) h3, ?_⟩
  simp only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, e1, e2, e3, e4]
  ring

end Gen

theorem cmpS_mk (I : Ideal (𝓞 D.host.E)) (r : 𝓞 D.host.E) :
    Formalism.L2.DIV.cmpS D.host.F I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E r) := by
  unfold Formalism.L2.DIV.cmpS
  exact Ideal.quotientMap_mk


set_option maxHeartbeats 1600000 in
theorem mem_cosSet_iff {S T : GlobalTheory.Grid.Node D} {e : AE D} (hS : Formalism.L2.DIV.IsFrame S.β S.Λ)
    (hT : Formalism.L2.DIV.IsFrame T.β T.Λ) (he0 : infPart D e = 0) {I : Ideal (𝓞 D.host.E)}
    (he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1s : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) = 1 - toEAf D e)
    (c : GlobalTheory.Grid.Coset S T I) (r : Fin T.V.rank → Fin S.V.rank → 𝓞 D.host.E)
    (hcos : ∀ i j, Formalism.L2.DIV.cmpS D.host.F I (c i j) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)))
    (x₀ : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (hx₀ : x₀ ∈ GlobalTheory.ChiGrid.homLat S.Λ T.Λ)
    (hN : ∀ i j, ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) =
      HMul.hMul (HMul.hMul (T.β⁻¹).val (x₀.map (eToEAf D))) S.β.val i j -
        (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j) : EAf D)) (x : WO S.V T.V) :
    (IsHalf e x ∧ InCosetOf S T I c x) ↔ x ∈ GlobalTheory.ChiGrid.cosSet e (GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩) := by
  have hAint : ∀ i j, (HMul.hMul (HMul.hMul (T.β⁻¹).val (x₀.map (eToEAf D))) S.β.val :
      Matrix (Fin T.V.rank) (Fin S.V.rank) (EAf D)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.FunObj.HatFrame.frame_int hS hT hx₀

  have hfr : ∀ y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E,
      HMul.hMul (HMul.hMul (T.β⁻¹).val ((x - e • y.map (incA D)).map (toEAf D))) S.β.val =
        frMapO S.V T.V S.β T.β x - toEAf D e • HMul.hMul (HMul.hMul (T.β⁻¹).val (y.map (eToEAf D))) S.β.val := by
    intro y
    rw [frame_sub, frame_smul_incA]; rfl
  change _ ↔ IsHalf e x ∧ ∃ x₀' : GlobalTheory.ChiGrid.homLat S.Λ T.Λ, GlobalTheory.ChiGrid.Cos.mk I x₀' = GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩ ∧
    x - e • (x₀' : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈
      GlobalTheory.ChiGrid.hatMx (I • GlobalTheory.ChiGrid.homLat S.Λ T.Λ)
  refine and_congr_right fun hx => ?_
  have hx' : ∀ i j, e * x i j = x i j := hx
  have hinf : ∀ (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) i j,
      infPart D ((x - e • y.map (incA D)) i j) = 0 := by
    intro y i j
    have h1 : (x - e • y.map (incA D)) i j = e * (x i j - y.map (incA D) i j) := by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, hx' i j]
    rw [h1, map_mul, he0, zero_mul]
  constructor
  · intro hc
    unfold InCosetOf at hc
    refine ⟨⟨x₀, hx₀⟩, rfl, ?_⟩
    rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D S.Λ T.Λ S.β T.β hS hT I]
    refine ⟨hinf x₀, fun i j => ?_⟩
    rw [hfr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have hq := ((quot_iff I _ (r i j)).1 ((hc i j).imp fun _ h => h.trans (hcos i j))).2
    exact step_fwd (hAint i j) hq (hN i j) h1s
  · rintro ⟨y, hyc, hmem⟩
    rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D S.Λ T.Λ S.β T.β hS hT I] at hmem
    have hdiff := (Submodule.Quotient.eq _).1 hyc
    unfold InCosetOf
    intro i j
    have et := hmem.2 i j
    rw [hfr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at et
    have hu := frame_mem_idS hS hT I hdiff i j
    rw [Submodule.coe_sub, Matrix.map_sub _ (map_sub (eToEAf D)), Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply] at hu
    have h := step_bwd (hAint i j) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)).2 he_int et hu (hN i j) h1s
    exact ((quot_iff I _ (r i j)).2 h).imp fun _ h => h.trans (hcos i j).symm

theorem cosetInd_eq_cosInd {S T : GlobalTheory.Grid.Node D} {e : AE D} (hS : Formalism.L2.DIV.IsFrame S.β S.Λ)
    (hT : Formalism.L2.DIV.IsFrame T.β T.Λ) (he0 : infPart D e = 0) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥)
    (he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1s : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) = 1 - toEAf D e)
    (c : GlobalTheory.Grid.Coset S T I) :
    ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ I, GlobalTheory.Grid.cosetInd S T e I c = GlobalTheory.ChiGrid.cosInd e κ := by
  choose r hr using fun i j => Ideal.Quotient.mk_surjective (I := I) (c i j)
  obtain ⟨x₀, hx₀, hN⟩ := _root_.GlobalTheory.FunObj.HatFrame.homLat_approx_mod S.Λ T.Λ S.β T.β hS hT I hI (fun i j => Formalism.L2.DIV.oToS D.host.F D.host.E (r i j))
  have hcos : ∀ i j, Formalism.L2.DIV.cmpS D.host.F I (c i j) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)) := fun i j =>
    (congrArg (Formalism.L2.DIV.cmpS D.host.F I) (hr i j)).symm.trans (cmpS_mk I (r i j))
  refine ⟨GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩, funext fun x => ?_⟩
  have key := mem_cosSet_iff hS hT he0 he_int h1s c r hcos x₀ hx₀ hN x
  unfold GlobalTheory.Grid.cosetInd GlobalTheory.ChiGrid.cosInd
  classical
  rw [Set.indicator_apply]
  by_cases h : IsHalf e x ∧ InCosetOf S T I c x
  · rw [if_pos h, if_pos (key.1 h)]; rfl
  · rw [if_neg h, if_neg fun h' => h (key.2 h')]

theorem coset_eq_cos : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  intro D S T e P d hS hT he c
  obtain ⟨he0, he_int, h1s⟩ := _root_.GlobalTheory.IdemSumIdeal.isIdemSum_props e P d he
  refine cosetInd_eq_cosInd hS hT he0 ?_ he_int h1s c
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

end GlobalTheory.CosetIndCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointIntegralIffDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory.DualRed

theorem adjA_entry : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO S T) (k : Fin S.rank) (j : Fin T.rank), adjA S T βS βT 1 x k j = Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (T.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) (fun c => toEAf D (x c k)) (fun c => βT.1 c j) := by
  intro D S T hS βS βT x k j
  have hE : toEAf D = GlobalTheory.LevSplit.finSw D := rfl
  unfold adjA frMapAdj
  rw [hS, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, map_one, one_smul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.map_mul]
  unfold Formalism.UG.hform
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, hE, GlobalTheory.LevSplit.finSw_cA,
    GlobalTheory.LevSplit.finSw_incA, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem adj_int_iff : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βT ΛT → ∀ (J : Ideal (𝓞 D.host.E)), Squarefree J → ∀ x : WO S T, IsFinPt x → ((IsIntM (adjA S T βS βT 1 x) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E, J ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 x) = 0) ↔ x ∈ hatA S T (tens (stdL D.host.E S.rank) (conjI J • ΛT))) := by
  intro D S T hS ΛT hsd βS βT hfr J hJ x hx
  have hJ0 : J ≠ ⊥ := by
    rw [← Submodule.zero_eq_bot]
    exact hJ.ne_zero
  rw [GlobalTheory.TensColRead.mem_hatA_stdL_iff D S T _ x hx]
  simp only [GlobalTheory.FrameIdeal.mem_hatL_conjI_iff_hform D T ΛT hsd βT hfr J hJ0, ← adjA_entry D S T hS βS βT x]
  unfold IsIntM redM
  constructor
  · rintro ⟨hint, hred⟩ k j
    refine ⟨⟨_, hint k j⟩, GlobalTheory.LiftLevel.mem_idS hJ fun PP hPP => ?_, rfl⟩
    have h0 := congrFun (congrFun (hred PP hPP) k) j
    simpa only [Matrix.zero_apply, Pi.zero_apply, dif_pos (hint k j)] using h0
  · intro h
    have hint : ∀ k j, adjA S T βS βT 1 x k j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro k j
      obtain ⟨s, -, hs⟩ := h k j
      rw [← hs]
      exact s.2
    refine ⟨hint, fun PP hPP => ?_⟩
    funext k j
    obtain ⟨s, hsI, hs⟩ := h k j
    have hse : (⟨adjA S T βS βT 1 x k j, hint k j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = s := Subtype.ext hs.symm
    simp only [Matrix.zero_apply, Pi.zero_apply, dif_pos (hint k j), hse]
    exact GlobalTheory.LiftLevel.resS_eq_zero hPP hsI

end GlobalTheory.DualRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartz
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree

theorem isDatum_add : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} [AddCommGroup Z]
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ),
    IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + Φ') (f + f') := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z _ crd Φ Φ' f f' h h'
  refine ⟨add_mem h.1 h'.1, fun u => ?_⟩
  have e : M.co.rho ψ u (Φ + Φ') = M.co.rho ψ u Φ + M.co.rho ψ u Φ' := by
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]
    ring
  rw [e, GlobalTheory.WeilM.thetaSum_add F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ h.1)
    (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ' h'.1), h.2 u, h'.2 u]
  rfl

end GlobalTheory.SquareAgree
end
end

