module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingLaplacianPolySoluti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormBoxStarNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0207
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingFormsGl
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HCSmoothGL

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem isAddHaarMeasure_volume_Lie : (volume : Measure (Lie E a)).IsAddHaarMeasure := by
  haveI : SigmaFinite (volume : Measure (InfinitePlace E → ℂ)) := inferInstance
  haveI : (volume : Measure (Fin a → InfinitePlace E → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : SigmaFinite (volume : Measure (Fin a → InfinitePlace E → ℂ)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

variable [_root_.NumberField.IsTotallyComplex E]


theorem exists_smooth_beta : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ β : Lie E a → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ invSet E a ∧ ∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  intro E _ _ _ a L W hW X hX N
  have hν := isAddHaarMeasure_volume_Lie (E := E) (a := a)
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite E a L W hW X hX N
  obtain ⟨α, hα, h⟩ := _root_.GlobalTheory.GLParametrix.exists_test_reproducing E a volume hν p hp0
  refine ⟨α, hα.1, hα.2.1, hα.2.2, fun φ hφm x => ?_⟩
  have hφ := hp φ hφm
  have h1 := h (chart φ.1 x) (φ.2 x) (fun y hy => by
    rw [Polynomial.aeval_eq_sum_range] at hφ
    have e := congrArg (fun ψ : Sm E a => chart ψ.1 x y) hφ
    rw [LinearMap.sum_apply] at e
    simp only [LinearMap.smul_apply] at e
    rw [GlobalTheory.HCFiniteSm.chart_sum' _ _ (fun k => (GlobalTheory.HCAlpha.lapOp E a ^ k) φ) _ hy] at e
    have e0 : chart (0 : Sm E a).1 x y = 0 := by simp [chart]
    rw [e0] at e
    rw [← e, GlobalTheory.HCAlpha.polyF, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.HCAlpha.chart_lapOp_pow E a φ x k y hy])
  simp only [mul_comm (chart φ.1 x _)]
  rw [h1]
  have := chart_val φ.1 x 1
  simpa using this

end GlobalTheory.HCSmoothGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProduct
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblDiagForm

open MeasureTheory GlobalTheory.DiagForm

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

local instance measAfD {F : Type} [Field F] [NumberField F] : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
local instance borelAfD {F : Type} [Field F] [NumberField F] : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

theorem lDiag_translate {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) (φ' : (κ ⊕ κ → AF F) → ℂ) (x : κ → AF F)
    (h : ∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + x) (u + x))) : lDiag F κ φ' = lDiag F κ φ := by
  have hi := integrable_resD hφ
  have e : resD F κ φ' = fun p => resD F κ φ (p + shiftOf x) := by
    funext p
    show φ' (Sum.elim (glue p) (glue p)) = φ (Sum.elim (glue (p + shiftOf x)) (glue (p + shiftOf x)))
    rw [h, glue_add_shiftOf]
  rw [lDiag, LinearMap.comp_apply, LinearMap.comp_apply, e,
    Lext_apply _ (hi.comp_add_right (shiftOf x)), Lext_apply _ hi]
  exact integral_add_right_eq_self _ _

theorem exists_form : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Ψ ∈ schA F κ, Ψ ≠ 0 →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ φ ∈ schA F (κ ⊕ κ), ∀ (φ' : (κ ⊕ κ → AF F) → ℂ) (x : κ → AF F),
      (∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + x) (u + x))) → l φ' = l φ) ∧ l (GlobalTheory.InertDbl.dblFun Ψ) ≠ 0 := by
  intro F _ _ κ _ Ψ hΨ hne
  exact ⟨lDiag F κ, lDiag_adm, fun φ hφ φ' x h => lDiag_translate hφ φ' x h,
    GlobalTheory.DiagSq.lDiag_boxFun_star_ne F κ Ψ hΨ hne⟩

end GlobalTheory.DblDiagForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittFrameInitCols
section
noncomputable section

namespace GlobalTheory.AdjugateAppendColumn

open Matrix

section General

variable {E : Type} [Field E] (s : E →+* E)

def adj {a b : Type} (A : Matrix a b E) : Matrix b a E := (A.map s)ᵀ

theorem adj_mul {a b c : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b c E) :
    adj s (A * B) = adj s B * adj s A := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one {a : Type} [DecidableEq a] : adj s (1 : Matrix a a E) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem adj_sub {a b : Type} (A B : Matrix a b E) : adj s (A - B) = adj s A - adj s B := by
  ext i j; simp [adj]

theorem adj_smul {a b : Type} (c : E) (A : Matrix a b E) : adj s (c • A) = s c • adj s A := by
  ext i j; simp [adj]

theorem adj_adj (hs : ∀ x, s (s x) = x) {a b : Type} (A : Matrix a b E) : adj s (adj s A) = A := by
  ext i j; simp [adj, hs]

variable {n m : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_left_inv {X : Matrix (Fin n) (Fin m) E} (hX : LinearIndependent E Xᵀ) :
    ∃ L : Matrix (Fin m) (Fin n) E, L * X = 1 := by
  have hi : Function.Injective X.mulVec := Matrix.mulVec_injective_iff.2 hX
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' X) (LinearMap.ker_eq_bot.2 hi)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem exists_dual [CharZero E] (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (hd : J.det ≠ 0)
    {X : Matrix (Fin n) (Fin m) E} (hX : LinearIndependent E Xᵀ) (h0 : adj s X * J * X = 0) :
    ∃ Y : Matrix (Fin n) (Fin m) E, adj s X * J * Y = 1 ∧ adj s Y * J * X = 1 ∧ adj s Y * J * Y = 0 := by
  obtain ⟨L, hL⟩ := exists_left_inv hX
  have flip : ∀ Z : Matrix (Fin n) (Fin m) E, adj s X * J * Z = 1 → adj s Z * J * X = 1 := fun Z hZ => by
    have := congrArg (adj s) hZ
    rwa [adj_mul, adj_mul, adj_adj s hs, hJ, adj_one, ← Matrix.mul_assoc] at this
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) (Fin m) E, adj s X * J * Z = 1 := ⟨J⁻¹ * adj s L, by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd.isUnit, ← adj_mul, hL, adj_one]⟩
  obtain ⟨G, hG⟩ : ∃ G, G = adj s Z * J * Z := ⟨_, rfl⟩
  have h1 : adj s X * J * (Z - (2 : E)⁻¹ • (X * G)) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, h0, hZ, Matrix.zero_mul, smul_zero, sub_zero]
  refine ⟨_, h1, flip _ h1, ?_⟩
  have hGG : adj s G = G := by
    rw [hG, adj_mul, adj_mul, adj_adj s hs, hJ, Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc _ X G, flip _ h1, Matrix.one_mul, adj_sub, adj_smul, adj_mul, hGG,
    Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc G, Matrix.mul_assoc G, hZ,
    Matrix.mul_one, ← hG, map_inv₀, map_ofNat, sub_sub, ← add_smul, show (2 : E)⁻¹ + 2⁻¹ = 1 by norm_num, one_smul, sub_self]

theorem gram_apply {a b : Type} (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) (i : a) (j : b) :
    (adj s A * J * B) i j = (fun k => s (Aᵀ i k)) ⬝ᵥ J *ᵥ (Bᵀ j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]; rfl

theorem form_symm (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (x y : Fin n → E) :
    s ((fun k => s (x k)) ⬝ᵥ J *ᵥ y) = (fun k => s (y k)) ⬝ᵥ J *ᵥ x := by
  have e : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, e, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def app (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) : Matrix (Fin n) (Fin (m + 1)) E :=
  (Matrix.of (Fin.snoc (α := fun _ => Fin n → E) Xᵀ z))ᵀ

theorem app_transpose (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) :
    (app X z)ᵀ = Fin.snoc (α := fun _ => Fin n → E) Xᵀ z := rfl

theorem app_last (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) : (app X z)ᵀ (Fin.last m) = z :=
  Fin.snoc_last (α := fun _ => Fin n → E) z Xᵀ

theorem app_cast (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) (i : Fin m) : (app X z)ᵀ i.castSucc = Xᵀ i :=
  Fin.snoc_castSucc (α := fun _ => Fin n → E) z Xᵀ i

theorem exists_ext [CharZero E] (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (hd : J.det ≠ 0) (k : ℕ) :
    ∀ (m : ℕ) (C : Matrix (Fin n) (Fin m) E), n ≤ m + k → LinearIndependent E Cᵀ → adj s C * J * C = 0 →
      ∃ (m' : ℕ) (hm : m ≤ m') (X Y : Matrix (Fin n) (Fin m') E), adj s X * J * X = 0 ∧ adj s Y * J * Y = 0 ∧
        adj s X * J * Y = 1 ∧ (∀ z : Fin n → E, (adj s X * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 →
          (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z = 0) ∧ X.submatrix id (Fin.castLE hm) = C := by
  have step : ∀ (m : ℕ) (C Y : Matrix (Fin n) (Fin m) E) (z : Fin n → E), LinearIndependent E Cᵀ → adj s C * J * C = 0 →
      adj s Y * J * C = 1 → (adj s C * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 → (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z ≠ 0 →
      LinearIndependent E (app C z)ᵀ ∧ adj s (app C z) * J * app C z = 0 := by
    intro m C Y z hC h0 h1 a b c hz
    constructor
    · rw [app_transpose]
      refine linearIndependent_finSnoc.2 ⟨hC, fun hm => hz ?_⟩
      obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hm
      have e : C *ᵥ u = z := by
        rw [← hu]; funext i; simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [← e, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at b
      rw [← e, b, Matrix.mulVec_zero]
    · have a' : ∀ i, (fun k => s (Cᵀ i k)) ⬝ᵥ J *ᵥ z = 0 := fun i => by
        have := congrFun a i
        rw [← Matrix.mulVec_mulVec] at this
        exact this
      ext i j
      rw [gram_apply, Matrix.zero_apply]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [app_last]; exact c
        | cast j =>
          rw [app_last, app_cast, ← form_symm s hs hJ, a', map_zero]
      | cast i =>
        induction j using Fin.lastCases with
        | last => rw [app_last, app_cast]; exact a' i
        | cast j =>
          rw [app_cast, app_cast, ← gram_apply, h0, Matrix.zero_apply]
  induction k with
  | zero =>
    intro m C hm hC h0
    obtain ⟨Y, h1, h2, h3⟩ := exists_dual s hs hJ hd hC h0
    refine ⟨m, le_rfl, C, Y, h0, h3, h1, fun z a b c => ?_, rfl⟩
    by_contra hz
    have := (step m C Y z hC h0 h2 a b c hz).1.fintype_card_le_finrank
    simp at this
    omega
  | succ k ih =>
    intro m C hm hC h0
    obtain ⟨Y, h1, h2, h3⟩ := exists_dual s hs hJ hd hC h0
    by_cases H : ∀ z : Fin n → E, (adj s C * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 →
      (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z = 0
    · exact ⟨m, le_rfl, C, Y, h0, h3, h1, H, rfl⟩
    push Not at H
    obtain ⟨z, a, b, c, hz⟩ := H
    obtain ⟨p, q⟩ := step m C Y z hC h0 h2 a b c hz
    obtain ⟨m', hm', X, Y', x1, x2, x3, x4, x5⟩ := ih (m + 1) (app C z) (by omega) p q
    refine ⟨m', by omega, X, Y', x1, x2, x3, x4, ?_⟩
    ext i j
    have := congrFun (congrFun x5 i) j.castSucc
    have e : app C z i j.castSucc = C i j := congrFun (app_cast C z j) i
    exact this.trans e

end General

theorem exists_wittFrame_initCols (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) (r : ℕ) (C : Matrix (Fin n) (Fin (r + 1)) E)
    (hC : LinearIndependent E (Matrix.transpose C)) (h0 : Formalism.UG.cT (σ : E →+* E) C * J * C = 0) :
    ∃ (m : ℕ) (hm : r < m) (X : Matrix (Fin n) (Fin m) E) (Y : Matrix (Fin n) (Fin m) E),
      GlobalTheory.SiegelSet.IsWittFrame σ J X Y ∧ GlobalTheory.StdPar.initCols X (⟨r, hm⟩ : Fin m) = C := by
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have := h.2.2.2 τ
    simp only [RingHom.coe_coe]
    rw [this, this, star_star]
  obtain ⟨m, hm, X, Y, x1, x2, x3, x4, x5⟩ := exists_ext (σ : E →+* E) (J := J) hs (Matrix.ext fun i j => hJ.1 i j) hJ.2
    n (r + 1) C (by omega) hC h0
  refine ⟨m, hm, X, Y, ⟨x1, x2, x3, fun z a b c => x4 z a b ?_⟩, x5⟩
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform] at c
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using c

end GlobalTheory.AdjugateAppendColumn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpDerEigenIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

def expDer (he : IsExp y e) (w : Fin g → ℂ) : epsPt y ⟶ G := (he.2.2.2.1 w).exists.choose

variable (he : IsExp y e)
include he

theorem expDer_spec (w : Fin g → ℂ) : IsDerivAt0 (fun z => (e z).left) w (expDer he w).left :=
  (he.2.2.2.1 w).exists.choose_spec

theorem exp_zero : e 0 = 1 := by
  have h := he.1 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_eq_iff (w : Fin g → ℂ) (v : epsPt y ⟶ G) :
    IsDerivAt0 (fun z => (e z).left) w v.left ↔ expDer he w = v :=
  ⟨fun hv => Over.OverMorphism.ext
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he w) hv), fun hv => hv ▸ expDer_spec he w⟩

theorem expDer_base (w : Fin g → ℂ) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (1 : Over.mk y ⟶ G).left := by
  rw [(expDer_spec he w).1]; show (e 0).left = _; rw [exp_zero he]

theorem expDer_injective : Function.Injective (expDer he) := by
  intro w w' h
  have h1 := expDer_spec he w
  have h2 := expDer_spec he w'
  rw [← h] at h2
  have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (e 0).left := h1.1
  exact (he.2.2.2.2 _ hb).unique h1 h2

theorem expDer_surj (v : epsPt y ⟶ G)
    (hv : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left) :
    ∃ w, expDer he w = v := by
  obtain ⟨w, hw, -⟩ := he.2.2.2.2 v (by rw [hv, exp_zero he])
  exact ⟨w, (expDer_eq_iff he w v).1 hw⟩

theorem expDer_add (w w' : Fin g → ℂ) : expDer he (w + w') = expDer he w * expDer he w' :=
  (expDer_eq_iff he _ _).1 (GlobalTheory.UnifCompare.isDerivAt0_mul (by rw [exp_zero he]) (expDer_spec he w)
    (expDer_spec he w'))

theorem expDer_zero : expDer he 0 = 1 := by
  have h := expDer_add he 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_smul (c : ℂ) (w : Fin g → ℂ) :
    (expDer he (c • w)).left = spMap (epsScale c) ≫ (expDer he w).left :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he _)
    (GlobalTheory.UnifCompare.isDerivAt0_smul (expDer_spec he w) c)

theorem expDer_prod {n : ℕ} (f : Fin n → Fin g → ℂ) :
    (List.ofFn fun j => expDer he (f j)).prod = expDer he (∑ j, f j) := by
  induction n with
  | zero => simp [expDer_zero he]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => f j.succ), Fin.sum_univ_succ, expDer_add he]

theorem expDer_mulVec (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (w : Fin g → ℂ) : expDer he (M *ᵥ w) = expDer he w ≫ φ := by
  have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom (expDer_spec he w) φ.left
  have h2 : (fun z => (e z).left ≫ φ.left) = fun z => (e (Matrix.mulVecLin M z)).left := by
    funext z; rw [Matrix.mulVecLin_apply, hM z, Over.comp_left]
  rw [h2, GlobalTheory.ThetaWitness.isDerivAt0_comp_linear_iff (fun z => (e z).left) he.2.2.1] at h1
  exact (expDer_eq_iff he _ _).1 h1

theorem expDer_eigen_iff (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (c : ℂ) (w : Fin g → ℂ) :
    (expDer he w ≫ φ).left = spMap (epsScale c) ≫ (expDer he w).left ↔ M *ᵥ w = c • w := by
  rw [← expDer_mulVec he M φ hM, ← expDer_smul he]
  constructor
  · intro h
    exact expDer_injective he (Over.OverMorphism.ext h)
  · intro h
    rw [h]

end GlobalTheory.UPel.HT.LieType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalDefiniteSpaceH
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem signs_pos_of_frame_gram_posdef {r : ℕ} (ε : Fin r → Bool) (fr G : Matrix (Fin r) (Fin r) ℂ)
    (h : fr.conjTranspose * Formalism.REAL.Jm ε * fr = G) (hs : Formalism.UG.HasSignature G r 0) :
    ∀ i, ε i = true := by
  obtain ⟨e, P, hP⟩ := hs
  have hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ) =
      (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  have hJ0 : Formalism.UG.Jpq r 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  rw [hcT, hJ0] at hP
  set P' : Matrix (Fin r) (Fin r) ℂ := (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).submatrix e e with hP'
  have h1 : P'.conjTranspose * G * P' = 1 := by
    have := congrArg (fun A : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ => A.submatrix e e) hP
    simp only [Matrix.reindex_apply] at this
    rw [← Matrix.submatrix_mul_equiv _ _ _ e _, ← Matrix.submatrix_mul_equiv _ _ _ e _] at this
    simpa [Matrix.submatrix_submatrix, Matrix.conjTranspose_submatrix, hP'] using this
  set Q := fr * P' with hQ
  have h2 : (Q.conjTranspose * Formalism.REAL.Jm ε) * Q = 1 := by
    rw [← h1, ← h]; simp only [hQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h3 : Q * (Q.conjTranspose * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp h2
  have h4 : Q * Q.conjTranspose = Formalism.REAL.Jm ε := by
    have := congrArg (· * Formalism.REAL.Jm ε) h3
    simpa [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self] using this
  intro i
  by_contra hi
  have hi' : ε i = false := by simpa using hi
  have h5 := congrFun (congrFun h4 i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hi'] at h5
  have h6 := congrArg Complex.re h5
  simp only [Complex.re_sum, Bool.false_eq_true, if_false, Complex.neg_re, Complex.one_re] at h6
  have h7 : ∀ k, 0 ≤ (Q i k * star (Q i k)).re := by
    intro k
    rw [Complex.star_def, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => h7 k)
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupSchemeStalkLengthConstant
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteGroupSchemeLength

theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  have h1 : Module.length R S = Module.length S S :=
    Module.length_eq_of_surjective (R := S) (M := S) (S := R) e.surjective
  let l : R ≃ₗ[R] S :=
    { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
      map_add' := e.map_add,
      map_smul' := fun r x => by
        simp only [smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
        rfl }
  rw [l.length_eq, h1]

theorem isClosed_singleton_of_isFinite {k : Type} [Field k] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of k)) [IsFinite f] (z : H) : IsClosed ({z} : Set H) := by
  have hz : f z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have hc : IsClosed (f ⁻¹' {IsLocalRing.closedPoint k}) :=
    (IsLocalRing.isClosed_singleton_closedPoint k).preimage f.continuous
  have hd := (f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)).to_subtype
  have := hc.isClosedEmbedding_subtypeVal.isClosedMap {⟨z, hz⟩} (isClosed_discrete _)
  rwa [Set.image_singleton] at this

theorem length_stalk_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  intro k _ _ G _ hf x x'
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have hsurj : ∀ y : G.left, ∃ a : 𝟙_ (Over (Sp k)) ⟶ G, a.left pt = y := by
    intro y
    have hy := isClosed_singleton_of_isFinite G.hom y
    exact ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
      pointOfClosedPoint_apply G.hom y hy _⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨a', rfl⟩ := hsurj x'
  let φ := GrpObj.mulRight (a⁻¹ * a')
  have h : a ≫ φ.hom = a' := by
    have : a ≫ φ.hom = a * (a⁻¹ * a') := by
      simp [φ, comp_lift_assoc, Hom.mul_def]
    rw [this, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
  have hx : φ.hom.left (a.left pt) = a'.left pt := by
    rw [← h]; rfl
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso φ).hom)
  have hi : IsIso (φ.hom.left.stalkMap (a.left pt)) :=
    ((isIso_iff_isIso_stalkMap φ.hom.left).1 inferInstance).2 _
  let e := (asIso (φ.hom.left.stalkMap (a.left pt))).commRingCatIsoToRingEquiv
  rw [← length_self_eq_of_ringEquiv e]
  congr 1 <;> rw [hx]

end GlobalTheory.FiniteGroupSchemeLength
end

