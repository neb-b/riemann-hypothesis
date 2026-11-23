module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeSum.GrowthAtPlace

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace

variable {n : ℕ} {ε : Fin n → Bool} {P G : Mx n}

theorem norm_entry_le (A : Mx n) (i j : Fin n) : ‖A i j‖ ≤ 1 + hs A := by
  have h : ‖A i j‖ ^ 2 ≤ hs A :=
    (Finset.single_le_sum (f := fun b => ‖A i b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ‖A a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))
  nlinarith [norm_nonneg (A i j)]

theorem one_add_hs_conj_le (Q y P : Mx n) : 1 + hs (Q * y * P) ≤ (1 + hs Q) * (1 + hs P) * (1 + hs y) := by
  have h1 := one_add_hs_mul_le (Q * y) P
  have h2 := mul_le_mul_of_nonneg_right (one_add_hs_mul_le Q y) (show 0 ≤ 1 + hs P by linarith [hs_nonneg P])
  nlinarith

theorem conj_mul (hP : IsUnit P) (a b : Mx n) : P⁻¹ * (a * b) * P = (P⁻¹ * a * P) * (P⁻¹ * b * P) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  calc P⁻¹ * (a * b) * P = P⁻¹ * a * (P * P⁻¹) * b * P := by
        rw [Matrix.mul_nonsing_inv _ hd]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_exp (hP : IsUnit P) (X : Mx n) (t : ℝ) :
    P⁻¹ * NormedSpace.exp (t • X) * P = NormedSpace.exp (t • (P⁻¹ * X * P)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  rw [Matrix.mul_assoc, exp_mul_eq hP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem conj_lie (hP : IsUnit P) (h : Pᴴ * Jm ε * P = G) {X : Mx n} (hX : X ∈ lieSet ε) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * Xᴴ * (P * P⁻¹)ᴴ * Jm ε * P + Pᴴ * Jm ε * (P * P⁻¹) * X * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (Xᴴ * Jm ε + Jm ε * X) * P := by
        rw [Matrix.mul_nonsing_inv _ hd]
        simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]

theorem normInf_atTau_le {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {ε : Fin V.rank → Bool} {P : Mx V.rank} (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ) :
    ∃ c : ℝ, ∀ y ∈ UJset ε, normInf θ V (atTau θ V τ (P⁻¹ * y * P)) ≤ c * (1 + hs y) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  set K : ℝ := (1 + hs P⁻¹) * (1 + hs P) + (1 + hs (1 : Mx V.rank)) with hK
  refine ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (K + K), fun y hy => ?_⟩
  have hs1 := hs_nonneg (1 : Mx V.rank)
  have hsy := hs_nonneg y
  have hPP : 0 ≤ (1 + hs P⁻¹) * (1 + hs P) := mul_nonneg (by linarith [hs_nonneg P⁻¹]) (by linarith [hs_nonneg P])
  have b1 : ∀ z : Mx V.rank, hs z = hs y → 1 + hs (P⁻¹ * z * P) ≤ K * (1 + hs y) := fun z hz => by
    have := one_add_hs_conj_le P⁻¹ z P
    rw [hz] at this
    nlinarith
  have b2 : 1 + hs (1 : Mx V.rank) ≤ K * (1 + hs y) := by nlinarith
  have sp := atTau_spec hθ V τ (conj_inv_mem hP h hy)
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ' _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have e := infMat_mul_inv θ V τ' (atTau θ V τ (P⁻¹ * y * P))
  rw [add_mul]
  refine add_le_add ((norm_entry_le _ i j).trans ?_) ((norm_entry_le _ i j).trans ?_)
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1]
      exact b1 y rfl
    · rw [sp.2.2 τ' c]
      exact b2
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1] at e
      have e2 : (P⁻¹ * y⁻¹ * P) * (P⁻¹ * y * P) = 1 := by
        rw [← conj_mul hP, inv_mul_UJ hy, Matrix.mul_one, Matrix.nonsing_inv_mul _ hd]
      rw [← left_inv_eq_right_inv e2 e]
      exact b1 _ (hs_inv hy)
    · rw [sp.2.2 τ' c, Matrix.one_mul] at e
      rw [e]
      exact b2

theorem umg_atTau : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ (ε : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ → ∀ x : GA D V, GlobalTheory.TypeSum.UMG ε (fun y => φ (x * atTau θ V τ (P⁻¹ * y * P))) := by
  intro D θ hθ V τ φ hφ ε P hP h x
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨c, hc⟩ := normInf_atTau_le hθ V τ hP h
  have hl : ∀ l : List (Mx V.rank), (∀ Y ∈ l, Y ∈ lieSet ε) →
      ∀ p ∈ l.map fun X => (τ, P⁻¹ * X * P), p.2 ∈ lieAt V p.1 := fun l hl p hp => by
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hp
    exact conj_lie hP h (hl Y hY)
  refine ⟨N, fun l y => ((l.map fun X => (τ, P⁻¹ * X * P)).foldr (fun p f => Rder θ V p.1 p.2 f) φ)
    (x * atTau θ V τ (P⁻¹ * y * P)), fun _ _ => rfl, fun l hl' X hX g hg => ?_, fun l hl' => ?_⟩
  · have hs := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Mx V.rank => Rder θ V p.1 p.2) _
      fun p hp => linOnSm_Rder (hl l hl' p hp)).mem φ hφ.smooth
    have hd := (differentiable_oneP hs (τ := τ) (conj_lie hP h hX) (x * atTau θ V τ (P⁻¹ * g * P)) 0).hasDerivAt
    refine HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hg) (conj_inv_mem hP h (exp_mem_UJ hX t)), conj_exp hP,
      ← mul_assoc]
    rfl
  · obtain ⟨C, hC⟩ := hN _ (hl l hl') x
    refine ⟨|C| * c ^ N, fun g hg => (hC _ (atTau_mem V τ _)).trans ?_⟩
    have h0 := normInf_nonneg (θ := θ) (atTau θ V τ (P⁻¹ * g * P))
    rw [mul_assoc |C|, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 (hc g hg) N) (pow_nonneg h0 _) (abs_nonneg _)

end GlobalTheory.TypeSum.GrowthAtPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.Frames

open GlobalTheory.Ker.ONBasis

variable {D : D7} {T : HSp D}

theorem negM_sq (T : HSp D) (q : ℕ) : negM T q * negM T q = 1 := by
  unfold negM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem negM_herm (T : HSp D) (q : ℕ) : (negM T q)ᴴ = negM T q := by
  unfold negM
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp

theorem compAt_eq (θ : InfFam D) (ρ : D.what₂.Tau) (h : GA D T) :
    compAt θ ρ (Formalism.L2.Theta.mt T h) = infMat D.sp.cm.sig T.gram (θ ρ) h := rfl

theorem compAt_unitary' {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (g : GA D T) :
    (compAt θ ρ (Formalism.L2.Theta.mt T g))ᴴ * gramAt D T ρ * compAt θ ρ (Formalism.L2.Theta.mt T g) = gramAt D T ρ := by
  rw [GlobalTheory.FockCompare.RealAction.gramAt_eq hθ]
  exact GlobalTheory.FockCompare.RealAction.unitary_map (cA D) ((θ ρ).comp (infPart D))
    (GlobalTheory.FockCompare.comp_cA hθ ρ) _ _ (mt_rel T g)

theorem isONeg_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T) :
    IsONeg T q (mvZ θ g Z) := by
  intro τ
  unfold mvZ
  rw [Matrix.conjTranspose_mul, ← hZ τ]
  conv_rhs => rw [← compAt_unitary' hθ τ g]
  simp only [Matrix.mul_assoc]

theorem mvZ_mul (θ : InfFam D) (Z : Fam T) (g g' : GA D T) : mvZ θ (g' * g) Z = mvZ θ g' (mvZ θ g Z) := by
  funext τ
  unfold mvZ
  have e : Formalism.L2.Theta.mt T (g' * g) = Formalism.L2.Theta.mt T g' * Formalism.L2.Theta.mt T g := by simp [Formalism.L2.Theta.mt]
  rw [e, ← Matrix.mul_assoc]
  congr 1
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem mvZ_fin (θ : InfFam D) (Z : Fam T) {g : GA D T} (hg : g ∈ GfC T) : mvZ θ g Z = Z := by
  funext τ
  have h1 : (Formalism.L2.Theta.mt T g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt T g) = ((Formalism.L2.Theta.mt T g).map (infPart D)).map (θ τ) := rfl
  unfold mvZ
  rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem cartZ_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T)
    (τ : D.what₂.Tau) :
    cartZ T q (mvZ θ g Z) τ * compAt θ τ (Formalism.L2.Theta.mt T g) = compAt θ τ (Formalism.L2.Theta.mt T g) * cartZ T q Z τ := by
  have hu' := isUnit_det (negM_sq T q) (isONeg_mvZ hθ hZ g τ)
  have e : (mvZ θ g Z τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T g) = (Z τ)⁻¹ := by
    symm
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ hu'
  unfold cartZ
  rw [Matrix.mul_assoc, e]
  unfold mvZ
  simp only [Matrix.mul_assoc]

theorem fin_of_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) {g : GA D T}
    (h : mvZ θ g Z = Z) : g ∈ GfC T := by
  refine (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).1 g fun τ => ?_
  have hu := isUnit_det (negM_sq T q) (hZ τ)
  have h1 : compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ = Z τ := congrFun h τ
  rw [← compAt_eq]
  calc _ = compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ * (Z τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu]

theorem exists_move {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z Z' : Fam T} (hZ : IsONeg T q Z)
    (hZ' : IsONeg T q Z') : ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  have hu := fun τ => isUnit_det (negM_sq T q) (hZ τ)
  obtain ⟨a, ha, h⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).2 (fun τ => Z' τ * (Z τ)⁻¹) (fun τ => by
    show (Z' τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z' τ * (Z τ)⁻¹) = gramAt D T τ
    have h2 := Matrix.mul_nonsing_inv _ (hu τ)
    calc _ = (Z τ)⁻¹ᴴ * ((Z' τ)ᴴ * gramAt D T τ * Z' τ) * (Z τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Z τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z τ * (Z τ)⁻¹) := by
          rw [hZ' τ, ← hZ τ]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one])
  refine ⟨a, ha, funext fun τ => ?_⟩
  unfold mvZ
  rw [compAt_eq, h τ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu τ), Matrix.mul_one]

theorem isOrtho_frOf {X : Data D.host.E T.rank} (eT : D.what₂.Tau ≃ X.Ψ) (hM : ModelW T rfl X)
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) {Z : Fam T} (hZ : IsONeg T X.p0 Z) : X.IsOrtho (frOf rfl eT Z) := by
  intro σ
  obtain ⟨τ, rfl⟩ := eT.surjective σ
  have hm : mat (frOf rfl eT Z) (eT τ) = Z τ := by
    ext a b
    simp [mat, frOf]
  have hG : ∀ a b, tauE D τ (X.Gm a b) = -gramAt D T τ b a := fun a b => by
    rw [hM.1]
    simp [gramAt]
  rw [hm, he]
  ext a b
  have h1 := congrFun (congrFun (hZ τ) b) a
  have h2 : FD.gram (tauE D τ) X.Gm (Z τ) a b = -((Z τ)ᴴ * gramAt D T τ * Z τ) b a := by
    simp only [FD.gram, hermC, FD.col, Matrix.of_apply, hG, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul, ← Finset.sum_neg_distrib, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, h1, negM]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), neg_zero]

theorem isUnitFr_of_isOrtho {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  unfold dmin
  have h : FD.gram τ.1 X.Gm (mat x τ) = sgnM X := hx τ
  rw [h, GlobalTheory.SW.Slab.lminor_sgnM]
  rcases GlobalTheory.SW.Slab.psgn_sq X.p0 i with h | h <;> rw [h] <;> norm_num

end GlobalTheory.OneMapRef.Frames


open GlobalTheory.OneMapRef.Frames GlobalTheory.Ker.ONBasis in
theorem GlobalTheory.OneMapRef.oneg_frames : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → frOf hr eT Z ∈ X.dom ∧ IsUnitFr X (frOf hr eT Z) ∧ X.IsOrtho (frOf hr eT Z) ∧ (∀ ρ, IsCartanInv (gramAt D T ρ) (cartZ T X.p0 Z ρ)) ∧ ∀ h : GA D T, IsONeg T X.p0 (mvZ θ h Z) ∧ (∀ ρ, cartZ T X.p0 (mvZ θ h Z) ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * cartZ T X.p0 Z ρ) ∧ (∀ h', mvZ θ (h' * h) Z = mvZ θ h' (mvZ θ h Z)) ∧ (h ∈ GfC T → mvZ θ h Z = Z) ∧ (mvZ θ h Z = Z → h ∈ GfC T) ∧ ∀ Z', IsONeg T X.p0 Z' → ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  intro D S T r g hr ψ θ X eT bas idx hS Z hZ
  subst hr
  obtain ⟨-, hθ, -, -, hM, -, he, -⟩ := hS
  have ho := isOrtho_frOf eT hM he hZ
  exact ⟨mem_dom X ho, isUnitFr_of_isOrtho X ho, ho,
    fun ρ => isCartanInv (negM_sq T _) (negM_herm T _) (hZ ρ),
    fun h => ⟨isONeg_mvZ hθ hZ h, cartZ_mvZ hθ hZ h, mvZ_mul θ Z h, mvZ_fin θ Z, fin_of_mvZ hθ hZ,
      fun _ hZ' => exists_move hθ hZ hZ'⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec.WordCont

theorem continuous_apply_family {Y L E : Type} [TopologicalSpace Y] [AddCommGroup L] [Module ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Y → L →ₗ[ℝ] E) (hW : ∀ x, Continuous fun y => W y x)
    {f : Y → L} (hf : Continuous f) : Continuous fun y => W y (f y) := by
  let b := Module.finBasis ℝ L
  have e : (fun y => W y (f y)) = fun y => ∑ i, b.coord i (f y) • W y (b i) := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr (f y), map_sum]
    simp only [map_smul, Module.Basis.coord_apply]
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp hf).smul (hW _)

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lieSub (G : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := GlobalTheory.UnitaryLieAlgebra.unitaryLie G

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem continuous_word [CompleteSpace H] (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G)
    (hσ : IsURepOn (UJset ε) σ) {Y : Type} [TopologicalSpace Y] (l : List (Y → Matrix (Fin n) (Fin n) ℂ))
    (hc : ∀ f ∈ l, Continuous f) (hm : ∀ f ∈ l, ∀ y, f y ∈ lieG G) :
    ∀ w ∈ smSub G (trRep σ P), Continuous fun y => word (trRep σ P) (l.map fun f => f y) w := by
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  induction l using List.reverseRecOn with
  | nil => intro w _; exact continuous_const
  | append_singleton l f ih =>
    intro w hw
    have hc' : ∀ f ∈ l, Continuous f := fun g hg => hc g (by simp [hg])
    have hm' : ∀ f ∈ l, ∀ y, f y ∈ lieG G := fun g hg => hm g (by simp [hg])
    have hl : ∀ y, ∀ X ∈ l.map (fun f => f y), X ∈ lieG G := fun y X hX => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hX
      exact hm' g hg y
    obtain ⟨hadd, hsm⟩ := _root_.GlobalTheory.SmVecLinear.dRep_linear n ε H σ P G hP h hσ w hw
    let W : Y → lieSub G →ₗ[ℝ] H := fun y =>
      { toFun := fun X => word (trRep σ P) (l.map fun f => f y) (dRep (trRep σ P) X w)
        map_add' := fun X Z => by
          rw [Submodule.coe_add, hadd _ X.2 _ Z.2,
            word_add hG hπ (hl y) (dRep_mem hG hπ hw X.2) (dRep_mem hG hπ hw Z.2)]
        map_smul' := fun a X => by
          rw [Submodule.coe_smul, hsm a _ X.2, word_smul hG hπ (hl y) _ (dRep_mem hG hπ hw X.2)]
          simp }
    have hf : Continuous fun y => (⟨f y, hm f (by simp) y⟩ : lieSub G) :=
      (hc f (by simp)).subtype_mk _
    have := continuous_apply_family W (fun X => ih hc' hm' _ (dRep_mem hG hπ hw X.2)) hf
    simp only [List.map_append, word_append, List.map_cons, List.map_nil, word_cons, word_nil]
    exact this

theorem word_rep {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    {w : H} (hw : w ∈ smSub G π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieG G) :
    word π l (π g w) = π g (word π (l.map fun X => g⁻¹ * X * g) w) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieG G := fun Y hY => hl Y (by simp [hY])
    have hm : ∀ Y ∈ l.map (fun X => g⁻¹ * X * g), Y ∈ lieG G := fun Y hY => by
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
      exact conj_mem_lieG hG hg (hl' Z hZ)
    rw [word_cons, ih hl', dRep_rep hG hπ (word_mem hG hπ hm hw) hg (hl X (by simp))]
    rfl

theorem continuous_sigma (hσ : IsURepOn (UJset ε) σ) {u : Formalism.REAL.UJ ε → H} (hu : Continuous u) :
    Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) (u g) := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have h1 : Tendsto (fun g => σ (umat g) (u g) - σ (umat g) (u g₀)) (𝓝 g₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : (fun g : Formalism.REAL.UJ ε => ‖σ (umat g) (u g) - σ (umat g) (u g₀)‖) = fun g => ‖u g - u g₀‖ := by
      funext g
      rw [← map_sub, hσ.2.1 _ g.2]
    rw [e]
    exact tendsto_iff_norm_sub_tendsto_zero.1 hu.continuousAt
  have h2 := h1.add (continuous_orbit hσ (u g₀)).continuousAt
  simpa [ContinuousAt] using h2

theorem continuous_word_translate : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), Continuous fun g : Formalism.REAL.UJ ε => word (trRep σ P) l (σ (umat g) w) := by
  intro n ε H _ _ _ σ P G hP h hσ l hl w hw
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hmem : ∀ g : Formalism.REAL.UJ ε, P⁻¹ * umat g * P ∈ Formalism.QuantumDeterminants.UH G := fun g => conj_mem_UH hP h g.2
  have hinv : ∀ g : Formalism.REAL.UJ ε, (P⁻¹ * umat g * P)⁻¹ = P⁻¹ * umat g⁻¹ * P := fun g => by
    apply Matrix.inv_eq_right_inv
    have e : umat g * umat g⁻¹ = 1 := Units.mul_inv g.1
    calc P⁻¹ * umat g * P * (P⁻¹ * umat g⁻¹ * P) = P⁻¹ * (umat g * (P * P⁻¹) * umat g⁻¹) * P := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv _ hd, Matrix.mul_one, e, Matrix.mul_one, nonsing_inv_mul _ hd]
  have c1 : Continuous fun g : Formalism.REAL.UJ ε => P⁻¹ * umat g * P :=
    (continuous_const.matrix_mul continuous_umat).matrix_mul continuous_const
  have c2 : Continuous fun g : Formalism.REAL.UJ ε => (P⁻¹ * umat g * P)⁻¹ := by
    simp only [hinv]
    exact c1.comp continuous_inv
  have hc := continuous_word hP h hσ
    (l.map fun X (g : Formalism.REAL.UJ ε) => (P⁻¹ * umat g * P)⁻¹ * X * (P⁻¹ * umat g * P))
    (fun f hf => by
      obtain ⟨X, _, rfl⟩ := List.mem_map.1 hf
      exact (c2.matrix_mul continuous_const).matrix_mul c1)
    (fun f hf g => by
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hf
      exact conj_mem_lieG hG (hmem g) (hl X hX)) w hw
  convert continuous_sigma hσ hc using 2 with g
  have := word_rep hG hπ hw (hmem g) hl
  rw [trRep_conj hP] at this
  rw [this, List.map_map]
  rfl

end GlobalTheory.SmVec.WordCont
end

