module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDerivCutoffConnectionDifferenceEq
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem mdbar_neg_cut_conn_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    {G₀ G₁ : V n → Matrix r r ℂ} {v : V n} (hρ : DifferentiableAt ℝ ρ v) (h₀ : MContDiffAt 2 G₀ v)
    (u₀ : IsUnit (G₀ v).det) (h₁ : MContDiffAt 2 G₁ v) (u₁ : IsUnit (G₁ v).det) :
    (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b))
      = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  funext a b
  have c₀ : MContDiffAt 1 (fun x => conn G₀ x (coordVec a)) v := h₀.conn u₀ (by norm_num) _
  have c₁ : MContDiffAt 1 (fun x => conn G₁ x (coordVec a)) v := h₁.conn u₁ (by norm_num) _
  have hρ' : DifferentiableAt ℝ (fun x => (ρ x : ℂ)) v := Complex.ofRealCLM.differentiableAt.comp v hρ
  have hs : mdbar (fun x => conn G₁ x (coordVec a) - conn G₀ x (coordVec a)) v (coordVec b) =
      mdbar (fun x => conn G₁ x (coordVec a)) v (coordVec b) -
        mdbar (fun x => conn G₀ x (coordVec a)) v (coordVec b) := by
    simp only [sub_eq_add_neg]
    rw [mdbar_add c₁ c₀.neg, mdbar_neg]
  rw [mdbar_neg (fun x => (ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a))),
    mdbar_smul hρ' (c₁.sub c₀), hs]
  simp only [Pi.sub_apply, Pi.smul_apply, curvAt, cutForm, curv, smul_sub, smul_neg]
  abel

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeightStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ τ, SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) ∧ ∀ a c : Fin V.rank, a ≤ c → dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) = if a = c then (w τ a : ℂ) • (v τ : M.H τ) else 0 := by
  first | exact @GlobalTheory.HolDict.VKill.borel_extVec | exact GlobalTheory.HolDict.VKill.borel_extVec | (intros; apply GlobalTheory.HolDict.VKill.borel_extVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramified
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem blockDiagonalMatrixOfAddEq_entries_mem_subring {R : Type} [CommRing R] (O : Subring R) {a b n : ℕ} (h : a + b = n)
    (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R)
    (hA : ∀ i j, A i j ∈ O) (hD : ∀ i j, D i j ∈ O) (i j : Fin n) : dgMat h A D i j ∈ O := by
  simp only [dgMat, reindex_apply, submatrix_apply]
  rcases (blkEq h).symm i with i' | i' <;> rcases (blkEq h).symm j with j' | j' <;>
    simp [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, hA, hD, O.zero_mem]

theorem det_mem_subring_of_entries_mem_fin {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (hA : ∀ i j, A i j ∈ O) : A.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => hA _ _)

theorem one_matrix_apply_mem_subring {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (i j : Fin m) :
    (1 : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  rw [Matrix.one_apply]; split_ifs
  · exact O.one_mem
  · exact O.zero_mem

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem character_det_integralGL_eq_one_of_unramified (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u ∈ GlobalTheory.LFun.KGL w (n := 1), μ (GeneralLinearGroup.det u) = 1) {m : ℕ} (k : GLw m w)
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := m)) : μ (GeneralLinearGroup.det k) = 1 := by
  set d := GeneralLinearGroup.det k
  let u : GL (Fin 1) (w.adicCompletion E) := Units.map (Matrix.scalar (Fin 1)).toMonoidHom d
  have hu : GeneralLinearGroup.det u = d := by
    ext; simp [u]
  rw [← hu]
  apply hμ
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (u : Matrix (Fin 1) (Fin 1) _) i j = (k.val).det := by
      simp [u, d, Subsingleton.elim i j]
    rw [this]; exact det_mem_subring_of_entries_mem_fin _ _ h1
  · have : (u⁻¹ : GL (Fin 1) _).val i j = (k⁻¹ : GLw m w).val.det := by
      simp [u, d, Subsingleton.elim i j, ← map_inv]
    rw [this]; exact det_mem_subring_of_entries_mem_fin _ _ h2

end GlobalTheory.BCT.CtLevel

namespace GlobalTheory.BCT.CtLevel

theorem lev_KGL_of_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n)
    (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ), (∀ u ∈ GlobalTheory.LFun.KGL w (n := 1), μ (GeneralLinearGroup.det u) = 1) →
    lev₁ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := a) ∧ lev₂ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := b) := by
  intro E _ _ _ a b n h w μ hμ
  constructor
  · refine le_antisymm (fun x hx => hx.1.1) fun k hk => ⟨⟨hk, ?_⟩, character_det_integralGL_eq_one_of_unramified w μ hμ k hk⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
    show dgM h w (k, 1) ∈ GlobalTheory.LFun.KGL w (n := n)
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ h1 (one_matrix_apply_mem_subring _) i j
    · rw [← map_inv, dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ h2 (fun i j => by simpa using one_matrix_apply_mem_subring (Ov E w) i j) i j
  · refine le_antisymm (fun x hx => hx.1.1) fun k hk => ⟨⟨hk, ?_⟩, character_det_integralGL_eq_one_of_unramified w μ hμ k hk⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
    show dgM h w (1, k) ∈ GlobalTheory.LFun.KGL w (n := n)
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ (one_matrix_apply_mem_subring _) h1 i j
    · rw [← map_inv, dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ (fun i j => by simpa using one_matrix_apply_mem_subring (Ov E w) i j) h2 i j

end GlobalTheory.BCT.CtLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixElementaryShearProperties
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem shear_self {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {R : Type} [CommRing R] (t : R) :
    shear τ a b t τ = Matrix.transvection a b t := by
  ext i j
  simp only [shear, Matrix.transvection, Matrix.add_apply, Matrix.of_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  rw [Matrix.single_apply]
  simp only [@eq_comm _ a i, @eq_comm _ b j]

theorem shear_ne {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {R : Type} [CommRing R] (t : R) (σ : ι)
    (h : σ ≠ τ) : shear τ a b t σ = 1 := by
  ext i j
  simp [shear, Sigma.mk.inj_iff, h]

theorem shear_props : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), a < b → ∀ (R : Type) [CommRing R] (t : R), (∀ σ, (shear τ a b t σ).det = 1) ∧ shear τ a b t * shear τ a b (-t) = 1 ∧ shear τ a b (0 : R) = 1 ∧ ∀ (S : Type) [CommRing S] (g : R →+* S), (shear τ a b t).map g = shear τ a b (g t) := by
  intro ι m τ a b hab R _ t
  have hne : a ≠ b := hab.ne
  refine ⟨fun σ => ?_, ?_, ?_, fun S _ g => ?_⟩
  · by_cases h : σ = τ
    · subst h; rw [shear_self]; exact Matrix.det_transvection_of_ne a b hne t
    · rw [shear_ne τ a b t σ h, Matrix.det_one]
  · funext σ
    rw [Pi.mul_apply, Pi.one_apply]
    by_cases h : σ = τ
    · subst h; rw [shear_self, shear_self, Matrix.transvection_mul_transvection_same (h := hne), add_neg_cancel,
        Matrix.transvection_zero]
    · rw [shear_ne τ a b _ σ h, shear_ne τ a b _ σ h, mul_one]
  · funext σ
    rw [Pi.one_apply]
    by_cases h : σ = τ
    · subst h; rw [shear_self, Matrix.transvection_zero]
    · rw [shear_ne τ a b _ σ h]
  · funext σ i j
    simp only [Mat.map, shear, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonal
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem blk_mul_dgM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (m k : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
    blk h w (k * m) X = dgM h w k * blk h w m X ∧
      blk h w (m * k) X = blk h w m (k.1.val * X * (k.2⁻¹).val) * dgM h w k := by
  intro E _ _ _ a b n h w m k X
  constructor
  · apply Units.ext
    rw [Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    simp [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc]
  · apply Units.ext
    rw [Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    have hk : (k.2⁻¹).val * k.2.val = 1 := Units.inv_mul k.2
    simp [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc, hk]

end GlobalTheory.BCT.CtLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerInfConjIntegralGLProdLeCptPart
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CentCpt

theorem twCent_inf_conjKK_le_cptPart (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E)
    (m q : GLw a w × GLw b w) :
    twCent (MonoidHom.id _) m ⊓ ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom ≤
      cptPart (twCent (MonoidHom.id _) m) := by
  rintro t ⟨ht, hK⟩
  apply Subgroup.subset_closure
  refine ⟨ht, ?_⟩
  have hc : IsCompact ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom :
      Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_map, Subgroup.coe_prod]
    refine ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2).image ?_
    show Continuous fun x : GLw a w × GLw b w => q * x * q⁻¹
    fun_prop
  have hz : (Subgroup.zpowers t : Set (GLw a w × GLw b w)) ⊆ _ :=
    (Subgroup.zpowers_le (H := ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom)).2 hK
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hz hc.isClosed)

end GlobalTheory.CentCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinCentComm

theorem commute_aeval {R : Type} [CommRing R] {r : ℕ} {m A : Matrix (Fin r) (Fin r) R}
    (h : Commute m A) (p : R[X]) : Commute m (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial k a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (h.pow_right k).smul_right a

theorem aeval_mulVec_krylov {R : Type} [CommRing R] {r : ℕ} (A : Matrix (Fin r) (Fin r) R)
    (v c : Fin r → R) :
    aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) *ᵥ v = GlobalTheory.ClassParam.krylov A v *ᵥ c := by
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.ClassParam.krylov, map_sum, aeval_monomial, Matrix.sum_mulVec,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eq_aeval_of_cyclic {R : Type} [CommRing R] {r : ℕ} (A : Matrix (Fin r) (Fin r) R) (v : Fin r → R)
    (hKu : IsUnit (GlobalTheory.ClassParam.krylov A v).det) (n : Matrix (Fin r) (Fin r) R) (hn : Commute n A) :
    ∃ q : R[X], n = aeval A q := by
  set K := GlobalTheory.ClassParam.krylov A v with hK
  let c := K⁻¹ *ᵥ (n *ᵥ v)
  refine ⟨∑ j : Fin r, monomial (j : ℕ) (c j), ?_⟩
  set p := aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) with hp
  have hpv : p *ᵥ v = n *ᵥ v := by
    rw [hp, aeval_mulVec_krylov, ← hK]
    simp only [c, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul]
  have hpA : Commute p A := (commute_aeval (Commute.refl A) _).symm
  have hcol : n * K = p * K := by
    ext i j
    have e1 : ∀ M : Matrix (Fin r) (Fin r) R, Commute M A →
        (M * K) i j = (A ^ (j : ℕ) *ᵥ (M *ᵥ v)) i := by
      intro M hM
      have : (M * K) i j = (M *ᵥ (A ^ (j : ℕ) *ᵥ v)) i := by
        simp [hK, GlobalTheory.ClassParam.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hM.pow_right _).eq]
    rw [e1 n hn, e1 p hpA, hpv]
  have := congrArg (· * K⁻¹) hcol
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu] using this

theorem commute_of_commute_map_separable {E R : Type} [Field E] [CommRing R] (f : E →+* R) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) E) (hA : A.charpoly.Separable) (X Y : Matrix (Fin r) (Fin r) R)
    (hX : X * A.map f = A.map f * X) (hY : Y * A.map f = A.map f * Y) : X * Y = Y * X := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field A hA
  have hKu : IsUnit (GlobalTheory.ClassParam.krylov (A.map f) (f ∘ v)).det := by
    rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hv).map f
  obtain ⟨q, rfl⟩ := eq_aeval_of_cyclic (A.map f) (f ∘ v) hKu Y hY
  exact (commute_aeval (m := X) hX q).eq

end GlobalTheory.BCT.FinCentComm

namespace GlobalTheory.BCT.FinCentComm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_fst_eq_one (a : finU (E := E) (n := n)) : ((a : UA E n) : GA E n).val.map (FinPtLoc.fstA E) = 1 := by
  have ha : cInf (a : UA E n) = 1 := a.2
  ext i j
  have h := congrArg (fun g : GL (Fin n) (Cinf E) => g.val i j) ha
  change (infEq E).symm (FinPtLoc.fstA E (((a : UA E n) : GA E n).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j at h
  rw [Matrix.map_apply]
  apply (infEq E).symm.injective
  rw [h]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem map_snd_finPt (γ : UE E n) :
    (((finPt γ : finU (E := E) (n := n)) : UA E n) : GA E n).val.map (pFin E) = γ.1.val.map (algebraMap E (Af E)) := by
  rw [FinPtLoc.finPt_eq]
  ext i j
  rw [Matrix.map_apply, FinPtLoc.snd_entry]
  rfl

end GlobalTheory.BCT.FinCentComm


open GlobalTheory.BCT.FinCentComm in
theorem GlobalTheory.BCT.finCent_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n),
    γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ),
      ∀ b ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), a * b = b * a := by
  intro E _ _ _ n γ hγ a ha b hb
  have key : ∀ c ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ),
      (((c : UA E n) : GA E n).val.map (pFin E)) * γ.1.val.map (algebraMap E (Af E)) =
        γ.1.val.map (algebraMap E (Af E)) * ((c : UA E n) : GA E n).val.map (pFin E) := by
    intro c hc
    have h : c * finPt γ = finPt γ * c := hc
    have h' := congrArg (fun z : finU (E := E) (n := n) => ((z : UA E n) : GA E n).val.map (pFin E)) h
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul] at h'
    rwa [map_snd_finPt] at h'
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  apply FinPtLoc.ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_fst_eq_one a, map_fst_eq_one b]
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact commute_of_commute_map_separable (algebraMap E (Af E)) γ.1.val hγ _ _ (key a ha) (key b hb)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChangeOfFrameHolomorphicInvertibleHolomorphicCha
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem analyticAt_ratVal_holoChart {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) {y : CxPts X.str σ} (hy : y ∈ e.source)
    {g : X.Fn} (hg : RegAt (under y) g) : AnalyticAt ℂ (fun v => ratVal g (e.symm v)) (e y) := by
  obtain ⟨U, hU, a, rfl⟩ := hg.exists_fnOf
  have hn : e.target ∩ e.symm ⁻¹' ptsIn X.str σ U ∈ 𝓝 (e y) := by
    refine Filter.inter_mem (e.open_target.mem_nhds (e.map_source hy)) ?_
    exact (e.tendsto_symm hy) ((isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU))
  exact GlobalTheory.SCV.analyticAt_of_differentiableOn ((he U a).congr fun w hw => ratVal_fnOf hw.2 _ a) hn

theorem changeFrame_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ e.source → ∀ {A A' : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → MContDiffAt 2 (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) (e y) ∧ IsUnit (((A' * A⁻¹).map (ratVal · (e.symm (e y))) ())ᵀ).det ∧ ∀ᶠ x in 𝓝 (e y), ∀ η, mdbar (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) x η = 0 := by
  intro F _ σ X m E e he y hy A A' hA hA'
  have hP : Par 0 ((ratOf X).O (under y)).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have han (i j : Fin m) : AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) (e y) :=
    analyticAt_ratVal_holoChart he hy (mem_O_ratOf.1 ((hP ()).1 j i))
  refine ⟨fun i j => ((han i j).contDiffAt (n := 2)).restrict_scalars ℝ, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    rw [Matrix.det_transpose, e.left_inv hy]
    exact ((hP.map_of (ratVal · y) ψ hψ).det_ne ()).isUnit
  · have h : ∀ᶠ x in 𝓝 (e y), ∀ i j : Fin m,
        AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) x :=
      eventually_all.2 fun i => eventually_all.2 fun j => (han i j).eventually_analyticAt
    filter_upwards [h] with x hx η
    ext i j
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx i j).differentiableAt]
    rfl

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyIntegralUnitConstCoeffOfMemMaxCompactStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_integral_unit_constCoeff_of_mem_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w), g ∈ GlobalTheory.LFun.KGL w (n := n) → (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (g.val.charpoly.coeff 0) = 1 := by
  first | exact @GlobalTheory.CharpolyInt.kint | exact GlobalTheory.CharpolyInt.kint | (intros; apply GlobalTheory.CharpolyInt.kint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegral
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem chernInt_one_eq_mInt : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧ ∀ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = mInt A (fun _ => φ.locPot) (fun _ => 1) := by
  intro Y L φ h
  haveI : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  haveI : T2Space (CxPts Y.str (RingHom.id ℂ)) := t2Space_cxPts_of_isProjOver _ Y.isProjOver
  haveI : SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) :=
    secondCountableTopology_of_isProjOver _ Y.isProjOver
  have hA₀ := AnRead.isAlgAtlas_finAtlas (AnRead.all Y.str (RingHom.id ℂ) Y.dim)
  have hi : φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) :=
    (h.chernInt_eq_mInt_of_isAlgAtlas hA₀ measurable_const).1.2
      (mIntegrableCont _ _
        (fun _ => ((Weight.isCInf_iff_isSmooth hA₀.anRead).1 h).isPotential hA₀) _ continuous_const)
  exact ⟨hi, fun A hA => (h.chernInt_eq_mInt_of_isAlgAtlas hA measurable_const).2 hi⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChart
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem holoChart_trans_algChart {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e)
    (c : AlgChart X.str σ X.dim) :
    DifferentiableOn ℂ (c.e ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.e.source) :=
  differentiableOn_euclidean.2 fun a => ((he _ (c.x a)).mono fun _ (hv : _ ∈ e.target ∩ e.symm ⁻¹' c.e.source) =>
    ⟨hv.1, c.source_subset hv.2⟩).congr fun _ hv => c.apply_eq _ hv.2 a

end GlobalTheory.GoodTop
end

