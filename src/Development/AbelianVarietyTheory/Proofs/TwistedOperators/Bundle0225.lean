module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalEigenvectorGeneratesIrreducibleSubrepre
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormClassOfRationalIsometryTraceForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.ParGL

theorem exists_isSatVecGL_bound : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → (∀ h ∈ Hecke ℂ (KGL w (n := n)), ∃ c : ℂ, heckeVec ρ (KGL w (n := n)) h x = c • x) → ∃ B, IsSatVecGL w ρ x B ∧ ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro E _ _ w n V _ _ ρ hun x hx0 hxf hs
  have hK : IsCommensurated (KGL w (n := n)) := Formalism.UG.Final.GLintComm E w n
  obtain ⟨U, hU, hxU, hirr, hunU, hline⟩ :=
    _root_.GlobalTheory.spherical_eigenvector_generates_irreducible ρ (KGL w (n := n)) (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1 hK hun x hx0 hxf hs
  set π := GlobalTheory.PRep.sub ρ U hU with hπ
  let x' : U := ⟨x, hxU⟩
  have hx'0 : x' ≠ 0 := fun e => hx0 (congrArg Subtype.val e)
  have hx'f : x' ∈ fixed π (KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hxf k hk)
  have hsub : ∀ g (y : U), U.subtype (π g y) = ρ g (U.subtype y) := fun _ _ => rfl
  have heig : ∀ h ∈ Hecke ℂ (KGL w (n := n)), ∃ c : ℂ, ∀ y ∈ fixed π (KGL w (n := n)), heckeVec π (KGL w (n := n)) h y = c • y := by
    intro h hh
    obtain ⟨c, hc⟩ := hs h hh
    have e1 : heckeVec π (KGL w (n := n)) h x' = c • x' := Subtype.val_injective (by
      have := map_heckeVec hK hh U.subtype hsub (x := x')
      exact this.trans hc)
    refine ⟨c, fun y hy => ?_⟩
    obtain ⟨a, rfl⟩ := hline y hy
    have := map_heckeVec hK hh (ρ := π) (ρ' := π) (a • LinearMap.id) (fun g y => by simp) (x := x')
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [← this, e1, smul_comm]
  obtain ⟨B, hB⟩ := GlobalTheory.LFun.ExSatGL.exists_hasSatGL E w n U π
    ((Submodule.ne_bot_iff _).2 ⟨x', hx'f, hx'0⟩) heig
  have hx' : IsSatVecGL w π x' B := hB.2 x' hx'f hx'0
  have hup := _root_.GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL GlobalTheory.SatakeBound.satakeTrivialBound E w n _ π B hirr hunU hB
  refine ⟨B, hx'.map U.subtype hsub hx0, fun β hβ => ⟨hup β hβ, ?_⟩⟩
  have hst := GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w n _ π x' B hunU hx'
  have h1 : β⁻¹ ∈ B.map star := hst ▸ Multiset.mem_map_of_mem _ hβ
  obtain ⟨β', hβ', e⟩ := Multiset.mem_map.1 h1
  have h2 : ‖((β⁻¹ : ℂˣ) : ℂ)‖ = ‖(β' : ℂ)‖ := by
    rw [← e]
    simp
  rw [h2]
  exact hup β' hβ'

end GlobalTheory.FinZeta.ParGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerResNonzero

variable {D : D7}

theorem exists_right_inv {V : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hC : LinearIndependent D.host.E C.transpose) :
    ∃ N : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * N = 1 := by
  set P := adj D C * V.gram with hP
  have hinj : Function.Injective (Matrix.toLin' Pᵀ) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    rw [Matrix.toLin'_apply] at ha
    rw [Matrix.mulVec_transpose, hP, ← Matrix.vecMul_vecMul] at ha
    have hG := GlobalTheory.LatVac.gram_det_isUnit V
    have h1 : a ᵥ* adj D C = 0 := by
      have := congrArg (fun v => v ᵥ* V.gram⁻¹) ha
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
      rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one] at this
    have h2 : C *ᵥ star a = 0 := by
      have e : a ᵥ* adj D C = star (C *ᵥ star a) := by
        rw [Matrix.star_mulVec, star_star]; rfl
      rw [e] at h1
      exact star_eq_zero.1 h1
    have h3 : star a = 0 := by
      funext j
      refine Fintype.linearIndependent_iff.1 hC (star a) ?_ j
      funext i
      have := congrFun h2 i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Pi.zero_apply] at this ⊢
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact star_eq_zero.1 h3
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Pᵀ) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
  have e : LinearMap.toMatrix' g * Pᵀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have := congrArg Matrix.transpose e
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem lattice_ratMx (D : D7) (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) ∧ LocallyCompactSpace (Mx D m n) ∧
    SecondCountableTopology (Mx D m n) ∧ T2Space (Mx D m n) ∧ DiscreteTopology (ratMx D m n) ∧
    ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ x : Mx D m n, ∃ γ ∈ ratMx D m n, γ + x ∈ K :=
  GlobalTheory.AdelicMatrixLattice.lattice D (Examples₂.posSpace Examples₂.star_isIntegral m) (Examples₂.posSpace Examples₂.star_isIntegral n)

theorem isoPart_add' {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y y' : Mx D W.rank r) :
    isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' :=
  Matrix.add_mul _ _ _

theorem isoPart_zero' {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    isoPart V W C (0 : Mx D W.rank r) = 0 := Matrix.zero_mul _

theorem midPart_zero' {V V' W : HSp D} (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B (0 : WO V' W) = 0 := Matrix.zero_mul _

theorem isoPart_mem_iff {V W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hC : LinearIndependent D.host.E C.transpose) (y : Mx D W.rank r) :
    isoPart V W C y ∈ ratL W V ↔ y ∈ ratMx D W.rank r := by
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨N, hN⟩ := exists_right_inv (V := V) hC
    refine ⟨Q * N, ?_⟩
    change (Q * N).map (incA D) = y
    have hQ' : Q.map (incA D) = y * (adj D C * V.gram).map (incA D) := hQ
    rw [Matrix.map_mul, hQ', Matrix.mul_assoc, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_one]
  · rintro ⟨γ₀, rfl⟩
    exact ⟨γ₀ * (adj D C * V.gram), by
      show (γ₀ * (adj D C * V.gram)).map (incA D) = _
      rw [Matrix.map_mul]; rfl⟩

theorem exists_res_ne_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  intro D V V' W r C B hs hF ψ hψ μ 𝓨 h
  obtain ⟨f₀, hf₀, hne₀⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ V W
  obtain ⟨x₀, hx₀⟩ : ∃ x, f₀ x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne₀ (funext hc)
  have hf₁ : IsThetaFunO ψ V W (heisO ψ V W x₀ f₀) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ x₀
  have h0 : heisO ψ V W x₀ f₀ 0 ≠ 0 := by
    simp only [heisO, zero_add, GlobalTheory.FinTranslate.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]
    exact hx₀

  have hiso : ∀ y y' : Mx D W.rank r, symplOH V W (isoPart V W C y) (isoPart V W C y') = 0 := fun y y' => by
    have := hF y y' 0 0
    rwa [midPart_zero', add_zero, add_zero, GlobalTheory.FinTranslate.symplOH_zero_left] at this

  have hc : ∀ (g : WO V W → ℂ), IsThetaFunO ψ V W g → ∀ a ∈ ratL W V, ∀ z,
      heisO ψ V W a g z = ψ (symplO V W z a) * g z := by
    intro g hg a ha z
    have := GlobalTheory.ThetaCoefficient.char_mul_heisO hg ha 0 z
    simp only [heisO, GlobalTheory.FinTranslate.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one, one_mul] at this
    exact this.symm
  refine by_contra fun hall => ?_
  push_neg at hall
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_ratMx D W.rank r
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hcont : Continuous (isoPart V W C : Mx D W.rank r → WO V W) := continuous_id.matrix_mul continuous_const
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (Mx D W.rank r) (ratMx D W.rank r) K hK hKc
    (ratL W V) (fun a y => ψ (symplO V W (isoPart V W C y) a))
    (fun a => by
      simp only [GlobalTheory.ThetaCoefficient.symplO_eq]
      exact hψ.1.1.comp (((GlobalTheory.FinTranslate.continuous_symplOH V W _).comp hcont).add
        ((GlobalTheory.FinTranslate.continuous_symplOH V W _).comp hcont)))
    (fun a x y => by
      simp only [isoPart_add', GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_add_left,
        ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun a b x => by
      show ψ (symplO V W (isoPart V W C x) (a + b)) = _
      simp only [GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_add_right, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun x => by
      show ψ (symplO V W (isoPart V W C x) 0) = 1
      rw [GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.1.2.1 _)
    (fun y => by
      rw [← isoPart_mem_iff hs.frame.2.1 y, ← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W]
      exact Subtype.forall)
    μ 𝓨 h.1 h.2.1 (fun y => heisO ψ V W x₀ f₀ (isoPart V W C y)) (hf₁.cont.comp hcont)
    (fun γ hγ y => by
      obtain ⟨γ₀, hγ₀⟩ := (isoPart_mem_iff (V := V) hs.frame.2.1 γ).2 hγ
      have e := hf₁.quasi γ₀ (isoPart V W C y)
      change ratW W V γ₀ = isoPart V W C γ at hγ₀
      rw [hγ₀, hiso, neg_zero, AddChar.map_zero_eq_one, one_mul] at e
      simp only [isoPart_add']
      exact e)
    (fun a => by
      have e := congrFun (hall _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₁ (a : WO V W))) 0
      simp only [res, midPart_zero', add_zero, Pi.zero_apply] at e
      rw [← e]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hc _ hf₁ a a.2 _).symm))
  have := congrFun key 0
  simp only [isoPart_zero', Pi.zero_apply] at this
  exact h0 this

end GlobalTheory.TowerResNonzero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTorusClassOfIrreducibleCharpolyUnitary
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RatEll

theorem sig_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨-, -, -, h⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h, h, star_star]

theorem exists_cls_of_irreducible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Function.Bijective (diagH σ J F) ∧ ∀ γ : GRat σ J, Irreducible γ.1.1.charpoly → ∃ P : PPol σ n, γ.1.1.charpoly = P.1 ∧ ∃ q, HasCls P F J (diagH σ J F γ) q := by
  intro F E _ _ _ _ _ σ hσ n J hJ
  refine ⟨_root_.GlobalTheory.TwistRatBij.diagH_bijective F E σ n J, ?_⟩
  intro γ hirr
  have hm : Formalism.UG.cT (σ : E →+* E) γ.1.1 * J * γ.1.1 = J := γ.2
  have hs := GlobalTheory.T.charpoly_unitary_eq_conjugateReciprocal F E σ n J hJ.2 γ
  have hdet : γ.1.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp γ.1.isUnit).ne_zero
  have h0 : eval 0 γ.1.1.charpoly ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero]
    intro hc
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, hc, mul_zero]
  have hP : γ.1.1.charpoly.Monic ∧ Irreducible γ.1.1.charpoly ∧ γ.1.1.charpoly.natDegree = n ∧
      eval 0 γ.1.1.charpoly ≠ 0 ∧ γ.1.1.charpoly = sharp σ n γ.1.1.charpoly :=
    ⟨Matrix.charpoly_monic _, hirr, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], h0, hs⟩
  let P : PPol σ n := ⟨γ.1.1.charpoly, hP⟩
  refine ⟨P, rfl, ?_⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_adjoinRoot_linearEquiv_of_charpoly_eq F E σ n P γ.1.1 rfl
  obtain ⟨x, hx0, hxs, hxf⟩ := _root_.GlobalTheory.TrEll.HermTrace.exists_trace_form F E σ (sig_sig hσ) n P J hJ γ.1.1 hm φ hφ
  exact _root_.GlobalTheory.RatCls.hasCls_of_ratIsom F E σ n P J φ x hx0 hxs hxf γ hφ

end GlobalTheory.TrEll.RatEll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVecOfNe
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.KapRedII

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem nP_pos' (F : Face D A) (b : Bool) : 0 < RealDat.nP F b := by
  have hcard : 0 < Nat.card (F.lvl b).P := Nat.card_pos
  unfold RealDat.nP
  exact_mod_cast hcard

end Defs

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ} {a : ℝ}
    (ha : 0 ≤ a) (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' ((a : ℂ) * c) := by
  intro v v'
  obtain ⟨hint, heq⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn
    rw [Measure.restrict_smul]
    exact hint.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, heq, ENNReal.toReal_ofReal ha, Complex.real_smul]
    ring

private theorem isMultIP_const_unique {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c c' : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0)
    (h : IsMultIP M μ 𝓕 T T' c) (h' : IsMultIP M μ 𝓕 T T' c') : c = c' := by
  have e := (h v v).2
  rw [(h' v v).2] at e
  exact (mul_right_cancel₀ hv e).symm

private theorem ipM_eq_of_isMultIP {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) (h : IsMultIP M μ 𝓕 T T' c) :
    ipM M μ 𝓕 T T' = c := by
  have hex : ∃ c, IsMultIP M μ 𝓕 T T' c := ⟨c, h⟩
  unfold ipM
  rw [dite_eq_left hex]
  exact isMultIP_const_unique v hv hex.choose_spec h

theorem ipM_smul_of_vec (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {a : ℝ}
    (ha : 0 < a) (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 T T' = (a : ℂ) * ipM M μ 𝓕 T T' := by
  by_cases hex : ∃ c, IsMultIP M μ 𝓕 T T' c
  · obtain ⟨c, hc⟩ := hex
    rw [ipM_eq_of_isMultIP v hv hc, ipM_eq_of_isMultIP v hv (isMultiplicityInner_smul_measure ha.le hc)]
  ·
    have hex' : ¬ ∃ c, IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' c := by
      rintro ⟨c', hc'⟩
      have hb := isMultiplicityInner_smul_measure (inv_nonneg.mpr ha.le) hc'
      rw [smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one,
        one_smul] at hb
      exact hex ⟨_, hb⟩
    unfold ipM
    rw [dite_eq_right hex, dite_eq_right hex', mul_zero]

theorem exists_vec_of_ne {M : DSModel V S} {T : MMap M} (hT : T ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical

  obtain ⟨v, hv⟩ : ∃ v : M.Vec, T v ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hT (MultilinearMap.ext fun x => by simp [hno x])
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => ?_⟩
  have hvt : v τ ≠ 0 := fun h0 => hv (T.map_coord_zero τ h0)
  rw [inner_self_ne_zero, ne_eq, Submodule.coe_eq_zero]
  exact hvt

end Schur

end GlobalTheory.KapRedII
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameCongruentSubOneMulVecMemIdealLatticeComplet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel Matrix NumberField
open scoped Pointwise TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.FrameCong

variable {D : D7}

theorem intAt_mul_mem {S : HSp D} {L : Lat S} {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (fun i => a * y i) ∈ latV S L (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have hint : a * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAt D (· = v) := by
      refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
      rw [RingHom.map_mul]
      exact FrameLat.mul_mem_intAE ha.2 (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)
    have h := FrameLat.int_mul_mem hint hx
    have h1 : ∀ i, (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D (x i) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i) := fun i => by
      change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simpa only [mul_assoc, h1] using h
  | zero => simp only [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg]; exact neg_mem hx

theorem inc_mul_mem {S : HSp D} {L : Lat S} {P : Pl D → Prop} {𝔪 : Ideal (𝓞 D.host.E)} {m : 𝓞 D.host.E} (hm : m ∈ 𝔪)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => incA D (m : D.host.E) * y i) ∈ latV S (𝔪 • L) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα0, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα0, 1, rfl, m • x, Submodule.smul_mem_smul hm hx, ?_⟩
    funext i
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] (m : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, one_mul]
    rfl
  | zero => simp only [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg]; exact neg_mem hx

theorem sub_one_mulVec_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (n : Type) [Fintype n]
    [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n),
    β.IsLat L (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ),
    (∃ m ∈ 𝔪, ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k],
      (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E))) →
    ∀ k₀ : GL n 𝒪[k], (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d) →
    ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = p.v) →
    (fun i => p.e * ((mt S (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)) - 1) *ᵥ y) i) ∈
      latV S (𝔪 • L) (· = p.v) := by
  intro D k _ _ _ _ p S L n _ _ β hβ 𝔪 d ⟨m, hm, hmd⟩ k₀ hk y hy
  have hpi : ∀ x : n → k, x ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) ↔ ∀ j, x j ∈ 𝒪[k] := by
    intro x
    simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    refine forall_congr' fun j => ⟨?_, fun h => ⟨⟨x j, h⟩, rfl⟩⟩
    rintro ⟨z, hz⟩
    rw [← hz]; exact z.2
  set g : GL n k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ with hg
  set Y : Fin S.rank → k := fun i => p.pr (y i) with hY
  set x : n → k := β.b' *ᵥ Y with hx
  have hbx : β.b *ᵥ x = Y := by rw [hx, Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
  have hxint : ∀ j, x j ∈ 𝒪[k] := by
    rw [← hpi, hβ x, hbx]
    simp only [hY, p.sec_pr]
    exact intAt_mul_mem (FrameLat.e_mem_intAt p) hy
  let x₀ : n → 𝒪[k] := fun j => ⟨x j, hxint j⟩
  have hz : ∀ i, ((k₀.1 - 1) *ᵥ x₀) i ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d := fun i =>
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hk i j)
  choose c hc hcz using fun i => hmd _ (hz i)
  have hgx : (g.val - 1) *ᵥ x = p.pr (incA D (m : D.host.E)) • c := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← hcz i]
    have h1 : g.val - 1 = (k₀.1 - 1).map (algebraMap 𝒪[k] k) := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
    rw [h1]
    exact (RingHom.map_mulVec (algebraMap 𝒪[k] k) (k₀.1 - 1) x₀ i).symm
  have hpr : ∀ i, p.pr (((mt S (β.gl g) - 1) *ᵥ y) i) = p.pr (incA D (m : D.host.E)) * (β.b *ᵥ c) i := by
    intro i
    rw [RingHom.map_mulVec, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), β.gl_mat g]
    have h2 : β.b * g.val * β.b' - 1 = β.b * (g.val - 1) * β.b' := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, β.bb']
    rw [h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (β.b *ᵥ ((g.val - 1) *ᵥ x)) i = _
    rw [hgx, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hc' := (hβ c).1 ((hpi c).2 hc)
  have h := inc_mul_mem hm hc'
  have heq : (fun i => p.e * ((mt S (β.gl g) - 1) *ᵥ y) i) =
      fun i => incA D (m : D.host.E) * p.sec ((β.b *ᵥ c) i) := by
    funext i
    rw [← p.sec_pr, hpr, mul_comm (incA D _), FrameLat.sec_mul_right, mul_comm]
  rw [heq]
  exact h

end GlobalTheory.FinPl.FrameCong
end
end

