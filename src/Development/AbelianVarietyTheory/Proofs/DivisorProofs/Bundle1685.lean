module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDarbouxChangeOperatorWithDoubleLowerUnipot
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.UnipOp

open GlobalTheory.AdelicSvNQuad GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem star_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : star (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [show star (ψ t) = starRingEnd ℂ (ψ t) from rfl, Complex.conj_mul', GlobalTheory.StdCharFromIsStd.norm_psi hψ t]
  simp

theorem invOf_two_eq : (⅟(2 : AF F)) = algebraMap F (AF F) (2⁻¹) := by
  refine invOf_eq_right_inv ?_
  rw [show (2 : AF F) = algebraMap F (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
    mul_inv_cancel₀ (two_ne_zero), map_one]

theorem quad_rat {κ : Type} [Fintype κ] (B : Matrix κ κ F) (ξ : κ → F) :
    quad (⅟(2 : AF F)) (B.map (algebraMap F (AF F))) (fun i => algebraMap F (AF F) (ξ i)) =
      algebraMap F (AF F) (quad (2⁻¹ : F) B ξ) := by
  rw [map_quad, invOf_two_eq]

theorem isOp_unip (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (C : Matrix κ κ F) (hC : Cᵀ = C) :
    IsOp ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1))
      (mulQ (F := F) ψ (⅟2) (C.map (algebraMap F (AF F)))) (mulQ (F := F) ψ (⅟2) (-(C.map (algebraMap F (AF F))))) := by
  set A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F)) with hAdef
  have hA : Aᵀ = A := by rw [hAdef, ← Matrix.transpose_map, hC]
  have inv : ∀ (B : Matrix κ κ (AF F)) φ, mulQ ψ (⅟2) (-B) (mulQ ψ (⅟2) B φ) = φ := fun B φ => by
    funext x
    rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have inv' : ∀ (B : Matrix κ κ (AF F)) φ, mulQ ψ (⅟2) B (mulQ ψ (⅟2) (-B) φ) = φ := fun B φ => by
    have := inv (-B) φ
    rwa [neg_neg] at this
  have adm : ∀ B : Matrix κ κ (AF F), ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ mulQ ψ (⅟2) B ∈ (adeleClass F).adm κ := by
    intro B l hl g hg
    obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ (⅟2) B hg
    obtain ⟨T, hT⟩ := hl g' hg'
    exact ⟨T.comp M, fun f => by rw [LinearMap.comp_apply, hM f, hT]; rfl⟩
  have nrm : ∀ (B : Matrix κ κ (AF F)) (φ : (κ → AF F) → ℂ) x, ‖mulQ ψ (⅟2) B φ x‖ₑ = ‖φ x‖ₑ := by
    intro B φ x
    rw [mulQ_apply, enorm_mul, ← ofReal_norm (ψ _), GlobalTheory.StdCharFromIsStd.norm_psi hψ, ENNReal.ofReal_one, one_mul]
  refine ⟨mulQ_mem ψ hψ _ A, mulQ_mem ψ hψ _ (-A), fun φ _ => inv A φ, fun φ _ => inv' A φ, adm A, adm (-A),
    fun w φ _ => funext fun x => ?_, ⟨1, one_ne_zero, fun φ _ => ?_⟩, ?_⟩
  · rw [act_unip, mulQ_apply]
    simp only [schr]
    rw [mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]
  · rw [one_mul]
    unfold thetaSum
    congr 1
    funext ξ
    rw [mulQ_apply, hAdef, quad_rat, hψ.2.1, one_mul]
  · intro μ μ' hμ hμ'
    letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : SecondCountableTopology (κ → AF F) := inferInstance
    haveI := hμ
    haveI := hμ'
    have e := Measure.isAddLeftInvariant_eq_smul μ' μ
    have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ
    refine ⟨(μ'.addHaarScalarFactor μ : ℝ≥0∞), by exact_mod_cast hpos.ne', ENNReal.coe_ne_top, fun φ _ => ?_⟩
    simp_rw [nrm]
    conv_lhs => rw [e]
    rw [lintegral_smul_measure]
    rfl

end GlobalTheory.TowU.UnipOp

namespace GlobalTheory.TowU.UnipOp

open GlobalTheory.AdelicSvNQuad GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem dblAct_unip {κ : Type} [Fintype κ] [DecidableEq κ] (C : Matrix κ κ F) :
    dblAct (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1) :
        (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)) =
      GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-(Matrix.fromBlocks C 0 0 (-C))) 1) := by
  funext w
  rw [act_unip]
  simp only [dblAct, act_unip]
  refine Prod.ext ?_ ?_
  · funext a
    rcases a with a | a <;> rfl
  · funext a
    rcases a with a | a <;>
      simp [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec] <;> ring

theorem quad_dbl {κ : Type} [Fintype κ] (h : AF F) (A : Matrix κ κ (AF F)) (x : κ ⊕ κ → AF F) :
    quad h (Matrix.fromBlocks A 0 0 (-A)) x = quad h A (x ∘ Sum.inl) + -quad h A (x ∘ Sum.inr) := by
  simp only [quad, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add, Matrix.neg_mulVec, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], ∀ C : Matrix κ κ F, Cᵀ = C → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1)) S S' := by
  intro F _ _ ψ hψ κ _ _ C hC
  set A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F)) with hAdef
  let Cd : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks C 0 0 (-C)
  have hCd : Cdᵀ = Cd := by
    simp only [Cd, Matrix.fromBlocks_transpose, hC, Matrix.transpose_zero, Matrix.transpose_neg]
  have hn : (-C).map (algebraMap F (AF F)) = -C.map (algebraMap F (AF F)) := Matrix.map_neg _ (map_neg _) _
  have hCdA : Cd.map (algebraMap F (AF F)) = Matrix.fromBlocks A 0 0 (-A) := by
    simp only [Cd, Matrix.fromBlocks_map, hAdef, Matrix.map_zero _ (map_zero _), hn]
  refine ⟨_, _, isOp_unip ψ hψ C hC, mulQ ψ (⅟2) (Cd.map (algebraMap F (AF F))),
    mulQ ψ (⅟2) (-(Cd.map (algebraMap F (AF F)))), ?_, fun φ₁ _ φ₂ _ => funext fun x => ?_⟩
  · rw [dblAct_unip]
    exact isOp_unip ψ hψ Cd hCd
  · rw [mulQ_apply, hCdA, quad_dbl]
    simp only [boxFun, Pi.star_apply, mulQ_apply, star_mul', star_star, star_psi hψ]
    rw [AddChar.map_add_eq_mul, ← hAdef]
    ring

end GlobalTheory.TowU.UnipOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BottomNu

theorem exists_heckeU_nu_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), ∃ χ : HeckeU D (botBig D i j + botSmall D i j), (∀ x, χ.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) ∧ ∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χ.n τ := by
  intro D T L sc μ₀ hL G i j
  have hu : (nuH G μ₀ i j)⁻¹.IsUnitary := by
    have h := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G μ₀ i j hL)
    intro x
    have e : (((nuH G μ₀ i j)⁻¹).1 x : ℂˣ) = ((nuH G μ₀ i j).1 x)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have htriv : (nuH G μ₀ i j)⁻¹.TrivOn D.host.F := by
    have h1 := (L.C.isMu0 j).triv
    have h2 := G.ch.triv (D.R.m - i) hm.1 hm.2
    have h3 : (L.xiH μ₀).TrivOn D.host.F := hL.xi_triv μ₀
    exact (((h1.mul h3).mul h2.inv)).inv
  have hp : ∀ τ, Even (2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i)) -
      ((botBig D i j + botSmall D i j : ℕ) : ℤ)) := by
    intro τ
    obtain ⟨h1, h2, -⟩ := ranks_exact D i j
    obtain ⟨u, hu⟩ := D.R.t_odd
    obtain ⟨v, hv⟩ := odd_sLen D
    have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
    obtain ⟨w, hw⟩ : ∃ w : ℕ, botBig D i j + botSmall D i j = 2 * w := ⟨(botBig D i j + botSmall D i j) / 2, by omega⟩
    refine ⟨(GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i) - w, ?_⟩
    rw [hw]; push_cast; ring
  have hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) →
      (nuH G μ₀ i j)⁻¹.1 (finIdl D u) = 1 := by
    obtain ⟨M, hM, h⟩ := _root_.GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E (nuH G μ₀ i j)⁻¹
    refine ⟨M, hM, fun u hu ⟨s, hs, e⟩ => h _ (GlobalTheory.Mem.Col2.SplitChar.finIdl_unit hu)
      (fun w => by rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_fst]; rfl) fun P => ?_⟩
    rw [GlobalTheory.Mem.Col2.SplitChar.vl_sub_one, e, map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs P)
  exact ⟨GlobalTheory.SplitCharGen.ofHChar _ (nuH G μ₀ i j)⁻¹ _ hu (_root_.GlobalTheory.FunObj.SqNum.nuH_inv_hasInf hL G i j) hp hc
    (_root_.GlobalTheory.NuCharNorm.chi_norm_one D _ htriv (_root_.GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E _)) (_root_.GlobalTheory.UnrKill.unr_kill D _ fun P hP => _root_.GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ hL G i j P hP), fun x => rfl, fun τ => _root_.GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen D sc.cGap i j τ⟩

end GlobalTheory.BottomNu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceTransversalOfLocalCoreStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_transversal_of_localCore : (∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ Z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z ∧ (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.TransvChoose.exists_transversal | exact GlobalTheory.TransvChoose.exists_transversal | (intros; apply GlobalTheory.TransvChoose.exists_transversal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRec
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn GlobalTheory.RunDepth

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eq_kaR {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (i : Fin D.R.m)
    (w : WeightFamilies.Wt D ((i : ℕ) + 1))
    (hP : ∀ τ (k : Fin (D.R.sigW ((i : ℕ) + 1)).1), w.aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k)
    (hM : ∀ τ (k : Fin (D.R.sigW ((i : ℕ) + 1)).2),
      w.aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k)
    (hn : w.n = D.R.nV) : w = kaR Tp hK ((i : ℕ) + 1) := by
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have h1 := (inR_succ i).1
  have h2 := (inR_succ i).2
  have hs : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ h1 h2 _
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  have eP : w.aP = (kaR Tp hK ((i : ℕ) + 1)).aP := by
    funext τ a
    have h := (hK _ h1 h2 τ).1 a
    have h' := GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D i τ a (hp ▸ a.2)
    have e := kaWt_big D hK (even_nV Tp) _ h1 h2 τ a
    rw [← h, ← hp, ← e] at h'
    rw [hP τ a, hs τ]
    exact_mod_cast h'
  have eM : w.aM = (kaR Tp hK ((i : ℕ) + 1)).aM := by
    funext τ c
    have h := (hK _ h1 h2 τ).2 (Fin.rev c)
    have hc := c.2
    have h' := GlobalTheory.RecordWeightVec.aMi_eq_aMinusQ D i τ _ c (Fin.rev c) hq (by rw [Fin.val_rev]; omega)
    have e := kaWt_small D hK (even_nV Tp) _ h1 h2 τ c
    rw [← hp, ← neg_neg (DV.aMinusQ _ _ _ _), ← h, ← Int.cast_neg, ← e] at h'
    rw [hM τ c, hs τ]
    exact_mod_cast h'
  have en : w.n = (kaR Tp hK ((i : ℕ) + 1)).n := hn.trans (kaWt_n _ _ _ _).symm
  generalize kaR Tp hK ((i : ℕ) + 1) = u at eP eM en
  cases w; cases u
  simp only at eP eM en
  subst eP eM en
  rfl

theorem exists_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst), J.Q.Canon → HalfEX J.toCore EX → RunsOk fw r → ∃ O : OnObj ((R.toCx F).data F.cr false) (Mir R) c, IsRec Tp hK EX F fw r O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c _ hE ok
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  have hc : LawsCore J.toCore := (ok.laws v₁).p.toLawsCore
  have hinj : Function.Injective D.what₂.OtoLL := fun x y hxy => by
    obtain ⟨x, rfl⟩ := J.Q.eO.surjective x
    obtain ⟨y, rfl⟩ := J.Q.eO.surjective y
    rw [← fw.alg_eq, ← fw.alg_eq] at hxy
    exact congrArg _ (RingOfIntegers.ext ((algebraMap J.Q.c.F D.what₂.LL).injective hxy))
  have hκ : ∀ i : Fin D.R.m, κ i = kaR Tp hK ((i : ℕ) + 1) := fun i =>
    eq_kaR Tp hK i (κ i) (fun τ => (fw.kap i τ).1) (fun τ => (fw.kap i τ).2.1)
      (fw.kap i (plOf D (false, Classical.arbitrary _))).2.2
  choose ρ hρ using fun i : Fin D.R.m =>
    ActionPin.exists_rep (T := (r.used v₁).full) (inst := inst) (R := R) (ok.action v₁ i) (mirIncl R)
  obtain ⟨O, z, act, y, ht⟩ := exists_tiedObj (F := F) (fw := fw) (hc := hc) (run := r.used) (h := fun v => (ok.laws v).p)
    (hinj := hinj) (EX := EX) (p := ownAt D) (wL := fun _ i => lR Tp hK ((i : ℕ) + 1))
    (wF := fun _ i => fR Tp hK ((i : ℕ) + 1)) (nT := Tp.TO) (ℓ := r.lev) (ph := fun _ => 1) (c := c) (mirIncl R)
    (blankObj D _ (Mir R) c fun i => R.nW i) ok.action ρ (fun _ i => hρ i)
  letI st : StarRing (𝓞 D.host.E) := J.Q.H.starRing
  letI := hostAlg D
  letI : ∀ s : GlobalTheory.RealIndexBound.RunData J, Algebra s.full.J.Q.c.F D.what₂.LL := fun _ => inst
  have hφ : ∀ x : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.what₂.LL x =
      algebraMap J.Q.c.F D.what₂.LL ((iE D hinj (recB hc) x : 𝓞 J.Q.c.F) : J.Q.c.F) := fun x => by
    refine Eq.trans ?_ (fw.alg_eq _).symm
    refine (oEOsFun_spec D x).symm.trans (congrArg D.what₂.OtoLL ?_)
    exact (J.Q.eO.apply_symm_apply _).symm
  have hσ : ∀ v (i : Fin D.R.m), O.σ v i =
      sigAt (Dw := J.Q.Dw ((i : ℕ) + 1)) (H := J.Q.H) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) ((i : ℕ) + 1) := fun v i => by
    letI : Algebra (recB (ok.laws v).p.toLawsCore).KO D.what₂.LL := inst
    refine (ht v i).1.toFormTieK.σ_eq.trans ?_
    rw [hκ i]
    exact (GlobalTheory.ScalarOfRun.sigAt_eq_sigRec D L Pm Tp hK (r.used v).full.toTop (ok.laws v).p hinj EX _ (inR_succ i) hE
      D.what₂.LL (algebraMap J.Q.c.F D.what₂.LL) hφ).symm
  refine ⟨{ O with
    E := fun v (j : Fin D.R.m) =>
      EAt (Xo := J.Q.Xo ((j : ℕ) + 1)) (c := J.Q.c) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) v ((j : ℕ) + 1)
    nnK := fun j : Fin D.R.m => nnKAt (H := J.Q.H) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) ((j : ℕ) + 1)
    T := (Tp.TO : ℝ)
    g1 := D.host.g 0
    g2 := D.host.g 1
    q1 := D.host.q
    dd := D.host.d
    sm := D.host.small
    k := (D.R.k : ℝ)
    m := (D.R.m : ℝ)
    f := (D.R.f : ℝ)
    x := L.sc.x
    eps := L.sc.eps
    Sc := L.Sc
    eta := L.etaSz
    bp := L.sc.b'
    X2 := L.sc.X'' D.R.n
    vd := vd2 D
    wt := fun _ => 2 * (D.R.f : ℝ) * L.sc.b
    th := fun l => Formalism.UnitaryBoundIntegral.thl D.R.k l
    ad := fun _ => 0
    DF := ((Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1)) : ℕ) : ℝ)
    rr := (D.R.r : ℝ)
    Nc := L.Nc
    T2 := D.host.T2.card
    pde := D.host.pde }, ok, hκ, ⟨hc, hinj, z, act, y, fun v i => ⟨{ (ht v i).1 with }, (ht v i).2⟩⟩, ⟨st, ?_⟩,
    rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨fun j => inR_succ j, fun _ => rfl, fun a => ?_, fun _ _ => rfl, hσ, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun j => ?_⟩
  · show star (D.embE (a : D.host.E)) = D.embE ((J.toCore.Q.H.bar a : 𝓞 D.host.E) : D.host.E)
    rw [bar_core, barE_eq_conj, D.embE_conj]
  · exact Nat.cast_le.2 (Finset.le_sup (f := fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1))) (Finset.mem_univ j))

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVacuumFinitePlacesRationalDarboux
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LatVac

theorem exists_isVac : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ M : Model σ X Y, (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ φ : (Fin n × Fin d → Fv F v) → ℂ, M.IsVac B.ψ v φ := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY M hrat v
  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood σ B hB
  obtain ⟨hAt, hSt⟩ := GlobalTheory.LatVac.latAtV_at_stable X Y v
  obtain ⟨hO, hC⟩ := GlobalTheory.T.hermitian_tensor_skewHermitian_lattice_open_compact σ B X Y r s r' s' hX hY M hrat v
  have hint := GlobalTheory.T.standardAddChar_symplectic_local_lattice_eq_one σ B X Y r s r' s' hB hX hY v θ
  have h2 : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (GlobalTheory.AdelicU.evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  let cc : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ)
  have hc0 : cc 0 = 1 := by simp [cc, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
  have hcc : ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      cc (γ + γ') = cc γ * cc γ' * B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') := by
    intro γ hγ γ' hγ'
    have e := GlobalTheory.T.traceSymplectic_add_self_expansion_half_idempotent σ B X Y r s r' s' hB hX hY (θ : E) hθ γ γ'
    have h1 := hint 1 (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
    rw [one_mul] at h1
    simp only [cc]
    rw [e]
    set a := GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ
    set b := GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ'
    set c := GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ'
    set f := GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ'
    have : ⅟(2 : AF F) * (a + b + 2 * c + f) = ⅟(2 : AF F) * a + ⅟(2 : AF F) * b + ⅟(2 : AF F) * f + c := by
      have h22 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self 2
      linear_combination c * h22
    rw [this, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1, mul_one]
  have hc2 : ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, cc (GlobalTheory.LatVac.liftV v 2 • γ) = 1 := by
    intro γ hγ
    simp only [cc]
    rw [GlobalTheory.LatVac.symp_smul_smul, ← mul_assoc, ← mul_assoc]
    refine hint _ ?_ γ hγ γ hγ
    rw [map_mul, map_mul, GlobalTheory.LatVac.evFin_liftV, h2]
    simpa using (v.adicCompletionIntegers F).natCast_mem 2
  obtain ⟨φ, hφ, hφ0, hact⟩ := GlobalTheory.T.exists_finitePlaceVacuum_of_heisenbergLattice M.co B.ψ v hB.std.1 (GlobalTheory.T.standard_adelic_character_nontrivial_at_places B.ψ hB.std v) _ hAt hSt hO hC
    cc hc0 hcc hc2
  exact ⟨φ, hφ, hφ0, θ, hθ, hact⟩

end GlobalTheory.LatVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v) {m n : Type} (P₀ P₁ : Matrix m n (Fv F v)), ∃ u : Matrix m n (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) u ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = P₀ ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = P₁ := by
  first | exact @GlobalTheory.SplitComps.exists_mat_comps | exact GlobalTheory.SplitComps.exists_mat_comps | (intros; apply GlobalTheory.SplitComps.exists_mat_comps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongrStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.FrameTransport.Cong.conj_mem_congLev | exact GlobalTheory.FrameTransport.Cong.conj_mem_congLev | (intros; apply GlobalTheory.FrameTransport.Cong.conj_mem_congLev <;> assumption)
end

