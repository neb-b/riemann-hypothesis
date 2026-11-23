module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0062
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0363
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisRowRowsMemEigensystemTypePart
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Formalism.LocalToGlobal.Columns.Bundle0026
public import Formalism.LocalToGlobal.Columns.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreMatching
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts


open AlgebraicGeometry CategoryTheory in
theorem GlobalTheory.OneMapRef.exists_scalar_of_marked : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → l.A = 1 → ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y') (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)), IsMark l L mk → A.Marked mk → A'.Marked mk → ∀ th th', A.Reads 1 y.s th → A'.Reads 1 y'.s th' → ∃ lam : ℂ, lam ≠ 0 ∧ th' = lam • th ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evR Xo c f y' = lam ^ n * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L hs hx hL hA y y' A A' mk hmk hm hm' th th' hr hr'
  have he := GlobalTheory.Dict.anFib_ex_eq E H Dw l Xo c r g X bas idx e x L y y' A A' hs hx hL hA mk hmk hm hm'
  have hfr : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z = A.fr j z := by
    intro j z hj
    have hch : ∀ z, ∃ i, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U i := fun z => by
      have h : (A.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
        rw [Xo.univ.t.PP.isLB.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      exact ⟨i, (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi⟩
    choose ch hc using hch
    have hyx : y'.x = y.x := by
      have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
      have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
      rw [← h1, ← h2, he]
    have ne' : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z ≠ 0 :=
      fun j z h => A'.fr_ne j z (by rw [he]; exact h)
    let q : (Fin g → ℂ) → ℂ := fun z => A.fr (ch z) z / A'.fr (ch z) z
    have key : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → q z = A.fr j z / A'.fr j z := fun j z h => by
      have hz : ⊤ ≤ (A.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (ch z)) := fun p hp => ⟨h hp, hc z hp⟩
      have h1 := A.fr_g j (ch z) z hz
      have h2 := A'.fr_g j (ch z) z (by rw [he]; exact hz)
      rw [he] at h2
      rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ A.fr_ne j z h))]
    have hq : Differentiable ℂ q := fun z0 => by
      have hO : IsOpen {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
        simpa using (A.hol (Xo.univ.t.PP.L.U (ch z0)) 0).1
      have h' : DifferentiableOn ℂ (A'.fr (ch z0)) {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
        simpa only [he] using A'.fr_hol (ch z0)
      have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} :=
        ((A.fr_hol (ch z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
          (key _ z hz).trans (div_eq_mul_inv _ _)
      exact hd.differentiableAt (hO.mem_nhds (hc z0))
    let pvh : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) GlobalTheory.Dict.FrameSign.pv_add
    let P : L →+ (Fin g → ℂ) := pvh.comp L.subtype.toAddMonoidHom
    have hP : Submodule.span ℝ (Set.range P) = ⊤ := by
      rw [← span_image_pv idx hs hx L (TensLat.span_of_selfD X hL)]
      congr 1
      ext w
      exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩
    have hper : ∀ z (a : L), ‖q (z + P a)‖ = ‖q z‖ := fun z a => by
      have h : ⊤ ≤ (A.ex (z + pv X idx x a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z) := by
        rw [GlobalTheory.Dict.FrameSign.ex_add_pv A z a.2]; exact hc z
      have h1 := A.fr_per a a.2 (ch z) z (hc z)
      have h2 := A'.fr_per a a.2 (ch z) z (by rw [he]; exact hc z)
      change ‖q (z + pv X idx x a)‖ = _
      rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
        A.χ_norm _ a.2, A'.χ_norm _ a.2,
        mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
    have hc0 := ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range P hP q hq hper z 0
    have h0 : q 0 = 1 := by
      have := A'.fr_0 (ch 0) (by rw [he]; exact hc 0)
      rw [hyx, ← A.fr_0 (ch 0) (hc 0)] at this
      change A.fr (ch 0) 0 / A'.fr (ch 0) 0 = 1
      rw [this, div_self (A.fr_ne _ _ (hc 0))]
    rw [h0, key j z hj] at hc0
    exact ((div_eq_one_iff_eq (ne' j z hj)).1 hc0).symm
  have hyx : y'.x = y.x := by
    have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
    have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
    rw [← h1, ← h2, he]
  have hu : y'.u = y.u := funext fun τ => funext fun i => by
    have d := A'.der ⟨τ, i⟩
    simp only [he] at d
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique d (A.der ⟨τ, i⟩)
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hyx hu
  subst hyx hu
  obtain ⟨a, ha⟩ := GlobalTheory.Frames.ChgOf.gen_unit' y.s s' y.gen gen'
  refine ⟨a, a.ne_zero, ?_, fun w n f hf => ?_⟩
  · refine (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L _ A' hs hx hL 1 s').1.unique hr' ?_
    intro j z pt h1 h2 hj
    rw [he] at h1 hj
    have h3 := hr j z pt h1 h2 hj
    have h4 := (GlobalTheory.sec_values_complex_fibre GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo y.x y.s).1
      a (fun _ => j) pt h2
    refine ((congrArg (Geo.Tor.valAt' pt _) (ha fun _ => j)).trans h4).trans ?_
    rw [hfr j z hj, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact congrArg _ h3
  · let t : Formalism.L2.Pj.Ix Dw → ℂˣ := fun i => match i with
      | none => a
      | some _ => 1
    refine (GlobalTheory.LamT.evR_frChg_tri (inferInstance) hf t (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
      (fun τ i => Matrix.one_apply_eq i) (y := y)
      (y' := ⟨y.x, hover', y.u, tan', eig', basis', s', gen'⟩)
      ⟨rfl, ((GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c ℂ y y y).1).2.1,
        (GlobalTheory.Frames.ChgOf.secBC_id_iff y.x _ y.s s').2 ha⟩).trans ?_
    congr 1
    simp [wchar, Fintype.prod_option, t, Formalism.L2.Pj.ex]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseWeightEqForcedLiftWeightStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseWeight_eq_forcedLiftWeight : ∀ (X : Stages) (i : Fin X.toD7.R.m) (τ : X.B.fields.Tau) (a : Fin X.B.R.nV),
    (X.B.wts.lamV ((i : ℕ) + 1) τ).w a =
      (Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ).w (Fin.cast (LiftBrg.rkEq X i) a) := by
  first | exact @GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef | exact GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef | (intros; apply GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisRowRowsMemEigensystemTypePartStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_row_rows_mem_eigensystem_type_part : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (hL : Lam3 Z), (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, (principalLevelFrame.isotE R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F.lv2 true))) (levChi _ (R.βY 0) (R.dat0 (R.levR F.lv2 true))) R.e0 (principalLevelFrame.rowRepR R.θ (Y.eFT (D.what₂.ft σ)))).comap R.HE.e ≤ R.EEp3 (Classical.choose hL (D.what₂.ft σ)) := by
  first | exact @GlobalTheory.Mem.IsotPart.isot_part | exact GlobalTheory.Mem.IsotPart.isot_part | (intros; apply GlobalTheory.Mem.IsotPart.isot_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcPrVEqOneOfAdAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdPlace

theorem bc_prV_eq_one_of_adAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (η : GL (Fin n) (AfE F E)), (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ i j, adAt F w (η.1 i j) = if i = j then 1 else 0) → bc (prV (E := E) v) η = 1 := by
  intro F E _ _ _ _ _ n v η h
  refine Units.ext (Matrix.ext fun i j => ?_)
  change prV (E := E) v (η.1 i j) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j
  rw [Matrix.one_apply, ← sub_eq_zero]
  have e : (if i = j then (1 : E ⊗[F] v.adicCompletion F) else 0) = prV (E := E) v (if i = j then 1 else 0) := by
    split_ifs <;> simp
  rw [e, ← map_sub]
  refine ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).1).2 fun w hw => ?_
  rw [map_sub, h w hw i j]
  split_ifs <;> simp

end GlobalTheory.Mem.Col2.AdPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceDefiniteFormIrreducibleAlgebraicStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientSpace_definiteForm_irreducibleAlgebraicWeight : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), RatIso P e → ∀ (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W), Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∃ (alg : Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e)) (irr : (wtRep c e).IsIrreducible), ∀ (a : NG.AlgWt D.host.E V.rank) (τ : D.what₂.Tau) (lam0 : Fin V.rank → ℤ), NG.AlgWt.IsDual { W := c.W, ρ := wtRep c e, alg := alg, irr := irr } a → a.HWAt (Formalism.L2.embT D τ) lam0 → lam0 = (lam τ).w := by
  first | exact @GlobalTheory.MtIn.wt_main | exact GlobalTheory.MtIn.wt_main | (intros; apply GlobalTheory.MtIn.wt_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterComplexEqLevelCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section
namespace GlobalTheory.Mem.ChiType

theorem embLL_chiAt_eq_levChi : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (w : Pl X.toD7.host.E) (hw : w ∈ (X.B.primes px).vGs) (u : (kP w)ˣ),
      X.toD7.what₂.embLL ((Formalism.L2.Col.chiAt I.Ch ⟨w, hw⟩ (i : ℕ) u : X.B.fields.Kˣ) : X.B.fields.K) =
        ((L.chi ((i : ℕ) + 1) w u : ℂˣ) : ℂ) := by
  intro X px I U L hI hL i w hw u
  have hw' : w ∈ L.Pg := hL.Pg ▸ hw
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP w)
  have hu0 : (u : kP w) ≠ 0 := u.ne_zero
  have ha0 : ((a : 𝓞 X.toD7.host.E) : X.toD7.host.E) ≠ 0 := by
    intro h0
    apply hu0
    rw [← ha, (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 X.toD7.host.E) X.toD7.host.E).1 h0, map_zero]
  let k : X.toD7.host.Eˣ := Units.mk0 _ ha0
  have h1 := (hI.ch_tied.mu0 i).atg ⟨w, hw⟩ k a u rfl ha.symm
  have h2 := hL.is.chi i w hw' a k u rfl ha.symm
  rw [hL.C] at h2
  have h2' : (L.chi ((i : ℕ) + 1) w u : ℂˣ) = ((((Top.Fr.at X I.C).mu0 i).locK w k))⁻¹ := by
    rw [← h2, MonoidHom.inv_apply, inv_inv]
  have e : Formalism.L2.Col.chiAt I.Ch ⟨w, hw⟩ (i : ℕ) u = I.Ch.chi i ⟨w, hw⟩ u := by
    simp only [Formalism.L2.Col.chiAt, Formalism.L2.Col.extChi]
    rw [dite_eq_left (show (i : ℕ) < X.B.R.m from i.2)]
    rfl
  rw [e, h2', Units.val_inv_eq_inv_val]
  change _ = (((((I.C.mu0 i).locK (⟨w, hw⟩ : {w // w ∈ (X.B.primes px).vGs}).1) k : ℂˣ) : ℂ))⁻¹
  rw [h1, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
  rfl

end GlobalTheory.Mem.ChiType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnPointEqOfDecoAndCosetReduction
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

theorem inv_smul_mem_of_be_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.at w.1) (h0 : d.be w x = 0) :
    ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • x ∈ d.at w.1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TopStep.liftFr_spec hd w
  set fr := d.liftFr w with hfr
  have e : fr (fr.symm x) = x := fr.apply_symm_apply x
  have hs : fr.symm x ∈ stdAt E n w.1 := (h1 _).1 (by rwa [e])
  have hr := h2 _ hs
  rw [e, h0] at hr
  have hi := GlobalTheory.TopStep.mem_stdAt.1 hs
  have hs' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • fr.symm x ∈ stdAt E n w.1 := GlobalTheory.TopStep.mem_stdAt.2 fun i => by
    have := GlobalTheory.TopStep.intAt_div_of_redP hq (hi i) (congrFun hr i).symm
    rwa [div_eq_inv_mul] at this
  have := (h1 _).2 hs'
  rwa [map_smul, e] at this

theorem sub_mem_of_be_eq {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {y y' z : Sp E n}
    (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.at w.1) (hy' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y' ∈ d.at w.1)
    (hz : z - y' ∈ d.at w.1)
    (e : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)) :
    y - y' ∈ d.at w.1 := by
  have hq0 : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hqz : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y') ∈ d.at w.1 :=
    GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) hz
  have e1 : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y')) = 0 := by
    rw [GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) hz, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul]
  have e2 := hd.be_add w _ hqz _ hy'
  rw [← smul_add, sub_add_cancel, e1, zero_add, ← e] at e2
  have hx : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (y - y') ∈ d.at w.1 := by
    rw [smul_sub]
    exact sub_mem hy hy'
  have e3 := hd.be_add w _ hx _ hy'
  rw [← smul_add, sub_add_cancel, e2, right_eq_add] at e3
  have := inv_smul_mem_of_be_eq_zero hd w hq hx e3
  rwa [smul_smul, inv_mul_cancel₀ hq0, one_smul] at this

theorem mem_coset {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] {L : Submodule A M} {y z : M} :
    z ∈ {z | z - y ∈ L} ↔ z - y ∈ L := Iff.rfl

theorem coset_eq {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] (L : Submodule A M) {y y' : M} (h : y - y' ∈ L) :
    {z | z - y ∈ L} = {z | z - y' ∈ L} := by
  refine Set.ext fun z => ?_
  rw [mem_coset, mem_coset]
  refine ⟨fun h' => ?_, fun h' => ?_⟩
  · have := add_mem h' h
    rwa [sub_add_sub_cancel] at this
  · have := sub_mem h' h
    rwa [sub_sub_sub_cancel_right] at this

theorem eq_of_deco_bar : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, q.1.1.deco = q'.1.1.deco → MemChart.bar q = MemChart.bar q' → q = q' := by
  intro X Pr R sel S mu cst u j hQ hq q q' hd hb
  have hP : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P => by
    have := P.2
    simpa [rowSG, uSG, hQ] using this
  have hfr : q.1.1 = q'.1.1 := by
    apply Subtype.ext
    have hE : ∀ a, a ∈ QE sel (mu : Chr X.F X.E X.K) → False := fun a ha => by
      rw [hQ] at ha
      simp at ha
    exact Prod.ext hd (funext fun P => (hE _ P.2).elim)
  suffices h2 : q.1.2 = q'.1.2 from Subtype.ext (Prod.ext hfr h2)
  by_cases hj : j + 1 = R.m
  · obtain ⟨y, hy, eY⟩ := q.mem_ybSet hj
    obtain ⟨y', hy', eY'⟩ := q'.mem_ybSet hj
    have eN : q'.1.1.deco.1.N = q.1.1.deco.1.N := by rw [hd]
    rw [eN] at hy' eY'
    have key : ∀ e : rowSG Pr sel mu → ℤ, (∀ P, e P = 0) → y - y' ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N e := by
      intro e he
      refine (mem_locLat _ _ _ _).2 fun P => ?_
      rw [he P, zpow_zero, inv_one, one_smul]
      have hm : q.1.1.deco.1.be ⟨P.1, hP P⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar q ⟨P.1, hP P⟩ :=
        ⟨y, by rw [eY, mem_coset, sub_self]; exact zero_mem _, rfl⟩
      rw [congrFun hb ⟨P.1, hP P⟩] at hm
      obtain ⟨z, hz, ez⟩ := hm
      rw [← hd] at ez
      rw [eY'] at hz
      have hz' := (mem_locLat _ _ _ _).1 (mem_coset.1 hz) P
      rw [if_pos (hP P), zpow_zero, inv_one, one_smul] at hz'
      have h1 := (mem_locLat _ _ _ _).1 hy P
      have h2 := (mem_locLat _ _ _ _).1 hy' P
      rw [if_pos (hP P), _root_.zpow_neg_one, inv_inv] at h1 h2
      exact sub_mem_of_be_eq q.1.1.deco.2 ⟨P.1, hP P⟩ (hq _ (hP P)) h1 h2 hz' ez
    rw [eY, eY']
    exact coset_eq _ (key _ fun P => if_pos (hP P))
  · have h1 := q.2
    have h1' := q'.2
    rw [ysAt_ys_of_ne sel mu cst hj] at h1 h1'
    exact h1.trans h1'.symm

end GlobalTheory.Mem.Col2.MemChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetCongrIndexFramesLocalLattices
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem cosetIn_congr : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p p' : PtAt R sel mu cst u j), p.1.2 = p'.1.2 → p.1.1.fr = p'.1.1.fr → (∀ w : Pr.vGs, localization₂ w.1.asIdeal p.1.1.deco.1.N = localization₂ w.1.asIdeal p'.1.1.deco.1.N ∧ p.1.1.deco.1.be w = p'.1.1.deco.1.be w) → cosetIn p = cosetIn p' := by
  intro X Pr R sel S mu cst u j p p' h2 hfr hloc
  have hF : ∀ P, frsF sel mu p.1.1 P = frsF sel mu p'.1.1 P := by
    intro P
    unfold frsF
    split_ifs with h
    · have e1 := (hloc ⟨P.1, h⟩).1
      have e2 := (hloc ⟨P.1, h⟩).2
      unfold Deco.liftFr Deco.at
      rw [e1, e2]
    · rw [hfr]
  funext P
  unfold cosetIn
  rw [h2, hF P]

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetFramesInvariantRationalUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_frames_invariant_rational_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → ∀ (q q' : PtAt R sel mu cst u j) (γ : UF X.E (R.N j)), q'.1.1 = ((γ, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • q.1.1 → q'.1.2 = (fun z => γ.1 z) '' q.1.2 → cosetIn q' = cosetIn q := by
  exact @GlobalTheory.Mem.Col2.cosetIn_smul_unitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesRationalActionEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem cosetIn_act_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (j : ℕ) (b : (I.stp u a j).β) (x : (I.stp u a j).G b) (p : (I.stp u a j).D b), x.2 = 1 → cosetIn ((I.stp u a j).act b x p) = cosetIn p := by
  intro B X I _ l u a j b x p hx
  obtain ⟨γ, κ⟩ := x
  simp only at hx
  subst hx
  exact _root_.GlobalTheory.Mem.Col2.cosetIn_smul_unitary _ _ _ _ _ _ _ _ _ (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr _ _ γ rfl rfl

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.StdSize

theorem vstd_size_ev : Top.Ev fun K => ∀ X : Stages, K.Over X.B.toPre →
    (∀ i, Formalism.IndefR.FWT.VStd X.toD7 i) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  intro K hK X hX
  obtain ⟨-, -, -, -, -, -, hVf, -⟩ := hK X hX
  obtain ⟨hR, -⟩ := GlobalTheory.Mem.HostFrames.val_of_over hX
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hVf i
    rw [GlobalTheory.StdFrameCounterexample.vstd_iff]
    refine ⟨Matrix.ext fun a b => ?_, fun x => ?_⟩
    · rw [HSpace.gram, h1, Matrix.one_apply]
    · rw [h2, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_sum_self]
      refine forall_congr' fun a => ?_
      constructor
      · rintro ⟨y, hy⟩
        rw [← hy]; exact y.2
      · intro h
        exact ⟨⟨x a, h⟩, rfl⟩
  · have h4 := hR.2.2.2
    show 8 * X.B.R.f * X.B.R.r + 4 ≤ X.B.R.r + X.B.R.t
    omega

end GlobalTheory.Mem.StdSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerDeepAtOnePlaceUnitAtOtherStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_deep_at_one_place_unit_at_other : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → A ≠ A' → ∀ c : Ω, IsIntegral ℤ c → c ≠ 0 → ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  first | exact @GlobalTheory.TwoPlaces.exists_deep_one_sub | exact GlobalTheory.TwoPlaces.exists_deep_one_sub | (intros; apply GlobalTheory.TwoPlaces.exists_deep_one_sub <;> assumption)
end

