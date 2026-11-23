module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralZpowOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.SecFrame

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FlagFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
  {Tau : Type} (κ : Tau ≃ X.Ψ)

def frameAt (z : Pt Tau j (r - j)) : Frame X.Ψ r := fun τ =>
  (mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) : mat (frameAt X hj κ z) τ =
    mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) := rfl

theorem frameCo_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    frameCo X hj (frameAt X hj κ z) τ = fromBlocks 1 (z (κ.symm τ)) 0 1 := by
  rw [frameCo, mat_frameAt, nonsing_inv_mul_cancel_left _ _ (det_x0F X _).isUnit, Equiv.apply_symm_apply]

theorem lminor_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i : Fin (m + 1)) : lminor Mᵀ i = lminor M i := by
  unfold lminor
  rw [← transpose_submatrix, det_transpose]

theorem frameAt_mem (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    frameAt X hj κ z ∈ X.dom := by
  intro τ
  set Z := z (κ.symm τ) with hZ
  set B : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ := fromBlocks 1 Z 0 1 with hB
  set M := (reindex (idx hj) (idx hj)).symm B with hM
  have hRM : reindex (idx hj) (idx hj) M = B := Equiv.apply_symm_apply _ _
  have hdM : M.det = 1 := by
    rw [hM, reindex_symm, det_reindex_self, hB, det_fromBlocks_zero₂₁]; simp
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_frameAt, det_mul, ← hM, hdM, mul_one]; exact det_x0F X τ
  · set Dg : Matrix (Fin r) (Fin r) ℂ := diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ) with hDg
    have h0 := congrArg transpose (isOrth_x0F X τ)
    rw [gram_eq_mul, diagonal_transpose, hp] at h0
    have hT : (gram τ.1 X.Gm (mat (frameAt X hj κ z) τ))ᵀ = Mᴴ * Dg * M := by
      rw [gram_eq_mul, mat_frameAt, ← hM, hDg, ← h0]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have hR : reindex (idx hj) (idx hj) (Mᴴ * Dg * M) = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
      have : reindex (idx hj) (idx hj) (Mᴴ * Dg * M) =
          (reindex (idx hj) (idx hj) M)ᴴ * reindex (idx hj) (idx hj) Dg * reindex (idx hj) (idx hj) M := by
        simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
      rw [this, hRM, hDg, reindex_sgn hj, Formalism.UG.Jpq, hB, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply,
        fromBlocks_multiply]
      simp [hQ, sub_eq_neg_add]
    have hZd : (hQ Z).PosDef := hz (κ.symm τ)
    have h2 : (reindex (idx hj) (idx hj) (Mᴴ * Dg * M)).toBlocks₂₂.PosDef := by
      rw [hR, toBlocks_fromBlocks₂₂]; exact hZd
    have hs : (-schur (reindex (idx hj) (idx hj) (Mᴴ * Dg * M))).PosDef := by
      rw [hR, schur, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
      have e : -(-1 - -Z * (hQ Z)⁻¹ * -Zᴴ) = (1 : Matrix (Fin j) (Fin j) ℂ) + Z * (hQ Z)⁻¹ * Zᴴ := by
        simp [Matrix.neg_mul, Matrix.mul_neg]; exact add_comm _ _
      rw [e]
      exact PosDef.add_posSemidef PosDef.one (hZd.inv.posSemidef.mul_mul_conjTranspose_same Z)
    have key := signs_of_blocks (isBlockOrderedSumEquiv_trueIndex hj) (Mᴴ * Dg * M) h2 hs i
    rw [dmin, hp, ← lminor_transpose, hT]
    exact key

theorem domPt_frameAt (z : Pt Tau j (r - j)) : domPt X hj κ (frameAt X hj κ z) = z := by
  funext t
  simp only [domPt, frameCo_frameAt, Equiv.symm_apply_apply, moeb_zero, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    inv_one, Matrix.mul_one]

theorem co_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    coW X hj (frameAt X hj κ z) τ = 1 ∧ coOm X hj (frameAt X hj κ z) τ = 1 := by
  simp [coW, coOm, frameCo_frameAt, toBlocks_fromBlocks₂₁]

theorem differentiable_frameAt [Fintype Tau] (τ : X.Ψ) (a b : Fin r) :
    Differentiable ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ => mat (frameAt X hj κ (unflat v)) τ a b) := by
  have hM : ∀ c, Differentiable ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ =>
      ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b) := by
    intro c
    simp only [reindex_symm, reindex_apply, Equiv.symm_symm, submatrix_apply]
    rcases (idx hj) c with c' | c' <;> rcases (idx hj) b with b' | b' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, unflat, of_apply] <;>
      first | exact differentiable_const _ | exact differentiable_apply _
  simp only [mat_frameAt, Matrix.mul_apply]
  exact Differentiable.fun_sum (u := Finset.univ) (A := fun c (v : Tau × Fin j × Fin (r - j) → ℂ) =>
    mat (x0F X) τ a c * ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b)
    fun c _ => (hM c).const_mul _

end GlobalTheory.ShFam.SecFrame

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorCorrespondencePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam
noncomputable section
namespace GlobalTheory.IntFam.TermLift

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev gB : D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (toUnit _) (𝟙 _)

abbrev trB (mu : D.X) : D.P.A ⟶ D.P.A := padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)

omit [IsDomain R] in
theorem comp_padd {T T' : Over (Spec (CommRingCat.of R))} (A : Over (Spec (CommRingCat.of R))) [GrpObj A]
    (x : T' ⟶ T) (a b : T ⟶ A) : x ≫ padd A a b = padd A (x ≫ a) (x ≫ b) := by
  rw [padd, padd, ← Category.assoc, comp_lift]

omit [IsDomain R] in
theorem comp_toUnit {Y T W : Over (Spec (CommRingCat.of R))} (f : 𝟙_ _ ⟶ W) (x : T ⟶ Y) :
    x ≫ toUnit Y ≫ f = toUnit T ≫ f := by
  rw [← Category.assoc, toUnit_unique (x ≫ toUnit Y) (toUnit T)]

theorem gB_famφT (β : D.X) (i : Fin 4) : (gB D).left ≫ famφT D (𝟙_ _) β i = D.famφB β i := by
  fin_cases i
  · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (lift_snd (toUnit D.P.A) (𝟙 D.P.A))
  · refine congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (?_ : gB D ≫ padd D.P.A (snd _ _) (toUnit _ ≫ D.c β) = _)
    rw [comp_padd, lift_snd, comp_toUnit]
  · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (comp_toUnit (D.c β) (gB D))
  · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (comp_toUnit (MonObj.one : 𝟙_ _ ⟶ D.P.A) (gB D))

theorem gB_trT (mu : D.X) : gB D ≫ trT D (toUnit (𝟙_ _) ≫ D.c mu) = trB D mu ≫ gB D := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, trT, lift_fst, lift_fst]
    exact toUnit_unique _ _
  · rw [Category.assoc, Category.assoc, trT, lift_snd, lift_snd, Category.comp_id, comp_padd, lift_snd,
      ← Category.assoc, lift_fst, comp_toUnit]

theorem gB_trT_famφT (mu α : D.X) (i : Fin 4) :
    (gB D).left ≫ (trT D (toUnit (𝟙_ _) ≫ D.c mu)).left ≫ famφT D (𝟙_ _) α i = (trB D mu).left ≫ D.famφB α i := by
  rw [← Category.assoc, ← Over.comp_left, gB_trT, Over.comp_left, Category.assoc, gB_famφT]

theorem formEq (k : ℕ) (α mu : D.X) :
    FormEq (Sum.elim (fun i => (trB D mu).left ≫ D.famφB α i)
        (fun i => (gB D).left ≫ deltaφT D (α + k • mu) α (toUnit (𝟙_ _) ≫ D.c mu) i))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.famφB (α + k • mu)) (DegPre.famε k) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, deltaφT, DegPre.deltaε, gB_famφT, gB_trT_famφT,
    zpow_neg, Finset.prod_inv_distrib]
  rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem prB_gB : DegPre.prB D F ≫ gB D = toUnit (TF (R := R) F) ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, whiskerRight_fst]
    exact toUnit_unique _ _
  · rw [Category.assoc, lift_snd, whiskerRight_snd, Category.comp_id]

theorem trF_prB (mu : D.X) : DegPre.trF D F mu ≫ DegPre.prB D F = DegPre.prB D F ≫ trB D mu := by
  rw [DegPre.trF, lift_snd, comp_padd, Category.comp_id, comp_toUnit]

end GlobalTheory.IntFam.TermLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeoIn

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}


set_option maxHeartbeats 1000000 in
theorem mkStable_of_rhoGeo (t : FWTie T R κ v₀) (hp : ∀ i, OMPins T R κ v₀ O i) (hr : RhoGeo t O) (i : Fin D.R.m) :
    (R.FW i).MKStable := by
  have hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (O i).lev2 := (hp i).2.act.1
  by_cases hk : ActKeeps (κ := κ) O i
  · have h0 := (hr i).1 hk
    intro g x
    have key : ∀ hx : x ∈ (R.FW i).WK, (R.FW i).ρ g x ∈ (R.FW i).WK ∧ (x ∈ (R.FW i).MK → (R.FW i).ρ g x ∈ (R.FW i).MK) := by
      intro hx
      obtain ⟨f, hf⟩ := (t.e i).surjective ⟨x, hx⟩
      have hfx : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = x := congrArg Subtype.val hf
      subst hfx
      obtain ⟨h1, h2⟩ := h0 g f
      rw [← h2]
      refine ⟨(t.e i _).2, fun hm => (t.mem_MK i _).2 ?_⟩
      exact GlobalTheory.LevActInt.intAll_actLev T κ i (O i).lev2 t.laws hact g f ⟨_, h1⟩ rfl ((t.mem_MK i f).1 hm)
    exact ⟨fun hx => (key hx).1, fun hx => (key hx.1).2 hx⟩
  · intro g x
    rw [(hr i).2 hk g]
    exact ⟨id, id⟩

end


set_option maxHeartbeats 1000000 in
theorem inGeo_and_lUnif_and_lIntegral : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (ph : Fin D.R.m → ℂ) (B : GeoHalf T R ph), PreChar R → R.grp_chiW → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → InGeo B ∧ R.LUnif ∧ R.LIntegral := by
  intro hP D G _ _ Pl0 T0 A T _ R ph B hC hχ hp hn
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hJ := GlobalTheory.CuspValues.jEvExists_and_jEvBar D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hI := GlobalTheory.MemberEvalInj.evInj_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hU := GlobalTheory.ReadingSpan.jUnif hP D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp hJ.1 hJ.2 hI hn
  have hL := GlobalTheory.MemberLatFull.latFull_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hG := GlobalTheory.geoAct_of_ties_of_equivAll T R B.κ B.v₀ B.O hC.lev hC.models.inf hC.models.HW ht hp B.pins B.equivAll
  have hx := _root_.GlobalTheory.EquivConst.exists_equivariant_constants T R B.κ B.v₀ B.O hC.lev ht hp B.pins
  refine ⟨⟨hJ.1, hJ.2, hI, hU, hG, hL, B.fw.dimMatch⟩, fun i σ => ?_, fun i => ?_⟩
  · exact ⟨(GlobalTheory.TiedUnif.indep_span_of_tie B.fw hC.models.HW B.bar hU i σ).1,
      (GlobalTheory.TiedUnif.indep_span_of_tie B.fw hC.models.HW B.bar hU i σ).2,
      GlobalTheory.TiedUnif.rhoIs_of_eqAt B.fw hC.models.HW hC.models.gW hχ B.bar B.rhoGeo hU i σ
        (fun h hV => B.equivAll i _ h hV (hx i _ h hV))
        fun h hV => B.equivAll i _ (good_resC T h) hV (hx i _ (good_resC T h) hV)⟩
  · exact ⟨B.fw.ks i, GlobalTheory.GoodLat.mkFull_of_tie B.fw hL i, mkStable_of_rhoGeo B.fw B.pins B.rhoGeo i⟩

end GlobalTheory.RealGeoIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m : ℕ}

theorem lin_comp {u u' : Fin m → V} (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0)
    (hu : ∀ j, u' j = ∑ i, A j i • u i) (d : Fin m → k) (j : Fin m) (hd : ∀ i, j < i → d i = 0) :
    ∃ e : Fin m → k, (∀ i, j < i → e i = 0) ∧ e j = d j * A j j ∧ ∑ i, d i • u' i = ∑ i, e i • u i := by
  refine ⟨fun i => ∑ l, d l * A l i, fun i hi => Finset.sum_eq_zero fun l _ => ?_, ?_, ?_⟩
  · rcases lt_or_ge j l with h | h
    · rw [hd l h, zero_mul]
    · rw [hA l i (h.trans_lt hi), mul_zero]
  · refine Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hA l j h, mul_zero]
    · rw [hd l h, zero_mul]
  · simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm

theorem lin_symm {u u' : Fin m → V} (hi : ∀ c c' : Fin m → k, ∑ i, c i • u' i = ∑ i, c' i • u' i → c = c')
    (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0) (hu : ∀ j, u' j = ∑ i, A j i • u i) :
    ∃ B : Fin m → Fin m → k, (∀ j i, j < i → B j i = 0) ∧ (∀ j, u j = ∑ i, B j i • u' i) ∧ ∀ j, A j j * B j j = 1 := by
  classical
  let M : Matrix (Fin m) (Fin m) k := Matrix.of A
  have key : ∀ d : Fin m → k, ∑ i, d i • u' i = ∑ i, Matrix.vecMul d M i • u i := fun d => by
    simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul, Matrix.vecMul, dotProduct, M, Matrix.of_apply]
    exact Finset.sum_comm
  have hM : IsUnit M := Matrix.vecMul_injective_iff_isUnit.1 fun d d' h => hi _ _ (by
    rw [key, key]; exact congrArg (fun c : Fin m → k => ∑ i, c i • u i) h)
  obtain ⟨I⟩ := hM.nonempty_invertible
  have ht : M.BlockTriangular OrderDual.toDual := fun j i h => hA j i h
  have hB : ∀ j i, j < i → M⁻¹ j i = 0 := fun j i h => Matrix.blockTriangular_inv_of_blockTriangular ht h
  have h2 : ∀ j, u j = ∑ i, M⁻¹ j i • u' i := fun j => by
    rw [key, show Matrix.vecMul (M⁻¹ j) M = (M⁻¹ * M) j from rfl, Matrix.inv_mul_of_invertible]
    simp [Matrix.one_apply]
  refine ⟨fun j i => M⁻¹ j i, hB, h2, fun j => ?_⟩
  obtain ⟨e, -, he, h⟩ := lin_comp (fun j i => M⁻¹ j i) hB h2 (A j) j (hA j)
  have := hi e (Pi.single j 1) (by rw [← h, ← hu]; simp [Pi.single_apply])
  rw [← he, this, Pi.single_eq_same]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

section Tan

variable {k : Type} [Field k] (x : Sp k ⟶ X) {m : ℕ}

def Ind (u : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def Tri (u u' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  ∀ j, ∃ cf : Fin m → k, (∀ i, j < i → cf i = 0) ∧ IsCombAtG t x u cf (u' j)

variable {t x} {u u' u'' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)}

theorem comb_iff (U : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (U i)).left) a w ↔ w = (tv (∑ i, a i • U i)).left := by
  have h := (GlobalTheory.LieMet.isComb_iff U a _).2 rfl
  refine ⟨fun h' => ?_, fun e => e ▸ h⟩
  exact ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h').symm.trans
    ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h)

theorem exists_tan (h : ∀ i, IsTanAtG t x (u i)) : ∃ U : Fin m → TanM x t.G, u = fun i => (tv (U i)).left :=
  ⟨fun i => tanOf (h i), rfl⟩

theorem Tri.comp (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u') {d : Fin m → k}
    {j : Fin m} (hd : ∀ i, j < i → d i = 0) {w : Sp (DualNumber k) ⟶ t.G.left} (hw : IsCombAtG t x u' d w) :
    ∃ c e : Fin m → k, IsCombAtG t x u c (u' j) ∧ (∀ i, j < i → e i = 0) ∧ e j = d j * c j ∧ IsCombAtG t x u e w := by
  obtain ⟨U, rfl⟩ := exists_tan hu
  obtain ⟨U', rfl⟩ := exists_tan hu'
  choose A hA hc using h
  obtain ⟨e, h1, h2, h3⟩ := lin_comp A hA (fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)) d j hd
  exact ⟨A j, e, hc j, h1, h2, (comb_iff _ _ _).2 (h3 ▸ (comb_iff _ _ _).1 hw)⟩

theorem Tri.trans (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u')
    (h' : Tri t x u' u'') : Tri t x u u'' := fun j => by
  obtain ⟨d, hd, hw⟩ := h' j
  obtain ⟨-, e, -, h1, -, h2⟩ := h.comp hu hu' hd hw
  exact ⟨e, h1, h2⟩

theorem Tri.symm (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') : Tri t x u' u ∧
    ∀ j c d, IsCombAtG t x u c (u' j) → IsCombAtG t x u' d (u j) → c j * d j = 1 := by
  obtain ⟨U, rfl⟩ := exists_tan hu.1
  obtain ⟨U', rfl⟩ := exists_tan hu'.1
  choose A hA hc using h
  obtain ⟨B, h1, h2, h3⟩ := lin_symm (u := U) (u' := U') (fun c c' e => hu'.2 c c' _ ((GlobalTheory.LieMet.isComb_iff _ _ _).2 rfl)
    ((GlobalTheory.LieMet.isComb_iff _ _ _).2 e)) A hA fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)
  refine ⟨fun j => ⟨B j, h1 j, (GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)⟩, fun j c d hc' hd => ?_⟩
  rw [hu.2 _ _ _ hc' (hc j), hu'.2 _ _ _ hd ((GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)), h3]

theorem Tri.diag (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') {j : Fin m} {c : Fin m → k}
    (hc : IsCombAtG t x u c (u' j)) : c j ≠ 0 ∧ ∀ i, j < i → c i = 0 := by
  obtain ⟨h1, h2⟩ := h.symm hu hu'
  obtain ⟨d, -, hd⟩ := h1 j
  obtain ⟨c', h3, h4⟩ := h j
  exact ⟨left_ne_zero_of_mul_eq_one (h2 j c d hc hd), hu.2 _ _ _ hc h4 ▸ h3⟩

end Tan

section Norm

variable {t} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}


end Norm

end GlobalTheory.ShFam.Pad.Pull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicOnProjectiveConst
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CxPts

namespace GlobalTheory.ConstFn

variable {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ}

theorem ev_top_eq (a : Γ(X, ⊤)) (y : CxPts p σ) :
    ev p σ ⊤ a y = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (y.1.appTop.hom a) := by
  have h : ⊤ ≤ y.1 ⁻¹ᵁ (⊤ : X.Opens) := le_rfl
  show valR y.1 ⊤ a = _
  rw [valR, dite_eq_left h]
  rfl

theorem exists_ev_eq [UniversallyClosed p] [GeometricallyIntegral p] (a : Γ(X, ⊤)) :
    ∃ b : ℂ, ∀ y : CxPts p σ, ev p σ ⊤ a y = b := by
  have hZ : IsIntegral (pullback p (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := p) (spMap σ) _ _ (.of_hasPullback _ _)
  let fs := pullback.fst p (spMap σ)
  let sn := pullback.snd p (spMap σ)
  let e : ℂ →+* Γ(pullback p (spMap σ), ⊤) :=
    sn.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  letI : Algebra ℂ Γ(pullback p (spMap σ), ⊤) := e.toAlgebra
  have hcomp : (algebraMap ℂ Γ(pullback p (spMap σ), ⊤)).comp
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom) =
      fs.appTop.hom.comp p.appTop.hom := by
    have h : fs ≫ p = sn ≫ spMap σ := pullback.condition
    ext c
    have h' := congrArg (fun m : pullback p (spMap σ) ⟶ Sp F => m.appTop.hom c) h
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h'
    simp only [RingHom.comp_apply]
    refine Eq.trans ?_ h'.symm
    show sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
    simp
  have hint : IsIntegral ℂ (fs.appTop.hom a) := by
    obtain ⟨P, hP, h0⟩ := isIntegral_appTop_of_universallyClosed p a
    refine ⟨P.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)
    (K := integralClosure ℂ Γ(pullback p (spMap σ), ⊤))).2 ⟨_, hint⟩
  have hr' : e r = fs.appTop.hom a := congrArg Subtype.val hr
  refine ⟨r, fun y => ?_⟩
  let z : Sp ℂ ⟶ pullback p (spMap σ) :=
    pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp])
  have h1 : z ≫ fs = y.1 := pullback.lift_fst _ _ _
  have h2 : z ≫ sn = 𝟙 _ := pullback.lift_snd _ _ _
  have h3 : y.1.appTop.hom a = z.appTop.hom (fs.appTop.hom a) := by
    rw [← h1, Scheme.Hom.comp_appTop]; rfl
  have h4 : z.appTop.hom (sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r := by
    have e₂ : (z ≫ sn).appTop = sn.appTop ≫ z.appTop := Scheme.Hom.comp_appTop _ _
    rw [h2] at e₂
    have e₃ := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) e₂
    exact Eq.trans e₃.symm (by simp)
  rw [ev_top_eq, h3, ← hr']
  show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (z.appTop.hom (sn.appTop.hom _)) = r
  rw [h4]
  simp

end GlobalTheory.ConstFn

theorem GlobalTheory.ConstFn.holoOn_univ_const : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim)
    (q : CxPts Y.str σ → ℂ), R.HoloOn Set.univ q → ∃ b : ℂ, ∀ z, q z = b := by
  intro F _ Y σ R q hq
  have hB := LB.isLB_triv Y.X
  have hs : (fun _ => q : (LB.triv Y.X).ι → CxPts Y.str σ → ℂ) ∈ R.holSec (LB.triv Y.X) := by
    refine ⟨⟨fun i j y hi _ => ?_, fun i y h => (h mem_ptsIn_top).elim⟩, fun i => hq.mono (Set.subset_univ _)⟩
    cases i; cases j
    rw [gv_self hB hi, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC Y.isProjOver R hB).2 ⟨_, hs⟩
  let M : Submodule ℂ ((LB.triv Y.X).ι → CxPts Y.str σ → ℂ) :=
    { carrier := {s | ∃ b : ℂ, ∀ i z, s i z = b}
      zero_mem' := ⟨0, fun _ _ => rfl⟩
      add_mem' := fun {s t} ⟨b, hb⟩ ⟨c, hc⟩ => ⟨b + c, fun i z => by simp [hb, hc]⟩
      smul_mem' := fun c s ⟨b, hb⟩ => ⟨c * b, fun i z => by simp [hb]⟩ }
  obtain ⟨b, hb⟩ : SecC.val x ∈ M := SecC.val_mem_of (fun s => by
    obtain ⟨b, hb⟩ := GlobalTheory.ConstFn.exists_ev_eq (p := Y.str) (σ := σ) (s.f PUnit.unit)
    exact ⟨b, fun i z => by cases i; exact hb z⟩) x
  refine ⟨b, fun z => ?_⟩
  have e := congrArg Subtype.val hx
  rw [AnRead.coe_valC] at e
  have := hb PUnit.unit z
  rw [e] at this
  exact this
end
end

