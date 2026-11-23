module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagLiftGenericPointSpecializesResidue
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

theorem exists_valuation_point {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (y : M.Z) :
    ∃ (V : ValuationSubring Ω) (v : Sp V ⟶ M.Z), spMap (algebraMap V Ω) ≫ v = M.pt ∧
      v (IsLocalRing.closedPoint V) = y := by
  haveI : IsLocalRing (M.O y).toSubring := inferInstanceAs (IsLocalRing (M.O y))
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.mk (M.O y).toSubring).exists_le_valuationSubring
  let ψ : M.Z.presheaf.stalk y →+* V :=
    (M.stalkHom y).codRestrict V (fun a => hle (M.stalkEquiv y a).2)
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    have h1 : IsUnit (Subring.inclusion hle (M.stalkEquiv y a)) := ha
    exact (MulEquiv.isUnit_map (M.stalkEquiv y)).1 (hloc.map_nonunit _ h1)⟩
  refine ⟨V, spMap ψ ≫ M.Z.fromSpecStalk y, ?_, ?_⟩
  · have hs := M.pt_specializes (IsLocalRing.closedPoint Ω) y
    have hc : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V Ω) =
        M.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt := by
      ext a
      rfl
    calc spMap (algebraMap V Ω) ≫ spMap ψ ≫ M.Z.fromSpecStalk y
        = Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V Ω)) ≫ M.Z.fromSpecStalk y := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt) ≫
            Spec.map (M.Z.presheaf.stalkSpecializes hs) ≫ M.Z.fromSpecStalk y := by
          rw [hc, Spec.map_comp, Category.assoc]
      _ = M.pt := by
          rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · have ec : spMap ψ (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint ψ
    show M.Z.fromSpecStalk y (spMap ψ (IsLocalRing.closedPoint V)) = y
    rw [ec]
    exact Scheme.fromSpecStalk_closedPoint

theorem exists_valuation_point_var {F : Type} [Field F] (Y : Var F) (y : Y.X) :
    ∃ (V : ValuationSubring Y.Fn) (v : Sp V ⟶ Y.X), spMap (algebraMap V Y.Fn) ≫ v = (ratOf Y).pt ∧
      v (IsLocalRing.closedPoint V) = y :=
  exists_valuation_point (ratOf Y) y

theorem lift_specializes_genericPoint : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ q : Sp Y₁.Fn ⟶ Y₂.X, q ≫ f₂ = (ratOf Y₁).pt ≫ f₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q → ∀ y : Y₁.X, (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = y → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X) → q (IsLocalRing.closedPoint Y₁.Fn) ⤳ genericPoint Y₂.X := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ q hq hco y hy
  obtain ⟨V, v, hvg, hvc⟩ := exists_valuation_point_var Y₁ y
  have hs : f₂ ≫ X.str = Y₂.str := h₂.1.inducedModelMorphism_comp_structureMap
  haveI : IsProper (f₂ ≫ X.str) := hs ▸ inferInstance
  haveI : UniversallyClosed f₂ := UniversallyClosed.of_comp_of_isSeparated f₂ X.str
  have hE : ValuativeCriterion.Existence f₂ :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f₂) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f₂).1
  have hsq : q ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁) := by
    exact hq.trans ((congrArg (· ≫ f₁) hvg.symm).trans (Category.assoc _ _ _))
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := Y₁.Fn, i₁ := q, i₂ := v ≫ f₁, commSq := ⟨hsq⟩ }
  have hl₁ : spMap (algebraMap V Y₁.Fn) ≫ l.l = q := l.fac_left
  have hl₂ : l.l ≫ f₂ = v ≫ f₁ := l.fac_right
  have hinc := _root_.GlobalTheory.FlagBundle.coBear_closedPoint F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v l.l hl₂.symm
    (by
      have e : spMap (algebraMap V Y₁.Fn) ≫ v ≫ f₁ = (ratOf Y₁).pt ≫ f₁ :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hvg)
      have key : ∀ (x x' : Sp Y₁.Fn ⟶ X.X) (p p' : Sp Y₁.Fn ⟶ Y₁.X) (r r' : Sp Y₁.Fn ⟶ Y₂.X), x = x' → p = p' →
          r = r' → CoBear Eb S₁ φ₁ S₂ φ₂ x p r → CoBear Eb S₁ φ₁ S₂ φ₂ x' p' r' := by
        rintro _ _ _ _ _ _ rfl rfl rfl h
        exact h
      exact key _ _ _ _ _ _ e.symm hvg.symm hl₁.symm hco)
  have ec : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
      IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
  have hp' := hy (IsLocalRing.ResidueField V) (spMap (IsLocalRing.residue V) ≫ v)
    (spMap (IsLocalRing.residue V) ≫ l.l)
    (by
      show v (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = y
      rw [ec]
      exact hvc)
    ((Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hl₂.symm).trans
      (Category.assoc _ _ _).symm))
    (by convert hinc using 1; exact Category.assoc _ _ _)
  have e2 : l.l (IsLocalRing.closedPoint V) = genericPoint Y₂.X := by
    change l.l (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = _ at hp'
    rwa [ec] at hp'
  have e1 : q (IsLocalRing.closedPoint Y₁.Fn) =
      l.l (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn)) := by
    have := congrArg (fun g : Sp Y₁.Fn ⟶ Y₂.X => g (IsLocalRing.closedPoint Y₁.Fn)) hl₁
    exact this.symm
  have h2 := (IsLocalRing.specializes_closedPoint
    (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn))).map l.l.continuous
  convert h2 using 1
  exact e2.symm

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherRowsUpdatedScalars
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem prim_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : PrimRows3 R F)
    (h1 : ∀ i t p v, 0 < lam i t p v) (h2 : (R.updS R.kap lam).PThmB) (h3 : (R.updS R.kap lam).PThmA)
    (h4 : ((R.updS R.kap lam).toCx3 F).GalD F.cr false) : PrimRows3 (R.updS R.kap lam) F := by
  obtain ⟨⟨hE, hR⟩, ⟨hW, hL⟩⟩ := h.hecke
  exact
  { heckeR := h.heckeR
    heckeL := h.heckeL
    hecke := ⟨⟨hE, ⟨hR.intw, hR.comm, hR.parts⟩⟩, ⟨hW, ⟨hL.intw, hL.comm, hL.parts⟩⟩⟩
    gUnit := h.gUnit
    gEquiv := h.gEquiv
    block := h.block
    rowTest := h.rowTest
    liftTest := h.liftTest
    liftTestB := h.liftTestB
    liftOnto := fun hW' hh => h.liftOnto hW' ⟨hh.intw, hh.comm, hh.parts⟩
    pos := h.pos
    posScal := ⟨h.posScal.1, h1⟩
    levE := h.levE
    h2P := h.h2P
    thmB := h2
    sumE := h.sumE
    unif := h.unif
    mLat := h.mLat
    levW := h.levW
    thmA := h3
    sumW := h.sumW
    scalConj := h4
    dimParts := h.dimParts }


set_option maxHeartbeats 4000000 in
theorem pins_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (hP : Pins R F cG)
    (hs : (R.updS R.kap lam).IsScal (reFace F Dc Sp Zsc)) : Pins ((R.updS R.kap lam).withErr e) (reFace F Dc Sp Zsc) cG := by
  have h := hP.char
  have hC : (R.updS R.kap lam).WeakCharacterisation (reFace F Dc Sp Zsc) :=
    ⟨h.base, ⟨h.inert.tie, h.inert.onto, h.inert.hR, h.inert.hL, h.inert.SF⟩, h.fullY, h.fullX, h.fullP, hs,
      ⟨h.tup.mu_off, h.tup.mu_used, h.tup.mu_ne, h.tup.mu_conj, h.tup.mu_on⟩, h.phase, h.allPl⟩
  exact ⟨RealDat3.weak_characterisation_with_error hC e, reFace_keep (R.updS R.kap lam) F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩


set_option maxHeartbeats 4000000 in
theorem furtherRows_updatedScalars (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.updS R.kap lam) F := ⟨h.ex, h.conj, h.levelW, h.integral⟩

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CovolGL

theorem lcsc_GL (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace, Units.isEmbedding_embedProduct.secondCountableTopology⟩

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem pFin_ratGL (γ : GL (Fin a) E) :
    GeneralLinearGroup.map (pFin E) (ratGL E a γ) = PIW.ClassFinD.glIncl E a γ := by
  ext i j
  rfl

variable [_root_.NumberField.IsTotallyComplex E]

theorem pFin_splitCentre (t : ℝ) : GeneralLinearGroup.map (pFin E) (splitCentre E a t) = 1 :=
  pFin_infGL _


variable (E a) in
theorem isFiniteMeasure_quotMeasure (μ : Measure (GA E a)) [μ.IsHaarMeasure] :
    IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin a) (Af E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Af E)) := ⟨rfl⟩
  obtain ⟨_, _⟩ := lcsc_GL (Cinf E) a
  obtain ⟨_, _⟩ := lcsc_GL (Af E) a
  obtain ⟨e, he⟩ := _root_.GlobalTheory.CuspRep.GASplit.exists_split E a
  obtain ⟨S, hS⟩ := PIW.ClassFinD.borelKGL_of _root_.GlobalTheory.IwasawaFinAd.iwasawaAf _root_.GlobalTheory.UnipApproxGL.unipApprox PIW.ClassFinD.idele_class_finite E a
  choose Λ hΛ hΛK using fun s => GlobalTheory.T.exists_lattice_stabilizer_conj_finiteAdeleGL_integral E a s
  choose Ω hΩ hcov using fun s => GlobalTheory.T.exists_finite_measure_reduction_domain_infinity E a (Λ s) (hΛ s) (Measure.haar : Measure (GL (Fin a) (Cinf E)))
  refine ⟨?_⟩
  rw [quotMeasure_univ (isFundamentalDomain_stdDom (latticeGL E a) μ)]
  refine GlobalTheory.Mem.VolFin.measure_lt_top_of_cover e (latticeGL E a) μ S (PIW.ClassFinD.KGL E a) (_root_.GlobalTheory.isCompact_KGL E a) Ω hΩ
    (fun g => ?_) _ (isFundamentalDomain_stdDom _ μ)
  obtain ⟨γ, s, hs, k, hk, hx⟩ := hS (GeneralLinearGroup.map (pFin E) g)
  obtain ⟨η, hη, n, hn⟩ := hcov s (GeneralLinearGroup.map (pInf E) (ratGL E a γ⁻¹ * g))
  have hmem : ratGL E a η * splitCentre E a 1 ^ n * ratGL E a γ⁻¹ ∈ latticeGL E a :=
    mul_mem (mul_mem (ratGL_mem_latticeGL η) (zpow_mem_latticeGL n)) (ratGL_mem_latticeGL _)
  have hg : ratGL E a η * splitCentre E a 1 ^ n * ratGL E a γ⁻¹ * g =
      (ratGL E a η * splitCentre E a 1 ^ n) * (ratGL E a γ⁻¹ * g) := by simp only [mul_assoc]
  refine ⟨⟨_, hmem⟩, s, hs, ?_, ?_⟩
  · rw [Subgroup.smul_def, smul_eq_mul, he, hg, map_mul]
    exact hn
  · rw [Subgroup.smul_def, smul_eq_mul, he]
    simp only [map_mul, map_zpow, pFin_ratGL, pFin_splitCentre, _root_.one_zpow, mul_one, hx, map_inv]
    refine ⟨s⁻¹ * PIW.ClassFinD.glIncl E a η * s * k, (PIW.ClassFinD.KGL E a).mul_mem (hΛK s η hη) hk, ?_⟩
    simp only [smul_eq_mul]
    group


variable (E a) in
theorem isMulRightInvariant (μ : Measure (GA E a)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  have hd := isFundamentalDomain_stdDom (latticeGL E a) μ
  have hfin := isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← quotMeasure_univ hd]; exact measure_ne_top _ _
  exact GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ μ hd (hd.measure_ne_zero (NeZero.ne μ)) h1

theorem finvol : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure], IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) ∧ μ.IsMulRightInvariant :=
  fun E _ _ _ a μ _ => ⟨isFiniteMeasure_quotMeasure E a μ, isMulRightInvariant E a μ⟩

end GlobalTheory.CovolGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFixedBasisReductionMapConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem cong_zsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℤ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  rw [← Finset.sum_sub_distrib]
  refine W.sum_mem fun l _ => ?_
  have h1 : ((a l - a' l : ℤ) : ZMod g) = 0 := by push_cast; rw [h l, sub_self]
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  rw [← sub_smul, ht, mul_comm, mul_zsmul, natCast_zsmul]
  exact W.zsmul_mem (hu l) t

theorem cong_nsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℕ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  have := cong_zsmul W u hu (fun l => (a l : ℤ)) (fun l => (a' l : ℤ)) (fun l => by push_cast; exact h l)
  simpa only [natCast_zsmul] using this

theorem sum_nsmul_sum {V : Type*} [AddCommGroup V] {r : ℕ} (u : Fin r → V) (a : Fin r → ℕ)
    (b : Fin r → Fin r → ℕ) :
    ∑ j, a j • ∑ l, b l j • u l = ∑ l, (∑ j, a j * b l j) • u l := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem rebase_rel {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (F : V →+ V) (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (M c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1)
    (h : ∀ i, F (u i) - ∑ j, (M j i).val • u j ∈ W) (i : Fin r) :
    F (∑ j, (c j i).val • u j) - ∑ m, ((d * M * c) m i).val • ∑ l, (c l m).val • u l ∈ W := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_nsmul]
  have e1 : ∑ j, (c j i).val • F (u j) = ∑ j, (c j i).val • (F (u j) - ∑ l, (M l j).val • u l) +
      ∑ j, (c j i).val • ∑ l, (M l j).val • u l := by
    rw [← Finset.sum_add_distrib]; congr 1; funext j; rw [← smul_add, sub_add_cancel]
  rw [e1, sum_nsmul_sum, sum_nsmul_sum, add_sub_assoc]
  refine W.add_mem (W.sum_mem fun j _ => W.nsmul_mem (h j) _) (cong_nsmul W u hu _ _ fun l => ?_)
  have e2 : c * (d * M * c) = M * c := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcd, Matrix.one_mul]
  have e3 := congrFun (congrFun e2 l) i
  rw [Matrix.mul_apply, Matrix.mul_apply] at e3
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [show ∑ x, c x i * M l x = ∑ j, M l j * c j i from Finset.sum_congr rfl fun _ _ => mul_comm _ _, ← e3]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem rebase_span {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1) (a : Fin r → ℤ) :
    ∃ e : Fin r → ℤ, ∑ j, a j • u j - ∑ m, e m • ∑ j, (c j m).val • u j ∈ W := by
  refine ⟨fun m => ∑ l, ((d m l).val : ℤ) * a l, ?_⟩
  have e1 : ∑ m, (∑ l, ((d m l).val : ℤ) * a l) • ∑ j, (c j m).val • u j =
      ∑ j, (∑ m, (∑ l, ((d m l).val : ℤ) * a l) * ((c j m).val : ℤ)) • u j := by
    simp only [Finset.smul_sum, ← natCast_zsmul, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [e1]
  refine cong_zsmul W u hu _ _ fun j => ?_
  have e2 := congrFun (congrFun hcd j) j
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  have e3 : ∑ m, (∑ l, d m l * (a l : ZMod g)) * c j m = ∑ l, (c * d) j l * (a l : ZMod g) := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e3, hcd]
  simp [Matrix.one_apply]

variable {D : D7}

theorem incl_sum_nsmul (X : HidaSetting D) {r : ℕ} (a : Fin r → ℕ) (x : Fin r → Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (∑ j, a j • x j) = ∑ j, a j • incl X.B.I (x j) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp [incl, map_sum, map_nsmul, Finset.sum_apply]

theorem incl_nsmul (X : HidaSetting D) (a : ℕ) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (a • x) = a • incl X.B.I x := by
  funext t
  simp [incl, map_nsmul]

theorem nsmul_mem_wLat (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ)
    (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {y : Fin X.B.I.n → X.B.I.E} (hy : y ∈ X.B.I.L) :
    g • y ∈ wLat X w := by
  apply Submodule.subset_span
  refine ⟨(g : 𝓞 X.B.I.E), ⟨(g : 𝓞 D.host.E), hg, by simp⟩, y, hy, by ext t; simp⟩

theorem incl_mem_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {y : Fin X.B.I.n → X.B.I.E}
    (hy : y ∈ wLat X w) : incl X.B.I y ∈ wLf X w :=
  Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem fixRed_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) (c : G0g D.nd), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → FixRed X red b → ∃ b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E, FixRed X (fun k => c⁻¹ * red k * c) b' := by
  intro D X red b c hg hf
  classical
  refine ⟨fun kv i => ∑ j, (((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
    Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • b kv j, fun kv => ?_⟩
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨⟨hbL, hbspan⟩, hrel⟩ := hf kv
  have hcd : ((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) *
      (((c kv)⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.mul_inv (c kv)
  have hgL : ∀ j, D.host.g kv.1 • b kv j ∈ (wLat X (D.naut.plGw kv.1 kv.2)).toAddSubgroup :=
    fun j => nsmul_mem_wLat X _ _ (hg kv) (hbL j)
  refine ⟨⟨fun i => ?_, fun y hy => ?_⟩, fun k hk i => ?_⟩
  · exact Submodule.sum_mem _ fun j _ => nsmul_mem (hbL j) _
  · obtain ⟨a, ha⟩ := hbspan y hy
    obtain ⟨e, he⟩ := rebase_span _ (b kv) hgL _ _ hcd a
    refine ⟨e, ?_⟩
    have h2 := Submodule.add_mem _ ha he
    simp only [Int.cast_smul_eq_zsmul] at h2 ⊢
    rwa [sub_add_sub_cancel] at h2
  · have hu : ∀ j, D.host.g kv.1 • incl X.B.I (b kv j) ∈ (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun j => by
      rw [← incl_nsmul]; exact incl_mem_wLf X _ (hgL j)
    have hM : ∀ i, (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom (incl X.B.I (b kv i)) -
        ∑ j, (((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • incl X.B.I (b kv j) ∈
        (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun i => by
      have := hrel k hk i
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this
    have key := rebase_rel _ _ _ hu _ _ _ hcd hM i
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply] at key
    simp only [incl_sum_nsmul, Nat.cast_smul_eq_nsmul, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
    exact key

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerEqThetaKO
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.OrientedKer

variable {D : D7}

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem ker_eq_thetaKO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (Wf : WeilFun D ψ) (S T : HSp D) (χS χT : IdC D), S.rank < T.rank → admitted T S χT χS → ∀ om, IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ Φ : ThS ψ T S, (f ≠ 0 → Φ ≠ 0) ∧ ∀ g h, Wf.ker T S χT χS Φ h g = thetaKO om g h f := by
  intro D ψ hψ Wf S T χS χT hr ha om H f hf
  have ha' : admitted S T χS χT := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
  obtain ⟨omO, H', e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ S T χS χT _ ha' hr (Wf.core.weil S T χS χT ha')
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D S T hr.le

  have hf0 : IsThetaFun ψ S T fun y => f (E.symm y) := by
    refine (h7 ψ _).1 ?_
    simp only [AddEquiv.symm_apply_apply]
    exact hf
  let Φ₀ : ThS ψ S T := ⟨fun y => f (E.symm y), mem_ThS.2 hf0⟩
  have hfΦ : f = fun x => Φ₀.1 (toTWsmall S T x) := by
    funext x
    simp only [Φ₀, ← hE, AddEquiv.symm_apply_apply]

  have hΦt : IsThetaFun ψ T S fun x => Φ₀.1 x.transpose :=
    (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ S T Φ₀.1).2.2 hr.ne (mem_ThS.1 Φ₀.2)
  let Φ : ThS ψ T S := ⟨fun x => Φ₀.1 x.transpose, mem_ThS.2 hΦt⟩
  refine ⟨Φ, fun h0 hΦ => h0 ?_, fun g h => ?_⟩
  · funext x
    have := congrFun (congrArg Subtype.val hΦ) (E x).transpose
    simp only [Φ, Φ₀, Matrix.transpose_transpose, AddEquiv.symm_apply_apply, Submodule.coe_zero, Pi.zero_apply] at this
    exact this
  · have hs := Wf.om_swap S T χS χT ha' g h Φ₀ Φ (fun x => congrArg Φ₀.1 (Matrix.transpose_transpose x)) 0
    rw [Matrix.transpose_zero] at hs
    have e1 := congrFun (e (g, h) Φ₀) 0
    rw [toTWsmall_zero, ← hfΦ] at e1
    have e2 := GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T χS χT omO om H' H (g, h) f hf
    unfold WeilFun.ker thetaKO
    rw [hs, ← e2]
    exact e1.symm

end GlobalTheory.Mem.OrientedKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelColumnsGoodRowsLePrincipalAndFiniteDimensio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem levCols_le_triv_and_finite : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  intro hF _ D G' _ _ Pl0 T A Ks _ _ _ R F _ hi _
  refine ⟨GlobalTheory.Mem.Th.EEat_le_triv R _, ?_⟩
  obtain ⟨U, hU, hJ⟩ := GlobalTheory.DefiniteEnd.exists_open_level (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
  exact GlobalTheory.MultFinite.hcFinite hF hi ⟨U, hU, fun k hk hk' => by
    obtain ⟨h1, h2⟩ := hJ k hk
    have hm : k ∈ levS (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) := ⟨hk', h1⟩
    have hc : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) k = 1 := congrArg Units.val h2
    obtain ⟨h3, h4⟩ := GlobalTheory.Mem.Th.principal_le_level (R.βY 0) (R.dat0 (R.levR F true)) (R.dat0 (R.levR F true)).P k hm
    exact ⟨h3, h4.trans hc⟩⟩

end GlobalTheory.Mem.SRe

end
end

