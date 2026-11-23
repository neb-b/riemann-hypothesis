module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumComponentDegreesDivLeLatticeSlope
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CovSum

theorem two_le_rdE (D : D7) : 2 ≤ D.host.rdE := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  have hq : (2 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 2 ≤ D.host.q)
  have hd : (2 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 2 ≤ D.host.d)
  have h4 : (2 : ℝ) ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    rw [Real.le_sqrt' (by norm_num)]; nlinarith
  linarith

theorem log_two_le (D : D7) (K : Type) [Field K] [NumberField K] (φ : D.host.E →+* K) :
    Real.log 2 ≤ Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ) := by
  letI : Algebra D.host.E K := φ.toAlgebra
  refine le_trans ?_ (GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower D.host.E K).2
  have h := Real.log_le_log (by norm_num) (two_le_rdE D)
  have hpos : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  unfold Formalism.BasicNotions.Host.rdE at h
  rw [Real.log_rpow (by simpa using hpos)] at h
  simpa [div_eq_inv_mul] using h

theorem slope_sq_nonneg_of_rk_zero {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (hL : L.FG)
    (h0 : Formalism.HN.rkK L = 0) (hK : Real.log 2 ≤ Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) : 0 ≤ slope_sq N L := by
  letI : StarRing K := starRingOfComm
  unfold slope_sq
  split_ifs with h
  · obtain ⟨-, h2, -⟩ := Formalism.HN.plLat K V _ h.some.2.1.1 h.some.2.1.2 (fun v => (h.some.2.2 v).1) L hL
    rw [h0, mul_zero] at h2
    unfold Formalism.HN.rk at h2
    unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope
    rw [h2]
    simp only [Nat.cast_zero, div_zero, mul_zero]
    linarith
  · exact le_rfl

theorem isComplexData {D : D7} (T : Core D) (hQ : T.Q.Pins) {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) :
    GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict := by
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [h.lev.1.2.1, hQ.2.1.1]
  refine ⟨h.lev.2, fun σ hσ => ⟨h.unf σ hσ, ?_, (GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)).2,
    h.xiAbs σ hσ⟩⟩
  obtain ⟨th, hr, h1, h2⟩ := h.dictU σ hσ
  exact ⟨Y.Kf, th, hr, hM ▸ h.levelK, h1, h2⟩

theorem sum_deg_div_le_mu : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), Y.GoodAt (wtOf (T.Q.Dw j) la 0) → Finite (Comp Y.d.Xo₂ Y.d.c₂) → (∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) → 2 * ((∑ᶠ Z, Y.degC la Z) / ∑ᶠ Z, Y.rkC la Z) ≤ Y.mu (wtOf (T.Q.Dw j) la 0) := by
  intro D T j Y e o hT _ hY _ _ la hG hfin _
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le D _ _ _ _ _ _ Y.U (fun _ => D.sp.W j) Y.dict (isComplexData _ hT.pins Y hY) _ hG
  have h3 : (∑ᶠ Z, Y.rkC la Z) = (rankW Y.U (wtOf (T.Q.Dw j) la 0) : ℝ) := by
    haveI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
    rw [h1, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum]
  rw [h3]
  rcases Nat.eq_zero_or_pos (rankW Y.U (wtOf (T.Q.Dw j) la 0)) with h0 | h0
  · rw [h0, Nat.cast_zero, div_zero, mul_zero]
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    set_option synthInstance.maxHeartbeats 200000 in
      exact slope_sq_nonneg_of_rk_zero _ _ hG.2.1 h0 (log_two_le D _ (τ.codRestrict Y.d.c₂.F (Y.d.c₂.conj τ)))
  · have hp : (0 : ℝ) < rankW Y.U (wtOf (T.Q.Dw j) la 0) := by exact_mod_cast h0
    rw [degW_eq] at h2
    rw [← mul_div_assoc, div_le_iff₀ hp]
    change 2 * (∑ᶠ Z, degOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) ≤
      slopeW_sq Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtOf (T.Q.Dw j) la 0) * _
    linarith

end GlobalTheory.CovSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem surj_restrict_snd {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (Y : Over S)
    (V : Y.left.Opens) : Function.Surjective ((snd A Y).left ∣_ V).appTop.hom := by
  let T : Over S := Over.mk (V.ι ≫ Y.hom)
  let j : T ⟶ Y := Over.homMk V.ι rfl
  let m : (A ⊗ T).left ⟶ (A ⊗ Y).left := (lift (fst A T) (snd A T ≫ j)).left
  have hT : IsPullback (fst A T).left (snd A T).left A.hom (V.ι ≫ Y.hom) := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback _ _
  have m₁ : m ≫ (fst A Y).left = (fst A T).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : m ≫ (snd A Y).left = (snd A T).left ≫ V.ι := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]; rfl
  have H : IsPullback m (snd A T).left (snd A Y).left V.ι :=
    IsPullback.of_right (by rw [m₁]; exact hT) m₂ hY
  let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict (snd A Y).left V) H.flip
  have he : e.hom ≫ (snd A T).left = (snd A Y).left ∣_ V := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hq : Function.Surjective (snd A T).left.appTop.hom := surj_snd GlobalTheory.SemiRigid.globalFns hA T
  have hi : Function.Surjective e.hom.appTop.hom := by
    have : IsIso (e.hom.app ⊤) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
  rw [← he]
  exact surj_comp hi hq

theorem same_of_local : ∀ (S : Scheme.{0}) (A T U : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (Y : Over S) (y : Y ⟶ T) (u : Y ⟶ U),
    (∀ p : Y.left, ∃ (Z : Over S) (z : Z ⟶ Y), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧
      Same A N M (z ≫ y) (z ≫ u)) → Same A N M y u := by
  intro S A T U _ hA N M hN hM Y y u loc
  rw [same_iff hN.isLB hM.isLB]
  rw [← sub_eq_zero]
  obtain ⟨L, hL, hc⟩ := cls_surj (evc hN.isLB (fst A Y) (snd A Y ≫ y) - evc hM.isLB (fst A Y) (snd A Y ≫ u))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ Y).left), Triv (L.pull f) ↔
      CechPic.pull f (evc hN.isLB (fst A Y) (snd A Y ≫ y)) = CechPic.pull f (evc hM.isLB (fst A Y) (snd A Y ≫ u)) := by
    intro X f
    rw [← sub_eq_zero, ← map_sub, ← hc, ← cls_pull hL f (pull_isLB hL f)]
    exact (cls_eq_zero_iff (pull_isLB hL f)).symm
  refine (cls_eq_zero_iff hL).2 (CubeGlue.triv_of_locally_triv hL (snd A Y).left (lift 1 (𝟙 Y)).left ?_
    (surj_restrict_snd hA Y) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key]
    simp only [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [hN.add.evc_one hN.isLB, hM.add.evc_one hM.isLB]
  · intro p
    obtain ⟨Z, z, hz, ⟨q, hq⟩, hs⟩ := loc p
    refine ⟨z.left.opensRange, ⟨q, hq⟩, ?_⟩
    let V := (snd A Y).left ⁻¹ᵁ z.left.opensRange
    let X' : Over S := Over.mk (V.ι ≫ (A ⊗ Y).hom)
    let i : X' ⟶ A ⊗ Y := Over.homMk V.ι rfl
    have hr : Set.range (i ≫ snd A Y).left ⊆ Set.range z.left := by
      rintro _ ⟨w, rfl⟩
      exact w.2
    let t : X' ⟶ Z := Over.homMk (IsOpenImmersion.lift z.left (i ≫ snd A Y).left hr) (by
      rw [← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
    have ht : t ≫ z = i ≫ snd A Y := by
      ext1; exact IsOpenImmersion.lift_fac _ _ _
    rw [same_iff hN.isLB hM.isLB] at hs
    have e := congrArg (CechPic.pull (lift (i ≫ fst A Y) t).left) hs
    simp only [pull_evc, lift_fst, lift_snd_assoc] at e
    rw [← Category.assoc t z y, ← Category.assoc t z u, ht, Category.assoc, Category.assoc] at e
    show Triv (L.pull i.left)
    rw [key, pull_evc, pull_evc]
    exact e

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmLineBundleIsoDescendsSubringFinset
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem symm_lbIso_descends_to_subring_containing_finset : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := by
  intro R _ S A _ _ B _ _ φ φ₂ P P₀ hB hφ sq hP hP₀ hw hsym
  haveI := hB.proper
  have hprop : IsProper (G2 B).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : QuasiCompact (G2 B).hom := inferInstance
  haveI : QuasiSeparated (G2 B).hom := inferInstance
  set sw₀ := (lift (snd B B) (fst B B)).left with hsw₀
  have hpb := isPullback_square hφ.1 φ₂ sq
  have H : LBIso (P₀.pull φ₂) ((P₀.pull sw₀).pull φ₂) :=
    LBIso.trans (pull_isLB hP₀ _) hP (pull_isLB (pull_isLB hP₀ _) _) hw.symm
      (LBIso.trans hP (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _) hsym
        (lbIso_square hP hP₀ hw (lift_square sq sq.2.symm sq.1.symm)))
  obtain ⟨F, hF⟩ := lbIso_descends_to_subring_containing_finset R S (G2 A).left (G2 B).left (G2 A).hom
    (G2 B).hom φ₂ P₀ (P₀.pull sw₀) hpb hP₀ (pull_isLB hP₀ _) H
  refine ⟨F, fun R₁ h hF₁ => ?_⟩
  have hpb₁ := isPullback_square (isGrpPullback (spMap (Subring.inclusion h)) B).1 _
    (isSquare (spMap (Subring.inclusion h)) B)
  have H₁ := hF R₁ h hF₁ _ _ _ hpb₁
  have e := lift_swap (spMap (Subring.inclusion h)) B
  refine LBIso.trans (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB (pull_isLB hP₀ _) _) H₁ ?_
  exact lbIso_square (pull_isLB hP₀ _) hP₀ (lbIso_refl (pull_isLB hP₀ sw₀)) e.symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisAffineOpenRestrictBasicOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

theorem spMap_res_chart {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE hW).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  IsAffineOpen.map_fromSpec U.2 W.2 (homOfLE hW).op

theorem tanBasis_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf w := by
  intro E _ _ _ H X t U W hW f _ n v hv hb
  open MonoidalCategory CartesianMonoidalCategory MonObj in
  open scoped CategoryTheory.Obj in
    let φ := (X.presheaf.map (homOfLE hW).op).hom
    let x := GlobalTheory.LogKS.chart U
    have := t.semi.comm
    have := t.semi.smooth
    have h₁ := isGrpPullback_pullback t.G x
    have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
    have h₃ := h₂.comp h₁
    have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
    have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
      Functor.isCommMonObj_obj
    obtain ⟨a₁, b₁⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t x _ _ h₁
    obtain ⟨-, b₃⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t _ _ _ h₃
    choose u hu using fun i => a₁ (v i) (hv i)
    have hbase : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hb⟩
    have hs : Smooth ((Over.pullback x).obj t.G).hom :=
      inferInstanceAs (Smooth (pullback.snd t.G.hom x))
    obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ _ _ _ h₂ hs n u hbase
    have e : Chart.dualMapR φ = dualMap φ := by
      ext a <;> rfl
    have key := (b₃ n u').1 hb'
    have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
        spMap (dualMap φ) ≫ v i := fun i => by
      rw [← Category.assoc, hu', e, Category.assoc, hu]
    rw [← funext e']
    rw [← spMap_res_chart U W hW]
    exact key.2

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisFrameMapImports
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem one_left_π {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) (T : Over S') :
    (1 : T ⟶ G').left ≫ π = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
    show _ = T.hom ≫ f
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
  have h := hg.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h
  have e : x₀ * x₀ = x₀ := Over.OverMorphism.ext h
  have e' : x₀ = 1 := by
    have := congrArg (· * x₀⁻¹) e
    simpa using this
  exact congrArg Over.Hom.left e'

theorem exists_unit {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) :
    ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = 1 := by
  obtain ⟨β₀, h1, h2⟩ := P'.fin.one O (lo P' x0 hu)
  have hβ₀ : β₀.comp P'.str = (algebraMap O O).comp x0 := by
    rw [GlobalTheory.HTMap.FP.str, ← RingHom.comp_assoc, h1, lo_comp]
    try rfl
  have hid : (specO O O).hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap O O)) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  let c : S ⟶ specO O O := Over.homMk S.hom (by rw [hid, Category.comp_id]; try rfl)
  refine ⟨c ≫ ptOf P' x0 hu β₀ hβ₀, ?_⟩
  have hz : ptOf P' x0 hu β₀ hβ₀ ≫ aH P' x0 hu hg.1 = 1 := by
    refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
    · rw [ptOf_aH_π, h2, one_left_π hg]
      refine (GlobalTheory.HTMap.one_of (G := t.G) (g := 𝟙 _) ?_).trans (Category.id_comp _)
      rw [Category.id_comp, hid, Category.id_comp, GlobalTheory.HTMap.spc_assoc, lo_comp]
    · rw [Over.w, Over.w]
  rw [Category.assoc, hz, MonObj.comp_one]

end GlobalTheory.FinPartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBaseChange

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp_spMap' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_algebraMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (Formalism.L2.Pj.dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul' {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (Formalism.L2.Pj.dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (Formalism.L2.Pj.dualMap ψ) := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem list_prod_comp' {X0 : Scheme.{0}} {G : Over X0} [MonObj G] {T T' : Over X0} (f : T' ⟶ T)
    (L : List (T ⟶ G)) : (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

theorem tan_comb_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ X) (x' : Sp S' ⟶ X), spMap φ ≫ x = x' → (∀ v : Sp (DualNumber S) ⟶ t.G.left, IsTanAtG t x v → IsTanAtG t x' (spMap (dualMap φ) ≫ v)) ∧ ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left), IsCombAtG t x v cf w → IsCombAtG t x' (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  intro E _ _ _ H X t S S' _ _ φ x x' hx
  subst hx
  refine ⟨fun v hv => ?_, fun m v cf w h => ?_⟩
  · obtain ⟨h1, h2⟩ := hv
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_spMap', dualMap_comp_algebraMap, ← spMap_comp_spMap',
        Category.assoc]
    · rw [← Category.assoc, spMap_comp_spMap', fstHom_comp_dualMap, ← spMap_comp_spMap', Category.assoc, h2]
      have e : (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ t.G) = 1 := by
        simp [Hom.one_def]
      rw [← e, Over.comp_left]
      rfl
  · obtain ⟨u, hu, hp⟩ := h
    let q : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (Formalism.L2.Pj.dualMap φ)) (by
      show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
        spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
      rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap', spMap_comp_spMap', dualMap_comp_algebraMap])
    refine ⟨fun i => q ≫ u i, fun i => ?_, ?_⟩
    · show spMap (Formalism.L2.Pj.dualMap φ) ≫ (u i).left = _
      rw [hu i, ← Category.assoc, spMap_comp_spMap', dualMap_comp_epsMul', ← spMap_comp_spMap', Category.assoc]
    · have e : List.ofFn (fun i => q ≫ u i) = (List.ofFn u).map (q ≫ ·) := by
        rw [List.map_ofFn]
        rfl
      rw [e, list_prod_comp', Over.comp_left, hp]
      rfl

end GlobalTheory.TanBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftBC

theorem isCombAtG_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    {a : Fin m → S} {w₁ w₂ : Sp (DualNumber S) ⟶ t.G.left} (h₁ : IsCombAtG t x v a w₁) (h₂ : IsCombAtG t x v a w₂) :
    w₁ = w₂ := by
  obtain ⟨u₁, hu₁, hw₁⟩ := h₁
  obtain ⟨u₂, hu₂, hw₂⟩ := h₂
  have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
  rw [← hw₁, ← hw₂, hu]

end GlobalTheory.FlatModel.LiftBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtFiniteSetStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_trivial_at_finite_set : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g - 1) = 0) →
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ₂ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ∉ S → φ₂ w = φ w) ∧ om' (g, h) (pure f φ) = pure f φ₂ := by
  first | exact @GlobalTheory.PureStabFin.pure_stab_fin | exact GlobalTheory.PureStabFin.pure_stab_fin | (intros; apply GlobalTheory.PureStabFin.pure_stab_fin <;> assumption)
end

