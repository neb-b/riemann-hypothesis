module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2236
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerWedgeFrameChange
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

theorem GlobalTheory.LogKSDiv.topPair_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) → (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) → ∃ u : (X₀ TF.Y Z).functionField, (u = 1 ∨ u = -1) ∧ ∀ η : RatForms (s₀ TF.Y Z) Dw.dim, GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D η = u * ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D' η := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hF _ _ w w' D D' A d hw hw' hA hd
  obtain ⟨n, n', e, e', ε, ε', L, hM, hD⟩ := GlobalTheory.T.genericPoint_logKodairaSpencer_frame_change E H Dw l Xo c TF Z hpq hF w w' D D' A hw hw' hA
  obtain ⟨u, hu, hdet⟩ := GlobalTheory.T.det_frameChange_balancedTensors_cmType E H Dw _ A n n' e e' ε ε' L hM
  refine ⟨u, hu, fun η => ?_⟩
  rw [GlobalTheory.T.topFormDerivationDetPairing_change_matrix _ D D' L hD η, hdet]
  congr 2
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  split_ifs <;> simp [zpow_natCast, hd]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixWeightedPairBundleRigidifiedAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.CechPic

noncomputable section
namespace GlobalTheory.PowFormProps

def preQ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left) (hQ : QHyp A Q) :
    SiegPre 0 1 (0 : ℤ) (specZIsTerminal.from S) where
  A := A
  ab := hQ.1
  P := Q
  isLB := hQ.2.1
  rig₁ := hQ.2.2.1
  rig₂ := hQ.2.2.2.1
  symm := hQ.2.2.2.2.1
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ hz => by
    rw [map_zero] at hz
    exact absurd hz z.ne_zero

theorem formLB_props : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q →
    ∀ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
      IsAbelianScheme (Out.powObj A r) ∧ (formLB A Q (Out.powPr A (n := r)) W).IsLB ∧
      Out.Rigidified (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) ∧
      Out.RelAmple (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) := by
  intro S A _ _ Q hQ r W hW
  let c := preQ A Q hQ
  have hA' : Out.RelAmple c.A c.diag := hQ.2.2.2.2.2
  let pr : Fin r → (Out.powObj A r ⟶ A) := Out.powPr A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin r → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A r, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit A r).lift (Fan.mk T y), fun u => (Out.powIsLimit A r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (formLB A Q pr W).IsLB := LB.isLB_linComb hQ.2.1 _ _
  have hLW : cls (formLB A Q pr W) hL = PrincipalIntegral.quad (cls c.P c.isLB) W pr := cls_linComb hQ.2.1 _ _ _
  have hadd := PrincipalIntegral.pair_mul c SemiRigid.globalFns hA'
  exact ⟨GlobalTheory.isAbelianScheme_powObj_of_isAbelianScheme A hQ.1 r, hL,
    PrincipalIntegral.rigidified hadd hmon hL hLW,
    PosDefAmple.relAmple_linComb_of_posDef SemiRigid.globalFns 0 1 r ℤ 0 S _ c (Out.powObj A r) pr W hmon huniv hA' hW⟩

end GlobalTheory.PowFormProps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEmbHOfClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem exists_trait_point {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (M : Modif R) (x : M.S)
    (hx : M.π x = closedPoint R) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
      GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x := by
  have : IsNoetherianRing R := hR.1.1
  have : CharZero R := hR.2
  have := M.proper
  have := M.integral
  have := M.dominant
  have : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (M.S.fromSpecStalk x ≫ M.π)
  have hψp : ∀ q : Spec (M.S.presheaf.stalk x), Spec.map ψ q = M.π (M.S.fromSpecStalk x q) := fun q => by
    rw [hψ, Scheme.Hom.comp_apply]
  have hloc : IsLocalHom ψ.hom := by
    rw [isLocalHom_iff_comap_closedPoint]
    have := hψp (closedPoint _)
    rw [Scheme.fromSpecStalk_closedPoint, hx] at this
    exact this

  let t₀ : Sp (FractionRing R) := closedPoint (FractionRing R)
  have hsp : M.gp t₀ ⤳ x := by
    rw [specializes_iff_mem_closure]
    have h1 : Set.range M.gp ⊆ {M.gp t₀} := by
      rintro _ ⟨t, rfl⟩
      rw [Subsingleton.elim t t₀]; rfl
    exact closure_mono h1 ((IsDominant.denseRange (f := M.gp)).closure_eq ▸ Set.mem_univ x)
  have hr : M.gp t₀ ∈ Set.range (M.S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hsp
  obtain ⟨q, hq⟩ := hr
  have e1 : Spec.map ψ q = jK R t₀ := by
    rw [hψp, hq, ← Scheme.Hom.comp_apply, M.gp_π]
  have h2 : Ideal.comap ψ.hom q.asIdeal = ⊥ := by
    have := congrArg (fun p : Sp R => (p : PrimeSpectrum R).asIdeal) e1
    change Ideal.comap ψ.hom q.asIdeal = Ideal.comap (algebraMap R (FractionRing R)) t₀.asIdeal at this
    rw [this, @Ideal.eq_bot_of_prime _ _ t₀.asIdeal t₀.isPrime]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
  have hinj : Function.Injective ψ.hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap ψ.hom q.asIdeal := by
      rw [Ideal.mem_comap, ha]; exact q.asIdeal.zero_mem
    rw [h2] at this
    exact this
  have : CharZero (M.S.presheaf.stalk x) := charZero_of_injective_ringHom hinj
  have key : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (χ : M.S.presheaf.stalk x →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective χ ∧ IsLocalHom χ := by
    by_cases h : IsField (M.S.presheaf.stalk x)
    · letI := h.toField
      refine ⟨PowerSeries (M.S.presheaf.stalk x), inferInstance, inferInstance, inferInstance, PowerSeries.C,
        ⟨inferInstance, ?_, ?_⟩, PowerSeries.C_injective, inferInstance⟩
      · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
      · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := M.S.presheaf.stalk x)) (RingHom.injective _)
    · obtain ⟨O, _, _, _, _, χ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating _ h
      have : CharZero O := charZero_of_injective_ringHom h1
      exact ⟨O, inferInstance, inferInstance, inferInstance, χ, ⟨inferInstance, inferInstance, inferInstance⟩, h1, h2⟩
  obtain ⟨W, _, _, _, χ, hW, hχ, hχl⟩ := key
  refine ⟨W, inferInstance, inferInstance, inferInstance, χ.comp ψ.hom, Spec.map (CommRingCat.ofHom χ) ≫ M.S.fromSpecStalk x,
    hW, hχ.comp hinj, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]; rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x) (IsLocalRing.comap_closedPoint χ)) Scheme.fromSpecStalk_closedPoint)

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem mem_embH_of_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    ∀ g : G.left, M.π (G.hom g) = closedPoint R → g ∈ GlobalTheory.Mum.SecEmb.embH s := by
  intro R _ _ _ hR M G _ _ B L _ _ N s θ Y _ _ j _ _ O hT g hg
  obtain ⟨W, _, _, _, φ, ξ, hW, hφ, hl, hξ, hξx⟩ := exists_trait_point hR M (G.hom g) hg
  obtain ⟨W', _, _, _, io, G', _, β, κ, e, hW', hio, hfin, hcart, -, -, hpts⟩ := hT W hW φ ξ hφ hl hξ
  have hiol : IsLocalHom io := by
    letI := io.toAlgebra
    have : Module.Finite W W' := hfin
    have : FaithfulSMul W W' := (faithfulSMul_iff_algebraMap_injective W W').2 hio
    exact (inferInstance : IsLocalHom (algebraMap W W'))
  have hc : (spMap io ≫ ξ) (closedPoint W') = G.hom g :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg ξ (IsLocalRing.comap_closedPoint io)).trans hξx)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap io ≫ ξ) g
    (closedPoint W') hc.symm
  have hg1 : β (hcart.1.isoPullback.inv z) = g := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_fst, hz1]
  have hg2 : G'.hom (hcart.1.isoPullback.inv z) = closedPoint W' := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_snd, hz2]
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := spMap (residue W'))
    (hcart.1.isoPullback.inv z) (closedPoint (ResidueField W'))
    (hg2.trans (IsLocalRing.comap_closedPoint (residue W')).symm)
  let F := ((Over.pullback (spMap (residue W'))).obj G').left
  let q' : F := q
  obtain ⟨⟨hs, -⟩, -⟩ := hpts (F.residueField q') (F.fromSpecResidueField q')
    (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W')))
    (F.fromSpecResidueField q' ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ)) rfl rfl
  have hm : closedPoint (F.residueField q') ∈
      ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)) := by
    rw [hs]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  rw [GlobalTheory.nonzeroLocus_secPull] at hi
  have hpt : ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)
      (closedPoint (F.residueField q')) = g := by
    have h1 : (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) (closedPoint (F.residueField q')) =
        hcart.1.isoPullback.inv z :=
      (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (pullback.fst G'.hom (spMap (residue W'))) (Scheme.fromSpecResidueField_apply q' _)).trans hq1)
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg β h1).trans hg1)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  rw [← hpt]
  exact hi

end GlobalTheory.Mum.SecEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelIdealOfAppEqZeroField
section
set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_comp_of_app_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G) (hfg : f ≫ g = (p : ℤ_[p]) • 𝟙 G)
    (a : G.A 1) (ha : g.app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp (f.app 1)) := by
  set K := kerIdeal ((G.mulP 1).comp (f.app 1)) with hK
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff ((G.mulP 1).comp (f.app 1)) x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp (f.app 2 : H.A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal (R := R) (A := H.A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff _ y).2 fun z => by
      have e : f.app 2 (mulBy R _ p z) = G.mulP 1 (f.app 1 (H.res 1 z)) := by
        rw [map_mulBy, ← PDivGroup.res_app, mulP_res]
      have := hx (H.res 1 z)
      rw [CoalgHomClass.counit_comp_apply] at this
      exact (congrArg x e).trans this
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app] at ha
  have hb : g.app 2 b ∈ torsionIdeal (R := R) (A := H.A 2) p := by
    have : g.app 2 b ∈ torsionIdeal (R := R) (A := H.A 2) (p ^ 1) := by
      rw [← H.ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x (f.app 2 (g.app 2 b)) = 0 := hy hb
  have e2 : f.app 2 (g.app 2 b) = mulBy R _ p b := by
    have := congrArg (fun φ : G ⟶ G => φ.app 2 b) hfg
    simp only [comp_app, natCast_smul_id_app] at this
    exact this
  rw [e2] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup


open GlobalTheory.PDivGroup in
theorem GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G →
    g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  intro p _ K _ G H f g hfg _ a ha
  have hmulP : Function.Injective (G.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := K) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := G.dual_mulP_surjective 1 φ
    change ψ.ofConv (G.mulP 1 a) = ψ.ofConv (G.mulP 1 b)
    rw [e]
  have h1 := mulP_mem_kerIdeal_comp_of_app_eq_zero p K G H f g hfg a ha
  rw [kerIdeal_comp] at h1
  rw [← GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective K _ _ (G.mulP 1) hmulP (kerIdeal (f.app 1))]
  exact h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPassScaled
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.RoadE

open GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def passScaled (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N : ℕ) : Lat (FR E) where
  carrier := {x | ∃ y' ∈ lattice c y, (N : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩ => ⟨a + b, (latticeSub c y).add_mem ha hb, by
    have : ptE t (x + x') = ptE t x + ptE t x' := by simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring
    rw [this, ← hxa, ← hxb]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨b, hb, hxb⟩ => ⟨algebraMap (OF E) E a * b, mul_mem_lattice (algebraMap_mem_orderC c a) hb, by
    rw [ptE_smul, ← hxb]; ring⟩

end GlobalTheory.RoadE

namespace GlobalTheory.RoadE
open GlobalTheory.CMVal

theorem passl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (y : (Af E)ˣ) (θ : E) (D M₀ : ℕ), IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → OneOver l y → 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → ¬ l ∣ M₀ → ∃ (M M' : ℕ) (L : Lat (FR E)), ¬ l ∣ M ∧ ¬ l ∣ M' ∧ M₀ ∣ M' ∧ HasLevel (M' * l ^ (padicValNat l D + a0 𝔣 l)) L ∧ (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y' ∈ lattice (condQ 𝔣 Q) y, ((M * D : ℕ) : E) * y' = (x 0 : E) * θ + (x 1 : E)) ∧ (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb (FR E)), Sz l lam (-(padicValNat l D : ℝ) / 2) ((i (v j) : ℝ) : ℂ)) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M' * l ^ (padicValNat l D + a0 𝔣 l) : ℕ) : ℂ) := by
  intro E _ _ _ l _ lam 𝔣 Q y θ D M₀ hf hQ hy hD hθ hθD hM₀
  have hl : l.Prime := Fact.out
  set c := condQ 𝔣 Q with hc
  obtain ⟨M, hMl, hMint⟩ := _root_.GlobalTheory.HilbFam.LatticeUp.exists_mul_integral E l c y hl hy
  obtain ⟨M₁, hM₁l, hM₁c⟩ := _root_.GlobalTheory.HilbFam.CondNumber.exists_mem_condQ E l 𝔣 Q hl hf hQ
  have hM₁0 : M₁ ≠ 0 := by rintro rfl; exact hM₁l (dvd_zero l)
  have hM0 : M ≠ 0 := by rintro rfl; exact hMl (dvd_zero l)
  have hR : 0 < M₁ * l ^ a0 𝔣 l := Nat.pos_of_ne_zero (mul_ne_zero hM₁0 (pow_ne_zero _ hl.ne_zero))
  obtain ⟨M₂, hM₂l, hM₂⟩ := _root_.GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice E l c y (M₁ * l ^ a0 𝔣 l) hl hy hR hM₁c
  obtain ⟨D', hD'⟩ := (fun {p n : ℕ} => _root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)) (p := l) (n := D)
  have hD'l : ¬ l ∣ D' := by
    rintro ⟨e, he⟩
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    refine ⟨e, ?_⟩
    calc D = l ^ padicValNat l D * D' := hD'
      _ = l ^ (multiplicity l D + 1) * e := by rw [he, ← Nat.padicValNat_def, pow_succ]; ring
  have hnat : ∀ n : ℕ, IsIntegral ℤ (n : E) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (n : ℤ)))
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hDF : (D : FR E) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ x ∈ passScaled θ c y (M * D), ∀ j,
      IsIntegral ℤ ((D : FR E) * ((D : FR E)⁻¹ * x j) ^ 2) ∧ IsIntegral ℤ (x j) := by
    rintro x ⟨y', hy', hxy⟩ j
    have hpt : (((D : FR E)⁻¹ * x 0 : FR E) : E) * θ + (((D : FR E)⁻¹ * x 1 : FR E) : E) = (M : E) * y' := by
      simp only [ptE] at hxy
      push_cast at hxy ⊢
      have h' : (M : E) * y' = (D : E)⁻¹ * (((x 0 : FR E) : E) * θ + ((x 1 : FR E) : E)) := by
        rw [← hxy]; field_simp
      rw [h']; ring
    have h := GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral E θ D (fun j => (D : FR E)⁻¹ * x j) hD hθ hθD (by rw [hpt]; exact hMint y' hy') j
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    simp only [mul_inv_cancel_left₀ hDF] at h2
    exact h2
  refine ⟨M, M₀ * M * D' * M₂ * M₁, passScaled θ c y (M * D), hMl, ?_, ⟨M * D' * M₂ * M₁, by ring⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    exacts [hM₀ h, hMl h, hD'l h, hM₂l h, hM₁l h]
  · refine ⟨fun w hw => ?_, fun x hx => ?_⟩
    · have hwj : ∀ j, IsIntegral ℤ ((w j : FR E) : E) := by
        intro j
        have hwj1 : w j ∈ (1 : Submodule (𝓞 (FR E)) (FR E)) := Submodule.mem_pi.1 hw j (Set.mem_univ j)
        obtain ⟨a, ha⟩ := Submodule.mem_one.1 hwj1
        rw [← ha]
        exact (RingOfIntegers.isIntegral_coe a).map (RingHom.toIntAlgHom (maximalRealSubfield E).subtype)
      have hP : IsIntegral ℤ ((M₀ : E) * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) :=
        (hnat M₀).mul (((hwj 0).mul hθ).add (hwj 1))
      refine ⟨_, hM₂ _ hP, ?_⟩
      have e : (D : E) = (l : E) ^ padicValNat l D * D' := by exact_mod_cast hD'
      simp only [ptE, Pi.smul_apply, Algebra.smul_def, Subfield.coe_mul, map_natCast]
      push_cast
      linear_combination ((M : E) * M₂ * M₁ * (l : E) ^ a0 𝔣 l * M₀ * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) * e
    · intro j _
      change x j ∈ (1 : Submodule (𝓞 (FR E)) (FR E))
      rw [Submodule.mem_one]
      exact ⟨⟨x j, (key x hx j).2⟩, rfl⟩
  · intro x; exact Iff.rfl
  · intro w hw j i
    have h1 := (key w hw j).1
    set f : FR E →ₐ[ℤ] ℂ := RingHom.toIntAlgHom (Complex.ofRealHom.comp i) with hf
    have h2 : IsIntegral ℤ ((D : ℂ) * (f ((D : FR E)⁻¹ * w j)) ^ 2) := by
      have := h1.map f
      simpa [map_mul, map_pow, map_natCast] using this
    have h3 := (_root_.GlobalTheory.SizeSqIntegral.main l lam D 0 (f ((D : FR E)⁻¹ * w j)) hD h2).1
    have h4 : (D : ℂ) * f ((D : FR E)⁻¹ * w j) = ((i (w j) : ℝ) : ℂ) := by
      rw [← map_natCast f D, ← map_mul, mul_inv_cancel_left₀ hDF]
      rfl
    rwa [h4] at h3
  · have h := (_root_.GlobalTheory.SizeSqIntegral.main l lam D (M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l) 0 hD (by simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ)))).2
    rwa [show M₀ * M * D' * M₂ * M₁ * l ^ (padicValNat l D + a0 𝔣 l) =
      M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l * l ^ padicValNat l D by ring]

end GlobalTheory.RoadE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStalkOfClassicalValuesNormLeOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem mem_O_of_norm_val_le_one : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ f ∈ M.ringOn (U₀ : Set M.Z), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ x y → ‖M.val (gPt p ≫ y) f‖ ≤ 1) → f ∈ M.O x := by
  intro o' Ω _ _ _ _ M hn U₀ hU x hx f hf hb
  obtain ⟨h1, h2⟩ := flat_and_lft_toInt M
  letI : Flat (M.s ≫ spMap (algebraMap ℤ o')) := h1
  letI : LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o')) := h2
  obtain ⟨φ, rfl⟩ := (RatModel.mem_ringOn_iff_exists hU).1 hf
  obtain ⟨W, ψ, hxW, h⟩ := GlobalTheory.regular_of_bounded_at_padicAlgCl_points.1 M.Z (M.s ≫ spMap (algebraMap ℤ o')) x hx
    (hn x).2 U₀ φ hU fun p _ y e1 e2 => (RatModel.val_valF e2 φ) ▸ hb p y ⟨e1, e2⟩
  have hWU := M.nonempty_inf ⟨x, hxW⟩ hU
  have e : valF M.pt W ψ = valF M.pt U₀ φ := (M.valF_resG inf_le_left hWU ψ).symm.trans
    ((congrArg _ h).trans (M.valF_resG inf_le_right hWU φ))
  exact e ▸ RatModel.valF_mem_O hxW ψ

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceSectionPullbackComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.toProj_secPull_secPull (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X)
    (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R)
    (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤)
    (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ =
      GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ := by
  refine GlobalTheory.ProjSpace.toProj_eq_of_locally hs₂ hs₁ fun z => ?_
  obtain ⟨k, hk⟩ : ∃ k : PUnit → L.ι, z ∈ (L.pull (g ≫ h)).U k :=
    GlobalTheory.ProjSpace.exists_chart_of_iSup_nonzeroLocus hs₂ z
  let l : ((L.pull h).pull g).ι := fun _ _ => k PUnit.unit
  have hle : (L.pull (g ≫ h)).U k ≤ ((L.pull h).pull g).U l := by
    rw [GlobalTheory.Cartier.pull_U L (g ≫ h) k, GlobalTheory.Cartier.pull_U (L.pull h) g l,
      GlobalTheory.Cartier.pull_U L h (fun _ => k PUnit.unit)]
    exact fun _ hy => hy
  refine ⟨_, hk, k, le_rfl, l, hle, 1, fun j => ?_⟩
  rw [_root_.one_mul]
  unfold GlobalTheory.secPull
  rw [GlobalTheory.chartSec_f, GlobalTheory.chartSec_f, GlobalTheory.chartSec_f (GlobalTheory.chartPullPull L (g ≫ h)) (s j) k]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_map]
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map]
  rfl
end

