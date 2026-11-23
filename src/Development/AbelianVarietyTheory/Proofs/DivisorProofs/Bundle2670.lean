module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftDegreeOneComparisonRelation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.CrysCmp

theorem exists_compatibleFormsCocycle_deRhamClass {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c : FirstDeRham s) :
    ∃ (f₀ : Z1 (O (dp0 R) s)) (k₀ : (KK (dp0 R) s).Z1), k₀.1.1 = f₀.1 ∧ H1.mk _ f₀ = c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hb := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R ⊥ (dp0 R) X s X (𝟙 X)).1.1.2
  have hfe : ((f.1, fun _ ↦ PUnit.unit) : (Cx.single (KK (dp0 R) s).M0).T1) ∈ (Cx.single (KK (dp0 R) s).M0).Z1 := by
    refine AddMonoidHom.mem_ker.2 (Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))
    funext T T' T'' φ ψ
    change mp (O (dp0 R) s) ψ (f.1 _ _ φ) - f.1 _ _ (φ ≫ ψ) + f.1 _ _ ψ = 0
    rw [f.2 φ ψ]; abel
  obtain ⟨q, hq⟩ := hb (QuotientAddGroup.mk ⟨_, hfe⟩)
  obtain ⟨k₀, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hq' := QuotientAddGroup.eq.1 ((QuotientAddGroup.map_mk _ _ _ _ k₀).symm.trans hq)
  rw [AddSubgroup.mem_addSubgroupOf] at hq'
  obtain ⟨g, hg⟩ := hq'
  have hk := AddMonoidHom.mem_ker.1 k₀.2
  let f₀ : Z1 (O (dp0 R) s) := ⟨k₀.1.1, fun T T' T'' φ ψ ↦ by
    have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hk) T) T') T'') φ) ψ
    change mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) - k₀.1.1 _ _ (φ ≫ ψ) + k₀.1.1 _ _ ψ = 0 at this
    change k₀.1.1 _ _ (φ ≫ ψ) = mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) + k₀.1.1 _ _ ψ
    linear_combination (norm := abel1) -this⟩
  refine ⟨f₀, k₀, rfl, ?_⟩
  rw [H1.mk_eq_mk]
  refine ⟨-g, ?_⟩
  funext T T' φ
  have := congrFun (congrFun (congrFun (congrArg Prod.fst hg) T) T') φ
  change g T' - mp (O (dp0 R) s) φ (g T) = -(k₀.1.1 T T' φ) + f.1 T T' φ at this
  change -g T' - mp (O (dp0 R) s) φ (-g T) = k₀.1.1 T T' φ - f.1 T T' φ
  rw [map_neg]
  linear_combination (norm := abel1) -this

section Theta

variable {D : Data} (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i)

def thAlg (U : AffOp D.X) : Sec D.s U.unop.1 →ₐ[D.R] (m.obj (Λ.L.obj U)).B :=
  { (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B) with commutes' := fun r ↦ (Λ.e U).commutes r }

def theta (U : AffOp D.X) :
    Thick.triv (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop) ⟶ m.obj (Λ.L.obj U) :=
  Thick.trivHom (thAlg Λ m U) (Λ.pt U)

end Theta

theorem key4 {G : Type} [AddCommGroup G] (A B C E : G) (h : A + B = C + E) : E - A = B - C := by
  rw [sub_eq_sub_iff_add_eq_add, add_comm E C, ← h, add_comm]

theorem lift_rel1_pull1_cmp1 : ∀ (D : Data) (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i) (c : FirstDeRham D.s), Λ.Rel1 (m.pull1 c) (cmp1 D.s c) := by
  intro D Λ m c
  obtain ⟨f₀, k₀, hk, rfl⟩ := exists_compatibleFormsCocycle_deRhamClass D.s c
  let k := (morMap m).z1 k₀
  let k' := ((KK D.κ D.t).resMap Λ.L).p1 k.1
  have hk' : k' ∈ ((KK D.κ D.t).res Λ.L).Z1 := (((KK D.κ D.t).resMap Λ.L).z1 k).2
  obtain ⟨w, hw, -⟩ := ((_root_.GlobalTheory.PDForm.lift_res_bij).1 D Λ).1 k'
  have hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((((_root_.GlobalTheory.PDForm.lift_res_bij).1 D Λ).2.2 k' w hw).1.1 hk')
  refine ⟨k, m.coef.pullbackOneCocycle f₀, ⟨w, hwZ⟩, rfl, ?_, ?_, hw⟩

  · rw [comparison_mk, Hyp1.mk_eq_mk]
    refine ⟨fun U ↦ (Λ.e U).symm (ev f₀ (theta Λ m U)), Tot1.ext (fun U V a ↦ ?_) (fun U ↦ ?_)⟩
    · change (Λ.e V).symm (ev f₀ (theta Λ m V)) - Sec.res D.s (leOfHom a.unop) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.1 U V a - (cmpZZ D.s f₀).1.1 U V a
      apply (Λ.e V).injective
      have h1 : Λ.e V (w.1 U V a) = ev f₀ (m.functor.map (Λ.L.map a)) := by
        refine (hw.1 U V a).symm.trans ?_
        change k₀.1.1 _ _ _ = _
        rw [hk]; rfl
      have h2 := Λ.nat a ((Λ.e U).symm (ev f₀ (theta Λ m U)))
      erw [AlgEquiv.apply_symm_apply] at h2
      have sq := ev_sq f₀ (theta Λ m U) (m.functor.map (Λ.L.map a))
          (Thick.trivHom (hx := affPt_w D.s U.unop) (T := Thick.triv _ _ (affPt_w D.s V.unop))
            (Sec.res D.s (leOfHom a.unop)) (affPt_res D.s (leOfHom a.unop))) (theta Λ m V)
          (by intro c; exact (Λ.nat a c).symm)
      rw [map_sub, map_sub, h1, cmpZZ_f]
      erw [AlgEquiv.apply_symm_apply]
      change _ - Λ.e V (mp (OAff D.s) a _) = _
      rw [h2]
      exact key4 _ _ _ _ sq
    · change KaehlerDifferential.D D.R (Sec D.s U.unop.1) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.2 U - connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)
      have hrel : rel D.R (Λ.L.obj U).δ = ⊥ :=
        (_root_.GlobalTheory.PDForm.rel_two_sided_and_bot).2 D.R (Λ.L.obj U).B (Λ.L.obj U).J (Λ.L.obj U).δ D.I D.κ (Λ.L.obj U).dp (Λ.gen U).le
      have inj : ∀ x y : Ω[(Λ.L.obj U).B⁄D.R],
          (Submodule.Quotient.mk x : K1 D.R (Λ.L.obj U).δ) = Submodule.Quotient.mk y → x = y := by
        intro x y h
        rw [Submodule.Quotient.eq] at h
        have h' : ι1 (x - y) ∈ rel D.R (Λ.L.obj U).δ := h
        rw [hrel, Ideal.mem_bot, map_sub, sub_eq_zero] at h'
        exact (ExteriorAlgebra.ι_inj _ _ _).1 h'
      have hk0 := AddMonoidHom.mem_ker.1 k₀.2
      have hcoc := congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hk0) _) _) (theta Λ m U)
      have hc := _root_.GlobalTheory.ConnCocycle.form_eq_connForm D.R D.X D.s k₀ f₀ hk (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop)
      have e1 : k₀.1.2 (m.obj (Λ.L.obj U)) = km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) +
          kd0 D.R (m.obj (Λ.L.obj U)).δ (ev f₀ (theta Λ m U)) := by
        have : k₀.1.2 (m.obj (Λ.L.obj U)) - km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) -
            kd0 D.R (m.obj (Λ.L.obj U)).δ (k₀.1.1 _ _ (theta Λ m U)) = 0 := hcoc
        rw [hk] at this
        exact sub_eq_zero.1 ((sub_sub _ _ _).symm.trans this)
      rw [hc, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add] at e1
      have e2 := hw.2 U
      change km1 (morSemi m (Λ.L.obj U)) (morDP m (Λ.L.obj U)) (k₀.1.2 (m.obj (Λ.L.obj U))) = _ at e2
      rw [e1] at e2
      erw [divPowerCompatOneFormMap_mk] at e2
      have e3 := inj _ _ e2
      have e3' : (Λ.semi U).m1 (w.2 U) = (Λ.semi U).m1 (connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)) +
          KaehlerDifferential.D D.R (Λ.L.obj U).B (ev f₀ (theta Λ m U)) := by
        rw [← e3, map_add (f := _)]
        congr 1
        · exact SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _
        · exact SemiHom.m1_D _ _
      have semiInv : SemiHom (RingHom.id D.R) ((Λ.e U).symm : (Λ.L.obj U).B →+* Sec D.s U.unop.1) :=
        fun r b ↦ map_smul (Λ.e U).symm r b
      have linv : ∀ ω, semiInv.m1 ((Λ.semi U).m1 ω) = ω := fun ω ↦
        (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) semiInv (SemiHom.of_algHom (AlgHom.id D.R (Sec D.s U.unop.1)))
          (fun b ↦ (Λ.e U).symm_apply_apply b) ω).trans (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω)
      have e5 := congrArg semiInv.m1 e3'
      rw [map_add (f := _), linv, linv] at e5
      rw [e5, add_sub_cancel_left]
      exact (SemiHom.m1_D semiInv _).symm
  · funext T T' φ
    change k₀.1.1 _ _ (m.functor.map φ) = f₀.1 _ _ (m.functor.map φ)
    rw [hk]

end GlobalTheory.PDForm.CrysCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem surjective_of_isFinite_of_dim_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    A.dim = B.dim → IsFinite f.hom.left → Surjective f.hom.left := by
  intro K _ A B f hdim hfin
  obtain ⟨hBi, -, -⟩ := _root_.GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K B
  set g := f.hom.left
  have eA : topologicalKrullDim A.X.left = Order.krullDim A.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := A.X.left))
  have eB : topologicalKrullDim B.X.left = Order.krullDim B.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := B.X.left))
  have dA := _root_.GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A
  have dB := _root_.GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K B
  rw [eA] at dA
  rw [eB] at dB

  have hm : StrictMono (g : A.X.left → B.X.left) := by
    intro a b hab
    have h1 : g a ≤ g b := (show b ⤳ a from hab.1).map g.continuous
    refine lt_of_le_not_ge h1 fun h2 ↦ hab.2 ?_
    have e : g b = g a := ((show g b ⤳ g a from h1).antisymm h2).eq
    have hd := (g.isDiscrete_preimage_singleton (g a)).to_subtype
    have : (⟨b, e⟩ : g ⁻¹' {g a}) ⤳ ⟨a, rfl⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp hab.1
    have hba : b = a := congrArg Subtype.val this.eq
    rw [hba]
  refine ⟨?_⟩
  by_contra hns
  have hη : genericPoint B.X.left ∉ Set.range g := by
    intro hη
    apply hns
    have hc : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
    intro y
    exact (genericPoint_specializes y).mem_closed hc hη
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 dA.ge
  have hlast : (l.map g hm).last < genericPoint B.X.left := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun h2 ↦ hη ?_
    have e := ((genericPoint_specializes ((l.map g hm).last)).antisymm h2).eq
    rw [e, LTSeries.last_map]
    exact ⟨_, rfl⟩
  have := Order.LTSeries.length_le_krullDim ((l.map g hm).snoc _ hlast)
  rw [dB, RelSeries.snoc_length, LTSeries.map_length, hl, ← hdim] at this
  norm_cast at this
  omega

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveTwistedKernelAdditiveLineBundleFamily
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistKerSurj

theorem exists_point_geom : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ S) (M : LB (A ⊗ Over.mk ξ).left), Fam A M → ∃ a : Over.mk ξ ⟶ A, Same A (abelian₂ A L) M a (𝟙 _) := by
  intro S A _ hA L hL hAmp K _ _ ξ M hM
  obtain ⟨A', _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A ξ
  have := hA
  have : IsProper A.hom := IsAbelianScheme.proper
  have hA' : IsAbelianScheme A' := by
    have : IsCommMonObj A := hA.comm
    have hc : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
        ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hφ.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hA.geomConnected⟩
  have := hA'
  have : IsCommMonObj A := IsAbelianScheme.comm
  have : IsCommMonObj A' := IsAbelianScheme.comm
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  have hAmp' : Out.RelAmple A' (L.pull φ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hAmp hφ.1
  have hs : 𝟙 (Sp K) ≫ ξ = ξ := Category.id_comp ξ
  have hN' : Fam A' (M.pull (BaseChange.toBase hφ hs)) := BaseChange.fam_toBase hφ hs hM
  obtain ⟨a', ha'⟩ := _root_.GlobalTheory.AddLineField.additive_eq_lam_of_ample K A' hA' (L.pull φ) hL' hAmp' _ hN'
  refine ⟨GlobalTheory.AbDual.pushP hφ hs a', ?_⟩

  obtain hsq := GlobalTheory.LamPull.exists_isSquare (G := A) (G' := A') (f := ξ) (φ := φ) hφ.1.w
  have hLam : (abelian₂ A L).IsLB := FullSiegel.isLB_lam hL
  have hLam' : (abelian₂ A' (L.pull φ)).IsLB := FullSiegel.isLB_lam hL'
  have eLam := (GlobalTheory.LamPull.lbIso_lam_pull hφ hL hL' (GlobalTheory.lbIso_self hL') hsq).symm
  have h0 := (same_iff hN'.isLB hLam' _ _).mp ha'
  have e1 : evc hN'.isLB (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ 𝟙 _) =
      GlobalTheory.CechPic.pull (BaseChange.toBase hφ hs) (evc hM.isLB (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ 𝟙 _)) := by
    simp only [GlobalTheory.AbDual.evc]
    rw [show lift (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ 𝟙 _) = 𝟙 _ by simp,
      show lift (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ 𝟙 _) = 𝟙 _ by simp,
      Over.id_left, Over.id_left, GlobalTheory.CechPic.pull_id]
    exact (GlobalTheory.CechPic.pull_id _).trans (GlobalTheory.CechPic.cls_pull hM.isLB _ hN'.isLB)
  rw [same_iff hLam hM.isLB]
  rw [BaseChange.pull_inj_iff (BaseChange.toBase hφ hs) (BaseChange.ofBase hφ hs)
    (BaseChange.ofBase_toBase hφ hs), ← e1]
  unfold BaseChange.toBase
  rw [pull_evc]
  refine Eq.trans (GlobalTheory.AbDual.evc_eq (f := φ) (g := φ) hsq.1 hsq.2 hLam hLam' eLam
      (s := (A' ⊗ 𝟙_ (Over (Sp K))).hom) (s₀ := (A' ⊗ 𝟙_ (Over (Sp K))).hom ≫ ξ)
      (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ a') _ _ ?_ ?_).symm h0.symm
  · rw [Over.comp_left, GlobalTheory.AbDual.lift_left_fst]; rfl
  · simp only [Over.comp_left]
    rw [← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
    simp [GlobalTheory.AbDual.pushP]

theorem surjective_twist_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → Surjective (h ≫ snd A T).left := by
  intro R _ _ A _ hA L hL hAmp T _ _ N hN H h _ hiff
  refine ⟨fun x => ?_⟩

  let Ω := AlgebraicClosure (T.left.residueField x)
  let p : Sp Ω ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) Ω)) ≫ T.left.fromSpecResidueField x
  let tpt : Over.mk (p ≫ T.hom) ⟶ T := Over.homMk p rfl
  have hMf := Fam.ev hN tpt
  obtain ⟨a, ha⟩ := exists_point_geom (Sp R) A hA L hL hAmp Ω (p ≫ T.hom) _ hMf
  have hs : Same A (abelian₂ A L) N a tpt := by
    rw [same_iff (FullSiegel.isLB_lam hL) hN.isLB]
    rw [same_iff (FullSiegel.isLB_lam hL) hMf.isLB] at ha
    rw [ha, GlobalTheory.AbDual.evc_ev hN.isLB]
    simp
  obtain ⟨z, hz⟩ := (hiff (Over.mk (p ≫ T.hom)) a tpt).mp hs
  have e : z.left ≫ (h ≫ snd A T).left = p := by
    rw [← Over.comp_left, ← Category.assoc, hz, lift_snd]
    rfl
  let q : Sp Ω := IsLocalRing.closedPoint Ω
  refine ⟨z.left.base q, ?_⟩
  have e2 : (h ≫ snd A T).left.base (z.left.base q) = p.base q :=
    (Scheme.Hom.comp_apply z.left (h ≫ snd A T).left q).symm.trans
      (congrArg (fun f : Sp Ω ⟶ T.left => f.base q) e)
  exact e2.trans ((Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _))

end GlobalTheory.TwistKerSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TMulOfBox
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

theorem tMul_of_box : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), IsBoxGen (φ := thφ D.P.A (x3 D.P.A)) (φ₁ := thφ D₁.P.A (x3 D₁.P.A)) (φ₂ := thφ D₂.P.A (x3 D₂.P.A)) (ε := thε) w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t → ∀ (T T₁ T₂ : Over (Sp R)) (P : T ⟶ D.P.A) (P₁ : T₁ ⟶ D₁.P.A) (P₂ : T₂ ⟶ D₂.P.A) (ρ₁ : T ⟶ T₁) (ρ₂ : T ⟶ T₂), P ≫ p₁ = ρ₁ ≫ P₁ → P ≫ p₂ = ρ₂ ≫ P₂ → ∀ (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : ∀ χ : D₁.X, LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ χ) Oinvε)) (t₂ : ∀ χ : D₂.X, LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ χ) Oinvε)), (∀ x, IsBoxGen w ρ₁.left ρ₂.left (t x) (t₁ (q₁ x)) (t₂ (q₂ x))) → TMul D₁ P₁ t₁ → TMul D₂ P₂ t₂ → TMul D P t := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w hc T T₁ T₂ P P₁ P₂ ρ₁ ρ₂ e₁ e₂ t t₁ t₂ hb h₁ h₂ χ χ'
  haveI := hS.hom₁
  haveI := hS.hom₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.P.isLB y
  have B : ∀ x, (om w y J₁ J₂ J (P * cP D T x).left)⁻¹ * om w y J₁ J₂ J (cP D T x).left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹ * val (t x) (𝟙 T.left) y J =
      val (t₁ (q₁ x)) ρ₁.left y J₁ * val (t₂ (q₂ x)) ρ₂.left y J₂ := fun x => by
    have := hb x T.left (𝟙 T.left) y J₁ J₂ J hJ₁ hJ₂ hJ
    simp only [Category.id_comp] at this
    rwa [GlobalTheory.TorusCoordPull.prod_O D P x (om w y J₁ J₂ J)] at this
  have K₁ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₁, cPoint_pr hS.c_pr₁, e₁, ← comp_cP D₁ ρ₁ (q₁ χ), ← comp_cP D₁ ρ₁ (q₁ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have K₂ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₂, cPoint_pr hS.c_pr₂, e₂, ← comp_cP D₂ ρ₂ (q₂ χ), ← comp_cP D₂ ρ₂ (q₂ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have C0 := hc T.left (lift (cP D T χ) (lift (cP D T χ') P)).left y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [K₁, K₂] at C0
  have pc := prod_cub (cP D T χ) (cP D T χ') P (om w y J₁ J₂ J)
  have C : (om w y J₁ J₂ J (cP D T χ * cP D T χ' * P).left * (om w y J₁ J₂ J (cP D T χ * cP D T χ').left)⁻¹ *
      (om w y J₁ J₂ J (cP D T χ * P).left)⁻¹ * (om w y J₁ J₂ J (cP D T χ' * P).left)⁻¹ *
      om w y J₁ J₂ J (cP D T χ).left * om w y J₁ J₂ J (cP D T χ').left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹) * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ := by
    rw [← pc]; exact C0
  have M₁ : val (t₁ (q₁ χ + q₁ χ')) ρ₁.left y J₁ *
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ =
      val (t₁ (q₁ χ)) ρ₁.left y J₁ * val (t₁ (q₁ χ')) ρ₁.left y J₁ := by
    have := (val_mul hJ₁ _ _ _).symm.trans ((val_corr hJ₁ (h₁ (q₁ χ) (q₁ χ')) ρ₁.left).trans (val_mul hJ₁ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₁ _ _ _).symm
  have M₂ : val (t₂ (q₂ χ + q₂ χ')) ρ₂.left y J₂ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ =
      val (t₂ (q₂ χ)) ρ₂.left y J₂ * val (t₂ (q₂ χ')) ρ₂.left y J₂ := by
    have := (val_mul hJ₂ _ _ _).symm.trans ((val_corr hJ₂ (h₂ (q₂ χ) (q₂ χ')) ρ₂.left).trans (val_mul hJ₂ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₂ _ _ _).symm
  have B0 := B (χ + χ')
  have Ba := B χ
  have Bb := B χ'
  rw [map_add (f := _), map_add (f := _), cPoint_add,
    show P * (cP D T χ * cP D T χ') = cP D T χ * cP D T χ' * P from mul_comm _ _] at B0
  rw [show P * cP D T χ = cP D T χ * P from mul_comm _ _] at Ba
  rw [show P * cP D T χ' = cP D T χ' * P from mul_comm _ _] at Bb
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans
    (congrArg (fun r => val D.cub.t r y J) (Category.id_comp _))))).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  show val (t (χ + χ')) (𝟙 T.left) y J * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
    val (t χ) (𝟙 T.left) y J * val (t χ') (𝟙 T.left) y J
  apply Additive.ofMul.injective
  have a0 := congrArg Additive.ofMul B0
  have a1 := congrArg Additive.ofMul Ba
  have a2 := congrArg Additive.ofMul Bb
  have a3 := congrArg Additive.ofMul C
  have a4 := congrArg Additive.ofMul M₁
  have a5 := congrArg Additive.ofMul M₂
  simp only [ofMul_mul, ofMul_inv] at a0 a1 a2 a3 a4 a5 ⊢
  linear_combination (norm := abel) a0 + a3 - a1 - a2 + a4 + a5

end GlobalTheory.ProdUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatricesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_periods_balanced_integralMatrices : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    letI := PowLim.mod xe (symUnitOf W h)
    ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
      (fun y => a • y) (fun y => star a • y) := by
  first | exact @GlobalTheory.Mum.PolTens.tauBal_polTens | exact GlobalTheory.Mum.PolTens.tauBal_polTens | (intros; apply GlobalTheory.Mum.PolTens.tauBal_polTens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataPeriodsBalancedMatrixAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensBal

theorem transpose_mul_eq {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det)
    (a : TensO (symUnitOf W h)) :
    (TensO.mat _ a).transpose * (W + W.transpose) = (W + W.transpose) * TensO.mat _ (star a) := by
  have hb : ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show _ = (W + W.transpose) * (((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ)))
  rw [hb.symm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem tauBal_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), letI := T.mod (symUnitOf W h); ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact _root_.GlobalTheory.TensBal.tauBal_tens R _ D D' W T (TensO.mat _ a) (TensO.mat _ (star a)) (transpose_mul_eq W h a)

end GlobalTheory.Mum.TensBal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListRealisedSystemUpToRootsOfUnityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A)) (c : Fin N → K), ThList ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) pt c → (∀ x, ∃ b, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  first | exact @GlobalTheory.UMin.thList_real | exact GlobalTheory.UMin.thList_real | (intros; apply GlobalTheory.UMin.thList_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionPullbackThetaSectionsGaloisTwistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupAction_pullbackThetaSectionsGaloisTwist : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R), σ.comp τ = AlgHom.id _ _ → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (a b : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), IsActOf A.A A.L N (thTw A N τ θ) a b → IsActOf A.A A.L N θ (secTw A N σ a) (secTw A N σ b) := by
  first | exact @GlobalTheory.Mum.Conj.isActOf_secTw | exact GlobalTheory.Mum.Conj.isActOf_secTw | (intros; apply GlobalTheory.Mum.Conj.isActOf_secTw <;> assumption)
end

