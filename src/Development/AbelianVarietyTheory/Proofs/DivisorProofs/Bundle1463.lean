module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc IntermediateField

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef.CurveFF

theorem isFF_of_trdeg_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (h : Algebra.trdeg k F = 1) : IsFF k F := by
  have hna : ¬ Algebra.IsAlgebraic k F := fun ha => by
    rw [trdeg_eq_zero_iff.mpr ha] at h; exact zero_ne_one h
  obtain ⟨x, hx⟩ : ∃ x : F, Transcendental k x := by
    by_contra hc
    push_neg at hc
    exact hna ⟨fun x => by simpa [Transcendental] using hc x⟩
  exact ⟨x, hx, finiteDimensional_adjoin_of_trdeg_le_one h.le x hx⟩

theorem isFF_of_stalk (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0}) [IsIntegral C]
    [Algebra k Γ(C, ⊤)] (hp : IsProjOver (strHom k (X := C))) (hd : topologicalKrullDim C = 1)
    (y : C) (hy : y = genericPoint C) (ψ : C.presheaf.stalk y ⟶ CommRingCat.of K)
    (hψ : Function.Surjective ψ.hom)
    (hc : Spec.map ψ ≫ C.fromSpecStalk y ≫ strHom k C = spMap (algebraMap k K)) : IsFF k K := by
  subst hy
  let φ : k →+* C.functionField := (Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ strHom k C)).hom
  have hφ : C.fromSpecStalk (genericPoint C) ≫ strHom k C = spMap φ := (Spec.map_preimage _).symm
  letI : Algebra k C.functionField := φ.toAlgebra
  have htr : Algebra.trdeg k C.functionField = 1 := by
    have := FunctionFieldTrdeg.trdeg_functionField_eq k C (strHom k C) 1 hp (by simpa using hd) φ hφ
    simpa using this
  have hfg : (⊤ : IntermediateField k C.functionField).FG :=
    FGFun.fg_functionField k C (strHom k C) hp k C.functionField φ (𝟙 _) (RingHom.id _) (by simp [hφ])
  haveI : Algebra.EssFiniteType k C.functionField := IntermediateField.fg_top_iff.mp hfg
  let ψ' : C.functionField →+* K := ψ.hom
  have hinj : Function.Injective ψ' := ψ'.injective
  have hcomm : ∀ c : k, ψ' (φ c) = algebraMap k K c := by
    rw [hφ] at hc
    have h1 : Spec.map (CommRingCat.ofHom φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      rw [Spec.map_comp]; exact hc
    have h2 := Spec.map_injective h1
    intro c
    exact congrArg (fun f => f.hom c) h2
  let e : C.functionField ≃ₐ[k] K :=
    AlgEquiv.ofBijective { ψ' with commutes' := hcomm } ⟨hinj, hψ⟩
  haveI : Algebra.EssFiniteType k K := (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  exact isFF_of_trdeg_eq_one (e.trdeg_eq ▸ htr)

theorem isFF_of_isGenOver : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  IsFF k K := by
  intro k K _ _ _ _ _ C _ x hx
  obtain ⟨⟨hs, hp, hg⟩, ⟨hdom, hpre⟩, hxs⟩ := hx
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hs hg
  let p : Sp K := IsLocalRing.closedPoint (CommRingCat.of K)
  haveI : Nonempty C := ⟨x p⟩
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hs
  have hgen : x p = genericPoint C := by
    have hr : Set.range x = {x p} := by
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        rw [Set.mem_singleton_iff, Subsingleton.elim v p]
      · rintro rfl
        exact ⟨p, rfl⟩
    refine ((genericPoint_spec C).eq ?_).symm
    rw [isGenericPoint_def, ← hr]
    exact x.denseRange.closure_range
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp
      (x.stalkMap_surjective _)
  refine isFF_of_stalk k K C hp hd _ hgen (Scheme.stalkClosedPointTo x) hsurj ?_
  rw [← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hxs]

end GlobalTheory.Nef.CurveFF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoCotMapOfIsOpenImmersion
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusCot

open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.Conormal GlobalTheory.SS.TorusSlice

theorem isFrame_append {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : IsFrame e₁) (he₂ : IsFrame e₂) :
    IsFrame (Fin.append (fun i => p₁.app U (e₁ i)) fun j => p₂.app U (e₂ j)) := by
  let ψ (V : S.Opens) : (Γ(F₁, V) × Γ(F₂, V)) ≃ₗ[Γ(S, V)] Γ(F, V) :=
    LinearEquiv.ofBijective ((QCoh.appLinear p₁ V).coprod (QCoh.appLinear p₂ V)) ⟨by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ hab
      change p₁.app V a + p₂.app V b = 0 at hab
      have a₁ := congrArg (i₁.app V) hab
      have a₂ := congrArg (i₂.app V) hab
      rw [map_add (f := _), map_zero, QCoh.app_app, QCoh.app_app] at a₁ a₂
      rw [h₁, h₄] at a₁
      rw [h₃, h₂] at a₂
      ext
      · simpa using a₁
      · simpa using a₂, fun c => ⟨(i₁.app V c, i₂.app V c), congr(($h).app V c)⟩⟩
  refine isFrame_of_basis (fun V k => (((he₁.basis k).prod (he₂.basis k)).map (ψ V)).reindex finSumFinEquiv)
    fun V k i => ?_
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply]
  rcases i with i | i
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]

section Geo

variable {S : Scheme.{0}} {T G B Y : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
  [IsMonHom u] {j : Y ⟶ G} {σ : Y ⟶ T}

end Geo

end GlobalTheory.TorusCot

namespace GlobalTheory.TorusPart

open GlobalTheory.TorusCot GlobalTheory.QCoh

end GlobalTheory.TorusPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSRIffIsKS
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Frames GlobalTheory.AllWt
open Formalism.L2.Pj
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsKSR (Φ : Finset (E →+* ℂ)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (x' : Sp (DualNumber S) ⟶ Xo.X) (M : HIx Dw Φ → S) : Prop :=
  ∃ (A : Over (Sp S)) (_ : GrpObj A) (A' : Over (Sp (DualNumber S))) (_ : GrpObj A')
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (epsRed S) i) (ψ : LinearMap.BilinForm S (HdR A))
    (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A),
    IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧
    IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
    (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧
    ∀ (τ : Φ) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, IsLieComb (fun b => M ⟨τ, a, b⟩) (ub τ.1) w ∧
      IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w

theorem isKSR_iff_isKS {Φ : Finset (E →+* ℂ)} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {x' : Sp (DualNumber K) ⟶ Xo.X} {M : HIx Dw Φ → K} : IsKSR Φ y x' M ↔ IsKS Φ y x' M := Iff.rfl

theorem IsKSR.baseChange (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {S S' : Type} [CommRing S] [Algebra c.F S]
    [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {y : FrPt Xo c S} {y' : FrPt Xo c S'} (h : FrMap ψ y y')
    {x : Sp (DualNumber S) ⟶ Xo.X} {M : HIx Dw Φ → S}
    (hM : IsKSR Φ y x M) : IsKSR Φ y' (spMap (dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  let : Algebra S S' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap S S'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (dualMap (algebraMap S S')))
  have e₀ : spMap (algebraMap S S') ≫ epsRed S = epsRed S' ≫ spMap (dualMap (algebraMap S S')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ epsRed S') ≫ spMap (dualMap (algebraMap S S')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (epsRed S') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 S A _ hA gA S' B φ hφ
  have hL := (P.2.1 S' B _ (PolPull.isAbelianScheme_of_isGrpPullback hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  choose tv htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1] <;> rfl
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, ArcQ.NormalForm.isLieComb_baseChange hφ (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp

end GlobalTheory.FlagTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOfIsOrtho
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.OrthoMetric

namespace GlobalTheory.SupFull

theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x : (U.X k).dom) (W : PullbackSections.UnfAt U k x) (Wu : PullbackSections.UnitAt W), (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  have hper : ∀ (v : Fin r → E) j, perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2 =
      if (((W.e.trans f) j).2 : ℕ) < (U.X k).p0 then
        FD.hermC ((W.e.trans f) j).1.1 (U.X k).Gm
          (FD.col (FD.mat x.1 ((W.e.trans f) j).1) ((W.e.trans f) j).2) (FD.Data.emb ((W.e.trans f) j).1.1 v)
      else ((FD.mat x.1 ((W.e.trans f) j).1)⁻¹.mulVec (FD.Data.emb ((W.e.trans f) j).1.1 v))
        ((W.e.trans f) j).2 := by
    intro v j
    have h := hf (W.e j)
    rw [Equiv.trans_apply]
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    generalize ((W.e j).2 : ℕ) = i at h ⊢
    dsimp only at h ⊢
    rw [← hp0] at h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dif_pos (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have key : Wu.Hm = Matrix.diagonal fun j => ((2 * (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) := by
    refine PullbackSections.UH.herm_eq_of_im W.Pm W.per.2.2.2.1 _ _ fun a b => ?_
    rw [Wu.c1, OrthoHerm.im_diag_eq_trace (U.X k).p0 _ (U.X k).Gm (U.X k).Ψ (U.X k).cmType (W.e.trans f) hcc x.1 hx
      (W.φ k a) (W.φ k b) _ _ (fun j => (W.pm_eq a j).trans (hper _ j)) (fun j => (W.pm_eq b j).trans (hper _ j)),
      ← W.isom, Rat.cast_intCast]
  have hd : ∀ j, (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    intro j
    have hn : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖((W.e.trans f) j).1.1 (U.X k).ξ0‖ := by
      rcases hf (W.e j) with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · rw [Equiv.trans_apply, h]
      · rw [Equiv.trans_apply, h]
        exact (Complex.norm_conj _).symm
    rw [hn]
    clear hn
    have hpos := Wu.pos (Pi.single j 1) (by simp)
    rw [key, hermForm, single_dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.single_eq_same, star_one,
      _root_.one_mul, _root_.mul_one, Complex.ofReal_re] at hpos
    generalize ((W.e.trans f) j).1.1 = τ at hpos ⊢
    have hre : (τ (-(U.X k).ξ0)).re = 0 := by
      have h := congrArg τ hcc
      rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg τ (-(U.X k).ξ0)] at h
      have := congrArg Complex.re h
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    have hp : 0 < (τ (-(U.X k).ξ0)).im := by linarith
    rw [← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.mpr hre, abs_of_pos hp]
  rw [key]
  simp only [hd]

theorem isMetric_of_isOrtho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (x : (U.X k).dom), (U.X k).IsOrtho x.1 → IsMetric (U.un k x) 1 (fun b => ((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • 1) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hpq k x hx
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := hm_eq_diagonal E H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨Φ₀⟩ := nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (secNZ_of_secGen lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2 Wu.c3 Wu.c4
    Wu.c5 Wu.c6 Wu.c7
  choose w hw using fun τ i => hD _ _ ((U.un k x).tan τ i) (W.der τ i)
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have hN := Wu.c9.symm
  have hG : ∀ (b : E →+* ℂ) (i j : Fin (Dw.mult b)),
      (((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) i j =
        Real.pi * hermForm Wu.Hm (Pi.single (W.e.symm ⟨b, j⟩) 1) (Pi.single (W.e.symm ⟨b, i⟩) 1) := by
    intro b i j
    rw [hH]
    simp [hermForm, Matrix.mulVec_diagonal, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all <;> ring
  exact isMetricAt_of Φ hg u Wu.Hm χ Wu.θ Wu.Fd w (fun b i => Pi.single (W.e.symm ⟨b, i⟩) 1)
    ⟨ht, hA, hR, hF, hFd, hN, hw, hG⟩

theorem isBddSec_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Unf Xo c σ r), GoodEmb c σ → IsUnf U → IsUnf U' → 1 ≤ Dw.p + Dw.q → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, (∀ k, (U.X k).IsBddSec (laU U a n k) (rdU U f k)) → ∀ k, (U'.X k).IsBddSec (laU U' a n k) (rdU U' f k) := by
  intro E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' hpq a n hd f hf hb k'
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hs' := hU'.2.2.2.2.1 a n hd f hf k'
  choose C hC using fun k => (hb k).2
  have hpos : ∀ (X : FD.Data E r) (b : E →+* ℂ), 0 < 2 * Real.pi * ‖relab c σ b X.ξ0‖ := fun X b =>
    mul_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero _).2 X.ξ0_ne))
  let κ : U.Comp → (E →+* ℂ) → ℝ := fun k b =>
    2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ / (2 * Real.pi * ‖relab c σ b (U'.X k').ξ0‖)
  let B : U.Comp → ℝ := fun k =>
    (∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2)) * |C k|
  refine ⟨hs', ∑ k, B k, fun x₁ hx₁ => ?_⟩
  obtain ⟨b, hbB, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U'.X k')).1 x₁ hx₁
  have hx' := FD.OrthogonalFrameDomain.rmul_mem_dom (U'.X k') hx₁ hbB
  rw [← (FD.orthonormalFlagTranslate_holds r (U'.X k')).2.1 _ _ hs'.2.1 x₁ hx₁ b hbB,
    PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ ho)]
  have hN := isMetric_of_isOrtho E H Dw l Xo c σ r U' hσ hU' hpq k' ⟨_, hx'⟩ ho
  have hrd' : ‖rdU U' f k' (FD.rmul x₁ b)‖ = cabs (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := by
    have e : rdU U' f k' (FD.rmul x₁ b) = toC (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := dif_pos hx'
    rw [e]; rfl
  rw [hrd']
  generalize U'.un k' ⟨_, hx'⟩ = y at hN ⊢
  obtain ⟨k, x, t, hx, ht⟩ := _root_.GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ r U hU y
  obtain ⟨g, hg0, hgd, hchg⟩ :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hm0 := isMetric_of_isOrtho E H Dw l Xo c σ r U hσ hU hpq k x hx
  have hm1 := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨hNN, hG⟩ := _root_.GlobalTheory.LamT.MetUniq.isMetric_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hnone : cabs (t none : CAt σ) = 1 := by
    rw [_root_.mul_one] at hNN
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hNN.symm
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), cabs (t (some p) : CAt σ) = (Real.sqrt (κ k p.1))⁻¹ := by
    rintro ⟨τ, i⟩
    rw [← hgd τ i]
    refine OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _
      (div_pos (hpos _ _) (hpos _ _)) (fun i j hij => hg0 τ j i hij) ?_ i
    have h1 := (congrFun hG τ).symm
    have h2 : ((2 * Real.pi * ‖relab c σ τ (U'.X k').ξ0‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos _ _).ne'
    dsimp only at h1
    rw [Complex.ofReal_div, div_eq_inv_mul, mul_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hev := hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n f hf t _ _ ht
  have hw : cabs (wchar (ex Dw a n) t) =
      ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2) := by
    rw [GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, hnone, one_pow, _root_.one_mul]
    exact Finset.prod_congr rfl fun p _ => by rw [hsome p]; rfl
  have hrd : ‖rdU U f k x.1‖ = cabs (evR Xo c f (U.un k x)) := by
    have e : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
    rw [e]; rfl
  have hle := hC k x.1 x.2
  rw [PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ hx), hrd] at hle
  have hB0 : ∀ k, 0 ≤ B k := fun k => mul_nonneg (Finset.prod_nonneg fun p _ => by positivity) (abs_nonneg _)
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw]
  exact (mul_le_mul_of_nonneg_left (hle.trans (le_abs_self _)) (Finset.prod_nonneg fun p _ => by positivity)).trans
    (Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_univ k))

end GlobalTheory.SupFull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepContinuousGroup
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

namespace GlobalTheory.FinLatF

theorem latRepF_cont : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om h f u
  have hσ : ∀ x, σ (σ x) = x := fun x => GlobalTheory.AdelicU.cm_conj_conj hB.cm x
  have H := isHeis_opFF hσ hS hT hξ hc h.hw
  have hfix : ∀ p : GAF σ JS × GAF σ JT, (∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ) →
      ∀ e, Fixes (opFF hc w) (latF F E nS nT Λ) e → Om p e = e := by
    intro p hp e he
    rw [h.vac p e he]
    exact GlobalTheory.FinWeilO.normOp_of_le H lam (h.sd' p) (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he
  have hev : ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f := by
    intro f
    have hf : f ∈ Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} := by
      rw [h.span]; trivial
    induction hf using Submodule.span_induction with
    | mem _ hm =>
      obtain ⟨x, e, he, rfl⟩ := hm
      obtain ⟨N, hN, hNl⟩ := h.lev (w • x)
      filter_upwards [h.near, h.near' x N hN] with p hp hp'
      obtain ⟨l, hl, hl'⟩ := hp'
      have e2 : gamFF σ JS JT ξ₀ B.ψ (w • x) (N • l) = 1 := by
        rw [gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNl l hl, one_mul]
      have e4 := H.comp x (N • l) e
      rw [he _ (nsmul_mem hl N), e2, one_smul] at e4
      rw [h.op, hfix p hp e he, hl', ← e4]
    | zero => exact Filter.Eventually.of_forall fun p => map_zero _
    | add u v _ _ hu hv => filter_upwards [hu, hv] with p h3 h4 using by rw [map_add (f := _), h3, h4]
    | smul c u _ hu => filter_upwards [hu] with p h3 using by rw [map_smul, h3]
  haveI : IsTopologicalGroup (GAF σ JS) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GAF σ JT) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)
  refine continuousAt_const.congr (f := fun _ => (Om q f : WOF F E nS nT → ℂ) u) ?_
  filter_upwards [h1.eventually (hev f)] with p hp
  conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]

end GlobalTheory.FinLatF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionThetaStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_adapted_pair_restriction_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), ∃ z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              M.co.rho B.ψ u (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ) := by
  first | exact @GlobalTheory.MixedLagr.exists_ratLagr | exact GlobalTheory.MixedLagr.exists_ratLagr | (intros; apply GlobalTheory.MixedLagr.exists_ratLagr <;> assumption)
end

