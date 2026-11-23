module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem adjKlt_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (T : Subring K) (φ : K →₀ ℚ) (S : Place c) (S' : Place c'), TrBasis c x → (∀ a, e a ∈ S'.ring ↔ a ∈ S.ring) → AdjKlt c n T S (dForm c x) φ → AdjKlt c' n (T.map e.toRingHom) S' (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) := by
  intro k K K' _ _ _ _ c c' e hce n x T φ S S' hx hS h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.FieldPair.placeEquiv_ringEquiv c c' e hce
  have hmem : ∀ (P : Place c) (b : K'), b ∈ (Φ P).ring ↔ e.symm b ∈ P.ring := fun P b => by
    simpa using (hΦ P).1 (e.symm b)
  have hord : ∀ (P : Place c) (b : K'), (Φ P).ord b = P.ord (e.symm b) := fun P b => by
    simpa using (hΦ P).2.1 (e.symm b)
  have hdisc : ∀ P : Place c, (Φ P).disc (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) =
      P.disc (dForm c x) φ := fun P => by
    simp only [Place.disc]
    rw [(hΦ P).2.2.1 φ, (hΦ P).2.2.2 n x hx]
    rfl
  have hΦS : Φ S = S' := Place.ext (ValuationSubring.ext _ _ fun b => by
    rw [hmem, ← hS (e.symm b), e.apply_symm_apply])
  have hk : Klt c n ⊤ (dForm c x) φ := ⟨h.1, h.2.1, fun P hP =>
    (P.ring_ne_top (eq_top_iff.2 fun f _ => hP f trivial)).elim⟩
  have hk' := ((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x ⊤ φ hx).2.2.1).1 hk
  refine ⟨hk'.1, hk'.2.1, ?_⟩
  intro Q' hQ' t' u' E' hTQ hmax hdim hSQ hEQ ht hu hoth
  set Q : Subring K := Q'.map e.symm.toRingHom with hQdef
  have hQmem : ∀ a : K, a ∈ Q ↔ e a ∈ Q' := fun a => by
    exact Subring.mem_map_equiv (f := e.symm) (K := Q')
  have hQQ : Q.map e.toRingHom = Q' := by
    ext b
    exact (Subring.mem_map_equiv (f := e) (K := Q)).trans ((hQmem _).trans (by rw [e.apply_symm_apply]))
  have hQ : IsLocModel c Q :=
    ((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x Q φ hx).2.1).2 (hQQ ▸ hQ')
  let ψ : Q' ≃+* Q := e.symm.subringMap
  have hψ : ∀ y, ((ψ y : Q) : K) = e.symm y := fun y => rfl
  have hprime : ∀ P : Place c, (Φ P).IsPrimeOf Q' ↔ P.IsPrimeOf Q := by
    intro P
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · have := h1 (e f) ((hQmem f).1 hf)
        rwa [hmem, e.symm_apply_apply] at this
      · obtain ⟨a, ha, b, hb, hb0, hbo, hfab⟩ :=
          h2 (e f) (by rw [hmem, e.symm_apply_apply]; exact hf)
        refine ⟨e.symm a, by rw [hQmem, e.apply_symm_apply]; exact ha,
          e.symm b, by rw [hQmem, e.apply_symm_apply]; exact hb,
          by simpa using hb0, by rw [← hord]; exact hbo, ?_⟩
        apply e.injective
        rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, hfab]
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · rw [hmem]
        exact h1 _ (by rw [hQmem, e.apply_symm_apply]; exact hf)
      · obtain ⟨a, ha, b, hb, hb0, hbo, hfab⟩ := h2 (e.symm f) ((hmem P f).1 hf)
        refine ⟨e a, (hQmem a).1 ha, e b, (hQmem b).1 hb, by simpa using hb0,
          by rw [hord, e.symm_apply_apply]; exact hbo, ?_⟩
        rw [← hfab, map_mul, e.apply_symm_apply]
  set E := Φ.symm E' with hEdef
  have hE : Φ E = E' := Φ.apply_symm_apply E'
  haveI := hQ'.isLocalRing
  haveI := hQ.isLocalRing
  have hTQ' : T ≤ Q := fun f hf => (hQmem f).2 (hTQ (Subring.mem_map.2 ⟨f, hf, rfl⟩))
  have hmax' : Ideal.span {ψ t', ψ u'} = IsLocalRing.maximalIdeal Q := by
    have h1 := congrArg (Ideal.map ψ) hmax
    rw [Ideal.map_span, Set.image_pair] at h1
    rw [h1]
    ext z
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      rwa [isUnit_map_iff]
    · intro hz
      refine ⟨ψ.symm z, ?_, ψ.apply_symm_apply z⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
      rwa [isUnit_map_iff ψ.symm]
  have hdim' : ringKrullDim Q = 2 := by
    rw [← ringKrullDim_eq_of_ringEquiv ψ]
    exact hdim
  have hSQ' : S.IsPrimeOf Q := (hprime S).1 (hΦS ▸ hSQ)
  have hEQ' : E.IsPrimeOf Q := (hprime E).1 (hE ▸ hEQ)
  have ht' : S.ord ((ψ t' : Q) : K) = 1 := by
    rw [hψ, ← hord, hΦS]
    exact ht
  have hu' : E.ord ((ψ u' : Q) : K) = 1 := by
    rw [hψ, ← hord, hE]
    exact hu
  have hoth' : ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.disc (dForm c x) φ = 0 := by
    intro P hP hPS hPE
    rw [← hdisc]
    refine hoth (Φ P) ((hprime P).2 hP) (fun hr => hPS ?_) (fun hr => hPE ?_)
    · have h3 : Φ P = Φ S := Place.ext (hr.trans (congrArg Place.ring hΦS).symm)
      rw [Φ.injective h3]
    · have h3 : Φ P = Φ E := Place.ext (hr.trans (congrArg Place.ring hE).symm)
      rw [Φ.injective h3]
  have key := h.2.2 Q hQ (ψ t') (ψ u') E hTQ' hmax' hdim' hSQ' hEQ' ht' hu' hoth'
  rw [← hE, hdisc]
  exact key

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangent
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
    {ι : Type} [Fintype ι] (y : FrPt Xo c K) (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X)
    (h1 : X ≫ Xo.s = sOf c _) (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x)
    (M : ι → K) : GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1]
    unfold sOf
    have e : (GlobalTheory.FlagTan.dir c M).toRingHom.comp (algebraMap c.F (TrivSqZeroExt K (ι → K))) =
        algebraMap c.F (DualNumber K) := (GlobalTheory.FlagTan.dir c M).comp_algebraMap
    rw [spMap_comp_spMap, ← RingHom.comp_assoc, e]
  · rw [← Category.assoc, spMap_comp_spMap, ← h2]
    congr 2
    ext z <;> simp

theorem ksIso_psiSet : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  obtain ⟨X, h1, h2, hks⟩ := _root_.GlobalTheory.FlagTan.KSUniv.ksUniv hP hG E H Dw l Xo c K y hpq
  refine ⟨X, h1, h2, fun x' hx => ?_⟩
  have key : ∀ M, IsKS (psiSet H) y x' M ↔ x' = spMap (dir c M).toRingHom ≫ X := fun M =>
    ⟨fun k => _root_.GlobalTheory.FlagTan.eq_of_isKS_eq hP hG E H Dw l Xo c K y _ _ M hpq hx (isTanX_dir y X h1 h2 M) k (hks M),
      fun e => e ▸ hks M⟩
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.KSExist.ksExist hP E H Dw l Xo c K y x' hpq hx
  exact ⟨⟨M, (key M).1 hM, fun M' e => _root_.GlobalTheory.FlagTan.isKS_unique hP E H Dw l Xo c K y x' hpq hx M' M ((key M').2 e) hM⟩, key⟩

end GlobalTheory.FlagTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
namespace GlobalTheory.SmoothDimTotal
open IsLocalRing

theorem topologicalKrullDim_eq_iSup_stalk (X : Scheme.{0}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  simp only [ringKrullDim_stalk_eq_coheight]

theorem ringKrullDim_stalk_le_of_smooth (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (.of K)) (n : ℕ)
    (h : SmoothOfRelativeDimension n f) (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ n := by
  haveI : Nonempty X := ⟨x⟩
  rw [ringKrullDim_stalk_eq_coheight, ← GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth f n h]
  exact (Order.coheight_le_krullDim x).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).ge

end GlobalTheory.SmoothDimTotal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsFinExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LabExt

open GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem qkExt_refl {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C]
    [Algebra (FractionRing R) C] {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

section Lab

variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] {ρ : R →+* R₁}
  {D : DegPre R} {D₁ : DegPre R₁} [Algebra (FractionRing R) (Kb R₁)]

variable {A : PolAV (Sp (FractionRing R))} {A₁ : PolAV (Sp (FractionRing R₁))}

end Lab

end GlobalTheory.LabExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPush
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorSym

open GlobalTheory.CechPic GlobalTheory.EndRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def genι (G : Over (Sp R)) : (Over.map (jK R)).obj ((Over.pullback (jK R)).obj G) ⟶ G :=
  Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

theorem lam_push (U : UnifPre I D A G) {T : Over (Sp (FractionRing R))} (x y : T ⟶ (Over.pullback (jK R)).obj G) :
    @id (Pic T.left) (lam (T := (Over.map (jK R)).obj T) (cls _ U.LG.isLB) (push (genι G) x) (push (genι G) y)) =
      lam (cls _ A.isLB) (x ≫ U.gen.hom) (y ≫ U.gen.hom) := by
  have := U.gen_hom
  have e := (cls_eq_iff (LB.isLB_pull A.isLB _) (LB.isLB_pull U.LG.isLB _)).2 U.ext
  rw [cls_pull A.isLB, cls_pull U.LG.isLB] at e
  have hm : ∀ x y : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) (x * y) = push (genι G) x * push (genι G) y :=
    fun x y => push_mul (genι G) (𝟙 _) (Category.id_comp _).symm x y
  have h1 : push (genι G) (1 : T ⟶ (Over.pullback (jK R)).obj G) = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hp : ∀ x : T ⟶ (Over.pullback (jK R)).obj G,
      @id (Pic T.left) (pull (push (genι G) x).left (cls _ U.LG.isLB)) =
        pull x.left (pull U.gen.hom.left (cls _ A.isLB)) := fun x => by
    rw [e, ← pull_comp]; rfl
  rw [← lam_pull U.gen.hom, lam, lam, ← hm, ← h1, ← hp, ← hp, ← hp, ← hp]
  rfl

theorem lam_act (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.OAct O}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) {T : Over (Sp (FractionRing R))}
    (x y : (Over.map (jK R)).obj T ⟶ G) :
    lam (cls _ U.LG.isLB) (x ≫ oG.act a) y = lam (cls _ U.LG.isLB) x (y ≫ oG.act (star a)) := by
  have sj : ∀ x : (Over.map (jK R)).obj T ⟶ G, ∃ x' : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) x' = x :=
    fun x => ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  obtain ⟨x, rfl⟩ := sj x
  obtain ⟨y, rfl⟩ := sj y
  have e' : ∀ f : G ⟶ G, push (genι G) ((Over.pullback (jK R)).map f) = genι G ≫ f := fun f =>
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  rw [← push_comp _ (e' _), ← push_comp _ (e' _)]
  refine (lam_push U _ _).trans (Eq.trans ?_ (lam_push U _ _).symm)
  obtain ⟨t, ht⟩ := GlobalTheory.RosatiDescent.exists_gen_of_rosatiAdj (oA.rosati a)
  have := cls_of_rosati A.isLB t ht (x ≫ U.gen.hom) (y ≫ U.gen.hom)
  rw [Category.assoc, Category.assoc, h.ext, h.ext, ← Category.assoc, ← Category.assoc, lam, lam, this]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F hF A' G' _ _ _ U' oA oG hlin G _ _ _ inc pr _ _ hip hpi κ₀ hκ
  have hs : oG.act (star F.e * F.f * F.e) = oG.act (star F.e * star F.f * F.e) :=
    congrArg oG.act hF.2.1
  have hi : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  let GK := (Over.pullback (jK R)).obj G
  have hL := U'.LG.isLB
  have sy : ∀ x y : (Over.map (jK R)).obj (G2 GK) ⟶ G,
      lam (cls _ hL) (x ≫ inc) (y ≫ inc ≫ oG.act F.f) = lam (cls _ hL) (y ≫ inc) (x ≫ inc ≫ oG.act F.f) := fun x y => by
    have e₁ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act F.f)
    have e₂ := lam_act U'.toUnifPre hlin F.f (x ≫ inc) (y ≫ inc)
    have e₃ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act (star F.f))
    have e₄ : inc ≫ oG.act F.f ≫ oG.act (star F.e) = inc ≫ oG.act (star F.f) ≫ oG.act (star F.e) := by
      have := congrArg (inc ≫ ·) hs
      simpa only [oG.map_mul, reassoc_of% hi] using this
    simp only [Category.assoc, hi] at e₁ e₂ e₃
    rw [e₁, e₄, ← e₃, ← e₂, lam_comm]
  have hP := pull_isLB (GlobalTheory.FullSiegel.isLB_lam hL)
    (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  refine (gen_iff_sum (pull_isLB hP κ₀) _ _).2 ?_
  rw [cls_pull hP, GlobalTheory.FullSiegel.cls_lam_pull hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, ← pull_comp]
  let X : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (fst GK GK)
  let Y : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (snd GK GK)
  have k₁ : κ₀ = (lift X Y).left := by
    refine pullback.hom_ext (hκ.1.trans ?_) (hκ.2.trans ?_)
    · exact (congrArg (·.left) (lift_fst X Y)).symm
    · exact (congrArg (·.left) (lift_snd X Y)).symm
  have k₂ : (lift (snd GK GK) (fst GK GK)).left ≫ κ₀ = (lift Y X).left := by
    rw [k₁]; exact lift_push (genι G) _ _
  have p₁ := pull_lam (lift X Y) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  have p₂ := pull_lam (lift Y X) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  rw [lift_fst_assoc, lift_snd_assoc] at p₁ p₂
  rw [← k₁] at p₁
  rw [← k₂] at p₂
  exact add_neg_eq_zero.2 (p₂.trans ((sy Y X).trans p₁.symm))

end GlobalTheory.Mum.FactorSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAutomorphismCongrOneModDetEqOne
section
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem det_eq_one_of_congMod (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X ≃+ X) (m : ℕ)
    (hm : 3 ≤ m) (hk : ∀ x, CongMod m (k x) x) :
    LinearMap.det (k.toIntLinearEquiv : X →ₗ[ℤ] X) = 1 := by
  set f : X ≃ₗ[ℤ] X := k.toIntLinearEquiv
  have hu : IsUnit (LinearMap.det (f : X →ₗ[ℤ] X)) := LinearEquiv.isUnit_det' f
  let b := Module.Free.chooseBasis ℤ X
  set M := LinearMap.toMatrix b b (f : X →ₗ[ℤ] X) with hM
  have hdet : M.det = LinearMap.det (f : X →ₗ[ℤ] X) := LinearMap.det_toMatrix b _
  have hmap : (Int.castRingHom (ZMod m)).mapMatrix M = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hk (b j)
    have hfb : (f : X →ₗ[ℤ] X) (b j) = k (b j) := rfl
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hM, LinearMap.toMatrix_apply, hfb, hw, map_add (f := _), map_nsmul,
      Finsupp.add_apply, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, Matrix.one_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hz : ((LinearMap.det (f : X →ₗ[ℤ] X) : ℤ) : ZMod m) = 1 := by
    rw [← hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod m)) M
    rw [hmap, Matrix.det_one] at this
    simpa using this
  rcases Int.isUnit_iff.mp hu with h | h
  · exact h
  · exfalso
    rw [h] at hz
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by
      have e : ((2 : ℕ) : ZMod m) = 1 - ((-1 : ℤ) : ZMod m) := by push_cast; ring
      rw [e, hz, sub_self]
    have hd := (ZMod.natCast_eq_zero_iff 2 m).mp h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Special

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem lbIso_pull' {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem main : ∀ (R₁ R₂ O K F₁ F₂ M Γ : Type) [CommRing R₁] [CommRing R₂] [CommRing O] [Field K] [Field F₁] [Field F₂] [Algebra F₁ K] [Algebra F₂ K] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), (∃ (P : PolAV (Sp O)) (b₁ : P.A.left ⟶ P₁.A.left) (b₂ : P.A.left ⟶ P₂.A.left), IsGrpPullback P.A P₁.A (spMap f₁) b₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) b₂ ∧ LBIso P.L (P₁.L.pull b₁) ∧ LBIso P.L (P₂.L.pull b₂) ∧ (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ b₁ = b₁ ≫ (e₁ E).left ∧ e.left ≫ b₂ = b₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp O ⟶ P.A.left, w ≫ P.A.hom = 𝟙 _ ∧ w ≫ b₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ b₂ = spMap f₂ ≫ (t₂ x).left) → ∀ (v : O →+* K) (k₁ : R₁ →+* F₁) (k₂ : R₂ →+* F₂), (algebraMap F₁ K).comp k₁ = v.comp f₁ → (algebraMap F₂ K).comp k₂ = v.comp f₂ → ∀ (A₁ : PolAV (Sp F₁)) (A₂ : PolAV (Sp F₂)) (φ₁ : A₁.A.left ⟶ P₁.A.left) (φ₂ : A₂.A.left ⟶ P₂.A.left), IsGrpPullback A₁.A P₁.A (spMap k₁) φ₁ → IsGrpPullback A₂.A P₂.A (spMap k₂) φ₂ → LBIso A₁.L (P₁.L.pull φ₁) → LBIso A₂.L (P₂.L.pull φ₂) → ∃ (P₀ : PolAV (Sp K)) (a₁ : P₀.A.left ⟶ A₁.A.left) (a₂ : P₀.A.left ⟶ A₂.A.left), IsGrpPullback P₀.A A₁.A (spMap (algebraMap F₁ K)) a₁ ∧ IsGrpPullback P₀.A A₂.A (spMap (algebraMap F₂ K)) a₂ ∧ LBIso P₀.L (A₁.L.pull a₁) ∧ LBIso P₀.L (A₂.L.pull a₂) ∧ (∀ x, ∃ w : Sp K ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a₁ ≫ φ₁ = spMap (v.comp f₁) ≫ (t₁ x).left ∧ w ≫ a₂ ≫ φ₂ = spMap (v.comp f₂) ≫ (t₂ x).left) ∧ ∀ (E : M) (w w₂ : Sp K ⟶ P₀.A.left), w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a₁ ≫ φ₁ = w ≫ a₁ ≫ φ₁ ≫ (e₁ E).left → w₂ ≫ a₂ ≫ φ₂ = w ≫ a₂ ≫ φ₂ ≫ (e₂ E).left := by
  intro R₁ R₂ O K F₁ F₂ M Γ _ _ _ _ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ hS v k₁ k₂ hk₁ hk₂ A₁ A₂ φ₁ φ₂ hA₁ hA₂ hL₁ hL₂
  obtain ⟨P, b₁, b₂, hb₁, hb₂, hPL₁, hPL₂, he, ht⟩ := hS
  let P₀ : PolAV (Sp K) := GlobalTheory.StrictPull.polPull P (spMap v)
  let β : P₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap v)
  have hβ : IsGrpPullback P₀.A P.A (spMap v) β := isGrpPullback_pullback P.A (spMap v)
  have eq₁ : spMap (algebraMap F₁ K) ≫ spMap k₁ = spMap v ≫ spMap f₁ := by rw [spc, spc, hk₁]
  have eq₂ : spMap (algebraMap F₂ K) ≫ spMap k₂ = spMap v ≫ spMap f₂ := by rw [spc, spc, hk₂]
  have c₁ := hβ.comp hb₁
  have c₂ := hβ.comp hb₂
  have w₁ : (β ≫ b₁) ≫ P₁.A.hom = (P₀.A.hom ≫ spMap (algebraMap F₁ K)) ≫ spMap k₁ := by
    rw [c₁.1.w, Category.assoc, eq₁]
  have w₂ : (β ≫ b₂) ≫ P₂.A.hom = (P₀.A.hom ≫ spMap (algebraMap F₂ K)) ≫ spMap k₂ := by
    rw [c₂.1.w, Category.assoc, eq₂]
  let a₁ : P₀.A.left ⟶ A₁.A.left := hA₁.1.lift _ _ w₁
  let a₂ : P₀.A.left ⟶ A₂.A.left := hA₂.1.lift _ _ w₂
  have ha₁ : a₁ ≫ φ₁ = β ≫ b₁ := hA₁.1.lift_fst _ _ w₁
  have ha₂ : a₂ ≫ φ₂ = β ≫ b₂ := hA₂.1.lift_fst _ _ w₂
  have ga₁ : IsGrpPullback P₀.A A₁.A (spMap (algebraMap F₁ K)) a₁ :=
    IsGrpPullback.cancel hA₁ (c₁.congr eq₁.symm ha₁.symm) (hA₁.1.lift_snd _ _ w₁)
  have ga₂ : IsGrpPullback P₀.A A₂.A (spMap (algebraMap F₂ K)) a₂ :=
    IsGrpPullback.cancel hA₂ (c₂.congr eq₂.symm ha₂.symm) (hA₂.1.lift_snd _ _ w₂)
  have hP₀L : P₀.L = P.L.pull β := rfl
  refine ⟨P₀, a₁, a₂, ga₁, ga₂, ?_, ?_, fun x => ?_, fun E w w₂' hw hw₂ h => ?_⟩
  · rw [hP₀L]
    exact LBIso.trans (pull_isLB P.isLB _) (pull_isLB P₁.isLB _) (pull_isLB A₁.isLB _)
      (lbIso_pull' hPL₁ β rfl) (lbIso_pull' hL₁ a₁ ha₁.symm).symm
  · rw [hP₀L]
    exact LBIso.trans (pull_isLB P.isLB _) (pull_isLB P₂.isLB _) (pull_isLB A₂.isLB _)
      (lbIso_pull' hPL₂ β rfl) (lbIso_pull' hL₂ a₂ ha₂.symm).symm
  · obtain ⟨wO, hs, h₁, h₂⟩ := ht x
    have sq : (spMap v ≫ wO) ≫ P.A.hom = 𝟙 _ ≫ spMap v := by
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
    have hl : pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β = spMap v ≫ wO := pullback.lift_fst _ _ _
    refine ⟨pullback.lift (spMap v ≫ wO) (𝟙 _) sq, pullback.lift_snd _ _ _, ?_, ?_⟩
    · calc pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ a₁ ≫ φ₁ = pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β ≫ b₁ := congrArg (fun z => pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ z) ha₁
        _ = (pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β) ≫ b₁ := (Category.assoc _ _ _).symm
        _ = _ := by rw [hl, Category.assoc, h₁, ← Category.assoc, spc]
    · calc pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ a₂ ≫ φ₂ = pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β ≫ b₂ := congrArg (fun z => pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ z) ha₂
        _ = (pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β) ≫ b₂ := (Category.assoc _ _ _).symm
        _ = _ := by rw [hl, Category.assoc, h₂, ← Category.assoc, spc]
  · obtain ⟨e, he₁, he₂⟩ := he E
    have sqe : (β ≫ e.left) ≫ P.A.hom = P₀.A.hom ≫ spMap v := by
      rw [Category.assoc, Over.w e]; exact pullback.condition
    let e₀ : P₀.A.left ⟶ P₀.A.left := pullback.lift (β ≫ e.left) P₀.A.hom sqe
    have he₀ : e₀ ≫ β = β ≫ e.left := pullback.lift_fst _ _ _
    have he₀' : e₀ ≫ P₀.A.hom = P₀.A.hom := pullback.lift_snd _ _ _
    have key : w₂' = w ≫ e₀ := by
      apply c₁.1.hom_ext
      · calc w₂' ≫ β ≫ b₁ = w₂' ≫ a₁ ≫ φ₁ := by rw [ha₁]
          _ = w ≫ a₁ ≫ φ₁ ≫ (e₁ E).left := h
          _ = w ≫ (a₁ ≫ φ₁) ≫ (e₁ E).left := by simp only [Category.assoc]
          _ = w ≫ β ≫ (b₁ ≫ (e₁ E).left) := by rw [ha₁, Category.assoc]
          _ = w ≫ (β ≫ e.left) ≫ b₁ := by rw [← he₁, Category.assoc]
          _ = (w ≫ e₀) ≫ β ≫ b₁ := by rw [← he₀]; simp only [Category.assoc]
      · rw [hw₂, Category.assoc, he₀', hw]
    calc w₂' ≫ a₂ ≫ φ₂ = (w ≫ e₀) ≫ β ≫ b₂ := by rw [key, ha₂]
      _ = w ≫ (e₀ ≫ β) ≫ b₂ := by simp only [Category.assoc]
      _ = w ≫ β ≫ (e.left ≫ b₂) := by rw [he₀, Category.assoc]
      _ = w ≫ (β ≫ b₂) ≫ (e₂ E).left := by rw [he₂]; simp only [Category.assoc]
      _ = w ≫ a₂ ≫ φ₂ ≫ (e₂ E).left := by rw [← ha₂]; simp only [Category.assoc]

end GlobalTheory.Poinc.Special
end
end

