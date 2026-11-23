module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem admissibleBase_powerSeries (k : Type) [Field k] : Out.AdmBase (PowerSeries k) (Ideal.span {PowerSeries.X}) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  have : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]; infer_instance
  have h := ReciprocityTheory.P1.isAdicComplete_ps (R := k)
  rwa [PowerSeries.maximalIdeal_eq_span_X] at h

theorem specOf_id (R : Type) [CommRing R] : Out.specOf (RingHom.id R) = 𝟙 _ := by
  simp [Out.specOf]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


set_option maxHeartbeats 1600000 in
theorem ArcWit.uwMove (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W W' : ArcWit Y a I f u χ) (ψ : W.t.G ≅ W'.t.G)
    [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ W'.m.φ = W.m.φ) (hact : ∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) :
    ∃ (bc : W.t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W'.t.G) (D'' : Out.DegData R I)
      (hD : Out.IsPullDeg (RingHom.id R) W'.P.D.toPre D''.toPre) (U'' : Out.Unif I D'' W'.P.A W.t.G)
      (_ : Module (𝓞 E) D''.toPre.X) (oD : letI := H.starRing; D''.toPre.OAct (𝓞 E)),
      IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = ψ.hom.left ∧
      U''.LG = W.P.U.LG ∧
      U''.gen.hom.left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
        pullback.fst W.t.G.hom (Out.jK R) ≫ ψ.hom.left ∧
      Out.IsPullUnif (RingHom.id R) hD bc W'.P.U U'' ∧
      (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, oD.onB.act x ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.P.oD.onB.act x)) ∧
      (letI := H.starRing; U''.toUnifPre.OLinear (𝓞 E) oD W'.P.oA W.t.act.toRingAct) ∧
      (letI := H.starRing; TraceFormTwistIso D''.toPre oD H.w0) := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback W.t.G W'.t.G (Out.specOf (RingHom.id R)) ψ.hom.left :=
    (isGrpPullback_of_iso ψ).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback W'.t.G (Out.specOf (RingHom.id R)))
  have gpG : IsGrpPullback W'.P.A.A W'.t.G (Out.jK R) (W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R)) := by
    have := W'.P.U.gen_hom
    have : IsMonHom W'.P.U.gen.symm.hom := by show IsMonHom W'.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso W'.P.U.gen.symm).comp (isGrpPullback_pullback W'.t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (Out.jK R)).obj W.t.G) W'.t.G (Out.jK R)
      (pullback.fst W.t.G.hom (Out.jK R) ≫ ψ.hom.left) :=
    ((isGrpPullback_pullback W.t.G (Out.jK R)).comp (isGrpPullback_of_iso ψ)).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : W'.P.U.gen.inv.left ≫ W'.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (W'.P.A.L.pull eA.hom.left) (W'.P.U.LG.L.pull (pullback.fst W.t.G.hom (Out.jK R) ≫ bc.hom.left ≫
      pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ W'.P.U.gen.inv.left)
      (chartPullSame W'.P.A.L (fun _ => eA.hom.left) (fun _ => W'.P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame W'.P.U.LG.L _ (fun _ => pullback.fst W'.t.G.hom (Out.jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) W'.P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr W'.P.bundle (CubeMap.ofHom ψ.hom) (sabMap_cubical W.m W'.m ψ hφ) hbc
    (e := Out.specOf (RingHom.id R)) hs
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR W'.P.D
  have hgen : (Out.specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI W'.P.D W'.P.A W'.t.G W'.t.semi W'.P.U
    Wo hψW hgen W.t.G bc mbc W'.P.A rfl eA mE wA W.t.PP wL' he' gL rL
  have hbcact : ∀ x, W.t.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫
          pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = pullback.fst _ _ ≫ (W'.t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (W.t.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc,
        ← Over.comp_left, hact, Over.comp_left]
    · exact (Over.w (W.t.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x))).symm
  have actA : ∀ x, (W'.P.oA.act x).left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
      W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) ≫ (W'.t.act.act x).left := by
    intro x
    have e : W'.P.oA.act x ≫ W'.P.U.gen.inv = W'.P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (W'.t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (W'.P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (Out.jK R)).map (W.t.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ W'.P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (Out.jK R)).map (W.t.act.act x)).left ≫ pullback.fst W.t.G.hom (Out.jK R) =
          pullback.fst W.t.G.hom (Out.jK R) ≫ (W.t.act.act x).left := pullback.lift_fst _ _ _
      have a₃ : (W.t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (W'.t.act.act x).left := by
        rw [← Over.comp_left, hact, Over.comp_left]
      show ((Over.pullback (Out.jK R)).map (W.t.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ W'.P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, el, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) W'.P.D W'.P.A W'.t.G W'.P.U
    W.t.G bc mbc W'.P.A D'' hD U'' hPU (𝓞 E) W'.P.oD W'.P.oA W'.t.act.toRingAct W'.P.lin W.t.act.toRingAct hbcact
    W'.P.oA extA
  refine ⟨bc, D'', hD, U'', mod'', oD'', mbc, hbc, hLG.trans W.P.bundle.symm, ?_, hPU, xl, el, lin'', w0'' H.w0 W'.P.w0⟩
  rw [hgenU]; exact heA

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def WitData {k : Type} [Field k] {b : O →+* k} (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) : Prop :=
  letI := H.starRing
  IsGrpPullback P.toPre.P.A a.D₀.P.A (spMap (PowerSeries.C (R := k))) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.toPre.P.A) (fun _ => 1)) P.toPre.rig
      (rigPullOf φ (spMap (PowerSeries.C (R := k))) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (oP.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ y, (P.toPre.c (e y)).left ≫ φ = spMap (PowerSeries.C (R := k)) ≫ (a.D₀.c y).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (uF : F),
      (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
      uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
      ∀ y, GenRel w (LB.pullGen _ _ _ (P.toPre.psi (e y)) (Out.jFK (R := PowerSeries k) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := k) F)) (uF ^ (a.be y y / 2))

def QkToAkInjSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), Out.AdmBase R I →
  ∀ (Dd : Out.DegData R I) (A : Out.PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Out.Unif I Dd A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (n : ℕ), 1 ≤ n → ∀ (p p' : Out.QkPt Dd.toPre F n) (x : Out.TFK (R := R) F ⟶ A.A),
      Out.QkToAkU U.toUnifPre F n p x → Out.QkToAkU U.toUnifPre F n p' x → Out.QkPt.Equiv Dd.toPre F p p'

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSOfIdToRingHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Dual

variable {S : Type} [CommRing S] (s : S)

abbrev dAway : DualNumber S →+* DualNumber (Localization.Away s) := dualMapR (algebraMap S (Localization.Away s))

theorem eq_inl_add_inr {R : Type} [CommRing R] (x : DualNumber R) :
    x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * TrivSqZeroExt.inr 1 := by
  ext <;> simp

theorem dAway_eps : dAway s (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1 := by
  ext <;> simp [dAway, dualMapR]

theorem dAway_inl (a : S) : dAway s (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (algebraMap S _ a) := by
  ext <;> simp [dAway, dualMapR]

theorem dAway_ext {T : Type} [CommRing T] {χ₁ χ₂ : DualNumber (Localization.Away s) →+* T}
    (h : χ₁.comp (dAway s) = χ₂.comp (dAway s)) : χ₁ = χ₂ := by
  have hinl : χ₁.comp (TrivSqZeroExt.inlHom _ _) = χ₂.comp (TrivSqZeroExt.inlHom _ _) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    refine RingHom.ext fun a => ?_
    have h1 := RingHom.congr_fun h (TrivSqZeroExt.inl a)
    simp only [RingHom.comp_apply, dAway_inl] at h1
    simpa using h1
  have heps : χ₁ (TrivSqZeroExt.inr 1) = χ₂ (TrivSqZeroExt.inr 1) := by
    have h1 := RingHom.congr_fun h (TrivSqZeroExt.inr 1)
    simp only [RingHom.comp_apply, dAway_eps] at h1
    exact h1
  refine RingHom.ext fun x => ?_
  have h1 := RingHom.congr_fun hinl x.fst
  have h2 := RingHom.congr_fun hinl x.snd
  simp only [RingHom.comp_apply, TrivSqZeroExt.inlHom_apply] at h1 h2
  rw [eq_inl_add_inr x, map_add (f := _), map_add (f := _), map_mul, map_mul, heps, h1, h2]

theorem dAway_lift {T : Type} [CommRing T] (gg : DualNumber S →+* T) (hu : IsUnit (gg (TrivSqZeroExt.inl s))) :
    ∃ χ : DualNumber (Localization.Away s) →+* T, χ.comp (dAway s) = gg := by
  let g0 : S →+* T := gg.comp (TrivSqZeroExt.inlHom S S)
  have hu0 : IsUnit (g0 s) := hu
  let φ : Localization.Away s →+* T := IsLocalization.Away.lift s hu0
  have hφ : ∀ a : S, φ (algebraMap S _ a) = gg (TrivSqZeroExt.inl a) := fun a =>
    IsLocalization.lift_eq _ a
  let e := gg (TrivSqZeroExt.inr 1)
  have he : e * e = 0 := by
    simp only [e, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
  refine ⟨{ toFun := fun x => φ x.fst + φ x.snd * e
            map_one' := by simp
            map_mul' := fun x y => by
              simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
                MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_add, map_mul]
              linear_combination (-(φ x.snd * φ y.snd)) * he
            map_zero' := by simp
            map_add' := fun x y => by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add (f := _)]; ring }, ?_⟩
  refine RingHom.ext fun x => ?_
  conv_rhs => rw [eq_inl_add_inr x]
  simp only [RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, dAway, dualMapR,
    TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add, map_add, map_mul, hφ]
  simp only [zero_mul, add_zero, e]

end Dual

section Iso

variable {S : Type} [CommRing S] (s : S)

abbrev Ld : Type := Localization.Away (TrivSqZeroExt.inl s : DualNumber S)

theorem isUnit_dAway : IsUnit (dAway s (TrivSqZeroExt.inl s)) := by
  rw [dAway_inl]
  exact (IsLocalization.Away.algebraMap_isUnit s).map (TrivSqZeroExt.inlHom _ _)

def toL : DualNumber (Localization.Away s) →+* Ld s :=
  (dAway_lift s (algebraMap (DualNumber S) (Ld s)) (IsLocalization.Away.algebraMap_isUnit _)).choose

theorem toL_comp : (toL s).comp (dAway s) = algebraMap (DualNumber S) (Ld s) :=
  (dAway_lift s (algebraMap (DualNumber S) (Ld s)) (IsLocalization.Away.algebraMap_isUnit _)).choose_spec

def fromL : Ld s →+* DualNumber (Localization.Away s) :=
  IsLocalization.Away.lift (TrivSqZeroExt.inl s) (isUnit_dAway s)

theorem fromL_comp : (fromL s).comp (algebraMap (DualNumber S) (Ld s)) = dAway s :=
  IsLocalization.lift_comp _

theorem fromL_toL : (fromL s).comp (toL s) = RingHom.id _ := by
  apply dAway_ext s
  rw [RingHom.comp_assoc, toL_comp, fromL_comp, RingHom.id_comp]

end Iso

section Glue

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in
theorem glue_tan {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G) (hw : ∀ k, TanS (w k))
    (hc : ∀ k l (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (s k)) →+* T)
      (β : DualNumber (Localization.Away (s l)) →+* T), α.comp (dAway (s k)) = β.comp (dAway (s l)) →
      Spec.map (CommRingCat.ofHom α) ≫ (w k).left = Spec.map (CommRingCat.ofHom β) ≫ (w l).left) :
    ∃ v : sp (R₀ := S) (DualNumber S) ⟶ G, TanS v ∧
      ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := by
  have hs' : Ideal.span (Set.range (fun k => (TrivSqZeroExt.inl (s k) : DualNumber S))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom S S)) hs
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber S)) _ hs').openCover
  let f : ∀ k, 𝒰.X k ⟶ G.left := fun k => Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left
  have hf : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ f k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ f l := by
    refine fun (k : Fin n) (l : Fin n) => Scheme.Cover.hom_ext (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.openCover _ _
      fun (i : (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.I₀) => ?_
    let a : Spec ((pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i) ⟶ pullback (𝒰.f k) (𝒰.f l) :=
      (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.f i
    let A : CommRingCat.of (Ld (s k)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.fst (𝒰.f k) (𝒰.f l))
    let B : CommRingCat.of (Ld (s l)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.snd (𝒰.f k) (𝒰.f l))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s l))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc]
      exact congrArg (a ≫ ·) pullback.condition
    have key : A.hom.comp (algebraMap (DualNumber S) (Ld (s k))) = B.hom.comp (algebraMap (DualNumber S) (Ld (s l))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hkey : (A.hom.comp (toL (s k))).comp (dAway (s k)) = (B.hom.comp (toL (s l))).comp (dAway (s l)) := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, toL_comp, toL_comp]
      exact key
    have h := hc k l _ (A.hom.comp (toL (s k))) (B.hom.comp (toL (s l))) hkey
    show a ≫ pullback.fst (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left =
      a ≫ pullback.snd (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (s l))) ≫ (w l).left
    rw [← Category.assoc a, ← Category.assoc a, ← ea, ← eb, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    exact h
  let g := 𝒰.glueMorphisms f hf
  have hι : ∀ k : Fin n, 𝒰.f k ≫ g = f k := fun k => Scheme.Cover.ι_glueMorphisms 𝒰 f hf k
  have hg : ∀ k : Fin n, Spec.map (CommRingCat.ofHom (dAway (s k))) ≫ g = (w k).left := by
    intro k
    have e : Spec.map (CommRingCat.ofHom (dAway (s k))) = Spec.map (CommRingCat.ofHom (fromL (s k))) ≫ 𝒰.f k := by
      show _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k))))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_comp]
    rw [e, Category.assoc, hι k]
    show Spec.map (CommRingCat.ofHom (fromL (s k))) ≫ Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_toL, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp]
  have hover : g ≫ G.hom = (sp (R₀ := S) (DualNumber S)).hom := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : Fin n) => ?_
    rw [← Category.assoc, hι k]
    show (Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (DualNumber S)))
    rw [Category.assoc, Over.w (w k)]
    show Spec.map (CommRingCat.ofHom (toL (s k))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (DualNumber (Localization.Away (s k))))) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← toL_comp, RingHom.comp_assoc]
    congr 1
    refine RingHom.ext fun r => ?_
    simp [TrivSqZeroExt.algebraMap_eq_inl', dAway_inl]
  let v : sp (R₀ := S) (DualNumber S) ⟶ G := Over.homMk g hover
  have hres : ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := fun k =>
    Over.OverMorphism.ext (hg k)
  refine ⟨v, ?_, hres⟩
  apply Over.OverMorphism.ext
  let 𝒱 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) _ hs).openCover
  refine Scheme.Cover.hom_ext 𝒱 _ _ fun (k : Fin n) => ?_
  have e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
        (spMap (TrivSqZeroExt.fstHom S S S)).left =
      (spMap (TrivSqZeroExt.fstHom S (Localization.Away (s k)) (Localization.Away (s k)))).left ≫
        (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k))))).left := by
    rw [spMap_left, spMap_left, spMap_left, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (dualMapS_fst (Algebra.ofId S (Localization.Away (s k))) x).symm
  have h1 := congrArg (fun q => Over.Hom.left q) (hw k)
  simp only [Over.comp_left] at h1
  show Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
      ((spMap (TrivSqZeroExt.fstHom S S S)).left ≫ v.left) =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫ (1 : sp (R₀ := S) S ⟶ G).left
  rw [← Category.assoc, e1, Category.assoc]
  have h2 : (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k))))).left ≫ v.left = (w k).left :=
    congrArg (fun q => Over.Hom.left q) (hres k)
  rw [h2, h1, one_left', one_left']
  show (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k))))) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap S S)) ≫ _)
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Algebra.algebraMap_self, RingHom.comp_id]

end Glue

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

