module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcGenericFibrePointsBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstPtsAddSmul
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts
open ConstGrp

theorem constPts_add_smul : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , (∀ v v', Ξ.x (v + v') = Ξ.x v * Ξ.x v') ∧ ∀ (e : 𝓞 E) v, Ξ.x (Λ.A.actV e v) = Ξ.x v ≫ W.t.act.act e := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  obtain ⟨hadd, -, hact⟩ := _root_.GlobalTheory.ArcPts.ex0_additive_surjective_equivariant hL hL2 E H D l c O β b a Λ
  have hG := hL.globalFns
  obtain ⟨gp, hw, -, ho, -, -⟩ := W.spec
  have hw' := (isGen_iff _).1 hw
  have hb : ∀ v, (Ξ.g v).b.left ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.ex0 v).b.left :=
    fun v => (Ξ.g_rel v 0).1 2
  let ρ : Over.mk (selfR.hom ≫ spMap (PowerSeries.C (R := ℂ))) ⟶ Out.TF (R := ℂ) ℂ :=
    Over.homMk (spMap (PowerSeries.C (R := ℂ))) (by
      rw [← Over.w (Λ.ex0 0).b]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hb 0).symm).trans ?_)
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) gp.1.w).trans ?_)
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (Ξ.g 0).b)))
  have r : ∀ v, Rel gp W.w W.e ρ (Ξ.g v) (Λ.ex0 v) := fun v =>
    rel_of_pmaps (fun x => (Ξ.g_rel v x).1) fun x =>
      pmaps_of_genRelR hw' W.P.D.toPre.P.isLB a.D₀.P.isLB ((Ξ.g v).isGen _)
        (DVR.pullGen_isGen _ _ _ _ ((Λ.ex0 v).isGen x) _) (Ξ.g_rel v x)
  have hc : ∀ x, pushHom gp selfR (DVR.cP W.P.D.toPre selfR (W.e x)) = ρ ≫ DVR.cP a.D₀ _ x := fun x =>
    Over.OverMorphism.ext ((Ξ.g_rel 0 x).1 1)
  have : IsHausdorff ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
    infer_instance
  refine ⟨fun v v' => (Ξ.x_pt (v + v')).unique (((Ξ.x_pt v).mul hG (Ξ.x_pt v')
    (isAdd_of_rel hG hw' hc W.e.surjective (r v) (r v') (r (v + v')) (hadd v v')))), fun e v => ?_⟩
  have hs := hact e v
  clear hact hadd
  have r₁ := r v
  have r₂ := r (Λ.A.actV e v)
  have x₁ := Ξ.x_pt v
  have x₂ := Ξ.x_pt (Λ.A.actV e v)
  letI := H.starRing
  exact x₂.unique (x₁.smul hG W.P.lin e
    (isSmulPt_of_rel hG hw' hc W.e.surjective W.P.oD a.oa (fun s x => W.e.map_smul s x) ho e r₁ r₂ hs))

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqSpMapOfInjective
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPoint

theorem eq_spMap_of_injective {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (i : A →+* B)
    (hi : Function.Injective i) (x : Sp A ⟶ Sp K) (ρ : K →+* A) (h : spMap i ≫ x = spMap (i.comp ρ)) :
    x = spMap ρ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  have h' : Spec.map (φ ≫ CommRingCat.ofHom i) = Spec.map (CommRingCat.ofHom (i.comp ρ)) := by
    rw [Spec.map_comp]; exact h
  have h2 := Spec.map_injective h'
  congr 1
  ext k
  exact hi (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) k)

theorem sumsAt_of_halfRing {K F : Type} [CommRing K] [CommRing F] {X Y : Scheme.{0}} (s : X ⟶ Sp K) (κ : K →+* F)
    (bF : F →+* ℂ) (j : pullback s (spMap κ) ⟶ Y) (χ : Sp ℂ⟦X⟧ ⟶ Y) (y : Sp ℂ⸨X⸩ ⟶ pullback s (spMap κ))
    (hj : y ≫ j = spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) ≫ χ)
    (hs : y ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ X)
    (hT : spMap (Conv.halfRing T).val.toRingHom ≫ yT = y ≫ pullback.fst _ _)
    (U : Y.Opens) (f : Γ(Y, U)) (hU : ⊤ ≤ χ ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ∀ z : Sp ℂ ⟶ pullback s (spMap κ),
      z ≫ pullback.fst _ _ = spMap (Conv.ev T w hw).toRingHom ≫ yT → z ≫ pullback.snd _ _ = spMap bF →
      ⊤ ≤ (z ≫ j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (z ≫ j) U f) := by
  have hval : (Conv.halfRing T).val.toRingHom.comp ((algebraMap ℂ (Conv.halfRing T)).comp bF) =
      (algebraMap ℂ ℂ⸨X⸩).comp bF := RingHom.ext fun _ => rfl
  have hover : yT ≫ s = spMap ((algebraMap ℂ (Conv.halfRing T)).comp bF) ≫ spMap κ := by
    rw [← spMap_comp]
    refine eq_spMap_of_injective (Conv.halfRing T).val.toRingHom Subtype.val_injective _ _ ?_
    rw [← Category.assoc, hT, Category.assoc, pullback.condition, ← Category.assoc, hs, ← spMap_comp,
      ← RingHom.comp_assoc, hval]
  let yF : Sp (Conv.halfRing T) ⟶ pullback s (spMap κ) := pullback.lift yT _ hover
  have hgen : spMap (Conv.halfRing T).val.toRingHom ≫ yF = y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hT]
    · rw [Category.assoc, pullback.lift_snd, hs, ← spMap_comp, hval]
  obtain ⟨T', hle, hw'⟩ := Conv.exists_sumsAt_halfCurve (yT := yF ≫ j) (χ := χ) rfl (RingHom.id _) (by
    rw [RingHom.id_comp, RingHom.id_comp, ← hj, ← hgen, Category.assoc, ← Category.assoc (spMap _) (spMap _),
      ← spMap_comp]
    rfl) hU
  refine ⟨T', hle, fun w hw hw2 z hz1 hz2 => ?_⟩
  have hz : z = spMap (Conv.ev T w hw).toRingHom ≫ yF := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hz1]
    · rw [Category.assoc, pullback.lift_snd, hz2, ← spMap_comp]
      congr 2
      ext x
      exact ((Conv.ev T w hw).commutes (bF x)).symm
  have hzj : z ≫ j = Conv.halfCurve (yF ≫ j) w := by
    rw [hz, Conv.halfCurve_eq _ hw, Category.assoc]
    rfl
  rw [hzj]
  exact ⟨(hw' w hw2).1, (hw' w hw2).2 f⟩

theorem point_sumsAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), ∀ (U : Y.X.Opens) (f : Γ(Y.X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u K.i (K.Pw w) → yF ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (yF ≫ Y.j) U f) := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K U f hU
  obtain ⟨T', hle, h⟩ := sumsAt_of_halfRing Xo.s _ bF Y.j χ C.yF C.yF_j C.yF_over Ψ.yT Ψ.yT_gen U f hU
  refine ⟨max T' K.T, fun w hw z hz1 hz2 => ?_⟩
  have h1 : T' < w.im := (le_max_left _ _).trans_lt hw
  have h2 : Ψ.T < w.im := hle.trans_lt h1
  exact h w h2 h1 z (hz1.trans ((K.u_eq w ((le_max_right _ _).trans_lt hw)).trans (Ψ.yw_eq w h2))) hz2

end GlobalTheory.ArcPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcGenericFibrePointsBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcGenericFibrePoints_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (F : Type) [Field F] (f : ℂ⸨X⸩ →+* F) (φ : ∀ j, (Σ α : A.X, A.Theta j α) → A.V → F), AnFin A → (∀ (j : ℕ) [NeZero j] i v, φ j i v = f (A.FSum j i.1 i.2 v)) → ∃ Θ : FPts (I := fun j => Σ α : A.X, A.Theta j α) (fun e v => A.actV e v) t (spMap f ≫ y) φ, (∀ v, (Θ.x v).left = spMap f ≫ (Φ.x v).left ∧ ∀ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ t.PP.L.U j → Θ.τ v j = f (Φ.τ v j)) ∧ ∀ (k : ℕ) [NeZero k] (ξ : 𝟙_ (Over S) ⟶ t.G) (la : A.La) (ψ : (Σ α : A.X, A.Theta k α) → A.V → ℂ⸨X⸩), Φ.LevelPt k (toUnit _ ≫ ξ) la → (∀ i z, IsFShift A k i.1 i.2 la z (ψ i z)) → Θ.Lev k (toUnit _ ≫ ξ) (fun i z => f (ψ i z)) := by
  first | exact @GlobalTheory.ArcBaseChange.exists_fpts_baseChange | exact GlobalTheory.ArcBaseChange.exists_fpts_baseChange | (intros; apply GlobalTheory.ArcBaseChange.exists_fpts_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCharacterRatioExpMulStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonvanishing_multiplicative_ratio : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → ∃ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u ∧ (∀ x z, u x z ≠ 0) ∧ ∀ x z z', u x (z + z') = u x z * u x z' := by
  first | exact @GlobalTheory.AbelianLetters.exists_isRatio_mul | exact GlobalTheory.AbelianLetters.exists_isRatio_mul | (intros; apply GlobalTheory.AbelianLetters.exists_isRatio_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GtRep

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_rep_and_shift : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (k : ℕ), 1 ≤ k → (∀ p, ∃ la, Λ.Rep k p la) ∧ ∀ p la e, Λ.Rep k p la → ∃ q : Out.QkPt a.D₀ ℂ k, q.y = Λ.ε (la + k • e).y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)) ∧ ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ q q' := by
  intro h1 h2 E _ _ _ H _ D l c O _ β _ _ b a Λ k hk
  obtain ⟨hadd, hsurj, -⟩ := _root_.GlobalTheory.ArcPts.ex0_additive_surjective_equivariant h1 h2 E H D l c O β b a Λ
  obtain ⟨hker, hio, -⟩ := _root_.GlobalTheory.ArcPts.GtKer.ker_iota_torus E H D l c O β b a Λ
  have hB := a.bimult
  let ex : Λ.A.V →+ Out.GtPtF a.D₀ ℂ :=
    AddMonoidHom.mk' Λ.ex0 fun z z' => (isAdd_iff_eq _ _ _).1 (hadd z z')
  have hex : ∀ z, Λ.ex0 z = ex z := fun _ => rfl
  have hio' : ∀ la : Λ.A.La, ex (Λ.A.P0 la) = iota hB ℂ (Λ.ε la.y) := fun la => (isIota_iff_eq hB _ _).1 (hio la)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hf : (algebraMap (FractionRing ℂ) ℂ).comp (algebraMap (FractionRing ℂ) (FractionRing ℂ)) =
      algebraMap (FractionRing ℂ) ℂ := RingHom.ext fun _ => rfl
  have hkk : ∀ v : Λ.A.V, (k : ℂ)⁻¹ • k • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hkk' : ∀ v : Λ.A.V, k • (k : ℂ)⁻¹ • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  refine ⟨fun p => ?_, fun p la e hrep => ?_⟩
  · obtain ⟨q, -, huniq⟩ := existsUnique_qkExt hB _ hf p
    obtain ⟨z, hz⟩ := hsurj q.g
    let l0 : Λ.A.La := AnArc.La.mk (Λ.ε.symm q.y) 0 0
    have hl0 : Λ.ε l0.y = q.y := Λ.ε.apply_symm_apply _
    have hzero : (Λ.ex0 (k • z - Λ.A.P0 l0)).IsZero := by
      rw [isZero_iff_eq, hex, map_sub, map_nsmul, ← hex z, hz, qk_nsmul hB, hio', hl0, sub_self]
    obtain ⟨l1, hl1, hl1'⟩ := (hker _).1 hzero
    refine ⟨l1 + l0, fun q' hq' => ?_⟩
    obtain rfl := huniq q' hq'
    refine ⟨by rw [AnArc.La.add_y, hl1, zero_add, hl0], ?_⟩
    rw [map_add (f := _), ← hl1', sub_add_cancel, hkk, hz]
  · refine ⟨qkMk hB (Λ.ε (la + k • e).y) (Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)))
      (by rw [hex, ← map_nsmul, hkk', hio']), rfl, rfl, fun q' hq' => ?_⟩
    obtain ⟨hy, hg⟩ := hrep q' hq'
    refine equiv_symm hB ((equiv_iff hB _ _).2 ⟨Λ.ε e.y, ?_, ?_⟩)
    · rw [qkMk_y, hy, AnArc.La.add_y, AnArc.La.nsmul_y, map_add (f := _), map_nsmul]
    · rw [qkMk_g, hg, hex, hex, map_add (f := _), map_nsmul, smul_add, hkk, map_add (f := _), hio']

end GlobalTheory.GtRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRigidifiedIsoAgreeAbelianFibres
section
noncomputable section

namespace GlobalTheory.RigIso

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem gm_eq_of_eq_along_section {Y Z T : Scheme.{0}} {N : LB Y} (hN : ∀ y : Y, ∃ i, y ∈ N.U i)
    (q : Z ⟶ Y) (p : Z ⟶ T) (e : T ⟶ Z) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {t₁ t₂ : LB.Gen N} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen)
    (h : ∀ (s : T) (i : N.ι), (e ≫ q) s ∈ N.U i → gm (e ≫ q) s (N.U i) (t₁.s i) = gm (e ≫ q) s (N.U i) (t₂.s i))
    {W : Scheme.{0}} (r : W ⟶ Z) (z : W) (i : N.ι) (hi : (r ≫ q) z ∈ N.U i) :
    gm (r ≫ q) z (N.U i) (t₁.s i) = gm (r ≫ q) z (N.U i) (t₂.s i) := by
  have tr : ∀ {t : LB.Gen N}, t.IsGen → ∀ (i j : N.ι) (x : Y), x ∈ N.U i ⊓ N.U j →
      gm (𝟙 Y) x (N.U i) (t.s i) = gm (𝟙 Y) x (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) x (N.U j) (t.s j) := by
    intro t ht i j x hx
    have := congrArg (gm (𝟙 Y) x (N.U i ⊓ N.U j)) (ht i j)
    rwa [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at this
  obtain ⟨u, hu⟩ := glue_unit ⊤ N.U (fun _ => le_top) (fun y _ => Opens.mem_iSup.2 (hN y))
    (fun i => t₁.s i * (t₂.s i)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, tr h₁ i j x hx, tr h₂ i j x hx, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨a, ha⟩ := hp (q.appTop.hom u.val)
  have key : ∀ (W : Scheme.{0}) (r : W ⟶ Z) (z : W) (i : N.ι), (r ≫ q) z ∈ N.U i →
      (gm (r ≫ q) z (N.U i) (t₁.s i) * (gm (r ≫ q) z (N.U i) (t₂.s i))⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro W r z i hi
    rw [← map_inv, ← map_mul, ← hu i, gm_res (r ≫ q) z _ hi]
    exact (gs_unit (r ≫ q) z ⊤ trivial _).symm.trans ((gs_pull r q z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    obtain ⟨i, hi⟩ := hN ((e ≫ q) y)
    have := key _ e y i hi
    rw [h y i hi, mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key _ r z i hi
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem valR_eq_of_gs {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) (h : ∀ z, gs x z U a = gs x z U b) : valR x U a = valR x U b := by
  rw [valR, valR, dite_eq_left hU, dite_eq_left hU]
  congr 1
  have : (x.app U).hom a = (x.app U).hom b := fn_ext fun z hz => by
    rw [gs_pull (𝟙 _) x z U hz, gs_pull (𝟙 _) x z U hz, Category.id_comp]
    exact h z
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, this]

theorem isAbelianScheme_fibre {S T : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (y : T ⟶ S)
    (hp : IsProper (pullback.snd G.hom y)) : IsAbelianScheme ((Over.pullback y).obj G) := by
  haveI := hG.comm
  haveI := hG.smooth
  haveI := hG.geomConnected
  exact ⟨inferInstance, (inferInstance : Smooth (pullback.snd G.hom y)), hp,
    (inferInstance : GeometricallyConnected (pullback.snd G.hom y))⟩

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), (∃ w, IsRigIso m.cm t'.PP t.PP w) ∧ ∀ (w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)), IsRigIso m.cm t'.PP t.PP w → IsRigIso m.cm t'.PP t.PP w' → ∀ (F : Type) [Field F] (y : Sp F ⟶ S') (x : Over.mk y ⟶ t'.G), IsProper (pullback.snd t'.G.hom y) → ∀ j j', ⊤ ≤ x.left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') → valR x.left _ (w.s (fun _ => j, j')).val = valR x.left _ (w'.s (fun _ => j, j')).val := by
  intro hL _ E _ _ _ H _ S S' t t' f m
  refine ⟨m.lin.imp fun w hw => ⟨hw.1, hw.2.1⟩, ?_⟩
  intro w w' hw hw' F _ y x hp j j' hU
  have hs : Function.Surjective (pullback.snd t'.G.hom y).appTop.hom :=
    (hL.globalFns _ _ (isAbelianScheme_fibre t'.G t'.semi y hp)).2
  have he : eSec t'.G ≫ t'.G.hom = 𝟙 S' := Over.w η[t'.G]
  have hx : x.left ≫ t'.G.hom = 𝟙 _ ≫ y := (Over.w x).trans (Category.id_comp y).symm
  have he' : (y ≫ eSec t'.G) ≫ t'.G.hom = 𝟙 _ ≫ y := by
    rw [Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) he).trans (Category.comp_id y))
  refine valR_eq_of_gs _ _ hU _ _ fun z => ?_
  have hz : x.left z ∈ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') :=
    hU (show z ∈ (⊤ : (Sp F).Opens) from trivial)
  rw [gs_unit _ _ _ hz, gs_unit _ _ _ hz]
  congr 1
  have hcov : ∀ a : t'.G.left, ∃ i, a ∈ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart t'.PP.isLB a
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (m.φ a)
    exact ⟨(fun _ => k, i), mem_pull.2 hk, hi⟩
  have gm_pullU_eq_gm_comp {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {U : X.Opens}
      (h : φ (r z) ∈ U) (x : Γ(X, U)ˣ) :
      gm r z (φ ⁻¹ᵁ U) (pullU φ U x) = gm (r ≫ φ) z U x := by
    have h₁ : r z ∈ φ ⁻¹ᵁ U := h
    have h₂ : (r ≫ φ) z ∈ U := h
    simp only [gm, dif_pos h₁, dif_pos h₂, MonoidHom.comp_apply]
    ext
    simp only [Units.coe_map, pullU, MonoidHom.coe_coe]
    first
      | rfl
      | (rw [Scheme.comp_app]; rfl)

  have gm_maps_pt {X : Scheme.{0}} {L' L : LB X} {w : LB.Iso L' L} {Y : Scheme.{0}} {φ : Y ⟶ X} {a : LB.Gen (L'.pull φ)}
      {b : LB.Gen (L.pull φ)} (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => φ) (fun _ => 1)) a b)
      {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : L.ι) (q : L'.ι) (hp : φ (r z) ∈ L.U p) (hq : φ (r z) ∈ L'.U q) :
      gm r z _ (b.s (fun _ => p)) = gm (r ≫ φ) z _ (w.s (p, q)) * gm r z _ (a.s (fun _ => q)) := by
    have hV : r z ∈ LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q) :=
      ⟨mem_pull.2 hp, mem_pull.2 hq⟩
    have h' : res (U := LB.wchart L (fun _ => φ) (fun _ => p))
          (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q)) inf_le_left
          (b.s (fun _ => p)) =
        (∏ _k : PUnit, (res (U := φ ⁻¹ᵁ (L.U p ⊓ L'.U q))
            (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q))
            (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => φ) (fun _ => p) PUnit.unit))
              (inf_le_right.trans (LB.wchart_le L' (fun _ => φ) (fun _ => q) PUnit.unit)))
            (pullU φ (L.U p ⊓ L'.U q) (w.s (p, q)))) ^ (1 : ℤ)) *
        res (U := LB.wchart L' (fun _ => φ) (fun _ => q))
          (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q)) inf_le_right
          (a.s (fun _ => q)) :=
      h (fun _ => p, fun _ => q)
    rw [Fintype.prod_unique, zpow_one] at h'
    have key := congrArg (gm r z (LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q))) h'
    rw [map_mul, gm_res r z (U := LB.wchart L (fun _ => φ) (fun _ => p)) _ hV (b.s (fun _ => p))] at key
    refine key.trans (congrArg₂ (· * ·) ((gm_res r z _ hV _).trans
      (gm_pullU_eq_gm_comp φ r z (U := L.U p ⊓ L'.U q) ⟨hp, hq⟩ (w.s (p, q)))) (gm_res r z _ hV _))
  have key := gm_eq_of_eq_along_section hcov (pullback.fst t'.G.hom y) (pullback.snd t'.G.hom y)
    (pullback.lift (y ≫ eSec t'.G) (𝟙 _) he') (pullback.lift_snd _ _ _) hs hw.1 hw'.1 (by
      rw [pullback.lift_fst]
      rintro s ⟨k, i⟩ ⟨hk, hi⟩
      have k₁ := gm_maps_pt hw.2 y s k i hk hi
      have k₂ := gm_maps_pt hw'.2 y s k i hk hi
      exact mul_right_cancel (k₁.symm.trans k₂))
    (pullback.lift x.left (𝟙 _) hx) z (fun _ => j, j')
  rw [pullback.lift_fst] at key
  exact key hz

end GlobalTheory.RigIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpEqOfIsometryMatchingMarkings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem exp_eq_of_matching_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P P' : (Fu.Di i).La →+ (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (inferInstance : StarRing (𝓞 E)) = H.starRing → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i) ty P' → (∀ u v, (Fu.Di i).EF (gam u) (gam v) = (Fu.Di i).EF u v) → (∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = Fu.t i v + l.M • e) → (∀ v, ∃ e, gam (Fu.t i v) = Fu.t i v + l.A • e) → (∀ u, P' (gam u) = h (P u)) → Fu.u i P = Fu.u i P' ∧ ∀ z, (Fu.ex i P' (h z)).left = (Fu.ex i P z).left := by
  intro E _ _ _ H _ D l Xo σ g ty Fu i P P' gam h _ hP hP' hiso hM hA hh
  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Fu.Di i).La),
      ∃ e, gam a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := Fu.t_surj i b
      obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩
  have hA' : ∀ a, ∃ e, gam a = a + l.A • e := by
    intro b
    obtain ⟨c, e, rfl⟩ := Fu.t_surj i b
    obtain ⟨e₁, he₁⟩ := hA c
    obtain ⟨r, hr⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
    refine ⟨e₁ + r • (gam e - e), ?_⟩
    rw [map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul, smul_sub]
    abel
  have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
    LinearMap.toMatrix'_mulVec _ z
  obtain ⟨-, h1, h2⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H D l Xo σ g ty Fu i P P' gam
    (LinearMap.toMatrix' h.toLinearMap) hP hP' hiso hM' hA' (fun a => by rw [hm, hh])
  exact ⟨h1, fun z => by rw [← hm]; exact h2 z⟩

end GlobalTheory.ArcPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FamilyUnifComponentConst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory

theorem isHolTo_comp_fin_one {X : Scheme.{0}} {B : Set ℂ} {y : ℂ → (Sp ℂ ⟶ X)} (h : IsHolTo B y) :
    IsHolTo {b : Fin 1 → ℂ | b 0 ∈ B} (fun b => y (b 0)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hc : Continuous (fun b : Fin 1 → ℂ => b 0) := continuous_apply (0 : Fin 1)
  refine ⟨h1.preimage hc, ?_⟩
  have hd : Differentiable ℂ (fun b : Fin 1 → ℂ => b 0) := differentiable_apply (0 : Fin 1)
  exact h2.comp hd.differentiableOn (fun b hb => hb)

theorem familyUnif_component_const :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (T : ℝ) (yw : ℂ → (Sp ℂ ⟶ Xo.X)), IsHolTo {w : ℂ | T < w.im} yw → (∀ w : ℂ, T < w.im → yw w ≫ Xo.s = spMap σ) → ∃ i, ∀ w : ℂ, T < w.im → ∃ P, IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw w := by
  intro E _ _ _ H _ D l Xo σ g ty Fu T yw hhol hσ
  classical
  set B : Set (Fin 1 → ℂ) := {b | T < (b 0).im} with hB
  have hBo : IsOpen B := isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply 0))
  have hBc : IsPreconnected B := by
    have hc : Convex ℝ B := by
      have := (convex_halfSpace_im_gt T).is_linear_preimage
        (f := fun b : Fin 1 → ℂ => b 0) ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      exact this
    exact hc.isPreconnected
  have hy : IsHolTo B (fun b => yw (b 0)) := isHolTo_comp_fin_one hhol
  have hex : ∀ b : Fin 1 → ℂ, ∃ i : Fin Fu.n, b ∈ B → ∃ P, IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw (b 0) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨i, P, h⟩ := Fu.onto _ (hσ (b 0) hb)
      exact ⟨i, fun _ => ⟨P, h⟩⟩
    · exact ⟨⟨0, Fu.n_pos⟩, fun h => absurd h hb⟩
  choose c hc using hex
  have hcont : ContinuousOn c B := by
    intro b₀ hb₀
    obtain ⟨B', i, P, ho, hm, hsub, hP, hu⟩ := Fu.lift 1 B _ hBo (fun b hb => hσ (b 0) hb) hy b₀ hb₀
    have key : ∀ b ∈ B', c b = i := by
      intro b hb
      obtain ⟨Q, hQ, hQu⟩ := hc b (hsub hb)
      exact Fu.disj _ _ Q (P b) hQ (hP.1 b hb) (hQu.trans (hu b hb).symm)
    have hev : c =ᶠ[nhds b₀] fun _ => i := Filter.eventually_of_mem (ho.mem_nhds hm) key
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  have h0 : (fun _ : Fin 1 => ((T + 1 : ℝ) : ℂ) * Complex.I) ∈ B := by
    simp [hB]
  refine ⟨c (fun _ : Fin 1 => ((T + 1 : ℝ) : ℂ) * Complex.I), fun w hw => ?_⟩
  have hwB : (fun _ : Fin 1 => w) ∈ B := hw
  rw [hBc.constant hcont h0 hwB]
  exact hc _ hwB

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FderivTorusCoordinateRatioEqZeroOfTangentStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fderiv_torusCoordinateRatio_eq_zero_of_tangent : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → 0 < n → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → (∀ x, DifferentiableAt ℂ (u x) 0) → (∀ x, u x 0 = 1) → ∀ (v : epsR ℂ ⟶ D.P.A) (ν : Out.GtPt D (epsR ℂ)) (z : Fin g → ℂ), Out.GtPt.IsPull (spMap (epsScaleR ((n : ℂ)⁻¹))) (sB (epsR ℂ) v) ν → IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) z v.left → (∀ x j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (ex 0) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (ex z) x j) 0 z)) → ∀ x, fderiv ℂ (u x) 0 z = 0 := by
  first | exact @GlobalTheory.AbelianLetters.fderiv_ratio_eq_zero | exact GlobalTheory.AbelianLetters.fderiv_ratio_eq_zero | (intros; apply GlobalTheory.AbelianLetters.fderiv_ratio_eq_zero <;> assumption)
end

