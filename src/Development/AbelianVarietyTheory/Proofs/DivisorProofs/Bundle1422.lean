module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelsOfChain
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportOfStTw2NeZero
section
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

noncomputable section

namespace GlobalTheory.BCT.GeoFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ne_zero_of_finprod_mem_ne_zero {α : Type} (f : α → ℂ) (S : Set α) (hf : (Function.mulSupport f).Finite)
    (h : ∏ᶠ w ∈ S, f w ≠ 0) : ∀ w ∈ S, f w ≠ 0 := by
  intro w hw h0
  have hfin : (S ∩ Function.mulSupport f).Finite := hf.subset Set.inter_subset_right
  apply h
  rw [finprod_mem_eq_prod_of_inter_mulSupport_eq f (t := hfin.toFinset) (by
    ext x; simp only [Set.mem_inter_iff, Set.Finite.coe_toFinset]; tauto)]
  exact Finset.prod_eq_zero (i := w) (by simp [hw, h0]) h0

theorem exists_support_of_stTw2_ne_zero (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X])
    (φ : GLw a w × GLw b w → ℂ) (h : stTw2 a b w Q₁ Q₂ φ ≠ 0) :
    ∃ y, φ y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂ := by
  obtain ⟨δ, ⟨hδ₁, hδ₂⟩, x, hx⟩ := exists_ne_zero_of_clSum_ne_zero
    ((thL a w).prodMap (thL b w))
    ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)))
    {y | (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂} 1 φ h
  refine ⟨_, hx, ?_, ?_⟩
  · change (nrmL a w (x.1⁻¹ * δ.1 * thL a w x.1)).val.charpoly = Q₁
    rw [nrmL_twConj, ← hδ₁, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]
  · change (nrmL b w (x.2⁻¹ * δ.2 * thL b w x.2)).val.charpoly = Q₂
    rw [nrmL_twConj, ← hδ₂, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]

end GlobalTheory.BCT.GeoFin

namespace GlobalTheory.BCT.GeoFin

end GlobalTheory.BCT.GeoFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFiniteFlat
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.HTTorsionFF

theorem exists_gen_idem {R : Type} [CommRing R] [IsDedekindDomain R] (w : Ideal R) (hw : w ≠ ⊥) :
    ∃ α x : R, α ≠ 0 ∧ α ∈ w ∧ x ∈ w ∧ x * x - x ∈ Ideal.span {α} ∧ w = Ideal.span {α, x} := by
  have hw2 : w ^ 2 ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, pow_eq_zero_iff two_ne_zero, Ideal.zero_eq_bot]; exact hw
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.pow_le_self two_ne_zero : w ^ 2 ≤ w) hw2
  obtain ⟨α, hα0, hα⟩ : ∃ α : R, α ≠ 0 ∧ w ^ 2 ⊔ Ideal.span {α} = w := by
    by_cases h0 : y = 0
    · subst h0
      rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq] at hy
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw2
      exact ⟨z, hz0, by rw [sup_eq_left.2 ((Ideal.span_singleton_le_iff_mem _).2 hz), hy]⟩
    · exact ⟨y, h0, hy⟩
  have hαw : α ∈ w := by
    rw [← hα]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self α)
  have hidem : IsIdempotentElem (w.map (Ideal.Quotient.mk (Ideal.span {α}))) := by
    unfold IsIdempotentElem
    conv_rhs => rw [← hα]
    rw [Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, sq, Ideal.map_mul]
  have hfg : (w.map (Ideal.Quotient.mk (Ideal.span {α}))).FG := Ideal.FG.map (IsNoetherian.noetherian w) _
  obtain ⟨e, he, hwe⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).1 hidem
  have he_mem : e ∈ w.map (Ideal.Quotient.mk (Ideal.span {α})) := by
    rw [hwe]; exact Submodule.mem_span_singleton_self e
  obtain ⟨x, hxw, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 he_mem
  refine ⟨α, x, hα0, hαw, hxw, ?_, le_antisymm (fun c hc => ?_) ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, he.eq, sub_self]
  · have hc' : Ideal.Quotient.mk (Ideal.span {α}) c ∈
        (R ⧸ Ideal.span {α}) ∙ (Ideal.Quotient.mk (Ideal.span {α}) x) := by
      rw [← hwe]; exact Ideal.mem_map_of_mem _ hc
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hc'
    obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
    have h1 : c - d' * x ∈ Ideal.span {α} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← smul_eq_mul, hd, sub_self]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 : c = a * α + d' * x := by rw [ha]; ring
    rw [h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact hαw
    · exact hxw

theorem ringHom_flat_of_retract {A B C : CommRingCat.{0}} (ψ : A ⟶ C) (σ : C ⟶ B) (π : B ⟶ C)
    (h : σ ≫ π = 𝟙 C) (hf : (ψ ≫ σ).hom.Flat) : ψ.hom.Flat := by
  letI := ψ.hom.toAlgebra
  letI := (ψ ≫ σ).hom.toAlgebra
  have hB : Module.Flat A B := hf
  have hπσ : ∀ z, π.hom (σ.hom z) = z := fun z => by
    rw [← CommRingCat.comp_apply, h, CommRingCat.id_apply]
  show Module.Flat A C
  let s : C →ₗ[A] B :=
    { toFun := σ.hom
      map_add' := map_add _
      map_smul' := fun a c => by
        simp only [Algebra.smul_def, RingHom.id_apply, map_mul, RingHom.algebraMap_toAlgebra,
          CommRingCat.hom_comp, RingHom.comp_apply] }
  let q : B →ₗ[A] C :=
    { toFun := π.hom
      map_add' := map_add _
      map_smul' := fun a c => by
        simp only [Algebra.smul_def, RingHom.id_apply, map_mul, RingHom.algebraMap_toAlgebra,
          CommRingCat.hom_comp, RingHom.comp_apply, hπσ] }
  exact Module.Flat.of_retract s q (LinearMap.ext fun z => hπσ z)

theorem flat_of_retract {X Y S : Scheme.{0}} (f : X ⟶ S) (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X)
    [Flat (r ≫ f)] : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  have hx : r (i x) = x := by
    rw [← Scheme.Hom.comp_apply, h]; rfl
  haveI : IsIso (i ≫ r) := by rw [h]; infer_instance
  haveI : IsOpenImmersion (i ≫ r) := inferInstance
  haveI : IsIso ((i ≫ r).stalkMap x) := inferInstance
  have key : (f.stalkMap (r (i x))).hom.Flat := by
    have e1 : r.stalkMap (i x) ≫ i.stalkMap x = (i ≫ r).stalkMap x := (Scheme.Hom.stalkMap_comp i r x).symm
    haveI hg : IsIso (r.stalkMap (i x) ≫ i.stalkMap x) := by rw [e1]; exact this
    have e2 : r.stalkMap (i x) ≫ (i.stalkMap x ≫ CategoryTheory.inv (r.stalkMap (i x) ≫ i.stalkMap x)) = 𝟙 _ := by
      rw [← Category.assoc, IsIso.hom_inv_id]
    refine ringHom_flat_of_retract (f.stalkMap (r (i x))) (r.stalkMap (i x)) _ e2 ?_
    · rw [← Scheme.Hom.stalkMap_comp]
      exact Flat.stalkMap (r ≫ f) (i x)
  rwa [hx] at key


open GlobalTheory.UPel.HT in
theorem oActN_natCast {S : Scheme.{0}} {O : Type} [Ring O] {G : Over S} [GrpObj G] (act : OActN O G) (n : ℕ) :
    act.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.1 h
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]


open GlobalTheory.UPel.HT in
theorem act_finite_flat {S : Scheme.{0}} [IsLocallyNoetherian S] {F O : Type} [Field F] [NumberField F] [Ring O]
    [Algebra (𝓞 F) O] (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (act : OActN O A)
    (c : 𝓞 F) (hc : c ≠ 0) :
    IsFinite (act.act (algebraMap (𝓞 F) O c)).left ∧ Flat (act.act (algebraMap (𝓞 F) O c)).left := by
  have he : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
  have hcomp : act.act (algebraMap (𝓞 F) O c) ≫ act.act (algebraMap (𝓞 F) O a) =
      𝟙 A ^ Ideal.absNorm (Ideal.span {c}) := by
    rw [← act.mul, ← map_mul, ha, map_natCast, oActN_natCast]
  obtain ⟨hfe, -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A hA _ (Nat.one_le_iff_ne_zero.2 he)
  have hpr := hA.proper
  have hsm := hA.smooth
  haveI : IsSeparated ((act.act (algebraMap (𝓞 F) O a)).left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (act.act (algebraMap (𝓞 F) O a)).left := IsSeparated.of_comp _ A.hom
  haveI : IsFinite ((act.act (algebraMap (𝓞 F) O c)).left ≫ (act.act (algebraMap (𝓞 F) O a)).left) := by
    rw [← Over.comp_left, hcomp]; exact hfe
  have hf : IsFinite (act.act (algebraMap (𝓞 F) O c)).left := IsFinite.of_comp _ (act.act (algebraMap (𝓞 F) O a)).left
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S A A _ inferInstance inferInstance hf fun K _ _ t => ?_⟩
  have hm := act.hom (algebraMap (𝓞 F) O c)
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (Out.TLinPf.isAb_pullback t A hA) _ inferInstance
    (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hf)).1


open KerGrp in
theorem exists_torsion_finite_flat : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (S : Scheme.{0}) [IsLocallyNoetherian S]
    (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s), w ≠ ⊥ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A),
      IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Flat K.hom ∧ ∀ (T : Over S) (x : T ⟶ o.A),
        GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N w S _ s o hw
  obtain ⟨α, x, hα0, -, -, hxx, hwx⟩ := exists_gen_idem w hw
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hxx
  have hA := o.ab
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O α)
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O x)
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O t)
  have comm : o.act.act (algebraMap (𝓞 D.F) D.O α) ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) =
      o.act.act (algebraMap (𝓞 D.F) D.O x) ≫ o.act.act (algebraMap (𝓞 D.F) D.O α) := by
    rw [← o.act.mul, ← o.act.mul, ← map_mul, ← map_mul, mul_comm]
  have idem : o.act.act (algebraMap (𝓞 D.F) D.O x) ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) =
      o.act.act (algebraMap (𝓞 D.F) D.O x) *
        (o.act.act (algebraMap (𝓞 D.F) D.O α) ≫ o.act.act (algebraMap (𝓞 D.F) D.O t)) := by
    rw [← o.act.mul, ← o.act.mul, ← o.act.add, ← map_mul, ← map_mul, ← map_add (f := _), ht]
    congr 2; ring

  set fα := o.act.act (algebraMap (𝓞 D.F) D.O α) with hfα
  set fx := o.act.act (algebraMap (𝓞 D.F) D.O x) with hfx
  set ft := o.act.act (algebraMap (𝓞 D.F) D.O t) with hft
  obtain ⟨hfinα, hflα⟩ := act_finite_flat o.A hA o.act α hα0
  letI gH : GrpObj (ker fα) := grp fα
  haveI : IsMonHom (pullback.fst fα η[o.A]) := isMonHom_fst fα
  have hPB := (IsPullback.of_hasPullback fα η[o.A]).map (Over.forget S)
  have hHfin : IsFinite (ker fα).hom := by
    rw [← Over.w (pullback.snd fα η[o.A])]
    haveI : IsFinite (pullback.snd fα η[o.A]).left := MorphismProperty.of_isPullback (P := @IsFinite) hPB hfinα
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 S))
  have hHflat : Flat (ker fα).hom := by
    rw [← Over.w (pullback.snd fα η[o.A])]
    haveI : Flat (pullback.snd fα η[o.A]).left := MorphismProperty.of_isPullback (P := @Flat) hPB hflα
    exact inferInstanceAs (Flat (_ ≫ 𝟙 S))

  set jH := pullback.fst fα η[o.A] with hjH
  have hj : jH ≫ fα = 1 := fst_comp fα
  let g : ker fα ⟶ ker fα := lift fα (jH ≫ fx) (by
    rw [Category.assoc, ← comm, ← Category.assoc, hj, MonObj.one_comp])
  have hg : g ≫ jH = jH ≫ fx := lift_fst _ _ _
  have hxx' : jH ≫ fx ≫ fx = jH ≫ fx := by
    rw [idem, MonObj.comp_mul, ← Category.assoc jH fα ft, hj, MonObj.one_comp, _root_.mul_one]
  letI gK : GrpObj (ker (jH ≫ fx)) := grp (jH ≫ fx)
  haveI : IsMonHom (pullback.fst (jH ≫ fx) η[o.A]) := isMonHom_fst (jH ≫ fx)
  set iK := pullback.fst (jH ≫ fx) η[o.A] with hiK
  have hk : iK ≫ jH ≫ fx = 1 := fst_comp (jH ≫ fx)
  have hrk : (𝟙 (ker fα) / g) ≫ jH ≫ fx = 1 := by
    rw [← Category.assoc, GrpObj.div_comp, Category.id_comp, hg, GrpObj.div_comp, Category.assoc, hxx',
      div_self']
  let r : ker fα ⟶ ker (jH ≫ fx) := lift (jH ≫ fx) (𝟙 (ker fα) / g) hrk
  have hr : r ≫ iK = 𝟙 (ker fα) / g := lift_fst _ _ _
  have hiKg : iK ≫ g = 1 := hom_ext fα (by
    rw [Category.assoc, hg, hk, MonObj.one_comp])
  have hir : iK ≫ r = 𝟙 _ := hom_ext (jH ≫ fx) (by
    rw [Category.assoc, hr, GrpObj.comp_div, Category.comp_id, hiKg, div_one, Category.id_comp])
  have hirl : iK.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]

  have hKfin : IsFinite (ker (jH ≫ fx)).hom := by
    haveI : IsFinite (r.left ≫ (ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHfin
    haveI : IsSeparated (r.left ≫ (ker (jH ≫ fx)).hom) := by rw [Over.w r]; infer_instance
    haveI : IsSeparated r.left := IsSeparated.of_comp _ (ker (jH ≫ fx)).hom
    haveI : IsFinite (iK.left ≫ r.left) := by rw [hirl]; infer_instance
    haveI : IsFinite iK.left := IsFinite.of_comp _ r.left
    rw [← Over.w iK]; infer_instance
  have hKflat : Flat (ker (jH ≫ fx)).hom := by
    haveI : Flat (r.left ≫ (ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHflat
    exact flat_of_retract _ iK.left r.left hirl
  refine ⟨ker (jH ≫ fx), gK, iK ≫ jH, inferInstance, inferInstance, hKfin, hKflat, fun T z => ?_⟩
  rw [hwx, Ideal.map_span, Set.image_pair, GlobalTheory.IwLevel.killedBy_span]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, GlobalTheory.IwLevel.htAct_act]
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · show ((y ≫ iK) ≫ jH) ≫ fα = 1
      rw [Category.assoc, hj, MonObj.comp_one]
    · show ((y ≫ iK) ≫ jH) ≫ fx = 1
      rw [Category.assoc, Category.assoc, hk, MonObj.comp_one]
  · refine ⟨lift (jH ≫ fx) (lift fα z h1) (by rw [← Category.assoc, KerGrp.lift_fst, h2]), ?_⟩
    rw [← Category.assoc, KerGrp.lift_fst, KerGrp.lift_fst]

end GlobalTheory.IwLevel.HTTorsionFF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionAbelianDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbHomExtDvr

theorem existsUnique_hom_extension_abelian_dvr :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G G' : Over (Sp W)) [GrpObj G] [GrpObj G'], IsAbelianScheme G → IsAbelianScheme G' → ∀ f : (Over.pullback (spMap (algebraMap W L))).obj G ⟶ (Over.pullback (spMap (algebraMap W L))).obj G', IsMonHom f → ∃! F : G ⟶ G', (Over.pullback (spMap (algebraMap W L))).map F = f := by
  intro W L _ _ _ _ _ _ G G' _ _ hG hG' f hf
  have hsm : GlobalTheory.SS.SmConn G := ⟨hG.comm, hG.smooth, by have := hG.proper; infer_instance,
    by have := hG.proper; infer_instance, hG.geomConnected⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr W L G G' hsm
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme G' hG') f hf
  have := hG.smooth
  have := hG'.proper
  have : Flat G.hom := inferInstance
  refine ⟨F, hF, fun F' hF' => ?_⟩
  exact GlobalTheory.KernelNoTorsion.eq_of_generic W L (hF'.trans hF.symm)

end GlobalTheory.AbHomExtDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.WeilTypeChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isCMField_of_cmExt {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : IsCMField E := by
  haveI := h.1; haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  exact IsCMField.ofCMExtension F E

def phase : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    ring

theorem phase_val (z : ℂˣ) : ((phase z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem continuous_phase : Continuous phase := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm) fun z => by simp
  · have : (fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((phase z⁻¹ : ℂˣ) : ℂ) :=
      funext fun z => by rw [map_inv]
    show Continuous fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)
    rw [this]
    show Continuous fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ) / ((‖((z⁻¹ : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_coe_inv.div (Complex.continuous_ofReal.comp Units.continuous_coe_inv.norm) fun z => by simp

theorem norm_phase (z : ℂˣ) : ‖((phase z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]

def chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : (AF F ⊗[F] E)ˣ →* ℂˣ :=
  ∏ w, phase.comp (Units.map (piInf (emb w)).toMonoidHom)

theorem chiInf_apply (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ((chiInf emb z : ℂˣ) : ℂ) = ∏ w, (piInf (emb w) z / ((‖piInf (emb w) z‖ : ℝ) : ℂ)) := by
  simp [chiInf, phase_val]

theorem continuous_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Continuous (chiInf emb) := by
  have e : ⇑(chiInf emb) = fun z => ∏ w, phase (Units.map (piInf (emb w)).toMonoidHom z) :=
    funext fun z => by simp [chiInf]
  rw [e]
  exact continuous_finsetProd _ fun w _ =>
    continuous_phase.comp (Continuous.units_map _ (GlobalTheory.ContMapReal.continuous_piInf (emb w)))

theorem norm_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ‖((chiInf emb z : ℂˣ) : ℂ)‖ = 1 := by
  simp [chiInf, norm_prod, norm_phase]

theorem exists_weil_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsCMField E := isCMField_of_cmExt hB.cm
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))
  have hq2 : 2 < q := by omega
  have htq : Nat.card (Units.torsion E) < q := by omega
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  obtain ⟨U, hU, hUinf, hUk⟩ := _root_.GlobalTheory.OpenCongrIdele.exists_open_congr F E q hq.ne_zero
  obtain ⟨χ, hχc, hχ1, hχU, hχk⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU
    (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb)
    (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu, hu1⟩ := hUk k hk
      refine Units.ext ?_
      rw [chiInf_apply, MonoidHom.one_apply, Units.val_one]
      have e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
          (B.emb w).1 ((u : 𝓞 E) : E) := fun w => by
        rw [hu]
        exact GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)
      simp only [e]
      exact (_root_.GlobalTheory.weil_unit_phase_prod F E σ hB.cm B.emb q hq hq2 ht u hu1).symm)
  refine ⟨GlobalTheory.unitaryCharToCircle χ hχ1, ⟨?_, fun k => ?_⟩, fun z hz => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp hχc) _
  · apply Circle.ext
    show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1
    rw [hχk]; rfl
  · show ((χ z : ℂˣ) : ℂ) = _
    rw [hχU z (hUinf z hz), chiInf_apply]
    simp

end GlobalTheory.WeilTypeChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreLineOverSurjection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open PrimeSpectrum in
theorem prime_line_mem_range_comap_mapRingHom {R K : Type} [CommRing R] [Field K] (χ : R →+* K)
    (hχ : Function.Surjective χ) (P : PrimeSpectrum (Polynomial R))
    (hP : PrimeSpectrum.comap (algebraMap R (Polynomial R)) P = PrimeSpectrum.comap χ (IsLocalRing.closedPoint K)) :
    P ∈ Set.range (PrimeSpectrum.comap (Polynomial.mapRingHom χ)) := by
  have hker : RingHom.ker χ ≤ Ideal.comap Polynomial.C P.asIdeal := by
    intro a ha
    have h1 := congrArg PrimeSpectrum.asIdeal hP
    simp only [PrimeSpectrum.comap_asIdeal] at h1
    have : a ∈ Ideal.comap (algebraMap R (Polynomial R)) P.asIdeal := by
      rw [h1, Ideal.mem_comap, RingHom.mem_ker.mp ha]
      exact Ideal.zero_mem _
    exact this
  rw [range_comap_of_surjective _ _ (Polynomial.map_surjective χ hχ), PrimeSpectrum.mem_zeroLocus,
    Polynomial.ker_mapRingHom, SetLike.coe_subset_coe]
  exact Ideal.map_le_iff_le_comap.mpr hker

theorem fibre_line_over_surjection : ∀ (R K : Type) [CommRing R] [Field K] (χ : R →+* K), Function.Surjective χ → ∀ (x : Sp (Polynomial R)), spMap (algebraMap R (Polynomial R)) x = spMap χ (IsLocalRing.closedPoint K) → x ∈ Set.range (spMap (Polynomial.mapRingHom χ)) := by
  intro R K _ _ χ hχ x hx
  exact prime_line_mem_range_comap_mapRingHom χ hχ x hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupSchemeStalkLengthConstantStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_group_scheme_stalk_length_constant : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  first | (exact @GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (exact GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (intros; apply GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLengthStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_fiber_eq_card_sections_mul_length : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Scheme.{0}) (q : P ⟶ Sp k), IsFinite q → ∀ (m : ℕ∞), (∀ x : P, Module.length (P.presheaf.stalk x) (P.presheaf.stalk x) = m) → ∀ z : Sp k, (q.finrank z : ℕ∞) = (Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} : ℕ∞) * m := by
  first | (exact @GlobalTheory.FinSchemeRank.finrank_eq_card_sections_mul) | (exact GlobalTheory.FinSchemeRank.finrank_eq_card_sections_mul) | (intros; apply GlobalTheory.FinSchemeRank.finrank_eq_card_sections_mul  <;> assumption)
end

