module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0007
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0009
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0008
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0005
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0003
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0001
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0002
public import Development.EtaleCohomology.CohomologicalPurity.LeafDiagPf
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0004
public import Development.EtaleCohomology.TateTwists.Bundle0003
public import Development.EtaleCohomology.TateTwists.Bundle0016
public import Development.EtaleCohomology.TateTwists.Bundle0026
public import Development.EtaleCohomology.TateTwists.Bundle0023
public import Development.EtaleCohomology.TateTwists.Bundle0009
public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0010
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.FinLeafChart
section
namespace LateralTheory.Fin.LeafChart
theorem etale_chart_localization_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafLoc := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafLoc_of
theorem etale_chart_shrinking_open_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafShrink := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafShrink_of
theorem etale_chart_conormal_rank_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafRank := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of
theorem etale_chart_generator_choice_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPick := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafPick_of
theorem etale_chart_ideal_span_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSpan := by
  apply LateralTheory.CohomologicalPurity.LeafSpanPf.LeafSpan_of
theorem etale_chart_etaleness_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafEt := by
  apply LateralTheory.CohomologicalPurity.LeafEtPf.LeafEt_of
theorem etale_chart_coordinate_functions_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafCoord := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafCoord_of <;> first | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds
theorem etale_chart_section_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  apply LateralTheory.CohomologicalPurity.LeafSecPf.LeafSec_of
theorem etale_chart_polynomial_algebra_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  apply LateralTheory.CohomologicalPurity.LeafPolyPf.LeafPoly_of
theorem etale_chart_neighborhood_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd_of <;> first | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds
theorem etale_coordinate_chart_existence : LateralTheory.CohomologicalPurity.LeafChart := by
  apply LateralTheory.CohomologicalPurity.ChartCut.goal_of <;> first | exact etale_chart_localization_property_holds | exact etale_chart_shrinking_open_property_holds | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds | exact etale_chart_coordinate_functions_property_holds | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds | exact etale_chart_neighborhood_property_holds
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafChart := etale_coordinate_chart_existence
end LateralTheory.Fin.LeafChart
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.FinLeafHens
section
namespace LateralTheory.Fin.LeafHens
theorem henselization_compatible_maps_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafComp := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafComp_of
theorem henselization_inverse_limit_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafInv := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafInv_of
theorem standard_etale_simple_root_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRootStd := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRootStd_of
theorem henselian_simple_root_lift_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRootHens := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRootHens_of
theorem henselization_simple_root_lift_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRoot := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRoot_of <;> first | exact standard_etale_simple_root_of_henselization | exact henselian_simple_root_lift_of_henselization
theorem henselization_supremum_neighborhood_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafSup := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafSup_of
theorem henselization_coequalizer_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafCoeq := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafCoeq_of <;> first | exact henselization_inverse_limit_of_henselization | exact henselization_compatible_maps_of_henselization
theorem henselization_diagonal_section_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafDiag := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafDiag_of <;> first | exact henselization_compatible_maps_of_henselization | exact henselization_supremum_neighborhood_of_henselization | exact henselization_coequalizer_of_henselization
theorem henselization_etale_neighborhood_stage_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafStage := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafStage_of
theorem henselization_colimit_henselian_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafColHens := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafColHens_of <;> first | exact henselization_etale_neighborhood_stage_of_henselization | exact henselization_inverse_limit_of_henselization | exact henselization_simple_root_lift_of_henselization
theorem henselization_colimit_universal_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafColUniv := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafColUniv_of
theorem etale_purity_henselian_local_of_henselization : LateralTheory.CohomologicalPurity.LeafHens := by
  apply LateralTheory.CohomologicalPurity.Hz.goal_of <;> first | exact henselization_compatible_maps_of_henselization | exact henselization_inverse_limit_of_henselization | exact henselization_simple_root_lift_of_henselization | exact henselization_supremum_neighborhood_of_henselization | exact henselization_coequalizer_of_henselization | exact henselization_diagonal_section_of_henselization | exact henselization_etale_neighborhood_stage_of_henselization | exact henselization_colimit_henselian_of_henselization | exact henselization_colimit_universal_of_henselization
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafHens := etale_purity_henselian_local_of_henselization
end LateralTheory.Fin.LeafHens
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafAWCutTw
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleFoundations

namespace LateralTheory.CohomologicalPurity.LeafAWCutTw

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  have e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]
  exact ulift_smul_eq_nsmul _ _

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : M.obj Γ(U, ⊤)) : Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)).symm

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem twF_loc (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun _ h => ∃ c : ℕ, Sec.res h (ofRings.sec (twF q i) V x) = c • twGen i (ζ.map h.appTop.hom) := by
  have L := LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
  have hZ := (etale_locally_roots_of_unity_structure_of_exists_and_kummer etale_locally_exists_primitive_root_of_unity_of_invertible_order etale_locally_kummer_roots_of_units_of_invertible_order q V).2.1
  have key : Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    induction f using Finsupp.induction with
    | zero =>
      refine L.1 V _ fun W h => ⟨0, ?_⟩
      rw [zero_smul, Submodule.Quotient.mk_zero]
      exact map_zero ((twF q i).map h.appTop).hom
    | single_add ξ b g _ _ ih =>
      refine L.2.1 V _ _ (L.2.2.1 V _ _ (hZ ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ =>
        ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩
      rw [Submodule.Quotient.mk_add]
      refine (map_add ((twF q i).map h.appTop).hom _ _).trans ?_
      rw [hc, twF_map_mk, Finsupp.mapDomain_single,
        twF_single_pow q i _ (ζ.map h.appTop.hom) (ξ.map h.appTop.hom) a ha b, add_smul]
      rfl
  refine L.2.1 V _ _ key fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  rw [sec_res, hc]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

theorem loc_surj (q : ℕ) (i : ℤ) (U : Scheme.{0}) (y : Sec (tw q i) U) :
    Loc U fun V g => ∃ x : (twF q i).obj Γ(V, ⊤), ofRings.sec (twF q i) V x = Sec.res g y :=
  (LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf.intersectionNumber_baseChange (ZMod q) (Scheme.Γ ⋙ twF q i)).1 U y

section Lift
variable {q : ℕ} [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U)
  (hn : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom))
  (hr : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
    e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ)

def liftL (U : Scheme.{0}) : ((Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤)) →ₗ[ULift.{1} (ZMod q)] Sec M U :=
  Submodule.liftQ _ (Finsupp.linearCombination _ (e U)) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, h, rfl⟩
    change Finsupp.linearCombination _ (e U) _ = 0
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, hr U ζ ξ a h,
      ulift_smul_eq_nsmul, sub_self])

def liftP : Scheme.Γ ⋙ twF q i ⟶ M.obj where
  app U := ModuleCat.ofHom (liftL i M e hr U.unop)
  naturality U V g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ b => ?_))
    revert ζ
    intro (ζ : Prim q Γ(U.unop, ⊤))
    change Finsupp.linearCombination _ (e V.unop) (Finsupp.mapDomain (Prim.map g.unop.appTop.hom) (Finsupp.single ζ b)) =
      Sec.res g.unop (Finsupp.linearCombination _ (e U.unop) (Finsupp.single ζ b))
    rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single, Finsupp.linearCombination_single, ← hn]
    exact (map_smul _ _ _).symm

include hn hr in
theorem lift_ex : ∃ φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  refine ⟨ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (liftP i M e hn hr) M.property), fun U ζ => ?_⟩
  have key := congrArg (fun η => (η.app (op U)).hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (liftP i M e hn hr) M.property)
  refine key.trans ?_
  change Finsupp.linearCombination _ (e U) (Finsupp.single ζ 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

end Lift

theorem twSec : EtaleTateTwistSectionsLocallyGenerated := by
  intro q _ i
  have L := LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
  refine ⟨fun U y => ?_, fun U ζ y => ?_, fun U _ ζ c hc => ?_, fun V U g ζ => ?_, fun U ζ ξ a h => ?_,
    fun M e hn hr => ?_⟩
  · refine L.2.2.2.2.1 U _ (L.2.1 U _ _ (loc_surj q i U y) fun V g ⟨x, hx⟩ => ?_)
    by_cases hne : Nonempty (Prim q Γ(V, ⊤))
    · obtain ⟨ζ⟩ := hne
      refine L.2.1 V _ _ (twF_loc q i V ζ x) fun W h ⟨c, hc⟩ => Or.inr ⟨ζ.map h.appTop.hom, c, ?_⟩
      rw [res_comp, ← hx]
      exact hc
    · refine L.1 V _ fun W h => Or.inl ?_
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have hf : f = 0 := Finsupp.ext fun ζ => absurd ⟨ζ⟩ hne
      have h0 : Sec.res g y = 0 := by
        rw [← hx, hf, Submodule.Quotient.mk_zero]
        unfold ofRings.sec
        exact map_zero _
      rw [res_comp, h0]
      exact map_zero _
  · refine L.2.2.2.2.1 U _ (L.2.1 U _ _ (loc_surj q i U y) fun V g ⟨x, hx⟩ => ?_)
    refine L.2.1 V _ _ (twF_loc q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
    have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
      apply Subtype.ext
      simp [Prim.map]
      rfl
    rw [res_comp, ← hx, ← hp]
    exact hc
  · have h1 : ((c : ZMod q).val • twGen i ζ) = c • twGen i ζ := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) c, ulift_smul_eq_nsmul]
      rfl
    have := GenConn.inj_of twF_gen_inj_of q U i ζ (a₁ := (c : ZMod q)) (a₂ := 0) (by
      simp only [h1, hc, ZMod.val_zero, zero_smul])
    exact (ZMod.natCast_eq_zero_iff c q).1 this
  · refine (sec_res (twF q i) g _).trans ?_
    rw [twF_map_mk, Finsupp.mapDomain_single]
    rfl
  · unfold twGen
    have := twF_single_pow q i Γ(U, ⊤) ζ ξ a h 1
    rw [ULift.one_down, one_mul] at this
    refine (congrArg (ofRings.sec (twF q i) U) this).trans ?_
    unfold ofRings.sec
    exact map_nsmul _ _ _
  · obtain ⟨φ, hφ⟩ := lift_ex i M e hn hr
    exact ⟨φ, hφ, fun ψ hψ => TwResExt.twuniq_pf q i M ψ φ fun U ζ => (hψ U ζ).trans (hφ U ζ).symm⟩

end LateralTheory.CohomologicalPurity.LeafAWCutTw
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafActNatPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem dbl_map_fold {P' P : Arrow Spc} (φ : P' ⟶ P) :
    dbl.map φ ≫ dbl.fold P = dbl.fold P' ≫ φ.right := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    simp
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc, pushout.inr_desc_assoc]
    simp

theorem LeafActNat_of : LeafActNat := by
  intro hA q _ P' P φ n m i j a b
  apply Subtype.ext
  have hc := (hA q).1 (dbl.map φ) (pull _ (dbl.fold P) (tw q i) n a) b.1
  change pull _ (dbl.map φ) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 -
      pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) =
    cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) -
      pull _ (dbl.fold P') _ _ (pull _ (dbl.inr P') _ _
        (cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1)))
  have e1 : pull (ZMod q) (dbl.map φ) (tw q i) n (pull _ (dbl.fold P) _ n a) =
      pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a) := by
    rw [← pull_comp, ← pull_comp, dbl_map_fold]
  have hcc : pull (ZMod q) (dbl.map φ) (tw q (i + j)) (n + m) (cup q (pull _ (dbl.fold P) _ n a) b.1) =
      cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) := by
    rw [hc, e1]
  rw [map_sub, hcc]
  congr 1
  rw [← hcc, ← pull_comp _ (dbl.map φ) (dbl.fold P), dbl_map_fold, pull_comp _ (dbl.fold P') φ.right,
    ← pull_comp _ φ.right (dbl.inr P), ← dbl.inr_map, pull_comp _ (dbl.inr P') (dbl.map φ)]

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafActPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom
namespace ActPf

variable {d : ℕ} {A : Type} [CommRing A]

def φ {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of A)) : A →+* Γ(U, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appTop).hom

theorem φ_comp {V U : Scheme.{0}} (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A)) :
    φ (f ≫ s) = f.appTop.hom.comp (φ s) := rfl

def actV (M : Matrix (Fin d) (Fin d) A) {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of A))
    (v : Fin (d + 1) → Γ(U, ⊤)) : Fin (d + 1) → Γ(U, ⊤) :=
  Fin.cons (v 0) ((M.map (φ s)).mulVec (Fin.tail v))

theorem actV_mem (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {U : Scheme.{0}}
    (s : U ⟶ Spec (CommRingCat.of A)) (v : Fin (d + 1) → Γ(U, ⊤)) (p : U)
    (h : ∃ i : Fin (d + 1), k ≤ i.val ∧ p ∈ U.basicOpen (v i)) :
    ∃ i : Fin (d + 1), k ≤ i.val ∧ p ∈ U.basicOpen (actV M s v i) := by
  obtain ⟨i, hi, hp⟩ := h
  by_contra hc
  push Not at hc
  have hM' : IsUnit (M.map (φ s)).det := by
    have h := hM.map (φ s); rw [RingHom.map_det] at h; exact h
  have hz : ∀ j : Fin d, (U.Γevaluation p).hom ((M.map (φ s)).mulVec (Fin.tail v) j) = 0 := by
    intro j
    have := hc j.succ (by simp; omega)
    simp only [actV, Fin.cons_succ] at this
    exact (Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).2 this
  have ht : ∀ j : Fin d, (U.Γevaluation p).hom (Fin.tail v j) = 0 := by
    intro j
    have hinv : (M.map (φ s))⁻¹.mulVec ((M.map (φ s)).mulVec (Fin.tail v)) = Fin.tail v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM', Matrix.one_mulVec]
    rw [← hinv, RingHom.map_mulVec]
    have : ((U.Γevaluation p).hom ∘ (M.map (φ s)).mulVec (Fin.tail v)) = 0 := funext hz
    rw [this, Matrix.mulVec_zero]; rfl
  cases i using Fin.cases with
  | zero =>
    have := hc 0 (by simp at hi; omega)
    simp only [actV, Fin.cons_zero] at this
    exact this hp
  | succ j =>
    exact ((Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).1 (ht j)) hp

def actF (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {U : Scheme.{0}}
    (s : U ⟶ Spec (CommRingCat.of A)) : Vec (d + 1) k U ⥤ Vec (d + 1) k U where
  obj v := ⟨actV M s v.1, fun p => actV_mem M hM hk s v.1 p (v.2 p)⟩
  map {v w} u := ⟨u.1, fun i => by
    cases i using Fin.cases with
    | zero => simp only [actV, Fin.cons_zero]; exact u.2 0
    | succ j =>
      simp only [actV, Fin.cons_succ]
      have : Fin.tail v.1 = (u.1 : Γ(U, ⊤)) • Fin.tail w.1 := funext fun l => by
        simp only [Fin.tail, Pi.smul_apply, smul_eq_mul]; exact u.2 l.succ
      rw [this, Matrix.mulVec_smul]; rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem comp_val {N k : ℕ} {U : Scheme.{0}} {X Y Z : Vec N k U} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (a ≫ b).1 = b.1 * a.1 := rfl

theorem eqToHom_val {N k : ℕ} {U : Scheme.{0}} {X Y : Vec N k U} (h : X = Y) : (eqToHom h).1 = 1 := by
  subst h; rfl

theorem actV_map (M : Matrix (Fin d) (Fin d) A) {V U : Scheme.{0}} (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A))
    (v : Fin (d + 1) → Γ(U, ⊤)) :
    (fun i => f.appTop.hom (actV M s v i)) = actV M (f ≫ s) (fun i => f.appTop.hom (v i)) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [actV]
  | succ j =>
    simp only [actV, Fin.cons_succ]
    rw [RingHom.map_mulVec, φ_comp, Matrix.map_map]
    rfl

theorem actF_map (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {V U : Scheme.{0}}
    (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A)) :
    actF M hM hk s ⋙ Vec.map (d + 1) k f = Vec.map (d + 1) k f ⋙ actF M hM hk (f ≫ s) := by
  refine CategoryTheory.Functor.ext (fun v => Subtype.ext (actV_map M f s v.1)) (fun v w u => ?_)
  apply Subtype.ext
  simp only [comp_val, eqToHom_val, one_mul]
  erw [eqToHom_val, mul_one]
  rfl

def actSp (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E : Spc}
    (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) : E ⟶ Pj (d + 1) k where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        ((show Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop from (a.app n).app U x) ⋙
          actF M hM hk (show U.unop ⟶ Spec (CommRingCat.of A) from (b.app n).app U x) :
          Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop)
      naturality := fun U U' f => by
        ext x
        have h1 := ConcreteCategory.congr_hom ((a.app n).naturality f) x
        have h2 := ConcreteCategory.congr_hom ((b.app n).naturality f) x
        refine (congrArg₂ (fun (F : Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U'.unop)
          (s : U'.unop ⟶ Spec (CommRingCat.of A)) => (F ⋙ actF M hM hk s : Fin (n.unop.len + 1) ⥤ _)) h1 h2).trans ?_
        exact congrArg (fun G => (show Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop from (a.app n).app U x) ⋙ G)
          (actF_map M hM hk f.unop (show U.unop ⟶ Spec (CommRingCat.of A) from (b.app n).app U x)).symm }
  naturality n m f := by
    ext U x
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (a.naturality f) U) x
    have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (b.naturality f) U) x
    exact (congrArg₂ (fun (F : Fin (m.unop.len + 1) ⥤ Vec (d + 1) k U.unop)
          (s : U.unop ⟶ Spec (CommRingCat.of A)) => (F ⋙ actF M hM hk s : Fin (m.unop.len + 1) ⥤ _)) h1 h2).trans rfl

theorem actSp_comp (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E' E : Spc}
    (g : E' ⟶ E) (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) :
    g ≫ actSp M hM hk a b = actSp M hM hk (g ≫ a) (g ≫ b) := by
  ext n U x; rfl

theorem actSp_incl (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {E : Spc}
    (a : E ⟶ Pj (d + 1) 1) (b : E ⟶ sp A) :
    actSp M hM le_rfl a b ≫ Pj.incl (d + 1) = actSp M hM (Nat.zero_le 1) (a ≫ Pj.incl (d + 1)) b := by
  ext n U x; rfl

theorem actSp_line (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E : Spc}
    (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) :
    actSp M hM hk a b ≫ Pj.line (d + 1) k = a ≫ Pj.line (d + 1) k := by
  ext n U x; rfl

theorem actSp_pt (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) (x : Fin d → A) :
    actSp M hM (Nat.zero_le 1) (Pj.pt (vec1 x)) (𝟙 (sp A)) = Pj.pt (vec1 (M.mulVec x)) := by
  ext n U f
  refine CategoryTheory.Functor.ext (fun _ => Subtype.ext ?_) (fun _ _ _ => ?_)
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      show ((M.map (φ _)).mulVec _) j = φ _ ((M.mulVec x) j)
      rw [RingHom.map_mulVec]
      rfl
  · apply Subtype.ext
    erw [comp_val, comp_val, eqToHom_val, eqToHom_val]
    simp only [one_mul, mul_one]
    erw [eqToHom_val]
    rfl

end ActPf

open ActPf in
theorem LeafAct_of : LeafAct := by
  intro d A _ M hM
  let gR : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A :=
    prod.lift (actSp M hM (Nat.zero_le 1) prod.fst prod.snd) prod.snd
  let gL : PR (d + 1) 1 A ⟶ PR (d + 1) 1 A := prod.lift (actSp M hM le_rfl prod.fst prod.snd) prod.snd
  have hw : gL ≫ (pr d A).hom = (pr d A).hom ≫ gR := by
    apply prod.hom_ext
    · simp only [pr, Arrow.mk_hom, Category.assoc, prod.map_fst, prod.lift_fst, gL, gR]
      rw [prod.lift_fst_assoc, actSp_incl, actSp_comp, prod.map_fst, prod.map_snd, Category.comp_id]
    · simp only [pr, Arrow.mk_hom, Category.assoc, prod.map_snd, Category.comp_id, prod.lift_snd, gL, gR]
  refine ⟨Arrow.homMk gL gR hw, ?_, ?_, ?_⟩
  · change gR ≫ prod.fst ≫ Pj.line (d + 1) 0 = _
    rw [prod.lift_fst_assoc, actSp_line]
  · change gR ≫ prod.snd = _
    exact prod.lift_snd _ _
  · intro x
    change chart x ≫ gR = _
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, actSp_comp, chart, prod.lift_fst, prod.lift_snd, actSp_pt, chart, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, chart, chart, prod.lift_snd, prod.lift_snd]

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafBZPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem LeafBZ_of : LeafBZ := by
  intro R _ K X U n W a ⟨b, hb0, hba⟩
  subst hba
  refine ⟨?_, ?_⟩
  · show ((K.X n).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    have e := congrArg (fun φ => φ.hom b) ((K.d (n - 1) n).hom.naturality (W.ι ⁻¹ᵁ U).ι.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [← e]
    have hb0' : ((K.X (n - 1)).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom b = 0 := hb0
    rw [hb0', map_zero]
  · show ((K.d n (n + 1)).hom.app (op W.toScheme)).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    change ((K.d (n - 1) n ≫ K.d n (n + 1)).hom.app (op W.toScheme)).hom b = 0
    rw [K.d_comp_d]
    rfl

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

