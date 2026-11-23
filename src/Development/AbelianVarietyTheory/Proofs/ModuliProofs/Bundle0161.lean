module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftRestrict
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AmpleDeterminantFramesPullbackOfIsAffineHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.RaisedAmple

theorem exists_closure {O F F' : Type} [CommRing O] [Field F] [Field F'] [CharZero F] [CharZero F'] (β : O →+* F)
    (k : F →+* F') (hβ : IsDedFrac β) (hk : k.Finite) :
    ∃ (O' : Type) (_ : CommRing O') (β' : O' →+* F') (b : O →+* O'), IsDedFrac β' ∧ β'.comp b = k.comp β ∧ b.Finite ∧
      ∀ x : F', IsIntegral ℤ x → x ∈ β'.range := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  letI := k.toAlgebra
  letI := (k.comp β).toAlgebra
  have : IsScalarTower O F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional F F' := hk
  have hD : IsDedekindDomain (integralClosure O F') := integralClosure.isDedekindDomain O F F'
  have hF : IsFractionRing (integralClosure O F') F' := integralClosure.isFractionRing_of_finite_extension F F'
  have hfin : Module.Finite O (integralClosure O F') := IsIntegralClosure.finite O F F' _
  refine ⟨integralClosure O F', inferInstance, algebraMap _ F', algebraMap O _, ⟨⟨inferInstance, hD⟩, inferInstance, hF⟩,
    rfl, hfin, fun x hx => ⟨⟨x, hx.tower_top⟩, rfl⟩⟩

theorem lift_lift {T X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (k : W ⟶ Z) (hk : g' ≫ g = k) (r : T ⟶ X)
    (s : T ⟶ W) (w : r ≫ f = s ≫ k) (r' : T ⟶ pullback f g) (h₁ : r' ≫ pullback.fst _ _ = r)
    (h₂ : r' ≫ pullback.snd _ _ = s ≫ g') :
    ∃ e : pullback f k ≅ pullback (pullback.snd f g) g', pullback.lift r' s h₂ = pullback.lift r s w ≫ e.hom := by
  subst hk
  refine ⟨(pullbackLeftPullbackSndIso f g g').symm, ?_⟩
  rw [Iso.symm_hom, Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst, h₁]
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd, pullback.lift_snd]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isIntegral_zeta {A : ℕ} (hA : 0 < A) : IsIntegral ℤ (zeta A) :=
  (Complex.isPrimitiveRoot_exp A hA.ne').isIntegral hA

theorem exists_coeff {l : Level H} (c : Coeff l) (l' : Level H) : ∃ c' : Coeff l', c.F ≤ c'.F := by
  have := c.fin
  have := GlobalTheory.BaseRing.finiteDimensional_KA l'
  have hM : 0 < l'.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l'.three_le) l'.A_pos
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l'.M'}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_zeta hM).tower_top
  refine ⟨⟨(c.F ⊔ KA l') ⊔ IntermediateField.adjoin ℚ {zeta l'.M'}, inferInstance, fun τ a => ?_, ?_, ?_⟩, ?_⟩
  · exact (le_sup_left.trans le_sup_left : c.F ≤ _) (c.conj τ a)
  · exact (le_sup_right : IntermediateField.adjoin ℚ {zeta l'.M'} ≤ _) (IntermediateField.subset_adjoin _ _ rfl)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_left.trans le_sup_left

theorem levComp_comp {D : Datum H} {l l' l'' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l'' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l'' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    {ξ : SABMap o''.t o'.t g} {ν : SABMap o'.t o.t r} (hd : l.Dvd l') (hd' : l'.Dvd l'') (h' : LevComp o'' o' g ξ)
    (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r)) (e : ν'.φ = ξ.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← Nat.div_mul_div hd'.1 hd.1, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.1 a), Category.assoc,
      h.1, Category.assoc]
  · rw [← Nat.div_mul_div hd'.2.2 hd.2.2, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.2 a),
      Category.assoc, h.2, Category.assoc]

theorem exists_isInc_of_mem {O : Type} [CommRing O] (i : O →+* ℂ) (hi : Function.Injective i) {S A : ℕ}
    (h₁ : (1 + H.rt0) / 2 ∈ i.range) (h₂ : (S : ℂ)⁻¹ ∈ i.range) (h₃ : zeta A ∈ i.range) :
    ∃ b : RZ H S A →+* O, IsInc (RZ H S A).subtype i b := by
  have hle : RZ H S A ≤ i.range := by
    unfold RZ
    rw [Subring.closure_le]
    rintro x (rfl | rfl | rfl) <;> assumption
  let e : O ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (Subring.inclusion hle), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))

theorem exists_cover (L₁ : Out.Laws) (L₂ : Out.Laws2) (L₃ : Out.Laws3) {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}
    (hN : ToroidalLevelCompatibility (H := H) (D := D)) {l l' : Level H} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O]
    [CommRing O'] {β : O →+* c.F} {β' : O' →+* c'.F} (Y : Model (Xo l) c β) (b : O →+* O') (d : l.Dvd l')
    (hc : c.F ≤ c'.F) (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    (hb : β'.comp b = (IntermediateField.inclusion hc).toRingHom.comp β) (hfin : b.Finite) :
    ∃ (Y' : Model (Xo l') c' β') (r : (Xo l').XF c' ⟶ (Xo l).XF c) (ν : SABMap Y'.oF.t Y.oF.t r)
      (a : (ofModel Y').Above (ofModel Y) b r ν), LevComp Y'.oF Y.oF r ν ∧ IsFinite a.π ∧ Surjective a.π := by
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l' (KA l') (KA l') (baseKA l') (baseKA l') (RingHom.id _) _ _ (Xo l').s
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ (Xo l').s)
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l').univ
  obtain ⟨k, r, ν, hr, hk, hl, hf, -, hs⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l l' c' o m0 d
  have hkk : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : (Xo l').XF c' ⟶ (Xo l).XF c, r' ≫ pullback.fst _ _ = r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨pullback.lift r (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom)
      (by rw [hr, hkk, spMap_comp, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m0.toSABMap ν r' hr₁
  have hl' : LevComp o Y.oF r' ν' :=
    ⟨fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.1, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.eta x).symm),
      fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.2, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.etaA x).symm)⟩
  obtain ⟨e, he⟩ := lift_lift (Xo l).s _ _ (spMap k) (by rw [hkk, spMap_comp]) r _ hr r' hr₁ hr₂
  have hf' : IsFinite (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hs' : Surjective (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hsm : Smooth (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) := by
    have := (Xo l').smooth
    have : Smooth (Xo l').s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  obtain ⟨C, ⟨a⟩⟩ := _root_.GlobalTheory.Models.Cpt.exists_above E H _ _ _ _ Y.oF.t β _ _ _
    (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) o.t β' (ofModel Y) b _ r' hr₂ ν' hβ hβ'
    hb hnorm hf'
  have hπ : IsFinite a.π := by
    have := a.fin
    have : IsFinite (spMap b) := (IsFinite.SpecMap_iff _).2 hfin
    rw [← pullback.lift_fst a.π C.s a.π_over]
    infer_instance
  have hr' : Surjective r' := by
    have : Surjective (spMap (IntermediateField.inclusion hc).toRingHom) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    rw [← pullback.lift_fst r' _ hr₂]
    infer_instance
  have hj : IsDominant (ofModel Y).j := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
    letI := β.toAlgebra
    exact (GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense).2.2.2.2.2.1
  have hd : IsDominant a.π := by
    have : IsDominant (C.j ≫ a.π) := by rw [a.j_comm]; infer_instance
    exact IsDominant.of_comp C.j a.π
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    r', ν', a, hl', hπ, surjective_of_isDominant_of_isClosed_range a.π a.π.isClosedMap.isClosed_range⟩

theorem amp_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N k T hN l₀ l B c O _ β Y hn hodd ⟨e, he⟩ hu hd hβ hR ⟨A⟩
  have hNpos : 0 < N := he ▸ pow_pos hn.pos e
  let l' : Level H := { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos hNpos }
  have d : l.Dvd l' := ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩
  have hNA : N ∣ l'.A := Nat.dvd_lcm_right _ _
  obtain ⟨c', hc⟩ := exists_coeff c l'
  have hkfin : (IntermediateField.inclusion hc).toRingHom.Finite := by
    have := c'.fin
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℚ c.F) ?_
    rw [Subsingleton.elim (RingHom.comp _ _) (algebraMap ℚ c'.F)]
    exact RingHom.finite_algebraMap.2 this
  obtain ⟨O', _, β', b, hβ', hb, hfin, hint⟩ := exists_closure β _ hβ hkfin
  obtain ⟨Y', r, ν, a, hl, hf, hs⟩ := exists_cover L₁ L₂ L₃ hN Y b d hc hβ hβ' hb hfin
  obtain ⟨b₁, r₁, ν₁, hb₁, hl₁, ⟨a₁⟩⟩ := hR
  have hbb : ∀ x, (c'.F.val.toRingHom.comp β') (b x) = (c.F.val.toRingHom.comp β) x := fun x =>
    congrArg Subtype.val (RingHom.congr_fun hb x)
  obtain ⟨ν₂, hν₂⟩ := LevelCover.sab_comp ν ν₁ rfl
  have hR' : Raises B Y' := ⟨b.comp b₁, r ≫ r₁, ν₂, fun x => (hbb _).trans (hb₁ x), levComp_comp hd d hl hl₁ ν₂ hν₂,
    ⟨(GlobalTheory.Models.above_comp E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C (ofModel Y) (ofModel Y') b₁ b r₁ ν₁ r ν ν₂
      a₁ a hν₂).choose⟩⟩
  have hi : Function.Injective (c'.F.val.toRingHom.comp β') := by
    letI := β'.toAlgebra
    have := hβ'.2.2
    exact Subtype.val_injective.comp (IsFractionRing.injective O' c'.F)
  obtain ⟨z, hz⟩ : ∃ z : RZ H n N →+* O', IsInc (RZ H n N).subtype (c'.F.val.toRingHom.comp β') z := by
    refine exists_isInc_of_mem _ hi
      ⟨b (b₁ ⟨(1 + H.rt0) / 2, Subring.subset_closure (by simp)⟩), (hbb _).trans (hb₁ _)⟩ ?_ ?_
    · obtain ⟨u, hu⟩ := hu.exists_right_inv
      refine ⟨b u, eq_inv_of_mul_eq_one_right ?_⟩
      rw [← map_natCast ((c'.F.val.toRingHom.comp β').comp b)]
      exact (map_mul ((c'.F.val.toRingHom.comp β').comp b) _ _).symm.trans (by rw [hu, map_one])
    · have hz : zeta N ∈ c'.F := by
        obtain ⟨m, hm⟩ := hNA
        have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => l'.A_pos.ne' (by rw [hm, h, mul_zero])
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
        have : zeta N = zeta l'.A ^ m := by
          rw [zeta, zeta, ← Complex.exp_nat_mul, hm]
          congr 1
          push_cast
          field_simp
        rw [this]
        exact pow_mem (c'.le (baseKA l').ζ.2) m
      obtain ⟨y, hy⟩ := hint ⟨zeta N, hz⟩
        ((isIntegral_algHom_iff c'.F.val.toRingHom.toIntAlgHom Subtype.val_injective).1 (isIntegral_zeta hNpos))
      exact ⟨y, congrArg Subtype.val hy⟩
  obtain ⟨g, hg, mu, -, hgf, -⟩ := GlobalTheory.AbelianLocusMap.exists_map_top L₁ L₂ L₃ hN B Y' z
    ⟨hd.1, hd.2.1, hd.2.2.trans d.2.2⟩ hNA hβ' hz hR'
  have haff : IsAffineHom g := by
    have : IsAffineHom (spMap z) := inferInstance
    have : IsAffineHom (pullback.fst T.s (spMap z)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
    rw [← pullback.lift_fst g Y'.s hg]
    infer_instance
  obtain ⟨A', -⟩ := _root_.GlobalTheory.AmpPull.ampFrames_pull_of_isAffineHom E H _ _ T.t Y'.t g mu _ A haff
  exact ⟨n ^ k, Y'.X, a.π, Y'.t, a.mu, hodd.pow, by rw [Nat.cast_pow]; exact hu.pow k, hf, hs, ⟨A'⟩⟩

end GlobalTheory.RaisedAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ShapePull

section Bundles

variable {X X' Y Y' : Scheme.{0}}

theorem iso_linComb_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} (H : LBIso L' (L.pull F)) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (e : ∀ k, ψ' k ≫ F = h ≫ ψ k) :
    LBIso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull h) := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.chartPull (chartPullId _) (chartPullOut L ψ ε h _ e) (iso_linComb ((isGen_iff w).1 hw) ψ' ε)

theorem iso_up {M N : LB Y} {M' N' : LB Y'} {h : Y' ⟶ Y} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (H : LBIso M N) : LBIso M' N' :=
  LBIso.trans hM' (pull_isLB hM h) hN' a (LBIso.trans (pull_isLB hM h) (pull_isLB hN h) hN'
    (H.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull N h h rfl)) b.symm)

end Bundles

section Field

variable {K : Type} [Field K] {S' : Scheme.{0}} (f : S' ⟶ Sp K)

theorem exists_point [Nonempty S'] :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (x : Sp K' ⟶ S'), x ≫ f = spMap i := by
  obtain ⟨y⟩ := ‹Nonempty S'›
  obtain ⟨i, hi⟩ := Spec.map_surjective (S'.fromSpecResidueField y ≫ f)
  exact ⟨S'.residueField y, inferInstance, i.hom, S'.fromSpecResidueField y, hi.symm⟩

variable {f}

theorem epi_of_isPullback [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) : Epi h := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have a : Flat f := inferInstance
  have b : Surjective f := inferInstance
  have : Flat h := MorphismProperty.of_isPullback (P := @Flat) H.flip a
  have : Surjective h := MorphismProperty.of_isPullback (P := @Surjective) H.flip b
  exact Flat.epi_of_flat_of_surjective h

theorem iso_down [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) (h₁ : Smooth p₀) (h₂ : IsProper p₀) (h₃ : GeometricallyConnected p₀)
    {M N : LB X₀} {M' N' : LB X} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (c : LBIso M' N') : LBIso M N := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have P : IsPullback (pullback.fst p x ≫ h) (pullback.snd p x) p₀ (spMap i) :=
    hx ▸ (IsPullback.of_hasPullback p x).paste_horiz H
  have d : LBIso (M.pull h) (N.pull h) := LBIso.trans (pull_isLB hM h) hM' (pull_isLB hN h) a.symm
    (LBIso.trans hM' hN' (pull_isLB hN h) c b)
  exact (_root_.GlobalTheory.lb_gen_iso_descend_field K K' i X₀ _ p₀ _ _ h₁ h₂ h₃ P).2 M N hM hN (d.chartPull
    (chartPullSame M _ _ _ (pullback.fst p x) fun _ => rfl) (chartPullSame N _ _ _ (pullback.fst p x) fun _ => rfl))

theorem relAmple_down [Nonempty S'] {A : Over (Sp K)} [GrpObj A] (hA : IsAbelianScheme A) {A' : Over S'}
    {φ : A'.left ⟶ A.left} (H : IsPullback φ A'.hom A.hom f) {M : LB A.left} {M' : LB A'.left} (hM : M.IsLB)
    (hM' : M'.IsLB) (a : LBIso M' (M.pull φ)) (c : Out.RelAmple A' M') : Out.RelAmple A M := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) H hA.proper
  have P : IsPullback (pullback.fst A.hom (spMap i)) (pullback.snd A.hom (spMap i)) A.hom (x ≫ f) :=
    hx ▸ IsPullback.of_hasPullback A.hom (spMap i)
  let ψ : pullback A.hom (spMap i) ⟶ A'.left := H.lift (pullback.fst _ _) (pullback.snd _ _ ≫ x)
    (P.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ φ = pullback.fst _ _ := H.lift_fst _ _ _
  have Q : IsPullback ψ (pullback.snd A.hom (spMap i)) A'.hom x :=
    IsPullback.of_right (hψ ▸ P) (H.lift_snd _ _ _) H
  exact _root_.GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K K' i A ((Over.pullback (spMap i)).obj A) (pullback.fst _ _) M (M'.pull ψ) hA
    (isGrpPullback_pullback A _) hM (pull_isLB hM' ψ)
    (a.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M' ψ ψ rfl) (chartPullSame M _ _ _ ψ fun _ => hψ.symm))
    (AmpleBaseChange.relAmple_of_isPullback hM' c Q)

end Field

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

section Points

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem eq_up {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) (hy : pushPt h.1.w y' = U ≫ y)
    (e : x = y) : x' = y' :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) (hx.trans (e ▸ hy.symm))) (by rw [Over.w, Over.w]))

theorem eq_down (hU : Epi U.left) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x)
    (hy : pushPt h.1.w y' = U ≫ y) (e : x' = y') : x = y :=
  Over.OverMorphism.ext ((cancel_epi U.left).1 (congrArg (fun q => q.left) (hx.symm.trans (e ▸ hy))))

theorem push_mul {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) (hy : pushPt h.1.w y' = U ≫ y) :
    pushPt h.1.w (x' * y') = U ≫ (x * y) :=
  (map_mul (pushHom h T') x' y').trans ((congrArg₂ (· * ·) hx hy).trans (MonObj.comp_mul U x y).symm)

theorem push_linComb {n : ℕ} {x' : Fin n → (T' ⟶ G')} {x : Fin n → (T ⟶ G)} (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (a : Fin n → ℕ) : pushPt h.1.w (Out.linComb x' a) = U ≫ Out.linComb x a := by
  refine (map_list_prod (pushHom h T') _).trans (Eq.trans ?_ (map_list_prod (preHom (G := G) U) _).symm)
  rw [List.map_ofFn, List.map_ofFn]
  refine congrArg (fun z => (List.ofFn z).prod) (funext fun i => ?_)
  exact (map_pow (pushHom h T') _ _).trans ((congrArg (· ^ a i) (hx i)).trans (map_pow (preHom (G := G) U) _ _).symm)

theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  rw [← Category.assoc, ← hx]
  refine Over.OverMorphism.ext ?_
  show (x'.left ≫ _) ≫ _ = (x'.left ≫ _) ≫ _
  rw [Category.assoc, ha, Category.assoc]

theorem iso_cubeLB_pull [IsCommMonObj G] [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left}
    (H : LBIso L' (L.pull φ)) {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : pushPt h.1.w a' = U ≫ a)
    (hb : pushPt h.1.w b' = U ≫ b) : LBIso (cubeLB G' ![a', b'] L') ((cubeLB G ![a, b] L).pull U.left) :=
  iso_linComb_pull H _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
    fin_cases i
    exacts [ha, hb]) I.down

end Points

def sqMap : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))

theorem push_fst : pushPt h.1.w (fst G' G') = sqMap h ≫ fst G G := (lift_fst _ _).symm

theorem push_snd : pushPt h.1.w (snd G' G') = sqMap h ≫ snd G G := (lift_snd _ _).symm

theorem isPullback_sqMap : IsPullback (sqMap h).left (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : (sqMap h).left ≫ (fst G G).left = (fst G' G').left ≫ φ := congrArg (fun q => q.left) (push_fst h).symm
  have e₂ : (sqMap h).left ≫ (snd G G).left = (snd G' G').left ≫ φ := congrArg (fun q => q.left) (push_snd h).symm
  have A : IsPullback (snd G G).left (fst G G).left G.hom G.hom := (IsPullback.of_hasPullback G.hom G.hom).flip
  have A' : IsPullback (snd G' G').left (fst G' G').left G'.hom G'.hom := (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have B := A'.paste_horiz h.1
  rw [← e₂, ← h.1.w] at B
  have C := (IsPullback.of_right B e₁ A).paste_vert h.1
  rwa [Over.w, Over.w] at C

def selfMap : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w

theorem push_id : pushPt h.1.w (𝟙 G') = selfMap h ≫ 𝟙 G :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem push_end {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w a' = selfMap h ≫ a :=
  Over.OverMorphism.ext ha

end Group

def baseMap {S S' : Scheme.{0}} (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
  Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.ShapePull

namespace GlobalTheory

open ShapePull

theorem shape_prim_pull_and_descend :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (w w' : J) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s'), TMap t' t f → (t.Shape Mat κ → t'.Shape Mat κ) ∧ (t.Prim w w' → t'.Prim w w') ∧ ∀ (K : Type) [Field K] (e : S = Sp K), IsAffine S' → Nonempty S' → (t'.Shape Mat κ → t.Shape Mat κ) ∧ (IsIntegral S' → t'.Prim w w' → t.Prim w w') := by
  intro o _ g k J b Mat κ w w' S S' s s' f t t' ⟨φ, h, hL, hpt, hact⟩
  letI := t.ab.comm
  letI := t'.ab.comm
  have lb : ∀ {X Y : Scheme.{0}} {L : LB X} (_ : L.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ),
      (LB.LinComb L ψ ε).IsLB := fun hL _ _ _ _ => DVR.linComb_isLB _ hL _ _
  have pt : ∀ i, pushPt h.1.w (t'.pt i) = baseMap f ≫ t.pt i := fun i => Over.OverMorphism.ext (hpt i)
  have p₁ := fun i j => push_comp h _ (pt i) (hact j)
  have p₂ : ∀ a, pushPt h.1.w (t'.lab a) = baseMap f ≫ t.lab a := fun a => push_linComb h _ pt _
  have i₁ : ∀ j, LBIso (LB.LinComb t'.L (K := Fin 2) ![𝟙 t'.A.left, (t'.act j).left] ![(κ : ℤ), -1])
      ((LB.LinComb t.L (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1]).pull φ) := fun j =>
    iso_linComb_pull hL _ _ _ φ fun i => by
      fin_cases i
      exacts [(Category.id_comp _).trans (Category.comp_id _).symm, hact j]
  have p₃ := push_mul h _ (push_end h (hact w)) (push_end h (hact w'))
  have i₂ := iso_cubeLB_pull h _ hL (push_comp h _ (push_fst h) (hact w)) (push_snd h)
  have i₃ := iso_cubeLB_pull h _ hL (push_fst h) (push_comp h _ (push_snd h) (hact w'))
  have i₄ := iso_cubeLB_pull h _ hL (push_id h) (push_end h (hact w))
  refine ⟨fun H j => ⟨fun i => eq_up h _ (p₁ i j) (p₂ _) ((H j).1 i), ?_⟩, fun H => ⟨eq_up h _ p₃ (push_id h) H.1,
    iso_up (lb t.isLB _ _) (lb t.isLB _ _) (lb t'.isLB _ _) (lb t'.isLB _ _) i₂ i₃ H.2.1,
    iso_up t.isLB (lb t.isLB _ _) t'.isLB (lb t'.isLB _ _) hL i₄ H.2.2⟩, ?_⟩
  · exact (pol_pull S S' t.A t'.A f φ _ _ (lb t.isLB _ _) (lb t'.isLB _ _) t.ab h (i₁ j)).2.1 (H j).2
  rintro K _ rfl - _
  have hf : Epi f := epi_of_isPullback (IsPullback.id_vert f)
  have hφ : Epi φ := epi_of_isPullback h.1
  have := t.ab.smooth
  have := t.ab.proper
  have := t.ab.geomConnected
  have pr : IsProper (t.A ⊗ t.A).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  exact ⟨fun H j => ⟨fun i => eq_down h _ hf (p₁ i j) (p₂ _) ((H j).1 i),
      relAmple_down t.ab h.1 (lb t.isLB _ _) (lb t'.isLB _ _) (i₁ j) (H j).2⟩,
    fun _ H => ⟨eq_down h _ hφ p₃ (push_id h) H.1,
      iso_down (isPullback_sqMap h) (smooth_tensorObj_hom _ _) pr (geometricallyConnected_tensorObj_hom _ _)
        (lb t.isLB _ _) (lb t.isLB _ _) (lb t'.isLB _ _) (lb t'.isLB _ _) i₂ i₃ H.2.1,
      iso_down h.1 ‹_› ‹_› ‹_› t.isLB (lb t.isLB _ _) t'.isLB (lb t'.isLB _ _) hL i₄ H.2.2⟩⟩

end GlobalTheory
end
end

