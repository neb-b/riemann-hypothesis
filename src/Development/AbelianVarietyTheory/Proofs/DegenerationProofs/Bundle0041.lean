module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.TorsionDivisible

theorem hom_ext_of_rationalPoints {K : Type} [Field K] [IsAlgClosed K] {X Y : Over (Sp K)}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsProper Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp K)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  let p : 𝟙_ (Over (Sp K)) ⟶ X :=
    Over.homMk (pointOfClosedPoint (K := K) X.hom x hx) (pointOfClosedPoint_comp (K := K) X.hom x hx)
  have h1 : pointOfClosedPoint (K := K) X.hom x hx ≫ f.left =
      pointOfClosedPoint (K := K) X.hom x hx ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) =
      g.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint K)) h1
  have h3 := pointOfClosedPoint_apply (K := K) X.hom x hx (IsLocalRing.closedPoint K)
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))

theorem finite_fibre_points {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Over (Sp K)} [LocallyOfFiniteType X.hom] (f : X ⟶ Y)
    [IsFinite f.left] (y : 𝟙_ (Over (Sp K)) ⟶ Y) :
    Finite {x : 𝟙_ (Over (Sp K)) ⟶ X // x ≫ f = y} := by
  have hfin : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}).Finite :=
    f.left.finite_preimage_singleton _
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun x => (⟨x.1.left (IsLocalRing.closedPoint K), by
      have h := congrArg (fun u => u.left (IsLocalRing.closedPoint K)) x.2
      exact h⟩ : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}))) ?_
  intro a b hab
  refine Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_apply_closedPoint_eq (K := K) X.hom (Over.w a.1) (Over.w b.1)
    (congrArg Subtype.val hab)

theorem finite_torsion_and_divisible :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ ∀ f : B ⟶ B, IsMonHom f → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ^ n = 1 → x ≫ f = 1) → ∃ g : B ⟶ B, IsMonHom g ∧ f = g ^ n := by
  intro k _ _ B _ hB n hn
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of k)).inv.hom
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion B hu
  refine ⟨?_, fun f hf hker => ?_⟩
  · have := finite_fibre_points (mulN B n) 1
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ mulN B n = 1) fun x => by
      rw [GrpTangent.comp_mulN])
  · have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
    have hc : IsClopen (Set.range (mulN B n).left) :=
      ⟨(mulN B n).left.isClosedMap.isClosed_range, (mulN B n).left.isOpenMap.isOpen_range⟩
    have h5 : Surjective (mulN B n).left :=
      ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))⟩
    have : IsReduced (torsion B n).left := isReduced_of_smooth_of_isReduced (torsion B n).hom
    have hι : torsion.ι B n ≫ mulN B n = 1 := by
      rw [Hom.one_def]
      exact pullback.condition.trans (congrArg (· ≫ η[B]) (toUnit_unique _ _))
    have h6 : torsion.ι B n ≫ f = 1 := hom_ext_of_rationalPoints _ _ fun x => by
      rw [← Category.assoc, MonObj.comp_one]
      refine hker _ ?_
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have h7 : ∀ (T : Over (Sp k)) (x : T ⟶ B), x ^ n = 1 → x ≫ f = 1 := fun T x hx => by
      have e : x ≫ mulN B n = toUnit T ≫ η[B] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
      obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion B n, y ≫ torsion.ι B n = x :=
        ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
      rw [← e', Category.assoc, h6, MonObj.comp_one]
    have hm : Out.mulA B n = mulN B n := (GrpTangent.mulN_eq_pow B n).symm
    have : Etale (Out.mulA B n).left := hm ▸ h2
    have : IsFinite (Out.mulA B n).left := hm ▸ h1
    have : Surjective (Out.mulA B n).left := hm ▸ h5
    obtain ⟨φ, hφ⟩ := DivisibleHom.exists_factor n f h7
    have : IsMonHom (Out.mulA B n ≫ φ) := hφ ▸ hf
    have : IsMonHom φ := DivisibleHom.isMonHom_of_factor n φ
    exact ⟨φ, this, by rw [← hφ, DivisibleHom.mulA_comp]⟩

end GlobalTheory.TorsionDivisible
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataIsoOfTwoWitnessesStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_iso_of_two_witnesses : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (W : ArcWit Y a I f u χ) (W' : ArcWit Y a I f u χ'), ∃ hD : IsPullDeg (RingHom.id R) W.P.D.toPre W'.P.D.toPre, (∀ y, hD.xe (W'.e y) = W.e y) ∧ (∀ x, (letI := H.starRing; W'.P.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (W.P.oD.onB.act x))) ∧ ∃ w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ)), W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ ∧ HEq W'.w w' ∧ Tri W.w hD.w w' := by
  first | exact @GlobalTheory.WitnessData.witness_data_iso | exact GlobalTheory.WitnessData.witness_data_iso | (intros; apply GlobalTheory.WitnessData.witness_data_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationSeriesTermsNest
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.Nest
variable {O : Type} [CommRing O] (N : NumD O)

theorem wQ_nest {n k l : ℕ} (hk : Odd k) (hl : Odd l) (e : l = n * (k * n)) (p'' : N.QT l) (p : N.QT k)
    (hy : p''.1.1 = p.1.1 ^ n) (hg : p.1.2 = p''.1.2 ^ n) :
    N.wQ p * mulq N.θ N.σ n p''.1.2.b ^ k = N.wQ p'' := by
  subst e
  have hb : p.1.2.b = p''.1.2.b ^ n := by rw [hg, NumD.Gt.pow_b]
  have hc : N.c p.1.1.toAdd = p''.1.2.b ^ (k * n) := by
    rw [← N.QT_pow_b p, hb, ← pow_mul']
  have hy' : p''.1.1.toAdd = n • p.1.1.toAdd := by rw [hy, toAdd_pow]
  obtain ⟨hA, hB⟩ := (SymLift.wQ_iff N hk p (N.wQ p)).mp rfl
  refine (SymLift.wQ_iff N hl p'' _).mpr ⟨?_, ?_⟩
  · simp only [NumD.tk, hg, NumD.Gt.pow_b] at hA
    have ps := NumD.Gt.pow_s p''.1.2 n p.1.1.toAdd
    have ss := PsiQuadratic.s_nsmul N p''.1.2 n p.1.1.toAdd
    have db := (_root_.GlobalTheory.Ex.mulq_laws O N.toNumB n 0 p''.1.2.b p''.1.2.b).2.2.1
    have cm1 := CubeBalance.cubN_mul N.cub n (k * n) p''.1.2.b p''.1.2.b
    have cm2 := CubeBalance.cubN_mul N.cub k n p''.1.2.b p''.1.2.b
    have sw := CubeBalance.cubN_swap N.cub k n (p''.1.2.b ^ n) p''.1.2.b
    rw [hc] at ps ss
    rw [← pow_mul'] at sw
    simp only [NumD.tk]
    rw [hy']
    apply Additive.ofMul.injective
    replace hA := congrArg Additive.ofMul hA
    replace ps := congrArg Additive.ofMul ps
    replace ss := congrArg Additive.ofMul ss
    replace db := congrArg Additive.ofMul db
    replace cm1 := congrArg Additive.ofMul cm1
    replace cm2 := congrArg Additive.ofMul cm2
    replace sw := congrArg Additive.ofMul sw
    simp only [ofMul_mul, ofMul_pow] at hA ps ss db cm1 cm2 sw ⊢
    linear_combination (norm := module) hA - (k : ℤ) • db + sw + ps - ss - cm1 - (n : ℤ) • cm2
  · rw [hb] at hB
    have hψ := PsiQuadratic.ψ_nsmul N n p.1.1.toAdd
    have hm1 := (_root_.GlobalTheory.Ex.mulq_laws O N.toNumB n (k * n) p''.1.2.b p''.1.2.b).1
    have hm2 := (_root_.GlobalTheory.Ex.mulq_laws O N.toNumB k n p''.1.2.b p''.1.2.b).1
    rw [hc] at hψ
    rw [hy']
    apply Additive.ofMul.injective
    replace hB := congrArg Additive.ofMul hB
    replace hψ := congrArg Additive.ofMul hψ
    replace hm1 := congrArg Additive.ofMul hm1
    replace hm2 := congrArg Additive.ofMul hm2
    simp only [ofMul_mul, ofMul_pow] at hB hψ hm1 hm2 ⊢
    linear_combination (norm := module)
      ((n : ℤ) ^ 2) • hB - hψ - hm1 - ((n : ℤ) ^ 2) • hm2

theorem txT_nest : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n m : ℕ), Odd n → Odd m → ∀ (p'' : N.QT ((n * m) ^ 2)) (p : N.QT (m ^ 2)), p''.1.1 = p.1.1 ^ n → p.1.2 = p''.1.2 ^ n → ∀ χ, N.txT (n * m) p'' χ = N.txT m p χ := by
  intro O _ N n m hn hm p'' p hy hg χ
  have hw := wQ_nest N hm.pow (hn.mul hm).pow (by ring) p'' p hy hg
  have hq := (_root_.GlobalTheory.Ex.mulq_laws O N.toNumB m n p''.1.2.b p''.1.2.b).1
  rw [mul_comm m n] at hq
  have hb : p.1.2.b = p''.1.2.b ^ n := by rw [hg, NumD.Gt.pow_b]
  have hu : N.wQ p'' / mulq N.θ N.σ (n * m) p''.1.2.b = N.wQ p / mulq N.θ N.σ m p.1.2.b := by
    rw [← hw, hq, hb, mul_div_mul_right_eq_div]
  simp only [NumD.txT]
  rw [hu, hg, ← pow_mul]

end GlobalTheory.Ex.Nest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsModelMapDefinedWeakNeronFamily
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SS.WeakNeronDef

theorem fromSpecStalk_comp {X : Scheme.{0}} {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p =
      Spec.map ((Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp

theorem isDominant_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (x : X) : IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_j (N : Model R A) : IsPullback N.j A.hom N.Y.hom (spMap (algebraMap R K)) := by
  have h := Over.w N.e.inv
  have : IsIso N.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map N.e.inv))
  refine IsPullback.of_iso (IsPullback.of_hasPullback N.Y.hom (spMap (algebraMap R K)))
    (asIso N.e.inv.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j]
  · simp [← h]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem exists_dvr_point (N : Model R A) [IsIntegral N.Y.left] (hN : N.Irr) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ y ∈ N.sp, IsDiscreteValuationRing (N.Y.left.presheaf.stalk y) ∧
      Irreducible (((Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫
        N.Y.left.presheaf.germ ⊤ y trivial).hom ϖ) := by
  have := N.smooth
  have hs := IsPullback.of_hasPullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  set i := pullback.fst N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) with hi
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : IsClosedImmersion i := by rw [hi]; infer_instance
  have := GlobalTheory.isReduced_of_smooth_of_isReduced
    (pullback.snd N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  have hr : Set.range i = N.sp := Set.ext fun x => DvrModel.mem_range_special hs x
  have : IrreducibleSpace ↥(pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
    have h1 : IrreducibleSpace (Set.range i) := by
      rw [hr]; exact Subtype.irreducibleSpace hN
    exact i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.surjective.irreducibleSpace
      i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.continuous
  have := isIntegral_of_irreducibleSpace_of_isReduced
    (pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  exact ⟨i (genericPoint _), hr.le ⟨_, rfl⟩, DvrModel.isDiscreteValuationRing_stalk_generic hϖ hs⟩

end GlobalTheory.SS.WeakNeronDef

namespace GlobalTheory.SS

open WeakNeronDef

theorem exists_defAt_of_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  intro R K _ _ _ _ _ _ A _ I M hM N hN
  have := N.smooth
  have hK := isPullback_j N
  have : IsIntegral N.Y.left := DvrModel.isIntegral hK
  have : IsOpenImmersion N.j := DvrModel.isOpenImmersion_generic hK
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨y, hy, hd, hi⟩ := exists_dvr_point N hN hϖ
  let ψ := (Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫ N.Y.left.presheaf.germ ⊤ y trivial
  let R' : Type := N.Y.left.presheaf.stalk y
  let K' : Type := FractionRing R'
  letI : Algebra R R' := ψ.hom.toAlgebra
  let s : Sp R' ⟶ N.Y.left := N.Y.left.fromSpecStalk y
  have hs : s ≫ N.Y.hom = spMap (algebraMap R R') := fromSpecStalk_comp N.Y.hom y
  have hi' : Irreducible (algebraMap R R' ϖ) := hi
  have := DvrModel.isLocalization_away (K := K) hϖ
  have hu : IsUnit (((algebraMap R' K').comp (algebraMap R R')) ϖ) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R' K')).2 hi'.ne_zero).isUnit
  let k : K →+* K' := IsLocalization.Away.lift ϖ hu
  have hk : spMap k ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R')) := by
    rw [← Spec.map_comp, ← IsLocalization.Away.lift_comp ϖ (S := K) hu]; rfl
  have hw : (spMap (algebraMap R' K') ≫ s) ≫ N.Y.hom = spMap k ≫ spMap (algebraMap R K) := by
    rw [hk, Category.assoc, hs, ← Spec.map_comp]; rfl
  let a := hK.lift _ _ hw
  have ha : a ≫ N.j = spMap (algebraMap R' K') ≫ s := hK.lift_fst _ _ _
  have ha' : a ≫ A.hom = spMap k := hK.lift_snd _ _ _
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' (by
    rw [hϖ.maximalIdeal_eq, hi'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]) a
    (by rw [← Category.assoc, ha', hk])
  have := (M i).smooth
  have := (M i).sep
  obtain ⟨U, hU, g, h₁, h₂⟩ := spread_out_of_isGermInjective' N.Y.hom (M i).Y.hom (x := y) b (hb.trans hs.symm)
  refine ⟨i, y, hy, U, g, hU, h₂, ?_⟩
  let t : Sp R' ⟶ U.toScheme := U.fromSpecStalkOfMem y hU
  have ht : t ≫ U.ι = s := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have hP := isPullback_morphismRestrict N.j U
  have hc : a ≫ N.j = (spMap (algebraMap R' K') ≫ t) ≫ U.ι := by rw [ha, Category.assoc, ht]
  let c := hP.lift _ _ hc.symm
  have hc₁ : c ≫ (N.j ⁻¹ᵁ U).ι = a := hP.lift_snd _ _ _
  have hc₂ : c ≫ (N.j ∣_ U) = spMap (algebraMap R' K') ≫ t := hP.lift_fst _ _ _
  have : IsDominant s := isDominant_fromSpecStalk _ _
  have := GlobalTheory.isDominant_spMap_of_isFractionRing R' K'
  have : IsDominant (c ≫ (N.j ⁻¹ᵁ U).ι ≫ N.j) := by
    rw [← Category.assoc, hc₁, ha]; infer_instance
  have : IsDominant c := IsDominant.of_comp_of_isOpenImmersion c ((N.j ⁻¹ᵁ U).ι ≫ N.j)
  refine ext_of_isDominant_of_isSeparated (M i).Y.hom ?_ c ?_
  · simp only [Category.assoc, h₂, Over.id_left, Category.id_comp, Model.j_hom]
    rw [morphismRestrict_ι_assoc, Model.j_hom]
  · simp only [Over.id_left, Category.id_comp]
    rw [← Category.assoc, hc₂, ← Category.assoc, hc₁, ← hb', Category.assoc]
    exact congrArg _ h₁.symm

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOneParameterSubgroupOfRationalFamily
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

namespace GlobalTheory.SS.ArcInf

theorem smConn_gm (k : Type) [Field k] : SmConn (Gm (Sp k)) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

noncomputable def selfIso (k : Type) [CommRing k] : algOver k k ≅ 𝟙_ (Over (Sp k)) :=
  Over.isoMk (Iso.refl _) (by
    show 𝟙 _ ≫ 𝟙 _ = spMap (algebraMap k k)
    rw [Category.comp_id]
    exact (Spec.map_id _).symm)

theorem algHom_algebraMap_eq_eval {k B : Type} [CommRing k] [CommRing B] [Algebra k B]
    [Algebra (Polynomial k) B] [IsScalarTower k (Polynomial k) B] (x : B →ₐ[k] k) (q : Polynomial k) :
    x (algebraMap (Polynomial k) B q) = q.eval (x (algebraMap (Polynomial k) B Polynomial.X)) := by
  have h := Polynomial.aeval_algHom_apply (x.comp (IsScalarTower.toAlgHom k (Polynomial k) B))
    Polynomial.X q
  rw [Polynomial.aeval_X_left_apply, Polynomial.coe_aeval_eq_eval] at h
  exact h.symm

theorem exists_oneParameter_of_rational_family : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), SmConn G → IsChart G j ε f → Pd ≠ 0 → (∃ i, P i ≠ 0) → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → (∀ t t', t ≠ 0 → t' ≠ 0 → Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t * t') ≠ 0 → (algOverHom (ψ t) ≫ j) * (algOverHom (ψ t') ≫ j) = algOverHom (ψ (t * t')) ≫ j) → ∃ F : Gm (Sp k) ⟶ G, IsMonHom F ∧ F ≠ 1 := by
  intro k _ _ G _ A _ _ j ε r f Pd P ψ hG hc hPd hP hψ hmul
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.exists_algHom_localizationAway_of_rational_points k A r f Pd P ψ hc.2.2.1 hPd hψ
  obtain ⟨jj, hjj, hjm⟩ := _root_.GlobalTheory.SS.TorOpen.exists_open_part k Pd
  have hq : Polynomial.X * Pd ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hPd
  have hinj : Function.Injective
      (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * Pd))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hq)
  have hnt : Nontrivial (Localization.Away (Polynomial.X * Pd)) := hinj.nontrivial
  have hu : IsUnit (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * Pd))
      (Polynomial.X * Pd)) := IsLocalization.Away.algebraMap_isUnit _
  have hpt : ∀ x : Localization.Away (Polynomial.X * Pd) →ₐ[k] k,
      x (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 ∧
      Pd.eval (x (algebraMap (Polynomial k) _ Polynomial.X)) ≠ 0 ∧
      x.comp χ = ψ (x (algebraMap (Polynomial k) _ Polynomial.X)) := by
    intro x
    have h := (hu.map x).ne_zero
    rw [algHom_algebraMap_eq_eval, Polynomial.eval_mul, Polynomial.eval_X] at h
    have h1 := left_ne_zero_of_mul h
    have h2 := right_ne_zero_of_mul h
    refine ⟨h1, h2, hc.hom_ext fun i => mul_right_cancel₀ h2 ?_⟩
    rw [hψ _ h1 h2, AlgHom.comp_apply, ← algHom_algebraMap_eq_eval x Pd, ← map_mul, hχ,
      algHom_algebraMap_eq_eval x (P i)]
  obtain ⟨F, hF, hFj⟩ := GlobalTheory.GenericHom.exists_monHom_extension k (Gm (Sp k)) G
    (algOver k (Localization.Away (Polynomial.X * Pd))) (smConn_gm k) hG jj (algOverHom χ ≫ j) hjj
    (inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away (Polynomial.X * Pd))))) (by
      intro x y z h
      obtain ⟨x', hx⟩ := algOverHom_surjective ((selfIso k).hom ≫ x)
      obtain ⟨y', hy⟩ := algOverHom_surjective ((selfIso k).hom ≫ y)
      obtain ⟨z', hz⟩ := algOverHom_surjective ((selfIso k).hom ≫ z)
      have h' := hjm x' y' z' (by
        rw [hx, hy, hz, Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul, h])
      obtain ⟨a1, a2, a3⟩ := hpt x'
      obtain ⟨b1, b2, b3⟩ := hpt y'
      obtain ⟨c1, c2, c3⟩ := hpt z'
      have hm := hmul _ _ a1 b1 a2 b2 (h' ▸ c2)
      rw [h', ← a3, ← b3, ← c3, algOverHom_comp, algOverHom_comp, algOverHom_comp, hx, hy, hz] at hm
      simp only [Category.assoc] at hm
      rw [← MonObj.comp_mul] at hm
      exact (cancel_epi (selfIso k).hom).1 hm)
  refine ⟨F, hF, fun h1 => ?_⟩
  obtain ⟨i, hi⟩ := hP
  have e : χ = (Algebra.ofId k _).comp ε := by
    apply eq_of_comp_eq hc.1
    rw [← hFj, h1, MonObj.comp_one, algOverHom_comp, Category.assoc, hc.2.1, MonObj.comp_one]
  have h2 := hχ i
  rw [e, AlgHom.comp_apply, hc.2.2.2, _root_.map_zero, zero_mul] at h2
  exact hi (hinj (h2.symm.trans (_root_.map_zero _).symm))

end GlobalTheory.SS.ArcInf
end

