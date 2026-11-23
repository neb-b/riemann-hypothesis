module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivLiftOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyFormalUniformisationTower
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.FormalTower

theorem exists_tq_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] (φ : A →+* A')
    (hφ : Function.Surjective φ) (hn : IsNilpotent (RingHom.ker φ)) {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Sp A')) [GrpObj G₀]
    (F : G₀.left ⟶ G.left) (hF : IsGrpPullback G₀ G (spMap φ) F) (Q₀ : TQ G₀ X) :
    ∃ Q : TQ G X, TorusCompat (spMap φ) F Q₀.i Q.i := by
  let e := RingHom.quotientKerEquivOfSurjective hφ
  let r : Sp (A ⧸ RingHom.ker φ) ⟶ Sp A' := spMap e.symm.toRingHom
  let s : Sp A' ⟶ Sp (A ⧸ RingHom.ker φ) := spMap e.toRingHom
  have hr : r ≫ spMap φ = red (RingHom.ker φ) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact e.symm_apply_eq.2 rfl
  have hs : s ≫ r = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact e.apply_symm_apply a
  have h₁ := isGrpPullback_pullback G₀ r
  obtain ⟨Q₁, c₁⟩ := exists_tq_baseChange _ _ _ X _ _ _ h₁ Q₀
  obtain ⟨Q, c⟩ := TorusQuotLift.main A _ hn X G _ _ ((h₁.comp hF).congr hr rfl) Q₁
  refine ⟨Q, ?_⟩
  rw [torusCompat_iff] at c c₁ ⊢
  rw [← hr, bcMap_comp, ← Category.assoc, ← c₁, Category.assoc, Category.assoc] at c
  have c' := congrArg (SplitTorus.bcMap s X ≫ ·) c
  simp only [← Category.assoc, ← bcMap_comp, hs, bcMap_id, Category.id_comp] at c'
  exact c'

theorem isCPPullback_of_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G]
    [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {P : CP G} {P' : CP G'}
    {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left}
    {F'' : G''.left ⟶ G.left} (h : IsCPPullback P' P f F) (h'' : IsCPPullback P'' P f'' F'')
    (hF : IsGrpPullback G'' G' f' F') (e : f' ≫ f = f'') (e' : F' ≫ F = F'') : IsCPPullback P'' P' f' F' := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, _, h''⟩ := h''
  exact ⟨hF, TowerEx.exists_cancel h h'' hF e e'⟩

theorem exists_isCPPullback_desc {S S' : Scheme.{0}} [ConnectedSpace S'] {f : S' ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    [ConnectedSpace G'.left] {F : G'.left ⟶ G.left} {P : CP G} {P' : CP G'} (hP : IsCPPullback P' P f F)
    {Q : TQ G X} {Q' : TQ G' X} (h : TorusCompat f F Q'.i Q.i) (D : Q.Desc P) (D' : Q'.Desc P') :
    ∃ β : Q'.B.left ⟶ Q.B.left, IsCPPullback D'.M D.M f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left := by
  obtain ⟨hF, _, hP⟩ := hP
  exact TowerEx.exists_transition hF hP h D D'

section Level

variable {R : Type} [CommRing R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

theorem isGrpPullback_thickMap (e : ℕ) :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem isNilpotent_of_le_map (n : ℕ) (J : Ideal (R ⧸ I ^ n)) (hJ : J ≤ I.map (Ideal.Quotient.mk (I ^ n))) :
    IsNilpotent J := by
  refine ⟨n, le_bot_iff.1 ((Ideal.pow_right_mono hJ n).trans ?_)⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

variable {I}

theorem pow_succ_ne_top (hI : I ≠ ⊤) (e : ℕ) : I ^ (e + 1) ≠ ⊤ := fun h =>
  hI (top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))

theorem isLocalRing_quot [IsLocalRing R] (hI : I ≠ ⊤) (e : ℕ) : IsLocalRing (R ⧸ I ^ (e + 1)) :=
  have := Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top hI e)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

theorem connectedSpace_sp (A : Type) [CommRing A] [IsLocalRing A] : ConnectedSpace (Sp A) :=
  SplitTorus.connectedSpace_of_isLocalRing A

theorem exists_tq_succ [IsLocalRing R] [IsCommMonObj G] (hI : I ≠ ⊤) (hG : IsSemiAbelian G) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (e : ℕ) (Q₀ : TQ (thickObj R I e G) X) :
    ∃ Q : TQ (thickObj R I (e + 1) G) X, TorusCompat (thickTrans R I e) (thickMap R I e G) Q₀.i Q.i := by
  have := isLocalRing_quot hI (e + 1)
  have := hG.smooth
  have : Smooth (thickObj R I (e + 1) G).hom := by
    change Smooth (pullback.snd G.hom _)
    infer_instance
  refine exists_tq_lift _ (Ideal.Quotient.factor_surjective _) (isNilpotent_of_le_map I _ _ fun x hx => ?_) _ _ _
    (isGrpPullback_thickMap I G e) Q₀
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.mem_map_of_mem _ (Ideal.pow_le_self (Nat.succ_ne_zero e) (Ideal.Quotient.eq_zero_iff_mem.1 hx))

theorem nonempty_biTriv (h₁ : Laws) (h₂ : Laws2) [IsLocalRing R] [IsNoetherianRing R] [IsCommMonObj G] [I.IsPrime]
    [IsIntegrallyClosed (R ⧸ I)] (hG : IsSemiAbelian G) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (e : ℕ) (Q : TQ (thickObj R I e G) X) (P : CP (thickObj R I e G)) :
    Nonempty (BiTriv P.c Q.i) := by
  let J := I.map (Ideal.Quotient.mk (I ^ (e + 1)))
  let ε : ((R ⧸ I ^ (e + 1)) ⧸ J) ≃+* R ⧸ I :=
    DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self (Nat.succ_ne_zero e))
  have : IsDomain ((R ⧸ I ^ (e + 1)) ⧸ J) := ε.toMulEquiv.isDomain _
  have : IsIntegrallyClosed ((R ⧸ I ^ (e + 1)) ⧸ J) := IsIntegrallyClosed.of_equiv ε.symm
  have := hG.smooth
  have := hG.geomConnected
  have : Smooth (thickObj R I e G).hom := by
    change Smooth (pullback.snd G.hom _)
    infer_instance
  have : GeometricallyConnected (thickObj R I e G).hom := by
    change GeometricallyConnected (pullback.snd G.hom _)
    infer_instance
  have : Smooth ((Over.pullback (red J)).obj (thickObj R I e G)).hom := by
    change Smooth (pullback.snd (thickObj R I e G).hom _)
    infer_instance
  have : GeometricallyConnected ((Over.pullback (red J)).obj (thickObj R I e G)).hom := by
    change GeometricallyConnected (pullback.snd (thickObj R I e G).hom _)
    infer_instance
  have : ConnectedSpace (Sp ((R ⧸ I ^ (e + 1)) ⧸ J)) := inferInstance
  have := (GroupConn.connectedSpace_group _ ((Over.pullback (red J)).obj (thickObj R I e G))).1
  have hp := isGrpPullback_pullback (thickObj R I e G) (red J)
  obtain ⟨Q₀, c⟩ := exists_tq_baseChange _ _ _ X _ _ _ hp Q
  obtain ⟨P₀, w, hw⟩ := exists_pull P (TowerEx.toBase_mul hp hp.1.w)
  exact biTriv_lift_of_isNilpotent _ J (isNilpotent_of_le_map I _ _ le_rfl) X _ _ _ _ hp P P₀ w hw _ _ Q.i_hom Q₀.i_hom c
    (BiextTriv.nonempty_biTriv_normal h₁ h₂ _ X _ _ _ _ Q₀.i_hom)

theorem exists_even (h₁ : Laws) (h₂ : Laws2) [IsDomain R] [IsCommMonObj G]
    (P : CP G) (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) (hW : HypW G P.L.L)
    {X : Type} [AddCommGroup X] (e : ℕ) (Q : TQ (thickObj R I e G) X) (P' : CP (thickObj R I e G))
    (h : IsLevelCP I e P' P) (b : Nonempty (BiTriv P'.c Q.i)) : ∃ σ : CubTriv P'.c Q.i, σ.Even := by
  obtain ⟨w, -, hw, -, -, hL, -⟩ := hW
  obtain ⟨v, hv⟩ := h
  exact EvenTriv.exists_even_cubTriv h₁ h₂ R G hG hp P w hw hL _ _ X Q P' _ _
    (isGrpPullback_pullback G (thick R I e)).1 v hv b

theorem connectedSpace_thickObj [IsLocalRing R] (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (e : ℕ) :
    ConnectedSpace (thickObj R I e G).left := by
  have := isLocalRing_quot hI e
  have := connectedSpace_sp (R ⧸ I ^ (e + 1))
  have := hG.smooth
  have := hG.geomConnected
  have : Smooth (thickObj R I e G).hom := by
    change Smooth (pullback.snd G.hom _)
    infer_instance
  have : GeometricallyConnected (thickObj R I e G).hom := by
    change GeometricallyConnected (pullback.snd G.hom _)
    infer_instance
  exact (GroupConn.connectedSpace_group _ (thickObj R I e G)).1


omit [GrpObj G] in
theorem thickMap_fst (e : ℕ) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem isCPPullback_thick [IsDomain R] [IsCommMonObj G] {P : CP G} {e : ℕ} {P' : CP (thickObj R I e G)}
    (h : IsLevelCP I e P' P) : IsCPPullback P' P (thick R I e) (pullback.fst G.hom (thick R I e)) :=
  ⟨isGrpPullback_pullback G _, h⟩

theorem isCPPullback_thickMap [IsDomain R] [IsCommMonObj G] {P : CP G} {e : ℕ} {P' : CP (thickObj R I e G)}
    {P'' : CP (thickObj R I (e + 1) G)} (h' : IsLevelCP I e P' P) (h'' : IsLevelCP I (e + 1) P'' P) :
    IsCPPullback P' P'' (thickTrans R I e) (thickMap R I e G) :=
  isCPPullback_of_comp (isCPPullback_thick G h'') (isCPPullback_thick G h') (isGrpPullback_thickMap I G e)
    (thickTrans_comp R I e) (thickMap_fst G e)

theorem exists_isCPPullback [IsDomain R] [IsLocalRing R] [IsCommMonObj G] (hI : I ≠ ⊤) (hG : IsSemiAbelian G) {P : CP G}
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] {e : ℕ} (l : Lev I P X e) (l' : Lev I P X (e + 1))
    (c : TorusCompat (thickTrans R I e) (thickMap R I e G) l.Q.i l'.Q.i) :
    ∃ β : l.Q.B.left ⟶ l'.Q.B.left, IsCPPullback l.D.M l'.D.M (thickTrans R I e) β ∧
      l.Q.q.left ≫ β = thickMap R I e G ≫ l'.Q.q.left :=
  have := isLocalRing_quot hI e
  have := connectedSpace_sp (R ⧸ I ^ (e + 1))
  have := connectedSpace_thickObj G hI hG e
  exists_isCPPullback_desc (isCPPullback_thickMap G l.lev l'.lev) c l'.D l.D

end Level

theorem nonempty_towerR : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → IsProper (pullback.snd G.hom (jK R)) → SplitOver G I → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), Nonempty (TowerR I P X) := by
  intro h₁ h₂ R _ _ _ I ⟨⟨hN, _⟩, _, _, hI, hC⟩ G _ _ P hG hW hp ⟨E, ⟨d⟩⟩
  have hI' := hI.ne_top
  have := E.free
  have := E.finite
  refine ⟨E.X, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨Q₁, -⟩ := exists_tq_of_gtDatum _ E _ d
  let r : Sp (R ⧸ I ^ (0 + 1)) ⟶ Sp (R ⧸ I) := spMap (Ideal.Quotient.factor (show I ≤ I ^ (0 + 1) by simp))
  have hr : r ≫ spMap (Ideal.Quotient.mk I) = thick R I 0 := by
    rw [← Spec.map_comp]
    rfl
  let F : (thickObj R I 0 G).left ⟶ ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj G).left :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by rw [Category.assoc, hr]; exact pullback.condition)
  obtain ⟨Q₀, -⟩ := exists_tq_baseChange _ _ r E.X _ _ F ((isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G (thick R I 0)).congr hr.symm (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)) Q₁
  choose nx hnx using fun e => exists_tq_succ (I := I) (X := E.X) G hI' hG e
  let Q : ∀ e, TQ (thickObj R I e G) E.X := fun e => Nat.rec Q₀ nx e
  have hQ : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (Q e).i (Q (e + 1)).i := fun e => hnx e (Q e)
  choose Pe hPe using fun e => exists_isLevelCP I e P
  have hD : ∀ e, Nonempty ((Q e).Desc (Pe e)) := fun e => by
    have := isLocalRing_quot hI' e
    have := connectedSpace_sp (R ⧸ I ^ (e + 1))
    have := connectedSpace_thickObj G hI' hG e
    have b := nonempty_biTriv G h₁ h₂ hG e (Q e) (Pe e)
    exact nonempty_desc _ E.X _ (Q e) (Pe e) b
      (exists_even G h₁ h₂ P hG hp hW e (Q e) (Pe e) (hPe e) b)
  let l : ∀ e, Lev I P E.X e := fun e => ⟨Q e, Pe e, hPe e, (hD e).some⟩
  choose β hβ hq using fun e => exists_isCPPullback G hI' hG (l e) (l (e + 1)) (hQ e)
  exact ⟨⟨l, hQ, β, hβ, hq⟩⟩

end GlobalTheory.FormalTower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickening
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleThickening

theorem surjective_spec_of_isNilpotent_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := by
  refine ⟨fun (x : PrimeSpectrum A) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap g) := by
    rw [range_comap_of_surjective _ _ hg]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker g ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem exists_sec_lbPow_of_pw {X : Scheme.{0}} {H : LB X} {n : ℕ} (σ : LB.Sec (pw H n)) :
    ∃ s : (lbPow H n).Sec, nonzeroLocus s = nonzeroLocus σ :=
  ⟨powSecMk n σ.f fun i j => (σ.compat i j).trans (congrArg (· * _) (by
      change (H.g i j ^ (n : ℤ)).val = _
      rw [zpow_natCast, Units.val_pow_eq_pow_val])),
    nonzeroLocus_powSecMk n _ _⟩

theorem relAmple_of_sq_zero : ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X : Over (Spec (CommRingCat.of A))) (X' : Over (Spec (CommRingCat.of A'))) (β : X'.left ⟶ X.left), IsPullback β X'.hom X.hom (Spec.map (CommRingCat.ofHom g)) → LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull β) → RelAmple X' L' → RelAmple X L := by
  intro A A' _ _ g hg h2 X X' β hβ _ L L' hL hL' hw hA
  have hn : IsNilpotent (RingHom.ker g) := ⟨2, h2⟩
  obtain ⟨d, -, m, s', hs'⟩ := (Unif.relAmple_iff_veryAmpleBy A' X' L' hL').1 hA
  have hP' : IsProper X'.hom := isProper_of_veryAmpleBy hs'
  have hs : Surjective (Spec.map (CommRingCat.ofHom g)) := surjective_spec_of_isNilpotent_ker g hg hn
  have hc : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) := .spec_of_surjective _ hg
  have : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) hβ.flip hs
  have : IsClosedImmersion β := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hβ.flip hc
  have hp : IsProper (β ≫ X.hom) := by rw [hβ.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective β X.hom
  have : IsSeparated X.hom := NilProper.isSeparated_of_comp_surjective β X.hom
  have : IsProper X.hom := {}
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have h : IsAmpleLB (L.pull β) :=
    (isAmpleLB_of_relAmple_of_isAffine X' hL' hA).of_lbIso (LB.isLB_pull hL β) hw.symm
  refine (relAmple_iff_isAmpleLB_of_isAffine X hL).2 ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := β.surjective x
  obtain ⟨n, hn₁, s, hz, ha⟩ := h.exists_affine z
  have hH := isLB_lbPow hL n
  obtain ⟨s₀, hs₀⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hH β) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL β n).symm s
  obtain ⟨D, hD, e⟩ := AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent A A' g hg hn _ _ X.hom X'.hom
    β hβ _ ha
  obtain ⟨t, ht⟩ := secOn_pull_surjective_of_surjective A A' g hg _ _ X.hom X'.hom β hβ _ hH D hD
    (GlobalTheory.LB.ofSec s₀ (β ⁻¹ᵁ D))
  obtain ⟨k, hk, σ, hσ⟩ := _root_.GlobalTheory.SecPow.exists_pow_section _ _ β
    (SquareZero.mul_eq_zero_of_app_eq_zero A A' g hg h2 _ _ X.hom X'.hom β hβ) _ hH s₀ D (e.trans hs₀.symm) t ht
  obtain ⟨u, hu⟩ := exists_sec_lbPow_of_pw σ
  have e' : nonzeroLocus (secOfPowPow u) = D := (nonzeroLocus_secOfPowPow u).trans (hu.trans hσ)
  exact ⟨n * k, Nat.mul_pos hn₁ hk, secOfPowPow u, e'.ge (e.ge hz), e' ▸ hD⟩

end GlobalTheory.AmpleThickening
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecOfIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.GeoHalf

theorem sec_of_iso {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀)
    (he : ∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a)
    (hs : ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.toScheme), z ∈ W ∧
      h ≫ Q.G.ι ≫ Q.P.hom = W.ι ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme)
        (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι →
        x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀) :
    Z.Sec := by
  obtain ⟨e, he1, he2, he3⟩ := he
  intro z a ha
  obtain ⟨W, h, hz, hh, hx⟩ := hs z a ha
  refine ⟨W, h ≫ e.inv, hz, ?_, ?_⟩
  · rw [← he1, Category.assoc, e.inv_hom_id_assoc]; exact hh
  · obtain ⟨u₀, hu, G, semi, dim, qproj, φ, cart, L, cub, sym, w, w_gen, w_rig, split⟩ := Z
    dsimp only at e he1 he2 he3 ⊢
    subst he2
    have he4 : φ ≫ e.hom = ex.a := eq_of_heq he3
    intro x x' h1 h2 h3
    have ha0 : φ ≫ e.hom ≫ Q.G.ι = Q.a₀ := by rw [← Category.assoc, he4, ex.a_eq]
    have h4 : x' ≫ pullback.snd _ _ ≫ U₀.ι = M.pt := by
      rw [← Q.cart.w, ← ha0, ← h2, ← he1]; simp only [Category.assoc]
    have h5 : (x' ≫ pullback.snd _ _) ≫ Q.u₀ = spMap S.R.val.toRingHom :=
      Q.u₀_pt _ (by rw [Category.assoc]; exact h4)
    have h6 := hx Ω x x' (h1.trans h4.symm) (by
      rw [h3, ← h5]; simp only [Category.assoc])
    rw [← cancel_mono (e.hom ≫ Q.G.ι)]
    simp only [Category.assoc, e.inv_hom_id_assoc]
    rw [h6, ha0]

theorem zhGeo_of
    (hhastests : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.HasTests ∧ ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧ ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)))
    (hprex : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law)
    (hab : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → Nonempty ex.core.Law → ex.core.HasTests → ex.core.HasCharts → IsOpen {z : M.Z | S.TT M z = ⊥} → (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) → Z.Ab)
    (hseco : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → BaseFacts S M U₀ EE → Z.Ab → (∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0) → Z.SecO EE)
    (hunifr : Laws → Laws2 → Laws3 → Laws4 → Laws5 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W))
    (htop : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Big → ρ.HasU → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE ∧ ρ.HasGeo ∧ ∃ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), ex.core.HasTests ∧ ex.core.Indep ∧ ex.core.Fib ∧ ex.core.HasCharts)
    (htheta : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)))
    (htorssec : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.TorsSec (S.r * S.N))
    (hhsec : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.toScheme), z ∈ W ∧ h ≫ Q.G.ι ≫ Q.P.hom = W.ι ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι → x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀)
    (hindepfib : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0)
    (hzab : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → IsOpen {z : M.Z | S.TT M z = ⊥} ∧ (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)))
    (hout : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀) (C : Clos ρ M U₀ EE) (ex : C.Ext), (∃ e : Q.G.left ≅ C.G.toScheme, e.hom ≫ C.G.ι ≫ C.P.hom = Q.G.hom ∧ Q.u₀ = C.u₀ ∧ HEq (Q.φ ≫ e.hom) ex.a) → S.Big → S.Over₀ M U₀ → S.IsEE M U₀ EE → Q.Sec → Q.LocTheta → Q.SecO EE → Q.Ab → Nonempty (ZHOut ρ M U₀ EE)) :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → Laws3 → Laws4 → Laws5 → UTorsSt → ZHGeoSt := by
  intro hx hN hU l1 l2 l3 l4 l5 hT o Ω _ _ _ _ S ρ hB M U₀ EE hov hee _
  have ll : GlobalTheory.UT.LL := ⟨l1, l2, l3, l4, l5⟩
  have hasU : ρ.HasU := fun p _ y₀ hy Fs => (hhastests hN hU l1 l2 hT o Ω S ρ).2 p y₀ Fs hy
  obtain ⟨bf, hg, Q, ex, ht, hi, hf, hc⟩ := htop ll hT o Ω S ρ M U₀ EE hB hasU hov hee
  obtain ⟨Z, he, hth, hlaw⟩ := hprex l1 l2 hU o Ω S ρ M U₀ EE Q ex hB ht hi hc
    (htorssec ll o Ω S ρ M U₀ EE bf Q ex hB hg hf) (htheta ll o Ω S ρ M U₀ EE bf Q ex hB hg)
  obtain ⟨z1, z2, z3⟩ := hzab ll o Ω S ρ M U₀ EE bf Q ex hB hg hf
  have hab : Z.Ab := hab o Ω S ρ M U₀ EE Q ex Z he hlaw ht hc z1 z2 z3
  have hso : Z.SecO EE := hseco o Ω S ρ M U₀ EE Q ex Z he bf hab
    (hindepfib ll o Ω S ρ M U₀ EE bf Q hB hg)
  exact hout hx (hunifr l1 l2 l3 l4 l5) hN hU l1 l2 hT o Ω S ρ M U₀ EE Z Q ex he hB hov hee
    (sec_of_iso Q ex Z he (hhsec ll o Ω S ρ M U₀ EE bf Q)) hth hso hab
end GlobalTheory.ZH.GeoHalf
end

