module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSpreadPointsEqSpreadRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumPair

theorem weilIs_of_spread : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] [IsNoetherianRing T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (k : ℕ) (x x' : baseOver (Sp Ω) ⟶ A.A) (y y' : baseOver (Sp T) ⟶ P.A) (c : Tˣ), 1 ≤ k → x.left ≫ φ = spMap jT ≫ y.left → x'.left ≫ φ = spMap jT ≫ y'.left → y ^ k = 1 → y' ^ k = 1 → WeilIs A.A A.L k x x' (unitOn (Units.map jT.toMonoidHom c)) → WeilIs P.A P.L k y y' (unitOn c) := by
  intro Ω T _ _ _ _ jT hj A P φ hp hw k x x' y y' c hk hx hx' hy hy' hW
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  haveI : IsCommMonObj A.A := A.isAb.comm
  haveI : IsLocallyNoetherian (Sp T) := inferInstance
  haveI : IsLocallyNoetherian (Sp Ω) := inferInstance
  obtain ⟨c₀, hc₀, -⟩ := (hL.weil (Sp T) P k (baseOver _)).1 y y' hy hy'
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap jT) ⟶ baseOver (Sp T) := Over.homMk (spMap jT) (by simp)
  have H1 := GlobalTheory.CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h hc₀
  have H2 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp T) (Sp Ω) P.A A.A (spMap jT) φ P.L A.L P.isLB A.isLB hp hw
    (baseOver (Sp Ω)) k x x' (h ≫ y) (h ≫ y') _ hx.symm hx'.symm).2 H1
  have inj : ∀ a b : baseOver (Sp Ω) ⟶ A.A, a.left ≫ φ = b.left ≫ φ → a = b := by
    intro a b e
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext e
    rw [Over.w, Over.w]
  have tors : ∀ (a : baseOver (Sp Ω) ⟶ A.A) (b : baseOver (Sp T) ⟶ P.A), a.left ≫ φ = spMap jT ≫ b.left →
      b ^ k = 1 → a ^ k = 1 := by
    intro a b e hb
    apply inj
    have e1 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) (a ^ k)) = (h ≫ b) ^ k := by
      rw [map_pow]
      congr 1
      exact Over.OverMorphism.ext e
    have e2 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) 1) = (h ≫ b) ^ k := by
      rw [map_one, ← MonObj.comp_pow, hb, MonObj.comp_one]
    exact (congrArg (fun z => z.left) e1).trans (congrArg (fun z => z.left) e2).symm
  have hxk := tors x y hx hy
  have hxk' := tors x' y' hx' hy'
  have U := (hL.weil (Sp Ω) A k (baseOver _)).1 x x' hxk hxk'
  have e3 := U.unique H2 hW
  have nat : ∀ a : T, (spMap jT).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (jT a) := by
    intro a
    have := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom jT))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  have ginj : Function.Injective (spMap jT).appTop.hom := by
    intro a b e
    have ea : a = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom a) := by
      simp
    have eb : b = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom b) := by
      simp
    rw [ea, eb, nat, nat] at e
    have e' := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom e
    have key : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom z) = z :=
      fun z => by simp
    rw [key, key] at e'
    rw [ea, eb, hj e']
  have e4 : c₀ = unitOn c := by
    apply Units.ext
    apply ginj
    exact (congrArg Units.val e3).trans (nat (c : T)).symm
  rw [← e4]
  exact hc₀

end GlobalTheory.MumPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.ExpKernel

theorem fderiv_apply_eq_zero {g : ℕ} (h : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) (hc : ∀ t : ℂ, h (t • w) = h 0) :
    fderiv ℂ h 0 w = 0 := by
  by_cases hd : DifferentiableAt ℂ h 0
  · have hl : HasFDerivAt (fun t : ℂ => t • w) ((ContinuousLinearMap.id ℂ ℂ).smulRight w) 0 :=
      ((ContinuousLinearMap.id ℂ ℂ).smulRight w).hasFDerivAt
    have h0 : HasFDerivAt h (fderiv ℂ h 0) ((0 : ℂ) • w) := by rw [zero_smul]; exact hd.hasFDerivAt
    have h1 := h0.comp (0 : ℂ) hl
    have h2 : HasFDerivAt (fun t : ℂ => h (t • w)) (0 : ℂ →L[ℂ] ℂ) 0 := by
      simp only [hc]; exact hasFDerivAt_const _ _
    have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (h1.unique h2)
    simpa using this
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

theorem kernel_isFullLattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
    SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e →
    ∃ Λ : Submodule ℤ (Fin g → ℂ), DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧
      ∀ z, e z = 1 ↔ z ∈ Λ := by
  intro X G _ _ g hG hg y e he
  obtain ⟨hadd, hsurj, hhol, hd1, hd2⟩ := he
  let A : Over (Sp ℂ) := (Over.pullback y).obj G
  letI : GrpObj A := Functor.grpObjObj
  let φ : A.left ⟶ G.left := pullback.fst G.hom y
  have hp : IsGrpPullback A G y φ := isGrpPullback_pullback G y
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hp
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 hg
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hgA
  obtain ⟨ht₁, ht₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hgA
  have inj : ∀ x x' : 𝟙_ (Over (Sp ℂ)) ⟶ A, x.left ≫ φ = x'.left ≫ φ → x = x' := fun x x' h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w x']))
  have lift : ∀ x₀ : Over.mk y ⟶ G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x x', Φ (x * x') = Φ x * Φ x' := fun x x' => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ x') (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ x')) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ x').symm)
  have Φinj : Function.Injective Φ := fun x x' h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (Φ (e z)).left) :=
    FibreUnif.isHolTo_of_isPullback hp.1 (e := fun z => (Φ (e z)).left) (fun z => Over.w (Φ (e z)))
      (by simpa only [hΦ] using hhol)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L g g u ht₁ ht₂ (fun z => Φ (e z))
    (fun z z' => by rw [hadd, Φmul]) hol
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun w hw => by
    have hconst : ∀ t : ℂ, e (t • w) = e 0 := fun t => Φinj (by
      rw [← hF, ← hF, map_smul, hw, smul_zero, map_zero])
    have hiff : ∀ v, IsDerivAt0 (fun z => (e z).left) w v ↔ IsDerivAt0 (fun z => (e z).left) 0 v := by
      intro v
      unfold IsDerivAt0
      refine and_congr_right fun _ => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_
      rw [map_zero, fderiv_apply_eq_zero _ w (fun t => by simp only [hconst t, zero_smul])]
    obtain ⟨v, hv, -⟩ := hd1 w
    exact (hd2 v hv.1).unique hv ((hiff _).1 hv)
  let F' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo F Finj
  have hF' : ∀ z, F' z = F z := fun _ => rfl
  have hker : ∀ z, e z = 1 ↔ F z ∈ u.Λ := fun z => by
    rw [← u.ker, hF, ← Φone, Φinj.eq_iff]
  let Λ : Submodule ℤ (Fin g → ℂ) := u.Λ.comap F.toAddMonoidHom.toIntLinearMap
  have hmem : ∀ z, z ∈ Λ ↔ F z ∈ u.Λ := fun _ => Iff.rfl
  refine ⟨Λ, ?_, ?_, fun z => (hker z).trans (hmem z).symm⟩
  · have := u.discrete
    let c : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := F'.toContinuousLinearEquiv
    let f : Λ → u.Λ := fun x => ⟨F x, (hmem x).1 x.2⟩
    have hcomp : (Subtype.val ∘ f) = c ∘ (Subtype.val : Λ → Fin g → ℂ) := rfl
    have hemb : Topology.IsEmbedding f := by
      rw [← Topology.IsEmbedding.subtypeVal.of_comp_iff, hcomp]
      exact c.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    exact hemb.discreteTopology
  · let Fr : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := F'.restrictScalars ℝ
    have hset : (Λ : Set (Fin g → ℂ)) = Fr.symm '' (u.Λ : Set (Fin g → ℂ)) := by
      rw [LinearEquiv.image_symm_eq_preimage]
      ext z
      exact hmem z
    rw [hset, ← LinearEquiv.coe_coe, Submodule.span_image, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact Fr.symm.surjective

end GlobalTheory.ExpKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpacePullbackRestrictOpenContainingFibr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geomFibre_restrict_open_connected : ∀ (H Q Z : Scheme.{0}) (U : H.Opens) (f : H ⟶ Q) (ν : Z ⟶ Q), (∀ h : H, f h ∈ Set.range ν → h ∈ U) → ConnectedSpace (pullback f ν : Scheme.{0}) → ConnectedSpace (pullback (U.ι ≫ f) ν : Scheme.{0}) := by
  intro H Q Z U f ν hU hc
  have hs : IsIso (pullback.snd U.ι (pullback.fst f ν)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [Scheme.Hom.opensRange_pullbackSnd]
    refine top_unique fun z _ => ?_
    show pullback.fst f ν z ∈ U.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    refine hU _ ⟨pullback.snd f ν z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  let e := Scheme.homeoOfIso ((pullbackRightPullbackFstIso f ν U.ι).symm ≪≫
    asIso (pullback.snd U.ι (pullback.fst f ν)))
  exact e.connectedSpace_iff.2 hc

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContrCupFormEqZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem contr_cup_form_eq_zero (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (v : epsR R ⟶ B) (hv : IsTangent v) (α : Form (A.hom ≫ 𝟙 _))
    (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (κ : Fn1 A)
    (hκ : IsContr (cupZ _ (m₁.coef.pullbackOneCocycle α.1) (m₂.coef.pullbackOneCocycle b)).1 v κ)
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) : κ D D' φ x = 0 := by
  obtain ⟨s, i, s', i', a, b', τ, hs, hi, hs', hi', ha, hb, hτ⟩ :=
    (ContrMor.exists_contr R A B v hv).1 D D' φ x
  rw [hκ D D' φ x s i s' i' a b' τ hs hi hs' hi' ha hb hτ]
  have ha0 : (m₁.coef.pullbackOneCocycle α.1).1 _ _ a = 0 := α.2 (m₁.functor.map a) rfl rfl
  have hb0 : (m₁.coef.pullbackOneCocycle α.1).1 _ _ b' = 0 := α.2 (m₁.functor.map b') rfl rfl
  let e : m₁.functor.obj (trivAt (pt0 B x)) ⟶ m₁.functor.obj (trivAt (ptV v x)) :=
    { φ := { toRingHom := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D),
             commutes' := fun r ↦ (TrivSqZeroExt.inlAlgHom R D D).commutes r }
      φ₀ := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D)
      comm := fun _ ↦ rfl
      dp := isDPMorphism_of_eq_bot _ rfl _ _
      pt := by
        have h1 : pt0 B x ≫ fst A B = x := lift_fst _ _
        have h2 : ptV v x ≫ fst A B =
            (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x : Pt A (DualNumber D)) := lift_fst _ _
        change spMap (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) ≫
          (pt0 B x).left ≫ (fst A B).left = (ptV v x).left ≫ (fst A B).left
        rw [← Over.comp_left, h1, ← Over.comp_left, h2, Over.comp_left]
        rfl }
  have he0 : α.1.1 _ _ e = 0 := α.2 e rfl rfl
  have hes : e ≫ m₁.functor.map i = m₁.functor.map s := Thick.Hom.ext' (AlgHom.ext fun c ↦ by
    change i.φ (TrivSqZeroExt.inl c) = s.φ c
    rw [hi]
    exact (hs c).symm)
  have hsi : (m₁.coef.pullbackOneCocycle α.1).1 _ _ s = (m₁.coef.pullbackOneCocycle α.1).1 _ _ i := by
    change α.1.1 _ _ (m₁.functor.map s) = α.1.1 _ _ (m₁.functor.map i)
    rw [← hes]
    have h := GlobalTheory.Cris.ev_comp α.1 e (m₁.functor.map i)
    simp only [GlobalTheory.Cris.ev] at h
    rw [h, he0, map_zero, zero_add]
  simp only [cupZ_apply]
  rw [ha0, hb0, hsi]
  simp

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentIndepOfIsComplAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.TChart

theorem cotangent_indep_of_isComplAt : ∀ (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (I : Type) [Fintype I] (R : Type) [CommRing R] [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) → ∀ (m : ℕ) (ι₀ : Fin m ↪ I), (∀ k, ψ (MvPolynomial.X (ι₀ k)) ∈ maximalIdeal R) → ∀ c : Fin m → R, ∑ k, c k * ψ (MvPolynomial.X (ι₀ k)) ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal W).map (ψ.comp MvPolynomial.C) → ∀ k, c k ∈ maximalIdeal R := by
  intro W _ _ _ I _ R _ _ ψ hψ hloc m ι₀ hX c hc k
  classical
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  haveI hflat : Module.Flat (MvPolynomial I W) R := hψ.2.2.1
  haveI := hloc
  have hsmul : ∀ (a : MvPolynomial I W) (r : R), a • r = ψ a * r := fun a r => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  let P : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ
  have hPm : P.map ψ = maximalIdeal R := hψ.2.2.2.1
  let δ : MvPolynomial I W → ResidueField R := fun f => residue R (ψ (MvPolynomial.pderiv (ι₀ k) f))
  have hπP : ∀ p ∈ P, residue R (ψ p) = 0 := fun p hp => (residue_eq_zero_iff _).2 hp
  have hδmul : ∀ a b, δ (a * b) = residue R (ψ a) * δ b + residue R (ψ b) * δ a := by
    intro a b; simp only [δ, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul]
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := by intro a b; simp [δ]
  let K : Ideal (MvPolynomial I W) :=
    { carrier := {x | x ∈ P ∧ δ x = 0}
      add_mem' := fun {a b} ha hb => ⟨P.add_mem ha.1 hb.1, by rw [hδadd, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨P.zero_mem, by simp [δ]⟩
      smul_mem' := fun a x hx => ⟨P.mul_mem_left a hx.1, by
        rw [smul_eq_mul, hδmul, hx.2, hπP x hx.1, mul_zero, zero_mul, add_zero]⟩ }
  have hCW : (maximalIdeal W).map (MvPolynomial.C : W →+* MvPolynomial I W) ≤ K := by
    refine Ideal.map_le_iff_le_comap.2 fun w hw => ⟨?_, by simp [δ]⟩
    show ψ (MvPolynomial.C w) ∈ maximalIdeal R
    exact map_nonunit (ψ.comp MvPolynomial.C) w hw
  have hP2 : P ^ 2 ≤ K := by
    rw [pow_two]
    refine Ideal.mul_le.2 fun p hp q hq => ⟨P.mul_mem_left p hq, ?_⟩
    show δ (p * q) = 0
    rw [hδmul, hπP p hp, hπP q hq]; simp
  have hJ : maximalIdeal R ^ 2 ⊔ (maximalIdeal W).map (ψ.comp MvPolynomial.C) ≤ K.map ψ := by
    rw [← hPm, ← Ideal.map_pow, ← Ideal.map_map, ← Ideal.map_sup]
    exact Ideal.map_mono (sup_le hP2 hCW)
  let muT : TensorProduct (MvPolynomial I W) R P →ₗ[MvPolynomial I W] R :=
    (TensorProduct.rid (MvPolynomial I W) R).toLinearMap ∘ₗ (Submodule.subtype P).lTensor R
  have hmu : Function.Injective muT :=
    (TensorProduct.rid (MvPolynomial I W) R).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hmut : ∀ (r : R) (p : P), muT (r ⊗ₜ p) = ψ p * r := fun r p => by
    simp [muT, hsmul]
  let f : R →+ P →+ ResidueField R := AddMonoidHom.mk'
    (fun r => AddMonoidHom.mk' (fun p : P => residue R r * δ p) (by intro a b; simp [hδadd, mul_add]))
    (by intro a b; ext p; simp [add_mul])
  have hf : ∀ (a : MvPolynomial I W) (r : R) (p : P), f (a • r) p = f r (a • p) := by
    intro a r p
    simp only [f, AddMonoidHom.mk'_apply, hsmul, Submodule.coe_smul, smul_eq_mul, hδmul, hπP p p.2, map_mul]
    ring
  let L : TensorProduct (MvPolynomial I W) R P →+ ResidueField R := TensorProduct.liftAddHom f hf
  have hLt : ∀ (r : R) (p : P), L (r ⊗ₜ p) = residue R r * δ p := fun r p => by
    simp [L, f]
  have hspan : ∀ y ∈ K.map ψ, ∀ r : R, ∃ t, muT t = r * y ∧ L t = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro r
      exact ⟨r ⊗ₜ ⟨j, hj.1⟩, by rw [hmut]; ring, by rw [hLt]; simp [hj.2]⟩
    | zero => intro r; exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      intro r
      obtain ⟨t₁, h₁, h₁'⟩ := hx r
      obtain ⟨t₂, h₂, h₂'⟩ := hy r
      exact ⟨t₁ + t₂, by rw [map_add (f := _), h₁, h₂]; ring, by rw [map_add (f := _), h₁', h₂', add_zero]⟩
    | smul a x _ hx =>
      intro r
      obtain ⟨t, h₁, h₂⟩ := hx (r * a)
      exact ⟨t, by rw [h₁, smul_eq_mul]; ring, h₂⟩
  have hX' : ∀ j, MvPolynomial.X (ι₀ j) ∈ P := hX
  let t₀ : TensorProduct (MvPolynomial I W) R P := ∑ j, c j ⊗ₜ ⟨MvPolynomial.X (ι₀ j), hX' j⟩
  have hmu0 : muT t₀ = ∑ j, c j * ψ (MvPolynomial.X (ι₀ j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [t₀, map_sum, hmut]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hL₀ : L t₀ = residue R (c k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [t₀, map_sum, hLt, δ, MvPolynomial.pderiv_X, Pi.single_apply, ι₀.injective.eq_iff]
    simp
  obtain ⟨t, ht₁, ht₂⟩ := hspan _ (hJ hc) 1
  have : t = t₀ := hmu (by rw [ht₁, _root_.one_mul, hmu0])
  rw [this, hL₀] at ht₂
  exact (residue_eq_zero_iff _).1 ht₂

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverDominatingPair
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

namespace GlobalTheory.Mean4O.CoverDom

theorem exists_cover_dominating_cover (F : Type) [Field F] [NumberField F] (Y : Var F) (W V : Mean4O.Cover Y)
    (k : W.G ⟶ V.G) (hk : k ≫ V.π = W.π) :
    ∃ (W' : Mean4O.Cover Y) (a : W'.X ⟶ W.X) (b : W'.X ⟶ V.X), a ≫ W.p = W'.p ∧ b ≫ V.p = W'.p ∧
      Lies W' W a ∧ Lies W' V b := by
  have H₀ := W.pb
  have := V.ar.isIntegral
  have := W.ar.isLocallyNoetherian
  have : IsProper W.p := CommonModel.isProper_of_isProjOver W.ar.isProjOver
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  let r := pullback.fst W.p V.p
  have hc : W.j ≫ W.p = (k ≫ V.j) ≫ V.p := by
    rw [W.pb.w, Category.assoc, Category.assoc, V.pb.w, ← hk]; simp only [Category.assoc]
  let h : W.G ⟶ pullback W.p V.p := pullback.lift W.j (k ≫ V.j) hc
  have hr : h ≫ r = W.j := pullback.lift_fst _ _ _
  have hr' : h ≫ pullback.snd W.p V.p = k ≫ V.j := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ W.p) := GlobalTheory.ProjSpace.isProjOver_pullback W.ar.isProjOver V.ar.isProjOver
  have w : h ≫ r ≫ W.p = (W.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ W.p) (spMap (algebraMap (𝓞 F) F))
  let f' : W.G ⟶ pullback (r ≫ W.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift h (W.π ≫ Y.str) w
  let ρ : pullback (r ≫ W.p) (spMap (algebraMap (𝓞 F) F)) ⟶ W.G :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ ≫ W.π ≫ Y.str = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 W.G := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ W.π ≫ Y.str) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ (W.π ≫ Y.str)
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : h = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ W.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom h := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h (r ≫ W.p) F (W.π ≫ Y.str) w
  have : GlobalTheory.IsNormalScheme W.G := isNormalScheme_G W
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat W.j := MorphismProperty.of_isPullback W.pb.flip ‹_›
  have : IsPreimmersion W.j := MorphismProperty.of_isPullback W.pb.flip ‹_›
  have e₁ : h.toNormalization ≫ h.fromNormalization ≫ r = W.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : h.toNormalization ≫ h.fromNormalization ≫ pullback.snd W.p V.p = k ≫ V.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hU := ModelDom.exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ r) W.j e₁
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    obtain ⟨U, hne, _⟩ := hU
    obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (h.fromNormalization ≫ r) U hne.to_subtype
    have := surjective_of_isDominant_of_isClosed_range (h.fromNormalization ≫ r)
      (h.fromNormalization ≫ r).isClosedMap.isClosed_range
    rw [← W.ar.dim_eq]
    exact (ModelDom.dim_le_of_birational (h.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (h.fromNormalization ≫ r).isClosedMap
        (h.fromNormalization ≫ r).surjective)
  have hfl : Flat (h.fromNormalization ≫ r ≫ W.p) := GlobalTheory.flat_fromNormalization_comp h F (r ≫ W.p) (W.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  let W' : Mean4O.Cover Y :=
    { X := h.normalization
      p := h.fromNormalization ≫ r ≫ W.p
      ar := ⟨W.ar.isDomain, W.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := W.G
      j := h.toNormalization
      π := W.π
      pb := hpb'
      φ := W.φ
      φ_spec := W.φ_spec }
  refine ⟨W', h.fromNormalization ≫ r, h.fromNormalization ≫ pullback.snd W.p V.p, Category.assoc _ _ _, ?_,
    ⟨𝟙 W.G, by rw [Category.id_comp]; exact e₁.symm, Category.id_comp _⟩, ⟨k, e₂.symm, hk⟩⟩
  change (h.fromNormalization ≫ pullback.snd W.p V.p) ≫ V.p = h.fromNormalization ≫ r ≫ W.p
  rw [Category.assoc, ← pullback.condition]

end GlobalTheory.Mean4O.CoverDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrComapFiniteIndexEssFiniteTypeComplexStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_comap_finiteIndex_essFiniteType_complex : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V), ((φ.comp c).codRestrict V hc).EssFiniteType → IsDiscreteValuationRing (V.comap φ) ∧ (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  first | exact @GlobalTheory.restrict_dvr_essFiniteType | exact GlobalTheory.restrict_dvr_essFiniteType | (intros; apply GlobalTheory.restrict_dvr_essFiniteType <;> assumption)
end

