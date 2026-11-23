module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0103
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionsIndependentOnClosedFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.IndepFib

theorem eq_zero_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((CrdCalc.isUnit_valR_iff _ U hU f).2 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem lin_eq_zero {k : Type} [Field k] [IsAlgClosed k] (Φ : FibPre k) [Smooth Φ.G.hom] {N : ℕ}
    {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X} {F : J → (Φ.H 1).Sec}
    (hG : Φ.Good N q cls F) (a : J → k) (h : ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, ∑ i, a i * v i = 0) : a = 0 := by
  have : IsReduced Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Φ.G.hom
  refine GlobalTheory.ZH.WtLin.linIndep k Φ N q J cls F hG a fun l => ?_
  refine eq_zero_of_points Φ.G.hom _ _ fun x hx hU => ?_
  have h1 := h _ ⟨x, hx, l, 1, hU, fun _ => rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CrdCalc.valR_eq x _ hU, map_sum, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, Units.val_one, _root_.one_mul]
  exact congrArg (· * _) (GlobalTheory.Points.valR_constFn_of_section Φ.G.hom x hx _ hU (a i))

theorem change_mul_change {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type} [Fintype J]
    {A : Subalgebra o Ω} {B B' C : Matrix J J Ω} (hC : C * B' = 1) {g g' : Matrix J J A}
    (h : B' = g.map (↑) * B) (h' : B = g'.map (↑) * B') : g * g' = 1 := by
  have h1 : B' * C = 1 := mul_eq_one_comm.1 hC
  have h2 : (g.map (↑) * g'.map (↑) : Matrix J J Ω) = 1 := by
    calc (g.map (↑) * g'.map (↑) : Matrix J J Ω) = (g.map (↑) * (g'.map (↑) * B')) * C := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = 1 := by rw [← h', ← h, h1]
  ext i j
  have := congrFun (congrFun h2 i) j
  by_cases hij : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, hij] using this

theorem indep_on_closed_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0 := by
  intro L o Ω _ _ _ _ S ρ M U₀ EE hB Q hBig hGeo l z hz hcl
  obtain ⟨hT, hC⟩ := _root_.GlobalTheory.ZH.exists_geoTest_tMap_and_centre L o Ω S ρ M U₀ EE hB Q hBig hGeo
  obtain ⟨p, hp, y, hy, hyU⟩ := hC z hcl
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := hT p y hyU
  have hG := _root_.GlobalTheory.ZH.TestInOpen.top_le_preimage_G L o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hBig
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hx : (rPt p ≫ y) (IsLocalRing.closedPoint (kb p)) = z := by
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans hy)
  have hr : Set.range (rPt p ≫ y) = {z} := hx ▸ RatModel.range_eq_singleton _ _
  refine ⟨kb p, inferInstance, rPt p ≫ y, hr, fun a ha => ?_⟩
  have hz' : z ∈ Q.W tm.l := hy ▸ tm.mem
  obtain ⟨g, hg, -⟩ := InFibChart.exists_change Q tm.l l hz' hz
  obtain ⟨g', hg', hc'⟩ := InFibChart.exists_change Q l tm.l hz hz'
  have hgg := change_mul_change (Q.c_inv l) hg hg'
  let χ := RatModel.valHom (rPt p ≫ y) z hr
  have hGG : g.map χ * g'.map χ = 1 := by
    rw [← Matrix.map_mul, hgg, Matrix.map_one _ χ.map_zero χ.map_one]
  let ψ : t.u.V →+* kb p := (IsLocalRing.residue (OO p)).comp t.u.j
  have hψ : spMap ψ = rPt p ≫ spMap t.u.j := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  have hs : Smooth t.u.G.hom := t.mod.smooth.smooth
  have : Smooth t.mod.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  have h0 := lin_eq_zero t.mod.Φ t.mod.good (Matrix.vecMul (Matrix.vecMul a (g.map χ)) (tm.m.map ψ)) ?_
  · have hdet : (tm.m.map ψ).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (tm.unit.map ψ).ne_zero
    have h1 := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
    have h2 := congrArg (Matrix.vecMul · (g'.map χ)) h1
    simpa [Matrix.vecMul_vecMul, hGG] using h2
  rintro v ⟨x, hxs, hv⟩
  have h1 := t.mod.red (Over.homMk x hxs) v hv
  have hxG : (x ≫ t.mod.r) ≫ t.u.G.hom = spMap ψ := by
    rw [Category.assoc, pb.w, ← Category.assoc, hxs, Category.id_comp, hψ]
  have h2 := tm.crd (kb p) ψ (x ≫ t.mod.r) v hxG h1
  have hov : ((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
    rw [Category.assoc, tm.f_over, ← Category.assoc, hxG, hψ, Category.assoc, c.fac]
  obtain ⟨x', hx'⟩ : ∃ x' : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme,
      x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = ((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι :=
    ⟨IsOpenImmersion.lift _ _ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have e : Q.P.hom ((((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) w) = z := by
        rw [← Scheme.Hom.comp_apply, Category.assoc, hov, Subsingleton.elim w (IsLocalRing.closedPoint (kb p)), hx]
      show Q.P.hom _ ∈ Q.W l
      rw [e]
      exact hz), IsOpenImmersion.lift_fac _ _ _⟩
  have hov' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = rPt p ≫ y := by
    rw [← Category.assoc, hx', Category.assoc, hov]
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) x'
  obtain ⟨u, hu⟩ := InFibChart.crd_change Q hB.ov.ne l tm.l x' _ (rPt p ≫ y) hx'.symm hov' hx hz hz' g' hc' hw h2
  have h3 : a ⬝ᵥ w = 0 := by
    obtain ⟨j, e, -, he⟩ := hw
    have h4 := ha x' j (by
      rw [hx', Category.assoc]
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hG (Set.mem_univ _)) hov'
    rw [dotProduct, ← mul_zero (e : kb p), ← h4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he i, mul_left_comm]
    rfl
  have h5 : (tm.m.map ψ).mulVec v = u • (g'.map χ).mulVec w := hu
  show Matrix.vecMul (Matrix.vecMul a (g.map χ)) (tm.m.map ψ) ⬝ᵥ v = 0
  rw [← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, h5, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG,
    Matrix.one_mulVec, dotProduct_smul, h3, smul_zero]

end GlobalTheory.ZH.IndepFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointWithCharactersIffPullDeg
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.TorusPull

open ReciprocityTheory.ChartRestriction.G.DVR

section One

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem mem_torus_iff {T : Scheme.{0}} (z : T ⟶ (thickObj R I e G).left) :
    (∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z) ↔
      z ≫ g.pG.left = z ≫ ((Over.map (thick R I e)).obj (thickObj R I e G)).hom ≫ eSec D.P.A := by
  have hb : (fstG I e G).left ≫ G.hom ≫ eSec D.P.A =
      ((Over.map (thick R I e)).obj (thickObj R I e G)).hom ≫ eSec D.P.A :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec D.P.A) (Over.w (fstG I e G)))
  constructor
  · rintro ⟨τ, rfl⟩
    have c := ((CharAgree.comp_q_eq_one_iff g g.i).1 g.isKernel.w).trans (congrArg (g.i.left ≫ ·) hb)
    exact (Category.assoc _ _ _).trans ((congrArg (τ ≫ ·) c).trans (Category.assoc _ _ _).symm)
  · intro h
    let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (z ≫ (thickObj R I e G).hom)
    let a : FinalForm ⟶ thickObj R I e G := Over.homMk z rfl
    have k := (CharAgree.comp_q_eq_one_iff g a).2 (h.trans (congrArg (z ≫ ·) hb.symm))
    exact ⟨(g.isKernel.lift a (toUnit _) k).left,
      congrArg (fun q => q.left) (g.isKernel.lift_fst a (toUnit _) k)⟩

theorem val_torus {T : Scheme.{0}}
    (τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left) (χ : D.X) {y : T}
    {J : (T ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J) :
    val (g.t χ) (τ ≫ g.i.left) y J = gm τ y ⊤ (charUnit _ D.X χ) := by
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (τ ≫ (splitTorus _ D.X).hom)
  let a : FinalForm ⟶ splitTorus _ D.X := Over.homMk τ rfl
  exact (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm a 1 y J hJ χ).1

end One

section Two

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {T : Over (Spec (CommRingCat.of R))}
  {T' : Over (Spec (CommRingCat.of R'))}
  (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)


include hp in
theorem unit_iff {Z : Scheme.{0}} (z : Z ⟶ T'.left) :
    z ≫ p'.left = z ≫ T'.hom ≫ eSec D'.P.A ↔ (z ≫ h) ≫ p.left = (z ≫ h) ≫ T.hom ≫ eSec D.P.A := by
  have b := TorusCoordPull.over_base hD p p' h hp
  have l : (z ≫ p'.left) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = (z ≫ h) ≫ p.left := by
    rw [Category.assoc, hp, Category.assoc]
  have r : (z ≫ T'.hom ≫ eSec D'.P.A) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (z ≫ h) ≫ T.hom ≫ eSec D.P.A := by
    rw [Category.assoc, Category.assoc, hD.he, Category.assoc, reassoc_of% b]
  refine ⟨fun H => l.symm.trans ((congrArg (· ≫ _) H).trans r), fun H => ?_⟩
  refine (pull_grp hD).1.hom_ext (l.trans (H.trans r.symm)) ?_
  have u : eSec D'.P.A ≫ D'.P.A.hom = 𝟙 _ := Over.w η[D'.P.A]
  rw [Category.assoc, Category.assoc, Category.assoc, u, Over.w]
  exact congrArg (z ≫ ·) (Category.comp_id _).symm

end Two

theorem appTop_ext {Y Y' Z : Scheme.{0}} (r : Z ⟶ Y) (r' : Z ⟶ Y') (a : Γ(Y, ⊤)ˣ) (b : Γ(Y', ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ a = gm r' z ⊤ b) : r.appTop.hom a.val = r'.appTop.hom b.val := by
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤
  intro z hz
  have := congrArg Units.val (h z)
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at this
  exact this

theorem torus_point_iff : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (e : ℕ) (g : GtCoord I D e G) (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), g'.pG.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ g.pG.left → (∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g'.pG x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ D.Oφ g.pG (hD.xe x) k, LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) (g'.t x) (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ Oinvε _ hψ (g.t (hD.xe x)))) → ∀ (T : Scheme.{0}) (z : T ⟶ (thickObj R' I' e G').left) (a : D'.X → Γ(T, ⊤)), (∃ τ' : T ⟶ (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left, τ' ≫ g'.i.left = z ∧ ∀ x, τ'.appTop.hom (charUnit _ D'.X x).val = a x) ↔ ∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z ≫ h ∧ ∀ x, τ.appTop.hom (charUnit _ D.X (hD.xe x)).val = a x := by
  intro R R' _ _ _ _ I I' φ D D' hD G _ _ G' _ _ e g g' h hp ht T z a
  have mem := (mem_torus_iff g' z).trans ((unit_iff hD g.pG g'.pG h hp z).trans (mem_torus_iff g (z ≫ h)).symm)
  have ch : ∀ τ' τ, τ' ≫ g'.i.left = z → τ ≫ g.i.left = z ≫ h → ∀ x,
      τ'.appTop.hom (charUnit _ D'.X x).val = τ.appTop.hom (charUnit _ D.X (hD.xe x)).val := by
    intro τ' τ h' h₀ x
    refine appTop_ext _ _ _ _ fun y => ?_
    obtain ⟨J, hJ⟩ := TorusCoordPull.exists_good' D.P.isLB y
    obtain ⟨J', hJ'⟩ := TorusCoordPull.exists_good' D'.P.isLB y
    obtain ⟨hψ, H⟩ := ht x
    have P := (maps_iff hD.w _ _ _ (g'.t x) (g.t (hD.xe x)) h _
      (GeneratorPullback.pullAlong_le D.P.L _ h _ _ hψ) (fun _ => rfl)).1 H
    let FinalForm : Over (Spec (CommRingCat.of R')) :=
      Over.mk (z ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom)
    let ρ : FinalForm ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G') := Over.homMk z rfl
    have hρ : ρ ≫ g'.pG = 1 := by
      refine Over.OverMorphism.ext (((mem_torus_iff g' z).1 ⟨τ', h'⟩).trans ?_)
      have k : (toUnit FinalForm).left = FinalForm.hom := (Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec D'.P.A) k.symm)
    have v := TorusCoordPull.val_unit_pull hD g.pG g'.pG h hp P ρ hρ (y := y) hJ hJ'
    have v' := val_torus g' τ' x hJ'
    have v₀ := val_torus g τ (hD.xe x) hJ
    rw [h'] at v'
    rw [h₀] at v₀
    exact v'.symm.trans (v.symm.trans v₀)
  constructor
  · rintro ⟨τ', h', hx⟩
    obtain ⟨τ, h₀⟩ := mem.1 ⟨τ', h'⟩
    exact ⟨τ, h₀, fun x => (ch τ' τ h' h₀ x).symm.trans (hx x)⟩
  · rintro ⟨τ, h₀, hx⟩
    obtain ⟨τ', h'⟩ := mem.2 ⟨τ, h₀⟩
    exact ⟨τ', h', fun x => (ch τ' τ h' h₀ x).trans (hx x)⟩

end GlobalTheory.TorusPull
end
end

