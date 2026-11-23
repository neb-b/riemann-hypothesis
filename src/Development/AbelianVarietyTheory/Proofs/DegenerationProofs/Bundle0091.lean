module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureWeightSectionToTwistedPolarisationPower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusKernelGenericFibre
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomGenericFibreKernelTorus
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0087
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusStableWeightsGenericFibre

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionNeZeroAt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem FibPre.exists_pure_ne_zero_at :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∀ (α : Φ.E.X) (x : Φ.Pt), ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) := by
  intro hL hL2 k _ _ Φ N hN π α x
  obtain ⟨s, hs⟩ := GlobalTheory.TwistNoBasePoint.exists_sec_twist hL hL2 k π.PB (N * 1) (by omega) _
    (x ≫ Φ.D.q ≫ π.β.hom)
  obtain ⟨φ, hφ, h⟩ := (_root_.GlobalTheory.ZH.TwSec.pure_sec_twist k Φ N 1 π α (by omega) le_rfl).2 s
  exact ⟨φ, hφ, (h x).2 hs⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem le_preimage_wchart_of_section {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (k : L.ι) : L.U k ≤ σ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => k) := by
  intro x hx
  refine Set.mem_iInter.2 fun _ => ?_
  change (σ ≫ π) x ∈ L.U k
  rw [h]
  exact hx

noncomputable def secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) : LB.Sec L where
  f k := (X.presheaf.map (homOfLE (le_preimage_wchart_of_section L π σ h k)).op).hom
    ((σ.app _).hom (s.f (fun _ => k)))
  compat i j := fn_ext fun x hx => by
    have li := le_preimage_wchart_of_section L π σ h i hx.1
    have lj := le_preimage_wchart_of_section L π σ h j hx.2
    rw [gs_res _ x inf_le_left hx, gs_mul _ x _ hx, gs_res _ x inf_le_right hx, gs_res _ x _ hx.1, gs_res _ x _ hx.2,
      gs_unit _ x _ hx]
    refine (gs_pull (𝟙 X) σ x _ li _).trans ((sec_trans s (𝟙 X ≫ σ) x li lj).trans
      (congrArg₂ (· * ·) ?_ (gs_pull (𝟙 X) σ x _ lj _).symm))
    simp only [trF, Fin.prod_univ_one, zpow_one, Category.assoc, h, Category.comp_id]

theorem gs_secOfSection {X Y Z : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (r : Z ⟶ X) (z : Z) (k : L.ι)
    (hz : r z ∈ L.U k) : gs r z _ ((secOfSection L π σ h s).f k) =
      gs (r ≫ σ) z (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (gs_res r z _ hz _).trans (gs_pull r σ z _ (le_preimage_wchart_of_section L π σ h k hz) _)

theorem valR_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) {F : Type} [CommRing F] (r : Sp F ⟶ X)
    (k : L.ι) (hr : ⊤ ≤ r ⁻¹ᵁ L.U k) : valR r _ ((secOfSection L π σ h s).f k) =
      valR (r ≫ σ) (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (HolHom.valR_res r _ _ hr).trans (HolHom.valR_comp r σ _ _).symm

theorem mem_nonzeroLocus_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (h' : π ≫ σ = 𝟙 Y) (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (y : Y)
    (hy : y ∈ nonzeroLocus s) : π y ∈ nonzeroLocus (secOfSection L π σ h s) := by
  obtain ⟨j, hj⟩ := AmpleSpan.exists_chart_of_mem s hy
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j (0 : Fin 1), funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hk : π y ∈ L.U k := Set.mem_iInter.1 hj 0
  rw [AmpleSpan.mem_nonzeroLocus_iff_gs _ π y hk, gs_secOfSection L π σ h s π y k hk, h']
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs s (𝟙 Y) y hj).1 hy

theorem exists_sec_of_baseOver : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), ∃ θ : LB.Sec P.L, (∀ y ∈ nonzeroLocus th, (snd (baseOver (Sp R)) P.A).left y ∈ nonzeroLocus θ) ∧ ∀ (z : baseOver (Sp R) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (a : R), IsValueAt P.A P.L 1 th z τ (fn a) → ∀ (F : Type) [CommRing F] (f : R →+* F) (k : P.L.ι), ⊤ ≤ (spMap f ≫ z.left) ⁻¹ᵁ P.L.U k → valR (spMap f ≫ z.left) _ (θ.f k) = f a * valR (X := (baseOver (Sp R)).left) (spMap f) _ (τ.s (fun _ => k)).val := by
  intro R _ P th
  let σ : P.A ⟶ baseOver (Sp R) ⊗ P.A := lift (toUnit P.A) (𝟙 P.A)
  have h : σ ≫ snd _ _ = 𝟙 _ := lift_snd _ _
  have h' : snd _ _ ≫ σ = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, Category.id_comp]
  have hl : σ.left ≫ (snd (baseOver (Sp R)) P.A).left = 𝟙 _ := by rw [← Over.comp_left, h, Over.id_left]
  have hl' : (snd (baseOver (Sp R)) P.A).left ≫ σ.left = 𝟙 _ := by rw [← Over.comp_left, h', Over.id_left]
  refine ⟨secOfSection P.L _ σ.left hl th, mem_nonzeroLocus_secOfSection P.L _ σ.left hl hl' th, ?_⟩
  intro z τ a hv F _ f k hk
  have e : z ≫ σ = ptSecT P.A z := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, ptSecT, lift_snd]
  have e' : z.left ≫ σ.left = (ptSecT P.A z).left := by rw [← Over.comp_left, e]
  let x : Sp F ⟶ (baseOver (Sp R)).left := spMap f
  have hw : ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => k) :=
    fun p hp => Set.mem_iInter.2 fun _ => hk hp
  have H := congrArg (valR x _) (hv (fun _ => k))
  have H₁ := (HolHom.valR_comp x (ptSecT P.A z).left _ _).trans ((HolHom.valR_res x _ _ hw).symm.trans H)
  have H₂ := H₁.trans (((HolHom.valR_eq x _ hw _).trans (map_mul _ _ _)).trans (congrArg₂ (· * ·)
    ((HolHom.valR_eq x _ hw _).symm.trans ((HolHom.valR_res x _ _ hw).trans (Conv.valR_spMap_top f a)))
    (HolHom.valR_eq x _ hw _).symm))
  refine (valR_secOfSection P.L _ σ.left hl th (x ≫ z.left) k hk).trans ?_
  rw [Category.assoc, e']
  exact H₂

end GlobalTheory.UnitTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusKernelGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitTorus_kernel_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∃ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i := by
  first | exact @GlobalTheory.ZJ.GenericTorus.exists_kerIs_generic | exact GlobalTheory.ZJ.GenericTorus.exists_kerIs_generic | (intros; apply GlobalTheory.ZJ.GenericTorus.exists_kerIs_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetricLift_action_geometricFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a)).left → x ^ S.N = 1 → ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)), SymLift u.A.A u.A.L S.N S.N x θ ∧ ∀ i t', IsActOf u.A.A u.A.L S.N θ (t i) t' → SecM.ofSec u.A.A t' = ∑ l, kf u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ a l i))) • SecM.ofSec u.A.A (t l) := by
  first | exact @GlobalTheory.ZH.ClassWeight.exists_symLift_act | exact GlobalTheory.ZH.ClassWeight.exists_symLift_act | (intros; apply GlobalTheory.ZH.ClassWeight.exists_symLift_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesOfGeometricFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoordinates_of_geometricFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : u.PtC) (v : S.J → PadicAlgCl p), Crd (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v → ρ.Crd (u.toA a) v := by
  first | exact @GlobalTheory.ZH.CrdMove.crd_of_moved | exact GlobalTheory.ZH.CrdMove.crd_of_moved | (intros; apply GlobalTheory.ZH.CrdMove.crd_of_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpan
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SpanImm

theorem closure_eq_top_iff {A B J : Type} [CommRing A] [CommRing B] (c : A →+* B) (r : J → B) :
    Subring.closure (Set.range c ∪ Set.range r) = ⊤ ↔
      Function.Surjective (MvPolynomial.eval₂Hom c r) := by
  rw [← RingHom.range_eq_top]
  suffices h : Subring.closure (Set.range c ∪ Set.range r) = (MvPolynomial.eval₂Hom c r).range by
    rw [h]
  refine le_antisymm (Subring.closure_le.2 ?_) ?_
  · rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  · rintro _ ⟨q, rfl⟩
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (Subring.subset_closure (Or.inr ⟨j, rfl⟩))

theorem range_constFn {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) :
    Set.range (constFn p U) = Set.range (p.appLE ⊤ U le_top).hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
  exact hs.range_comp (p.appLE ⊤ U le_top).hom

theorem immBy_iff {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type}
    (s : J → H.Sec) : ImmBy p H s Set.univ ↔ AmpleSpan.EmbedsBy p s := by
  unfold ImmBy AmpleSpan.EmbedsBy
  simp only [Set.mem_univ, iSup_pos, forall_true_left, range_constFn, closure_eq_top_iff]
  rfl

theorem immBy_of_span : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsProper p] (H : LB X), H.IsLB → ∀ (I J : Type) [Fintype I] [Fintype J] (t : I → H.Sec) (s : J → H.Sec), ImmBy p H t Set.univ → (∀ i, ∃ a : J → k, IsLin p s a (t i)) → ImmBy p H s Set.univ) := by
  intro k _ X p _ H _ I J _ _ t s ht hs
  refine (immBy_iff p H s).2 (((immBy_iff p H t).1 ht).of_inSpan fun i => ?_)
  obtain ⟨a, ha⟩ := hs i
  exact ⟨fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (a j), ha⟩

end GlobalTheory.ZH.SpanImm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomGenericFibreKernelTorusStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_generic_fibre_kernel_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → IsMonHom i := by
  first | exact @GlobalTheory.ZJ.KerSubgroup.isMonHom_generic | exact GlobalTheory.ZJ.KerSubgroup.isMonHom_generic | (intros; apply GlobalTheory.ZJ.KerSubgroup.isMonHom_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemKLOfHom
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory

theorem memKL_of_hom : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B), IsMonHom ψ → ∀ (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → LBIso L (M.pull ψ.left) → ∀ (T : Over S) (x : T ⟶ A), GlobalTheory.MemKL B M (x ≫ ψ) → GlobalTheory.MemKL A L x := by
  intro S A B _ _ ψ hψ L M hL hM hw T x hx
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let U : T ⊗ A ⟶ T ⊗ B := lift (fst T A) (snd T A ≫ ψ)
  have k₁ : U ≫ fst T B = fst T A := lift_fst _ _
  have k₂ : U ≫ snd T B = snd T A ≫ ψ := lift_snd _ _
  have k₃ : U ≫ ((fst T B ≫ x ≫ ψ) * snd T B) = ((fst T A ≫ x) * snd T A) ≫ ψ := by
    rw [MonObj.comp_mul, k₂, ← Category.assoc, k₁, MonObj.mul_comp, Category.assoc]
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst T B).left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst T B).left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ U.left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ U.left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q.left y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn M _ _ _) c hc
  let φ' : Fin 2 → (((fst T A).left ⁻¹ᵁ V).toScheme ⟶ A.left) := fun k => ((fst T A).left ⁻¹ᵁ V).ι ≫
    (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _) k
  obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame M (fun k => φ' k ≫ ψ.left) _ ![1, -1] n (fun k => by
    show (_ ≫ _) ≫ ψ.left = n ≫ _ ≫ _
    rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
    fin_cases k
    exacts [congrArg (fun q => _ ≫ q.left) k₃.symm, congrArg (fun q => _ ≫ q.left) k₂.symm])) c₁ h₁
  obtain ⟨c₃, h₃⟩ := exists_down hw hM hL c₂ h₂
  exact gen_chartPull (chartPullOut L _ _ _ φ' fun _ => rfl) c₃ h₃

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarMemOfPsiMemIdealStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → ∀ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), PsiScal D ga a → ∀ (x : D'.X) (J' : Ideal V), D'.PsiIn x J' → ∀ p q : R, algebraMap R (FractionRing R) q * (a (xe x)).val = algebraMap R (FractionRing R) p → ∃ m ∈ J', φ p = φ q * m := by
  first | exact @GlobalTheory.PsiRing.scalar_mem_of_psiIn | exact GlobalTheory.PsiRing.scalar_mem_of_psiIn | (intros; apply GlobalTheory.PsiRing.scalar_mem_of_psiIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanTranslatesMultiplicationPullbackThetaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_translates_multiplicationPullback_theta : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(S, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ (κ : Type) [Fintype κ] (b : κ → SecM P.A P.L N (baseOver S)), UnivBasis P N b → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver S)), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver S)) (t : I → LB.Sec (LPow P.A P.L N (baseOver S))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver S).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver S))) = ⊤ := by
  first | exact @GlobalTheory.ThetaReal.span_translates_mulPull | exact GlobalTheory.ThetaReal.span_translates_mulPull | (intros; apply GlobalTheory.ThetaReal.span_translates_mulPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFrame_isUnit_along_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → (∀ (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A (S.r * S.N)).left] ![(((S.r * S.N) : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig (S.r * S.N) α → ∃ κ, κ.IsGen ∧ Q.MulRel (S.r * S.N) α κ) → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w := by
  first | exact @GlobalTheory.ZH.TorsFrame.frameUnit | exact GlobalTheory.ZH.TorsFrame.frameUnit | (intros; apply GlobalTheory.ZH.TorsFrame.frameUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusStableWeightsGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusStable_weights_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → (∀ a', Stable i ((C.pull (pullback.fst G.hom (Out.jK R))).W a')) ∧ (∀ a' j', C.wt j' = C.c₀ → HasWt i ((C.pull (pullback.fst G.hom (Out.jK R))).W a') ((C.pull (pullback.fst G.hom (Out.jK R))).r a' j') 0) ∧ ∀ a' j' n, C.wt j' = c n → HasWt i ((C.pull (pullback.fst G.hom (Out.jK R))).W a') ((C.pull (pullback.fst G.hom (Out.jK R))).r a' j') (Pi.single n 1) := by
  first | exact @GlobalTheory.ZJ.GenericWt.stable_and_hasWt_generic | exact GlobalTheory.ZJ.GenericWt.stable_and_hasWt_generic | (intros; apply GlobalTheory.ZJ.GenericWt.stable_and_hasWt_generic <;> assumption)
end

