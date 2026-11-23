module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.WitnessIsFormalParam
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTangentVectorsCompat
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiePull


set_option maxHeartbeats 800000 in
theorem exists_lieBasis_of_tanBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    (t : SAB H X0) {K : Type} [CommRing K] (x0 : Sp K ⟶ X0) (A : Over (Sp K)) [GrpObj A] (θ : A.left ⟶ t.G.left)
    (hθ : IsGrpPullback A t.G x0 θ) {m : ℕ} (u : Fin m → (Sp (DualNumber K) ⟶ t.G.left))
    (hu : ∀ j, IsTanAtG t x0 (u j)) (hc : ∀ w, IsTanAtG t x0 w → ∃! c : Fin m → K, IsCombAtG t x0 u c w) :
    ∃ v : Fin m → (epsR K ⟶ A), IsLieBasis v ∧ ∀ j, (v j).left ≫ θ = u j := by
  classical
  let up : ∀ w : Sp (DualNumber K) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x0 →
      (epsR K ⟶ A) := fun w h => Over.homMk (hθ.1.lift w _ h) (hθ.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ θ = w := fun w h => hθ.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp K)} {a b : T ⟶ A}, a.left ≫ θ = b.left ≫ θ → a = b := fun h =>
    Over.OverMorphism.ext (hθ.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp K), (1 : T ⟶ A).left ≫ θ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hθ T))
  have tan : ∀ w : epsR K ⟶ A, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ θ) := fun w => by
    have e : (1 : Chart.sp (R₀ := K) K ⟶ A).left ≫ θ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id K)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hθ.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ θ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (a : Fin n → (epsR K ⟶ A)), (List.ofFn a).prod.left ≫ θ =
      (List.ofFn fun i => (pushPt hθ.1.w (a i) : tEpsG x0 ⟶ t.G)).prod.left := fun a =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hθ (epsR K)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → K) (v : Fin n → (epsR K ⟶ A)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ θ) c (w.left ≫ θ) := fun c v w => by
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨fun i => pushPt hθ.1.w (a i), fun i => (congrArg (· ≫ θ) (ha i)).trans (Category.assoc _ _ _), (pr a).symm⟩
    · rintro ⟨a, ha, hw⟩
      refine ⟨fun i => up (a i).left (Over.w _), fun i => hθ.1.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((ha i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (a i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : a = fun i => (pushPt hθ.1.w (up (a i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (a i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this
  let v : Fin m → (epsR K ⟶ A) := fun j => up (u j) (hu j).1
  have hv : (fun i => (v i).left ≫ θ) = u := funext fun j => hup _ _
  refine ⟨v, ⟨fun j => (tan _).2 (by rw [hup]; exact hu j), fun w hw => ?_⟩, fun j => hup _ _⟩
  have key : ∀ c, IsLieComb c v w ↔ IsCombAtG t x0 u c (w.left ≫ θ) := fun c => by
    rw [comb, hv]
  obtain ⟨c, hc1, hc2⟩ := hc _ ((tan w).1 hw)
  exact ⟨c, (key c).2 hc1, fun c' h' => hc2 c' ((key c').1 h')⟩

theorem lieBasis_of_tanBasis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}} (t : ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H X0) {K : Type} [CommRing K] (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ X0) (A : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (θ : A.left ⟶ t.G.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A t.G x0 θ → ∀ {m : ℕ} (u : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ t.G.left)), (∀ j, Formalism.L2.Pj.IsTanAtG t x0 (u j)) → (∀ w, Formalism.L2.Pj.IsTanAtG t x0 w → ∃! c : Fin m → K, Formalism.L2.Pj.IsCombAtG t x0 u c w) → ∃ v : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR K ⟶ A), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v ∧ ∀ j, (v j).left ≫ θ = u j :=
  by
  intro E _ _ _ H X0 t K _ x0 A _ θ hθ m u hu hc
  exact exists_lieBasis_of_tanBasis t x0 A θ hθ u hu hc

end GlobalTheory.LiePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FibrePull

theorem fibre_isPull : ∀ (S T : Scheme.{0}) (A₀ : Over T) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S), P₀.IsLB → P.IsLB → SameFib A₀ P₀ (𝟙 _) A P f → ∃ (φ : A₀.left ⟶ A.left) (φ₂ : (G2 A₀).left ⟶ (G2 A).left), IsGrpPullback A₀ A f φ ∧ IsSquare φ φ₂ ∧ LBIso P₀ (P.pull φ₂) ∧ LBIso (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  intro S T A₀ _ _ P₀ A _ _ P f hP₀ hP hS
  obtain ⟨H, _, _, a, a₂, a', a₂', h₁, s₁, h₂, s₂, w⟩ := hS
  have : IsMonHom (Iso.refl A₀).hom := inferInstanceAs (IsMonHom (𝟙 A₀))
  obtain ⟨e, he, hea⟩ := grpPullback_iso h₁ (isGrpPullback_of_iso (Iso.refl A₀))
  have hea' : e.hom.left = a := by simpa using hea
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hinv : e.inv.left ≫ a = 𝟙 _ := by rw [← hea', ← Over.comp_left, e.inv_hom_id, Over.id_left]
  let ψ : G2 A₀ ⟶ G2 H := lift (fst A₀ A₀ ≫ e.inv) (snd A₀ A₀ ≫ e.inv)
  have ext2 : ∀ {G : Over T} {X : Scheme.{0}} (u v : X ⟶ (G2 G).left), u ≫ (fst G G).left = v ≫ (fst G G).left →
      u ≫ (snd G G).left = v ≫ (snd G G).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
  have ext2' : ∀ {X : Scheme.{0}} (u v : X ⟶ (G2 A).left), u ≫ (fst A A).left = v ≫ (fst A A).left →
      u ≫ (snd A A).left = v ≫ (snd A A).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
  have k1 : ψ.left ≫ (fst H H).left = (fst A₀ A₀).left ≫ e.inv.left := by rw [← Over.comp_left, lift_fst, Over.comp_left]
  have k2 : ψ.left ≫ (snd H H).left = (snd A₀ A₀).left ≫ e.inv.left := by rw [← Over.comp_left, lift_snd, Over.comp_left]
  have d1 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (fst A₀ A₀).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
  have d2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (snd A₀ A₀).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have d1' : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
  have d2' : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have hψ : ψ.left ≫ a₂ = 𝟙 _ := by
    apply ext2
    · rw [Category.assoc, s₁.1, Category.id_comp, ← Category.assoc, k1, Category.assoc, hinv, Category.comp_id]
    · rw [Category.assoc, s₁.2, Category.id_comp, ← Category.assoc, k2, Category.assoc, hinv, Category.comp_id]
  have hψ₀ : LBIso P₀ ((P₀.pull a₂).pull ψ.left) :=
    GlobalTheory.ThetaAffineGlue.lbIso_cancel hP₀ (pull_isLB hP₀ _) hP₀
      (by rw [hψ]; exact GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP₀)
      (LBIso.trans (pull_isLB hP₀ _) (pull_isLB hP _) (pull_isLB hP₀ _) w w.symm)
  have hP₀₂ : LBIso P₀ (P.pull (ψ.left ≫ a₂')) :=
    hψ₀.trans hP₀ (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP _) (GlobalTheory.ThetaAffineGlue.lbIso_pull w ψ.left)
  have hd : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (ψ.left ≫ a₂') = (e.inv.left ≫ a') ≫ (lift (𝟙 A) (𝟙 A)).left := by
    apply ext2'
    · simp only [Category.assoc]
      rw [s₂.1, d1', Category.comp_id, ← Category.assoc ψ.left, k1, ← Category.assoc, ← Category.assoc, d1, Category.id_comp]
    · simp only [Category.assoc]
      rw [s₂.2, d2', Category.comp_id, ← Category.assoc ψ.left, k2, ← Category.assoc, ← Category.assoc, d2, Category.id_comp]
  refine ⟨e.inv.left ≫ a', ψ.left ≫ a₂', ?_, ?_, hP₀₂, ?_⟩
  · exact ((isGrpPullback_of_iso e.symm).comp h₂).congr (Category.id_comp _) rfl
  · constructor
    · rw [Category.assoc, s₂.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
    · rw [Category.assoc, s₂.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · have h3 := GlobalTheory.ThetaAffineGlue.lbIso_pull hP₀₂ (lift (𝟙 A₀) (𝟙 A₀)).left
    rw [hd] at h3
    have hΔ := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
    exact h3.trans (pull_isLB hP₀ _) (pull_isLB hP _) (pull_isLB hΔ _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull
        (show LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P.pull (lift (𝟙 A) (𝟙 A)).left) from
          LBIso.trans hΔ (pull_isLB hΔ _) hΔ (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ) (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ))) (e.inv.left ≫ a')).symm

end GlobalTheory.FibrePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H0LowerBoundIntersectionNumberClosureStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h0_lower_bound_of_isAmple_cartierDiv : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X) (k : ℕ) (q : ℚ),
  IsAmpleLB (toLB A) → letI := algebraΓOfHom p; topologicalKrullDim (closure ({z} : Set X)) = k →
  q < (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤
    (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) : ℚ) := by
  first | exact @GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed | exact GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed | (intros; apply GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1StructureBaseChangeExtension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem isAffineHom_of_isPullback {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : IsAffineHom pr :=
  MorphismProperty.of_isPullback hp.flip inferInstance

theorem res_bijective (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] : Function.Bijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 :=
  have H := _root_.GlobalTheory.Obs.BC.preAff_basis X₀ X₁ pr (_root_.GlobalTheory.SqZeroBC.preimage_surj R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp)
  _root_.GlobalTheory.Obs.BasisO.restrict_bijective_one R₁ X₁ s₁ _ (preAff pr) H.1 H.2

theorem tens_bijective {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) [IsAffineHom pr] :
    Function.Bijective (tensCoef hp.w).pull1 := by
  exact _root_.GlobalTheory.Obs.BC.natCoef_pull1_bijective R₁ _ _ _ _ (tensCoef hp.w).naturality (tensCoef hp.w).smul fun U ↦ _root_.GlobalTheory.Obs.BC.tensHom_bijective R₀ R₁ X₀ X₁ s₀ s₁ pr hp U.unop _

def trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) :
    CatCoh.H1 (OAff s₁) ≃+ CatCoh.H1 (ext R₁ (OAff s₀)) :=
  haveI := isAffineHom_of_isPullback hp
  (AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 (res_bijective q hq hp)).trans
    (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).symm

theorem tens_trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] (c : CatCoh.H1 (OAff s₁)) :
    (tensCoef hp.w).pull1 (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) = (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c :=
  (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).apply_symm_apply _

section Compat

variable {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} [IsAffineHom pr] [IsAffineHom pr']
  {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁} (e : f₁ ≫ pr = pr' ≫ f₀)

def pullBC (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) :
    CoefMap (RingHom.id R₁) (preAff pr ⋙ OAff s₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairSnd f₀
  α p := (pairPull h₁).α ((pairBC pr pr' e).obj p)
  naturality a b := (pairPull h₁).naturality ((pairBC pr pr' e).map a) b
  smul p r b := (pairPull h₁).smul ((pairBC pr pr' e).obj p) r b

def resBC : CoefMap (RingHom.id R₁) (preAff pr' ⋙ OAff t₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairFst f₀
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

end Compat

end GlobalTheory.Obs.BC

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem extendedCoefficients_pullback_compat (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0)
    {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀}
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀)
    (c : CatCoh.H1 (OAff s₁)) (c' : CatCoh.H1 (OAff t₁))
    (H : IsExtendedPullbackDegOne R₁ h₀ (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) :
    IsPullO h₁ c c' := by
  haveI := isAffineHom_of_isPullback hp
  haveI := isAffineHom_of_isPullback hp'
  have kd := tens_trEquiv q hq hp c
  have kd' := tens_trEquiv q hq hp' c'
  let Φ := CoefMap.restrict (OPair f₁ t₁) (pairBC pr pr' e)
  have inj : Function.Injective Φ.pull1 := by
    intro x x' hx
    obtain ⟨y, rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x
    obtain ⟨y', rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x'
    have HH := _root_.GlobalTheory.Obs.BC.pairBC_fst_basis X₀ X₁ Y₀ Y₁ pr pr' f₀ f₁ e (_root_.GlobalTheory.SqZeroBC.preimage_surj R₀ R₁ q hq Y₀ Y₁ t₀ t₁ pr' hp')
    have B := _root_.GlobalTheory.Obs.BasisO.restrict_bijective_one R₁ Y₁ t₁ _ (pairBC pr pr' e ⋙ pairFst f₁) HH.1 HH.2
    have k : ∀ z, Φ.pull1 ((pairRes f₁ t₁).pull1 z) =
        (CoefMap.restrict (OAff t₁) (pairBC pr pr' e ⋙ pairFst f₁)).pull1 z := by
      intro z; obtain ⟨z, rfl⟩ := H1.mk_surjective _ z; rfl
    rw [k, k] at hx
    rw [B.1 hx]
  have k1 : Φ.pull1 ((pairPull h₁).pull1 c) = (tensPair hp'.w e).pull1 ((extMap R₁ (pairPull h₀)).pull1
      (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c)) := by
    have a1 : Φ.pull1 ((pairPull h₁).pull1 c) =
        (pullBC e h₁).pull1 ((CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c) := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [a1, ← kd, ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp.w).comp (pullBC e h₁))
      ((extMap R₁ (pairPull h₀)).comp (tensPair hp'.w e)) (𝟙 (pairSnd f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff s₀)) _ b)).trans ?_
    exact _root_.GlobalTheory.Obs.BC.tensPair_extMap_pairPull R₀ R₁ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' hp.w hp'.w f₀ f₁ h₀ h₁ e p b
  have k2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') = (tensPair hp'.w e).pull1 ((extMap R₁ (pairRes f₀ t₀)).pull1
      (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) := by
    have a2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') =
        (resBC e).pull1 ((CoefMap.restrict (OAff t₁) (preAff pr')).pull1 c') := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c'; rfl
    rw [a2, ← kd', ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp'.w).comp (resBC e))
      ((extMap R₁ (pairRes f₀ t₀)).comp (tensPair hp'.w e)) (𝟙 (pairFst f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff t₀)) _ b)).trans ?_
    have hc : coefHom (pairRes f₀ t₀) p = AlgHom.id R₀ _ := AlgHom.ext fun _ ↦ rfl
    change (tensPair hp'.w e).α p (extHom R₁ (coefHom (pairRes f₀ t₀) p) b) = _
    rw [hc]
    exact congrArg ((tensPair hp'.w e).α p) (DFunLike.congr_fun Algebra.TensorProduct.map_id b)
  apply inj
  unfold IsExtendedPullbackDegOne at H
  rw [k1, k2, H]

end GlobalTheory.Obs.BC

theorem GlobalTheory.Obs.BC.extO1 : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H1 (OAff s₁) ≃+ GlobalTheory.CatCoh.H1 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegOne R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullO h₁ c c' :=
  fun _ _ _ _ _ q hq ↦ ⟨GlobalTheory.Obs.BC.trEquiv q hq, fun _ _ _ _ _ hp _ _ _ _ _ hp' _ _ h₀ h₁ e c c' H ↦
    GlobalTheory.Obs.BC.extendedCoefficients_pullback_compat q hq hp hp' h₀ h₁ e c c' H⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT.KerBy

theorem ev_nsmul {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hadd : ∀ x y, f (x + y) = f x * f y)
    (e : ℕ) (y : La) : f (e • y) = f y ^ e := by
  induction e with
  | zero =>
    have h := hadd 0 0
    rw [add_zero] at h
    simpa using (mul_eq_left.1 h.symm)
  | succ e ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem pow_eq_one_at_geom (hC : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1) {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (e : ℕ) (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f)
    (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (g : Over.mk x₀ ⟶ o.A)
    (hg : ∃ t : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, t.IsGen) :
    g ^ e = 1 := by
  have hpr : p.Prime := Fact.out
  obtain ⟨e', he', hk⟩ := o.kerP
  have hn : g ^ e' = 1 := hk _ g hg
  have hpos : 0 < e' := by
    rcases Nat.eq_zero_or_pos e' with h | h
    · subst h
      have := (Nat.coprime_zero_left p).1 he'
      exact absurd this hpr.one_lt.ne'
    · exact h
  let φ := Spec.preimage (x₀ ≫ t)
  have hβ : x₀ ≫ t = spMap φ.hom := by
    simp [spMap, φ]
  obtain ⟨I, -⟩ := o.geom k x₀ φ.hom hβ
  have hunit : ∀ m : ℕ, m.Coprime p → ((m : ℕ) : k) ≠ 0 := fun m hm => by
    have := (b.unit m hm).map φ.hom
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨y, hy⟩ := (I.onto e' hpos he' g).1 hn
  have hadd : ∀ m, ∀ u v, I.ev m (u + v) = I.ev m u * I.ev m v := fun m u v => I.add m u v

  have vanish : ∀ (m : ℕ), 0 < m → m.Coprime p → ∀ y' z : D.La, I.ev m y' ^ 2 = g →
      I.ζ m ^ (2 * D.EF y' z) = 1 := by
    intro m hm hmp y' z ha
    have ha1 : I.ev m y' ^ m = 1 := (I.onto m hm hmp _).2 ⟨y', rfl⟩
    have hb1 : I.ev m z ^ m = 1 := (I.onto m hm hmp _).2 ⟨z, rfl⟩
    have hgen : ∃ t : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ I.ev m y' ^ 2) (fst o.A (Over.mk x₀))).left).Gen,
        t.IsGen := ha ▸ hg
    have hc := hC S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ m (hunit m hmp) _ _ ha1 hb1 hgen _
      (I.isom m hm hmp y' z)
    exact ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (hc.trans (map_one _).symm)
  have key : ∀ z, (e' : ℤ) ∣ D.EF y z := by
    intro z
    by_cases hp2 : p = 2
    · subst hp2
      have hodd : Odd e' := Nat.odd_iff.2 (by
        rcases Nat.even_or_odd e' with h | h
        · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 h) he') (by norm_num)
        · exact Nat.odd_iff.1 h)
      obtain ⟨r, hr⟩ := hodd
      have h2 : 2 • ((r + 1) • y) = y + e' • y := by
        rw [smul_smul, hr]
        rw [show (2 * (r + 1)) = 1 + (2 * r + 1) by ring, add_smul, one_smul]
      have ha : I.ev e' ((r + 1) • y) ^ 2 = g := by
        rw [← ev_nsmul _ (hadd e'), h2, hadd, ev_nsmul _ (hadd e'), hy, hn, _root_.mul_one]
      have h1 := vanish e' hpos he' _ z ha
      have h3 := ((I.ζ_prim e' hpos he').zpow_eq_one_iff_dvd _).1 h1
      rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
      have h4 : (e' : ℤ) ∣ (((r + 1) * 2 : ℕ) : ℤ) * D.EF y z := by
        have : (2 : ℤ) * (((r + 1 : ℕ) : ℤ) * D.EF y z) = (((r + 1) * 2 : ℕ) : ℤ) * D.EF y z := by push_cast; ring
        rw [← this]; exact_mod_cast h3
      have hcop : IsCoprime (e' : ℤ) (((r + 1) * 2 : ℕ) : ℤ) := by
        rw [Nat.isCoprime_iff_coprime]
        have : (r + 1) * 2 = e' + 1 := by omega
        rw [this]
        exact (Nat.coprime_self_add_right.2 (Nat.coprime_one_right e'))
      exact hcop.dvd_of_dvd_mul_left h4
    · have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp2)
      have hmp : (e' * 2).Coprime p := Nat.Coprime.mul_left he' h2p
      have ha : I.ev (e' * 2) y ^ 2 = g := by
        rw [I.tower e' 2 hpos two_pos hmp y, hy]
      have h1 := vanish (e' * 2) (by omega) hmp y z ha
      have h3 := ((I.ζ_prim (e' * 2) (by omega) hmp).zpow_eq_one_iff_dvd _).1 h1
      have h4 : (e' : ℤ) * 2 ∣ D.EF y z * 2 := by
        have : (2 : ℤ) * D.EF y z = D.EF y z * 2 := by ring
        rw [← this]; exact_mod_cast h3
      exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / e'
      map_add' := fun u v => by
        rw [map_add (f := _), Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (e' : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = e' • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev e' y ^ e := by rw [hy]
    _ = I.ev e' (e • y) := (ev_nsmul _ (hadd e') e y).symm
    _ = 1 := by rw [hyw]; exact (I.ker e' hpos he' _).2 ⟨w, rfl⟩

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem gen_comp : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left) (T T' : Over S) (a : T' ⟶ T) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → ∃ t : (P.pull (lift (snd A T' ≫ a ≫ x) (fst A T')).left).Gen, t.IsGen := by
  intro S A _ P T T' a x hx
  obtain ⟨t, ht⟩ := hx
  have e : (A ◁ a) ≫ lift (snd A T ≫ x) (fst A T) = lift (snd A T' ≫ a ≫ x) (fst A T') := by
    rw [comp_lift, whiskerLeft_snd_assoc, whiskerLeft_fst]
  rw [← e, Over.comp_left]
  exact ⟨_, LB.isGen_pullGen P _ _ t ht (A ◁ a).left⟩

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem siegKerBy_toSieg_of (hA : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ, (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left), ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1) (hB : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left) (T T' : Over S) (a : T' ⟶ T) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → ∃ t : (P.pull (lift (snd A T' ≫ a ≫ x) (fst A T')).left).Gen, t.IsGen) (hC : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1) : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e := by
  intro p _ D R _ b N S t o h M t₁ lev hl e _ hEF
  refine ⟨Obj.toSieg_ample o hl, ?_⟩
  intro T x hx
  obtain ⟨e', he', hk⟩ := o.kerP
  have hx' : x ^ e' = 1 := hk T x hx
  have hu : IsUnit ((e' : ℕ) : Γ(S, ⊤)) := by
    have h1 := (b.unit e' he').map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    have h2 := h1.map t.appTop.hom
    simpa using h2
  refine hA S o.A o.ab e' hu T x hx' e (fun k _ _ ξ => ?_)
  have hx2 := hB S o.A o.P T (Over.mk (ξ ≫ T.hom)) (Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) x hx
  exact pow_eq_one_at_geom hC o e hEF k (ξ ≫ T.hom) _ hx2

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem siegKerBy_toSieg : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e :=
  siegKerBy_toSieg_of GlobalTheory.T.pow_eq_one_of_geometric_points_torsion gen_comp GlobalTheory.T.commutatorPairing_eq_one_trivial_on_axis

end GlobalTheory.UPel.HT.KerBy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftEqComapSystemFiltrationStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCrystalHodgeLiftClasses_eq_comap_sys : CrystallineSmoothLift → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀], IsProper A₀.hom → GeometricallyConnected A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom → ∀ S : Sys I π A₀.hom, S.Presents X.hom i → primitiveCrystalHodgeLiftClasses (divided₂ hI) A₀ X i h.w = (S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype := by
  first | exact @GlobalTheory.LiftSys.hodgeFiltration_lift_eq_comap_systemFiltration | exact GlobalTheory.LiftSys.hodgeFiltration_lift_eq_comap_systemFiltration | (intros; apply GlobalTheory.LiftSys.hodgeFiltration_lift_eq_comap_systemFiltration <;> assumption)
end

