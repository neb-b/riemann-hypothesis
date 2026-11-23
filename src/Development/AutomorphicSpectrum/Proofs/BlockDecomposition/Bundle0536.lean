module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionFieldOfPointCoordsTop
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.GenTop

theorem appLE_fromSpecResidueField {X : Scheme.{0}} {U : X.Opens} (x : X) (hx : x ∈ U)
    (h : ⊤ ≤ X.fromSpecResidueField x ⁻¹ᵁ U) :
    (X.fromSpecResidueField x).appLE U ⊤ h = X.evaluation U x hx ≫ (Scheme.ΓSpecIso _).inv := by
  have h' : ⊤ ≤ Spec.map (X.residue x) ⁻¹ᵁ (X.fromSpecStalk x ⁻¹ᵁ U) := h
  have e : X.fromSpecResidueField x = Spec.map (X.residue x) ≫ X.fromSpecStalk x := rfl
  have := Scheme.Hom.appLE_comp_appLE (Spec.map (X.residue x)) (X.fromSpecStalk x) U (X.fromSpecStalk x ⁻¹ᵁ U) ⊤ le_rfl h'
  rw [appLE_of_eq e U ⊤ h (h'.trans le_rfl), ← this, ← Scheme.Hom.app_eq_appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, Scheme.Hom.map_appLE]
  rw [← Scheme.germ_residue, Category.assoc, Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem pullRatio_SpecMap_fromSpec {N : ℕ} (i : Fin (N + 1)) {R : CommRingCat.{0}}
    (ψ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ R)
    (h : ⊤ ≤ (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    pullRatio (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⊤ i h j =
      (Scheme.ΓSpecIso R).inv (ψ (ratio ℤ N i j)) := by
  have h1 : (isAffineOpen_chart ℤ N i).fromSpec.appLE (chart ℤ N i) ⊤
      (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h3 := Scheme.Hom.appLE_comp_appLE (Spec.map ψ) (isAffineOpen_chart ℤ N i).fromSpec
    (chart ℤ N i) ⊤ ⊤ (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge le_rfl
  unfold pullRatio
  rw [← h3, h1]
  have := congrArg (fun q => q.hom (ratio ℤ N i j)) (Scheme.ΓSpecIso_inv_naturality ψ)
  exact this.symm

theorem surjective_of_factor {X : Scheme.{0}} (x : X) {F : Type} [Field F]
    (ι : CommRingCat.of F ⟶ X.residueField x) (G : Spec (.of F) ⟶ X)
    (h : Spec.map ι ≫ G = X.fromSpecResidueField x) : Function.Surjective ι.hom := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective G
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  have hz : z = x := by
    have e := congrArg (fun f : Spec (X.residueField x) ⟶ X => f default) h
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hz
  rw [← Category.assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (φ ≫ ι) = Spec.map (𝟙 _) := by
    rw [← cancel_mono (X.fromSpecResidueField _), Spec.map_id, Category.id_comp]
    exact h
  have h3 : φ ≫ ι = 𝟙 _ := Spec.map_injective h2
  intro a
  refine ⟨φ.hom a, ?_⟩
  have := congrArg (fun q => q.hom a) h3
  simpa using this

theorem blockFnField_ptCoord_eq_top (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n)
    [CharZero ((MP ℤ m n).residueField x)] : blockFnField (ptCoord x) = ⊤ := by
  have hone : ∀ k, ptCoord x ⟨k, ptChart x k⟩ = 1 := fun k => by
    simp only [ptCoord, pullRatio_self, map_one]
  have hmem : ∀ p, ptCoord x p ∈ blockFnField (ptCoord x) := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, by rw [hone, div_one]⟩
  let F := blockFnField (ptCoord x)
  let r : ∀ k, Fin (n k + 1) → F := fun k j => ⟨ptCoord x ⟨k, j⟩, hmem _⟩
  have hr : ∀ k, r k (ptChart x k) = 1 := fun k => Subtype.ext (hone k)
  let ρ : ∀ k, Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k)) ⟶ CommRingCat.of F := fun k =>
    CommRingCat.ofHom (R := Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k))) (S := F)
      (chartLift (ptChart x k) (Int.castRingHom F) (r k))
  let g : ∀ k, Spec (CommRingCat.of F) ⟶ projectiveSpace ℤ (n k) := fun k =>
    Spec.map (ρ k) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec
  let G : Spec (CommRingCat.of F) ⟶ MP ℤ m n :=
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (Spec.map (CommRingCat.ofHom (Int.castRingHom F))) g
      (fun _ => specZIsTerminal.hom_ext _ _)
  let ι : CommRingCat.of F ⟶ (MP ℤ m n).residueField x := CommRingCat.ofHom F.val.toRingHom
  have key : Spec.map ι ≫ G = (MP ℤ m n).fromSpecResidueField x := by
    refine GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_
    rw [Category.assoc, GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr]
    have hx := mem_ptChart x k
    have h₂' : ⊤ ≤ (MP ℤ m n).fromSpecResidueField x ⁻¹ᵁ blockChart n k (ptChart x k) := fun s _ => by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hx
    have e1 : Spec.map ι ≫ g k = Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec := by
      rw [Spec.map_comp, Category.assoc]
    have h₁ : ⊤ ≤ (Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec) ⁻¹ᵁ
        chart ℤ (n k) (ptChart x k) := by
      rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
      exact le_top
    rw [e1]
    refine GlobalTheory.ProjSpace.hom_ext (specZIsTerminal.hom_ext _ _) fun _ =>
      ⟨⊤, trivial, ptChart x k, h₁, by rw [Scheme.Hom.comp_preimage]; exact h₂', fun j => ?_⟩
    rw [pullRatio_SpecMap_fromSpec]
    have e2 := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k) (hi := le_rfl)
      (j := j) ((MP ℤ m n).fromSpecResidueField x) h₂'
    refine Eq.trans ?_ e2
    rw [appLE_fromSpecResidueField x hx]
    show _ = (Scheme.ΓSpecIso _).inv (ptCoord x ⟨k, j⟩)
    congr 1
    show F.val (chartLift (ptChart x k) (Int.castRingHom F) (r k) (ratio ℤ (n k) (ptChart x k) j)) = _
    rw [chartLift_ratio _ _ (hr k)]
    rfl
  have hs := surjective_of_factor x ι G key
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨b, rfl⟩ := hs a
  exact b.2

end GlobalTheory.CompanionTheory.MPDict.GenTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatement
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.RegroupFin

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem map_phiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  simp [PhiU, GlobalTheory.Tw.Phi, GeneralLinearGroup.map, apply_ite f]

theorem map_thetaGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) = thetaGL n c' (GeneralLinearGroup.map f g) := by
  have h1 : ∀ x : GL (Fin n) R, GeneralLinearGroup.map f (invT n R x) = invT n S (GeneralLinearGroup.map f x) := by
    intro x
    apply Units.ext
    ext i j
    have e : (GeneralLinearGroup.map f x)⁻¹ = GeneralLinearGroup.map f x⁻¹ := (map_inv _ x).symm
    simp only [invT, MonoidHom.coe_mk, OneHom.coe_mk, e]
    rfl
  have h2 : GeneralLinearGroup.map f (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map f g) := by
    apply Units.ext
    ext i j
    exact h _
  have h3 : ∀ (T : Type) [CommRing T] (d : T →+* T) (x : GL (Fin n) T),
      thetaGL n d x = PhiU n T * invT n T (GeneralLinearGroup.map d x) * (PhiU n T)⁻¹ := fun _ _ _ _ => rfl
  rw [h3, h3, map_mul, map_mul, map_inv, map_phiU, h1, h2]

theorem evw_pv (v : PlF E) (w : Above v) (y : Gf E a b) : evw w (pv a b v y) = atW w.1 y := by
  refine Prod.ext ?_ ?_ <;> · apply Units.ext; ext i j; rfl

theorem cjv_spec (hc : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hc E v
  unfold cjv
  rw [dite_eq_left h]
  exact h.choose_spec.2 x

theorem pv_thP (hc : CjEx) (v : PlF E) (y : Gf E a b) : pv a b v (thP E a b y) = thv a b v (pv a b v y) :=
  Prod.ext (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) a y.1) (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) b y.2)

theorem finprod_fibres {X Y : Type} (u : X → Y) (S : Set X) (hu : Set.InjOn u S) (F : X → ℂ) :
    ∏ᶠ w ∈ S, F w = ∏ᶠ v : Y, ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 := by
  set G : Y → ℂ := fun v => ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 with hG
  have hone : ∀ v, v ∉ u '' S → G v = 1 := by
    intro v hv
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have hw : w.1 ∉ S := fun hw => hv ⟨w.1, hw, w.2⟩
    simp [hw]
  have hval : ∀ w ∈ S, G (u w) = F w := by
    intro w hw
    have hs : {i : {x : X // u x = u w} | i.1 ∈ S} = {⟨w, rfl⟩} := by
      ext i
      change i.1 ∈ S ↔ i = ⟨w, rfl⟩
      constructor
      · intro hi
        exact Subtype.ext (hu hi hw i.2)
      · rintro rfl
        exact hw
    have : G (u w) = ∏ᶠ i ∈ {i : {x : X // u x = u w} | i.1 ∈ S}, F i.1 := rfl
    rw [this, hs, finprod_mem_singleton]
  have h1 : ∏ᶠ v, G v = ∏ᶠ v ∈ u '' S, G v := by
    rw [← finprod_mem_univ]
    refine finprod_mem_inter_mulSupport_eq' _ _ _ fun v hv => ?_
    simp only [Set.mem_univ, true_iff]
    by_contra hn
    exact hv (hone v hn)
  rw [h1, finprod_mem_image hu]
  exact (finprod_mem_congr rfl hval).symm

theorem regroup_of_cjEx (hc : CjEx) : Regroup := by
  intro E _ _ _ a b S hS φ₁ φ₂ _ _ y
  have hinj : Set.InjOn (fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))) S := by
    intro u hu u' hu' h
    obtain ⟨x, -, hx⟩ := hS u
    exact (hx u ⟨hu, rfl⟩).trans (hx u' ⟨hu', h.symm⟩).symm
  unfold finFn
  rw [finprod_fibres _ S hinj]
  refine finprod_congr fun v => ?_
  unfold fv
  refine finprod_congr fun w => finprod_congr fun _ => ?_
  rw [evw_pv, ← pv_thP hc, evw_pv]

theorem regroup : Regroup := regroup_of_cjEx GlobalTheory.CompanionTheory.CjEx.cjEx

end GlobalTheory.CompanionTheory.RegroupFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodSetCompactLinearlyIndependent
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma cont_coord (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (b : Fin n) (i : Fin M) (w : W) :
    Continuous fun X : Fin n → Fin M → K => κ (X b i) w :=
  (continuous_apply w).comp (hκ.continuous.comp ((continuous_apply i).comp (continuous_apply b)))

lemma isOpen_nearK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (w : W) (s : Fin n → ℂ) (ε : ℝ) :
    IsOpen (nearK (M := M) κ w s ε) := by
  have : nearK (M := M) κ w s ε = ⋂ i, {X | ‖∑ b, s b * κ (X b i) w‖ < ε} := by
    ext X; simp [nearK]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  refine isOpen_lt ?_ continuous_const
  refine Continuous.norm ?_
  refine continuous_finsetSum _ fun b _ => ?_
  exact continuous_const.mul (cont_coord κ hκ b i w)

lemma isCompact_boxK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (r : Fin n → W → ℝ) :
    IsCompact (boxK (M := M) κ r) := by
  let e : K ≃ₜ (W → ℂ) := hκ.homeomorph κ
  let Φ : (Fin n → Fin M → K) ≃ₜ (Fin n → Fin M → W → ℂ) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => e
  have hB : IsCompact (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_univ_pi fun w =>
      isCompact_closedBall _ _
  have : boxK (M := M) κ r = Φ ⁻¹' (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) := by
    ext X
    simp [boxK, Φ, e]
  rw [this]
  exact (Homeomorph.isCompact_preimage Φ).2 hB

lemma linIndep_iff (κ : K ≃+* (W → ℂ)) {n M : ℕ} (X : Fin n → Fin M → K) :
    LinearIndependent K X ↔ ∀ w, LinearIndependent ℂ (fun b i => κ (X b i) w) := by
  classical
  constructor
  · intro hX w
    rw [Fintype.linearIndependent_iff] at hX ⊢
    intro t ht b
    have key := hX (fun b => κ.symm (Pi.single w (t b))) (by
      funext i
      apply κ.injective
      funext w'
      have := congrFun ht i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, Finset.sum_apply, Pi.mul_apply]
      by_cases h : w' = w
      · subst h; simpa using this
      · simp [Pi.single_apply, h])
    have := congrFun (congrArg κ (key b)) w
    simpa using this
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro c hc b
    apply κ.injective
    funext w
    have hw := h w
    rw [Fintype.linearIndependent_iff] at hw
    have := hw (fun b => κ (c b) w) (by
      funext i
      have := congrArg (fun y => κ y w) (congrFun hc i)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Finset.sum_apply, map_sum, map_mul] using this) b
    simpa using this

lemma isOpen_linIndep (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) (n M : ℕ) :
    IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} := by
  have : {X : Fin n → Fin M → K | LinearIndependent K X} =
      ⋂ w, (fun X : Fin n → Fin M → K => fun b i => κ (X b i) w) ⁻¹'
        {Y : Fin n → Fin M → ℂ | LinearIndependent ℂ Y} := by
    ext X; simp [linIndep_iff κ X]
  rw [this]
  refine isOpen_iInter_of_finite fun w => ?_
  refine isOpen_setOfPred_linearIndependent.preimage ?_
  exact continuous_pi fun b => continuous_pi fun i => cont_coord κ hκ b i w

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma goodK_subset (κ : K ≃+* (W → ℂ)) {n M : ℕ} (R ε : ℝ) (hε : 0 < ε) :
    goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro X hX
  rcases hX with ⟨-, hX⟩
  show LinearIndependent K X
  rw [Fintype.linearIndependent_iff]
  intro c hc b0
  by_contra h0
  have hk : κ (c b0) ≠ 0 := by
    intro h; exact h0 (κ.injective (by simpa using h))
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hk
  haveI : Nonempty (Fin n) := ⟨b0⟩
  obtain ⟨a, ha⟩ := Finite.exists_max fun b => ‖κ (c b) w‖
  have hca : κ (c a) w ≠ 0 := by
    intro h
    have := ha b0
    rw [h, norm_zero] at this
    exact hw (norm_le_zero_iff.1 this)
  have hsum : ∀ i, ∑ b, κ (c b) w * κ (X b i) w = 0 := by
    intro i
    have := congrArg (fun y => κ y w) (congrFun hc i)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Finset.sum_apply, map_sum, map_mul] using this
  apply hX
  simp only [Set.mem_iUnion]
  refine ⟨w, a, fun b => κ (c b) w / κ (c a) w, ⟨div_self hca, fun b => ?_⟩, ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ (ha b) (norm_nonneg _)
  · intro i
    have : ∑ b, κ (c b) w / κ (c a) w * κ (X b i) w = (κ (c a) w)⁻¹ * ∑ b, κ (c b) w * κ (X b i) w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, hsum i, mul_zero, norm_zero]
    exact hε

theorem boxK_goodK_topology : ∀ (K W : Type) [CommRing K] [TopologicalSpace K] [Fintype W] (κ : K ≃+* (W → ℂ)), IsHomeomorph κ → ∀ n M : ℕ, (∀ r : Fin n → W → ℝ, IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) ∧ IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} ∧ ∀ R ε : ℝ, 0 < ε → IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε) ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro K W _ _ _ κ hκ n M
  refine ⟨fun r => isCompact_boxK κ hκ r, isOpen_linIndep κ hκ n M, fun R ε hε => ⟨?_, goodK_subset κ R ε hε⟩⟩
  refine (isCompact_boxK κ hκ _).diff ?_
  exact isOpen_iUnion fun w => isOpen_iUnion fun a => isOpen_iUnion fun s => isOpen_iUnion fun _ =>
    isOpen_nearK κ hκ w s ε

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepDualInverse
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem ev_unit_inv_mul {m : ℕ} {n : Fin (m + 1) → ℕ} {U : (MP ℤ m n).Opens} (v : Γ(MP ℤ m n, U)ˣ)
    (y : CxPts (mpStr ℤ m n) σ₀) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ U) :
    CxPts.ev (mpStr ℤ m n) σ₀ U (↑v⁻¹ : Γ(MP ℤ m n, U)) y *
      CxPts.ev (mpStr ℤ m n) σ₀ U (v : Γ(MP ℤ m n, U)) y = 1 := by
  unfold CxPts.ev ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  split_ifs with h
  · rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  · exact (h hy).elim

theorem isHermRep_dual : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep M.dual A.inv := by
  intro m n M A hA
  obtain ⟨u, h1, h2, h3⟩ := hA
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_, ?_⟩
  · rintro (i : M.B.ι) (j : M.B.ι) c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (M.B.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv, ← mul_inv]
    exact congrArg (·⁻¹) (h1 i j c)
  · rintro (i : M.B.ι) c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-A.a k)
    rw [map_inv, map_inv]
    have h := congrArg (·⁻¹) (h2 i c c')
    simp only [mul_inv, ← Finset.prod_inv_distrib, ← zpow_neg] at h
    exact h
  · rintro (i : M.B.ι) c y z hz (hyin : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    change (A.h z)⁻¹ = (∏ k, ‖z ⟨k, c k⟩‖ ^ (-A.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y‖ * Real.exp (-(M.φ σ₀).φ i y / 2)
    have e : CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y =
        (CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)) y)⁻¹ :=
      eq_inv_of_mul_eq_one_left (ev_unit_inv_mul (u i c) y hyin)
    rw [h3 i c y z hz hyin]
    simp only [zpow_neg, Finset.prod_inv_distrib, neg_div, Real.exp_neg, mul_inv]
    congr 2
    rw [e, norm_inv]

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTrivialLineBundle
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isHermRep_triv : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), IsHermRep (HermLB.triv (mpStr ℤ m n)) (GlobalTheory.CompanionTheory.Ar.Top.trivLine (Bk n)) := by
  intro m n
  refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
    exact (map_one (Semi.res _)).symm
  · intro i c c'
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]
  · intro i c y z _ hy
    have e : CxPts.ev (mpStr ℤ m n) σ₀ ((HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)
        (((1 : Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)ˣ)) :
          Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)) y = 1 := by
      rw [CxPts.ev_eq hy, Units.val_one, map_one]
    rw [e]
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine, HermLB.triv, Weight.ofFun]

end GlobalTheory.CompanionTheory.MPDict
end
end

