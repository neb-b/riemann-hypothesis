module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankTotalDegreeImageGrowth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureComponentTrdegGe
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0150

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen

namespace GlobalTheory.Biadditive

section Tools

variable {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {L : LB X}

theorem triv_of_formal (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : Triv (LB.LinComb L φ ε))
    (h : ∀ (U : Type) [CommGroup U] (k : (Y ⟶ X) → U), ∏ i, k (φ i) ^ ε i = ∏ i, k (φ' i) ^ ε' i) :
    Triv (LB.LinComb L φ' ε') := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := φ') (ε' := ε') h t ht
  exact ⟨t', ht'⟩

theorem triv_mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : Triv (LB.LinComb L φ ε)) (H' : Triv (LB.LinComb L φ' ε')) :
    Triv (LB.LinComb L (K := K ⊕ K') (Sum.elim φ φ') (Sum.elim ε ε')) := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨t', ht'⟩ := H'
  exact ⟨_, DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht'⟩

theorem triv_inv {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : Triv (LB.LinComb L φ ε)) :
    Triv (LB.LinComb L φ (fun k => - ε k)) := by
  obtain ⟨t, ht⟩ := H
  exact ⟨_, DVR.invGen_isGen _ _ _ _ ht⟩

theorem triv_pull_comp {f : Y ⟶ X} (H : Triv (L.pull f)) {Z : Scheme.{0}} (r : Z ⟶ Y) :
    Triv (L.pull (r ≫ f)) := by
  obtain ⟨t, ht⟩ := H
  exact ⟨_, DVR.pullGen_isGen _ _ _ t ht r⟩

end Tools

section Cube

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem triv_of_faces (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {H₀ : LB A.left} (hH : H₀.IsLB)
    (hamp : Out.RelAmple A H₀) {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    (φ : K → ((G3 A).left ⟶ X)) (ε : K → ℤ)
    (face : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S),
      r ≫ (x3 A i).left = b ≫ η[A].left → TrivAt M φ ε r)
    (formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (b : Z ⟶ S),
      r ≫ (x3 A 0).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ X) → U),
        ∏ i, k (r ≫ φ i) ^ ε i = 1) :
    Triv (LB.LinComb M φ ε) := by
  have := hA.geomConnected
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have H := fibTriv_clopen M φ ε (x3 A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart A j
    have hB := isAb_baseChange hA (j ≫ A.hom)
    have one := one_left_fst (A := A) (j ≫ A.hom)
    have pB : IsProjBy ((Over.pullback (j ≫ A.hom)).obj A).hom :=
      (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A H₀ hA hH hamp R (j ≫ A.hom) _ _ _
        (IsPullback.of_hasPullback _ _)).1
    let B := (Over.pullback (j ≫ A.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ φ k) ε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy R _ _ sm (isProjBy_tensor R B B pB pB)
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' => CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine face _ 1 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine face _ 0 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M φ ε (x3 A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M φ ε (x3 A 2).left := fun t => by
    have hr : Set.range (S.fromSpecResidueField (A.hom t)) = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := S.fromSpecResidueField (A.hom t) ≫ η[A].left
    have gw : g ≫ A.hom = S.fromSpecResidueField (A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec (S.residueField (A.hom t)) ⟶ S => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨S.residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 A 2).left g,
      face _ 2 (pullback.snd _ g ≫ S.fromSpecResidueField (A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm)⟩
  let e : A ⟶ G3 A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM φ ε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => formal _ (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

variable {B : Over S} (F : A ⊗ A ⟶ B)

def fourPts {T : Over S} (x x' y : T ⟶ A) : Fin 4 → (T.left ⟶ B.left) :=
  ![(lift (x * x') y ≫ F).left, (lift x y ≫ F).left, (lift x' y ≫ F).left, (lift 1 y ≫ F).left]

theorem comp_fourPts {T T' : Over S} (r : T' ⟶ T) (x x' y : T ⟶ A) (i : Fin 4) :
    r.left ≫ fourPts F x x' y i = fourPts F (r ≫ x) (r ≫ x') (r ≫ y) i := by
  fin_cases i <;>
  · simp only [fourPts, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    rw [← Over.comp_left, ← Category.assoc, comp_lift]
    try simp only [MonObj.comp_mul, MonObj.comp_one]

theorem exists_over {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S)
    (h : r ≫ (x3 A i).left = b ≫ η[A].left) :
    ∃ x : Over.mk (r ≫ (G3 A).hom) ⟶ G3 A, x.left = r ∧ x ≫ x3 A i = 1 := by
  have hb : b = r ≫ (G3 A).hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  refine ⟨Over.homMk r rfl, rfl, ?_⟩
  apply Over.OverMorphism.ext
  rw [Hom.one_def]
  exact h.trans (by rw [hb]; rfl)

theorem prod_fourPts {T : Over S} {x x' : T ⟶ A} (y : T ⟶ A) (h : x = 1 ∨ x' = 1)
    (U : Type) [CommGroup U] (k : (T.left ⟶ B.left) → U) :
    ∏ i, k (fourPts F x x' y i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  rcases h with rfl | rfl
  · simp [Fin.prod_univ_four, fourPts, -Over.comp_left]
  · simp [Fin.prod_univ_four, fourPts, -Over.comp_left, mul_comm]

theorem triv_add (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {H₀ : LB A.left} (hH : H₀.IsLB)
    (hamp : Out.RelAmple A H₀) {M : LB B.left} (hM : M.IsLB)
    (h₁ : Triv (M.pull (lift (1 : A ⟶ A) (𝟙 A) ≫ F).left))
    (h₂ : Triv (M.pull (lift (𝟙 A) (1 : A ⟶ A) ≫ F).left)) {T : Over S} (x x' y : T ⟶ A) :
    Triv (LB.LinComb M (K := Fin 3)
      ![(lift (x * x') y ≫ F).left, (lift x y ≫ F).left, (lift x' y ≫ F).left] ![1, -1, -1]) := by
  have a₁ : ∀ {T : Over S} (y : T ⟶ A), Triv (M.pull (lift 1 y ≫ F).left) := fun y => by
    have := triv_pull_comp h₁ y.left
    rwa [← Over.comp_left, ← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have a₂ : ∀ {T : Over S} (y : T ⟶ A), Triv (M.pull (lift y 1 ≫ F).left) := fun y => by
    have := triv_pull_comp h₂ y.left
    rwa [← Over.comp_left, ← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S), i = 0 ∨ i = 1 →
      r ≫ (x3 A i).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ B.left) → U),
        ∏ i, k (r ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
    intro Z r i b hi h U _ k
    obtain ⟨w, hw, h'⟩ := exists_over r i b h
    have := prod_fourPts F (x := w ≫ x3 A 0) (x' := w ≫ x3 A 1) (w ≫ x3 A 2)
      (hi.imp (fun e => e ▸ h') (fun e => e ▸ h')) U k
    simp only [← comp_fourPts, hw] at this
    exact this
  have cube := triv_of_faces hG hA hH hamp hM (fourPts F (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, 1]
    (fun r i b h => by
      by_cases hi : i = 0 ∨ i = 1
      · exact trivAt_of_formal hM r (formal r i b hi h)
      · obtain rfl : i = 2 := by omega
        obtain ⟨w, hw, h'⟩ := exists_over r 2 b h
        have e : (fun k => r ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) k) =
            fourPts F (w ≫ x3 A 0) (w ≫ x3 A 1) 1 := funext fun k => by
          rw [← h', ← comp_fourPts, hw]
        unfold TrivAt
        rw [e]
        refine triv_of_formal hM (triv_mul (triv_mul (a₂ (w ≫ x3 A 0 * w ≫ x3 A 1)) (triv_inv (a₂ (w ≫ x3 A 0))))
          (triv_mul (triv_inv (a₂ (w ≫ x3 A 1))) (a₂ (T := Over.mk (r ≫ (G3 A).hom)) 1))) fun U _ k => ?_
        simp [Fin.prod_univ_four, fourPts, -Over.comp_left, Fintype.prod_sum_type, _root_.mul_assoc])
    (fun r b h => formal r 0 b (Or.inl rfl) h)
  have c₀ : TrivAt M (fourPts F (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, 1] (lift x (lift x' y)).left := by
    obtain ⟨t, ht⟩ := cube
    exact ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
  have e : (fun k => (lift x (lift x' y)).left ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) k) =
      fourPts F x x' y := funext fun k => by
    rw [comp_fourPts]
    simp [x3]
  unfold TrivAt at c₀
  rw [e] at c₀
  refine triv_of_formal hM (triv_mul c₀ (triv_inv (a₁ y))) fun U _ k => ?_
  simp [Fin.prod_univ_four, Fin.prod_univ_three, fourPts, -Over.comp_left, Fintype.prod_sum_type]

end Cube

theorem biadditive_of_triv_axes :
    Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → ∀ (Pb : LB (G2 A).left), Pb.IsLB → (∃ t : (Pb.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Pb.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen := by
  intro hG S A _ _ H₀ hA hH hamp Pb hP h₁ h₂ T x x' y
  constructor
  · have := triv_add (𝟙 (A ⊗ A)) hG hA hH hamp hP (by rw [Category.comp_id]; exact h₁)
      (by rw [Category.comp_id]; exact h₂) x x' y
    simp only [Category.comp_id] at this
    exact this
  · have sw : ∀ {T : Over S} (a b : T ⟶ A), lift a b ≫ lift (snd A A) (fst A A) = lift b a := fun a b => by
      rw [comp_lift, lift_snd, lift_fst]
    have := triv_add (lift (snd A A) (fst A A)) hG hA hH hamp hP (by rw [sw]; exact h₂)
      (by rw [sw]; exact h₁) x x' y
    simp only [sw] at this
    exact this

end GlobalTheory.Biadditive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.TripleGlueMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nonempty_cast {A B : Scheme.{0}} {t : SAB H A} {t' : SAB H B} {f g : A ⟶ B} (h : f = g)
    (m : SABMap t t' f) : Nonempty (SABMap t t' g) := by
  subst h
  exact ⟨m⟩

theorem exists_transport {A B : Scheme.{0}} (e : A ≅ B) (t : SAB H A) :
    ∃ t' : SAB H B, Nonempty (SABMap t' t e.inv) ∧ Nonempty (SABMap t t' e.hom) := by
  have hp := sabPull Out.CubePf.cubePull e.inv t
  have m := hp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  obtain ⟨i, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨i'⟩ := nonempty_cast (by simp) i (g := e.hom ≫ e.inv)
  obtain ⟨k, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m i'
  exact ⟨_, ⟨m⟩, ⟨k⟩⟩

theorem mem_genericPoints_iso {A B : Scheme.{0}} (e : A ≅ B) (x : A) (hx : e.hom x ∈ genericPoints B) :
    x ∈ genericPoints A := by
  have hx' : closure {Scheme.homeoOfIso e x} ∈ irreducibleComponents B := by
    rw [Scheme.coe_homeoOfIso]
    exact hx
  have key := preimage_mem_irreducibleComponents hx' (Scheme.homeoOfIso e).isOpenEmbedding
    ⟨Scheme.homeoOfIso e x, subset_closure rfl, x, rfl⟩
  rw [(Scheme.homeoOfIso e).preimage_closure, ← Set.image_singleton,
    (Scheme.homeoOfIso e).injective.preimage_image] at key
  exact key

theorem generic_transport {A B : Scheme.{0}} (e : A ≅ B) {t : SAB H A} {t' : SAB H B} (m : SABMap t' t e.inv)
    (h : IsReduced A ∧ genericPoints A ⊆ abLocus t.G) : IsReduced B ∧ genericPoints B ⊆ abLocus t'.G := by
  obtain ⟨hr, hg⟩ := h
  refine ⟨@isReduced_of_isOpenImmersion _ _ e.inv _ hr, ?_⟩
  intro y hy
  have hy' : e.inv y ∈ genericPoints A := by
    apply mem_genericPoints_iso e
    have hyy : e.hom (e.inv y) = y := (Scheme.homeoOfIso e).apply_symm_apply y
    rw [hyy]
    exact hy
  have ha := hg hy'
  simp only [abLocus, Set.mem_setOf_eq] at ha ⊢
  intro K _ _ u hu
  have hp : IsProper (pullback.snd t.G.hom (u ≫ e.inv)) := by
    apply ha K (u ≫ e.inv)
    obtain ⟨p, rfl⟩ := hu
    exact ⟨p, rfl⟩
  have sq := (IsPullback.of_hasPullback t'.G.hom u).paste_horiz m.cart.1
  rw [← sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback t.G.hom (u ≫ e.inv))]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mpr hp

theorem exists_sab_glue_of_isPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ X₁ X₂ : Scheme.{0}) (ψ₁ : X₁ ⟶ X) (ψ₂ : X₂ ⟶ X) (φ₁ : X₀ ⟶ X₁) (φ₂ : X₀ ⟶ X₂) (t₀ : SAB H X₀) (t₁ : SAB H X₁) (t₂ : SAB H X₂) (_ : SABMap t₀ t₁ φ₁) (_ : SABMap t₀ t₂ φ₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → (∀ x : X, x ∈ Set.range ψ₁ ∨ x ∈ Set.range ψ₂) → (IsReduced X₁ ∧ genericPoints X₁ ⊆ abLocus t₁.G) → (IsReduced X₂ ∧ genericPoints X₂ ⊆ abLocus t₂.G) → ∃ t : SAB H X, Nonempty (SABMap t₁ t ψ₁) ∧ Nonempty (SABMap t₂ t ψ₂) := by
  intro E _ _ _ H X X₀ X₁ X₂ ψ₁ ψ₂ φ₁ φ₂ t₀ t₁ t₂ m₁ m₂ h₁ h₂ sq hcov g₁ g₂
  obtain ⟨t₁', ⟨a₁⟩, ⟨b₁⟩⟩ := exists_transport ψ₁.isoOpensRange t₁
  obtain ⟨t₂', ⟨a₂⟩, ⟨b₂⟩⟩ := exists_transport ψ₂.isoOpensRange t₂
  have G₁ := generic_transport ψ₁.isoOpensRange a₁ g₁
  have G₂ := generic_transport ψ₂.isoOpensRange a₂ g₂
  have hr : Set.range (pullback.fst ψ₁ ψ₂ ≫ ψ₁) = Set.range (ψ₁.opensRange ⊓ ψ₂.opensRange).ι := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι]
    simp
  let e₀ : X₀ ≅ (ψ₁.opensRange ⊓ ψ₂.opensRange).toScheme :=
    sq.isoPullback ≪≫ IsOpenImmersion.isoOfRangeEq _ _ hr
  have he₀ : e₀.hom ≫ (ψ₁.opensRange ⊓ ψ₂.opensRange).ι = φ₁ ≫ ψ₁ := by
    simp [e₀]
  obtain ⟨t₀', ⟨a₀⟩, -⟩ := exists_transport e₀ t₀
  obtain ⟨c₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ a₀
  obtain ⟨d₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₁ c₁
  obtain ⟨c₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₂ a₀
  obtain ⟨d₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₂ c₂
  have k₁ : (e₀.inv ≫ φ₁) ≫ ψ₁.isoOpensRange.hom =
      X.homOfLE (inf_le_left : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₁.opensRange) := by
    rw [← cancel_mono ψ₁.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← he₀, Iso.inv_hom_id_assoc]
  have k₂ : (e₀.inv ≫ φ₂) ≫ ψ₂.isoOpensRange.hom =
      X.homOfLE (inf_le_right : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₂.opensRange) := by
    rw [← cancel_mono ψ₂.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← sq.w, ← he₀, Iso.inv_hom_id_assoc]
  obtain ⟨M₁⟩ := nonempty_cast k₁ d₁
  obtain ⟨M₂⟩ := nonempty_cast k₂ d₂
  have hUV : ψ₁.opensRange ⊔ ψ₂.opensRange = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union,
      Scheme.Hom.coe_opensRange, Set.mem_univ, iff_true]
    exact hcov x
  obtain ⟨t, n₁, n₂, -⟩ := GlobalTheory.TripleGlue.exists_sab_glue E H X _ _ t₁' t₂' t₀' M₁ M₂ hUV G₁ G₂
  obtain ⟨p₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₁ b₁
  obtain ⟨p₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₂ b₂
  exact ⟨t, nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₁) p₁,
    nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₂) p₂⟩

end GlobalTheory.TripleGlueMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelRaises
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LocalModelExists

theorem exists_model_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (b : RZ H (n * l₀.M) 1 →+* O), 0 < n → l₀.Dvd l → IsDedFrac β → IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp β) b → ∃ Y : Model (Xo l) c β, Raises B Y := by
  intro L1 L2 L3 E _ _ _ H D Xo n N T hN l₀ l B c O _ β b hn hd hβ hb
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ _ (Xo l).s
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l).univ
  obtain ⟨k, r, ν, hr, hk, hlev, hfin, -, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L1 L2 L3 E H D Xo hN l₀ l c o m0 hd
  have hpos : 0 < n * l₀.M := Nat.mul_pos hn (by have := l₀.three_le; omega)
  have hB : IsDedFrac B.β := by
    have aux : ∀ a : ℕ, l₀.A = a → a = 1 → ∀ β₀ : RZ H (n * l₀.M) a →+* KA l₀,
        IsInc (RZ H (n * l₀.M) a).subtype (KA l₀).val.toRingHom β₀ → IsDedFrac β₀ := by
      intro a ha h1
      subst ha
      exact (_root_.GlobalTheory.BaseRing.isDedFrac_RZ E H l₀ (n * l₀.M) 0 hpos (by simp [h1])).2.2
    exact aux 1 B.A_one rfl B.β B.β_inc
  have hcomp : β.comp b = k.comp B.β := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hsm : Smooth (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.Models.Cpt.exists_above E H _ _ _ (Xo l₀).s (Xo l₀).univ.t B.β _ _ _
    (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) o.t β B.C b k r hr ν hB hβ hcomp
    hnorm hfin
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    b, r, ν, hb, hlev, hC⟩

end GlobalTheory.LocalModelExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTypeOfIsQProjOverAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem finiteType_of_isQProjOver_affineOpen {o : Type} [CommRing o] {X : Scheme.{0}} {s : X ⟶ Sp o}
    (hs : IsQProjOver s) (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X) [IsOpenImmersion x]
    (hx : x ≫ s = spMap (algebraMap o R)) : Algebra.FiniteType o R := by
  obtain ⟨N, i, hi, -, rfl⟩ := hs
  have := isProper_str o N
  have h : LocallyOfFiniteType (spMap (algebraMap o R)) := by
    rw [← hx]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  exact RingHom.finiteType_algebraMap.mp h

theorem ThetaFam.smooth_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → (∀ (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  intro h1 h2 g n N' J Mat κ w w' o _ b em C d F hb hC ht
  have : IsDedekindDomain o := hb.1
  refine _root_.GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine o F.MM F.s d fun R _ _ x hx hxs => ?_
  exact _root_.GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le o em R d hb.2.2 (finiteType_of_isQProjOver_affineOpen F.qproj R x hxs)
    (_root_.GlobalTheory.ZM.GenericTrdeg.exists_algebraicIndependent h1 h2 n g N' J Mat κ w w' o b em C d F hb hC R x hx hxs)
    (fun he => ht R x hx hxs he)

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasTransitionCompatibleFramesOfNoCompleteDVRPoinStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTransitionCompatibleFrames_of_no_completeDVR_points : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ), 1 ≤ n' → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z)) → HasFrames G L N A n r s → HasFrames G L N A n' r s := by
  first | exact @GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty | exact GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty | (intros; apply GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty <;> assumption)
end

