module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusImageFactorQuotientGoodOpen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOfUnitAt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.TwistNoBasePoint

section
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.NoBasePoint

theorem exists_sec_of_unitAt {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt L φ ε y) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), y ∈ nonzeroLocus s := by
  obtain ⟨s, hs⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
  exact ⟨s, (mem_nonzeroLocus s y).2 ⟨fun i => J (𝟙 _ ≫ φ i), Good.mem hJ φ (𝟙 _), hs J hJ⟩⟩

theorem unitAt_twist (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K))
    (x : baseOver (Sp K) ⟶ P.A) (p : (baseOver (Sp K)).left) (m : ℕ) (b : baseOver (Sp K) ⟶ P.A) :
    UnitAt P.L ![(translPt P.A b).left, (snd (baseOver (Sp K)) P.A).left] ![1, (m : ℤ) + 1]
      ((ptSecT P.A x).left p) := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := geometricallyIntegral_of_smooth _
  let t : Spec (CommRingCat.of K) ⟶ Sp K := 𝟙 _
  have : IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 : Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L (1 : ℕ) (Over.mk t)) = 1 ^ P.g :=
    hL.globalSectionsRank K P 1 le_rfl
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let y : (Over.mk t ⊗ P.A).left := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    unitAt_transl P.isLB θ k a y (by
      rw [← ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hL.square _ P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  exact main m b

end

theorem exists_sec_twist :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ), 4 ≤ n → ∀ c x : Out.baseOver (Sp k) ⟶ P.A, ∃ s : LB.Sec (Out.twistLB P.A P.L n c), ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s) := by
  intro hL _ k _ _ P n hn c x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let p : (Out.baseOver (Sp k)).left := IsLocalRing.closedPoint k
  have h : H1.SquareUnits.UnitAt P.L (K := Fin 2)
      ![(snd (Out.baseOver (Sp k)) P.A).left, (Out.translPt P.A c).left] ![((m + 2 : ℕ) : ℤ) - 1, 1]
      ((Out.ptSecT P.A x).left p) := by
    refine H1.SquareUnits.UnitAt.congr P.isLB (H1.SquareUnits.formEq_of_add fun U _ hh => ?_) (unitAt_twist hL k P x p m c)
    simp [Fin.sum_univ_succ]
    module
  obtain ⟨s, hs⟩ := exists_sec_of_unitAt P.isLB h
  refine ⟨s, fun q _ => ?_⟩
  obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact hs

end GlobalTheory.TwistNoBasePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_resG_apply {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_secOn_glue {X : Scheme.{0}} (B : LB X) (V : X.Opens) {κ : Type} (T : κ → X.Opens)
    (hT : ∀ k, T k ≤ V) (hV : ∀ x ∈ V, ∃ k, x ∈ T k) (σ : ∀ k j, Γ(X, T k ⊓ B.U j))
    (hσ : ∀ k, σ k ∈ secOn B (T k))
    (hc : ∀ k k' j, resG X (inf_le_inf_right _ inf_le_left : (T k ⊓ T k') ⊓ B.U j ≤ T k ⊓ B.U j) (σ k j) =
      resG X (inf_le_inf_right _ inf_le_right : (T k ⊓ T k') ⊓ B.U j ≤ T k' ⊓ B.U j) (σ k' j)) :
    ∃ τ ∈ secOn B V, ∀ k j, resG X (inf_le_inf_right _ (hT k)) (τ j) = σ k j := by
  have H : ∀ j, ∃ τ : Γ(X, V ⊓ B.U j), ∀ k, resG X (inf_le_inf_right _ (hT k)) τ = σ k j := fun j => by
    obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' (fun k => T k ⊓ B.U j) (V ⊓ B.U j)
      (fun k => homOfLE (inf_le_inf_right _ (hT k)))
      (fun x hx => by
        obtain ⟨k, hk⟩ := hV x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hx.2⟩) (fun k => σ k j) (fun k k' => by
        have e : (T k ⊓ B.U j) ⊓ (T k' ⊓ B.U j) ≤ (T k ⊓ T k') ⊓ B.U j :=
          fun x hx => ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
        have := congrArg (resG X e) (hc k k' j)
        rw [resG_resG_apply, resG_resG_apply] at this
        exact this)
    exact ⟨g, hg⟩
  choose τ hτ using H
  refine ⟨τ, fun i j => ?_, fun k j => hτ j k⟩
  refine X.sheaf.eq_of_locally_eq' (fun k => T k ⊓ B.U i ⊓ B.U j) (V ⊓ B.U i ⊓ B.U j)
    (fun k => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hT k))))
    (fun x hx => by
      obtain ⟨k, hk⟩ := hV x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ⟨hk, hx.1.2⟩, hx.2⟩) _ _ fun k => ?_
  have h := hσ k i j
  rw [← hτ i k, ← hτ j k, resG_resG_apply, resG_resG_apply] at h
  change resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _ =
    resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _
  rw [map_mul, resG_resG_apply, resG_resG_apply, resG_resG_apply]
  exact h

theorem sum_mul_mem_secOn {X : Scheme.{0}} (B : LB X) (V : X.Opens) {I : Type} [Fintype I] (f : I → Γ(X, V))
    (σ : I → ∀ j, Γ(X, V ⊓ B.U j)) (hσ : ∀ i, σ i ∈ secOn B V) :
    (fun j => ∑ i, resG X inf_le_left (f i) * σ i j) ∈ secOn B V := fun j j' => by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.mul_sum, resG_resG_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hσ i j j', mul_left_comm]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem ZHPre.genVal_res (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V V' : Q.G.left.Opens} (e : V' ≤ V)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V' (fun j => resG _ (inf_le_inf_right _ e) (σ j)) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  rw [h K β g r jP jL h1 h2 h3 h4 (h5.trans e)]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (V' ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact (valR_res (g ≫ Q.φ) _ hU _).symm

theorem ZHPre.genVal_of_cover (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V : Q.G.left.Opens} {κ : Type}
    (T : κ → Q.G.left.Opens) (hT : ∀ a, T a ≤ V) (hV : ∀ x ∈ V, ∃ a, x ∈ T a)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ a, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c (T a)
      (fun j => resG _ (inf_le_inf_right _ (hT a)) (σ j))) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  obtain ⟨a, ha⟩ := hV _ (h5 ⟨IsLocalRing.closedPoint K, rfl⟩)
  have h6 : Set.range (g ≫ Q.φ) ⊆ T a := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) w (IsLocalRing.closedPoint K)]
    exact ha
  rw [h a K β g r jP jL h1 h2 h3 h4 h6]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (T a ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h6 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact valR_res (g ≫ Q.φ) _ hU _

theorem ZHPre.genVal_sum (k : ℤ) {I J : Type} [Fintype I] [Fintype J]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : J → I → Ω) (W : M.Z.Opens)
    (hW : (W : Set M.Z).Nonempty) (f : J → Γ(M.Z, W))
    (σ : J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ i, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (c i) _ (σ i)) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (fun l => ∑ i, valF M.pt W (f i) * c i l) _
      (fun j => ∑ i, resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i)) * σ i j) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  have hV : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W) := fun w _ => h5 ⟨w, rfl⟩
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [Category.assoc, Q.cart.1.w, ← h1]
    rfl
  have hf : ∀ i, (valMap (g ≫ Q.φ) _ hU).hom (resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i))) =
      β (valF M.pt W (f i)) := fun i => by
    rw [← valR_eq, valR_res _ _ hU, valR_appLE _ _ _ hV, hp, valR_spMap_comp β M.pt W (M.top_le_preimage_pt hW),
      valF_eq_valR]
  have hi := fun i => h i K β g r jP jL h1 h2 h3 h4 h5
  set_option synthInstance.maxHeartbeats 100000 in
    rw [valF_eq_valR (g ≫ Q.φ), valR_eq _ _ hU, map_sum, Finset.mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_mul, hf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, ← valR_eq, ← valF_eq_valR, ← hi i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _

end GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_secOn_genVal_of_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  intro o Ω _ _ _ S ρ M U₀ EE Q hU hb W x₀ v hv
  have H : ∀ z : W, ∃ T : M.Z.Opens, z.1 ∈ T ∧ T ≤ W ∧
      ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ T),
        GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
    rintro ⟨z, hz⟩
    obtain ⟨U, b, hzU, -, hE⟩ := EE.loc z
    have h1 := (hv z hz).2
    rw [hE z hzU] at h1
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun i l => b i l)).1 h1
    let T : M.Z.Opens := W ⊓ U ⊓ ⟨⋂ i, {z' | (a i : Ω) ∈ M.O z'},
      isOpen_iInter_of_finite fun i => M.isOpen_setOf_mem_O _⟩
    have hzT : z ∈ T := ⟨⟨hz, hzU⟩, Set.mem_iInter.2 fun i => (a i).2⟩
    have hne : (T : Set M.Z).Nonempty := ⟨z, hzT⟩
    have h2 : ∀ i, ∃ f : Γ(M.Z, T), valF M.pt T f = a i := fun i =>
      (RatModel.mem_ringOn_iff_exists hne).1 (RatModel.mem_ringOn.2 fun z' hz' => Set.mem_iInter.1 hz'.2 i)
    choose f hf using h2
    obtain ⟨σ, hσ⟩ := hb T x₀ b fun z' hz' => ⟨(hv z' hz'.1.1).1, hE z' hz'.1.2⟩
    refine ⟨T, hzT, inf_le_left.trans inf_le_left, _,
      sum_mul_mem_secOn _ _ (fun i => (Q.G.hom.appLE T _ le_rfl).hom (f i)) σ fun i => (hσ i).1, ?_⟩
    have h3 := Q.genVal_sum S.N ρ.s (fun i l => b i l / S.th x₀) T hne f σ fun i => (hσ i).2
    have h4 : (fun l => ∑ i, valF M.pt T (f i) * (b i l / S.th x₀)) = fun l => v l / S.th x₀ := by
      funext l
      rw [← ha, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf, ← mul_div_assoc]
      rfl
    rw [h4] at h3
    exact h3
  choose T hz hT σ hσ hg using H
  have hle : ∀ z, Q.G.hom ⁻¹ᵁ T z ≤ Q.G.hom ⁻¹ᵁ W := fun z x hx => hT z hx
  have hcov : ∀ x ∈ Q.G.hom ⁻¹ᵁ W, ∃ z, x ∈ Q.G.hom ⁻¹ᵁ T z := fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩
  obtain ⟨τ, hτ, hr⟩ := exists_secOn_glue _ (Q.G.hom ⁻¹ᵁ W) (fun z => Q.G.hom ⁻¹ᵁ T z) hle hcov σ hσ
    fun z z' j => congrFun (Q.eq_of_genVal hU _ _ _ _ _ _ (Q.genVal_res _ _ _ inf_le_left _ (hg z))
      (Q.genVal_res _ _ _ inf_le_right _ (hg z'))) j
  refine ⟨τ, hτ, Q.genVal_of_cover _ _ _ _ hle hcov τ fun z => ?_⟩
  have h5 := hg z
  rw [← funext (hr z)] at h5
  exact h5

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.ClassWeight

section General
open ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.ThetaPtMove
variable {B B' : Scheme.{0}} {G : Over B} [GrpObj G] {A : Over B'} [GrpObj A]
  {f : B' ⟶ B} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over B'} {T₀ : Over B} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem sv_sum_smul {L : LB A.left} {k : ℤ} {I : Type} (F : Finset I) (c : I → Γ(T.left, ⊤))
    (v : I → SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    ThetaAct.sv (∑ l ∈ F, c l • v l) r z J =
      ∑ l ∈ F, gs (r ≫ (fst T A).left) z ⊤ (c l) * ThetaAct.sv (v l) r z J := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have h := ThetaAct.sv_add (0 : SecM A L k T) 0 r z hJ
    rw [add_zero] at h
    exact left_eq_add.1 h
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ, ih]

theorem secRel_sum {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T₀.left, ⊤))
    {t : I → LB.Sec (LPow A L₁ k T)} {s : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (s l)) :
    SecRel hp τ hτ w (SecM.toSec A (∑ l, τ.appTop.hom (c l) • SecM.ofSec A (t l)))
      (SecM.toSec G (∑ l, c l • SecM.ofSec G (s l))) := by
  intro Z r z J J' hJ hJ'
  refine (sv_sum_smul Finset.univ c (fun l => SecM.ofSec G (s l)) (r ≫ psi hp τ hτ) z hJ).trans (Eq.trans ?_
    (congrArg (_ * ·) (sv_sum_smul Finset.univ (fun l => τ.appTop.hom (c l)) (fun l => SecM.ofSec A (t l))
      r z hJ').symm))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, Category.assoc, psi_fst', ← Category.assoc]
  exact congrArg₂ (· * ·) (gs_pull _ τ z ⊤ trivial (c l)).symm (h l Z r z J J' hJ hJ')

theorem isActOf_unique {L : LB A.left} (hL : L.IsLB) {k : ℤ} {θ : ThetaGrp A L k T}
    {s s₁ s₂ : LB.Sec (LPow A L k T)} (h₁ : IsActOf A L k θ s s₁) (h₂ : IsActOf A L k θ s s₂) :
    SecM.ofSec A s₁ = SecM.ofSec A s₂ :=
  ThetaAct.sv_ext hL fun y J hJ =>
    ((ThetaAct.isActOf_iff hL θ s s₁).1 h₁ y J hJ).trans ((ThetaAct.isActOf_iff hL θ s s₂).1 h₂ y J hJ).symm

theorem exists_isActOf' {L : LB A.left} (hL : L.IsLB) {k : ℤ} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' := by
  obtain ⟨v, hv⟩ := ThetaAct.exists_act hL θ (SecM.ofSec A s)
  exact ⟨SecM.toSec A v, (ThetaAct.isActOf_iff hL θ _ _).2 fun y J hJ => hv _ _ y J hJ⟩

theorem ofSec_eq_sum {L : LB A.left} {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T.left, ⊤))
    (s : I → LB.Sec (LPow A L k T)) (σ : LB.Sec (LPow A L k T))
    (h : ∀ j, σ.f j = ∑ l, liftFun A _ (c l) * (s l).f j) : σ = SecM.toSec A (∑ l, c l • SecM.ofSec A (s l)) := by
  have e : SecM.ofSec A σ = ∑ l, c l • SecM.ofSec A (s l) := by
    refine Subtype.ext (funext fun j => (h j).trans ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [← e]
  rfl

theorem symLift_act_move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ₀ : ThetaGrp G L₀ k T₀}
    (H₀ : SymLift G L₀ k n x₀ θ₀) {I : Type} [Fintype I] (c : I → I → Γ(T₀.left, ⊤)) (c' : I → I → Γ(T.left, ⊤))
    (hc : ∀ l i, τ.appTop.hom (c l i) = c' l i)
    {t : I → LB.Sec (LPow A L₁ k T)} {s : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (s l))
    (hs : ∀ i σ, IsActOf G L₀ k θ₀ (s i) σ → ∀ j, σ.f j = ∑ l, liftFun G _ (c l i) * (s l).f j) :
    ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧ ∀ i t', IsActOf A L₁ k θ (t i) t' →
      SecM.ofSec A t' = ∑ l, c' l i • SecM.ofSec A (t l) := by
  obtain ⟨θ, hθ, H⟩ := symLift_move hp τ hτ hw hL₀ hL₁ hx hn H₀
  refine ⟨θ, hθ, fun i t' ht' => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isActOf' hL₀ θ₀ (s i)
  have e := ofSec_eq_sum _ _ σ (hs i σ hσ)
  have hr := secRel_sum hp τ hτ (fun l => c l i) h
  rw [← e] at hr
  refine (isActOf_unique hL₁ ht' (H _ _ _ _ (h i) hr hσ)).trans ?_
  simp only [hc]
  rfl

end General

theorem appTop_fn {R : Type} [CommRing R] (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F]
    [Algebra (FractionRing V) F] (y : R →+* F) (c : R) :
    (show (TFK (R := V) F).left ⟶ (baseOver (Sp R)).left from spMap y).appTop.hom (fn c) = kf V F (y c) :=
  (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem exists_symLift_act : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a)).left → x ^ S.N = 1 → ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)), SymLift u.A.A u.A.L S.N S.N x θ ∧ ∀ i t', IsActOf u.A.A u.A.L S.N θ (t i) t' → SecM.ofSec u.A.A t' = ∑ l, kf u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ a l i))) • SecM.ofSec u.A.A (t l) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u w hw t ht a x hx hn
  have := u.A.isAb.comm
  exact symLift_act_move u.cart (T := TFK (R := u.V) (PadicAlgCl p))
    (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) hw ρ.P.isLB u.A.isLB hx.symm hn (ρ.U_sym a)
    (fun l i => fn (algebraMap o S.R (S.ρ a l i))) _ (fun l i => appTop_fn u.V (PadicAlgCl p) y₀ _) ht (ρ.U_act a)

end GlobalTheory.ZH.ClassWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusQuotientNoCocharacter
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS.MaxTorus
open GlobalTheory.SplitTorus

theorem surjective_of_mono {S : Scheme.{0}} [Nonempty S] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (φ : Y →+ X) [Mono (torusMap S φ)] : Function.Surjective φ := by
  let π : X →+ X ⧸ φ.range := QuotientAddGroup.mk' _
  have h : π.comp φ = (0 : X →+ X ⧸ φ.range).comp φ := by
    ext y
    simp [π]
  have h' : π = 0 := by
    apply torusMap_injective (S := S)
    rw [← cancel_mono (torusMap S φ), ← torusMap_comp, ← torusMap_comp, h]
  intro x
  have : π x = 0 := by rw [h']; rfl
  exact (QuotientAddGroup.eq_zero_iff x).1 this

theorem injective_of_surjective {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (φ : Y →+ X) (h : Function.Surjective φ) (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) :
    Function.Injective φ := by
  have h1 : Module.finrank ℤ X ≤ Module.finrank ℤ Y :=
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toIntLinearMap) h
  let e : Y ≃ₗ[ℤ] X := LinearEquiv.ofFinrankEq _ _ (le_antisymm hr h1)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap φ.toIntLinearMap e.injective h

theorem exists_inv {S : Scheme.{0}} [ConnectedSpace S] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (σ : splitTorus S X ⟶ splitTorus S Y) [IsMonHom σ] [Mono σ]
    (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) : ∃ τ, τ ≫ σ = 𝟙 _ := by
  obtain ⟨φ, rfl⟩ := exists_eq_torusMap σ
  have hs := surjective_of_mono (S := S) φ
  let e : Y ≃+ X := AddEquiv.ofBijective φ ⟨injective_of_surjective φ hs hr, hs⟩
  refine ⟨torusMap S e.symm.toAddMonoidHom, ?_⟩
  rw [← torusMap_comp, ← torusMap_id]
  congr 1
  ext y
  exact e.symm_apply_apply y

theorem exists_quot_no_cocharacter : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → f = 1 := by
  classical
  intro k _ _ G _ hG
  obtain ⟨hc, hsm, hsep, hqc, hgc⟩ := id hG
  have : ConnectedSpace G.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  let P : ℕ → Prop := fun n => ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (i : splitTorus (Sp k) X ⟶ G), IsMonHom i ∧ (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) ∧ Module.finrank ℤ X = n
  have hb : ∀ n, P n → n ≤ g := by
    rintro _ ⟨X, _, _, _, i, hi, hV, rfl⟩
    obtain ⟨B, _, q, -, hd⟩ := _root_.GlobalTheory.TorusQuotientGlue.main k G hG X i hi hV
    obtain ⟨a, -, ha⟩ := hd g hg
    omega
  obtain ⟨n₀, h₀⟩ : ∃ n, P n := by
    obtain ⟨X', _, _, _, i', ρ, h1, -, -, -, hV⟩ := _root_.GlobalTheory.TorusImage.exists_factor_goodOpen k G hG PUnit 1
      (inferInstanceAs (IsMonHom (toUnit _ ≫ η[G])))
    exact ⟨_, X', _, ‹_›, ‹_›, i', h1, hV, rfl⟩
  obtain ⟨X, _, _, _, i, hi, hV, hn⟩ : P (Nat.findGreatest P g) := Nat.findGreatest_spec (hb _ h₀) h₀
  obtain ⟨B, _, q, hq, -⟩ := _root_.GlobalTheory.TorusQuotientGlue.main k G hG X i hi hV
  refine ⟨X, _, inferInstance, inferInstance, B, _, i, q, hq, fun f hf => ?_⟩
  obtain ⟨j, hj, rfl⟩ := _root_.GlobalTheory.SS.exists_lift_oneParameter k G hG X B i q hq f hf
  obtain ⟨-, hqm, -, -, -, hpb, -⟩ := hq
  have : Mono (η[B]) := ⟨fun a b _ => toUnit_unique a b⟩
  have : Mono i := hpb.mono_fst_of_mono
  let φ : splitTorus (Sp k) (X × ULift.{0} ℤ) ⟶ G :=
    (torusMap _ (AddMonoidHom.inl X (ULift.{0} ℤ)) ≫ i) * (torusMap _ (AddMonoidHom.inr X (ULift.{0} ℤ)) ≫ j)
  obtain ⟨X', _, _, _, i', ρ, h1, h2, -, h3, hV'⟩ := _root_.GlobalTheory.TorusImage.exists_factor_goodOpen k G hG (X × ULift.{0} ℤ) φ
    (by simp only [φ]; rw [Hom.mul_def]; infer_instance)
  have hr : Module.finrank ℤ X' ≤ Module.finrank ℤ X := by
    have hP : P (Module.finrank ℤ X') := ⟨X', _, ‹_›, ‹_›, i', h1, hV', rfl⟩
    rw [hn]
    exact Nat.le_findGreatest (hb _ hP) hP
  have e1 : torusMap _ (AddMonoidHom.fst X (ULift.{0} ℤ)) ≫ φ = i := by
    simp only [φ, MonObj.comp_mul, ← Category.assoc, ← torusMap_comp, AddMonoidHom.fst_comp_inl,
      AddMonoidHom.fst_comp_inr, torusMap_id, torusMap_zero, Category.id_comp, MonObj.one_comp, _root_.mul_one]
  have e2 : torusMap _ (AddMonoidHom.snd X (ULift.{0} ℤ)) ≫ φ = j := by
    simp only [φ, MonObj.comp_mul, ← Category.assoc, ← torusMap_comp, AddMonoidHom.snd_comp_inl,
      AddMonoidHom.snd_comp_inr, torusMap_id, torusMap_zero, Category.id_comp, MonObj.one_comp, _root_.one_mul]
  let σ := torusMap _ (AddMonoidHom.fst X (ULift.{0} ℤ)) ≫ ρ
  have e3 : σ ≫ i' = i := by rw [Category.assoc, h3, e1]
  have : Mono σ := mono_of_mono_fac e3
  obtain ⟨τ, hτ⟩ := exists_inv σ hr
  have e4 : i' = τ ≫ i := by rw [← e3, ← Category.assoc, hτ, Category.id_comp]
  have e5 : i ≫ q = 1 := hpb.w
  rw [← e2, ← h3, e4]
  simp only [Category.assoc, e5, MonObj.comp_one]

end GlobalTheory.SS.MaxTorus
end

