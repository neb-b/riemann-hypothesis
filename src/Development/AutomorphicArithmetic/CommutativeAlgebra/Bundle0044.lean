module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteDimensionalHodgeCohomologyOfSmoothProj
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

set_option maxSynthPendingDepth 1

noncomputable section

private theorem smulHom_eq {X : Scheme.{0}} (F : X.Modules) (r : Γ(X, ⊤)) :
    GlobalTheory.smulHom F r = GroundTheory.Arith.SchemeCoh.smulHom F r := by
  ext U x
  rfl

private def cohEquiv {X : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] (F : X.Modules)
    (n : ℕ) : coh F n ≃ₗ[R] Sheaf.H.{0} (GroundTheory.Arith.SchemeCoh.modulesAb F) n :=
  { (coh.toH F n) with
    map_smul' := fun r x => by
      have h := coh.toH_map R (smulHom F (algebraMap R Γ(X, ⊤) r)) n x
      rw [← cohOn.smul_eq_map] at h
      refine h.trans ?_
      rw [smulHom_eq]
      rfl }

private theorem finiteType_sec {Z : Scheme.{0}} (s : Z ⟶ Sp ℂ) [LocallyOfFiniteType s]
    {U : Z.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℂ (CechDR.Sec s U) := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : (CechDR.secMap s U).hom.FiniteType := by
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ U le_top).hom.FiniteType
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp h (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  exact h2

private theorem isCoherent_Omega {Z : Scheme.{0}} (s : Z ⟶ Sp ℂ) [LocallyOfFiniteType s] (a : ℕ) :
    GroundTheory.Arith.SchemeCoh.IsCoherent (Omega s a) := by
  refine ⟨inferInstance, fun U hU => ?_⟩
  haveI := finiteType_sec s hU
  have h : Module.Finite (CechDR.Sec s U) (CechDR.OmU s U a) := inferInstance
  have h' : Module.Finite (CechDR.Sec s U) Γ(Omega s a, U) := Module.Finite.equiv (toOmEquiv s a hU)
  exact h'

theorem UpperTheory.finiteDimensional_hodgeCohomology_of_smooth_proj :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s → ∀ a b : ℕ, FiniteDimensional ℂ (hodgeH s a b) := by
  intro Z _ s d _ hp a b
  obtain ⟨N, i, hi, his⟩ := hp
  haveI : IsProper (PSpace.str ℂ N) :=
    inferInstanceAs (IsProper (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase ℂ N))
  haveI : IsProper s := by rw [← his]; infer_instance
  letI : Z.Over (Spec (.of ℂ)) := ⟨s⟩
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := inferInstanceAs (IsProper s)
  have hc : GroundTheory.Arith.SchemeCoh.IsCoherent (Omega s a) := isCoherent_Omega s a
  have h := @GroundTheory.Arith.SchemeCoh.finite_H_of_isProper ℂ _ _ Z _ _ (Omega s a) hc b
  letI := algΓ s
  have h' : Module.Finite ℂ (coh (Omega s a) b) := by
    haveI : Module.Finite ℂ (Sheaf.H.{0} (GroundTheory.Arith.SchemeCoh.modulesAb (Omega s a)) b) := h
    exact Module.Finite.equiv (cohEquiv ℂ (Omega s a) b).symm
  exact h'

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IteratedFiberPowerZeroIsIsoAndSuccIsPullback
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem UpperTheory.power_zero_isIso {S : Scheme.{0}} (A : Over S) : IsIso (GlobalTheory.KS.pow A 0).hom := by
  let g : Over.mk (𝟙 S) ⟶ GlobalTheory.KS.pow A 0 := Pi.lift fun i => Fin.elim0 i
  let f : GlobalTheory.KS.pow A 0 ⟶ Over.mk (𝟙 S) := Over.homMk (GlobalTheory.KS.pow A 0).hom
  have hfg : f ≫ g = 𝟙 _ := Pi.hom_ext _ _ fun i => Fin.elim0 i
  refine ⟨⟨g.left, ?_, ?_⟩⟩
  · have h := congrArg (fun x => x.left) hfg
    simpa [f] using h
  · simpa using Over.w g

private theorem UpperTheory.power_succ_lift {S : Scheme.{0}} (A : Over S) (m : ℕ) (T : Over S)
    (a : T ⟶ GlobalTheory.KS.pow A m) (b : T ⟶ A) :
    ∃ l : T ⟶ GlobalTheory.KS.pow A (m + 1),
      l ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc) = a ∧
      l ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m) = b := by
  refine ⟨Pi.lift fun j => Fin.lastCases (motive := fun _ => T ⟶ A) b
    (fun i => a ≫ Pi.π (fun _ : Fin m => A) i) j, ?_, ?_⟩
  · refine Pi.hom_ext _ _ fun i => ?_
    simp
  · simp

private theorem UpperTheory.power_succ_lift_unique {S : Scheme.{0}} (A : Over S) (m : ℕ) (T : Over S)
    (l l' : T ⟶ GlobalTheory.KS.pow A (m + 1))
    (h₁ : l ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc) =
      l' ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc))
    (h₂ : l ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m) =
      l' ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m)) : l = l' := by
  refine Pi.hom_ext _ _ fun j => ?_
  induction j using Fin.lastCases with
  | last => exact h₂
  | cast i => simpa using congrArg (· ≫ Pi.π (fun _ : Fin m => A) i) h₁

theorem UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback :
    ∀ {S : Scheme.{0}} (A : Over S), IsIso (GlobalTheory.KS.pow A 0).hom ∧ ∀ m : ℕ, ∃ (u : (GlobalTheory.KS.pow A (m + 1)).left ⟶ (GlobalTheory.KS.pow A m).left) (v : (GlobalTheory.KS.pow A (m + 1)).left ⟶ A.left), IsPullback u v (GlobalTheory.KS.pow A m).hom A.hom ∧ u ≫ (GlobalTheory.KS.pow A m).hom = (GlobalTheory.KS.pow A (m + 1)).hom := by
  intro S A
  refine ⟨UpperTheory.power_zero_isIso A, fun m => ?_⟩
  let P : GlobalTheory.KS.pow A (m + 1) ⟶ GlobalTheory.KS.pow A m :=
    Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc
  let Q : GlobalTheory.KS.pow A (m + 1) ⟶ A := Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m)
  have w : P.left ≫ (GlobalTheory.KS.pow A m).hom = Q.left ≫ A.hom := (Over.w P).trans (Over.w Q).symm
  have hL := fun s : PullbackCone (GlobalTheory.KS.pow A m).hom A.hom =>
    UpperTheory.power_succ_lift A m (Over.mk (s.snd ≫ A.hom)) (Over.homMk s.fst s.condition)
      (Over.homMk s.snd rfl)
  refine ⟨P.left, Q.left, IsPullback.of_isLimit' ⟨w⟩
    (PullbackCone.IsLimit.mk w (fun s => (hL s).choose.left) ?_ ?_ ?_), Over.w P⟩
  · intro s
    rw [← Over.comp_left, (hL s).choose_spec.1]
    rfl
  · intro s
    rw [← Over.comp_left, (hL s).choose_spec.2]
    rfl
  · intro s n hn1 hn2
    have hn : n ≫ (GlobalTheory.KS.pow A (m + 1)).hom = s.snd ≫ A.hom := by
      rw [← Over.w Q, ← Category.assoc, hn2]
    let N : Over.mk (s.snd ≫ A.hom) ⟶ GlobalTheory.KS.pow A (m + 1) := Over.homMk n hn
    have h1 : N ≫ P = (hL s).choose ≫ P := by
      rw [(hL s).choose_spec.1]
      apply (Over.forget S).map_injective
      simpa [N] using hn1
    have h2 : N ≫ Q = (hL s).choose ≫ Q := by
      rw [(hL s).choose_spec.2]
      apply (Over.forget S).map_injective
      simpa [N] using hn2
    exact congrArg (fun x => x.left) (UpperTheory.power_succ_lift_unique A m _ N _ h1 h2)
end

