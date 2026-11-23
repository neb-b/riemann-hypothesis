module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleSpecialFibreExtendedPrincipalPolarisatio
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.SpecialAmple

theorem exists_sec_ne_zero {X X' : Scheme.{0}} (π : X' ⟶ X) [IsIso π] {M : LB X} {M' : LB X'} (hM : M.IsLB)
    (hM' : M'.IsLB) (h : LBIso M' (M.pull π)) (hs : ∃ s : LB.Sec M, ∃ j, s.f j ≠ 0) :
    ∃ s' : LB.Sec M', ∃ j, s'.f j ≠ 0 := by
  obtain ⟨s, j, hj⟩ := hs
  obtain ⟨w, hw⟩ := h
  obtain ⟨⟨s', hs', -⟩, -⟩ := SecPullIso.section_pull X X' π M M' w hM hM' hw s
  refine ⟨s', ?_⟩
  by_contra h
  push Not at h
  refine hj (fn_ext fun x hx => ?_)
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨k, hz⟩ := exists_chart hM' z
  have e := hs' z j k hx hz
  have e₀ : gs (𝟙 X') z (M'.U k) (s'.f k) = 0 :=
    (congrArg (gs (𝟙 X') z _) (h k)).trans (AmpleCrit.gs_zero' _ z _ hz)
  replace e := e.trans ((congrArg _ e₀).trans (mul_zero _))
  rw [gs_stalkMap π z _ hx] at e
  rw [AmpleCrit.gs_zero' (𝟙 X) (π z) _ hx]
  exact AmpleCrit.injective_stalkMap π z (e.trans (map_zero _).symm)

theorem exists_iso {X Y S T T' : Scheme.{0}} {φ : Y ⟶ X} {a : Y ⟶ T} {b : X ⟶ S} {f : T ⟶ S}
    (h : IsPullback φ a b f) (e : T' ⟶ T) [IsIso e] (g : T' ⟶ S) (he : e ≫ f = g) :
    ∃ u : pullback b g ⟶ Y, IsIso u ∧ u ≫ φ = pullback.fst b g := by
  subst he
  let u : pullback b (e ≫ f) ⟶ Y := h.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e)
    (by rw [Category.assoc]; exact pullback.condition)
  have hu : u ≫ φ = pullback.fst _ _ := h.lift_fst _ _ _
  have H : IsPullback u (pullback.snd b (e ≫ f)) a e :=
    IsPullback.of_right (by rw [hu]; exact IsPullback.of_hasPullback _ _) (h.lift_snd _ _ _) h
  exact ⟨u, H.isIso_fst_of_isIso, hu⟩

theorem exists_sec_pull {X Y Y' : Scheme.{0}} {N : LB X} (hN : N.IsLB) {a : Y ⟶ X} {b : Y' ⟶ X} (u : Y' ⟶ Y)
    [IsIso u] (hu : u ≫ a = b) (hs : ∃ s : LB.Sec (N.pull a), ∃ j, s.f j ≠ 0) :
    ∃ s : LB.Sec (N.pull b), ∃ j, s.f j ≠ 0 :=
  by
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  exact exists_sec_ne_zero u (pull_isLB hN a) (pull_isLB hN b)
    (LBIso.chartPull (chartPullSame N _ _ _ u fun _ => hu.symm) (Geo.Tor.chartPullPull _ u u rfl)
      ⟨_, CubePf.idIsoL_isGen (pull_isLB hN a)⟩) hs

theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) :
    LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem isIso_spMap {R R' : Type} [CommRing R] [CommRing R'] (e : R ≃+* R') : IsIso (spMap e.toRingHom) :=
  inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))

theorem exists_sec_pow {K : Type} [Field K] (P : PolAV (Sp K)) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ s : LB.Sec (AbLaw.pw P.L d), ∃ j, s.f j ≠ 0 := by
  obtain ⟨d, hd, n, a, ha, -⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ P.A P.L P.isLB).1 P.ample
  have hy : eSec P.A (IsLocalRing.closedPoint K) ∈ ⨆ i, nonzeroLocus (a i) := by rw [ha]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  refine ⟨d, hd, a i, j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem exists_prime (Ω : Type) [Field Ω] (m : ℕ) (hm : 0 < m) : ∃ n : ℕ, n.Prime ∧ (n : Ω) ≠ 0 ∧ ¬ n ∣ m := by
  obtain ⟨n, hn, hp⟩ := Nat.exists_infinite_primes (m + ringChar Ω + 1)
  refine ⟨n, hp, fun h => ?_, fun h => ?_⟩
  · rcases (Nat.dvd_prime hp).1 ((ringChar.spec Ω n).1 h) with e | e
    · exact CharP.ringChar_ne_one e
    · omega
  · have := Nat.le_of_dvd hm h
    omega

theorem relAmple_special_fibre : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple ((Over.pullback (spMap (IsLocalRing.residue V))).obj B) (M.L.L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue V)))) := by
  intro hL hL2 V K _ _ _ _ _ _ P B _ _ M φ hB hφ hiso hV
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  obtain ⟨d, hd, h₀⟩ := exists_sec_pow P
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  set_option backward.isDefEq.respectTransparency false in
  have isLB_pw : ∀ {X : Scheme.{0}} {H : LB X}, H.IsLB → (t : ℤ) → (AbLaw.pw H t).IsLB := by
    intro X H hH t
    refine { cover := hH.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simpa only [AbLaw.pw, one_zpow, ← map_zpow] using h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simpa only [AbLaw.pw, mul_zpow, ← map_zpow] using h
  have hN := isLB_pw M.L.isLB d

  have h₁ : ∃ s : LB.Sec ((AbLaw.pw M.L.L d).pull φ), ∃ j, s.f j ≠ 0 := by
    refine exists_sec_ne_zero (𝟙 _) (isLB_pw P.isLB d) (pull_isLB hN φ) ?_ h₀
    refine LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) ?_
    rw [AmpleCrit.pull_pw_eq]
    exact lbIso_pw hiso.symm d
  have h₂ : ∃ s : LB.Sec ((AbLaw.pw M.L.L d).pull (pullback.fst B.hom (jK V))), ∃ j, s.f j ≠ 0 := by
    let e : K ≃+* FractionRing V := (FractionRing.algEquiv V K).symm.toRingEquiv
    have := isIso_spMap e
    obtain ⟨u, _, hu⟩ := exists_iso hφ.1 (spMap e.toRingHom) (jK V) (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext v
      exact (FractionRing.algEquiv V K).symm.commutes v)
    exact exists_sec_pull hN u hu h₁

  have h₃ := GlobalTheory.SpreadSec.exists_ne_zero_closed_fibre V B _ hN h₂
  let r := spMap (IsLocalRing.residue V)
  have h₄ : ∃ s : LB.Sec ((AbLaw.pw M.L.L d).pull (pullback.fst B.hom r)), ∃ j, s.f j ≠ 0 := by
    let e : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) ≃+* IsLocalRing.ResidueField V :=
      Ideal.quotEquivOfEq (by rw [zero_add, pow_one])
    have := isIso_spMap e
    obtain ⟨u, _, hu⟩ := exists_iso
      (IsPullback.of_hasPullback B.hom (thick V (IsLocalRing.maximalIdeal V) 0)) (spMap e.toRingHom) r (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2)
    exact exists_sec_pull hN u hu h₃
  rw [AmpleCrit.pull_pw_eq] at h₄
  obtain ⟨s, hs⟩ := h₄

  let k := IsLocalRing.ResidueField V
  let B' : Over (Sp k) := (Over.pullback r).obj B
  have h : IsGrpPullback B' B r (pullback.fst B.hom r) := isGrpPullback_pullback B r
  have : IsCommMonObj B' := PolPull.isCommMonObj_of_isGrpPullback h
  have hB' : IsAbelianScheme B' := {
    comm := inferInstance
    smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hB.smooth
    proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hB.proper
    geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hB.geomConnected }
  obtain ⟨hL', hr, ⟨c', -⟩, -⟩ := CubePf.cubePull _ _ B B' (cubeMapOf h) M.L M.c
  let Ω := AlgebraicClosure k
  obtain ⟨n, hn, hnΩ, hnd⟩ := exists_prime Ω (2 * d) (by omega)
  refine AmpleCrit.relAmple_of_effective (_root_.GlobalTheory.UU.TorsionCount.card_torsion_points hL.globalFns hL.rigidity) k (Field.toIsField k) B' hB'
    ((cubeMapOf h).rigLB M.L hL' hr) c' d s hd hs Ω (spMap (algebraMap k Ω)) n hn hnΩ hnd fun x hxn htr => ?_
  let f : V →+* Ω := (algebraMap k Ω).comp (IsLocalRing.residue V)
  have hf : IsLocalHom f := RingHom.isLocalHom_comp _ _
  have key : ∀ p' : Sp Ω ⟶ Sp V, p' = spMap f →
      ∀ y : Over.mk p' ⟶ B, y ^ n = 1 → AbLaw.Triv (translDiff B M.L.L y) → y = 1 := by
    rintro _ rfl
    exact _root_.GlobalTheory.PrincipalModel.torsion_eq_one_of_triv hL hL2 V K P B M φ hB hφ hiso hV Ω f hf n hnΩ
  have e : pushHom h _ x = 1 := key _ (Spec.map_comp _ _).symm (pushHom h _ x)
    (by rw [← map_pow, hxn, map_one]) (AmpleCrit.triv_translDiff_push h M.L.isLB x htr)
  have e' := e.trans (map_one (pushHom h (Over.mk (spMap (algebraMap k Ω))))).symm
  exact Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e') (by rw [Over.w, Over.w]))

end GlobalTheory.SpecialAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem seesaw_reduced_of_dense :
    Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ σ : S ⟶ X, σ ≫ f = 𝟙 S → (∃ c : (N.pull σ).Gen, c.IsGen) → ∃ c : N.Gen, c.IsGen := by
  intro hG S₀ B _ M hB hM hA S X _ t π f N hp hN hd σ hσ hc
  exact GlobalTheory.exists_gen_of_local_of_section X S f σ N hN hσ
    (GlobalTheory.BaseChangeFns.app_surjective hG S₀ B hB S X t π f hp)
    (GlobalTheory.SeesawLocal.triv_locally_of_dense S₀ B M hB hM hA S X t π f N hp hN hd) hc

end GlobalTheory
end

