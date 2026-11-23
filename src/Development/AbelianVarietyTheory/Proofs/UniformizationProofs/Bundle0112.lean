module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecPullNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleCrit

variable {X X' : Scheme.{0}}

theorem pull_pw_eq (M : LB X) (π : X' ⟶ X) (t : ℤ) :
    (AbLaw.pw M t).pull π = AbLaw.pw (M.pull π) t := by
  refine congrArg (LB.mk (M.pull π).ι (M.pull π).U) ?_
  funext j j'
  change ∏ _k : PUnit, _ = (∏ _k : PUnit, _) ^ t
  refine Eq.trans ?_ (Finset.prod_zpow
    (G := Γ(X', LB.wchart M (fun _ : PUnit => π) j ⊓ LB.wchart M (fun _ : PUnit => π) j')ˣ) _ _ t)
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (zpow_one _).trans (Eq.trans ?_ (congrArg (· ^ t) (zpow_one _)).symm)
  exact (congrArg (res _) (map_zpow (pullU π _) (M.g (j k) (j' k)) t)).trans (map_zpow (res _) _ t)

theorem pw_pw_eq (M : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw M a) b = AbLaw.pw M (a * b) := by
  simp only [AbLaw.pw, zpow_mul]
  rfl

theorem injective_stalkMap (π : X' ⟶ X) [Flat π] (z : X') : Function.Injective (π.stalkMap z).hom := by
  algebraize [(π.stalkMap z).hom]
  have : Module.Flat (X.presheaf.stalk (π z)) (X'.presheaf.stalk z) := Flat.stalkMap π z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (π z)) (X'.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap z).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk (π z)) (B := X'.presheaf.stalk z)
  exact FaithfulSMul.algebraMap_injective _ _

theorem gs_zero' (π : X' ⟶ X) (z : X') (U : X.Opens) (h : π z ∈ U) : gs π z U 0 = 0 := by
  rw [gs_eq π z U h, map_zero, map_zero]

theorem exists_sec_pull_ne_zero (π : X' ⟶ X) [Flat π] [Surjective π] {M : LB X} (hM : M.IsLB)
    (s : LB.Sec M) (hs : ∃ j, s.f j ≠ 0) : ∃ s' : LB.Sec (M.pull π), ∃ j, s'.f j ≠ 0 := by
  have hM' := pull_isLB hM π
  obtain ⟨⟨s', hs', -⟩, -⟩ := SecPullIso.section_pull X X' π M (M.pull π) _ hM hM'
    (CubePf.idIsoL_isGen hM') s
  refine ⟨s', ?_⟩
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := hs
  refine hj (fn_ext fun x hx => ?_)
  obtain ⟨z, rfl⟩ := π.surjective x
  have hz : z ∈ (M.pull π).U (fun _ => j) := mem_pull.2 hx
  have e := hs' z j (fun _ => j) hx hz
  have e₀ : gs (𝟙 X') z ((M.pull π).U fun _ => j) (s'.f fun _ => j) = 0 :=
    (congrArg (gs (𝟙 X') z _) (h fun _ => j)).trans (gs_zero' _ z _ hz)
  replace e := e.trans ((congrArg _ e₀).trans (mul_zero _))
  rw [gs_stalkMap π z _ hx] at e
  rw [gs_zero' (𝟙 X) (π z) _ hx]
  exact injective_stalkMap π z (e.trans (map_zero _).symm)

def zeroSec (M : LB X) : LB.Sec M := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩

theorem exists_cover_of_pull {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat)
    [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R')) (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    [Surjective π] {M : LB X} (hM : M.IsLB) {n : ℕ} (t : Fin (n + 1) → LB.Sec (M.pull π))
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) :
    ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec M), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  choose m c u hu using fun i => FlatSec.exists_comb_of_flat R R' g hg X f X' π f' h M hM (t i)
  let I := Σ i, Fin (m i)
  let e : Option I ≃ Fin (Fintype.card I + 1) := Fintype.equivFinOfCardEq Fintype.card_option
  let v : Option I → LB.Sec M := fun o => o.elim (zeroSec M) fun q => u q.1 q.2
  refine ⟨Fintype.card I, fun a => v (e.symm a), top_le_iff.1 fun x _ => ?_⟩
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show z ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
  obtain ⟨J, hJ, hun⟩ := (mem_nonzeroLocus _ _).1 hi
  have hk : π z ∈ M.U (J PUnit.unit) := mem_pull.1 hJ
  have e₁ := hu i z (J PUnit.unit) hk
  have hun' := (congrArg IsUnit e₁).mp hun
  obtain ⟨a, -, ha⟩ := IsLocalRing.exists_of_isUnit_sum hun'
  have ha' := isUnit_of_mul_isUnit_right ha
  rw [gs_stalkMap π z _ hk] at ha'
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨e (some ⟨i, a⟩), ?_⟩
  beta_reduce
  rw [Equiv.symm_apply_apply]
  exact (mem_nonzeroLocus _ _).2 ⟨_, hk, (isUnit_map_iff (π.stalkMap z).hom _).1 ha'⟩

theorem exists_map {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB)
    {n : ℕ} (t : Fin (n + 1) → LB.Sec M) (ht : ⨆ i, nonzeroLocus (t i) = ⊤) :
    ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of R)) (H : LB P) (φ : X ⟶ P), IsProper q ∧ H.IsLB ∧
      φ ≫ q = f ∧ LBIso M (H.pull φ) ∧
      ∀ i, ∃ V : P.Opens, IsAffineOpen V ∧ nonzeroLocus (t i) = φ ⁻¹ᵁ V := by
  obtain ⟨P, q, H, s, hH, hva, heq⟩ := ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  obtain ⟨φ, w, hφ, hw, hs⟩ := exists_hom_of_veryAmpleBy R P q H n s hH hva X f M t hM ht (fun d F hF h0 k => by
    obtain ⟨a, ha⟩ := (heq d F hF).1 h0 0
    rw [Ideal.mem_bot] at ha
    have : F = 0 := ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1))) (R := R)).pow a).left
      (ha.trans (mul_zero _).symm)
    rw [this, map_zero])
  exact ⟨P, q, H, φ, isProper_of_isProjBy R P q ⟨H, hH, n, s, hva⟩, hH, hφ, ⟨w, hw⟩, fun i =>
    ⟨_, (hva.2 i).1, (SecPullIso.section_pull P X φ H M w hH hM hw (s i)).2 (t i) (hs i)⟩⟩

theorem triv_translDiff_push {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {L : LB A.left} (hL : L.IsLB) {T' : Over S'}
    (x : T' ⟶ A') (hx : Triv (translDiff A' (L.pull φ) x)) : Triv (translDiff A L (pushPt h.1.w x)) := by
  obtain ⟨c, hc⟩ := hx
  have hL' := pull_isLB hL φ
  let T : Over S := Over.mk (T'.hom ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ T'.hom)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ T'.hom) ≫ f :=
    pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ T' := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₂ : (lift a b).left ≫ (snd T' A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst T' A' ≫ x) * snd T' A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst T' A' ≫ x) * snd T' A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff _).1 (CubePf.idIsoL_isGen hL')) hL hL' c hc
  refine gen_chartPull (chartPullSame L _ _ _ (lift a b).left fun k => ?_) c₂ h₂
  fin_cases k
  exacts [k₃.symm, k₂.symm]

theorem relAmple_of_effective : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (R : Type) [CommRing R], IsField R → ∀ (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (k : ℕ) (s : LB.Sec (pw L.L k)), 1 ≤ k → (∃ j, s.f j ≠ 0) → ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ 2 * k → (∀ x : Over.mk p ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → RelAmple B L.L := by
  intro hcount R _ hR B _ _ hB L c k s hk hs K _ _ p n hn hnK hnk hx
  obtain ⟨g, rfl⟩ : ∃ g : R →+* K, p = Spec.map (CommRingCat.ofHom g) :=
    ⟨(Spec.preimage p).hom, (Spec.map_preimage p).symm⟩
  have hg : g.Flat := RingHom.Flat.of_isField hR g
  set p := Spec.map (CommRingCat.ofHom g) with hp
  have : Flat p := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hg
  have : Surjective p := ⟨fun y => by
    let := hR.toField
    have : Subsingleton (Spec (CommRingCat.of R)) := inferInstanceAs (Subsingleton (PrimeSpectrum R))
    exact ⟨(default : PrimeSpectrum K), Subsingleton.elim _ _⟩⟩
  have := hB.proper
  let B' : Over (Spec (CommRingCat.of K)) := (Over.pullback p).obj B
  let π : B'.left ⟶ B.left := pullback.fst B.hom p
  have h : IsGrpPullback B' B p π := isGrpPullback_pullback B p
  have : IsCommMonObj B' := PolPull.isCommMonObj_of_isGrpPullback h
  have hB' : IsAbelianScheme B' := by
    have := hB.comm
    exact
      { comm := PolPull.isCommMonObj_of_isGrpPullback h
        smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hB.smooth
        proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hB.proper
        geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hB.geomConnected }
  have : Flat π := MorphismProperty.of_isPullback (P := @Flat) h.1.flip inferInstance
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip inferInstance
  obtain ⟨hL', hr, ⟨c', -⟩, -⟩ := CubePf.cubePull _ _ B B' (cubeMapOf h) L c

  have hsec : ∃ s' : LB.Sec (AbLaw.pw (L.L.pull π) k), ∃ j, s'.f j ≠ 0 :=
    pull_pw_eq L.L π k ▸ exists_sec_pull_ne_zero π (isLB_pw L.isLB k) s hs
  obtain ⟨s', hs'⟩ := hsec
  have hcov : ∃ (m : ℕ) (t : Fin (m + 1) → LB.Sec ((AbLaw.pw L.L (2 * k : ℕ)).pull π)),
      ⨆ i, nonzeroLocus (t i) = ⊤ := by
    rw [pull_pw_eq]
    exact CubeFree.exists_cover_nonzeroLocus K B' hB' ((cubeMapOf h).rigLB L hL' hr) c' k s' hs'
  obtain ⟨m', t', ht'⟩ := hcov
  have hM := isLB_pw L.isLB (2 * k : ℕ)
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  obtain ⟨m, t, ht⟩ := exists_cover_of_pull g hg B.hom π B'.hom h.1 hM t' ht'
  obtain ⟨P, q, H, φ, hq, hH, hφ, hiso, hloc⟩ := exists_map B.hom hM t ht

  let Z : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd q p)
  let ρ : Z.left ⟶ P := pullback.fst q p
  let φ' : B' ⟶ Z := Over.homMk (pullback.lift (π ≫ φ) B'.hom (by rw [Category.assoc, hφ]; exact h.1.w))
    (pullback.lift_snd _ _ _)
  have hφ' : φ'.left ≫ ρ = π ≫ φ := pullback.lift_fst _ _ _
  have hZ : IsPullback ρ Z.hom q p := IsPullback.of_hasPullback q p
  have hsq : IsPullback π φ'.left φ ρ := by
    refine IsPullback.of_bot ?_ hφ'.symm hZ
    rw [Over.w φ', hφ]
    exact h.1
  have : IsProper Z.hom := MorphismProperty.of_isPullback (P := @IsProper) hZ hq
  have : Surjective ρ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip inferInstance
  have hqf' : LocallyQuasiFinite φ'.left := by
    refine _root_.GlobalTheory.CubicalQuasiFinite.locallyQuasiFinite_of_pow_iso_pull hcount K B' hB' ((cubeMapOf h).rigLB L hL' hr) c' (2 * k) n hn hnK hnk
      (fun x hxn htr => ?_) Z φ' (H.pull ρ) (pull_isLB hH ρ) ?_
    · have key : ∀ p' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R), p' = p →
          ∀ y : Over.mk p' ⟶ B, y ^ n = 1 → Triv (translDiff B L.L y) → y = 1 := by
        rintro _ rfl
        exact hx
      have e : pushHom h _ x = 1 := key _ (Category.id_comp p) (pushHom h _ x)
        (by rw [← map_pow, hxn, map_one]) (triv_translDiff_push h L.isLB x htr)
      have e' := e.trans (map_one (pushHom h (baseOver _))).symm
      exact Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e') (by rw [Over.w, Over.w]))
    · show LBIso (AbLaw.pw (L.L.pull π) (2 * k : ℕ)) ((H.pull ρ).pull φ'.left)
      rw [← pull_pw_eq]
      exact LBIso.chartPull (Geo.Tor.chartPullPull _ π π rfl)
        (chartPullLinComb H ρ (fun _ => φ'.left) (fun _ => φ) (fun _ => 1) π fun _ => hφ') hiso
  have : IsProper (φ ≫ q) := hφ ▸ hB.proper
  have : IsProper φ := IsProper.of_comp φ q
  have : LocallyQuasiFinite φ := Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ φ φ'.left π ρ hsq
    inferInstance inferInstance inferInstance hqf'
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hva := veryAmpleBy_pw_of_affine_loci R B.left B.hom _ m t hM ht fun i => by
    obtain ⟨V, hV, e⟩ := hloc i
    rw [e]
    exact hV.preimage φ
  obtain ⟨d, hd, hva⟩ := hva
  rw [pw_pw_eq, ← Nat.cast_mul] at hva
  exact (Unif.relAmple_iff_veryAmpleBy R B L.L L.isLB).2
    ⟨2 * k * d, Nat.mul_pos (by omega) hd, hva⟩

end GlobalTheory.AmpleCrit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gm_eq_of_flat_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    {U V : Y.Opens} (a : Γ(Y, U)ˣ) (b : Γ(Y, V)ˣ)
    (h : ∀ x : X, π x ∈ U → π x ∈ V → gm π x U a = gm π x V b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hU : r z ∈ U) (hV : r z ∈ V) :
    gm r z U a = gm r z V b := by
  have e : pullU π (U ⊓ V) (res inf_le_left a) = pullU π (U ⊓ V) (res inf_le_right b) := by
    apply unit_ext
    intro x hx
    have hx' : π x ∈ U ⊓ V := hx
    have h₁ := gm_pull (𝟙 X) π x (U ⊓ V) hx' (res inf_le_left a)
    have h₂ := gm_pull (𝟙 X) π x (U ⊓ V) hx' (res inf_le_right b)
    rw [Category.id_comp] at h₁ h₂
    exact h₁.trans ((gm_res π x _ hx' a).trans ((h x hx'.1 hx'.2).trans
      ((gm_res π x _ hx' b).symm.trans h₂.symm)))
  have e' : (res inf_le_left a : Γ(Y, U ⊓ V)ˣ) = res inf_le_right b :=
    Units.ext (FunDescent.app_injective π (U ⊓ V) (congrArg Units.val e))
  have hz : r z ∈ U ⊓ V := ⟨hU, hV⟩
  exact (gm_res r z _ hz a).symm.trans ((congrArg (gm r z _) e').trans (gm_res r z _ hz b))

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}


omit [IsDomain R] in
theorem trans_comp_proj (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem trans_comp_q (e : ℕ) :
    thickMap R I e G ≫ (U.gt (e + 1)).q.left = (U.gt e).q.left ≫ thickMap R I e D.toPre.P.A := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((U.gt_q e).trans
      ((congrArg ((U.gt e).q.left ≫ ·) (trans_comp_proj e D.toPre.P.A).symm).trans
        (Category.assoc _ _ _).symm))
  · have h₁ : (U.gt (e + 1)).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt (e + 1)).q
    have h₀ : (U.gt e).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt e).q
    have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg (thickMap R I e G ≫ ·) h₁).trans ((k G).trans
      ((congrArg (· ≫ thickTrans R I e) h₀.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg ((U.gt e).q.left ≫ ·) (k _).symm).trans (Category.assoc _ _ _).symm)))))

theorem gw_trans (e : ℕ) (y : (thickObj R I e G).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (U.gt e).pG.left y ∈ D.toPre.P.L.U jM) (hL : (fstG I e G).left y ∈ U.LG.L.U jL) :
    gw (U.w (e + 1)) (thickMap R I e G) y jM (fun _ => jL) = gw (U.w e) (𝟙 _) y jM (fun _ => jL) := by
  have hM' : (U.gt (e + 1)).pG.left (thickMap R I e G y) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g y ∈ D.toPre.P.L.U jM) (U.gt_q e)).mpr hM
  have hL' : (fstG I (e + 1) G).left (thickMap R I e G y) ∈ U.LG.L.U jL :=
    (congrArg (fun g => g y ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL
  have hm : y ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt (e + 1)).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I (e + 1) G).left).U (fun _ => jL)) ⊓
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)) :=
    ⟨⟨mem_pull.2 hM', mem_pull.2 hL'⟩, mem_pull.2 hM, mem_pull.2 hL⟩
  have H := congrArg (gm (𝟙 _) y _)
    (U.w_compat e (fun _ => jM, fun _ => jL) _ inf_le_left inf_le_right)
  have h₁ := gm_pull (𝟙 _) (thickMap R I e G) y _ hm.1 ((U.w (e + 1)).s (fun _ => jM, fun _ => jL))
  rw [Category.id_comp] at h₁
  exact h₁.symm.trans ((gm_res (𝟙 _) y inf_le_left hm _).symm.trans
    (H.trans (gm_res (𝟙 _) y inf_le_right hm _)))

end GlobalTheory.UnifCompare

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor UnifCompare

theorem unifPre_polarised_iso :
    GlobalFnsSt → SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) := by
  intro hGF hS hA R _ _ _ I hR D D' A A' G _ _ hG U U' wL he hgen hrig
  choose β hβm hβ using unifPre_abelianPart_iso R I hR D D' A A' G hG U U'
  choose v hvg hv using fun e =>
    T.uniformisation_polarisations_agree_at_level hGF R I hR D D' A A' G hG U U' wL he hgen hrig e (β e) (hβm e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG I e D.toPre.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG I e D.toPre.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R I e D'.toPre.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R I e D.toPre.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q, Category.assoc, hβl,
      trans_comp_q, ← Category.assoc, hβl]
  obtain ⟨hN, -, -, hC⟩ := hR
  obtain ⟨Φ, w, hw, H⟩ := _root_.GlobalTheory.exists_iso_of_compatible_thickenings hS hA R I D.toPre.P D'.toPre.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R I e D'.toPre.P.A).left,
        y ∈ (D.toPre.P.L.pull ((β e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') →
        thickMap R I e D'.toPre.P.A y ∈
          (D.toPre.P.L.pull ((β (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I (e + 1) D'.toPre.P.A).left).U (fun _ => j') := by
      intro y hy
      have k : thickMap R I e D'.toPre.P.A ≫ (β (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left =
          (β e).hom.left ≫ (fstG I e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U j) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ D'.toPre.P.L.U j') (trans_comp_proj e _)).mpr
          (mem_pull.1 hy.2))⟩
    have hz : r z ∈ (D.toPre.P.L.pull ((β e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG I e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG I e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hp e)).mp (mem_pull.1 hx.1)
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_pull.1 hx.2
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R I e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U' e x j' jL' hM' hL', gw_trans U e x j jL hM hL, trans_comp_q, trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  refine ⟨Φ, w, hw, fun e => ⟨?_, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  · exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  · have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
      ((congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hp e)).mpr hM) hM'
    rw [Category.assoc] at h
    exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

end GlobalTheory
end

