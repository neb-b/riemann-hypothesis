module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0743
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0734
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LbSpreads
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GDeep

theorem big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem exists_deep : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z)
    (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s →
    ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ →
      ∀ m₀ : ℕ, ∃ D : Deep X₁ ε₁, m₀ ≤ D.m := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ hε₁ m₀
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j, hk, hB, hj, big⟩ :=
    big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 ((X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) * max m₀ 1) ^ 2)
  have hun1 : IsUnit (X₁.ρ.n : X₁.o₁) := by
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [hL₁]; exact dvd_pow_self _ (by omega)
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) X₁.S.unit
  have hunK : IsUnit ((((X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 : ℕ)) : X₁.o₁) := by
    push_cast
    exact ((hun1.pow _).mul ((hun1.pow _).pow _)).pow _
  obtain ⟨o₂, Ω₂, _, _, _, _, _, κ, fd, gal, hκ, hc, R, h, P, ψ, ze, hfg, hfr, hh, hPg, hpb, hlb, ⟨lev⟩⟩ :=
    _root_.GlobalTheory.Poinc.exists_deep_level X₁ _ (by have := hℓp.pos; positivity) hunK
  have hS := _root_.GlobalTheory.Poinc.hypS_polAV_pullback X₁.ρ.P P (spMap h) ψ hpb hlb X₁.ρ.hypS
  have hun2 : IsUnit (X₁.ρ.n : o₂) := by simpa using hun1.map κ
  obtain ⟨S₂, ρ₂, hR, φ, -, hN₂, hr₂, hg₂, hpb₂, hlb₂, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o₂ Ω₂ R hfg hfr P X₁.ρ.n k j ze hℓp X₁.ρ.n_odd hk hj hun2 hS lev
  set h' : X₁.S.R →+* S₂.R := (Subalgebra.inclusion hR).toRingHom.comp h with hh'
  have hval : ∀ a, ((h' a : S₂.R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => hh a
  have hpb' : IsGrpPullback ρ₂.P.A X₁.ρ.P.A (spMap h') (φ ≫ ψ) := by
    rw [hh', ← spMap_comp']
    exact hpb₂.comp hpb
  have hlb' : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (lbIso_pull_comp' hlb φ rfl)
  obtain ⟨ε₂, hε₂, hεc⟩ := _root_.GlobalTheory.Poinc.isDiagEnd_pullback F W X₁.ρ.P ρ₂.P X₁.u (spMap h') (φ ≫ ψ) ε₁ hε₁ hpb' hlb'
  have hsharp : SharpOver F W ρ₂.P (spMap h' ≫ X₁.u) := by
    obtain ⟨c, hc₁, pr, hpr, hun, hLc, -⟩ := hε₂
    exact ⟨c, hc₁, pr, hpr, hun, hLc⟩
  have key : spMap S₂.R.val.toRingHom ≫ spMap h' = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [spMap_comp', spMap_comp']
    congr 1
    ext a
    exact hval a
  have hgen : ∀ w, (spMap S₂.R.val.toRingHom ≫ spMap h' ≫ X₁.u) w ∈ genericPoints F.X := by
    intro w
    rw [← Category.assoc, key, Category.assoc, Scheme.Hom.comp_apply]
    exact X₁.gen _
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := _root_.GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional X₁ o₂ Ω₂ κ hκ hc
  haveI := hq
  haveI := X₁.fin
  have hcomp : M₂.pt ≫ q ≫ X₁.π = spMap S₂.R.val.toRingHom ≫ (spMap h' ≫ X₁.u) ≫ i := by
    rw [← Category.assoc, hqgen, Category.assoc, X₁.comp, Category.assoc, ← Category.assoc (spMap S₂.R.val.toRingHom),
      key, Category.assoc]
  have hbase : spMap S₂.R.val.toRingHom ≫ (spMap h' ≫ X₁.u) ≫ F.s =
      spMap ((algebraMap o₂ Ω₂).comp (κ.comp X₁.κ)) := by
    rw [← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, X₁.base, spMap_comp', ← RingHom.comp_assoc, ← hc]
  have hbig : S₂.Big := big j le_rfl o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : Setup F W i := Setup.mk o₂ Ω₂ S₂ ρ₂ hbig (spMap h' ≫ X₁.u) hsharp hgen M₂ hMn (q ≫ X₁.π) inferInstance hcomp
    X₁.one_le X₁.three_le X₁.odd X₁.z X₁.proj X₁.normalZ X₁.imm X₁.thetaSetup_structureMap_comp X₁.dense X₁.e8 X₁.thetaInt (κ.comp X₁.κ) hbase
  have hle : X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) * max m₀ 1 ≤ X₁.ρ.n ^ k :=
    (Nat.pow_le_pow_iff_left two_ne_zero).1 hB
  have hpos : 1 ≤ X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := Nat.one_le_pow _ _ (by omega)
  have hm₁ : 1 ≤ max m₀ 1 := le_max_right _ _
  have hm₀ : m₀ ≤ X₁.ρ.n ^ k :=
    (le_max_left m₀ 1).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans hle)
  have hdm : X₁.S.r * X₁.S.N ∣ X₁.ρ.n ^ k := by
    rw [hL₁]
    refine pow_dvd_pow _ ((Nat.pow_le_pow_iff_right hℓ2).1 ?_)
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans hle
  have hd₂ : X₁.S.r * X₁.S.N ∣ S₂.r * S₂.N := by
    rw [hN₂]
    exact (hdm.trans (dvd_pow_self _ two_ne_zero)).trans (dvd_mul_left _ _)
  obtain ⟨lab, hsame, hrange⟩ :=
    _root_.GlobalTheory.Poinc.DeepLab.exists_lab_same X₁.S S₂ X₁.ρ ρ₂ ε₁ ε₂ (algebraMap X₁.Ω₁ Ω₂) h' (φ ≫ ψ) hval hpb' hlb' hεc hd₂
  exact ⟨Deep.mk X₂ ε₂ hε₂ fd gal X₂.projM q hq hqgen rfl (X₁.ρ.n ^ k) hN₂ hdm lab hsame hrange, hm₀⟩

end GlobalTheory.Poinc.GDeep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoTransOfSelfPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LBIsoEnd

def SelfPt {X : Scheme.{0}} (L : LB X) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : L.ι), f y ∈ L.U i → gm f y (L.U i ⊓ L.U i) (L.g i i) = 1

theorem selfPt_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : SelfPt L :=
  fun _ f y _ hi => gm_self hL f y hi

theorem selfPt_of_lbIso {X : Scheme.{0}} {B P : LB X} (hB : B.IsLB) (H : LBIso B P) : SelfPt P := by
  intro Y f y k hk
  obtain ⟨w, hw⟩ := H
  obtain ⟨i, hi⟩ := exists_chart hB (f y)
  have hm : f y ∈ P.U k ⊓ B.U i ⊓ (P.U k ⊓ B.U i) := ⟨⟨hk, hi⟩, hk, hi⟩
  have e := congrArg (gm f y (P.U k ⊓ B.U i ⊓ (P.U k ⊓ B.U i))) (hw (k, i) (k, i))
  have e' := (gm_res f y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div B P f y (k, i) (k, i) hm) (gm_res f y _ hm _))))
  rw [gm_self hB f y hi, inv_one, _root_.mul_one] at e'
  exact _root_.mul_eq_right.1 e'.symm

section Tri

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem indep_comp' (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w')
    (hL : SelfPt L) (hL'' : SelfPt L'') {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have a := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have b := hw' Y f y i i' k k hi hi' hk hk
  rw [hL Y ((f ≫ F') ≫ F) y j hj] at a
  rw [hL'' Y f y k hk] at b
  rw [a, b]
  generalize gm (f ≫ F') y _ (L'.g i i') = B
  generalize gw w (f ≫ F') y j i' = C
  generalize gw w' f y i' k = D
  rw [_root_.one_mul, inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, _root_.inv_mul_cancel, _root_.one_mul]

theorem exists_comp' (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL : SelfPt L) (hL'' : SelfPt L'') :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have glue : ∀ (j : L.ι) (k : L''.ι), ∃ s : Γ(X'', (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i → f y ∈ L''.U k →
        gm f y _ s = gw w (f ≫ F') y j i * gw w' f y i k := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : L'.ι → X''.Opens, ∀ i x, x ∈ W i ↔ F (F' x) ∈ L.U j ∧ F' x ∈ L'.U i ∧ x ∈ L''.U k :=
      ⟨fun i => F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull₂.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.2⟩
    have l₁ : ∀ i, W i ≤ F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) := fun i x hx =>
      ⟨mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
    have l₂ : ∀ i, W i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull.2 ((hW i x).1 hx).2.1, ((hW i x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X'', W i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), f y ∈ W i →
        gm f y (W i) (u i) = gw w (f ≫ F') y j i * gw w' f y i k :=
      ⟨fun i => res (l₁ i) (pullU F' _ (w.s (fun _ => j, i))) * res (l₂ i) (w'.s (fun _ => i, k)), fun Y f y i hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ i) hy _).trans (gm_pull f F' y _ (l₁ i hy) _)) (gm_res f y (l₂ i) hy _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hW i x).2 ⟨mem_pull₂.1 hx.1, hi, hx.2⟩⟩) u (fun i i' x hx => by
        have h₁ := (hW i x).1 hx.1
        have h₂ := (hW i' x).1 hx.2
        exact (hu _ (𝟙 X'') x i hx.1).trans ((indep_comp' w w' hw hw' hL hL'' (𝟙 X'') x j i i' k h₁.1 h₁.2.1 h₂.2.1
          h₁.2.2).trans (hu _ (𝟙 X'') x i' hx.2).symm))
    refine ⟨s, fun Y f y i hj hi hk => ?_⟩
    have hy := (hW i (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ i) hy s).symm.trans ((congrArg (gm f y (W i)) (hs i)).trans (hu Y f y i hy))
  choose s hs using glue
  exact ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, fun Y f y j i k hj hi hk => hs j k Y f y i hj hi hk⟩

end Tri

theorem lbIso_trans_of_selfPt {X : Scheme.{0}} {A B C : LB X} (hA : SelfPt A) (hB : B.IsLB) (hC : SelfPt C)
    (H : LBIso A B) (H' : LBIso B C) : LBIso A C := by
  obtain ⟨w', h'⟩ := H.chartPull (chartPullId A) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w, h⟩ := H'.chartPull (chartPullId B) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull C (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w'', T⟩ := exists_comp' hB w w' ((isGen_iff w).1 h) ((isGen_iff w').1 h') hC hA
  exact LBIso.chartPull (chartPullId A) (chartPullUnpull C _ (Category.id_comp _))
    ⟨w'', (isGen_iff w'').2 (T.pgen_comp hB ((isGen_iff w).1 h) ((isGen_iff w').1 h'))⟩

theorem lbIso_trans_end : ∀ (X : Scheme.{0}) (A B P : LB X), A.IsLB → B.IsLB → LBIso A B → LBIso P B → LBIso A P :=
  fun _ _ _ _ hA hB H H' =>
    lbIso_trans_of_selfPt (selfPt_of_isLB hA) hB (selfPt_of_lbIso hB H'.symm) H H'.symm

end GlobalTheory.LBIsoEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.PolRigid

open GlobalTheory.CechPic

theorem cls_lam_pull {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : LB B.left} (hL : L.IsLB)
    (x y : B ⟶ B) (h : ((abelian₂ B L).pull (lift x y).left).IsLB) :
    cls _ h = lam (cls L hL) x y := by
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have h₁ : cls _ hlam = lam (cls L hL) (fst B B) (snd B B) := cls_cube_two hL _ _ hlam
  rw [cls_pull hlam, h₁, pull_lam, lift_fst, lift_snd]

theorem lbIso_lam_of_quotient : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [CommRing R₀] [Nontrivial R₀] (π : R →+* R₀), Function.Surjective π → ∀ (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left), P.IsLB → (∃ t : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → ∀ (L : LB B.left) (L₀ : LB B₀.left), L.IsLB → L₀.IsLB → LBIso (L.pull i) L₀ → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → LBIso (abelian₂ B L) P := by
  intro R R₀ _ _ _ _ π hπ B _ _ B₀ _ _ i i₂ hA hpb hsq P hP hP₁ hP₂ L L₀ hL hL₀ e₀ e
  haveI : IsLocalRing R₀ := IsLocalRing.of_surjective' π hπ
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hlam₀ : (abelian₂ B₀ L₀).IsLB := LB.isLB_linComb hL₀ _ _
  have hD : (LB.div (abelian₂ B L) P).IsLB := LB.isLB_div hlam hP
  have hcD : cls _ hD = cls _ hlam - cls P hP := cls_div hlam hP hD

  have triv_of : ∀ {Y : Scheme.{0}} (f : Y ⟶ (G2 B).left), pull f (cls _ hlam) = pull f (cls P hP) →
      GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull f) := fun f hf =>
    (cls_eq_zero_iff (pull_isLB hD f)).1 (by rw [cls_pull hD, hcD, map_sub, hf, sub_self])

  have ax : ∀ (x y : B ⟶ B), (∃ t : (P.pull (lift x y).left).Gen, t.IsGen) → lam (cls L hL) x y = 0 →
      GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift x y).left) := fun x y hPxy hl => by
    refine triv_of _ ?_
    rw [← cls_pull hlam _ (pull_isLB hlam _), cls_lam_pull hL x y, hl, ← cls_pull hP _ (pull_isLB hP _)]
    exact ((cls_eq_zero_iff (pull_isLB hP _)).2 hPxy).symm
  have h₁ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift (𝟙 B) 1).left) := ax _ _ hP₂ (lam_one_right _ _)
  have h₂ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift 1 (𝟙 B)).left) := ax _ _ hP₁ (lam_one_left _ _)

  have hsq₀ : pull i₂ (cls _ hlam) = pull i₂ (cls P hP) := by
    have a : LBIso (abelian₂ B₀ L₀) ((abelian₂ B L).pull i₂) := GlobalTheory.ZM.SiegPull.lbIso_lam_pull hpb e₀.symm hsq
    rw [← cls_pull hlam _ (pull_isLB hlam _), ← cls_pull hP _ (pull_isLB hP _),
      ← (cls_eq_iff hlam₀ (pull_isLB hlam _)).2 a, (cls_eq_iff hlam₀ (pull_isLB hP _)).2 e]

  let k := ResidueField R₀
  let g₀ : R →+* k := (residue R₀).comp π
  have hpb₂ : IsPullback i₂ (G2 B₀).hom (G2 B).hom (spMap π) :=
    GlobalTheory.SiegelDescent.isPullback_square hpb.1 i₂ hsq
  have h₀ := (IsPullback.of_hasPullback (G2 B₀).hom (spMap (residue R₀))).paste_horiz hpb₂
  have e₁ : spMap (residue R₀) ≫ spMap π = Spec.map (CommRingCat.ofHom g₀) := by
    simp only [spMap, g₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [e₁] at h₀
  have ht₀ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (pullback.fst (G2 B₀).hom (spMap (residue R₀)) ≫ i₂)) :=
    triv_of _ (by rw [pull_comp, pull_comp, hsq₀])
  have hPf : GlobalTheory.SpreadingModels.PerfAll :=
    GlobalTheory.T.perfect_of_models (_root_.GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads _root_.GlobalTheory.CompanionTheory.NoethApprox.schemeModels GlobalTheory.T.smooth_spreads_out _root_.GlobalTheory.CompanionTheory.SpreadingModels.properSpreads _root_.GlobalTheory.CompanionTheory.LBLimit.lbSpreads)
  haveI := hA.smooth
  haveI := hA.proper
  have sm : Smooth (B ⊗ B).hom := by
    change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  have pr : IsProper (B ⊗ B).hom := by
    change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  obtain ⟨r, hr, hU⟩ := GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.globalFns_holds GlobalTheory.AbLaw.Seesaw.seesaw
    (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.globalFns_holds GlobalTheory.KuennethOne.kuenneth_injective)
    R B hA _ hD (hPf R _ (B ⊗ B).hom sm pr _ hD) h₁ h₂ k g₀ _ _ _ h₀ ht₀

  have hru : IsUnit r := by
    by_contra hnu
    refine hr ?_
    show residue R₀ (π r) = 0
    rw [residue_eq_zero_iff]
    intro hu
    obtain ⟨s, hs⟩ := hu.exists_right_inv
    obtain ⟨t, rfl⟩ := hπ s
    have hk : r * t - 1 ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hs, map_one, sub_self]
    have hm : RingHom.ker π ≤ maximalIdeal R := le_maximalIdeal (RingHom.ker_ne_top π)
    have hunit : IsUnit (r * t) := by
      by_contra h'
      have h1 : r * t ∈ maximalIdeal R := (mem_maximalIdeal _).2 h'
      have h2 : (1 : R) ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem h1 (hm hk)
        simpa using this
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
    exact hnu (isUnit_of_mul_isUnit_left hunit)
  let U := (B ⊗ B).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)
  have hsub : Set.range (𝟙 (B ⊗ B).left) ⊆ Set.range U.ι := by
    rintro x -
    rw [Scheme.Opens.range_ι]
    change r ∉ ((B ⊗ B).hom x).asIdeal
    exact fun hx => ((B ⊗ B).hom x).2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hru)
  have hT := GlobalTheory.AbLaw.CubeOpen.triv_comp (IsOpenImmersion.lift U.ι (𝟙 _) hsub) (IsOpenImmersion.lift_fac _ _ _) hU
  have hz : cls _ hD = 0 := by
    rw [← pull_id (cls _ hD), ← cls_pull hD _ (pull_isLB hD _)]
    exact (cls_eq_zero_iff _).2 hT
  exact (cls_eq_iff hlam hP).1 (sub_eq_zero.1 (hcD ▸ hz))

end GlobalTheory.PolRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem lbIso_of_generic_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (H : Over (Sp R)) [Smooth H.hom] [GeometricallyIntegral H.hom] (e : Sp R ⟶ H.left), e ≫ H.hom = 𝟙 _ → ∀ L L' : LB H.left, L.IsLB → L'.IsLB → LBIso (L.pull (pullback.fst H.hom (jK R))) (L'.pull (pullback.fst H.hom (jK R))) → LBIso L L' := by
  intro R _ _ _ _ _ H _ _ e he L L' hL hL' h
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have : IsDominant (jK R) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  have : QuasiCompact (jK R) := inferInstance
  refine (GlobalTheory.CechPic.cls_eq_iff hL hL').1 (GlobalTheory.ZH.EndoExtend.pic_ext (jK R) hn H e he ?_ ?_)
  · exact (GlobalTheory.DualOpen.pic_sp_local_eq_zero R _).trans
      (GlobalTheory.DualOpen.pic_sp_local_eq_zero R _).symm
  · exact (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2 h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericSemiAbelianCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.lbIso_of_generic_semiAbelian_cdvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (φ : GK.left ⟶ G₁.left), IsGrpPullback GK G₁ (jK V) φ → ∀ L L' : LB G₁.left, L.IsLB → L'.IsLB → LBIso (L.pull φ) (L'.pull φ) → LBIso L L' := by
  intro V _ _ _ hV G₁ _ _ hG GK _ φ hφ L L' hL hL' h
  haveI : IsDiscreteValuationRing V := hV.1
  have hi : pullback.fst G₁.hom (jK V) = hφ.1.isoPullback.inv ≫ φ := hφ.1.isoPullback_inv_fst.symm
  have h' : LBIso (L.pull (pullback.fst G₁.hom (jK V))) (L'.pull (pullback.fst G₁.hom (jK V))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp hφ.1.isoPullback.inv hi h
  exact GlobalTheory.lbIso_of_generic_normal_local V inferInstance inferInstance G₁.left G₁.hom (eSec G₁) hG.smooth
    hG.quasiCompact (GlobalTheory.geometricallyIntegral_of_isSemiAbelian G₁ (h := hG)) (Over.w (MonObj.one (X := G₁))) L L' hL hL' h'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionEqOfIso
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObsUniq

theorem obAt_eq_of_iso : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (C : Type) [Category.{0} C] (G : C ⥤ AffOp X₀) (d d' : GlobalTheory.CatCoh.H2 (ext R₁ (G ⋙ OAff s₀))), L.IsLB → L'.IsLB → LBIso L L' → ObAt S α L G d → ObAt S α L' G d' → d = d' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L L' C _ G d d' hL hL' e hd hd'
  obtain ⟨u, hu, hobs⟩ := hd
  obtain ⟨u', hu', hobs'⟩ := hd'
  obtain ⟨t, ht⟩ := GlobalTheory.FrameCob.frames_cohomologous X₀ C (opOf G) (opOf_le G) L L' u u' hL hL' e hu hu'
  refine _root_.GlobalTheory.LBObs.obU_eq_of_cohomologous R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) u u' t d d'
    ((ofSys_isFun S).restrict G) (fun T T' a ↦ ?_) hobs hobs'
  have := congrArg (fun w : Γ(X₀, opOf G T')ˣ ↦ (w : Γ(X₀, opOf G T'))) (ht T T' a)
  rw [Units.val_mul, Units.val_mul] at this
  exact this

end GlobalTheory.LBObsUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionTensorAdditive
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObL_tens : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L L' c c' hL hL'
  obtain ⟨C, _, _, G, hG, hLG⟩ := hL
  obtain ⟨C', _, _, G', hG', hLG'⟩ := hL'
  obtain ⟨D, _, _, K, H, H', ⟨θ⟩, ⟨θ'⟩, hK⟩ := GlobalTheory.LBObs.common_refinement X₀ C C' G G' hG hG'
  have h₁ := _root_.GlobalTheory.LBObs.obAt_refine R R₀ I hI π hπ hk R₁ α X₀ s₀ S L c C D G K H θ hLG
  have h₂ := _root_.GlobalTheory.LBObs.obAt_refine R R₀ I hI π hπ hk R₁ α X₀ s₀ S L' c' C' D G' K H' θ' hLG'
  obtain ⟨u, hu, hU⟩ := h₁
  obtain ⟨u', hu', hU'⟩ := h₂
  refine ⟨D, inferInstance, inferInstance, K, hK, fun T T' a ↦ u T T' a * u' T T' a,
    _root_.GlobalTheory.LBObs.isFrame_tens X₀ D (opOf K) (opOf_le K) L L' u u' hu hu', ?_⟩
  rw [map_add (f := _)]
  exact GlobalTheory.LBObs.isObU_mul R R₀ I hI π hπ hk R₁ α D (K ⋙ OAff s₀) ((ofSys S).restrict K) u u' _ _ hU hU'

end GlobalTheory.LBObs
end

