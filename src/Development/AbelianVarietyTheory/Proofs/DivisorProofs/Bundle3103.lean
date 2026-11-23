module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenNearOfFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibreOpen

theorem eq_one_of_local {S' : Scheme.{0}} {G : Over S'} [GrpObj G] (T : Over S') (x : T ⟶ G)
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ x = 1) : x = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨U, hp, hx⟩ := h p
  refine ⟨U, hp, ?_⟩
  have h1 : (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ (1 : T ⟶ G) = 1 := MonObj.comp_one _
  rw [← h1] at hx
  exact congrArg (fun q => q.left) hx

theorem unit_residue : ∀ (S' : Scheme.{0}) (W : S'.Opens) (s : S'), s ∈ W → ∀ d : ℕ, IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → IsUnit ((d : ℕ) : S'.residueField s) := by
  intro S' W s hs d hd
  let x : W.toScheme := ⟨s, hs⟩
  have h1 : IsUnit ((d : ℕ) : W.toScheme.residueField x) := by
    have := hd.map (W.toScheme.evaluation ⊤ x trivial).hom
    simpa using this
  have hx : W.ι.base x = s := rfl
  rw [isUnit_iff_ne_zero] at h1 ⊢
  intro h0
  apply h1
  have := congrArg (Scheme.Hom.residueFieldMap W.ι x).hom (hx ▸ h0 : ((d : ℕ) : S'.residueField (W.ι.base x)) = 0)
  simpa using this


open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison GlobalTheory.KerKilledLocal in
theorem kerKilledOn_of_global : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (V : S'.Opens), (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → x ^ d = 1) → GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' G _ _ P V h T x hs
  apply down_injective G V
  rw [down_pow, down_one]
  let T' : Over S' := Over.mk (T.hom ≫ V.ι)
  let GV := (Over.pullback V.ι).obj G
  have hr : Set.range T'.hom.base ⊆ (V : Set S') := by
    rintro _ ⟨t, rfl⟩
    have h' : T'.hom.base t ∈ Set.range V.ι.base := ⟨T.hom.base t, rfl⟩
    rwa [Scheme.Opens.range_ι] at h'
  refine h T' (down G V x) hr ?_
  let Y : Over V.toScheme := Over.mk ((snd G T').left ≫ T.hom)
  have w1 : (fst G T').left ≫ G.hom = (G ⊗ T').hom := Over.w (fst G T')
  have w2 : (snd G T').left ≫ (T.hom ≫ V.ι) = (G ⊗ T').hom := Over.w (snd G T')
  let u : Y ⟶ GV := Over.homMk (pullback.lift (fst G T').left ((snd G T').left ≫ T.hom) (by
      rw [w1, Category.assoc, w2])) (pullback.lift_snd _ _ _)
  let v : Y ⟶ T := Over.homMk (snd G T').left rfl
  have heq : (lift u v).left ≫ (lift (snd GV T ≫ x) (fst GV T)).left ≫ pφ₂ V.ι G =
      (lift (snd G T' ≫ down G V x) (fst G T')).left ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply adelic_GL2_ext_of_local_components G
    · simp only [Category.assoc, pφ₂_fst]
      rw [lift_left_fst'_assoc, lift_left_fst']
      simp only [Over.comp_left, Category.assoc]
      rw [lift_left_snd'_assoc]
      rfl
    · simp only [Category.assoc, pφ₂_snd]
      rw [lift_left_snd'_assoc, lift_left_snd', lift_left_fst'_assoc]
      change pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι = _
      rw [pullback.lift_fst]
  obtain ⟨t, ht⟩ := gen_pull3 P (pφ₂ V.ι G) _ (lift u v).left _ (𝟙 _) heq hs
  exact gen_chartPull (chartPullUnpull _ _ rfl) t ht

theorem comp_pow_overScheme_grpObj {S' : Scheme.{0}} {G T T' : Over S'} [GrpObj G] (u : T' ⟶ T) (x : T ⟶ G) :
    ∀ n : ℕ, u ≫ x ^ n = (u ≫ x) ^ n
  | 0 => by rw [pow_zero, pow_zero, MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj u x n]

theorem kerKilledOn_near_of_fibre : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → ∀ s ∈ W, GlobalTheory.KerKilledNear.FibreKilled d G P s → ∃ V : S'.Opens, s ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' _ G _ _ P hA hP hg₁ hg₂ hsym W hamp hd s hs hfib
  obtain ⟨V₀, Z, i, hs₀, hmono, hfin, h1, hmul, hinv, hfac, hloc⟩ := GlobalTheory.T.exists_finite_kernel_near_diagonal_ample S' G P hA hP hg₁ hg₂ hsym W hamp s hs
  have hfibZ : ∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s),
      T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1 := by
    rintro T z ⟨f, hf⟩
    have hT : Set.range T.hom.base ⊆ (V₀ : Set S') := by
      rintro _ ⟨p, rfl⟩
      have e : (f ≫ S'.fromSpecResidueField s).base p = s :=
        Set.mem_singleton_iff.mp (Scheme.range_fromSpecResidueField s ▸ Set.mem_range_self (f.base p))
      rw [hf, e]
      exact hs₀
    refine eq_one_of_local T _ fun p => ?_
    obtain ⟨U, hp, c, hc⟩ := hloc T z hT p
    refine ⟨U, hp, ?_⟩
    rw [comp_pow_overScheme_grpObj]
    exact hfib (Over.mk (U.ι ≫ T.hom)) _ ⟨U.ι ≫ f, by simp [hf]⟩ ⟨c, hc⟩
  obtain ⟨V, hsV, hVV₀, hV⟩ := GlobalTheory.T.finite_subgroup_killed_near_point_of_fibre S' G Z i V₀ d s hmono hs₀ hfin h1 hmul hinv (unit_residue S' W s hs d hd) hfibZ
  refine ⟨V, hsV, kerKilledOn_of_global d S' G P V fun T x hT hx => ?_⟩
  obtain ⟨z, rfl⟩ := hfac T x (hT.trans hVV₀) hx
  exact hV T z hT

end GlobalTheory.KerKilledFibreOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEqOfCodimOneEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelOne

variable {R : Type} [CommRing R]

theorem pull_iso_bijective' {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem laurentVar_map {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar B) = laurentVar C := by
  ext
  simp only [laurentVar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  have h := congrArg (fun g => g.hom (LaurentPolynomial.T 1 : LaurentPolynomial B))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  rw [laurentMap_T] at h
  exact h.symm

end GlobalTheory.EtC.GmStep.LevelOne

namespace GlobalTheory.EtC.GmStep.LevelOne

theorem rowOne_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (rowOne A A' q i k) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, h2⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr1 := GlobalTheory.T.laurentKummerCupProductMap_bijective_finite_strictHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap1 := congrArg (fun f => disc.map f) h1
  have hmap2 := congrArg (fun f => disc.map f) h2
  simp only [Functor.map_comp] at hmap1 hmap2
  have hqL : IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
    have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.comp
      (LaurentPolynomial.C : A →+* LaurentPolynomial A))
    simpa using this
  have hkum : pull _ (disc.map e.hom) (tw q 1) 1 (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A))) =
      kum q (laurentVar (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) := by
    rw [← pull_comp, augK]
    erw [hmap2]
    have := (GlobalTheory.EtC.a6nat_holds q).2.2.2 (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A
      (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) (laurentVar A) hqL
    rw [laurentVar_map] at this
    exact this
  have hcst : ∀ a, pull _ (disc.map e.hom) (tw q (i - 1)) 0
      (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q (i - 1)) 0
        (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    rw [← pull_comp, hmap1, pull_comp]
    rfl
  have heq : ∀ a, pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1 (rowOne A A' q i k a) =
      gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    simp only [rowOne, gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [pull_cast, (GlobalTheory.EtC.a6nat_holds q).1, hcst, hkum]
    rfl
  have hcomp : (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) ∘ (rowOne A A' q i k) =
      (gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i) ∘ (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) :=
    pull_iso_bijective' (disc.mapIso e) (tw q i) 1
  have he0 : Function.Bijective (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    pull_iso_bijective' (disc.mapIso e0) (tw q (i - 1)) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr1.comp he0

end GlobalTheory.EtC.GmStep.LevelOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceConstantLiftMemFil
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount.LieZFil

theorem omega_sq {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) :
    D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
  rw [← D.tr_eq, ← D.nm_eq]; ring

theorem end_sq {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (h : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) (act (algebraMap (𝓞 D.F) D.O D.ω) h) =
      (D.tr : C) • act (algebraMap (𝓞 D.F) D.O D.ω) h - (D.nm : C) • h := by
  have e := congrArg (fun x => act (algebraMap (𝓞 D.F) D.O x) h) (omega_sq D)
  simp only [map_mul, map_sub, map_intCast, Module.End.mul_apply, LinearMap.sub_apply] at e
  rw [e]
  simp [Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

theorem rho_part_eig {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (ρ : C) (hρ : ρ ^ 2 - D.tr * ρ + D.nm = 0) (y : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) -
      ρ • ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) = 0 := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, end_sq]
  have hn : (D.nm : C) = ρ * (D.tr - ρ) := by linear_combination hρ
  rw [hn]
  module

theorem sum_mem_fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {C : Type} [CommRing C] [IsLocalRing C] (β : R →+* C)
    {s : Sp C ⟶ Sp R} (hs : s = spMap β) (o : GlobalTheory.UPel.HT.Obj b N s) {r : ℕ} (lam : Fin r → C)
    (c : Fin r → 𝓞 D.F) (hlam : ∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) (y : HdR o.A) :
    ∑ l, lam l • GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O (c l))
      ((GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O D.ω) -
        ((D.tr : C) - β b.ρ) • 1) y) ∈ Fil o.A := by
  set act := GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act with hact
  set u := (act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - β b.ρ) • 1) y with hu
  have hfil : ∀ (x : D.O) {h : HdR o.A}, h ∈ Fil o.A → act x h ∈ Fil o.A := fun x h hh => by
    haveI := o.act.hom x
    exact push_mem_Fil (o.act.act x) hh
  have hρ : β b.ρ ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hω : act (algebraMap (𝓞 D.F) D.O D.ω) u - β b.ρ • u ∈ Fil o.A := by
    rw [hu, rho_part_eig act (β b.ρ) hρ y]; exact zero_mem _
  obtain ⟨w, hw, hsum⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N C β s hs o u hω
  set c' := fun l => algebraMap (𝓞 D.F) D.O (c l)
  have h1 : ∀ l, act (c' l) u - ∑ i, act (c' l) (w i) ∈ Fil o.A := fun l => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_sub]; exact hfil _ hsum
  have h2 : ∀ i, ∑ l, lam l • act (c' l) (w i) ∈ Fil o.A := fun i => by
    have e : ∑ l, lam l • act (c' l) (w i) = ∑ l, lam l • (act (c' l) (w i) - β (b.t i (c l)) • w i) +
        (∑ l, lam l * β (b.t i (c l))) • w i := by
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_sub, mul_smul]; abel
    rw [e, hlam i, zero_smul, add_zero]
    exact sum_mem fun l _ => Submodule.smul_mem _ _ (hw i (c l))
  have e : ∑ l, lam l • act (c' l) u = ∑ l, lam l • (act (c' l) u - ∑ i, act (c' l) (w i)) +
      ∑ i, ∑ l, lam l • act (c' l) (w i) := by
    rw [Finset.sum_comm (f := fun i l => lam l • act (c' l) (w i)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.smul_sum, ← smul_add, sub_add_cancel]
  show ∑ l, lam l • act (c' l) u ∈ Fil o.A
  rw [e]
  exact add_mem (sum_mem fun l _ => Submodule.smul_mem _ _ (h1 l)) (sum_mem fun i _ => h2 i)

theorem dualNumber_local (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

end GlobalTheory.HTCount.LieZFil

namespace GlobalTheory.HTCount


open LieZFil in
set_option maxHeartbeats 800000 in
theorem lieZ_mem_fil_and_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  intro p _ D R _ b N k _ t o₀ β ht o' m' z hz
  constructor
  · induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      exact sum_mem_fil β ht o₀ lam c hlam y'
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  · have hbc := GlobalTheory.HTRealise.isBC_constMor o₀.ab
    suffices H : ∀ z ∈ lieZ o₀ β, hbc.bcMap z ∈ liftFil (epsDP k) m'.cart by
      refine ⟨hbc.bcMap z, H z hz, fun c => ?_⟩
      rw [(hbc.corr_iff.2 rfl) c]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    have hE : ∀ (x : D.O) (h : HdR o₀.A), crysToDR (epsDP k) m'.cart (hbc.bcMap (crysAct o₀ x h)) =
        GlobalTheory.HTSummand.crysAct (dp0 (DualNumber k)) (𝟙 _) o'.act x (crysToDR (epsDP k) m'.cart (hbc.bcMap h)) := by
      intro x h
      haveI := o₀.act.hom x
      haveI := o'.act.hom x
      have e1 : hbc.bcMap (crysAct o₀ x h) =
          push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act x) (hbc.bcMap h) := by
        rw [← hbc.corr_iff]
        exact GrpMor.Corr.push (m := constMor o₀.A) (constMor o₀.A) (o₀.act.act x) (o₀.act.act x) (by rfl)
          (hbc.corr_iff.2 rfl)
      have e2 := crysToDR_push (epsDP k) m'.cart m'.cart (o₀.act.act x) (o'.act.act x) (m'.act x).symm (hbc.bcMap h)
      exact (congrArg (crysToDR (epsDP k) m'.cart) e1).trans e2
    have hs : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
      rw [ht]; unfold spMap; rw [← Spec.map_comp]; rfl
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      have hlam' : ∀ i, ∑ l, algebraMap k (DualNumber k) (lam l) *
          ((algebraMap k (DualNumber k)).comp β) (b.t i (c l)) = 0 := fun i => by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [RingHom.comp_apply, ← map_mul, ← map_sum, hlam i, map_zero]
      haveI : IsLocalRing (DualNumber k) := dualNumber_local k
      have key := sum_mem_fil ((algebraMap k (DualNumber k)).comp β) hs o' (fun l => algebraMap k _ (lam l)) c hlam'
        (crysToDR (epsDP k) m'.cart (hbc.bcMap y'))
      rw [liftFil, Submodule.mem_comap]
      convert key using 2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smulₛₗ, hE, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, RingHom.comp_apply, map_intCast, RingHom.id_apply, map_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.HTCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTCount

theorem crysAct_mem_Fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (x : D.O) {h : HdR o₀.A} (hh : h ∈ Fil o₀.A) : crysAct o₀ x h ∈ Fil o₀.A := by
  haveI := o₀.act.hom x
  exact push_mem_Fil (o₀.act.act x) hh

theorem crysAct_intCast {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (n : ℤ) (h : HdR o₀.A) : crysAct o₀ (algebraMap (𝓞 D.F) D.O (n : 𝓞 D.F)) h = (n : k) • h := by
  rw [map_intCast, map_intCast, Int.cast_smul_eq_zsmul]
  rfl

theorem lieZ_le_Fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β →
    ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  intro p _ D R _ b N k _ β s hs o₀
  rw [lieZ, Submodule.span_le]
  rintro z ⟨r, lam, c, y, ⟨x, rfl⟩, hlam, rfl⟩
  set T := crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) with hT

  have hω : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.nm_eq, ← D.tr_eq]; ring
  have hT2 : T (T x) = (D.tr : k) • T x - (D.nm : k) • x := by
    have := congrArg (fun u => crysAct o₀ (algebraMap (𝓞 D.F) D.O u) x) hω
    simp only [map_mul, map_sub, Module.End.mul_apply, LinearMap.sub_apply] at this
    rw [crysAct_intCast, crysAct_intCast] at this
    exact this

  have hρ : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this

  have hy0 : T ((T - ((D.tr : k) - β b.ρ) • 1) x) - β b.ρ • (T - ((D.tr : k) - β b.ρ) • 1) x = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hT2]
    rw [← hρ]
    module
  obtain ⟨w, hw, hyw⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N k β s hs o₀ _ (hy0 ▸ zero_mem _)
  set y := (T - ((D.tr : k) - β b.ρ) • 1) x
  set q := (Fil o₀.A).mkQ
  have key : ∀ c' : 𝓞 D.F, q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = ∑ i, β (b.t i c') • q (w i) := by
    intro c'
    have h1 : crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y - ∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i) ∈ Fil o₀.A := by
      have := crysAct_mem_Fil o₀ (algebraMap (𝓞 D.F) D.O c') hyw
      rwa [map_sub, map_sum] at this
    have e1 : q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = q (∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i)) :=
      (Submodule.Quotient.eq _).2 h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    exact (Submodule.Quotient.eq _).2 (hw i c')
  rw [SetLike.mem_coe, ← Submodule.Quotient.mk_eq_zero]
  change q _ = 0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, key, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hlam, zero_smul, Finset.sum_const_zero]

end GlobalTheory.HTCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAmpleKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrinThicken

open GlobalTheory.AbDual GlobalTheory.CechPic

theorem evc_comm {S : Scheme.{0}} {X Y : Over S} {M : LB (X ⊗ X).left} (hM : M.IsLB)
    (hc : cls M hM = CechPic.pull (lift (snd X X) (fst X X)).left (cls M hM)) (a b : Y ⟶ X) :
    evc hM a b = evc hM b a := by
  rw [evc, evc]
  conv_lhs => rw [hc]
  rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]

end GlobalTheory.PrinThicken
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenySquareCompatCompQuasiInv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.QCompat

theorem comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ B₁ _ _ _ _ φ θ ψ₁ ψ₁' hB hk hq hq₁ hφ hsq
  obtain ⟨h1, h2, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow T B₁ hB k hk
  haveI : Epi ((𝟙 B₁) ^ k).left := Flat.epi_of_flat_of_surjective _
  have e₁ : ψ₁'.left ≫ ψ₁.left = ((𝟙 B₁) ^ k).left := by rw [← Over.comp_left, hq₁.2.2.2]
  haveI : Epi (ψ₁'.left ≫ ψ₁.left) := by rw [e₁]; infer_instance
  haveI : Epi ψ₁.left := epi_of_epi ψ₁'.left ψ₁.left
  rw [← cancel_epi ψ₁.left, ← Category.assoc, ← hsq, Category.assoc, ← Over.comp_left, hq.2.2.1,
    ← Category.assoc, ← Over.comp_left, hq₁.2.2.1]
  exact (GlobalTheory.LamF.IsGrpPullback.id_pow_left hφ k).symm

end GlobalTheory.UPel.HT.ES.QCompat
end

