module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0305
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0308
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0297
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0306
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0303
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedModuleSystemRestriction
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue


open MvPolynomial in
theorem exists_finite_sub (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [DirectSum.Decomposition 𝒢]
    (h : ∀ i : ι, ∃ T : Finset G, ∀ y : G, ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set G)) :
    ∃ K : Submodule (MvPolynomial ι R) G, K.IsHomogeneous 𝒢 ∧
      Module.Finite (MvPolynomial ι R) K ∧ ∀ (t : ℤ) (I : Finset ι), I.Nonempty →
        Function.Bijective (homLocMap (isGradedMap_subtype 𝒢 K) I t) := by
  obtain ⟨r, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 h
  have hhom : (Submodule.span (MvPolynomial ι R) (Set.range g)).IsHomogeneous 𝒢 :=
    isHomogeneous_span_gr 𝒢 (by
      rintro _ ⟨l, rfl⟩
      exact ⟨d l, hg l⟩)
  refine ⟨_, hhom, Module.Finite.span_of_finite _ (Set.finite_range g), fun t I ⟨i, hi⟩ => ?_⟩
  letI := grSubDecomposition 𝒢 hhom
  exact homLocMap_bijective_of_X _ hi
    (fun m hm => ⟨0, by
      rw [(map_eq_zero_iff _ (Submodule.injective_subtype _)).1 hm, smul_zero]⟩)
    (fun y => by simpa using hsat i y) t

theorem pairs_of_cube {ι : Type} [LinearOrder ι] {A : Type} [CommRing A] (C : Cube.{0} ι A)
    (hpairs : ∀ c : ∀ i j : ι, C.obj {i, j}, (∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) +
      Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k)) →
      ∃ b : ∀ i : ι, C.obj {i}, ∀ i j, c i j = Cube.res C (sub_pair_left i j) (b i) -
        Cube.res C (sub_pair_right i j) (b j))
    {P : Finset ι → Type} [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)]
    [∀ S, Module (MvPolynomial ι A) (P S)]
    (Qs : ∀ S, Submodule A (P S))
    (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')
    (ψ : ∀ I : Finset ι, I.Nonempty → (C.obj I →ₗ[A] Qs I))
    (hb : ∀ I hI, Function.Bijective (ψ I hI))
    (hr : ∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (z : C.obj I),
      (ψ J hJ (Cube.res C h z) : P J) = res I J h (ψ I hI z : P I))
    (c : ∀ i j : ι, P {i, j}) (hc : ∀ i j, c i j ∈ Qs {i, j})
    (hcoc : ∀ i j k, res {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) +
      res {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) =
        res {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) :
    ∃ b : ∀ i : ι, P {i}, (∀ i, b i ∈ Qs {i}) ∧
      ∀ i j, c i j = res {i} {i, j} (sub_pair_left i j) (b i) -
        res {j} {i, j} (sub_pair_right i j) (b j) := by
  have n2 (i j : ι) : ({i, j} : Finset ι).Nonempty := Finset.insert_nonempty _ _
  have n1 (i : ι) : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  have n3 (i j k : ι) : ({i, j, k} : Finset ι).Nonempty := Finset.insert_nonempty _ _
  choose c' hc' using fun i j => (hb {i, j} (n2 i j)).2 ⟨c i j, hc i j⟩
  have hv (i j : ι) : (ψ _ (n2 i j) (c' i j) : P {i, j}) = c i j := congrArg Subtype.val (hc' i j)
  obtain ⟨b', hb'⟩ := hpairs c' fun i j k => by
    refine (hb _ (n3 i j k)).1 (Subtype.ext ?_)
    rw [map_add (f := _), Submodule.coe_add, hr _ _ (n2 i j) (n3 i j k), hr _ _ (n2 j k) (n3 i j k),
      hr _ _ (n2 i k) (n3 i j k), hv, hv, hv, hcoc]
  refine ⟨fun i => ψ _ (n1 i) (b' i), fun i => (ψ _ (n1 i) (b' i)).2, fun i j => ?_⟩
  rw [← hv i j, hb' i j, map_sub, Submodule.coe_sub, hr _ _ (n1 i) (n2 i j),
    hr _ _ (n1 j) (n2 i j)]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem serre_cech_pairs : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] [IsNoetherianRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, PolyGradedSMul ι (𝒢 S)] [∀ S, DirectSum.Decomposition (𝒢 S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h)) → (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (i : ι) (S : Finset ι), i ∈ S → Function.Bijective fun m : P S => (MvPolynomial.X i : MvPolynomial ι A) • m) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ i : ι, ∃ s : Finset (P {i}), ∀ m : P {i}, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι A) ^ k • m ∈ Submodule.span (MvPolynomial ι A) (s : Set (P {i}))) → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ c : ∀ i j : ι, P {i, j}, (∀ i j, c i j ∈ 𝒢 {i, j} t) → (∀ i j k, res {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) + res {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) = res {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i : ι, P {i}, (∀ i, b i ∈ 𝒢 {i} t) ∧ ∀ i j, c i j = res {i} {i, j} (sub_pair_left i j) (b i) - res {j} {i, j} (sub_pair_right i j) (b j) := by
  intro ι _ _ A _ _ P _ _ _ _ 𝒢 _ _ res hgr hid hcomp hbij hinj hsurj hfin
  have iI := GlobalTheory.CompanionTheory.FormalAlg.IterInj.iter_localisation_injective ι A P res hid hcomp hinj
  have iS := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.xProd_pow_smul_mem_range_res_iter ι A P res hid hcomp hsurj
  have g1 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_compatible_family_of_singleton ι A P res hid hcomp hinj hsurj
  have K1 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.smul_eq_zero_of_ev_eq_zero ι A P res hcomp iI
  have K2 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_xProd_pow_smul_eq_ev ι A P res hcomp iS g1
  letI : DirectSum.Decomposition (glueGr res 𝒢) := glueDec 𝒢 hgr
  have sat : ∀ i : ι, ∃ T : Finset (glue res), ∀ y : glue res, ∃ k : ℕ,
      (MvPolynomial.X i : MvPolynomial ι A) ^ k • y ∈
        Submodule.span (MvPolynomial ι A) (T : Set (glue res)) := by
    intro i
    refine GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat.saturated_fg_of_powerTorsion_ker_coker (MvPolynomial ι A) (MvPolynomial.X i) (glue res) (P {i})
      (ev res {i} (Finset.singleton_nonempty i)) (fun m hm => ?_) (fun f => ?_) (hfin i)
    · simpa [xProd] using K1 {i} _ m hm
    · simpa [xProd] using K2 {i} (Finset.singleton_nonempty i) f
  obtain ⟨K, hK, hKf, hb⟩ := exists_finite_sub ι A (glue res) (glueGr res 𝒢) sat
  letI := grSubDecomposition (glueGr res 𝒢) hK
  obtain ⟨t₀, ht₀⟩ := cubeComplex_grCube_exactAt_of_finite ι A K (grSub (glueGr res 𝒢) K) hKf
  refine ⟨t₀, fun t ht c hc hcoc => ?_⟩
  have hex := (cechComplex_exactAt_succ_iff _ 0).1
    ((cechComplex_exactAt_succ_iff_cube _ 0).2 (ht₀ t ht 2))
  obtain ⟨φ, hφb, hφr⟩ := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_homLoc_pieces_compatible ι A (glue res) (glueGr res 𝒢) P 𝒢 res (ev res)
    (isGradedMap_ev 𝒢 hgr) (fun I J hI hJ h m => res_ev hcomp hI hJ h m) hbij K1 K2 t
  refine pairs_of_cube (grCube ι (grSub (glueGr res 𝒢) K) t) (GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_coboundary_of_pairs_cocycle ι A _ hex)
    (fun S => 𝒢 S t) res
    (fun I hI => φ I hI ∘ₗ homLocMap (isGradedMap_subtype _ K) I t)
    (fun I hI => (hφb I hI).comp (hb t I hI)) (fun I J hI hJ h z => ?_) c hc hcoc
  have e : homLocMap (isGradedMap_subtype (glueGr res 𝒢) K) J t (Cube.res _ h z) =
      homLocRes _ h t (homLocMap (isGradedMap_subtype (glueGr res 𝒢) K) I t z) :=
    homLocMap_homLocRes _ h t z
  exact (congrArg (fun w => ((φ J hJ w : 𝒢 J t) : P J)) e).trans (hφr I J hI hJ h _)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedPiecesGeneratedByIdealGenerators
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

def liftSub {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e)
    (e : ℕ) (V : X.Opens) (W : Submodule Γ(X, V) Γ(gr hS e, V)) : Submodule Γ(X, V) Γ(P, V) where
  carrier := {t | ∃ x : Γ((lvl S e : X.Modules), V),
    (lvl S e).arrow.app V x = t ∧ (grπ hS e).app V x ∈ W}
  add_mem' := by
    rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    exact ⟨x + y, map_add _ _ _, by rw [map_add (f := _)]; exact W.add_mem hx hy⟩
  zero_mem' := ⟨0, map_zero _, by rw [map_zero]; exact W.zero_mem⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl, hx⟩
    exact ⟨c • x, Scheme.Modules.Hom.app_smul _ _ _,
      by rw [Scheme.Modules.Hom.app_smul]; exact W.smul_mem c hx⟩

lemma incl_arrow_app {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) (V : X.Opens) (y : Γ((lvl S (e + 1) : X.Modules), V)) :
    (lvl S e).arrow.app V ((incl hS e).app V y) = (lvl S (e + 1)).arrow.app V y := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, incl_arrow]

lemma incl_grπ_app {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) (V : X.Opens) (y : Γ((lvl S (e + 1) : X.Modules), V)) :
    (grπ hS e).app V ((incl hS e).app V y) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, incl_grπ]
  rfl

lemma pow_smul_le_secs_lvl {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} (hP : P.IsQuasicoherent) {S : ℕ → Subobject P}
    (hS : ClosedSys I P S) (e : ℕ) (U : X.affineOpens) {n : Γ(P, U)}
    (hn : n ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ e) • ⊤ :
      Submodule Γ(X, U) Γ(P, U))) : n ∈ secs (lvl S e) (U : X.Opens) := by
  cases e with
  | zero =>
    have : IsIso (lvl S 0).arrow := by
      change IsIso (⊤ : Subobject P).arrow
      infer_instance
    refine ⟨(inv (lvl S 0).arrow).app (U : X.Opens) n, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.inv_hom_id]
    simp
  | succ e =>
    have h1 : n ∈ secs (powSub I P (e + 1)) (U : X.Opens) := by
      rw [GlobalTheory.T.ideal_power_subobject_sections I P hP (e + 1) U U.2]
      exact hn
    exact (_root_.GlobalTheory.CompanionTheory.GE.le_iff_secs_subset _ _).1 (hS.pow_le e) U h1

theorem span_grT_eq_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} (hP : P.IsQuasicoherent) (S : ℕ → Subobject P)
    (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A) (hg : Ideal.span (Set.range g) = I)
    (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (e : ℕ) (U : X.affineOpens) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) = ⊤ := by
  set W := Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) with hW
  have hgen : ∀ i, ∀ n ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ e) • ⊤ :
      Submodule Γ(X, U) Γ(P, U)),
      toFunctions (A := A) (U : X.Opens) (g i) • n ∈ liftSub (anti hS) (e + 1) (U : X.Opens) W := by
    intro i n hn
    obtain ⟨v, hv⟩ := pow_smul_le_secs_lvl I hP (S := S) hS e U hn
    rw [← hv]
    refine ⟨(mulLvl (hr i) e).app (U : X.Opens) v, ?_, ?_⟩
    · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, mulLvl_arrow,
        Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, GroundTheory.Arith.SchemeCoh.smulHom_app_apply]
      congr 1
      exact restrictTop_restrict (homOfLE le_top) _
    · refine Submodule.subset_span (Set.mem_iUnion.2 ⟨i, (grπ (anti hS) e).app (U : X.Opens) v, ?_⟩)
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, grπ_grT,
        Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have hle : (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ (e + 1)) • ⊤ :
      Submodule Γ(X, U) Γ(P, U)) ≤ liftSub (anti hS) (e + 1) (U : X.Opens) W := by
    rw [pow_succ', Ideal.map_mul, Submodule.mul_smul, Submodule.smul_le]
    intro r hr' n hn
    rw [← hg, Ideal.map_span] at hr'
    induction hr' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := h
      exact hgen i n hn
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hb
  haveI : ((lvl S (e + 1 + 1) : Subobject P) : X.Modules).IsQuasicoherent := hS.qcoh (e + 1)
  haveI : ((lvl S (e + 1) : Subobject P) : X.Modules).IsQuasicoherent := hS.qcoh e
  have hsur : Function.Surjective ((grπ (anti hS) (e + 1)).app (U : X.Opens)) :=
    surjective_cokernel_π_app (incl (anti hS) (e + 1)) U.2
  rw [eq_top_iff]
  intro s _
  obtain ⟨x, rfl⟩ := hsur s
  have hq : ((powSub I P (e + 1) : Subobject P) : X.Modules).IsQuasicoherent :=
    haveI := hP
    (closedSys_pow I P).qcoh e
  have hx : (lvl S (e + 1)).arrow.app (U : X.Opens) x ∈
      secs (S (e + 1) ⊔ powSub I P (e + 1)) (U : X.Opens) := by
    rw [← hS.succ e]
    exact ⟨x, rfl⟩
  rw [(GlobalTheory.T.quasicoherent_sup_sections hP _ _ (hS.qcoh (e + 1)) hq).2 U U.2] at hx
  obtain ⟨_, ⟨y, rfl⟩, t, ht, hxy⟩ := hx
  rw [GlobalTheory.T.ideal_power_subobject_sections I P hP (e + 1) U U.2] at ht
  obtain ⟨x', hx't, hx'W⟩ := hle ht
  have hdec : x = (incl (anti hS) (e + 1)).app (U : X.Opens) y + x' := by
    apply injective_app_of_mono (lvl S (e + 1)).arrow (U : X.Opens)
    rw [map_add (f := _), hx't, hxy]
    exact congrArg (· + t) (incl_arrow_app (anti hS) (e + 1) (U : X.Opens) y).symm
  have hz : ∀ z : Γ((lvl S (e + 1 + 1) : X.Modules), (U : X.Opens)),
      (grπ (anti hS) (e + 1)).app (U : X.Opens)
        ((incl (anti hS) (e + 1)).app (U : X.Opens) z + x') =
      (grπ (anti hS) (e + 1)).app (U : X.Opens) x' := fun z => by
    rw [map_add (f := _), incl_grπ_app, zero_add]
  rw [hdec]
  exact Eq.mpr (congrArg (· ∈ W) (hz y)) hx'W

end GlobalTheory.CompanionTheory.GE.Step
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealElementMapsClosedSystemDown
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step.Maps

section Pull

variable {X : Scheme.{0}} {P : X.Modules}

lemma le_pullback_of_factors {Y T : Subobject P} (φ : P ⟶ P) (h : T.Factors (Y.arrow ≫ φ)) :
    Y ≤ (Subobject.pullback φ).obj T := by
  rw [Subobject.pullback_obj]
  exact Subobject.le_mk_of_comm
    (pullback.lift (T.factorThru (Y.arrow ≫ φ) h) Y.arrow (Subobject.factorThru_arrow _ _ _))
    (pullback.lift_snd _ _ _)

lemma factors_of_le_pullback {Y T : Subobject P} (φ : P ⟶ P)
    (h : Y ≤ (Subobject.pullback φ).obj T) : T.Factors (Y.arrow ≫ φ) := by
  rw [Subobject.pullback_obj] at h
  have e : Y.arrow ≫ φ = (Y.ofLE _ h ≫ (Subobject.underlyingIso (pullback.snd T.arrow φ)).hom ≫
      pullback.fst T.arrow φ) ≫ T.arrow := by
    rw [← Subobject.ofLE_arrow h, ← Subobject.underlyingIso_hom_comp_eq_mk]
    simp only [Category.assoc, pullback.condition]
  rw [e]
  exact Subobject.factors_comp_arrow _

lemma restrictTop_whole (r : Γ(X, ⊤)) : restrictTop (X := X) ⊤ r = r := by
  unfold GroundTheory.Arith.SchemeCoh.restrictTop
  simp

end Pull

section Mul

attribute [local instance] algebraOfOver

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
  [X.Over (Spec (.of A))]

lemma exists_smulHom_eq (P : X.Modules) {a : A} (ha : a ∈ I ^ 1) :
    ∃ m : P ⟶ idealPow I P 1, m ≫ idealPowι I P 1 = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
  rw [← span_idealGen (I ^ 1)] at ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ha
  have ht : (∑ i, GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) (c i)) ≫
      biproduct.ι (fun _ : Fin (idealGenNum (I ^ 1)) => P) i) ≫ idealSumMap P (I ^ 1) =
      GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    unfold idealSumMap
    rw [Preadditive.sum_comp]
    simp only [Category.assoc, biproduct.ι_desc, smulHom_comp_smulHom]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← smulHom_sum, ← hc, map_sum]
    simp only [smul_eq_mul, map_mul]
  refine ⟨kernel.lift _ (GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a)) ?_, ?_⟩
  · rw [← ht, Category.assoc, cokernel.condition, comp_zero]
  · exact kernel.lift_ι _ _ _

lemma factors_powSub (P : X.Modules) (n : ℕ) {a : A} (ha : a ∈ I ^ 1) :
    (powSub I P (n + 1)).Factors ((powSub I P n).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a)) := by
  show (Subobject.mk (idealPowι I P (n + 1))).Factors _
  rw [Subobject.mk_factors_iff]
  refine ⟨(Subobject.underlyingIso (idealPowι I P n)).hom ≫ idealPowMul I P (n := n) a ha, ?_⟩
  show ((Subobject.underlyingIso (idealPowι I P n)).hom ≫ idealPowMul I P (n := n) a ha) ≫
    idealPowι I P (n + 1) = _
  rw [Category.assoc, idealPowMul_ι, ← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  rfl

theorem mapsDown_toFunctions {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules} (_ : P.IsQuasicoherent)
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (a : A) (ha : a ∈ I) :
    MapsDown S (toFunctions (X := X) (A := A) ⊤ a) := by
  have ha1 : a ∈ I ^ 1 := by rwa [pow_one]
  have hr : toFunctions (X := X) (A := A) ⊤ a = algebraMap A Γ(X, ⊤) a := by
    simp only [GroundTheory.Arith.SchemeCoh.toFunctions, RingHom.comp_apply]
    exact restrictTop_whole _
  rw [hr]
  intro e
  cases e with
  | zero =>
    show (S 0).Factors ((⊤ : Subobject P).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P _)
    apply Subobject.factors_of_le _ (hS.pow_le 0)
    obtain ⟨m, hm⟩ := exists_smulHom_eq I P ha1
    show (Subobject.mk (idealPowι I P 1)).Factors _
    rw [Subobject.mk_factors_iff]
    refine ⟨(⊤ : Subobject P).arrow ≫ m, ?_⟩
    show ((⊤ : Subobject P).arrow ≫ m) ≫ idealPowι I P 1 = _
    rw [Category.assoc, hm]
  | succ e =>
    show (S (e + 1)).Factors ((S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P _)
    apply factors_of_le_pullback
    rw [hS.succ e]
    apply sup_le
    · apply le_pullback_of_factors
      rw [← GroundTheory.Arith.SchemeCoh.smulHom_comp]
      exact Subobject.factors_comp_arrow _
    · apply le_pullback_of_factors
      apply Subobject.factors_of_le _ (hS.pow_le (e + 1))
      exact factors_powSub I P (e + 1) ha1

end Mul

end GlobalTheory.CompanionTheory.GE.Step.Maps
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransport
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParIndBridge

theorem parInd_equiv_parabolicInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ W _ _ ρ
  have hP : parab k e = blockUpper k N β := _root_.GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper k e β hβ
  have h12 : ∀ {p : GL (Fin N) k}, p ∈ parab k e → p ∈ blockUpper k N β := fun h => hP ▸ h
  have h21 : ∀ {p : GL (Fin N) k}, p ∈ blockUpper k N β → p ∈ parab k e := fun h => hP ▸ h
  have hchar : ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β) (w : W),
      (deltaHalf k m (leviProj k e ⟨p, h1⟩) : ℂ) • ρ (leviProj k e ⟨p, h1⟩) w =
        sqrtModular k N β ⟨p, h2⟩ •
          ρ (φ.symm (GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩)) w := by
    intro p h1 h2 w
    have hL := _root_.GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq k e β hβ φ hφ p h1 h2
    rw [← hL, MulEquiv.symm_apply_apply, _root_.GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular k e β hβ φ hφ, hL,
      GroundTheory.Automorphic.Parabolic.sqrtModular_leviProj]
  let σ := ρ.comp φ.symm.toMonoidHom
  let E : IndSp e ρ ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.parabolicIndSpace k N β σ :=
    { toFun := fun f => ⟨f.1.1, fun p g => by
          have h := parInd_law e ρ f ⟨p.1, h21 p.2⟩ g
          refine h.trans ?_
          exact hchar p.1 (h21 p.2) p.2 _,
        GroundTheory.Automorphic.stabilizerOf (GlobalTheory.PRep.ind (parab k e)
          ((twist ρ (deltaHalf k m)).comp (leviProj k e))) f.1, f.2, fun x hx g => by
          have h := GroundTheory.Automorphic.mem_stabilizerOf.1 hx
          exact congrFun (congrArg Subtype.val h) g⟩
      invFun := fun f => ⟨⟨f.1, fun p g => by
          have h := f.2.1 ⟨p.1, h12 p.2⟩ g
          refine h.trans ?_
          exact (hchar p.1 p.2 (h12 p.2) _).symm⟩, by
          obtain ⟨-, K, hK, hf⟩ := f.2
          refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds (one_mem K)) fun x hx => ?_)
          exact Subtype.ext (funext fun g => hf x hx g)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Representation.Equiv.mk E fun g => LinearMap.ext fun f => Subtype.ext (funext fun x => rfl)⟩

end GlobalTheory.CompanionTheory.ParIndBridge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSequenceCoherent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

theorem isCoherent_biproduct {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → X.Modules) (hF : ∀ i, IsCoherent (F i)) : IsCoherent (⨁ F) := by
  haveI : ∀ i, SheafOfModules.IsQuasicoherent (F i) := fun i => (hF i).1
  refine ⟨isQuasicoherent_biproduct F, fun U hU => ?_⟩
  haveI : ∀ i, Module.Finite Γ(X, U) ((F i).presheaf.obj (Opposite.op U)) := fun i => (hF i).2 U hU
  let L : ∀ j, (F j).presheaf.obj (Opposite.op U) →ₗ[Γ(X, U)] (⨁ F).presheaf.obj (Opposite.op U) :=
    fun j =>
    { toFun := fun x => ConcreteCategory.hom (Scheme.Modules.Hom.app (biproduct.ι F j) U) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        exact Scheme.Modules.Hom.app_smul _ r x }
  let f : (∀ j, (F j).presheaf.obj (Opposite.op U)) →ₗ[Γ(X, U)] (⨁ F).presheaf.obj (Opposite.op U) :=
    ∑ j, (L j).comp (LinearMap.proj j)
  refine Module.Finite.of_surjective f ?_
  intro m
  refine ⟨fun j => ConcreteCategory.hom (Scheme.Modules.Hom.app (biproduct.π F j) U) m, ?_⟩
  rw [LinearMap.sum_apply]
  exact (biproduct_app_eq_sum F U m).symm

theorem isCoherent_kerSeq : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d →
    ∀ e, IsCoherent (KerSeq.kerSeq T d e) := by
  intro X _ k M T d h e
  haveI : SheafOfModules.IsQuasicoherent (M (d + e + 1)) := (h.coherent _).1
  exact isCoherent_kernel (KerSeq.sumMap T d e) (isCoherent_biproduct _ fun _ => h.coherent _)

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem kun_res {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃) (b₁ : ∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n)) (b₂ : ∀ a n, Function.Bijective ((resU (E.F₂ a) k₂).pull n)) (b₃ : ∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n)) : (E.Kun U₁ U₂ U₃ h₁ h₂ ↔ E.Kun U₁' U₂' U₃' h₁' h₂') :=
  _root_.GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (P' := fun a => CH.cx (U₁'.ι ⋙ E.F₁ a)) (Q' := fun a => CH.cx (U₂'.ι ⋙ E.F₂ a)) (T' := fun a => CH.cx (U₃'.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha) (fun {a a' c} ha => E.pr U₁' U₂' U₃' h₁' h₂' ha)
    (fun a => (resU (E.F₁ a) k₁).hom) (fun a => (resU (E.F₂ a) k₂).hom) (fun a => (resU (E.F₃ a) k₃).hom)
    b₁ b₂ b₃
    (fun ha _ _ _ h x y => _root_.GlobalTheory.CompanionTheory.KunGlue.pr_res E h₁ h₂ h₁' h₂' k₁ k₂ k₃ ha h x y)

end GlobalTheory.CompanionTheory.KunGlue
end

