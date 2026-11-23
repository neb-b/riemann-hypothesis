module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtale
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem diagComplHom_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  intro Z X f _ _
  have hopen : IsOpen (Set.range (pullback.diagonal f)) :=
    (pullback.diagonal f).isOpenEmbedding.isOpen_range
  have hcl : IsClosedImmersion (diagCompl f).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact hopen.isClosed_compl)
  unfold diagComplHom
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.EtC.Tr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAicLocalSubring
section
noncomputable section

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem exists_aic_local_subring (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] (φ : k →+* K) :
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  obtain ⟨D, m₀, hD, hm₀, hres, hint⟩ := _root_.GlobalTheory.exists_polySubring_maximal_integral k K φ
  obtain ⟨R, 𝔪, hR, h𝔪, hres', hfr, hic⟩ := _root_.GlobalTheory.integralClosure_maximal_residue_algClosed k K φ D m₀ hD hm₀ hres hint
  exact GlobalTheory.T.exists_local_subring_monic_roots_residue k K φ R 𝔪 hR h𝔪 hres' hfr hic

section Eqv
variable {R : Type} [CommRing R] (F : Shv R)

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_trans {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

theorem eqv_of_eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) :
    Eqv R g F := by
  intro n
  have h : ∀ x, pull R (f ≫ g) F n x = pull R f F n (pull R g F n x) := pull_comp R f g F n
  refine ⟨fun x y hxy => (hfg n).1 (by rw [h, h, hxy]), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (hfg n).2 (pull R f F n y)
  exact ⟨x, (hf n).1 (by rw [← h, hx])⟩

variable {X Y W S : Scheme.{0}} (p : X ⟶ S) (d : Y ⟶ S) (g : W ⟶ Y)

theorem fst_comp_eq : pullback.fst p (g ≫ d) =
    (pullbackLeftPullbackSndIso p d g).inv ≫ pullback.fst (pullback.snd p d) g ≫ pullback.fst p d := by
  rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_fst]

theorem eqv_fst_comp (h1 : Eqv R (sch.map (pullback.fst (pullback.snd p d) g)) F)
    (h2 : Eqv R (sch.map (pullback.fst p d)) F) : Eqv R (sch.map (pullback.fst p (g ≫ d))) F := by
  rw [fst_comp_eq, Functor.map_comp, Functor.map_comp]
  exact eqv_trans F (eqv_iso F _) (eqv_trans F h1 h2)

theorem eqv_fst_of_comp (h1 : Eqv R (sch.map (pullback.fst (pullback.snd p d) g)) F)
    (h2 : Eqv R (sch.map (pullback.fst p (g ≫ d))) F) : Eqv R (sch.map (pullback.fst p d)) F := by
  refine eqv_of_eqv_comp F h1 ?_
  have : pullback.fst (pullback.snd p d) g ≫ pullback.fst p d =
      (pullbackLeftPullbackSndIso p d g).hom ≫ pullback.fst p (g ≫ d) := by
    rw [pullbackLeftPullbackSndIso_hom_fst]
  rw [← Functor.map_comp, this, Functor.map_comp]
  exact eqv_trans F (eqv_iso F _) h2

end Eqv

theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem eqv_fieldChange (hE2 : E2) (hE3 : E3) (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K]
    [IsAlgClosed K] (φ : k →+* K) (hq : IsUnit (q : k)) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    [Smooth p] (i : ℤ) : Eqv (ZMod q) (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) (tw q i) := by
  obtain ⟨T, hφT, ⟨hloc, hT, hres⟩, hfr⟩ := exists_aic_local_subring k K φ
  let α : k →+* T := φ.codRestrict T (fun c => hφT ⟨c, rfl⟩)
  have hqT : IsUnit (q : T) := by simpa using hq.map α
  let a := Spec.map (CommRingCat.ofHom α)

  have hb : Function.Bijective ((IsLocalRing.residue T).comp α) := by
    refine ⟨(IsLocalRing.residue T).comp α |>.injective, fun y => ?_⟩
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, h, hc⟩ := hres t
    refine ⟨c, ?_⟩
    change IsLocalRing.residue T (α c) = IsLocalRing.residue T t
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have e : α c - t = -(t - ⟨φ c, h⟩) := by rw [neg_sub]; rfl
    rw [e]
    exact (IsLocalRing.maximalIdeal T).neg_mem hc
  haveI : IsIso (CommRingCat.ofHom ((IsLocalRing.residue T).comp α)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue T))
  have hra : r ≫ a = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue T).comp α)) := (spec_comp _ _).symm
  have hsp : Eqv (ZMod q) (sch.map (pullback.fst (pullback.snd p a) r)) (tw q i) :=
    eqv_spInc hE2 hT q hqT (pullback.snd p a) i
  have hXT : Eqv (ZMod q) (sch.map (pullback.fst p a)) (tw q i) := by
    refine eqv_fst_of_comp _ p a r hsp ?_
    rw [hra]
    exact eqv_iso _ _

  let e := IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K
  have hφ : φ = (e.toRingEquiv.toRingHom).comp ((algebraMap T (FractionRing T)).comp α) := by
    ext c
    simp only [RingHom.comp_apply]
    rw [show e.toRingEquiv.toRingHom (algebraMap T (FractionRing T) (α c)) = e (algebraMap T (FractionRing T) (α c)) from rfl,
      AlgEquiv.commutes]
    rfl
  haveI : IsIso (CommRingCat.ofHom (e.toRingEquiv.toRingHom)) := e.toRingEquiv.toCommRingCatIso.isIso_hom
  have hgen : Eqv (ZMod q) (sch.map (pullback.fst (pullback.snd p a)
      (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))))) (tw q i) :=
    eqv_genInc hE3 hT q hqT (pullback.snd p a) i
  rw [hφ, spec_comp, spec_comp]
  refine eqv_fst_comp _ p _ _ (eqv_iso _ _) (eqv_fst_comp _ p a _ hgen hXT)

end GlobalTheory.GenusTwoPureComparison.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffine
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem ringHom_count_bound {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : g.Finite) : ∃ n : ℕ, ∀ (K : Type) [Field K] (ψ : A →+* K) (φ : Fin (n + 1) → (B →+* K)),
      (∀ j, (φ j).comp g = ψ) → ¬ Function.Injective φ := by
  letI := g.toAlgebra
  have hfin : Module.Finite A B := hg
  obtain ⟨S, hS⟩ := hfin.fg_top
  refine ⟨S.card, fun K _ ψ φ hφ hinj => ?_⟩
  let L : (Fin (S.card + 1) → K) →ₗ[K] (S → K) :=
    { toFun := fun c s => ∑ j, c j * φ j (s : B)
      map_add' := by intro c d; funext s; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a c; funext s; simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hcS : ∀ s ∈ S, ∑ j, c j * φ j s = 0 := by
    intro s hs
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨s, hs⟩
    simpa [L] using this
  have hall : ∀ b : B, ∑ j, c j * φ j b = 0 := by
    intro b
    have hb : b ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact hcS x hx
    | zero => simp
    | add x y _ _ hx hy => simp [mul_add, Finset.sum_add_distrib, hx, hy]
    | smul a x _ hx =>
      have e : ∀ j, φ j (a • x) = ψ a * φ j x := by
        intro j
        rw [Algebra.smul_def, map_mul, ← hφ j]
        rfl
      simp only [e]
      calc ∑ j, c j * (ψ a * φ j x) = ψ a * ∑ j, c j * φ j x := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hx, mul_zero]
  have hli := (linearIndependent_monoidHom B K).comp (fun j => (φ j : B →* K))
    (fun i j h => hinj (RingHom.ext fun b => DFunLike.congr_fun h b))
  have := (Fintype.linearIndependent_iff.1 hli) c (by
    funext b
    simpa [Finset.sum_apply, smul_eq_mul] using hall b)
  exact hc0 (funext this)

theorem finite_fibrePointsLE_of_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X],
    ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := by
  intro Z X f _ _
  haveI := isAffine_of_isAffineHom f
  obtain ⟨n, hn⟩ := ringHom_count_bound f.appTop.hom f.finite_appTop
  refine ⟨n, fun K _ y s hs hinj => ?_⟩
  refine hn K (y.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    (fun j => ((s j).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) (fun j => ?_) ?_
  · rw [← hs j, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [CommRingCat.hom_comp]
  · intro i j h
    apply hinj
    apply ext_of_isAffine
    exact (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1 (CommRingCat.hom_ext h)

end GlobalTheory.EtC.Tr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPr
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem fibrePointsLE_diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ)
    (h : FibrePointsLE f (n + 1)) : FibrePointsLE (diagComplHom f) n := by
  intro K _ y s hs hinj
  set t : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z) := fun j => s j ≫ (diagCompl f).ι ≫ pullback.fst f f
    with ht
  have hsnd : ∀ j, s j ≫ (diagCompl f).ι ≫ pullback.snd f f = y := fun j => by
    simpa [diagComplHom] using hs j
  have htf : ∀ j, t j ≫ f = y ≫ f := fun j => by
    simp only [ht, Category.assoc, pullback.condition]
    rw [← hsnd j]
    simp only [Category.assoc]
  have hne : ∀ j, t j ≠ y := by
    intro j hj
    have heq : s j ≫ (diagCompl f).ι = y ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp [← hj, ht]
      · simp [hsnd j]
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
    have h1 : (s j ≫ (diagCompl f).ι).base x ∈ diagCompl f := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    rw [heq] at h1
    exact h1 ⟨_, rfl⟩
  apply h K (y ≫ f) (Fin.cons y t)
  · intro j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simpa using htf j
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij.symm (hne _)
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij (hne _)
    · rename_i i j
      simp only [Fin.cons_succ] at hij
      congr 1
      apply hinj
      rw [← cancel_mono (diagCompl f).ι]
      apply pullback.hom_ext
      · simpa [ht] using hij
      · simp [hsnd i, hsnd j]

end GlobalTheory.EtC.Tr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeHomExtOfCoveringStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeSch_hom_ext_of_etale_covering : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (φ ψ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F) (T : Sieve S), T ∈ Scheme.etaleTopology S → (∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ φ = (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ ψ) → φ = ψ := by
  first | (exact @GlobalTheory.EtC.Tr.free_hom_ext_of_covering) | (exact GlobalTheory.EtC.Tr.free_hom_ext_of_covering) | (intros; apply GlobalTheory.EtC.Tr.free_hom_ext_of_covering  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeHomGlueOfCoveringStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_freeSch_hom_glue_of_etale_covering : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S), T ∈ Scheme.etaleTopology S → ∀ (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F)), (∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V), (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) → ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v), (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv := by
  first | (exact @GlobalTheory.EtC.Tr.free_hom_glue_of_covering) | (exact GlobalTheory.EtC.Tr.free_hom_glue_of_covering) | (intros; apply GlobalTheory.EtC.Tr.free_hom_glue_of_covering  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeSheafSumSectionsEqOfTwoSplittings
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr.SumEq

end GlobalTheory.EtC.Tr.SumEq

namespace GlobalTheory.EtC.Tr

open CategoryTheory Limits AlgebraicGeometry in
private lemma exists_sigma_ι_apply_eq_of_finite_coprod {σ : Type} [Finite σ] (g : σ → Scheme.{0}) (q : ↥(∐ g)) :
    ∃ k a, (Sigma.ι g k) a = q :=
  (sigmaOpenCover g).exists_eq q

open CategoryTheory Limits AlgebraicGeometry in
private lemma exists_pullback_lift_apply_eq_of_isIso_sigmaDesc {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    (p : ↥(pullback f y)) : ∃ k a, pullback.lift (s k) (𝟙 V) (by simp [hc k]) a = p := by
  obtain ⟨q, rfl⟩ := Scheme.Hom.surjective
    (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) p
  obtain ⟨k, a, rfl⟩ := exists_sigma_ι_apply_eq_of_finite_coprod _ q
  exact ⟨k, a, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩

open CategoryTheory Limits AlgebraicGeometry in
private lemma isOpenImmersion_pullback_lift_of_isIso_sigmaDesc {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)] (k : Fin m) :
    IsOpenImmersion (pullback.lift (s k) (𝟙 V) (by simp [hc k]) : V ⟶ pullback f y) := by
  rw [← Sigma.ι_desc (fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
    (j : Fin m) → V ⟶ pullback f y) k]
  infer_instance

open CategoryTheory Limits AlgebraicGeometry in
private lemma pullback_snd_lift_id_apply {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} (t : V ⟶ Z)
    (h : t ≫ f = 𝟙 V ≫ y) (a : ↥V) : pullback.snd f y (pullback.lift t (𝟙 V) h a) = a := by
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

open CategoryTheory Limits AlgebraicGeometry in
private lemma index_eq_of_pullback_lift_apply_eq {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    {j j' : Fin m} (a b : ↥V)
    (h : (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) a =
      (pullback.lift (s j') (𝟙 V) (by simp [hc j']) : V ⟶ pullback f y) b) :
    j = j' := by
  have h1 : (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) (Sigma.ι (fun _ : Fin m => V) j a) =
      (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) (Sigma.ι (fun _ : Fin m => V) j' b) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Sigma.ι_desc]
    exact h
  have h2 : (Sigma.ι (fun _ : Fin m => V) j) a = (Sigma.ι (fun _ : Fin m => V) j') b :=
    Scheme.Hom.injective _ h1
  exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => V) j j' a b).mp (by convert h2))

open CategoryTheory Limits AlgebraicGeometry in
private lemma injective_of_pullback_lift_apply_eq_of_isIso {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m m' : ℕ}
    {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y) (hc' : ∀ j, s' j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    (x : ↥V) (K : Fin m → Fin m') (A : Fin m → ↥V)
    (hKA : ∀ j, (pullback.lift (s' (K j)) (𝟙 V) (by simp [hc' (K j)]) : V ⟶ pullback f y) (A j) =
      (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) x) : Function.Injective K := by
  intro j j' hjj
  have hA : ∀ i, A i = x := fun i => by
    have := congrArg (pullback.snd f y) (hKA i)
    rwa [pullback_snd_lift_id_apply, pullback_snd_lift_id_apply] at this
  refine index_eq_of_pullback_lift_apply_eq hc x x ?_
  rw [← hKA j, ← hKA j', hA, hA]
  have key : ∀ k k' : Fin m', k = k' →
      (pullback.lift (s' k) (𝟙 V) (by simp [hc' k]) : V ⟶ pullback f y) x =
      (pullback.lift (s' k') (𝟙 V) (by simp [hc' k']) : V ⟶ pullback f y) x := by
    rintro k _ rfl
    rfl
  exact key _ _ hjj


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings : ∀ (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X}
    {m m' : ℕ} {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)}, _root_.GlobalTheory.EtC.Tr.SplitBy f y s → _root_.GlobalTheory.EtC.Tr.SplitBy f y s' →
    ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s j)) = ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s' j)) := by
  intro R _ Z X V f y m m' s s' hs hs'
  obtain ⟨hc, hi⟩ := hs
  obtain ⟨hc', hi'⟩ := hs'
  let T : Sieve V :=
    { arrows := fun W v => (_root_.GlobalTheory.EtC.free R).map (yoneda.map v) ≫
          ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s j)) =
        (_root_.GlobalTheory.EtC.free R).map (yoneda.map v) ≫
          ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s' j))
      downward_closed := by
        intro W W' v hv g
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hv] }
  refine _root_.GlobalTheory.EtC.Tr.free_hom_ext_of_covering R (_root_.GlobalTheory.EtC.Tr.freeSch R Z) _ _ T ?_ (fun W v hv => hv)
  apply Scheme.zariskiTopology_le_etaleTopology
  choose K A hKA using fun (x : ↥V) (j : Fin m) =>
    exists_pullback_lift_apply_eq_of_isIso_sigmaDesc hc' ((pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) x)
  choose K' A' hKA' using fun (x : ↥V) (k : Fin m') =>
    exists_pullback_lift_apply_eq_of_isIso_sigmaDesc hc ((pullback.lift (s' k) (𝟙 V) (by simp [hc' k]) : V ⟶ pullback f y) x)
  have hopen := isOpenImmersion_pullback_lift_of_isIso_sigmaDesc hc'
  let U : ↥V → V.Opens := fun x =>
    ⟨⋂ j, (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) ⁻¹'
        Set.range (pullback.lift (s' (K x j)) (𝟙 V) (by simp [hc' (K x j)]) : V ⟶ pullback f y),
      isOpen_iInter_of_finite fun j =>
        (Scheme.Hom.isOpenEmbedding _).isOpen_range.preimage (Scheme.Hom.continuous _)⟩
  have hxU : ∀ x, x ∈ U x := fun x => Set.mem_iInter.mpr fun j => ⟨A x j, hKA x j⟩
  have hagree : ∀ x, T ((U x).ι) := by
    intro x
    have hinj := injective_of_pullback_lift_apply_eq_of_isIso hc hc' x (K x) (A x) (hKA x)
    have hinj' := injective_of_pullback_lift_apply_eq_of_isIso hc' hc x (K' x) (A' x) (hKA' x)
    have hbij : Function.Bijective (K x) := (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) (Fintype.card_le_of_injective _ hinj')⟩
    have hsec : ∀ j, (U x).ι ≫ s j = (U x).ι ≫ s' (K x j) := by
      intro j
      have hr : Set.range ⇑((U x).ι ≫ (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y)) ⊆
          Set.range (pullback.lift (s' (K x j)) (𝟙 V) (by simp [hc' (K x j)]) : V ⟶ pullback f y) := by
        rintro _ ⟨w, rfl⟩
        have hw : (U x).ι w ∈ U x := by
          have hw' : (U x).ι w ∈ Set.range (U x).ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at hw'
        rw [Scheme.Hom.comp_apply]
        exact Set.mem_iInter.mp hw j
      have hg := IsOpenImmersion.lift_fac _ _ hr
      have hgι : IsOpenImmersion.lift _ _ hr = (U x).ι := by
        have := congrArg (· ≫ pullback.snd f y) hg
        simp only [Category.assoc, pullback.lift_snd, Category.comp_id] at this
        exact this
      rw [hgι] at hg
      have := congrArg (· ≫ pullback.fst f y) hg
      simp only [Category.assoc, pullback.lift_fst] at this
      exact this.symm
    show (_root_.GlobalTheory.EtC.free R).map (yoneda.map (U x).ι) ≫ _ =
      (_root_.GlobalTheory.EtC.free R).map (yoneda.map (U x).ι) ≫ _
    rw [Preadditive.comp_sum, Preadditive.comp_sum]
    refine Fintype.sum_equiv (Equiv.ofBijective _ hbij) _ _ fun j => ?_
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      Equiv.ofBijective_apply, hsec j]
  rw [show Scheme.zariskiTopology = Scheme.grothendieckTopology @IsOpenImmersion from rfl,
    Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers V (fun x => (U x : Scheme.{0})) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hxU x⟩, rfl⟩), ?_⟩
  rintro W _ ⟨x⟩
  exact hagree x

end GlobalTheory.EtC.Tr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsEmptyOfFibreFieldPointsCardLEZero
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem isEmpty_of_fibrePointsLE_zero {Z X : Scheme.{0}} (f : Z ⟶ X) (h : FibrePointsLE f 0) :
    IsEmpty Z := by
  refine ⟨fun z => ?_⟩
  exact h (Z.residueField z) (Z.fromSpecResidueField z ≫ f) (fun _ => Z.fromSpecResidueField z)
    (fun _ => rfl) (fun a b _ => Fin.subsingleton_one.elim a b)

end GlobalTheory.EtC.Tr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilitiesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_char_compatibilities : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h) (s : ℝ), (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧ (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧ a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧ (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧ (WD.lpZero (h := h)).lpChar c = WD.lpZero (h := h) ∧ (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) := by
  exact @GlobalTheory.WeilDeligne.lpChar_laws_closed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataCrystallineAdmissibleStatement
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_data_crystalline_admissible : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ), Module.Finite LL (FiniteCohomology PD ρ) → ∀ n : ℕ, Module.length O (↥(latticeFiniteCocycles PD L) ⧸ ((latticeFiniteCocycles PD L).map ((((PD.p : ℕ) : O) ^ n) • (LinearMap.id : (G → V) →ₗ[O] (G → V))) ⊔ latticeCoboundaries L).comap (latticeFiniteCocycles PD L).subtype) ≤ (n : ℕ∞) * (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * lenOl PD (O := O) + Module.length O ↥(Representation.invariants (repD L)) := by
  first | exact @GlobalTheory.length_H1fT_modPow_le | exact GlobalTheory.length_H1fT_modPow_le | (intros; apply GlobalTheory.length_H1fT_modPow_le <;> assumption)
end

