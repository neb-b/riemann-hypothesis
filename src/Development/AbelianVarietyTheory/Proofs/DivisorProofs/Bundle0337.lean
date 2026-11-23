module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelPreservesCofilteredLimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

lemma cechLev_π {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) (j : Fin (k.unop.len + 1)) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫ WidePullback.π (fun _ => g.hom) j =
      WidePullback.π (fun _ => f.hom) j ≫ F.left := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_π]

lemma cechLev_base {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫
        WidePullback.base (fun _ : Fin (k.unop.len + 1) => g.hom) =
      WidePullback.base (fun _ => f.hom) ≫ F.right := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_base]

theorem cech_level_limit (I : Type) [SmallCategory I] [IsCofiltered I] (A : I ⥤ Arrow PSh) (cA : Cone A)
    (hl : IsLimit (Arrow.leftFunc.mapCone cA)) (_hA : ∀ ⦃i j : I⦄ (f : i ⟶ j), IsIso (A.map f).right)
    (hR : ∀ i, IsIso (cA.π.app i).right) (k : SimplexCategoryᵒᵖ) :
    Nonempty (IsLimit (((evaluation _ PSh).obj k).mapCone (SimplicialObject.cechNerve.mapCone cA))) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  let L : ∀ (s : Cone ((A ⋙ SimplicialObject.cechNerve) ⋙ (evaluation _ PSh).obj k))
      (j : Fin (k.unop.len + 1)), s.pt ⟶ cA.pt.left := fun s j =>
    hl.lift
      { pt := s.pt
        π :=
          { app := fun i => s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j
            naturality := by
              intro i i' f
              have h := s.w f
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                Functor.comp_obj, Arrow.leftFunc_obj, Functor.comp_map, Arrow.leftFunc_map] at h ⊢
              rw [← h]
              exact (Category.assoc _ _ _).trans
                ((congrArg (s.π.app i ≫ ·) (cechLev_π (A.map f) k j)).trans (Category.assoc _ _ _).symm) } }
  have hLfac : ∀ s j i, L s j ≫ (cA.π.app i).left =
      s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j := by
    intro s j i
    exact hl.fac _ i
  have hLbase : ∀ s j i, L s j ≫ cA.pt.hom ≫ (cA.π.app i).right =
      s.π.app i ≫ WidePullback.base (fun _ : Fin (k.unop.len + 1) => (A.obj i).hom) := by
    intro s j i
    have hw : (cA.π.app i).left ≫ (A.obj i).hom = cA.pt.hom ≫ (cA.π.app i).right := Arrow.w (cA.π.app i)
    rw [← hw, ← Category.assoc, hLfac]
    exact (Category.assoc _ _ _).trans (congrArg (s.π.app i ≫ ·) (WidePullback.π_arrow _ j))
  refine ⟨{ lift := fun s => WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) (fun j => by
              rw [← cancel_mono (cA.π.app i₀).right, Category.assoc, Category.assoc, hLbase, hLbase])
            fac := ?_
            uniq := ?_ }⟩
  · intro s i
    apply WidePullback.hom_ext
    · intro j
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_π (cA.π.app i) k j)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).left) (WidePullback.lift_π _ _ _ _ j)).trans ?_
      exact hLfac s j i
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_base (cA.π.app i) k)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).right) (WidePullback.lift_base _ _ _ _)).trans ?_
      exact (Category.assoc _ _ _).trans (hLbase s 0 i)
  · intro s m hm
    have hmj : ∀ j, m ≫ WidePullback.π (fun _ => cA.pt.hom) j = L s j := by
      intro j
      apply hl.hom_ext
      intro i
      refine Eq.trans ?_ (hLfac s j i).symm
      refine Eq.trans ?_ (congrArg (· ≫ WidePullback.π (fun _ => (A.obj i).hom) j) (hm i))
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (cechLev_π (cA.π.app i) k j).symm
    apply WidePullback.hom_ext
    · intro j
      exact (hmj j).trans (WidePullback.lift_π _ _ _ _ j).symm
    · refine Eq.trans ?_ (WidePullback.lift_base _ _ _ _).symm
      refine Eq.trans ?_ (congrArg (· ≫ cA.pt.hom) (hmj 0))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (WidePullback.π_arrow _ 0).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta : ∀ (R : Type) [CommRing R] , (∀ E : Spc, ((chains R).obj E).IsStrictlyLE 0) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (p : ℕ), ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom = (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p)))) ∧ ∀ (E : Spc) (p : ℕ), (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
  first | (exact @GlobalTheory.EtC.chains_basic) | (exact GlobalTheory.EtC.chains_basic) | (intros; apply GlobalTheory.EtC.chains_basic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
open Simplicial SimplicialObject.Augmented
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EtC.CechSplit

variable {P Q : PSh} (φ : P ⟶ Q) (hφ : ∀ U, Function.Surjective (φ.app U)) (U : Scheme.{0})

def lft (c : yoneda.obj U ⟶ Q) : yoneda.obj U ⟶ P :=
  yonedaEquiv.symm (hφ (op U) (yonedaEquiv c)).choose

lemma lft_comp (c : yoneda.obj U ⟶ Q) : lft φ hφ U c ≫ φ = c := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, lft, Equiv.apply_symm_apply]
  exact (hφ (op U) (yonedaEquiv c)).choose_spec

def sf (n : ℕ) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n + 1⦌) :=
  WidePullback.lift (x ≫ WidePullback.base _)
    (Fin.cases (lft φ hφ U (x ≫ WidePullback.base _)) (fun i => x ≫ WidePullback.π _ i))
    (fun i => by cases i using Fin.cases <;> simp [lft_comp])

def sf' (c : yoneda.obj U ⟶ Q) : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋0⦌) :=
  lft φ hφ U c ≫ WidePullback.lift φ (fun _ => 𝟙 P) (by simp)

lemma sf'_comp_aug (c : yoneda.obj U ⟶ Q) : sf' φ hφ U c ≫ (Arrow.mk φ).augmentedCechNerve.hom.app (op ⦋0⦌) = c := by
  simp [sf', lft_comp]

lemma sf_zero_comp_δ_one (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋0⦌)) :
    sf φ hφ U 0 x ≫ (Arrow.mk φ).cechNerve.δ 1 =
      sf' φ hφ U (x ≫ (Arrow.mk φ).augmentedCechNerve.hom.app (op ⦋0⦌)) := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf, sf']
  apply WidePullback.hom_ext
  · intro j
    fin_cases j
    simp
  · simp [lft_comp]

lemma sf_comp_δ_zero (n : ℕ) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    sf φ hφ U n x ≫ (Arrow.mk φ).cechNerve.δ 0 = x := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf]
  ext j
  · simp
  · simp

lemma sf_succ_comp_δ_succ (n : ℕ) (i : Fin (n + 2)) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n + 1⦌)) :
    sf φ hφ U (n + 1) x ≫ (Arrow.mk φ).cechNerve.δ i.succ = sf φ hφ U n (x ≫ (Arrow.mk φ).cechNerve.δ i) := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf]
  ext j
  · induction j using Fin.cases <;> simp
  · simp

lemma sf_comp_σ_succ (n : ℕ) (i : Fin (n + 1)) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    sf φ hφ U n x ≫ (Arrow.mk φ).cechNerve.σ i.succ = sf φ hφ U (n + 1) (x ≫ (Arrow.mk φ).cechNerve.σ i) := by
  dsimp [SimplicialObject.σ, SimplexCategory.σ, sf]
  ext j
  · induction j using Fin.cases <;> simp
  · simp

def ed : ExtraDegeneracy (((whiskering _ _).obj (coyoneda.obj (op (yoneda.obj U)))).obj
    (Arrow.mk φ).augmentedCechNerve) where
  s' := TypeCat.ofHom (sf' φ hφ U)
  s n := TypeCat.ofHom (sf φ hφ U n)
  s'_comp_ε := by ext c; exact sf'_comp_aug φ hφ U c
  s₀_comp_δ₁ := by ext x; exact sf_zero_comp_δ_one φ hφ U x
  s_comp_δ₀ n := by ext x; exact sf_comp_δ_zero φ hφ U n x
  s_comp_δ n i := by ext x; exact sf_succ_comp_δ_succ φ hφ U n i x
  s_comp_σ n i := by ext x; exact sf_comp_σ_succ φ hφ U n i x

def toConst : (Arrow.mk φ).augmentedCechNerve ⟶ SimplicialObject.Augmented.const.obj Q where
  left := (Arrow.mk φ).augmentedCechNerve.hom
  right := 𝟙 Q
  w := by ext : 1; simp

include hφ in
theorem free_sections_quasiIso (R : Type) [CommRing R] :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map
      (((SimplicialObject.whiskering _ _).obj ((evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙
        ModuleCat.free (ULift.{1} R))).map
          (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from (Arrow.mk φ).augmentedCechNerve.hom))) := by
  let G : PSh ⥤ ModuleCat.{1} (ULift.{1} R) :=
    (evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R)
  let X := (Arrow.mk φ).augmentedCechNerve
  let e1 : coyoneda.obj (op (yoneda.obj U)) ⋙ ModuleCat.free (ULift.{1} R) ≅ G :=
    Functor.isoWhiskerRight (largeCurriedYonedaLemma.app (op U)) (ModuleCat.free (ULift.{1} R))
  let ed0 : ExtraDegeneracy (((whiskering _ _).obj (coyoneda.obj (op (yoneda.obj U)) ⋙
      ModuleCat.free (ULift.{1} R))).obj X) := (ed φ hφ U).map (ModuleCat.free (ULift.{1} R))
  let ed1 : ExtraDegeneracy (((whiskering _ _).obj G).obj X) :=
    ed0.ofIso (((whiskering _ _).mapIso e1).app X)
  have h1 := ed1.homotopyEquiv.quasiIso_hom
  have h2 := ((ExtraDegeneracy.const Q).map G).homotopyEquiv.quasiIso_hom
  have nat := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := ModuleCat.{1} (ULift.{1} R))).naturality
    (((whiskering _ _).obj G).map (toConst φ))
  have hp : (point ⋙ ChainComplex.single₀ _).map (((whiskering _ _).obj G).map (toConst φ)) = 𝟙 _ := by
    change (ChainComplex.single₀ _).map (G.map (𝟙 Q)) = 𝟙 _
    rw [G.map_id, CategoryTheory.Functor.map_id]
  rw [hp, Category.comp_id] at nat
  haveI : QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q))) := h2
  rw [← quasiIso_iff_comp_right _ (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q)))]
  have key : QuasiIso ((drop ⋙ AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map
        (((whiskering _ _).obj G).map (toConst φ)) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q))) := by
    rw [nat]; exact h1
  exact key

end GlobalTheory.EtC.CechSplit

namespace GlobalTheory.EtC

theorem chains_cechNerve_quasiIso_of_surjective : ∀ (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q),
    (∀ U, Function.Surjective (φ.app U)) →
      QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from
        (Arrow.mk φ).augmentedCechNerve.hom)) := by
  intro R _ P Q φ hφ
  exact chains_quasiIso_of_sections R _ (fun U => CechSplit.free_sections_quasiIso φ hφ U R)

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosurePrimeRegularHeight
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_prime_regular_height : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∀ (Q : Ideal (GlobalTheory.KeyOriginNoeth.closure A R D)) [Q.IsPrime],
      (∀ a : A, a ≠ 0 → algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a) ∉ Q) →
      Algebra.IsEtaleAt R Q := by
  first | (exact @GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint) | (exact GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint) | (intros; apply GlobalTheory.KeyOriginNoeth.isEtaleAt_closure_of_disjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycleCompHomComplex_assoc_on_cohomology_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  first | (exact @GlobalTheory.cocycle_comp_assoc_classes) | (exact GlobalTheory.cocycle_comp_assoc_classes) | (intros; apply GlobalTheory.cocycle_comp_assoc_classes  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleEqChainMapShiftCompatClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_eq_chainMap_shift_compat_classes : ∀ (R : Type) [CommRing R] (L C : Cx R) (d : ℤ) (ψ : Cocycle L C d), ∃ (L' : Cx R) (g : L' ⟶ C), (∀ m, L.IsStrictlyGE m → L'.IsStrictlyGE (m + d)) ∧ ((∀ n, CategoryTheory.Injective (L.X n)) → ∀ n, CategoryTheory.Injective (L'.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : CohomologyClass K L (n - d) ≃ CohomologyClass K L' n, ∀ a, cpush K g n (e a) = cpost K ψ (n - d) n (by omega) a := by
  first | (exact @GlobalTheory.EtC.cocycle_as_chainMap_of_shift) | (exact GlobalTheory.EtC.cocycle_as_chainMap_of_shift) | (intros; apply GlobalTheory.EtC.cocycle_as_chainMap_of_shift  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefVFContDiffOn
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.VFComp

variable {d : ℕ}

theorem dw_contDiffOn {U : Set (E d)} (hU : IsOpen U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) :
    ∀ w : List (Fin d), ContDiffOn ℝ ∞ (dw w u) U
  | [] => hu
  | j :: w => by
    have h : ContDiffOn ℝ ∞ (fderiv ℝ (dw w u)) U :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen (𝕜 := ℝ) hU).mp (dw_contDiffOn hU hu w)).2
    exact h.clm_apply contDiffOn_const

theorem diffAt_of {U : Set (E d)} (hU : IsOpen U) {f : E d → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    {x : E d} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  (((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hf).1).differentiableAt (hU.mem_nhds hx)

def coefB (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (n : ℕ) (w : Fin n → Fin d) (x : E d) : ℂ :=
  if n ≤ m then ∑ j, c j x * fderiv ℝ (a n w) x (ev j) else 0

def coefA (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ) :
    (n : ℕ) → (Fin n → Fin d) → E d → ℂ
  | 0, _ => fun _ => 0
  | k + 1, w => fun x => if k ≤ m then c (w 0) x * a k (Fin.tail w) x else 0

def coefVF (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (n : ℕ) (w : Fin n → Fin d) (x : E d) : ℂ :=
  coefA m a c n w x + coefB m a c n w x

theorem sum_cons {M : Type*} [AddCommMonoid M] (k : ℕ) (g : (Fin (k + 1) → Fin d) → M) :
    ∑ w : Fin (k + 1) → Fin d, g w = ∑ j : Fin d, ∑ w : Fin k → Fin d, g (Fin.cons j w) := by
  rw [← (Fin.consEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type]
  rfl

end GlobalTheory.VFComp

namespace GlobalTheory.VFComp
variable {d : ℕ}

theorem coefVF_contDiffOn {U : Set (E d)} (hU : IsOpen U) (m : ℕ)
    (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) (hc : ∀ j, ContDiffOn ℝ ∞ (c j) U) (n : ℕ) (w : Fin n → Fin d) :
    ContDiffOn ℝ ∞ (coefVF m a c n w) U := by
  have hB : ContDiffOn ℝ ∞ (coefB m a c n w) U := by
    unfold coefB
    split_ifs
    · exact ContDiffOn.sum fun j _ => (hc j).mul (dw_contDiffOn hU (ha n w) [j])
    · exact contDiffOn_const
  have hA : ContDiffOn ℝ ∞ (coefA m a c n w) U := by
    cases n with
    | zero => exact contDiffOn_const
    | succ k =>
      show ContDiffOn ℝ ∞ (fun x => if k ≤ m then c (w 0) x * a k (Fin.tail w) x else 0) U
      split_ifs
      · exact (hc _).mul (ha _ _)
      · exact contDiffOn_const
  exact hA.add hB

theorem symb_coefVF (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (x ξ : E d) : symb (m + 1) (coefVF m a c) x ξ = (∑ j, c j x * ((ξ j : ℝ) : ℂ)) * symb m a x ξ := by
  unfold symb coefVF coefB
  rw [sum_cons, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [coefA, le_refl, if_true, show ¬ (m + 1 ≤ m) by omega, if_false, add_zero, Fin.cons_zero,
    Fin.tail_cons, Fin.prod_univ_succ, Fin.cons_succ]
  ring

end GlobalTheory.VFComp

namespace GlobalTheory.VFComp
variable {d : ℕ}

theorem fderiv_apOp {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) {x : E d} (hx : x ∈ U)
    (j : Fin d) :
    fderiv ℝ (apOp m a u) x (ev j) = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      (fderiv ℝ (a n w) x (ev j) * dw (List.ofFn w) u x + a n w x * dw (j :: List.ofFn w) u x) := by
  have hd := HasFDerivAt.sum (u := Finset.range (m + 1)) (x := x)
    (A := fun n => ∑ w : Fin n → Fin d, a n w * dw (List.ofFn w) u) fun n _ =>
      HasFDerivAt.sum (u := Finset.univ) fun w _ =>
        (diffAt_of hU (ha n w) hx).hasFDerivAt.mul
          (diffAt_of hU (dw_contDiffOn hU hu (List.ofFn w)) hx).hasFDerivAt
  have he : apOp m a u = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, a n w * dw (List.ofFn w) u := by
    funext y
    simp [apOp, Finset.sum_apply]
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [dw]
  ring

end GlobalTheory.VFComp

namespace GlobalTheory.VFComp
variable {d : ℕ}

theorem apOp_coefVF {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (c : Fin d → E d → ℂ) (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U)
    {x : E d} (hx : x ∈ U) :
    ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) = apOp (m + 1) (coefVF m a c) u x := by
  have hL : ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) =
      (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (∑ j, c j x * fderiv ℝ (a n w) x (ev j)) * dw (List.ofFn w) u x) +
      ∑ n ∈ Finset.range (m + 1), ∑ j : Fin d, ∑ w : Fin n → Fin d,
        c j x * a n w x * dw (j :: List.ofFn w) u x := by
    simp only [fderiv_apOp hU m a ha hu hx, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      ring
  have hR : apOp (m + 1) (coefVF m a c) u x =
      (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (∑ j, c j x * fderiv ℝ (a n w) x (ev j)) * dw (List.ofFn w) u x) +
      ∑ n ∈ Finset.range (m + 1), ∑ j : Fin d, ∑ w : Fin n → Fin d,
        c j x * a n w x * dw (j :: List.ofFn w) u x := by
    simp only [apOp, coefVF, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.sum_range_succ]
      have h0 : ∑ w : Fin (m + 1) → Fin d, coefB m a c (m + 1) w x * dw (List.ofFn w) u x = 0 := by
        simp [coefB]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun w _ => ?_
      have : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      simp [coefB, this]
    · rw [Finset.sum_range_succ']
      have h0 : ∑ w : Fin 0 → Fin d, coefA m a c 0 w x * dw (List.ofFn w) u x = 0 := by
        simp [coefA]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun n hn => ?_
      have : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [sum_cons]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      simp [coefA, this, List.ofFn_cons]
  rw [hL, hR]

end GlobalTheory.VFComp

theorem GlobalTheory.VFComp.vectorField_comp : ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → (∀ j, ContDiffOn ℝ ∞ (c j) U) → ∃ a' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a' n w) U) ∧ (∀ x ξ : E d, symb (m + 1) a' x ξ = (∑ j, c j x * ((ξ j : ℝ) : ℂ)) * symb m a x ξ) ∧ ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ∀ x ∈ U, ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) = apOp (m + 1) a' u x := by
  intro d m U hU a c ha hc
  exact ⟨GlobalTheory.VFComp.coefVF m a c, GlobalTheory.VFComp.coefVF_contDiffOn hU m a c ha hc,
    GlobalTheory.VFComp.symb_coefVF m a c, fun u hu x hx => GlobalTheory.VFComp.apOp_coefVF hU m a c ha hu hx⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvariantOfLocallyConstantTwistStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinvariant_of_locally_constant_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (R : Finset (GL (Fin a) k)),
    Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) → IsLocallyConstant χ →
    (∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y) →
    (∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) → Φ ∈ coinv ν β a (a + b) := by
  first | exact @GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | exact GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | (intros; apply GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimitsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexCohomology_commutes_with_filteredColimits : ∀ (N : CommRingCat.{0} ⥤ AbCx), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ n, PreservesFilteredColimitsOfSize.{0, 0} (term N n)) ∧ (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) := by
  first | (exact @GlobalTheory.EtC.ContFin.cohomology_filteredColimit) | (exact GlobalTheory.EtC.ContFin.cohomology_filteredColimit) | (intros; apply GlobalTheory.EtC.ContFin.cohomology_filteredColimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeContractingHomotopy
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_contracting_homotopy : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ), (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b), ε a b (bop α β) = 1) ∧ (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧ ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)), cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  first | (exact @GlobalTheory.EZ.Cone.coneContraction) | (exact GlobalTheory.EZ.Cone.coneContraction) | (intros; apply GlobalTheory.EZ.Cone.coneContraction  <;> assumption)
end

