module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
section
noncomputable section

open AlgebraicGeometry NumberField
open scoped Matrix

namespace GlobalTheory.BalProj

def eigSp {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k) :
    Submodule k (Fin n → k) where
  carrier := {c | ∀ a, c ᵥ* B a = χ a • c}
  zero_mem' := fun a => by simp
  add_mem' := fun {c d} hc hd a => by rw [Matrix.add_vecMul, hc a, hd a, smul_add]
  smul_mem' := fun r c hc a => by rw [Matrix.smul_vecMul, hc a, smul_comm]

def eigRank {O R k : Type} [CommRing R] [Field k] (φ : R →+* k) {n : ℕ} (A : O → Matrix (Fin n) (Fin n) R)
    (χ : O → R) : ℕ :=
  Module.finrank k (eigSp (fun a => (A a).map φ) (fun a => φ (χ a)))

def embR {E : Type} [Field E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {R : Type}
    [CommRing R] (ι : F →+* R) (τ : E →+* ℂ) (a : 𝓞 E) : R :=
  ι ⟨τ (a : E), hF τ a⟩

def fnHom {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

end GlobalTheory.BalProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartCocycleCoboundaryOfHodgeDeRham
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem sndPull_cohom_zero_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ u : Fn1 (A ⊗ B), IsCoc P.U u → Cohom (chartsA P) (sndPull u v) (Fn1.zero A) := by
  intro hHDR R _ A B _ _ g hA hB hgA hgB P hP v hv u hu
  have hFree : GlobalTheory.Published.AbelianDeRham.Free := (_root_.GlobalTheory.abelianDeRham_free_hodge_baseChange hHDR).1
  have hAB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have hgAB : SmoothOfRelativeDimension (g + g) (A ⊗ B).hom := AbDual.smooth_prod hgA hgB
  obtain ⟨u', hu', hExt⟩ :=
    _root_.GlobalTheory.PtExt.CocExt.cocycle_extends R (A ⊗ B) P.ι P.U hP.cover u hu
  have hSurj := _root_.GlobalTheory.PtExt.toH1O_surjective_of_abelian hHDR R (A ⊗ B) (g + g) hAB hgAB
  obtain ⟨f, hLift⟩ := _root_.GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective R (A ⊗ B) hSurj u' hu'
  have hprim : CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) := by
    have h : AllPrim (dp0 R) (𝟙 _) (A ⊗ B) := (hFree R (A ⊗ B) (g + g) hAB hgAB).1
    rw [primDR, h]; trivial
  have hTan := _root_.GlobalTheory.PtExt.cohom_sndPull_zero R A B f hprim v
  unfold Cohom at hExt hLift hTan ⊢
  obtain ⟨k1, c1⟩ := hExt
  obtain ⟨k2, c2⟩ := hLift
  obtain ⟨k3, c3⟩ := hTan
  refine ⟨fun D _ _ x ↦ (k1 (DualNumber D) (ptV v x)).snd + (k2 (DualNumber D) (ptV v x)).snd + k3 D x, ?_⟩
  intro D _ _ D' _ _ φ x hx
  have e1 := congrArg TrivSqZeroExt.snd (c1 _ _ (epsHom φ) (ptV v x) (sm_ptV P hv hx))
  have e2 := congrArg TrivSqZeroExt.snd (c2 _ _ (epsHom φ) (ptV v x) (sm_whole _))
  have e3 := c3 D D' φ x (sm_whole _)
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_neg,
    TrivSqZeroExt.snd_sub, spOver_epsHom_ptV, snd_epsHom] at e1 e2 e3 ⊢
  rw [map_add (f := _), map_add (f := _)]
  linear_combination e1 + e2 + e3

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ k : ℕ, 1 ≤ k → ∀ p : Sp Rg, ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧ ∀ g : Rg, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f → ∀ (Ag : Over (Sp (Localization.Away g))) [GrpObj Ag] [IsCommMonObj Ag] (φ : Ag.left ⟶ A.left), IsGrpPullback Ag A (spMap (algebraMap Rg (Localization.Away g))) φ → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver (Sp (Localization.Away g))) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp (Localization.Away g))) ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤) := by
  first | exact @GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis | exact GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis | (intros; apply GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayBasis

open GlobalTheory.InvFieldRing

theorem decompR {K : Type} [CommRing K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} {π : Y' ⟶ Sp (DualNumber K)} {ρ : Y' ⟶ Y}
    (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)) :
    ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  refine GlobalTheory.RelConstThickening.existsUnique_comb (W := ⊤) (fun U hU _ F => ?_) O le_top F
  refine GlobalTheory.RelConstThickening.existsUnique_of_isPushout (GlobalTheory.RelConstThickening.constHom q U) (ρ.app U)
    (GlobalTheory.RelConstThickening.constHom π (ρ ⁻¹ᵁ U)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber K))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [GlobalTheory.RelConstThickening.constHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [GlobalTheory.RelConstThickening.constHom]

section Field

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

def transl (u : epsR R ⟶ G) : epsR R ⊗ G ⟶ G := snd _ G * (fst _ G ≫ u)

def red (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (spMap_fst_comp R)

def fib (G : Over (Sp R)) : G ⟶ epsR R ⊗ G := lift (toUnit G ≫ red R) (𝟙 G)

theorem fib_snd : (fib G).left ≫ (snd (epsR R) G).left = 𝟙 _ := by
  rw [← Over.comp_left, fib, lift_snd]; rfl

theorem fib_fst : (fib G).left ≫ (fst (epsR R) G).left = G.hom ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  rw [← Over.comp_left, fib, lift_fst, Over.comp_left, Over.toUnit_left]; rfl

theorem fib_transl {u : epsR R ⟶ G} (hu : IsTangent u) : (fib G).left ≫ (transl u).left = 𝟙 _ := by
  have hs : red R ≫ u = η[G] := Over.OverMorphism.ext hu
  have hT : fib G ≫ transl u = 𝟙 G := by
    rw [transl, fib, MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.assoc, hs, ← Hom.one_def, _root_.mul_one]
  rw [← Over.comp_left, hT]; rfl

theorem isPullback_thickR : IsPullback (snd (epsR R) G).left (fst (epsR R) G).left G.hom
    (spMap (algebraMap R (DualNumber R))) :=
  (IsPullback.of_hasPullback (epsR R).hom G.hom).flip

theorem surjective_fib : Surjective (fib G).left := by
  have hp : IsPullback (fib G).left G.hom (fst (epsR R) G).left (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    refine IsPullback.of_right ?_ fib_fst isPullback_thickR
    rw [fib_snd, spMap_fst_comp]
    exact IsPullback.id_horiz G.hom
  exact MorphismProperty.of_isPullback (P := @Surjective) hp.flip (surjective_spMap_fst R)

theorem preimage_translR {u : epsR R ⟶ G} (hu : IsTangent u) (O : G.left.Opens) :
    (transl u).left ⁻¹ᵁ O = (snd (epsR R) G).left ⁻¹ᵁ O := by
  ext x
  obtain ⟨y, rfl⟩ := (surjective_fib (G := G)).surj x
  change ((fib G).left ≫ (transl u).left).base y ∈ O ↔ ((fib G).left ≫ (snd (epsR R) G).left).base y ∈ O
  rw [fib_transl hu, fib_snd]

theorem real_partR {u : epsR R ⟶ G} (hu : IsTangent u) (O : G.left.Opens) (f a b : Γ(G.left, O))
    (h : ((transl u).left.appLE O _ (preimage_translR hu O).ge).hom f =
      ((snd (epsR R) G).left.app O).hom a + constFn (fst (epsR R) G).left _ DualNumber.eps *
        ((snd (epsR R) G).left.app O).hom b) : a = f := by
  have hjO : O ≤ (fib G).left ⁻¹ᵁ ((snd (epsR R) G).left ⁻¹ᵁ O) := by
    rw [← Scheme.Hom.comp_preimage, fib_snd, Scheme.Hom.id_preimage]
  have k := congrArg ((fib G).left.appLE _ _ hjO).hom h
  simp only [map_add (f := _), map_mul, Scheme.Hom.app_eq_appLE, appLE_appLE, appLE_constFn] at k
  rw [appLE_eq_of_eq (fib_transl hu) O O _ le_rfl, appLE_eq_of_eq fib_snd O O _ le_rfl, fib_fst] at k
  have h0 : (TrivSqZeroExt.fstHom R R R).toRingHom DualNumber.eps = 0 := by simp
  rw [constFn_spMap, h0] at k
  simp only [constFn, map_zero, zero_mul, add_zero] at k
  have hid : ∀ s : Γ(G.left, O), ((𝟙 G.left : G.left ⟶ G.left).appLE O O le_rfl).hom s = s := fun s =>
    (congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_eq_app (𝟙 G.left) (U := O))).trans rfl
  rw [hid, hid] at k
  exact k.symm

variable [IsCommMonObj G]

def pt (v : TanM (𝟙 (Sp R)) G) : epsR R ⟶ G :=
  Over.homMk (tv v).left ((Over.w (tv v)).trans (Category.comp_id _))

theorem isTangent_pt (v : TanM (𝟙 (Sp R)) G) : IsTangent (pt v) := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.scK_zero_iff]
  apply Over.OverMorphism.ext
  have h := congrArg (fun V => V.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
  refine Eq.trans h ?_
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
  exact congrArg (· ≫ _) (Category.comp_id _)

theorem exists_isInv (v : TanM (𝟙 (Sp R)) G) : ∃ dd : Fld G.left, IsInv G v dd := by
  have hu := isTangent_pt v
  have hd := fun (O : G.left.Opens) (f : Γ(G.left, O)) =>
    decompR (isPullback_thickR (G := G)) O (((transl (pt v)).left.appLE O _ (preimage_translR hu O).ge).hom f)
  choose ab hab huq using hd
  have huniq : ∀ O f (a b : Γ(G.left, O)),
      ((transl (pt v)).left.appLE O _ (preimage_translR hu O).ge).hom f =
        ((snd (epsR R) G).left.app O).hom a + constFn (fst (epsR R) G).left _ DualNumber.eps *
          ((snd (epsR R) G).left.app O).hom b → (ab O f).2 = b :=
    fun O f a b h => congrArg Prod.snd (huq O f (a, b) h).symm
  have hre : ∀ O f, (ab O f).1 = f := fun O f => real_partR hu O f _ _ (hab O f)
  have hee := fun O : G.left.Opens => constFn_eps_sq (fst (epsR R) G).left ((snd (epsR R) G).left ⁻¹ᵁ O)
  refine ⟨fun O f => (ab O f).2, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W _ f f'
    refine huniq W _ (f + f') _ ?_
    rw [map_add (f := _), hab W f, hab W f', hre, hre]
    simp only [map_add (f := _)]
    ring
  · intro W _ f f'
    refine huniq W _ (f * f') _ ?_
    rw [map_mul, hab W f, hab W f', hre, hre]
    simp only [map_add (f := _), map_mul]
    linear_combination (((snd (epsR R) G).left.app W).hom (ab W f).2 *
      ((snd (epsR R) G).left.app W).hom (ab W f').2) * hee W
  · intro W W' h _ f
    refine huniq W' _ (resG _ h f) _ ?_
    have h' : (snd (epsR R) G).left ⁻¹ᵁ W' ≤ (snd (epsR R) G).left ⁻¹ᵁ W := (snd (epsR R) G).left.preimage_mono h
    rw [appLE_res _ h h' (preimage_translR hu W).ge, hab W f, hre, map_add (f := _), map_mul, res_app _ h h',
      res_app _ h h', res_constFn]
  · intro S _ φ g₀ w O f hg hgO htr
    obtain ⟨g', v', hg', hv', rfl⟩ := htr
    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    let kA : tEpsG (g₀ ≫ G.hom) ⟶ epsR R := Over.homMk (spMap (dualMap φ)) (by
      change spMap (dualMap φ) ≫ spMap (algebraMap _ _) = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ G.hom
      rw [hg, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e])
    have hk : lift kA g' ≫ transl (pt v) = g' * v' := by
      unfold transl
      rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
      congr 1
      exact Over.OverMorphism.ext hv'.symm
    have hk2 : (lift kA g').left ≫ (snd (epsR R) G).left = spMap (algebraMap S (DualNumber S)) ≫ g₀ := by
      rw [← Over.comp_left, lift_snd, hg']
    have hk1 : (lift kA g').left ≫ (fst (epsR R) G).left = spMap (dualMap φ) := by
      rw [← Over.comp_left, lift_fst]
      rfl
    have hT : (g' * v').left = (lift kA g').left ≫ (transl (pt v)).left := by rw [← hk, Over.comp_left]
    have hx : ⊤ ≤ (lift kA g').left ⁻¹ᵁ ((snd (epsR R) G).left ⁻¹ᵁ O) := by
      intro y _
      show ((lift kA g').left ≫ (snd (epsR R) G).left).base y ∈ O
      rw [hk2]
      exact hgO (Set.mem_univ _)
    rw [hT, ← valR_appLE _ _ O _ (preimage_translR hu O).ge hx, hab O f, hre, valR_add _ _ hx, valR_mul _ _ hx,
      valR_constFn _ _ _ hk1 _ hx, Scheme.Hom.app_eq_appLE, valR_appLE _ _ _ _ _ hx, valR_appLE _ _ _ _ _ hx, hk2,
      valR_spMap_comp _ _ _ hgO, valR_spMap_comp _ _ _ hgO]
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM (𝟙 (Sp R)) G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_add, ih]


open ReciprocityTheory.ChartRestriction.G.PullbackSections in
theorem exists_basis [IsLocalRing R] (hG : Smooth G.hom) :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) := by
  have hS := isGrpPullback_pullback G (𝟙 (Sp R))
  have hsm : Smooth ((Over.pullback (𝟙 (Sp R))).obj G).hom := by
    show Smooth (pullback.snd _ _)
    infer_instance
  obtain ⟨n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis ((Over.pullback (𝟙 (Sp R))).obj G) hsm
  let b : Fin n → TanM (𝟙 (Sp R)) G := fun i =>
    mkT (pushHom hS (epsR R) (v i)) ((isTangent_iff hS _).1 (hv.1 i))
  have hb : ∀ m : TanM (𝟙 (Sp R)) G, ∃! a : Fin n → R, m = ∑ i, a i • b i := fun m => by
    obtain ⟨w', hw'⟩ := push_surj hS (tv m)
    have htan : IsTangent w' := (isTangent_iff hS w').2 (by rw [hw']; exact tv_mem m)
    have key : ∀ a : Fin n → R, IsLieComb a v w' ↔ m = ∑ i, a i • b i := by
      intro a
      rw [isLieComb_iff hS, hw']
      constructor
      · intro h
        apply tanM_ext
        rw [h, tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
      · intro h
        rw [h, tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
    obtain ⟨C, hC, hCu⟩ := hv.2 w' htan
    exact ⟨C, (key C).1 hC, fun a ha => hCu a ((key a).2 ha)⟩
  refine ⟨n, ⟨Module.Basis.mk (v := b) ?_ ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun ((hb 0).unique hg.symm (y₂ := 0) (by simp)) i
  · intro m _
    obtain ⟨a, ha, -⟩ := hb m
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Field

theorem exists_basis_isInv : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  intro R _ _ _ D O _ _ _ oa Y
  have h1 : Smooth Y.q.left := Y.smooth_q
  have h2 : Smooth D.P.A.hom := D.P.isAb.smooth
  have hG : Smooth Y.H.hom := by
    rw [← Over.w Y.q]
    infer_instance
  obtain ⟨n, ⟨v⟩⟩ := exists_basis hG
  choose dd hdd using fun a => exists_isInv (v a)
  exact ⟨n, v, dd, hdd⟩

end GlobalTheory.RayBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleSectionUnitAtClosedPointTorusChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SecConst


open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic in
theorem exists_secB_isUnit_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ mu α : P.D.toPre.X, ∃ σ : P.D.toPre.SecB e α, ∀ zz J, Good P.D.toPre.P.L zz J → IsUnit (sval σ (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz J) := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _ Y n' v' dd _ D q _ h _ _ _ ρ hρ B' _ π₁ π₂ c' _ _ _ _
  refine ⟨6, fun e he mu al => ?_⟩
  have hpt : ∀ zz, (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz =
      (P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d)) := by
    intro zz
    rw [Scheme.Hom.comp_apply]
    congr 1
    have key : ∀ r : ChartRing k m d,
        (constHom ρ) r = algebraMap k (DualNumber k) (MvPowerSeries.constantCoeff r) := by
      intro r
      simp [constHom, hρ r]
    apply PrimeSpectrum.ext
    ext r
    show (constHom ρ) r ∈ PrimeSpectrum.asIdeal (R := DualNumber k) zz ↔
      r ∈ IsLocalRing.maximalIdeal (ChartRing k m d)
    rw [key, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      isUnit_iff_ne_zero, not_not]
    by_cases h0 : MvPowerSeries.constantCoeff r = 0
    · simp [h0, Ideal.zero_mem]
    · refine iff_of_false (fun hm => ?_) h0
      have hu : IsUnit (algebraMap k (DualNumber k) (MvPowerSeries.constantCoeff r)) :=
        (isUnit_iff_ne_zero.2 h0).map _
      exact (PrimeSpectrum.isPrime (R := DualNumber k) zz).ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hxc : P.D.toPre.P.A.hom ((P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d))) =
      IsLocalRing.closedPoint (ChartRing k m d) := by
    show ((P.D.toPre.c mu).left ≫ P.D.toPre.P.A.hom) _ = _
    rw [Over.w (P.D.toPre.c mu)]
    rfl
  obtain ⟨σ₂, hσ₂⟩ := _root_.GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre (ChartRing k m d) (GlobalTheory.MumfordChart.admissibleBase_chartRing k m d).2.2.2 P.D.toPre al _ hxc
  have hA := (GlobalTheory.abelianSchemeLaws_all).1.ample
  obtain ⟨N, s, hcov⟩ := (hA (Spec (CommRingCat.of (ChartRing k m d))) P.D.toPre.P (e - 2) (by omega)).1 ⊤
    (isAffineOpen_top _)
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : P.D.toPre.P.A.left ⟶ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).toScheme,
      ρ' ≫ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show ρ' ((P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d))) ∈ ⨆ i, nonzeroLocus (s i) by
      rw [hcov]; trivial)
  have hF : FormEq (Sum.elim (DegPre.famφB P.D.toPre al)
      (fun _ : Fin (e - 2) => ρ' ≫ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).ι))
      (Sum.elim (DegPre.famε 2) (fun _ => 1)) (DegPre.famφB P.D.toPre al) (DegPre.famε e) := by
    intro U _ hh
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hρ', Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, zpow_one, Fin.prod_univ_four]
    have e0 : DegPre.famφB P.D.toPre al 0 = 𝟙 _ := rfl
    have x0 : DegPre.famε 2 0 = 1 := by simp [DegPre.famε]
    have y0 : DegPre.famε e 0 = (e : ℤ) - 1 := rfl
    have x1 : DegPre.famε 2 1 = DegPre.famε e 1 := rfl
    have x2 : DegPre.famε 2 2 = DegPre.famε e 2 := rfl
    have x3 : DegPre.famε 2 3 = DegPre.famε e 3 := rfl
    rw [x0, y0, x1, x2, x3, e0, show (e : ℤ) - 1 = 1 + ((e - 2 : ℕ) : ℤ) by omega, zpow_add, zpow_natCast,
      zpow_one]
    ac_rfl
  obtain ⟨σ, hσ⟩ := exists_sec P.D.toPre.P.isLB hF (mulSec σ₂ (pullSec (s i) ρ'))
  refine ⟨σ, fun zz J hJ => ?_⟩
  rw [hσ _ _ zz J hJ, sval_mulSec _ _ _ zz hJ]
  erw [sval_pullSec (s i) ρ' _ zz hJ]
  refine IsUnit.mul ?_ ?_
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hσ₂
    exact isUnit_sval σ₂ _ zz hJ j (by rw [hpt]; exact hj)
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) _ zz hJ j (by rw [Scheme.Hom.comp_apply, hpt]; exact hj)

end GlobalTheory.SecConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLab
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_isLab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X), IsLab X₁ ε₁ c yy := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p _ z₁ c
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', u', hsame, hi₀, hle, hdiag', y₀, hy₀, hpt, hint⟩ :=
    _root_.GlobalTheory.Poinc.rechart_at_classical_trait g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p z₁ c
  obtain ⟨u, l, j, hq, hcong⟩ :=
    GlobalTheory.T.exists_labelled_uniformisedModel_thetaSystem_trait g n F W he8 X₁.o₁ X₁.Ω₁ _ ρ' ε' u' hdiag' p y₀ c.T c.ι c.int hpt hint
  let jm : ModN (X₁.S.r * X₁.S.N) u.D.toPre.X →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X) :=
    QuotientAddGroup.map _ _ j.toAddMonoidHom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, by simp⟩)
  refine ⟨jm.comp l.yy, c₀, hc, R', fg, frac, hth', hev, ρ', ε', hsame, hi₀, hle, y₀, hy₀, u, l, j, hq, ?_, hcong⟩
  intro a χ ha
  simp only [AddMonoidHom.comp_apply, ha, jm]
  rfl

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicGenericFibreQuotientStrictHenselisationNoTorsStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_generic_fibre_quotient_strictHenselisation_no_torsion_alt : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  first | (exact @GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion) | (exact GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion) | (intros; apply GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion  <;> assumption)
end

