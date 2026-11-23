module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGenSecNear
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EmbLocal

open ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}}

theorem exists_isGenSec_near (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∀ (R : Type) [CommRing R] (q : Sp R ⟶ S), Set.range q ⊆ V →
      ∃ th, IsGenSec P.A P.L 1 (T := Over.mk q) th := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  refine ⟨V, hV, fun R _ q hqV => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
    ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose b' hb' using fun i =>
    PushInv.exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
  obtain ⟨-, hsp⟩ := hb R t b' hb'
  refine ⟨b' hq.default, fun s => ?_⟩
  rw [Set.range_unique] at hsp
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem exists_mulPull (hG : GlobalFnsSt) (P : PolAV S) (k : ℕ) (T : Over S) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]),
      α.IsGen := by
  obtain ⟨α₀, hα₀⟩ := (MulPull.mulPull_of_cube_of_symm AbLaw.CubeAssembly.cube_gen (exists_gen_negLB hG)).1 S P k
  have e₁ : (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left])
    (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα⟩

theorem exists_symLift_near (hG : GlobalFnsSt) (P : PolAV S) {k : ℕ} (hk : Odd k) {T : Over S} (y : T ⟶ P.A)
    (hy : y ^ k = 1) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧ ∀ (T' : Over S) (h : T' ⟶ T), Set.range h.left ⊆ V →
      ∃ θ : ThetaGrp P.A P.L k T', SymLift P.A P.L k k (h ≫ y) θ := by
  obtain ⟨V, hV, θ, hθ⟩ := ((symLift_odd hG
    (kerPow_of_square (AbSquare.square_of_cube AbLaw.CubeAssembly.cube_gen).1).2.2 (exists_gen_negLB hG)).1
      S P k hk T y hy).1 p
  refine ⟨V, hV, fun T' h hh => ?_⟩
  have hr : Set.range h.left ⊆ Set.range V.ι := hh.trans (Scheme.Opens.range_ι V).ge
  let l : T' ⟶ overRes V := Over.homMk (IsOpenImmersion.lift V.ι h.left hr) (by
    show IsOpenImmersion.lift V.ι h.left hr ≫ V.ι ≫ T.hom = T'.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w h])
  have e : l ≫ overResι V = h := Over.OverMorphism.ext (IsOpenImmersion.lift_fac V.ι h.left hr)
  obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB l hθ
  exact ⟨θ', by rw [← e, Category.assoc]; exact hθ'⟩

theorem exists_affine_nhds {R : Type} [CommRing R] (W : (Sp R).Opens) (p : Sp R) (hp : p ∈ W) :
    ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧
      Set.range (spMap φ) ⊆ W := by
  obtain ⟨_, ⟨r, rfl⟩, hr, hW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := W.1) hp W.isOpen
  have e : Set.range (spMap (algebraMap R (Localization.Away r))) = (PrimeSpectrum.basicOpen r).1 :=
    PrimeSpectrum.localization_away_comap_range (R := R) (Localization.Away r) r
  refine ⟨Localization.Away r, inferInstance, algebraMap _ _, ?_, e.ge hr, e.le.trans hW⟩
  exact inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))

theorem lab_pow {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} (t : TObj g k J b s)
    (a : Ix g k) : t.lab a ^ k = 1 := by
  have := t.ab.comm
  rw [TObj.lab, linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]

end GlobalTheory.EmbLocal

namespace GlobalTheory

open EmbLocal

theorem exists_emb_locally : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S), Odd N' → m ∣ N' → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ := by
  intro hL hL2 o _ g N' J b S s t m R _ x hN hm p
  have hmo : Odd m := hN.of_dvd_nat hm
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hN.pos.ne'⟩
  let u : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
  have hy : ∀ a, ((u ≫ t.lab a) ^ ((N' / m) ^ 2)) ^ (m ^ 2) = 1 := fun a => by
    rw [← pow_mul, ← mul_pow, Nat.div_mul_cancel hm, ← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  obtain ⟨V, hV, hth⟩ := exists_isGenSec_near hL2.secBaseChangeAny t.pol (x p)
  choose W hW hU using fun a => exists_symLift_near hL.globalFns t.pol (k := m ^ 2) hmo.pow
    (T := Over.mk x) _ (hy a) p
  obtain ⟨R', _, φ, hφ, hp, hsub⟩ := exists_affine_nhds
    (x ⁻¹ᵁ V ⊓ ⟨⋂ a, (W a).1, isOpen_iInter_of_finite fun a => (W a).isOpen⟩) p
    ⟨hV, Set.mem_iInter.2 hW⟩
  let T : Over S := Over.mk (spMap φ ≫ x)
  let h : T ⟶ Over.mk x := Over.homMk (spMap φ) rfl
  obtain ⟨th, hth⟩ := hth R' (spMap φ ≫ x) (by
    rintro _ ⟨z, rfl⟩
    exact (hsub ⟨z, rfl⟩).1)
  obtain ⟨α, hα⟩ := exists_mulPull hL.globalFns t.pol m T
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull t.isLB (Out.mulT t.A T m) (snd T t.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 α hα th
  have hU' : ∀ a, ∃ θ : Out.ThetaGrp t.A t.L ((m : ℤ) ^ 2) T, Out.SymLift t.A t.L ((m : ℤ) ^ 2) (m ^ 2)
      (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2)) θ := fun a => by
    obtain ⟨θ, hθ⟩ := hU a T h fun z hz => Set.mem_iInter.1 (hsub hz).2 a
    rw [← Nat.cast_pow]
    refine ⟨θ, ?_⟩
    have e : h ≫ (u ≫ t.lab a) ^ ((N' / m) ^ 2) =
        ((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2) := by
      rw [MonObj.comp_pow, ← Category.assoc]; rfl
    rw [← e]
    exact hθ
  choose U hU' using hU'
  choose σ hσ using fun a => ThetaPtExist.exists_isTwistPull t.isLB (Out.translT t.A (U a).pt)
    (Out.translPt t.A (U a).pt) (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (U a).φ (U a).isGen s₁
  exact ⟨R', inferInstance, φ, σ, hφ, hp, th, s₁, α, U, hth, hα, hs₁, hU', hσ⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtens
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.IsoOverField

theorem eSec_pullback_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq]
  erw [ExtUnique.pullback_map_left_fst, ← Category.assoc, ← pullback.condition]
  simp

theorem isAbelianScheme_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

variable {U' U S : Scheme.{0}} (k : U' ⟶ U) (j : U ⟶ S)

noncomputable def toBase (A : Over S) : (Over.mk (k ≫ j) ⊗ A).left ⟶ pullback A.hom j :=
  pullback.lift (snd (Over.mk (k ≫ j)) A).left ((fst (Over.mk (k ≫ j)) A).left ≫ k)
    (by rw [Over.w, Category.assoc]; exact (Over.w (fst (Over.mk (k ≫ j)) A)).symm)

theorem toBase_fst (A : Over S) : toBase k j A ≫ pullback.fst A.hom j = (snd (Over.mk (k ≫ j)) A).left :=
  pullback.lift_fst _ _ _

theorem toBase_snd (A : Over S) : toBase k j A ≫ pullback.snd A.hom j = (fst (Over.mk (k ≫ j)) A).left ≫ k :=
  pullback.lift_snd _ _ _

theorem isPullback_snd (T A : Over S) : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
  (IsPullback.of_hasPullback T.hom A.hom).flip

theorem isPullback_toBase (A : Over S) :
    IsPullback (toBase k j A) (fst (Over.mk (k ≫ j)) A).left (pullback.snd A.hom j) k := by
  refine IsPullback.of_right ?_ (toBase_snd k j A) (IsPullback.of_hasPullback A.hom j)
  rw [toBase_fst]
  exact isPullback_snd (Over.mk (k ≫ j)) A

theorem exists_iso_over [Flat k] [Surjective k] [QuasiCompact k] [Mono j] (A B : Over S) [GrpObj A] [GrpObj B]
    (φ : Over.mk (k ≫ j) ⊗ A ≅ Over.mk (k ≫ j) ⊗ B) (hφ : φ.hom ≫ fst _ _ = fst _ _)
    (h₁ : lift (𝟙 (Over.mk (k ≫ j))) (1 : Over.mk (k ≫ j) ⟶ A) ≫ φ.hom ≫ snd _ _ = 1)
    (κ : Over.mk (k ≫ j) ⟶ Over.mk j) (g : Over.mk j ⊗ A ⟶ B) (hg : κ ▷ A ≫ g = φ.hom ≫ snd _ _) :
    ∃ f : (Over.pullback j).obj A ≅ (Over.pullback j).obj B,
      η[(Over.pullback j).obj A] ≫ f.hom = η[(Over.pullback j).obj B] ∧
      toBase k j A ≫ f.hom.left ≫ pullback.fst B.hom j = (φ.hom ≫ snd _ _).left := by
  have hκ : κ.left = k := (cancel_mono j).1 (Over.w κ)
  let s : pullback A.hom j ⟶ (Over.mk j ⊗ A).left := (pullbackSymmetry A.hom j).hom
  have s₁ : s ≫ (fst (Over.mk j) A).left = pullback.snd A.hom j := pullbackSymmetry_hom_comp_fst _ _
  have s₂ : s ≫ (snd (Over.mk j) A).left = pullback.fst A.hom j := pullbackSymmetry_hom_comp_snd _ _
  have hs : toBase k j A ≫ s = (κ ▷ A).left := by
    refine (isPullback_snd (Over.mk j) A).hom_ext ?_ ?_
    · rw [Category.assoc, s₂, toBase_fst, ← Over.comp_left, whiskerRight_snd]
    · rw [Category.assoc, s₁, toBase_snd, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hκ]
  have hw : (s ≫ g.left) ≫ B.hom = pullback.snd A.hom j ≫ j := by
    rw [Category.assoc, Over.w, ← s₁, Category.assoc]
    exact congrArg (s ≫ ·) (Over.w (fst (Over.mk j) A)).symm
  let f : (Over.pullback j).obj A ⟶ (Over.pullback j).obj B :=
    Over.homMk (pullback.lift (s ≫ g.left) (pullback.snd A.hom j) hw) (pullback.lift_snd _ _ _)
  have f₁ : f.left ≫ pullback.fst B.hom j = s ≫ g.left := pullback.lift_fst _ _ _
  have f₂ : f.left ≫ pullback.snd B.hom j = pullback.snd A.hom j := pullback.lift_snd _ _ _
  have key : toBase k j A ≫ f.left ≫ pullback.fst B.hom j = (φ.hom ≫ snd _ _).left := by
    rw [f₁, ← Category.assoc, hs, ← Over.comp_left, hg]
  have hφ' : φ.hom.left ≫ (fst (Over.mk (k ≫ j)) B).left = (fst (Over.mk (k ≫ j)) A).left := by
    rw [← Over.comp_left, hφ]
  have sq : toBase k j A ≫ f.left = φ.hom.left ≫ toBase k j B := by
    apply pullback.hom_ext
    · rw [Category.assoc, key, Category.assoc, toBase_fst, Over.comp_left]
    · rw [Category.assoc, f₂, Category.assoc, toBase_snd, toBase_snd, ← Category.assoc, hφ']
  have pb : IsPullback (toBase k j A) φ.hom.left f.left (toBase k j B) := by
    refine IsPullback.of_bot ?_ sq (isPullback_toBase k j B)
    rw [hφ', f₂]
    exact isPullback_toBase k j A
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (toBase k j B) :=
    MorphismProperty.of_isPullback (isPullback_toBase k j B).flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hi : IsIso f.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0}) pb.flip hQ
      (inferInstanceAs (IsIso ((Over.forget S).map φ.hom)))
  have : IsIso ((Over.forget U).map f) := hi
  have : IsIso f := isIso_of_reflects_iso f (Over.forget U)
  refine ⟨asIso f, ?_, key⟩
  have : Epi k := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have one : ∀ (G : Over S) [GrpObj G], (1 : Over.mk (k ≫ j) ⟶ G).left = (k ≫ j) ≫ eSec G := fun G _ => by
      rw [Hom.one_def, Over.comp_left]
      congr 1
    have e : (lift (𝟙 (Over.mk (k ≫ j))) (1 : Over.mk (k ≫ j) ⟶ A)).left ≫ toBase k j A =
        k ≫ eSec ((Over.pullback j).obj A) := by
      apply pullback.hom_ext
      · rw [Category.assoc, toBase_fst, ← Over.comp_left, lift_snd, one, Category.assoc, Category.assoc]
        exact congrArg (k ≫ ·) (eSec_pullback_fst j A).symm
      · rw [Category.assoc, toBase_snd, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc]
        exact (Category.id_comp _).trans ((Category.comp_id k).symm.trans
          (congrArg (k ≫ ·) (Over.w η[(Over.pullback j).obj A]).symm))
    refine (cancel_epi k).1 ?_
    change k ≫ (eSec ((Over.pullback j).obj A) ≫ f.left) ≫ pullback.fst B.hom j =
      k ≫ eSec ((Over.pullback j).obj B) ≫ pullback.fst B.hom j
    rw [eSec_pullback_fst, Category.assoc, ← Category.assoc k, ← e, Category.assoc, key, ← Over.comp_left, h₁,
      one, Category.assoc]
  · exact (Over.w _).trans (Over.w _).symm

theorem exists_iso_over_dvr : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P P' : PolAV (Sp V)) (C : Type) [Field C] [Algebra (FractionRing V) C] (φ : TF (R := V) C ⊗ P.A ≅ TF (R := V) C ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (TF (R := V) C)) (1 : TF (R := V) C ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (TF (R := V) C) P.A).left) (P'.L.pull (φ.hom ≫ snd (TF (R := V) C) P'.A).left) → ∀ (κ : TF (R := V) C ⟶ TK V) (g : TK V ⊗ P.A ⟶ P'.A), κ ▷ P.A ≫ g = φ.hom ≫ snd _ _ → ∃ Ψ : P.A ≅ P'.A, IsMonHom Ψ.hom ∧ φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom ∧ LBIso P.L (P'.L.pull Ψ.hom.left) := by
  intro hl _ V _ _ _ P P' C _ _ φ hφ h₁ hL κ g hg
  have : Flat (jFK (R := V) C) := FieldBaseChange.flat_spMap (algebraMap (FractionRing V) C)
  have : Surjective (jFK (R := V) C) := FieldBaseChange.surjective_spMap (algebraMap (FractionRing V) C)
  have : QuasiCompact (jFK (R := V) C) := by
    have : IsAffine (TK V).left := inferInstanceAs (IsAffine (Spec _))
    infer_instance
  have : Mono (jK V) := by
    have : IsPreimmersion (jK V) := IsPreimmersion.of_isLocalization (nonZeroDivisors V)
    infer_instance
  obtain ⟨f, hf₁, hf⟩ := exists_iso_over (jFK (R := V) C) (jK V) P.A P'.A φ hφ h₁ κ g hg
  have hm : IsMonHom f.hom := hl.rigidity _ _ _ (isAbelianScheme_pullback _ _ P.isAb)
    (isAbelianScheme_pullback _ _ P'.isAb) f.hom hf₁
  have hm' : IsMonHom f.inv := inferInstance
  have semi_of_ab {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) : IsSemiAbelian B := by
    have := h.proper
    refine ⟨h.comm, h.smooth, inferInstance, inferInstance, h.geomConnected, ?_⟩
    intro Ω _ _ p
    have hab := isAbelianScheme_pullback p B h
    refine ⟨{ X := PUnit, B := _, isAbelian := hab, q := 𝟙 _, q_hom := inferInstance
              q_flat := ?_, q_surjective := ?_, q_quasiCompact := ?_
              i := toUnit _ ≫ η, i_hom := ?_, isKernel := ?_ }⟩
    · rw [Over.id_left]; infer_instance
    · rw [Over.id_left]; infer_instance
    · rw [Over.id_left]; infer_instance
    · have := hab.comm; infer_instance
    · have hident : 𝟙 (splitTorus (Spec (CommRingCat.of Ω)) PUnit) = 1 := by
        rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
        congr 1
      have : IsIso (toUnit (splitTorus (Spec (CommRingCat.of Ω)) PUnit)) := ⟨η, hident.symm, toUnit_unique _ _⟩
      exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  have hs := semi_of_ab P.A P.isAb
  have hs' := semi_of_ab P'.A P'.isAb
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := homExtension_semiAbelian_dvr_unconditional V (FractionRing V) P.A P'.A hs hs' f.hom hm
  obtain ⟨G, ⟨-, eG⟩, -⟩ := homExtension_semiAbelian_dvr_unconditional V (FractionRing V) P'.A P.A hs' hs f.inv hm'
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing V (FractionRing V)
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P'.isAb.smooth
  have := P'.isAb.proper
  have : IsIso F := ExtUnique.isIso_of_pullback (jK V) f F G eF eG
  have e : φ.hom ≫ snd _ _ = snd _ _ ≫ F := by
    apply Over.OverMorphism.ext
    rw [← hf, ← eF, Over.comp_left, ← toBase_fst (jFK (R := V) C) (jK V) P.A, Category.assoc]
    exact congrArg (_ ≫ ·) (ExtUnique.pullback_map_left_fst (jK V) F)
  refine ⟨asIso F, hF, e, ?_⟩
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
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
  have hN := pull_isLB P'.isLB F.left
  have hβ : jFK (R := V) C ≫ jK V =
      spMap ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V))) := (Spec.map_comp _ _).symm
  refine IsoDescent.lbIso_of_field V C ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V)))
    ((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))) P.A P.isAb _
    (snd (TF (R := V) C) P.A).left (fst (TF (R := V) C) P.A).left (hβ ▸ isPullback_snd (TF (R := V) C) P.A)
    P.L (P'.L.pull F.left) P.isLB hN ?_ ?_
  all_goals
    obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, comp, linComb, -⟩ := CechPicMul.exists_picardGroup
    let _ := groups
    have pull_class {S T : Scheme.{0}} (f : T ⟶ S) {L : LB S} (hL : L.IsLB) :
        (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
      simpa only [Fintype.prod_unique, zpow_one] using
        linComb S T L hL PUnit (fun _ => f) (fun _ => 1)
  · have eF' : eSec P.A ≫ F.left = eSec P'.A := congrArg (·.left) (IsMonHom.one_hom F)
    apply (iso_iff _ _ _ (pull_isLB P.isLB _) (pull_isLB hN _)).1
    rw [(gen_iff _ _ (pull_isLB P.isLB _)).2 P.rigid,
      (pull_class _ hN).2, (pull_class _ P'.isLB).2, ← comp, eF',
      ← (pull_class _ P'.isLB).2, (gen_iff _ _ (pull_isLB P'.isLB _)).2 P'.rigid]
  · apply (iso_iff _ _ _ (pull_isLB P.isLB _) (pull_isLB hN _)).1
    have hL' := (iso_iff _ _ _ (pull_isLB P.isLB _) (pull_isLB P'.isLB _)).2 hL
    rw [(pull_class _ P'.isLB).2, e] at hL'
    rw [hL', (pull_class _ hN).2, (pull_class _ P'.isLB).2, ← comp, Over.comp_left]

end GlobalTheory.IsoOverField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionCubeLBIsoPolarisationTranslate
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.TorsionTranslation

open Out CommutatorPairing PrimCocycle CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem transl_mulA (k : ℕ) (y : 𝟙_ (Over S) ⟶ A) (hy : y ^ k = 1) :
    ((toUnit A ≫ y) * 𝟙 A).left ≫ (mulA A k).left = (mulA A k).left := by
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
    MonObj.comp_one, _root_.one_mul]

theorem exists_character (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {X : Scheme.{0}} {M : LB X} (hM : M.IsLB)
    {I : Type} [Fintype I] (φ : I → (A.left ⟶ X)) (ε : I → ℤ) (k : ℕ)
    (u : LB.Gen (LB.LinComb M (fun i => (mulA A k).left ≫ φ i) ε)) (hu : u.IsGen) :
    ∃ χ : {y : 𝟙_ (Over S) ⟶ A // y ^ k = 1} → Γ((𝟙_ (Over S)).left, ⊤)ˣ,
      (∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) ∧
      ∀ y (z : A.left) J, Good M z J →
        val u ((toUnit A ≫ y.1) * 𝟙 A).left z J = val u (𝟙 _) z J * gm (toUnit A).left z ⊤ (χ y) := by
  have he : (1 : 𝟙_ (Over S) ⟶ A).left ≫ (toUnit A).left = 𝟙 _ := by
    rw [← Over.comp_left, comp_toUnit, toUnit_unit]; rfl
  have hp : Function.Surjective (toUnit A).left.appTop.hom := by
    have e : (toUnit A).left = A.hom := (Category.comp_id _).symm.trans (Over.w (toUnit A))
    rw [e]
    exact (hG _ _ hA).2
  have H : ∀ y : {y : 𝟙_ (Over S) ⟶ A // y ^ k = 1}, ∃ c : Γ((𝟙_ (Over S)).left, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good M z J →
        val u (r ≫ ((toUnit A ≫ y.1) * 𝟙 A).left) z J = val u r z J * gm (r ≫ (toUnit A).left) z ⊤ c := by
    intro y
    obtain ⟨c, hc⟩ := exists_ratio hM (fun U _ h => Finset.prod_congr rfl fun i _ => by
        rw [← Category.assoc, transl_mulA k y.1 y.2]) (toUnit A).left _ he hp
      (DVR.pullGen_isGen _ _ _ u hu ((toUnit A ≫ y.1) * 𝟙 A).left) hu
    exact ⟨c, fun Z r z J hJ => (val_pull hJ _ _ _).symm.trans (hc Z r z J hJ)⟩
  choose χ hχ using H
  refine ⟨χ, fun x y => unit_ext fun z _ => ?_, fun y z J hJ => ?_⟩
  · choose J hJ using fun ψ : (𝟙_ (Over S)).left ⟶ X => exists_chart hM (ψ z)
    have a := hχ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ _ (1 : 𝟙_ (Over S) ⟶ A).left z J hJ
    have b := hχ x _ (1 : 𝟙_ (Over S) ⟶ A).left z J hJ
    have c := hχ y _ ((1 : 𝟙_ (Over S) ⟶ A).left ≫ ((toUnit A ≫ x.1) * 𝟙 A).left) z J hJ
    have e₁ : ((toUnit A ≫ x.1) * 𝟙 A).left ≫ ((toUnit A ≫ y.1) * 𝟙 A).left =
        ((toUnit A ≫ (x.1 * y.1)) * 𝟙 A).left := by
      rw [← Over.comp_left, MonObj.comp_mul, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id,
        ← _root_.mul_assoc, mul_comm (toUnit A ≫ y.1)]
    have e₂ : ((toUnit A ≫ x.1) * 𝟙 A).left ≫ (toUnit A).left = (toUnit A).left := by
      rw [← Over.comp_left, comp_toUnit]
    rw [b, Category.assoc, Category.assoc, e₁, e₂, a, he, _root_.mul_assoc, ← map_mul] at c
    exact mul_left_cancel c
  · have := hχ y _ (𝟙 _) z J hJ
    rwa [Category.id_comp, Category.id_comp] at this

theorem exists_gen_mulA {M : LB A.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta A M), t.IsGen) (k : ℕ)
    (x : 𝟙_ (Over S) ⟶ A) (hx : x ^ k = 1) :
    ∃ u : LB.Gen (LB.LinComb M (fun I : ULift.{0} (Finset (Fin 2)) =>
      (mulA A k).left ≫ (psum A ![toUnit A ≫ x, 𝟙 A] I.down).left) lamε), u.IsGen := by
  refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
  have h₁ : (cubeLB A ![toUnit A ≫ x, 𝟙 A] M).IsLB := LB.isLB_linComb hM _ _
  have e := congrArg (CechPic.pull (mulA A k).left) ((cls_linComb hM _ _ h₁).symm.trans (cls_cube_two hM _ _ h₁))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pull_lam, comp_toUnit_assoc, Category.comp_id, map_sum] at e
  have e' : lam (cls M hM) (toUnit A ≫ x) (mulA A k) = 0 := by
    rw [mulA, lam_pow_right hM hΘ, ← lam_pow_left hM hΘ, ← MonObj.comp_pow, hx, MonObj.comp_one, lam_one_left]
  rw [cls_linComb hM]
  refine Eq.trans (Finset.sum_congr rfl fun I _ => ?_) (e.trans e')
  rw [map_zsmul, pull_comp]

end GlobalTheory.TorsionTranslation

namespace GlobalTheory

open TorsionTranslation PairingDetermines IsoDescent PrimCocycle

theorem exists_torsion_lbIso_cubeLB : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → (k : K) ≠ 0 → x ^ k = 1 → ∃ y : 𝟙_ (Over (Sp K)) ⟶ P.A, y ^ k = 1 ∧ LBIso (cubeLB P.A ![toUnit P.A ≫ x, 𝟙 P.A] M) (cubeLB P.A ![toUnit P.A ≫ y, 𝟙 P.A] P.L) := by
  intro hL hL' K _ _ P M k x hM hk hx
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨u, hu⟩ := exists_gen_mulA hM (AbLaw.CubeAssembly.cube_gen _ P M hM) k x hx
  obtain ⟨χ, hχ, vχ⟩ := exists_character hL.globalFns P.isAb hM _ _ k u hu
  obtain ⟨y, ⟨hy, hw⟩, -⟩ := hL'.charPair K P k hk (fun δ => (χ δ)⁻¹) (fun a b =>
    (congrArg (·⁻¹) (hχ a b)).trans (mul_inv _ _))
  refine ⟨y, hy, ?_⟩
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_lam hL.globalFns hL.cube P (𝟙 P.A) 1 k y hy
  obtain ⟨u', hu', v'⟩ := exists_gen P.isLB (φ' := fun I : ULift.{0} (Finset (Fin 2)) =>
      (Out.mulA P.A k).left ≫ (psum P.A ![toUnit P.A ≫ y, 𝟙 P.A] I.down).left) (ε' := lamε)
    (fun U _ h => Finset.prod_congr rfl fun I _ => by
      have e : (lift (toUnit P.A ≫ y) (𝟙 P.A)).left ≫ lamφ P.A I =
          (psum P.A ![toUnit P.A ≫ y, 𝟙 P.A] I.down).left :=
        congrArg (fun q => q.left) ((psum_hom (preHom (lift (toUnit P.A ≫ y) (𝟙 P.A))) (x2 P.A) I.down).trans
          (congrArg (fun q => psum P.A q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
      rw [Over.id_left, Category.comp_id, e, Nat.cast_one, _root_.mul_one]) u₀ hu₀
  refine lbIso_of_invariant hM P.isLB _ _ _ _ (Out.mulA P.A k).left
    (I := {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ k = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun δ => transl_mulA k δ.1 δ.2)
    (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
      obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
      exact ⟨a, b, c, e⟩) K P k hk U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
    (fun δ z J J' hJ hJ' => ?_)
  have w := CommPairing.weilIs_symm P.isLB (hw δ)
  rw [inv_inv] at w
  have h₁ := vχ δ z J hJ
  have h₂ := v₀ δ.1 (χ δ) δ.2 (by rw [Category.comp_id, Category.comp_id]; exact w) z J' hJ'
  rw [pow_one, ← v' _ _ z J' hJ', ← v' _ _ z J' hJ'] at h₂
  refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
  exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h

end GlobalTheory
end
end

