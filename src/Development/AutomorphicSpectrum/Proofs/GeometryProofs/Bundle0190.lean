module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtends
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0187

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrEigenTangentExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.EigLin

theorem model_cast {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x y : Sp R ⟶ S} (h : x = y)
    {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) :
    ∃ M' : LieModel G y L, ∀ l, (M'.pt l).left = (M.pt l).left := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem mem_span_iff : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (T : Over (Sp V)) [GrpObj T] [IsCommMonObj T] (GK : Over (Sp K)) [GrpObj GK] (φ₀ : GK.left ⟶ T.left)
    (Oe : Type) [CommRing Oe] (actT : OAct Oe T) (actK : OAct Oe GK) (g n : ℕ) (ML : LieModel GK (𝟙 _) (Fin g → K))
    (ρK : Oe →+* Module.End K (Fin g → K)) (σV : Oe →+* V) (vV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T)) (b : Fin n → Fin g → K),
    IsGrpPullback GK T (spMap (algebraMap V K)) φ₀ → (∀ a, (actK.act a).left ≫ φ₀ = φ₀ ≫ (actT.act a).left) →
    ML.IsActOf actK.act ρK → IsEigFrame actT (𝟙 _) σV vV →
    (∀ i, (ML.pt (b i)).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ (vV i).left) →
    ∀ w, w ∈ Submodule.span V (Set.range b) ↔
      (∃ a : epsAt (𝟙 (Sp V)) ⟶ T, IsTanAt T (𝟙 _) a ∧ (ML.pt w).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ a.left) ∧
        ∀ r, ρK r w = algebraMap V K (σV r) • w := by
  intro V K _ _ _ _ _ _ T _ _ GK _ φ₀ Oe _ actT actK g n ML ρK σV vV b hpull hact hML hF hb w
  have halg : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  obtain ⟨ET, _, _, ⟨MT⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_exists (Sp V) T V (𝟙 _)
  have hpt : 𝟙 (Sp K) ≫ spMap (algebraMap V K) =
      Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ 𝟙 (Sp V) := by simp
  obtain ⟨M', hM'⟩ := model_cast hpt (LieMove.pushModel hpull ML)
  obtain ⟨j, hj1, hj2, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_baseChange (Sp V) T V K (𝟙 _) ET (Fin g → K) MT M'
  have key1 : ∀ e, (ML.pt (j e)).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ (MT.pt e).left := fun e =>
    (hM' (j e)).symm.trans (hj1 e)
  have uniq : ∀ u u' : Fin g → K, (ML.pt u).left ≫ φ₀ = (ML.pt u').left ≫ φ₀ → u = u' := fun u u' h =>
    ML.inj (LieMove.pushEps_inj hpull (Over.OverMorphism.ext h))
  have hjinj : Function.Injective j := fun e e' h =>
    MT.inj (LieTangent.tan_ext halg (MT.tan e) (MT.tan e') ((key1 e).symm.trans (by rw [h]; exact key1 e')))
  have eig : ∀ r e e', MT.pt e' = MT.pt e ≫ actT.act r → j e' = ρK r (j e) := by
    intro r e e' h
    apply uniq
    have h1 : ML.pt (ρK r (j e)) = ML.pt (j e) ≫ actK.act r := hML r (j e)
    rw [key1 e', h1, Over.comp_left, Category.assoc, hact r, ← Category.assoc, key1 e, h, Over.comp_left,
      Category.assoc]
  have htan : ∀ r v, IsTanAt T (𝟙 _) v → IsTanAt T (𝟙 _) (v ≫ actT.act r) := by
    intro r v h
    haveI := actT.hom r
    refine (LieTangent.isTanAt_iff _).2 ?_
    rw [← Category.assoc, (LieTangent.isTanAt_iff _).1 h]
    exact MonObj.one_comp _
  choose eV heV using fun i => MT.onto (vV i) (hF.1 i).1
  obtain rfl : vV = fun i => MT.pt (eV i) := funext fun i => (heV i).symm
  have hbj : ∀ i, b i = j (eV i) := fun i => uniq _ _ ((hb i).trans (key1 (eV i)).symm)
  have jcomb : ∀ c : Fin n → V, j (∑ i, c i • eV i) = ∑ i, c i • b i := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hj2, ← hbj, algebraMap_smul]
  constructor
  · intro hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hw
    refine ⟨⟨MT.pt (∑ i, c i • eV i), MT.tan _, ?_⟩, fun r => ?_⟩
    · rw [← jcomb]
      exact key1 _
    · have heig : ∀ i, ρK r (b i) = algebraMap V K (σV r) • b i := by
        intro i
        have h : MT.pt (σV r • eV i) = MT.pt (eV i) ≫ actT.act r :=
          Over.OverMorphism.ext ((MT.smul _ _).trans ((hF.1 i).2 r).symm)
        have h2 := eig r _ _ h
        rw [← hbj i, hj2, ← hbj i] at h2
        exact h2.symm
      have hs : ∀ i, c i • b i = algebraMap V K (c i) • b i := fun i => (algebraMap_smul K (c i) (b i)).symm
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hs, map_sum, map_smul, heig, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · rintro ⟨⟨a, ha, hka⟩, hr⟩
    obtain ⟨e, rfl⟩ := MT.onto a ha
    obtain rfl : w = j e := uniq _ _ (hka.trans (key1 e).symm)
    have hE : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec actT (𝟙 _) σV (MT.pt e) := by
      refine ⟨MT.tan e, fun r => ?_⟩
      obtain ⟨e', he'⟩ := MT.onto _ (htan r _ (MT.tan e))
      have h1 := eig r e e' he'
      rw [hr r, ← hj2] at h1
      rw [← he', hjinj h1]
      exact MT.smul _ _
    obtain ⟨c, hc, -⟩ := hF.2 _ hE
    have he : e = ∑ i, c i • eV i := MT.inj ((LieEigFrame.isComb_pt_iff MT eV c _).1 hc)
    rw [he, jcomb]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.EigLin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrSpecializationLieLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem fibAt_lat_eq_stdLat : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Em : Type) [AddCommGroup Em] [Module Ω Em]
    (M : LieModel G ξ Em) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (x : Sp K ⟶ X) (z : Sp V ⟶ X) (h₁ : genPt ξ ⤳ centre x) (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K) (g : ℕ)
    (ℓ : Fin g → Em) (MX : LieModel G x (Fin g → K)) (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z) (Fin g → K)),
    spMap (algebraMap V K) ≫ z = x → (∀ e, (MC.pt e).left = (MX.pt e).left) → IsCptGen ξ →
    regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ →
    (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    M.lat.IsFrameAt ℓ ⟨_, h₂⟩ →
    (∀ w : Fin g → regAt ξ ⟨_, h₁⟩, M.ValAt x (comb ℓ w) (MX.pt (fun i => ψ (w i)))) →
    M.fibAt M.lat z MC = stdLat V K g := by
  intro X G _ Ω _ ξ Em _ _ M V K _ _ _ _ _ _ x z h₁ h₂ ψ g ℓ MX MC hx hpt hξ hle hint hfr hval
  subst hx
  have hMC : ∀ e, MC.pt e = MX.pt e := fun e => Over.OverMorphism.ext (hpt e)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨h, e, he, hv⟩
    have he' : e ∈ M.lat ⟨_, h₂⟩ := he
    rw [hfr.2] at he'
    obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    have hc : comb ℓ (fun i => (⟨(r i : Ω), hle (r i).2⟩ : regAt ξ ⟨_, h₁⟩)) = ∑ i, r i • ℓ i := rfl
    have h3 := hval (fun i => ⟨(r i : Ω), hle (r i).2⟩)
    rw [hc] at h3
    have e1 := LieModel.ValAt.unique hξ hv h3
    rw [hMC] at e1
    have e2 := MX.inj e1
    intro i
    rw [e2]
    exact hint _ _ (r i).2
  · intro w hw
    have hw' : ∀ i, w i ∈ (algebraMap V K).range := hw
    choose v hv using hw'
    have hsum : w = ∑ i, v i • (Pi.single i 1 : Fin g → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hv]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h₂, ℓ i, ?_, ?_⟩)
    · rw [hfr.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    · have h3 := hval (Pi.single i 1)
      have hc : comb ℓ (Pi.single i 1 : Fin g → regAt ξ ⟨_, h₁⟩) = ℓ i := by
        unfold comb
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      have hs : (fun j => ψ ((Pi.single i 1 : Fin g → regAt ξ ⟨_, h₁⟩) j)) = (Pi.single i 1 : Fin g → K) := by
        ext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [hc, hs] at h3
      rw [hMC]
      exact h3

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLieModelCompleteDvr
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan

open MonObj
open GlobalTheory.CompanionTheory.Ar.LieTangent (epsBase epsScale isTanAt_iff isTanAt_scale spec_dual_eps spec_eps_alg)

section Push

variable (T : CDVR) {X : Scheme.{0}} (zV : Spec (CommRingCat.of T.V) ⟶ X) {A : CategoryTheory.Over X} [GrpObj A]
  {B : CategoryTheory.Over (Spec (CommRingCat.of T.V))} [GrpObj B] {Ψ : B.left ⟶ A.left}

theorem epsOver_hom :
    (epsOver T.V T.V).hom = Spec.map (CommRingCat.ofHom (algebraMap T.V (DualNumber T.V))) :=
  rfl

def idU : epsAt zV ⟶ CategoryTheory.Over.mk ((epsOver T.V T.V).hom ≫ zV) :=
  CategoryTheory.Over.homMk (𝟙 _) (by rw [Category.id_comp]; rfl)

def pushAt (h : IsGrpPullback B A zV Ψ) : (epsOver T.V T.V ⟶ B) →* (epsAt zV ⟶ A) :=
  (preHom (idU T zV)).comp (pushHom h (epsOver T.V T.V))

def pushGen (h : IsGrpPullback B A zV Ψ) : (epsOver T.V T.V ⟶ B) →* (epsAt (gen T zV) ⟶ A) :=
  (preHom (epsBase (algebraMap T.V T.Fr) rfl)).comp (pushAt T zV h)

variable {T zV}

theorem pushAt_left (h : IsGrpPullback B A zV Ψ) (v : epsOver T.V T.V ⟶ B) :
    (pushAt T zV h v).left = v.left ≫ Ψ := by
  simp [pushAt, preHom, pushHom, pushPt, idU]

theorem pushGen_left (h : IsGrpPullback B A zV Ψ) (v : epsOver T.V T.V ⟶ B) :
    (pushGen T zV h v).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  simp [pushGen, preHom, pushAt_left, GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase]
private theorem key_lemma' {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {Y : Scheme.{0}} (zV : Y ⟶ X)
    {f : Y ⟶ X} (hf : f = zV) :
    (1 : CategoryTheory.Over.mk f ⟶ A).left = (1 : CategoryTheory.Over.mk zV ⟶ A).left := by
  subst hf
  rfl

private theorem one_left_comp_of_isGrpPullback_over {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {Tb : CDVR}
    {zV : Spec (CommRingCat.of Tb.V) ⟶ X} {B : CategoryTheory.Over (Spec (CommRingCat.of Tb.V))} [GrpObj B]
    {Ψ : B.left ⟶ A.left} (h : IsGrpPullback B A zV Ψ) (T' : CategoryTheory.Over (Spec (CommRingCat.of Tb.V))) :
    (1 : T' ⟶ B).left ≫ Ψ = (1 : CategoryTheory.Over.mk (T'.hom ≫ zV) ⟶ A).left := by
  have := congrArg CategoryTheory.Over.Hom.left (map_one (pushHom h T'))
  simpa [pushHom, pushPt] using this

theorem one_left (h : IsGrpPullback B A zV Ψ) :
    (1 : ptOver T.V T.V ⟶ B).left ≫ Ψ = (1 : CategoryTheory.Over.mk zV ⟶ A).left := by
  have hf : (ptOver T.V T.V).hom ≫ zV = zV := by
    simp [ptOver, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
  rw [← key_lemma' zV hf]
  exact one_left_comp_of_isGrpPullback_over h (ptOver T.V T.V)

theorem isTanAt_push (h : IsGrpPullback B A zV Ψ) {v : epsOver T.V T.V ⟶ B} (hv : IsTan v) :
    IsTanAt A zV (pushAt T zV h v) := by
  have e : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
      (1 : ptOver T.V T.V ⟶ B).left := hv
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ (pushAt T zV h v).left =
    (1 : CategoryTheory.Over.mk zV ⟶ A).left
  rw [pushAt_left, ← Category.assoc, e]
  exact one_left h

theorem isTan_of_push (h : IsGrpPullback B A zV Ψ) {v : epsOver T.V T.V ⟶ B}
    (hv : IsTanAt A zV (pushAt T zV h v)) : IsTan v := by
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
    (1 : ptOver T.V T.V ⟶ B).left
  have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ (pushAt T zV h v).left =
      (1 : CategoryTheory.Over.mk zV ⟶ A).left := hv
  rw [pushAt_left, ← Category.assoc, ← one_left h] at hv'
  refine h.1.hom_ext hv' ?_
  rw [Category.assoc, CategoryTheory.Over.w v, CategoryTheory.Over.w (1 : ptOver T.V T.V ⟶ B), epsOver_hom,
    GlobalTheory.CompanionTheory.Ar.LieTangent.spec_comp]
  simp [ptOver, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]

theorem pushAt_surj (h : IsGrpPullback B A zV Ψ) (v : epsAt zV ⟶ A) :
    ∃ v' : epsOver T.V T.V ⟶ B, pushAt T zV h v' = v := by
  have hw : v.left ≫ A.hom = (epsOver T.V T.V).hom ≫ zV := by
    rw [CategoryTheory.Over.w v, epsOver_hom]
    rfl
  refine ⟨CategoryTheory.Over.homMk (h.1.lift v.left (epsOver T.V T.V).hom hw) (h.1.lift_snd _ _ _), ?_⟩
  apply CategoryTheory.Over.OverMorphism.ext
  rw [pushAt_left]
  exact h.1.lift_fst _ _ _

end Push

section Model

variable {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {R : Type} [CommRing R]
  {x : Spec (CommRingCat.of R) ⟶ X} {EC : Type} [AddCommGroup EC] [Module R EC]

theorem pt_list_sum (MC : LieModel A x EC) (l : List EC) : MC.pt l.sum = (l.map MC.pt).prod := by
  induction l with
  | nil =>
    simp only [List.sum_nil, List.map_nil, List.prod_nil]
    exact MC.pt_zero
  | cons a l ih => rw [List.sum_cons, MC.add, ih, List.map_cons, List.prod_cons]

theorem pt_sum (MC : LieModel A x EC) {r : ℕ} (f : Fin r → EC) :
    MC.pt (∑ i, f i) = (List.ofFn fun i => MC.pt (f i)).prod := by
  rw [← List.sum_ofFn, pt_list_sum, List.map_ofFn]
  rfl

theorem mem_eigSp_iff {O : Type} [CommRing O] (ρ : O →+* Module.End R EC) (σ : O →+* R) (w : EC) :
    w ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ↔ ∀ a, ρ a w = σ a • w := by
  simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

end Model

section Main

variable (T : CDVR) {X : Scheme.{0}} (zV : Spec (CommRingCat.of T.V) ⟶ X) {A : CategoryTheory.Over X} [GrpObj A]
  {B : CategoryTheory.Over (Spec (CommRingCat.of T.V))} [GrpObj B] {Ψ : B.left ⟶ A.left}

theorem eigen_span_lie_basis (h : IsGrpPullback B A zV Ψ) {O : Type} [CommRing O] (aA : O → (A ⟶ A))
    (hA : ∀ a, IsMonHom (aA a)) (aB : O → (B ⟶ B)) (hc : ∀ a, (aB a).left ≫ Ψ = Ψ ≫ (aA a).left)
    {EC : Type} [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC]
    (MC : LieModel A (FinRd.Roots.gen T zV) EC) (ρC : O →+* Module.End T.Fr EC) (hρ : MC.IsActOf aA ρC)
    (σ : O →+* T.V) {r : ℕ} (ub : Fin r → (epsOver T.V T.V ⟶ B)) (hut : ∀ i, IsTan (ub i))
    (hue : ∀ i a, (ub i ≫ aB a).left =
      Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left)
    (hub : ∀ w : epsOver T.V T.V ⟶ B, IsTan w →
      (∀ a, (w ≫ aB a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) →
      ∃ cf : Fin r → T.V, IsComb ub cf w)
    (yb : Fin r → EC)
    (hyb : ∀ i, (MC.pt (yb i)).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ)
    (L : Submodule T.V EC)
    (hL : ∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ A, GlobalTheory.CompanionTheory.Ar.IsTanAt A zV v ∧
      (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) :
    L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V =
      Submodule.span T.V (Set.range yb) := by
  have hue' : ∀ i a, (ub i ≫ aB a).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (σ a))) ≫ (ub i).left := hue
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V (FractionRing T.V)
  apply le_antisymm
  · rintro w ⟨hwL, hwE⟩
    obtain ⟨v, hvt, hvl⟩ := (hL w).1 hwL
    obtain ⟨v', rfl⟩ := pushAt_surj h v
    have hv't := isTan_of_push h hvt
    have hwE' : ∀ a, ρC a w = ((algebraMap T.V T.Fr).comp σ) a • w := (mem_eigSp_iff _ _ _).1 hwE
    have hpw : MC.pt w = pushGen T zV h v' := by
      apply CategoryTheory.Over.OverMorphism.ext
      rw [pushGen_left, hvl, pushAt_left]
    have hv'e : ∀ a, (v' ≫ aB a).left =
        Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ v'.left := by
      intro a
      have hp := isTanAt_push h hv't
      have ht1 : GlobalTheory.CompanionTheory.Ar.IsTanAt A zV (pushAt T zV h v' ≫ aA a) := by
        have hp' := hp
        unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at hp' ⊢
        rw [CategoryTheory.Over.comp_left, ← Category.assoc, hp', ← CategoryTheory.Over.comp_left]
        have := hA a
        simp
      have ht2 : GlobalTheory.CompanionTheory.Ar.IsTanAt A zV (GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale zV (σ a) ≫ pushAt T zV h v') :=
        isTanAt_scale (σ a) hp
      have eq1 : pushAt T zV h v' ≫ aA a = GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale zV (σ a) ≫ pushAt T zV h v' := by
        refine GlobalTheory.CompanionTheory.Ar.LieTangent.tan_ext hinj ht1 ht2 ?_
        have e1 := congrArg CategoryTheory.Over.Hom.left (hρ a w)
        rw [hwE' a, MC.smul, hpw, CategoryTheory.Over.comp_left, pushGen_left] at e1
        simp only [CategoryTheory.Over.comp_left, pushAt_left, Category.assoc] at e1 ⊢
        rw [← e1]
        simp only [GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale, CategoryTheory.Over.homMk_left]
        simp only [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]
      refine h.1.hom_ext ?_ ?_
      · rw [CategoryTheory.Over.comp_left, Category.assoc, hc a, ← Category.assoc, ← pushAt_left h v',
          ← CategoryTheory.Over.comp_left, eq1, CategoryTheory.Over.comp_left, pushAt_left]
        simp only [GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale, CategoryTheory.Over.homMk_left, Category.assoc]
        rfl
      · rw [CategoryTheory.Over.w (v' ≫ aB a), Category.assoc, CategoryTheory.Over.w v', epsOver_hom]
        exact (GlobalTheory.CompanionTheory.Ar.LieTangent.spec_eps_alg (σ a)).symm
    obtain ⟨cf, hcf⟩ := hub v' hv't hv'e
    obtain ⟨u, hu, hv'u⟩ := hcf
    have hw : w = ∑ i, cf i • yb i := by
      apply MC.inj
      rw [hpw, pt_sum, hv'u, map_list_prod, List.map_ofFn]
      congr 1
      apply congrArg List.ofFn
      funext i
      apply CategoryTheory.Over.OverMorphism.ext
      rw [Function.comp_apply, pushGen_left, hu i, ← algebraMap_smul T.Fr (cf i) (yb i), MC.smul, hyb i]
      simp only [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
      rw [show Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (cf i))) =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (cf i))) from rfl, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨(hL _).2 ⟨pushAt T zV h (ub i), isTanAt_push h (hut i), by rw [hyb i, pushAt_left]⟩, ?_⟩
    show yb i ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)
    rw [mem_eigSp_iff]
    intro a
    apply MC.inj
    apply CategoryTheory.Over.OverMorphism.ext
    rw [hρ a (yb i), MC.smul, CategoryTheory.Over.comp_left, hyb i]
    simp only [Category.assoc]
    rw [← hc a, ← Category.assoc (ub i).left, ← CategoryTheory.Over.comp_left, hue' i a]
    simp only [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]

end Main

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan

theorem GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → (∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left) → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf tX.act.act ρC → ∀ (σ : 𝓞 E →+* T.V) (r : ℕ) (ub : Fin r → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i a, (ub i ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → (∀ a, (w ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) → ∃ cf : Fin r → T.V, IsComb ub cf w) → ∀ yb : Fin r → EC, (∀ i, (MC.pt (yb i)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ) → ∀ L : Submodule T.V EC, (∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ tX.G, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G zV v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) → L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V = Submodule.span T.V (Set.range yb) := by
  intro E _ _ _ H X tX T zV G Ψ h hc EC _ _ _ _ MC ρC hρ σ r ub hut hue hub yb hyb L hL
  exact eigen_span_lie_basis T zV h tX.act.act tX.act.hom G.act.act hc MC ρC hρ σ ub hut hue hub yb hyb L hL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointAbelianMapCompat
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open CategoryTheory.Limits

theorem genFibre_pullback_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (y : FrPt Xo c F) (t' : SAB H (Spec (CommRingCat.of F))) (m1 : SABMap t' Xo.univ.t y.x) (g : Spec (CommRingCat.of F) ⟶ X), Small.ptY Y y = g ≫ f → ∃ b : t'.G.left ⟶ tX.G.left, IsGrpPullback t'.G tX.G g b ∧ (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (u' : Spec (CommRingCat.of (DualNumber F)) ⟶ t'.G.left), u' ≫ m1.φ = y.u τ i → u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) → u' ≫ b ≫ m.φ = Small.tanY Y y τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ y t' m1 g hg
  have wa : m1.φ ≫ Xo.univ.t.G.hom = (t'.G.hom ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [m1.cart.1.w, Category.assoc, Small.ptF_fst]
  let a : t'.G.left ⟶ Y.oF.t.G.left := Y.m0.cart.1.lift m1.φ (t'.G.hom ≫ Small.ptF y) wa
  have ha1 : a ≫ Y.m0.toSABMap.φ = m1.φ := IsPullback.lift_fst _ _ _ _
  have ha2 : a ≫ Y.oF.t.G.hom = t'.G.hom ≫ Small.ptF y := IsPullback.lift_snd _ _ _ _
  have gpa : IsGrpPullback t'.G Y.oF.t.G (Small.ptF y) a :=
    IsGrpPullback.cancel Y.m0.cart (m1.cart.congr (Small.ptF_fst y).symm ha1.symm) ha2
  have gpY : IsGrpPullback t'.G Y.t.G (g ≫ f) (a ≫ Y.m.φ) := (gpa.comp Y.m.cart).congr hg rfl
  have wb : (a ≫ Y.m.φ) ≫ Y.t.G.hom = (t'.G.hom ≫ g) ≫ f := by
    rw [gpY.1.w, Category.assoc]
  let b : t'.G.left ⟶ tX.G.left := m.cart.1.lift (a ≫ Y.m.φ) (t'.G.hom ≫ g) wb
  have hb1 : b ≫ m.φ = a ≫ Y.m.φ := IsPullback.lift_fst _ _ _ _
  have hb2 : b ≫ tX.G.hom = t'.G.hom ≫ g := IsPullback.lift_snd _ _ _ _
  have acta : ∀ r, (t'.act.act r).left ≫ a = a ≫ (Y.oF.t.act.act r).left := by
    intro r
    apply Y.m0.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha1, Y.m0.act r, ← Category.assoc, ha1, m1.act r]
    · rw [Category.assoc, Category.assoc, ha2, Over.w (Y.oF.t.act.act r), ha2, ← Category.assoc,
        Over.w (t'.act.act r)]
  refine ⟨b, IsGrpPullback.cancel m.cart (gpY.congr rfl hb1.symm) hb2, fun r => ?_, fun τ i u' h1 h2 => ?_⟩
  · apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hb1, m.act r, ← Category.assoc b, hb1, Category.assoc, ← Y.m.act r,
        ← Category.assoc, acta r, Category.assoc]
    · rw [Category.assoc, Category.assoc, hb2, Over.w (tX.act.act r), hb2, ← Category.assoc,
        Over.w (t'.act.act r)]
  · have e : u' ≫ a = Small.tanF Y y τ i := by
      apply Small.eq_tanF
      · rw [Category.assoc, ha1, h1]
      · rw [Category.assoc, ha2, ← Category.assoc, h2]
    rw [hb1, ← Category.assoc, e]
    rfl

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

