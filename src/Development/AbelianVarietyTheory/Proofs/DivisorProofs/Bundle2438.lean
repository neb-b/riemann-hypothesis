module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPrincipallyPolarisedAbelianScheme
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SumPol

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.PolProd

theorem exists_isPullback_restrict {X Y Z S : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (P : IsPullback p q f g) (h : Z ⟶ S) (hh : p ≫ f = h) (U : S.Opens) :
    ∃ (p' : (h ⁻¹ᵁ U).toScheme ⟶ (f ⁻¹ᵁ U).toScheme) (q' : (h ⁻¹ᵁ U).toScheme ⟶ (g ⁻¹ᵁ U).toScheme),
      p' ≫ (f ⁻¹ᵁ U).ι = (h ⁻¹ᵁ U).ι ≫ p ∧ q' ≫ (g ⁻¹ᵁ U).ι = (h ⁻¹ᵁ U).ι ≫ q ∧
        IsPullback p' q' (f ∣_ U) (g ∣_ U) := by
  have Hf := isPullback_morphismRestrict f U
  have Hg := isPullback_morphismRestrict g U
  have Hh := isPullback_morphismRestrict h U
  have w₁ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ p) ≫ f := by rw [Category.assoc, hh, Hh.w]
  have w₂ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ q) ≫ g := by rw [Category.assoc, ← P.w, hh, Hh.w]
  refine ⟨Hf.lift _ _ w₁, Hg.lift _ _ w₂, Hf.lift_snd _ _ _, Hg.lift_snd _ _ _, ?_⟩
  have A : IsPullback (Hf.lift _ _ w₁) (h ⁻¹ᵁ U).ι (f ⁻¹ᵁ U).ι p := by
    refine IsPullback.of_right ?_ (Hf.lift_snd _ _ _) Hf
    rw [Hf.lift_fst, hh]
    exact Hh
  have B := A.paste_vert P
  refine IsPullback.of_bot ?_ (by rw [Hf.lift_fst, Hg.lift_fst]) Hg
  rw [Hg.lift_snd, Hf.w]
  exact B

theorem relAmple_prod {S : Scheme.{0}} (A B : Over S) [IsProper A.hom] [IsProper B.hom] [IsProper (A ⊗ B).hom]
    {L : LB A.left} {M : LB B.left} {N : LB (A ⊗ B).left} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (e : cls N hN = pull (fst A B).left (cls L hL) + pull (snd A B).left (cls M hM))
    (aL : RelAmple A L) (aM : RelAmple B M) : RelAmple (A ⊗ B) N := by
  refine (relAmple_iff_isAmpleLB _ hN).2 fun U hU => ?_
  obtain ⟨p', q', hp, hq, H⟩ := exists_isPullback_restrict (p := (fst A B).left) (q := (snd A B).left)
    (f := A.hom) (g := B.hom) (IsPullback.of_hasPullback _ _) (A ⊗ B).hom (Over.w _) U
  have : IsAffine U := hU
  have h₀ := pull_isLB hN ((A ⊗ B).hom ⁻¹ᵁ U).ι
  have h₁ := pull_isLB (pull_isLB hL (A.hom ⁻¹ᵁ U).ι) p'
  have h₂ := pull_isLB (pull_isLB hM (B.hom ⁻¹ᵁ U).ι) q'
  refine IsAmpleLB.box ((relAmple_iff_isAmpleLB _ hL).1 aL U hU) ((relAmple_iff_isAmpleLB _ hM).1 aM U hU) h₀ H
    ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div h₀ h₁) h₂)).1 ?_)
  rw [cls_div (LB.isLB_div h₀ h₁) h₂, cls_div h₀ h₁, cls_pull hN, e, cls_pull (pull_isLB hL _), cls_pull hL,
    cls_pull (pull_isLB hM _), cls_pull hM, map_add, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, hp, hq]
  abel

theorem exists_sum_polAV : ∀ (S : Scheme.{0}) (P₁ P₂ : PolAV S), ∃ (P : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A), IsSumPolAV P P₁ P₂ a₁ a₂ ∧ P.L = extLB P₁.L P₂.L a₁.left a₂.left := by
  intro S P P'
  have hB : IsAbelianScheme (P.A ⊗ P'.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb
  let p := fst P.A P'.A
  let q := snd P.A P'.A
  let M : LB (P.A ⊗ P'.A).left := extLB P.L P'.L p.left q.left
  have hM : M.IsLB := isLB_tens (pull_isLB P.isLB p.left) (pull_isLB P'.isLB q.left)
  have eM : cls M hM = pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB) := rfl
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := hB.proper
  have hdim : SmoothOfRelativeDimension (P.g + P'.g) (P.A ⊗ P'.A).hom := by
    haveI := P.smoothDim
    haveI : SmoothOfRelativeDimension P'.g (pullback.fst P.A.hom P'.A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip P'.smoothDim
    rw [add_comm]
    exact inferInstanceAs (SmoothOfRelativeDimension (P'.g + P.g) (pullback.fst P.A.hom P'.A.hom ≫ P.A.hom))
  have hrig : Rigidified (P.A ⊗ P'.A) M := by
    rw [rigidified_iff _ hM, eM, map_add (f := _), ← pull_comp, ← pull_comp, eSec_comp p, eSec_comp q,
      (rigidified_iff _ P.isLB).1 P.rigid, (rigidified_iff _ P'.isLB).1 P'.rigid, add_zero]
  have hsym : Out.Sym (P.A ⊗ P'.A) M := by
    have h₁ := ((sym_iff _ P.isLB).1 P.sym).pull_over (π' := (P.A ⊗ P'.A).hom) p.left (Over.w p)
    have h₂ := ((sym_iff _ P'.isLB).1 P'.sym).pull_over (π' := (P.A ⊗ P'.A).hom) q.left (Over.w q)
    rw [sym_iff _ hM, eM]
    convert locZero_add h₁ h₂ using 1
    rw [map_add (f := _), map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, inv_comp_left p,
      inv_comp_left q]
    abel
  refine ⟨⟨P.A ⊗ P'.A, hB, P.g + P'.g, hdim, M, hM, hrig, hsym,
    relAmple_prod _ _ P.isLB P'.isLB hM eM P.ample P'.ample,
    kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩, p, q,
    ⟨inferInstance, inferInstance, ?_, PolBaseChange.lbIso_refl hM⟩, rfl⟩
  show IsIso (lift (fst P.A P'.A) (snd P.A P'.A))
  rw [lift_fst_snd]
  infer_instance

end GlobalTheory.MumProd.SumPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMapOfModelHasDiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdMap

open GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.QCoh.Qcqs

theorem pCrd_pt {o A : Type} [CommRing o] [CommRing A] {n : ℕ} (c : o →+* A) (v : Fin (n + 1) → A)
    (hv : Ideal.span (Set.range v) = ⊤) : PCrd (pt c v hv) v := by
  have hφ := toProj_coord o n
  have hstr : pt c v hv ≫ PSpace.str o n = spMap c := by
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  have h1 := (ProjCoord.secCoord_iff (Equiv.refl _) (toProj (PSpace.str o n) (coord o n) (iSup_nonzeroLocus_coord o n))
    c (pt c v hv) (by rw [hφ, Category.comp_id]; exact hstr) v).2 ⟨by simpa using hv, by rw [hφ, Category.comp_id]; rfl⟩
  exact (FibreEmbed.secCoord_iff_of_secMaps (LB.isLB_pull (O1_isLB o n) _) (O1_isLB o n)
    (fun j => secMaps_toProjIso _ _ _ j) (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord o n) _)
    (iSup_nonzeroLocus_coord o n)).1 h1

section Map

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {n : ℕ} (c : Fin (n + 1) → Ω)

def dOpen (i : Fin (n + 1)) : M.Z.Opens := ⟨{z | M.Div c i z}, M.isOpen_setOf_div c i⟩

theorem subsingleton_of_not_nonempty {X : Scheme.{0}} {V : X.Opens} (hV : ¬ (V : Set X).Nonempty) :
    Subsingleton Γ(X, V) := by
  have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
  subst this
  infer_instance


variable {M} in
theorem eq_of_valF {V : M.Z.Opens} {f g : Γ(M.Z, V)}
    (h : ∀ hV : (V : Set M.Z).Nonempty, valF M.pt V f = valF M.pt V g) : f = g := by
  by_cases hV : (V : Set M.Z).Nonempty
  · exact M.valF_injective hV (h hV)
  · have := subsingleton_of_not_nonempty hV
    exact Subsingleton.elim _ _


open Classical in
def fnOf (V : M.Z.Opens) (x : Ω) : Γ(M.Z, V) :=
  if h : ∃ f : Γ(M.Z, V), valF M.pt V f = x then h.choose else 0


variable {M} in
theorem valF_fnOf {V : M.Z.Opens} {x : Ω} (h : ∃ f : Γ(M.Z, V), valF M.pt V f = x) :
    valF M.pt V (fnOf M V x) = x := by
  rw [fnOf, dite_eq_left h]
  exact h.choose_spec

def ratioFn (i j : Fin (n + 1)) : Γ(M.Z, dOpen M c i) := fnOf M (dOpen M c i) (c j / c i)

variable {M c}

theorem valF_ratioFn {i j : Fin (n + 1)} {V : M.Z.Opens} (hV : V ≤ dOpen M c i) (hne : (V : Set M.Z).Nonempty) :
    valF M.pt V (resG M.Z hV (ratioFn M c i j)) = c j / c i := by
  have hne' : ((dOpen M c i : M.Z.Opens) : Set M.Z).Nonempty := hne.mono hV
  rw [M.valF_resG hV hne, ratioFn, valF_fnOf]
  exact (RatModel.mem_ringOn_iff_exists hne').1 (RatModel.mem_ringOn.2 fun z hz => hz.2 j)

theorem valF_one' {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) : valF M.pt V 1 = 1 := by
  rw [← M.res_apply V hne, map_one]

theorem valF_mul' {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) (f g : Γ(M.Z, V)) :
    valF M.pt V (f * g) = valF M.pt V f * valF M.pt V g := by
  rw [← M.res_apply V hne, map_mul, M.res_apply, M.res_apply]

theorem isCoordFamily_ratioFn (hd : M.HasDiv c) : IsCoordFamily (dOpen M c) (ratioFn M c) := by
  refine { cover := top_le_iff.1 fun z _ => TopologicalSpace.Opens.mem_iSup.2 (hd z)
           self := ?_, mul := ?_, basicOpen_le := ?_ }
  · intro i
    refine eq_of_valF fun hne => ?_
    obtain ⟨z, hz⟩ := hne
    have := valF_ratioFn (j := i) (le_refl (dOpen M c i)) ⟨z, hz⟩
    rw [resG_self] at this
    rw [this, valF_one' ⟨z, hz⟩, div_self hz.1]
  · intro i j k
    refine eq_of_valF fun hne => ?_
    obtain ⟨z, hz⟩ := hne
    rw [valF_mul' ⟨z, hz⟩, valF_ratioFn _ ⟨z, hz⟩, valF_ratioFn _ ⟨z, hz⟩, valF_ratioFn _ ⟨z, hz⟩]
    have h1 := hz.1.1
    have h2 := hz.2.1
    field_simp
  · intro i j z hz
    have hzi : z ∈ dOpen M c i := M.Z.basicOpen_le _ hz
    have hu := (RatModel.isUnit_valF_iff hzi (ratioFn M c i j)).2 hz
    have e : valF M.pt (dOpen M c i) (ratioFn M c i j) = c j / c i := by
      have := valF_ratioFn (j := j) (le_refl (dOpen M c i)) ⟨z, hzi⟩
      rwa [resG_self] at this
    have e' : (⟨valF M.pt (dOpen M c i) (ratioFn M c i j), RatModel.valF_mem_O hzi _⟩ : M.O z) =
        ⟨c j / c i, (show M.Div c i z from hzi).2 j⟩ := Subtype.ext e
    rw [e'] at hu
    exact ((show M.Div c i z from hzi).div_iff_isUnit j).2 hu

end Map

section Main

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {n : ℕ} {c : Fin (n + 1) → Ω}

theorem appLE_eq_fnOn {X : Scheme.{0}} (x : Sp Ω ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    (x.appLE U ⊤ h).hom f = fnOn ⊤ (valF x U f) := by
  rw [valF, dite_eq_left h, fnOn, RingHom.comp_apply, resG_self]
  simp

theorem pt_comp_toHom (hd : M.HasDiv c) (hc : Ideal.span (Set.range c) = ⊤) :
    M.pt ≫ (isCoordFamily_ratioFn hd).toHom M.s = pt (algebraMap o Ω) c hc := by
  let _ := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := o)
  set H := isCoordFamily_ratioFn hd
  obtain ⟨i, hi⟩ := hd (genericPoint M.Z)
  have hpt : ⊤ ≤ M.pt ⁻¹ᵁ dOpen M c i := M.top_le_preimage_pt ⟨_, RatModel.div_genericPoint hi.1⟩
  have h₁ : ⊤ ≤ (M.pt ≫ H.toHom M.s) ⁻¹ᵁ chart o n i :=
    GlobalTheory.Points.le_preimage_comp M.pt _ (H.le_toHom_preimage M.s i) hpt
  have hchart : pt (algebraMap o Ω) c hc ⁻¹ᵁ chart o n i = spOpen (c i) := by
    rw [pt, chart, ProjPoint.ofHom_preimage_basicOpen _ _ _ one_pos (X_mem o n i),
      MvPolynomial.eval₂Hom_X']
    rfl
  have h₂ : ⊤ ≤ pt (algebraMap o Ω) c hc ⁻¹ᵁ chart o n i := by
    rw [hchart]
    exact fun y _ => mem_spOpen.2 fun hm => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (Ne.isUnit hi.1))
  have hstr : pt (algebraMap o Ω) c hc ≫ PSpace.str o n = spMap (algebraMap o Ω) := by
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C (algebraMap o Ω) c r
  refine hom_ext (by rw [Category.assoc, H.toHom_str, M.pt_s, hstr]) fun _ => ⟨⊤, trivial, i, h₁, h₂, fun j => ?_⟩
  have hratio : pullRatio (pt (algebraMap o Ω) c hc) ⊤ i h₂ j * fnOn ⊤ (c i) = fnOn ⊤ (c j) := by
    let β := algebraMap o Ω
    have hunit : IsUnit (MvPolynomial.eval₂Hom β c (MvPolynomial.X i)) := by
      rw [MvPolynomial.eval₂Hom_X']
      exact Ne.isUnit hi.1
    have haway : pt β c hc =
        spMap (ProjPoint.awayLift (grading o n) (MvPolynomial.eval₂Hom β c) (MvPolynomial.X i) hunit) ≫ _ :=
      ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem o n i) hunit
    have heval := ProjPoint.awayLift_mk_mul (grading o n) (MvPolynomial.eval₂Hom β c) hunit
      (X_mem o n i) 1 (MvPolynomial.X j) (X_mem o n j)
    rw [pullRatio_of_eq haway h₂ (haway ▸ h₂), pullRatio_spMap_awayι, ← map_mul]
    exact congrArg _ (by simpa only [ratioAway, MvPolynomial.eval₂Hom_X', pow_one] using heval)
  have hu : IsUnit (fnOn (⊤ : (Sp Ω).Opens) (c i)) := (Ne.isUnit hi.1).map _
  refine hu.mul_right_cancel ?_
  rw [hratio, ← appLE_pullRatio (φ := H.toHom M.s) (hi := H.le_toHom_preimage M.s i) M.pt hpt, H.pullRatio_toHom,
    appLE_eq_fnOn, ← map_mul]
  congr 1
  have := valF_ratioFn (M := M) (c := c) (j := j) (le_refl (dOpen M c i)) ⟨_, RatModel.div_genericPoint hi.1⟩
  rw [resG_self] at this
  rw [this, div_mul_cancel₀ _ hi.1]

theorem exists_map_of_hasDiv : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ)
    (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace k n, h ≫ PSpace.str k n = M.s ∧ PCrd (M.pt ≫ h) c := by
  intro k Ω _ _ _ M n c hd
  obtain ⟨i, hi⟩ := hd (genericPoint M.Z)
  have hc : Ideal.span (Set.range c) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (Ne.isUnit hi.1)
  refine ⟨(isCoordFamily_ratioFn hd).toHom M.s, (isCoordFamily_ratioFn hd).toHom_str M.s, ?_⟩
  rw [pt_comp_toHom hd hc]
  exact pCrd_pt _ c hc

end Main

end GlobalTheory.UMin.CrdMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpacePointOfUnitCoordinate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem exists_pCrd_of_isUnit : ∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (β : o →+* R) (v : Fin (n + 1) → R),
    (∃ j, IsUnit (v j)) → ∃ ξ : Sp R ⟶ PSpace o n, ξ ≫ PSpace.str o n = spMap β ∧ PCrd ξ v := by
  intro o R _ _ n β v ⟨j, hj⟩
  have hv : Ideal.span (Set.range v) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) hj
  have hstr : GlobalTheory.ProjSpace.pt β v hv ≫ PSpace.str o n = spMap β := by
    rw [GlobalTheory.ProjSpace.pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C β v r
  refine ⟨GlobalTheory.ProjSpace.pt β v hv, hstr, ?_⟩
  have h1 := (GlobalTheory.ZM.ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) β (GlobalTheory.ProjSpace.pt β v hv)
    (by rw [Category.comp_id, hstr]) v).2 ⟨hv, Category.comp_id _⟩
  have h2 := (GlobalTheory.ZM.RepBC.secCoord_pull (GlobalTheory.ProjSpace.O1 o n) (GlobalTheory.ProjSpace.coord o n) (𝟙 _) _ v).1 h1
  rwa [Category.comp_id] at h2

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOnRescale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullDegResc

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.RescaleLift
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_fnOn_le {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) {W : (Sp R₀).Opens}
    (hle : W ≤ (Sp R₀).basicOpen (fnSp R₀ f)) : IsUnit (fnOn W r) := by
  have e := appTop_fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) (RingHom.id R₀) ((Sp R₀).homOfLE hle) W.ι (by
    rw [Scheme.homOfLE_ι]
    exact (Category.comp_id _).symm.trans (congrArg (W.ι ≫ ·) (Spec.map_id _).symm)) r
  have := (isUnit_fnOn f r N hr).map ((Sp R₀).homOfLE hle).appTop.hom
  rw [e] at this
  exact this

theorem gm_mono {R₀ K : Type} [CommRing R₀] [Field K] (W : (Sp R₀).Opens) (α : R₀ →+* K) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp K) (h : t ≫ W.ι = s ≫ spMap α) {I : Type} [Fintype I] (a : I → R₀)
    (ha : ∀ k, IsUnit (fnOn W (a k))) (h0 : ∀ k, α (a k) ≠ 0) (n : I → ℤ) (v : Kˣ)
    (hv : (v : K) = ∏ k, α (a k) ^ n k) (z : Z) :
    gm t z ⊤ (∏ k, (ha k).unit ^ n k) = gm s z ⊤ (unitOn v) := by
  obtain rfl : v = ∏ k, Units.mk0 (α (a k)) (h0 k) ^ n k := Units.ext (by
    rw [hv]; simp)
  show _ = GlobalTheory.TauTwist.unitAt s z _
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  exact congrArg (· ^ n k) (gm_fnOn W α t s h (a k) _ _ (ha k).unit_spec rfl z)

theorem exists_psiOn_rescale {R₀ : Type} [CommRing R₀] [IsDomain R₀] (D₁ : DegPre R₀) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    {W W' : (Sp R₀).Opens} (ψ : PsiOn D₁ W) (hle : W' ≤ W) (u : D₁.X → Γ(W'.toScheme, ⊤)ˣ)
    (hu : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (s : Z ⟶ (TK R₀).left), t ≫ W'.ι = s ≫ jK R₀ → ∀ z,
      gm t z ⊤ (u y) = gm s z ⊤ (unitOn (κ₀ y))) :
    ∃ ψW : PsiOn (GlobalTheory.PolDeg.rescale D₁ κ₀) W', ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J,
      Good D₁.P.L z J → val (ψW.psi y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ (Sp R₀).homOfLE hle) z J := by
  let m : W'.toScheme ⟶ W.toScheme := (Sp R₀).homOfLE hle
  have hm : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have hφ : ∀ y : D₁.X, m ≫ (toUnit (TW W) ≫ D₁.c y).left = (toUnit (TW W') ≫ D₁.c y).left := fun y => by
    show m ≫ W.ι ≫ (D₁.c y).left = W'.ι ≫ (D₁.c y).left
    rw [← Category.assoc, hm]
  choose b hb vb using fun y : D₁.X => exists_gen D₁.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W') ≫ D₁.c y).left) (ε' := fun _ => -1)
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) (hφ y))
    (GlobalTheory.UU.scaleGen (u y) (LB.pullGen D₁.P.L _ _ (ψ.psi y) m))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m))
  have ev : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J, Good D₁.P.L z J →
      val (b y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ m) z J := fun y Z t z J hJ =>
    (vb y Z t z J hJ).trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  refine ⟨{ psi := b, psi_gen := hb, psi_eq := fun y => corr_of_val D₁.P.isLB fun z J hJ => ?_ }, ev⟩
  refine (val_pull hJ _ _ _).trans ((ev y _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine (congrArg₂ (· * ·) ?_ ?_).trans (GlobalTheory.UU.val_scaleGen (unitOn (κ₀ y)) (D₁.psi y) _ hJ).symm
  · refine hu y _ _ ?_ z
    rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  · refine GlobalTheory.ArcSpecialise.psiOn_generic ψ y _ _ ?_ hJ
    rw [Category.assoc, hm, Category.id_comp, Category.id_comp, morphismRestrict_ι]

theorem exists_rescale {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    (κ : D.X → (FractionRing R)ˣ) {I : Type} [Fintype I] (s : I → R₀) (hs : ∀ k, φ (s k) ≠ 0) (n : D₁.X → I → ℤ)
    (h₀ : ∀ y, (κ₀ y : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k)
    (h₁ : ∀ x, (κ x : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) :
    ∃ h' : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ), proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  classical
  have hf : φ (∏ k, s k) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hs k
  set f := ∏ k, s k with hfd
  set W' : (Sp R₀).Opens := h.W ⊓ (Sp R₀).basicOpen (fnSp R₀ f) with hW'
  have hsq : jK R ≫ specOf φ = 𝟙 (TK R).left ≫ spMap ((algebraMap R (FractionRing R)).comp φ) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R (FractionRing R)))).symm
  have hpre : (jK R ≫ specOf φ) ⁻¹ᵁ (Sp R₀).basicOpen (fnSp R₀ f) = ⊤ := by
    rw [Scheme.preimage_basicOpen]
    refine Scheme.basicOpen_of_isUnit _ ?_
    rw [hsq]
    refine (congrArg IsUnit (appTop_comp_spMap ((algebraMap R (FractionRing R)).comp φ) (𝟙 _) f)).mpr ?_
    exact ((IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf)).map (fnSp _)).map
      (Scheme.Hom.appTop (𝟙 (Sp (FractionRing R)))).hom
  obtain ⟨g, hg⟩ : ∃ g : (TK R).left ⟶ (TW W').left, g ≫ W'.ι = jK R ≫ specOf φ :=
    ⟨IsOpenImmersion.lift W'.ι (jK R ≫ specOf φ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, (show y ∈ (jK R ≫ specOf φ) ⁻¹ᵁ (Sp R₀).basicOpen (fnSp R₀ f) from hpre.ge trivial)⟩
      rw [← h.g_comm]
      exact (h.g y).2), IsOpenImmersion.lift_fac _ _ _⟩
  have hle : W' ≤ h.W := inf_le_left
  have hU : ∀ k, IsUnit (fnOn W' (s k)) := fun k =>
    isUnit_fnOn_le f _ 1 (by rw [pow_one]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) inf_le_right
  have s0 : ∀ k, algebraMap R₀ (FractionRing R₀) (s k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective R₀ _)).2 fun e => hs k (by rw [e, map_zero])
  obtain ⟨ψW, hψW⟩ := exists_psiOn_rescale D₁ κ₀ h.psiW hle (fun y => ∏ k, (hU k).unit ^ n y k)
    (fun y Z t r e z => gm_mono W' (algebraMap R₀ (FractionRing R₀)) t r e s hU s0 (n y) _ (h₀ y) z)
  have hgm : g ≫ (Sp R₀).homOfLE hle = h.g := by
    rw [← cancel_mono h.W.ι, Category.assoc, Scheme.homOfLE_ι, hg, h.g_comm]
  have hv : ∀ (x : D.X) (z : (TK R).left) J J', Good D₁.P.L z J → Good D.P.L z J' →
      val (ψW.psi (h.xe x)) g z J = (om h.w z J J' (D.xK x))⁻¹ * val ((GlobalTheory.PolDeg.rescale D κ).psi x) (𝟙 _) z J' :=
    fun x z J J' hJ hJ' => by
    rw [hψW _ g z J hJ, hgm]
    have e1 := GlobalTheory.PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
    rw [Category.id_comp] at e1
    have e2 : val ((GlobalTheory.PolDeg.rescale D κ).psi x) (𝟙 _) z J' =
        gm (𝟙 (TK R).left) z ⊤ (unitOn (κ x)) * val (D.psi x) (𝟙 _) z J' :=
      GlobalTheory.UU.val_scaleGen (unitOn (κ x)) (D.psi x) (𝟙 _) hJ'
    have e3 := gm_mono W' ((algebraMap R (FractionRing R)).comp φ) g (𝟙 _) (by rw [hg, hsq]) s hU
      (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs k)) (n (h.xe x)) (κ x) (h₁ x) z
    rw [e3, e1, e2, mul_left_comm]
    simp only [om, Category.id_comp]
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap φ) (proj h) := pull_grp h
  have hr : PMaps (K := PUnit) h.w (fun _ => eSec D.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D.rig D₁.rig (spMap φ) :=
    GlobalTheory.FieldPull.pmaps_rig h
  have hc : ∀ x : D.X, (D.c x).left ≫ proj h = spMap φ ≫ (D₁.c (h.xe x)).left := h.c_pr
  have hw : PGen h.w := (isGen_iff h.w).1 h.w_gen
  obtain ⟨hD, k₁, k₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW (GlobalTheory.PolDeg.rescale D₁ κ₀)
    (GlobalTheory.PolDeg.rescale D κ) ψW g hg gp h.w hw hr h.xe hc hv
  exact ⟨hD, k₁, k₂⟩

theorem rescale_inv {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (x : D.X) :
    (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) fun y => (g y)⁻¹).psi x = D.psi x :=
  GlobalTheory.TorusExt.gen_ext_val D.P.isLB ((GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) fun y => (g y)⁻¹).psi_gen x)
    (D.psi_gen x) fun y J hJ => by
      refine (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (GlobalTheory.UU.val_scaleGen _ _ _ hJ)).trans ?_)
      show GlobalTheory.TauTwist.unitAt _ y (g x)⁻¹ * (GlobalTheory.TauTwist.unitAt _ y (g x) * _) = _
      rw [map_inv, inv_mul_cancel_left]

theorem exists_withPsi {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (ψ₁ : GlobalTheory.TauTwist.PsiFam D₁) (g₁ : ∀ χ, (ψ₁ χ).IsGen)
    (ψ : GlobalTheory.TauTwist.PsiFam D) (g : ∀ χ, (ψ χ).IsGen) (e₁ : D₁.psi = ψ₁) (e : D.psi = ψ) :
    ∃ h' : IsPullDeg φ (GlobalTheory.TauTwist.withPsi D₁ ψ₁ g₁) (GlobalTheory.TauTwist.withPsi D ψ g),
      proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  subst e₁ e
  exact ⟨h, rfl, fun _ => rfl⟩

theorem exists_unscale {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ)
    (h : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ)) {I : Type} [Fintype I] (s : I → R₀)
    (hs : ∀ k, φ (s k) ≠ 0) (n : D₁.X → I → ℤ)
    (h₀ : ∀ y, (((κ₀ y)⁻¹ : (FractionRing R₀)ˣ) : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k)
    (h₁ : ∀ x, (((κ x)⁻¹ : (FractionRing R)ˣ) : FractionRing R) =
      ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) :
    ∃ h' : IsPullDeg φ D₁ D, proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x := by
  obtain ⟨h₂, a₁, a₂⟩ := exists_rescale h (fun y => (κ₀ y)⁻¹) (fun y => (κ y)⁻¹) s hs n h₀ h₁
  obtain ⟨h₃, b₁, b₂⟩ := exists_withPsi h₂ D₁.psi D₁.psi_gen D.psi D.psi_gen (funext (rescale_inv D₁ κ₀))
    (funext (rescale_inv D κ))
  exact ⟨h₃, b₁.trans a₁, fun x => (b₂ x).trans (a₂ x)⟩

theorem exists_rescale_inv {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R}
    {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ : D.X → (FractionRing R)ˣ) :
    ∃ h' : IsPullDeg φ D₁ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹),
      proj h' = proj h ∧ ∀ x, h'.xe x = h.xe x :=
  exists_withPsi h D₁.psi D₁.psi_gen _ ((GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹).psi_gen) rfl
    (funext (rescale_inv D κ)).symm

theorem main : (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ) {I : Type} [Fintype I] (s : I → R₀), (∀ k, φ (s k) ≠ 0) → ∀ n : D₁.X → I → ℤ, (∀ y, (κ₀ y : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k) → (∀ x, (κ x : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) → ∃ h' : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ), h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) ∧ (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (κ₀ : D₁.X → (FractionRing R₀)ˣ) (κ : D.X → (FractionRing R)ˣ) (h : IsPullDeg φ (GlobalTheory.PolDeg.rescale D₁ κ₀) (GlobalTheory.PolDeg.rescale D κ)) {I : Type} [Fintype I] (s : I → R₀), (∀ k, φ (s k) ≠ 0) → ∀ n : D₁.X → I → ℤ, (∀ y, (((κ₀ y)⁻¹ : (FractionRing R₀)ˣ) : FractionRing R₀) = ∏ k, algebraMap R₀ (FractionRing R₀) (s k) ^ n y k) → (∀ x, (((κ x)⁻¹ : (FractionRing R)ˣ) : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (φ (s k)) ^ n (h.xe x) k) → ∃ h' : IsPullDeg φ D₁ D, h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) ∧ (∀ {R₀ R : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] {φ : R₀ →+* R} {D₁ : DegPre R₀} {D : DegPre R} (h : IsPullDeg φ D₁ D) (κ : D.X → (FractionRing R)ˣ), ∃ h' : IsPullDeg φ D₁ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D κ) fun y => (κ y)⁻¹), h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) = h.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf φ) ∧ ∀ x, h'.xe x = h.xe x) :=
  ⟨fun h κ₀ κ _ _ s hs n h₀ h₁ => exists_rescale h κ₀ κ s hs n h₀ h₁,
    fun κ₀ κ h _ _ s hs n h₀ h₁ => exists_unscale κ₀ κ h s hs n h₀ h₁, fun h κ => exists_rescale_inv h κ⟩

end GlobalTheory.PullDegResc
end
end

