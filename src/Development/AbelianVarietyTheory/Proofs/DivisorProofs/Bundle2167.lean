module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ParamTriple

theorem exists_param : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens), (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∃ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), IsIntegral Y.left ∧ Smooth x.left ∧ Surjective x.left ∧ p ≫ V.ι = v.left ∧ (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) ∧ Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ := by
  intro S _ _ A _ hA V hV
  have := hA.smooth
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hAA.smooth
  have : GeometricallyIntegral (A ⊗ A).hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hAA.smooth hAA.geomConnected
  let B : Over S := Over.mk (V.ι ≫ A.hom)
  let j : B ⟶ A := Over.homMk V.ι
  have hBs : Smooth B.hom := by dsimp [B]; infer_instance
  have hBsurj : Surjective (V.ι ≫ A.hom) := ⟨fun s => by
    obtain ⟨x, hx, rfl⟩ := hV s
    exact ⟨⟨x, hx⟩, rfl⟩⟩
  have hBgi : GeometricallyIntegral B.hom := _root_.GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective _ _ _ V.ι A.hom hBsurj
  let P : Over S := (A ⊗ A) ⊗ B
  let X : P ⟶ A := fst _ _ ≫ fst A A
  let Aa : P ⟶ A := fst _ _ ≫ snd A A
  let Vv : P ⟶ A := snd _ _ ≫ j
  let O : P.left.Opens := (X * Aa).left ⁻¹ᵁ V ⊓ (X * Aa⁻¹).left ⁻¹ᵁ V ⊓ (Vv * Aa).left ⁻¹ᵁ V ⊓
    (Vv * Aa⁻¹).left ⁻¹ᵁ V
  have hsurj : Surjective (O.ι ≫ X.left) :=
    _root_.GlobalTheory.TranslateSurj.exists_translates_surjective S A hA V B j (fun b => b.2) hBs hBgi
  let Y : Over S := Over.mk (O.ι ≫ P.hom)
  let i : Y ⟶ P := Over.homMk O.ι
  have hmem : ∀ (f : P ⟶ A), O ≤ f.left ⁻¹ᵁ V → ∀ y, (i ≫ f).left y ∈ V := by
    intro f hf y
    exact hf y.2

  let s : B ⟶ P := lift (lift j 1) (𝟙 B)
  have hsX : s ≫ X = j := by simp [s, X]
  have hsA : s ≫ Aa = 1 := by simp [s, Aa]
  have hsV : s ≫ Vv = j := by simp [s, Vv]
  have hsO : ∀ b, s.left b ∈ O := by
    intro b
    have h1 : ∀ f : P ⟶ A, s ≫ f = j → s.left b ∈ f.left ⁻¹ᵁ V := by
      intro f hf
      show (s.left ≫ f.left) b ∈ V
      rw [← Over.comp_left, hf]
      exact b.2
    refine ⟨⟨⟨h1 _ ?_, h1 _ ?_⟩, h1 _ ?_⟩, h1 _ ?_⟩
    · rw [MonObj.comp_mul, hsX, hsA, _root_.mul_one]
    · rw [MonObj.comp_mul, GrpObj.comp_inv, hsX, hsA, inv_one, _root_.mul_one]
    · rw [MonObj.comp_mul, hsV, hsA, _root_.mul_one]
    · rw [MonObj.comp_mul, GrpObj.comp_inv, hsV, hsA, inv_one, _root_.mul_one]
  have hrO : Set.range s.left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨b, rfl⟩; exact hsO b
  let e0 : V.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι s.left hrO
  have he0 : e0 ≫ O.ι = s.left := IsOpenImmersion.lift_fac _ _ _
  let x : Y ⟶ A := i ≫ X
  let a : Y ⟶ A := i ≫ Aa
  let v : Y ⟶ A := i ≫ Vv
  let p : Y.left ⟶ V.toScheme := O.ι ≫ (snd (A ⊗ A) B).left
  have hxl : x.left = O.ι ≫ X.left := rfl
  have hre : Set.range e0 ⊆ Set.range (x.left ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨b, rfl⟩
    show (e0 ≫ x.left) b ∈ V
    rw [hxl, ← Category.assoc, he0, ← Over.comp_left, hsX]
    exact b.2
  let e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift _ e0 hre
  have he : e ≫ (x.left ⁻¹ᵁ V).ι = e0 := IsOpenImmersion.lift_fac _ _ _
  have hsec : e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _ := by
    rw [← Category.assoc, ← Category.assoc, he, he0]
    show (s ≫ snd (A ⊗ A) B).left = _
    rw [lift_snd]; rfl
  obtain ⟨s0⟩ := (inferInstance : Nonempty S)
  obtain ⟨x0, hx0, -⟩ := hV s0
  have : Nonempty V.toScheme := ⟨⟨x0, hx0⟩⟩
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ A.hom)
  have : Flat (A ⊗ A).hom := inferInstance
  have : UniversallyOpen (A ⊗ A).hom := inferInstance
  have : IsIntegral B.left := ‹IsIntegral V.toScheme›
  have : IsLocallyNoetherian B.left := ‹IsLocallyNoetherian V.toScheme›
  have : IsIntegral P.left := inferInstanceAs (IsIntegral (pullback (A ⊗ A).hom B.hom))
  obtain ⟨b0⟩ := (inferInstance : Nonempty V.toScheme)
  have : Nonempty O.toScheme := ⟨⟨s.left b0, hsO b0⟩⟩
  have hYi : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  have hgi : GeometricallyIntegral (((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom) := by
    refine _root_.GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective _ _ _ _ _ ?_
    have : Surjective (e ≫ ((x.left ⁻¹ᵁ V).ι ≫ O.ι) ≫ pullback.snd (A ⊗ A).hom B.hom) := by
      rw [hsec]; infer_instance
    exact Surjective.of_comp e _
  have hxa : x * a = i ≫ (X * Aa) := by simp only [x, a, MonObj.comp_mul]
  have hxa' : x * a⁻¹ = i ≫ (X * Aa⁻¹) := by simp only [x, a, MonObj.comp_mul, GrpObj.comp_inv]
  have hva : v * a = i ≫ (Vv * Aa) := by simp only [v, a, MonObj.comp_mul]
  have hva' : v * a⁻¹ = i ≫ (Vv * Aa⁻¹) := by simp only [v, a, MonObj.comp_mul, GrpObj.comp_inv]
  refine ⟨Y, x, a, v, p, e, hYi, ?_, hsurj, ?_, fun y => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show Smooth (O.ι ≫ pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom)
    infer_instance
  · show (O.ι ≫ (snd (A ⊗ A) B).left) ≫ V.ι = O.ι ≫ (snd (A ⊗ A) B ≫ j).left
    rw [Category.assoc, Over.comp_left]; rfl
  · rw [hxa]; exact hmem _ (fun z hz => hz.1.1.1) y
  · rw [hxa']; exact hmem _ (fun z hz => hz.1.1.2) y
  · rw [hva]; exact hmem _ (fun z hz => hz.1.2) y
  · rw [hva']; exact hmem _ (fun z hz => hz.2) y
  · show Smooth ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom)
    infer_instance
  · show GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom)
    rw [← Category.assoc]; exact hgi
  · show e ≫ (x.left ⁻¹ᵁ V).ι ≫ O.ι ≫ pullback.snd (A ⊗ A).hom B.hom = 𝟙 _
    rw [← hsec]; simp only [Category.assoc]

end GlobalTheory.ParamTriple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermutationLeadingMinors
section
namespace GlobalTheory

open Matrix

theorem exists_isUnit_of_isUnit_sum_localRing {R : Type} [CommRing R] [IsLocalRing R]
    {ι : Type} (s : Finset ι) (f : ι → R) (h : IsUnit (∑ i ∈ s, f i)) :
    ∃ i ∈ s, IsUnit (f i) := by
  by_contra hne
  push_neg at hne
  apply (IsLocalRing.mem_maximalIdeal _).mp _ h
  exact Ideal.sum_mem _ fun i hi => (IsLocalRing.mem_maximalIdeal _).mpr (hne i hi)

theorem exists_perm_isUnit_leading_minors_localRing :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R),
      IsUnit M.det → ∃ w : Equiv.Perm (Fin m), ∀ (k : ℕ) (hk : k ≤ m),
        IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  intro R _ _ m
  induction m with
  | zero =>
    intro M _
    refine ⟨1, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    simp
  | succ n ih =>
    intro M hM
    rw [Matrix.det_succ_row M (Fin.last n)] at hM
    obtain ⟨j, -, hj⟩ := exists_isUnit_of_isUnit_sum_localRing _ _ hM
    have hN := isUnit_of_mul_isUnit_right hj
    rw [Fin.succAbove_last] at hN
    obtain ⟨v, hv⟩ := ih _ hN
    let f : Fin (n + 1) → Fin (n + 1) := fun i =>
      if h : i = Fin.last n then j else j.succAbove (v (i.castPred h))
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      by_cases ha : a = Fin.last n <;> by_cases hb : b = Fin.last n
      · rw [ha, hb]
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab.symm (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_false] at hab
        have := v.injective (Fin.succAbove_right_injective hab)
        exact Fin.castPred_inj.mp this
    let w : Equiv.Perm (Fin (n + 1)) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    refine ⟨w, fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have heq : (M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk) =
          ((M.submatrix Fin.castSucc j.succAbove).submatrix id v).submatrix
            (Fin.castLE hk') (Fin.castLE hk') := by
        ext a b
        have hb : Fin.castLE hk b ≠ Fin.last n := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [submatrix_apply, id, w, Equiv.ofBijective_apply, f, hb, dite_false]
        congr 2
        all_goals (ext; simp)
      rw [heq]
      exact hv k hk'
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      have : Fin.castLE hk = id := Fin.castLE_rfl _
      rw [this, Matrix.submatrix_id_id, Matrix.det_permute']
      refine IsUnit.mul ?_ ?_
      · rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
      · rw [Matrix.det_succ_row M (Fin.last n)]
        exact hM

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.GenPol

theorem exists_polAV_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → TraceFormTwistIso D.toPre o w → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ (A' : PolAV (Sp (FractionRing R))) (gen' : (Over.pullback (jK R)).obj G ≅ A'.A), IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ hB D A G _ _ hG U O _ _ _ o oA oG hlin w hw hpsi P hP
  have laws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have : IsCommMonObj A.A := A.isAb.comm
  have hwA : IsMonHom (oA.act w) := oA.hom w
  have hwA' : IsMonHom (oA.act (star w)) := oA.hom (star w)
  have hs : oA.act w * oA.act (star w) = 𝟙 A.A := by
    rw [Hom.mul_def]
    change padd A.A (oA.act w) (oA.act (star w)) = 𝟙 A.A
    rw [← oA.map_add, hw, oA.map_one]
  have ha := (GlobalTheory.RosLam.rosatiAdj_iff_lamEq laws.globalFns _ A _ _ hwA hwA').1 (oA.rosati w)
  obtain ⟨L', h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.CM.exists_normalised_polarisation laws (FractionRing R) A _ _ hwA hwA' hs ha
  let A' : PolAV (Sp (FractionRing R)) :=
    { A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := L', isLB := h1, rigid := h2, sym := h3,
      ample := h4, ktriv := h5 }
  refine ⟨A', U.gen, U.gen_hom, ?_⟩
  haveI := U.gen_hom
  have hLG := U.LG.isLB
  have hAL := A.isLB
  let φ := pullback.fst G.hom (jK R)
  let GK := (Over.pullback (jK R)).obj G
  let wGK := (Over.pullback (jK R)).map (oG.act w)
  have lbc : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B))
      {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL => DVR.linComb_isLB _ hL _ _
  have s1 : LBIso L' (cubeLB A.A ![𝟙 A.A, oA.act w] A.L) := by
    have e := GlobalTheory.LamCalc.lbIso_of_lamEq h6 (𝟙 A.A) (oA.act w)
    simp only [Category.comp_id] at e
    exact LBIso.trans h1 (lbc _ h1) (lbc _ hAL) h7 e
  have s2 := GlobalTheory.RigidBundleGlue.LBIso.pull s1 U.gen.hom.left
  have hext : LBIso (U.LG.L.pull φ) (A.L.pull U.gen.hom.left) := by
    obtain ⟨v, hv⟩ := U.ext
    exact LBIso.symm ⟨v, hv⟩
  have hgp := isGrpPullback_of_iso U.gen
  have s3 := GlobalTheory.ShapePull.iso_cubeLB_pull hgp (pushPt hgp.1.w (𝟙 GK)) hext
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 A.A) (b := oA.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      have e := congrArg (fun q => q.left) (hlin.ext w)
      simp only [Over.comp_left] at e
      simp only [pushPt, Over.homMk_left, Over.comp_left, Over.id_left, Category.id_comp]
      exact e)
  have hpb := isGrpPullback_pullback G (jK R)
  have s4 := GlobalTheory.ShapePull.iso_cubeLB_pull hpb (pushPt hpb.1.w (𝟙 GK)) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hLG φ))
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 G) (b := oG.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      show wGK.left ≫ φ = (𝟙 GK.left ≫ φ) ≫ (oG.act w).left
      rw [Category.id_comp]
      simp only [wGK, φ, Over.pullback_map_left, pullback.lift_fst])
  have s5 := GlobalTheory.RigidBundleGlue.LBIso.pull hP φ
  have e3 : (pushPt hgp.1.w (𝟙 GK)).left = U.gen.hom.left := by simp [pushPt]
  have e4 : (pushPt hpb.1.w (𝟙 GK)).left = φ := Category.id_comp _
  rw [e3] at s3
  rw [e4] at s4
  have i1 := pull_isLB h1 U.gen.hom.left
  have i2 := pull_isLB (lbc ![𝟙 A.A, oA.act w] hAL) U.gen.hom.left
  have i3 := lbc ![𝟙 GK, wGK] (pull_isLB hLG φ)
  have i4 := pull_isLB (lbc ![𝟙 G, oG.act w] hLG) φ
  have i5 := pull_isLB P.L.isLB φ
  exact LBIso.trans i1 i2 i5 s2 (LBIso.trans i2 i3 i5 s3.symm (LBIso.trans i3 i4 i5 s4 s5.symm))

end GlobalTheory.Mum.GenPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNonzeroPairSectionOfAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem exists_pos_nonzero_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ),
      ∃ (c : ℕ) (h : X.functionField), 0 < c ∧ h ≠ 0 ∧ h ∈ P.H a c := by
  intro k _ X _ p D hX P hA a
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.VolBr.Pair.exists_rep k X p P a 0
  obtain ⟨b, hb, u, hu⟩ := exists_sec_finite_subset_nonzeroLocus k X p D hX M P.A hA {genericPoint X}
    (Set.finite_singleton _)
  have hA1 := (Pair.rep_base k X p P).2.1
  have hAb := Pair.rep_pow k X p P 0 1 P.A b hA1
  have hN := Pair.rep_tens k X p P a 0 _ _ M (P.A.pow b) hM hAb
  have e1 : a + (b : ℤ) * 0 = a := by ring
  have e2 : (0 : ℤ) + (b : ℤ) * 1 = b := by ring
  rw [e1, e2] at hN
  obtain ⟨e, -, hrange, -, hloc⟩ := RepDict.rep_dict k X p P a b _ hN
  have hmem : e u ∈ P.H a b := by
    have : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i :=
    Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))
  obtain ⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j :=
    Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))
  have hU := (hloc u (genericPoint X) i j hi hj).1 (hu rfl)
  refine ⟨b, e u, hb, fun h0 => ?_, hmem⟩
  have hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField) := by
    rintro x ⟨w, hw, h⟩
    exact (hw.map (algebraMap _ X.functionField)).ne_zero h
  rw [h0] at hU
  have z : P.loc a b 0 i j = 0 := by simp [Pair.loc]
  rw [z] at hU
  exact hz _ hU

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZeroSmoothAffineOpen
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

theorem sec_exists_pow_of_D_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (U : X.affineOpens) (u : GlobalTheory.CechDR.Sec s U.1), KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.1) u = 0 → ∃ h : GlobalTheory.CechDR.Sec s U.1, h ^ p = u := by
  intro p _ k _ _ hk X _ s _ U u hu
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s U.1) := by
    haveI : IsOpenImmersion (GlobalTheory.CechDR.affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have h : Smooth (GlobalTheory.CechDR.affPt s U ≫ s) := inferInstance
    rw [GlobalTheory.CechDR.affPt_w] at h
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h)
  by_cases hU : Nonempty U.1
  · haveI : IsDomain (GlobalTheory.CechDR.Sec s U.1) := IsIntegral.component_integral (X := X) U.1
    exact _root_.GlobalTheory.exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain p k hk _ u hu
  · have e : U.1 = ⊥ := by
      ext x
      exact ⟨fun hx ↦ hU ⟨⟨x, hx⟩⟩, fun hx ↦ hx.elim⟩
    have hs : Subsingleton Γ(X, U.1) := by rw [e]; infer_instance
    haveI : Subsingleton (GlobalTheory.CechDR.Sec s U.1) := hs
    exact ⟨u, Subsingleton.elim _ _⟩

end GlobalTheory.ConjSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAw
section
open GlobalTheory.LogDerProj

set_option autoImplicit false

namespace GlobalTheory.LogDerProj

theorem exists_pow_smul_eq_res : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R)
    [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R)
    (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R),
    ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  intro k R S _ _ _ _ f _ φ hφ J n
  letI : Algebra k R := φ.toAlgebra
  haveI : Algebra.FiniteType k R := hφ
  haveI : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : Algebra k S := ((algebraMap R S).comp φ).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hn0 : ∀ c : k, n.1 (algebraMap R S (φ c)) = 0 := fun c => n.2.1 c
  have hnJ : ∀ y ∈ J.map (algebraMap R S), n.1 y ∈ J.map (algebraMap R S) := n.2.2
  let gl : R →ₗ[k] S :=
    { toFun := fun r => n.1 (algebraMap R S r)
      map_add' := fun a b => by simp
      map_smul' := fun c r => by
        rw [RingHom.id_apply, Algebra.smul_def, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        show _ = algebraMap R S (φ c) * _
        rw [show algebraMap k R c = φ c from rfl, hn0, mul_zero, add_zero] }
  let g : Derivation k R S := Derivation.mk' gl fun a b => by
    show n.1 (algebraMap R S (a * b)) = a • n.1 (algebraMap R S b) + b • n.1 (algebraMap R S a)
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
  have hg : ∀ r, g r = n.1 (algebraMap R S r) := fun r => rfl
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule (Submonoid.powers f)
    (Algebra.linearMap R S) g.liftKaehlerDifferential
  let D' : Derivation k R R := h.compDer (KaehlerDifferential.D k R)
  have hD' : ∀ r, algebraMap R S (D' r) = algebraMap R S s * n.1 (algebraMap R S r) := by
    intro r
    have := congrArg (fun L : Ω[R⁄k] →ₗ[R] S => L (KaehlerDifferential.D k R r)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
      Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    rw [← hg]
    exact this
  have hJfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨T, hT⟩ := hJfg
  have hex : ∀ t : T, ∃ m : Submonoid.powers f, (m : R) * D' t ∈ J := by
    intro t
    have ht : (t : R) ∈ J := hT ▸ Ideal.subset_span t.2
    have h1 : algebraMap R S (D' t) ∈ J.map (algebraMap R S) := by
      rw [hD']
      exact Ideal.mul_mem_left _ _ (hnJ _ (Ideal.mem_map_of_mem _ ht))
    obtain ⟨m, hm, hmJ⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) S J _).1 h1
    exact ⟨⟨m, hm⟩, hmJ⟩
  choose c hc using hex
  let m : Submonoid.powers f := ∏ t, c t
  have hmT : ∀ t ∈ T, (m : R) * D' t ∈ J := by
    intro t ht
    have hdvd : (c ⟨t, ht⟩ : R) ∣ (m : R) := by
      show (c ⟨t, ht⟩ : R) ∣ ((∏ t, c t : Submonoid.powers f) : R)
      change (c ⟨t, ht⟩ : R) ∣ (Submonoid.subtype (Submonoid.powers f)) (∏ t, c t)
      rw [map_prod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, mul_comm _ q, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hc ⟨t, ht⟩)
  let D : Derivation ℤ R R := (m : R) • D'.restrictScalars ℤ
  have hDapp : ∀ r, D r = (m : R) * D' r := fun r => rfl
  have hDmem : D ∈ logSub φ J := by
    refine ⟨fun a => ?_, fun y hy => ?_⟩
    · rw [hDapp, show φ a = algebraMap k R a from rfl, D'.map_algebraMap, mul_zero]
    · rw [← hT] at hy
      induction hy using Submodule.span_induction with
      | mem x hx => rw [hDapp]; exact hmT x hx
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x hx' hx =>
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        have hxJ : x ∈ J := by rw [← hT]; exact hx'
        exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hxJ)
  refine ⟨(⟨D, hDmem⟩, m * s), ?_⟩
  apply Subtype.ext
  refine der_ext f _ _ fun r => ?_
  rw [res_apply, hDapp]
  show ((m * s : Submonoid.powers f) : R) • n.1 (algebraMap R S r) = _
  rw [Algebra.smul_def, Submonoid.coe_mul, map_mul, map_mul, hD', mul_assoc]

end GlobalTheory.LogDerProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTorsionAndDescentAbelianVarietyAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ), (n : k) ≠ 0 → Finite {g : 𝟙_ (Over (Sp k)) ⟶ A // g ^ n = 1} ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ A), g ^ n = 1 → ∃ g₀ : 𝟙_ (Over (Sp k)) ⟶ A, g₀ ^ n = 1 ∧ g = toUnit (Over.mk x) ≫ g₀ := by
  first | (exact @GlobalTheory.AbTorsionGeomDescent.finite_torsion_and_descent) | (exact GlobalTheory.AbTorsionGeomDescent.finite_torsion_and_descent) | (intros; apply GlobalTheory.AbTorsionGeomDescent.finite_torsion_and_descent  <;> assumption)
end

