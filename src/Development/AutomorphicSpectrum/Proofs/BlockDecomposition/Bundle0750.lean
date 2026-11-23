module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0253
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusLocalToGlobal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem locus_of_locally : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → ∀ (T : Scheme.{0}) (t : T ⟶ Y.left),
    (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ Locus N (W.ι ≫ t)) → Locus N t := by
  intro S A Y _ hA N hN h0 T t hloc
  let T₀ : Over S := Over.mk (t ≫ Y.hom)
  let y : T₀ ⟶ Y := Over.homMk t rfl
  let M : LB (A ⊗ T₀).left := ev N (fst A T₀) (snd A T₀ ≫ y)
  have hM : M.IsLB := pull_isLB hN _
  have key : ∀ (Z : Over S) (u : Z ⟶ A ⊗ T₀), evc hN (u ≫ fst A T₀) (u ≫ snd A T₀ ≫ y) = 0 →
      Triv (M.pull u.left) := by
    intro Z u h
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM]
    have e := pull_evc hN u (fst A T₀) (snd A T₀ ≫ y)
    rw [h] at e
    exact e
  show Triv M
  refine GlobalTheory.CompanionTheory.Ar.Approx.triv_of_section_of_locally_triv (A ⊗ T₀).left T (snd A T₀).left
    (lift (1 : T₀ ⟶ A) (𝟙 T₀)).left ?_ ?_ M hM ?_ ?_
  · rw [← Over.comp_left, lift_snd]; rfl
  · intro U
    exact GlobalTheory.CompanionTheory.Ar.Approx.isIso_app_of_isAbelianScheme T ((Over.pullback T₀.hom).obj A)
      (CubeGen.isAb_baseChange hA T₀.hom) U
  · refine key T₀ _ ?_
    rw [lift_fst, lift_snd_assoc, Category.id_comp]
    have e := congrArg (CechPic.pull y.left) ((triv_ev_iff hN _ _).1 h0)
    rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e
  · intro x
    obtain ⟨W, hx, hW⟩ := hloc x
    refine ⟨W, hx, ?_⟩
    let p := (snd A T₀).left
    let W₀ : Over S := Over.mk ((W.ι ≫ t) ≫ Y.hom)
    let y' : W₀ ⟶ Y := Over.homMk (W.ι ≫ t) rfl
    let Z : Over S := Over.mk ((p ⁻¹ᵁ W).ι ≫ (A ⊗ T₀).hom)
    let u : Z ⟶ A ⊗ T₀ := Over.homMk (p ⁻¹ᵁ W).ι rfl
    have hr : Set.range ((p ⁻¹ᵁ W).ι ≫ p) ⊆ Set.range W.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let l : Z.left ⟶ W₀.left := IsOpenImmersion.lift W.ι ((p ⁻¹ᵁ W).ι ≫ p) hr
    have hl : l ≫ W.ι = (p ⁻¹ᵁ W).ι ≫ p := IsOpenImmersion.lift_fac _ _ _
    have wz : l ≫ W₀.hom = Z.hom := by
      have hs : p ≫ t ≫ Y.hom = (A ⊗ T₀).hom := Over.w (snd A T₀)
      show l ≫ (W.ι ≫ t) ≫ Y.hom = (p ⁻¹ᵁ W).ι ≫ (A ⊗ T₀).hom
      rw [← hs, ← Category.assoc (p ⁻¹ᵁ W).ι, ← hl]
      simp only [Category.assoc]
    let w : Z ⟶ W₀ := Over.homMk l wz
    have hwy : w ≫ y' = u ≫ snd A T₀ ≫ y := by
      apply Over.OverMorphism.ext
      show l ≫ W.ι ≫ t = (p ⁻¹ᵁ W).ι ≫ p ≫ t
      rw [← Category.assoc, hl, Category.assoc]
    refine key Z u ?_
    have e := pull_evc hN (lift (u ≫ fst A T₀) w) (fst A W₀) (snd A W₀ ≫ y')
    rw [(triv_ev_iff hN _ _).1 hW, map_zero, lift_fst, lift_snd_assoc, hwy] at e
    exact e.symm

end GlobalTheory.CompanionTheory.TrivLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNull
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf : ∀ (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp ℤ) (σ : ℤ →+* ℂ) (D : ℕ) (c : GlobalTheory.AlgChart q σ D) (W : X.Opens)
    (h : genericPoint X ∈ W) (g : Γ(X, W)), fnOf W h g ≠ 0 →
    volume (c.e.target ∩ c.e.symm ⁻¹' {y | y ∈ ptsIn q σ W ∧ ev q σ W g y = 0}) = 0 := by
  intro X _ q σ D c W h g hg
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · have ht : c.e.target = ∅ := by rw [← c.e.image_source_eq_target, hs, Set.image_empty]
    simp [ht]
  have sectionFrameQuotient := mem_ptsIn.1 (c.source_subset hy0)
  haveI : Nonempty c.U := ⟨⟨_, sectionFrameQuotient⟩⟩
  have hgU : genericPoint X ∈ c.U := gen_mem sectionFrameQuotient
  haveI := functionField_isFractionRing_of_isAffineOpen X c.U c.affine
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, c.U)) (fnOf W h g)
  have hal : ∀ t : Γ(X, c.U), algebraMap Γ(X, c.U) X.functionField t = fnOf c.U hgU t :=
    fun _ => rfl
  rw [hal, hal] at hab
  have hb0 : fnOf c.U hgU b ≠ 0 := fun e =>
    nonZeroDivisors.ne_zero hb ((map_eq_zero_iff _ (fnOf_injective _ _)).1 e)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hg
    rw [← hab, map_zero, zero_div]
  have hrel : fnOf W h g * fnOf c.U hgU b = fnOf c.U hgU a := by
    rw [← hab, div_mul_cancel₀ _ hb0]
  have hI : genericPoint X ∈ W ⊓ c.U := ⟨h, hgU⟩
  have hres : resG X (inf_le_left : W ⊓ c.U ≤ W) g * resG X (inf_le_right : W ⊓ c.U ≤ c.U) b =
      resG X (inf_le_right : W ⊓ c.U ≤ c.U) a := by
    apply fnOf_injective _ hI
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG]
    exact hrel
  obtain ⟨Q, hQ, r, hQr⟩ := GlobalTheory.ChernNull.exists_poly_dvd _ c.etale a ha0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ (RingHom.injective_int σ) (by rw [e, map_zero]))
  refine measure_mono_null ?_ (GlobalTheory.ChernNull.volume_poly_zero D _ hP)
  rintro v ⟨hv, hyW, hyz⟩
  have hys : c.e.symm v ∈ c.e.source := c.e.map_target hv
  have hyU := c.source_subset hys
  have hyI : c.e.symm v ∈ ptsIn q σ (W ⊓ c.U) := mem_ptsIn_inf.2 ⟨hyW, hyU⟩
  have hay : ev q σ c.U a (c.e.symm v) = 0 := by
    rw [← ev_res inf_le_right hyI, ← hres, ev_mul, ev_res inf_le_left hyI, hyz, zero_mul]
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun i => c.e (c.e.symm v) i) := by
    refine MvPolynomial.ringHom_ext (fun i => ?_) (fun i => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq _ hys]
  have hQy := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at hQy
  show MvPolynomial.eval (fun i => v i) (MvPolynomial.map σ Q) = 0
  rw [c.e.right_inv hv] at hQy
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← hQy, hQr, map_mul, ← ev_eq hyU, hay,
    zero_mul]
end

