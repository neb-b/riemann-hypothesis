module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ZarGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_pull {T Y : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
  refine ⟨hL, (isAdditive_iff hL).2 fun Z a a' t => ?_⟩
  rw [evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL]
  simp only [lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)


omit [GrpObj A] in
theorem hom_open_eq (V : S.Opens) {Y : Over S} (u u' : Y ⟶ Over.mk V.ι) : u = u' := by
  apply Over.OverMorphism.ext
  have h : u.left ≫ V.ι = u'.left ≫ V.ι := (Over.w u).trans (Over.w u').symm
  exact (cancel_mono V.ι).1 h


omit [GrpObj A] in
theorem exists_hom_open (V : S.Opens) (Y : Over S) (h : ∀ z, Y.hom z ∈ V) : Nonempty (Y ⟶ Over.mk V.ι) := by
  refine ⟨Over.homMk (IsOpenImmersion.lift V.ι Y.hom ?_) (IsOpenImmersion.lift_fac _ _ _)⟩
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h z

theorem isChart_of_rep (V : S.Opens) {B : Over S} (b : B ⟶ Over.mk V.ι) {P : LB (A ⊗ B).left} (h : Rep A b P) :
    IsChart A P := by
  refine ⟨h.fam, ?_, ?_⟩
  · intro Y u u' hs
    have hA : (ev P (fst A Y) (snd A Y ≫ u)).IsLB := pull_isLB h.fam.isLB _
    have hB : (ev P (fst A Y) (snd A Y ≫ u')).IsLB := pull_isLB h.fam.isLB _
    obtain ⟨x, -, hx⟩ := h.univ Y (u ≫ b) _ (fam_pull h.fam u)
    rw [hx u ⟨rfl, LBIso.trans hA hB hA hs (LBIso.symm hs)⟩, hx u' ⟨hom_open_eq V _ _, hs⟩]
  · intro T N hN
    refine ⟨T.hom ⁻¹ᵁ V, fun Y y => ⟨?_, ?_⟩⟩
    · rintro ⟨u, -⟩ z
      have hb : b.left ≫ V.ι = B.hom := Over.w b
      have e : (u.left ≫ b.left) ≫ V.ι = y.left ≫ T.hom := by
        rw [Over.w y, Category.assoc, hb, Over.w u]
      have hmem : (y.left ≫ T.hom) z ∈ Set.range V.ι := ⟨(u.left ≫ b.left) z, by rw [← e]; rfl⟩
      rw [Scheme.Opens.range_ι] at hmem
      exact hmem
    · intro hz
      have hY : ∀ z, Y.hom z ∈ V := fun z => by
        rw [← Over.w y]
        exact hz z
      obtain ⟨t⟩ := exists_hom_open V Y hY
      obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ Y t _ (fam_pull hN y)
      exact ⟨x, hx⟩


omit [GrpObj A] in
theorem good_iso_comp {g : ℕ} {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y}
    (h : GlobalTheory.DualCon.Good g f) : GlobalTheory.DualCon.Good g (e ≫ f) := ⟨MorphismProperty.RespectsIso.precomp @IsProper e f h.proper,
  by
    haveI := h.smooth
    have h0 : SmoothOfRelativeDimension (0 + g) (e ≫ f) := inferInstance
    rwa [zero_add] at h0,
  by
    haveI := h.conn
    have hsq : IsPullback e (e ≫ f) f (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq h.conn⟩

theorem zariski_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, HasRep A (g i) (Over.mk (V i).ι)) → ∃ (B : Over S) (P : LB (A ⊗ B).left), Rep A (toUnit B) P ∧ ∀ i, GlobalTheory.DualCon.Good (g i) (pullback.snd B.hom (V i).ι) := by
  intro S A _ hA Ix V g hcov hrep
  have hrep' : ∀ i, ∃ (B : Over S) (b : B ⟶ Over.mk (V i).ι) (P : LB (A ⊗ B).left),
      Rep A b P ∧ GlobalTheory.DualCon.Good (g i) b.left := hrep
  choose Bi bi Pi hRi hGi using hrep'
  obtain ⟨B, P, j, hR, -, -, -⟩ := _root_.GlobalTheory.PicGlue.glue S A hA Ix Bi Pi
    (fun i => isChart_of_rep (V i) (bi i) (hRi i)) (by
      intro K _ _ s N hN
      obtain ⟨i, hi⟩ := hcov (s (default : Sp K))
      have hs : ∀ z : Sp K, s z ∈ V i := fun z => by
        rw [Subsingleton.elim z default]
        exact hi
      obtain ⟨t⟩ := exists_hom_open (V i) (Over.mk s) hs
      obtain ⟨x, ⟨-, hx⟩, -⟩ := (hRi i).univ _ t N hN
      exact ⟨i, x, (same_id_iff hN.isLB (hRi i).fam.isLB x).2 hx⟩)
  refine ⟨B, P, hR, fun i => ?_⟩
  have hpb : IsPullback (fst B (Over.mk (V i).ι)) (snd B (Over.mk (V i).ι)) (toUnit B)
      (toUnit (Over.mk (V i).ι)) :=
    IsPullback.of_is_product' (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
      SemiCartesianMonoidalCategory.isTerminalTensorUnit
  have hR' := GlobalTheory.T.rep_ev_of_isPullback S A B (𝟙_ (Over S)) (Over.mk (V i).ι) (B ⊗ Over.mk (V i).ι) (toUnit B) P
    (toUnit _) (fst _ _) (snd _ _) hR hpb
  obtain ⟨e, he, -⟩ := GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso S A _ _ _ (snd B (Over.mk (V i).ι)) _ (bi i) (Pi i) hR' (hRi i)
  haveI : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  have h2 := good_iso_comp e.hom.left (hGi i)
  rw [← Over.comp_left, he] at h2
  exact h2

end GlobalTheory.DualCon.ZarGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClass
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def pullCompare {Y X : Over (Sp R)} (u : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) u.left)
    {D : Type} [CommRing D] [Algebra R D] (w : Pt Y D) (z : Pt X D)
    (h : z = (w ≫ u : Pt X D)) :
    trivAt z ⟶ m.obj (trivAt w) :=
  Thick.trivHom { RingHom.id D with commutes' := fun _ ↦ rfl } (by
    subst z
    change spMap (RingHom.id D) ≫ (w ≫ u).left = w.left ≫ u.left
    rw [Cris.spMap_id, Category.id_comp, Over.comp_left])

theorem exists_crystallineCocycleOnPoints_pullback_cohomologous {Y X : Over (Sp R)} (u : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) u.left)
    (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) :
    ∃ c : Fn0 Y, ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (w : Pt Y D),
      fv (m.coef.pullbackOneCocycle f) D D' φ w = fv f D D' φ (w ≫ u) + (c D' (spOver φ ≫ w) - φ (c D w)) := by
  refine ⟨fun D _ _ w ↦ ev f (pullCompare u m w (w ≫ u) rfl), fun D _ _ D' _ _ φ w ↦ ?_⟩
  have h1 : ∀ (z : Pt X D') (h : z = (spOver φ ≫ w) ≫ u),
      @Eq D' (ev f (pullCompare u m (spOver φ ≫ w) z h))
        (ev f (pullCompare u m (spOver φ ≫ w) _ rfl)) := fun z h ↦ by subst z; rfl
  have k := ev_sq f (trivMap φ (w ≫ u))
    (pullCompare u m (spOver φ ≫ w) (spOver φ ≫ w ≫ u) (Category.assoc _ _ _).symm)
    (pullCompare u m w (w ≫ u) rfl) (m.functor.map (trivMap φ w)) fun _ ↦ rfl
  have key : ∀ a b b' c d : D', b = b' → a + b = c + d → d = a + (b' - c) :=
    fun a b b' c d e h ↦ by rw [← e]; linear_combination -h
  exact key _ _ _ _ _ (h1 _ _) k

theorem exists_isAdd_of_mem_primDR (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (hf : CatCoh.H1.mk _ f ∈ primDR A) :
    ∃ g : Fn2 A, IsAdd (fv f) g := by
  have h := (mem_prim_iff (dp0 R) (𝟙 _) A _).1 hf
  have M : ∀ u : A ⊗ A ⟶ A,
      IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 _) (RingHom.id R) u.left := fun u ↦
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have h' : CatCoh.H1.mk _ ((M μ[A]).coef.pullbackOneCocycle f) =
      CatCoh.H1.mk _ ((M (fst A A)).coef.pullbackOneCocycle f + (M (snd A A)).coef.pullbackOneCocycle f) := by
    rw [map_add (f := _)]; exact h
  obtain ⟨k, hk⟩ := H1.mk_eq_mk.1 h'
  obtain ⟨c, hc⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M μ[A]) f
  obtain ⟨c₁, hc₁⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M (fst A A)) f
  obtain ⟨c₂, hc₂⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M (snd A A)) f
  let k' : Fn0 (A ⊗ A) := fun D _ _ w ↦ k (trivAt w)
  refine ⟨fun D _ _ x y ↦ k' D (lift x y) - c D (lift x y) + c₁ D (lift x y) + c₂ D (lift x y),
    fun D _ _ D' _ _ φ x y ↦ ?_⟩
  have e : k' D' (spOver φ ≫ lift x y) - φ (k' D (lift x y)) =
      fv ((M μ[A]).coef.pullbackOneCocycle f) D D' φ (lift x y) -
        (fv ((M (fst A A)).coef.pullbackOneCocycle f) D D' φ (lift x y) +
          fv ((M (snd A A)).coef.pullbackOneCocycle f) D D' φ (lift x y)) :=
    congrFun (congrFun (congrFun hk _) _) (trivMap φ (lift x y))
  rw [hc, hc₁, hc₂, lift_fst, lift_snd, ← Hom.mul_def, comp_lift] at e
  simp only [map_add (f := _), map_sub]
  linear_combination e

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartLiftToModuliScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Points

namespace GlobalTheory.Poinc.ChartAt

theorem exists_affine_chart_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (w : X₁.M.Z), X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (u : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  intro g n F W Z i X₁ w hw
  haveI := X₁.imm
  set V : X₁.M.Z.Opens := X₁.π ⁻¹ᵁ i.opensRange with hVdef
  have hwV : w ∈ V := by
    show X₁.π w ∈ (i.opensRange : Set Z)
    simpa [Scheme.Hom.coe_opensRange] using hw
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X₁.M.Z) (U := V) hwV
  have hne : ((U : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hUi : ∀ w' ∈ U, X₁.π w' ∈ Set.range i := by
    intro w' hw'
    have := hUV hw'
    simpa [hVdef, Scheme.Hom.coe_opensRange] using this
  let φ : Γ(X₁.M.Z, U) ⟶ CommRingCat.of (X₁.M.ringOn U) :=
    CommRingCat.ofHom (X₁.M.sectionsEquiv U hne).toRingHom
  let f : Sp (X₁.M.ringOn U) ⟶ X₁.M.Z := Spec.map φ ≫ hU.fromSpec
  have hrange : Set.range (f ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    apply hUi
    have : hU.fromSpec (Spec.map φ y) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  refine ⟨U, IsOpenImmersion.lift i (f ≫ X₁.π) hrange, hU, hwU, hUi, ?_⟩
  rw [← cancel_mono i, Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, ← X₁.comp]
  have hpt : ⊤ ≤ X₁.M.pt ⁻¹ᵁ U := X₁.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom (X₁.M.ringOn U).val.toRingHom = valMap X₁.M.pt U hpt := by
    ext a
    show ((X₁.M.sectionsEquiv U hne a : X₁.M.ringOn U) : X₁.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap (X₁.M.ringOn U).val.toRingHom ≫ f = X₁.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  rw [← hf]
  simp only [f, Category.assoc]

end GlobalTheory.Poinc.ChartAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartSmoothLiftSqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift


open MvPolynomial in
theorem standardSmoothRelDim_lift_of_sqZero {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (B₀ : Type) [CommRing B₀]
    [Algebra R₀ B₀] (hB₀ : Algebra.IsStandardSmoothOfRelativeDimension g R₀ B₀) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀),
      (∀ r, p (algebraMap R B r) = algebraMap R₀ B₀ (π r)) ∧ Function.Surjective p ∧
      (∀ b, p b = 0 → b ∈ I.map (algebraMap R B)) ∧ Algebra.IsStandardSmoothOfRelativeDimension g R B := by
  obtain ⟨κ, τ, _, _, P, hP⟩ := hB₀.out
  classical
  have : Fintype τ := Fintype.ofFinite τ
  have hmap : Function.Surjective (MvPolynomial.map (σ := κ) π) := MvPolynomial.map_surjective π hπ
  let v : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (P.relation j)
  have hv : ∀ j, MvPolynomial.map π (v j) = P.relation j := fun j => Function.surjInv_eq hmap _
  let J : Ideal (MvPolynomial κ R) := Ideal.span (Set.range v)
  let φ : MvPolynomial κ R →+* B₀ := (aeval P.val).toRingHom.comp (MvPolynomial.map π)
  have hφ : ∀ f, φ f = aeval P.val (MvPolynomial.map π f) := fun _ => rfl
  have hJ : J ≤ RingHom.ker φ := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hφ, hv, Algebra.Presentation.aeval_val_relation]
  let p : (MvPolynomial κ R ⧸ J) →+* B₀ := Ideal.Quotient.lift J φ hJ
  have hp : ∀ f, p (Ideal.Quotient.mk J f) = φ f := fun _ => rfl
  have halg : ∀ r : R, p (algebraMap R _ r) = algebraMap R₀ B₀ (π r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial κ R) (MvPolynomial κ R ⧸ J)]
    simp [Ideal.Quotient.algebraMap_eq, hp, hφ]
  have hsurj : Function.Surjective p := by
    intro b
    obtain ⟨g, rfl⟩ := P.aeval_val_surjective b
    obtain ⟨f, rfl⟩ := hmap g
    exact ⟨Ideal.Quotient.mk J f, rfl⟩
  have hker : ∀ b, p b = 0 → b ∈ I.map (algebraMap R (MvPolynomial κ R ⧸ J)) := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    intro h0
    rw [hp, hφ] at h0
    have hmem : MvPolynomial.map π f ∈ Ideal.span (Set.range P.relation) := by
      rw [P.span_range_relation_eq_ker]
      first
        | exact h0
        | exact RingHom.mem_ker.mpr h0
        | (rw [Algebra.Generators.ker_eq_ker_aeval_val]; exact h0)
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
    let c' : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (c j)
    have hc' : ∀ j, MvPolynomial.map π (c' j) = c j := fun j => Function.surjInv_eq hmap _
    have hg : f - ∑ j, c' j * v j ∈ RingHom.ker (MvPolynomial.map (σ := κ) π) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, map_sub, map_sum, ← hc]
      simp [hc', hv]
    rw [MvPolynomial.ker_map, hk] at hg
    have hs : ∑ j, c' j * v j ∈ J :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have : Ideal.Quotient.mk J f = Ideal.Quotient.mk J (f - ∑ j, c' j * v j) := by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hs, sub_zero]
    rw [this]
    have hmm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hg
    rwa [Ideal.map_map] at hmm
  let Q := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  have hjac : p Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have h1 : ∀ f : MvPolynomial κ R, algebraMap Q.Ring (MvPolynomial κ R ⧸ Ideal.span (Set.range v)) f =
        Ideal.Quotient.mk J f := fun _ => rfl
    rw [h1, hp, hφ, Algebra.Generators.algebraMap_apply]
    congr 1
    rw [RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    show MvPolynomial.map π (pderiv (P.map i) (v j)) = pderiv (P.map i) (P.relation j)
    rw [mvPolynomial_map_pderiv_lift, hv]
  have hunit : IsUnit Q.jacobian := by
    refine isUnit_of_isUnit_map_of_sqZero_ker p hsurj (I.map (algebraMap R _)) ?_ hker _
      (by rw [hjac]; exact P.jacobian_isUnit)
    rw [← Ideal.map_pow, hI]; simp
  let Q' : Algebra.SubmersivePresentation R (MvPolynomial κ R ⧸ J) κ τ :=
    { Q with jacobian_isUnit := hunit }
  have hdim : Q'.dimension = g := hP
  exact ⟨_, inferInstance, inferInstance, p, halg, hsurj, hker, Q'.isStandardSmoothOfRelativeDimension hdim⟩

theorem isPushout_of_surjective {R C C₀ : Type} [CommRing R] [CommRing C] [CommRing C₀] (J : Ideal R)
    [Algebra (R ⧸ J) C₀] (σ : R →+* C) (p : C →+* C₀) (hp : Function.Surjective p)
    (hσ : ∀ r, p (σ r) = algebraMap (R ⧸ J) C₀ (Ideal.Quotient.mk J r))
    (hker : ∀ c, p c = 0 → c ∈ J.map σ) :
    IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom (Ideal.Quotient.mk J)) (CommRingCat.ofHom p)
      (CommRingCat.ofHom (algebraMap (R ⧸ J) C₀)) := by
  have hinv : Function.RightInverse (Function.surjInv hp) p := Function.surjInv_eq hp
  have hle : ∀ (T : CommRingCat.{0}) (u : C →+* T) (w : R ⧸ J →+* T),
      (∀ a, u (σ a) = w (Ideal.Quotient.mk J a)) → RingHom.ker p ≤ RingHom.ker u := by
    intro T u w huw c hc
    have h : J.map σ ≤ RingHom.ker u := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, huw, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact h (hker c hc)
  have hcond : ∀ (s : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom (Ideal.Quotient.mk J))) (a : R),
      s.inl.hom (σ a) = s.inr.hom (Ideal.Quotient.mk J a) := fun s a => congr($(s.condition) a)
  refine ⟨⟨by ext a; exact hσ a⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (p.liftOfRightInverse _ hinv ⟨s.inl.hom, hle _ _ _ (hcond s)⟩)) ?_ ?_ ?_⟩⟩
  · intro s; ext c
    exact p.liftOfRightInverse_comp_apply _ hinv _ c
  · intro s; ext a
    show p.liftOfRightInverse _ hinv _ (algebraMap (R ⧸ J) C₀ (Ideal.Quotient.mk J a)) = _
    rw [← hσ, p.liftOfRightInverse_comp_apply]
    exact hcond s a
  · intro s m h₁ _
    ext b
    obtain ⟨c, rfl⟩ := hp b
    have e : m.hom (p c) = s.inl.hom c := congr($h₁ c)
    rw [e]
    exact (p.liftOfRightInverse_comp_apply _ hinv ⟨s.inl.hom, hle _ _ _ (hcond s)⟩ c).symm

theorem exists_chart_lift : ∀ (R : Type) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ → ∀ (g : ℕ) (B : Over (Sp R))
    (b : B ⟶ Over.mk (spMap (Ideal.Quotient.mk J))), SmoothOfRelativeDimension g b.left → ∀ x : B.left,
    ∃ (C : Type) (_ : CommRing C) (σ : R →+* C)
      (j : Over.mk (spMap σ) ⊗ Over.mk (spMap (Ideal.Quotient.mk J)) ⟶ B),
      SmoothOfRelativeDimension g (spMap σ) ∧ j ≫ b = snd _ _ ∧ IsOpenImmersion j.left ∧
        x ∈ Set.range j.left := by
  intro R _ J hJ g B b hsm x
  let s₀ : B.left ⟶ Sp (R ⧸ J) := b.left
  have hsm₀ : SmoothOfRelativeDimension g s₀ := hsm
  obtain ⟨U₂, hU₂, V₂, hV₂, hx₂, e₂, h₂⟩ := hsm₀.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨r, s, hxs, e, hf⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).2
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves g).away x
    ⟨⊤, isAffineOpen_top _⟩ ⟨U₂, hU₂⟩ ⟨V₂, hV₂⟩ ⟨V₂, hV₂⟩ hx₂ hx₂ e₂ h₂ trivial
  let V : B.left.affineOpens := ⟨B.left.basicOpen s, hV₂.basicOpen s⟩
  have hle : V.1 ≤ s₀ ⁻¹ᵁ ⊤ := le_top
  have htop : RingHom.IsStandardSmoothOfRelativeDimension g (s₀.appLE ⊤ V.1 hle).hom := by
    have : IsLocalization.Away r Γ(Sp (R ⧸ J), (Sp (R ⧸ J)).basicOpen r) :=
      (isAffineOpen_top _).isLocalization_basicOpen r
    have heq : s₀.appLE ⊤ V.1 hle = CommRingCat.ofHom (algebraMap Γ(Sp (R ⧸ J), ⊤)
        Γ(Sp (R ⧸ J), (Sp (R ⧸ J)).basicOpen r)) ≫ s₀.appLE _ _ e := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Scheme.Hom.map_appLE]
    rw [heq]
    exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).1 _ r _ hf
  have hC₀ : Algebra.IsStandardSmoothOfRelativeDimension g (R ⧸ J) (Sec s₀ V.1) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).symm.commRingCatIsoToRingEquiv htop
  obtain ⟨C, _, _, p, hpσ, hp, hker, hC⟩ := standardSmoothRelDim_lift_of_sqZero J (by rw [hJ]; rfl)
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.mk_ker) g (Sec s₀ V.1) hC₀
  let σ : R →+* C := algebraMap R C
  have hpo := isPushout_of_surjective J σ p hp hpσ hker
  have H1 := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  let A : Over (Sp R) := Over.mk (spMap σ)
  let A' : Over (Sp R) := Over.mk (spMap (Ideal.Quotient.mk J))
  have H0 : IsPullback (fst A A').left (snd A A').left A.hom A'.hom := IsPullback.of_hasPullback _ _
  let k := H0.isoIsPullback _ _ H1
  have hk₂ : k.hom ≫ spMap (algebraMap (R ⧸ J) (Sec s₀ V.1)) = (snd A A').left :=
    H0.isoIsPullback_hom_snd _ _ H1
  have hw : (k.hom ≫ affPt s₀ V) ≫ B.hom = (A ⊗ A').hom := by
    rw [← Over.w b, ← Over.w (snd A A'), ← hk₂]
    simp only [Category.assoc]
    rw [← Category.assoc (affPt s₀ V), affPt_w]
  let j : A ⊗ A' ⟶ B := Over.homMk (k.hom ≫ affPt s₀ V) hw
  have hjl : j.left = k.hom ≫ affPt s₀ V := rfl
  refine ⟨C, inferInstance, σ, j, ?_, ?_, ?_, ?_⟩
  · exact HasRingHomProperty.Spec_iff.2 (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 hC))
  · ext1
    rw [Over.comp_left, hjl, Category.assoc]
    exact (congrArg (k.hom ≫ ·) (affPt_w s₀ V)).trans hk₂
  · rw [hjl]; infer_instance
  · have hxV : x ∈ Set.range (affPt s₀ V) := by rw [GlobalTheory.LiftSys.Coh.range_affPt]; exact hxs
    obtain ⟨z, hz⟩ := hxV
    refine ⟨k.inv z, ?_⟩
    rw [hjl, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc, hz]

end GlobalTheory.LBLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNhdsAvoidingImagesOfSpecializations
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.BadOpen

theorem exists_affine_nhds_avoid : ∀ (X Y : Scheme.{0}) [IsIntegral X] (s : Y ⟶ X) [IsProper s] (T : Set Y) (σ : Y) (y : X) (N : CartierDiv X), T.Finite → (∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → ¬ s w ⤳ y) → ∃ (U : X.Opens) (e : X.functionFieldˣ), IsAffineOpen U ∧ y ∈ U ∧ (∀ x ∈ U, N.IsEqn x e) ∧ ∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → s w ∉ U := by
  intro X Y _ s _ T σ y N hT hbad
  obtain ⟨g, hg⟩ := N.exists_isEqn y
  obtain ⟨U₁, hyU₁, hU₁⟩ := hg.exists_nhds
  set C : Set X := ⋃ v ∈ T, s.base '' (closure {v} ∩ closure {σ}) with hC
  have hCc : IsClosed C := by
    refine hT.isClosed_biUnion fun v _ => ?_
    exact s.isClosedMap _ (isClosed_closure.inter isClosed_closure)
  have hyC : y ∉ C := by
    simp only [hC, Set.mem_iUnion, Set.mem_image, not_exists, not_and]
    intro v hv w hw hwy
    exact hbad v hv w (specializes_iff_mem_closure.2 hw.1) (specializes_iff_mem_closure.2 hw.2)
      (hwy ▸ specializes_rfl)
  let V : X.Opens := U₁ ⊓ ⟨Cᶜ, hCc.isOpen_compl⟩
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := y) ⟨hyU₁, hyC⟩
  refine ⟨W, g, hW, hyW, fun x hx => hU₁ x (hWV hx).1, fun v hv w hvw hσw hw => ?_⟩
  have := (hWV hw).2
  apply this
  simp only [hC, Set.mem_iUnion, Set.mem_image]
  exact ⟨v, hv, w, ⟨specializes_iff_mem_closure.1 hvw, specializes_iff_mem_closure.1 hσw⟩, rfl⟩

end GlobalTheory.BadOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionConstantPeriodRatioPolarisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fraction_constant_period_ratio_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)), IsGrpPullback D.P.A Q.B (spMap ρ) β → IsSquare β β₂ → w.IsGen → (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) → ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b, ∃ k : (FractionRing R')ˣ, ∀ z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn k) = (letI := D.P.isAb.comm; lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J') * val (Q.tau (e a) (e b)) κ z J := by
  first | exact @GlobalTheory.HalfRatio.ratio_exists | exact GlobalTheory.HalfRatio.ratio_exists | (intros; apply GlobalTheory.HalfRatio.ratio_exists <;> assumption)
end

