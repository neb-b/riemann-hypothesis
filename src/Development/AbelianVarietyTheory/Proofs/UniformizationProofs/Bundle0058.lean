module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsAffineOpen
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TorusQuotLift

theorem isMonHom_of_points {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H)
    (key : ∀ {T : Over S} (x y : T ⟶ G), (x * y) ≫ φ = (x ≫ φ) * (y ≫ φ)) : IsMonHom φ := by
  refine ⟨?_, ?_⟩
  ·
    have hsq := key (T := 𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at hsq
    have hid : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) = 1 := by
      have h2 : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) =
          ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * 1 := by rw [← hsq, _root_.mul_one]
      exact mul_left_cancel h2
    have eG : (1 : 𝟙_ (Over S) ⟶ G) = η := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have eH : (1 : 𝟙_ (Over S) ⟶ H) = η := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [eG, eH] at hid
    exact hid
  ·
    have hm := key (T := G ⊗ G) (fst G G) (snd G G)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
    have ht : (φ ⊗ₘ φ) = lift (fst G G ≫ φ) (snd G G ≫ φ) := by
      ext <;> simp
    rw [ht]
    exact hm

private lemma pullback_fst_comp_mul_left {S S' : Scheme.{0}} {G : Over S} [GrpObj G] (f : S' ⟶ S) {T : Over S'}
    (u v : T ⟶ (Over.pullback f).obj G) :
    (u * v).left ≫ pullback.fst G.hom f =
      ((Over.homMk (U := Over.mk (T.hom ≫ f)) (V := G) (u.left ≫ pullback.fst G.hom f)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w u))) *
        (Over.homMk (U := Over.mk (T.hom ≫ f)) (V := G) (v.left ≫ pullback.fst G.hom f)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w v)))).left := by
  rw [Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, Over.comp_left, Over.comp_left, Over.comp_left,
    Category.assoc, Category.assoc]
  have hmap : ((Over.pullback f).map μ[G]).left ≫ pullback.fst G.hom f =
      pullback.fst (G ⊗ G).hom f ≫ μ[G].left :=
    GlobalTheory.TorusLift.map_left_fst f μ[G]
  rw [hmap, ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst]
    erw [pullback.lift_fst_assoc, pullback.lift_fst]
    · rfl
    all_goals exact (Over.w _).trans (Over.w _).symm
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd]
    erw [pullback.lift_snd_assoc, pullback.lift_snd]
    · rfl
    all_goals exact (Over.w _).trans (Over.w _).symm

theorem exists_iso_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    ∃ e : G' ≅ (Over.pullback f).obj G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst G.hom f = F := by
  obtain ⟨hpb, hmul⟩ := h
  let e : G' ≅ (Over.pullback f).obj G :=
    Over.isoMk hpb.isoPullback (by simp)
  have he : e.hom.left ≫ pullback.fst G.hom f = F := by
    simp [e]
  refine ⟨e, ?_, he⟩
  apply isMonHom_of_points
  intro T x y
  apply GlobalTheory.TorusLift.hom_ext_fst f
  rw [pullback_fst_comp_mul_left]
  rw [Over.comp_left, Category.assoc, he]
  symm
  apply hmul T x y
  · simp [he]
  · simp [he]

theorem exists_isAffineOpen {R : Type} [CommRing R] [IsLocalRing R] {X : Type} [AddCommGroup X]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (Q : TQ G X) :
    ∃ W : G.left.Opens, IsAffineOpen W ∧ Q.i.left ⁻¹ᵁ W = ⊤ := by
  have := Q.q_affine
  let s₀ : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ := Q.B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((η[Q.B]).left s₀)) isOpen_univ
  refine ⟨Q.q.left ⁻¹ᵁ V, hV.preimage Q.q.left, ?_⟩

  have hw : Q.i.left ≫ Q.q.left = (splitTorus _ X).hom ≫ (η[Q.B]).left := by
    have := congrArg CommaMorphism.left Q.isKernel.w
    simpa using this

  have htop : (η[Q.B]).left ⁻¹ᵁ V = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff (R := R) _).mp hbV
  have hpre : Q.i.left ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) = (splitTorus _ X).hom ⁻¹ᵁ ((η[Q.B]).left ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
  rw [hpre, htop, Scheme.Hom.preimage_top]

theorem exists_torus (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left)
    (h : IsGrpPullback G₀ G (red J) F) (Q₀ : TQ G₀ X) :
    ∃ i : splitTorus _ X ⟶ G, IsMonHom i ∧ TorusCompat (red J) F Q₀.i i := by
  have hi₀hom := Q₀.i_hom
  obtain ⟨e, he_hom, he_fst⟩ := exists_iso_pullback h

  have hJtop : J ≠ ⊤ := by
    intro hJt
    obtain ⟨n, hn⟩ := hJ
    rw [hJt, Ideal.top_pow, Ideal.zero_eq_bot] at hn
    exact top_ne_bot hn
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

  let i₀ : (Over.pullback (red J)).obj (splitTorus (Spec (CommRingCat.of A)) X) ⟶
      (Over.pullback (red J)).obj G :=
    (SplitTorus.bcIso (red J) X).inv ≫ Q₀.i ≫ e.hom
  have hi₀ : IsMonHom i₀ := by
    dsimp only [i₀]
    infer_instance
  obtain ⟨W₀, hW₀, hW₀top⟩ := exists_isAffineOpen Q₀
  have hcomp : i₀.left ≫ e.inv.left = (SplitTorus.bcIso (red J) X).inv.left ≫ Q₀.i.left := by
    simp [i₀]
  have hW : ∃ W : ((Over.pullback (red J)).obj G).left.Opens, IsAffineOpen W ∧ i₀.left ⁻¹ᵁ W = ⊤ := by
    have : IsIso e.inv.left :=
      ⟨e.hom.left, by rw [← Over.comp_left, e.inv_hom_id, Over.id_left],
        by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]⟩
    refine ⟨e.inv.left ⁻¹ᵁ W₀, hW₀.preimage _, ?_⟩
    rw [← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage, hW₀top, Scheme.Hom.preimage_top]
  obtain ⟨i, ⟨hi, hmap⟩, -⟩ := GlobalTheory.TorusLift.main A J hJ X G i₀ hi₀ hW
  refine ⟨i, hi, ?_⟩
  rw [torusCompat_iff, ← SplitTorus.bcIso_hom_fst, Category.assoc, ← GlobalTheory.TorusLift.map_left_fst, hmap]
  simp only [i₀, Over.comp_left, Category.assoc, he_fst]
  rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]

theorem main : (∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ Q₀ : TQ G₀ X, ∃ Q : TQ G X, TorusCompat (red J) F Q₀.i Q.i) := by
  intro A _ _ J hJ X _ _ _ G _ _ _ G₀ _ F h Q₀
  obtain ⟨i, hi, hc⟩ := exists_torus A J hJ X G G₀ F h Q₀
  obtain ⟨B, q, j, hjpb, -, haff, hloc⟩ := _root_.GlobalTheory.TorusQuotientLift.exists_quotient_scheme A J hJ X G G₀ F h Q₀ i hi hc
  obtain ⟨hmono, hflat, hsurj, hsmooth, hcoset⟩ := _root_.GlobalTheory.LocTriv.main _ X G B i q hi haff hloc
  have : IsAffineHom q.left := haff
  obtain ⟨grpB, hcommB, hq, hker⟩ := GlobalTheory.grpObj_of_flat_coset_quotient _ G (splitTorus _ X) B i q
    hi hmono hflat hsurj inferInstance hcoset
  have hBsmooth : Smooth B.hom := hsmooth inferInstance

  have hB₀ := Q₀.isAb
  have hsnd : pullback.snd B.hom (red J) = hjpb.isoPullback.inv ≫ Q₀.B.hom := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
  have hPG := GlobalTheory.NilProper.isProper_and_geometricallyConnected_of_isNilpotent A J hJ B
  have hAb : IsAbelianScheme B := by
    constructor
    case comm => exact hcommB
    case smooth => exact hBsmooth
    case proper =>
      refine hPG.1 ?_
      rw [hsnd]
      have := hB₀.proper
      infer_instance
    case geomConnected =>
      refine hPG.2 ?_
      rw [hsnd]
      have := hB₀.geomConnected
      have hst : MorphismProperty.IsStableUnderBaseChange (@GeometricallyConnected.{0}) := inferInstance
      have hRI : MorphismProperty.RespectsIso (@GeometricallyConnected.{0}) :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected.{0}) _ _).mpr this
  have hloc' : ∀ (b : B.left) (χ : X), ∃ V : B.left.Opens, b ∈ V ∧
      ∃ u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ, IsWt i _ u.val χ := by
    intro b χ
    obtain ⟨V, hbV, -, -, -, -, u, hu⟩ := hloc b
    exact ⟨V, hbV, u (Multiplicative.ofAdd χ), hu χ⟩
  exact ⟨⟨B, hAb, q, i, hq, hi, hflat, hsurj, haff, hker, hloc'⟩, hc⟩

end GlobalTheory.TorusQuotLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPreUSetPsi
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def gtCoordSetPsi {e : ℕ} (g : GtCoord I D e G) (ψ) (h) : GtCoord I (setPsi D ψ h) e G where
  q := g.q
  q_hom := g.q_hom
  q_flat := g.q_flat
  q_surj := g.q_surj
  q_affine := g.q_affine
  i := g.i
  i_hom := g.i_hom
  isKernel := g.isKernel
  t := g.t
  t_gen := g.t_gen
  t_mul := g.t_mul
  t_unit := g.t_unit
  t_weight := g.t_weight

def PreU.setPsi (U : PreU I D A G) (ψ) (h) : PreU I (setPsi D ψ h) A G where
  semi := U.semi
  gen := U.gen
  gen_hom := U.gen_hom
  P := U.P
  wA := U.wA
  wA_gen := U.wA_gen
  gt := fun e => gtCoordSetPsi (U.gt e) ψ h
  gt_q := U.gt_q
  gt_t := U.gt_t
  w := U.w
  w_gen := U.w_gen
  w_vals := U.w_vals
  w_compat := U.w_compat
end

theorem exists_preU_setPsi : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) ψ h, ∃ (U' : PreU I (setPsi D ψ h) A G) (hP : U'.P = U.P), U'.gen = U.gen ∧ HEq U'.wA U.wA ∧ ∀ θ f, U.Theta θ f → ∃ θ', U'.Theta θ' f :=
  fun _ _ _ _ _ _ _ _ _ U ψ h => ⟨U.setPsi ψ h, rfl, rfl, HEq.rfl, fun θ _ hθ => ⟨θ, hθ⟩⟩
end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaRep

theorem finrank_secM (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {n : ℕ}
    (hn : 1 ≤ n) {F : Type} [Field F] (q : Spec (CommRingCat.of F) ⟶ S) :
    Module.finrank Γ((Over.mk q).left, ⊤) (SecM P.A P.L n (Over.mk q)) = n ^ P.g := by
  obtain ⟨U, hU, b, hb⟩ := hS S P n hn (q (IsLocalRing.closedPoint F))
  have hr : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    obtain rfl : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
    exact ⟨⟨_, hU⟩, rfl⟩
  let t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver S) U).left := IsOpenImmersion.lift U.ι q hr
  have ht : t ≫ (overRes (T := baseOver S) U).hom = q := by
    show IsOpenImmersion.lift U.ι q hr ≫ (U.ι ≫ 𝟙 _) = q
    rw [Category.comp_id, IsOpenImmersion.lift_fac]
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L n (baseAt t)),
      IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨h₁, h₂⟩ := hb F t b' hb'
  rw [← ht]
  haveI : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  exact (Module.finrank_eq_card_basis (Module.Basis.mk h₁ h₂.ge)).trans (Fintype.card_fin _)

theorem eq_one_of_weilIs (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] (q : Spec (CommRingCat.of F) ⟶ S) {n : ℕ} (hn : (n : F) ≠ 0) (x : Over.mk q ⟶ P.A)
    (hx : x ^ n = 1) (h : ∀ y : Over.mk q ⟶ P.A, y ^ n = 1 → WeilIs P.A P.L n x y 1) : x = 1 := by
  obtain ⟨P', g, hg, -, hm, t, ht⟩ := hL.polBaseChange S _ q P
  have hp : IsGrpPullback P'.A P.A q g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm (⟨t, ht⟩ : LBIso _ _)
  let ρ : Over.mk q ⟶ Over.mk (𝟙 _ ≫ q) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  let Φ : (baseOver (Spec (CommRingCat.of F)) ⟶ P'.A) →* (Over.mk q ⟶ P.A) :=
    MonoidHom.mk' (fun y => ρ ≫ toBase hg.w y) (fun a b => by rw [hm, MonObj.comp_mul])
  have hΦ : ∀ y, (Φ y).left = y.left ≫ g := fun y => Category.id_comp _
  have inj : Function.Injective Φ := fun a b e => Over.OverMorphism.ext (hg.hom_ext
    ((hΦ a).symm.trans ((congrArg CommaMorphism.left e).trans (hΦ b))) ((Over.w a).trans (Over.w b).symm))
  let x' : baseOver (Spec (CommRingCat.of F)) ⟶ P'.A :=
    Over.homMk (hg.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp q).symm)) (hg.lift_snd _ _ _)
  have ex : Φ x' = x := Over.OverMorphism.ext ((hΦ x').trans (hg.lift_fst _ _ _))
  have hx' : x' ^ n = 1 := inj (by rw [map_pow, ex, hx, map_one])
  have := hL.weilNondeg F P' n hn x' hx' fun y hy =>
    (GlobalTheory.weilIs_grpPullback_iff hL.globalFns hL.cube P P' hp w hw (t := q) (t' := 𝟙 _) (Category.id_comp q).symm n x' y hx' hy x (Φ y)
      ((congrArg CommaMorphism.left ex).symm.trans (hΦ x')) (hΦ y) 1).1 (h _ (by rw [← map_pow, hy, map_one]))
  rw [← ex, this, map_one]

theorem exists_projective_rep : Laws → Laws2 → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → ∃ (Φ : {x : Over.mk p ⟶ P.A // x ^ N = 1} → (SecM P.A P.L N (Over.mk p) ≃ₗ[Γ((Over.mk p).left, ⊤)] SecM P.A P.L N (Over.mk p))) (e : {x : Over.mk p ⟶ P.A // x ^ N = 1} → {x : Over.mk p ⟶ P.A // x ^ N = 1} → Γ((Over.mk p).left, ⊤)ˣ), Module.finrank Γ((Over.mk p).left, ⊤) (SecM P.A P.L N (Over.mk p)) = N ^ P.g ∧ (∀ a, ∃ θ : ThetaGrp P.A P.L N (Over.mk p), θ.pt = a.1 ∧ ∀ v, IsActOf P.A P.L N θ (SecM.toSec P.A v) (SecM.toSec P.A (Φ a v))) ∧ (∀ a b c, c.1 = a.1 * b.1 → ∃ r : Γ((Over.mk p).left, ⊤)ˣ, ∀ v, Φ c v = r.val • Φ a (Φ b v)) ∧ (∀ a b, WeilIs P.A P.L N a.1 b.1 (e a b) ∧ ∀ v, Φ a (Φ b v) = (e a b).val • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a.1 = 1) := by
  intro hL _ S _ P F _ _ p N hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun e => hN (by rw [e, Nat.cast_zero])
  haveI : Subsingleton (Over.mk p).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (Over.mk p).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨ρ, hact, hcomm, hrat, hmul⟩ := thetaGrp_acts_linearly hL.globalFns S P N (Over.mk p)
  choose θ hθ using fun a : {x : Over.mk p ⟶ P.A // x ^ N = 1} =>
    BoxTheta.exists_theta hL.kerPow P hN1 (T := Over.mk p) a.1 a.2
  choose e he using fun a b : {x : Over.mk p ⟶ P.A // x ^ N = 1} =>
    ((hL.weil S P N (Over.mk p)).1 a.1 b.1 a.2 b.2).exists
  refine ⟨fun a => ρ (θ a), e, finrank_secM hL.secBaseChange P hN1 p,
    fun a => ⟨θ a, hθ a, fun v => (hact _ _ _).2 rfl⟩, fun a b c hc => ?_, fun a b => ⟨he a b, ?_⟩, fun a ha => ?_⟩
  · obtain ⟨θ', h₁, h₂⟩ := hmul (θ a) (θ b)
    obtain ⟨r, hr⟩ := hrat θ' (θ c) (by rw [h₁, hθ, hθ, hθ, hc])
    exact ⟨r, fun v => by rw [← h₂]; exact hr v⟩
  · refine hcomm _ _ _ ((GlobalLift.weilIs_iff_commIsOf hL.globalFns P.isAb P.isLB _ _ _).1 ?_)
    rw [hθ, hθ]
    exact he a b
  · exact eq_one_of_weilIs hL P p hN a.1 a.2 fun y hy => ha ⟨y, hy⟩ ▸ he a ⟨y, hy⟩

end GlobalTheory.ThetaRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.existsUnique_thickTorus_level_weight_expansion : (∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (k : ℕ) (σ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => g.pG.left) (fun _ => (k : ℤ)))), ∃! f : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)), ∃ s : Finset D.X, (∀ α ∉ s, ∀ j, (f α).f j = 0) ∧ ∀ (z : (thickObj R I e G).left) (J), Good D.P.L z J → sval σ (𝟙 (thickObj R I e G).left) z J = ∑ α ∈ s, sval (f α) g.q.left z J * (val (g.t α) (𝟙 (thickObj R I e G).left) z J).val) := by
  first | exact @GlobalTheory.existsUnique_level_expansion | exact GlobalTheory.existsUnique_level_expansion | (intros; apply GlobalTheory.existsUnique_level_expansion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_unit_val_eq_mul {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ c.val * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← Units.mul_inv_eq_iff_eq_mul, ← Units.val_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ,
    val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

theorem exists_psiScal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V), ∃ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a := by
  intro V _ _ _ D
  choose ga hga using fun χ : D.X =>
    DVR.exists_gen_of_local (V := V) D.P.L D.P.isLB (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  have key := fun χ : D.X => exists_unit_val_eq_mul D.P.isLB (D.psi_gen χ)
    (DVR.pullGen_isGen D.P.L _ _ (ga χ) (hga χ) (toUnit (TK V)).left)
  choose c hc using key
  refine ⟨ga, fun χ => Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom.toMonoidHom (c χ),
    fun χ => ⟨hga χ, fun T κ z J hJ => ?_⟩⟩
  have e : κ.left ≫ (toUnit (TK V)).left = (toUnit T).left := by
    rw [← Over.comp_left, comp_toUnit]
  refine (hc χ T.left κ.left z J hJ).trans ?_
  refine congrArg₂ (· * ·) ?_ (congrArg Units.val ((val_pull hJ (ga χ) _ κ.left).trans (by rw [e])))
  have e₂ : scal κ.left ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom (c χ).val) =
      κ.left.appTop.hom (c χ).val :=
    congrArg κ.left.appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))) _)
  refine Eq.trans ?_ (congrArg (gs (𝟙 _) z ⊤) e₂).symm
  exact (congrArg (fun q => gs q z ⊤ (c χ).val) (Category.id_comp κ.left)).symm.trans
    (gs_pull (𝟙 _) κ.left z ⊤ trivial _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLin

theorem sval_comb {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' t'' : LB.Sec (LB.LinComb L φ ε)} (a : Γ(Y, ⊤))
    (h : ∀ j, t''.f j = (Y.presheaf.map (homOfLE le_top).op).hom a * t.f j + t'.f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t'' r z J = gs r z ⊤ a * sval t r z J + sval t' r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_add _ _ _ hm _ _).trans (congrArg (· + _) ((gs_mul _ _ _ hm _ _).trans (congrArg (· * _) ?_)))
  exact gs_res r z le_top hm a

theorem gs_scal_mul {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (a b : R) : gs r z ⊤ (scal p (a * b)) = gs r z ⊤ (scal p a) * gs r z ⊤ (scal p b) := by
  rw [← gs_mul r z ⊤ trivial]
  simp only [scal, map_mul]

theorem sum_append {α β M : Type*} [AddCommMonoid M] {n m : ℕ} (g : α → β → M) (c : Fin n → α) (c' : Fin m → α)
    (s : Fin n → β) (s' : Fin m → β) :
    ∑ i, g (Fin.append c c' i) (Fin.append s s' i) = ∑ i, g (c i) (s i) + ∑ i, g (c' i) (s' i) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem expF_linear : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' t'' s s' s'' (c : F), U.ExpF F k t s → U.ExpF F k t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → (∀ α j, (s'' α).f j = DegPre.constBF D F c _ * (s α).f j + (s' α).f j) → U.ExpF F k t'' s'') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k t t' t'' s s' s'' c ⟨n, a, σ, f, h1, h2, h3⟩ ⟨m, a', σ', f', h1', h2', h3'⟩ ht hs
  refine ⟨n + m, Fin.append (fun i => c * a i) a', Fin.append σ σ', Fin.append f f', fun i => ?_,
    fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e z J hJ => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact h1 i
    · simp only [Fin.append_right]; exact h1' i
  · rw [sum_append (fun x y => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left x) * sval y rG z JG),
      ← h2' Z rA y rG e1 e2 z JA JG hA hG]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 Z rA y rG e1 e2 z JA JG hA hG,
      sval_comb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (scal (fst (TFK (R := V) F) A.A).left c) ht rA z hA]
    ring
  · rw [sum_append (fun x (y : ∀ α, SecBT D (𝟙_ _) k α) =>
      gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left x) * sval (y α) rB z J), ← h3' α Z rF rB e z J hJ]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 α Z rF rB e z J hJ]
    exact sval_comb (scal (fst (TF (R := V) F) D.P.A).left c) (hs α) rF z hJ

end GlobalTheory.UU.ExpLin
end
end

