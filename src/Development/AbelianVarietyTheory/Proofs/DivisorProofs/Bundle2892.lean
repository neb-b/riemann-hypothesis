module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0029
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageQuotientFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.AffinePreimageFibre

theorem isPullback_comp_mono {C : Type*} [Category C] {A B T : C} (f : A ⟶ B) (c : B ⟶ T) [Mono c] :
    IsPullback f (𝟙 A) c (f ≫ c) :=
  IsPullback.of_isLimit' ⟨by simp⟩
    (PullbackCone.IsLimit.mk _ (fun s => s.snd)
      (fun s => by
        rw [← cancel_mono c]
        simp only [Category.assoc]
        exact s.condition.symm)
      (fun s => by simp)
      (fun s m _ h2 => by simpa using h2))

theorem isAffineOpen_preimage_fibre : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), IsPullback ι q p (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ W : Z.Opens, IsAffineOpen W → W ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (ι ⁻¹ᵁ W) := by
  intro X Z p U m A q ι H W hW hWU
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  let h : (W : Scheme) ⟶ Sp Γ(X, U.1) := p.resLE U.1 W hWU ≫ U.2.isoSpec.hom
  have hh : W.ι ≫ p = h ≫ chart U := by
    simp [h, chart, IsAffineOpen.fromSpec]
  have big := (isPullback_morphismRestrict ι W).paste_vert H
  rw [hh] at big
  have comm : (ι ∣_ W) ≫ h = ((ι ⁻¹ᵁ W).ι ≫ q) ≫ spMap (Ideal.Quotient.mk m) := by
    rw [← cancel_mono (chart U)]
    simpa [Category.assoc] using big.w
  have sq : IsPullback (ι ∣_ W) ((ι ⁻¹ᵁ W).ι ≫ q) h (spMap (Ideal.Quotient.mk m)) :=
    IsPullback.of_bot (v₂₁ := 𝟙 _) (by simpa using big) comm (isPullback_comp_mono _ _)
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk m)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsAffineHom (ι ∣_ W) := MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip inferInstance
  haveI : IsAffine (W : Scheme) := hW
  exact isAffine_of_isAffineHom (ι ∣_ W)

end GlobalTheory.AffinePreimageFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonGenericFibreOfMaximalAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem isClosed_singleton_of_maximal {X : Scheme.{0}} [JacobsonSpace X] (U : X.affineOpens)
    (mm : Ideal Γ(X, U.1)) (hm : mm.IsMaximal) (y : X) (hy : y ∈ U.1)
    (h : ∀ f ∈ mm, y ∉ X.basicOpen f) : IsClosed ({y} : Set X) := by
  have hU : IsAffineOpen U.1 := U.2
  set p := hU.primeIdealOf ⟨y, hy⟩ with hp
  have hpy : hU.fromSpec p = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  have hle : mm ≤ p.asIdeal := by
    intro f hf
    by_contra hfp
    apply h f hf
    have h1 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hfp
    rw [← hpy]; exact h1
  have heq : mm = p.asIdeal := hm.eq_of_le p.isPrime.ne_top hle
  have hcl : IsClosed ({p} : Set (PrimeSpectrum Γ(X, U.1))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 (heq ▸ hm)
  have he := hU.fromSpec.isOpenEmbedding
  have hlc := IsLocallyClosed.image (f := hU.fromSpec) (s := {p}) hcl.isLocallyClosed he.isInducing
    he.isOpen_range.isLocallyClosed
  have e : hU.fromSpec '' {p} = {y} := Set.image_singleton.trans (congrArg _ hpy)
  exact isClosed_singleton_of_isLocallyClosed_singleton (e ▸ hlc)

theorem isClosed_singleton_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (mm : Ideal Γ(Y.X, U.1)), mm.IsMaximal → ∀ x : gen Y, genι Y x ∈ U.1 → (∀ f ∈ mm, genι Y x ∉ Y.X.basicOpen f) → IsClosed ({x} : Set (gen Y)) := by
  intro E _ _ _ H Dw l Xo c Y U mm hm x hx h
  have : LocallyOfFiniteType Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    have := isProper_str c.F N
    rw [← hs]; infer_instance
  have : JacobsonSpace (Sp c.F) := inferInstanceAs (JacobsonSpace (PrimeSpectrum c.F))
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace Y.s
  have hc := isClosed_singleton_of_maximal U mm hm _ hx h
  have hiso : IsIso (genι Y) := isIso_fst Y
  have hinj : Function.Injective (genι Y) := (genι Y).isOpenEmbedding.injective
  have := hc.preimage (genι Y).continuous
  rwa [← Set.image_singleton, Set.preimage_image_eq _ hinj] at this

end GlobalTheory.LocReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfLeAffineOpenToroidalModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ModelQC

theorem isCompact_of_le_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (W : Y.X.Opens), W ≤ U.1 → IsCompact (W : Set Y.X) := by
  intro E _ _ _ H Dw l Xo c Y U W hW
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  have := isProper_str c.F N
  have : IsProper Y.s := hs ▸ inferInstance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : IsNoetherian Y.X := ⟨⟩
  exact TopologicalSpace.NoetherianSpace.isCompact _

end GlobalTheory.ModelQC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizOfComm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TranslHoriz

theorem isHoriz_of_comm : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ A.left), IsGrpPullback B' A (spMap ρ) π₁ → IsGrpPullback B' A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (dl : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK A₀.hom A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → ∀ (s : 𝟙_ (Over (Sp R)) ⟶ A) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left → T₀ ≫ A₀.hom = A₀.hom → (∀ (W : A.left.Opens) (f : Γ(A.left, W)), dl ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W) (((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left.app W).hom f) = pbT T₀ (dl W f) (m₀ ⁻¹ᵁ ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W))) → ∀ x : Sp (DualNumber k) ⟶ B'.left, x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ s.left → x ≫ π₂ = spMap (constHom ρ) ≫ s.left := by
  intro k _ R _ A _ hA ρ B' _ π₁ π₂ h₁ h₂ hcl A₀ _ m₀ hm₀ dl hdl s T₀ hT₀ hT₀h hcomm x hx hx1
  set fst := (TrivSqZeroExt.fstHom k k k).toRingHom with hfst
  set alg := algebraMap k (DualNumber k) with halg
  have e_fa : spMap fst ≫ spMap alg = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; congr 1
  have e_c : spMap (constHom ρ) = spMap alg ≫ spMap (fst.comp ρ) := by
    simp only [spMap, constHom, ← Spec.map_comp]; rfl
  have e_r : spMap (fst.comp ρ) = spMap fst ≫ spMap ρ := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have P₁ := h₁.1
  have P₂ := h₂.1
  have P₀ := hm₀.1
  have wr : π₂ ≫ A.hom = (B'.hom ≫ spMap alg) ≫ spMap (fst.comp ρ) := by
    rw [P₂.w, e_c, Category.assoc]
  let r : B'.left ⟶ A₀.left := P₀.lift π₂ (B'.hom ≫ spMap alg) wr
  have hr1 : r ≫ m₀ = π₂ := P₀.lift_fst _ _ _
  have hr2 : r ≫ A₀.hom = B'.hom ≫ spMap alg := P₀.lift_snd _ _ _
  have Pr : IsPullback r B'.hom A₀.hom (spMap alg) := by
    refine IsPullback.of_right ?_ hr2 P₀
    rw [hr1, ← e_c]; exact P₂
  have wj : m₀ ≫ A.hom = (A₀.hom ≫ spMap fst) ≫ spMap (constHom ρ) := by
    rw [P₀.w, Category.assoc, e_c, ← Category.assoc (spMap fst), e_fa, Category.id_comp]
  let j : A₀.left ⟶ B'.left := P₂.lift m₀ (A₀.hom ≫ spMap fst) wj
  have hj1 : j ≫ π₂ = m₀ := P₂.lift_fst _ _ _
  have hj2 : j ≫ B'.hom = A₀.hom ≫ spMap fst := P₂.lift_snd _ _ _
  have hjr : j ≫ r = 𝟙 _ := P₀.hom_ext (by rw [Category.assoc, hr1, hj1, Category.id_comp])
    (by rw [Category.assoc, hr2, ← Category.assoc, hj2, Category.assoc, e_fa, Category.comp_id, Category.id_comp])
  have hjπ₁ : j ≫ π₁ = m₀ := by rw [hcl A₀.left j A₀.hom hj2, hj1]
  obtain ⟨-, Pj, -⟩ := GlobalTheory.ConstThickening.structure_dualNumber k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
  have hjs : Surjective j :=
    MorphismProperty.of_isPullback (P := @Surjective) Pj.flip GlobalTheory.ConstThickening.surjective_spMap_fst
  have hm : m₀ ≫ A.hom = A₀.hom ≫ spMap fst ≫ spMap ρ := by rw [P₀.w, e_r]
  obtain ⟨Φ, hΦj, hΦp, hΦ⟩ := GlobalTheory.KS.DerMorK.exists_hom_of_derivation k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
    R ρ A.left A.hom m₀ dl hm hdl
  have hb : ∀ y, Φ y = m₀ (r y) := by
    intro y
    obtain ⟨y₀, rfl⟩ := hjs.surj y
    show (j ≫ Φ) y₀ = (j ≫ r ≫ m₀) y₀
    rw [hΦj, ← Category.assoc, hjr, Category.id_comp]
  have wT : (r ≫ T₀) ≫ A₀.hom = B'.hom ≫ spMap alg := by rw [Category.assoc, hT₀h, hr2]
  let TB : B'.left ⟶ B'.left := Pr.lift (r ≫ T₀) B'.hom wT
  have hTB1 : TB ≫ r = r ≫ T₀ := Pr.lift_fst _ _ _
  have hTB2 : TB ≫ B'.hom = B'.hom := Pr.lift_snd _ _ _
  have hcΦ : TB ≫ Φ = Φ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left :=
    _root_.GlobalTheory.KS.LiftComm.translate_comm k A₀.left B'.left A.left m₀ B'.hom r dl Φ hb hΦ _ T₀ TB hT₀ hTB1 hTB2 hcomm
  let α : B'.left ⟶ B'.left := P₁.lift Φ B'.hom hΦp
  have hα1 : α ≫ π₁ = Φ := P₁.lift_fst _ _ _
  have hα2 : α ≫ B'.hom = B'.hom := P₁.lift_snd _ _ _
  have hjα : j ≫ α = j := P₁.hom_ext (by rw [Category.assoc, hα1, hΦj, hjπ₁]) (by rw [Category.assoc, hα2])
  let αo : B' ⟶ B' := Over.homMk α hα2
  have hB' : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₁
  set w : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := η[B'] ≫ αo with hw
  have hαo : αo = lift (toUnit B' ≫ w) (𝟙 B') ≫ μ[B'] := _root_.GlobalTheory.RigidEndo.eq_translate k B' hB' αo (fun Z z y hz => by
    change z ≫ α = z
    rw [← Pj.lift_fst z y hz, Category.assoc, hjα])
  let xo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk x hx
  have wσ : (spMap (constHom ρ) ≫ s.left) ≫ A.hom = 𝟙 _ ≫ spMap (constHom ρ) := by
    rw [Category.assoc, Over.w s, Category.id_comp]; rfl
  let σ : Sp (DualNumber k) ⟶ B'.left := P₂.lift (spMap (constHom ρ) ≫ s.left) (𝟙 _) wσ
  have hσ1 : σ ≫ π₂ = spMap (constHom ρ) ≫ s.left := P₂.lift_fst _ _ _
  have hσ2 : σ ≫ B'.hom = 𝟙 _ := P₂.lift_snd _ _ _
  let σo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk σ hσ2
  have tx := _root_.GlobalTheory.TranslPull.transl_comp_of_isGrpPullback B' A (spMap ρ) π₁ h₁ xo s hx1
  have tσ := _root_.GlobalTheory.TranslPull.transl_comp_of_isGrpPullback B' A (spMap (constHom ρ)) π₂ h₂ σo s hσ1
  have hTBσ : TB = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left := by
    refine P₂.hom_ext ?_ ?_
    · rw [tσ, ← hr1, ← Category.assoc, hTB1, Category.assoc, hT₀, ← Category.assoc]
    · rw [hTB2, Over.w]
  have hcα : αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo := by
    apply Over.OverMorphism.ext
    refine P₁.hom_ext ?_ ?_
    · show α ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']).left ≫ π₁ =
        (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left ≫ α ≫ π₁
      rw [tx, ← Category.assoc, hα1, ← hcΦ, hTBσ]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  haveI : IsCommMonObj B' := hB'.comm
  have hτ : ∀ (u y : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B'), y ≫ (lift (toUnit B' ≫ u) (𝟙 B') ≫ μ[B']) = u * y := by
    intro u y
    rw [← Category.assoc, comp_lift, ← Category.assoc, toUnit_unique (y ≫ toUnit B') (𝟙 _), Category.id_comp,
      Category.comp_id, ← Hom.mul_def]
  have h1 : (η[B'] : 𝟙_ _ ⟶ B') = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have e1 : η[B'] ≫ αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = xo * w := by
    rw [← Category.assoc, ← hw, hτ]
  have e2 : η[B'] ≫ (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo = w * σo := by
    rw [← Category.assoc, hτ, h1, _root_.mul_one]
    nth_rewrite 1 [hαo]
    rw [hτ]
  have key : xo * w = w * σo := by
    rw [← e1, ← e2]
    exact congrArg (η[B'] ≫ ·) hcα
  have hxσ : xo = σo := by
    rw [_root_.mul_comm w σo] at key
    exact _root_.mul_right_cancel key
  have : x = σ := congrArg Over.Hom.left hxσ
  rw [this, hσ1]

end GlobalTheory.TranslHoriz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvariantFieldDualNumberOfIsInvariantTangentVe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDerBridge

theorem valR_add_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f + g) = valR a O f + valR a O g := by
  simp only [valR, dif_pos ha, map_add (f := _)]

theorem valR_mul_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f * g) = valR a O f * valR a O g := by
  simp only [valR, dif_pos ha, map_mul]

theorem isInvDer_of_isInv : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (v : TanM (𝟙 (Sp K)) A) (u : epsR K ⟶ A) (dd : Fld A.left), u.left = (tv v).left → IsTangent u → IsInv A v dd → GlobalTheory.KS.IsInvDer u dd := by
  intro K _ A _ _ v u dd hu ht hd W f
  have hpre : ((fst (epsR K) A ≫ u) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W :=
    GlobalTheory.InvFieldBasis.preimage_translate ht W
  refine GlobalTheory.LogKSBal.ext_valR _ _ fun B _ x hx => ?_
  obtain ⟨β, hβ⟩ : ∃ β : DualNumber K →+* B, x ≫ (fst (epsR K) A).left = spMap β :=
    ⟨(Spec.preimage (x ≫ (fst (epsR K) A).left)).hom, (Spec.map_preimage _).symm⟩
  letI : Algebra K B := (β.comp (algebraMap K (DualNumber K))).toAlgebra
  set e : B := β DualNumber.eps with he_def
  have he : e * e = 0 := by rw [he_def, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  let βa : DualNumber K →ₐ[K] B := { β with commutes' := fun _ => rfl }
  have hβe : βa = GlobalTheory.SqZero.epsTo K e he := DualNumber.algHom_ext (by simp [βa, e])
  have hxw : x ≫ (epsR K ⊗ A).hom = (Chart.sp (R₀ := K) B).hom := by
    rw [← Over.w (fst (epsR K) A), ← Category.assoc, hβ]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let xt : Chart.sp (R₀ := K) B ⟶ epsR K ⊗ A := Over.homMk x hxw
  let z : Chart.sp (R₀ := K) B ⟶ A := xt ≫ snd (epsR K) A
  have hfst : xt ≫ fst (epsR K) A = Chart.spMap (GlobalTheory.SqZero.epsTo K e he) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Chart.spMap_left, ← hβe]
    exact hβ
  have hmu : x ≫ ((fst (epsR K) A ≫ u) * snd (epsR K) A).left =
      ((Chart.spMap (GlobalTheory.SqZero.epsTo K e he) ≫ u : Chart.sp (R₀ := K) B ⟶ A) * z).left := by
    rw [← hfst, Category.assoc, ← MonObj.comp_mul]
    rfl
  have hz : ⊤ ≤ z.left ⁻¹ᵁ W := fun p hp => hx hp
  obtain ⟨-, H⟩ := GlobalTheory.Heat.DlogIndep.valR_translate hu ht hd e he z W hz
  rw [GlobalTheory.LogKSBal.valR_pbT x _ hpre.ge hx, hmu, H, valR_add_of x hx, valR_mul_of x hx,
    GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx, GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx,
    GlobalTheory.LogKSBal.valR_constFn _ x hx hβ]
  rfl

end GlobalTheory.InvDerBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerAffineChartOfBasicOpenStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  first | exact @GlobalTheory.KSChartRes.isKS_top_of_basicOpen | exact GlobalTheory.KSChartRes.isKS_top_of_basicOpen | (intros; apply GlobalTheory.KSChartRes.isKS_top_of_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerOfCohomologousCocycle
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSCoh

open GlobalTheory.LogKSLin
open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res le_preimage_mono)

theorem isKS_of_cohomologous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (a : ∀ i, Γ(t.G.left, W i)ˣ) (u : ∀ i i', Γ(t.G.left, W i ⊓ W i')ˣ), ⨆ i, W i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V) → (∀ i, IsField (W i) (d i)) → (∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r)) → (∀ i i', (u i i').val * resG t.G.left (inf_le_right : W i ⊓ W i' ≤ W i') (a i').val = resG t.G.left (inf_le_left : W i ⊓ W i' ≤ W i) (a i).val * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) → (∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ b, IsTranslate t φ g₀ (v b) (w b)) → valR g₀ O (d i O f - d i' O f) = ∑ b, ∑ b', φ (Θ b b') * ((valR (w b') (W i ⊓ W i') (u i i').val).snd * valR g₀ (W i ⊓ W i') (u i i')⁻¹.val) * (valR (w b) O f).snd) → IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U n v hv D Θ J W j d hj α u hcov hF hD hu hc
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup W i).trans (hcov.le.trans (t.G.hom.preimage_mono inf_le_left))
  choose dd hdF hd0 hdv using fun b => exists_invField U (hv b)
  let cf : ∀ i, Fin n → Γ(t.G.left, W i) := fun i a => -∑ b, (t.G.hom.appLE U.1 (W i) (hWU i)).hom (Θ a b) *
    (dd b (W i) (α i).val * (α i)⁻¹.val)
  refine ⟨J, W, j, fun i O f => d i O f + ∑ a, smulFld (cf i a) (dd a) O f, hcov, hj,
    fun i => isField_add (hF i) (isField_sum fun a => isField_smul _ (isField_mono (hWU i) (hdF a))),
    fun i h s => ?_, fun i i' O hO f S _ φ g w hg hgO hw => ?_⟩
  · beta_reduce
    simp only [smulFld_of_le le_rfl, hd0, mul_zero, Finset.sum_const_zero, add_zero]
    exact hD i h s
  · have hi : O ≤ W i := hO.trans inf_le_left
    have hi' : O ≤ W i' := hO.trans inf_le_right
    have hred := fun b => translate_red (hv b) hg (hw b)
    have hcf : ∀ r, O ≤ W r → valR g O (∑ a, smulFld (cf r a) (dd a) O f) = ∑ a, -∑ b, φ (Θ a b) *
        ((valR (w b) (W r) (α r).val).snd * valR g (W r) (α r)⁻¹.val) * (valR (w a) O f).snd := by
      intro r hr
      have hgr := le_preimage_mono g hr hgO
      set_option synthInstance.maxHeartbeats 100000 in
        rw [valR_eq _ _ hgO, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← valR_eq _ _ hgO, smulFld_of_le hr, valR_mul _ _ hgO, valR_res _ hr hgO,
        hdv a O (hr.trans (hWU r)) f S φ g (w a) hg hgO (hw a), valR_eq _ _ hgr, map_neg, map_sum, neg_mul,
        Finset.sum_mul]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun b _ => ?_)
      rw [← valR_eq _ _ hgr, valR_mul _ _ hgr, valR_mul _ _ hgr, valR_base U _ hg hgr,
        hdv b _ (hWU r) _ S φ g (w b) hg hgr (hw b)]
    have hgii : ⊤ ≤ g ⁻¹ᵁ (W i ⊓ W i') := le_preimage_mono g hO hgO
    have hLL : W i ⊓ W i' ≤ t.PP.L.U (j i) ⊓ t.PP.L.U (j i') := inf_le_inf (hj i) (hj i')
    have e : ∀ b, (valR (w b) _ (u i i').val).snd * valR g _ (u i i')⁻¹.val =
        (valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g _ (t.PP.L.g (j i) (j i'))⁻¹.val +
        ((valR (w b) _ (α i).val).snd * valR g _ (α i)⁻¹.val -
          (valR (w b) _ (α i').val).snd * valR g _ (α i')⁻¹.val) := by
      intro b
      have hwb := GlobalTheory.CechKS.le_preimage_of_red (hred b) hgii
      have h0 := congrArg (valR (w b) (W i ⊓ W i')) (hu i i')
      rw [valR_mul _ _ hwb, valR_mul _ _ hwb] at h0
      erw [valR_res _ _ hwb, valR_res _ _ hwb, valR_res _ _ hwb] at h0
      refine GlobalTheory.CechKS.dlog_of_mul_eq _ _ _ _ _ _ _ _ (by rw [h0])
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) (le_preimage_mono g hi hgO) (α i))
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) (le_preimage_mono g hi' hgO) (α i'))
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) (le_preimage_mono g hLL hgii) _)
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) hgii (u i i'))
    beta_reduce
    rw [show d i O f + ∑ a, smulFld (cf i a) (dd a) O f - (d i' O f + ∑ a, smulFld (cf i' a) (dd a) O f) =
        (d i O f - d i' O f) + ∑ a, smulFld (cf i a) (dd a) O f - ∑ a, smulFld (cf i' a) (dd a) O f by ring,
      GlobalTheory.CechInv.valR_sub _ _ hgO, valR_add _ _ hgO, hc i i' O hO f S φ g w hg hgO hw, hcf i hi, hcf i' hi']
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    linear_combination (φ (Θ a b) * (valR (w a) O f).snd) * e b

end GlobalTheory.LogKSCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenKawamataLogTerminalLocusLogCanonicalLocus
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isOpen_kltLocus_lcLocus : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  intro hP k _ _ X _ _ _ p n hp hdim Δ m G hm hG
  obtain ⟨η, hη⟩ := hG.exists_isLogMult hm
  have hZ : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : x ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at this
    exact this
  obtain ⟨Y, hY, s, hs, K, B, hres, -⟩ := GlobalTheory.T.exists_log_resolution hP k X p n hp hdim η m G hη.ne_zero ⊥ hZ
  haveI := hres.smooth
  haveI : Smooth (s ≫ p) := hres.smooth.smooth
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (s ≫ p)
  exact GlobalTheory.T.log_resolution_multiplier_open k X p n hp hdim Δ η m G Y s K B hη hres

end GlobalTheory.Discrepancy
end

