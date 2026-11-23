module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0281
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0503
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionNbhdIsolatedFibrePoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ZmtNbhd

theorem quasiFiniteAt_of_isolated : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), LocallyOfFiniteType φ →
    ∀ (z : H) (O : H.Opens), z ∈ O → (∀ w ∈ O, φ w = φ z → w = z) → φ.QuasiFiniteAt z := by
  intro H X φ _ z O hzO hO
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (φ.fiberHomeo (φ z)).isOpen_image]
  simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  rw [isOpen_induced_iff]
  refine ⟨O, O.isOpen, ?_⟩
  ext ⟨w, hw⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext (hO w h hw)
  · intro h
    have : w = z := congrArg Subtype.val h
    exact this ▸ hzO

theorem exists_image_of_isOpenImmersion : ∀ (U T X : Scheme.{0}) (j : U ⟶ T) (q : T ⟶ X),
    IsOpenImmersion j → QuasiCompact j → IsFinite q →
    ∃ (X' : Scheme.{0}) (ν : X' ⟶ X) (i : U ⟶ X'), IsFinite ν ∧ IsOpenImmersion i ∧
      i ≫ ν = j ≫ q ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  intro U T X j q _ _ _
  refine ⟨j.image, j.imageι ≫ q, j.toImage, inferInstance, inferInstance, by simp, inferInstance, ?_⟩
  intro V
  exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (C := CommRingCat)
    (F := j.image.sheaf) j.toImage.c V (fun x _ => j.stalkFunctor_toImage_injective x)

theorem exists_finite_openImmersion_nbhd : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), IsNoetherian X → IsSeparated φ → LocallyOfFiniteType φ → QuasiCompact φ → ∀ Z : Set H, (∀ z ∈ Z, ∃ O : H.Opens, z ∈ O ∧ ∀ w ∈ O, φ w = φ z → w = z) → ∃ (H' : H.Opens) (X' : Scheme.{0}) (ν : X' ⟶ X) (i : H'.toScheme ⟶ X'), Z ⊆ H' ∧ IsFinite ν ∧ IsOpenImmersion i ∧ i ≫ ν = H'.ι ≫ φ ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  intro H X φ hX hsep hloft hqc Z hZ
  let H' := φ.quasiFiniteLocus
  have hZH : Z ⊆ (H' : Set H) := fun z hz => by
    obtain ⟨O, hzO, hO⟩ := hZ z hz
    exact quasiFiniteAt_of_isolated H X φ hloft z O hzO hO
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian φ
  have : QuasiCompact H'.ι := inferInstance
  obtain ⟨T, q, j, hq, hj, hjq⟩ := _root_.GlobalTheory.ZMTFin.exists_finite_openImmersion H'.toScheme X (H'.ι ≫ φ) hX inferInstance
    inferInstance inferInstance inferInstance
  have : QuasiCompact j := by
    have : QuasiCompact (j ≫ q) := by rw [hjq]; infer_instance
    exact QuasiCompact.of_comp j q
  obtain ⟨X', ν, i, hν, hi, hiν, hdom, hinj⟩ := exists_image_of_isOpenImmersion H'.toScheme T X j q hj this hq
  exact ⟨H', X', ν, i, hZH, hν, hi, by rw [hiν, hjq], hdom, hinj⟩

end GlobalTheory.ZmtNbhd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagModelPointOfFlagBundleFieldPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open GlobalTheory.Toroidal (gen genι genStr)

theorem exists_rel_of_mem_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → ∃ z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hbar K _ p hp

  obtain ⟨yF, hyF, hcar⟩ := GlobalTheory.Mean4O.CompModel.exists_flagPt C p

  haveI := Y.jQ_open
  have hr : Set.range (p ≫ C.π) ⊆ Set.range Y.jQ := by
    rintro _ ⟨s, rfl⟩
    exact hp s
  let y := IsOpenImmersion.lift Y.jQ (p ≫ C.π) hr
  have hy : y ≫ Y.jQ = p ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hys : y ≫ pullback.snd _ _ = spMap yF.fK := by
    rw [← Y.jQ_over, ← Category.assoc, hy, hyF]
    exact yF.y_over

  obtain ⟨P, hPy, hPw⟩ := GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) Y K yF.fK y
    (yF.y ≫ genι Y) yF.frame hys (by rw [← Category.assoc, hy, hyF])
  letI : Algebra c.F K := yF.fK.toAlgebra
  have hPX : GlobalTheory.FlagMod.frX P = y := hPy
  have hl := X.lies_ptY P
  have hxg : X.ptY P ≫ X.π = yF.y ≫ genι Y := by
    rw [hl.1, hPX, Model.j, ← Category.assoc, hy, hyF]

  have hr₀ : Set.range (X.ptY P) ⊆ Set.range (GlobalTheory.CompHS.inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    show X.π (X.ptY P s) ∈ GlobalTheory.CompHS.barComp Y Z
    have e : X.π (X.ptY P s) = genι Y (j (f (p s))) := by
      rw [← Scheme.Hom.comp_apply, hxg, ← hyF, hπ]
      rfl
    rw [e]
    exact (hbar _).2 ⟨f (p s), rfl⟩
  let z := IsOpenImmersion.lift (GlobalTheory.CompHS.inc₀ X Z) (X.ptY P) hr₀
  have hz : z ≫ GlobalTheory.CompHS.inc₀ X Z = X.ptY P := IsOpenImmersion.lift_fac _ _ _
  refine ⟨z, ?_⟩
  rw [hz]

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY P)
  have hφ : X.ptY P ≫ X.π ≫ Y.s = spMap yF.fK := GlobalTheory.CompHS.ptY_str X P
  obtain ⟨g₂, hg₂⟩ := hFE K yF.fK (X.ptY P) k hk hφ
  refine ⟨yF.fK, k, hk, g₂, hφ, hg₂, ?_⟩

  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd P) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  have ht' := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).2.2.1 _ _ _ ht
  have hPx : GlobalTheory.FlagMod.frX P ≫ Y.j = X.ptY P ≫ X.π := hl.1.symm
  choose b hb hdiag hsum using fun τ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (X.F.M k).toMChart) (X.F.inM hk rfl) hPx hQ.over ht' τ

  have hgv : ∀ τ i, yF.frame.v τ i = (tv (GlobalTheory.FlagMod.frVec Y P hPx τ i)).left := by
    intro τ i
    obtain ⟨w, hw1, hw2, hw3⟩ := hPw τ i
    rw [← hPX] at hw1
    have hL : w = GlobalTheory.FlagMod.liftTan Y (GlobalTheory.FlagMod.frX P) ((GlobalTheory.FlagMod.frX_fst P).symm ▸ P.tan τ i) :=
      Y.m0.cart.1.hom_ext (hw2.trans (GlobalTheory.FlagMod.liftTan_univ _ _).symm)
        (hw1.trans (GlobalTheory.FlagMod.liftTan_over _ _).symm)
    show yF.frame.v τ i = _
    rw [← hw3, hL]
    rfl
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
  have hd : yF.frame.Tri (RingHom.id K) g₂ (fun τ i => (t⁻¹) (some ⟨τ, i⟩)) := by
    refine ⟨by rw [h2, Category.id_comp, hxg], rfl, fun τ i => ⟨fun m => b τ m i, hdiag τ i,
      fun m hm => hb τ hm, ?_⟩⟩
    simp only [h1, Category.id_comp]
    have e : (fun m => yF.frame.v τ m) = fun m => (tv (GlobalTheory.FlagMod.frVec Y P hPx τ m)).left := funext (hgv τ)
    rw [e, hg₂ τ i, GlobalTheory.LieMet.isComb_iff, ← hQ.frVec_eq rfl hQ.over τ]
    exact hsum τ i
  exact carries_of_tri C hd hcar

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibrePullbackSiegelTraitModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.GenFibre

theorem exists_generic_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (f : T.V →+* W) (fK : FractionRing T.V →+* FractionRing W), (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left, IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧ κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) := by
  intro g n o _ ζ F T W _ _ f fK hfK
  have hsq : spMap fK ≫ jK T.V = jK W ≫ spMap f := by
    have h : fK.comp (algebraMap T.V (FractionRing T.V)) = (algebraMap W (FractionRing W)).comp f := RingHom.ext hfK
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]
  have gB := ((isGrpPullback_pullback ((Over.pullback (spMap f)).obj T.G) (jK W)).comp
    (isGrpPullback_pullback T.G (spMap f))).congr hsq.symm rfl
  have he := isGrpPullback_pullback T.G (jK T.V)
  set B := (Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)
  have w : (pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f)) ≫ T.G.hom =
      (B.hom ≫ spMap fK) ≫ jK T.V := by
    rw [Category.assoc B.hom]; exact gB.1.w
  obtain ⟨α, h₁, h₂⟩ : ∃ α : B.left ⟶ ((Over.pullback (jK T.V)).obj T.G).left,
      α ≫ pullback.fst T.G.hom (jK T.V) =
        pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) ∧
      α ≫ ((Over.pullback (jK T.V)).obj T.G).hom = B.hom ≫ spMap fK :=
    ⟨he.1.lift _ _ w, he.1.lift_fst _ _ _, he.1.lift_snd _ _ _⟩
  have gα := he.cancel (gB.congr rfl h₁.symm) h₂
  haveI := T.U.gen_hom
  refine ⟨α ≫ T.U.gen.hom.left, (gα.comp (isGrpPullback_of_iso T.U.gen)).congr (Category.comp_id _) rfl, ?_⟩
  rw [Category.assoc, ← Category.assoc T.U.gen.hom.left, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]
  exact h₁

end GlobalTheory.Poinc.GenFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericallyRegularQuotientDominatingPrime
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem prime_generically_regular_quotient :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)]
      (B : Type) [CommRing B] [Algebra Λ B] [Algebra.FiniteType Λ B] (p : Ideal B) [p.IsPrime],
      (∀ a : Λ, algebraMap Λ B a ∈ p → a = 0) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q →
        g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q))) := by
  intro Λ _ _ _ _ B _ _ _ p _ hp
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType Λ B)
  set Q : Ideal (MvPolynomial (Fin n) Λ) := p.comap φ with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0 := by
    intro a ha
    apply hp a
    have : φ (MvPolynomial.C a) ∈ p := ha
    rwa [MvPolynomial.algHom_C] at this
  obtain ⟨h, f, s, g₀, hg₀, hfQ, hgQ, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (Fin n) Q hQ
  set δ := (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det with hδ
  refine ⟨φ (g₀ * δ), ?_, ?_⟩
  · intro hmem
    have : g₀ * δ ∈ Q := hmem
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h1 | h1
    · exact hg₀ h1
    · exact hdet h1
  · intro q _ hpq hgq
    set N : Ideal (MvPolynomial (Fin n) Λ) := q.comap φ with hN
    haveI : N.IsPrime := Ideal.comap_isPrime _ _
    have hQN : Q ≤ N := Ideal.comap_mono hpq
    have hgN : g₀ * δ ∉ N := hgq
    have hg₀N : g₀ ∉ N := fun h1 => hgN (N.mul_mem_right _ h1)
    have hδN : δ ∉ N := fun h1 => hgN (N.mul_mem_left _ h1)
    let D : Fin h → Derivation ℤ (MvPolynomial (Fin n) Λ) (MvPolynomial (Fin n) Λ) :=
      fun i => (MvPolynomial.pderiv (s i)).restrictScalars ℤ
    have hdetD : (Matrix.of fun i j => D i (f j)).det ∉ N := by
      simpa [D] using hδN
    have hreg := _root_.GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient (MvPolynomial (Fin n) Λ) h f D N (fun j => hQN (hfQ j)) hdetD
    have heq : (Ideal.span (Set.range f)).map
          (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N)) =
        Q.map (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N)) := by
      apply le_antisymm
      · apply Ideal.map_mono
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        exact hfQ j
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        have hu : IsUnit (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N) g₀) :=
          IsLocalization.map_units (Localization.AtPrime N) (⟨g₀, hg₀N⟩ : N.primeCompl)
        rw [← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul]
        exact Ideal.mem_map_of_mem _ (hgQ x hx)
    rw [heq] at hreg
    obtain ⟨e⟩ := GlobalTheory.localization_quotient_comap_equiv (MvPolynomial (Fin n) Λ) B
      φ.toRingHom hφ p q
    haveI : IsRegularLocalRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        (p.comap φ.toRingHom).map (algebraMap _ (Localization.AtPrime (q.comap φ.toRingHom)))) := hreg
    exact IsRegularLocalRing.of_ringEquiv e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeomPtSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem exists_geomPt_specializes (R : Type) [CommRing R] (R₁ : Subring R) (p : Sp R₁) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ Sp R), ∀ u, (z ≫ spMap R₁.subtype) u ⤳ p := by
  haveI := p.isPrime
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R₁)) (J := p.asIdeal) bot_le
  obtain ⟨P, hP, hPq⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := R₁.subtype) Subtype.val_injective q hq
  obtain ⟨K, _, _, t, ht⟩ := GlobalTheory.SiegelTypings.exists_geomPt (S := Sp R) ⟨P, hP⟩
  refine ⟨K, inferInstance, inferInstance, t, fun u => ?_⟩
  have e : t u = ⟨P, hP⟩ := by
    obtain ⟨v, hv⟩ := ht
    rw [Subsingleton.elim u v, hv]
  rw [Scheme.Hom.comp_apply, e]
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  show P.comap R₁.subtype ≤ p.asIdeal
  rw [hPq]
  exact hqp

section Labels

variable {h M : ℕ}

def toStd : (Fin (h + h) → ZMod M) →+ IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M where
  toFun c := (fun i => c (Fin.castAdd h i), fun i => c (Fin.natAdd h i))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toStd_append (a : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) : toStd (Fin.append a.1 a.2) = a :=
  Prod.ext (funext fun i => Fin.append_left a.1 a.2 i) (funext fun i => Fin.append_right a.1 a.2 i)

theorem append_toStd (c : Fin (h + h) → ZMod M) : Fin.append (toStd c).1 (toStd c).2 = c :=
  Fin.append_castAdd_natAdd

theorem toStd_injective : Function.Injective (toStd (h := h) (M := M)) := fun c c' e => by
  rw [← append_toStd c, ← append_toStd c', e]

theorem sum_val_smul [NeZero M] (c : Fin (h + h) → ZMod M) :
    ∑ i, (c i).val • toStd (Pi.single i (1 : ZMod M)) = toStd c := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [← map_nsmul, ← map_sum]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Pi.single_smul, nsmul_eq_mul, _root_.mul_one, ZMod.natCast_zmod_val]

end Labels

section Sections

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem lv_zero (add : ∀ a b, lv (a + b) = lv a * lv b) : lv 0 = 1 := by
  have e := add 0 0
  rw [add_zero] at e
  exact left_eq_mul.1 e

theorem lv_nsmul (add : ∀ a b, lv (a + b) = lv a * lv b) (n : ℕ) (a) : lv (n • a) = lv a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, lv_zero add]
  | succ n ih => rw [succ_nsmul, add, ih, pow_succ]

theorem lv_pow (add : ∀ a b, lv (a + b) = lv a * lv b) (a) : lv a ^ M = 1 := by
  rw [← lv_nsmul add, show M • a = 0 by ext i <;> simp, lv_zero add]

theorem linComb_lv (add : ∀ a b, lv (a + b) = lv a * lv b) {T : Over S} (g : T ⟶ 𝟙_ (Over S)) :
    ∀ {r : ℕ} (v : Fin r → IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) (n : Fin r → ℕ),
      Out.linComb (fun i => g ≫ lv (v i)) n = g ≫ lv (∑ i, n i • v i) := by
  intro r
  induction r with
  | zero =>
    intro v n
    simp [Out.linComb, lv_zero add]
  | succ r ih =>
    intro v n
    have e := ih (fun i => v i.succ) (fun i => n i.succ)
    simp only [Out.linComb] at e ⊢
    rw [List.ofFn_succ, List.prod_cons, e, Fin.sum_univ_succ, add, MonObj.comp_mul, lv_nsmul add,
      MonObj.comp_pow]

end Sections

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

section Cond

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem cond_iff [NeZero M] (add : ∀ a b, lv (a + b) = lv a * lv b) {k : Type} [Field k] (x : Sp k ⟶ S) :
    ((Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) ↔
    ∀ y : Over.mk x ⟶ A, y ^ M = 1 → ∃! c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) = y := by
  have E : ∀ c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) =
        toUnit (Over.mk x) ≫ lv (toStd c) := fun c =>
    (linComb_lv add (toB x) _ _).trans (by rw [sum_val_smul]; rfl)
  have tors : ∀ a, (toUnit (Over.mk x) ≫ lv a) ^ M = 1 := fun a => by
    rw [← MonObj.comp_pow, lv_pow add, MonObj.comp_one]
  constructor
  · rintro ⟨inj, sp⟩ y hy
    obtain ⟨a, rfl⟩ := (sp y).1 hy
    refine ⟨Fin.append a.1 a.2, by beta_reduce; rw [E, toStd_append], fun c hc => toStd_injective ?_⟩
    rw [toStd_append]
    exact inj ((E c).symm.trans hc)
  · intro H
    refine ⟨fun a b e => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
    · obtain ⟨c, -, hc⟩ := H _ (tors a)
      have ea := hc (Fin.append a.1 a.2) (by beta_reduce; rw [E, toStd_append])
      have eb := hc (Fin.append b.1 b.2) (by beta_reduce; rw [E, toStd_append]; exact e.symm)
      rw [← toStd_append a, ← toStd_append b, ea, eb]
    · obtain ⟨c, hc, -⟩ := H g hg
      exact ⟨toStd c, (E c).symm.trans hc⟩
    · rintro ⟨a, rfl⟩
      exact tors a

end Cond

section Transfer

variable {h M : ℕ} {S S₁ : Scheme.{0}} {A : Over S} [GrpObj A] {A₁ : Over S₁} [GrpObj A₁] {f : S ⟶ S₁}
  {φ : A.left ⟶ A₁.left} {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}
  {lv₁ : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S₁) ⟶ A₁)}

theorem push_lv (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) (T : Over S) (a) :
    pushHom hp T (toUnit T ≫ lv a) = toUnit (Over.mk (T.hom ≫ f)) ≫ lv₁ a := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (lv a).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ (lv₁ a).left
  rw [Category.assoc, hl, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem cond_push (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) {k : Type} [Field k]
    (x : Sp k ⟶ S)
    (H : (Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) :
    (Function.Injective fun a => toUnit (Over.mk (x ≫ f)) ≫ lv₁ a) ∧
      ∀ g : Over.mk (x ≫ f) ⟶ A₁, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk (x ≫ f)) ≫ lv₁ a = g := by
  have P := push_lv hp hl (Over.mk x)
  have inj := push_injective hp (Over.mk x)
  refine ⟨fun a b e => H.1 (inj ?_), fun g => ?_⟩
  · rw [P, P]
    exact e
  · obtain ⟨g', rfl⟩ := push_surjective hp (Over.mk x) g
    rw [← map_pow, ← map_one (pushHom hp (Over.mk x)), inj.eq_iff, H.2 g']
    refine exists_congr fun a => ?_
    rw [← inj.eq_iff, P]
    rfl

end Transfer

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem isLevel_of_subring : ∀ (h M : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ : A.left ⟶ A₁.left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → IsUnit (M : R₁) → IsAbelianScheme A₁ → IsGrpPullback A A₁ (spMap R₁.subtype) φ → (∀ a, (lv a).left ≫ φ = spMap R₁.subtype ≫ (lv₁ a).left) → (∀ a b, lv₁ (a + b) = lv₁ a * lv₁ b) → IsLevel A lv → IsLevel A₁ lv₁ := by
  intro h M R _ R₁ A _ A₁ _ φ lv lv₁ hM hu hA hp hl hadd hlev
  haveI : NeZero M := ⟨hM.ne'⟩
  have hu' : IsUnit ((M : ℕ) : Γ(Sp R₁, ⊤)) := by
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom
  refine ⟨hadd, fun k _ _ x => (cond_iff hadd x).2 fun y hy => ?_⟩
  refine torsion_basis_of_generization A₁ M (h + h) (fun i => lv₁ (toStd (Pi.single i 1))) hA hM hu'
    (fun i => lv_pow hadd _) (fun p => ?_) k x y hy
  obtain ⟨K, _, _, z, hz⟩ := exists_geomPt_specializes R R₁ p
  exact ⟨K, inferInstance, inferInstance, z ≫ spMap R₁.subtype, hz,
    (cond_iff hadd _).1 (cond_push hp hl z (hlev.2 K z))⟩

end GlobalTheory.LevelDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerGenericEigenFrameStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logKodairaSpencer_genericEigenFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z f₀.v D := by
  first | exact @GlobalTheory.LogKSDiv.GenKSProof.exists_genKS | exact GlobalTheory.LogKSDiv.GenKSProof.exists_genKS | (intros; apply GlobalTheory.LogKSDiv.GenKSProof.exists_genKS <;> assumption)
end

