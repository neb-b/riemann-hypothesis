module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousPolynomialVolumePullbackCombina
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVariety

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}

theorem Cpt.basic_of_isDedFrac (C : Cpt c t₀ β) (hβ : IsDedFrac β) :
    IsLocallyNoetherian C.X ∧ IsReduced C.X ∧ IsProper C.s ∧ IsPreimmersion C.j ∧ Flat C.j ∧ IsDominant C.j ∧
      QuasiCompact C.j ∧ C.j ≫ C.s = c ≫ spMap β := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
  letI := β.toAlgebra
  obtain ⟨h1, -, -, h2, h3, h4, h5⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  refine ⟨h1, ?_, ?_, h2, h3, h4, h5, ?_⟩
  · have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  · obtain ⟨N, i, hi, e⟩ := C.proj
    have := isProper_str O N
    rw [← e]; infer_instance
  · rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem Cpt.exists_extension_of_above (C : Cpt c t₀ β) (C' : Cpt c' t₀' β') (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    {b : O →+* O'} {r : U' ⟶ U} {ν : SABMap t₀' t₀ r} (A : C'.Above C b r ν) (hb : IsFinite (spMap b))
    (hr : Surjective r) {R : Type} [CommRing R] {Z : Scheme.{0}} (sZ : Z ⟶ Sp R) (b' : R →+* O') (q : C'.X ⟶ Z)
    (hq : q ≫ sZ = C'.s ≫ spMap b') (hfin : IsFinite (pullback.lift q C'.s hq))
    (e : U ⟶ U) (e' : U' ⟶ U') (he : e ≫ c = c) (he' : e' ≫ c' = c') (hee : e' ≫ r = r ≫ e)
    (hqe : e' ≫ C'.j ≫ q = C'.j ≫ q) :
    ∃ ρ : C.X ⟶ C.X, ρ ≫ C.s = C.s ∧ C.j ≫ ρ = e ≫ C.j := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := C.basic_of_isDedFrac hβ
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := C'.basic_of_isDedFrac hβ'
  obtain ⟨ρ', ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C'.X U' _ C'.X C'.j C'.normal m4 m5 m6 m7
    (pullback.lift q C'.s hq) (pullback.lift q C'.s hq) (e' ≫ C'.j) inferInstance (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, hqe]
      · simp only [Category.assoc, pullback.lift_snd, m8, reassoc_of% he'])
  have h3 : ρ' ≫ C'.s = C'.s := by
    have := congrArg (· ≫ pullback.snd sZ (spMap b')) h2
    simpa only [Category.assoc, pullback.lift_snd] using this
  have hπf : IsFinite A.π := by
    have h4 := A.fin
    have h5 : IsFinite (pullback.fst C.s (spMap b)) := inferInstance
    have h6 : A.π = pullback.lift A.π C'.s A.π_over ≫ pullback.fst C.s (spMap b) := (pullback.lift_fst _ _ _).symm
    rw [h6]; infer_instance
  have hπd : IsDominant A.π := by
    have : IsDominant (C'.j ≫ A.π) := by rw [A.j_comm]; infer_instance
    exact IsDominant.of_comp C'.j A.π
  have hπs : Surjective A.π := surjective_of_isDominant_of_isClosed_range A.π A.π.isClosedMap.isClosed_range
  obtain ⟨ρ, h7, h8⟩ := GlobalTheory.exists_desc_of_isFinite_of_densePart (Sp O) C'.X C.X U' U C.X A.π C'.j C.j r C.s C.s
    (ρ' ≫ A.π) (e ≫ C.j) C.normal m2 hπf hπs hr m6 m7 n4 n5 n6 n7 inferInstance inferInstance A.j_comm
    (by rw [reassoc_of% h1, A.j_comm, reassoc_of% hee])
    (by rw [Category.assoc, A.π_over, reassoc_of% h3])
    (by rw [Category.assoc, n8, reassoc_of% he])
  refine ⟨ρ, ext_of_isDominant C.j ?_, h7⟩
  rw [reassoc_of% h7, n8, reassoc_of% he]

end

theorem extendsAut_of_above : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (h : l₁.A = N) (O₀ O₁ : Type) [CommRing O₀] [CommRing O₁] (β₀ : O₀ →+* KA l₀) (β₁ : O₁ →+* KA l₁) (C : Cpt (Xo l₀).s (Xo l₀).univ.t β₀) (C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁) (b : O₀ →+* O₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (_ : C₁.Above C b r ν) (b' : RZ H n N →+* O₁) (q : C₁.X ⟶ T.Z) (hq : q ≫ T.s = C₁.s ≫ spMap b'), IsDedFrac β₀ → IsDedFrac β₁ → Algebra.FiniteType ℤ O₀ → IsFinite (spMap b) → IsFinite (pullback.lift q C₁.s hq) → C₁.j ≫ q = T.a l₁ h → l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → N.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → Surjective r → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k ∧ β₁.comp b = k.comp β₀) → ∀ (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → C.ExtendsAut r₀ ν₀ := by
  intro hext L1 L2 L3 E _ _ _ H D Xo n N T hpq l₀ l₁ h O₀ O₁ _ _ β₀ β₁ C C₁ b r ν A b' q hq hβ₀ hβ₁ hft hb hfin hjq
    hA hM hMb hcop hlev hr hk r₀ ν₀ g hr₀ hη
  obtain ⟨k, hk1, hk2, -⟩ := hk
  obtain ⟨r₁, ν₁, h1, h2, -, h4⟩ := _root_.GlobalTheory.LiftAut.exists_lift_keeping_etaA L1 L2 L3 E H D Xo hpq l₀ l₁ r ν r₀ ν₀ g hA hM hMb (h ▸ hcop) hlev
    ⟨k, hk1, hk2⟩ hr₀ hη
  have h5 : r₁.hom ≫ T.a l₁ h = T.a l₁ h := (T.compat l₁ l₁ h h r₁.hom ν₁ (RingHom.id _) (fun _ => rfl) (by
    rw [h1]
    exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id (CommRingCat.of (KA l₁))).symm)) h4).1
  obtain ⟨ρ, hρ1, hρ2⟩ := C.exists_extension_of_above C₁ hβ₀ hβ₁ A hb hr T.s b' q hq hfin r₀.hom r₁.hom hr₀ h1 h2
    (by rw [hjq, h5])
  obtain ⟨ρ', hρ1', hρ2'⟩ := C.exists_extension_of_above C₁ hβ₀ hβ₁ A hb hr T.s b' q hq hfin r₀.inv r₁.inv
    (by rw [Iso.inv_comp_eq, hr₀]) (by rw [Iso.inv_comp_eq, h1])
    (by rw [Iso.inv_comp_eq, reassoc_of% h2, Iso.hom_inv_id, Category.comp_id])
    (by rw [hjq, Iso.inv_comp_eq, h5])
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := C.basic_of_isDedFrac hβ₀
  let σ : C.X ≅ C.X :=
    { hom := ρ
      inv := ρ'
      hom_inv_id := ext_of_isDominant_of_isSeparated C.s (by rw [Category.assoc, hρ1', hρ1, Category.id_comp]) C.j
        (by rw [reassoc_of% hρ2, hρ2', Iso.hom_inv_id_assoc, Category.comp_id])
      inv_hom_id := ext_of_isDominant_of_isSeparated C.s (by rw [Category.assoc, hρ1, hρ1', Category.id_comp]) C.j
        (by rw [reassoc_of% hρ2', hρ2, Iso.inv_hom_id_assoc, Category.comp_id]) }
  obtain ⟨mu, hmu⟩ := exists_sabMap_extending hext E H _ _ _ _ _ β₀ _ _ _ _ _ β₀ C C r₀.hom ν₀ ρ hβ₀ hft
    (Xo l₀).univ.proper hρ2
  exact ⟨σ, mu, hρ1, hρ2, hmu⟩

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalOfGenericFibreDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.PolDvr

theorem exists_polAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsLocalRing R] (t : SAB H (Sp R)) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) :
    ∃ (P : Out.PolAV (Sp R)) (e : P.A ≅ t.G), (∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] (f : Sp R ⟶ S)
      (φ : t.G.left ⟶ B.left) (M : LB B.left), IsGrpPullback t.G B f φ → LBIso t.PP.L (M.pull φ) →
        IsGrpPullback P.A B f (e.hom.left ≫ φ) ∧ LBIso P.L (M.pull (e.hom.left ≫ φ))) := by
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim R t.G hab
  let P : Out.PolAV (Sp R) :=
    { A := t.G
      isAb := hab
      g := g
      smoothDim := hg
      L := t.PP.L
      isLB := t.PP.isLB
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := GlobalTheory.CechPic.sym_of_isSymmetric t.PP t.sym
      ample := hA
      ktriv := hK }
  refine ⟨P, Iso.refl _, ?_⟩
  intro S B _ f φ M h₁ h₂
  simp only [Iso.refl_hom, Over.id_left, Category.id_comp]
  exact ⟨h₁, h₂⟩

theorem relAmple_kTriv_of_generic_fibre : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (t : SAB H (Sp V)) (tK : SAB H (Sp K)) (_ : SABMap tK t (spMap (algebraMap V K))), IsProper t.G.hom → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  intro hH hL hL2 E _ _ _ H V K _ _ _ _ _ _ t tK m hp hA hK
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  have hiso : LBIso tK.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨t', -, e, -, -, hA', hK'⟩ := _root_.GlobalTheory.GoodPol.exists_sab_of_generic hH hL hL2 E H V K t.G tK m.cm.F hab m.cart hA hK
  have hp' : IsProper t'.G.hom := by
    have := hp
    have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨P, e', -⟩ := exists_polAV t' hp' hA' hK'
  have : IsIso (e'.hom ≫ e.hom).left := ((Over.forget _).mapIso (e' ≪≫ e)).isIso_hom
  have hAmp : Out.RelAmple t.G t.PP.L :=
    _root_.GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous hL hL2 V K P t.G (e'.hom ≫ e.hom) t.PP.L tK.G m.cm.F tK.PP.L hab t.PP.isLB tK.PP.isLB
      inferInstance inferInstance inferInstance m.cart hiso hA
  refine ⟨hAmp, ?_⟩
  have hpK : IsProper tK.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp
  obtain ⟨P₀, e₀, hu⟩ := exists_polAV tK hpK hA hK
  obtain ⟨hpb, hlb⟩ := hu t.G (spMap (algebraMap V K)) m.cm.F t.PP.L m.cart hiso
  have hsym : ∃ s : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![(ι[t.G]).left, 𝟙 t.G.left] ![1, -1]), s.IsGen := by
    obtain ⟨s, hs, -⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric t.PP t.sym
    exact ⟨s, hs⟩
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hL.globalFns (Sp V) t.G hab).1 t.PP ⟨t.cub.t, t.cub.isGen⟩ hsym
  have key := _root_.GlobalTheory.KTrivSpread.kTriv_of_generic_fibre hL V K P₀ t.G M (e₀.hom.left ≫ m.cm.F) hab hpb (by rw [hM]; exact hlb)
    (by rw [hM]; exact hAmp)
  rw [hM] at key
  exact key

end GlobalTheory.PolDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SumMonomialAddSingle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.VolPoly

theorem eval_eq_of_eventually {r r' : ℕ} (Ψ : MvPolynomial (Fin (r + 1)) ℚ) (Ψ' : MvPolynomial (Fin (r' + 1)) ℚ)
    (a : Fin (r + 1) → ℤ) (a' : Fin (r' + 1) → ℤ)
    (h : ∀ᶠ t : ℕ in Filter.atTop,
      MvPolynomial.eval (fun i => (((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ =
        MvPolynomial.eval (fun i => (((a' + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ') :
    MvPolynomial.eval (fun i => (a i : ℚ)) Ψ = MvPolynomial.eval (fun i => (a' i : ℚ)) Ψ' := by
  have key : ∀ {r : ℕ} (Ψ : MvPolynomial (Fin (r + 1)) ℚ) (a : Fin (r + 1) → ℤ), ∃ p : Polynomial ℚ,
      ∀ t : ℕ, p.eval (t : ℚ) =
        MvPolynomial.eval (fun i => (((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ := by
    intro r Ψ a
    refine ⟨MvPolynomial.aeval (fun i => Polynomial.C (a i : ℚ) + if i = 0 then Polynomial.X else 0) Ψ, fun t => ?_⟩
    rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval]
    congr 2
    funext i
    by_cases hi : i = 0 <;> simp [hi, Pi.single_apply]
  obtain ⟨p, hp⟩ := key Ψ a
  obtain ⟨p', hp'⟩ := key Ψ' a'
  have e : p = p' := by
    obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 h
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite t₀).image (f := fun t : ℕ => (t : ℚ)) Nat.cast_injective.injOn)
    rintro _ ⟨t, ht, rfl⟩
    show p.eval (t : ℚ) = p'.eval (t : ℚ)
    rw [hp, hp', ht₀ t ht]
  have h0 := (hp 0).symm.trans (e ▸ hp' 0)
  simpa using h0

theorem sum_monomial_add_single {r : ℕ} (a : Fin (r + 1) → ℤ) (t : ℕ) :
    ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) ((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i) =
      ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (a i) + (t : Polynomial ℤ) := by
  simp only [Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
  congr 1
  rw [Fin.sum_univ_succ]
  simp

theorem exists_poly_extension (g : ℕ) (A : Polynomial ℤ → Prop) (V : Polynomial ℤ → ℚ → Prop)
    (hV : ∀ F x y, V F x → V F y → x = y)
    (hΨ : ∀ r : ℕ, ∃ Ψ : MvPolynomial (Fin r) ℚ, Ψ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ,
      A (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) →
        V (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) (MvPolynomial.eval (fun i => (a i : ℚ)) Ψ))
    (hA : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, A (F + t)) :
    ∃ D : Polynomial ℤ → ℚ, (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ,
      D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) ∧
      ∀ F, A F → V F (D F) := by
  choose Ψ hh hΨ using hΨ
  have hF : ∀ F : Polynomial ℤ,
      ∑ i : Fin (F.natDegree + 1), Polynomial.monomial (i : ℕ) (F.coeff i) = F := fun F => by
    rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (F.coeff i))]
    exact (F.as_sum_range).symm
  refine ⟨fun F => MvPolynomial.eval (fun i : Fin (F.natDegree + 1) => (F.coeff i : ℚ)) (Ψ _), fun r => ?_,
    fun F h => ?_⟩
  · refine ⟨MvPolynomial.aeval (Fin.snoc (α := fun _ => MvPolynomial (Fin r) ℚ) MvPolynomial.X 0) (Ψ (r + 1)), ?_,
      fun a => ?_⟩
    · have := (hh (r + 1)).aeval (n := 1) (Fin.snoc (α := fun _ => MvPolynomial (Fin r) ℚ) MvPolynomial.X 0)
        (fun i => by
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using MvPolynomial.isHomogeneous_zero _ _ _
          · simpa using MvPolynomial.isHomogeneous_X _ _)
      simpa using this
    · set F := ∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i) with hFa
      have e : ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (Fin.snoc (α := fun _ => ℤ) a 0 i) = F := by
        rw [Fin.sum_univ_castSucc]
        simp [hFa]
      have e₂ := eval_eq_of_eventually (Ψ (F.natDegree + 1)) (Ψ (r + 1)) (fun i => F.coeff i)
        (Fin.snoc (α := fun _ => ℤ) a 0) ((hA F).mono fun t ht => by
          have h₁ := hΨ _ ((fun i : Fin (F.natDegree + 1) => F.coeff i) + Pi.single (M := fun _ => ℤ) 0 (t : ℤ))
          have h₂ := hΨ _ (Fin.snoc (α := fun _ => ℤ) a 0 + Pi.single (M := fun _ => ℤ) 0 (t : ℤ))
          rw [sum_monomial_add_single, hF] at h₁
          rw [sum_monomial_add_single, e] at h₂
          exact hV _ _ _ (h₁ ht) (h₂ ht))
      refine e₂.trans ?_
      rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
      congr 2
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  · have := hΨ _ (fun i : Fin (F.natDegree + 1) => F.coeff i)
    rw [hF] at this
    exact this h

theorem relAmple_of_cls_eq {K : Type} [Field K] (P : Out.PolAV (Sp K)) {M N : LB P.A.left} (hM : M.IsLB) (hN : N.IsLB)
    (e : CechPic.cls M hM = CechPic.cls N hN) (h : Out.RelAmple P.A M) : Out.RelAmple P.A N := by
  haveI : IsProper P.A.hom := P.isAb.proper
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hM] at h
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hN]
  exact h.of_lbIso hN ((CechPic.cls_eq_iff hN hM).1 e.symm)

theorem exists_vol_poly : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → ∃ D : Polynomial ℤ → ℚ, (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous P.g ∧ ∀ a : Fin r → ℤ, D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) ∧ (∀ F, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) → Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) P.g ((D F : ℚ) : ℝ)) ∧ ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F + t)] P.L) ∧ IsFinite (ev (F + t)).left := by
  intro h₁ h₂ K _ _ P M s hM hs ev e₁ eadd eX
  obtain ⟨-, emul, hform, -, hdiv, hone, -⟩ := (_root_.GlobalTheory.formPoly_bundles h₁ h₂ K P M s hM hs).2 ev e₁ eadd eX
  have hB : ∀ F, (cubeLB P.A ![𝟙 P.A, ev F] P.L).IsLB := fun F => LB.isLB_linComb P.isLB _ _
  let b : Polynomial ℤ →+ CechPic.Pic P.A.left := AddMonoidHom.mk' (fun F => CechPic.cls _ (hB F)) fun F G => by
    have := (CechPic.cls_eq_iff (LB.isLB_div (hB _) (hB _)) (hB _)).2 (hdiv F G)
    rw [CechPic.cls_div (hB _) (hB _)] at this
    exact (sub_eq_iff_eq_add'.1 this)
  have hb : ∀ F, b F = CechPic.cls _ (hB F) := fun _ => rfl
  have hp : ∀ n, (lbPow P.L n).IsLB := fun n => LB.isLB_linComb P.isLB _ _
  have b₁ : b 1 = 2 • CechPic.cls _ P.isLB :=
    ((CechPic.cls_eq_iff (hB 1) (hp 2)).2 hone).trans (CechPic.cls_lbPow P.isLB 2 _)
  have hA : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F + t)] P.L) := fun F => by
    have h := _root_.GlobalTheory.AmpleDominates.eventually_sec_and_relAmple K P P.L _ P.isLB (hB (-F)) P.ample
    have ht : Filter.Tendsto (fun t : ℕ => t * 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun t => by show t ≤ t * 2; omega) Filter.tendsto_id
    refine (ht.eventually h).mono fun t h => relAmple_of_cls_eq P (LB.isLB_div (hp _) (hB _)) (hB _) ?_ h.2
    rw [CechPic.cls_div (hp _) (hB _), CechPic.cls_lbPow P.isLB, ← hb, ← hb, map_neg, map_add (f := _), ← nsmul_one t,
      map_nsmul, b₁, mul_smul, sub_neg_eq_add, add_comm]
  obtain ⟨D, hD, hD'⟩ := exists_poly_extension P.g (fun F => Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L))
    (fun F x => Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev F] P.L) P.g (x : ℝ))
    (fun F x y hx hy => by exact_mod_cast (_root_.GlobalTheory.VolBasic.vol_basic K P _ P.g (hB F)).2.1 _ _ hx hy)
    (fun r => by
      let φ : Fin r × ULift.{0} (Finset (Fin 2)) → (P.A.left ⟶ P.A.left) := fun p =>
        (psum P.A ![𝟙 P.A, ev (Polynomial.monomial (p.1 : ℕ) 1)] p.2.down).left
      obtain ⟨Φ, hΦ, hv⟩ := _root_.GlobalTheory.VolPoly.exists_vol_linComb_poly h₁ h₂ K P _ φ
      refine ⟨MvPolynomial.aeval (fun p : Fin r × ULift.{0} (Finset (Fin 2)) =>
        MvPolynomial.C ((-1 : ℚ) ^ (2 - p.2.down.card)) * MvPolynomial.X p.1) Φ, ?_, fun a ha => ?_⟩
      · simpa using hΦ.aeval (n := 1) (fun p : Fin r × ULift.{0} (Finset (Fin 2)) =>
          MvPolynomial.C ((-1 : ℚ) ^ (2 - p.2.down.card)) * MvPolynomial.X p.1)
          fun p => (MvPolynomial.isHomogeneous_X ℚ p.1).C_mul _
      · let ε : Fin r × ULift.{0} (Finset (Fin 2)) → ℤ := fun p => a p.1 * (-1) ^ (2 - p.2.down.card)
        have hC : (LB.LinComb P.L φ ε).IsLB := LB.isLB_linComb P.isLB _ _
        have e : CechPic.cls _ (hB (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i))) = CechPic.cls _ hC := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← hb, map_sum, CechPic.cls_linComb P.isLB, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => ?_
          have : Polynomial.monomial (i : ℕ) (a i) = a i • Polynomial.monomial (i : ℕ) (1 : ℤ) := by
            rw [Polynomial.smul_monomial, smul_eq_mul, _root_.mul_one]
          rw [this, map_zsmul, hb]
          refine (congrArg (a i • ·) (CechPic.cls_linComb P.isLB _ _ _)).trans ?_
          simp only [Finset.smul_sum, ε, φ, mul_smul]
        have := (_root_.GlobalTheory.VolBasic.vol_basic K P _ P.g hC).2.2.1 _ _ (hB _) ((CechPic.cls_eq_iff _ _).1 e.symm)
          (hv ε (relAmple_of_cls_eq P (hB _) hC e ha))
        convert this using 2
        rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
        congr 2
        funext p
        simp [ε, mul_comm])
    hA
  refine ⟨D, hD, hD', fun F => (hA F).mono fun t ht => ⟨ht, ?_⟩⟩
  have hf := (GlobalTheory.FormFinite.isFinite_and_surjective_of_formIs h₁ h₂ K P _ _ (hB _) ht (hform _)).1
  rw [mul_comm, emul, Over.comp_left] at hf
  haveI : IsProper P.A.hom := P.isAb.proper
  haveI : IsSeparated ((ev 2).left ≫ P.A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (ev 2).left := IsSeparated.of_comp _ P.A.hom
  exact IsFinite.of_comp _ (ev 2).left

end GlobalTheory.VolPoly

end
end

