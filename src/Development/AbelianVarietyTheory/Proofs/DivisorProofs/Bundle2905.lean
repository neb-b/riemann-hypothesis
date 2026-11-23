module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValuesDetOmegaDeltaLocalUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open Classical

namespace GlobalTheory.KeyValsPf

theorem smooth_bG : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g (KeyVals.bG G ξ).hom := by
  intro S G _ g R _ ξ h
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) (isGrpPullback_pullback G ξ).1 h

theorem semi_bG : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    IsSemiAbelian G → IsSemiAbelian (KeyVals.bG G ξ) := by
  intro S G _ R _ ξ h
  exact IsSemiAbelian.pullback ξ G h

theorem mem_abLocus_bG {S : Scheme.{0}} (G : Over S) {R : Type} [CommRing R] (ξ : Sp R ⟶ S) (q : Sp R)
    (h : ξ q ∈ abLocus G) : q ∈ abLocus (KeyVals.bG G ξ) := by
  intro K _ _ t ⟨z, hz⟩
  have := h K (t ≫ ξ) ⟨z, by rw [← hz]; rfl⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom ξ) t).paste_horiz (IsPullback.of_hasPullback G.hom ξ)
  have e := P.isoPullback_hom_snd
  show IsProper (pullback.snd (pullback.snd G.hom ξ) t)
  rw [← e]
  infer_instance

theorem mem_abLocus_of_bG {S : Scheme.{0}} (G : Over S) {R : Type} [CommRing R] (ξ : Sp R ⟶ S) [IsOpenImmersion ξ] (q : Sp R)
    (h : q ∈ abLocus (KeyVals.bG G ξ)) : ξ q ∈ abLocus G := by
  intro K _ _ t ⟨z, hz⟩
  have hr : Set.range t ⊆ Set.range ξ := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w z]
    exact ⟨q, hz.symm⟩
  obtain ⟨u, rfl⟩ : ∃ u : Sp K ⟶ Sp R, u ≫ ξ = t := ⟨IsOpenImmersion.lift ξ t hr, IsOpenImmersion.lift_fac _ _ _⟩
  have : IsProper (pullback.snd (pullback.snd G.hom ξ) u) := h K u ⟨z, ξ.isOpenEmbedding.injective hz⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom ξ) u).paste_horiz (IsPullback.of_hasPullback G.hom ξ)
  rw [← P.isoPullback_inv_snd]
  infer_instance

theorem abLocus_generic : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G], genericPoint S ∈ abLocus G →
    abLocus (KeyVals.bG G (KeyVals.genPt S)) = Set.univ := by
  intro S _ G _ h
  refine Set.eq_univ_of_forall fun q => mem_abLocus_bG G _ q ?_
  have hp : KeyVals.genPt S q ∈ Set.range (S.fromSpecStalk (genericPoint S)) := ⟨q, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  rwa [(hp.antisymm (genericPoint_specializes _)).eq]

theorem abLocus_affine : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] (W : S.Opens) (hW : IsAffineOpen W), (W : Set S).Nonempty →
    IsOpen (abLocus G) → genericPoint S ∈ abLocus G → IsOpen (abLocus (KeyVals.bG G hW.fromSpec)) ∧
      Set.range (spMap (algebraMap Γ(S, W) (FractionRing Γ(S, W)))).base ⊆ abLocus (KeyVals.bG G hW.fromSpec) := by
  intro S _ G _ W hW hne hop h
  haveI : Nonempty W := ⟨⟨hne.some, hne.some_mem⟩⟩
  have e : abLocus (KeyVals.bG G hW.fromSpec) = hW.fromSpec ⁻¹' abLocus G :=
    Set.ext fun q => ⟨mem_abLocus_of_bG (R := Γ(S, W)) G hW.fromSpec q, mem_abLocus_bG (R := Γ(S, W)) G hW.fromSpec q⟩
  have ho : IsOpen (hW.fromSpec ⁻¹' abLocus G) := hop.preimage hW.fromSpec.continuous
  rw [e]
  refine ⟨ho, ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨q, hq⟩ : genericPoint S ∈ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    exact ((genericPoint_spec S).mem_open_set_iff W.isOpen).2 ⟨hne.some, trivial, hne.some_mem⟩
  refine Specializes.mem_open (y := q) ?_ ho (show hW.fromSpec q ∈ abLocus G from hq ▸ h)
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  intro a ha
  have ha' : algebraMap Γ(S, W) (FractionRing Γ(S, W)) a ∈ (show PrimeSpectrum (FractionRing Γ(S, W)) from z).asIdeal := ha
  have hz : (show PrimeSpectrum (FractionRing Γ(S, W)) from z).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [hz, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at ha'
  exact ha' ▸ Ideal.zero_mem _

theorem exists_keyVal : ∀ κ : Rule, ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∀ (c : VB.Chart (LieVB.omega G) g) (i : δ.ι), genericPoint S ∈ c.U ⊓ δ.U i → ∃ v, KeyVals.IsKeyVal κ g L σ c i v := by
  intro κ S _ _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i hgen
  have hgab : genericPoint S ∈ abLocus G := by
    obtain ⟨p, hp⟩ := hne
    exact ((genericPoint_spec S).mem_open_set_iff hop).2 ⟨p, trivial, hp⟩
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.KeyValsSec.exists_locSec S G L δ σ i _ (KeyVals.genPt S) hδ (KeyVals.genPt_le _ hgen.2)
  obtain ⟨y, hy, hyb⟩ := _root_.GlobalTheory.KeyVals.DualBasis.exists_isDual S G g c _ (KeyVals.genPt S) hsa hsm (KeyVals.genPt_le _ hgen.1)
  have hab := abLocus_generic S G hgab
  obtain ⟨x, hxg, hx⟩ := GlobalTheory.KeyDatumAb.exists_keyOn (KeyVals.FF S) (KeyVals.FF S) (RingHom.id _)
    (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)) t g y hg (semi_bG S G _ _ hsa)
    (smooth_bG S G g _ _ hsm) (by rw [hab]; exact isOpen_univ) (_root_.GlobalTheory.KeyVals.isSymmetric_bL S G L _ _ hsym) (_root_.GlobalTheory.KeyValsPol.polOnAb_genPt S G L hop hgab hpol) hyb
    (_root_.GlobalTheory.KeyVals.nzFib_of_isLocSec S G L δ σ i _ _ t (KeyVals.genPt_le _ hgen.2) ht hnz) (by rw [hab]; exact Set.subset_univ _)
  exact ⟨_, t, y, x, hxg, ht, hy, hx, rfl⟩

theorem keyVal_unit : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∀ (c : VB.Chart (LieVB.omega G) g) (i : δ.ι) (v : KeyVals.FF S), KeyVals.IsKeyVal κ g L σ c i v → ∀ p ∈ c.U ⊓ δ.U i,
      ∃ (V : S.Opens) (_ : V ≤ c.U ⊓ δ.U i) (_ : p ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V,
        S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = v := by
  intro κ hH hF hL S _ _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i v hv p hp
  obtain ⟨t', y', x, hxg, ht', hy', hx, rfl⟩ := hv
  have hgab : genericPoint S ∈ abLocus G := by
    obtain ⟨p, hp⟩ := hne
    exact ((genericPoint_spec S).mem_open_set_iff hop).2 ⟨p, trivial, hp⟩
  obtain ⟨W, hW, hpW, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hp
  have hW : IsAffineOpen W := hW
  haveI : Nonempty W := ⟨⟨p, hpW⟩⟩
  obtain ⟨hic, hcz, hft⟩ := _root_.GlobalTheory.KeyVals.ring_of_isAffineOpen S s W hW ⟨p, hpW⟩ hN hs h0
  haveI : IsNoetherianRing Γ(S, W) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hr : ∀ U : S.Opens, W ≤ U → ⊤ ≤ hW.fromSpec ⁻¹ᵁ U := fun U h q _ =>
    h (show hW.fromSpec q ∈ (W : Set S) from hW.range_fromSpec ▸ ⟨q, rfl⟩)
  have hri := hr _ (hle.trans inf_le_right)
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.KeyValsSec.exists_locSec S G L δ σ i Γ(S, W) hW.fromSpec hδ hri
  obtain ⟨y, hy, hyb⟩ := _root_.GlobalTheory.KeyVals.DualBasis.exists_isDual S G g c Γ(S, W) hW.fromSpec hsa hsm (hr _ (hle.trans inf_le_left))
  obtain ⟨hopW, habW⟩ := abLocus_affine S G W hW ⟨p, hpW⟩ hop hgab
  have hsaW := semi_bG S G Γ(S, W) hW.fromSpec hsa
  have hsmW := smooth_bG S G g Γ(S, W) hW.fromSpec hsm
  have hsyW := _root_.GlobalTheory.KeyVals.isSymmetric_bL S G L Γ(S, W) hW.fromSpec hsym
  have hpoW := _root_.GlobalTheory.KeyVals.PolOpen.polOnAb_affine S G L W hW hop hpol
  have hnzW := _root_.GlobalTheory.KeyVals.nzFib_of_isLocSec S G L δ σ i Γ(S, W) hW.fromSpec t hri ht hnz
  obtain ⟨z, hzg, hz⟩ := GlobalTheory.KeyDatumAb.exists_keyOn Γ(S, W) (FractionRing Γ(S, W)) (algebraMap _ _)
    (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t g y hg hsaW hsmW hopW hsyW hpoW hyb hnzW habW
  subst hzg
  obtain ⟨u, hu⟩ := hL Γ(S, W) (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t z y hsaW hsmW hopW hsyW hpoW
    (_root_.GlobalTheory.KeyVals.unifAlong_affineOpen S G L W hW hsa hunif) hyb hnzW hz
  refine ⟨W, hle, hpW, u, fun h => ?_⟩
  let r : Γ(S, W) →+* KeyVals.FF S := (S.presheaf.germ W (genericPoint S) h).hom
  have hinj : Function.Injective r := germ_injective_of_isIntegral S (genericPoint S) h
  let e : FractionRing Γ(S, W) →+* KeyVals.FF S := IsFractionRing.lift hinj
  have he : (RingHom.id _).comp r = e.comp (algebraMap _ _) := RingHom.ext fun a => (IsFractionRing.lift_algebraMap hinj a).symm
  have hξ := KeyVals.spMap_germ_fromSpec W hW h
  have hx' := _root_.GlobalTheory.KeyValsTrans.keyOn_trans S G _ L δ σ i Γ(S, W) (KeyVals.FF S) (KeyVals.FF S) hW.fromSpec r (KeyVals.genPt S) (RingHom.id _)
    t y t' y' x hxg hξ hri ht ht' (_root_.GlobalTheory.KeyVals.Vec.dual_vec S G _ c Γ(S, W) (KeyVals.FF S) hW.fromSpec r (KeyVals.genPt S) y y' hξ hsa hsm hy hy') hx
  rw [he] at hx'
  have hpb := GlobalTheory.KeyEven.keyPB_of_keyOn_comp Γ(S, W) (FractionRing Γ(S, W)) (KeyVals.FF S) (algebraMap _ _) e
    (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t _ y z x rfl hxg hz hx'
  rw [hF _ _ e z x hpb, hu]
  exact (IsFractionRing.lift_algebraMap hinj _).symm

theorem keyVal_compat : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)]
    (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S) (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec),
    IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → δ.IsLB →
    ∀ (c c' : VB.Chart (LieVB.omega G) g) (i i' : δ.ι) (v v' : KeyVals.FF S)
      (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
      (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
      KeyVals.IsKeyVal κ g L σ c i v → KeyVals.IsKeyVal κ g L σ c' i' v' →
      v * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
        S.presheaf.germ _ (genericPoint S) h1
          ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * v' := by
  intro κ hH hF S _ _ G _ _ g L δ σ hsa hsm hδ c c' i i' v v' h1 h2 hv hv'
  obtain ⟨t, y, x, hg, ht, hy, hk, rfl⟩ := hv
  obtain ⟨t', y', x', hg', ht', hy', hk', rfl⟩ := hv'
  obtain ⟨M, hM, hdet⟩ := _root_.GlobalTheory.KeyVals.LieRel.lieRel S G g hsa hsm c c' h1 y y' hy hy'
  have hs := _root_.GlobalTheory.KeySecRel.locSec_eq_germ_mul S G L δ σ hδ i i' h2 t t' ht ht'
  have := GlobalTheory.KeyEven.keyValue_homog_of_fibres κ hH hF (KeyVals.FF S) (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)) t' t g y' y
    x' x hg' hg _ M hk' hk hs hM
  rw [← hdet, mul_comm]
  exact this

theorem keyVals : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  intro κ hH hF hL S _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  haveI : CharZero (KeyVals.FF S) :=
    charZero_of_injective_ringHom (f := (S.presheaf.germ ⊤ (genericPoint S) trivial).hom)
      (germ_injective_of_isIntegral S (U := ⊤) (genericPoint S) trivial)
  let f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S) := fun c i =>
    if h : ∃ v, KeyVals.IsKeyVal κ g L σ c i v then h.choose else 1
  have hf : ∀ c i, genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i → KeyVals.IsKeyVal κ g L σ c i (f c i) := by
    intro c i h
    have ex := exists_keyVal κ S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i h
    simp only [f, dif_pos ex]
    exact ex.choose_spec
  have hgen : ∀ U : S.Opens, (U : Set S).Nonempty → genericPoint S ∈ U := fun U ⟨p, hp⟩ =>
    ((genericPoint_spec S).mem_open_set_iff U.isOpen).2 ⟨p, trivial, hp⟩
  refine ⟨f, fun c i p hp => ?_, fun c c' i i' h1 h2 => ?_⟩
  · exact keyVal_unit κ hH hF hL S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i (f c i)
      (hf c i (hgen _ ⟨p, hp⟩)) p hp
  · exact keyVal_compat κ hH hF S G g L δ σ hsa hsm hδ c c' i i' (f c i) (f c' i') h1 h2
      (hf c i ⟨h1.1, h2.1⟩) (hf c' i' ⟨h1.2, h2.2⟩)

end GlobalTheory.KeyValsPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupClassicalTraitPeriodsBoundedBelowMaxId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.LamBound

theorem exists_not_dvd_le {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ y, y ≠ 0 → 0 < β y y) (m : ℕ) (hm : 2 ≤ m) :
    ∀ (k : ℕ) (x : X), (β x x).toNat = k → x ≠ 0 →
      ∃ x', x' ≠ 0 ∧ (¬ ∃ v, x' = m • v) ∧ β x' x' ≤ β x x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx
    by_cases hd : ∃ v, x = m • v
    · obtain ⟨v, rfl⟩ := hd
      have hv : v ≠ 0 := by rintro rfl; simp at hx
      have hvv := hβ v hv
      have e : β (m • v) (m • v) = (m : ℤ) * ((m : ℤ) * β v v) := by
        simp [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
      have h2 : 2 * β v v ≤ (m : ℤ) * β v v := mul_le_mul_of_nonneg_right hm' hvv.le
      have h3 : 2 * ((m : ℤ) * β v v) ≤ (m : ℤ) * ((m : ℤ) * β v v) :=
        mul_le_mul_of_nonneg_right hm' (by linarith)
      have hlt : β v v < β (m • v) (m • v) := by rw [e]; linarith
      obtain ⟨x', h1, h2, h3⟩ := ih (β v v).toNat (by omega) v rfl hv
      exact ⟨x', h1, h2, h3.trans hlt.le⟩
    · exact ⟨x, hx, hd, le_rfl⟩

theorem isE8_apply_zero_zero_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (h : IsE8 W) : 0 < W 0 0 := by
  have h1 := h.1.diag_pos (i := 0)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h1
  have : (0 : ℝ) < W 0 0 := by linarith
  exact_mod_cast this

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem beta_pos (T : Trait F) (x : T.D.toPre.X) (hx : x ≠ 0) : 0 < T.β x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem sc_pos {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero
  have h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (c.int _).1 hinv
    apply c.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold CTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem exists_shortest {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (a : X) :
    ∃ v : X, ∀ v0, q (a + N • v) ≤ q (a + N • v + N • v0) := by
  have hfin : {x | ¬ q a < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop (q a))
  obtain ⟨b, ⟨hb, v, rfl⟩, hmin⟩ := Set.exists_min_image ({x | ¬ q a < q x} ∩ Set.range fun v => a + N • v) q
    (hfin.inter_of_left _) ⟨a, lt_irrefl _, 0, by simp⟩
  refine ⟨v, fun v0 => ?_⟩
  by_cases h : q a < q (a + N • v + N • v0)
  · exact (not_lt.1 hb).trans h.le
  · exact hmin _ ⟨h, v + v0, by simp [add_assoc]⟩

theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) (ha : a ≠ 0) : 0 < q a := by
  by_contra h
  have h : q a ≤ 0 := not_lt.1 h
  have hfin : {x | ¬ (0 : ℝ) < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • a) (smul_left_injective ℤ ha) (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) h

theorem qW_single {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (x : X) :
    qW W β (Pi.single 0 x) = W 0 0 * β x x := by
  simp [qW, Fin.sum_univ_succ]

theorem lab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ ε yy, IsLab X₁ ε c yy := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ c
  obtain ⟨ε, hε, -⟩ := GlobalTheory.Poinc.exists_diagEnd_isMonHom g n F W _ X₁.ρ.P X₁.u X₁.sharp
  exact ⟨ε, GlobalTheory.Poinc.exists_isLab g n F W Z i X₁ hg hn ho hi hE hT hP ε hε p z₁ c⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ hz
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  have hdiv : X₁.M.HasDiv X₁.S.th :=
    hT X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.u X₁.sharp X₁.gen X₁.M X₁.π X₁.normal X₁.comp
  refine ⟨(W 0 0 : ℝ) / X₁.S.N, fun c x hx => ?_⟩
  obtain ⟨x', hx', hnd, hle⟩ :=
    exists_not_dvd_le c.T.β (beta_pos c.T) X₁.S.N X₁.S.N_ge _ x rfl hx
  obtain ⟨ε, yy, c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR, y₀, hat, u, l, j, hq, -⟩ :=
    lab g n F W Z i X₁ hg hn ho hi hE hT hP p z₁ c
  let S' := X₁.S.rechart c₀ hc R' fg frac hth hev
  have hdiv' : X₁.M.HasDiv S'.th := fun z => (hdiv z).imp fun k hk => (RatModel.div_mul_iff hc).2 hk
  have htests : S'.HasTests :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hU hL hL2 hUT X₁.o₁ X₁.Ω₁ S' ρ').1
  have hy : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ S'.R a)‖ ≤ 1 := fun a => by
    rw [hat]
    exact RatModel.norm_val_le_one c.cen ((X₁.M.O z₁).algebraMap_mem a)
  obtain ⟨τ, e, hτ, -⟩ := exists_test_match X₁.o₁ X₁.Ω₁ S' ρ' p y₀ u l
    (_root_.GlobalTheory.ZH.TestVal.main hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (_root_.GlobalTheory.UnitTheta.closure_unit_theta hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
    (_root_.GlobalTheory.ZH.WeightBound.main hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (_root_.GlobalTheory.TestFibre.exists_norm_FF_eq hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
  let α₀ : τ.X := e.symm (j.symm (Pi.single 0 x'))
  obtain ⟨v, hv⟩ := exists_shortest τ.q τ.pos X₁.S.N α₀
  have hne : α₀ + X₁.S.N • v ≠ 0 := fun h0 => hnd ⟨-(j (e v) 0), by
    have h1 := congrFun (congrArg (fun t => j (e t)) h0) 0
    simp only [α₀, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, map_zero, Pi.add_apply, Pi.single_eq_same,
      Pi.smul_apply, Pi.zero_apply] at h1
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h1⟩
  have hqle : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x' x') := by
    have h1 := hv (-v)
    rw [smul_neg, add_neg_cancel_right] at h1
    refine h1.trans_eq ?_
    rw [hτ, hq]
    simp only [α₀, AddEquiv.apply_symm_apply, qW_single]
    push_cast
    ring
  obtain ⟨h, hm, hh⟩ := GlobalTheory.exists_mem_maximalIdeal_exp_le_norm_val X₁.o₁ X₁.Ω₁ S' X₁.M X₁.normal hdiv' htests z₁ hz p
    c.y y₀ c.cen (fun a ha => hR ha) hat τ _ hv (pos_of_tendsto τ.q τ.pos _ hne)
  refine ⟨h, hm, le_trans (Real.exp_le_exp.2 ?_) hh⟩
  have hsc := sc_pos c
  have hW : (0 : ℝ) ≤ W 0 0 := by exact_mod_cast (isE8_apply_zero_zero_pos hE).le
  have hNpos : (0 : ℝ) < X₁.S.N := by
    have := X₁.S.N_ge
    exact_mod_cast (by omega : 0 < X₁.S.N)
  have hb : (c.T.β x' x' : ℝ) ≤ c.T.β x x := by exact_mod_cast hle
  have h1 : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x x) :=
    hqle.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hsc.le) hW)
  rw [neg_le_neg_iff, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h1 hNpos.le

end GlobalTheory.Poinc.LamBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningEqOfGenericSectionRatios
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem fstG_comm_thick (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) (g : G ⟶ G) :
    ((Over.pullback (thick R I e)).map g).left ≫ (fstG I e G).left = (fstG I e G).left ≫ g.left := by
  first
    | (have := congrArg CommaMorphism.left ((Over.mapPullbackAdj (thick R I e)).counit.naturality g)
       simpa [fstG] using this)
    | (simp [fstG]; exact pullback.lift_fst _ _ _)

theorem thick_eq_of_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) → ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g = φ → ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb N S hS hC φ hφ g hg hgφ e
  have hcomm : φ.left ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ g.left := by
    subst hgφ
    first
      | (simp; done)
      | (simp; exact pullback.lift_fst _ _ _)
      | exact pullback.lift_fst _ _ _
  have hGI : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_isSemiAbelian G (h := hG)
  have hfin : Finite (irreducibleComponents (Sp R)) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hfl : Flat G.hom := by
    obtain ⟨_, hsm, -, -, -, -⟩ := hG
    infer_instance
  have hred : IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents G.hom
  have hdom : IsDominant (pullback.fst G.hom (jK R)) :=
    isDominant_genericFibre_of_flat R (FractionRing R) G.hom

  have hGrat : ∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k),
      SecRatioEq U.LG.L g.left (𝟙 G.left) s₁ s₂ (S k s₁) (S k s₂) := by
    intro k s₁ s₂
    apply SecRatioEq.of_isDominant (pullback.fst G.hom (jK R))
    rw [← hcomm, Category.comp_id]
    exact hφ k s₁ s₂

  have hxc : ((Over.pullback (thick R (maximalIdeal R) e)).map g).left ≫ (fstG (maximalIdeal R) e G).left =
      (fstG (maximalIdeal R) e G).left ≫ g.left := fstG_comm_thick R (maximalIdeal R) e G g
  have hxrat : ∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k),
      SecRatioEq U.LG.L (((Over.pullback (thick R (maximalIdeal R) e)).map g).left ≫ (fstG (maximalIdeal R) e G).left)
        (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂) := by
    intro k s₁ s₂
    have := secRatioEq_comp U.LG.L g.left (𝟙 G.left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)
      (hGrat k s₁ s₂)
    rwa [Category.comp_id, ← hxc] at this
  have hxmon : IsMonHom ((Over.pullback (thick R (maximalIdeal R) e)).map g) := inferInstance
  obtain ⟨k₀, hk₀, hnear⟩ := _root_.GlobalTheory.Mum.agree_near_of_ratios R hB D A G hG U
  obtain ⟨s₀, hs₀⟩ := hC k₀ hk₀

  obtain ⟨y, i'', i', hy1, hy2⟩ :=
    formalEnd_secCoNonzero_lift R hB D A G hG U a h' b hb k₀ (N * k₀) s₀ (S k₀ s₀) hs₀ e
  obtain ⟨i, hy0⟩ := _root_.GlobalTheory.Mum.mem_basicOpen_of_secRatioEq R hB D A G hG U e k₀ (N * k₀) hk₀
    ((Over.pullback (thick R (maximalIdeal R) e)).map g) (S k₀) (hxrat k₀) y s₀ i' hy2
  obtain ⟨W, hyW, hW⟩ := hnear e k₀ (N * k₀) le_rfl ((Over.pullback (thick R (maximalIdeal R) e)).map g) (b e)
    (S k₀) (hxrat k₀) (fun s₁ s₂ => hS k₀ e s₁ s₂) y s₀ i i' i'' hy0 hy2 hy1
  exact _root_.GlobalTheory.MumAgree.eq_of_eq_on_open R hB D A G hG U e _ (b e) hxmon (hb.1 e) W y hyW hW

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDataTranslateOrderTwoIsTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem isTwist_of_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g := by
  intro R _ _ _ hB D A G _ _ hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨β, hβm, hβq⟩ := _root_.GlobalTheory.MumCmp.abelianPart_iso_of_twoUnif R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨xe, hxe⟩ := GlobalTheory.unifPre_characterGroup_iso R (maximalIdeal R) hB.1 D D₂ A A₂ G hG U.toUnifPre U₂.toUnifPre
  obtain ⟨w, hw, h0⟩ := _root_.GlobalTheory.MumCmp.exists_iso_twist_of_translate R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq
  have hc := _root_.GlobalTheory.MumCmp.TranslC.c_correspond R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe w hw
  exact ⟨β, xe, hβm, hc, w, hw,
    _root_.GlobalTheory.MumCmp.psi_twist R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw h0⟩

end GlobalTheory.MumCmp
end

