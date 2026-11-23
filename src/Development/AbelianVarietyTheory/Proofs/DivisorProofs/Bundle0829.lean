module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab
section
namespace GlobalTheory.HeckeDual

section Group

open MeasureTheory

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem exists_rep (K : Subgroup H) (ho : IsOpen (K : Set H)) (hc : IsCompact (K : Set H)) (b : H) :
    ∃ R : Finset H, (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * b * k₂) ∧
      ∀ x : H, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * b * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  classical
  haveI : DiscreteTopology (H ⧸ K) := QuotientGroup.discreteTopology ho
  have hf : ((fun k : H => ((k * b : H) : H ⧸ K)) '' (K : Set H)).Finite :=
    (hc.image (QuotientGroup.continuous_mk.comp (continuous_mul_const b))).finite_of_discrete
  refine ⟨hf.toFinset.image Quotient.out, fun γ hγ => ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨k, hk, rfl⟩ := hf.mem_toFinset.1 hq
    obtain ⟨k', hk'⟩ := QuotientGroup.mk_out_eq_mul K (k * b)
    exact ⟨k, hk, k', k'.2, hk'⟩
  · rintro x ⟨k₁, h₁, k₂, h₂, rfl⟩
    have e : ((k₁ * b : H) : H ⧸ K) = ((k₁ * b * k₂ : H) : H ⧸ K) := (QuotientGroup.mk_mul_of_mem _ h₂).symm
    refine ⟨((k₁ * b : H) : H ⧸ K).out, ⟨Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ⟨k₁, h₁, rfl⟩), ?_⟩, ?_⟩
    · rw [← QuotientGroup.eq, QuotientGroup.out_eq', e]
    · rintro γ ⟨hγ, h⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
      rw [← QuotientGroup.eq, QuotientGroup.out_eq'] at h
      rw [h, e]

theorem exists_rep_inv [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hmod : ∀ h : H, Measure.modularCharacter h = 1) {G : Type} [Group G] (ι : H →* G) (hι : Function.Injective ι)
    (K : Subgroup H) (ho : IsOpen (K : Set H)) (hc : IsCompact (K : Set H)) (KS : Set G)
    (hK : ∀ g, g ∈ KS ↔ ∃ k ∈ K, ι k = g) (a : H) (R : Finset G)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ KS, ∃ k₂ ∈ KS, γ = k₁ * ι a * k₂)
    (h2 : ∀ x : G, (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * ι a * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ KS) :
    ∃ R' : Finset G, (∀ γ ∈ R', γ ∈ ι.range ∧ ∃ k₁ ∈ KS, ∃ k₂ ∈ KS, γ = k₁ * (ι a)⁻¹ * k₂) ∧
      (∀ x : G, (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * (ι a)⁻¹ * k₂) → ∃! γ, γ ∈ R' ∧ γ⁻¹ * x ∈ KS) ∧
      R'.card = R.card := by
  classical
  have hK' : ∀ k, ι k ∈ KS ↔ k ∈ K := fun k =>
    (hK _).trans ⟨fun ⟨k', h, e⟩ => hι e ▸ h, fun h => ⟨k, h, rfl⟩⟩
  have hdc : ∀ (b : H) (x : G), (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * ι b * k₂) ↔
      ∃ y, ι y = x ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * b * k₂ := fun b x => by
    constructor
    · rintro ⟨k₁, h₁, k₂, h₂, rfl⟩
      obtain ⟨l₁, g₁, rfl⟩ := (hK _).1 h₁
      obtain ⟨l₂, g₂, rfl⟩ := (hK _).1 h₂
      exact ⟨_, by rw [map_mul, map_mul], l₁, g₁, l₂, g₂, rfl⟩
    · rintro ⟨_, rfl, k₁, h₁, k₂, h₂, rfl⟩
      exact ⟨_, (hK' _).2 h₁, _, (hK' _).2 h₂, by rw [map_mul, map_mul]⟩
  obtain ⟨R', h3, h4⟩ := exists_rep K ho hc a⁻¹
  let μ : Measure H := Measure.haar
  haveI : μ.IsMulRightInvariant := ⟨fun g => by
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq, hmod, one_smul]⟩
  have hcard := GlobalTheory.card_leftCosets_doubleCoset_inv_eq μ K a (R.preimage ι hι.injOn) R' ho.measurableSet
    (ho.measure_pos μ ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne (fun γ hγ => by
      obtain ⟨y, e, h⟩ := (hdc _ _).1 (h1 _ (Finset.mem_preimage.1 hγ))
      exact hι e ▸ h) (fun x hx => by
      obtain ⟨γ, ⟨hγ, h⟩, hu⟩ := h2 (ι x) ((hdc _ _).2 ⟨x, rfl, hx⟩)
      obtain ⟨y, rfl, -⟩ := (hdc _ _).1 (h1 _ hγ)
      refine ⟨y, ⟨Finset.mem_preimage.2 hγ, (hK' _).1 (by rwa [map_mul, map_inv])⟩, fun z hz => hι (hu _
        ⟨Finset.mem_preimage.1 hz.1, ?_⟩)⟩
      rw [← map_inv, ← map_mul]
      exact (hK' _).2 hz.2) h3 h4
  rw [← map_inv]
  refine ⟨R'.image ι, fun γ hγ => ?_, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨⟨y, rfl⟩, (hdc _ _).2 ⟨y, rfl, h3 y hy⟩⟩
  · obtain ⟨y, rfl, hy⟩ := (hdc _ _).1 hx
    obtain ⟨γ, ⟨hγ, h⟩, hu⟩ := h4 y hy
    refine ⟨ι γ, ⟨Finset.mem_image_of_mem _ hγ, ?_⟩, ?_⟩
    · rw [← map_inv, ← map_mul]
      exact (hK' _).2 h
    · rintro z ⟨hz, h'⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
      rw [hu w ⟨hw, (hK' _).1 (by rwa [map_mul, map_inv])⟩]
  · rw [Finset.card_image_of_injective _ hι, ← hcard, Finset.card_preimage, Finset.filter_true_of_mem]
    intro γ hγ
    obtain ⟨y, e, -⟩ := (hdc _ _).1 (h1 _ hγ)
    exact ⟨y, e⟩

end Group

section Local

open scoped TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.AdelicUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem modular_eq_one (hσ : ∀ x, σ (σ x) = x) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (hJ : IsHermND σ J)
    (v : HeightOneSpectrum (𝓞 F)) (g : GLoc σ J v) : Measure.modularCharacter g = 1 := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  letI : Algebra ℚ (Fv F v ⊗[F] E) := ((inclR (F := F) (Fv F v)).comp (algebraMap ℚ E)).toAlgebra
  obtain ⟨M, hM⟩ := exists_framed (σ := (σ : E →+* E)) hσ (J := J) (by ext i j; exact hJ.1 i j) hJ.2
  have hF : Framed (sigR (Fv F v) σ) (JR (Fv F v) J) (M.map (inclR (Fv F v))) := hM.map fun x => rfl
  have hss : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  obtain ⟨T, hTc, hT, hT'⟩ := exists_involution (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Fv F v) σ) hss hF
  have hgen : Generic (sigR (Fv F v) σ) :=
    generic_of_semilocal (δ := inclR (Fv F v) δ) (hδ.isUnit.map _) (by
      rw [← map_neg, ← hσδ]; rfl)
  have key : ∀ T : GLoc σ J v →* GLoc σ J v, Continuous T → (∀ x, T (T x) = x) → ∀ x,
      Measure.modularCharacter (T x) = Measure.modularCharacter x := fun T => modular_involution T
  exact char_eq_one hss hF hgen (Measure.modularCharacter (G := GLoc σ J v)) (fun x x' h => by
    rw [hT' x x' h]
    exact key T hTc hT x) g

end Local

section Host

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem idem_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    e * e = e ∧ ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v f := by
  rcases h with ⟨⟨⟨he, -, v, ε, ⟨α, rfl, h1, h2⟩, hf⟩, -⟩, rfl⟩ | ⟨rfl, ⟨v, ε, ⟨α, rfl, h1, h2⟩, rfl⟩, -⟩
  · exact ⟨he, v, hf ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2⟩
  · have h := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) h1 h2
    exact ⟨(GlobalTheory.SuppLocal.idem_mul_iff h _).2 ⟨h.1, h.2.2⟩, v, h⟩

theorem suppF_iff (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D}
    (hf : GlobalTheory.PlaceComp.IsIdemOf D.host.E v f) (g : GA D V) :
    SuppF V f g ↔ g ∈ (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v).range := by
  have h1 : ∀ w (g : GA D V), GlobalTheory.PlaceComp.locMat D.sp.cm V w g = 1 ↔
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram w g = 1 := fun w g => by
    rw [← GlobalTheory.AdelicU.projFinLoc_projFin]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg (HA.mat _ _ _) h⟩
  refine (GlobalTheory.SuppLocal.supp_iff D.sp.cm V hf g).trans ?_
  simp only [h1]
  constructor
  · rintro ⟨h2, h3⟩
    refine ⟨GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g, GlobalTheory.AdelicU.GAd_ext _ _ (fun w => ?_) fun u => ?_⟩
    · rw [GlobalTheory.AdelicU.projArch_emb, GlobalTheory.AdelicU.mem_finPts_iff_forall.1 h2 w]
    · by_cases e : u = v
      · rw [e, GlobalTheory.AdelicU.proj_emb_self]
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e, h3 u e]
  · rintro ⟨x, rfl⟩
    exact ⟨GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x), fun w hw => GlobalTheory.AdelicU.proj_emb_ne _ _ hw x⟩

theorem exists_skew (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  by_contra! h
  have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun a => (D.sp.cm.fixed a).1 (by
    by_contra hne
    exact h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))
  have := (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
    ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq
  rw [D.sp.cm.deg2, Module.finrank_self] at this
  omega

theorem isLattice_frameLat (V : HSp D) : Submodule.IsLattice D.host.E (GlobalTheory.AdelicU.frameLat V) := by
  exact Submodule.IsLattice.of_fg D.host.E (GlobalTheory.AdelicU.frameLat_fg V)

end Host

end GlobalTheory.HeckeDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIso
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem gm_eq_map_stalk {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U h, Units.coe_map, gm_val _ (f y) U h, ← Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem isoOn_of_lbIso (X : Scheme.{0}) (W : X.Opens) (L M : LB X) (h : LBIso (L.pull W.ι) (M.pull W.ι)) :
    ∃ w : Cmp W L M, IsoOn W L M w := by
  obtain ⟨s, hs⟩ := h
  have hle : ∀ (a : L.ι) (b : M.ι), W ⊓ (L.U a ⊓ M.U b) ≤
      W.ι ''ᵁ ((M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a)) := by
    intro a b x hx
    obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx.1⟩, rfl⟩
    exact W.ι.apply_mem_image_iff.2 ⟨mem_pull.2 hx.2.2, mem_pull.2 hx.2.1⟩
  refine ⟨fun a b => (res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹, ?_⟩
  intro x hx a a' b b' ha ha' hb hb'
  obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have E : ∀ (a : L.ι) (b : M.ι), W.ι y ∈ L.U a → W.ι y ∈ M.U b →
      gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) =
      (gm (𝟙 _) y _ (s.s (fun _ => b, fun _ => a)))⁻¹ := by
    intro a b ha hb
    have hm : W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) := ⟨hx, ha, hb⟩
    have hv : (𝟙 W.toScheme) y ∈ (M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a) :=
      ⟨mem_pull.2 hb, mem_pull.2 ha⟩
    have e := GlobalTheory.GlueLineBundle.gm_imU W.ι (𝟙 _) y _ hv (s.s (fun _ => b, fun _ => a))
    rw [Category.id_comp] at e
    rw [map_inv, gm_res W.ι y (hle a b) hm, e]
    rfl
  have EL : ∀ (a a' : L.ι), W.ι y ∈ L.U a → W.ι y ∈ L.U a' →
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') = gm (𝟙 _) y _ ((L.pull W.ι).g (fun _ => a) (fun _ => a')) := by
    intro a a' ha ha'
    have e := gm_pull_g L W.ι (𝟙 _) y (fun _ => a) (fun _ => a') (mem_pull.2 ha) (mem_pull.2 ha')
    rw [Category.id_comp] at e
    exact e.symm
  have EM : ∀ (b b' : M.ι), W.ι y ∈ M.U b → W.ι y ∈ M.U b' →
      gm W.ι y (M.U b ⊓ M.U b') (M.g b b') = gm (𝟙 _) y _ ((M.pull W.ι).g (fun _ => b) (fun _ => b')) := by
    intro b b' hb hb'
    have e := gm_pull_g M W.ι (𝟙 _) y (fun _ => b) (fun _ => b') (mem_pull.2 hb) (mem_pull.2 hb')
    rw [Category.id_comp] at e
    exact e.symm
  have hp : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b, fun _ => a) := ⟨mem_pull.2 hb, mem_pull.2 ha⟩
  have hq : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b', fun _ => a') := ⟨mem_pull.2 hb', mem_pull.2 ha'⟩
  have G := (isGen_iff_germ s).1 hs y _ _ hp hq
  rw [gm_div' (M.pull W.ι) (L.pull W.ι) (𝟙 _) y _ _ hp hq] at G
  have alg : ∀ {Gp : Type} [CommGroup Gp] (S Mg large₂ S' : Gp), S = Mg * large₂⁻¹ * S' → S⁻¹ * Mg = large₂ * S'⁻¹ := by
    intro Gp _ S Mg large₂ S' e
    rw [e, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
    exact _root_.mul_comm _ _
  have key : gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) *
        gm W.ι y (M.U b ⊓ M.U b') (M.g b b') =
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') * gm W.ι y (W ⊓ (L.U a' ⊓ M.U b'))
        ((res (hle a' b') (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b', fun _ => a'))))⁻¹) := by
    rw [E a b ha hb, E a' b' ha' hb', EL a a' ha ha', EM b b' hb hb']
    exact alg _ _ _ _ G
  have hinj : Function.Injective (Units.map (W.ι.stalkMap y).hom.toMonoidHom) := fun u v e =>
    Units.ext ((ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1 (congrArg Units.val e))
  apply hinj
  rw [map_mul, map_mul, ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) from ⟨hx, ha, hb⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ M.U b ⊓ M.U b' from ⟨hb, hb'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ L.U a ⊓ L.U a' from ⟨ha, ha'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a' ⊓ M.U b') from ⟨hx, ha', hb'⟩)]
  exact key

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPrimeMultOfFiresAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.ThetaFiresLinear

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {G' H' S' Sinf TK Tau : Type} [MeasurableSpace H'] [AddCommGroup S'] [Module ℂ S'] [AddCommGroup Sinf] [Module ℂ Sinf]
  [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]

theorem exists_isThetaP (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' →ₗ[ℂ] ℂ) (pt : Sinf →ₗ[ℂ] S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 (fun g h s => th g h s) (fun s => pt s) io A thP := by
  refine ⟨LinearMap.mk₂ ℂ (fun f e g => ∫ h in 𝓕, th g h (pt (io e ((f : H' → Tau) h))) ∂ν) ?_ ?_ ?_ ?_, hint,
    fun f e g => rfl⟩
  · intro f f' e
    funext g
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
    exact integral_add (hint f e g) (hint f' e g)
  · intro c f e
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul]
    exact integral_smul c _
  · intro f e e'
    funext g
    simp only [Pi.add_apply, map_add (f := _), LinearMap.add_apply]
    exact integral_add (hint f e g) (hint f e' g)
  · intro c f e
    funext g
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply]
    exact integral_smul c _

theorem exists_isThetaP' (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf → S')
    (thL : G' → H' → S' →ₗ[ℂ] ℂ) (ptL : Sinf →ₗ[ℂ] S') (h1 : ∀ g h s, th g h s = thL g h s) (h2 : ∀ s, pt s = ptL s)
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 th pt io A thP := by
  obtain rfl : th = fun g h s => thL g h s := funext fun g => funext fun h => funext fun s => h1 g h s
  obtain rfl : pt = fun s => ptL s := funext h2
  exact exists_isThetaP ν 𝓕 thL ptL io A hint

theorem exists_linear_choice {X M N : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (W : Submodule ℂ M) (r : M →ₗ[ℂ] N) (u : X →ₗ[ℂ] N)
    (h : ∀ x, ∃ m ∈ W, r m = u x) : ∃ y : X →ₗ[ℂ] M, (∀ x, y x ∈ W) ∧ ∀ x, r (y x) = u x := by
  choose m hm hr using h
  let b := Module.Basis.ofVectorSpace ℂ X
  let y' : X →ₗ[ℂ] W := b.constr ℂ fun k => ⟨m (b k), hm _⟩
  refine ⟨W.subtype ∘ₗ y', fun x => (y' x).2, fun x => ?_⟩
  have : r ∘ₗ W.subtype ∘ₗ y' = u := b.ext fun k => by
    simp only [LinearMap.comp_apply, y', Module.Basis.constr_basis, Submodule.subtype_apply, hr]
  exact LinearMap.congr_fun this x

theorem exists_linear_lift {ι X : Type} [AddCommGroup X] [Module ℂ X] {M : ι → Type} [∀ a, AddCommGroup (M a)]
    [∀ a, Module ℂ (M a)] (low : ∀ a, Submodule ℂ (M a)) (W : Submodule ℂ ((∀ a, M a) →ₘₗ[ℂ] (G' → ℂ)))
    (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf → S')
    (thL : G' → H' → S' →ₗ[ℂ] ℂ) (ptL : Sinf →ₗ[ℂ] S') (h1 : ∀ g h s, th g h s = thL g h s) (h2 : ∀ s, pt s = ptL s)
    (io : (⨂[ℂ] a, low a) →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (ext : X →ₗ[ℂ] (H' → Tau))
    (h : ∀ x, (∀ e g, IntegrableOn (fun h => th g h (pt (io e (ext x h)))) 𝓕 ν) ∧
      ∃ U ∈ W, ∀ v : ∀ a, low a, U (fun a => (v a : M a)) = Lift.thetaPInt ν 𝓕 th pt io (ext x) (PiTensorProduct.tprod ℂ v)) :
    ∃ y : X →ₗ[ℂ] ((∀ a, M a) →ₘₗ[ℂ] (G' → ℂ)), (∀ x, y x ∈ W) ∧
      ∃ thP : LinearMap.range ext →ₗ[ℂ] ((⨂[ℂ] a, low a) →ₗ[ℂ] (G' → ℂ)),
        Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range ext) thP ∧
          ∀ (x : X) (v : ∀ a, low a), y x (fun a => (v a : M a)) = thP (ext.rangeRestrict x) (PiTensorProduct.tprod ℂ v) := by
  obtain ⟨thP, hP⟩ := exists_isThetaP' ν 𝓕 th pt thL ptL h1 h2 io (LinearMap.range ext) (by
    rintro ⟨_, x, rfl⟩ e g
    exact (h x).1 e g)
  let r : ((∀ a, M a) →ₘₗ[ℂ] (G' → ℂ)) →ₗ[ℂ] ((∀ a, low a) → G' → ℂ) :=
    { toFun := fun U v => U fun a => (v a : M a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : ((⨂[ℂ] a, low a) →ₗ[ℂ] (G' → ℂ)) →ₗ[ℂ] ((∀ a, low a) → G' → ℂ) :=
    { toFun := fun U v => U (PiTensorProduct.tprod ℂ v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨y, hy, hr⟩ := exists_linear_choice W r (p ∘ₗ thP ∘ₗ ext.rangeRestrict) fun x => by
    obtain ⟨U, hU, hv⟩ := (h x).2
    exact ⟨U, hU, funext fun v => funext fun g =>
      (congrFun (hv v) g).trans (hP.eq (ext.rangeRestrict x) (PiTensorProduct.tprod ℂ v) g).symm⟩
  exact ⟨y, hy, thP, hP, fun x v => congrFun (hr x) v⟩

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernelL (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : WO (Vc D i) (Wc D i) => ℂ) 0 ∘ₗ R.ωP i t (h, g)

end GlobalTheory.ThetaFiresLinear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetract
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

theorem germ_pull_eq_stalkMap {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val f y U h, gm_val (𝟙 X) (f y) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f U y h _).symm

theorem retract_section_apply {X Y : Scheme.{0}} (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (y : Y) : p (e y) = y := by
  have := congrArg (fun f : Y ⟶ Y ↦ f y) hep
  simpa using this

theorem norm_glue_comm {G : Type} [CommGroup G] (A B F G' R R' : G) (k : A * G' = F * B) :
    A * (G' * R') * (F * R)⁻¹ = B * R' * R⁻¹ := by
  rw [← _root_.mul_assoc, k, mul_inv]
  simp only [_root_.mul_assoc]
  rw [mul_left_comm F, mul_left_comm F, mul_inv_cancel_left]

theorem norm_match_comm {G : Type} [CommGroup G] (A S R R' : G) (h : S = A * R' * R⁻¹) :
    A * S⁻¹ * R' = R := by
  rw [h]; simp only [mul_inv]; simp [mul_comm, mul_left_comm, _root_.mul_assoc]

theorem exists_norm (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (V : Y.Opens)
    (W₁ W₂ : X.Opens) (L M : LB X) (w : Cmp (p ⁻¹ᵁ V) L M) (r : RigD e L) (r' : RigD e M)
    (hL : IsOn W₁ L) (hM : IsOn W₂ M) (h₁ : p ⁻¹ᵁ V ≤ W₁) (h₂ : p ⁻¹ᵁ V ≤ W₂)
    (hw : IsoOn (p ⁻¹ᵁ V) L M w) (hr : RigOn e L r) (hr' : RigOn e M r') :
    ∃ w' : Cmp (p ⁻¹ᵁ V) L M, IsoOn (p ⁻¹ᵁ V) L M w' ∧ Norm e (p ⁻¹ᵁ V) L M w' r r' := by
  have hpt := retract_section_apply p e hep
  let O : L.ι × M.ι → Y.Opens := fun i ↦ e ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2))
  have hOV : ∀ i, O i ≤ V := fun i y hy ↦ by
    have : p (e y) ∈ V := hy.1
    rwa [hpt] at this
  have hOa : ∀ i, O i ≤ e ⁻¹ᵁ L.U i.1 := fun i y hy ↦ hy.2.1
  have hOb : ∀ i, O i ≤ e ⁻¹ᵁ M.U i.2 := fun i y hy ↦ hy.2.2
  have hcov : V ≤ iSup O := fun y hy ↦ by
    have hx : e y ∈ p ⁻¹ᵁ V := show p (e y) ∈ V by rwa [hpt]
    obtain ⟨a, ha⟩ := hL.cov _ (h₁ hx)
    obtain ⟨b, hb⟩ := hM.cov _ (h₂ hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), ⟨hx, ha, hb⟩⟩
  let u : ∀ i, Γ(Y, O i)ˣ := fun i ↦
    pullU e _ (w i.1 i.2) * res (hOb i) (r' i.2) * (res (hOa i) (r i.1))⁻¹
  have hu : ∀ i, ∀ y ∈ O i, gm (𝟙 Y) y (O i) (u i) =
      gm e y _ (w i.1 i.2) * gm (𝟙 Y) y _ (r' i.2) * (gm (𝟙 Y) y _ (r i.1))⁻¹ := by
    intro i y hy
    simp only [u, map_mul, map_inv]
    rw [gm_res (𝟙 Y) y (hOb i) hy, gm_res (𝟙 Y) y (hOa i) hy, gm_pull (𝟙 Y) e y _ hy, Category.id_comp]
  obtain ⟨s, hs⟩ := glue_unit V O hOV hcov u (by
    intro i j y hy
    rw [hu i y hy.1, hu j y hy.2]
    obtain ⟨⟨hV, ha, hb⟩, -, ha', hb'⟩ := hy
    have k := congrArg (Units.map (e.stalkMap y).hom.toMonoidHom) (hw (e y) hV i.1 j.1 i.2 j.2 ha ha' hb hb')
    simp only [map_mul, ← germ_pull_eq_stalkMap] at k
    rw [← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2)) ⟨hV, ha, hb⟩,
      ← germ_pull_eq_stalkMap e y (M.U i.2 ⊓ M.U j.2) ⟨hb, hb'⟩,
      ← germ_pull_eq_stalkMap e y (L.U i.1 ⊓ L.U j.1) ⟨ha, ha'⟩,
      ← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U j.1 ⊓ M.U j.2)) ⟨hV, ha', hb'⟩] at k
    rw [hr y i.1 j.1 ha ha', hr' y i.2 j.2 hb hb']
    exact norm_glue_comm _ _ _ _ _ _ k)
  have hle : ∀ (a : L.ι) (b : M.ι), p ⁻¹ᵁ V ⊓ (L.U a ⊓ M.U b) ≤ p ⁻¹ᵁ V := fun _ _ ↦ inf_le_left
  refine ⟨fun a b ↦ w a b * (res (hle a b) (pullU p V s))⁻¹, ?_, ?_⟩
  · intro x hx a a' b b' ha ha' hb hb'
    simp only [map_mul, map_inv]
    rw [gm_res (𝟙 X) x (hle a b) ⟨hx, ha, hb⟩, gm_res (𝟙 X) x (hle a' b') ⟨hx, ha', hb'⟩]
    have k := hw x hx a a' b b' ha ha' hb hb'
    rw [mul_right_comm, k, _root_.mul_assoc]
  · intro y a b hV ha hb
    simp only [map_mul, map_inv]
    have hy : y ∈ O (a, b) := ⟨hV, ha, hb⟩
    rw [gm_res e y (hle a b) ⟨hV, ha, hb⟩, gm_pull e p y V hV, hep, ← gm_res (𝟙 Y) y (hOV (a, b)) hy, hs,
      hu (a, b) y hy]
    exact norm_match_comm _ _ _ _ rfl

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCutInductionStepOfOpenSubgroupStatement
section
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_whittakerCut_inductionStep_of_open_subgroup : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ U : Subgroup (GL (Fin (m + 1)) F), IsCompact (U : Set (GL (Fin (m + 1)) F)) → IsOpen (U : Set (GL (Fin (m + 1)) F)) → ∀ z : GL (Fin (m + 1)) F, ∃ U₁ : Subgroup (GL (Fin (m + 1)) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin (m + 1)) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 1)) F))) {g | ∃ p : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1 ∧ ∃ u ∈ U₁, g = p * u}) → ∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h := by
  first
  | exact @GlobalTheory.JSW.Cut.exists_cut_cor_of_sub
  | exact GlobalTheory.JSW.Cut.exists_cut_cor_of_sub
  | (intros; apply GlobalTheory.JSW.Cut.exists_cut_cor_of_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrePowerMapOfTotalSpaces_isPullback : ∀ (S S' : Scheme.{0}) (A : Over S) (A' : Over S') (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (hφ : φ ≫ A.hom = A'.hom ≫ f), IsPullback φ A'.hom A.hom f → ∀ m : ℕ, IsPullback (powMap f φ hφ m) (pow A' m).hom (pow A m).hom f := by
  first | (exact @GlobalTheory.KS.PowPB.powMap_isPullback) | (exact GlobalTheory.KS.PowPB.powMap_isPullback) | (intros; apply GlobalTheory.KS.PowPB.powMap_isPullback  <;> assumption)
end

