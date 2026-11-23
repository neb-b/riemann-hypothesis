module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalArtinHasNormGroups
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import GroundTheory.LocalFields.LocalArtinMap
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmoothWeilCharEqOneOfToAbsGaloisAbEqOne
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilCharKer

open GlobalTheory.LocDict GlobalTheory.HeckeGal Neutral.B1

theorem commutator_le_of_dense {Γ W : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [Group W] (ψ : W →* Γ) (hd : ∀ (g : Γ) (H : Subgroup Γ), IsOpen (H : Set Γ) → ∃ σ : W, g⁻¹ * ψ σ ∈ H)
    (F : Subgroup Γ) (hF : IsOpen (F : Set Γ)) (hc : ∀ σ τ : W, ψ (σ * τ * σ⁻¹ * τ⁻¹) ∈ F) :
    commutator Γ ≤ F := by
  have : Finite (Γ ⧸ F) := Subgroup.quotient_finite_of_isOpen F hF
  have : F.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hN : IsOpen (F.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (F.normalCore_isClosed (F.isClosed_of_isOpen hF))
  rw [commutator, Subgroup.commutator_le]
  intro g _ k _
  obtain ⟨σ, hσ⟩ := hd g _ hN
  obtain ⟨τ, hτ⟩ := hd k _ hN
  have e1 : QuotientGroup.mk' F.normalCore g = QuotientGroup.mk' F.normalCore (ψ σ) := QuotientGroup.eq.2 hσ
  have e2 : QuotientGroup.mk' F.normalCore k = QuotientGroup.mk' F.normalCore (ψ τ) := QuotientGroup.eq.2 hτ
  have e3 : QuotientGroup.mk' F.normalCore (ψ (σ * τ * σ⁻¹ * τ⁻¹)) =
      QuotientGroup.mk' F.normalCore (g * k * g⁻¹ * k⁻¹) := by
    simp only [map_mul, map_inv, e1, e2]
  have e4 := F.mul_mem (hc σ τ) (F.normalCore_le (QuotientGroup.eq.1 e3))
  rw [mul_inv_cancel_left] at e4
  exact e4

theorem index_normGroup {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [CharZero K] (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsAbelianGalois K L] :
    (normGroup K L).index = Nat.card (L ≃ₐ[K] L) := by
  have e : normGroup K L = (GroundTheory.LocalField.normUnits K L).range := rfl
  rw [e, ← GroundTheory.LocalField.ker_restrictAb_localArtinMap (Ω := AlgebraicClosure K) L, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (GroundTheory.LocalField.surjective_restrictAb_localArtinMap L), Subgroup.card_top]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem art_inj {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    Function.Injective fun x : (w.adicCompletion E)ˣ => art (localIdele E w x) :=
  _root_.GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w

theorem exists_inverse (h : IsPlaceOver A w) {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧
      ∀ σ : Weil h, art (localIdele E w (a σ)) = toAb E Ω σ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.LocNormGrp.art_range_weil E Ω A w h art ha
  choose a ha' using h1
  refine ⟨MonoidHom.mk' a fun σ τ => art_inj ha ?_, fun y => ?_, ha'⟩
  · simp only [map_mul, ha', Subgroup.coe_mul]
  · obtain ⟨τ, hτ⟩ := h2 y
    exact ⟨τ, art_inj ha ((ha' τ).trans hτ.symm)⟩

theorem mem_of_toAb_eq_one (h : IsPlaceOver A w) (H : Subgroup (Weil h)) (hfin : H.FiniteIndex)
    (hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H}) (hcomm : ∀ σ τ : Weil h, σ * τ * σ⁻¹ * τ⁻¹ ∈ H)
    (σ : Weil h) (hσ : toAb E Ω σ = 1) : σ ∈ H := by
  obtain ⟨K, hK, hloc, hHK⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hfin hop
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  obtain ⟨W, h'⟩ := GlobalTheory.LocNormGrp.exists_place h K
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb E Ω A w h
  obtain ⟨ι', hι'⟩ := GlobalTheory.LocDict.exists_isLocEmb K Ω A W h'
  obtain ⟨f, b, hf, hb1, hb2, hfE, -, -, -, hNc, hNg⟩ := GlobalTheory.T.local_embeddings_tower_compatible E K Ω A w W h h' hloc ι ι' hι hι'
  letI := f.toAlgebra
  have hN := GlobalTheory.T.completion_embedding_compatible_closures E K w W (fun x : K => ι (algebraMap K Ω x)) f b hf hb1
    (fun x => by rw [hb2, ι'.commutes, IsScalarTower.algebraMap_apply K (W.adicCompletion K)]) hfE
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds E Ω
  obtain ⟨artK, hartK⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  obtain ⟨a, hasurj, ha⟩ := exists_inverse h hart
  let N := Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)
  have key := GlobalTheory.LocNormGrp.art_norm_eq_res E K Ω art artK hart hartK w W
    (GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h') N (Continuous.units_map _ hNc) fun z => Units.ext (hNg z)
  obtain ⟨h1, -⟩ := GlobalTheory.LocNormGrp.art_range_weil K Ω A W h' artK hartK
  set Kw := w.adicCompletion E
  have : CharZero Kw := charZero_of_injective_algebraMap (algebraMap E Kw).injective
  have : IsGalois Kw (Kbar w) := IsAlgClosure.isGalois Kw (Kbar w)
  set L := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hL

  have hHN : H ≤ (normGroup Kw L).comap a := fun s hs => by
    obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.WeilSurj.exists_weil_of_fixes E K Ω A w W h h' s ((hHK s).1 hs)
    obtain ⟨y, hy⟩ := h1 τ
    rw [Subgroup.mem_comap, hN]
    exact ⟨y, art_inj hart ((key y τ s hτ hy).trans (ha s).symm)⟩

  have hfd : FiniteDimensional Kw L := by
    let pb := Field.powerBasisOfFiniteOfSeparable E K
    let j : K →ₐ[E] Kbar w := ι.comp K.val
    have hfd0 : FiniteDimensional Kw (IntermediateField.adjoin Kw {j pb.gen}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    have hle : L ≤ IntermediateField.adjoin Kw {j pb.gen} := by
      rw [hL, IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      obtain ⟨p, rfl⟩ := pb.exists_eq_aeval' x
      show j (aeval pb.gen p) ∈ IntermediateField.adjoin Kw {j pb.gen}
      rw [← aeval_algHom_apply, ← aeval_map_algebraMap Kw]
      exact IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  obtain ⟨θ, hθ, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hψ : ∀ s : Weil h, Lifts ι (ψ s) (s : G E Ω) := fun s => hl _
  have hψ' : ∀ (s : Weil h) (g : GalLoc w), Lifts ι g s → ψ s = g := fun s g hg => by
    have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) s := by
      have := hl (θ.symm g)
      rw [θ.apply_symm_apply] at this
      exact Subtype.ext (this.eq hg)
    show θ _ = g
    rw [← e, θ.apply_symm_apply]
  have hHL : ∀ s : Weil h, s ∈ H ↔ ψ s ∈ L.fixingSubgroup := fun s => by
    rw [hHK, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, hL, IntermediateField.adjoin_le_iff]
    constructor
    · rintro hs _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      refine (Subgroup.zpowers_le (H := MulAction.stabilizer (GalLoc w) (ι (algebraMap K Ω x)))).2 ?_ hg
      show ψ s (ι x) = ι x
      rw [hψ, hs]
    · intro hs x
      have := (IntermediateField.mem_fixedField_iff _ _).1 (hs ⟨x, rfl⟩) _ (Subgroup.mem_zpowers _)
      rw [hψ] at this
      exact ι.toRingHom.injective this
  have hLo : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := L.fixingSubgroup_isOpen
  have hcl : commutator (GalLoc w) ≤ L.fixingSubgroup :=
    commutator_le_of_dense ψ (fun g U hU => by
      obtain ⟨s, g', h1, h2⟩ := GlobalTheory.LocDec.exists_lifts_mul_mem A w h ι θ hθ hl g U hU
      exact ⟨s, by rwa [hψ' s g' h1]⟩) _ hLo fun s t => (hHL _).1 (hcomm s t)
  have hnorm : L.fixingSubgroup.Normal := Subgroup.Normal.of_commutator_le _ hcl
  have hgal : IsGalois Kw L := (InfiniteGalois.normal_iff_isGalois L).1 hnorm
  have hab : IsAbelianGalois Kw L := GroundTheory.LocalField.isAbelianGalois_of_le_maximalAbelianExtension L (by
    rw [GroundTheory.LocalField.maximalAbelianExtension, IntermediateField.le_iff_le]
    exact Subgroup.topologicalClosure_minimal _ hcl (Subgroup.isClosed_of_isOpen _ hLo))

  have hHker : H = ((AlgEquiv.restrictNormalHom L).comp ψ).ker := by
    ext s
    rw [hHL, ← IntermediateField.restrictNormalHom_ker]; rfl
  have i1 : H.index ≤ Nat.card (L ≃ₐ[Kw] L) := by
    rw [hHker, Subgroup.index_ker]
    exact Subgroup.card_le_card_group _
  have i2 : ((normGroup Kw L).comap a).index = Nat.card (L ≃ₐ[Kw] L) := by
    rw [Subgroup.index_comap_of_surjective _ hasurj, index_normGroup]
  have i3 := Subgroup.relIndex_mul_index hHN
  have i4 : H.relIndex ((normGroup Kw L).comap a) = 1 := by
    have := hfin.index_ne_zero
    rw [i2] at i3
    have hp : 0 < Nat.card (L ≃ₐ[Kw] L) := Nat.card_pos
    generalize H.relIndex ((normGroup Kw L).comap a) = r at i3
    rcases r with _ | _ | r
    · omega
    · rfl
    · nlinarith
  refine Subgroup.relIndex_eq_one.1 i4 ?_
  have : a σ = 1 := art_inj hart (by simp only [ha, hσ, map_one])
  rw [Subgroup.mem_comap, this]
  exact Subgroup.one_mem _

theorem deg_eq_zero_of_toAb_eq_one (h : IsPlaceOver A w) (σ : Weil h) (hσ : toAb E Ω σ = 1) : deg σ = 0 := by
  let n := (deg σ).natAbs + 1
  let r : Weil h →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp (degHom h)
  have hr : ∀ s, s ∈ r.ker ↔ (n : ℤ) ∣ deg s := fun s => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; rfl
  have := mem_of_toAb_eq_one h r.ker inferInstance
    (by simp [hr]) (fun s t => by simp [hr]) σ hσ
  rw [hr] at this
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by simp only [Int.natAbs_natCast]; omega)

theorem apply_eq_one_of_toAb_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ξ : Weil h →* ℂˣ), GlobalTheory.WeilDeligne.IsSmooth ξ → ∀ σ : Weil h, GlobalTheory.HeckeGal.toAb E Ω σ = 1 → ξ σ = 1 := by
  intro E Ω _ _ _ _ _ A w h ξ hξ σ hσ
  let ξ' : Weil h →* ℂˣ := ξ * unrChar h (ξ (frob h))⁻¹
  have h0 : ∀ s, deg s = 0 → ξ' s = ξ s := fun s hs => by simp [ξ', hs]
  have h1 : ξ' (frob h) = 1 := by simp [ξ']
  have hop : IsOpen {s : Ine (F := E) A | ineIncl h s ∈ ξ'.ker} := by
    simp only [MonoidHom.mem_ker, h0 _ (deg_ineIncl _)]
    exact hξ
  have := compactSpace_Ine (E := E) A
  have hq : Finite (Ine (F := E) A ⧸ (ξ'.comp (ineIncl h)).ker) := Subgroup.quotient_finite_of_isOpen _ hop
  have hr : Finite (ξ'.comp (ineIncl h)).range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).toEquiv
  have hle : ξ'.range ≤ (ξ'.comp (ineIncl h)).range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
    refine ⟨t, ?_⟩
    conv_rhs => rw [ht, map_mul, map_zpow, h1, _root_.one_zpow, one_mul]
    rfl
  have hr' : Finite ξ'.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have := mem_of_toAb_eq_one h ξ'.ker inferInstance hop (fun s t => by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (ξ' s) (ξ' t)]
    group) σ hσ
  rw [← h0 σ (deg_eq_zero_of_toAb_eq_one h σ hσ)]
  exact this

end GlobalTheory.WeilCharKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOutIffGenAt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.PtExt

variable {D : D7}


open Classical in
def sys (L : LocAll (lay0 D)) (i : L.X.nd.Loc) (x : L.X.nd.X i) : PlE D.host → ℕ → ℂ := fun v k =>
  if SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then
    iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x)
  else 0

theorem splitOut_iff_genAt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (v : PlE D.host) (k : ℕ) :
    (SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) ↔ GenAt D (D.what₂.places.resChar w) (C.Q w) v k := by
  obtain ⟨Sp, -, -⟩ := hB
  have hw : L.X.nd.w i = w := ((L.X.nd.locs_mem j w i).1 hi).2
  have hl : L.X.nd.l i = D.what₂.places.resChar w := by rw [← hw]; exact (L.X.nd.w_l i).symm
  have hQ : L.X.nd.Q i = C.Q w := (Sp.Q_eq j w i hi).trans (Sp.Qc_eq j w)
  have hS : v ∈ L.X.nd.S i ↔ v ∈ placesS D (L.X.nd.l i) := L.X.nd.S_def i v
  unfold SplitOut GenAt
  rw [hS, ← hl, ← hQ]
  tauto

theorem sys_of_genAt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) {v : PlE D.host} {k : ℕ}
    (h : GenAt D (D.what₂.places.resChar w) (C.Q w) v k) :
    sys L i x v k = iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) := by
  unfold sys
  rw [if_pos ((splitOut_iff_genAt hB hi v k).2 h)]

theorem sys_of_not_genAt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) {v : PlE D.host} {k : ℕ}
    (h : ¬ GenAt D (D.what₂.places.resChar w) (C.Q w) v k) : sys L i x v k = 0 := by
  unfold sys
  rw [if_neg (fun h' => h ((splitOut_iff_genAt hB hi v k).1 h'))]

theorem sys_mem {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) :
    sys L i x ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w) := by
  refine ⟨fun v k h => sys_of_not_genAt hB hi x h, ?_⟩
  have hB' := hB
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB'
  obtain ⟨hj, hw⟩ := (L.X.nd.locs_mem j w i).1 hi
  subst hj hw
  obtain ⟨P, hP⟩ := L.Y.naut.pt_surj i x
  have key : ∃ y : D.what₂.Mt (L.X.nd.mu i) (L.X.nd.j i), y ≠ 0 ∧
      ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        GenAt D (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) v k → IsConjPl D.host v s.w →
        IsUnif D.host.E s.v ϖ →
        NG.tN (M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).J s ϖ k ((M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).real y) =
          sys L i x v k • (M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).real y := by
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (L.Y.naut.typeV_ne i P)
    refine ⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩
    obtain ⟨hso, k1, k2⟩ := (splitOut_iff_genAt hB hi v k).2 hg
    rw [sys_of_genAt hB hi x hg]
    exact (Au.ptV i P x).1 hP v k s ϖ hso hc hu k1 k2 y hy
  rw [L.X.nd.mu_w i] at key
  exact key

theorem iotaO_injective (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : Function.Injective (iotaO L.X.nd L.Y.naut i) := by
  intro a b h
  unfold iotaO at h
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  exact IsFractionRing.injective (L.X.nd.O i) (FractionRing (L.X.nd.O i))
    ((L.Y.naut.iotaQ i).injective ((L.Y.naut.iotaQC i).injective h))

theorem sys_inj (L : LocAll (lay0 D)) (i : L.X.nd.Loc) {x x' : L.X.nd.X i} (h : sys L i x = sys L i x') : x = x' := by
  by_contra hne
  obtain ⟨f, hf, hfx⟩ := L.X.nd.T_sep i x x' hne
  apply hfx
  let E : Subalgebra (L.X.nd.O i) (L.X.nd.X i → L.X.nd.O i) :=
    AlgHom.equalizer (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x)
      (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x')
  have hle : L.X.nd.T i ≤ E := by
    rw [← L.X.nd.T_gen i, Algebra.adjoin_le_iff]
    rintro g ⟨v, k, hs, hl, hS, hQ, k1, k2, rfl⟩
    have hv : SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV := ⟨⟨hs, hl, hS, hQ⟩, k1, k2⟩
    have := congrFun (congrFun h v) k
    unfold sys at this
    rw [if_pos hv, if_pos hv] at this
    exact iotaO_injective L i this
  exact hle hf

end GlobalTheory.PtExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TameRecord

section Transport

variable {G H V : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_comp (ρ : Representation ℂ H V) (φ : G →* H) (hφ : Continuous φ) (h : GlobalTheory.PRep.IsSmooth ρ) :
    GlobalTheory.PRep.IsSmooth (ρ.comp φ) := fun v => (h v).preimage hφ

theorem isIrreducible_comp (ρ : Representation ℂ H V) (φ : G →* H) (hs : Function.Surjective φ)
    (h : GlobalTheory.GLp.IsIrrRep ρ) : Representation.IsIrreducible (ρ.comp φ) := by
  rw [GlobalTheory.CuspRep.isIrreducible_iff]
  refine ⟨h.1, fun W hW => h.2 W fun y v hv => ?_⟩
  obtain ⟨x, rfl⟩ := hs y
  exact hW x v hv

theorem isSupercuspidal_comp [IsTopologicalGroup G] [IsTopologicalGroup H] (ρ : Representation ℂ H V) (φ : G →* H)
    (ψ : H →* G) (hφ : Continuous φ) (hψ : Continuous ψ) (h1 : ∀ x, ψ (φ x) = x) (h2 : ∀ y, φ (ψ y) = y)
    (h : GlobalTheory.PRep.IsSupercuspidal ρ) : GlobalTheory.PRep.IsSupercuspidal (ρ.comp φ) := by
  refine ⟨isSmooth_comp ρ φ hφ h.1, fun v l hl => ?_⟩
  have hl' : l ∈ GlobalTheory.PRep.smoothPart (Representation.dual ρ) := by
    have e : {y : H | Representation.dual ρ y l = l} =
        ψ ⁻¹' {x : G | Representation.dual (ρ.comp φ) x l = l} := by
      ext y
      simp [Representation.dual_apply, h2]
    show IsOpen {y : H | Representation.dual ρ y l = l}
    rw [e]
    exact hl.preimage hψ
  obtain ⟨C, hC, hCv⟩ := h.2 v l hl'
  refine ⟨ψ '' C, hC.image hψ, fun x hx => ?_⟩
  obtain ⟨z, hz, c, hc, e⟩ := hCv (φ x) hx
  refine ⟨ψ z, Subgroup.mem_center_iff.2 fun y => ?_, ψ c, ⟨c, hc, rfl⟩, ?_⟩
  · rw [← h1 y, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz (φ y))]
  · rw [← map_mul, ← e, h1]

end Transport

section GLMap

variable {n : Type} [Fintype n] [DecidableEq n] {K₁ K₂ : Type} [Field K₁] [Field K₂] [TopologicalSpace K₁]
  [TopologicalSpace K₂] [IsTopologicalRing K₁] [IsTopologicalRing K₂]

theorem continuous_glMap (f : K₁ →+* K₂) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := n) f) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id hf)

theorem glMap_symm_apply (i : K₁ ≃+* K₂) (x : GL n K₁) :
    Matrix.GeneralLinearGroup.map i.symm.toRingHom (Matrix.GeneralLinearGroup.map i.toRingHom x) = x := by
  ext a b
  simp

theorem glMap_apply_symm (i : K₁ ≃+* K₂) (y : GL n K₂) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom y) = y := by
  ext a b
  simp

end GLMap

theorem continuous_symm {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : Continuous i.symm := by
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toRingHom.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

def transRep {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) :=
  ⟨_, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom),
    isSmooth_comp _ _ (continuous_glMap _ (continuous_symm _ (I.i k v) (I.cont k v))) hs,
    isIrreducible_comp _ _ (fun y => ⟨_, glMap_apply_symm (I.i k v).symm y⟩) h⟩

theorem transRep_comp {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])) (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    (transRep I k v π h hs).ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom) = π.ρ :=
  MonoidHom.ext fun x => by
    show π.ρ _ = π.ρ x
    rw [glMap_symm_apply]

theorem iso_pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])) (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    Nonempty (π ≅ pull I k v (transRep I k v π h hs)) :=
  by
    have E : π.ρ.Equiv ((transRep I k v π h hs).ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)) := by
      rw [transRep_comp]; exact Representation.Equiv.refl _
    exact ⟨(Rep.mkIso E : Rep.of π.ρ ≅ _)⟩

end GlobalTheory.TameRecord
end
end

