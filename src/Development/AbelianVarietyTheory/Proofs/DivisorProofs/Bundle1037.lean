module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelUniqueInjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

variable {X : Scheme.{0}} [IsIntegral X]

theorem latSec_map {V V' : Type} [AddCommGroup V] [AddCommGroup V'] (M : X → AddSubgroup V)
    (φ : V →+ V') (hφ : Function.Injective φ) (U : X.Opens) (h : genericPoint X ∈ U) :
    (latSec M U).map φ = latSec (fun y => (M y).map φ) U := by
  ext w
  simp only [latSec, AddSubgroup.mem_map, AddSubgroup.mem_iInf]
  constructor
  · rintro ⟨v, hv, rfl⟩ y hy
    exact ⟨v, hv y hy, rfl⟩
  · intro hw
    obtain ⟨v, -, hv⟩ := hw _ h
    refine ⟨v, fun y hy => ?_, hv⟩
    obtain ⟨u, hu, hu'⟩ := hw y hy
    rwa [hφ (hu'.trans hv.symm)] at hu

def LatModel.mapLin {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V']
    [Module X.functionField V'] {M : X → AddSubgroup V} {F : X.Modules} (L : LatModel M F)
    (φ : V →ₗ[X.functionField] V') (hφ : Function.Injective φ) :
    LatModel (fun y => (M y).map φ.toAddMonoidHom) F where
  val U h := φ.toAddMonoidHom.comp (L.val U h)
  inj U h := hφ.comp (L.inj U h)
  range U h := by
    rw [AddMonoidHom.range_comp, L.range U h]
    exact latSec_map M φ.toAddMonoidHom hφ U h
  res U W e h s := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, L.res U W e h s]
  smul U h r s := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, L.smul U h r s, LinearMap.toAddMonoidHom_coe,
      LinearMap.map_smul]

def LatModel.transfer {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) (h : genericPoint X ∈ U)
    (s : Γ(F, U)) : Γ(F', U) :=
  Classical.choose (show L.val U h s ∈ (L'.val U h).range by
    rw [L'.range U h, ← L.range U h]; exact ⟨s, rfl⟩)

theorem LatModel.val_transfer {V : Type} [AddCommGroup V] [Module X.functionField V]
    {M : X → AddSubgroup V} {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(F, U)) : L'.val U h (L.transfer L' U h s) = L.val U h s :=
  Classical.choose_spec (show L.val U h s ∈ (L'.val U h).range by
    rw [L'.range U h, ← L.range U h]; exact ⟨s, rfl⟩)

def LatModel.secEquiv {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) (h : genericPoint X ∈ U) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F', U) where
  toFun := L.transfer L' U h
  map_add' s t := L'.inj U h (by simp only [map_add (f := _), LatModel.val_transfer])
  map_smul' r s := L'.inj U h (by
    simp only [RingHom.id_apply, LatModel.val_transfer, L'.smul U h, L.smul U h])
  invFun := L'.transfer L U h
  left_inv s := L.inj U h (by simp only [LatModel.val_transfer])
  right_inv s := L'.inj U h (by simp only [LatModel.val_transfer])

theorem LatModel.val_secEquiv {V : Type} [AddCommGroup V] [Module X.functionField V]
    {M : X → AddSubgroup V} {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(F, U)) : L'.val U h (L.secEquiv L' U h s) = L.val U h s :=
  L.val_transfer L' U h s

theorem subsingleton_sec_of_not_gen (F : X.Modules) {U : X.Opens} (hU : genericPoint X ∉ U) :
    Subsingleton Γ(F, U) := by
  haveI : Subsingleton Γ(X, U) := ⟨fun a b => fn_ext fun h => absurd h hU⟩
  exact Module.subsingleton Γ(X, U) Γ(F, U)


open Classical in
def LatModel.secEquiv' {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F', U) :=
  if h : genericPoint X ∈ U then L.secEquiv L' U h else
    haveI := subsingleton_sec_of_not_gen F h
    haveI := subsingleton_sec_of_not_gen F' h
    LinearEquiv.ofSubsingleton _ _

def LatModel.iso {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') : F ≅ F' :=
  GlobalTheory.LB.isoOfLinear (L.secEquiv' L') fun {U W} e s => by
    by_cases hW : genericPoint X ∈ W
    · have hU : genericPoint X ∈ U := e hW
      apply L'.inj W hW
      simp only [LatModel.secEquiv', dif_pos hW, dif_pos hU]
      rw [L.val_secEquiv L' W hW, L'.res U W e hW, L.res U W e hW, L.val_secEquiv L' U hU]
    · haveI := subsingleton_sec_of_not_gen F' hW
      exact Subsingleton.elim _ _

theorem latModel_map_and_unique : ∀ (X : Scheme.{0}) [IsIntegral X] {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V'] [Module X.functionField V'] (M : X → AddSubgroup V) (F F' : X.Modules) (φ : V →ₗ[X.functionField] V'), Function.Injective φ → LatModel M F → (Nonempty (LatModel (fun y => (M y).map φ.toAddMonoidHom) F)) ∧ (LatModel M F' → Nonempty (F ≅ F')) := by
  intro X _ V V' _ _ _ _ M F F' φ hφ L
  exact ⟨⟨L.mapLin φ hφ⟩, fun L' => ⟨L.iso L'⟩⟩

end GlobalTheory.LogDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkNeTopOfNoGenerisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory

namespace GlobalTheory

theorem isFiniteLength_localized_of_minimal_prime {A B M N : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [Algebra A B] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime B p]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] (f : M →ₗ[A] N) [IsLocalizedModule p.primeCompl f]
    (h : ∀ q : Ideal A, q.IsPrime → Module.annihilator A M ≤ q → q ≤ p → q = p) :
    IsFiniteLength B N := by
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  have : Module.Finite B N := Module.Finite.of_isLocalizedModule p.primeCompl f
  have : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B p
  have : IsArtinianRing (B ⧸ Module.annihilator B N) := by
    rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
    refine ⟨inferInstance, Ring.krullDimLE_zero_iff.mpr fun Q hQ => ?_⟩
    let Q' := Q.comap (Ideal.Quotient.mk (Module.annihilator B N))
    have hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
    have h1 : Module.annihilator A M ≤ Q'.comap (algebraMap A B) := by
      intro a ha
      have : algebraMap A B a ∈ Module.annihilator B N := by
        rw [← map_annihilator_of_isLocalizedModule p.primeCompl f]
        exact Ideal.mem_map_of_mem _ ha
      simp only [Q', Ideal.mem_comap]
      rw [Ideal.Quotient.eq_zero_iff_mem.2 this]
      exact Q.zero_mem
    have h2 : Q'.comap (algebraMap A B) ≤ p := by
      rw [← IsLocalization.AtPrime.under_maximalIdeal B p]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ'.ne_top)
    have h3 : Ideal.under A Q' = p := h _ (Ideal.comap_isPrime _ _) h1 h2
    have h4 : Q' = IsLocalRing.maximalIdeal B := by
      rw [← IsLocalization.map_under p.primeCompl B Q', h3,
        IsLocalization.AtPrime.map_eq_maximalIdeal]
    have h5 : Q'.IsMaximal := h4 ▸ IsLocalRing.maximalIdeal.isMaximal B
    have h6 := Ideal.map_eq_top_or_isMaximal_of_surjective
      (Ideal.Quotient.mk (Module.annihilator B N)) Ideal.Quotient.mk_surjective h5
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h6
    exact h6.resolve_left hQ.ne_top
  exact isFiniteLength_of_isArtinianRing_annihilator

theorem QCoh.length_stalk_ne_top_of_no_generisation (X : Scheme.{0}) [IsLocallyNoetherian X]
    (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] (w : X)
    (h : ∀ y ∈ GlobalTheory.QCoh.support F, w ∈ closure ({y} : Set X) → y = w) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ := by
  obtain ⟨U, hU, hx⟩ := QCoh.exists_affine_mem w
  obtain ⟨x, rfl⟩ : ∃ x' : U, x' = w := ⟨⟨w, hx⟩, rfl⟩
  have := hU.isLocalization_stalk x
  have := QCoh.isLocalizedModule_germLinear F hU x
  have := QCoh.finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  rw [Module.length_ne_top_iff]
  refine isFiniteLength_localized_of_minimal_prime (hU.primeIdealOf x).asIdeal
    (QCoh.germLinear F x) fun q hq h1 h2 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q, hq⟩
  have hP : hU.fromSpec P ∈ QCoh.support F := by
    have : P ∈ Module.support Γ(X, U) Γ(F, U) := Module.mem_support_iff_of_finite.2 h1
    rw [← QCoh.fromSpec_preimage_support F hU] at this
    exact this
  have hs : P ⤳ hU.primeIdealOf x := (PrimeSpectrum.le_iff_specializes _ _).1 h2
  have hs' : hU.fromSpec P ⤳ (x : X) := by
    rw [← hU.fromSpec_primeIdealOf x]
    exact hs.map hU.fromSpec.continuous
  have e := h _ hP (specializes_iff_mem_closure.1 hs')
  rw [← hU.fromSpec_primeIdealOf x] at e
  have e' : P = hU.primeIdealOf x := hU.fromSpec.isOpenEmbedding.injective e
  exact congrArg PrimeSpectrum.asIdeal e'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkReducedClosedGenericPointEqRank
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory

namespace GlobalTheory.StalkLength

theorem length_stalk_pushforward {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i]
    (F : Y.Modules) (y : Y) :
    Module.length (X.presheaf.stalk (i y))
        (((Scheme.Modules.pushforward i).obj F).presheaf.stalk (i y) :) =
      Module.length (Y.presheaf.stalk y) (F.presheaf.stalk y :) := by
  let G := (Scheme.Modules.pushforward i).obj F
  let φ := i.stalkMap y
  letI : Algebra (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) := φ.hom.toAlgebra
  letI : Module (X.presheaf.stalk (i y)) (F.presheaf.stalk y :) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk (i y)) (Y.presheaf.stalk y))
  haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (F.presheaf.stalk y :) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Ψ : (G.presheaf.stalk (i y) :) →+ (F.presheaf.stalk y :) :=
    (F.presheaf.stalkPushforward _ i.base y).hom
  have hΨ (U : X.Opens) (hU : i y ∈ U) (s : Γ(G, U)) :
      Ψ (G.presheaf.germ U _ hU s) = F.presheaf.germ (i ⁻¹ᵁ U) y hU s :=
    congr($(TopCat.Presheaf.stalkPushforward_germ _ i.base F.presheaf U y hU).hom s)
  have hiso := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
    (f := i.base) i.isClosedEmbedding.isInducing F.presheaf y
  have hbij : Function.Bijective Ψ :=
    ConcreteCategory.bijective_of_isIso (F.presheaf.stalkPushforward _ i.base y)
  have hsmul (a : X.presheaf.stalk (i y)) (m : (G.presheaf.stalk (i y) :)) :
      Ψ (a • m) = φ.hom a • Ψ m := by
    obtain ⟨U₁, hU₁, r, rfl⟩ := X.presheaf.germ_exist a
    obtain ⟨U₂, hU₂, s, rfl⟩ := G.presheaf.germ_exist m
    have hU : i y ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) _ hU,
      ← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) _ hU]
    generalize X.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r = r'
    generalize G.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op s = s'
    rw [← GlobalTheory.QCoh.germ_smul G, hΨ, hΨ]
    refine (GlobalTheory.QCoh.germ_smul F (U := i ⁻¹ᵁ (U₁ ⊓ U₂)) _ _ (i.app _ r') s').trans ?_
    congr 1
    exact congr($(Scheme.Hom.germ_stalkMap i (U₁ ⊓ U₂) y hU).hom r').symm
  let e : (G.presheaf.stalk (i y) :) ≃ₗ[X.presheaf.stalk (i y)] (F.presheaf.stalk y :) :=
    { AddEquiv.ofBijective Ψ hbij with map_smul' := hsmul }
  exact e.length_eq.trans (Module.length_eq_of_surjective (i.stalkMap_surjective y))

theorem length_stalk_pushforward_genericPoint : ∀ (X : Scheme.{0}) (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [GlobalTheory.QCoh.IsFiniteQC G],
    Module.length (X.presheaf.stalk (redι Z (genericPoint _)))
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) =
      (GlobalTheory.VB.genRank G : ℕ∞) := by
  intro X Z _ G _
  rw [length_stalk_pushforward]
  exact Module.length_eq_finrank (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.functionField
    (GlobalTheory.VB.genStalk G)

end GlobalTheory.StalkLength
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LettersEqFockVarsCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh


set_option maxHeartbeats 1000000 in
theorem letters_eq_fockVars_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (X : Data D.host.E D.R.r) (g : ℕ) (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (vr : Harm.Var X.Ψ (T.Q.Dw ((i : ℕ) + 1)).p X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → IsVarOf (Vc D i) (Wc D i) X (T.Q.Dw ((i : ℕ) + 1)).p vr → (∀ ℓ : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank, (vr (Dc.eL ℓ)).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (vr (Dc.eL ℓ)).1 ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (vr (Dc.eL ℓ)).1) ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hT i Tp tup O _ X g Dc vr hM hp hv ℓ
  have hP := hT.laws.pins
  have hm : ∀ τ, τ ∉ X.Ψ → (T.Q.Dw ((i : ℕ) + 1)).mult τ ≤ X.p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg fun h : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 => hτ ((hM.psi τ).2 (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ h)), hp]
  obtain ⟨h1, h2⟩ := Dic.letter Dc (fun τ => RingHom.ext fun _ => rfl) hm ℓ
  obtain ⟨g1, g2, g3⟩ := hv (Dc.eL ℓ)
  refine ⟨g2.trans h1, ?_⟩
  rcases h2 with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩
  · rw [e1, Sum.elim_inl] at g3
    exact Or.inl ⟨e2.trans g1, g3.trans e3⟩
  · rw [e1, Sum.elim_inr] at g3
    exact Or.inr ⟨by rw [← g1]; exact e2, by rw [g3, e3]⟩

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpFrame.LevelMap

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ}

theorem grpA_mul (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) (g h : ι → GL (Fin N) O) :
    grpA O N lam (g * h) = grpA O N lam g * grpA O N lam h := by
  apply Subtype.ext
  show grp O N lam (g * h) = grp O N lam g * grp O N lam h
  unfold grp
  exact map_mul _ g h

theorem grpA_one (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) :
    grpA O N lam 1 = 1 := by
  apply Subtype.ext
  show grp O N lam 1 = 1
  unfold grp
  exact map_one _

def jK (F : Frame l ι N) (lam : ι → ℕ → ℕ) : F.K →* alg F.O N lam where
  toFun κ := (F.chi κ : F.O) • grpA F.O N lam (F.kap κ)
  map_one' := by simp [grpA_one]
  map_mul' a b := by
    rw [map_mul, map_mul, grpA_mul, Units.val_mul, smul_mul_smul_comm]

end GlobalTheory.ExpFrame.LevelMap

theorem GlobalTheory.ExpFrame.levelMap_exists : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), ∃ (jK : F.K →* alg F.O N lam), F.IsJ lam jK := by
  intro l _ ι _ _ N F lam
  exact ⟨GlobalTheory.ExpFrame.LevelMap.jK F lam, fun κ => rfl⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZeroStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HatInt in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → ∀ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q ≠ 0 → ∀ s : 𝓞 D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i H Dw ι t l₂ φ hφ q hq s hs b
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by
    have := l₂.three_le
    omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    let single : Fin (Vc D i).rank → Dw.La := Pi.single b w
    let shift : Fin (Vc D i).rank → Dw.La := fun j => H.bar s • single j
    have hinv : ∀ x, φ (x + fun j => Submodule.Quotient.mk (shift j)) = φ x := by
      intro x
      obtain ⟨y, rfl⟩ : ∃ y : Fin (Vc D i).rank → Dw.La,
          x = fun j => Submodule.Quotient.mk (y j) :=
        ⟨fun j => qRep (x j), funext fun j =>
          (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x j))).symm⟩
      have hshift := (he (fun j => y j + shift j)).2
      have horig := (he y).2
      simp only [RingHom.id_apply] at hshift horig
      have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t →
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun j => ι (y j + shift j)) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun j => ι (y j)) := by
        intro PP hP
        have hmap : (fun j => ι (y j + shift j)) =
            fun j => ι (y j) + ((H.bar s : 𝓞 D.host.E) : D.host.E) • ι (single j) := by
          funext j
          change ι (y j + H.bar s • single j) = _
          rw [map_add (f := _), map_smul]
          rfl
        rw [hmap, uMat_add_smul, sig_bar]
        exact redM_add_smul PP _ _ (he y).1 (he _).1 s (hs PP hP)
      rw [omegaK_congr _ _ _ (fun PP hP => hred PP (Or.inl hP)),
        omegaQ_congr _ _ _ _ _ _ (fun PP hP => hred PP (Or.inr hP)), ← horig] at hshift
      change φ (fun j => Submodule.Quotient.mk (y j) + Submodule.Quotient.mk (shift j)) = _
      simpa only [Submodule.Quotient.mk_add] using hshift
    have hpair := dvd_of_invariant l₂ φ q hq shift hinv
    unfold Formalism.L2.Pj.pairL at hpair
    rw [Finset.sum_eq_single b] at hpair
    · simpa [shift, single, Dw.adj, LevelPairing.bar_bar] using hpair
    · intro j _ hj
      simp [shift, single, Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have halt := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt, zero_add, add_zero] at halt
    have hskew : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by
      linarith
    rw [hskew]
    exact (hdvd y).neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit.CornerFubini

theorem lintegral_prod_le_symm {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z ∂(μ.prod ν) ≤ ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  rw [← lintegral_prod_swap]
  exact lintegral_prod_le _

theorem lintegral_cons_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (n : ℕ)
    (G : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ u, ∫⁻ x, G (Fin.cons x u) ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  rw [h.lintegral_map_equiv G _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_col_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (m n : ℕ)
    (G : (Fin m → Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ M, ∫⁻ v, G (fun i => Fin.cons (v i) (M i)) ∂(Measure.pi fun _ : Fin m => μ)
        ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : Fin m => e)
      (Measure.pi fun _ : Fin m => μ.prod (Measure.pi fun _ : Fin n => μ))
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) :=
    measurePreserving_pi _ _ (f := fun _ : Fin m => e) (fun _ => h)
  have h2 := (measurePreserving_arrowProdEquivProdArrow α (Fin n → α) (Fin m) (fun _ => μ)
    (fun _ => Measure.pi fun _ : Fin n => μ)).symm
  rw [h1.lintegral_map_equiv G _, h2.lintegral_map_equiv _ _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  refine lintegral_congr fun M => lintegral_congr fun v => congrArg G ?_
  funext i
  change e (v i, M i) = _
  simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_volM_le_corner (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ)
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞) :
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  refine (lintegral_cons_le (Measure.pi fun _ : Fin (n + 1) => ν) n F).trans ?_
  refine (lintegral_col_le ν n n _).trans ?_
  refine lintegral_mono fun M => lintegral_mono fun v => ?_
  exact lintegral_cons_le ν n
    (fun r => F (Matrix.of (Fin.cons r (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))))

end GlobalTheory.KSplit.CornerFubini
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquivStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K K' : Type) [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'],
    (K ≃+* K') → ∀ (Y a b b' : G.C),
    (∃ (u : Kˣ) (z : (K ⊗[ℚ] G.C)ˣ), Commute (z : K ⊗[ℚ] G.C) (inC G K Y) ∧
      inC G K a = algebraMap K (K ⊗[ℚ] G.C) (u : K) * ((z : K ⊗[ℚ] G.C) * inC G K b *
        (starT G.star K (z : K ⊗[ℚ] G.C)).unop * inC G K b')) →
    ∃ (u : K'ˣ) (z : (K' ⊗[ℚ] G.C)ˣ), Commute (z : K' ⊗[ℚ] G.C) (inC G K' Y) ∧
      inC G K' a = algebraMap K' (K' ⊗[ℚ] G.C) (u : K') * ((z : K' ⊗[ℚ] G.C) * inC G K' b *
        (starT G.star K' (z : K' ⊗[ℚ] G.C)).unop * inC G K' b') := by
  first | (exact @GlobalTheory.FinClsLoc.localTransfer) | (exact GlobalTheory.FinClsLoc.localTransfer) | (intros; apply GlobalTheory.FinClsLoc.localTransfer  <;> assumption)
end

