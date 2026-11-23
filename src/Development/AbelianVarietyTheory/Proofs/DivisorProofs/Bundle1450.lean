module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueNormalOfProfiniteInvariantsStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnValuationRings
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCongrOfResidueFixedByDecomposition
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ResidueFixed

theorem residue_fixed_mem : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ x ∈ V, (∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → V.valuation (σ x - x) < 1) → ∃ r : R, V.valuation (x - algebraMap K Ω (algebraMap R K r)) < 1 := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV x hx hfix
  classical
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have h : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact h
  let φ : R →+* V := (algebraMap R Ω).codRestrict V.toSubring hRV

  have hmR : ∀ r ∈ maximalIdeal R, V.valuation (algebraMap R Ω r) < 1 := by
    intro r hr
    by_contra hlt
    have h1 : V.valuation (algebraMap R Ω r) = 1 :=
      le_antisymm (V.valuation_le_one (φ r)) (not_lt.1 hlt)
    have hu : IsUnit (φ r) := (V.valuation_eq_one_iff (φ r)).2 h1
    have hne : algebraMap R K r ≠ 0 := by
      intro h0
      rw [show algebraMap R Ω r = algebraMap K Ω (algebraMap R K r) from rfl, h0, map_zero, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω (algebraMap R K r)⁻¹ ∈ V
      obtain ⟨u, hu'⟩ := hu
      have : ((u⁻¹ : Vˣ) : V) * φ r = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Vˣ) : V)) : Ω) = algebraMap K Ω (algebraMap R K r)⁻¹ := by
        rw [map_inv₀]
        refine (eq_inv_of_mul_eq_one_left ?_)
        exact congrArg Subtype.val this
      rw [← h2]; exact SetLike.coe_mem _
    rw [hV] at hinv
    obtain ⟨r', hr'⟩ := hinv
    apply (mem_maximalIdeal r).1 hr
    refine isUnit_iff_exists_inv.2 ⟨r', IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr', map_one, mul_inv_cancel₀ hne]

  let B := integralClosure R Ω
  have hBV : ∀ b : B, (b : Ω) ∈ V := by
    intro b
    obtain ⟨p, hpm, hp⟩ := b.2
    have hint : IsIntegral V (b : Ω) := by
      refine ⟨p.map φ, hpm.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hp
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    rw [← hy]; exact y.2
  let ψ : B →+* V := (B.val : B →+* Ω).codRestrict V.toSubring hBV
  let Q : Ideal B := (maximalIdeal V).comap ψ
  have hQ : ∀ b : B, b ∈ Q ↔ V.valuation (b : Ω) < 1 := fun b => V.valuation_lt_one_iff (ψ b)
  let G := Ω ≃ₐ[K] Ω
  have hc : SMulCommClass G R Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have : ContinuousSMul G B := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant R B G := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral R k := by
      have h2 : IsIntegral R (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff ).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hQP : Q.LiesOver (maximalIdeal R) := by
    constructor
    refine le_antisymm (fun r hr => ?_) (IsLocalRing.le_maximalIdeal ?_)
    · change algebraMap R B r ∈ Q
      rw [hQ]; exact hmR r hr
    · intro h1
      have h : (1 : R) ∈ Q.comap (algebraMap R B) := by
        change (1 : R) ∈ Q.under R
        rw [h1]; exact Submodule.mem_top
      rw [Ideal.mem_comap, map_one, hQ] at h
      simp at h
  have hQmax : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (maximalIdeal R)
  letI := Ideal.Quotient.field (maximalIdeal R)
  letI := Ideal.Quotient.field Q
  haveI hN : Normal (R ⧸ maximalIdeal R) (B ⧸ Q) := GlobalTheory.T.residue_normal_of_profinite_invariants G (maximalIdeal R) Q
  haveI : PerfectField (R ⧸ maximalIdeal R) := ‹PerfectField (ResidueField R)›
  haveI : IsGalois (R ⧸ maximalIdeal R) (B ⧸ Q) := {}

  have hBle : ∀ b : B, V.valuation (b : Ω) ≤ 1 := fun b => V.valuation_le_one (ψ b)

  have hsub : ∀ g ∈ MulAction.stabilizer G Q, ∀ y ∈ V, g y ∈ V := by
    intro g hg y hy
    obtain ⟨a, s, ha, hs, hsv, hys⟩ := _root_.GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove R K Ω V hV y hy
    let a' : B := ⟨a, ha⟩
    let s' : B := ⟨s, hs⟩
    have hs'Q : s' ∉ Q := by rw [hQ]; exact fun h => (ne_of_lt h) hsv
    have hgs : g • s' ∉ Q := by
      intro h
      apply hs'Q
      have h' : g • s' ∈ g • Q := by rw [MulAction.mem_stabilizer_iff.1 hg]; exact h
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul] at h'
      exact h'
    have hgsv : V.valuation (g s) = 1 := by
      rw [hQ] at hgs
      exact le_antisymm (hBle (g • s')) (not_lt.1 hgs)
    have hga : V.valuation (g a) ≤ 1 := hBle (g • a')
    apply V.mem_of_valuation_le_one
    have : g y * g s = g a := by rw [← map_mul, hys]
    rw [← this, map_mul, hgsv, _root_.mul_one] at hga
    exact hga
  have hstabV : ∀ g ∈ MulAction.stabilizer G Q, g • V = V := by
    intro g hg
    ext z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hz
      have := hsub g hg _ hz
      have e : g (g⁻¹ • z) = z := smul_inv_smul g z
      rwa [e] at this
    · intro hz
      exact hsub g⁻¹ (inv_mem hg) z hz

  obtain ⟨a, s, ha, hs, hsv, hxs⟩ := _root_.GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove R K Ω V hV x hx
  let a' : B := ⟨a, ha⟩
  let s' : B := ⟨s, hs⟩
  have hs'Q : s' ∉ Q := by rw [hQ]; exact fun h => (ne_of_lt h) hsv
  have hsne : Ideal.Quotient.mk Q s' ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  let ξ : B ⧸ Q := Ideal.Quotient.mk Q a' / Ideal.Quotient.mk Q s'
  have hξ : ∀ τ : (B ⧸ Q) ≃ₐ[R ⧸ maximalIdeal R] (B ⧸ Q), τ ξ = ξ := by
    intro τ
    obtain ⟨⟨σ, hσQ⟩, hστ⟩ :=
      Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) (maximalIdeal R) Q τ
    have hlt := hfix σ (hstabV σ hσQ)
    have hσs : σ • s' ∉ Q := by
      intro h
      apply hs'Q
      have h' : σ • s' ∈ σ • Q := by rw [MulAction.mem_stabilizer_iff.1 hσQ]; exact h
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul] at h'
      exact h'
    have hσsv : V.valuation (σ s) = 1 := by
      have h := hσs
      rw [hQ] at h
      exact le_antisymm (hBle (σ • s')) (not_lt.1 h)
    have hσs0 : Ideal.Quotient.mk Q (σ • s') ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hστ]
    simp only [ξ, map_div₀, Ideal.Quotient.stabilizerHom_apply]
    change Ideal.Quotient.mk Q (σ • a') / Ideal.Quotient.mk Q (σ • s') = _
    rw [div_eq_div_iff hσs0 hsne, ← map_mul, ← map_mul, Ideal.Quotient.eq, hQ]
    have e : ((σ • a' * s' - a' * σ • s' : B) : Ω) = (σ x - x) * s * σ s := by
      change σ a * s - a * σ s = _
      rw [← hxs, map_mul]; ring
    rw [e, map_mul, map_mul, hsv, hσsv, _root_.mul_one, _root_.mul_one]
    exact hlt
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := R ⧸ maximalIdeal R) ξ).2 hξ
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨r, ?_⟩
  have h1 : Ideal.Quotient.mk Q (algebraMap R B r) = ξ := hc
  have h2 : Ideal.Quotient.mk Q (algebraMap R B r * s') = Ideal.Quotient.mk Q a' := by
    rw [map_mul, h1, div_mul_cancel₀ _ hsne]
  rw [Ideal.Quotient.eq, hQ] at h2
  have e : ((algebraMap R B r * s' - a' : B) : Ω) = (algebraMap K Ω (algebraMap R K r) - x) * s := by
    change algebraMap K Ω (algebraMap R K r) * s - a = _
    rw [← hxs]; ring
  rw [e, map_mul, hsv, _root_.mul_one, Valuation.map_sub_swap] at h2
  exact h2

end GlobalTheory.ResidueFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaCmType
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.EtaCMType

theorem idFF_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : Fˣ) :
    idFF F E (Units.map (algebraMap F (AF F)).toMonoidHom a) =
      Units.map (incAF F E).toMonoidHom (Units.map (algebraMap F E).toMonoidHom a) := by
  apply Units.ext
  change algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (a : F)) =
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E (a : F))
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem continuous_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Continuous (idFF F E) := by
  haveI := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  exact Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E)))

theorem at_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : (AF F)ˣ)
    (h : At (evI F) ((a : AF F) - 1)) :
    At (evI F) (((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) := by
  intro u hu
  have e : ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = algebraMap (AF F) (AF F ⊗[F] E) ((a : AF F) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [e, Algebra.smul_def, ← map_mul, ← smul_eq_mul, h u hu, map_zero]

theorem exists_eta_cmType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨ξ, hξ, hξe⟩ := _root_.GlobalTheory.WeilTypeChar.exists_weil_char F E σ B hB
  obtain ⟨η₀, hη₀, huniq⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E hB.cm.2.2.1
  have hη₀' : IsEtaF E η₀ := hη₀
  let lam : (AF F)ˣ →* Circle := ξ.comp (idFF F E) * η₀⁻¹
  have hlam : ∀ a, lam a = ξ (idFF F E a) * (η₀ a)⁻¹ := fun a => rfl
  have hlc : Continuous lam := by
    have : Continuous fun a => ξ (idFF F E a) * (η₀ a)⁻¹ :=
      (hξ.1.comp continuous_idFF).mul (hη₀.1.inv)
    exact this
  have hlF : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1 := by
    intro a
    rw [hlam, idFF_rat, hξ.2, hη₀.2.1, inv_one, one_mul]
  have hlinf : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1 := by
    intro a ha
    have e1 := hξe _ (at_idFF a ha)
    have e2 := _root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign F E σ B hB η₀ hη₀' a ha
    have e3 : ξ (idFF F E a) = η₀ a := by
      apply Circle.ext
      rw [e1, e2]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [zpow_one]
    rw [hlam, e3, mul_inv_cancel]
  obtain ⟨lam', hl'H, hl'inf, hl'res⟩ := _root_.GlobalTheory.HeckeExtend.exists_extend_hecke F E σ B hB lam hlc hlF hlinf
  refine ⟨ξ * lam'⁻¹, ⟨hξ.1.mul hl'H.1.inv, fun x => ?_⟩, ⟨⟨η₀, hη₀'⟩, fun η hη a => ?_⟩, fun z hz => ?_⟩
  · change ξ _ * (lam' _)⁻¹ = 1
    rw [hξ.2, hl'H.2, inv_one, one_mul]
  · change ξ _ * (lam' _)⁻¹ = _
    rw [huniq η hη, hl'res, hlam, pow_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]
  · change ((ξ z * (lam' z)⁻¹ : Circle) : ℂ) = _
    rw [hl'inf z hz, inv_one, mul_one]
    exact hξe z hz

end GlobalTheory.EtaCMType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisSmulEqValuationSubringOverDvr
section
open scoped Pointwise
open GlobalTheory.Published GlobalTheory.Published.AbVarRed

namespace GlobalTheory.ValConj

theorem isLocallyConstant_apply {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (x : Ω) :
    IsLocallyConstant (fun g : Ω ≃ₐ[K] Ω => g x) := by
  let : TopologicalSpace Ω := ⊥
  have : DiscreteTopology Ω := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) Ω :=
    continuousSMul_iff_stabilizer_isOpen.mpr fun y => stabilizer_isOpen_of_isIntegral y
  rw [IsLocallyConstant.iff_continuous]
  exact (continuous_id.smul continuous_const : Continuous fun g : Ω ≃ₐ[K] Ω => g • x)

theorem exists_smul_eq_of_isAbove (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (V V' : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) (hV' : IsAbove R K V'.toSubring) :
    ∃ g : Ω ≃ₐ[K] Ω, g • V = V' := by
  classical
  have key := (isCompact_univ (X := Ω ≃ₐ[K] Ω)).inter_iInter_nonempty
    (fun x : Ω => {g : Ω ≃ₐ[K] Ω | g x ∈ V' ↔ x ∈ V})
    (fun x => ((isLocallyConstant_apply (K := K) x).comp (fun y => y ∈ V' ↔ x ∈ V)).isClosed_fiber True
      |> fun h => by simpa using h)
    (fun u => by
      let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K (u : Set Ω)).toIntermediateField
      have hL : ∀ x ∈ u, x ∈ L := fun x hx => FiniteGaloisIntermediateField.subset_adjoin K (u : Set Ω) hx
      have hc : ∀ W : ValuationSubring Ω, IsAbove R K W.toSubring →
          IsAbove R K (W.comap (algebraMap L Ω)).toSubring := fun W hW => by
        unfold IsAbove at hW ⊢
        rw [← hW]
        ext y
        rfl
      obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.ProlongConj.exists_smul_eq_of_isAbove R K L _ _ (hc V hV) (hc V' hV')
      refine ⟨τ.liftNormal Ω, trivial, Set.mem_iInter₂.2 fun x hx => ?_⟩
      have h1 : τ.liftNormal Ω x = algebraMap L Ω (τ ⟨x, hL x hx⟩) := τ.liftNormal_commutes Ω ⟨x, hL x hx⟩
      change τ.liftNormal Ω x ∈ V' ↔ x ∈ V
      rw [h1, ← ValuationSubring.mem_comap, ← hτ]
      exact ValuationSubring.smul_mem_pointwise_smul_iff (g := τ) (x := (⟨x, hL x hx⟩ : L))
        (S := V.comap (algebraMap L Ω)))
  obtain ⟨g, -, hg⟩ := key
  refine ⟨g, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := g.surjective y
  have := Set.mem_iInter.1 hg x
  exact (ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (x := x)).trans (Iff.symm this)

end GlobalTheory.ValConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCmPtFrPolyNeZero
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj GlobalTheory.LamT

namespace GlobalTheory.CMDetect

theorem exists_half_max {α : Type} (s : Set α) (f : α → ℝ) (C : ℝ) (hC : ∀ x ∈ s, f x ≤ C) {x₁ : α} (hx₁ : x₁ ∈ s)
    (hpos : 0 < f x₁) : ∃ z ∈ s, (∀ x ∈ s, f x ≤ 2 * f z) ∧ 0 < f z := by
  have hb : BddAbove (f '' s) := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  have hle : ∀ x ∈ s, f x ≤ sSup (f '' s) := fun x hx => le_csSup hb ⟨x, hx, rfl⟩
  have h1 := hle x₁ hx₁
  obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (s := f '' s) ⟨_, x₁, hx₁, rfl⟩
    (show sSup (f '' s) / 2 < sSup (f '' s) by linarith)
  exact ⟨z, hz, fun x hx => by linarith [hle x hx], by linarith⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_maj_lower (X : FD.DataX E r) (hr : 0 < r) {z : FD.Frame X.Ψ r} (hz : z ∈ X.dom) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ v ∈ X.L', v ≠ 0 → s ^ 2 ≤ ∑ τ, X.maj z τ (FD.Data.emb τ.1 v) := by
  have hnn : ∀ τ v, 0 ≤ X.maj z τ v := fun τ v => FD.MajorantConjugateTransfer.maj_nonneg X.toData hz τ v
  have hc : ∀ τ, X.c τ = X.k0 := fun τ => by
    unfold FD.Data.c
    rw [X.ξ0_abs τ]
    ring
  have hk := X.minWeight_pos
  have hN : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  have hla : 0 < X.firstMinimumSq z := Real.sqrt_pos.1 (AR.Up.ModeHalfC.first_minimum_pos X.toData hz (by
    by_contra h
    push Not at h
    have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      exact h
    rw [X.Λ_span] at h1
    have : (Pi.single ⟨0, hr⟩ (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E)) := Submodule.mem_top
    rw [h1, Submodule.mem_bot] at this
    have := congrFun this ⟨0, hr⟩
    simp at this))
  have hm : 0 < X.firstMinimumSq z / (X.k0 * (X.NC : ℝ) ^ 2) := by positivity
  refine ⟨Real.sqrt (min 1 (X.firstMinimumSq z / (X.k0 * (X.NC : ℝ) ^ 2))), Real.sqrt_pos.2 (lt_min one_pos hm),
    Real.sqrt_le_one.2 (min_le_left _ _), fun v hv hv0 => ?_⟩
  rw [Real.sq_sqrt (lt_min one_pos hm).le]
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj z τ (FD.Data.emb τ.1 v)} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, -, -, rfl⟩
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (by rw [hc]; exact hk.le) (hnn τ _)
  have hne : (X.NC : E) • v ≠ 0 := smul_ne_zero (by exact_mod_cast X.NC_pos.ne') hv0
  have h1 : X.firstMinimumSq z ≤ ∑ τ, X.c τ * X.maj z τ (FD.Data.emb τ.1 ((X.NC : E) • v)) :=
    csInf_le hb ⟨_, X.NC_sub v hv, hne, rfl⟩
  refine h1.trans (le_of_eq ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : FD.Data.emb τ.1 ((X.NC : E) • v) = (((X.NC : ℝ) : ℂ)) • FD.Data.emb τ.1 v := by
    funext a
    simp [FD.Data.emb]
  rw [e, FD.FlowMajorantFlags.maj_smul X.toData hz, hc]
  ring

theorem exists_cm_frame (X : FD.DataX E r) (Y : FD.Data E r) (hX : X.toData = Y) (hr : 0 < r) (la : FD.Wt Y.Ψ r)
    (P : FD.Frame Y.Ψ r → ℂ) (hP : Y.IsBddSec la P) {x₁ : FD.Frame Y.Ψ r} (hx₁ : x₁ ∈ Y.dom) (hne : P x₁ ≠ 0) :
    ∃ (La : ℝ) (x : FD.Frame Y.Ψ r) (lam : Fin r → Fin r → E), x ∈ Y.dom ∧ FD.LamBasis X La (hX ▸ x) lam ∧
      P x ≠ 0 := by
  subst hX
  obtain ⟨hS, C, hC⟩ := hP
  have hpos : 0 < X.pnorm la P x₁ := by
    have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), FD.dmin X.Gm x₁ τ i ≠ 0 := fun τ i h => by
      have := (hx₁ τ).2 i
      rw [h, Complex.zero_re, mul_zero] at this
      exact lt_irrefl _ this
    refine mul_pos (norm_pos_iff.2 hne) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos ?_ _)
    exact norm_pos_iff.2 (div_ne_zero (hd τ _) (hd τ _))
  obtain ⟨z, hz, hhalf, hzpos⟩ := exists_half_max X.dom (X.pnorm la P) C hC hx₁ hpos
  obtain ⟨s, hs0, hs1, hs⟩ := exists_maj_lower X hr hz
  obtain ⟨x, lam, hx, hB, hPx, -⟩ := Formalism.L2.Pj.FundamentalDomainD5.t41H_statement r X la P z s (max 1 (∑ τ, X.spread la τ)) hS hz
    hhalf hzpos (le_max_right _ _) (le_max_left _ _) hr hs0 hs1 hs
  exact ⟨_, x, lam, hx, hB, hPx⟩

theorem exists_good_cmPt_frPoly_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), IsUnf U → 0 < r → (∀ k, ∃ (Xx : FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), Xx.toData = U.X k ∧ 𝔄 ≠ 0 ∧ Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u}) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, F ≠ 0 → (∀ k, (U.X k).IsBddSec (laU U a n k) (rdU U F k)) → ∃ (z : CMPt Xo c) (La : ℝ), z.Good (Module.finrank ℚ E / 2) La ∧ ∀ G, IsFrPoly F z.y G → G ≠ 0 := by
  intro E _ _ _ H Dw l Xo c _ hstar r U hU hr hdat a n F hF hF0 hbdd
  classical
  have hinj := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ r
    (Formalism.L2.PjFree.Unf.ofPj U) ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) a n).2 F hF
  have hex : ∃ k, ∃ x ∈ (U.X k).dom, rdU U F k x ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (hinj h)
  obtain ⟨k, x₁, hx₁, hne₁⟩ := hex
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := hdat k
  obtain ⟨La, x, lam, hx, hB, hne⟩ := exists_cm_frame Xx (U.X k) hX hr _ _ (hbdd k) hx₁ hne₁
  obtain ⟨z, σ₁, hz, hzx⟩ := GlobalTheory.LamT.exists_good_cmPt_at_frame E H Dw l Xo c hstar r U hU hr k ⟨x, hx⟩ Xx hX 𝔄 h𝔄 hΛ
    La lam hB
  have hev : evR Xo c F (U.un k ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x ∈ (U.X k).dom then toC (evR Xo c F (U.un k ⟨x, h⟩)) else 0) = 0
    rw [dite_eq_left hx]
    exact h0
  exact ⟨z, La, hz, fun G hG =>
    (GlobalTheory.LamT.isFrPoly_equiv_and_ne_zero E H Dw l Xo c z.K z.y a n F hF G hG).2 _ σ₁ _ hzx hev⟩

end GlobalTheory.CMDetect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransform
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaParseval

theorem exists_lintegral_sq_eq_mul_setLIntegral_theta : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν := by
  intro F _ _ ψ hψ κ _ μ hμ ν hν 𝓕 h𝓕
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := _root_.GlobalTheory.RatVecDomain.exists_fundamentalDomain F κ μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := _root_.GlobalTheory.PeriodicIterated.lintegral_ratPair_fundamentalDomain_eq_iterated F κ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  refine ⟨(c₁ * μ 𝓕₁)⁻¹, fun Φ hΦ => ?_⟩
  have hm := _root_.GlobalTheory.ThetaTransformMeas.main F ψ hψ κ Φ hΦ
  have hG : @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) =>
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
  rw [hc _ hG (fun γ hγ w => by rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, _root_.GlobalTheory.ThetaRatInv.norm_thetaSum_schr_ratPair_add F ψ hψ κ Φ γ hγ w])]
  simp_rw [_root_.GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq F ψ hψ κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
  rw [lintegral_const_mul' _ _ htop, _root_.GlobalTheory.ThetaUnfold.unfold F κ μ hμ 𝓕₁ h𝓕₁ Φ hΦ, ← mul_assoc c₁, ← mul_assoc,
    ENNReal.inv_mul_cancel (mul_ne_zero hc0 h0) (ENNReal.mul_ne_top hctop htop), one_mul]

end GlobalTheory.ThetaParseval
end

