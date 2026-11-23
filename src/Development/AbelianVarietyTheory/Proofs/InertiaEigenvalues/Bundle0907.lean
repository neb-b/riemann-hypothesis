module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0904

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormMaxPowDividingConjugatePlace
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.ConjNormPow

theorem absNorm_comap_equiv {K : Type} [Field K] [NumberField K] (e : 𝓞 K ≃+* 𝓞 K)
    (I : Ideal (𝓞 K)) : Ideal.absNorm (I.comap e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv (I.comap e) I e
    (Ideal.map_comap_of_surjective _ e.surjective I).symm).toEquiv

theorem absNorm_maxPowDividing_conjPl : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (N : ℕ), Ideal.absNorm ((Formalism.L2.DIV.conjPl P).maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) = Ideal.absNorm (P.maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) := by
  intro D P N
  classical
  let σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingEquiv.ofRingHom Formalism.L2.DIV.starOHom Formalism.L2.DIV.starOHom
    (RingHom.ext fun a => Formalism.L2.DIV.starO_starO a) (RingHom.ext fun a => Formalism.L2.DIV.starO_starO a)
  have hc : (Formalism.L2.DIV.conjPl P).asIdeal = P.asIdeal.comap σ := rfl
  set J : Ideal (𝓞 D.host.E) := Ideal.span {((N : ℕ) : 𝓞 D.host.E)} with hJdef
  have hJ : J.comap σ = J := by
    rw [← Ideal.map_symm, hJdef, Ideal.map_span, Set.image_singleton, map_natCast]
  have hpow : ∀ k : ℕ, (P.asIdeal.comap σ) ^ k = (P.asIdeal ^ k).comap σ := by
    intro k
    rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  have hiff : ∀ k : ℕ, J ≤ (P.asIdeal.comap σ) ^ k ↔ J ≤ P.asIdeal ^ k := by
    intro k
    rw [hpow, ← hJ, Ideal.comap_le_comap_iff_of_surjective _ σ.surjective, hJ]
  have hcount : (Associates.mk (Formalism.L2.DIV.conjPl P).asIdeal).count (Associates.mk J).factors =
      (Associates.mk P.asIdeal).count (Associates.mk J).factors := by
    by_cases hJ0 : J = ⊥
    · rw [hJ0, ← Ideal.zero_eq_bot, Associates.mk_zero, Associates.factors_zero]
      simp only [Associates.count]
      split_ifs <;> rfl
    have hm : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr hJ0
    have key : ∀ (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (k : ℕ),
        k ≤ (Associates.mk Q.asIdeal).count (Associates.mk J).factors ↔ J ≤ Q.asIdeal ^ k := by
      intro Q k
      rw [← Associates.prime_pow_dvd_iff_le hm (Associates.irreducible_mk.mpr Q.irreducible),
        ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]
    apply le_antisymm
    · rw [key P, ← hiff, ← hc, ← key]
    · rw [key (Formalism.L2.DIV.conjPl P), hc, hiff, ← key]
  simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
  rw [hcount, hc, hpow, absNorm_comap_equiv]

end GlobalTheory.ConjNormPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsModHalfLatticeFinsetSum
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.DivPtFourier.Prod

theorem sum_idem {D : D7} {ι : Type} (s : Finset ι) (cs : ι → AE D)
    (hi : ∀ i ∈ s, cs i * cs i = cs i) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) :
    (∑ i ∈ s, cs i) * (∑ i ∈ s, cs i) = ∑ i ∈ s, cs i := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi' => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => ho i hi' j hj (Ne.symm hji))
    (fun h => absurd hi' h), hi i hi']

theorem sum_orth {D : D7} {ι : Type} (s : Finset ι) (cs : ι → AE D) (i : ι) (hi : i ∉ s)
    (ho : ∀ j ∈ s, cs i * cs j = 0) : cs i * (∑ j ∈ s, cs j) = 0 := by
  rw [Finset.mul_sum]; exact Finset.sum_eq_zero ho

set_option maxHeartbeats 800000 in
theorem card_add {D : D7} {S T : HSp D} (Λ : AddSubgroup (WO S T))
    (hst : ∀ c : AE D, c * c = c → ∀ u ∈ Λ, c • u ∈ Λ) (c₁ c₂ : AE D) (h₁ : c₁ * c₁ = c₁) (h₂ : c₂ * c₂ = c₂)
    (h₁₂ : c₁ * c₂ = 0) (N : ℕ) :
    Nat.card (DQ Λ (c₁ + c₂) N) = Nat.card (DQ Λ c₁ N) * Nat.card (DQ Λ c₂ N) := by
  have h₂₁ : c₂ * c₁ = 0 := by rw [mul_comm]; exact h₁₂
  have orth : ∀ (a b : AE D), a * b = 0 → ∀ x : WO S T, b • x = x → a • x = 0 := by
    intro a b hab x hx
    rw [← hx, smul_smul, hab, zero_smul]
  have gmem : ∀ (c : AE D), c * c = c → ∀ y ∈ divPts Λ (c₁ + c₂) N, c • y ∈ divPts Λ c N := by
    intro c hc y hy
    refine ⟨by rw [smul_smul, hc], ?_⟩
    rw [smul_comm]; exact hst c hc _ hy.2
  let g : ∀ (c : AE D), c * c = c → ↥(divPts Λ (c₁ + c₂) N) →+ ↥(divPts Λ c N) := fun c hc =>
    { toFun := fun y => ⟨c • (y : WO S T), gmem c hc _ y.2⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun x y => Subtype.ext (smul_add _ _ _) }
  let φ : ↥(divPts Λ (c₁ + c₂) N) →+ DQ Λ c₁ N × DQ Λ c₂ N :=
    ((QuotientAddGroup.mk' _).comp (g c₁ h₁)).prod ((QuotientAddGroup.mk' _).comp (g c₂ h₂))
  have hker : ∀ (c : AE D) (hc : c * c = c) (y : ↥(divPts Λ (c₁ + c₂) N)),
      (QuotientAddGroup.mk' ((Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (divPts Λ c N))) (g c hc y) = 0 ↔
        c • (y : WO S T) ∈ Λ := by
    intro c hc y
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, (GlobalTheory.PlaceModel.mem_half S T).2 (gmem c hc _ y.2).1⟩⟩
  have hle : (Λ ⊓ GlobalTheory.PlaceModel.half S T (c₁ + c₂)).addSubgroupOf (divPts Λ (c₁ + c₂) N) ≤ φ.ker := by
    intro y hy
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    rw [AddMonoidHom.mem_ker]
    refine Prod.ext ?_ ?_
    · exact (hker c₁ h₁ y).2 (hst c₁ h₁ _ hy.1)
    · exact (hker c₂ h₂ y).2 (hst c₂ h₂ _ hy.1)
  let ψ' := QuotientAddGroup.lift _ φ hle
  have hbij : Function.Bijective ψ' := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H y =>
      have e := hq
      change φ y = 0 at e
      have e1 := (hker c₁ h₁ y).1 (congrArg Prod.fst e)
      have e2 := (hker c₂ h₂ y).1 (congrArg Prod.snd e)
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      have hy : (c₁ + c₂) • (y : WO S T) = y := y.2.1
      refine ⟨?_, (GlobalTheory.PlaceModel.mem_half S T).2 hy⟩
      rw [← hy, add_smul]; exact Λ.add_mem e1 e2
    · rintro ⟨q₁, q₂⟩
      induction q₁ using QuotientAddGroup.induction_on with
      | H y₁ =>
      induction q₂ using QuotientAddGroup.induction_on with
      | H y₂ =>
      have a₁ : c₁ • (y₁ : WO S T) = y₁ := y₁.2.1
      have a₂ : c₂ • (y₂ : WO S T) = y₂ := y₂.2.1
      have b₁ : c₁ • (y₂ : WO S T) = 0 := orth c₁ c₂ h₁₂ _ a₂
      have b₂ : c₂ • (y₁ : WO S T) = 0 := orth c₂ c₁ h₂₁ _ a₁
      have hmem : (y₁ : WO S T) + y₂ ∈ divPts Λ (c₁ + c₂) N := by
        refine ⟨?_, ?_⟩
        · rw [add_smul, smul_add, smul_add, a₁, a₂, b₁, b₂, add_zero, zero_add]
        · rw [nsmul_add]; exact Λ.add_mem y₁.2.2 y₂.2.2
      refine ⟨QuotientAddGroup.mk ⟨_, hmem⟩, ?_⟩
      change φ ⟨_, hmem⟩ = _
      refine Prod.ext ?_ ?_
      · change QuotientAddGroup.mk (g c₁ h₁ ⟨_, hmem⟩) = QuotientAddGroup.mk y₁
        congr 1; apply Subtype.ext; change c₁ • ((y₁ : WO S T) + y₂) = y₁
        rw [smul_add, a₁, b₁, add_zero]
      · change QuotientAddGroup.mk (g c₂ h₂ ⟨_, hmem⟩) = QuotientAddGroup.mk y₂
        congr 1; apply Subtype.ext; change c₂ • ((y₁ : WO S T) + y₂) = y₂
        rw [smul_add, a₂, b₂, zero_add]
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod]

theorem card_zero {D : D7} {S T : HSp D} (Λ : AddSubgroup (WO S T)) (N : ℕ) :
    Nat.card (DQ Λ (0 : AE D) N) = 1 := by
  haveI : Subsingleton (DQ Λ (0 : AE D) N) := by
    constructor
    intro q₁ q₂
    induction q₁ using QuotientAddGroup.induction_on with
    | H y₁ =>
    induction q₂ using QuotientAddGroup.induction_on with
    | H y₂ =>
    have e₁ : y₁ = 0 := Subtype.ext (by rw [← y₁.2.1, zero_smul]; rfl)
    have e₂ : y₂ = 0 := Subtype.ext (by rw [← y₂.2.1, zero_smul]; rfl)
    rw [e₁, e₂]
  exact Nat.card_of_subsingleton (0 : DQ Λ (0 : AE D) N)

end GlobalTheory.DivPtFourier.Prod

theorem GlobalTheory.DivPtFourier.card_DQ_sum : ∀ {D : D7} {S T : HSp D} (Λ : AddSubgroup (WO S T)), (∀ c : AE D, c * c = c → ∀ u ∈ Λ, c • u ∈ Λ) → ∀ {ι : Type} (s : Finset ι) (cs : ι → AE D), (∀ i ∈ s, cs i * cs i = cs i) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) → ∀ N : ℕ, Nat.card (GlobalTheory.DivPtFourier.DQ Λ (∑ i ∈ s, cs i) N) = ∏ i ∈ s, Nat.card (GlobalTheory.DivPtFourier.DQ Λ (cs i) N) := by
  intro D S T Λ hst ι s cs hi ho N
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.DivPtFourier.Prod.card_zero Λ N
  | insert i s his ih =>
    have hi' : ∀ j ∈ s, cs j * cs j = cs j := fun j hj => hi j (Finset.mem_insert_of_mem hj)
    have ho' : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → cs j * cs k = 0 := fun j hj k hk hjk =>
      ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    rw [Finset.sum_insert his, Finset.prod_insert his,
      GlobalTheory.DivPtFourier.Prod.card_add Λ hst _ _ (hi i (Finset.mem_insert_self i s))
        (GlobalTheory.DivPtFourier.Prod.sum_idem s cs hi' ho')
        (GlobalTheory.DivPtFourier.Prod.sum_orth s cs i his fun j hj =>
          ho i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) (fun h => his (h ▸ hj))),
      ih hi' ho']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsSplitPlaceLocalMatrices
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.DivPtLocalCard

open GlobalTheory.Core.Rk.SWQ

variable {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

private lemma selfDual_isFullLattice (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

def phi (h : w.under (𝓞 D.host.F) = q) {m n : ℕ} (B : Matrix (Fin m) (Fin m) (w.adicCompletion D.host.E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion D.host.E)) :
    Matrix (Fin m) (Fin n) (AE D) →+ Matrix (Fin m) (Fin n) (w.adicCompletion D.host.E) :=
  AddMonoidHom.mk' (fun y => B * y.map (cw h) * A) fun y y' => by
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem phi_apply (h : w.under (𝓞 D.host.F) = q) {m n : ℕ} (B : Matrix (Fin m) (Fin m) (w.adicCompletion D.host.E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion D.host.E)) (y : Matrix (Fin m) (Fin n) (AE D)) :
    phi h B A y = B * y.map (cw h) * A := rfl

theorem eq_iota_cw {h : w.under (𝓞 D.host.F) = q} {ι : w.adicCompletion D.host.E →+ AE D}
    (hι : GlobalTheory.DivPtLocal.IsIotaAt h ι) {x : AE D} (hx : ι 1 * x = x) : x = ι (cw h x) := by
  obtain ⟨-, -, -, -, h4, -, -, -⟩ := hι
  have := h4 x 1
  rw [mul_one] at this
  rw [← this, mul_comm, hx]

theorem gl_cancel {k : Type} [Field k] {m n : ℕ} (b : GL (Fin m) k) (a : GL (Fin n) k) (Y : Matrix (Fin m) (Fin n) k) :
    b.1 * ((b⁻¹).1 * Y * a.1) * (a⁻¹).1 = Y := by
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc b.1, Units.mul_inv, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem gl_cancel' {k : Type} [Field k] {m n : ℕ} (b : GL (Fin m) k) (a : GL (Fin n) k) (Y : Matrix (Fin m) (Fin n) k) :
    (b⁻¹).1 * (b.1 * Y * (a⁻¹).1) * a.1 = Y := by
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (b⁻¹).1, Units.inv_mul, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.DivPtLocalCard


set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.Rk.SWQ in
theorem GlobalTheory.DivPtLocalCard.card_DQ_eq : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) → ∀ ι : P.adicCompletion D.host.E →+ AE D, GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) (ι 1) N) = Nat.card (GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) := by
  intro D S T ΛS ΛT hS hT P hs ι hι N hN
  obtain ⟨e, ⟨⟨a, ha, -⟩, -⟩, -, -⟩ := GlobalTheory.LFun.SplitChart.exists_isSplitChart (GlobalTheory.AdelicU.isCMExt_host D)
    (GlobalTheory.Doubling.isHermND_gram S) hS.1.fg (Submodule.IsFullLattice.span_eq_top (self := GlobalTheory.DivPtLocalCard.selfDual_isFullLattice S ΛS hS)) (rfl : P.under (𝓞 D.host.F) = _) hs
    (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hS _)
  obtain ⟨b, hb⟩ := GlobalTheory.Core.Rk.SWQ.LatHalf.mem_latO_iff_intM D _ P rfl hs S T ΛS ΛT hS hT a ha
  have hP : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := rfl
  have hι' := hι
  obtain ⟨-, h1, h2, h3, h4, -, -, -⟩ := hι'
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (fun v => v = P.under (𝓞 D.host.F)) with hΛ
  set c := ι 1 with hc
  set Φ := GlobalTheory.DivPtLocalCard.phi hP (b⁻¹).1 a.1 with hΦ
  have hent : ∀ y : WO S T, c • y = y → ∀ i j, y i j = ι (cw hP (y i j)) := fun y hy i j =>
    GlobalTheory.DivPtLocalCard.eq_iota_cw hι (by simpa [Matrix.smul_apply] using congrFun (congrFun hy i) j)
  have hoff : ∀ y : WO S T, c • y = y → offM (P.under (𝓞 D.host.F)) y = 0 := by
    intro y hy
    ext i j
    simp only [offM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [hent y hy i j, h3, sub_self]
  have hcA : ∀ y : WO S T, c • y = y → ∀ i j, cw hP (cA D (y i j)) = 0 := by
    intro y hy i j
    rw [hent y hy i j]
    exact h2 _
  have hmem : ∀ y : WO S T, c • y = y → (y ∈ Λ ↔ GlobalTheory.Core.Rk.SWQ.IntM (Φ y)) := fun y hy => hb y (hoff y hy) (hcA y hy)
  have hInt : ∀ Z, GlobalTheory.Core.Rk.SWQ.IntM Z ↔ Z ∈ GlobalTheory.DivPtLocal.locInt P T.rank S.rank := fun Z => Iff.rfl
  have hIntN : ∀ Z, GlobalTheory.Core.Rk.SWQ.IntM (N • Z) ↔ Z ∈ GlobalTheory.DivPtLocal.locDiv P N T.rank S.rank := by
    intro Z
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [Matrix.smul_apply, nsmul_eq_mul]
    rfl
  have hcN : ∀ y : WO S T, c • y = y → c • (N • y) = N • y := fun y hy => by rw [smul_comm, hy]
  let Ψ : Matrix (Fin T.rank) (Fin S.rank) (P.adicCompletion D.host.E) → WO S T :=
    fun Z => (b.1 * Z * (a⁻¹).1).map ι
  have hΨc : ∀ Z, c • Ψ Z = Ψ Z := by
    intro Z
    ext i j
    simp only [Ψ, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, hc, h4, h1, one_mul]
  have hΦΨ : ∀ Z, Φ (Ψ Z) = Z := by
    intro Z
    rw [hΦ, GlobalTheory.DivPtLocalCard.phi_apply]
    have : (Ψ Z).map (cw hP) = b.1 * Z * (a⁻¹).1 := by
      ext i j
      simp only [Ψ, Matrix.map_apply, h1]
    rw [this, GlobalTheory.DivPtLocalCard.gl_cancel']
  have hinj : ∀ y y' : WO S T, c • y = y → c • y' = y' → Φ y = Φ y' → y = y' := by
    intro y y' hy hy' H
    have H' : y.map (cw hP) = y'.map (cw hP) := by
      rw [← GlobalTheory.DivPtLocalCard.gl_cancel b a (y.map (cw hP)), ← GlobalTheory.DivPtLocalCard.gl_cancel b a (y'.map (cw hP))]
      exact congrArg (fun M => b.1 * M * (a⁻¹).1) H
    ext i j
    rw [hent y hy i j, hent y' hy' i j]
    exact congrArg ι (congrFun (congrFun H' i) j)
  have hdiv : ∀ y : ↥(GlobalTheory.DivPtFourier.divPts Λ c N), Φ y ∈ GlobalTheory.DivPtLocal.locDiv P N T.rank S.rank := by
    rintro ⟨y, hy1, hy2⟩
    rw [← hIntN, ← map_nsmul]
    exact (hmem _ (hcN y hy1)).1 hy2
  let f : ↥(GlobalTheory.DivPtFourier.divPts Λ c N) →+ GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank :=
    (QuotientAddGroup.mk' _).comp ((Φ.comp (GlobalTheory.DivPtFourier.divPts Λ c N).subtype).codRestrict _ hdiv)
  have hsurj : Function.Surjective f := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H Z =>
    have hy2 : N • Ψ Z ∈ Λ := by
      rw [hmem _ (hcN _ (hΨc Z)), map_nsmul, hΦΨ, hIntN]
      exact Z.2
    refine ⟨⟨Ψ Z, hΨc Z, hy2⟩, ?_⟩
    change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
    congr 1
    exact Subtype.ext (hΦΨ Z)
  have hker : f.ker = (Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (GlobalTheory.DivPtFourier.divPts Λ c N) := by
    ext ⟨y, hy1, hy2⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf]
    change (QuotientAddGroup.mk _ : GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    change Φ y ∈ GlobalTheory.DivPtLocal.locInt P T.rank S.rank ↔ y ∈ Λ ∧ y ∈ GlobalTheory.PlaceModel.half S T c
    rw [← hInt, ← hmem y hy1]
    exact ⟨fun h => ⟨h, hy1⟩, fun h => h.1⟩
  exact Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj)).toEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactHoweDualityIsotypicMemOfStableSubspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.HoweGen

theorem cvType_mem_of_stable : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (U : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank)), (∀ u ∈ GinfC (Vc D i), ∀ P ∈ U, ∀ P' : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → P' ∈ U) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → P ∈ U → P' ∈ U) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W), R.ioP i x w ∈ U) → ∀ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → ∀ w, φ w ∈ U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t U hstab hlie hio φ hφ w
  have hadd : ∀ a b : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t (a + b) = R.ptP i t a + R.ptP i t b := by
    intro a b; unfold RealDat.ptP; simp
  have hsmul : ∀ (c : ℂ) (a : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t (c • a) = c • R.ptP i t a := by
    intro c a; unfold RealDat.ptP; simp
  have hzero : R.ptP i t 0 = 0 := by simpa using hsmul 0 0
  let M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) :=
    { carrier := {ψ | (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) ∧ ∀ w, ψ w ∈ U}
      add_mem' := by
        rintro ψ₁ ψ₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.add_apply, hadd, h₁ u hu w', h₂ u hu w', map_add (f := _)]
        · simp only [LinearMap.add_apply]; exact U.add_mem (h₁' w) (h₂' w)
      zero_mem' := by
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.zero_apply, hzero, map_zero]
        · simp only [LinearMap.zero_apply]; exact U.zero_mem
      smul_mem' := by
        rintro c ψ ⟨h₁, h₁'⟩
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.smul_apply, hsmul, h₁ u hu w', map_smul]
        · simp only [LinearMap.smul_apply]; exact U.smul_mem c (h₁' w) }
  have hioM : ∀ x, R.ioP i x ∈ M := fun x =>
    ⟨fun u hu w' => ((hG.core.thP.ioP i t).1 u hu x w').symm, fun w => hio x w⟩
  have hne : M ≠ ⊥ := by
    obtain ⟨v, w₀, -, -, hv⟩ := (hG.core.thP.ioP i t).2.2
    intro hM
    have h0 : R.ioP i (PiTensorProduct.tprod ℂ v) ∈ (⊥ : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)) := hM ▸ hioM _
    rw [Submodule.mem_bot] at h0
    apply GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) i
    rw [← hv, h0]
    rfl
  have hφM : φ ∈ M := _root_.GlobalTheory.HoweIrrCompact.howe_irr D G Pl0 T A Ks R F hG hF i t M (fun ψ hψ => hψ.1)
    (fun ψ hψ τ Y hY ψ' hd => ⟨_root_.GlobalTheory.LieEquivFock.lie_equivariant D G Pl0 T A Ks R F hG hF i t τ Y hY ψ ψ' hψ.1 hd,
      fun w => hlie τ Y hY (ψ w) (ψ' w) (fun z => hd w z) (hψ.2 w)⟩) hne φ hφ
  exact hφM.2 w

end GlobalTheory.HoweGen
end

