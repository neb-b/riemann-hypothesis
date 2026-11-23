module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0714
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalUnitaryDoubledLagrangianFrameWitt
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurL2PairingRealFiniteTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem schur_trPair_real_fin : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x y : (R.HW i (sg0 D A)).H), ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL i hLP v x y u hu γ hγ
  have hθ : IsInfFam R.θ := hL.models.inf
  obtain ⟨-, hr, -⟩ := hL.models.HW i (sg0 D A)
  have hHaar : (R.νW i).IsHaarMeasure := (hL.models.νW i).1.1
  have hfd : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hL.models.νW i).2
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e x) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ x
      exact this)
  have hTm' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  set J' : Set (GA D (Wc D i)) := {k | k ∈ levW R i ∧ γ⁻¹ * k * γ ∈ levW R i} with hJ'
  have hT1 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e x) :=
    ⟨hTm.aut, hTm.cusp, fun w k hk g => by rw [hTm.lev w k hk.1 g, hLP.2.1 k hk.1], hTm.equiv, hTm.cont⟩
  have hT2 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := by
    have hT3 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e y) :=
      ⟨hTm'.aut, hTm'.cusp, fun w k hk g => by rw [hTm'.lev w k hk.1 g, hLP.2.1 k hk.1], hTm'.equiv, hTm'.cont⟩
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT3 (fun k hk => ?_) (fun w k hk g => ?_)
    · rw [Finset.mem_singleton] at hk
      exact hk ▸ hγ
    · simp only [heckeLin_apply, Finset.sum_singleton, one_mul]
      have e : g * k * γ = g * γ * (γ⁻¹ * k * γ) := by group
      rw [e, hTm'.lev w _ hk.2 (g * γ), hLP.2.1 _ hk.2, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.MultFinite.schurMult (θ := R.θ) (M := R.MW i (sg0 D A)) (J := J') (χ := fun _ => 1) hP
    (R.νW i) (R.fdW i) hθ hHaar hfd _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT1) _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT2)
  have hip := ipM_spec _ _ _ _ _ ⟨c, hc⟩
  obtain ⟨v', hv', hmove⟩ := GlobalTheory.RealPointMove.translate_eq_move D R.θ hθ (Wc D i) _ (R.MW i (sg0 D A)) J' (fun _ => 1) _ hT2
    u hu (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))
  have htr : trPair R i γ x y = dimProd A i * ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e x)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := rfl
  have hint : ∀ z, star (val R i v x z) * val R i v y (z * (u * γ)) =
      star ((R.HW i (sg0 D A)).e x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) z) *
        heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y) v' z := fun z => by
    rw [← hmove z]
    simp [val, heckeOn, postOn_apply, heckeLin_apply, mul_assoc]
  simp_rw [hint]
  rw [(hip (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) v').2, htr, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [hv' ρ]

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.ChiExtend

theorem placesOver_finite' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem maximalIdeal_le_comap {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) {O₀ O₁ : Type}
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[p] O₀] [Module.Finite ℤ_[p] O₀]
    [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra ℤ_[q] O₁] [Module.Finite ℤ_[q] O₁]
    (φ : O₀ →+* O₁) (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') :
    IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁) := by
  subst h
  have hc : φ.comp (algebraMap ℤ_[p] O₀) = algebraMap ℤ_[p] O₁ := by
    ext z
    exact hφ z z HEq.rfl
  haveI : (Ideal.comap φ (IsLocalRing.maximalIdeal O₁)).IsPrime := Ideal.comap_isPrime _ _
  have h1 : (Ideal.comap (algebraMap ℤ_[p] O₀) (Ideal.comap φ (IsLocalRing.maximalIdeal O₁))).IsMaximal := by
    rw [Ideal.comap_comap, hc]
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[p])
      (IsLocalRing.maximalIdeal O₁)
  have h2 := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := ℤ_[p]) (Ideal.comap φ (IsLocalRing.maximalIdeal O₁)) h1
  rw [IsLocalRing.eq_maximalIdeal h2]

theorem continuous_of_le_comap {O₀ O₁ : Type} [CommRing O₀] [IsLocalRing O₀] [TopologicalSpace O₀]
    [IsTopologicalRing O₀] [CommRing O₁] [IsLocalRing O₁] [TopologicalSpace O₁] [IsTopologicalRing O₁]
    (h₀ : IsAdic (IsLocalRing.maximalIdeal O₀)) (h₁ : IsAdic (IsLocalRing.maximalIdeal O₁))
    (φ : O₀ →+* O₁) (hφ : IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁)) :
    Continuous φ := by
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 h₁).2 s hs
  have ho := (isAdic_iff.1 h₀).1 n
  refine Filter.mem_map.2 <| Filter.mem_of_superset (ho.mem_nhds (Ideal.zero_mem _)) fun x hx => hn ?_
  exact (Ideal.pow_right_mono hφ n |>.trans (Ideal.le_comap_pow φ n)) hx

theorem cyc_heq (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q)
    (σ : G F Ω) : HEq ((cycZ F Ω p σ : ℤ_[p]ˣ) : ℤ_[p]) ((cycZ F Ω q σ : ℤ_[q]ˣ) : ℤ_[q]) := by
  subst h
  rfl

end GlobalTheory.ChiExtend

namespace GlobalTheory.ChiExtend

theorem iotaO_injective {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    Function.Injective (iotaO N A i) := by
  show Function.Injective (((A.iotaQC i).toRingHom.comp (A.iotaQ i)).comp (algebraMap (N.O i) (FractionRing (N.O i))))
  simp only [RingHom.coe_comp]
  exact (A.iotaQC i).injective.comp ((A.iotaQ i).injective.comp (IsFractionRing.injective _ _))

theorem eq_of_dense {X O : Type*} [TopologicalSpace X] [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (h : IsAdic (IsLocalRing.maximalIdeal O)) (hH : IsHausdorff (IsLocalRing.maximalIdeal O) O)
    {f g : X → O} (hf : Continuous f) (hg : Continuous g) {s : Set X} (hs : Dense s) (he : ∀ x ∈ s, f x = g x) :
    f = g := by
  funext x
  rw [← sub_eq_zero]
  apply hH.haus' (f x - g x)
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  have hcl : IsClosed ((fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O)) := by
    refine IsClosed.preimage (hf.sub hg) ?_
    exact AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ n).toAddSubgroup
      ((isAdic_iff.1 h).1 n)
  have hsub : s ⊆ (fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
    intro y hy
    simp only [Set.mem_preimage, he y hy, sub_self, SetLike.mem_coe]
    exact Ideal.zero_mem _
  have := closure_minimal hsub hcl
  rw [hs.closure_eq] at this
  exact this (Set.mem_univ x)

end GlobalTheory.ChiExtend

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenConductor
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.ExtTheta

variable {D : D7}

theorem isoTyp_congr {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) {S S' : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (h : NG.IsoRep S S') : NG.isoTyp ρ S = NG.isoTyp ρ S' := by
  unfold NG.isoTyp
  congr 1
  ext T
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h.symm hS).trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩⟩

variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}



end GlobalTheory.ExtTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.ExtRing

theorem qCast_trans {a p q : ℕ} [Fact a.Prime] [Fact p.Prime] [Fact q.Prime] (ι : Qbar a ≃+* ℂ) (h₀ : a = p)
    (h₁ : a = q) (hl : p = q) : qCast h₁ ι = qCast hl (qCast h₀ ι) := by
  subst h₀; subst hl; rfl

theorem exists_gens {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ s : Finset (Qbar l), ∀ x, ι x ∈ Submodule.span ℚ_[l] (s : Set (Qbar l)) := by
  classical
  obtain ⟨K, hK, hfd, -⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι hι
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℚ_[l] K).FG)
  refine ⟨t.image Subtype.val, fun x => ?_⟩
  have hx : (⟨ι x, (hK _).2 ⟨x, rfl⟩⟩ : K) ∈ Submodule.span ℚ_[l] (t : Set K) := ht ▸ Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := K.val.toLinearMap) hx
  rw [← Submodule.span_image] at this
  rw [Finset.coe_image]
  exact this

theorem exists_ringHom {l₀ l₁ : ℕ} [Fact l₀.Prime] [Fact l₁.Prime] (hl : l₀ = l₁)
    {O₀ : Type} [cr₀ : CommRing O₀] [dm₀ : IsDomain O₀] [dv₀ : IsDiscreteValuationRing O₀] [al₀ : Algebra ℤ_[l₀] O₀]
    [fi₀ : Module.Finite ℤ_[l₀] O₀]
    {O₁ : Type} [cr₁ : CommRing O₁] [dm₁ : IsDomain O₁] [dv₁ : IsDiscreteValuationRing O₁] [al₁ : Algebra ℤ_[l₁] O₁]
    [fi₁ : Module.Finite ℤ_[l₁] O₁]
    (ι₀ : FractionRing O₀ →+* Qbar l₀)
    (hι₀ : ∀ z : ℤ_[l₀], ι₀ (algebraMap O₀ (FractionRing O₀) (algebraMap ℤ_[l₀] O₀ z)) =
      algebraMap ℚ_[l₀] (Qbar l₀) (z : ℚ_[l₀]))
    (ι₁ : FractionRing O₁ →+* Qbar l₁)
    (hι₁ : ∀ z : ℤ_[l₁], ι₁ (algebraMap O₁ (FractionRing O₁) (algebraMap ℤ_[l₁] O₁ z)) =
      algebraMap ℚ_[l₁] (Qbar l₁) (z : ℚ_[l₁]))
    (c₀ : Qbar l₀ ≃+* ℂ) (c₁ : Qbar l₁ ≃+* ℂ) (hc : c₁ = qCast hl c₀) (s : Set (Qbar l₀))
    (hs : ∀ x, ι₀ x ∈ Submodule.span ℚ_[l₀] s) (hs₁ : ∀ y ∈ s, ∃ x, c₁ (ι₁ x) = c₀ y) :
    ∃ φ : O₀ →+* O₁, (∀ z, c₁ (ι₁ (algebraMap O₁ _ (φ z))) = c₀ (ι₀ (algebraMap O₀ _ z))) ∧
      ∀ (z : ℤ_[l₀]) (z' : ℤ_[l₁]), HEq z z' → φ (algebraMap ℤ_[l₀] O₀ z) = algebraMap ℤ_[l₁] O₁ z' := by
  subst hl
  have hc' : ∀ x, c₁ x = c₀ x := fun x => by rw [hc]; rfl
  simp only [hc'] at hs₁ ⊢
  obtain ⟨K₀, hK₀, -, hn₀⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₀ hι₀
  obtain ⟨K₁, hK₁, -, hn₁⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₁ hι₁
  have hsK : s ⊆ (K₁ : Set (Qbar l₀)) := by
    intro y hy
    obtain ⟨x, hx⟩ := hs₁ y hy
    exact (hK₁ y).2 ⟨x, c₀.injective hx⟩
  have hspan : Submodule.span ℚ_[l₀] s ≤ K₁.toSubalgebra.toSubmodule := Submodule.span_le.2 hsK
  let f₀ : O₀ →+* Qbar l₀ := ι₀.comp (algebraMap O₀ (FractionRing O₀))
  let f₁ : O₁ →+* Qbar l₀ := ι₁.comp (algebraMap O₁ (FractionRing O₁))
  have hf₁ : Function.Injective f₁ := ι₁.injective.comp (IsFractionRing.injective O₁ (FractionRing O₁))
  have hrange : ∀ z, f₀ z ∈ f₁.range := by
    intro z
    have h1 : f₀ z ∈ K₁ := hspan (hs _)
    obtain ⟨y, hy⟩ := (hK₁ _).1 h1
    have hle : ‖ι₀ (algebraMap O₀ (FractionRing O₀) z)‖ ≤ 1 := (hn₀ _).2 ⟨z, rfl⟩
    have hy1 : ‖ι₁ y‖ ≤ 1 := by rw [hy]; exact hle
    obtain ⟨u, rfl⟩ := (hn₁ y).1 hy1
    exact ⟨u, hy⟩
  let e₁ : O₁ ≃+* f₁.range := RingEquiv.ofBijective f₁.rangeRestrict
    ⟨fun a b h => hf₁ (congrArg Subtype.val h), f₁.rangeRestrict_surjective⟩
  let φ : O₀ →+* O₁ := e₁.symm.toRingHom.comp (f₀.codRestrict f₁.range hrange)
  have hφ : ∀ z, f₁ (φ z) = f₀ z := by
    intro z
    have : e₁ (φ z) = f₀.codRestrict f₁.range hrange z := e₁.apply_symm_apply _
    exact congrArg Subtype.val this
  refine ⟨φ, fun z => congrArg c₀ (hφ z), fun z z' hzz => ?_⟩
  cases eq_of_heq hzz
  apply hf₁
  rw [hφ]
  change ι₀ _ = ι₁ _
  rw [hι₀, hι₁]

end GlobalTheory.CoefDuty.ExtRing

end

end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenUnitary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.EigPlace

theorem finite_and_mem (hstd : HeckeStdPlain) {D : D7} {M : MtFam D} (HT : HeckeTied D M) (av : AVTied D M)
    (T : NormalizedLocalCompatibility D M) (i : D.nd.Loc) (x : D.nd.X i) (Q : Finset (PlE D.host)) (hQ : D.nd.Q i = Q) :
    (EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q).Finite ∧
      ptSys D i x ∈ EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q := by
  subst hQ
  have hi : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.EigFinite.eigSet_finite hstd D _ _ _ _ _ (badPl D i) ?_ ?_
    · exact hypOutside_transport (D.nd.mu_w i) rfl (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ _ (HT.J_hyp i)
    · intro v k s hg hc
      rw [T.Q_eq _ _ i hi] at hg
      exact genOutBad_of T _ _ i hi v k s hg hc
  · rw [D.nd.w_l i]
    exact GlobalTheory.FitHecke.mt_transport M (fun μ j m => ptSys D i x ∈ EigSet m (D.nd.l i) (D.nd.Q i)) (D.nd.mu_w i) rfl
      (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ (GlobalTheory.PointEigen.ptSys_mem_eigSet D M av i x)


end GlobalTheory.EigPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelEisensteinDoubledThetaTermsEqLagrangianInt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLagTerms

variable {D : D7}

theorem rat_of_mem (V : HSp D) (γ : GA D V) (h : γ ∈ GQ V) :
    ∃ g₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = g₀.map (incA D) := by
  obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h)
  exact ⟨g.1, (congrArg Units.val hg).symm⟩

theorem integral_eq {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)} {𝓗 : Set (GA D V)}
    {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ}
    (h₁ : IsThetaFunO ψ V W f₁) (h₂ : IsThetaFunO ψ V W f₂) (ν : Measure (Mx D V.rank W.rank))
    (𝓖' : Set (Mx D V.rank W.rank)) (hν : IsCovolOne (ratL V W) ν 𝓖') (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (hγ : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) (Y : Lag W)
    (hY : IsLagFrame W Y (frameOf W g₀)) :
    ∫ y in 𝓖', GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) ∂ν =
      lagTerm μ 𝓕 (frameOf W g₀) f₁ f₂ := by
  have hψ : ∀ x, ‖ψ x‖ = 1 := hS.weil.std.1.2.1
  simp_rw [_root_.GlobalTheory.SWLagTerms.dbl_actO_lagr D V W f₁ f₂ γ g₀ hγ]
  unfold lagTerm
  exact _root_.GlobalTheory.SWChangeVar.integral_adjO_eq D V W ν 𝓖' μ 𝓕 hν hS.covol
    (fun u => f₁ (ratMul (frameOf W g₀).1 u) * star (f₂ (ratMul (frameOf W g₀).2 u)))
    (fun c u => GlobalTheory.RawLift.Model.integrand_periodic hψ hY h₁ h₂ c u)

theorem classes (W : HSp D) :
    ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q,
      ∃ g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E,
        Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) ((q.out : GQ (GlobalTheory.Doubling.dblSp W)) : GA D (GlobalTheory.Doubling.dblSp W)) =
          g₀.map (incA D) ∧ IsLagFrame W (e q) (frameOf W g₀) := by
  classical
  have hg : ∀ γ : GQ (GlobalTheory.Doubling.dblSp W), ∃ g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E,
      Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) (γ : GA D (GlobalTheory.Doubling.dblSp W)) = g₀.map (incA D) :=
    fun γ => rat_of_mem (GlobalTheory.Doubling.dblSp W) γ γ.2
  choose g₀ hg₀ using hg
  have hY : ∀ γ : GQ (GlobalTheory.Doubling.dblSp W), ∃ Y : Lag W, IsLagFrame W Y (frameOf W (g₀ γ)) :=
    fun γ => _root_.GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf D W γ (g₀ γ) (hg₀ γ)
  choose Y hY using hY
  have key : ∀ a b : GQ (GlobalTheory.Doubling.dblSp W), Y a = Y b ↔
      ((b : GA D (GlobalTheory.Doubling.dblSp W)) * (a : GA D (GlobalTheory.Doubling.dblSp W))⁻¹ ∈ GlobalTheory.Doubling.siegel W) :=
    fun a b => _root_.GlobalTheory.SWLagSame.sameClass D W a b (g₀ a) (g₀ b) (hg₀ a) (hg₀ b) (Y a) (Y b) (hY a) (hY b)
  let f : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) → Lag W :=
    Quotient.lift Y (fun a b hab => (key a b).2 (by
      have := QuotientGroup.rightRel_apply.1 hab
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this))
  have hf : ∀ a, f (Quotient.mk _ a) = Y a := fun a => rfl
  have inj : Function.Injective f := by
    intro p q hpq
    induction p using Quotient.inductionOn
    induction q using Quotient.inductionOn
    rename_i a b
    rw [hf, hf] at hpq
    apply Quotient.sound
    refine QuotientGroup.rightRel_apply.2 ?_
    rw [Subgroup.mem_subgroupOf]
    simpa using (key a b).1 hpq
  have surj : Function.Surjective f := by
    intro Z
    obtain ⟨γ, hγQ, g₁, hg₁, hZ⟩ := _root_.GlobalTheory.SWLagTerms.exists_rat_unitary_lagFrame D W Z
    refine ⟨Quotient.mk _ ⟨γ, hγQ⟩, ?_⟩
    rw [hf]
    have := (_root_.GlobalTheory.SWLagSame.sameClass D W γ γ (g₀ ⟨γ, hγQ⟩) g₁ (hg₀ ⟨γ, hγQ⟩) hg₁ (Y ⟨γ, hγQ⟩) Z (hY ⟨γ, hγQ⟩) hZ).2
    exact this (by simpa using (GlobalTheory.Doubling.siegel W).one_mem)
  refine ⟨Equiv.ofBijective f ⟨inj, surj⟩, fun q => ⟨g₀ q.out, hg₀ q.out, ?_⟩⟩
  show IsLagFrame W (f q) _
  conv_lhs => rw [← Quotient.out_eq q]
  exact hY q.out

theorem lagTerms_eq : ∀ (D : D7) ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)), IsCovolOne (ratL V W) ν 𝓖' → ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q, ∃ C, IsLagFrame W (e q) C ∧ ∫ y in 𝓖', GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V ((q.out : GQ (GlobalTheory.Doubling.dblSp W)) : GA D (GlobalTheory.Doubling.dblSp W))⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) ∂ν = lagTerm μ 𝓕 C f₁ f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂ ν 𝓖' hν
  obtain ⟨e, he⟩ := classes W
  refine ⟨e, fun q => ?_⟩
  obtain ⟨g₀, hg₀, hY⟩ := he q
  exact ⟨frameOf W g₀, hY, integral_eq hS h₁ h₂ ν 𝓖' hν _ g₀ hg₀ (e q) hY⟩

end GlobalTheory.SWLagTerms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTBRecords

theorem aux_of_blochKato_tateDuality_eulerChar :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
        LocalSituation.Conclusion4 D HW F := by
  intro hBK hTD hEC D HW F _Cm
  obtain ⟨_J, hA⟩ := GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler hTD hEC D HW F
  exact _root_.GlobalTheory.TheoremTB.tb_assembled D HW F hA (_root_.GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ hBK hTD hEC D)

end GlobalTheory.TheoremTBRecords
end

