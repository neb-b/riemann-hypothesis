module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchUpOfTr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MatchUpProof

theorem matchUp_of_tr : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.TrCopy.TRLev R F SF → MatchUp R SF := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hTR c hE i

  have hHE := hC.models.HE
  unfold RealDat.models_HE at hHE
  obtain ⟨hinjE, hrngE, -⟩ := hHE

  have hHW := hC.models.HW
  unfold RealDat.models_HW at hHW
  obtain ⟨-, hrngW, -⟩ := hHW i (sg0 D A)

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hE
  have hE' : TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) R.e0 SF c ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨R.HE.e x, Submodule.mem_inf.2 ⟨hx, ?_⟩, ?_⟩
    · have hmem : R.HE.e x ∈ LinearMap.range R.HE.e := LinearMap.mem_range_self _ x
      rw [hrngE] at hmem
      exact hmem
    · intro h0
      exact hx0 (hinjE (h0.trans (map_zero R.HE.e).symm))

  have hW' : TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) (R.eWf i (sg0 D A)) SF c ≠ ⊥ := by
    intro hbot
    apply hE'
    apply Submodule.rank_eq_zero.1
    rw [(hTR i).1 c]
    exact Submodule.rank_eq_zero.2 hbot

  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hW'
  obtain ⟨hyF, hyG⟩ := Submodule.mem_inf.1 hy
  have hyR : y ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hrngW]
    exact (Submodule.mem_inf.1 hyG).1
  obtain ⟨z, rfl⟩ := hyR
  refine (Submodule.ne_bot_iff _).2 ⟨z, ?_, ?_⟩
  · show (R.HW i (sg0 D A)).e z ∈ R.Wat i (sg0 D A) R.triv ⊓ _
    exact Submodule.mem_inf.2 ⟨hyG, hyF⟩
  · rintro rfl
    exact hy0 (map_zero _)

end GlobalTheory.MatchUpProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.StabLatInv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem intGL_mulVec_mem (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hx : ∀ i, x i ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) :
    (intGL F E n y).val.mulVec x i ∈ Formalism.L2.Herm.intAf F E := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => mul_mem (y.val i j).2 (hx j)

theorem isFrame_mul_of_mem_St (β k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hβ : IsFrame β Λ) (hk : k ∈ St β) : IsFrame (k * β) Λ := by
  obtain ⟨y, hy⟩ := hk
  have e : k * β = β * intGL F E n y := by
    rw [← hy]
    change β * intGL F E n y * β⁻¹ * β = _
    rw [inv_mul_cancel_right]
  intro x
  rw [hβ x, e, mul_inv_rev, ← map_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · exact intGL_mulVec_mem y⁻¹ _
  · intro h
    have h2 := intGL_mulVec_mem y _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h2

end General

theorem mem_latO_iff_actO_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D S T ΛS ΛT βS βT _ _ hS hT g h hg hh u
  have hS' := isFrame_mul_of_mem_St βS _ ΛS hS hg
  have hT' := isFrame_mul_of_mem_St βT _ ΛT hT hh
  have eS : (finE S g * βS).val = (Formalism.L2.Theta.mt S g).map (toEAf D) * βS.val := rfl
  have eT : (finE T h * βT).val = (Formalism.L2.Theta.mt T h).map (toEAf D) * βT.val := rfl
  constructor
  · exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g h ΛS ΛS ΛT ΛT βS _ βT _ hS hS' hT hT' eS eT u
  · intro hu
    have h1 := GlobalTheory.AdelicLatMove.actO_mem_latO S T g⁻¹ h⁻¹ ΛS ΛS ΛT ΛT _ βS _ βT hS' hS hT' hT
      (GlobalTheory.AdelicLatMove.frame_inv S g _ _ eS) (GlobalTheory.AdelicLatMove.frame_inv T h _ _ eT) _ hu
    have h2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
    rw [inv_inv, inv_inv] at h2
    rwa [h2] at h1

end GlobalTheory.StabLatInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelInvariantFormUpperTriangularPairAction
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem isBorelU_inv_mixeq {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {g : GU σ n} (hg : IsBorelU g) :
    IsBorelU g⁻¹ := by
  intro i j hij
  exact Formalism.UG.P.spherical_upper_inv (g : GL (Fin n) L) ((Formalism.UG.P.spherical_upper_iff _).1 hg) hij

theorem mixLat_form_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) → ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (v : M), ℓ (ρ (embLow n' n z) (ω (g, h) v)) = ℓ (ω (g, h) s) * ℓ (ρ (embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1)) v) := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS ℓ hℓ huniq g h hg hh
  have hU := hS.1.unr
  have hnorm : ∀ (g : GU σ n) (h : GU σ n') (x : Matrix (Fin n') (Fin n) L),
      ω (g, h) * ρ x = ρ (h.1.1 * x * ((g.1)⁻¹ : GL (Fin n) L).1) * ω (g, h) := hS.1.norm
  have c1 : ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h →
      ∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v := by
    intro g h hg hh
    refine huniq (ℓ.comp (ω (g, h))) (fun a ha v => ?_)
    have hm := (_root_.GlobalTheory.SphTheta.borel_mixLat_lowBlock L ϖ σ q hU n n' g⁻¹ h (isBorelU_inv_mixeq hg) hh).1 a ha
    show ℓ (ω (g, h) (ρ a v)) = ℓ (ω (g, h) v)
    rw [← Module.End.mul_apply, hnorm, Module.End.mul_apply]
    exact hℓ _ hm _
  refine ⟨c1 g h hg hh, fun z v => ?_⟩
  obtain ⟨a, ha, ha0, he⟩ := (_root_.GlobalTheory.SphTheta.borel_mixLat_lowBlock L ϖ σ q hU n n' g h⁻¹ hg (isBorelU_inv_mixeq hh)).2 z
  have key : ρ (embLow n' n z) * ω (g, h) = ω (g, h) * ρ ((h⁻¹).1.1 * embLow n' n z * g.1.1) := by
    rw [hnorm]
    congr 2
    simp [Matrix.mul_assoc]
  set E' := embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1) with hE'
  have h0 : locH σ δ (antiG L n) (antiG L n') a E' = 0 := by
    rw [locH_antiG]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_)
    by_cases hj : j.1 < n - n / 2
    · rw [ha0 i j hj, zero_mul]
    · rw [hE', embLow, dite_eq_right (by simp only [Fin.val_rev]; omega), map_zero, mul_zero]
  have hsplit : ρ (a + E') = ρ a * ρ E' := by
    rw [hS.1.rho_mul, h0]
    simp
  rw [← Module.End.mul_apply, key, Module.End.mul_apply, c1 g h hg hh, he, hsplit, Module.End.mul_apply, hℓ a ha]

end GlobalTheory.SphTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem norm_gE_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HE → R.models_gE → R.models_ν0 → ∀ g x, ‖R.gE g x‖ = ‖x‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hE hg h0 g x
  unfold RealDat.models_HE RealDat.models_gE RealDat.models_ν0 at *
  obtain ⟨hinj, hrange, hip⟩ := hE
  obtain ⟨hm, hfd⟩ := h0
  obtain ⟨hHaar, -⟩ := hm

  let u : R.HE.H ≃ₗ[ℂ] R.HE.H :=
    LinearEquiv.ofLinear (R.gE g) (R.gE g⁻¹)
      (by
        ext y
        show R.gE g (R.gE g⁻¹ y) = y
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
      (by
        ext y
        show R.gE g⁻¹ (R.gE g y) = y
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])

  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    intro y
    have hy : R.HE.e y ∈ LinearMap.range R.HE.e := ⟨y, rfl⟩
    rw [hrange] at hy
    exact (Submodule.mem_inf.mp hy).1

  have hact : ∀ y v, R.HE.e (u y) v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e y v) := by
    intro y v
    show R.HE.e (R.gE g y) v = _
    rw [hg]
    rfl
  exact _root_.GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel R.θ (R.MY 0) (R.βY 0) (R.dat0 R.triv) (levS _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) R.HE.H R.HE.e 1 R.ν0 R.fd0
    (fun y z => by rw [one_mul]; exact hip y z) hinj hmem hHaar hfd (R.eG g) u hact x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem gW_norm_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → R.models_gW → R.models_νW → ∀ i σ g x, ‖R.gW i σ g x‖ = ‖x‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hH hg hν i σ g x
  unfold RealDat.models_HW at hH
  unfold RealDat.models_gW at hg
  unfold RealDat.models_νW at hν
  obtain ⟨hinj, hrange, hip⟩ := hH i σ
  unfold ipAt at hip
  have hfd := hν i
  unfold IsMeasFD at hfd
  have hHaar : (R.νW i).IsHaarMeasure := by
    have h := hfd.1
    unfold IsMeasLev IsMeasLevW at h
    exact h.1
  let u : (R.HW i σ).H ≃ₗ[ℂ] (R.HW i σ).H :=
    LinearEquiv.ofLinear (R.gW i σ g) (R.gW i σ g⁻¹) (by ext y; simp) (by ext y; simp)
  have hmem : ∀ y, (R.HW i σ).e y ∈ R.Wall i σ := fun y => by
    rw [← hrange]
    exact LinearMap.mem_range_self _ y
  exact _root_.GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel R.θ (R.MW i σ) (R.βW i) (R.datWp i R.triv) _ _ (R.HW i σ).H (R.HW i σ).e _
    (R.νW i) (R.fdW i) hip hinj hmem hHaar hfd.2 (R.eG g) u
    (fun y v => congrArg (fun T => T v) (hg i σ g y)) x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosAtBase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PosAtBase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem Wp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) (i : Fin D.R.m) :
    R.Wp3 i p = R.Wc' i c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ ((hU p c c0 hc h0).2 i).le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.Wc' i c) c0 h0 le_rfl

theorem EEp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) :
    R.EEp3 p = R.EEc c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ (hU p c c0 hc h0).1.le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.EEc c) c0 h0 le_rfl

theorem Wp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) (i : Fin D.R.m) :
    R.Wp3 i p = ⊥ := by
  unfold RealDat3.Wp3
  simp [h]

theorem EEp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) :
    R.EEp3 p = ⊥ := by
  unfold RealDat3.EEp3
  simp [h]

end GlobalTheory.PosAtBase

namespace GlobalTheory.PosAtBase


set_option maxHeartbeats 1000000 in
theorem pos_at_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (_hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F) (_hE : R.toRealDat.ExAt)
    (hS : Scal R.toRealDat R.SF) (hM : MatchUp R.toRealDat R.SF)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    (hex : ∃ p, R.EEp3 p ≠ ⊥) :
    0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
  obtain ⟨lam, κ, hκ, hl, hA, hB⟩ := hS
  have hlam : ∀ i t p c, R.Carries p c → R.Wc' i c ≠ ⊥ → R.lam3 i t p A3.A.v0 = lam i t c := by
    intro i t p c hc hne
    have hW := Wp3_eq hU hc i
    refine hC.scal.lam0 i t p _ (by rw [hW]; exact hne) fun x hx ↦ hA i t c x ?_
    rw [hW] at hx
    exact hx
  have hpos : ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
    intro i t p
    by_cases hW : R.Wp3 i p = ⊥
    · rw [hC.scal.abs0 i t p hW]
      exact Real.exp_pos _
    · by_cases hc : ∃ c, R.Carries p c
      · obtain ⟨c, hc⟩ := hc
        rw [hlam i t p c hc (by rw [← Wp3_eq hU hc i]; exact hW)]
        exact hl i t c
      · exact absurd (Wp3_bot (not_exists.1 hc) i) hW
  refine ⟨?_, hpos⟩
  have hK : Lift.IsKap D.R.m (fun t ↦ R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ := by
    intro t p x hx
    by_cases hc : ∃ c, R.Carries p c
    · obtain ⟨c, hc⟩ := hc
      have hx' : x ∈ R.EEc c := EEp3_eq hU hc ▸ hx
      have hpr : ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p = ∏ j, lam j t c :=
        (RealDat3.prod_lamN t p).trans (Finset.prod_congr rfl fun j _ ↦ hlam j t p c hc (hM c hc.1 j))
      have h1 := hB t c x hx'
      calc (R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) x = R.Th t (LinearMap.adjoint (R.Th t) x) := rfl
        _ = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x := h1
        _ = ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p : ℝ) : ℂ) • x := by rw [hpr]
    · have hb : R.EEp3 p = ⊥ := EEp3_bot (not_exists.1 hc)
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).1 (hb ▸ hx)
      subst hx0
      rw [map_zero, smul_zero]
  obtain ⟨p, hp⟩ := hex
  rw [hC.scal.kap κ hK ⟨A3.A.μ0, p, hp, ?_⟩]
  · exact hκ
  · rw [RealDat3.prod_lamN]
    exact (Finset.prod_pos fun j _ ↦ hpos j _ p).ne'

end GlobalTheory.PosAtBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem adAt_mem_lieAt (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : adAt θ k τ X ∈ lieAt V τ := by

  have hU : Matrix.conjTranspose (infMat D.sp.cm.sig V.gram (θ τ) k) * gramAt D V τ *
      infMat D.sp.cm.sig V.gram (θ τ) k = gramAt D V τ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ
  exact skew_conj hU (GlobalTheory.Mem.AutSpace.infMat_mul_inv (θ := θ) (V := V) (τ := τ) (g := k)) hX

private theorem infMat_eq_one_of_mem_GfC {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) f = 1 := by

  have h1 : infHom V f = 1 := hf
  have h2 := congrArg (fun u => (u.val).map (θ τ)) h1
  simp only [Units.val_one] at h2
  rw [Matrix.map_one (θ τ) (map_zero (θ τ)) (map_one (θ τ))] at h2
  exact h2

private theorem adAt_mul_of_mem_GfC (a : GA D V) {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : adAt θ (a * f) τ X = adAt θ a τ X := by

  unfold adAt
  rw [mul_inv_rev, GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, infMat_eq_one_of_mem_GfC hf τ,
    infMat_eq_one_of_mem_GfC (inv_mem hf) τ, one_mul, mul_one]

theorem oneP_mul_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : oneP θ V τ X t * k = k * oneP θ V τ (adAt θ k τ X) t := by

  obtain ⟨a, ha, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have hreal : IsRealPt θ a := ⟨ha, fun σ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a σ⟩
  have hinf : oneP θ V τ (adAt θ a τ X) t ∈ GinfC V := atTau_mem V τ _
  rw [adAt_mul_of_mem_GfC a hf, ← mul_assoc, oneP_mul hθ hreal hX t, mul_assoc, mul_assoc,
    comm_of_mem V hinf hf]

theorem Rder_rTr_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ (adAt θ k τ X) φ) := by

  funext g
  show deriv (fun t : ℝ => φ (g * oneP θ V τ X t * k)) 0 = deriv (fun t : ℝ => φ (g * k * oneP θ V τ (adAt θ k τ X) t)) 0
  congr 1
  funext t
  rw [mul_assoc, oneP_mul_adelic hθ k hX t, ← mul_assoc]

theorem rWord_rTr_adelic (hθ : IsInfFam θ) (k : GA D V) (φ : GA D V → ℂ)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) :
    rWord θ V l (rTr V k φ) = rTr V k (rWord θ V (l.map fun p => (p.1, adAt θ k p.1 p.2)) φ) := by

  induction l with
  | nil => simp only [rWord, wordAct, List.foldr_nil, List.map_nil]
  | cons p l ih =>
    have hp : p.2 ∈ lieAt V p.1 := hl p List.mem_cons_self
    have hl' : IsLieWord V l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have ih' := ih hl'
    simp only [rWord, wordAct, List.foldr_cons, List.map_cons] at ih' ⊢
    rw [ih', Rder_rTr_adelic hθ k hp]

theorem rTr_mem_smFun (hθ : IsInfFam θ) (k : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    rTr V k φ ∈ SmFun θ V := by

  intro n τs Xs hXs g
  have key := hφ n τs (fun i => adAt θ k (τs i) (Xs i)) (fun i => adAt_mem_lieAt hθ k (hXs i)) (g * k)
  convert key using 1
  funext t
  show φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * k) =
    φ (g * k * (List.ofFn fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)).prod)
  rw [mul_assoc, prod_mul_eq k n (fun i => oneP θ V (τs i) (Xs i) (t i))
    (fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)) (fun i => oneP_mul_adelic hθ k (hXs i) (t i)),
    ← mul_assoc]

private theorem rapidDecSm_rTr_of_mem_GinfC (hθ : IsInfFam θ) {a : GA D V} (ha : a ∈ GinfC V) {φ : GA D V → ℂ}
    (h : RapidDecSm θ V φ) : RapidDecSm θ V (Formalism.L2.Theta.rTr V a φ) := by

  have hR := h.rapidDec.mul_right a
  refine ⟨⟨hR.1, ?_, hR.2.1⟩, rTr_mem_smFun hθ a h.smooth, fun l hl => ?_⟩
  · obtain ⟨U, hU, hUφ⟩ := h.level
    refine ⟨U, hU, fun u hu huf g => ?_⟩
    show φ (g * u * a) = φ (g * a)
    rw [mul_assoc, ← comm_of_mem V ha huf, ← mul_assoc, hUφ u hu huf]
  · rw [rWord_rTr_adelic hθ a φ hl]
    refine (h.decay _ fun p hp => ?_).mul_right a
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact adAt_mem_lieAt hθ a (hl q hq)

theorem RapidDecSm.rTr (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : RapidDecSm θ V φ) (k : GA D V) :
    RapidDecSm θ V (Formalism.L2.Theta.rTr V k φ) := by

  obtain ⟨a, ha, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have e : Formalism.L2.Theta.rTr V (a * f) φ = Formalism.L2.Theta.rTr V a (Formalism.L2.Theta.rTr V f φ) := by
    funext g
    simp only [Formalism.L2.Theta.rTr, mul_assoc]
  rw [e]
  exact rapidDecSm_rTr_of_mem_GinfC hθ ha (h.rTr_fin hf)

end GlobalTheory.Size

end
end

