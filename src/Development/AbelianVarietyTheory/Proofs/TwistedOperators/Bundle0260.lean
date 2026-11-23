module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRep
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExThOfChain
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProjectedLift

theorem ex_Th_of_chain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → R.ex_Th := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hr t
  obtain ⟨Th, hTh⟩ := GlobalTheory.ProjectedLift.exists_chain_Th D G Pl0 T A Ks R h0 hf hm hr
  exact ⟨Th t, fun x => hTh t x⟩

end GlobalTheory.ProjectedLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.WeilConj

variable {D : D7}

theorem dag_dag {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ T S) (f : WO T S → ℂ) :
    dag S T (dag T S f) = f := by
  funext y
  simp only [dag, Complex.conj_conj, h.invol y]

theorem dag_add (S T : HSp D) (f f' : WO S T → ℂ) : dag S T (f + f') = dag S T f + dag S T f' := by
  funext y; simp [dag]

theorem dag_smul (S T : HSp D) (c : ℂ) (f : WO S T → ℂ) : dag S T (c • f) = starRingEnd ℂ c • dag S T f := by
  funext y; simp [dag]

def conjE (S T : HSp D) (A : Module.End ℂ (WO S T → ℂ)) : Module.End ℂ (WO T S → ℂ) where
  toFun f := dag S T (A (dag T S f))
  map_add' f f' := by simp only [dag_add, map_add (f := _)]
  map_smul' c f := by simp only [dag_smul, map_smul, Complex.conj_conj, RingHom.id_apply]

def conjRep {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S) (ω : WRep S T) :
    WRep T S where
  toFun p := conjE S T (ω (p.2, p.1))
  map_one' := by
    apply LinearMap.ext; intro f
    show dag S T (ω 1 (dag T S f)) = f
    rw [map_one, Module.End.one_apply, dag_dag hTS]
  map_mul' p q := by
    apply LinearMap.ext; intro f
    show dag S T (ω ((p * q).2, (p * q).1) (dag T S f)) = dag S T (ω (p.2, p.1) (dag T S (dag S T (ω (q.2, q.1) (dag T S f)))))
    rw [dag_dag hST]
    have : ((p * q).2, (p * q).1) = (p.2, p.1) * (q.2, q.1) := rfl
    rw [this, map_mul, Module.End.mul_apply]

theorem conjRep_apply {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (ω : WRep S T) (h : GA D T) (g : GA D S) (f : WO T S → ℂ) :
    conjRep hST hTS ω (h, g) f = dag S T (ω (g, h) (dag T S f)) := rfl

theorem adjO_zero {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ S T) : adjO S T 0 = 0 := by
  have := h.add 0 0
  rw [add_zero] at this
  simpa using this

theorem unit_transport {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (μ : Measure (WO T S)) (𝓕 : Set (WO T S)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL S T) 𝓕 μ) :
    ∃ (μ' : Measure (WO S T)) (𝓕' : Set (WO S T)), μ'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL T S) 𝓕' μ' ∧
      ∀ G : WO S T → ENNReal, ∫⁻ w in 𝓕, G (adjO S T w) ∂μ = ∫⁻ v in 𝓕', G v ∂μ' := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D S.rank T.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (WO T S) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  let eA : WO T S ≃+ WO S T :=
    { toFun := adjO S T
      invFun := adjO T S
      left_inv := fun x => hTS.invol x
      right_inv := fun y => hST.invol y
      map_add' := hST.add }
  let eH : WO T S ≃ₜ WO S T := ⟨eA.toEquiv, hST.cont, hTS.cont⟩
  let eM : WO T S ≃ᵐ WO S T := eH.toMeasurableEquiv
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hST.cont hTS.cont
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL S T → ratL T S := fun g => ⟨adjO S T g, (hST.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO T S g, (hTS.rat g).2 g.2⟩, Subtype.ext (hST.invol g)⟩⟩
    have e := congrArg (fun x : ratL T S => adjO T S (x : WO S T)) hg
    simp only [eG, hTS.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL T S) (eM.symm ⁻¹' 𝓕) (μ.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO T S (adjO S T g + x) = (g : WO T S) + adjO T S x
    rw [hTS.add, hTS.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext a; simp
  refine ⟨μ.map eM, eM.symm ⁻¹' 𝓕, hHaar, hF, fun G => ?_⟩
  symm
  rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, hpre]
  rfl

theorem enorm_dag (S T : HSp D) (f : WO S T → ℂ) (y : WO T S) : ‖dag S T f y‖ₑ = ‖f (adjO S T y)‖ₑ := by
  simp only [dag]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_conj]

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  refine ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hε, ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]

theorem suppAt_cA {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]
  exact h i j

theorem exists_detAt_cA {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) : ∃ x' : (AE D)ˣ, IsDetAt (cA D e) V g x' ∧
      ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D χ n → χ x' = χ x := by
  have hi : cA D e * cA D e = cA D e := by rw [← map_mul, he.1]
  refine ⟨GlobalTheory.SplitDetCharacter.cutDet (cA D e) hi V g, ?_, fun χ n hχ => ?_⟩
  · show _ = _
    rw [GlobalTheory.SplitDetCharacter.cutDet_val]; ring
  · refine GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hχ _ _ ?_
    rw [GlobalTheory.SplitDetCharacter.cutDet_val, hx, map_add (f := _), map_mul, map_sub, map_one]
    have hd := GlobalTheory.SplitDetCharacter.det_mul_conj V g
    linear_combination (1 - cA D (Formalism.L2.Theta.mt V g).det + (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det
      - (Formalism.L2.Theta.mt V g).det) * hi + cA D e * hd

theorem exists_conj_weilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T), IsWeilDatumO ψ S T χS χT ω → ∃ ω' : WRep T S, IsWeilDatumO ψ T S χT χS ω' ∧ ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), ω' (h, g) (dag S T f) = dag S T (ω (g, h) f) := by
  intro D ψ S T χS χT ω H
  have hST : AdjLaw ψ S T := _root_.GlobalTheory.AdjLawPf.adjLaw D ψ H.std S T
  have hTS : AdjLaw ψ T S := _root_.GlobalTheory.AdjLawPf.adjLaw D ψ H.std T S
  refine ⟨conjRep hST hTS ω, ?_, fun g h f => by rw [conjRep_apply, dag_dag hST]⟩
  refine
    { std := H.std
      hecS := H.hecT
      hecT := H.hecS
      resS := H.resT
      resT := H.resS
      om_pres := fun p f hf => hST.theta _ (H.om_pres _ _ (hTS.theta f hf))
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro h g w₀ f hf
    rw [conjRep_apply, conjRep_apply]
    have e1 := hTS.Heisenberg₂ (adjO S T w₀) f
    rw [hTS.invol] at e1
    rw [← e1, H.om_heis g h (adjO S T w₀) _ (hTS.theta f hf), ← hST.act, hST.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [conjRep_apply]
    simp only [dag]
    rw [adjO_zero hST, H.om_aut γ' hγ' γ hγ _ (hTS.theta f hf)]
    simp only [dag]
    rw [adjO_zero hTS, Complex.conj_conj]
  · intro f hf w
    exact Complex.continuous_conj.comp ((H.om_cont _ (hTS.theta f hf) (adjO S T w)).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨μ', 𝓕', hμ', h𝓕', hG⟩ := unit_transport hST hTS μ 𝓕 hμ h𝓕
    have e1 : ∀ w, ‖conjRep hST hTS ω p f w‖ₑ ^ 2 = (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show ‖dag S T (ω (p.2, p.1) (dag T S f)) w‖ₑ ^ 2 = _
      rw [enorm_dag]
    have e2 : ∀ w, ‖f w‖ₑ ^ 2 = (fun v => ‖dag T S f v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show _ = ‖dag T S f (adjO S T w)‖ₑ ^ 2
      rw [enorm_dag, hTS.invol]
    simp only [e1, e2]
    exact (hG (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2)).trans
      ((H.om_unit μ' 𝓕' hμ' h𝓕' _ _ (hTS.theta f hf)).trans (hG (fun v => ‖dag T S f v‖ₑ ^ 2)).symm)
  · intro e he h g hTh hSg y x hy hx
    obtain ⟨x', hx', hxx⟩ := exists_detAt_cA he hx
    obtain ⟨y', hy', hyy⟩ := exists_detAt_cA he hy
    obtain ⟨r, hr, hℓ⟩ := H.om_split (cA D e) (isSplitIdem_cA he) g h (suppAt_cA hSg) (suppAt_cA hTh) x' y' hx' hy'
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    let ℓω : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun F F' => by simp only [dag_add, map_add (f := _)]
        map_smul' := fun c F => by simp only [dag_smul, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply] }
    have hinvω : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓω (heisO ψ S T u F) = ℓω F := by
      intro u hu F hF
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      have e1 := hST.Heisenberg₂ (adjO T S u) F
      rw [hST.invol] at e1
      have hh : IsHalf (cA D (cA D (cA D e))) (adjO T S u) := hTS.half _ u hu
      rw [GlobalTheory.DualPairCheck.cA_cA] at hh
      rw [← e1, hinv _ hh _ (hST.theta F hF)]
    have key := hℓ ℓω hinvω (dag T S f) (hTS.theta f hf)
    have k1 : ℓω (ω (g, h) (dag T S f)) = starRingEnd ℂ (ℓ (conjRep hST hTS ω (h, g) f)) := rfl
    have k2 : ℓω (dag T S f) = starRingEnd ℂ (ℓ f) := by
      show starRingEnd ℂ (ℓ (dag S T (dag T S f))) = _
      rw [dag_dag hTS]
    rw [k1, k2] at key
    have hsf : (starRingEnd ℂ) ((splitFacO χS χT x' y' : Circle) : ℂ) = ((splitFacO χT χS y x : Circle) : ℂ) := by
      rw [← Circle.coe_inv_eq_conj]
      congr 1
      unfold splitFacO
      rw [hxx χT _ H.resT, hyy χS _ H.resS, _root_.mul_inv_rev, inv_inv]
    have key' := congrArg (starRingEnd ℂ) key
    rw [Complex.conj_conj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, hsf] at key'
    exact key'

end GlobalTheory.WeilConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelOfOrthonormalBasisCarta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jm_mul_self {n : ℕ} (e : Fin n → Bool) : Formalism.REAL.Jm e * Formalism.REAL.Jm e = 1 := by
  ext a b
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem jm_injective {n : ℕ} {e e' : Fin n → Bool} (h : Formalism.REAL.Jm e = Formalism.REAL.Jm e') : e = e' := by
  funext a
  have := congrFun (congrFun h a) a
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq] at this
  cases he : e a <;> cases he' : e' a <;> simp_all <;> norm_num at this

theorem dsModel_of_onb_cart : ∀ (D : D7), GlobalTheory.Published.DiscreteSeriesUpqExists → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε) → (∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) → ∃ M : DSModel V S, cart M = C ∧ onb M = O := by
  intro D hDS V S O C h1 h2
  choose lam ε hE hP hG using h1
  choose H i1 i2 σ hσ using fun τ =>
    (GlobalTheory.Published.discreteSeriesExists_iff.1 hDS) V.rank (ε τ) (lam τ) (hP τ)
  have hdet : ∀ τ, IsUnit (O τ).det := fun τ => by
    refine Matrix.isUnit_det_of_left_inverse (B := Formalism.REAL.Jm (ε τ) * ((O τ)ᴴ * gramAt D V τ)) ?_
    rw [Matrix.mul_assoc, hG τ, jm_mul_self]
  have hr : ∀ τ, O τ * (O τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (hdet τ)
  have hl : ∀ τ, (O τ)⁻¹ * O τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet τ)
  have hii : ∀ τ, ((O τ)⁻¹)⁻¹ = O τ := fun τ => Matrix.nonsing_inv_nonsing_inv _ (hdet τ)
  let M : DSModel V S :=
    { H := H, nacg := i1, ips := i2, σ := σ, lam := lam, ε := ε, fr := fun τ => (O τ)⁻¹,
      enum := hE, ds := hσ,
      fr_unit := fun τ => (Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det _).2 (hdet τ))
      fr_gram := fun τ => by
        rw [← hG τ]
        calc ((O τ)⁻¹)ᴴ * ((O τ)ᴴ * gramAt D V τ * O τ) * (O τ)⁻¹
            = (O τ * (O τ)⁻¹)ᴴ * gramAt D V τ * (O τ * (O τ)⁻¹) := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = gramAt D V τ := by rw [hr τ]; simp }
  refine ⟨M, ?_, ?_⟩
  · funext τ
    obtain ⟨e', hG', hC⟩ := h2 τ
    have he : e' = ε τ := jm_injective (by rw [← hG', hG τ])
    rw [he] at hC
    show ((O τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (O τ)⁻¹ = C τ
    rw [hii, ← hC, Matrix.mul_assoc, hr, Matrix.mul_one]
  · funext τ
    exact hii τ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsWeilOfEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isWeil_of_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S S' T' Tg : HSp D} (hS : S = S') (hT : Tg = T')
    {χS χT : (AE D)ˣ →* Circle} (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS χT ω') :
    ∃ ω : GlobalTheory.Grid.WRep S Tg, GlobalTheory.Grid.IsWeil ψ false S Tg χS χT ω ∧ HEq ω ω' := by
  subst hS hT
  exact ⟨ω', h, HEq.rfl⟩

theorem omCol_of_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V, GlobalTheory.Grid.IsWeil R.ψ false (G.Xp j).V (G.nX j).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ω ∧ HEq ω (W.om (.top t j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ t j hj
  have hS : (G.Xp j).V = G'.V (.top j) := (hSp.top j hj.le).sp
  have hT : (G.nX j).V = G'.V (.top (j + 1)) := (hSp.top (j + 1) hj).sp
  have hω := W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have hr : ∀ k, k ≤ D.R.m → Even (G'.V (.top k)).rank := fun k hk => by
    have := (G'.isV (X := .top k) hk (fun _ h => by cases h)).rank
    rw [this]; exact even_rankX D k
  have eS : G'.chrS (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrS, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr j hj.le)]
  have eT : G'.chrT (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrT, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr (j + 1) hj)]
  rw [eS, eT, hW.ψ] at hω
  exact exists_isWeil_of_eq hS hT _ hω

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumTestGridOfLevelChoiceGrid
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem hT_eq_coords (S : HSp D) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * S.gram i j * S.frame.repr y j := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Formalism.BasicNotions.HSpace.gram]
  ring

theorem hT_cols (S : HSp D) {k l : ℕ} (a : Matrix (Fin S.rank) (Fin k) D.host.E) (b : Matrix (Fin S.rank) (Fin l) D.host.E)
    (q : Fin k) (p : Fin l) :
    S.hT (S.frame.equivFun.symm (fun i => a i q)) (S.frame.equivFun.symm (fun i => b i p)) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) a * S.gram * b) q p := by
  rw [hT_eq_coords]
  have e1 : ∀ v : Fin S.rank → D.host.E, S.frame.repr (S.frame.equivFun.symm v) = v := fun v => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [e1, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_orthogonalSum_testGrid_of_levelChoiceGrid {D : D7} (A B : GlobalTheory.Grid.Node D) {c : ℕ} {ε : D.host.E}
    (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A.V B.V c ε) (𝔟 : Fin c → GlobalTheory.Grid.FrId D) (_hε : ε = 1 ∨ ε = -1)
    (hΛ : B.Λ = d.lat A.Λ 𝔟) :
    ∃ d' : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c, d'.ι = d.ι ∧ d'.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c ε p q) 𝔟 := by
  refine ⟨⟨d.ι, fun p => B.V.frame.equivFun.symm (fun k => d.a k p)⟩, rfl, ?_⟩
  have e1 : ∀ v : Fin B.V.rank → D.host.E, B.V.frame.repr (B.V.frame.equivFun.symm v) = v := fun v => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨d.isom, ?_, ?_, d.rank, ?_⟩
  ·
    intro x p
    show B.V.hT _ (d.ι x) = 0
    conv_lhs => rw [← A.V.frame.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h1 := B.V.herm.eq (d.ι (A.V.frame k)) (B.V.frame.equivFun.symm (fun i => d.a i p))
    have h2 : d.ι (A.V.frame k) = B.V.frame.equivFun.symm (fun i => frameMat B.V A.V d.ι i k) := by
      apply B.V.frame.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      ext i
      simp [frameMat, LinearMap.toMatrix_apply]
    have h3 : B.V.hT (d.ι (A.V.frame k)) (B.V.frame.equivFun.symm (fun i => d.a i p)) = 0 := by
      rw [h2, hT_cols, d.perp]; rfl
    rw [← h1, h3]
    simp
  ·
    intro p q
    show B.V.hT _ _ = _
    rw [hT_cols, d.gram]
    simp only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp_all [Fin.ext_iff]; omega) | simp_all
  ·
    have key : ∀ (x : A.V.V) (t : Fin c → D.host.E),
        B.V.frame.equivFun (d.ι x + ∑ p, t p • B.V.frame.equivFun.symm (fun k => d.a k p)) =
          frameMat B.V A.V d.ι *ᵥ A.V.frame.equivFun x + d.a *ᵥ t := by
      intro x t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum]
      congr 1
      · simp only [Module.Basis.equivFun_apply, frameMat]
        exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm
      · simp only [map_smul, LinearEquiv.apply_symm_apply]
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    intro y
    show B.V.frame.equivFun y ∈ B.Λ ↔ _
    rw [hΛ]
    constructor
    · rintro ⟨z, hz, u, hu, hy⟩
      refine ⟨A.V.frame.equivFun.symm z, ?_, u, hu, ?_⟩
      · show A.V.frame.equivFun (A.V.frame.equivFun.symm z) ∈ A.Λ
        rwa [LinearEquiv.apply_symm_apply]
      · apply B.V.frame.equivFun.injective
        rw [key, LinearEquiv.apply_symm_apply]
        exact hy
    · rintro ⟨x, hx, t, ht, rfl⟩
      exact ⟨A.V.frame.equivFun x, hx, t, ht, key x t⟩

end GlobalTheory.GridJoin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : UniformSpace E) (_ : IsUniformAddGroup E) (_ : CompleteSpace E) (_ : T2Space E) (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)), Function.Injective ι ∧ (∀ φ, φ ∈ Set.range ι ↔ Continuous φ ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ IsCuspFun V φ ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N φ ≠ ⊤) ∧ (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) ∧ ∀ τ, ∃ π dπ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E), GlobalTheory.SmoothGlob.IsSmoothModRep (A.ε τ) p π dπ ∧ (∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), ∀ x, ι (π g x) = rTr V (A.elt θ τ g) (ι x)) ∧ ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (A.ε τ), ∀ x, ι (dπ X x) = Rder θ V τ ((A.fr τ)⁻¹ * X * A.fr τ) (ι x) := by
  first | exact @GlobalTheory.CuspFrechet.exists_frechet | exact GlobalTheory.CuspFrechet.exists_frechet | (intros; apply GlobalTheory.CuspFrechet.exists_frechet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridNodeSignatureSelfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.Grid.Vertex

theorem negIdx_of_sig {D : D7} (V : HSp D) (q : ℕ) (h : V.SigOK) (hs : ∀ τ : D.host.E →+* ℂ, V.sig τ = (V.rank - q, q)) :
    NegIdx V q := fun τ => by
  have := h (tauE D τ)
  rw [hs] at this
  exact this

end GlobalTheory.Grid.Vertex

end
end

