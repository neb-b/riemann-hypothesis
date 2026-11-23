module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import GroundTheory.GlobalFields.Adele.Discrete
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0686
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0667
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0679
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0662

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.AdmDiscFin

section Dual

variable {K : Type} [Group K]

def shiftL (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) (k : K) : Y →ₗ[ℂ] Y where
  toFun f := ⟨fun x => f.1 (k * x), hY f.1 f.2 k⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dualRep (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) :
    Representation ℂ K (Module.Dual ℂ Y) where
  toFun k := (shiftL Y hY k).dualMap
  map_one' := by
    refine LinearMap.ext fun ξ => LinearMap.ext fun f => ?_
    change ξ (shiftL Y hY 1 f) = ξ f
    congr 1
    exact Subtype.ext (funext fun x => by simp [shiftL])
  map_mul' k l := by
    refine LinearMap.ext fun ξ => LinearMap.ext fun f => ?_
    change ξ (shiftL Y hY (k * l) f) = ξ (shiftL Y hY l (shiftL Y hY k f))
    congr 1
    exact Subtype.ext (funext fun x => by simp [shiftL, mul_assoc])

theorem le_coeffSpan_dualRep (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) :
    Y ≤ GlobalTheory.Published.AutFin.coeffSpan (dualRep Y hY) := by
  intro f hf
  let ev : Module.Dual ℂ Y := (LinearMap.proj (1 : K)).comp Y.subtype
  refine Submodule.subset_span ⟨Module.Dual.eval ℂ Y ⟨f, hf⟩, ev, funext fun k => ?_⟩
  change f k = f (k * 1)
  rw [mul_one]

theorem isContRep_dualRep [TopologicalSpace K] [ContinuousMul K] (Y : Submodule ℂ (K → ℂ))
    (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) [FiniteDimensional ℂ Y] (hc : ∀ f ∈ Y, Continuous f) :
    GlobalTheory.Published.AutFin.IsContRep (dualRep Y hY) := by
  intro ℓ ξ
  let ev : K → Module.Dual ℂ Y := fun x => (LinearMap.proj x).comp Y.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ x, v.1 x = 0 := fun x => hv _ (Submodule.subset_span ⟨x, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (funext h2)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ Y).surjective ℓ
  have key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev), Continuous fun k => ξ (shiftL Y hY k f) := by
    intro ξ hl
    induction hl using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      exact (hc f.1 f.2).comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  exact key ξ (hspan ▸ Submodule.mem_top)

end Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ}

theorem continuous_slice (φ : Sm E M) (g : GA E M) :
    Continuous fun k : Kinf E M => φ.1 (g * infGL E M (Unitary.toUnits k)) := by
  have h1 : Continuous fun k : Kinf E M => (Unitary.toUnits k : GL (Fin M) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have e : (fun k : Kinf E M => φ.1 (g * infGL E M (Unitary.toUnits k))) =
      fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin M) (Cinf E)).val) := by
    funext k
    rw [chart_val]
  rw [e]
  have hc : ContinuousOn (chart φ.1 g) (invSet E M) := (φ.2 g).continuousOn
  have h3' : Continuous fun k : Kinf E M =>
      ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E)) :=
    (Units.continuous_val (M := Matrix (Fin M) (Fin M) (Cinf E))).comp h1
  have h3 : Continuous fun k : Kinf E M =>
      toL ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E)) := h3'
  exact hc.comp_continuous h3 fun k => val_mem_invSet _

theorem admissible_discrete_spaces : PositivityTheory.Rg.BcB.SpectralAccumulation.AdmDisc := by
  intro E _ _ _ M K' W' hK' hW' V hV
  haveI := hW'
  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ := fun τ u =>
    GlobalTheory.DiscLocEx.exists_scalarD hV (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  choose c hc using hsc
  let Y : Submodule ℂ (Kinf E M → ℂ) := Submodule.span ℂ
    {f | ∃ φ : Sm E M, φ ∈ V ∧ TypeB K' W' φ ∧ ∃ g : GA E M, f = fun k => φ.1 (g * infGL E M (Unitary.toUnits k))}
  have hYW : Y ≤ W' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, -, hφ, g, rfl⟩
    exact hφ.2 g
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW
  have hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y := by
    intro f hf k
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, hφV, hφ, g, rfl⟩ := hf
      refine Submodule.subset_span ⟨φ, hφV, hφ, g * infGL E M (Unitary.toUnits k), funext fun x => ?_⟩
      simp only [map_mul, mul_assoc]
    | zero => exact Y.zero_mem
    | add x y _ _ hx hy => exact Y.add_mem hx hy
    | smul r x _ hx => exact Y.smul_mem r hx
  have hYc : ∀ f ∈ Y, Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, -, -, g, rfl⟩ := hf
      exact continuous_slice φ g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  haveI hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E M K' hK' (Module.Dual ℂ Y) (dualRep Y hYl)
    (isContRep_dualRep Y hYl hYc) c
  have hle : {φ | φ ∈ V ∧ TypeB K' W' φ} ⊆ GlobalTheory.Published.AutFinGL.forms K' (dualRep Y hYl) c := by
    rintro φ ⟨hφV, hφ⟩
    refine ⟨hV.aut φ hφV, fun k hk => Subtype.ext (funext fun g => hφ.1 k hk g), fun g => ?_,
      fun τ u => hc τ u φ hφV⟩
    exact le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨φ, hφV, hφ, g, rfl⟩)
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hle)

end GlobalTheory.CompanionTheory.AdmDiscFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSet
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi.Den

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (Fv F v) t) = v.valuation F t :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t

theorem exists_valued_bound (v : HeightOneSpectrum (𝓞 F)) {C : Set (Fv F v)} (hC : IsCompact C) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ x ∈ C, Valued.v x ≤ γ := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  obtain ⟨s, -, hs⟩ := hC.elim_nhds_subcover
    (fun x => {y : Fv F v | y - x ∈ v.adicCompletionIntegers F}) (fun x _ => by
      have hopen : IsOpen {y : Fv F v | y - x ∈ v.adicCompletionIntegers F} :=
        hO.preimage (continuous_id.sub continuous_const)
      exact hopen.mem_nhds (by simp))
  obtain ⟨M, hM⟩ := (s.image fun x => Valued.v x).exists_le
  refine ⟨max M 1, (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).ne', fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp (hs hy)
  have h1 : Valued.v (y - x) ≤ 1 := hxy
  have h2 : Valued.v x ≤ M := hM _ (Finset.mem_image_of_mem _ hx)
  have h3 : y = (y - x) + x := by ring
  rw [h3]
  exact (Valuation.map_add _ _ _).trans
    (max_le (h1.trans (le_max_right _ _)) (h2.trans (le_max_left _ _)))

theorem exists_finset_inv_integral {D : Set (AF F)ˣ} (hD : IsCompact D) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ u ∈ D, ∀ v, v ∉ T →
      ((u⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
  obtain ⟨s, -, hs⟩ := hD.elim_nhds_subcover
    (fun a : (AF F)ˣ => {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F}) (fun a _ => by
      have hopen : IsOpen {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F} :=
        (IdeleGroup.isOpen_standardOpenSubgroup F).preimage (continuous_const.mul continuous_id)
      exact hopen.mem_nhds (by simp [one_mem]))
  have hfin : ∀ a : (AF F)ˣ, {v : HeightOneSpectrum (𝓞 F) |
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∉ v.adicCompletionIntegers F}.Finite := fun a =>
    Filter.eventually_cofinite.mp ((a⁻¹ : (AF F)ˣ) : AF F).2.2
  refine ⟨s.biUnion fun a => (hfin a).toFinset, fun u hu v hv => ?_⟩
  obtain ⟨a, ha, hau⟩ := Set.mem_iUnion₂.mp (hs hu)
  have hav : ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
    by_contra hcon
    exact hv (Finset.mem_biUnion.mpr ⟨a, ha, (hfin a).mem_toFinset.mpr hcon⟩)
  have hh := ((IdeleGroup.mem_standardOpenSubgroup F).mp hau v).2
  have hu' : u⁻¹ = (a⁻¹ * u)⁻¹ * a⁻¹ := by group
  have hmul : ((u⁻¹ : (AF F)ˣ) : AF F).2 v =
      (((a⁻¹ * u)⁻¹ : (AF F)ˣ) : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v := by
    conv_lhs => rw [hu']
    rfl
  rw [hmul]
  exact mul_mem hh hav

theorem exists_inv_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ u ∈ D, Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ γ := by
  have hc : Continuous fun u : (AF F)ˣ => ((u⁻¹ : (AF F)ˣ) : AF F).2 v :=
    Units.continuous_val.comp ((IdeleGroup.continuous_finiteProj (K := F) v).comp continuous_inv)
  obtain ⟨γ, h0, hγ⟩ := exists_valued_bound v (hD.image hc)
  exact ⟨γ, h0, fun u hu => hγ _ (Set.mem_image_of_mem _ hu)⟩

theorem exists_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (A : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)),
      ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
        (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
        ∀ v, v.valuation F t ≤ if v ∈ T then A v else 1 := by
  obtain ⟨T₀, hT₀⟩ := exists_finset_inv_integral hD
  choose B _ hB using fun v => exists_inv_bound hD v
  have hG : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ : WithZero (Multiplicative ℤ), v ∈ S →
      ∀ x ∈ C v, Valued.v x ≤ γ := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨γ, -, h⟩ := exists_valued_bound v (hC v hv)
      exact ⟨γ, fun _ => h⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose G hG using hG
  refine ⟨T₀ ∪ S, fun v => max (G v) 1 * B v, fun u hu t h1 h2 v => ?_⟩
  have hinv : (u : AF F).2 v * ((u⁻¹ : (AF F)ˣ) : AF F).2 v = 1 :=
    congrArg (fun a : AF F => a.2 v) (Units.mul_inv u)
  have hx : algebraMap F (Fv F v) t =
      (algebraMap F (Fv F v) t * (u : AF F).2 v) * ((u⁻¹ : (AF F)ˣ) : AF F).2 v := by
    rw [mul_assoc, hinv, mul_one]
  have hval : v.valuation F t = Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) *
      Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) := by
    rw [← valued_algebraMap, ← map_mul, ← hx]
  have hfirst : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ max (G v) 1 := by
    by_cases hv : v ∈ S
    · exact (hG v hv _ (h1 v hv)).trans (le_max_left _ _)
    · have a : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hv
      exact a.trans (le_max_right _ _)
  by_cases hvT : v ∈ T₀ ∪ S
  · rw [if_pos hvT, hval]
    exact mul_le_mul' hfirst (hB v u hu)
  · rw [if_neg hvT, hval]
    have hvS : v ∉ S := fun h => hvT (Finset.mem_union_right _ h)
    have hvT₀ : v ∉ T₀ := fun h => hvT (Finset.mem_union_left _ h)
    have a1 : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hvS
    have a2 : Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ 1 := hT₀ u hu v hvT₀
    simpa using mul_le_mul' a1 a2

theorem valuation_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    v.valuation F (n : F) ≤ 1 := by
  have := HeightOneSpectrum.valuation_le_one (K := F) v (n : 𝓞 F)
  simpa using this

theorem exists_nat_mul_le_one (v : HeightOneSpectrum (𝓞 F)) (A : WithZero (Multiplicative ℤ)) :
    ∃ n : ℕ, 0 < n ∧ v.valuation F (n : F) * A ≤ 1 := by
  by_cases hA : A = 0
  · exact ⟨1, one_pos, by simp [hA]⟩
  have hlt : v.valuation F ((Ideal.absNorm v.asIdeal : ℕ) : F) < 1 := by
    have h := (v.valuation_lt_one_iff_mem (K := F) ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2
      (Ideal.absNorm_mem _)
    simpa using h
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hlt (Units.mk0 _ (inv_ne_zero hA))
  have hpos : 0 < Ideal.absNorm v.asIdeal := by
    refine Nat.pos_of_ne_zero fun h => v.ne_bot ?_
    exact Ideal.absNorm_eq_zero_iff.mp h
  refine ⟨Ideal.absNorm v.asIdeal ^ k, pow_pos hpos k, ?_⟩
  have h3 : v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) < A⁻¹ := by
    push_cast
    rw [map_pow]
    exact hk
  calc v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) * A ≤ A⁻¹ * A :=
        mul_le_mul' h3.le le_rfl
    _ = 1 := inv_mul_cancel₀ hA

theorem common_denominator (F : Type) [Field F] [NumberField F] (D : Set (AF F)ˣ) (hD : IsCompact D)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
      (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
      ∃ y : 𝓞 F, (y : F) = N * t := by
  obtain ⟨T, A, hA⟩ := exists_bound hD S C hC
  choose n hn0 hn using fun v => exists_nat_mul_le_one (F := F) v (A v)
  refine ⟨∏ v ∈ T, n v, Finset.prod_pos fun v _ => hn0 v, fun u hu t h1 h2 => ?_⟩
  refine exists_eq_of_forall_mem_adicCompletionIntegers F _ fun v => ?_
  rw [coe_mem_adicCompletionIntegers_iff, map_mul]
  have ht := hA u hu t h1 h2 v
  by_cases hv : v ∈ T
  · rw [if_pos hv] at ht
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hv
    have hN : v.valuation F (((∏ v ∈ T, n v : ℕ)) : F) ≤ v.valuation F (n v : F) := by
      rw [hm]
      push_cast
      rw [map_mul]
      simpa using mul_le_mul' (le_refl (v.valuation F (n v : F))) (valuation_natCast_le_one v m)
    exact (mul_le_mul' hN ht).trans (hn v)
  · rw [if_neg hv] at ht
    simpa using mul_le_mul' (valuation_natCast_le_one v (∏ v ∈ T, n v)) ht

end GlobalTheory.CompanionTheory.BasePsi.Den

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFactsStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_places_facts : ConjPlaces := by
  first | exact @GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | exact GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | (intros; apply GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceCutoffContinuousCompactSupport
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi.Test

theorem psiA_isTest : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    ∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiA S g a v) ∧ HasCompactSupport (psiA S g a v) := by
  intro F _ _ S g a hg v
  have hu : (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1 := by
    have h : ((a : AF F) * ((a⁻¹ : (AF F)ˣ) : AF F)).2 v = (1 : AF F).2 v := by rw [a.mul_inv]
    exact h
  have ha : (a : AF F).2 v ≠ 0 := left_ne_zero_of_mul_eq_one hu
  let e : (Unit → Fv F v) ≃ₜ Fv F v :=
    (Homeomorph.funUnique Unit (Fv F v)).trans (Homeomorph.mulLeft₀ ((a : AF F).2 v) ha)
  have he : ∀ y, e y = (a : AF F).2 v * y () := fun y => rfl
  have hO : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isClopen_integer _
  have hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have key : ∀ h : Fv F v → ℝ, Continuous h → HasCompactSupport h →
      Continuous (h ∘ e) ∧ HasCompactSupport (h ∘ e) := fun h h1 h2 =>
    ⟨h1.comp e.continuous, h2.comp_isClosedEmbedding e.isClosedEmbedding⟩
  by_cases hv : v ∈ S
  · have hfun : psiA S g a v = g v ∘ e := by
      funext y
      simp [psiA, hv, he]
    rw [hfun]
    exact key _ (hg v hv).1 (hg v hv).2
  · have hfun : psiA S g a v =
        (Set.indicator (v.adicCompletionIntegers F : Set (Fv F v)) (fun _ => (1 : ℝ))) ∘ e := by
      funext y
      simp [psiA, hv, he, Set.indicator_apply]
    rw [hfun]
    refine key _ (hO.continuous_indicator continuous_const) ?_
    exact HasCompactSupport.intro hOc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.CompanionTheory.BasePsi.Test

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiExpansionBounded
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem fold_abs {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) [SFinite μ] (S : Set X) (hS : μ S = 1)
    (Z T : X × X → ℂ) (hZ : StronglyMeasurable Z) (hT : StronglyMeasurable T) (B B₂ : ℝ)
    (hB : ∀ v, ‖Z v‖ ≤ B) (hB₂ : ∀ v, ‖T v‖ ≤ B₂)
    (c a : ι → X → ℂ) (hc : ∀ i, StronglyMeasurable (c i)) (hc1 : ∀ i x, ‖c i x‖ = 1)
    (ha : ∀ y, Summable fun i => ‖a i y‖) (hTs : ∀ y x, T (y, x) = ∑' i, c i x * a i y) :
    ∫ y in S, ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y ∂μ = ∫ v in S ×ˢ S, Z v * T v ∂(μ.prod μ) := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simp [hS]⟩
  have hZs : ∀ y, StronglyMeasurable fun x => Z (y, x) := fun y => hZ.comp_measurable measurable_prodMk_left
  have inner : ∀ y, ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y = ∫ x in S, Z (y, x) * T (y, x) ∂μ := by
    intro y
    have hint : ∀ i, Integrable (fun x => c i x * Z (y, x) * a i y) (μ.restrict S) := by
      intro i
      refine Integrable.of_bound ((((hc i).mul (hZs y)).mul stronglyMeasurable_const).aestronglyMeasurable)
        (B * ‖a i y‖) (ae_of_all _ fun x => ?_)
      rw [norm_mul, norm_mul, hc1, one_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    have hsum : Summable fun i => ∫ x in S, ‖c i x * Z (y, x) * a i y‖ ∂μ := by
      have h : ∀ i, ∫ x in S, ‖c i x * Z (y, x) * a i y‖ ∂μ = (∫ x in S, ‖Z (y, x)‖ ∂μ) * ‖a i y‖ := by
        intro i
        simp only [norm_mul, hc1, one_mul]
        exact integral_mul_const _ _
      simp only [h]
      exact (ha y).mul_left _
    have h1 := integral_tsum_of_summable_integral_norm hint hsum
    calc ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y
        = ∑' i, ∫ x in S, c i x * Z (y, x) * a i y ∂μ :=
          tsum_congr fun i => (integral_mul_const _ _).symm
      _ = ∫ x in S, ∑' i, c i x * Z (y, x) * a i y ∂μ := h1
      _ = ∫ x in S, Z (y, x) * T (y, x) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          show ∑' i, c i x * Z (y, x) * a i y = Z (y, x) * T (y, x)
          rw [hTs, ← tsum_mul_left]
          exact tsum_congr fun i => by ring
  simp only [inner]
  haveI hfin : IsFiniteMeasure ((μ.prod μ).restrict (S ×ˢ S)) := by
    rw [← Measure.prod_restrict]; infer_instance
  have hi : IntegrableOn (fun v => Z v * T v) (S ×ˢ S) (μ.prod μ) := by
    refine Integrable.of_bound ((hZ.mul hT).aestronglyMeasurable) (B * B₂) (ae_of_all _ fun v => ?_)
    rw [norm_mul]
    exact mul_le_mul (hB v) (hB₂ v) (norm_nonneg _) ((norm_nonneg _).trans (hB v))
  exact (setIntegral_prod (fun v => Z v * T v) hi).symm

theorem fj_fold_mean : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (g : G D n) (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p, ∀ B : ℝ, (∀ y x, ‖zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))‖ ≤ B) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g))) → FJ M m ψ b₀ F g φ = ∫ v in m.𝓕 ×ˢ m.𝓕, zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) * conj (th ψ b₀ φ 0 v.2 v.1) ∂(m.μ.prod m.μ) := by
  intro D n ρ p hn M m ψ hψ b₀ F hF g θ hθ φ hφ B hB hZ
  obtain ⟨hH, hfd, h1⟩ := m.hμ
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : SFinite m.μ := inferInstance
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨by simp [h1]⟩
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  obtain ⟨-, -, hnorm, -, -, hcont⟩ := _root_.GlobalTheory.CompanionTheory.FJE.chv_facts (ρ := ρ) (p := p) ψ hψ b₀
  have hφc : Continuous φ := GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ ⟨φ, hφ⟩
  have hφi : Integrable φ m.μ := GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ m.μ ⟨φ, hφ⟩
  obtain ⟨B₂, hB₂⟩ := _root_.GlobalTheory.CompanionTheory.FJE.periodisation_bound θ hθ φ hφ
  have hD := _root_.GlobalTheory.CompanionTheory.FJE.dsum_stronglyMeasurable ψ hψ b₀ φ hφc.stronglyMeasurable (fun y => (hB₂ y).1)
  set Z : Mx D ρ p × Mx D ρ p → ℂ := fun v => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) with hZdef
  have hpcm : StronglyMeasurable fun y => pc M m ψ b₀ F (M.sh y * g) :=
    hZ.integral_prod_right' (ν := m.μ.restrict m.𝓕)
  have hpcb : ∀ y, ‖pc M m ψ b₀ F (M.sh y * g)‖ ≤ B := by
    intro y
    have h := norm_integral_le_of_norm_le_const (μ := m.μ.restrict m.𝓕)
      (f := fun x => zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))) (C := B) (ae_of_all _ fun x => hB y x)
    show ‖∫ x in m.𝓕, zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g)) ∂m.μ‖ ≤ B
    simpa [Measure.real, h1] using h
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hpcb 0)
  have hP : Integrable (fun y => pc M m ψ b₀ F (M.sh y * g) * conj (φ y)) m.μ := by
    refine (hφi.norm.const_mul B).mono'
      (hpcm.aestronglyMeasurable.mul (Complex.continuous_conj.comp hφc).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hpcb y) (norm_nonneg _)
  have hPξ : ∀ (y : Mx D ρ p) (ξ : Matrix (Fin ρ) (Fin p) D.host.E),
      pc M m ψ b₀ F (M.sh (rt ξ + y) * g) * conj (φ (rt ξ + y)) =
        (∫ x in m.𝓕, conj (chv ψ b₀ x (rt ξ)) * Z (y, x) ∂m.μ) * conj (φ (rt ξ + y)) := by
    intro y ξ
    rw [← GlobalTheory.CompanionTheory.FJE.sh_add M (rt ξ) y, mul_assoc, _root_.GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh M m ψ hψ b₀ F hF ξ (M.sh y * g)]
  have hfold := GlobalTheory.T.integral_eq_fundamental_domain_lattice_sum m _ hP
  have hmain := fold_abs m.μ m.𝓕 h1 Z (fun v => conj (dsum ψ b₀ φ v.2 v.1)) hZ
    (Complex.continuous_conj.comp_stronglyMeasurable hD) B B₂ (fun v => hB v.1 v.2)
    (fun v => ?_)
    (fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) x => conj (chv ψ b₀ x (rt ξ)))
    (fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) y => conj (φ (rt ξ + y)))
    (fun ξ => (Complex.continuous_conj.comp
      (hcont.comp (continuous_id.prodMk continuous_const))).stronglyMeasurable)
    (fun ξ x => by rw [RCLike.norm_conj]; exact hnorm _ _)
    (fun y => by simpa only [RCLike.norm_conj] using (hB₂ y).1)
    (fun y x => by
      show conj (dsum ψ b₀ φ x y) = _
      rw [dsum, Complex.conj_tsum]
      exact tsum_congr fun ξ => map_mul _ _ _)
  · show ∫ y, pc M m ψ b₀ F (M.sh y * g) * conj (φ y) ∂m.μ = _
    rw [hfold]
    simp only [hPξ]
    rw [hmain]
    simp only [th_zero]
    rfl
  · rw [RCLike.norm_conj, dsum]
    have hs : Summable fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖chv ψ b₀ v.2 (rt ξ) * φ (rt ξ + v.1)‖ := by
      simpa only [norm_mul, hnorm, one_mul] using (hB₂ v.1).1
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    simpa only [norm_mul, hnorm, one_mul] using (hB₂ v.1).2

end GlobalTheory.CompanionTheory.FJE
end
end

