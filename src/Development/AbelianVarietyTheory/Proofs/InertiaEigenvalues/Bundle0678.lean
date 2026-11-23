module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRelationsExtendToPlaceCommonEigen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

variable {D : D7}

theorem psi_ne_zero' (ψ : AddChar (AF D.host.F) ℂ) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem heisO_injective (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) {f g : WO S T → ℂ}
    (h : heisO ψ S T w f = heisO ψ S T w g) : f = g := by
  funext x
  have := congrFun h (x - w)
  simp only [heisO, sub_add_cancel] at this
  exact mul_left_cancel₀ (psi_ne_zero' ψ _) this

theorem heisO_fun_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    heisO ψ S T w (0 : WO S T → ℂ) = 0 := by
  funext x
  simp [heisO]

theorem comb_eq_linearCombination (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ)
    (X : WO S T → ℂ) : comb ψ S T c X = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u X) c := by
  rw [Finsupp.linearCombination_apply]
  rfl

theorem comb_sum_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ι : Type} (s : Finset ι) (r : ι → WO S T)
    (z : ι → ℂ) (X : WO S T → ℂ) :
    comb ψ S T (∑ i ∈ s, Finsupp.single (r i) (z i)) X = ∑ i ∈ s, z i • heisO ψ S T (r i) X := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb_eq_linearCombination, map_sum]
  simp only [Finsupp.linearCombination_single]

theorem comb_fun_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) :
    comb ψ S T c (0 : WO S T → ℂ) = 0 := by
  unfold comb Finsupp.sum
  exact Finset.sum_eq_zero fun u _ => by
    show c u • heisO ψ S T u 0 = 0
    rw [heisO_fun_zero, smul_zero]

theorem relOff_factor {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Sb : Finset (FinPl D)} {p f : WO S T → ℂ}
    (hR : RelOff ψ S T Sb p f) (w : WO S T) (s : Finset (WO S T)) (a e : WO S T → ℂ) (r : WO S T → WO S T)
    (hr : ∀ u ∈ s, OffPl Sb (r u))
    (hp : ∀ u ∈ s, heisO ψ S T u p = e u • heisO ψ S T w (heisO ψ S T (r u) p))
    (hf : ∀ u ∈ s, heisO ψ S T u f = e u • heisO ψ S T w (heisO ψ S T (r u) f))
    (h0 : ∑ u ∈ s, a u • heisO ψ S T u p = 0) : ∑ u ∈ s, a u • heisO ψ S T u f = 0 := by
  classical
  set c' : WO S T →₀ ℂ := ∑ u ∈ s, Finsupp.single (r u) (a u * e u) with hc'
  have key : ∀ X : WO S T → ℂ, (∀ u ∈ s, heisO ψ S T u X = e u • heisO ψ S T w (heisO ψ S T (r u) X)) →
      ∑ u ∈ s, a u • heisO ψ S T u X = heisO ψ S T w (comb ψ S T c' X) := by
    intro X hX
    rw [hc', comb_sum_single, GlobalTheory.SplitScalar.heisO_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hX u hu, GlobalTheory.SplitScalar.heisO_smul, smul_smul]
  have hsupp : ∀ u ∈ c'.support, OffPl Sb u := by
    intro u hu
    rw [hc'] at hu
    obtain ⟨x, hx, hx'⟩ := Finsupp.mem_support_finsetSum u hu
    have heq : u = r x := Finset.mem_singleton.1 (Finsupp.support_single_subset hx')
    rw [heq]
    exact hr x hx
  have hp0 : comb ψ S T c' p = 0 := by
    apply heisO_injective ψ S T w
    rw [← key p hp, h0, heisO_fun_zero]
  rw [key f hf, hR c' hsupp hp0, heisO_fun_zero]

theorem offPl_zero (Sb : Finset (FinPl D)) (S T : HSp D) : OffPl Sb (0 : WO S T) :=
  ⟨by ext i j; simp, fun _ _ _ _ _ _ => by simp⟩

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (z : ℂ) (X : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u z) X = z • heisO ψ S T u X := by
  unfold comb
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem isHalf_one_sub {S T : HSp D} {b : AE D} (hb2 : b * b = b) (u : WO S T) : IsHalf (1 - b) (u - b • u) := by
  intro i j
  show (1 - b) * (u i j - b * u i j) = u i j - b * u i j
  rw [mul_sub, sub_mul, sub_mul, one_mul, one_mul, ← mul_assoc, hb2, sub_self, sub_zero]

theorem heisO_decomp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {b : AE D} (hb2 : b * b = b) (hcb : cA D b = b)
    (u u0 : WO S T) (X : WO S T → ℂ) (z : ℂ) (hX : heisO ψ S T (b • u - b • u0) X = z • X) :
    heisO ψ S T u X = ((ψ (symplOH S T (b • u0) (u - b • u0)))⁻¹ * z) •
      heisO ψ S T (b • u0) (heisO ψ S T (u - b • u) X) := by
  have hab : cA D (1 - b) * b = 0 := by rw [map_sub, map_one, hcb, sub_mul, one_mul, hb2, sub_self]
  have horth0 : symplO S T (u - b • u) (b • u - b • u0) = 0 :=
    GlobalTheory.SplitScalar.symplO_eq_zero S T hab (isHalf_one_sub hb2 u)
      (GlobalTheory.SplitScalar.isHalf_sub (GlobalTheory.SplitScalar.isHalf_smul hb2 u) (GlobalTheory.SplitScalar.isHalf_smul hb2 u0))
  have h1 : heisO ψ S T (b • u0) (heisO ψ S T (u - b • u) (heisO ψ S T (b • u - b • u0) X)) =
      ψ (symplOH S T (b • u0) (u - b • u0)) • heisO ψ S T u X := by
    rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T horth0, GlobalTheory.SplitScalar.heisO_heisO, sub_add_sub_cancel,
      add_sub_cancel]
  rw [hX, GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_smul] at h1
  rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (psi_ne_zero' ψ _), one_smul]

theorem offPl_sub_idem {S T : HSp D} {Sb : Finset (FinPl D)} {v : FinPl D} {u : WO S T}
    (hu : OffPl (dropPl Sb v) u) : OffPl Sb (u - idem D (.inl v) • u) := by
  classical
  obtain ⟨hidem, horth, -, hfin, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  refine ⟨Matrix.ext fun i j => ?_, fun q hq ε hε i j => ?_⟩
  · have h : infPart D (u i j) = 0 := congrFun (congrFun hu.1 i) j
    show infPart D (u i j - idem D (.inl v) * u i j) = 0
    rw [map_sub, map_mul, (hfin v).1, h, zero_mul, sub_zero]
  · rw [placeIdem_eq hε]
    show idem D (.inl q) * (u i j - idem D (.inl v) * u i j) = 0
    by_cases hqv : q = v
    · rw [hqv, mul_sub, ← mul_assoc, hidem, sub_self]
    · have hq' : q ∈ dropPl Sb v := by unfold dropPl; exact Finset.mem_erase.2 ⟨hqv, hq⟩
      have h1 := hu.2 q hq' _ ((hfin q).2.2) i j
      rw [placeIdem_eq ((hfin q).2.2)] at h1
      rw [mul_sub, h1, ← mul_assoc, horth (.inl q) (.inl v) (fun h => hqv (Sum.inl.inj h)), zero_mul, sub_zero]

theorem relOff_dropPl_of_coEig : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D))
    (v : FinPl D), v ∈ Sb → ∀ (p f : WO S T → ℂ), (∀ u, IsHalf (idem D (.inl v)) u → CoEig ψ S T p f u ∨
      ∃ l, IsHalf (idem D (.inl v)) l ∧ CoEig ψ S T p f l ∧ ψ (symplO S T l u) ≠ 1) →
    RelOff ψ S T Sb p f → RelOff ψ S T (dropPl Sb v) p f := by
  classical
  intro D ψ S T Sb v _ p f hH hR c hc hcp
  have hrest : ∀ u : WO S T, OffPl (dropPl Sb v) u → OffPl Sb (u - idem D (.inl v) • u) :=
    fun u hu => offPl_sub_idem hu
  obtain ⟨hidem, -, hconj, -, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  obtain ⟨b, hb⟩ : ∃ b, b = idem D (.inl v) := ⟨_, rfl⟩
  rw [← hb] at hH hrest
  have hb2 : b * b = b := by rw [hb]; exact hidem _
  have hcb : cA D b = b := by rw [hb]; exact hconj _
  by_cases hp0 : p = 0
  · have hf0 : f = 0 := by
      have h1 := hR (Finsupp.single 0 1) (fun u hu => by
        rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]; exact offPl_zero Sb S T) (by
        rw [comb_single, GlobalTheory.SplitScalar.heisO_zero, one_smul, hp0])
      rwa [comb_single, GlobalTheory.SplitScalar.heisO_zero, one_smul] at h1
    rw [hf0, comb_fun_zero]

  have hcl : ∀ l : {l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l}, ∃ z : ℂ, z ≠ 0 ∧
      heisO ψ S T l.1 p = z • p ∧ heisO ψ S T l.1 f = z • f := by
    rintro ⟨l, -, z, h1, h2⟩
    refine ⟨z, fun hz => hp0 ?_, h1, h2⟩
    apply heisO_injective ψ S T l
    rw [h1, hz, zero_smul, heisO_fun_zero]
  choose cl hcl0 hclp _ using hcl
  obtain ⟨χ, hχ⟩ : ∃ χ : WO S T → {l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l} → ℂ,
      ∀ u l, χ u l = ψ (symplO S T l.1 u) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : (WO S T → ℂ) → ({l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l} → ℂ) → (WO S T → ℂ),
      ∀ X k, V X k = ∑ u ∈ c.support with χ u = k, c u • heisO ψ S T u X := ⟨_, fun _ _ => rfl⟩
  have hcomb : ∀ X, ∑ k ∈ c.support.image χ, V X k = comb ψ S T c X := by
    intro X
    simp only [hV]
    exact Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_image_of_mem χ hu) _
  have heig : ∀ k ∈ c.support.image χ, ∀ l, GlobalTheory.SplitScalar.heisL ψ S T l.1 (V p k) = (k l * cl l) • V p k := by
    intro k _ l
    rw [GlobalTheory.SplitScalar.heisL_apply, hV, GlobalTheory.SplitScalar.heisO_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← (Finset.mem_filter.1 hu).2, hχ, GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_comm, hclp,
      GlobalTheory.SplitScalar.heisO_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hVp : ∀ k ∈ c.support.image χ, V p k = 0 :=
    GlobalTheory.joint_eigenvectors_eq_zero_of_sum_eq_zero _ _ _ (fun l => GlobalTheory.SplitScalar.heisL ψ S T l.1)
      (fun k l => k l * cl l) (V p) _ heig
      (fun k1 _ k2 _ h => funext fun l => mul_right_cancel₀ (hcl0 l) (congrFun h l)) (by rw [hcomb]; exact hcp)
  have hVf : ∀ k ∈ c.support.image χ, V f k = 0 := by
    intro k hk
    obtain ⟨u0, _, hu0k⟩ := Finset.mem_image.1 hk
    have hCo : ∀ u ∈ c.support.filter (fun u => χ u = k), ∃ z : ℂ,
        heisO ψ S T (b • u - b • u0) p = z • p ∧ heisO ψ S T (b • u - b • u0) f = z • f := by
      intro u hu
      have hχu := (Finset.mem_filter.1 hu).2
      rcases hH _ (GlobalTheory.SplitScalar.isHalf_sub (GlobalTheory.SplitScalar.isHalf_smul hb2 u)
          (GlobalTheory.SplitScalar.isHalf_smul hb2 u0)) with h | ⟨l, hl, hlco, hne⟩
      · exact h
      · exfalso
        apply hne
        have e1 : ψ (symplO S T l u) = ψ (symplO S T l u0) := by
          have := congrFun (hχu.trans hu0k.symm) ⟨l, hl, hlco⟩
          rwa [hχ, hχ] at this
        have hbl : ∀ x, symplO S T l (b • x) = symplO S T l x := fun x => by
          conv_lhs => rw [← hcb]
          rw [← GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.SplitScalar.isHalf_iff _ l).1 hl]
        have e2 : symplO S T l (b • u - b • u0) + symplO S T l (b • u0) = symplO S T l (b • u) := by
          rw [← GlobalTheory.LatVac.symplO_add_right, sub_add_cancel]
        rw [hbl, hbl] at e2
        have e3 := congrArg ψ e2
        rw [AddChar.map_add_eq_mul, e1] at e3
        exact mul_right_cancel₀ (psi_ne_zero' ψ _) (e3.trans (one_mul _).symm)
    choose! eco hecp hecf using hCo
    have key := relOff_factor hR (b • u0) (c.support.filter fun u => χ u = k) c
      (fun u => (ψ (symplOH S T (b • u0) (u - b • u0)))⁻¹ * eco u) (fun u => u - b • u)
      (fun u hu => hrest u (hc u (Finset.mem_filter.1 hu).1))
      (fun u hu => heisO_decomp ψ S T hb2 hcb u u0 p _ (hecp u hu))
      (fun u hu => heisO_decomp ψ S T hb2 hcb u u0 f _ (hecf u hu))
      (by rw [← hV]; exact hVp k hk)
    rw [hV]
    exact key
  rw [← hcomb f]
  exact Finset.sum_eq_zero hVf

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseLocalArtinContinuousOnInertia
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ArtinInvCont

theorem absoluteGaloisAbelianization_t2Space (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] :
    T2Space (GlobalTheory.HeckeGal.Gab E Ω) := by
  unfold GlobalTheory.HeckeGal.Gab TopologicalAbelianization
  haveI : IsClosed (((commutator (G E Ω)).topologicalClosure : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

theorem continuous_localIdele' (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    Continuous (Neutral.B1.localIdele E v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_mulSingle (A := fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E) v
  have hs : Continuous (Neutral.B1.finiteSingle E v) := (RestrictedProduct.continuous_inclusion hle).comp hf
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const hs

theorem isCompact_valOne (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact {x : (w.adicCompletion E)ˣ | Valued.v (x : w.adicCompletion E) = 1} := by
  rw [Units.isEmbedding_val₀.isInducing.isCompact_iff]
  have e : (Units.val '' {x : (w.adicCompletion E)ˣ | Valued.v (x : w.adicCompletion E) = 1}) =
      {y : w.adicCompletion E | Valued.v y = 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      have h0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      exact ⟨Units.mk0 y h0, hy, rfl⟩
  rw [e]
  have hK : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  refine hK.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {y : w.adicCompletion E | Valued.v y ≤ 1} := by
      have : {y : w.adicCompletion E | Valued.v y ≤ 1} = (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
        ext y
        exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).symm
      rw [this]
      exact hK.isClosed
    have h2 : IsOpen {y : w.adicCompletion E | Valued.v y < 1} := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      rw [Valued.mem_nhds]
      refine ⟨1, fun z hz => ?_⟩
      have hz' : Valued.v (z - y) < 1 := by simpa using hz
      have : z = (z - y) + y := by ring
      show Valued.v z < 1
      rw [this]
      exact Valuation.map_add_lt _ hz' hy
    have e2 : {y : w.adicCompletion E | Valued.v y = 1} =
        {y : w.adicCompletion E | Valued.v y ≤ 1} ∩ {y : w.adicCompletion E | Valued.v y < 1}ᶜ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
      exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
    rw [e2]
    exact h1.inter h2.isClosed_compl
  · intro y hy
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (le_of_eq hy)

theorem continuous_inv_on_ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (a : Weil h →* (w.adicCompletion E)ˣ), GlobalTheory.HeckeGal.IsGlobalArtin art → (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) → (∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ) → Continuous fun σ : Ine (F := E) A => a (ineIncl h σ) := by
  intro E Ω _ _ _ _ _ A w h art a ha hord hart
  haveI := absoluteGaloisAbelianization_t2Space E Ω
  let K : Set (w.adicCompletion E)ˣ := {x | Valued.v (x : w.adicCompletion E) = 1}
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_valOne E w)
  let f : K → GlobalTheory.HeckeGal.Gab E Ω := fun x => art (Neutral.B1.localIdele E w x.1)
  have hf : Continuous f :=
    (ha.quot.continuous.comp (continuous_localIdele' E w)).comp continuous_subtype_val
  have hinj : Function.Injective f := fun x y hxy =>
    Subtype.ext (GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w hxy)
  have hemb := hf.isClosedEmbedding hinj
  have hmem : ∀ σ : Ine (F := E) A, a (ineIncl h σ) ∈ K := by
    intro σ
    have hd : deg (ineIncl h σ) = 0 := by
      rw [deg_eq (a := 0) (b := 0) (actsAs_zero_iff.mpr σ.2)]
      simp
    have ho := hord (ineIncl h σ)
    rw [hd, neg_zero, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at ho
    show Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    rw [← WithZero.exp_log (by simp : Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0),
      ho, WithZero.exp_zero]
  let g : Ine (F := E) A → K := fun σ => ⟨a (ineIncl h σ), hmem σ⟩
  have hg : Continuous g := by
    rw [hemb.isInducing.continuous_iff]
    have e : f ∘ g = fun σ : Ine (F := E) A => GlobalTheory.HeckeGal.toAb E Ω (σ : G E Ω) :=
      funext fun σ => hart (ineIncl h σ)
    rw [e]
    exact continuous_quot_mk.comp continuous_subtype_val
  exact continuous_subtype_val.comp hg

end GlobalTheory.ArtinInvCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNeg
section
namespace CrystallineMultiplicity
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CompanionTheory.CharInv

theorem isCrys_and_multV_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  intro l _ P AI T K LL μ a hμ hm
  obtain ⟨h1, -, h2⟩ := GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL 0
  rw [zpow_zero] at h1
  simp only [zpow_zero] at h2
  have hρ : ∀ g x, charRep (1 : ↥(GK K) →* (↥LL.1)ˣ) g x = (μ g : ↥LL.1) • charRep μ⁻¹ g x :=
    fun g x => by simp [charRep]
  refine ⟨(GlobalTheory.TopSteps.CrysRules.isCrys_iff T K LL _ _ μ hρ hμ).2 h1, fun τ c => ?_⟩
  have hs := GlobalTheory.TopSteps.CrysRules.multV_shift T K LL _ _ μ hρ hμ τ (a τ)
    (fun b => by rw [hm, Multiset.count_singleton]; split_ifs <;> rfl) c
  rw [← hs, h2]
  exact if_congr (by omega) rfl rfl

end GlobalTheory.CompanionTheory.CharInv

end

end CrystallineMultiplicity
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
theorem _root_.GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  first | exact @CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | exact CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | (intros; apply CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSpherical
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isUnramChar_of_isCusp_of_isSpherical : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (x : IrrGL (k := k)), x.IsCusp → IsSpherical x.rep → x.IsUnramChar := by
  intro hG hBZ hZ k _ _ _ _ _ x hx hs
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have h1 := _root_.GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα
  have h2 : HasSupport x.rep {x} := hasSupport_self hx
  have he := GlobalTheory.T.supercuspidalSupport_unique_GL hG hBZ hZ k x _ _ h1 h2
  have hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i)) := by
    rw [he]; exact Multiset.mem_singleton_self x
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertiaStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localInertia_iff_mem_placeInertia : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p)),
      (∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x)) →
      ∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  first | exact @GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | exact GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | (intros; apply GlobalTheory.DecInertia.inertiaK_iff_mem_Ine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCentralCharacter
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem prod_roots_prod_of_monic {ι : Type*} (s : Multiset ι) (p : ι → ℂ[X]) (hp : ∀ i, (p i).Monic) :
    (s.map p).prod.roots.prod = (s.map fun i => (p i).roots.prod).prod := by
  have h0 : (0 : ℂ[X]) ∉ s.map p := by
    rw [Multiset.mem_map]
    rintro ⟨i, -, hi⟩
    exact (hp i).ne_zero hi
  rw [Polynomial.roots_multiset_prod _ h0, Multiset.bind_map, Multiset.prod_bind]

end GlobalTheory.LocLanglands
end

