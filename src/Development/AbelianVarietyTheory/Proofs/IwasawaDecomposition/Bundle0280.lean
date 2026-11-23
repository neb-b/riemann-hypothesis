module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCurveLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

noncomputable section

namespace GlobalTheory.Mem.Col2.CurveLat

theorem exists_periodPair_mul_image {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : 𝓞 K →+* ℂ) (hσ : Function.Injective σ) (a : 𝓞 K) (ha : (σ a).im ≠ 0) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ c : 𝓞 K, z = δ * σ c := by
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans hK)
  have hs : ∀ x : 𝓞 K, σ x = b.repr x 0 * σ (b 0) + b.repr x 1 * σ (b 1) := by
    intro x
    have := congrArg σ (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ (b 0) ≠ 0 := (map_ne_zero_iff σ hσ).2 (b.ne_zero 0)
  have h0 : (σ (b 1) * starRingEnd ℂ (σ (b 0))).im ≠ 0 := by
    intro h0
    have e := hs (a * b 0)
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ (b 0))).im) e
    simp only [map_mul] at e'
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨δ * σ (b 0), δ * σ (b 1), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e0
    have e : (x : ℂ) * σ (b 0) + (y : ℂ) * σ (b 1) = 0 := by
      apply mul_left_cancel₀ hδ
      simp only [Complex.real_smul] at e0
      linear_combination e0
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 1)).im * e1 - (σ (b 1)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 0)).re * e2 - (σ (b 0)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m • b 0 + n • b 1, by simp; ring⟩
    · rintro ⟨x, rfl⟩
      exact ⟨b.repr x 0, b.repr x 1, by rw [hs x]; ring⟩

theorem not_isIntegral_half : ¬ IsIntegral ℤ (1 / 2 : ℂ) := by
  intro h
  have h1 : IsIntegral ℤ (1 / 2 : ℚ) := by
    refine (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).1 ?_
    simpa using h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  have h2 : (2 * y : ℚ) = 1 := by
    simp only [eq_intCast] at hy
    rw [hy]; norm_num
  have h3 : 2 * y = 1 := by exact_mod_cast h2
  omega

theorem not_isIntegral_of_re {z : ℂ} (hz : z.re = 1 / 4) : ¬ IsIntegral ℤ z := by
  intro h
  have h1 : IsIntegral ℤ (starRingEnd ℂ z) := h.map (starRingEnd ℂ).toIntAlgHom
  have h2 := h.add h1
  rw [Complex.add_conj, hz] at h2
  apply not_isIntegral_half
  have e : ((2 * (1 / 4) : ℝ) : ℂ) = 1 / 2 := by
    push_cast
    norm_num
  rwa [e] at h2

variable {R : Ranks} (H : Host R)

def embO : 𝓞 H.K →+* ℂ := (H.φ₀.comp H.K.val.toRingHom).comp (algebraMap (𝓞 H.K) H.K)

theorem mem_lamOf_top (δ z : ℂ) : z ∈ Th.lamOf H ⊤ δ ↔ ∃ c : 𝓞 H.K, z = δ * embO H c := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, -, rfl⟩ := hx
      exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by rw [map_add (f := _), mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, by rw [map_neg, mul_neg]⟩
  · rintro ⟨c, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, rfl⟩

theorem exists_periodPair_lamOf (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Th.lamOf H ⊤ δ ↔ z ∈ L.lattice := by
  have hK : Module.finrank ℚ H.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq
  have hinj : Function.Injective (embO H) :=
    (H.φ₀.comp H.K.val.toRingHom).injective.comp RingOfIntegers.coe_injective
  have ha : (embO H ⟨_, HostK.isIntegral_half H⟩).im ≠ 0 := by
    have e : embO H ⟨_, HostK.isIntegral_half H⟩ = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2 := by
      rw [← HostK.φ₀_sqrt]
      change (H.φ₀.comp H.K.val.toRingHom) ((1 + (⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ : H.K)) / 2) = _
      rw [map_div₀, map_add (f := _), map_one, map_ofNat]
      rfl
    have hd : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
    rw [e]
    simp [hd.ne']
  obtain ⟨L, hL⟩ := exists_periodPair_mul_image hK (embO H) hinj _ ha δ hδ
  exact ⟨L, fun z => by rw [mem_lamOf_top, hL]⟩

theorem not_mem_lamOf (δ : ℂ) (hδ : δ ≠ 0) {z : ℂ} (hz : z.re = 1 / 4) : δ * z ∉ Th.lamOf H ⊤ δ := by
  rw [mem_lamOf_top]
  rintro ⟨c, hc⟩
  apply not_isIntegral_of_re hz
  rw [mul_left_cancel₀ hδ hc]
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) c).map (embO H).toIntAlgHom

end GlobalTheory.Mem.Col2.CurveLat

namespace GlobalTheory.Mem.Col2

open CurveLat

theorem exists_curve_lattice : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  intro R H
  obtain ⟨L₁, h₁⟩ := exists_periodPair_lamOf H 1 one_ne_zero
  have hΔ := (GlobalTheory.LatticeInvariants.invariants_dictionary L₁ _ h₁).2.2.1
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (Th.lamOf H ⊤ 1)) (n := 12) (by norm_num)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hδ]; norm_num)
  obtain ⟨L, hL⟩ := exists_periodPair_lamOf H δ hδ0
  refine ⟨δ, L, δ, hδ, AddSubgroup.ext fun z => (hL z).symm, ?_, ?_, ?_⟩
  · exact (mem_lamOf_top H δ _).2 ⟨1, by rw [map_one]; ring⟩
  · have := not_mem_lamOf H δ hδ0 (z := (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring
  · have := not_mem_lamOf H δ hδ0 (z := (1 - Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocCompSplit
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU

theorem exists_locComp_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsAdmissible σ.ρ ∧ π.IsLocComp w σ ∧ (IsUnramU π.V w ↔ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := n))) := by
  intro E _ _ _ n π w hw
  obtain ⟨e, he⟩ := _root_.GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := _root_.GlobalTheory.DefU.LocAdm.exists_admissible_comp E n π w
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hsym : ∀ x : locU n w, e.symm (cLoc w (x : UA E n)) = x := fun x => by
    rw [← he, e.symm_apply_apply]
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) σ₀.V :=
    σ₀.ρ.comp e.symm.toMulEquiv.toMonoidHom
  have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
  let σ : SmIrr (GL (Fin n) (w.adicCompletion E)) :=
    { V := σ₀.V
      ρ := ρ
      smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
      irred := GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ₀.ρ e.symm.toMulEquiv σ₀.irred }
  have hf' : ∀ (x : locU n w) v, f (σ₀.ρ x v) = RU E n x (f v) := hf
  refine ⟨σ, GlobalTheory.CuspMult.isAdmissible_comp_equiv σ₀.ρ e.symm hadm, ⟨σ.irred, f, hf0, hfm, fun x v => ?_⟩, ?_, ?_⟩
  · change f (ρ (cLoc w (x : UA E n)) v) = _
    rw [hρ, hsym, hf']
  · rintro ⟨φ, hφ, h0, hK⟩
    let F : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hsup := (_root_.GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π.V σ₀.V σ₀.V π.rep (locU n w).subtype σ₀.ρ σ₀.ρ
      π.isIrreducible_rep σ₀.irred σ₀.irred (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ₀.ρ σ₀.irred
      (fun h : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => h.toLinearMap)
      (fun h g u => LinearMap.congr_fun (h.isIntertwining' g) u)
      {k | cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n)} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hK k k.2 hk))
      (hsup ▸ Submodule.mem_top)
    intro hb
    have hmem : v ∈ fixed ρ (GlobalTheory.LFun.KGL w (n := n)) := fun g => by
      have h1 : σ₀.ρ (e.symm g.1) v = v := hv _ (by
        have h2 : cLoc w ((e.symm g.1 : locU n w) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
          rw [hcl]
          exact g.2
        exact h2)
      simpa [hρ] using h1
    have hb' : fixed ρ (GlobalTheory.LFun.KGL w (n := n)) = ⊥ := hb
    rw [hb'] at hmem
    exact hv0 ((Submodule.mem_bot _).1 hmem)
  · intro hsph
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hinj : Function.Injective f := by
      have hk := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ₀.irred).2 (LinearMap.ker f) (fun g u hu => by
        rw [LinearMap.mem_ker] at hu ⊢
        rw [hf', hu, map_zero])
      rcases hk with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · exact absurd (LinearMap.ker_eq_top.1 h) hf0
    refine ⟨f v, hfm v, fun h => hv0 (hinj (h.trans (map_zero f).symm)), fun x hx hk => ?_⟩
    have h1 : σ₀.ρ (⟨x, hx⟩ : locU n w) v = v := by
      have h2 : ρ (cLoc w x) v = v := by simpa using hv ⟨_, hk⟩
      rwa [hρ, hsym (⟨x, hx⟩ : locU n w)] at h2
    have h3 := hf' ⟨x, hx⟩ v
    rw [h1] at h3
    exact h3.symm

end GlobalTheory.DefU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosIsQuotInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Mem.QuotHaar

theorem exists_pos_isQuotInt : ∀ (D : D7) (V : HSp D), V.SigOK → ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ r : ℝ, 0 < r ∧
    ∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → IntegrableOn φ 𝓕 ν →
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V r φ (∫ g in 𝓕, φ g ∂ν) := by
  intro D V hV ν hν
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ₀, hμ₀, huniq⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV
  haveI := hμ₀.1
  obtain ⟨-, 𝓕₀, h𝓕₀⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ₀ hμ₀.1
  have e : ν = Measure.haarScalarFactor ν μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul ν μ₀
  have cpos : 0 < Measure.haarScalarFactor ν μ₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ₀
  set c := Measure.haarScalarFactor ν μ₀
  refine ⟨c, by exact_mod_cast cpos, ?_⟩
  intro 𝓕 h𝓕 φ hφ hint
  refine ⟨⟨(μ₀, 𝓕₀), hμ₀, h𝓕₀⟩, ?_⟩
  rintro ⟨m, F'⟩ ⟨hm, hF'⟩
  obtain rfl : m = μ₀ := huniq m hm
  have e' : m = c⁻¹ • ν := by rw [e, smul_smul, inv_mul_cancel₀ cpos.ne', one_smul]
  have hac : m ≪ ν := by
    rw [e']
    exact Measure.smul_absolutelyContinuous
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 m := h𝓕.mono hac
  have hinv : ∀ (γ : GQ V) (g : GA D V), φ (γ • g) = φ g := fun γ g => hφ γ γ.2 g
  have hint' : IntegrableOn φ 𝓕 m := by
    rw [e', IntegrableOn, Measure.restrict_smul, ENNReal.smul_def]
    exact hint.smul_measure ENNReal.coe_ne_top
  refine ⟨(h𝓕'.integrableOn_iff hF' hinv).1 hint', ?_⟩
  simp only
  rw [← h𝓕'.setIntegral_eq hF' hinv]
  conv_lhs => rw [e]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, Complex.real_smul]

end GlobalTheory.Mem.QuotHaar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreimagePositiveResidueDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem exists_residueDegree_pos_of_mem_range (W Z : Scheme.{0}) (g : W ⟶ Z) [QuasiCompact g]
    [LocallyOfFiniteType g] (z : Z) (hz : z ∈ Set.range g) :
    ∃ w, g w = z ∧ 0 < g.residueDegree w := by
  obtain ⟨w₀, hw₀⟩ := hz
  let F := g.fiber z
  have hne : (Set.univ : Set F).Nonempty := ⟨(g.fiberHomeo z).symm ⟨w₀, hw₀⟩, trivial⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton isClosed_univ hne
  have h₁ : LocallyOfFiniteType (F.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h₂ : LocallyOfFiniteType (g.fiberToSpecResidueField z) := by
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let h : F ⟶ Z := g.fiberι z ≫ g
  have e : h x = z := by
    have := (g.range_fiberι z).le ⟨x, rfl⟩
    simpa [h] using this
  let β : Z.residueField z ⟶ F.residueField x := (Z.residueFieldCongr e.symm).hom ≫ h.residueFieldMap x
  have hβ : Spec.map β = F.fromSpecResidueField x ≫ g.fiberToSpecResidueField z := by
    rw [← cancel_mono (Z.fromSpecResidueField z)]
    simp only [β, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp [h, Scheme.Hom.fiber_fac]
  have hβft : β.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map β) := hβ ▸ inferInstance
    exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) |>.mp this
  have hβf : β.hom.Finite := by
    letI := β.hom.toAlgebra
    haveI : Algebra.FiniteType (Z.residueField z) (F.residueField x) := hβft
    exact finite_of_finite_type_of_isJacobsonRing _ _
  have hhf : (h.residueFieldMap x).hom.Finite := by
    have : h.residueFieldMap x = (Z.residueFieldCongr e.symm).inv ≫ β := by simp [β]
    rw [this, CommRingCat.hom_comp]
    exact hβf.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Z.residueFieldCongr e.symm).inv).2)
  refine ⟨g.fiberι z x, e, ?_⟩
  rw [show h.residueFieldMap x = g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x
    from Scheme.residueFieldMap_comp _ _ _] at hhf
  letI := (g.residueFieldMap (g.fiberι z x)).hom.toAlgebra
  letI := ((g.fiberι z).residueFieldMap x).hom.toAlgebra
  letI := (g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x))
      (F.residueField x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (F.residueField x) := hhf
  let φ := IsScalarTower.toAlgHom (Z.residueField (g (g.fiberι z x)))
    (W.residueField (g.fiberι z x)) (F.residueField x)
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x)) :=
    Module.Finite.of_injective φ.toLinearMap φ.toRingHom.injective
  exact Module.finrank_pos

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeOverSplitNotMemConj
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

namespace GlobalTheory.Mem.Col2.SplitPrime

theorem mem_xor {A : Type*} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (p t m : ℤ) (hp : (p : A) ∈ P) (a a' : A)
    (hm : a * a' = (p : A) * m) (ht : a + a' = t) (hc : IsCoprime p t) :
    (a ∈ P ∧ a' ∉ P) ∨ (a' ∈ P ∧ a ∉ P) := by
  have hnot : ¬ (a ∈ P ∧ a' ∈ P) := by
    rintro ⟨h1, h2⟩
    have h3 : (t : A) ∈ P := ht ▸ P.add_mem h1 h2
    obtain ⟨u, v, huv⟩ := hc
    have h4 : (u : A) * p + (v : A) * t = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) huv
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (h4 ▸ P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h3)))
  have h5 : a * a' ∈ P := hm ▸ P.mul_mem_right _ hp
  rcases hP.mem_or_mem h5 with h | h
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩

theorem exists_over (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥ (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K)))]
    exact bot_le)
  have hmem : (p : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Ideal.mem_bot).1 hmem)

theorem exists_elt {R : Ranks} (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (a : H.K) (t m : ℤ), IsIntegral ℤ a ∧ a * HostK.conjK H a = (p : H.K) * m ∧ a + HostK.conjK H a = t ∧
      IsCoprime (p : ℤ) t := by
  set θ : H.K := ⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ with hθ
  have hsq : θ ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa [hθ] using H.sqrtMinusD_sq)
  have hcj : HostK.conjK H θ = -θ := Subtype.ext (by simpa [hθ, HostK.coe_conjK] using H.conj_sqrtMinusD)
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 8 * m := by
      have := H.hyp.2.2.2.1
      exact ⟨(H.d + 1) / 8, by omega⟩
    have hm' : (H.d : H.K) + 1 = 8 * m := by exact_mod_cast hm
    refine ⟨(1 + θ) / 2, 1, m, HostK.isIntegral_half H, ?_, ?_, isCoprime_one_right⟩
    · rw [map_div₀, map_add (f := _), map_one, hcj, map_ofNat]
      push_cast
      linear_combination (-1 / 4 : H.K) * hsq + (1 / 4 : H.K) * hm'
    · rw [map_div₀, map_add (f := _), map_one, hcj, map_ofNat]
      push_cast
      ring
  · have hj : jacobiSym (-(H.d : ℤ)) p = 1 := hs.resolve_left h2
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
    have hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h
      rw [(legendreSym.eq_zero_iff p _).2 h] at hj
      exact zero_ne_one hj
    obtain ⟨s, hs'⟩ := (legendreSym.eq_one_iff p hne).1 hj
    obtain ⟨r, rfl⟩ := ZMod.intCast_surjective s
    have hr : ¬ (p : ℤ) ∣ r := by
      intro h
      rw [hs', (ZMod.intCast_zmod_eq_zero_iff_dvd r p).2 h] at hne
      exact hne (mul_zero _)
    have hdiv : (p : ℤ) ∣ r * r + H.d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast at hs' ⊢
      linear_combination -hs'
    obtain ⟨m, hm⟩ := hdiv
    have hm' : (r : H.K) * r + H.d = (p : H.K) * m := by exact_mod_cast congrArg (Int.cast : ℤ → H.K) hm
    have hθi : IsIntegral ℤ θ := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hsq]
      exact (isIntegral_natCast H.d).neg
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    refine ⟨r + θ, 2 * r, m, (isIntegral_intCast r).add hθi, ?_, ?_, ?_⟩
    · rw [map_add (f := _), map_intCast, hcj]
      linear_combination hm' - hsq
    · rw [map_add (f := _), map_intCast, hcj]
      push_cast
      ring
    · refine (hpi.coprime_iff_not_dvd).2 fun h => ?_
      rcases hpi.dvd_or_dvd h with h | h
      · have h' : p ∣ 2 := by exact_mod_cast h
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
      · exact hr h

theorem exists_prime_not_conj (R : Ranks) (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧
      (β : H.K) = HostK.conjK H α := by
  obtain ⟨a, t, m, hai, hm, ht, hc⟩ := exists_elt H p hp hs
  have hai' : IsIntegral ℤ (HostK.conjK H a) := by
    have : HostK.conjK H a = t - a := by linear_combination ht
    rw [this]
    exact (isIntegral_intCast t).sub hai
  obtain ⟨𝔭, h𝔭⟩ := exists_over H.K p hp
  let x : 𝓞 H.K := ⟨a, hai⟩
  let y : 𝓞 H.K := ⟨HostK.conjK H a, hai'⟩
  have hx : (x : H.K) = a := rfl
  have hy : (y : H.K) = HostK.conjK H a := rfl
  have h1 : x * y = ((p : ℤ) : 𝓞 H.K) * m := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using hm
  have h2 : x + y = t := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using ht
  rcases mem_xor 𝔭.asIdeal 𝔭.isPrime p t m (by exact_mod_cast h𝔭) x y h1 h2 hc with h | h
  · exact ⟨𝔭, x, y, h𝔭, h.1, h.2, rfl⟩
  · exact ⟨𝔭, y, x, h𝔭, h.1, h.2, by rw [hx, hy, HostK.conjK_conjK]⟩

end GlobalTheory.Mem.Col2.SplitPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyIrreducibleLocalEmbeddingStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_irreducible_local_embedding : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∀ σ : G K Ω, ∃ τ ∈ Dec (F := K) A, ∀ x : L, τ (algebraMap L Ω x) = σ (algebraMap L Ω x)) → ∀ ι : Ω →ₐ[K] Kbar v, IsLocEmb A v ι → ∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K))) := by
  first | exact @GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible | exact GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible | (intros; apply GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible <;> assumption)
end

