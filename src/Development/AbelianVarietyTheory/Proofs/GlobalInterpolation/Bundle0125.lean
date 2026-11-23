module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUni
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem natCast_residueField_completion_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

theorem unipotent_type_character_finite_order : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (a t skip fc : ℕ) (zl : Bool) (_ : GLev S G a t 0 skip fc zl) (K : Type) [Field K] (s : K →+* ℂ), (∀ i, (gp i).Prime) → (∀ i, ∃ ζ : K, IsPrimitiveRoot ζ (gp i)) → ∃ N : ℕ, 0 < N ∧ ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ n J T f bad S gp G a t skip fc zl L K _ s hp hζ
  refine ⟨gp 0 * gp 1, Nat.mul_pos (hp 0).pos (hp 1).pos, fun x => ?_⟩
  rw [L.chi_eq x]
  let P : ℂ → Prop := fun z => z ^ (gp 0 * gp 1) = 1 ∧ ∃ r : K, s r = z
  have h1 : P 1 := ⟨one_pow _, 1, map_one s⟩
  have hm : ∀ y z, P y → P z → P (y * z) := by
    rintro y z ⟨hy, r, rfl⟩ ⟨hz, q, rfl⟩
    exact ⟨by rw [mul_pow, hy, hz, one_mul], r * q, map_mul s r q⟩
  change P _
  refine Finset.prod_induction _ P hm h1 fun i _ => ?_
  refine finprod_induction P h1 hm fun v => ?_
  refine finprod_induction P h1 hm fun h => ?_
  obtain ⟨⟨r, hr⟩, hpow⟩ := _root_.GlobalTheory.lamJ_zero_blocks_mem_range_and_pow_eq_one (kv F v) K s (gp i) (hp i)
    (natCast_residueField_completion_eq_zero F v (gp i) h) (hζ i) n (G.psi0 i v h) (G.chiB i v h) a t skip
    (redM F v (G.mat i v h (L.fr i v h) (bc (prV (E := E) v) x.1)))
  refine ⟨?_, r⁻¹, by rw [map_inv₀, hr]⟩
  have hd : gp i ∣ gp 0 * gp 1 := by
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  obtain ⟨c, hc⟩ := hd
  rw [inv_pow, hc, pow_mul, hpow, one_pow, inv_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryFourfoldLatticePreservesRationalVectors
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatDesc

theorem unitary_maps_rational : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  intro D cc δ B hcc u hidx v
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) with hM
  set n := Formalism.L2.Th1.H.relIdx S M with hn

  have h1 : ∀ x ∈ M, n • x ∈ S := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨x, hx⟩ : M)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set y := B.γ₀.g.symm v with hy
  obtain ⟨t, ht, hint⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.exists_nat_mul D.host.E (Finset.univ.image y)
  set N := Ideal.absNorm cc with hNdef
  have hN : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hw₀ : δ * (N : ℂ) ∈ lamOf D cc δ := by
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K), hNc, ?_⟩
    simp
  have hm : (δ * (N : ℂ)) • emb4 D (t • y) ∈ Formalism.L2.Th1.H.pow4 B.lamM :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀ fun a => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different (by
      have := hint _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
      simpa using this)
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hg : B.gC (emb4 D (t • y)) = (t : ℂ) • V := by
    rw [show B.gC (emb4 D (t • y)) = _ from B.gC_spec (t • y), map_nsmul, hy, LinearEquiv.apply_symm_apply]
    funext w
    simp [hV]
  have hmem : (δ * (N : ℂ) * (t : ℂ)) • u V ∈ M := by
    refine ⟨B.gC ((δ * (N : ℂ)) • emb4 D (t • y)), ⟨_, hm, rfl⟩, ?_⟩
    show u (B.gC _) = _
    rw [map_smul, hg, smul_smul, map_smul]
  have hS' := h1 _ hmem
  rw [hS, Formalism.L2.Th1.H.mem_stdLat] at hS'
  have hc : ∀ w, ∃ c ∈ cc, ((n • ((δ * (N : ℂ) * (t : ℂ)) • u V)) w) = δ * D.host.φ₀ (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) :=
    fun w => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 (hS' w))
  choose c _ hc using hc
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨fun w => ((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)), ?_⟩
  funext w
  have h := hc w
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at h
  have e : D.host.φ₀ (((((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)) : D.host.K)) : D.host.E)
      = D.host.φ₀ (((c w : 𝓞 D.host.K) : D.host.K) : D.host.E) / ((n : ℂ) * (N : ℂ) * (t : ℂ)) := by
    push_cast
    rw [map_div₀, map_mul, map_mul, map_natCast, map_natCast, map_natCast]
  rw [e, eq_div_iff (mul_ne_zero (mul_ne_zero hnC hNC) htC)]
  apply mul_left_cancel₀ hδ
  rw [← h]
  ring

end GlobalTheory.LatDesc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalUnitaryDomains

theorem isDiscreteWithDomains_of_discrete {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [hc : Countable Γ] [hd : DiscreteTopology Γ] : IsDiscreteWithDomains Γ := by
  refine ⟨hc, hd, fun μ _ => ?_⟩
  obtain ⟨𝓕, hF, h⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  exact ⟨𝓕, hF, IsFundamentalDomain.mk' hF.nullMeasurableSet h⟩

theorem isDiscreteWithDomains_ratPts' (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    IsDiscreteWithDomains (ratPts (AF F) σ J) := by
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have : Countable (ratPts (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have : DiscreteTopology (ratPts (AF F) σ J) := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  exact isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsDiscreteWithDomains (ratPts (AF F) σ J) :=
  fun F E _ _ _ _ _ σ _ M J _ => isDiscreteWithDomains_ratPts' F E σ M J

end GlobalTheory.RationalUnitaryDomains
end

