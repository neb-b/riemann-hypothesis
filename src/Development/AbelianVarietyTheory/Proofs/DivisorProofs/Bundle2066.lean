module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorFiniteCoverNearPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem locGen_near_fibre_of_finite : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  intro H X X' p hp L hL x
  obtain ⟨W₀, hW₀, hxW₀, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineOpen.preimage hW₀ p
  have hF : (p.base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton p x
  have hFW : p.base ⁻¹' {x} ⊆ (p ⁻¹ᵁ W₀ : Set X') := by
    intro y hy
    show p.base y ∈ W₀
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    rw [hy]; exact hxW₀
  obtain ⟨V, a, hFV, ha⟩ := H X' L hL (p ⁻¹ᵁ W₀) hA _ hF hFW
  have hcl : IsClosed (p.base '' (V : Set X')ᶜ) := p.isClosedMap _ V.isOpen.isClosed_compl
  let W : X.Opens := ⟨(p.base '' (V : Set X')ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hWV : p ⁻¹ᵁ W ≤ V := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hxW : x ∈ W := by
    rintro ⟨y, hy, hyx⟩
    exact hy (hFV (show p.base y = x from hyx))
  refine ⟨W, fun k ↦ res (inf_le_inf_right _ hWV) (a k), hxW, ?_⟩
  intro y k k' hy hk hk'
  rw [gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk⟩, gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk'⟩]
  exact ha y k k' (hWV hy) hk hk'

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FibreBasisSpread

theorem exists_away_linearCombination_bijective : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (J : Type) [Fintype J] (v : J → M) (p : Ideal R) [p.IsPrime],
    Function.Bijective (Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i)) →
    ∃ g : R, g ∉ p ∧ (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R v c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R v c = 0 → ∃ n : ℕ, g ^ n • c = 0) := by
  intro R _ M _ _ _ _ J _ v p _ hbij
  classical
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let Rp := Localization.AtPrime p
  have hloc : Function.Bijective (IsLocalizedModule.map p.primeCompl
      (Finsupp.mapRange.linearMap (Algebra.linearMap R Rp)) (TensorProduct.mk R Rp M 1)
      (Finsupp.linearCombination R v)) := by
    rw [IsLocalizedModule.map_linearCombination, LinearMap.coe_restrictScalars]
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [← (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).comp_bijective]
    have heq : (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).toLinearMap ∘ₗ
        Finsupp.linearCombination p.ResidueField
          (TensorProduct.mk Rp p.ResidueField (Rp ⊗[R] M) 1 ∘ (TensorProduct.mk R Rp M 1 ∘ v)) =
        Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i) := by
      ext i
      simp
    convert hbij using 1
    rw [← heq, LinearMap.coe_comp]
    rfl
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective
    (Finsupp.linearCombination R v) p _ _ hloc
  refine ⟨g, hg, fun x => ?_, fun c hc => ?_⟩
  · obtain ⟨y, hy⟩ := h.2 (LocalizedModule.mk x 1)
    induction y using LocalizedModule.induction_on with
    | h c s =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨⟨u, hu⟩, hu'⟩ := hy
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, hb⟩ := s.2
      refine ⟨a + b, g ^ a • c, ?_⟩
      have hb' : (s : R) = g ^ b := hb.symm
      simp only [Submonoid.smul_def, one_smul] at hu'
      rw [map_smul, hu', hb', smul_smul, pow_add]
  · have h0 : LocalizedModule.map (Submonoid.powers g) (Finsupp.linearCombination R v)
        (LocalizedModule.mk c 1) = LocalizedModule.map (Submonoid.powers g)
        (Finsupp.linearCombination R v) 0 := by
      rw [LocalizedModule.map_mk, hc, map_zero, LocalizedModule.zero_mk]
    have h1 := h.1 h0
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
    obtain ⟨⟨u, hu⟩, hu'⟩ := h1
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, by simpa [Submonoid.smul_def] using hu'⟩

end GlobalTheory.FibreBasisSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomCompleteDVRPrincipalMaximalIdeal
section
open IsLocalRing

namespace GlobalTheory.PrincDvr

def powInf {B : Type} [CommRing B] (ϖ : B) : Ideal B := ⨅ n : ℕ, Ideal.span {ϖ ^ n}

variable {B : Type} [CommRing B] [IsLocalRing B] {ϖ : B}

theorem pow_not_mem_span_succ (hm : maximalIdeal B = Ideal.span {ϖ}) (hϖ : ϖ ∈ nonZeroDivisors B) (n : ℕ) :
    ϖ ^ n ∉ Ideal.span {ϖ ^ (n + 1)} := by
  intro h
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  have hn : ϖ ^ n ∈ nonZeroDivisors B := pow_mem hϖ n
  have e : (b * ϖ - 1) * ϖ ^ n = 0 := by linear_combination hb
  have e1 : b * ϖ - 1 = 0 := (mem_nonZeroDivisors_iff.1 hn).2 _ e
  have hmem : ϖ ∈ maximalIdeal B := by rw [hm]; exact Ideal.mem_span_singleton_self ϖ
  exact (mem_maximalIdeal _).1 hmem (isUnit_iff_exists_inv.2 ⟨b, by rw [mul_comm]; exact sub_eq_zero.1 e1⟩)

theorem exists_unit_mul_pow (hm : maximalIdeal B = Ideal.span {ϖ}) (x : B) (hx : x ∉ powInf ϖ) :
    ∃ (n : ℕ) (u : Bˣ), x = u * ϖ ^ n := by
  classical
  have hex : ∃ n, ¬ ϖ ^ n ∣ x := by
    by_contra h
    push_neg at h
    exact hx (Ideal.mem_iInf.2 fun n => Ideal.mem_span_singleton.2 (h n))
  obtain ⟨N, hN, hmin⟩ : ∃ N, ¬ ϖ ^ N ∣ x ∧ ∀ m < N, ϖ ^ m ∣ x :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.1 (Nat.find_min hex hm)⟩
  clear hex
  have hN0 : N ≠ 0 := by
    intro h0; apply hN; rw [h0, pow_zero]; exact one_dvd x
  obtain ⟨u, hu⟩ : ϖ ^ (N - 1) ∣ x := hmin _ (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos)
  have hu' : IsUnit u := by
    by_contra hu'
    have hmem : u ∈ Ideal.span {ϖ} := by rw [← hm]; exact (mem_maximalIdeal u).2 hu'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hmem
    apply hN
    refine ⟨c, ?_⟩
    rw [hu, hc, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)]
  exact ⟨N - 1, hu'.unit, by rw [hu, IsUnit.unit_spec, mul_comm]⟩

theorem isPrime_powInf (hm : maximalIdeal B = Ideal.span {ϖ}) (hϖ : ϖ ∈ nonZeroDivisors B) :
    (powInf ϖ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    exact pow_not_mem_span_succ hm hϖ 0 (by simpa using Ideal.mem_iInf.1 h 1)
  · intro a b hab
    by_contra h
    push_neg at h
    obtain ⟨m, u, rfl⟩ := exists_unit_mul_pow hm a h.1
    obtain ⟨k, v, rfl⟩ := exists_unit_mul_pow hm b h.2
    have hmem := Ideal.mem_iInf.1 hab (m + k + 1)
    apply pow_not_mem_span_succ hm hϖ (m + k)
    have e1 : (u : B) * ϖ ^ m * (v * ϖ ^ k) = ((u * v : Bˣ) : B) * ϖ ^ (m + k) := by push_cast; ring
    have e : ϖ ^ (m + k) = (((u * v)⁻¹ : Bˣ) : B) * ((u : B) * ϖ ^ m * (v * ϖ ^ k)) := by
      rw [e1, Units.inv_mul_cancel_left]
    rw [e]
    exact Ideal.mul_mem_left _ _ hmem

theorem exists_cDvr_localHom : ∀ (B : Type) [CommRing B] [IsLocalRing B] (ϖ : B), maximalIdeal B = Ideal.span {ϖ} →
    ϖ ∈ nonZeroDivisors B → CharZero (ResidueField B) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W)
    (_ : IsLocalRing W) (h : B →+* W), GlobalTheory.LN.CDvr W ∧ IsLocalHom h ∧ h ϖ ≠ 0 := by
  intro B _ _ ϖ hm hϖ h0
  haveI := isPrime_powInf hm hϖ
  have hp0 : Ideal.Quotient.mk (powInf ϖ) ϖ ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    exact pow_not_mem_span_succ hm hϖ 1 (by simpa using Ideal.mem_iInf.1 h 2)
  have hnu : ∀ a : B, ¬ IsUnit a → ∃ c, Ideal.Quotient.mk (powInf ϖ) a =
      Ideal.Quotient.mk (powInf ϖ) ϖ * Ideal.Quotient.mk (powInf ϖ) c := by
    intro a ha
    have hmem : a ∈ Ideal.span {ϖ} := by rw [← hm]; exact (mem_maximalIdeal a).2 ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨c, by rw [← hc, map_mul, mul_comm]⟩
  have hpu : ¬ IsUnit (Ideal.Quotient.mk (powInf ϖ) ϖ) := by
    rintro ⟨w, hw⟩
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (w⁻¹ : (B ⧸ powInf ϖ)ˣ).val
    have e : Ideal.Quotient.mk (powInf ϖ) (ϖ * c) = Ideal.Quotient.mk (powInf ϖ) 1 := by
      rw [map_mul, hc, ← hw, Units.mul_inv, map_one]
    have h1 := Ideal.mem_iInf.1 (Ideal.Quotient.eq.1 e) 1
    rw [pow_one] at h1
    have h2 : (1 : B) ∈ Ideal.span {ϖ} := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self ϖ)) h1
      simpa using this
    exact pow_not_mem_span_succ hm hϖ 0 (by simpa using h2)
  have hirr : Irreducible (Ideal.Quotient.mk (powInf ϖ) ϖ) := by
    refine irreducible_iff.2 ⟨hpu, fun a b hab => ?_⟩
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    by_cases ha : IsUnit a'
    · exact Or.inl (ha.map _)
    · obtain ⟨c, hc⟩ := hnu a' ha
      right
      rw [hc, mul_assoc] at hab
      have e := mul_left_cancel₀ hp0 ((mul_one _).trans hab)
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact e.symm⟩
  have hfac : ∀ {x : B ⧸ powInf ϖ}, x ≠ 0 → ∃ n, Associated (Ideal.Quotient.mk (powInf ϖ) ϖ ^ n) x := by
    intro x hx
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : x' ∉ powInf ϖ := fun h => hx (Ideal.Quotient.eq_zero_iff_mem.2 h)
    obtain ⟨n, u, rfl⟩ := exists_unit_mul_pow hm x' hx'
    refine ⟨n, Units.map (Ideal.Quotient.mk (powInf ϖ)).toMonoidHom u, ?_⟩
    simp only [map_mul, map_pow, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  haveI : IsDiscreteValuationRing (B ⧸ powInf ϖ) :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, hfac⟩
  have hle : powInf ϖ ≤ RingHom.ker (residue B) := by
    intro a ha
    rw [RingHom.mem_ker, residue_eq_zero_iff, hm]
    simpa using Ideal.mem_iInf.1 ha 1
  have hc0 : CharZero (B ⧸ powInf ϖ) := RingHom.charZero (Ideal.Quotient.lift (powInf ϖ) (residue B) hle)
  have hloc : IsLocalHom (Ideal.Quotient.mk (powInf ϖ)) := ⟨fun a ha => by
    by_contra h
    obtain ⟨c, hc⟩ := hnu a h
    rw [hc] at ha
    exact hpu (isUnit_of_mul_isUnit_left ha)⟩
  obtain ⟨W, _, _, _, g, hW, hinj, hg⟩ := GlobalTheory.LocalCompletion.exists_cDvr_embedding (B ⧸ powInf ϖ) inferInstance
    inferInstance (IsDiscreteValuationRing.ringKrullDim_eq_one _) hc0
  refine ⟨W, inferInstance, inferInstance, inferInstance, g.comp (Ideal.Quotient.mk (powInf ϖ)), hW, ?_, ?_⟩
  · haveI := hloc; haveI := hg; infer_instance
  · intro h
    exact hp0 (hinj (by rw [map_zero]; exact h))

end GlobalTheory.PrincDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerGenericEigenFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSDiv.GenKSProof

theorem embK_conj_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c ((starRingEnd ℂ).comp τ) (H.bar x) = embK c τ x := by
  apply Subtype.ext
  show ((starRingEnd ℂ).comp τ) ((H.bar x : 𝓞 E) : E) = τ (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem embK_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c ((starRingEnd ℂ).comp τ) x := by
  apply Subtype.ext
  show τ ((H.bar x : 𝓞 E) : E) = ((starRingEnd ℂ).comp τ) (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem card_pairIx {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) : Fintype.card (GlobalTheory.LogKSDiv.PairIx H Dw) = Dw.dim := by
  have h := FlagTan.isHalf_psiSet H
  have hc : Fintype.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} = Module.finrank ℚ E / 2 := by
    rw [← h.card, FlagTan.psiSet, Fintype.card_subtype]
  have hm : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      Dw.mult τ.1 * Dw.mult ((starRingEnd ℂ).comp τ.1) = Dw.p * Dw.q := fun τ => by
    rcases FlagTan.mult_conj (Dw := Dw) τ.1 with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b]
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b, mul_comm]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, hm, Finset.sum_const, Finset.card_univ, hc,
    smul_eq_mul, Datum.dim, mul_assoc]

theorem symPair_mem_balanced {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (R : Type) [CommRing R] (κ : c.F → R) (n : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : GlobalTheory.LogKSDiv.PairIx H Dw) :
    GlobalTheory.LogKSDiv.symPair (R := R) e P ∈
      LogKS.balanced H.bar (fun a => Matrix.diagonal fun j => κ (embK c (e.symm j).1 a)) := by
  refine (LogKS.mem_balanced_diagonal H.bar (fun j a => κ (embK c (e.symm j).1 a)) _).2 ⟨?_, fun a i k => ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    rw [add_comm]
    congr 1 <;> congr 1 <;> exact propext and_comm
  · simp only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    by_cases h1 : i = e ⟨P.1.1, P.2.1⟩ ∧ k = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [Equiv.symm_apply_apply, embK_conj_bar', sub_self, zero_mul]
    by_cases h2 : i = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ k = e ⟨P.1.1, P.2.1⟩
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [Equiv.symm_apply_apply, embK_bar', sub_self, zero_mul]
    · rw [if_neg h1, if_neg h2, add_zero, mul_zero]

theorem exists_ext (k R K : Type) [CommRing k] [CommRing R] [Field K] (ρ : R →+* K) (α : k →+* K) (κ : k → R)
    (hfr : letI := ρ.toAlgebra; IsFractionRing R K) (hκ : ∀ a, ρ (κ a) = α a) (d : Derivation ℤ R R)
    (hd : ∀ a, d (κ a) = 0) :
    ∃ D : (letI := α.toAlgebra; Derivation k K K), ∀ r, D (ρ r) = ρ (d r) := by
  letI := ρ.toAlgebra
  obtain ⟨δ, hδ, hδρ⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (A := R) (B := K) (nonZeroDivisors R) (fun r => ρ (d r))
    (fun x y => by rw [map_add (f := _), map_add (f := _)]) (fun x y => by
      rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul]; rfl)
  have hα : ∀ a, δ (α a) = 0 := fun a => by
    rw [← hκ a]
    exact (hδρ (κ a)).trans (by rw [hd, map_zero])
  letI := α.toAlgebra
  have hs : ∀ (a : k) (x : K), δ (a • x) = a • δ x := fun a x => by
    show δ (α a * x) = α a * δ x
    rw [hδ.mul, hα, mul_zero, add_zero]
  let D0 : K →ₗ[k] K := { toFun := δ, map_add' := hδ.add, map_smul' := hs }
  exact ⟨{ toLinearMap := D0, map_one_eq_zero' := hδ.der_one, leibniz' := (fun x y => hδ.mul x y) },
    fun r => hδρ r⟩

theorem exists_genKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z f₀.v D := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ φ₀ f₀ hφ₀
  obtain ⟨U, hU, ρ, n, e, v, hch, htan, huq, hf, heig⟩ := _root_.GlobalTheory.LogKSDiv.spread_genFrame E H Dw l Xo c TF Z φ₀ f₀ hφ₀
  obtain ⟨hfr, hconst⟩ := GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart E H Dw l Xo c TF Z U hU ρ hch
  obtain ⟨e', he'⟩ := TF.logKS U n v _ htan huq heig
  let ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw := (Fintype.equivFinOfCardEq (card_pairIx H Dw)).symm
  let Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U :=
    fun j => e'.symm ⟨GlobalTheory.LogKSDiv.symPair e (ε j), symPair_mem_balanced H Dw l c _ _ n e (ε j)⟩
  have hD := fun j => exists_ext c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField ρ (GlobalTheory.Cartier.constFn (s₀ TF.Y Z))
    (constFn TF.Y.s U.1) hfr hconst (Dl j).1 (Dl j).2.1
  choose D hD using hD
  refine ⟨D, U, hU, ρ, n, e, v, ε, Dl, hch, htan, huq, fun τ i => hf τ i, fun j => ?_, hD⟩
  refine (he' (Dl j) _).2 ?_
  simp only [Dl, LinearEquiv.apply_symm_apply]

end GlobalTheory.LogKSDiv.GenKSProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoFiniteTypeAgreementLocusInjectiveFamil
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualGraph

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem evc_ev_comp {T P Y : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (f : P ⟶ T)
    (h : (ev N (fst A P) (snd A P ≫ f)).IsLB) (a : Y ⟶ A) (p : Y ⟶ P) : evc h a p = evc hN a (p ≫ f) := by
  rw [evc_ev hN, lift_fst, lift_snd_assoc]

theorem fam_ev {T P : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (f : P ⟶ T) :
    Fam A (ev N (fst A P) (snd A P ≫ f)) := by
  have h : (ev N (fst A P) (snd A P ≫ f)).IsLB := pull_isLB hN.isLB _
  refine ⟨h, (isAdditive_iff h).2 fun Y a a' p ↦ ?_⟩
  rw [evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h]
  exact (isAdditive_iff hN.isLB).1 hN.add Y a a' (p ≫ f)

theorem same_prod_iff {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (p : Y ⟶ T ⊗ U) :
    Same A (ev N (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ fst T U)) (ev M (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ snd T U)) p p ↔
      Same A N M (p ≫ fst T U) (p ≫ snd T U) := by
  have h₁ : (ev N (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ fst T U)).IsLB := pull_isLB hN _
  have h₂ : (ev M (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ snd T U)).IsLB := pull_isLB hM _
  rw [same_iff h₁ h₂, same_iff hN hM, evc_ev_comp hN _ h₁, evc_ev_comp hM _ h₂, Category.assoc, Category.assoc]

theorem exists_mono_same : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (T U : Over S) [IsLocallyNoetherian T.left] [LocallyOfFiniteType U.hom] (N : LB (A ⊗ T).left)
      (M : LB (A ⊗ U).left), Fam A N → Fam A M → Inj A M → ∃ (G : Over S) (π : G ⟶ T), Mono π.left ∧
        LocallyOfFiniteType π.left ∧ ∀ (Y : Over S) (y : Y ⟶ T),
          (∃ u : Y ⟶ U, Same A N M y u) ↔ ∃ z : Y.left ⟶ G.left, z ≫ π.left = y.left := by
  intro S A _ hA T U _ _ N M hN hM hI
  have hf : LocallyOfFiniteType (fst T U).left := by
    show LocallyOfFiniteType (pullback.fst T.hom U.hom)
    infer_instance
  haveI : IsLocallyNoetherian (T ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (fst T U).left
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.DualLocus.exists_closed_same S A (T ⊗ U) hA _ _ (fam_ev hN (fst T U))
    (fam_ev hM (snd T U))
  have key : ∀ (Y : Over S) (z : Y ⟶ G), Same A N M (z ≫ i ≫ fst T U) (z ≫ i ≫ snd T U) := fun Y z ↦ by
    rw [← Category.assoc, ← Category.assoc, ← same_prod_iff hN.isLB hM.isLB]
    exact (hG Y (z ≫ i)).2 ⟨z, rfl⟩
  have hw : i.left ≫ (fst T U).left ≫ T.hom = G.hom := by
    rw [Over.w (fst T U), Over.w i]
  refine ⟨G, i ≫ fst T U, ⟨fun {W} a b hab ↦ ?_⟩, ?_, fun Y y ↦ ⟨?_, ?_⟩⟩
  · let Y : Over S := Over.mk (a ≫ G.hom)
    let a' : Y ⟶ G := Over.homMk a rfl
    let b' : Y ⟶ G := Over.homMk b (by
      show b ≫ G.hom = a ≫ G.hom
      simp only [Over.comp_left] at hab
      rw [← hw, reassoc_of% hab])
    have e₁ : a' ≫ i ≫ fst T U = b' ≫ i ≫ fst T U := Over.OverMorphism.ext (by
      simpa only [Over.comp_left, a', b', Over.homMk_left] using hab)
    have e₂ : a' ≫ i ≫ snd T U = b' ≫ i ≫ snd T U := by
      refine hI Y _ _ ((same_iff hM.isLB hM.isLB _ _).2 ?_)
      rw [← (same_iff hN.isLB hM.isLB _ _).1 (key Y a'), ← (same_iff hN.isLB hM.isLB _ _).1 (key Y b'), e₁]
    have e : a' ≫ i = b' ≫ i := by
      rw [← Category.assoc, ← Category.assoc] at e₁ e₂
      exact CartesianMonoidalCategory.hom_ext _ _ e₁ e₂
    have e' := congrArg (fun q : Y ⟶ T ⊗ U ↦ q.left) e
    simp only [Over.comp_left, a', b', Over.homMk_left] at e'
    exact (cancel_mono i.left).1 e'
  · rw [Over.comp_left]
    infer_instance
  · rintro ⟨u, hu⟩
    have hs := (same_prod_iff hN.isLB hM.isLB (lift y u)).2 (by rwa [lift_fst, lift_snd])
    obtain ⟨z, hz⟩ := (hG Y (lift y u)).1 hs
    refine ⟨z.left, ?_⟩
    rw [← Over.comp_left, ← Category.assoc, hz, lift_fst]
  · rintro ⟨z, hz⟩
    let z' : Y ⟶ G := Over.homMk z (by
      show z ≫ G.hom = Y.hom
      rw [← hw, ← Over.w y, ← hz, Over.comp_left]
      simp only [Category.assoc])
    have ey : z' ≫ i ≫ fst T U = y := Over.OverMorphism.ext (by
      simpa only [Over.comp_left, z', Over.homMk_left] using hz)
    refine ⟨z' ≫ i ≫ snd T U, ?_⟩
    have := key Y z'
    rwa [ey] at this

end GlobalTheory.DualGraph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMvPolynomialLiftConductorCoeffs
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mvPolynomial_lift_of_mem_conductor :
    ∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G := by
  intro R R' ν _ _ _ c hc G hG
  have key : ∀ z ∈ c.map (algebraMap R R'), ∃ y ∈ c, algebraMap R R' y = z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => ∃ y ∈ c, algebraMap R R' y = z)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · exact ⟨0, c.zero_mem, map_zero _⟩
    · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, c.add_mem ha hb, map_add _ _ _⟩
    · rintro r _ _ ⟨a, ha, rfl⟩
      obtain ⟨y, hy, h⟩ := hc a ha r
      exact ⟨y, hy, by rw [h, smul_eq_mul, mul_comm]⟩
  rw [MvPolynomial.mem_map_C_iff] at hG
  choose y hy hyG using fun m => key _ (hG m)
  refine ⟨∑ m ∈ G.support, MvPolynomial.monomial m (y m), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [MvPolynomial.map_monomial, Ideal.Quotient.eq_zero_iff_mem.mpr (hy m), map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      conv_rhs => rw [G.as_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.map_monomial, hyG]

end GlobalTheory
end

