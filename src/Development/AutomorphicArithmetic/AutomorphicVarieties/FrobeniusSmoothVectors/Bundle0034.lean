module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FieldEx
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem fix_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (Ω ≃ₐ[ℚ] Ω))
    (h : IsOpen (H : Set (Ω ≃ₐ[ℚ] Ω))) : (IntermediateField.fixedField H).fixingSubgroup = H :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen h⟩

private theorem commutator_le_ker_of_hom_int_units {Γ : Type*} [Group Γ] (η : Γ →* ℤˣ) : commutator Γ ≤ η.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

private theorem conj_ne_self_of_sq_eq_neg_natCast (z : ℂ) (D : ℕ) (hD : 0 < D) (h : z ^ 2 = -(D : ℂ)) :
    starRingEnd ℂ z ≠ z := by
  intro hc
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hc
  have h1 := congrArg Complex.re h
  simp [pow_two, him] at h1
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [mul_self_nonneg z.re]

theorem UpperTheory.V.Fr.field_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (U : Subgroup (G ℚ Ω)), UFacts l η Ψ M m U → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : Algebra L Ω), IsAbelianGalois ℚ L ∧ upl Ω L = U ∧ galOf ℚ L Ω = U ⊓ η.ker := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m U hU
  obtain ⟨D, δ, hD, -, hδ2, hδ⟩ := hG.quad
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ2
    omega
  have hker : ∀ s : G ℚ Ω, η s = 1 ↔ s δ = δ := by
    intro s
    constructor
    · intro h
      rw [hδ s, h]
      simp
    · intro h
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact h1
      · exfalso
        rw [hδ s, h1] at h
        simp at h
        have h2 : (2 : Ω) * δ = 0 := by linear_combination -h
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact two_ne_zero h3
        · exact hδ0 h3
  have hint : IsIntegral ℚ δ := Algebra.IsIntegral.isIntegral δ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {δ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hkerO : IsOpen (η.ker : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {δ}))
    intro s hs
    rw [MonoidHom.mem_ker, hker]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs δ
      (IntermediateField.mem_adjoin_simple_self ℚ δ)
  have hHo : IsOpen ((U ⊓ η.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    rw [Subgroup.coe_inf]
    exact hU.isOpen.inter hkerO
  have hcomm : commutator (G ℚ Ω) ≤ U ⊓ η.ker := le_inf hU.ab (commutator_le_ker_of_hom_int_units η)
  set L := IntermediateField.fixedField (U ⊓ η.ker) with hLdef
  have hfix : L.fixingSubgroup = U ⊓ η.ker := fix_fix _ hHo
  haveI : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hHo)
  haveI : NumberField L := ⟨⟩
  have hN : (L.fixingSubgroup).Normal := by
    rw [hfix]
    refine ⟨fun n hn g => ?_⟩
    have hc : g * n * g⁻¹ * n⁻¹ ∈ U ⊓ η.ker :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have he : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by
      group
    rw [he]
    exact Subgroup.mul_mem _ hc hn
  have hAb : @IsAbelianGalois ℚ L _ _ (IntermediateField.algebra' L) := by
    letI : Algebra ℚ L := IntermediateField.algebra' L
    haveI hg : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp hN
    haveI : IsMulCommutative Gal(L/ℚ) := ⟨⟨fun a b => by
      obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω a
      obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω b
      have hc : a' * b' * a'⁻¹ * b'⁻¹ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker := by
        rw [IntermediateField.restrictNormalHom_ker, hfix]
        exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b'))
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hc
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)⟩⟩
    exact ⟨⟩
  haveI : IsAbelianGalois ℚ L := by
    convert hAb <;> exact Subsingleton.elim _ _
  have hδL : δ ∈ L := by
    rw [IntermediateField.mem_fixedField_iff]
    intro s hs
    exact (hker s).mp (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hs).2)
  have hδL2 : (⟨δ, hδL⟩ : L) ^ 2 = -(D : L) := by
    apply Subtype.ext
    simpa using hδ2
  haveI : NumberField.IsTotallyComplex L := ⟨fun v => by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_iff]
    intro hv
    apply conj_ne_self_of_sq_eq_neg_natCast (v.embedding ⟨δ, hδL⟩) D hD
    · rw [← map_pow, hδL2]
      simp
    · have := RingHom.congr_fun hv ⟨δ, hδL⟩
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at this⟩
  obtain ⟨j, hj⟩ := hG.cc
  have hσU : σ ∈ U := hU.real σ hG.cc
  have hησ : η σ = -1 := by
    rcases Int.units_eq_one_or (η σ) with h | h
    · exfalso
      have hσδ : σ δ = δ := (hker σ).mp h
      apply conj_ne_self_of_sq_eq_neg_natCast (j δ) D hD
      · rw [← map_pow, hδ2]
        simp
      · rw [← hj, hσδ]
    · exact h
  have hcc : ∀ z : L, σ (z : Ω) = ((NumberField.IsCMField.complexConj L z : L) : Ω) := by
    intro z
    apply j.injective
    rw [hj]
    exact (NumberField.IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) z).symm
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · ext s
    change (∀ x ∈ NumberField.maximalRealSubfield L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U
    constructor
    · intro h
      rw [← fix_fix U hU.isOpen, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hyL : y ∈ L := (IntermediateField.mem_fixedField_iff _ _).mpr fun f hf =>
        (IntermediateField.mem_fixedField_iff _ _).mp hy f (Subgroup.mem_inf.mp hf).1
      have hre : (⟨y, hyL⟩ : L) ∈ NumberField.maximalRealSubfield L := by
        rw [← NumberField.IsCMField.complexConj_eq_self_iff]
        apply Subtype.ext
        rw [← hcc]
        exact (IntermediateField.mem_fixedField_iff _ _).mp hy σ hσU
      exact h _ hre
    · intro hs x hx
      have hσx : σ (x : Ω) = x := by
        rw [hcc, (NumberField.IsCMField.complexConj_eq_self_iff L x).mpr hx]
      show s (x : Ω) = x
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact (IntermediateField.mem_fixedField_iff _ _).mp x.2 s (Subgroup.mem_inf.mpr ⟨hs, h1⟩)
      · have hm : σ * s ∈ U ⊓ η.ker := by
          refine Subgroup.mem_inf.mpr ⟨U.mul_mem hσU hs, ?_⟩
          rw [MonoidHom.mem_ker, map_mul, hησ, h1]
          rfl
        have := (IntermediateField.mem_fixedField_iff _ _).mp x.2 (σ * s) hm
        rw [AlgEquiv.mul_apply] at this
        apply σ.injective
        rw [this, hσx]
  · ext s
    change (∀ x : L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U ⊓ η.ker
    rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusGaloisFieldFourCompatibility
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

namespace UpperTheory.V.Fr.DescentValuationAlt

private theorem smul_val_lt {Ω : Type} [Field Ω] [Algebra ℚ Ω] (g : G ℚ Ω) (A : ValuationSubring Ω) (n : ℕ)
    (hA : A.valuation (n : Ω) < 1) : (g • A).valuation (n : Ω) < 1 := by
  have fix : ∀ y : Ω, g y = y → (y ∈ g • A ↔ y ∈ A) := by
    intro y hy
    have hy' : g • y = y := hy
    constructor
    · intro h
      obtain ⟨s, hs, hgs⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists g y A).mp h
      have : s = y := by
        rw [← inv_smul_smul g s, hgs, inv_smul_eq_iff, hy']
      rwa [this] at hs
    · intro h
      have := ValuationSubring.smul_mem_pointwise_smul g y A h
      rwa [hy'] at this
  have vlt : ∀ (C : ValuationSubring Ω) (x : Ω), x ≠ 0 → (C.valuation x < 1 ↔ x ∈ C ∧ x⁻¹ ∉ C) := by
    intro C x hx
    haveI : Nontrivial C.ValueGroup := GroupWithZero.toNontrivial
    rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff, map_inv₀,
      inv_le_one₀ ((Valuation.pos_iff _).mpr hx), lt_iff_le_not_ge]
  by_cases h0 : (n : Ω) = 0
  · rw [h0, map_zero]
    haveI : Nontrivial (g • A).ValueGroup := GroupWithZero.toNontrivial
    exact zero_lt_one
  · have hn : g (n : Ω) = n := map_natCast g n
    have hni : g ((n : Ω)⁻¹) = (n : Ω)⁻¹ := by rw [map_inv₀, hn]
    rw [vlt _ _ h0] at hA ⊢
    rw [fix _ hn, fix _ hni]
    exact hA

private theorem descend {U Γ k : Type} [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [CompactSpace U]
    [Group Γ] [TopologicalSpace Γ] [T2Space Γ] [CommRing k] (p : U →* Γ) (hc : Continuous p)
    (hs : Function.Surjective p) (S : Set U) (hk : p.ker = (Subgroup.normalClosure S).topologicalClosure)
    (χ : Γ →* kˣ) (y : U → k) (hl : IsLocallyConstant y) (hy : ∀ s t, y (s * t) = y s + χ (p s) * y t)
    (hS : ∀ s ∈ S, y s = 0) :
    ∃ φ : Γ → k, IsLocallyConstant φ ∧ ∀ s, φ (p s) = y s := by
  have hy1 : y 1 = 0 := by
    have e := hy 1 1
    rw [mul_one, map_one, map_one, Units.val_one, one_mul] at e
    linear_combination -e
  let H : Subgroup U :=
    { carrier := {t | p t = 1 ∧ y t = 0}
      one_mem' := ⟨map_one p, hy1⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        show p (a * b) = 1 ∧ y (a * b) = 0
        refine ⟨by rw [map_mul, ha1, hb1, one_mul], ?_⟩
        rw [hy, ha2, hb2, mul_zero, add_zero]
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        show p a⁻¹ = 1 ∧ y a⁻¹ = 0
        refine ⟨by rw [map_inv, ha1, inv_one], ?_⟩
        have e := hy a a⁻¹
        rw [mul_inv_cancel, hy1, ha2, ha1, map_one, Units.val_one, one_mul, zero_add] at e
        exact e.symm }
  have hH : H.Normal := ⟨fun t ht g => by
    obtain ⟨ht1, ht2⟩ := ht
    show p (g * t * g⁻¹) = 1 ∧ y (g * t * g⁻¹) = 0
    refine ⟨by rw [map_mul, map_mul, map_inv, ht1, mul_one, mul_inv_cancel], ?_⟩
    have e1 := hy (g * t) g⁻¹
    have e2 := hy g t
    have e3 := hy g g⁻¹
    rw [mul_inv_cancel, hy1] at e3
    rw [map_mul, ht1, mul_one] at e1
    rw [ht2, mul_zero, add_zero] at e2
    rw [e1, e2, ← e3]⟩
  have hcl : IsClosed (H : Set U) :=
    (isClosed_eq hc continuous_const).inter (hl.isClosed_fiber 0)
  have hKH : p.ker ≤ H := by
    rw [hk]
    apply Subgroup.topologicalClosure_minimal _ _ hcl
    haveI := hH
    apply Subgroup.normalClosure_le_normal
    intro s hsS
    have hps : p s = 1 := by
      rw [← MonoidHom.mem_ker, hk]
      exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hsS)
    exact ⟨hps, hS s hsS⟩
  have hfib : ∀ s t, p s = p t → y s = y t := by
    intro s t hst
    have hk' : s⁻¹ * t ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel]
    obtain ⟨_, h2⟩ := hKH hk'
    have e := hy s (s⁻¹ * t)
    rw [mul_inv_cancel_left, h2, mul_zero, add_zero] at e
    exact e.symm
  have hq : Topology.IsQuotientMap p := (hc.isClosedMap).isQuotientMap hc hs
  refine ⟨fun γ => y (Function.surjInv hs γ), fun V => ?_, fun s => hfib _ _ (Function.surjInv_eq hs (p s))⟩
  have e : p ⁻¹' ((fun γ => y (Function.surjInv hs γ)) ⁻¹' V) = y ⁻¹' V := by
    ext s
    simp only [Set.mem_preimage]
    rw [hfib _ _ (Function.surjInv_eq hs (p s))]
  apply hq.isOpen_preimage.mp
  rw [e]
  exact hl V

end UpperTheory.V.Fr.DescentValuationAlt

open UpperTheory.V.Fr.DescentValuationAlt in
theorem UpperTheory.V.Fr.frobenius_galoisField_four_compatibility :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O)), UFacts l η Ψ M m (upl Ω L) → Linked l η Ψ σ g₁ B M L Φ → ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L) → Nontrivial (H1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) fun _ => ⊥) := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL a ha hS
  obtain ⟨k, -⟩ := hL
  obtain ⟨y, hyl, hyc, hyn, hyd, hyi⟩ := hS
  have hχ : ∀ s : upl Ω L, (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (k.p s)
      = ((barChar O Ψ)⁻¹ ^ a * etaO O η) s := by
    intro s
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply,
      MonoidHom.inv_apply, MonoidHom.inv_apply, k.psi]
    congr 1
    simp only [Frame.delK, etaO, MonoidHom.comp_apply, k.del]
  have hUc : IsClosed (upl Ω L : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen _ hU.isOpen
  haveI : CompactSpace (upl Ω L) := isCompact_iff_compactSpace.mp hUc.isCompact
  obtain ⟨φ, hφl, hφ⟩ := descend k.p k.p_cont k.p_surj _ k.p_ker (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))
    (fun s => y s) (hyl.comp_continuous continuous_subtype_val)
    (fun s t => by rw [hχ s]; exact hyc s t)
    (fun s hs => by
      obtain ⟨B', hB', hI, hη, hb⟩ := hs
      exact hyi B' hB' s (Subgroup.mem_inf.mpr ⟨hI, s.2⟩) hη hb)
  have hρ : ∀ (γ : Φ.Γ) (w : ResidueField O),
      (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ) w
        = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * w := fun γ w => rfl
  have hcoc : ∀ γ δ : Φ.Γ, φ (γ * δ)
      = φ γ + ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * φ δ := by
    intro γ δ
    obtain ⟨s, rfl⟩ := k.p_surj γ
    obtain ⟨t, rfl⟩ := k.p_surj δ
    rw [← map_mul, hφ, hφ, hφ, hχ]
    exact hyc s t
  have hloc : ∀ v : Φ.V, ∃ b : ResidueField O, ∀ g : Φ.Gv v,
      φ (Φ.loc v g) = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (Φ.loc v g) : ResidueField O) * b - b := by
    intro v
    obtain ⟨γ, -, hγ⟩ := k.pl_conj v
    have hv : (k.pl v).valuation (l : Ω) < 1 := by
      rw [hγ]
      exact smul_val_lt γ B l hG.over_l
    obtain ⟨b, hb⟩ := hyd _ hv
    refine ⟨b, fun g => ?_⟩
    rw [k.j_loc, hφ, hχ]
    exact hb _ ((k.j_range v _).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
  choose b hb using hloc
  let z : Z1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) (fun _ => ⊥) :=
    ⟨(φ, b), ⟨hφl, fun γ δ => by rw [hρ]; exact hcoc γ δ,
      fun v g => by rw [Submodule.mem_bot, hρ, ← hb v g, sub_self]⟩⟩
  refine ⟨⟨Submodule.Quotient.mk z, 0, fun h => ?_⟩⟩
  have hz := (Submodule.Quotient.mk_eq_zero _).mp h
  rw [Submodule.mem_comap] at hz
  obtain ⟨X, hX1, -⟩ := hz
  apply hyn
  refine ⟨X, fun s hs => ?_⟩
  have e1 := hφ ⟨s, hs⟩
  have e2 := hX1 (k.p ⟨s, hs⟩)
  rw [hρ, hχ] at e2
  rw [← e2]
  exact e1.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HlayPlace
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem hlay_place (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hmem : (p : Ω) ∈ (⊥ : Subring Ω) := Subring.mem_bot.mpr ⟨p, by simp⟩
  set x : (⊥ : Subring Ω) := ⟨p, hmem⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨b, hb⟩ := Subring.mem_bot.mp (u⁻¹ : (⊥ : Subring Ω)ˣ).1.2
    have h1 : (u : (⊥ : Subring Ω)) * (↑u⁻¹ : (⊥ : Subring Ω)) = 1 := u.mul_inv
    have h2 : ((p : ℤ) * b : ℤ) = (1 : Ω) := by
      have := congrArg Subtype.val h1
      simp only [Subring.coe_mul, Subring.coe_one] at this
      rw [hu] at this
      push_cast
      rw [hb]
      exact this
    have h3 : (p : ℤ) * b = 1 := by exact_mod_cast h2
    have h4 : (p : ℤ) ∣ 1 := ⟨b, h3.symm⟩
    have : p ∣ 1 := by exact_mod_cast h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (ValuationSubring.mem_nonunits_iff B).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

private theorem hlay_cop (l : ℕ) [hl : Fact l.Prime] (m : ℕ) : (l ^ m).Coprime (l - 1) := Nat.Coprime.pow_left m ((Nat.coprime_self_sub_right hl.out.one_le).mpr (Nat.coprime_one_right _))

private theorem hlay_card (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (h2 : l ≠ 2) :
    Nat.card ((⊤ : Subgroup (ZMod (l ^ (m + 1)))ˣ).map (powMonoidHom (l - 1))) = l ^ m := by
  haveI := ZMod.isCyclic_units_of_prime_pow l hl.out h2 (m + 1)
  rw [← MonoidHom.range_eq_map, IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ hl.out]
  have hpos : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  rw [Nat.gcd_comm, Nat.gcd_mul_left_right]
  exact Nat.mul_div_cancel _ hpos

private theorem hlay_inf {l : ℕ} [hl : Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) (h1 : u ∈ KStar.TotallyRealRoots.princ l 1)
    (h : KStar.TotallyRealRoots.redPow l (m + 1) u ^ (l - 1) = 1) : KStar.TotallyRealRoots.redPow l (m + 1) u = 1 := by
  set x := KStar.TotallyRealRoots.redPow l (m + 1) u with hx
  have hd : l ^ 1 ∣ l ^ (m + 1) := pow_dvd_pow l (by omega)
  set f := ZMod.unitsMap hd
  have hfx : f x = 1 := by
    have : f x = KStar.TotallyRealRoots.redPow l 1 u := by
      ext
      simp only [f, hx, ZMod.unitsMap, KStar.TotallyRealRoots.redPow, Units.coe_map, MonoidHom.coe_coe]
      exact congrArg (fun g => g (u : ℤ_[l])) (PadicInt.zmod_cast_comp_toZModPow 1 (m + 1) (by omega))
    rw [this]
    exact h1
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective hd
  have hcardG : Nat.card (ZMod (l ^ (m + 1)))ˣ = l ^ m * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hl.out]
  have hcardH : Nat.card (ZMod (l ^ 1))ˣ = l - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out]
  have hker : Nat.card f.ker = l ^ m := by
    have e := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcardH, hcardG] at e
    exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hl.out.one_lt) e
  have hpow : x ^ (l ^ m) = 1 := by
    have := pow_card_eq_one' (G := f.ker) (x := ⟨x, hfx⟩)
    rw [hker] at this
    exact congrArg Subtype.val this
  have hdvd : orderOf x ∣ Nat.gcd (l ^ m) (l - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one h)
  rw [hlay_cop l m, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact hdvd

theorem UpperTheory.V.Fr.hlay :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (m : ℕ), l ≠ 2 → IsOpen (Hlay Ω l m : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ Hlay Ω l m ∧ (Hlay Ω l m).index = l ^ m ∧ Hlay Ω l m ⊓ (cycMod ℚ Ω l 1).ker = (cycMod ℚ Ω l (m + 1)).ker ∧ (∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → Ine (F := ℚ) B' ≤ Hlay Ω l m) ∧ ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → (Hlay Ω l m).relIndex (Ine (F := ℚ) B') = l ^ m ∧ ∀ r, (Ine (F := ℚ) B').map (cycMod ℚ Ω l r) = ⊤ := by
  intro Ω _ _ _ l _ m h2
  obtain ⟨A, hA⟩ := hlay_place Ω l Fact.out
  have hsurjIne : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 →
      ∀ r, (Ine (F := ℚ) B').map (cycMod ℚ Ω l r) = ⊤ := by
    intro B' hB' r
    rw [eq_top_iff]
    rintro y -
    obtain ⟨v, rfl⟩ := KStar.TotallyRealRoots.redPow_surjective (l := l) r y
    obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l B' hB' v
    exact ⟨σ, hσ, by rw [← hσv]; rfl⟩
  have hidx : ∀ K : Subgroup (G ℚ Ω), K.map (cycMod ℚ Ω l (m + 1)) = ⊤ →
      (Hlay Ω l m).relIndex K = l ^ m := by
    intro K hK
    have hsub : (Hlay Ω l m).subgroupOf K = ((cycMod ℚ Ω l (m + 1) ^ (l - 1)).comp K.subtype).ker := by
      ext x
      rfl
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
    have hr : ((cycMod ℚ Ω l (m + 1) ^ (l - 1)).comp K.subtype).range =
        (⊤ : Subgroup (ZMod (l ^ (m + 1)))ˣ).map (powMonoidHom (l - 1)) := by
      ext y
      simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_top, true_and, MonoidHom.comp_apply,
        Subgroup.coe_subtype, MonoidHom.pow_apply, powMonoidHom_apply]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨z, rfl⟩
        have hz : z ∈ K.map (cycMod ℚ Ω l (m + 1)) := hK ▸ Subgroup.mem_top z
        obtain ⟨k, hk, rfl⟩ := hz
        exact ⟨⟨k, hk⟩, rfl⟩
    rw [hr]
    exact hlay_card l m h2
  have hcont := (UpperTheory.V.Base.contTw ℚ Ω l).1
  have hkerle : (cycMod ℚ Ω l (m + 1)).ker ≤ Hlay Ω l m := by
    intro σ hσ
    show (cycMod ℚ Ω l (m + 1) σ) ^ (l - 1) = 1
    rw [MonoidHom.mem_ker.mp hσ, one_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun B' hB' => ⟨hidx _ (hsurjIne B' hB' _), hsurjIne B' hB'⟩⟩
  · apply Subgroup.isOpen_mono hkerle
    have hset : ((cycMod ℚ Ω l (m + 1)).ker : Set (G ℚ Ω)) =
        cycZ ℚ Ω l ⁻¹' (KStar.TotallyRealRoots.princ l (m + 1) : Set ℤ_[l]ˣ) := by
      ext σ
      rfl
    rw [hset]
    exact (KStar.TotallyRealRoots.isOpen_princ (m + 1)).preimage hcont
  · exact Abelianization.commutator_subset_ker _
  · rw [← Subgroup.relIndex_top_right]
    exact hidx ⊤ (top_unique ((hsurjIne A hA _).symm.le.trans (Subgroup.map_mono le_top)))
  · apply le_antisymm
    · rintro σ ⟨h1, h1'⟩
      exact hlay_inf m (cycZ ℚ Ω l σ) h1' h1
    · intro σ hσ
      exact ⟨hkerle hσ, KStar.TotallyRealRoots.princ_anti (by omega) hσ⟩
  · intro B' hB'
    refine ((UpperTheory.V.Base.places ℚ Ω l B').2.2.2 hB').trans ?_
    intro σ hσ
    apply hkerle
    show KStar.TotallyRealRoots.redPow l (m + 1) (cycZ ℚ Ω l σ) = 1
    rw [MonoidHom.mem_ker.mp hσ, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SoCls
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem so_cls {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (s : G ℚ Ω) :
    Chr.cls ℚ Ω (l ^ 1) s = cycMod ℚ Ω l 1 s := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  refine (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s _ (fun ζ hζ => ?_)
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ

theorem UpperTheory.V.Fr.sc_om :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l], Af.KillsMu l (omO Ω l O) ∧ ∀ σ : G ℚ Ω, IsCC σ → omO Ω l O σ = -1 := by
  intro Ω _ _ _ l _ O _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact (Fact.out : l.Prime).one_lt⟩
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycMod ℚ Ω l 1 s = 1 := by
      rw [← so_cls]
      refine (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s 1 (fun ζ hζ => ?_)
      rw [pow_one] at hζ
      rw [hs ζ hζ, Units.val_one, ZMod.val_one, pow_one]
    simp only [omO, GC.cycF, MonoidHom.comp_apply, h1, map_one]
  · have h1 : cycMod ℚ Ω l 1 σ = -1 := by
      rw [← so_cls]
      exact (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.2.1 σ hσ
    simp only [omO, GC.cycF, MonoidHom.comp_apply, h1]
    ext
    simp
end

