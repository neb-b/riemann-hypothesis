module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarSpecialUnitaryProductChartFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioConjOfToricRatioConjugates
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open Cardinal

namespace GlobalTheory.ToricRatioBridge

abbrev algC : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

theorem mem_algC {z : ℂ} : z ∈ algC ↔ IsAlgebraic ℚ z := mem_algebraicClosure_iff

theorem isAlgebraic_finPart {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {m : I → ℤ}
    {χ : HChar E} (hm : HasInf χ φ m) {c : Ideal (OF E)} [Finite (PicO c)] (hu : ∀ y ∈ hatOUnits c, finPart χ y = 1)
    (y : (Af E)ˣ) : IsAlgebraic ℚ (finPart χ y : ℂ) := by
  let M : Subfield ℂ := algC
  let H : Subgroup (Af E)ˣ := M.toSubmonoid.units.comap (finPart χ)
  have hH : ∀ y, y ∈ H ↔ (finPart χ y : ℂ) ∈ M := fun y =>
    ⟨fun h => h.1, fun h => (Submonoid.mem_units_iff _ _).2 ⟨h, by rw [Units.val_inv_eq_inv_val]; exact M.inv_mem h⟩⟩
  have hE : ∀ (σ : E →+* ℂ) (x : E), σ x ∈ M := fun σ x =>
    mem_algC.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic
  have hle : princ ⊔ hatOUnits c ≤ H := by
    refine sup_le ?_ fun u h => (hH u).2 (by rw [hu u h]; exact one_mem M)
    rintro _ ⟨k, rfl⟩
    rw [hH, eq_inv_of_mul_eq_one_left (finPart_mul_inf χ k), Units.val_inv_eq_inv_val, (hasInfRatio_iff χ φ m).1 hm k]
    exact inv_mem (prod_mem fun i _ => zpow_mem (div_mem (hE _ _) (hE ((starRingEnd ℂ).comp (φ i)) _)) _)
  let p : PicO c →* (Af E)ˣ ⧸ H := QuotientGroup.map _ _ (MonoidHom.id _) hle
  have : Finite ((Af E)ˣ ⧸ H) := Finite.of_surjective p fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hn := pow_card_eq_one' (G := (Af E)ˣ ⧸ H) (x := (QuotientGroup.mk y))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hH, map_pow, Units.val_pow_eq_pow_val] at hn
  exact IsAlgebraic.of_pow Nat.card_pos (mem_algC.1 hn)

theorem exists_eq_of_isAlgebraic {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) :
    ∃ x : Ω, j x = z := by
  let _ : Algebra Ω ℂ := j.toAlgebra
  have : CharZero Ω := RingHom.charZero j
  have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast j q).symm
  have hi : IsIntegral Ω z := (hz.isIntegral).tower_top
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one Ω z
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hi))
  exact ⟨x, hx⟩

theorem comp_eq_of_sqrt {R : Ranks} (H : Host R) (f g : H.E →+* ℂ) (h : f H.sqrtMinusD = g H.sqrtMinusD) :
    f.comp (algebraMap H.K H.E) = g.comp (algebraMap H.K H.E) := by
  refine RingHom.ext fun x => ?_
  have hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqrtMinusD} := by
    have h1 : IsIntegral ℚ H.sqrtMinusD := Algebra.IsIntegral.isIntegral _
    have : (x : H.E) ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := x.2
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1.isAlgebraic] at this
    exact this
  have hle : Algebra.adjoin ℚ {H.sqrtMinusD} ≤ AlgHom.equalizer f.toRatAlgHom g.toRatAlgHom :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 h)
  show f (x : H.E) = g (x : H.E)
  exact hle hx

theorem upIdele_eq (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele K E t = Units.map (GlobalTheory.AdeleBaseChange.adMap K E).toMonoidHom t :=
  Units.ext (FiniteAdeleRing.ext _ fun P => (GlobalTheory.CharTransport.locMap_eq K E P _).symm)

theorem countable_of_isAlgClosure (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Countable Ω := by
  have hK : #K ≤ ℵ₀ := by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (Algebra.IsAlgebraic.cardinalMk_le_max K Ω).trans (max_le hK le_rfl)

end GlobalTheory.ToricRatioBridge

namespace GlobalTheory.ToricRatioBridge

open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (ToricRatioConjugates IsSymbol classOf conjChar)

theorem ratioConj_of_toricRatioConjugates (hG : ToricRatioConjugates) : GlobalTheory.ToricRational.RatioConj := by
  intro R H I _ φ s κ 𝔣 χ hD Ω _ _ _ j τ₀ hj art ha T₀ hT₀ h0 Q hQ hfin T hT
  have : IsCMField H.E := H.isCMField_hostE
  have hU : UnramFin H.E := GlobalTheory.ToricDenomBridge.host_unramFin H
  let ι : H.K →+* ℂ := (φ τ₀).comp (algebraMap H.K H.E)
  have hι : ∀ i, (φ i).comp (algebraMap H.K H.E) = ι := fun i => comp_eq_of_sqrt H _ _ (hD.2.1 i τ₀)
  let δ : H.K := ⟨H.sqrtMinusD, H.sqd_mem_K⟩
  have hδ : δ ^ 2 = -(H.d : H.K) := Subtype.ext (by push_cast; exact H.sqrtMinusD_sq)
  have hK2 : Module.finrank ℚ H.K = 2 := H.finrank_K
  obtain ⟨T₀', Tw, hT₀', -, hTw, halg, hconj⟩ := hG H.E H.K H.d δ ι I φ s κ 𝔣 Q χ hU hK2 H.hyp.2.1.pos hδ hD.1 hι
    hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1 hQ hD.2.2.2.2.2
  have h𝔣 : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  have hT₀'' : IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀' := by rw [h𝔣]; exact hT₀'
  have e0 : T₀' = T₀ := hT₀''.unique hT₀
  subst e0
  let up : (PicO (condQ 𝔣 Q) →* Ωˣ) → (PicO (condQ 𝔣 Q) →* ℂˣ) := fun ψ => (Units.map j.toMonoidHom).comp ψ
  have hsum : ∀ ψ', Tw ψ' = ∑ᶠ q, ((ψ' q : ℂˣ) : ℂ)⁻¹ * T q := fun ψ' => by
    obtain ⟨_, S, hS, e⟩ := hTw ψ'
    rw [e]
    refine finsum_congr fun q => ?_
    obtain ⟨S', hS', e'⟩ := hT q
    rw [e', mul_assoc, (hS q).unique hS']
    rfl
  have hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed H.K
  choose ρ hρ using fun ψ => exists_eq_of_isAlgebraic j (halg (up ψ))
  refine ⟨ρ, fun ψ => by rw [hρ, hsum]; rfl, fun g hgE hgl t ht ψ => ?_⟩
  have : Countable Ω := countable_of_isAlgClosure H.K Ω
  obtain ⟨g', hg'⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq j (j.comp g.toRingEquiv.toRingHom)
  have hfix : ∀ z : ℂ, IsAlgebraic ℚ z → (∀ x, j x = z → g x = x) → g' z = z := fun z hz hx => by
    obtain ⟨x, rfl⟩ := exists_eq_of_isAlgebraic j hz
    rw [hg']
    exact congrArg j (hx x rfl)
  have hφ : ∀ i (x : H.E), IsAlgebraic ℚ (φ i x) := fun i x =>
    ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map (φ i).toRatAlgHom).isAlgebraic
  have : Finite (PicO (condQ 𝔣 ∅)) := hT₀.1
  have hl : ∀ y, IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y) := fun y => by
    have h1 := isAlgebraic_finPart hD.2.2.2.2.2.2.2.1 (c := condQ 𝔣 ∅)
      (OrderUnits.finPart_eq_one H.E I φ hD.1 s κ 𝔣 ∅ χ hU hD.2.2.2.2.1 (fun _ h => absurd h (Finset.notMem_empty _))
        hD.2.2.2.2.2) y
    refine mem_algC.1 (mul_mem (mem_algC.2 h1) ?_)
    rw [Complex.ofReal_pow]
    exact pow_mem (GlobalTheory.ToricRational.modF_mem _ y) s
  have hσ : ∀ x, j (g x) = g' (j x) := fun x => (hg' x).symm
  have hsym : IsSymbol art t g := by rw [IsSymbol, ht, map_inv, inv_inv]
  obtain ⟨e, -⟩ := hconj Ω j art (RingHom.ext hj) ha g' g t (fun i x => hfix _ (hφ i x) fun x' hx' => hgE x' i x hx')
    (fun y => hfix _ (hl y) fun x' hx' => hgl x' y hx') hσ hsym (up ψ)
  have hc : conjChar g' (up ψ) = up ((Units.map g.toRingEquiv.toMonoidHom).comp ψ) :=
    MonoidHom.ext fun q => Units.ext (hg' _)
  have hcls : classOf H.K (condQ 𝔣 Q) t = QuotientGroup.mk (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele H.K H.E t) := by
    rw [classOf, upIdele_eq]
  apply j.injective
  rw [hσ, hρ, e, hc, hcls, map_mul, map_inv₀, hρ]
  rfl

end GlobalTheory.ToricRatioBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfCompactOpen
section
open GlobalTheory.LKCount
open scoped Classical

namespace GlobalTheory.RelIndexCompact

theorem relIndex_ne_zero_of_compact_open {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {K L : Subgroup G} (hL : IsCompact (L : Set G))
    (hK : IsOpen (K : Set G)) : K.relIndex L ≠ 0 := by
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((K.subgroupOf L : Subgroup L) : Set L) := hK.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem conj_map_isCompact_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (x : G) (hK : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) :
    IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ∧
      IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have hc : Continuous (fun g : G => x * g * x⁻¹) := by fun_prop
  refine ⟨hK.image hc, ?_⟩
  have : ((MulAut.conj x).toMonoidHom : G → G) '' (K : Set G) =
      (fun g : G => x⁻¹ * g * x) ⁻¹' (K : Set G) := by
    ext y; simp [MulAut.conj_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa [mul_assoc] using ha
    · intro hy; exact ⟨x⁻¹ * y * x, hy, by group⟩
  rw [this]; exact ho.preimage (by fun_prop)

end GlobalTheory.RelIndexCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section Hom

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem subst_sum_smul {σ τ ι : Type} [Fintype ι] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (m : ι → C)
    (f : ι → MvPowerSeries σ C) : subst a (∑ i, m i • f i) = ∑ i, m i • (subst a (f i) : MvPowerSeries τ C) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← substAlgHom_apply ha, map_sum]
  simp only [map_smul, substAlgHom_apply]

theorem isIntHom_comp {d d' d'' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'} {G'' : LogFGL v d''}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {ψ : Fin d'' → MvPowerSeries (Fin d') C}
    {M : Matrix (Fin d') (Fin d) C} {N : Matrix (Fin d'') (Fin d') C}
    (hφ : IsIntHom G G' φ M) (hψ : IsIntHom G' G'' ψ N) :
    IsIntHom G G'' (fun b => subst φ (ψ b)) (N * M) := by
  obtain ⟨hφ0, hφi, hφl⟩ := hφ
  obtain ⟨hψ0, hψi, hψl⟩ := hψ
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  refine ⟨fun b => constantCoeff_subst_eq_zero hφs hφ0 (hψ0 b), fun b => ?_, fun c => ?_⟩
  · exact ptIntSer_subst hφs (fun s => hφi s) (hψi b)
  · rw [← subst_comp_subst_apply hψs hφs, hψl c, subst_sum_smul hφs]
    simp_rw [hφl, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm

end Hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

section Labels

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def embO (σ : E →+* ℂ) : 𝓞 E →+* X.O where
  toFun a := (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose
  map_one' := X.ints.hom_inj (by rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_one, map_one])
  map_zero' := X.ints.hom_inj (by
    rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_zero, map_zero])
  map_mul' a b := X.ints.hom_inj (by
    rw [map_mul (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_mul])
  map_add' a b := X.ints.hom_inj (by
    rw [map_add (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_add])

theorem algebraMap_embO (σ : E →+* ℂ) (a : 𝓞 E) : algebraMap X.O X.C (embO io X σ a) = embX io X σ a :=
  (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose_spec

def red (σ : E →+* ℂ) : 𝓞 E →+* ResidueField X.O := (residue X.O).comp (embO io X σ)

theorem residue_eq_zero_iff_v (x : X.O) : residue X.O x = 0 ↔ X.v (algebraMap X.O X.C x) < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, X.ints.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (X.ints.map_le_one x) h, fun h => h.ne⟩

theorem residue_eq_iff_v (x y : X.O) :
    residue X.O x = residue X.O y ↔ X.v (algebraMap X.O X.C x - algebraMap X.O X.C y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_v, map_sub]

theorem primeBelow_eq_ker (σ : E →+* ℂ) : primeBelow io X σ = RingHom.ker (red io X σ) := by
  ext a
  rw [RingHom.mem_ker]
  show X.v (embX io X σ a) < 1 ↔ residue X.O (embO io X σ a) = 0
  rw [residue_eq_zero_iff_v, algebraMap_embO]

theorem red_eq_pow_iff (σ σ' : E →+* ℂ) (a : 𝓞 E) (n : ℕ) :
    red io X σ' a = red io X σ a ^ n ↔ X.v (embX io X σ' a - embX io X σ a ^ n) < 1 := by
  show residue X.O (embO io X σ' a) = residue X.O (embO io X σ a) ^ n ↔ _
  rw [← map_pow, residue_eq_iff_v, map_pow, algebraMap_embO, algebraMap_embO]

theorem charP_residueField_of_irreducible : CharP (ResidueField X.O) p := by
  have h : ((p : ℕ) : ResidueField X.O) = 0 := by
    rw [← map_natCast (residue X.O), residue_eq_zero_iff]
    exact X.nonunit.out
  exact (CharP.charP_iff_prime_eq_zero Fact.out).2 h

theorem vX_vp_pos_iff (x : X.C) : 0 < vX_vp X x ↔ X.v x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpO : ¬ IsUnit (p : X.O) := X.nonunit.out
  have hp1 : X.v (p : X.C) < 1 := by
    have h := X.ints.map_le_one (p : X.O)
    rw [map_natCast] at h
    refine lt_of_le_of_ne h fun h1 => hpO ?_
    apply X.ints.isUnit_of_one'
    rw [map_natCast]
    exact h1
  have hp0 : (0 : NNReal) < X.v (p : X.C) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : (0 : NNReal) < X.v x := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact hx
  have hlp : Real.log (X.v (p : X.C) : ℝ) < 0 :=
    Real.log_neg (by exact_mod_cast hp0) (by exact_mod_cast hp1)
  have hi : (Real.log (X.v (p : X.C) : ℝ))⁻¹ < 0 := inv_lt_zero.mpr hlp
  rw [vX_vp_apply X hx, show (0 : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) from rfl, WithTop.coe_lt_coe,
    mul_pos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact absurd h1 (not_lt.mpr hi.le)
    · have h3 := (Real.log_neg_iff (by exact_mod_cast hx0)).mp h2
      exact_mod_cast h3
  · intro h
    right
    exact ⟨hi, Real.log_neg (by exact_mod_cast hx0) (by exact_mod_cast h)⟩

end Labels

variable {Dw : Datum H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr}
  {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def tanX (a : 𝓞 E) : Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  Matrix.of fun i j => jX X (coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a i))

end GlobalTheory.PrimePart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarSpecialUnitaryEqSmulHaar
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory.RiemConst

theorem riemHaar_eq_smul (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)]
    (ν : Measure (realSU X.Ψ X.Gm)) (hr : 1 ≤ r) (hx : IsOrth X x) (hν : ν.IsHaarMeasure)
    (hfib : ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) →
      ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν =
        ∫⁻ z, φ (cpt X x z) ∂muF X x) :
    riemHaar X.Ψ X.Gm x = ENNReal.ofReal
      (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) • ν := by
  obtain ⟨hdc, hd0, hdet⟩ := _root_.GlobalTheory.DensOne.dens_one E r X x hx
  obtain ⟨hf, hnd⟩ := _root_.GlobalTheory.ChartCount.fdeg_and_nd E r X
  obtain ⟨σ, ρ, D₁, hρ, hσ0, hσc, hσB, hσD, hD₁⟩ := _root_.GlobalTheory.SUChartSection.exists_section E r X x hx
  obtain ⟨t, Dt, htx, htmul, htc, htD, hDt, hstab⟩ := _root_.GlobalTheory.TorusFrame.torus_param E r X x hx
  have ht0 : t 0 = 1 := by
    have h := congrArg (fun g => (t 0)⁻¹ * g) (htmul 0 0)
    simp only [add_zero, inv_mul_cancel, inv_mul_cancel_left] at h
    exact h.symm
  let D : ChartSp X →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ) :=
    D₁.comp (ContinuousLinearMap.fst ℝ (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ)) +
      Dt.comp (ContinuousLinearMap.snd ℝ (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ))
  have hQD := _root_.GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity X.Ψ r (realSU X.Ψ X.Gm) (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ) σ t D₁ Dt hσ0 ht0 hσD htD
  have hspec : ∀ w : ChartSp X, D w ∈ realLie X.Ψ X.Gm ∧
      (∀ τ a b, b < a → inFrame x (D w) τ a b = nmat X w.1 τ a b) ∧
        ∀ τ a, inFrame x (D w) τ a a = Complex.I * (angles (w.2 τ) a : ℂ) := by
    intro w
    have hDw : D w = D₁ w.1 + Dt w.2 := rfl
    have e : ∀ τ, inFrame x (D w) τ = inFrame x (D₁ w.1) τ + inFrame x (Dt w.2) τ := by
      intro τ
      simp only [inFrame, hDw]
      rw [show Matrix.of ((D₁ w.1 + Dt w.2) τ) = Matrix.of (D₁ w.1 τ) + Matrix.of (Dt w.2 τ) from rfl,
        Matrix.mul_add, Matrix.add_mul]
    obtain ⟨h1, h2, h3⟩ := hD₁ w.1
    obtain ⟨h4, h5⟩ := hDt w.2
    refine ⟨?_, fun τ a b hab => ?_, fun τ a => ?_⟩
    · rw [hDw]; exact (realLie X.Ψ X.Gm).add_mem h1 h4
    · rw [e, Matrix.add_apply, h2 τ a b hab, h5, if_neg (ne_of_gt hab), add_zero]
    · rw [e, Matrix.add_apply, h3, h5, if_pos rfl, zero_add]
  obtain ⟨hDinj, hriem⟩ := GlobalTheory.T.riemannianMeasure_lieAlgebra_eq_smul_map_chartLebesgue E r X x hr hx D hspec
  have hform := _root_.GlobalTheory.FibreVol.haar_chart_formula E r X x ν σ t ρ hr hx hν hfib hρ hσc hσB htx htmul htc hstab
  have hsurj := _root_.GlobalTheory.eq_chart_mul_of_near_one E r X x σ t ρ hx hρ hσ0 hσc hσB htx htmul htc hstab
  set m := (r - 1) * X.Ψ.card with hm
  set a : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.pi) ^ m) with ha
  have hpi : 0 < (2 * Real.pi) ^ m := by positivity
  have ha0 : a ≠ 0 := by
    rw [ha, Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have htend : Tendsto (fun w : ChartSp X => ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ m)) (𝓝 0) (𝓝 a) := by
    have h1 : ContinuousAt (fun w : ChartSp X => densF X x w.1) 0 :=
      ContinuousAt.comp (g := densF X x) (f := Prod.fst) (x := (0 : ChartSp X)) hdc continuous_fst.continuousAt
    have h2 := (ENNReal.continuous_ofReal.continuousAt).tendsto.comp ((h1.div_const ((2 * Real.pi) ^ m)).tendsto)
    rw [ha]
    simpa [Function.comp_def, hd0] using h2
  have hρ' : 0 < min ρ Real.pi := lt_min hρ Real.pi_pos
  have hQ0 : (fun w : ChartSp X => σ w.1 * t w.2) 0 = 1 := by simp [hσ0, ht0]
  haveI : (volume : Measure (X.Ψ → Fin (r - 1) → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ChartSp X)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (V (nd X))) (volume : Measure (X.Ψ → Fin (r - 1) → ℝ))
  have hlim := _root_.GlobalTheory.SUVol.DensChart.density_at_one X.Ψ r (realSU X.Ψ X.Gm) ν (ChartSp X) volume (fun w => σ w.1 * t w.2) D
    (fun w => ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ m)) a (min ρ Real.pi) hQD hQ0 hDinj hsurj htend
    ha0 hatop hρ' hform
  obtain ⟨hRH, hRdens⟩ := GlobalTheory.SUVol.DensOne.tangentHaar_riemLie X.Ψ X.Gm X.Gm_det x hdet
  have hRH' : (riemHaar X.Ψ X.Gm x).IsHaarMeasure := hRH
  set k := (riemHaar X.Ψ X.Gm x).haarScalarFactor ν with hkdef
  have hk : riemHaar X.Ψ X.Gm x = k • ν := Measure.isMulLeftInvariant_eq_smul _ _
  set K := ENNReal.ofReal (2 ^ nd X * Real.sqrt r ^ X.Ψ.card) with hKdef
  have hK0 : K ≠ 0 := by
    rw [hKdef, Ne, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast hr)
    positivity
  have hKtop : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : Tendsto (fun ε : ℝ => (k : ℝ≥0∞) * (ν (grpBall (realSU X.Ψ X.Gm) ε) /
      ((volume : Measure (ChartSp X)).map D) (tanBall X.Ψ r ε)) * K⁻¹) (𝓝[>] 0) (𝓝 ((k : ℝ≥0∞) * a * K⁻¹)) :=
    ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top))
      (Or.inr (ENNReal.inv_ne_top.2 hK0))
  unfold HasDensityOne at hRdens
  have h2 : Tendsto (fun ε : ℝ => (k : ℝ≥0∞) * (ν (grpBall (realSU X.Ψ X.Gm) ε) /
      ((volume : Measure (ChartSp X)).map D) (tanBall X.Ψ r ε)) * K⁻¹) (𝓝[>] 0) (𝓝 1) := by
    refine hRdens.congr fun ε => ?_
    rw [show tangentHaar (realSU X.Ψ X.Gm) (riemLie X.Ψ X.Gm x) = riemHaar X.Ψ X.Gm x from rfl, hk, hriem]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hK0) (Or.inl hKtop)]
    ring
  have e := tendsto_nhds_unique h1 h2
  have hkval : (k : ℝ≥0∞) = ENNReal.ofReal
      (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) := by
    have e' : (k : ℝ≥0∞) * (a * K⁻¹) = 1 := by rw [← mul_assoc]; exact e
    have hai : a⁻¹ = ENNReal.ofReal ((2 * Real.pi) ^ m) := by
      rw [ha, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
    rw [ENNReal.eq_inv_of_mul_eq_one_left e', ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop), inv_inv, hai,
      hKdef, ← ENNReal.ofReal_mul hpi.le]
    congr 1
    rw [hf, hnd, hm]
    generalize r * (r - 1) / 2 = n1
    generalize r - 1 = n2
    ring
  rw [hk, ← hkval]
  ext s _
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory.RiemConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersJointEigenspaceDisjointBiSup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

theorem eigSp_disjoint_biSup : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (s : Finset (F →+* ℂ)) (τ : F →+* ℂ), τ ∉ s → Disjoint (eigSp φ τ) (⨆ τ' ∈ s, eigSp φ τ') := by
  intro F _ _ g φ s τ hτ
  let ρ : 𝓞 F →+* Module.End ℂ (Fin g → ℂ) := (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)).toRingEquiv.toRingHom.comp φ
  have hcomm : ∀ a b : 𝓞 F, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : 𝓞 F => ρ a)
    (fun i j m => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) m)
  let χ : (F →+* ℂ) → (𝓞 F → ℂ) := fun σ c => σ (c : F)
  have hχ : Function.Injective χ := by
    intro σ₁ σ₂ he
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
    ext c
    exact congrFun he c
  have hle : ∀ σ : F →+* ℂ, eigSp φ σ ≤ ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (χ σ c) := by
    intro σ u hu
    rw [Submodule.mem_iInf]
    intro c
    apply (Module.End.genEigenspace (ρ c) (χ σ c)).mono le_top
    rw [Module.End.mem_eigenspace_iff]
    have := hu c
    simpa [ρ, χ, Matrix.toLin'_apply] using this
  have hnot : χ τ ∉ (χ '' (s : Set (F →+* ℂ))) := by
    rintro ⟨σ, hσ, he⟩
    exact hτ (hχ he ▸ hσ)
  have hd := h.disjoint_biSup hnot
  refine (hd.mono_left (hle τ)).mono_right ?_
  refine iSup₂_le fun σ hσ => (hle σ).trans ?_
  exact le_iSup₂_of_le (f := fun (x : 𝓞 F → ℂ) (_ : x ∈ χ '' (s : Set (F →+* ℂ))) => ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (x c)) (χ σ) ⟨σ, hσ, rfl⟩ le_rfl

end GlobalTheory.UPel.HT.LieType
end
end

