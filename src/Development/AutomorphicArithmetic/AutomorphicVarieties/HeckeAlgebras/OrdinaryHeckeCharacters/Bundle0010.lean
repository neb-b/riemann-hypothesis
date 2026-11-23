module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeFixedLevelSpaces.FreeMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeFixedLevelSpaces.AddOnePowEqRingHomImageAddPrimeMulZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ProdZpowConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ReHecke
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem re_chi {n : ℕ} {k H : Type} [CommRing k] [Group H] (χ : Fin n → H →* kˣ) (g : H) :
    (W.GDet.ofRep (W.diagRep χ)).chi (MonoidAlgebra.single g 1) = ∏ i, (X - C (χ i g : k)) := by
  change (W.GDet.repAlg (W.diagRep χ) k[X] _).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [W.GDet.repAlg, W.diagRep, Matrix.one_apply, Matrix.diagonal_apply, h]

private theorem re_hecke {k : Type} [Field k] {n q : ℕ} (hq : (q : k) ≠ 0) (P : k[X]) (hm : P.Monic)
    (hn : P.natDegree = n) : ∃ b : Fin n → k,
      P = heckePol n q fun j => if h : 0 < j ∧ j - 1 < n then b ⟨j - 1, h.2⟩ else 1 := by
  refine ⟨fun i => (-1) ^ (i + 1 : ℕ) * ((q : k) ^ ((i + 1) * i / 2 : ℕ))⁻¹ * P.coeff (n - (i + 1)), ?_⟩
  rw [Hi.heckePol, ← Finset.sum_range_reflect]
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow, hn]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
  rw [show j + d + 1 - 1 - j = d by omega, show j + d - d = j by omega]
  congr 2
  rcases d with _ | d
  · have := hm.coeff_natDegree
    rw [hn] at this
    simpa using this
  · rw [dite_eq_left ⟨by omega, by omega⟩]
    simp only [Nat.add_sub_cancel]
    have h1 : ((-1 : k) ^ (d + 1)) * (-1) ^ (d + 1) = 1 := by rw [← mul_pow]; simp
    have h2 : (q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq)
    linear_combination (-P.coeff j) * h2 - P.coeff j * ((q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹) * h1

open scoped Pointwise in
private theorem re_frob {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (χ : G E Ω →* M) {w : HeightOneSpectrum (𝓞 E)}
    (hχ : ∀ A, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, χ s = 1) {q : ℕ} {A B : ValuationSubring Ω}
    (hA : IsPlaceOver A w) (hB : IsPlaceOver B w) {σ τ : G E Ω} (hσ : IsFrob A q σ) (hτ : IsFrob B q τ) :
    χ τ = χ σ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := E) hA hB
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  have h0 : IsFrob (F := E) A q (g⁻¹ * τ * g) := by
    refine ⟨?_, fun x hx => ?_⟩
    · have h1 : τ • g • A = g • A := hτ.1
      show (g⁻¹ * τ * g) • A = A
      rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · have h1 := hτ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
        ← ValuationSubring.valuation_le_one_iff])
      have e : τ (g x) - g x ^ q = g ((g⁻¹ * τ * g) x - x ^ q) := by
        rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
      rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
        ← valuation_lt_one_iff'] at h1
  have h2 := hχ A hA _ (inv_mul_mem_Ine_of_isFrob hσ h0)
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul] at h2
  exact h2.symm

private theorem re_art {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) {M : Type} [CommGroup M]
    (ψ : Dec (F := E) A →* M) (hψ : IsOpen (ψ.ker : Set (Dec (F := E) A))) {x y : Weil h} (hxy : a x = a y) :
    ψ (Subgroup.inclusion (Weil_le_Dec h) x) = ψ (Subgroup.inclusion (Weil_le_Dec h) y) := by
  haveI : CompactSpace (Dec (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : Finite (Dec (F := E) A ⧸ ψ.ker) := ψ.ker.quotient_finite_of_isOpen hψ
  haveI : Finite ψ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  let ι := Subgroup.inclusion (Weil_le_Dec h)
  by_contra hne
  have h1 : ψ.rangeRestrict (ι (x * y⁻¹)) ≠ 1 := fun h1 => hne (by
    have h2 : ψ (ι (x * y⁻¹)) = 1 := congrArg Subtype.val h1
    rwa [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h2)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ψ.range ℂ h1
  have hs : GlobalTheory.WeilDeligne.IsSmooth (ψ.comp ι) :=
    hψ.preimage (f := Subgroup.inclusion (Ine_le_Dec (F := E) A)) (continuous_inclusion (Ine_le_Dec (F := E) A))
  obtain ⟨χ, -, hχ⟩ := ha.factor (φ.comp (ψ.rangeRestrict.comp ι)) (hs.of_le fun σ hσ => by
    have : ψ.rangeRestrict (ι σ) = 1 := Subtype.ext hσ
    simp only [MonoidHom.comp_apply, this, map_one])
  apply hφ
  have h3 := DFunLike.congr_fun hχ (x * y⁻¹)
  rw [MonoidHom.comp_apply χ, map_mul a, map_inv a, hxy, mul_inv_cancel, map_one] at h3
  exact h3

private theorem re_eps {l : ℕ} [Fact l.Prime] (c : Coef l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (ε : H →* ℤ_[l]ˣ) (hε : Continuous ε) :
    IsOpen (((Units.map ((algebraMap c.O (ResidueField c.O)).comp (algebraMap ℤ_[l] c.O)).toMonoidHom).comp ε).ker : Set H) := by
  haveI : FaithfulSMul ℤ_[l] c.O := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    have h1 : algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℤ_[l] (PadicAlgCl l) y := congrArg Subtype.val hxy
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l], IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] _ y] at h1
    exact Subtype.ext ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h1)
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := inferInstance
  have hc : Continuous fun g => ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ := by fun_prop
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
    (Filter.mem_of_superset ((isOpen_lt hc continuous_const (g := fun _ => 1)).mem_nhds (by simp)) fun g hg => ?_)
  have h1 : ((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := PadicInt.mem_nonunits.2 hg
  have h2 := (residue_eq_zero_iff _).2 (map_nonunit (algebraMap ℤ_[l] c.O) _ h1)
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h2
  exact Units.ext h2

theorem UpperTheory.V.Hi.resEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ r : Resid V.frame c.O n, ∃ a, IsRes Q r τ₀ a := by
  intro hN l _ L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ r
  have H1 : ∀ w : (hset Q τ₀).Wp, ∃ b : Fin n → c.O, ∀ (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 →
      IsFrob B (normV w.1) σ → r.Dbar.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) =
      heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (b ⟨j - 1, h.2⟩) else 1 := by
    rintro ⟨w, hw, -⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun hl => hw (V.sub (Or.inl (by
      change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
      rwa [map_natCast])))
    have hq : ((normV w : ℕ) : ResidueField c.O) ≠ 0 := by
      have h1 := (cycZ L Ω l φ).isUnit.map ((residue c.O).comp (algebraMap ℤ_[l] c.O))
      rw [cycZ_of_isFrob hl hA hφ, map_natCast] at h1
      exact h1.ne_zero
    have hI : ∀ B, IsPlaceOver B w → ∀ t ∈ Ine (F := L) B, V.pr t = 1 := fun B hB t ht => by
      refine Subtype.ext ((QuotientGroup.eq_one_iff _).2 ?_)
      refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
      simp only [Set.mem_iUnion]
      refine ⟨w.under (𝓞 (Lp L)), hw, B, fun x => ?_, ht.1, ht.2⟩
      rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
      exact hB (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
    obtain ⟨b, hb⟩ := re_hecke (n := n) hq (∏ i, (X - C (r.chib i (V.pr φ⁻¹) : ResidueField c.O)))
      (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _)
      (by rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp)
    choose b' hb' using fun i => residue_surjective (b i)
    refine ⟨b', fun B σ hB hσ => ?_⟩
    simp only [hb']
    rw [← hb]
    refine (re_chi r.chib (V.pr σ⁻¹)).trans (Finset.prod_congr rfl fun i _ => ?_)
    have := re_frob ((r.chib i).comp V.pr) (fun B hB t ht =>
      (congrArg (r.chib i) (hI B hB t ht)).trans (map_one _)) hA hB hφ hσ
    rw [← inv_inj, ← map_inv, ← map_inv] at this
    exact congrArg (fun u : (ResidueField c.O)ˣ => X - C (u : ResidueField c.O)) this
  have H2 : ∀ (v : V.frame.Vl) (j : Fin n), ∃ b : c.O, ∀ (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)),
      (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
      ((∏ i with i ≤ j, r.psib v i g * (hset Q τ₀).epsV (ResidueField c.O) v g ^ (i : ℕ) : (ResidueField c.O)ˣ) :
        ResidueField c.O) = residue c.O b := by
    intro v j
    have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := Classical.epsilon_spec (UpperTheory.V.Loc.localArtinReciprocity hN (s.hw v.1))
    obtain ⟨y, hy⟩ := ha.surj (unif _)
    obtain ⟨b, hb⟩ := residue_surjective (R := c.O) ((∏ i with i ≤ j,
      r.psib v i (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) *
      (hset Q τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) ^ (i : ℕ) :
        (ResidueField c.O)ˣ) : ResidueField c.O)
    refine ⟨b, fun x g hg hx => ?_⟩
    obtain rfl : g = Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) x := Subtype.ext hg
    rw [hb]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have e1 := re_art ha (r.psib v i) (r.psib_open v i) (hx.trans hy.symm)
    have e2 := re_art ha ((hset Q τ₀).epsV (ResidueField c.O) v)
      (re_eps c ((cycZ L Ω l).comp (Dec (F := L) (s.A v.1)).subtype)
        ((continuous_cycZ L Ω l).comp continuous_subtype_val)) (hx.trans hy.symm)
    exact congrArg₂ (fun u t : (ResidueField c.O)ˣ => u * t ^ (i : ℕ)) e1 e2
  choose b1 hb1 using H1
  choose b2 hb2 using H2
  exact ⟨Sum.elim (fun x => b1 x.1 x.2) (fun x => b2 x.1 x.2), ⟨hb1, hb2⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem spec_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem spec_int {l : ℕ} [Fact l.Prime] (c : Coef l) (ι : Qbar l ≃+* ℂ) [Algebra c.O ℂ]
    (h : ∀ a : c.O, algebraMap c.O ℂ a = ι a) (μ : ℂ) : IsIntegral c.O μ ↔ ‖ι.symm μ‖ ≤ 1 := by
  let e : Qbar l →ₐ[c.O] ℂ := { ι.toRingHom with commutes' := fun a => (h a).symm }
  have h1 : IsIntegral c.O (e (ι.symm μ)) ↔ IsIntegral c.O (ι.symm μ) := isIntegral_algHom_iff e ι.injective
  have h2 : e (ι.symm μ) = μ := ι.apply_symm_apply μ
  rw [h2] at h1
  rw [h1, ← spec_intIff]
  exact ⟨fun h => isIntegral_trans _ h, fun h => h.tower_top⟩

private theorem spec_unit {l : ℕ} [Fact l.Prime] (c : Coef l) (ι : Qbar l ≃+* ℂ) [Algebra c.O ℂ]
    (h : ∀ a : c.O, algebraMap c.O ℂ a = ι a) (μ : ℂ) : IsIntUnit c.O μ ↔ ‖ι.symm μ‖ = 1 := by
  rw [IsIntUnit, spec_int c ι h, spec_int c ι h, map_inv₀, norm_inv]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have h3 : 0 < ‖ι.symm μ‖ := norm_pos_iff.2 ((map_ne_zero ι.symm).2 h0)
    exact le_antisymm h1 ((inv_le_one₀ h3).1 h2)
  · intro h1
    refine ⟨fun h0 => ?_, h1.le, by rw [h1, inv_one]⟩
    rw [h0, map_zero, norm_zero] at h1
    exact zero_ne_one h1

private theorem spec_chi {G : Type} [Group G] {I : Iwa G} {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω]
    (hinj : Function.Injective (algebraMap O Ω)) (R : WtRep I O Ω) :
    ∃ ψ : I.T →* Oˣ, ∀ t : I.T, algebraMap O Ω (ψ t) = R.χ ⟨t, I.T_le t.2⟩ := by
  have h : ∀ t : I.T, ∃ a : O, algebraMap O Ω a = R.χ ⟨t, I.T_le t.2⟩ := fun t => by
    have h1 := R.integral_torusCharacter t t.2 0 0
    have h2 := R.torusAction ⟨t, I.T_le t.2⟩ 0
    rw [if_pos rfl] at h2
    rw [← h2]
    exact h1
  choose a ha using h
  let f : I.T →* O :=
    { toFun := a
      map_one' := hinj (by rw [ha, map_one]; exact congrArg Units.val (map_one R.χ))
      map_mul' := fun s t => hinj (by
        rw [map_mul, ha, ha, ha, ← Units.val_mul, ← map_mul]
        rfl) }
  exact ⟨f.toHomUnits, ha⟩

private theorem spec_cl {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
    (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (e : ℕ) (φ : H.X.I.T →* ℂˣ)
    (hφ : ∀ v i y, (φ (eV n H.Sl v i y) : ℂ) = ι (H.finPart θ x lam v i y)) :
    H.ClAt θ ι x lam ξ K e = H.X.Cl (H.τC ι) ξ (H.lev K) e φ := by
  ext F
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, -⟩, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨h1, h2⟩, h3, h4, ?_⟩
    let M : Submonoid H.X.I.T :=
      { carrier := {t | H.X.rpF ℂ d H.m t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          have ha' : H.X.rpF ℂ d H.m a F = (((φ a)⁻¹ : ℂˣ) : ℂ) • F := ha
          have hb' : H.X.rpF ℂ d H.m b F = (((φ b)⁻¹ : ℂˣ) : ℂ) • F := hb
          change H.X.rpF ℂ d H.m ((a : GV n H.Sl) * b) F = (((φ (a * b))⁻¹ : ℂˣ) : ℂ) • F
          rw [map_mul, Module.End.mul_apply, hb', map_smul, ha', smul_smul, map_mul, mul_inv_rev, Units.val_mul] }
    refine Sp.torus_mem_submonoid_of_elementaryTorus H.Sl M fun v i y => ?_
    have h6 : F ∈ ⨅ (v) (i) (y), Module.End.eigenspace (H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T))
      (ι (H.finPart θ x lam v i y))⁻¹ := h5
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at h6
    change H.X.rpF ℂ d H.m _ F = _
    rw [Units.val_inv_eq_inv_val, hφ]
    exact h6 v i y
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    refine ⟨⟨⟨⟨⟨h1, fun u hu => h2 u (Subgroup.mem_sup_left hu)⟩, h2⟩, h3⟩, h4⟩, ?_⟩
    change F ∈ ⨅ (v) (i) (y), Module.End.eigenspace (H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T))
      (ι (H.finPart θ x lam v i y))⁻¹
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro v i y
    rw [← hφ, ← Units.val_inv_eq_inv_val]
    exact h5 _

attribute [local instance 2000] UpperTheory.V.W.coefLocal

theorem UpperTheory.V.Hi.spec :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n), H.Arith θ x.toRingHom lam → ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam ⟨e0, he0⟩
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨⟨c1, -, hx1⟩, a, ha1, -, ha⟩ := (GradeZeroInterpolatingElement.coPt c A).1 x
  obtain ⟨c', hc', hR⟩ := wtRep L l n H.V H.Sl ι lam c1
  letI : Algebra c'.O ℂ := (ι.toRingHom.comp (algebraMap c'.O (Qbar l))).toAlgebra
  have hal : ∀ a : c'.O, algebraMap c'.O ℂ a = ι a := fun _ => rfl
  obtain ⟨R, hR, hχ⟩ : ∃ R : WtRep H.X.I c'.O ℂ, IsAlgWt (S := H.Sl) ι lam R.ξ ∧ _ := hR
  haveI : IsCNL c'.O := { complete := (abelian₂.dvr_finite l c'.O).1, finite := (abelian₂.dvr_finite l c'.O).2.1 }
  let y : A →+* c'.O := x.toRingHom.codRestrict c'.O fun b => hc' (hx1 b)
  letI : Algebra A c'.O := y.toAlgebra
  letI : Algebra A ℂ := (ι.toRingHom.comp x.toRingHom).toAlgebra
  haveI : IsScalarTower A c'.O ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap c'.O ℂ) := ι.injective.comp Subtype.val_injective
  haveI : IsLocalHom (algebraMap A c'.O) := ⟨fun b hu => by
    by_contra hb
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : x b * (w : PadicAlgCl l) = 1 := congrArg Subtype.val hw
    have h2 : ‖x b‖ ≤ a := by simpa using ha 1 b (by rwa [pow_one])
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have h4 := mul_le_of_le_one_right (norm_nonneg (x b))
      ((spec_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) w).map c'.O.val) : ‖(w : PadicAlgCl l)‖ ≤ 1)
    linarith⟩
  obtain ⟨ψ, hψ⟩ := spec_chi hinj R
  let φ : H.X.I.T →* c'.Oˣ := (Units.map y.toMonoidHom).comp θ / ψ
  have hφχ : ∀ t : H.X.I.T, algebraMap A ℂ (θ t) = algebraMap c'.O ℂ (φ t) * R.χ ⟨t, H.X.I.T_le t.2⟩ := fun t => by
    rw [← hψ, ← map_mul, ← Units.val_mul]
    simp only [φ, MonoidHom.div_apply, div_mul_cancel]
    rfl
  have hφe : ∀ v i z, algebraMap c'.O ℂ (φ (eV n H.Sl v i z)) = ι (H.finPart θ x.toRingHom lam v i z) := fun v i z => by
    rw [HSet.finPart, map_div₀, ← Sp.chi_eV H.Sl ι lam R.χ hχ]
    exact (eq_div_iff (Units.ne_zero _)).2 (hφχ _).symm
  have htriv : ∀ v i (z : Uo ((H.Sl v).adicCompletion L)), (z : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (max e0 R.c0 + 1) →
      H.finPart θ x.toRingHom lam v i z = 1 := fun v i z hz =>
    he0 v i z (Sp.Uc_anti _ ((le_max_left _ _).trans (Nat.le_succ _)) hz)
  have hφ1 : ∀ t : H.X.I.T, (t : GV n H.Sl) ∈ H.X.I.Tc (max e0 R.c0) → φ t = 1 :=
    Sp.gen_Tc H.Sl (MonoidHom.mker φ) _ fun v i z hz => Units.ext (hinj ((hφe v i z).trans (by
      rw [htriv v i z hz]; simp)))
  have hτ : H.τC ι = (Matrix.GeneralLinearGroup.map (algebraMap A ℂ)).comp (H.τA A) := by
    ext u i j
    exact congrArg ι (x.commutes _).symm
  obtain ⟨h1, sp, h2, h3, h4, h5, h6, h7⟩ := Sp.absSpec H.X hinj R (H.τA A) θ hθ.cont φ (max e0 R.c0) (le_max_right _ _) hφ1 hφχ
    H.lev (Sp.lev_dir H) hH.fin hθ.free (H.τC ι) hτ _ rfl
  have hcl := fun K e => spec_cl H θ ι x.toRingHom lam R.ξ K e ((Units.map (algebraMap c'.O ℂ).toMonoidHom).comp φ) hφe
  have hlow : ∀ v j, (R.χ ⟨alV n H.Sl v j, H.X.I.P_le _ (Sp.alV_mem H.Sl v j)⟩ : ℂ) = H.lowVal ι lam v j :=
    Sp.chi_alV H.Sl ι lam R.χ hχ
  have hU : ∀ v (j : Fin n), H.opC ι lam (R.d + 1) (.inr (v, j)) = H.X.UF H.m R ⟨_, Sp.alV_mem H.Sl v (j + 1)⟩ := fun v j => by
    rw [Frame.UF, Units.val_inv_eq_inv_val, hlow]
    rfl
  have hz : H.uzC ι lam (R.d + 1) = H.X.UF H.m R ⟨_, H.X.I.z_mem⟩ := by
    have := congrArg Units.val (Sp.weightChar_central_eq_prod_uniformizerDiag H.Sl R.χ)
    rw [Units.coe_prod] at this
    simp only [Units.coe_prod] at this
    rw [Frame.UF, Units.val_inv_eq_inv_val, HSet.uzC]
    congr 2
    exact (this.trans (Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => hlow v j)).symm
  refine ⟨R.d + 1, R.ξ, max e0 R.c0, sp, hR, htriv, fun K e he => ?_, fun K e he i F hF => ?_,
    fun K e he i F hF h0 μ hμ => ?_, h2, h3, fun K e he => ?_, h5, fun K i f hf => ?_, fun K K' q g f hf _ => ?_⟩
  · rw [hcl]
    exact (h1 K e he).1
  · rw [hcl] at hF ⊢
    rcases i with ⟨w, j⟩ | ⟨v, j⟩
    · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w.1 (j + 1)
      obtain ⟨e1, e2⟩ := hu ℂ _ (H.X.raF (R.d + 1) (H.τC ι))
      have e3 : H.opC ι lam (R.d + 1) (.inl (w, j)) = _ := e1
      rw [e3]
      exact Sp.sum_cl H.X R _ _ e _ _ u F hF (e2 hH w.2 K F hF.1.2)
    · rw [hU]
      exact ((h1 K e he).2.1 _).1 F hF
  · rw [hcl] at hF
    rw [← spec_int c' ι hal]
    rcases i with ⟨w, j⟩ | ⟨v, j⟩
    · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w.1 (j + 1)
      have e3 : H.opC ι lam (R.d + 1) (.inl (w, j)) = _ := (hu ℂ _ (H.X.raF (R.d + 1) (H.τC ι))).1
      rw [e3] at hμ
      exact (h1 K e he).2.2 κ u F hF h0 μ hμ
    · rw [hU] at hμ
      exact ((h1 K e he).2.1 _).2 F hF h0 μ hμ
  · rw [h4 K e he, HSet.OrdAt, hcl, hz]
    refine le_antisymm (iSup_le fun μ => ?_) (iSup_le fun μ => ?_)
    · exact le_iSup_of_le ⟨μ.1, (spec_unit c' ι hal _).1 μ.2⟩ le_rfl
    · exact le_iSup_of_le ⟨μ.1, (spec_unit c' ι hal _).2 μ.2⟩ le_rfl
  · rcases i with ⟨w, j⟩ | ⟨v, j⟩
    · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w.1 (j + 1)
      obtain ⟨e1, e2⟩ := hu ℂ _ (H.X.raF (R.d + 1) (H.τC ι))
      have e3 : H.opC ι lam (R.d + 1) (.inl (w, j)) = _ := e1
      have e4 : H.op A (.inl (w, j)) = _ := (hu A _ (H.X.ra (H.τA A))).1
      rw [e3, e4]
      exact h7 K K κ u (e2 hH w.2 K) f hf
    · rw [hU]
      exact h6 K ⟨_, Sp.alV_mem H.Sl v (j + 1)⟩ f hf
  · obtain ⟨K'', hK⟩ := Sp.lev_act H hH K q g
    have := h7 K K'' Unit (fun _ => H.sec (H.wq q) g) (fun F hF => by
      rw [Fintype.sum_unique]
      exact hK ℂ _ _ F hF) f hf
    rw [Fintype.sum_unique, Fintype.sum_unique] at this
    exact this
end

