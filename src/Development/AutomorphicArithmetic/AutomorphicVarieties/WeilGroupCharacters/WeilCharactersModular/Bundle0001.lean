module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AbStruct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiGS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UniversalDeformationRingNonemptyOfNonemptyPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LamEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

theorem UpperTheory.V.W.lamEx :
    LocCFTAll → LamEx := by
  intro h l hl L Ω _ _ _ _ _ _ s V c n r
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField ℤ_[l]) l :=
    charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom)
      (PadicInt.residueField (p := l)).symm.injective l
  haveI : CharP (ResidueField c.O) l :=
    charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l
  obtain ⟨d₀, hd, hA⟩ := h l L Ω s
  let d : V.frame.Vl → ℕ := d₀
  obtain ⟨⟨Λ⟩, hΛ⟩ := lam_ex_free l V.frame c.O n r d fun v => (hA v).some
  obtain ⟨e, -⟩ := hΛ Λ
  have hsum : ∑ v : V.frame.Vl, d v = Module.finrank ℚ (Lp L) :=
    (finsum_eq_sum_of_fintype (α := V.frame.Vl) d).symm.trans hd
  have hc : Fintype.card (Σ v : V.frame.Vl, Fin n × Fin (d v)) = n * Module.finrank ℚ (Lp L) := by
    rw [Fintype.card_sigma, ← hsum, Finset.mul_sum]
    simp
  exact ⟨Λ, ⟨e.symm.trans (MvPowerSeries.renameEquiv c.O (Fintype.equivFinOfCardEq hc))⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LocCFT
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

private theorem lc_sum (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] :
    ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, ReciprocityTheory.Gal.locDeg v.1 = Module.finrank ℚ F := by
  classical
  have hl : l.Prime := Fact.out
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  have h0 : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ)}) (𝓞 F)
  rw [RingOfIntegers.rank] at hsum
  have hover : ∀ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal},
      v.1.asIdeal ∈ (Ideal.span {(l : ℤ)}).primesOver (𝓞 F) := fun v => by
    refine ⟨v.1.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.1.isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using v.2
  let e : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} → (Ideal.span {(l : ℤ)}).primesOver (𝓞 F) :=
    fun v => ⟨v.1.asIdeal, hover v⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)), fun q => ?_⟩
    obtain ⟨q, h1, h2⟩ := q
    refine ⟨⟨⟨q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot h0 q⟩, ?_⟩, rfl⟩
    have : (l : ℤ) ∈ q.under ℤ := h2.over ▸ Ideal.mem_span_singleton_self _
    simpa using this
  rw [← hsum, ← finsum_eq_sum_of_fintype]
  exact finsum_eq_of_bijective e he fun _ => rfl

private theorem lc_ab {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ) (I : Subgroup G)
    (hI : ∀ g, φ g ∈ Loc.Iq l ↔ g ∈ I) : Nonempty (LocAb l G I φ.range.index) := by
  obtain ⟨-, -, π, a, m, hπ, ha, hm, hmu, hIa, hsa, hIs, hu⟩ := Loc.abStruct φ hφ
  let b : G →* Multiplicative ((Fin φ.range.index → ℤ_[l]) × ℤ_[l]) :=
    (MulEquiv.prodMultiplicative _ _).symm.toMonoidHom.comp (π.prod a)
  have hb : ∀ g x, b g = Multiplicative.ofAdd x ↔ π g = Multiplicative.ofAdd x.1 ∧ a g = Multiplicative.ofAdd x.2 :=
    fun g x => Prod.ext_iff
  refine ⟨⟨b, hπ.prodMk ha, fun x => ?_, fun x => ⟨?_, fun hx => ?_⟩, fun C _ _ hC χ hχ h1 g hg => ?_, m, hm,
    fun g hg => (hmu g hg).2.2⟩⟩
  · obtain ⟨g0, h0⟩ := hsa (Multiplicative.ofAdd x.toAdd.2)
    obtain ⟨g1, h1, h2, -⟩ := hIs (Multiplicative.ofAdd x.toAdd.1 * (π g0)⁻¹) 1
    refine ⟨g1 * g0, (hb _ x.toAdd).2 ⟨?_, ?_⟩⟩
    · rw [map_mul, h2, inv_mul_cancel_right]
    · rw [map_mul, hIa g1 h1, one_mul, h0]
  · rintro ⟨g, hg, h⟩
    have := ((hb g x).1 h).2
    rw [hIa g ((hI g).2 hg)] at this
    exact this.symm
  · obtain ⟨g, h1, h2, -⟩ := hIs (Multiplicative.ofAdd x.1) 1
    exact ⟨g, (hI g).1 h1, (hb g x).2 ⟨h2, by rw [hIa g h1, hx]; rfl⟩⟩
  · obtain ⟨hg1, hg2⟩ := (hb g 0).1 hg
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective _ (m g : TopologicalAbelianization G)
    have hmem : h ∈ muG l G := by
      refine Subgroup.mem_comap.2 ?_
      rw [hh]; exact (m g).2
    obtain ⟨p1, p2, p3⟩ := hmu h hmem
    have hmh : m h = m g := Subtype.ext (p3.trans hh)
    have := hu C hC χ hχ (g * h⁻¹) (by rw [map_mul, map_inv, p1, hg1]; simp) (by rw [map_mul, map_inv, p2, hg2]; simp)
      (by rw [map_mul, map_inv, hmh, mul_inv_cancel])
    have h3 : χ h = 1 := h1 hmem
    rw [map_mul, map_inv, h3, inv_one, mul_one] at this
    exact this

theorem UpperTheory.V.W.locCFT :
    GlobalTheory.Published.GlobalArtinReciprocity → Pa.CohP → LocCFTAll := by
  intro _ _ l _ L Ω _ _ _ _ _ _ s
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  refine ⟨fun v => ReciprocityTheory.Gal.locDeg v.1, lc_sum l (Lp L), fun v => ?_⟩
  obtain ⟨v, hv⟩ := v
  have hA := s.hA v
  have hsp := s.split v (Or.inl hv)
  change Nonempty (LocAb l (Dec (F := L) (s.A v)) ((Ine (F := L) (s.A v)).subgroupOf (Dec (F := L) (s.A v)))
    (ReciprocityTheory.Gal.locDeg v))
  generalize s.A v = A at hA hsp
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).1 A v hA hv
  obtain ⟨-, φ', -, a2, a3, -, -, a6⟩ := (Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, φ, b1, -, b3, b4, -, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  have hr : φ'.range = φ.range := by
    ext σ
    refine ⟨?_, fun h => (a3 σ).2 fun x => ?_⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g', hg'⟩ := hsp g.2
      refine (b3 _).2 fun x => ?_
      rw [a2, ← hg']
      exact congrArg j (g'.commutes x)
    · rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
      exact (b3 σ).1 h _
  rw [← a6 v hA, hr]
  exact lc_ab φ b1 _ fun g => (b4 g).trans Subgroup.mem_subgroupOf.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.PhiAll
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

theorem UpperTheory.V.W.phiAll :
    Pa.CohP → PhiAll := by
  intro hP l _ L Ω _ _ _ _ _ _ s V
  have h := Pa.phiGS hP.gf l L Ω s V
  exact ⟨h, Pa.Det.phiSub l V.frame.η.ker V.frame.η_open h,
    fun v => Pa.phiDec hP.lf l L Ω (s.A v.1) (s.w v.1) (s.hw v.1)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ProModularRingExists
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

theorem UpperTheory.V.W.b0Ex :
    PhiAll → ProModularRingExists := by
  intro h l hl L Ω _ _ _ _ _ _ s V c n r R _ _ _ hp
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField ℤ_[l]) l :=
    charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom)
      (PadicInt.residueField (p := l)).symm.injective l
  haveI : CharP (ResidueField c.O) l :=
    charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l
  obtain ⟨-, h0, hv⟩ := h l L Ω s V
  exact UpperTheory.V.CA.universalDeformationRing_nonempty_of_nonempty_pair r h0 hv ⟨R, _, _, inferInstance, hp⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.SgnEqOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

open Classical in
private noncomputable def sgn {Γ : Type} [Group Γ] (H : Subgroup Γ) (h : H.index = 2) : Γ →* ℤˣ :=
  MonoidHom.mk' (fun g => if g ∈ H then 1 else -1) fun a b => by
    simp only [Subgroup.mul_mem_iff_of_index_two h]
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ha, hb]

theorem UpperTheory.V.W.levEx :
    LevEx := by
  intro l _ L Ω _ _ _ _ _ _ s S' hfin hsub hsplit
  have key : ∀ σ : G (Lp L) Ω, σ ∈ (resP L Ω).range ↔
      ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x := by
    intro σ
    constructor
    · rintro ⟨τ, rfl⟩ x
      exact τ.commutes x
    · intro h
      exact ⟨{ σ with commutes' := h }, AlgEquiv.ext fun _ => rfl⟩
  have hrange : (resP L Ω).range = (AlgEquiv.restrictNormalHom (F := Lp L) (K₁ := Ω) L).ker := by
    ext σ
    rw [key, MonoidHom.mem_ker]
    change _ ↔ σ.restrictNormal L = 1
    constructor
    · intro h
      refine AlgEquiv.ext fun x => (algebraMap L Ω).injective ?_
      rw [AlgEquiv.restrictNormal_commutes, h x, AlgEquiv.one_apply]
    · intro h x
      rw [← AlgEquiv.restrictNormal_commutes σ L x, h, AlgEquiv.one_apply]
  have hidx : (resP L Ω).range.index = 2 := by
    rw [hrange, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (F := Lp L) (K₁ := L) Ω),
      Subgroup.card_top, IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hc : s.c ∉ (resP L Ω).range := by
    intro hm
    obtain ⟨j, hj⟩ := s.hc
    apply IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap L Ω))
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hj, (key _).1 hm x]
  have hsg : ∀ g, sgn _ hidx g = 1 ↔ g ∈ (resP L Ω).range := by
    intro g
    simp only [sgn, MonoidHom.mk'_apply]
    split_ifs with h
    · simp [h]
    · simp only [h, iff_false]
      decide
  have hclosed : IsClosed ((resP L Ω).range : Set (G (Lp L) Ω)) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range UpperTheory.V.W.continuous_resP).isClosed
  have hnorm : (resP L Ω).range.Normal := by
    rw [hrange]
    infer_instance
  have hNS : NS Ω S' ≤ (resP L Ω).range := by
    apply Subgroup.topologicalClosure_minimal _ _ hclosed
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    exact s.unr A v hA hσA
  have hcycClosed : IsClosed ((cycZ (Lp L) Ω l).ker : Set (G (Lp L) Ω)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_cycZ (Lp L) Ω l)
  have hNS2 : NS Ω S' ≤ (cycZ (Lp L) Ω l).ker := by
    apply Subgroup.topologicalClosure_minimal _ _ hcycClosed
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    have hl : ((l : 𝓞 (Lp L))) ∉ v.asIdeal := fun h => hv (hsub (Or.inl h))
    exact GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hA hl hσA
  have hNSη : NS Ω S' ≤ (sgn _ hidx).ker := fun σ hσ => (hsg σ).2 (hNS hσ)
  let η : GS Ω S' →* ℤˣ := QuotientGroup.lift (NS Ω S') (sgn _ hidx) hNSη
  let ε : GS Ω S' →* ℤ_[l]ˣ := QuotientGroup.lift (NS Ω S') (cycZ (Lp L) Ω l) hNS2
  have hηg : ∀ g, η (toGS Ω S' g) = sgn _ hidx g := fun g => QuotientGroup.lift_mk _ hNSη g
  have hpre : (QuotientGroup.mk ⁻¹' (η.ker : Set (GS Ω S')) : Set (G (Lp L) Ω)) =
      ((resP L Ω).range : Set (G (Lp L) Ω)) := by
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker]
    rw [← hsg g]
    exact Iff.rfl
  haveI : (resP L Ω).range.FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  refine ⟨⟨S', hfin, hsub, hsplit, η, ?_, ?_, ?_, ε, ?_, ?_⟩, rfl⟩
  · intro g
    rw [hηg, hsg]
  · rw [← (QuotientGroup.isQuotientMap_mk (NS Ω S')).isOpen_preimage, hpre]
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ hclosed
  · rw [hηg]
    simp only [sgn, MonoidHom.mk'_apply, if_neg hc]
  · exact MonoidHom.ext fun g => QuotientGroup.lift_mk _ hNS2 g
  · exact (QuotientGroup.isQuotientMap_mk (NS Ω S')).continuous_iff.mpr
      (by exact continuous_cycZ (Lp L) Ω l)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ToZModOneIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

private theorem toZMod_one_iff {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    PadicInt.toZMod x = 1 ↔ PadicInt.toZModPow 1 x = 1 := by
  rw [← map_one (PadicInt.toZMod (p := l)), ← map_one (PadicInt.toZModPow (p := l) 1), ← RingHom.sub_mem_ker_iff,
    ← RingHom.sub_mem_ker_iff, PadicInt.ker_toZMod, PadicInt.ker_toZModPow, PadicInt.maximalIdeal_eq_span_p, pow_one]

private theorem fix_iff {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] {ζ : Ω} (hζ : IsPrimitiveRoot ζ l) (x : ℤ_[l]) :
    ζ ^ (PadicInt.toZModPow 1 x).val = ζ ↔ PadicInt.toZMod x = 1 := by
  have h1 : 1 < l ^ 1 := by simpa using (Fact.out : l.Prime).one_lt
  haveI : Fact (1 < l ^ 1) := ⟨h1⟩
  haveI : NeZero (l ^ 1) := ⟨by omega⟩
  rw [toZMod_one_iff]
  constructor
  · intro h
    apply ZMod.val_injective
    rw [ZMod.val_one]
    refine hζ.pow_inj ?_ (Fact.out : l.Prime).one_lt (by rw [h, pow_one])
    simpa using ZMod.val_lt (PadicInt.toZModPow 1 x)
  · intro h
    rw [h, ZMod.val_one, pow_one]

theorem UpperTheory.V.W.muL :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev), (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) ↔ ∃ g : V.frame.G₀, PadicInt.toZMod ((V.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1 := by
  intro l _ L Ω _ _ _ _ _ _ s V
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have : IsGalois L Ω := ⟨⟩
  have hε : ∀ σ : G L Ω, V.ε (V.pr σ).1 = cycZ (Lp L) Ω l (resP L Ω σ) := fun σ =>
    DFunLike.congr_fun V.hε (resP L Ω σ)
  have key : ∀ (σ : G L Ω) (ζ : Ω), IsPrimitiveRoot ζ l →
      (σ ζ = ζ ↔ PadicInt.toZMod ((V.ε (V.pr σ).1 : ℤ_[l]ˣ) : ℤ_[l]) = 1) := fun σ ζ hζ => by
    have h : σ ζ = ζ ^ (PadicInt.toZModPow 1 ((cycZ (Lp L) Ω l (resP L Ω σ) : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (Ω ≃ₐ[Lp L] Ω) Ω (resP L Ω σ)) ζ
        (by rw [pow_one, hζ.pow_eq_one])
    rw [hε, h, fix_iff hζ]
  have hsurj : ∀ g : V.η.ker, ∃ σ : G L Ω, V.pr σ = g := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  change _ ↔ ∃ g : V.η.ker, PadicInt.toZMod ((V.ε g.1 : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1
  constructor
  · intro hn
    by_contra hc
    push Not at hc
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
    have hm : ζ ∈ (⊥ : IntermediateField L Ω) := by
      rw [InfiniteGalois.mem_bot_iff_fixed]
      exact fun σ => (key σ ζ hζ).2 (hc _)
    obtain ⟨z, rfl⟩ := IntermediateField.mem_bot.1 hm
    exact hn ⟨z, hζ.of_map_of_injective (algebraMap L Ω).injective⟩
  · rintro ⟨g, hg⟩ ⟨z, hz⟩
    obtain ⟨σ, rfl⟩ := hsurj g
    exact hg ((key σ _ (hz.map_of_injective (algebraMap L Ω).injective)).1 (σ.commutes z))
end

