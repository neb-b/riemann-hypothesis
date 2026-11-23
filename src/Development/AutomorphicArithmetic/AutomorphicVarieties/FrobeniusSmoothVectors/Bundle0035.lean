module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002
public import ReciprocityTheory.GaloisValuations.ArithOfA

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HthPlace
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem hth_place (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring
    (Ideal.span {(⟨(p : Ω), natCast_mem _ p⟩ : (⊥ : Subring Ω))}) (by
      intro h
      rw [Ideal.span_singleton_eq_top] at h
      obtain ⟨⟨b, hb⟩, hb1⟩ := isUnit_iff_exists_inv.mp h
      obtain ⟨n, rfl⟩ := Subring.mem_bot.mp hb
      have h0 : ((p : Ω) * (n : Ω)) = 1 := congrArg Subtype.val hb1
      have h1 : ((p : ℤ) * n : ℤ) = 1 := by exact_mod_cast h0
      have h2 : (p : ℤ) ∣ 1 := ⟨n, h1.symm⟩
      have h3 : p ∣ 1 := by exact_mod_cast h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3))
  exact ⟨B, B.mem_nonunits_iff.mp (hB ⟨_, Ideal.subset_span rfl, rfl⟩)⟩

private theorem hth_spec (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (w : ℕ) [hw : Fact w.Prime]
    (s : G ℚ Ω) (ζ : Ω) (h : ζ ^ w = 1) : s ζ = ζ ^ ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have h1 : ζ ^ w ^ 1 = 1 := by rwa [pow_one]
  exact cyclotomicCharacter.spec (L := Ω) w (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ h1

private theorem hth_iff (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (w : ℕ) [hw : Fact w.Prime] (s : G ℚ Ω) :
    (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a ^ l) ↔
      cycMod ℚ Ω w 1 s ∈ (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero w := ⟨hw.out.ne_zero⟩
  have hred : ∀ (ζ : Ω) (m : ℕ), ζ ^ w = 1 → ζ ^ m = ζ ^ (m % w) := by
    intro ζ m hζ
    conv_lhs => rw [← Nat.mod_add_div m w, pow_add, pow_mul, hζ, one_pow, mul_one]
  have hcv : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val < w :=
    lt_of_lt_of_eq (ZMod.val_lt _) (pow_one w)
  have hl0 : l ≠ 0 := hl.out.ne_zero
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω w
    have e1 := ha ζ0 hζ0.pow_eq_one
    rw [hth_spec Ω w s ζ0 hζ0.pow_eq_one, hred ζ0 (a ^ l) hζ0.pow_eq_one] at e1
    have e2 : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val = a ^ l % w :=
      hζ0.pow_inj hcv (Nat.mod_lt _ (Nat.pos_of_neZero w)) e1
    have e3 : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)) = (a : ZMod (w ^ 1)) ^ l := by
      apply ZMod.val_injective
      rw [e2, ← Nat.cast_pow, ZMod.val_natCast, pow_one]
    have hu : IsUnit (a : ZMod (w ^ 1)) := (isUnit_pow_iff hl0).mp (e3 ▸ (cycMod ℚ Ω w 1 s).isUnit)
    exact ⟨hu.unit, Units.ext (by simp [e3])⟩
  · rintro ⟨u, hu⟩
    refine ⟨(u : ZMod (w ^ 1)).val, fun ζ hζ => ?_⟩
    have e : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)) =
        (((u : ZMod (w ^ 1)).val ^ l : ℕ) : ZMod (w ^ 1)) := by
      rw [← hu]
      simp
    rw [hth_spec Ω w s ζ hζ, hred ζ (((u : ZMod (w ^ 1)).val) ^ l) hζ, e, hred ζ _ hζ,
      ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_pow_self w one_ne_zero)]

theorem UpperTheory.V.Fr.hth :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → w ≡ 1 [MOD l] → IsOpen (Hth Ω l w : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ Hth Ω l w ∧ (Hth Ω l w).index = l ∧ (∀ B' : ValuationSubring Ω, ¬ B'.valuation (w : Ω) < 1 → Ine (F := ℚ) B' ≤ Hth Ω l w) ∧ ∀ B' : ValuationSubring Ω, B'.valuation (w : Ω) < 1 → ¬ Ine (F := ℚ) B' ≤ Hth Ω l w := by
  intro Ω _ _ _ l hl w hwp hw1
  haveI hw : Fact w.Prime := ⟨hwp⟩
  haveI : Fact (w ^ 1).Prime := ⟨by rw [pow_one]; exact hwp⟩
  have hmem : ∀ s : G ℚ Ω, s ∈ Hth Ω l w ↔
      cycMod ℚ Ω w 1 s ∈ (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range := by
    intro s
    change (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a ^ l) ∧
      (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s⁻¹ ζ = ζ ^ a ^ l) ↔ _
    rw [hth_iff Ω l w s, hth_iff Ω l w s⁻¹, map_inv, inv_mem_iff, and_self]
  have hker : (cycMod ℚ Ω w 1).ker ≤ Hth Ω l w := fun s hs =>
    (hmem s).mpr (by rw [MonoidHom.mem_ker.mp hs]; exact one_mem _)
  have hZ : ∀ s, cycMod ℚ Ω w 1 s = KStar.TotallyRealRoots.redPow w 1 (cycZ ℚ Ω w s) := fun s => rfl
  obtain ⟨A, hA⟩ := hth_place Ω w hwp
  have hsurj : Function.Surjective (cycMod ℚ Ω w 1) := by
    intro v
    obtain ⟨u, rfl⟩ := KStar.TotallyRealRoots.redPow_surjective (l := w) 1 v
    obtain ⟨σ, -, hσ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω w A hA u
    exact ⟨σ, by rw [hZ, hσ]⟩
  have hidx : (Hth Ω l w).index = l := by
    have hH : Hth Ω l w =
        (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range.comap (cycMod ℚ Ω w 1) := by
      ext s
      exact hmem s
    rw [hH, Subgroup.index_comap_of_surjective _ hsurj, IsCyclic.index_powMonoidHom_range,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hwp]
    exact Nat.gcd_eq_right ((Nat.modEq_iff_dvd' hwp.one_lt.le).mp hw1.symm)
  refine ⟨?_, ?_, hidx, ?_, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := (KStar.TotallyRealRoots.princ w 1).comap (cycZ ℚ Ω w)) ?_ ?_
    · intro s hs
      apply hker
      rw [MonoidHom.mem_ker, hZ]
      exact hs
    · exact (contTw ℚ Ω w).1.isOpen_preimage _ (KStar.TotallyRealRoots.isOpen_princ 1)
  · exact (Abelianization.commutator_subset_ker (cycMod ℚ Ω w 1)).trans hker
  · intro B' hB' s hs
    apply hker
    rw [MonoidHom.mem_ker, hZ, MonoidHom.mem_ker.mp ((places ℚ Ω w B').2.2.2 hB' hs), map_one]
  · intro B' hB' hle
    have htop : Hth Ω l w = ⊤ := by
      refine eq_top_iff.mpr fun s _ => ?_
      obtain ⟨u, hu⟩ := KStar.TotallyRealRoots.redPow_surjective (l := w) 1 (cycMod ℚ Ω w 1 s)
      obtain ⟨σ, hσI, hσ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω w B' hB' u
      have h1 := (hmem σ).mp (hle hσI)
      rw [hZ, hσ, hu] at h1
      exact (hmem s).mpr h1
    rw [htop, Subgroup.index_top] at hidx
    exact hl.out.one_lt.ne hidx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OkBasic
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

private theorem padic_hom_ext {l : ℕ} [Fact l.Prime] {k : Type} [CommRing k] [CharP k l] (f g : ℤ_[l] →+* k) : f = g := by
  ext x
  have h := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  have e : x = y * l + (x.zmodRepr : ℤ_[l]) := by rw [hy]; ring
  rw [e]
  simp

private theorem cc_sq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {c : G F Ω} {j : Ω →+* ℂ}
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) : c * c = 1 := by
  refine AlgEquiv.ext fun x => j.injective ?_
  rw [AlgEquiv.mul_apply, h, h, starRingEnd_self_apply]
  rfl

private theorem eta_cc {Ω : Type} [Field Ω] [CharZero Ω] {η : G ℚ Ω →* ℤˣ} {D : ℕ} {δ : Ω} (hD : 0 < D)
    (hδ : δ ^ 2 = -(D : Ω)) (hη : ∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) {c : G ℚ Ω} {j : Ω →+* ℂ}
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) : η c = -1 := by
  refine (Int.units_eq_one_or _).resolve_left fun h1 => ?_
  have h2 := h δ
  rw [hη, h1, Units.val_one, one_smul] at h2
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2.symm
  have h3 := congrArg j hδ
  rw [map_pow, map_neg, map_natCast, hr] at h3
  have h4 : r ^ 2 = -(D : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [sq_nonneg r]

private theorem smul_over {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} {B : ValuationSubring Ω} (γ : G ℚ Ω)
    (h : B.valuation (l : Ω) < 1) : (γ • B).valuation (l : Ω) < 1 := by
  rw [valuation_lt_one_iff'] at h ⊢
  simpa only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_natCast, map_inv₀] using h

private theorem cpt_gal (F Ω : Type) [Field F] [CharZero F] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra F Ω] :
    CompactSpace (G F Ω) := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois F Ω := IsGalois.tower_top_of_isGalois ℚ F Ω
  infer_instance

theorem UpperTheory.V.Fr.ok_basic :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O)), UFacts l η Ψ M m (upl Ω L) → Linked l η Ψ σ g₁ B M L Φ → barChar O Ψ g₁ ^ 2 ≠ 1 → IsOpen (Φ.del.ker : Set Φ.Γ) ∧ Φ.c * Φ.c = 1 ∧ Φ.del Φ.c = -1 ∧ (∀ v, Continuous (Φ.loc0 v)) ∧ Continuous Φ.eps ∧ IsOpen (Φ.Ψ.ker : Set Φ.Γ) ∧ Φ.Ψ Φ.c = 1 ∧ Φ.Ψ Φ.g0 ^ 2 ≠ 1 ∧ Fintype.card Φ.Inf = Φ.d ∧ (∀ w, Φ.cw w * Φ.cw w = 1) ∧ (∀ w, Φ.del (Φ.cw w) = -1) ∧ (∃ g : Φ.G0, Φ.om (ResidueField O) g ≠ 1) ∧ (∀ j : ℤ, j = 1 ∨ j = -1 → ∃ g : Φ.G0, Φ.om (ResidueField O) g * Φ.Ψ g ^ j ≠ 1) ∧ (∀ j : ℤ, j = 2 ∨ j = -2 → ∃ g, Φ.om (ResidueField O) g * Φ.Ψ g ^ j * Φ.delK (ResidueField O) g ≠ 1) ∧ (∀ v, ∃ g, Φ.Ψ (Φ.loc v g) ^ 2 ≠ 1) ∧ (¬ ∃ j : ℤ, ∀ g : Φ.G0, Φ.om (ResidueField O) g = Φ.Ψ g ^ j) ∧ (∀ v, ∀ g ∈ Φ.Nv v, Φ.Ψ (Φ.loc v g) = 1) ∧ (∀ v, l ^ m ≤ Φ.dv v) ∧ Nonempty Φ.V := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL hg₁
  obtain ⟨k, S, π, ι, pl, e, c, F, hπ, -⟩ := hL
  haveI : CompactSpace (G (W.Lp L) Ω) := cpt_gal _ _
  have hq : Topology.IsQuotientMap π := F.g.cont.isClosedMap.isQuotientMap F.g.cont F.g.onto
  have hom : ∀ s, Φ.om (ResidueField O) (k.p s) = omO Ω l O s := fun s => by
    apply Units.ext
    show (ZMod.castHom (dvd_refl l) (ResidueField O)).comp PadicInt.toZMod (Φ.eps (k.p s) : ℤ_[l]ˣ) =
      (ZMod.castHom (dvd_pow_self l one_ne_zero) (ResidueField O)).comp (PadicInt.toZModPow 1) (cycZ ℚ Ω l s : ℤ_[l]ˣ)
    rw [k.eps, padic_hom_ext ((ZMod.castHom (dvd_refl l) (ResidueField O)).comp PadicInt.toZMod)]
  have hpl : ∀ v, (k.pl v).valuation (l : Ω) < 1 := fun v => by
    obtain ⟨γ, -, h⟩ := k.pl_conj v
    exact h ▸ smul_over γ hG.over_l
  have h0 : ∀ s (h : s ∈ upl Ω L ⊓ η.ker), k.p ⟨s, h.1⟩ ∈ Φ.del.ker := fun s h => (k.del _).trans h.2
  have f5 : ¬ ∃ j : ℤ, ∀ g : Φ.G0, Φ.om (ResidueField O) g = Φ.Ψ g ^ j := by
    rintro ⟨j, hj⟩
    refine hU.f5 ⟨j, fun s hs => ?_⟩
    have := hj ⟨_, h0 s hs⟩
    rwa [hom, k.psi] at this
  obtain ⟨hσ, hc⟩ := k.c
  obtain ⟨hg, hg0⟩ := k.g0
  obtain ⟨D, δ, hD, -, hδ, hη⟩ := hG.quad
  refine ⟨F.del_open, ?_, F.del_c, fun v => ?_, ?_, ?_, ?_, ?_, ?_, fun w => ?_, fun w => ?_, ?_, fun j hj => ?_,
    fun j hj => ?_, fun v => ?_, f5, fun v g hg => ?_, fun v => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hG.cc
    rw [← hc, ← map_mul, ← map_one k.p]
    exact congrArg k.p (Subtype.ext (cc_sq hj))
  · refine continuous_induced_rng.2 ?_
    have : Subtype.val ∘ Φ.loc0 v = k.p ∘ k.j v := funext (k.j_loc v)
    exact this ▸ k.p_cont.comp (k.j_cont v)
  · refine hq.continuous_iff.2 ?_
    have : Φ.eps ∘ π = cycZ (W.Lp L) Ω l := funext F.eps
    exact this ▸ continuous_cycZ _ _ l
  · exact hq.isOpen_preimage.1 (Subgroup.isOpen_mono (H₂ := Φ.Ψ.ker.comap π) F.K_Ψ F.g.isOpen)
  · rw [← hc, k.psi]
    exact hG.even
  · rw [← hg0, k.psi]
    exact hg₁
  · classical
    haveI := F.real
    rw [Fintype.card_congr e, Frame.d, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, ← IsTotallyReal.finrank,
      ← sum_locDegree l (Finset.univ.image pl) fun v => by
        rw [← F.loc.mem, Finset.mem_image]; exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, Finset.mem_univ _, h⟩⟩,
      Finset.sum_image fun a _ b _ h => F.loc.inj h]
    exact Finset.sum_congr rfl fun v _ => (F.dv v).symm
  · obtain ⟨j, hj, -⟩ := F.cc w
    rw [F.cw, ← map_mul, cc_sq hj, map_one]
  · obtain ⟨j, hj, -⟩ := F.cc w
    rw [F.cw, hπ _ fun x hx => (c w).commutes ⟨x, hx⟩, k.del]
    exact eta_cc hD hδ hη hj
  · by_contra h
    exact f5 ⟨0, fun g => by_contra fun h' => h ⟨g, by simpa using h'⟩⟩
  · obtain ⟨s, hs, h⟩ := hU.f2b j hj
    exact ⟨⟨_, h0 s hs⟩, by rwa [hom, k.psi]⟩
  · obtain ⟨s, hs, h⟩ := hU.f2c j hj
    refine ⟨k.p ⟨s, hs.1⟩, ?_⟩
    rwa [hom, k.psi, Frame.delK, MonoidHom.comp_apply, MonoidHom.mem_ker.1 (h0 s hs), map_one, mul_one]
  · obtain ⟨s, hs, h⟩ := hU.f3 _ (hpl v)
    obtain ⟨g, hg⟩ := (k.j_range v ⟨s, hs.2⟩).2 hs.1
    exact ⟨g, by rwa [k.j_loc, k.psi, hg]⟩
  · obtain ⟨j, hj⟩ := hG.Ψ_l
    have h1 : Φ.eps (Φ.loc v g) = 1 := hg.2
    have h2 : Φ.om (ResidueField O) (Φ.loc v g) = 1 := by rw [Frame.om, MonoidHom.comp_apply, h1, map_one]
    rw [k.j_loc, hom] at h2
    rw [k.j_loc, k.psi, hj _ (hpl v) _ ((k.j_ine v g).1 hg.1), h2, one_pow]
  · exact k.dv v ▸ hU.deg _ (hpl v)
  · exact ⟨(k.pl_all B hG.over_l).exists.choose⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.RootOfUnityEqOneOfCloseResidue
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem vg_ne {Γ : Type} [LinearOrderedCommGroupWithZero Γ] : (0 : Γ) < 1 := by
  refine lt_of_le_of_ne zero_le' fun h => ?_
  obtain ⟨x, y, hxy⟩ := (GroupWithZero.toNontrivial (G₀ := Γ)).exists_pair_ne
  exact hxy (by rw [← mul_one x, ← mul_one y, ← h, mul_zero, mul_zero])

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => rw [pow_zero, sub_self, map_zero]; exact vg_ne
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  have h10 : (1 : A.ValueGroup) ≠ 0 := vg_ne.ne'
  exact A.valuation.map_sum_lt h10 fun i _ => power_bounds_of_between A (aux_one A hm hη) h i

private theorem ine_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) (ζ : Ω) (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have h1 := aux_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hζ
    exact zero_ne_one hζ
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine root_of_unity_eq_one_of_close_residue A hm hv (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, h1, div_one]; exact hg.2 ζ h1.le
  exact (div_eq_one_iff_eq h0).1 this

private theorem val_nat_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (natCast_mem A n)

private theorem act_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) (n : ℕ) (s : G ℚ Ω) :
    ∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → (s ^ n) ζ = ζ ^ a ^ n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero w := ⟨hw⟩
  haveI : NeZero (w : Ω) := ⟨Nat.cast_ne_zero.2 hw⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω w
  obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one (ξ := s z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  have h1 : ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a := fun ζ h => by
    obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one h
    rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨a, fun ζ h => ?_⟩
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h1 ζ h, ← pow_mul, pow_succ']

private theorem pow_mem_Upl {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    {Hb H₀ : Subgroup (G ℚ Ω)} {w : ℕ} (hw : w ≠ 0) (hab : commutator (G ℚ Ω) ≤ Hb) (hidx : ∃ a : ℕ, Hb.index = l ^ a) (m : ℕ) :
    ∃ N : ℕ, ∀ s ∈ H₀, s ^ l ^ N ∈ Upl l Hb H₀ w m := by
  obtain ⟨a, ha⟩ := hidx
  haveI : Hb.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by group
    rw [this]
    exact Hb.mul_mem (hab (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))) hn⟩
  refine ⟨1 + a + m, fun s hs => ⟨⟨⟨H₀.pow_mem hs _, ?_⟩, ?_⟩, ?_⟩⟩
  · have : s ^ l ∈ Hth Ω l w := ⟨act_pow hw l s, by
      show ∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → (s ^ l)⁻¹ ζ = ζ ^ a ^ l
      rw [← inv_pow]; exact act_pow hw l s⁻¹⟩
    rw [add_assoc, pow_add, pow_one, pow_mul]
    exact Subgroup.pow_mem _ this _
  · have : s ^ l ^ a ∈ Hb := ha ▸ Hb.pow_index_mem s
    rw [add_comm 1 a, add_assoc, pow_add, pow_mul]
    exact Subgroup.pow_mem _ this _
  · have : s ^ l ^ m ∈ Hlay Ω l m := by
      have hl : l.Prime := Fact.out
      haveI : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
      show (cycMod ℚ Ω l (m + 1) ^ (l - 1)) (s ^ l ^ m) = 1
      rw [MonoidHom.pow_apply, map_pow, ← pow_mul, ← Nat.totient_prime_pow_succ hl, ← ZMod.card_units_eq_totient]
      exact pow_card_eq_one
    rw [add_comm (1 + a) m, pow_add, pow_mul]
    exact Subgroup.pow_mem _ this _

private theorem core {Γ k : Type} [Group Γ] [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (κ : Γ →* kˣ)
    (U H₀ E : Subgroup Γ) (hU : ∃ N : ℕ, ∀ s ∈ H₀, s ^ l ^ N ∈ U) (h2 : H₀.index = 2) (t : Γ) (ht : t ∉ H₀) (htE : t ∈ E)
    (hκ : κ t = 1) (h : ∀ s ∈ U ⊓ E, κ s = 1) : ∀ s ∈ E, κ s = 1 := by
  obtain ⟨N, hN⟩ := hU
  have h0 : ∀ s ∈ H₀, s ∈ E → κ s = 1 := fun s hs hE => by
    have h1 := h _ ⟨hN s hs, E.pow_mem hE _⟩
    rw [map_pow] at h1
    have h3 : (κ s : k) ^ l ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have h4 : ((κ s : k) - 1) ^ l ^ N = 0 := by rw [sub_pow_char_pow, h3, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h4))
  intro s hs
  by_cases hH : s ∈ H₀
  · exact h0 s hH hs
  · have := h0 (s * t) ((Subgroup.mul_mem_iff_of_index_two h2).2 (by simp [hH, ht])) (E.mul_mem hs htE)
    rwa [map_mul, hκ, mul_one] at this

theorem UpperTheory.V.Fr.l15 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (H₀ : Subgroup (G ℚ Ω)) (w : ℕ), FrobeniusSplitPrimeDatum η M H₀ → FrobeniusWitnessPrime l η Ψ M w → ∀ (m : ℕ) (i j : ℤ), ((∀ s ∈ Upl l Hb H₀ w m, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) → ∀ s, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) ∧ ((∀ s ∈ Upl l Hb H₀ w m, omO Ω l O s ^ i * barChar O Ψ s ^ j = etaO O η s) → ∀ s, omO Ω l O s ^ i * barChar O Ψ s ^ j = etaO O η s) ∧ ((∀ s ∈ Upl l Hb H₀ w m ⊓ η.ker, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) → ∀ s ∈ η.ker, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) := by
  intro Ω _ _ _ l hl O _ _ _ η Ψ σ B M Hb hG H₀ w h0 hW m i j
  have hU := pow_mem_Upl l (H₀ := H₀) hW.prime.ne_zero hG.Hb_ab hG.Hb_idx m
  obtain ⟨A, hA, hI⟩ := h0.ram
  obtain ⟨t, ht, htH⟩ := SetLike.not_le_iff_exists.1 hI
  obtain ⟨a, ka, kb⟩ := hG.cyc
  have hM1 : A.valuation (M : Ω) = 1 := le_antisymm (val_nat_le A M) (not_lt.1 hA)
  have hMa : ¬ A.valuation ((M ^ a : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hM1, one_pow]; exact lt_irrefl _
  have hfix := ine_fix A (pow_ne_zero a hG.M_ne) hMa ht
  have hη : η t = 1 := ka t hfix
  have hΨ : barChar O Ψ t = 1 := kb t hfix
  have hlv : ¬ A.valuation (l : Ω) < 1 := fun h => hA (by
    obtain ⟨c, rfl⟩ := hG.l_dvd
    rw [Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_nat_le A c)) h)
  have hω : omO Ω l O t = 1 := by
    have h1 : cycZ ℚ Ω l t = 1 := (UpperTheory.V.Base.places ℚ Ω l A).2.2.2 hlv ht
    simp [GC.cycF, cycMod, h1]
  have he : etaO O η t = 1 := by simp [hη]
  let κ : G ℚ Ω →* (ResidueField O)ˣ := omO Ω l O ^ i * barChar O Ψ ^ j
  have hκ : ∀ s, κ s = omO Ω l O s ^ i * barChar O Ψ s ^ j := fun s => by simp [κ]
  have hκt : κ t = 1 := by rw [hκ, hω, hΨ]; simp
  refine ⟨fun h s => ?_, fun h s => ?_, fun h s hs => ?_⟩
  · rw [← hκ]
    exact core l κ _ H₀ ⊤ hU h0.idx t htH trivial hκt (fun s hs => by rw [hκ]; exact h s hs.1) s trivial
  · have := core l (κ * (etaO O η)⁻¹) _ H₀ ⊤ hU h0.idx t htH trivial
      (by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hκt, he]; simp)
      (fun s hs => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hκ, h s hs.1, mul_inv_cancel]) s trivial
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hκ] at this
    exact mul_inv_eq_one.1 this
  · rw [← hκ]
    exact core l κ _ H₀ η.ker hU h0.idx t htH hη hκt (fun s hs => by rw [hκ]; exact h s hs) s hs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScQuad
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_quad :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (η : G ℚ Ω →* ℤˣ) (D : ℕ) (δ : Ω), 0 < D → δ ^ 2 = -(D : Ω) → (∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω), Module.finrank ℚ K = 2 ∧ IsTotallyComplex K ∧ galOf ℚ K Ω = η.ker := by
  intro Ω _ _ _ η D δ hD hδ hη
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 : ((D : ℕ) : Ω) = 0 := by
      have := hδ.symm
      simpa using this
    exact hD.ne' (by exact_mod_cast h0)
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (D : ℚ) with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hdeg : p.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hroot : Polynomial.aeval δ p = 0 := by
    simp [hp, hδ]
  have hirr : Irreducible p := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hmin : p = minpoly ℚ δ := minpoly.eq_of_irreducible_of_monic hirr hroot hmon
  have hint : IsIntegral ℚ δ := ⟨p, hmon, by rw [← Polynomial.aeval_def]; exact hroot⟩
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({δ} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField (IntermediateField.adjoin ℚ ({δ} : Set Ω)) := by constructor
  refine ⟨IntermediateField.adjoin ℚ ({δ} : Set Ω), inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [IntermediateField.adjoin.finrank hint, ← hmin, hdeg]
  · refine ⟨fun v => ?_⟩
    rw [NumberField.InfinitePlace.isComplex_iff]
    intro hr
    rw [NumberField.ComplexEmbedding.isReal_iff] at hr
    set φ := v.embedding
    let d : IntermediateField.adjoin ℚ ({δ} : Set Ω) := ⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩
    have hd : d ^ 2 = -(D : IntermediateField.adjoin ℚ ({δ} : Set Ω)) := Subtype.ext (by simpa [d] using hδ)
    have hz : (φ d) ^ 2 = -(D : ℂ) := by
      have := congrArg φ hd
      simpa using this
    have hc : (starRingEnd ℂ) (φ d) = φ d := by
      have := RingHom.congr_fun hr d
      simpa using this
    have him : (φ d).im = 0 := Complex.conj_eq_iff_im.mp hc
    have hre := congrArg Complex.re hz
    simp [pow_two, him] at hre
    nlinarith [mul_self_nonneg (φ d).re]
  · ext σ
    rw [mem_galOf, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : σ δ = δ := h ⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩
      rw [hη σ] at h1
      rcases Int.units_eq_one_or (η σ) with h2 | h2
      · exact h2
      · exfalso
        rw [h2] at h1
        simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h1
        have : (2 : Ω) * δ = 0 := by linear_combination -h1
        rcases mul_eq_zero.mp this with h3 | h3
        · exact two_ne_zero h3
        · exact hδ0 h3
    · intro h x
      have hσδ : σ δ = δ := by rw [hη σ, h]; simp
      have hext : ((σ : Ω →ₐ[ℚ] Ω).comp (IntermediateField.val _) :
          IntermediateField.adjoin ℚ ({δ} : Set Ω) →ₐ[ℚ] Ω) = IntermediateField.val _ :=
        IntermediateField.algHom_ext_of_eq_adjoin ℚ rfl (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hσδ)
      exact AlgHom.congr_fun hext x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

theorem UpperTheory.V.Fr.st_conj :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k : Type) [Field k] (κ : G ℚ Ω →* kˣ) (y : G ℚ Ω → k), (∀ s t, y (s * t) = y s + κ s * y t) → ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → (∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = κ s * b - b) → ∃ b, ∀ s ∈ Dec (F := ℚ) A', y s = κ s * b - b := by
  intro Ω _ _ _ k _ κ y hy v A A' hA hA' ⟨b, hb⟩
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) hA hA'
  refine ⟨(κ σ : k) * b - y σ, fun s hs => ?_⟩
  have hs' : s • A' = A' := mem_Dec.mp hs
  have ht : σ⁻¹ * s * σ ∈ Dec (F := ℚ) A := by
    rw [mem_Dec, mul_smul, mul_smul, hσ, hs', ← hσ, ← mul_smul, inv_mul_cancel, one_smul]
  have hbt := hb _ ht
  have hκ : κ (σ⁻¹ * s * σ) = κ s := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have hκ' : ((κ (σ⁻¹ * s * σ) : kˣ) : k) = κ s := congrArg Units.val hκ
  have h1 := hy s σ
  have h2 := hy σ (σ⁻¹ * s * σ)
  have h3 : σ * (σ⁻¹ * s * σ) = s * σ := by group
  rw [h3] at h2
  linear_combination -h1 + h2 + (κ σ : k) * hbt + (κ σ : k) * b * hκ'
end

