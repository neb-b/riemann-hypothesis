module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Formalism.DirichletDensity.DirichletDensityProofs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.FdAdjoinRange
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

private theorem char_finext (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (ψ : Γ →* (PadicAlgCl l)ˣ) (hψ : IsOpen (ψ.ker : Set Γ)) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ g, (ψ g : PadicAlgCl l) ∈ K := by
  haveI : Finite (Γ ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ
  refine ⟨_, fd_adjoin_range l (fun q : Γ ⧸ ψ.ker => (ψ q.out : PadicAlgCl l)), fun g => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ψ.ker g
  refine IntermediateField.subset_adjoin _ _ ⟨(g : Γ ⧸ ψ.ker), ?_⟩
  have h1 : ψ (h : Γ) = 1 := h.2
  simp only [hh, map_mul, h1, mul_one]

private theorem coc_finext (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (K₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K₀]
    (θ c : Γ → PadicAlgCl l) (hθ : ∀ g, θ g ∈ K₀) (hθ1 : θ 1 = 1) (hc : Continuous c)
    (hcoc : ∀ g h, c (g * h) = c g + θ g * c h) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ K₀ ≤ E ∧ ∀ g, c g ∈ E := by
  obtain ⟨ι, _, K, hK, hcov⟩ := GlobalTheory.CompactRepField.exists_countable_family l
  have hc1 : c 1 = 0 := by
    have := hcoc 1 1
    rw [one_mul, hθ1, one_mul] at this
    exact left_eq_add.1 this
  let H : ι → Subgroup Γ := fun i =>
    { carrier := {g | c g ∈ K₀ ⊔ K i}
      one_mem' := by
        show c 1 ∈ K₀ ⊔ K i
        rw [hc1]; exact zero_mem _
      mul_mem' := fun {g h} hg hh => by
        show c (g * h) ∈ K₀ ⊔ K i
        rw [hcoc]
        exact add_mem hg (mul_mem ((le_sup_left : K₀ ≤ _) (hθ g)) hh)
      inv_mem' := fun {g} hg => by
        show c g⁻¹ ∈ K₀ ⊔ K i
        have h1 := hcoc g⁻¹ g
        rw [inv_mul_cancel, hc1] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm]
        exact neg_mem (mul_mem ((le_sup_left : K₀ ≤ _) (hθ _)) hg) }
  have hcl : ∀ i, IsClosed (H i : Set Γ) := fun i => by
    haveI := hK i
    haveI : FiniteDimensional ℚ_[l] (K₀ ⊔ K i).toSubalgebra.toSubmodule :=
      (inferInstance : FiniteDimensional ℚ_[l] (K₀ ⊔ K i : IntermediateField ℚ_[l] (PadicAlgCl l)))
    exact (Submodule.closed_of_finiteDimensional (K₀ ⊔ K i).toSubalgebra.toSubmodule).preimage hc
  have hun : ⋃ i, (H i : Set Γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨i, hi⟩ := hcov {c g} (Set.finite_singleton _)
    exact Set.mem_iUnion.2 ⟨i, (le_sup_right : K i ≤ K₀ ⊔ K i) (hi rfl)⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (H i : Set Γ) := Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (Γ ⧸ H i) := Subgroup.quotient_finite_of_isOpen _ hop
  haveI := fd_adjoin_range l (fun q : Γ ⧸ H i => c q.out)
  haveI := hK i
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun q : Γ ⧸ H i => c q.out) ⊔ (K₀ ⊔ K i), inferInstance,
    le_sup_left.trans le_sup_right, fun g => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H i) g
  have hg : g = (g : Γ ⧸ H i).out * (h : Γ)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, hcoc]
  refine add_mem ?_ (mul_mem ?_ ?_)
  · exact (le_sup_left : IntermediateField.adjoin ℚ_[l] (Set.range fun q : Γ ⧸ H i => c q.out) ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(g : Γ ⧸ H i), rfl⟩)
  · exact (le_sup_left.trans le_sup_right : K₀ ≤ _) (hθ _)
  · exact (le_sup_right : K₀ ⊔ K i ≤ _) ((H i).inv_mem h.2)

theorem UpperTheory.V.X.soBar :
    ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (ψ : G k Ω →* (PadicAlgCl l)ˣ), IsOpen (ψ.ker : Set (G k Ω)) →
    ∀ e : ℕ, 1 ≤ e → ∀ θ : G k Ω → PadicAlgCl l, (∀ g, θ g * (ψ g : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (cycZ k Ω l g : ℤ_[l]) ^ e = 1) →
    ∀ c : G k Ω → PadicAlgCl l, Continuous c → (∀ g h, c (g * h) = c g + θ g * c h) →
    (∀ A : ValuationSubring Ω, ∃ m, ∀ g ∈ Ine (F := k) A, c g = θ g * m - m) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Dec (F := k) A, c g = θ g * m - m) → ∃ m, ∀ g, c g = θ g * m - m := by
  intro CK hK hPT hLF hLT k Ω _ _ _ _ _ l _ ψ hψ e he θ hθ c hc hcoc h1 h2
  obtain ⟨K₀, hK₀, hψK⟩ := char_finext l (G k Ω) ψ hψ
  have hθK : ∀ g, θ g ∈ K₀ := fun g => by
    have h := hθ g
    rw [mul_assoc] at h
    rw [eq_inv_of_mul_eq_one_left h]
    refine inv_mem (mul_mem (hψK g) (pow_mem ?_ _))
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact K₀.algebraMap_mem _
  have hθ1 : θ 1 = 1 := by simpa using hθ 1
  obtain ⟨E, hE, hle, hcE⟩ := coc_finext l (G k Ω) K₀ θ c hθK hθ1 hc hcoc
  obtain ⟨m, -, hm⟩ := UpperTheory.V.X.soVec CK hK hPT hLF hLT k Ω l E ψ hψ (fun g => hle (hψK g)) e he θ hθ c hc hcE hcoc h1 h2
  exact ⟨m, hm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Xpp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.xpp :
    CorX → UnitaryThreeInertia.HostXpp := by
  intro hX Ω _ _ _ l hlp c N _ e ψ o₁ hD q hq S A F hF
  obtain ⟨d, f, n, _, φ, ξ, hx, hγ⟩ := dir Ω l c N e ψ o₁ hD q hq
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hlp.out).2 (by
    have h := (dvrFacts l c.O).2.2.1
    have h1 : (l : c.O) ∈ maximalIdeal c.O := by
      have : ¬ IsUnit (algebraMap ℤ_[l] c.O l) := fun h2 => PadicInt.irreducible_p.not_isUnit (h.map_nonunit _ h2)
      rw [map_natCast] at this
      exact this
    have := (residue_eq_zero_iff _).2 h1
    rwa [map_natCast] at this)
  set γ : G ℚ Ω →* (ResidueField c.O)ˣ := (redChar Ω (residue c.O) (prodX φ ξ))⁻¹ with hγd
  let κ : G ℚ Ω →* ℤˣ × (ResidueField c.O)ˣ := (F.η.prod F.Ψbar).comp F.π
  have hidx : ¬ l ∣ κ.ker.index := by
    rw [Subgroup.index_ker]
    intro h
    have h1 := h.trans (Subgroup.card_subgroup_dvd_card κ.range)
    rw [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card, Fintype.card_units_int] at h1
    haveI := Fintype.ofFinite (ResidueField c.O)
    obtain ⟨r, -, hr⟩ := FiniteField.card (ResidueField c.O) l
    rcases hlp.out.dvd_mul.1 h1 with h2 | h2
    · exact hD.l_odd ((Nat.prime_dvd_prime_iff_eq hlp.out Nat.prime_two).1 h2)
    · rw [Nat.card_eq_fintype_card, hr] at h2
      have h3 : l ∣ l ^ (r : ℕ) := dvd_pow_self l r.ne_zero
      have h4 := Nat.dvd_sub h3 h2
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hlp.out.pos)] at h4
      exact hlp.out.one_lt.ne' (Nat.dvd_one.1 h4)
  have hπ : F.π = toGS Ω _ := hF.π
  let γ' : UnitaryThreeInertia.Gam Ω S → ResidueField c.O := fun g =>
    (((F.Ψbar g)⁻¹ : (ResidueField c.O)ˣ) : ResidueField c.O) ^ 2 * ((F.η g : ℤ) : ResidueField c.O)
  have hred : ∀ g, (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O) =
      (F.Ψbar (F.π g) : ResidueField c.O) ^ 2 * ((F.η (F.π g) : ℤ) : ResidueField c.O) := fun g => by
    rw [hγ, ← hF.Ψ, ← hF.η]; rfl
  have hγ' : ∀ g, γ' (toGS Ω _ g) = γ g := fun g => by
    rw [← hπ, hγd, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hred]
    simp only [γ', Units.val_inv_eq_inv_val, mul_inv, inv_pow]
    rcases Int.units_eq_one_or (F.η (F.π g)) with h | h <;> simp [h]
  have hK : κ.ker ≤ γ.ker := fun g hg => by
    have h1 : F.η (F.π g) = 1 := congrArg Prod.fst hg
    have h2 : F.Ψbar (F.π g) = 1 := congrArg Prod.snd hg
    refine Units.ext ?_
    rw [← hγ', ← hπ]
    simp [γ', h1, h2]
  have hl : (A F.vl).valuation (l : Ω) < 1 := by
    have h := (hF.isOver F.vl ((l : ℕ) : 𝓞 ℚ)).2 hF.vl
    simpa using h
  have hV := vanOf Ω l _ γ (hX Ω l c _ (residue c.O) d f n φ ξ hx γ (.inr rfl)) {l} (fun _ => A F.vl) κ.ker
    (by simpa using ⟨Fact.out, hl⟩) inferInstance hidx
  refine xppOf F γ' (fun g => by simp only [γ']; rw [mul_right_comm, ← mul_pow]; simp) fun z z1 z2 z3 z4 => ?_
  have hz : ∀ g h, z (toGS Ω _ (g * h)) = z (toGS Ω _ g) + (γ g : ResidueField c.O) * z (toGS Ω _ h) := fun g h => by
    rw [map_mul, z2, hγ']
  obtain ⟨m, hm⟩ := hV (fun g => z (toGS Ω _ g)) (z1.comp_continuous (continuous_toGS Ω _)) hz
    (unrOf Ω _ γ κ.ker hK _ {l} z hz fun v hv => by
      by_cases h : (⟨v, hv⟩ : S) = F.vl
      · exact .inl ⟨l, Finset.mem_singleton_self l, by have := hF.vl; rwa [← h] at this⟩
      · refine .inr ⟨A ⟨v, hv⟩, hF.isOver _, fun g hg hk => ?_⟩
        have hgD : g ∈ F.D ⟨v, hv⟩ := hF.D _ ▸ Ine_le_Dec _ hg
        have hgI : g ∈ F.I ⟨v, hv⟩ := hF.I _ ▸ hg
        rw [← hπ]
        exact z3 _ h ⟨g, hgD⟩ ⟨⟨hgI, congrArg Prod.fst hk⟩, congrArg Prod.snd hk⟩)
    (fun v _ => by
      obtain ⟨m, hm⟩ := z4
      refine ⟨m, fun g hg => ?_⟩
      have hgD : g ∈ F.D F.vl := hF.D _ ▸ hg
      rw [← hγ', ← hπ]
      exact hm ⟨g, hgD⟩)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  exact (hm g).trans (by rw [← hγ']; rfl)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ZqField
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem zq_unit {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  exact hx

private theorem zq_dvd {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) (h : PadicInt.toZMod x = 0) : (l : ℤ_[l]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  exact h

private theorem zq_cast {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    (((PadicInt.toZModPow 1 x).val : ℕ) : ZMod l) = PadicInt.toZMod x := by
  have h : PadicInt.toZModPow 1 (x - (((PadicInt.toZModPow 1 x).val : ℕ) : ℤ_[l])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h
  exact h.symm

private theorem zq_four {l e : ℕ} (hl : 5 ≤ l) (he : Even e) (h1 : l - 1 ∣ 2 * e) (h2 : ¬ l - 1 ∣ e) (ho : l % 2 = 1) :
    l % 4 = 1 ∧ l / 2 ∣ e := by
  obtain ⟨n, rfl⟩ : ∃ n, l = 2 * n + 1 := ⟨l / 2, by omega⟩
  have e1 : 2 * n + 1 - 1 = 2 * n := by omega
  have e2 : (2 * n + 1) / 2 = n := by omega
  rw [e1] at h1 h2
  rw [e2]
  obtain ⟨k, rfl⟩ : n ∣ e := Nat.dvd_of_mul_dvd_mul_left two_pos h1
  refine ⟨?_, dvd_mul_right _ _⟩
  rcases Nat.even_mul.1 he with ⟨j, hj⟩ | ⟨j, hj⟩
  · omega
  · exact absurd ⟨j, by rw [hj]; ring⟩ h2

private theorem zq_gen {l e : ℕ} [Fact l.Prime] (h2 : ¬ l - 1 ∣ e) :
    ∃ u : ℤ_[l]ˣ, PadicInt.toZMod (u : ℤ_[l]) ^ e ≠ 1 := by
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have ho : orderOf b = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hb, Nat.card_eq_fintype_card, ZMod.card_units]
  have h0 : PadicInt.toZMod (((b : ZMod l).val : ℕ) : ℤ_[l]) = b := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  obtain ⟨u, hu⟩ := zq_unit _ (h0 ▸ b.ne_zero)
  refine ⟨u, fun h => h2 ?_⟩
  rw [hu, h0] at h
  rw [← ho, orderOf_dvd_iff_pow_eq_one]
  exact Units.ext (by simpa using h)

private theorem zq_root (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hp : Fact l.Prime]
    (h4 : l % 4 = 1) : ∃ s : Ω, s ^ 2 = (l : Ω) ∧ ∀ g : G ℚ Ω, (g s = s ∨ g s = -s) ∧
      (g s = s → PadicInt.toZMod (cycZ ℚ Ω l g : ℤ_[l]) ^ (l / 2) = 1) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨hp.out.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  obtain ⟨⟨s, hs⟩, h⟩ := CF.gauss Ω l ζ (by omega) hζ
  have hs2 : s ^ 2 = (l : Ω) := by
    rw [hs, CF.pStar, Even.neg_one_pow ⟨l / 4, by omega⟩]
    simp
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hp.out.ne_zero (by exact_mod_cast (hs2.symm.trans (by simp) : (l : Ω) = 0))
  refine ⟨s, hs2, fun g => ⟨?_, fun hg => ?_⟩⟩
  · refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, hs2, map_natCast]
  · have h1 := cyclotomicCharacter.spec l (n := 1) g.toRingEquiv ζ (by rw [pow_one, hζ.pow_eq_one])
    have h2 := (h s hs).2 g.toRingEquiv.toRingHom _ h1
    have h3 : s = _ := hg.symm.trans h2
    have h5 : legendreSym l ((PadicInt.toZModPow 1 (cycZ ℚ Ω l g : ℤ_[l])).val : ℕ) = 1 := by
      have : (1 : Ω) * s = _ := (one_mul s).trans h3
      exact_mod_cast (mul_right_cancel₀ hs0 this).symm
    have h6 := legendreSym.eq_pow l (((PadicInt.toZModPow 1 (cycZ ℚ Ω l g : ℤ_[l])).val : ℕ) : ℤ)
    rw [h5, Int.cast_natCast, zq_cast, Int.cast_one] at h6
    exact h6.symm

private theorem zq_hom (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) (hp : l.Prime) (hl : 5 ≤ l) (hK : Module.finrank ℚ K = 2) (hd : discr K = l)
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (h2 : ∀ m : M, 2 • m = 0 → m = 0)
    (φ : galOf ℚ K Ω → M) (hφ : φ ∈ Kum.XDual l (galOf ℚ K Ω) R M) (u : galOf ℚ K Ω) (hu : l • φ u = 0) : φ u = 0 := by
  rw [← Kum.pullOnto ℚ Ω K _ le_rfl l R M hp.ne_zero le_rfl (Or.inr h2)] at hφ
  obtain ⟨θ, hθ, rfl⟩ := hφ
  rw [Kum.clPull_apply] at hu ⊢
  generalize Kum.artCl K Ω (Kum.toGal K le_rfl u) = c at hu ⊢
  let θ' : ClassGroup (𝓞 K) →* Multiplicative M := MonoidHom.mk' (fun c => Multiplicative.ofAdd (θ c)) fun a b => by
    rw [hθ.1, ofAdd_add]
  have h1 : classNumber K • θ c = 0 := by
    have : θ' (c ^ classNumber K) = 1 := by rw [classNumber, pow_card_eq_one, map_one]
    rw [map_pow] at this
    exact this
  have hc : l.Coprime (classNumber K) :=
    (Nat.coprime_of_lt_prime (classNumber_pos K).ne' (hQuad K l hp hl hK hd) hp)
  have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hu) (addOrderOf_dvd_of_nsmul_eq_zero h1)
  rw [hc.gcd_eq_one, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at this
  exact this

open IntermediateField in
private theorem zq_field (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) (hp : l.Prime) (h4 : l % 4 = 1)
    (s : Ω) (hs : s ^ 2 = (l : Ω)) (δ : G ℚ Ω) (hδ : δ s ≠ s) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω) (_ : IsAlgClosure K Ω),
      Module.finrank ℚ K = 2 ∧ discr K = l ∧ ∀ g : G ℚ Ω, g ∈ galOf ℚ K Ω ↔ g s = s := by
  have hi : IsIntegral ℚ s := Algebra.IsIntegral.isIntegral s
  haveI : FiniteDimensional ℚ ℚ⟮s⟯ := adjoin.finiteDimensional hi
  haveI : NumberField ℚ⟮s⟯ := NumberField.of_module_finite ℚ _
  refine ⟨ℚ⟮s⟯, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, fun g => ⟨fun h => ?_, fun h x => ?_⟩⟩
  · rw [adjoin.finrank hi]
    refine le_antisymm ?_ ((minpoly.two_le_natDegree_iff hi).2 ?_)
    · have := minpoly.min ℚ s (Polynomial.monic_X_pow_sub_C (l : ℚ) two_ne_zero) (by simp [hs])
      rw [Polynomial.degree_X_pow_sub_C two_pos] at this
      exact Polynomial.natDegree_le_of_degree_le this
    · rintro ⟨q, rfl⟩
      exact hδ (δ.commutes q)
  · refine Formalism.HF.quadDiscr _ l (AdjoinSimple.gen ℚ s) (Subtype.ext (by simpa using hs)) ?_
      (Int.squarefree_natCast.2 hp.squarefree) (by omega)
    exact lift_injective _ ((lift_adjoin_simple ℚ ℚ⟮s⟯ (AdjoinSimple.gen ℚ s)).trans (lift_top ℚ ℚ⟮s⟯).symm)
  · exact h (AdjoinSimple.gen ℚ s)
  · have : ℚ⟮s⟯ ≤ fixedField (Subgroup.zpowers g) := by
      rw [adjoin_simple_le_iff, mem_fixedField_iff]
      intro f hf
      exact (Subgroup.zpowers_le.2 (show g ∈ MulAction.stabilizer (G ℚ Ω) s from h)) hf
    exact (mem_fixedField_iff _ _).1 (this x.2) g (Subgroup.mem_zpowers g)

private theorem zq_main (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hp : Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (hl : 5 ≤ l) (e : ℕ) (he : Even e)
    (h1 : l - 1 ∣ 2 * e) (h2 : ¬ l - 1 ∣ e) : Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  obtain ⟨h4, hdv⟩ := zq_four hl he h1 h2 (hp.out.eq_two_or_odd.resolve_left (by omega))
  obtain ⟨u, hu⟩ := zq_gen h2
  obtain ⟨s, hs, hG⟩ := zq_root Ω l h4
  obtain ⟨A₀, hA₀⟩ := (B3.placesQ Ω).1 l hp.out
  obtain ⟨δ, -, hδ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A₀ hA₀ u
  have hpow : ∀ g : G ℚ Ω, g s = s → PadicInt.toZMod (cycZ ℚ Ω l g : ℤ_[l]) ^ e = 1 := fun g hg => by
    obtain ⟨k, rfl⟩ := hdv
    rw [pow_mul, (hG g).2 hg, one_pow]
  have hδs : δ s ≠ s := fun h => hu (hδ ▸ hpow δ h)
  obtain ⟨K, _, _, _, _, hK, hd, hU⟩ := zq_field Ω l hp.out h4 s hs δ hδs
  set α : G ℚ Ω →* Oˣ := (1 : G ℚ Ω →* Oˣ)⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ)) with hα
  have hαg : ∀ g, α g = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ ℚ Ω l g ^ e)⁻¹ := fun g => by
    simp [hα, chiO]
  have hαs : ∀ g, (α g : O) - 1 = algebraMap ℤ_[l] O (-((cycZ ℚ Ω l g ^ e)⁻¹ : ℤ_[l]ˣ) * ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1)) :=
    fun g => by
      rw [hαg, ← Units.val_pow_eq_pow_val, mul_sub, neg_mul, Units.inv_mul, map_sub]
      simp [sub_eq_neg_add, add_comm]
  have hun : ∀ g, cycZ ℚ Ω l g = u → IsUnit ((α g : O) - 1) := fun g hg => by
    rw [hαs, hg]
    refine IsUnit.map _ ((Units.isUnit _).neg.mul (zq_unit _ ?_))
    rw [map_sub, map_pow, map_one]
    exact sub_ne_zero.2 hu
  have htr : ∀ g : G ℚ Ω, g s = s → ∀ m : QO l O, l • m = 0 → (α g : O) • m = m := fun g hg m hm => by
    obtain ⟨y, hy⟩ := zq_dvd ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1) (by rw [map_sub, map_pow, map_one, hpow g hg, sub_self])
    have : ((α g : O) - 1) • m = 0 := by
      rw [hαs, hy, mul_left_comm, map_mul, map_natCast, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hm, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have hin : ∀ A : ValuationSubring Ω, ¬ Over A l → ∀ g ∈ Ine (F := ℚ) A, α g = 1 := fun A hA g hg => by
    have : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hA hg
    rw [hαg, this, one_pow, inv_one, map_one]
  have htwo : ∀ m : QO l O, 2 • m = 0 → m = 0 := fun m hm => by
    have h : IsUnit ((2 : ℕ) : O) := by
      rw [← map_natCast (algebraMap ℤ_[l] O)]
      refine IsUnit.map _ (zq_unit _ ?_)
      rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd two_pos h) (by omega)
    exact h.smul_eq_zero.1 ((Nat.cast_smul_eq_nsmul _ _ _).trans hm)
  have key : ∀ a : O, ∀ c ∈ ShT (QO l O) α δ l a, l • c = 0 → c = 0 := by
    rintro a c ⟨⟨hlc, hc⟩, hcδ, -, hI, hD⟩ hcl
    have hcl' : ∀ g, l • c g = 0 := fun g => congrFun hcl g
    have hdec : ∀ A : ValuationSubring Ω, Over A l → ∀ g ∈ Dec (F := ℚ) A, g s = s → c g = 0 := fun A hA g hg hgs => by
      obtain ⟨m, -, hm⟩ := hD A hA
      obtain ⟨t, ht, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
      have hlm : l • m = 0 := by
        refine (hun t htu).smul_eq_zero.1 ?_
        rw [smul_comm, sub_smul, one_smul, ← hm t (Ine_le_Dec (F := ℚ) A ht), hcl']
      rw [hm g hg, htr g hgs m hlm, sub_self]
    have hX : (fun v : galOf ℚ K Ω => c v) ∈ Kum.XDual l (galOf ℚ K Ω) O (QO l O) := by
      refine ⟨hlc.comp_continuous continuous_subtype_val, fun v w => ?_, fun A v hv => ?_, fun A hA v hv => ?_⟩
      · show c (v * w) = c v + c w
        rw [hc, htr v ((hU _).1 v.2) _ (hcl' _)]
      · by_cases hA : Over A l
        · exact hdec A hA v (Ine_le_Dec (F := ℚ) A hv) ((hU _).1 v.2)
        · exact hI A hA v hv
      · exact hdec A hA v hv ((hU _).1 v.2)
    have h0 : ∀ g : G ℚ Ω, g s = s → c g = 0 := fun g hg =>
      zq_hom Ω K l hp.out hl hK hd O (QO l O) htwo _ hX ⟨g, (hU g).2 hg⟩ (hcl' g)
    funext g
    rcases (hG g).1 with hg | hg
    · exact h0 g hg
    · have : (δ⁻¹ * g) s = s := by
        rw [AlgEquiv.mul_apply, hg]
        exact δ.symm_apply_eq.2 ((hG δ).1.resolve_left hδs).symm
      rw [← mul_inv_cancel_left δ g, hc, hcδ, h0 _ this, smul_zero, add_zero, Pi.zero_apply]
  refine nonpos_iff_eq_zero.1 (shaToShT Ω l O α δ (hun δ hδ) l hp.out.ne_zero hin (fun A h h' => absurd h h') 0 fun a ha => ?_)
  have hnu : ¬ IsUnit (l : O) := fun h => by
    haveI := (dvrFacts l O).2.2.1
    rw [← map_natCast (algebraMap ℤ_[l] O), isUnit_map_iff] at h
    exact PadicInt.irreducible_p.not_isUnit h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ∣ (l : O) ^ n := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hπ
    refine ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd ?_ n)⟩
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
    exact hnu
  have hall : ∀ n : ℕ, ∀ c ∈ ShT (QO l O) α δ l a, l ^ n • c = 0 → c = 0 := by
    intro n
    induction n with
    | zero => intro c _ h; simpa using h
    | succ n ih =>
      intro c hc h
      exact ih c hc (key a _ (nsmul_mem hc _) (by rw [smul_smul, ← pow_succ', h]))
  have : ShT (QO l O) α δ l a = ⊥ := by
    refine eq_bot_iff.2 fun c hc => hall n c hc (funext fun g => ?_)
    obtain ⟨y, hy⟩ := hn
    rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, hy, mul_comm, mul_smul, hc.2.2.1 g, smul_zero, Pi.zero_apply]
  rw [this]
  simp

theorem UpperTheory.V.X.zQuad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], 5 ≤ l → ∀ e : ℕ, Even e → l - 1 ∣ 2 * e → ¬ l - 1 ∣ e → Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  intro Ω _ inst _ l _ O _ _ _ _ _ hl e he h1 h2
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact zq_main Ω l O hl e he h1 h2
end

