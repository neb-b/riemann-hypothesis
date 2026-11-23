module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KerQFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem mem_princ_of_pow {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ∈ KStar.TotallyRealRoots.princ l 1) {n : ℕ}
    (h : u ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l n) : u ∈ KStar.TotallyRealRoots.princ l n := by
  have hl : l.Prime := Fact.out
  rw [KStar.TotallyRealRoots.mem_princ] at hu h ⊢
  rw [Units.val_pow_eq_pow_val] at h
  set x : ℤ_[l] := (u : ℤ_[l]) with hx
  set S : ℤ_[l] := ∑ i ∈ Finset.range (l - 1), x ^ i with hSdef
  have hgeom : x ^ (l - 1) - 1 = (x - 1) * S := by
    rw [hSdef, mul_comm, geom_sum_mul]
  have hl1 : (l : ℤ_[l]) ∣ x - 1 := by simpa using hu
  have hdiff : (l : ℤ_[l]) ∣ ∑ i ∈ Finset.range (l - 1), (x ^ i - 1) :=
    Finset.dvd_sum fun i _ => dvd_trans hl1 (by simpa [one_pow] using sub_dvd_pow_sub_pow x 1 i)
  have hSeq : S = ∑ i ∈ Finset.range (l - 1), (x ^ i - 1) + ((l : ℤ_[l]) - 1) := by
    rw [Finset.sum_sub_distrib, hSdef]
    simp [Nat.cast_sub hl.one_le]
  have hlnu : ¬IsUnit (l : ℤ_[l]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  have hS : IsUnit S := by
    by_contra hne
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at hne
    apply hlnu
    apply isUnit_of_dvd_one
    have h2 := dvd_sub (dvd_add hdiff (dvd_refl (l : ℤ_[l]))) hne
    convert h2 using 1
    rw [hSeq]
    ring
  rw [hgeom] at h
  exact hS.dvd_mul_right.mp h

private theorem comm_le_ker {Γ M : Type} [Group Γ] [Monoid M] (f : Γ →* M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    commutator Γ ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, ← map_mul f a b, hf a b,
    map_mul, mul_assoc (f b), ← map_mul f a a⁻¹, mul_inv_cancel, map_one, mul_one, ← map_mul,
    mul_inv_cancel, map_one]

theorem UpperTheory.V.Ws.kerOverRationals_open_commutator_layer :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (F : IntermediateField ℚ Ω) [NumberField F] [IsAbelianGalois ℚ F], IsOpen (kerQ D F : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ kerQ D F ∧ ∀ (m : ℕ) (F' : IntermediateField ℚ Ω), IsLayer l m F F' → kerQ D F' = levU l (kerQ D F) (m + 1) ∧ cycU l (kerQ D F) ≤ F'.fixingSubgroup := by
  intro Ω _ _ _ l _ c D hD F hnf hab
  haveI := hnf
  haveI := hab
  have hnorm : Normal ℚ F := by
    haveI : IsGalois ℚ F := IsAbelianGalois.toIsGalois
    exact IsGalois.to_normal
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrb, -, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hcm : (cycMod ℚ Ω l 1).ker = Subgroup.comap (cycZ ℚ Ω l) (KStar.TotallyRealRoots.princ l 1) := rfl
  have key : ∀ g, g ∈ (cycMod ℚ Ω l 1).ker ↔ cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l 1 := fun g => by
    rw [hcm]
    rfl
  have hdiag : ∀ g, D.rbar g = Matrix.diagonal fun i => IsLocalRing.residue c.O ((D.ps i g : (c.O)ˣ) : c.O) := by
    intro g
    ext i j
    simp [Raw.rbar, Raw.r0, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hrc : ∀ a b, D.rbar (a * b) = D.rbar (b * a) := by
    intro a b
    rw [map_mul, map_mul, hdiag, hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · show IsOpen ((F.fixingSubgroup ⊓ D.rbar.ker ⊓ (cycMod ℚ Ω l 1).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))
    rw [Subgroup.coe_inf, Subgroup.coe_inf, hcm, Subgroup.coe_comap]
    exact (F.fixingSubgroup_isOpen.inter hrb).inter
      ((KStar.TotallyRealRoots.isOpen_princ 1).preimage (continuous_cycZ ℚ Ω l))
  · refine le_inf (le_inf ?_ ?_) ?_
    · rw [← @IntermediateField.restrictNormalHom_ker _ _ _ _ _ F hnorm]
      exact comm_le_ker _ fun a b => by
        rw [map_mul, map_mul]
        exact (IsMulCommutative.is_comm (M := Gal(F/ℚ))).comm _ _
    · exact comm_le_ker _ hrc
    · exact comm_le_ker _ fun a b => by rw [map_mul, map_mul, mul_comm]
  · intro m F' hL
    constructor
    · ext g
      simp only [kerQ, levU, Subgroup.mem_inf, Subgroup.mem_comap, key, hL g]
      constructor
      · rintro ⟨⟨⟨hF, hp⟩, hr⟩, h1⟩
        exact ⟨⟨⟨hF, hr⟩, h1⟩, mem_princ_of_pow h1 hp⟩
      · rintro ⟨⟨⟨hF, hr⟩, h1⟩, hn⟩
        exact ⟨⟨⟨hF, Subgroup.pow_mem _ hn _⟩, hr⟩, h1⟩
    · intro g hg
      simp only [cycU, kerQ, Subgroup.mem_inf, MonoidHom.mem_ker] at hg
      rw [hL g]
      refine ⟨hg.1.1.1, ?_⟩
      rw [hg.2, one_pow]
      exact one_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KrFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cyc_open (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [hl : Fact l.Prime] : IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) := by
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have e1 : ((cycMod F Ω l 1).ker : Set (G F Ω)) =
      (fun g => ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) - 1) ⁻¹' Metric.closedBall 0 ((l : ℝ) ^ (-(1 : ℕ) : ℤ)) := by
    ext g
    rw [Set.mem_preimage, mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, map_one, sub_eq_zero, SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [e1]
  refine (IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))).preimage ?_
  exact (Units.continuous_val.comp (continuous_cycZ F Ω l)).sub continuous_const

private theorem not_dvd_ker {H : Type} [Group H] (l : ℕ) [hl : Fact l.Prime] (φ : H →* (ZMod (l ^ 1))ˣ) :
    ¬ l ∣ φ.ker.index := by
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  intro h
  rw [Subgroup.index_ker] at h
  have h1 : l ∣ Nat.card (ZMod (l ^ 1))ˣ := h.trans (Subgroup.card_subgroup_dvd_card _)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out] at h1
  have h2 := hl.out.two_le
  have := Nat.le_of_dvd (by omega) h1
  omega

private theorem rbar_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (g : G ℚ Ω) :
    D.rbar g = 1 ↔ ∀ i, Units.map (residue c.O).toMonoidHom (D.ps i g) = 1 := by
  have hr : D.rbar g = Matrix.diagonal fun i => residue c.O (D.ps i g : c.O) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Raw.rbar, Raw.r0, diagRep]
    · simp [Raw.rbar, Raw.r0, diagRep, h]
  rw [hr, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
  exact forall_congr' fun i => by rw [Units.ext_iff]; rfl

theorem UpperTheory.V.Ws.residualKernel_properties :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Kr.Normal ∧ IsOpen (T.Kr : Set (G T.F Ω)) ∧ ¬ l ∣ T.Kr.index ∧ T.Kr ≤ (cycMod T.F Ω l 1).ker ∧ (∀ g ∈ T.Kr, D.rbar (resQ T.F g) = 1) ∧ (∀ w g, D.rbar (resQ T.F g) = 1 → T.rbU w g = 1) ∧ (prodS D ≠ 0 ∧ l ∣ prodS D) ∧ (∀ g ∈ ineOff T.F Ω (prodS D), g ∈ (T.fr ∅).N ∧ D.rbar (resQ T.F g) = 1) ∧ ∀ r, XRk l 1 (kerQ D T.F) r → XRk l 1 T.Kr r := by
  intro Ω _ _ _ l hl c D hD T
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, fo, -, fu⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  obtain ⟨hN, hI, -⟩ := UpperTheory.V.X.spKer D
  obtain ⟨hE, -, -⟩ := galEmbTop ℚ T.F Ω
  obtain ⟨hDI, -, -, -⟩ := galEmbFam ℚ T.F Ω l
  have hfix : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have hK : T.Kr = D.rbar.ker.comap (resQ T.F) ⊓ (cycMod T.F Ω l 1).ker := by
    ext g
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hfix g, h.1⟩, h.2⟩⟩
  refine ⟨?_, ?_, ?_, hK ▸ inf_le_right, fun g hg => hg.1.2, fun w g hg => ?_,
    ⟨Finset.prod_ne_zero_iff.2 fun p hp => (hD.S_prime p hp).ne_zero, Finset.dvd_prod_of_mem _ hD.l_mem⟩, ?_, fun r hr => ?_⟩
  · rw [hK]
    infer_instance
  · rw [hK]
    exact (fo.preimage hE.continuous).inter (cyc_open T.F Ω l)
  · rw [hK, ← Subgroup.relIndex_mul_index inf_le_left, Subgroup.inf_relIndex_left]
    intro h
    rcases (Nat.Prime.dvd_mul hl.out).1 h with h2 | h2
    · exact not_dvd_ker l _ (h2.trans (Subgroup.relIndex_dvd_index_of_normal _ _))
    · rw [Subgroup.index_comap] at h2
      exact hI (h2.trans (Subgroup.relIndex_dvd_index_of_normal _ _))
  · have h := fun i => (rbar_iff D _).1 hg (lab T.pr i)
    show Units.map (residue c.O).toMonoidHom
      ((D.ps (lab T.pr 0) (resQ T.F g) * (D.ps (lab T.pr 1) (resQ T.F g))⁻¹) ^ w.1 *
        (D.ps (lab T.pr 0) (resQ T.F g) * (D.ps (lab T.pr 2) (resQ T.F g))⁻¹) ^ w.2) = 1
    simp only [map_mul, map_zpow, map_inv, h, inv_one, mul_one, one_zpow]
  · rintro g ⟨A, hA, hg⟩
    have hS : Raw.Away D.S A := fun p hp hv => hA (by
      obtain ⟨m, hm⟩ : p ∣ prodS D := Finset.dvd_prod_of_mem _ hp
      rw [hm, Nat.cast_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (natCast_mem A m))) hv)
    have hg' : resQ T.F g ∈ Ine (F := ℚ) A := by
      rw [← (hDI A).2] at hg
      exact hg
    have h1 : D.rbar (resQ T.F g) = 1 := (rbar_iff D _).2 fun i => by
      rw [MonoidHom.mem_ker.1 (fu i A hS hg'), map_one]
    refine ⟨⟨A, fun p hp => ?_, hg, h1⟩, h1⟩
    have : p = l := by simpa using hp
    exact hS p (this ▸ hD.l_mem)
  · have hle : kerQ D T.F ≤ galOf ℚ T.F Ω := fun g hg x =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg.1.1 x.1 x.2
    obtain ⟨⟨ε, -, hε, -⟩, -⟩ := UpperTheory.V.Kum.xdualBase ℚ Ω T.F 1 (kerQ D T.F) (ZMod l) (ZMod l) hle
    have e := (ε.ofSubmodules _ _ hε).toEquiv
    exact CardLe.of_injective hr e.symm e.symm.injective
end

