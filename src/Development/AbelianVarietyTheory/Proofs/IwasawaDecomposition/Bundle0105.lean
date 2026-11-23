module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0001
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEta
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjQuotientOfRationalUnitaryDeterminantMa
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.RatPts

theorem exists_mul_apply_eq_of_mul_apply_eq_one_of_involution {L : Type} [Field L] (c : L →+* L) (hc : ∀ x, c (c x) = x) (hne : ∃ a, c a ≠ a)
    (z : L) (hz : z * c z = 1) : ∃ k : Lˣ, z * c (k : L) = k := by
  by_cases h : 1 + z = 0
  · obtain ⟨a, ha⟩ := hne
    refine ⟨Units.mk0 (a - c a) (sub_ne_zero.2 ha.symm), ?_⟩
    have hz1 : z = -1 := by linear_combination h
    rw [Units.val_mk0, map_sub, hc, hz1]
    ring
  · refine ⟨Units.mk0 (1 + z) h, ?_⟩
    rw [Units.val_mk0, map_add (f := _), map_one]
    linear_combination hz

theorem fixed_of_two {L : Type} [Field L] (c : L →+* L) (z : L) (k k' : Lˣ)
    (h : z * c (k : L) = k) (h' : z * c (k' : L) = k') :
    c ((k⁻¹ * k' : Lˣ) : L) = ((k⁻¹ * k' : Lˣ) : L) := by
  have h0 : c (k : L) ≠ 0 := (map_ne_zero c).2 k.ne_zero
  have h1 : (k : L) ≠ 0 := k.ne_zero
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  field_simp
  linear_combination c (k : L) * h' - c (k' : L) * h


open Classical in
theorem rat_points : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsRationalUnitaryDeterminantMap H (e1T H) ∧ (letI := H.cmStar; ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k) := by
  intro R H
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  letI := H.cmStar
  have h90 : ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k := by
    intro z
    refine exists_mul_apply_eq_of_mul_apply_eq_one_of_involution (H.conj : H.E →+* H.E) (fun x => ?_) ?_ (z : H.E) ?_
    · show H.conj (H.conj x) = x
      rw [← hc, ← hc, IsCMField.complexConj_apply_apply]
    · by_contra hn
      push Not at hn
      exact IsCMField.complexConj_ne_one H.E (AlgEquiv.ext fun x => (hc x).trans (hn x))
    · show (z : H.E) * H.conj (z : H.E) = 1
      rw [← bridge_star_holds R H]
      exact z.2.2
  have hwd : ∀ (z : H.E) (k k' : (H.E)ˣ), z * H.conj (k : H.E) = k → z * H.conj (k' : H.E) = k' →
      (QuotientGroup.mk (Neutral.B1.diagUnits H.E k) : DtT H) = QuotientGroup.mk (Neutral.B1.diagUnits H.E k') := by
    intro z k k' h h'
    have hfix := fixed_of_two (H.conj : H.E →+* H.E) z k k' h h'
    have hF : ((k⁻¹ * k' : (H.E)ˣ) : H.E) ∈ H.F :=
      (IsCMField.complexConj_eq_self_iff H.E _).1 ((hc _).trans hfix)
    have hne : (⟨_, hF⟩ : H.F) ≠ 0 := fun e => (k⁻¹ * k').ne_zero (congrArg Subtype.val e)
    have e : Formalism.L2.Host.upF H.F (Units.mk0 _ hne) = k⁻¹ * k' := Units.ext rfl
    have := (_root_.GlobalTheory.Mem.KerDet.kernel_open_and_factor R H).2.2.1 (Units.mk0 _ hne)
    rw [e, map_mul, map_inv] at this
    exact QuotientGroup.eq.2 this
  refine ⟨isRationalUnitaryDeterminantMap_rationalUnitaryToDeterminants H ?_, h90⟩
  choose s hs using h90
  refine ⟨MonoidHom.mk' (fun z => QuotientGroup.mk (Neutral.B1.diagUnits H.E (s z))) fun z z' => ?_,
    fun k z h => hwd z k (s z) h (hs z)⟩
  rw [← QuotientGroup.mk_mul, ← map_mul]
  refine hwd ((z * z' : unitary H.E) : H.E) _ _ (hs _) ?_
  rw [Submonoid.coe_mul, Units.val_mul, map_mul, mul_mul_mul_comm, hs, hs]

end GlobalTheory.Mem.RatPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.FrameVal

theorem exists_galois_ge (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ IsGalois ℚ N ∧ M ≤ N := by
  have hn : IsNormalClosure ℚ M (IntermediateField.normalClosure ℚ M ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun x => IsAlgClosed.splits _)
  have : Normal ℚ (IntermediateField.normalClosure ℚ M ℂ) := hn.normal
  exact ⟨IntermediateField.normalClosure ℚ M ℂ, inferInstance, {}, IntermediateField.le_normalClosure M⟩

theorem exists_roots (n : ℕ) (hn : 0 < n) :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ ∀ x : ℂ, x ^ n = 1 → x ∈ N := by
  have hfin : {x : ℂ | x ^ n = 1}.Finite := by
    refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => ?_
    simpa [Polynomial.mem_nthRoots hn] using hx
  have := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ {x : ℂ | x ^ n = 1}, IntermediateField.finiteDimensional_adjoin fun x hx => ?_,
    fun x hx => IntermediateField.subset_adjoin _ _ hx⟩
  exact IsIntegral.of_pow hn (by rw [show x ^ n = 1 from hx]; exact isIntegral_one)

theorem valuesIn_mono {L : Type} [Field L] [NumberField L] {χ : Formalism.L2.Host.HChar L} {s : ℝ} {M N : IntermediateField ℚ ℂ}
    (h : χ.ValuesIn s M.val.toRingHom) (hMN : M ≤ N) : χ.ValuesIn s N.val.toRingHom := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨⟨y, hMN y.2⟩, hy⟩

theorem exists_of_order {L : Type} [Field L] [NumberField L] {χ : Formalism.L2.Host.HChar L} (h : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn 0 M.val.toRingHom := by
  obtain ⟨n, hn, ho⟩ := h
  obtain ⟨N, hN, hr⟩ := exists_roots n hn
  refine ⟨N, hN, fun v _ => ⟨⟨(χ.val v : ℂ), hr _ ?_⟩, by simp [Formalism.L2.Host.HChar.valTw]⟩⟩
  have h1 : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : Formalism.L2.Host.HChar L => ξ.1 x) ho
  have h2 : χ.val v ^ n = 1 := h1 _
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]

theorem exists_of_emb {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ x, φ x ∈ M :=
  ⟨φ.toRatAlgHom.fieldRange, (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv.finiteDimensional, fun x => ⟨x, rfl⟩⟩


open Classical in
theorem frame_values : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : HFrame H e), (∀ j τ, ∃ z : ℤ, e j τ = z) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧ (∀ g x, H.emb g x ∈ M) ∧ (∀ j, (C.mu0 j).ValuesIn 0 M.val.toRingHom) ∧ C.eta.ValuesIn (1 / 2) M.val.toRingHom ∧ C.chiPsi.ValuesIn 0 M.val.toRingHom ∧ C.del.ValuesIn 0 M.val.toRingHom ∧ C.del'.ValuesIn 0 M.val.toRingHom ∧ ∀ k a, ((C.W.om k a : ℂˣ) : ℂ) ∈ M := by
  intro R H e C he
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have alg := _root_.GlobalTheory.Mem.ValAlg.values_in_numberField H.F H.E c (R.Psi) (Formalism.L2.Host.embPsi H) hcm
  choose Me hMe hMe' using fun φ : H.E →+* ℂ => exists_of_emb φ
  have hmu : ∀ j, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (C.mu0 j).ValuesIn 0 M.val.toRingHom := by
    intro j
    obtain ⟨n, hn, hi⟩ := (C.isMu0 j).inf
    have := alg (C.mu0 j) n 0 hi fun i => by
      obtain ⟨z, hz⟩ := he j i
      have h1 : (n i : ℚ) = 2 * -e j i := hn i
      rw [hz] at h1
      have h2 : n i = 2 * -z := by exact_mod_cast h1
      exact ⟨-z, by rw [h2]; ring⟩
    simpa using this
  choose Mm hMm hMm' using hmu
  obtain ⟨M1, hM1, hM1'⟩ := alg C.eta (fun _ => 1) 1 C.isEta.inf fun _ => by simp
  obtain ⟨M2, hM2, hM2'⟩ := alg C.chiPsi (fun _ => 2) 0 C.isChi.inf fun _ => by simp
  rw [Int.cast_one] at hM1'
  rw [Int.cast_zero, zero_div] at hM2'
  obtain ⟨M3, hM3, hM3'⟩ := exists_of_order C.isDel.fin
  obtain ⟨M4, hM4, hM4'⟩ := exists_of_order C.isDel'.fin
  choose Mo hMo hMo' using fun k : Fin 2 => exists_roots (Nat.card (ZMod (H.g k))ˣ) Nat.card_pos
  obtain ⟨N, hN, hG, hle⟩ := exists_galois_ge ((⨆ φ, Me φ) ⊔ (⨆ j, Mm j) ⊔ (⨆ k, Mo k) ⊔ M1 ⊔ M2 ⊔ M3 ⊔ M4)
  simp only [sup_le_iff, iSup_le_iff] at hle
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hle
  refine ⟨N, hN, hG, fun g x => h1 _ (hMe' _ x), fun j => valuesIn_mono (hMm' j) (h2 j), valuesIn_mono hM1' h4,
    valuesIn_mono hM2' h5, valuesIn_mono hM3' h6, valuesIn_mono hM4' h7, fun k a => h3 k (hMo' k _ ?_)⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

end GlobalTheory.Mem.FrameVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityTypeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ (e : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ0 : ∀ v : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), (∀ w ∈ S, ∀ w', ConjPl c.toRingEquiv w w' → w' ∉ S) → (∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) → (∏ i, φ i ((ζ : 𝓞 L) : L) ^ (-e i)) * ∏ w ∈ S, ((θ0 w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1) → ∃ χ : Formalism.L2.Host.HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => -2 * e i) ∧ (∀ v, χ.TameAt v) ∧ (∀ v, v ∉ S → (∀ w ∈ S, ¬ ConjPl c.toRingEquiv w v) → χ.UnrAt v) ∧ (∀ w ∈ S, ∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ w.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → χ.locK w k = θ0 w b) ∧ (∀ w ∈ S, ∀ n : ℕ, ((∀ x, Formalism.L2.Host.IsUnitAt w x → χ.loc w x ^ n = 1) ↔ θ0 w ^ n = 1) ∧ ∀ w', ConjPl c.toRingEquiv w w' → ((∀ x, Formalism.L2.Host.IsUnitAt w' x → χ.loc w' x ^ n = 1) ↔ θ0 w ^ n = 1)) := by
  first | exact @GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | exact GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | (intros; apply GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharPow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.PsiExist

section General

variable {L : Type} [Field L] [NumberField L]


theorem trivOn_pow {F : Type} [Field F] [NumberField F] [Algebra F L] {χ : Formalism.L2.Host.HChar L} (h : χ.TrivOn F) (n : ℕ) :
    (χ ^ n).TrivOn F := by
  induction n with
  | zero => rw [pow_zero, ← mul_inv_cancel χ]; exact h.mul h.inv
  | succ n ih => rw [pow_succ]; exact ih.mul h


end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)



end GlobalTheory.Mem.PsiExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHost
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.ChiPsiExist


open Classical in
theorem exists_chiPsi : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ χ : Formalism.L2.Host.HChar H.E, Formalism.L2.Host.IsChiPsi H χ := by
  intro R H
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (Formalism.L2.Host.embPsi H) hcm (fun _ => -1) ∅ (fun _ => 1)
      (fun w hw => absurd hw (Finset.notMem_empty w))
      (by
        intro ζ hζ
        rw [Finset.prod_empty, mul_one]
        exact UpperTheory.Mu.prod_emb_zpow H (Equiv.refl _) hζ _)
  exact ⟨χ, hu, fun v => hunr v (Finset.notMem_empty v) (fun w hw => absurd hw (Finset.notMem_empty w)), ht, hi⟩

end GlobalTheory.Mem.ChiPsiExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEtaStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_resEta_alt : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → (∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), Formalism.L2.Host.ordF P (Formalism.L2.Host.upF F k) = Formalism.L2.Host.ordF (P.under (𝓞 F)) k) → (∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), Formalism.L2.Host.etaFin (L := L) F v a) * ∏ w : InfinitePlace F, Formalism.L2.Host.etaInf F w a = 1) → ∀ (n : I → ℤ), (∀ i, Odd (n i)) → (∀ ζ : L, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ∃ δ : Lˣ, (δ : L) = ζ * c (δ : L) ∧ (∀ P : HeightOneSpectrum (𝓞 L), (Formalism.L2.Host.aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (Formalism.L2.Host.ordF P δ)) ∧ ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) → ∃ χ : Formalism.L2.Host.HChar L, χ.IsUnitary ∧ (∀ v, χ.UnrAt v) ∧ χ.ResEta F ∧ χ.HasInf φ n := by
  first | exact @GlobalTheory.Mem.EtaExt.exists_unramified_resEta | exact GlobalTheory.Mem.EtaExt.exists_unramified_resEta | (intros; apply GlobalTheory.Mem.EtaExt.exists_unramified_resEta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmSqPullG
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqLevel

open TopologicalSpace

variable {X : Scheme.{0}}

abbrev sqLB (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {L : LB X} {x : X} {J : Fin 1 → L.ι} : x ∈ (sqLB L).U J ↔ x ∈ L.U (J 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_sq_pull {Y : Scheme.{0}} {L : LB X} {F : Y ⟶ X} {y : Y} {J : PUnit → Fin 1 → L.ι} :
    y ∈ ((sqLB L).pull F).U J ↔ F y ∈ L.U (J PUnit.unit 0) :=
  mem_pull.trans mem_sq

theorem gm_sq_g {Y : Scheme.{0}} (L : LB X) (r : Y ⟶ X) (y : Y) (J J' : Fin 1 → L.ι) (hJ : r y ∈ L.U (J 0))
    (hJ' : r y ∈ L.U (J' 0)) :
    gm r y ((sqLB L).U J ⊓ (sqLB L).U J') ((sqLB L).g J J') = gm r y _ (L.g (J 0) (J' 0)) ^ 2 := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => 2) r y J J' (mem_sq.2 hJ) (mem_sq.2 hJ')).trans ?_
  rw [Fin.prod_univ_one, Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm

theorem gm_sq_pull_g {Y Z : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (J J' : PUnit → Fin 1 → L.ι)
    (hJ : F (r z) ∈ L.U (J PUnit.unit 0)) (hJ' : F (r z) ∈ L.U (J' PUnit.unit 0)) :
    gm r z (((sqLB L).pull F).U J ⊓ ((sqLB L).pull F).U J') (((sqLB L).pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit 0) (J' PUnit.unit 0)) ^ 2 :=
  (gm_pull_g (sqLB L) F r z J J' (mem_sq_pull.2 hJ) (mem_sq_pull.2 hJ')).trans
    (gm_sq_g L (r ≫ F) z _ _ hJ hJ')

variable {B G E : Scheme.{0}} {M : LB B} {L : LB G} {p : E ⟶ B} {f : E ⟶ G}

theorem sqIso_le (q : (PUnit → Fin 1 → M.ι) × (PUnit → Fin 1 → L.ι)) :
    ((sqLB M).pull p).U q.1 ⊓ ((sqLB L).pull f).U q.2 ≤
      (M.pull p).U (fun _ => q.1 PUnit.unit 0) ⊓ (L.pull f).U (fun _ => q.2 PUnit.unit 0) :=
  fun _ h => ⟨mem_pull.2 (mem_sq_pull.1 h.1), mem_pull.2 (mem_sq_pull.1 h.2)⟩

def sqIso (w : LB.Iso (L.pull f) (M.pull p)) : LB.Iso ((sqLB L).pull f) ((sqLB M).pull p) :=
  ⟨fun q => res (sqIso_le q) (w.s (fun _ => q.1 PUnit.unit 0, fun _ => q.2 PUnit.unit 0)) ^ 2⟩

theorem gw_sqIso (w : LB.Iso (L.pull f) (M.pull p)) {Z : Scheme.{0}} (r : Z ⟶ E) (z : Z) (J : Fin 1 → M.ι)
    (K : PUnit → Fin 1 → L.ι) (hJ : p (r z) ∈ M.U (J 0)) (hK : f (r z) ∈ L.U (K PUnit.unit 0)) :
    gw (sqIso w) r z J K = gw w r z (J 0) (fun _ => K PUnit.unit 0) ^ 2 := by
  have hm : r z ∈ ((sqLB M).pull p).U (fun _ => J) ⊓ ((sqLB L).pull f).U K :=
    ⟨mem_sq_pull.2 hJ, mem_sq_pull.2 hK⟩
  exact (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hm _))

theorem sqIso_isGen {w : LB.Iso (L.pull f) (M.pull p)} (hw : w.IsGen) : (sqIso w).IsGen := by
  rw [isGen_iff] at hw ⊢
  intro Y r y j j' k k' hj hj' hk hk'
  have hj₀ := mem_sq.1 hj
  have hj₀' := mem_sq.1 hj'
  have hk₀ := mem_sq_pull.1 hk
  have hk₀' := mem_sq_pull.1 hk'
  rw [gw_sqIso w r y j k hj₀ hk₀, gw_sqIso w r y j' k' hj₀' hk₀', gm_sq_g M (r ≫ p) y j j' hj₀ hj₀',
    gm_sq_pull_g L f r y k k' hk₀ hk₀']
  have e := hw Y r y (j 0) (j' 0) (fun _ => k PUnit.unit 0) (fun _ => k' PUnit.unit 0) hj₀ hj₀'
    (mem_pull.2 hk₀) (mem_pull.2 hk₀')
  rw [gm_pull_g L f r y _ _ (mem_pull.2 hk₀) (mem_pull.2 hk₀')] at e
  rw [e, mul_pow, mul_pow, inv_pow]

end GlobalTheory.SqLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinityStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_finiteOrder_of_trivial_at_infinity : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), (∀ k, χ.inf k = 1) → ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n := by
  first | exact @GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one | exact GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one | (intros; apply GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdIdeleCharGlobalUnitEqOne
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
  GlobalTheory.NormCompat

namespace GlobalTheory.ProdLocUnit

theorem prod_locUnit_eq_one : ∀ (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (B : Type) [CommGroup B] (ψ : Neutral.B1.Ideles F →* B), IsOpen (ψ.ker : Set (Neutral.B1.Ideles F)) → (∀ k : Fˣ, ψ (Neutral.B1.diagUnits F k) = 1) → ∀ (a : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ T, ψ (locUnit F v a) = 1) → ∏ v ∈ T, ψ (locUnit F v a) = 1 := by
  intro F _ _ _ B _ ψ hker hd a T hT
  classical
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ hker
  let ι : (InfiniteAdeleRing F)ˣ →* Neutral.B1.Ideles F :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hι : Continuous ι := Continuous.units_map _ (continuous_id.prodMk continuous_const)
  have hinf : ∀ u, ψ (ι u) = 1 := by
    intro u
    obtain ⟨y, rfl⟩ := GlobalTheory.HeckeInfTriv.infUnit_surj F u
    have hc : Continuous fun y => ψ (ι (GlobalTheory.HeckeInfTriv.infUnit F y)) :=
      hψ.comp (hι.comp (GlobalTheory.HeckeInfTriv.continuous_infUnit F))
    have e := PreconnectedSpace.constant inferInstance hc (x := y) (y := 1)
    rw [e, map_one, map_one, map_one]
  let P : Neutral.B1.Ideles F →* (InfiniteAdeleRing F)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let u : (InfiniteAdeleRing F)ˣ := P (Neutral.B1.diagUnits F a)
  let av : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ :=
    fun v => Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let z : Neutral.B1.Ideles F := Neutral.B1.diagUnits F a * (ι u)⁻¹ * (∏ v ∈ T, locUnit F v a)⁻¹
  have hPι : P (ι u) = u := Units.ext rfl
  have hPl : ∀ v, P (locUnit F v a) = 1 := fun v => Units.ext rfl
  have hz1 : (z : AdeleRing (𝓞 F) F).1 = 1 := by
    have h : P z = 1 := by
      simp only [z, map_mul, map_inv, map_prod, hPι, hPl, Finset.prod_const_one, inv_one, mul_one]
      exact mul_inv_cancel u
    exact congrArg Units.val h
  have hev_d : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (Neutral.B1.diagUnits F a) = av v := fun v => Units.ext rfl
  have hev_i : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (ι u) = 1 := fun v => Units.ext rfl
  have hev_l : ∀ v w, Units.map (GlobalTheory.Mem.LocTriv.ev v) (locUnit F w a) = if w = v then av v else 1 := by
    intro v w
    apply Units.ext
    split_ifs with h
    · subst h
      exact GlobalTheory.Mem.LocTriv.ev_local_self w _
    · exact GlobalTheory.Mem.LocTriv.ev_local_ne (Ne.symm h) _
  have hzl : ∀ v, ψ (Neutral.B1.localIdele F v (Units.map (GlobalTheory.Mem.LocTriv.ev v) z)) = 1 := by
    intro v
    have e : Units.map (GlobalTheory.Mem.LocTriv.ev v) z = av v * (∏ w ∈ T, if w = v then av v else 1)⁻¹ := by
      simp only [z, map_mul, map_inv, map_prod, hev_d, hev_i, hev_l, inv_one, mul_one]
    rw [e, Finset.prod_ite_eq' T v]
    split_ifs with hv
    · rw [mul_inv_cancel, map_one, map_one]
    · rw [inv_one, mul_one]
      exact hT v hv
  have hz := GlobalTheory.FrobDense.eq_one_of_local ψ hψ z hz1 hzl
  simp only [z, map_mul, map_inv, map_prod, hd, hinf, inv_one, one_mul] at hz
  exact inv_eq_one.mp hz

end GlobalTheory.ProdLocUnit
end
end

