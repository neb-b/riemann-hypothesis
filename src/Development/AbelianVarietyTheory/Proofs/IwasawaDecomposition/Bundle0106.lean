module

public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormEqOfNcardPlacesOver
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.HostSplit

theorem absNorm_eq_of_ncard_placesOver (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ}
    (hp : p.Prime) (h : (placesOver E p).ncard = Module.finrank ℚ E) :
    ∀ v ∈ placesOver E p, Ideal.absNorm v.asIdeal = p := by
  intro v hv
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hPp := v.isPrime
  have hlo : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ v.asIdeal
    rw [map_natCast]
    exact hv
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 E)
    (E ≃ₐ[ℚ] E)
  rw [← ncard_placesOver E hp, h, IsGalois.card_aut_eq_finrank,
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal (E ≃ₐ[ℚ] E)] at hf
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h1 := Nat.eq_of_mul_eq_mul_left hpos (hf.trans (mul_one _).symm)
  have h2 := Nat.eq_one_of_mul_eq_one_left h1
  have h3 := Ideal.absNorm_pow_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal
  rw [h2, pow_one] at h3
  rw [← h3]
  simp

theorem split_completely_of_modEq_one : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime →
    p ≡ 1 [MOD H.QS * H.q * H.d] →
    (placesOver H.E p).ncard = Module.finrank ℚ H.E ∧ H.cls p = PrimeClass.splitK ∧
      ∀ v ∈ placesOver H.E p, Ideal.absNorm v.asIdeal = p := by
  intro R H p hp hc
  have hn : 0 < H.QS := H.QS_pos
  have hq : 0 < H.q := H.hyp.1.pos
  have hd : 1 < H.d := H.hyp.2.1.one_lt
  have hlt : 1 < H.QS * H.q * H.d := by
    have : 0 < H.QS * H.q := by positivity
    nlinarith
  have hm : p % (H.QS * H.q * H.d) = 1 := by
    rw [Nat.ModEq] at hc
    rw [hc, Nat.mod_eq_of_lt hlt]
  obtain ⟨h1, h2⟩ := split_of_one_mod R H p hp hm
  have hG : IsGalois ℚ H.E := H.galois
  exact ⟨h1, h2, absNorm_eq_of_ncard_placesOver H.E hp h1⟩

end GlobalTheory.HostSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArtinRestrictEqArtinNormSinglePlace
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem val_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem res_art_eq_art_norm : ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Neutral.B1.Ideles E →* Gab E Ω) (artK : Neutral.B1.Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      (∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W) →
      ∀ (y : Kˣ) (τ : G K Ω),
        toAb K Ω τ = artK (Neutral.B1.localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y)) →
        toAb E Ω (τ.restrictScalars E) =
          art (Neutral.B1.localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
            (Units.map (Algebra.norm E (S := K)) y))) := by
  intro E Ω _ _ _ _ _ _ K _ _ _ art artK ha haK v W hW hWu y τ hτ
  classical
  haveI : IsTotallyComplex K := _root_.GlobalTheory.isTotallyComplex_of_algebra E K
  haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let r : G K Ω →* Gab E Ω := (toAb E Ω).comp (AlgEquiv.restrictScalarsHom E)
  have hr : Continuous r := QuotientGroup.continuous_mk.comp (_root_.GlobalTheory.restrictScalarsHom_continuous_krull E Ω K)
  let ρ : Gab K Ω →* Gab E Ω := liftAb r hr
  have hρ : ∀ σ : G K Ω, ρ (toAb K Ω σ) = toAb E Ω (σ.restrictScalars E) := fun σ => rfl
  have hρc : Continuous ρ := continuous_liftAb r hr
  let NK : Kˣ →* Eˣ := Units.map (Algebra.norm E (S := K))
  have hdE : ∀ k : Eˣ, art (Neutral.B1.diagUnits E k) = 1 := fun k => by
    have hk : Neutral.B1.diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hdK : ∀ k : Kˣ, artK (Neutral.B1.diagUnits K k) = 1 := fun k => by
    have hk : Neutral.B1.diagUnits K k ∈ artK.ker := by
      rw [haK.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  show toAb E Ω (τ.restrictScalars E) = art (locUnit E v (NK y))
  rw [← hρ, hτ]
  change ρ (artK (locUnit K W y)) = art (locUnit E v (NK y))
  rw [← div_eq_one]
  refine _root_.GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  suffices h : χ (ρ (artK (locUnit K W y))) = χ (art (locUnit E v (NK y))) by
    have h2 : χ (ρ (artK (locUnit K W y)) / art (locUnit E v (NK y))) = 1 := by
      rw [map_div, h, div_self']
    exact (QuotientGroup.eq_one_iff _).mp h2
  let ψ1 : Neutral.B1.Ideles K →* Gab E Ω ⧸ U := χ.comp (ρ.comp artK)
  let ψ2 : Neutral.B1.Ideles E →* Gab E Ω ⧸ U := χ.comp art
  have hker1 : (ψ1.ker : Set (Neutral.B1.Ideles K)) = (ρ.comp artK) ⁻¹' U := by
    ext x; simp [ψ1, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hker2 : (ψ2.ker : Set (Neutral.B1.Ideles E)) = art ⁻¹' U := by
    ext x; simp [ψ2, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have ho1 : IsOpen (ψ1.ker : Set (Neutral.B1.Ideles K)) := by
    rw [hker1]; exact hU.preimage (hρc.comp haK.quot.continuous)
  have ho2 : IsOpen (ψ2.ker : Set (Neutral.B1.Ideles E)) := by
    rw [hker2]; exact hU.preimage ha.quot.continuous

  obtain ⟨SE, ME, hvS, hSu, hSc⟩ := _root_.GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E ψ2.ker ho2 {v}
  have hvSE : v ∈ SE := hvS (Finset.mem_singleton_self v)
  obtain ⟨TSK, hTSK⟩ := _root_.GlobalTheory.PlacesOver.places_over_finset E K SE
  have hWT : W ∈ TSK := (hTSK W).mpr ⟨v, hvSE, hW⟩
  obtain ⟨MainNotions, MK, hTS, -, hSKc⟩ := _root_.GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr K ψ1.ker ho1 TSK
  choose M' hM' using fun v' : HeightOneSpectrum (𝓞 E) => _root_.GlobalTheory.NormCompat.NormCont.norm_close_to_one E K v' ME
  let M'' : ℕ := SE.sup M'
  let m : ℕ := (WithZero.log (W.valuation K (y : K))).natAbs
  obtain ⟨a, ha'⟩ := _root_.GlobalTheory.FinPlaceApprox.approx_target K TSK (fun w => if w = W then (y : K) else 1) (MK + M'' + m + 1)
  have haW : W.valuation K (a - y) ≤ WithZero.exp (-(((MK + M'' + 1 : ℕ) : ℤ) + m)) := by
    have := ha' W hWT
    rw [ite_eq_left rfl] at this
    exact val_le_of_le W this (by push_cast; omega)
  have hz : W.valuation K (a / y - 1) ≤ WithZero.exp (-((MK + M'' + 1 : ℕ) : ℤ)) :=
    val_div_sub_one_le W y.ne_zero le_rfl haW
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
    omega
  let au : Kˣ := Units.mk0 a ha0
  let zu : Kˣ := au / y
  have hzu : (zu : K) = a / y := by simp [zu, au]
  have hauy : au = y * zu := by simp [zu]

  have F1 : ψ1 (locUnit K W au) = ψ1 (locUnit K W y) := by
    have hm : locUnit K W zu ∈ ψ1.ker := hSKc W (hTS hWT) zu (by
      rw [hzu]; exact val_le_of_le W hz (by push_cast; omega))
    rw [hauy, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F2 : ψ2 (locUnit E v (NK au)) = ψ2 (locUnit E v (NK y)) := by
    have hm : locUnit E v (NK zu) ∈ ψ2.ker := hSc v hvSE (NK zu) (by
      refine hM' v (zu : K) fun w hw => ?_
      rw [hWu w hw, hzu]
      exact val_le_of_le W hz (by
        have : M' v ≤ M'' := Finset.le_sup hvSE
        push_cast; omega))
    rw [hauy, map_mul, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F3 : ∀ w ∈ TSK, w ≠ W → ψ1 (locUnit K w au) = 1 := fun w hw hne => by
    have := ha' w hw
    rw [ite_eq_right hne] at this
    exact MonoidHom.mem_ker.mp (hSKc w (hTS hw) au (val_le_of_le w this (by push_cast; omega)))
  have F4 : ∀ v' ∈ SE, v' ≠ v → ψ2 (locUnit E v' (NK au)) = 1 := fun v' hv' hne => by
    refine MonoidHom.mem_ker.mp (hSc v' hv' (NK au) ?_)
    refine hM' v' (au : K) fun w hw => ?_
    have hwT : w ∈ TSK := (hTSK w).mpr ⟨v', hv', hw⟩
    have hwW : w ≠ W := by
      rintro rfl
      exact hne (HeightOneSpectrum.ext (hw.symm.trans hW))
    have := ha' w hwT
    rw [ite_eq_right hwW] at this
    exact val_le_of_le w this (by
      have : M' v' ≤ M'' := Finset.le_sup hv'
      push_cast; omega)

  have hunitE : ∀ v' ∉ SE, ∀ x, Formalism.L2.Host.IsUnitAt v' x → ψ2 (Neutral.B1.localIdele E v' x) = 1 := fun v' hv' x hx =>
    MonoidHom.mem_ker.mp (hSu v' hv' x hx)
  have hchi := fun (v' : HeightOneSpectrum (𝓞 E)) (hv' : v' ∉ SE) (w : HeightOneSpectrum (𝓞 K))
      (hw : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v'.asIdeal) =>
    _root_.GlobalTheory.NormCompat.chi_artin_restrict E Ω K art artK ha haK ρ hρ (Gab E Ω ⧸ U) χ v' w hw (hunitE v' hv')
  obtain ⟨TK, TE, hTK1, hTK2, hTE1, hTE2, hprod⟩ := GlobalTheory.T.prod_localValues_global_over_places_above E K (Gab E Ω ⧸ U) ψ1 ψ2 SE hunitE
    (fun v' hv' w hw => (hchi v' hv' w hw).1) (fun v' hv' w hw => (hchi v' hv' w hw).2) au

  have hPK : (∏ w ∈ TK, ψ1 (locUnit K w au)) * ψ1 (locUnit K W au) = 1 := by
    have hdisj : Disjoint TK TSK := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      obtain ⟨v', hv', e⟩ := (hTSK w).mp h2
      exact hTK1 w h1 v' hv' e
    have h := _root_.GlobalTheory.ProdLocUnit.prod_locUnit_eq_one K (Gab E Ω ⧸ U) ψ1 ho1 (fun k => by simp [ψ1, hdK]) au (TK ∪ TSK) fun w hw => by
      rw [Finset.mem_union, not_or] at hw
      refine hTK2 w hw.1 fun v' hv' e => hw.2 ((hTSK w).mpr ⟨v', hv', e⟩)
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem W hWT F3] at h
    exact h
  have hPE : (∏ v' ∈ TE, ψ2 (locUnit E v' (NK au))) * ψ2 (locUnit E v (NK au)) = 1 := by
    have hdisj : Disjoint TE SE := by
      rw [Finset.disjoint_left]
      intro v' h1 h2
      exact hTE1 v' h1 h2
    have h := _root_.GlobalTheory.ProdLocUnit.prod_locUnit_eq_one E (Gab E Ω ⧸ U) ψ2 ho2 (fun k => by simp [ψ2, hdE]) (NK au) (TE ∪ SE) fun v' hv' => by
      rw [Finset.mem_union, not_or] at hv'
      exact hTE2 v' hv'.1 hv'.2
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem v hvSE F4] at h
    exact h
  have key : ψ1 (locUnit K W au) = ψ2 (locUnit E v (NK au)) := by
    rw [← hprod] at hPE
    exact mul_left_cancel (hPK.trans hPE.symm)
  show ψ1 (locUnit K W y) = ψ2 (locUnit E v (NK y))
  rw [← F1, key, F2]

end GlobalTheory.NormCompat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
section
open Formalism.IndefR Formalism.L2.DIV

namespace GlobalTheory

theorem classPres_extMem_extBij_isom : ∀ (G Γ : Type) [Group G] [Group Γ] (ι : Γ →* G) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ), P.ExtMem ∧ P.ExtBij ∧ P.Isom := by
  intro G Γ _ _ ι W _ _ K _ _ _ S σ ρ J χ P
  obtain ⟨h1, h2, h3, -⟩ := classPres_basic ι S σ ρ J χ P
  exact ⟨h1, h3, h2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocommStatement
section
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_divisible_of_cocomm : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (A : Type) [CommRing A] [Bialgebra ↥(intO C) A] [Coalgebra.IsCocomm ↥(intO C) A] [Module.Finite ↥(intO C) A] [Module.Free ↥(intO C) A] (q : ↥(intO C)), q ≠ 0 → ∀ D : A →ₗ[↥(intO C)] ↥(intO C), (∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := ↥(intO C)) a * D b - Coalgebra.counit (R := ↥(intO C)) b * D a) → (∀ u : A, IsGroupLikeElem ↥(intO C) u → q ∣ D u) → ∀ c : ↥(intO C), ‖(c : C)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → ∀ a : A, q ∣ c * D a := by
  first | exact @GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | exact GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | (intros; apply GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
section
noncomputable section

namespace GlobalTheory.Mem.An.ZeroWindow

open Complex DirichletCharacter

theorem analyticOff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
  intro s hs
  exact (χ.differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt

theorem exists_entire {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 1 ≠ 0 ∧ ∀ s, s ≠ 1 → LFunction χ s = 0 → F s = 0 := by
  by_cases h : χ = 1
  · subst h
    refine ⟨LFunctionTrivChar₁ q, differentiable_LFunctionTrivChar₁ q,
      LFunctionTrivChar₁_apply_one_ne_zero q, fun s hs h0 => ?_⟩
    rw [LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, h0, mul_zero]
  · exact ⟨LFunction χ, differentiable_LFunction h, LFunction_apply_one_ne_zero h,
      fun _ _ h0 => h0⟩

theorem ne_one_of_mem {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {t T : ℝ} {ρ : ℂ}
    (h : ρ ∈ zerosIn χ t T) : ρ ≠ 1 := by
  rintro rfl
  have h2 := h.2.1
  simp at h2

theorem finite_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) :
    (zerosIn χ t T).Finite := by
  obtain ⟨F, hF, h1, h0⟩ := exists_entire χ
  have hA : AnalyticOnNhd ℂ F Set.univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  by_contra hinf
  have hinf : (zerosIn χ t T).Infinite := hinf
  have hsub : zerosIn χ t T ⊆ Metric.closedBall (0 : ℂ) (1 + |t| + T) := by
    rintro ρ ⟨h0, h1, h2, -⟩
    rw [mem_closedBall_zero_iff]
    have := Complex.norm_le_abs_re_add_abs_im ρ
    have h3 : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h4 : |ρ.im| ≤ |t| + T := by
      have := abs_sub_abs_le_abs_sub ρ.im t
      linarith
    linarith
  obtain ⟨z, -, hz⟩ := hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall _ _) hsub
  have hfr : ∃ᶠ w in nhdsWithin z {z}ᶜ, F w = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hz
    exact hz.mono fun w hw => h0 w (ne_one_of_mem hw) hw.2.2.2
  have := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hfr
  exact h1 (this (Set.mem_univ 1))

theorem order_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
  intro ht
  rw [analyticOrderAt_eq_top] at ht
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have := (analyticOff χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hρ ht
  exact χ.LFunction_ne_zero_of_one_le_re (s := 2) (Or.inr h2) (by simp) (this h2)

theorem one_le_zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosIn χ t T) : 1 ≤ zmult χ ρ := by
  unfold zmult analyticOrderNatAt
  have h1 := order_ne_top χ (ne_one_of_mem hρ)
  have h2 : analyticOrderAt (LFunction χ) ρ ≠ 0 := by
    rw [analyticOrderAt_ne_zero]
    exact ⟨analyticOff χ ρ (ne_one_of_mem hρ), hρ.2.2.2⟩
  rw [Nat.one_le_iff_ne_zero]
  simp [h1, h2]

theorem finite_and_one_le_zmult : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ),
    (zerosIn χ t T).Finite ∧ ∀ ρ ∈ zerosIn χ t T, 1 ≤ zmult χ ρ :=
  fun _ _ χ t T => ⟨finite_zeros χ t T, fun _ hρ => one_le_zmult χ hρ⟩

end GlobalTheory.Mem.An.ZeroWindow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Branching

noncomputable section

namespace GlobalTheory.CoefIrred

theorem eq_bot_or_top_of_tensor {K ι : Type} [Field K] [Fintype ι] {V κ G : ι → Type}
    [∀ τ, AddCommGroup (V τ)] [∀ τ, Module K (V τ)] [Fintype (∀ τ, κ τ)] {W : Type} [AddCommGroup W] [Module K W]
    (b : ∀ τ, Module.Basis (κ τ) K (V τ)) (t : (∀ τ, V τ) →ₘₗ[K] W)
    (B : Module.Basis (∀ τ, κ τ) K W)
    (hB : ∀ i, B i = t fun τ => b τ (i τ)) (ρ : ∀ τ, G τ → Module.End K (V τ))
    (hρ : ∀ τ, Submodule.span K (Set.range (ρ τ)) = ⊤) (U : Submodule K W)
    (hU : ∀ g : ∀ τ, G τ, ∃ L : Module.End K W,
      (∀ f, L (t f) = t fun τ => ρ τ (g τ) (f τ)) ∧ ∀ x ∈ U, L x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨i₀, hi₀⟩ : ∃ i, B.repr x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext h))
  let Φ : (∀ τ, Module.End K (V τ)) →ₘₗ[K] W :=
    ∑ i, B.repr x i • t.compLinearMap fun τ => LinearMap.applyₗ (b τ (i τ))
  have hΦ : ∀ T, Φ T = ∑ i, B.repr x i • t fun τ => T τ (b τ (i τ)) := by
    intro T
    simp [Φ]
  have h0 : U.mkQ.compMultilinearMap Φ = 0 := by
    refine MultilinearMap.ext_of_span_eq_top hρ fun g => ?_
    obtain ⟨L, hL, hLU⟩ := hU g
    have : Φ (fun τ => ρ τ (g τ)) = L x := by
      rw [hΦ]
      conv_rhs => rw [← B.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hB, hL]
    simpa [this] using hLU x hx
  have hmem : ∀ T, Φ T ∈ U := fun T => by
    simpa using congrArg (fun m => m T) h0
  have hj : ∀ j, B j ∈ U := by
    intro j
    have h1 := hmem fun τ => ((b τ).coord (i₀ τ)).smulRight (b τ (j τ))
    rw [hΦ, Finset.sum_eq_single i₀] at h1
    · simp only [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, one_smul, ← hB] at h1
      exact (U.smul_mem_iff hi₀).1 h1
    · intro i _ hi
      obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hi
      rw [t.map_coord_zero τ, smul_zero]
      simp [Finsupp.single_eq_of_ne hτ.symm]
    · simp
  rw [eq_top_iff, ← B.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hj j

variable {K ι : Type} [Field K] [Fintype ι] {n : ℕ}

def tenMul (lam : ι → DomWeight n) : (∀ τ, nablaSq K n (lam τ)) →ₘₗ[K] VV K lam :=
  haveI := Classical.decEq ι
  ((MultilinearMap.mkPiAlgebra K ι (Pol K ι n)).compLinearMap fun τ =>
    (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap ∘ₗ (nablaSq K n (lam τ)).subtype).codRestrict (VV K lam)
    fun f => Submodule.subset_span ⟨fun τ => f τ, fun τ => (f τ).2, by simp⟩

theorem tenMul_coe (lam : ι → DomWeight n) (f : ∀ τ, nablaSq K n (lam τ)) :
    (tenMul lam f : Pol K ι n) = ten fun τ => (f τ : MvPolynomial (Fin n × Fin n) K) := by
  classical
  exact (MultilinearMap.mkPiAlgebra_apply (R := K) _).trans rfl

def ssBasis (K : Type) [Field K] (mu : DomWeight n) :
    Module.Basis (Formalism.GradedWeylDivisibility.ssIdx n n mu.natW) K (nablaSq K n mu) :=
  (Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis K n n mu.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis K n n mu.natW).choose_spec.1.2.1)

theorem ssBasis_coe (mu : DomWeight n) (i : Formalism.GradedWeylDivisibility.ssIdx n n mu.natW) :
    (ssBasis K mu i : MvPolynomial (Fin n × Fin n) K) = ssB K mu.natW i := by
  simp only [ssBasis, ssB, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

theorem vv_irreducible_unitary :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → Formalism.BasicNotions.DomWeight n) (U : Submodule ℂ (Formalism.L2.DIV.VV ℂ lam)), (∀ g : ι → GL (Fin n) ℂ, (∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ x ∈ U, Formalism.L2.DIV.rhoK lam g x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro ι _ n lam U hU
  refine eq_bot_or_top_of_tensor (G := fun _ => Matrix.unitaryGroup (Fin n) ℂ)
    (fun τ => ssBasis ℂ (lam τ)) (tenMul lam) (bVV ℂ lam) (fun i => ?_)
    (fun τ => smallRep (unitaryIncl n) (lam τ))
    (fun τ => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ (isIrreducible_smallRep_unitary n (lam τ)))
    U fun g => ⟨rhoK lam fun τ => unitaryIncl n (g τ), fun f => ?_, hU _ fun τ => (g τ).2⟩
  · apply Subtype.ext
    rw [bVV_coe, tenMul_coe, bVVfun]
    simp only [ssBasis_coe]
  · apply Subtype.ext
    rw [tenMul_coe]
    change actP lam _ (tenMul lam f : Pol ℂ ι n) = _
    rw [tenMul_coe, actTen]
    rfl

end GlobalTheory.CoefIrred
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjQuotientOfRationalUnitaryDeterminantMaStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsRationalUnitaryDeterminantMap H (e1T H) ∧ (letI := H.cmStar; ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k) := by
  first | exact @GlobalTheory.Mem.RatPts.rat_points | exact GlobalTheory.Mem.RatPts.rat_points | (intros; apply GlobalTheory.Mem.RatPts.rat_points <;> assumption)
end

