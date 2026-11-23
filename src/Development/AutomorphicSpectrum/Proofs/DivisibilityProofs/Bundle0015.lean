module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.WeilBound.CoreStatements.FlagImmersions.RestDegreePowerBound
public import Development.WeilBound.CoreStatements.FlagImmersions.RootModelArithmeticIntersection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditive
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycList_divCycle_add_first : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  exact @BaseChangeColon.cycList_additive_first_class

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumLinearSubst
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_linear_subst : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime V → ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → genNum F V (fun t => ∑ i, M t i • cls i) H Q = genNum F V cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  exact @BaseChangeColon.genNum_linear_change_classes

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenericPointFieldIso
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenIso

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem genMap_bijective_of_eq {X : Scheme.{0}} {K : Type} [Field K] (η : Spec (CommRingCat.of K) ⟶ X)
    (hη : IsCptGen η) (y : X) (hy : genPt η ⤳ y) (hyq : y = genPt η) :
    Function.Bijective (genMap η ⟨y, hy⟩) := by
  subst hyq
  have : genMap η ⟨genPt η, hy⟩ = (Scheme.stalkClosedPointTo η).hom := by
    simp [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  rw [this]
  exact hη.bij

theorem genMap_comp {X : Scheme.{0}} {K : Type} [Field K] (η : Spec (CommRingCat.of K) ⟶ X) (y : X)
    (hy : genPt η ⤳ y) : spMap (genMap η ⟨y, hy⟩) ≫ X.fromSpecStalk y = η := by
  have hy' : η (IsLocalRing.closedPoint (CommRingCat.of K)) ⤳ y := hy
  change Spec.map (X.presheaf.stalkSpecializes hy' ≫ Scheme.stalkClosedPointTo η) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk η

theorem exists_iso_of_genPt_eq : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X),
    IsCptGen ξ → IsCptGen ξ' → genPt ξ = genPt ξ' → ∃ ψ : Ω' ≃+* Ω, spMap ψ.toRingHom ≫ ξ' = ξ := by
  intro X Ω Ω' _ _ ξ ξ' h h' hq
  have hs : genPt ξ ⤳ genPt ξ' := hq ▸ specializes_rfl
  let p : Cpt ξ := ⟨genPt ξ', hs⟩
  let p' : Cpt ξ' := ⟨genPt ξ', specializes_rfl⟩
  let e := RingEquiv.ofBijective (genMap ξ p) (genMap_bijective_of_eq ξ h _ hs hq.symm)
  let e' := RingEquiv.ofBijective (genMap ξ' p') (genMap_bijective_of_eq ξ' h' _ specializes_rfl rfl)
  refine ⟨e'.symm.trans e, ?_⟩
  have c1 : spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') = ξ := genMap_comp ξ _ hs
  have c2 : spMap (genMap ξ' p') ≫ X.fromSpecStalk (genPt ξ') = ξ' := genMap_comp ξ' _ specializes_rfl
  calc spMap (e'.symm.trans e).toRingHom ≫ ξ'
      = spMap (e'.symm.trans e).toRingHom ≫ (spMap (genMap ξ' p') ≫ X.fromSpecStalk (genPt ξ')) := by
        rw [c2]
    _ = spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') := by
        rw [← Category.assoc]
        congr 1
        rw [spMap, spMap, spMap, ← Spec.map_comp]
        congr 1
        ext x
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
        change e (e'.symm (genMap ξ' p' x)) = genMap ξ p x
        rw [show e'.symm (genMap ξ' p' x) = x from e'.symm_apply_apply x]
        rfl
    _ = ξ := c1

end GlobalTheory.CompanionTheory.Ar.GenIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionNumberFieldEquiv
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem intNumL_map_ringEquiv : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (V : Ideal (MRing ι F)) (l : List (K → ℤ)), intNumL F' (V.map (MvPolynomial.map (e : F →+* F'))) l = intNumL F V l := by
  intro K _ _ ι _ F F' _ _ e V l
  exact GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.GenFibNef.intNum_map e V l.get

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LieTermFlagBound
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem kappa_bound_of_decomp : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (u : Wt Ψ N) (g : ℝ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → ∀ (τ : Ψ) (σ : Ψ ⊕ Ψ) (k : ℕ), 2 ≤ k → k ≤ N → |k * degFl (pLie j (k - 1) σ * Q τ k)| ≤ ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) * ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
  intro Ψ _ _ N j u g Q _ hjN hW hD τ σ k hk2 hkN
  obtain ⟨τ', I, hcard, hsmall, heq⟩ :=
    RootFieldNumerics.M5.small_block j hjN σ (k - 1) (by omega) (Q τ k)
  have hbound : ∀ i ∈ I,
      |(k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| ≤
        ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
          (2 ^ (k - 1) / (k.factorial : ℝ) * ((⨆ i, u τ i) - ⨅ i, u τ i) *
            (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) :=
    fun i hi => RootFieldNumerics.M5.one_bound j u g Q hW hD τ τ' k hk2 hkN i (hsmall i hi)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc |(k : ℝ) * degFl (pLie j (k - 1) σ * Q τ k)|
      = (k : ℝ) * |RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (pLie j (k - 1) σ * Q τ k)| := by
        rw [RootFieldNumerics.M5.degFl_eq, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg hk0]
    _ = (k : ℝ) * |∑ i ∈ I, RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| := by
        rw [heq]
    _ = |∑ i ∈ I, (k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| := by
        rw [← Finset.mul_sum, abs_mul, abs_of_nonneg hk0]
    _ ≤ ∑ i ∈ I, |(k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
          (2 ^ (k - 1) / (k.factorial : ℝ) * ((⨆ i, u τ i) - ⨅ i, u τ i) *
            (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) :=
        Finset.sum_le_sum hbound
    _ = ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) *
          ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormula
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem top_comb_eq_arFun : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → II M.K M.ι M.P (dimFl Ψ N + 1) (fun _ => combLine (M.line t) n) = M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) :=
  RootFieldNumerics.root_model_arithmetic_intersection

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelBlockPullback
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num.PullModel

noncomputable section

open ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem smooth_trivLine : IsSmoothHerm (trivLine ι) := contDiffOn_const

theorem pull_trivLine (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) :
    IsPullHerm κ v (trivLine ι) (trivLine ι') := by
  refine ⟨?_, fun _ => rfl⟩
  funext k
  simp [trivLine, pullDeg]

theorem pull_oneLine (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) :
    IsPullHerm κ v (ReciprocityTheory.ChartRestriction.G.Geo.oneLine : HermLine ι) (ReciprocityTheory.ChartRestriction.G.Geo.oneLine : HermLine ι') := by
  refine ⟨?_, fun _ => rfl⟩
  funext k
  simp [ReciprocityTheory.ChartRestriction.G.Geo.oneLine, HermLine.ofWeight, pullDeg]

theorem smooth_monoLines {J : Type} {ℓ : J → HermLine ι} (h : ∀ j, IsSmoothHerm (ℓ j)) (m : J →₀ ℕ) (d : ℕ)
    (k : Fin d) : IsSmoothHerm (monoLines ℓ m d k) := by
  unfold monoLines
  split_ifs
  · exact h _
  · exact smooth_trivLine

theorem pull_monoLines {J : Type} {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {ℓ : J → HermLine ι}
    {ℓ' : J → HermLine ι'} (h : ∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) (m : J →₀ ℕ) (d : ℕ) (k : Fin d) :
    IsPullHerm κ v (monoLines ℓ m d k) (monoLines ℓ' m d k) := by
  unfold monoLines
  split_ifs
  · exact h _
  · exact pull_trivLine κ v

theorem snoc_oneLine {I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {n : ℕ} (L : Fin n → HermLine ι)
    (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) L ReciprocityTheory.ChartRestriction.G.Geo.oneLine) =
      -ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  have h1 : (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∉ P :=
    fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  rw [hI.2.2 P n L ReciprocityTheory.ChartRestriction.G.Geo.oneLine 1 (fun _ => 0) hP hL ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_oneLine
    (fun k => by simp [ReciprocityTheory.ChartRestriction.G.Geo.oneLine, HermLine.ofWeight])
    ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one h1]
  have hint : arInt P 1 ReciprocityTheory.ChartRestriction.G.Geo.oneLine L =
      ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    unfold arInt
    congr 1
    funext z
    exact ReciprocityTheory.ChartRestriction.G.Geo.logNorm_oneLine z
  unfold recR
  rw [ReciprocityTheory.ChartRestriction.G.Geo.divSupp_one, finsum_mem_empty, hint]
  ring

end Lines

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem smooth_line (M : RootModel Ψ N) (t : ℝ) (r : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t r) := by
  cases r with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

section Cover

variable {M M' : RootModel Ψ N} [CharZero M'.Ω] {II : IntersectionSystem}
  {κ : M.K → M'.K} {v : (Σ k, M.ι k) → (Σ k, M'.ι k)}

abbrev coverDeg (M M' : RootModel Ψ N) [CharZero M'.Ω] (v : (Σ k, M.ι k) → (Σ k, M'.ι k)) : ℕ :=
  IntermediateField.relfinrank (blockFnField (M'.y ∘ v)) (blockFnField M'.y)

theorem coverDeg_ne_zero (hδ : M'.δ = coverDeg M M' v * M.δ) : coverDeg M M' v ≠ 0 := by
  intro h
  have := M'.δ_pos
  rw [hδ, h, zero_mul] at this
  exact lt_irrefl _ this

theorem arMono_eq (hII : ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II) (hb : IsBlockMap κ v)
    (hP : imageZ v M'.P = M.P) (hl : ∀ t r, IsPullHerm κ v (M.line t r) (M'.line t r))
    (hk : M'.kA = M.kA) (hδ : M'.δ = coverDeg M M' v * M.δ) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M'.arMono II t m = M.arMono II t m := by
  have hP' : imageZ v (mCoordIdeal M'.y) = M.P := hP
  have he : (coverDeg M M' v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (coverDeg_ne_zero hδ)
  have hδ0 : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.δ_pos.ne'
  have hk0 : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.kA_pos.ne'
  have hpf := hII.2.2.1 M.K M.ι M'.K M'.ι κ v M'.Ω M'.y (dimFl Ψ N + 1)
    (monoLines (M.line t) m (dimFl Ψ N + 1)) (monoLines (M'.line t) m (dimFl Ψ N + 1)) hb M'.arith
    (by rw [hP']; exact M.arith) (smooth_monoLines (smooth_line M t) m _) (pull_monoLines (hl t) m _)
  rw [hP'] at hpf
  unfold RootModel.arMono
  split_ifs
  · change ReciprocityTheory.ChartRestriction.G.Geo.IntersectionSystem at II
    have hpf' : II M'.K M'.ι M'.P (dimFl Ψ N + 1) (monoLines (M'.line t) m (dimFl Ψ N + 1)) = _ := hpf
    rw [hpf', hk, hδ]
    push_cast
    field_simp
  · rfl

theorem geoMono_eq (hII : ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II) (hb : IsBlockMap κ v)
    (hP : imageZ v M'.P = M.P) (hl : ∀ t r, IsPullHerm κ v (M.line t r) (M'.line t r))
    (hk : M'.kA = M.kA) (hδ : M'.δ = coverDeg M M' v * M.δ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M'.geoMono m = M.geoMono m := by
  have hP' : imageZ v (mCoordIdeal M'.y) = M.P := hP
  have he : (coverDeg M M' v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (coverDeg_ne_zero hδ)
  have hδ0 : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.δ_pos.ne'
  have hk0 : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.kA_pos.ne'
  unfold RootModel.geoMono
  split_ifs
  · set L := monoLines (M.line 1) m (dimFl Ψ N) with hLdef
    set L' := monoLines (M'.line 1) m (dimFl Ψ N) with hL'def
    have hLs : ∀ j, IsSmoothHerm (L j) := smooth_monoLines (smooth_line M 1) m _
    have hL's : ∀ j, IsSmoothHerm (L' j) := smooth_monoLines (smooth_line M' 1) m _
    have hLp : ∀ j, IsPullHerm κ v (L j) (L' j) := pull_monoLines (hl 1) m _
    have hpf := hII.2.2.1 M.K M.ι M'.K M'.ι κ v M'.Ω M'.y (dimFl Ψ N + 1)
      (Fin.snoc (α := fun _ => HermLine M.ι) L ReciprocityTheory.ChartRestriction.G.Geo.oneLine)
      (Fin.snoc (α := fun _ => HermLine M'.ι) L' ReciprocityTheory.ChartRestriction.G.Geo.oneLine) hb M'.arith
      (by rw [hP']; exact M.arith)
      (fun j => by
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_oneLine
        · simpa using hLs i)
      (fun j => by
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using pull_oneLine κ v
        · simpa using hLp i)
    rw [hP'] at hpf
    have e1 := snoc_oneLine (hII.1 M'.K M'.ι) L' M'.arith hL's
    have e2 : II M.K M.ι M.P (dimFl Ψ N + 1)
        (Fin.snoc (α := fun _ => HermLine M.ι) L ReciprocityTheory.ChartRestriction.G.Geo.oneLine) =
        -ptsIntegral M.P (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
      snoc_oneLine (hII.1 M.K M.ι) L M.arith hLs
    have hpf' := hpf
    rw [e1, e2] at hpf'
    have hpts : ptsIntegral (mCoordIdeal M'.y) (fun j z => Real.log ((L' j).h z)) (fun _ => 1) =
        (coverDeg M M' v : ℝ) * ptsIntegral M.P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
      linarith
    change ptsIntegral (mCoordIdeal M'.y) (fun j z => Real.log ((L' j).h z)) (fun _ => 1) / _ = _
    rw [hpts, hk, hδ]
    push_cast
    field_simp
  · rfl

end Cover

end

theorem numbers_of_cover : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M M' : RootModel Ψ N) [CharZero M'.Ω] (II : IntersectionSystem), ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II → ∀ (κ : M.K → M'.K) (v : (Σ k, M.ι k) → (Σ k, M'.ι k)), ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v → ReciprocityTheory.ChartRestriction.G.AI.I4.imageZ v M'.P = M.P → (∀ t r, ReciprocityTheory.ChartRestriction.G.AI.I4.IsPullHerm κ v (M.line t r) (M'.line t r)) → M'.kA = M.kA → M'.δ = IntermediateField.relfinrank (ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (M'.y ∘ v)) (ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField M'.y) * M.δ → (∀ t, M'.arFun II t = M.arFun II t) ∧ M'.PP II = M.PP II ∧ (M.Converges II → M'.Converges II) ∧ M'.geoFun = M.geoFun := by
  intro Ψ _ _ N M M' _ II hII κ v hb hP hl hk hδ
  have hm : ∀ t, M'.arMono II t = M.arMono II t := fun t => funext fun m =>
    arMono_eq hII hb hP hl hk hδ t m
  have hg : M'.geoMono = M.geoMono := funext fun m => geoMono_eq hII hb hP hl hk hδ m
  refine ⟨fun t => ?_, ?_, fun hc m => ?_, ?_⟩
  · unfold RootModel.arFun
    rw [hm t]
  · unfold RootModel.PP
    congr 2
    funext m
    congr 1
    funext t
    exact congrFun (hm t) m
  · obtain ⟨L, hL⟩ := hc m
    exact ⟨L, by simpa only [hm] using hL⟩
  · unfold RootModel.geoFun
    rw [hg]

end GlobalTheory.CompanionTheory.Ar.Num.PullModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelComparisonLimit
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Root

theorem word_expand (hI : Inputs) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) {σ : Type} [Fintype σ] [DecidableEq σ]
    {d : ℕ} (hd : IsArithVar M.P d) (ℓ : σ → HermLine M.ι) (n : Fin d → σ → ℤ) (L : Fin d → HermLine M.ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (hℓ : ∀ a, IsSmoothHerm (ℓ a))
    (ha : ∀ j, (L j).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)).a)
    (hh : ∀ j, ∀ z ∈ mcPts M.P, (L j).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)).h z) :
    II _ _ M.P d L = ∑ u : Fin d → σ, (∏ k, (n k (u k) : ℝ)) * II _ _ M.P d (fun k => ℓ (u k)) := by
  have hc : ∀ j, IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)) := fun j =>
    (_root_.GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj _ M.ι σ ℓ (n j)).1 hℓ
  rw [hI.metricLocal _ M.ι (II _ M.ι) (hII.1 _ M.ι) M.P d L (fun j => GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)) hd hL hc ha hh]
  exact _root_.GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine_expansion II hII _ M.ι M.P d σ ℓ n hd hℓ

theorem cmp_root : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M₁ M₂ : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (σ : Type) [Fintype σ] [DecidableEq σ] (ℓ₁ : ℝ → σ → HermLine M₁.ι) (ℓ₂ : ℝ → σ → HermLine M₂.ι) (n : Ψ × Fin N → σ → ℤ) (s : Ψ × Fin N → Ψ × Fin N) (e₁ e₂ : ℕ), e₁ ≠ 0 → e₁ * M₁.δ = e₂ * M₂.δ → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (ℓ₁ t a) ∧ IsSmoothHerm (ℓ₂ t a)) ∧ (∀ r, (M₁.x t (s r)).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).a ∧ ∀ z ∈ mcPts M₁.P, (M₁.x t (s r)).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).h z) ∧ ∀ r, (M₂.x t r).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).a ∧ ∀ z ∈ mcPts M₂.P, (M₂.x t r).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).h z) → (∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ, Tendsto (fun t => (e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (w j)) - (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (w j))) (𝓝[>] 0) (𝓝 0)) → ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M₁.P _ (fun j => M₁.x t (s (w j))) / M₁.δ - II _ _ M₂.P _ (fun j => M₂.x t (w j)) / M₂.δ) (𝓝[>] 0) (𝓝 0) := by
  intro hI II hII Ψ _ _ N M₁ M₂ σ _ _ ℓ₁ ℓ₂ n s e₁ e₂ he₁ hδ hev hnull w
  have hδ₁ : (M₁.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M₁.δ_pos.ne'
  have hδ₂ : (M₂.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M₂.δ_pos.ne'
  have he₁' : (e₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he₁
  have hδR : (e₁ : ℝ) * M₁.δ = e₂ * M₂.δ := by exact_mod_cast hδ
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ))
    (fun u _ => (hnull u).const_mul (∏ k, (n (w k) (u k) : ℝ)))
  have hdiv := hsum.const_mul (((e₁ : ℝ) * M₁.δ)⁻¹)
  simp only [mul_zero, Finset.sum_const_zero] at hdiv
  refine Tendsto.congr' ?_ hdiv
  filter_upwards [hev] with t ht
  obtain ⟨hsm, h1, h2⟩ := ht
  have E₁ := word_expand hI II hII M₁ M₁.arith (ℓ₁ t) (fun k => n (w k)) (fun j => M₁.x t (s (w j)))
    (fun j => M₁.x_smooth t _) (fun a => (hsm a).1) (fun j => (h1 (w j)).1) (fun j => (h1 (w j)).2)
  have E₂ := word_expand hI II hII M₂ M₂.arith (ℓ₂ t) (fun k => n (w k)) (fun j => M₂.x t (w j))
    (fun j => M₂.x_smooth t _) (fun a => (hsm a).2) (fun j => (h2 (w j)).1) (fun j => (h2 (w j)).2)
  rw [E₁, E₂]
  have hsplit : ∀ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
      (∏ k, (n (w k) (u k) : ℝ)) * ((e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j)) -
        (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) =
      (e₁ : ℝ) * ((∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j))) -
        (e₂ : ℝ) * ((∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) := fun u => by ring
  simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  generalize (∑ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
    (∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j))) = A
  generalize (∑ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
    (∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) = B
  have hB : (e₂ : ℝ) * B / ((e₁ : ℝ) * M₁.δ) = B / M₂.δ := by
    rw [hδR]
    have he₂ : (e₂ : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hδR
      exact mul_ne_zero he₁' hδ₁ hδR
    field_simp
  rw [← hB]
  field_simp

end GlobalTheory.CompanionTheory.Ar.Cmp.Root
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_theorem_B : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmB_functional | exact GlobalTheory.CompanionTheory.Ar.Top.thmB_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmB_functional <;> assumption)
end

