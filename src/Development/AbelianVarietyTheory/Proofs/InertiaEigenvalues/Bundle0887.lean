module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0883
public import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0880
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0873
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntersectionFamilyMultilinear
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionLocalIntegers
section
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem exists_linRetraction_of_isTorsionFree {R S : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    [Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S))] :
    ∃ r : S →ₗ[R] R, r 1 = 1 := by
  set N := LinearMap.range (Algebra.linearMap R S) with hN
  haveI : Module.Free R (S ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let φ : S →ₗ[R] S := LinearMap.id - s ∘ₗ N.mkQ
  have hφ : ∀ x, φ x ∈ N := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (N.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    have this' : (Submodule.Quotient.mk (s (Submodule.Quotient.mk x)) : S ⧸ N) = Submodule.Quotient.mk x := this
    simp [φ, Submodule.Quotient.mk_sub, this']
  have hinj' : Function.Injective (Algebra.linearMap R S) := hinj
  let e := LinearEquiv.ofInjective (Algebra.linearMap R S) hinj'
  refine ⟨e.symm.toLinearMap ∘ₗ φ.codRestrict N hφ, ?_⟩
  have h1 : (1 : S) ∈ N := ⟨1, map_one (algebraMap R S)⟩
  have hφ1 : φ 1 = 1 := by
    have : N.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero N).2 h1
    simp [φ, this]
  apply hinj'
  have := congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict N hφ 1))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofInjective_apply] at this
  rw [this, LinearMap.codRestrict_apply, hφ1, Algebra.linearMap_apply, map_one]

theorem isTorsionFree_quot_range {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (H : ∀ a : R, a ≠ 0 → ∀ (b : R) (z : S), algebraMap R S b = algebraMap R S a * z → ∃ c, algebraMap R S c = z) :
    Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S)) := by
  refine ⟨fun a ha => ?_⟩
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with | _ x => ?_
  induction y using Submodule.Quotient.induction_on with | _ y => ?_
  have hxy' : (Submodule.Quotient.mk (a • x) : S ⧸ LinearMap.range (Algebra.linearMap R S)) =
      Submodule.Quotient.mk (a • y) := hxy
  rw [Submodule.Quotient.eq] at hxy' ⊢
  obtain ⟨b, hb⟩ := hxy'
  rw [← smul_sub, Algebra.smul_def] at hb
  obtain ⟨c, hc⟩ := H a ha.ne_zero b (x - y) hb
  exact ⟨c, hc⟩

end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem incO_injective {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    Function.Injective (incO h) := by
  intro a b hab
  have := congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hab
  exact Subtype.ext (Subtype.ext this)

theorem incO_div {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {a b : ↥(OL LL)} (ha0 : a ≠ 0)
    {z : ↥(OL LL')} (hb : incO h b = incO h a * z) : ∃ c, incO h c = z := by
  have haL : ((a : ↥LL.1) : Om l) ≠ 0 := fun e => ha0 (Subtype.ext (Subtype.ext e))
  have hb' : ((b : ↥LL.1) : Om l) = ((a : ↥LL.1) : Om l) * ((z : ↥LL'.1) : Om l) :=
    congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hb
  have hz : ((z : ↥LL'.1) : Om l) = ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) := by
    rw [eq_div_iff haL, mul_comm]
    exact hb'.symm
  have hc : (b : ↥LL.1) / (a : ↥LL.1) ∈ OL LL := by
    rw [Formalism.BasicNotions.Examples₂.LB.mem_OL]
    have hz1 := (Formalism.BasicNotions.Examples₂.LB.mem_OL LL' (z : ↥LL'.1)).1 z.2
    rw [hz] at hz1
    simpa using hz1
  refine ⟨⟨_, hc⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) = ((z : ↥LL'.1) : Om l)
  rw [hz]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_intRetraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1),
    ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  intro l _ LL LL' h
  letI A : Algebra ↥(OL LL) ↥(OL LL') := (incO h).toAlgebra
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  haveI T : IsScalarTower ℤ_[l] ↥(OL LL) ↥(OL LL') := IsScalarTower.of_algebraMap_eq (fun x => by
    apply Subtype.ext; apply Subtype.ext; rfl)
  haveI : Module.Finite ℤ_[l] ↥(OL LL') := Formalism.BasicNotions.Examples₂.LB.OL_finite LL'
  haveI : Module.Finite ↥(OL LL) ↥(OL LL') := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI := isTorsionFree_quot_range (R := ↥(OL LL)) (S := ↥(OL LL')) (fun a ha b z hb => incO_div h ha hb)
  obtain ⟨r, hr⟩ := exists_linRetraction_of_isTorsionFree (R := ↥(OL LL)) (S := ↥(OL LL')) (incO_injective h)
  refine ⟨r.toAddMonoidHom, fun a x => ?_, hr⟩
  show r (incO h a * x) = a * r x
  have e1 : incO h a * x = a • x := (Algebra.smul_def a x).symm
  rw [e1, map_smul, smul_eq_mul]

end GlobalTheory.UseLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimes
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.LocalPositionData

theorem position_data_exist : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x), AdmissibleParameterJ.JumpConditions (Fm.L x a) → ∀ l : ℕ, l.Prime → LevelStarExponents.lStar (Fm.L x a) < (l : ℝ) → (5 ≤ l ∧ (Fm.D x a).R.t + 1 < l ∧ l ≠ (Fm.D x a).host.q ∧ l ≠ (Fm.D x a).host.d ∧ l ∉ (Fm.D x a).host.small) ∧ (l ∉ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x a) → ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x a).R.m → ∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → (Fm.D x a).what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n (Fm.D x a).R.t h w η typ U ∧ ∀ (c : ZMod n) (b : ℤ), ((U c).count (b + w c) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)) ∧ (U c).count (b + w c) ≤ 1) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar Fm
  refine ⟨x0, fun x hx hx1 a _ l hl hlS => ?_⟩
  obtain ⟨hqS, hdS, hsS⟩ := hx0 x hx hx1 a
  obtain ⟨htη, hη, hB, hSc, hls1, hls2, hH⟩ := _root_.GlobalTheory.lStar_numerics_at_record Fm x hx1 a
  have ht1 : 1 ≤ (Fm.D x a).R.t := by
    have := (Fm.D x a).R.rank_add_five_le; omega
  have htR : (0 : ℝ) ≤ (Fm.D x a).R.t := by positivity
  refine ⟨⟨?_, ?_, ?_, ?_, fun h => absurd (hsS l h) (not_lt.2 hlS.le)⟩, ?_⟩
  · have : (7 : ℝ) < l := by linarith
    exact_mod_cast (show 5 ≤ l by exact_mod_cast (show (5 : ℝ) ≤ l by linarith))
  · have : ((Fm.D x a).R.t : ℝ) + 1 < l := by linarith
    exact_mod_cast this
  · intro h; rw [h] at hlS; linarith
  · intro h; rw [h] at hlS; linarith
  intro hexc j hj1 hjm n _ up τ
  have hfinL : ∀ c, (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.lowJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin (Fm.D x a).R.m => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) - ((Fm.D x a).hc (τ c)).b i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.lowT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  have hfinC : ∀ c, (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.cloudJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin ((Fm.D x a).R.k - 1) => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) + ((Fm.D x a).hc (τ c)).v i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.cloudT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  set Fl : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)) with hFl
  set Fc : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)) with hFc
  have hdat : ∀ c, ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
      (∀ z ∈ Fl c, |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
        2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
          |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
      (∀ z ∈ Fc c, W0 ≤ (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
        (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
          W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1) := by
    intro c
    obtain ⟨hlo, W0, hW0, hcl⟩ := _root_.GlobalTheory.LetterWindows.lows_cloud_windows Fm x hx1 a j hj1 hjm (up c) (τ c)
    refine ⟨W0, hW0, fun z hz => hlo z ((GlobalTheory.PositionData.mem_intPts (hfinL c) z).1 hz),
      fun z hz => hcl z ((GlobalTheory.PositionData.mem_intPts (hfinC c) z).1 hz)⟩
  set hh : ZMod n → ℕ := fun c => GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) with hhh
  have hhle : ∀ c, (hh c : ℝ) ≤ (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 := by
    intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, hW2⟩ := _root_.GlobalTheory.Proof.baseSize_bounds_along_family.main Fm x hx1 a W0 hW0
    have := _root_.GlobalTheory.hS_le_bound (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 ht1 htη hB hSc hlo hcl hW1
    show ((GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) : ℕ) : ℝ) ≤ _
    linarith
  have hsg : ∀ c, (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) ≤ 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) := by
    intro c
    have hl2 : 2 ≤ l := hl.two_le
    set W := (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 with hW
    have hW0 : 0 ≤ W := le_trans (Nat.cast_nonneg _) (hhle c)
    have h1 := Formalism.IrreducibleCountingLemmas.TOP.carryFloorLeGeom n l hh ⌊W⌋₊ hl2 (fun c' => Nat.le_floor (hhle c')) c
    have h2 : ((⌊W⌋₊ : ℕ) : ℝ) / ((l : ℝ) - 1) ≤ W / ((l : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right (Nat.floor_le hW0)
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      linarith
    have h3 := Formalism.IrreducibleCountingLemmas.TOP.geomRatioBound l (LevelStarExponents.lStar (Fm.L x a)) (Fm.L x a).sc.b W hW0 hls1 hlS hH
    have h4 : (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) = (Formalism.IrreducibleCountingLemmas.TOP.sg n l hh c : ℝ) := rfl
    rw [h4, ← mul_div_assoc]
    linarith
  refine ⟨hh, fun c => GlobalTheory.PositionData.wS (up c) (Fl c) (Fc c), fun c => GlobalTheory.PositionData.etaS (Fm.D x a).R.t (Fl c),
    up, fun c => GlobalTheory.PositionData.US (up c) (Fl c) (Fc c), ?_, ?_⟩
  · intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, -⟩ := _root_.GlobalTheory.Proof.baseSize_bounds_along_family.main Fm x hx1 a W0 hW0
    have hex : ∀ m : ℤ, W0 + (-(Fm.L x a).etaSz - 2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) - 3) ≤ (m : ℝ) →
        (m : ℝ) ≤ W0 + ((Fm.L x a).Sc + (Fm.L x a).etaSz + (Fm.L x a).etaSz +
          2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) + 4) → ¬ (l : ℤ) ∣ m :=
      fun m h1 h2 hd => hexc ⟨hl, hlS, W0, hW0, m, ⟨h1, h2⟩, hd⟩
    have hσP : Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus
      apply Int.le_floor.mpr
      rw [mul_div_assoc]; exact hsg c
    have hT1 : 2 * (Fm.L x a).etaSz + 8 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + 7 < (l : ℝ) := by linarith
    exact _root_.GlobalTheory.PositionData.position_conditions l (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a)) (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c)
      ht1 htη hB hSc hlo hcl hW1 hex (hsg c) hσP hT1
  · intro c b
    rw [GlobalTheory.PositionData.count_US]
    have hm : b ∈ Fl c ∪ Fc c ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c) := by
      rw [Finset.mem_union, GlobalTheory.PositionData.mem_intPts (hfinL c), GlobalTheory.PositionData.mem_intPts (hfinC c)]
      unfold AdmissibleParameterJ.JW
      rw [Set.mem_union]; tauto
    rw [← hm]
    split_ifs <;> simp_all

end GlobalTheory.LocalPositionData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRecordCgTrueT
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain GlobalTheory.LocGL GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem good_loc_ofChar (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    UpperTheory.Zero.LLC.Good (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (k := w.adicCompletion E)) := by
  have h : (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (k := w.adicCompletion E)) =
      IrrGL.ofChar (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := ParLawsT.cls_loc_eq_of_isLocComp (CG.isLoc_ofChar χ w)
  rw [h]
  exact ⟨_, hasSupport_self (IrrGL.isCusp_ofChar _ _), fun y hy => Or.inl (by rw [Multiset.mem_singleton.1 hy]; rfl)⟩

theorem cls_loc_twist (π : CG E a) (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    (⟨a, ParLaws.toCl ((π.twist χ).loc w)⟩ : IrrGL (k := w.adicCompletion E)) =
      IrrGL.tw ⟨a, ParLaws.toCl (π.loc w)⟩ (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  refine (ParLawsT.cls_loc_eq_of_isLocComp (hσ.twist χ)).trans ?_
  rw [show (⟨a, ParLaws.toCl (CG.loc (Quotient.mk _ π) w)⟩ : IrrGL (k := w.adicCompletion E)) = _ from
    ParLawsT.cls_loc_eq_of_isLocComp hσ]
  exact (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

end Loc

section Host
variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {a : ℕ}

theorem goodAll_one (χ : HostCGu H 1) : GoodAll χ := fun w => by
  haveI := host_isCMField H
  have h := good_loc_ofChar χ.1.toChar w
  rwa [CG.ofChar_toChar] at h

theorem goodAll_tw_iff (π : HostCGu H a) (χ : HostCGu H 1) :
    haveI := host_isCMField H; GoodAll (H := H) (π.tw χ) ↔ GoodAll π := by
  haveI := host_isCMField H
  refine forall_congr' fun w => ?_
  have h := cls_loc_twist π.1 χ.1.toChar w
  have h2 := GlobalTheory.RecT.good_tw_iff (⟨a, ParLaws.toCl (π.1.loc w)⟩ : IrrGL (k := w.adicCompletion H.E)) (χ.1.toChar.loc w)
    (ParLaws.isSmoothChar_loc _ w)
  rw [← h] at h2
  exact h2

end Host

section Char
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locParT_unr (hT : UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLawsT.locParT hT (CG.ofChar χ) h).unr ∧
      (ParLawsT.locParT hT (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨a, ha, H⟩ := ParLawsT.isRecT_locRecT hT h
  have e2 : ParLawsT.locParT hT (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLawsT.locParT_ofChar_eq, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  exact ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), by simp⟩

end Char


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def trueKT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
      (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
      (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
      (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLawsT.lawsT hT GlobalTheory.automorphicFormsFiniteGL D.host D.nd.Om D.nd.plOm
  have U : ∀ {a} (π : HostCGu D.host a) w, D.naut.unr ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) ↔
      (ParLawsT.locGT hT D.nd.plOm π w).unr :=
    fun π w => by rw [T.unr, Equiv.apply_symm_apply]
  have Fr : ∀ {a} (π : HostCGu D.host a) w, (ParLawsT.locGT hT D.nd.plOm π w).unr →
      D.naut.frobEig ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = (ParLawsT.locGT hT D.nd.plOm π w).frobEig :=
    fun π w h => by rw [T.frobEig _ _ ((U π w).2 h), Equiv.apply_symm_apply]
  have Dm : ∀ {a} (π : HostCGu D.host a) w, D.naut.lpDim ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = a :=
    fun π w => by rw [← T.dim, Equiv.apply_symm_apply]; exact L.1 π w
  { CG := fun a => {π : HostCGu D.host a // 0 < a ∧ GoodAll π}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLawsT.locGT hT D.nd.plOm π.1 w)
    locG_dim := fun π w => Dm π.1 w
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w h => (U π.1 w).2 h
    tw := fun π χ => ⟨π.1.tw χ.1, π.2.1, (goodAll_tw_iff π.1 χ.1).2 π.2.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ (Dm χ.1 w), Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w (π.2.2 w))
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc hu => by
      have h := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc ((U π.1 w).1 hu)
      exact ⟨(U π.1 w').2 h.1, by rw [Fr π.1 w' h.1, Fr π.1 w ((U π.1 w).1 hu)]; exact h.2⟩
    etaT := ⟨η, one_pos, goodAll_one η⟩
    etaTinv := ⟨η', one_pos, goodAll_one η'⟩
    etaT_unr := fun w => (U η w).2 (h1 w)
    etaT_inert := fun w h => by rw [Fr η w (h1 w)]; exact h2 w h
    etaTinv_def := fun w => ⟨(U η' w).2 (h3 w).1, by rw [Fr η' w (h3 w).1, Fr η w (h1 w)]; exact (h3 w).2⟩
    etaT_split := fun w w' hs hc a b ha hb => by
      rw [Fr η w (h1 w)] at ha; rw [Fr η w' (h1 w')] at hb; exact h4 w w' hs hc a b ha hb }


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def trueCGT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' h1 h2 h3 h4) :
    CGTrueT hT (setCG D hE (trueKT hT D T η η' h1 h2 h3 h4)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  good := fun _ π => π.2.2
  surj := fun _ h π hπ => ⟨⟨π, h, hπ⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2.1⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem etaLawsT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) :
    haveI := host_isCMField D.host
    ∃ η η' : HostCGu D.host 1, η.1 = CG.ofChar χ ∧ η'.1 = CG.ofChar χ⁻¹ ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr) ∧
      (∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1}) ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
        (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹)) ∧
      (∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
        (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
        (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) := by
  haveI := host_isCMField D.host
  have hi : (χ⁻¹).IsUnitary := fun x => by
    have := hχ.unitary x
    change ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, this, inv_one]
  have hu : ∀ w, (χ⁻¹).UnrAt w := fun w x hx => by
    have loc_inv : (χ⁻¹).loc w x = (χ.loc w x)⁻¹ := rfl
    rw [loc_inv, hχ.unr w x hx, inv_one]
  have P := fun w => locParT_unr hT χ (D.nd.plOm.2 w) (hχ.unr w)
  have Q := fun w => locParT_unr hT χ⁻¹ (D.nd.plOm.2 w) (hu w)
  refine ⟨⟨CG.ofChar χ, CG.isUnitary_ofChar hχ.unitary⟩, ⟨CG.ofChar χ⁻¹, CG.isUnitary_ofChar hi⟩, rfl, rfl,
    fun w => (P w).1, fun w hw => (P w).2.trans ?_, fun w => ⟨(Q w).1, (Q w).2.trans ?_⟩,
    fun w w' hw hc a b ha hb => ?_⟩
  · rw [CGTrueModel.val_inert hχ hw]; simp
  · refine Eq.trans ?_ (congrArg (Multiset.map (·⁻¹)) (P w).2).symm
    simp
  · have ha' := (P w).2.symm.trans ha
    have hb' := (P w').2.symm.trans hb
    rw [Multiset.singleton_inj] at ha' hb'
    rw [← ha', ← hb', ← Units.val_mul, ← mul_inv, CGTrueModel.val_split hχ hw hc, inv_one, Units.val_one]

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalDomainPoissonCuspidal
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_poisson_cuspidal : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ γ : {ξ : Fin (m + 1) → E // ξ ≠ 0} → GL (Fin (m + 1)) E,
    (∀ ξ, Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) (γ ξ).val = ξ.1) → ∀ h : GA E (m + 1),
    HasSum (fun ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0} =>
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (Matrix.vecMul (algebraMap E (Ad E) ∘ ξ.1) h.val) *
          partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) (ratGL E (m + 1) (γ ξ) * h)))
      (partialCoeff (GlobalTheory.RSnm.colSmooth (m + 1) F φ) (m + 1 + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  first | (exact @GlobalTheory.ColFourier.hasSum_colSmooth) | (exact GlobalTheory.ColFourier.hasSum_colSmooth) | (intros; apply GlobalTheory.ColFourier.hasSum_colSmooth  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralDetLeOneEqGeometricSeriesShellsStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_det_le_one_eq_geometric_series_shells : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ (F : GA E a → ℂ), Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → ∀ χ : ℂ, ‖χ‖ = 1 → (∀ g, F (splitCentre E a 1 * g) = χ * F g) → ∀ s : ℂ, 1 < s.re → ∫ g in 𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ) / (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) := by
  first | (exact @GlobalTheory.RSThetaGeom.integral_low_geometric) | (exact GlobalTheory.RSThetaGeom.integral_low_geometric) | (intros; apply GlobalTheory.RSThetaGeom.integral_low_geometric  <;> assumption)
end

