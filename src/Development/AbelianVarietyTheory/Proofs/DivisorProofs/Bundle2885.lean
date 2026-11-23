module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudPointUnitPartCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismProjSpaceBasepointFreeSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSAmp.GenMap

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem mem_chart {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
  Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))

theorem loc_mul_div (P : Pair p) (e : ℕ) (f ρ : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc e 0 f i j * (ρ / P.loc e 0 1 i j) = f * ρ := by
  have := (P.r i).ne_zero
  have := (P.r' j).ne_zero
  simp only [Pair.loc]
  field_simp

theorem loc_eq_mul_inv (P : Pair p) (e : ℕ) (f ρ : X.functionField) (hρ : ρ ≠ 0) (i : P.L.B.ι)
    (j : P.A.B.ι) : P.loc e 0 f i j = f * ρ * (ρ / P.loc e 0 1 i j)⁻¹ := by
  have := (P.r i).ne_zero
  have := (P.r' j).ne_zero
  simp only [Pair.loc]
  field_simp

theorem exists_secs (P : Pair p) {D e : ℕ} {x : Fin (D + 1) → X.functionField} (hx : Gens P D e x) :
    ∃ (ρ : (P.L.pow e).B.ι → X.functionFieldˣ) (s : Fin (D + 1) → (P.L.pow e).B.Sec),
      (∀ z c i j, z ∈ (P.L.pow e).B.U c → z ∈ P.L.B.U i → z ∈ P.A.B.U j →
        UnitAt z ((ρ c : X.functionField) / P.loc e 0 1 i j)) ∧
      (∀ (σ : k →+* ℂ) (y : CxPts p σ) c j, y ∈ ptsIn p σ ((P.L.pow e).B.U c) → y ∈ ptsIn p σ (P.A.B.U j) →
        ‖ratVal ((ρ c : X.functionField) / P.loc e 0 1 (c PUnit.unit) j) y‖ = 1) ∧
      ∀ l c (hc : genericPoint X ∈ (P.L.pow e).B.U c), fnOf _ hc ((s l).f c) = x l * ρ c := by
  obtain ⟨ρ, hρ, hu, hn⟩ := Pair.rep_pow k X p P 1 0 P.L e (Pair.rep_base k X p P).1
  simp only [mul_one, mul_zero] at hu hn
  have hs : ∀ l, ∃ u : (P.L.pow e).B.Sec, ∀ c (hc : genericPoint X ∈ (P.L.pow e).B.U c),
      fnOf _ hc (u.f c) = x l * ρ c := fun l =>
    RepDict.exists_sec hρ fun c z hz => by
      obtain ⟨i, hi⟩ := mem_chart P.L.isLB z
      obtain ⟨j, hj⟩ := mem_chart P.A.isLB z
      rw [← loc_mul_div P e (x l) _ i j]
      exact (hx.mem l z i j hi hj).mul (hu z c i j hz hi hj).regAt
  choose s hs using hs
  refine ⟨ρ, s, hu, fun σ y c j hc hj => ?_, hs⟩
  have hc' := mem_pow_iff.1 hc
  have hU := hu _ c _ j (mem_ptsIn.1 hc) (mem_ptsIn.1 hc') (mem_ptsIn.1 hj)
  have h1 := hn σ y c _ j hc hc' hj
  have h2 : ((P.L.pow e).φ σ).φ c y = ((e : ℤ) : ℝ) * (P.L.φ σ).φ (c PUnit.unit) y := Weight.zpow_φ _ _ _ _
  rw [h2] at h1
  push_cast at h1
  refine Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 (ratVal_ne_zero hU)) ?_
  linarith

end GlobalTheory.HSAmp.GenMap

namespace GlobalTheory.HSAmp.GenMap

theorem toProj_gens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → x 0 ≠ 0 → ∃ (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  intro k _ X _ p D _ P e x hx hx0
  obtain ⟨ρ, s, hu, hn1, hs⟩ := exists_secs P hx
  have hnz : ∀ l z i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j →
      (z ∈ Out.nonzeroLocus (s l) ↔ UnitAt z (P.loc e 0 (x l) i j)) := by
    intro l z i j hi hj
    obtain ⟨c, hc⟩ := mem_chart (P.L.pow e).isLB z
    have hU := hu z c i j hc hi hj
    rw [mem_nonzeroLocus_iff (s l) c hc, ← unitAt_fnOf_iff hc (gen_mem hc), hs l c (gen_mem hc)]
    exact ⟨fun h => loc_eq_mul_inv P e (x l) _ (ρ c).ne_zero i j ▸ h.mul hU.inv,
      fun h => loc_mul_div P e (x l) _ i j ▸ h.mul hU⟩
  have hcov : ⨆ l, Out.nonzeroLocus (s l) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨i, hi⟩ := mem_chart P.L.isLB z
    obtain ⟨j, hj⟩ := mem_chart P.A.isLB z
    obtain ⟨l, hl⟩ := hx.cover z
    exact Opens.mem_iSup.2 ⟨l, (hnz l z i j hi hj).2 (hl i j hi hj)⟩
  obtain ⟨c, hc⟩ := mem_chart (P.L.pow e).isLB (genericPoint X)
  have hη : genericPoint X ∈ Out.nonzeroLocus (s 0) := by
    rw [mem_nonzeroLocus_iff (s 0) c hc, X.mem_basicOpen _ _ hc]
    show IsUnit (fnOf _ hc ((s 0).f c))
    rw [hs 0 c hc]
    exact isUnit_iff_ne_zero.2 (mul_ne_zero hx0 (ρ c).ne_zero)
  have hpre := ProjSpace.toProj_preimage_chart p s hcov 0
  have hmem : genericPoint X ∈ ProjSpace.toProj p s hcov ⁻¹ᵁ ProjSpace.chart k D 0 := by
    rw [hpre]; exact hη
  refine ⟨ProjSpace.toProj p s hcov, ProjSpace.toProj_str p s hcov, ⟨hmem, fun j => ?_⟩, fun u hu' => ?_⟩
  · change fnOf _ hmem _ = _
    rw [ProjSpace.pullRatio_toProj_on p s hcov 0 j le_rfl, fnOf_resG]
    have hc' : genericPoint X ∈ Out.nonzeroLocus (s 0) ⊓ (P.L.pow e).B.U c := ⟨hη, hc⟩
    have e1 := congrArg (fnOf _ hc') (ProjSpace.secRatio_spec (s 0) (s j) c)
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hs j c hc, hs 0 c hc] at e1
    rw [eq_div_iff hx0]
    refine mul_right_cancel₀ (ρ c).ne_zero ?_
    linear_combination -e1
  · have he : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hx.pos.ne'
    refine (HermLB.isometric_pull_fs_toProj k X p ((up P.L u).pow e) D s hcov (fun _ => 1) (fun _ => by simp)
      (fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩) ?_).symm
    intro σ i y hy
    change y ∈ ptsIn p σ ((P.L.pow e).B.U i) at hy
    have hy' : y ∈ ptsIn p σ (P.L.B.U (i PUnit.unit)) := mem_pow_iff.1 hy
    have hj : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
    have hg := hn1 σ y i _ hy hj
    have hA : ∀ l, ‖valR y.1 ((P.L.pow e).B.U i) ((s l).f i)‖ =
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ := fun l => by
      have hη := gen_mem (mem_ptsIn.1 hy)
      change ‖ev p σ _ ((s l).f i) y‖ = _
      rw [← ratVal_fnOf hy hη, hs l i hη, ← loc_mul_div P e (x l) _ (i PUnit.unit) _,
        ratVal_mul (hx.mem l _ _ _ (mem_ptsIn.1 hy') (mem_ptsIn.1 hj))
          (hu _ i _ _ (mem_ptsIn.1 hy) (mem_ptsIn.1 hy') (mem_ptsIn.1 hj)).regAt, norm_mul, hg, mul_one]
    have hnu : ∀ l, P.nu e 0 σ y (x l) ^ 2 =
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2 *
          Real.exp (-((e : ℝ) * (P.L.φ σ).φ (i PUnit.unit) y)) := fun l => by
      rw [nu_eq k X p P e 0 (x l) (hx.mem l) σ y _ _ hy' hj, mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    set S := ∑ l, ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2 with hS
    have hSpos : 0 < S := by
      obtain ⟨l, hl⟩ := hx.cover (under y)
      have h0 := norm_pos_iff.2 (ratVal_ne_zero (hl _ _ (mem_ptsIn.1 hy') (mem_ptsIn.1 hj)))
      exact (pow_pos h0 2).trans_le (Finset.single_le_sum (f := fun l =>
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ l))
    have hsum : ∑ l, P.nu e 0 σ y (x l) ^ (2 * 1) = Real.exp (-((e : ℝ) * (P.L.φ σ).φ (i PUnit.unit) y)) * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_one, hnu l, mul_comm]
    have hu1 := hu' σ y
    rw [hsum, Real.log_mul (Real.exp_pos _).ne' hSpos.ne', Real.log_exp] at hu1
    change (((P.L.φ σ).addFn (u.u σ)).zpow (e : ℤ)).φ i y = _
    refine (Weight.zpow_φ _ _ _ _).trans ?_
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    change ((e : ℤ) : ℝ) * ((P.L.φ σ).φ (i PUnit.unit) y + u.u σ y) =
      Real.log (∑ l, ‖valR y.1 ((P.L.pow e).B.U i) ((s l).f i)‖ ^ 2)
    simp only [hA, ← hS]
    rw [hu1]
    push_cast
    field_simp
    ring

end GlobalTheory.HSAmp.GenMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIntegralCompletedHomLattice
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CosetOrth.LatInt

theorem exists_pow_mem (D : D7) : ∃ k : ℕ, (((D.host.QS * D.host.q) ^ k : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟 := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hJ, hp⟩
    have hne : J ≠ ⊥ := fun e => hb (le_bot_iff.1 (e ▸ hJ))
    exact GlobalTheory.HalfCompare.two_q_mem (P := ⟨J, hp, hne⟩) (Ideal.dvd_iff_le.2 hJ)
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [Nat.cast_pow]; exact hk⟩

theorem homL_entry {D : D7} {N N' : ℕ} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    have h1 : (Pi.single j (1 : D.host.E) : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
      intro l _
      by_cases h : l = j
      · subst h
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h2 := hA _ h1 i trivial
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem YYl_entry {D : D7} {N N' : ℕ} {B : Matrix (Fin N') (Fin N) D.host.E}
    (hB : B ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    B i j ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (homL_entry hA i j)
    have : (a • A) i j = c • a := by
      rw [Matrix.smul_apply, smul_eq_mul, ← hc, Algebra.smul_def, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ c ha
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem mul_int {D : D7} {n : 𝓞 D.host.E} (hn : n ∈ D.host.𝔟) {x : D.host.E}
    (hx : x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = algebraMap (𝓞 D.host.E) D.host.E n * x := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h1 : algebraMap (𝓞 D.host.E) D.host.E n * x ∈
      (D.host.𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0 :=
    FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hn) hx
  rw [Formalism.BasicNotions.Host.AA0, mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb)] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

theorem inHat_tmul {D : D7} {α : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (c x : D.host.E) (b : 𝓞 D.host.E)
    (hb : algebraMap (𝓞 D.host.E) D.host.E b = c * x) :
    InHat 1 (algebraMap D.host.E (FA D) c * fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x)) := by
  have e : fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E α * algebraMap D.host.E (FA D) x := rfl
  rw [e, mul_left_comm, ← map_mul, ← hb]
  refine InHat.mul_left ((inHat_one_iff _).2 fun w => ?_) ((inHat_one_iff _).2 fun w => ?_)
  · exact GlobalTheory.AdeleBaseChange.adMap_int (F := D.host.F) (E := D.host.E) hα w
  · change Valued.v ((algebraMap (𝓞 D.host.E) D.host.E b : D.host.E) : w.adicCompletion D.host.E) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact w.valuation_le_one b

theorem exists_hatPt_of_mem_latO : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (LB : Lat T), r ≠ 0 →
  (∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finPt (S := S) (T := T) rfl rfl r z ∈ (latO S T (stdLat S) LB fun _ => True) →
    z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank)) →
  ∃ k : ℕ, ∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) 1 u := by
  intro D S T r LB hr hz
  obtain ⟨k, hk⟩ := exists_pow_mem D
  refine ⟨k, fun u hu => ⟨Matrix.ext fun i j => GlobalTheory.LatVac.infPart_of_mem hu i j, fun i j => ?_⟩⟩
  refine GlobalTheory.LatVac.latO_induction (p := fun u => InHat 1
    (algebraMap D.host.E (FA D) ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) * fe D (u i j))) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h1 := GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hM
    have e : finPt (S := S) (T := T) rfl rfl r (-r • M) = GlobalTheory.LatVac.finTens 1 M := by
      have : (Matrix.of fun i j => -(r⁻¹ * (-r • M) (Fin.cast rfl i) (Fin.cast rfl j))) = M := by
        ext i j
        simp [hr]
      unfold finPt
      rw [this]
      rfl
    obtain ⟨b, hb⟩ := mul_int hk (YYl_entry (hz _ (e ▸ h1)) i j)
    refine inHat_tmul hα _ _ (-b) ?_
    rw [map_neg, hb, map_natCast, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [Matrix.zero_apply, map_zero, mul_zero]
    exact inHat_zero _
  · intro x y hx hy
    rw [Matrix.add_apply, map_add (f := _), mul_add]
    exact hx.add hy
  · intro x hx
    rw [Matrix.neg_apply, map_neg, mul_neg]
    exact hx.neg

end GlobalTheory.CosetOrth.LatInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipallyPolarisedPowerUnimodularForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensPow

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower GlobalTheory.MumFam GlobalTheory.MumFam.TensPol

theorem exists_pow_data_polAV : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ LBIso P'.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)) := by
  intro R _ _ _ _ Q r W hpd hdet
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := siegLamData hG Q
  have hP : c.P.IsLB := c.isLB
  have hD : c.diag.IsLB := pull_isLB hP _
  have hamp : RelAmple c.A c.diag := relAmple_diag Q hD
  let G := Out.powObj Q.B r
  let pr : Fin r → (G ⟶ Q.B) := Out.powPr Q.B
  have hpr : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have hu : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ Q.B)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit Q.B r).lift (Fan.mk T y), fun u => (Out.powIsLimit Q.B r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit Q.B r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hB : ∀ (T : Over (Sp R)) (x x' y : T ⟶ c.A), bi hP (x * x') y = bi hP x y + bi hP x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2
      (GlobalTheory.T.biadditive_of_trivial_on_axes hG (Sp R) c.A c.diag c.ab hD hamp c.P hP c.rig₁ c.rig₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [bi]
    abel
  have hs : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), bi hP x y = bi hP y x := fun T x y => by
    have e : cls c.P hP = bi hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    rw [bi, e, pull_bi, lift_fst, lift_snd]
  have hLB : (sharp c.P pr W).IsLB := LB.isLB_linComb hP _ _
  refine ⟨{ A := G
            isAb := isAbelianScheme_powObj_of_isAbelianScheme Q.B Q.isAb r
            g := r * Q.g
            smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ r Q.smoothDim
            L := sharp c.P pr W
            isLB := hLB
            rigid := rigidified_sharp hP pr W hpr hB
            sym := sym_sharp hP pr W hpr hB hs
            ample := GlobalTheory.T.relAmple_formBundle_power_of_posDef hG 0 1 r R 1 (Sp R) (𝟙 _) c G pr W hpr hu hamp hpd
            ktriv := kTriv_sharp hP pr W hpr hB hs hu (GlobalTheory.Mum.PowPol.det_eq_one W hpd hdet)
              (fun T x hx => eq_one_of_lam Q.M.isLB Q.ktriv x hx) }, pr, hpr, ⟨Out.powIsLimit Q.B r⟩, ?_⟩
  refine lbIso_nested Q.M.isLB _ _ (fun uv : Fin r × Fin r => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ _ ?_
  simp only [prod_lam (pr _) (pr _) (PrimNorm.cls Q.M.L)]
  rw [Fintype.prod_prod_type (f := fun k : (Fin r × Fin r) × Fin 4 => PrimNorm.cls Q.M.L (tensφ pr k) ^ tensε W k)]
  refine Finset.prod_congr rfl fun uv _ => ?_
  simp only [Fin.prod_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, diff₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, zpow_mul]
  simp only [zpow_one, zpow_neg, mul_zpow, inv_zpow]

end GlobalTheory.Mum.TensPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudGaugeGeneratorWeightNegStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_raynaudGauge_generator_weight_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (mu : Q.X) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), (x ≫ Y.q) * Q.c mu = 1 → ∀ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1), ψ₀.IsGen → ∃ e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1]), e.IsGen ∧ (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y (-mu) (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J = 1 := by
  first | exact @GlobalTheory.Heat.ShiftGauge.exists_gauge | exact GlobalTheory.Heat.ShiftGauge.exists_gauge | (intros; apply GlobalTheory.Heat.ShiftGauge.exists_gauge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudPointUnitPartCoordinatesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_raynaudPoint_unitPart_coordinates : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), Q.TauBimult → (∀ i, t i ≠ 0) → ∀ (n : Q.X → Fin m → ℕ), (∀ χ i, gam i χ χ = 2 * n χ i) → ∀ (ψ₀ : ∀ χ : Q.X, LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1)), (∀ χ, (ψ₀ χ).IsGen) → (∀ χ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n χ i) * (val (ψ₀ χ) (r ≫ jK R) z J).val) → ∀ mu : Q.X, ∃ xp : 𝟙_ (Over (Sp R)) ⟶ Y.H, xp ≫ Y.q = Q.c mu ∧ ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (χ : Q.X) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z (∏ i, t i ^ n (mu + χ) i) * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s χ) (𝟙 Z) z J).val = cst (g ≫ jK R) z (∏ i, t i ^ (n mu i + n χ i)) * (val (Q.tau mu χ) g z J).val := by
  first | exact @GlobalTheory.UnitPartPt.exists_unitPartPt | exact GlobalTheory.UnitPartPt.exists_unitPartPt | (intros; apply GlobalTheory.UnitPartPt.exists_unitPartPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerMulGlobalFunction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecSmul

theorem map_resTop {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (c : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resTop U c) = resTop V c := by
  simp only [resTop]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_smul : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (c : Γ(X, ⊤)),
    ∃ σ'' : SecM (𝟙 X) L k, ∀ j, σ''.f j = resTop _ c * σ.f j := by
  intro X L k σ c
  refine ⟨⟨fun j => resTop _ c * σ.f j, fun i j => ?_⟩, fun j => rfl⟩
  rw [map_mul, map_mul, σ.compat i j, map_resTop, map_resTop]
  ring

end GlobalTheory.SecSmul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackPowerBundleScalarOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecRestr

theorem exists_restr : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k), ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ 1 := by
  intro X₂ Y L₂ f₂ k σ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.TG.pullSec' L₂ _ _ σ f₂ (fun _ => f₂) (fun _ => (Category.comp_id _).symm), ?_⟩
  intro j₁ j₂ hc
  have hj : j₁ = j₂ := funext fun i => by
    rw [Subsingleton.elim i 0]
    exact hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm
  subst hj
  rw [ReciprocityTheory.ChartRestriction.G.DVR.TG.pullSec'_f]
  have h1 : ReciprocityTheory.ChartRestriction.G.Out.resTop (LB.wchart L₂ (fun _ : Fin 1 => f₂) j₁ ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂ ≫ 𝟙 X₂) j₁) (1 : Γ(Y, ⊤)) = 1 := map_one _
  rw [h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.SecRestr
end
end

