module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralFourierCoeffClassIndicatorLevelPoint
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovInt

open IsDedekindDomain

def intZ (D : D7) {H : Host D.host.E} (Dw : Datum H) (l : Level H) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) : ℕ :=
  Nat.card (Fin n → LevQ Dw l) * (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w *
    l.M ^ Formalism.L2.Pj.DF Dw w

theorem intZ_eq (D : D7) {H : Host D.host.E} (Dw : Datum H) (l : Level H) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) :
    intZ D Dw l n w = l.M ^ (Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) * n) *
      (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w * l.M ^ Formalism.L2.Pj.DF Dw w := by
  rw [intZ, GlobalTheory.PlaceInt.card_fun_levQ]

theorem sum_padicValNat_mul_le (v : ℕ → ℤ) (hv : ∀ a b, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b) (h0 : ∀ a, 0 ≤ v a)
    {N : ℕ} (hN : N ≠ 0) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, (padicValNat p N : ℤ) * v p ≤ v N := by
  classical
  have h1 : v 1 = 0 := by have := hv 1 1 one_ne_zero one_ne_zero; rw [Nat.mul_one] at this; omega
  have key : ∀ N : ℕ, N ≠ 0 → ∑ p ∈ s, (padicValNat p N : ℤ) * v p ≤ v N := by
    intro N
    induction N using Nat.recOnMul with
    | zero => exact fun h => absurd rfl h
    | one => intro _; simp [Nat.padicValNat_def, h1]
    | prime l hl =>
      intro _
      have : ∀ p ∈ s, (padicValNat p l : ℤ) * v p = if p = l then v l else 0 := by
        intro p hp
        haveI := Fact.mk (hs p hp)
        haveI := Fact.mk hl
        split_ifs with h
        · subst h; simp [Nat.padicValNat_def, Nat.Prime.multiplicity_self]
        · simp [Nat.padicValNat_def, multiplicity_primes h]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs
      exacts [le_rfl, h0 _]
    | mul a b iha ihb =>
      intro hab
      have ha := left_ne_zero_of_mul hab
      have hb := right_ne_zero_of_mul hab
      have : ∀ p ∈ s, (padicValNat p (a * b) : ℤ) * v p = (padicValNat p a : ℤ) * v p + (padicValNat p b : ℤ) * v p := by
        intro p hp
        haveI := Fact.mk (hs p hp)
        rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) ha hb]; push_cast; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hv a b ha hb]
      exact add_le_add (iha ha) (ihb hb)
  exact key N hN

theorem ram_sum_le_vV_discr (E : Type) [Field E] [NumberField E] (T : CDVR) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (e X : ℕ) :
    ∑ p ∈ s, (vV T.V (p : T.Fr) : ℝ) / e *
        ((padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ)) * (X : ℝ) / 2 ≤
      (vV T.V (((NumberField.discr E).natAbs ^ X : ℕ) : T.Fr) : ℝ) / e := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  have hN : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
  have h0 : ∀ a : ℕ, 0 ≤ vV T.V (a : T.Fr) := fun a => GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T a
  have h1 := sum_padicValNat_mul_le (fun a => vV T.V (a : T.Fr))
    (fun a b ha hb => by
      simp only [Nat.cast_mul]
      exact vV_mul (Nat.cast_ne_zero.2 ha) (Nat.cast_ne_zero.2 hb)) h0 hN s hs
  have h2 : ∑ p ∈ s, (padicValNat p (NumberField.discr E).natAbs : ℝ) * (vV T.V (p : T.Fr) : ℝ) ≤
      (vV T.V (((NumberField.discr E).natAbs : ℕ) : T.Fr) : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).2 h1
    rw [Int.cast_sum] at h
    simpa only [Int.cast_mul, Int.cast_natCast] using h
  have hk : (1 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))
  rw [Nat.cast_pow, GlobalTheory.ShortBound.vV_pow (Nat.cast_ne_zero.2 hN), Int.cast_mul, Int.cast_natCast]
  have hX : (0 : ℝ) ≤ (X : ℝ) / e := by positivity
  refine le_trans ?_ ((mul_le_mul_of_nonneg_left h2 hX).trans (le_of_eq (by ring)))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h3 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast h0 p
  have h4 : (padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) ≤
      (padicValNat p (NumberField.discr E).natAbs : ℝ) := div_le_self (Nat.cast_nonneg _) hk
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hX h3)
  have h6 : (0 : ℝ) ≤ (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) * (padicValNat p (NumberField.discr E).natAbs : ℝ) :=
    mul_nonneg (mul_nonneg hX h3) (Nat.cast_nonneg _)
  calc _ = (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) *
        ((padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ)) / 2 := by ring
    _ ≤ (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) * (padicValNat p (NumberField.discr E).natAbs : ℝ) := by linarith
    _ = _ := by ring

theorem log_discr_natAbs_le (E : Type) [Field E] [NumberField E] :
    Real.log ((NumberField.discr E).natAbs : ℝ) ≤ (Module.finrank ℚ E : ℝ) * fieldSz E := by
  have hk : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))
  have h := (div_le_iff₀ hk).1 (log_rd_le_fieldSz E)
  rw [Nat.cast_natAbs, Int.cast_abs]
  linarith

theorem isIntegral_fourierCoeff_classIndicator_levelPoint {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) (hM : l.M ≠ 0) {n : ℕ} (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw l) : IsIntegral ℤ (x0Dat c x0 q) := by
  unfold x0Dat
  refine ⟨Polynomial.X ^ l.M - 1, Polynomial.monic_X_pow_sub_C 1 hM, ?_⟩
  have h1 : zetaM c ^ l.M = 1 := GlobalTheory.Survey.BaseClassMove.zetaM_pow c
  have h2 : (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b))) ^ l.M = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
  simp [h2]

end GlobalTheory.CovInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedComplexPointsOpenVariety
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts

namespace GlobalTheory.CxConn

variable {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {d : ℕ}

theorem exists_algX_eq [IsProper p] [GeometricallyIntegral p] (a : Γ(Y, ⊤)) : ∃ c : F, algX p ⊤ c = a := by
  have : IsIso p.appTop := ProperFunctions.isIso_appTop_of_field p
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso p.appTop).2 a
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 b
  exact ⟨c, congrArg (fun g : Γ(Sp F, ⊤) ⟶ Γ(Y, ⊤) => g ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c))
    (p.appLE_eq_app (U := ⊤))⟩

theorem eq_of_holoOn_univ [SmoothOfRelativeDimension d p] [IsProper p] [GeometricallyIntegral p]
    (hp : IsProjOver p) (R : AnRead p σ d) {f : CxPts p σ → ℂ} (hf : R.HoloOn univ f) (y z : CxPts p σ) :
    f y = f z := by
  have hs : (fun _ : (Out.Inh.trivLB Y).ι => f) ∈ R.holSec (Out.Inh.trivLB Y) := by
    refine ⟨⟨fun i j w hi hj => ?_, fun i w h => (h mem_ptsIn_top).elim⟩, fun i => hf.mono (subset_univ _)⟩
    have e : gv p σ (Out.Inh.trivLB Y) i j w = 1 :=
      (ev_eq (mem_ptsIn_inf.2 ⟨hi, hj⟩) _).trans (map_one _)
    rw [e, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC hp R (Out.Inh.trivLB_isLB Y)).2 ⟨_, hs⟩
  let L : ((Out.Inh.trivLB Y).ι → CxPts p σ → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => s PUnit.unit y - s PUnit.unit z
      map_add' := fun s t => add_sub_add_comm _ _ _ _
      map_smul' := fun c s => (mul_sub c _ _).symm }
  have h := SecC.val_mem_of (M := LinearMap.ker L) (fun s => by
    obtain ⟨c, hc⟩ := exists_algX_eq (p := p) (s.f PUnit.unit)
    have e (w : CxPts p σ) : secVal p σ s PUnit.unit w = σ c :=
      (congrArg (fun a => ev p σ ⊤ a w) hc.symm).trans (ev_algX mem_ptsIn_top c)
    change secVal p σ s PUnit.unit y - secVal p σ s PUnit.unit z = 0
    rw [e, e, sub_self]) x
  have e : SecC.val x = fun _ : (Out.Inh.trivLB Y).ι => f := congrArg Subtype.val hx
  rw [e] at h
  exact sub_eq_zero.1 h

theorem exists_holoOn_univ_of_local {R : AnRead p σ d} {A : Set (CxPts p σ)} (hA : Dense A) {u : CxPts p σ → ℂ}
    (h : ∀ y, ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ A)) :
    ∃ f, R.HoloOn univ f ∧ EqOn f u A := by
  choose T f hT hy hf he using h
  refine ⟨fun y => f y y, AnRead.holoOn_of_cover (T := T) hT (fun y _ => ⟨y, hy y⟩)
    fun y => ((hf y).mono inter_subset_right).congr fun z hz => ?_, fun y hS => he y ⟨hy y, hS⟩⟩
  have ho := (hT z).inter (hT y)
  have e : EqOn (f z) (f y) (T z ∩ T y ∩ A) := fun w hw =>
    (he z ⟨hw.1.1, hw.2⟩).trans (he y ⟨hw.1.2, hw.2⟩).symm
  exact e.of_subset_closure (((hf z).mono inter_subset_left).continuousOn ho)
    (((hf y).mono inter_subset_right).continuousOn ho) inter_subset_left (hA.open_subset_closure_inter ho)
    ⟨hy z, hz.2⟩

theorem exists_local_extension [GeometricallyIntegral p] [LocallyOfFiniteType p] (R : AnRead p σ d) {W : Y.Opens}
    (hW : (W : Set Y).Nonempty) {u : CxPts p σ → ℂ} (hu : R.HoloOn (ptsIn p σ W) u) {C : ℝ}
    (hC : ∀ y, ‖u y‖ ≤ C) (y : CxPts p σ) :
    ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ ptsIn p σ W) := by
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton p
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  obtain ⟨φ, hφ, hφW⟩ := CxPtsDense.exists_ne_zero_basicOpen_le c.affine
    ⟨_, mem_ptsIn.1 (c.source_subset hi)⟩ hW
  have hD : Dense (ptsIn p σ (Y.basicOpen φ)) := by
    refine (CxPtsDense.nonempty_and_dense_of_geometricallyIntegral p σ).2 _ (nonempty_iff_ne_empty.2 fun h => hφ ?_)
    exact (basicOpen_eq_bot_iff φ).1 (Opens.ext h)
  have hin {z} (hz : z ∈ c.e.source) : z ∈ ptsIn p σ (Y.basicOpen φ) ↔ ev p σ c.U φ z ≠ 0 :=
    mem_ptsIn_basicOpen (c.source_subset hz) φ
  obtain ⟨v, hv, he⟩ := GlobalTheory.LogExt.riemann_extension_log _ c.e.target (ev p σ c.U φ ∘ c.e.symm) (u ∘ c.e.symm)
    c.e.open_target ((c.holo c.U φ).mono fun b hb => ⟨hb, c.source_subset (c.e.map_target hb)⟩)
    ((hu i).mono fun b hb => ⟨hb.1, ptsIn_mono hφW ((hin (c.e.map_target hb.1)).2 hb.2)⟩)
    (fun b hb => by
      have hs := c.e.map_target hb
      have h₁ := hD.open_subset_closure_inter c.e.open_source hs
      have h₂ := (c.e.continuousAt hs).continuousWithinAt.mem_closure_image h₁
      rw [c.e.right_inv hb] at h₂
      refine closure_mono ?_ h₂
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨c.e.map_source hz.1, ?_⟩
      rw [Function.comp_apply, c.e.left_inv hz.1]
      exact (hin hz.1).1 hz.2)
    fun b _ => ⟨C, 0, Eventually.of_forall fun b' _ => by rw [pow_zero, mul_one]; exact hC _⟩
  have hf : R.HoloOn c.e.source (v ∘ c.e) := by
    have := AnRead.holoOn_of_chart (R := R) (S := univ) (f := v ∘ c.e) c
      ((hv.mono inter_subset_left).congr fun b hb => congrArg v (c.e.right_inv hb.1))
    rwa [inter_univ] at this
  refine ⟨c.e.source, v ∘ c.e, c.e.open_source, hi, hf, ?_⟩
  have ho := c.e.open_source.inter (isOpen_ptsIn (p := p) (σ := σ) W)
  have e : EqOn (v ∘ c.e) u (c.e.source ∩ ptsIn p σ W ∩ ptsIn p σ (Y.basicOpen φ)) := fun z hz => by
    have := he (x := c.e z) ⟨c.e.map_source hz.1.1, by
      rw [Function.comp_apply, c.e.left_inv hz.1.1]; exact (hin hz.1.1).1 hz.2⟩
    simpa only [c.e.left_inv hz.1.1, Function.comp_apply] using this
  exact e.of_subset_closure ((hf.mono inter_subset_left).continuousOn ho)
    ((hu.mono inter_subset_right).continuousOn ho) inter_subset_left (hD.open_subset_closure_inter ho)

theorem isPreconnected_ptsIn_of_isProjOver (d : ℕ) [SmoothOfRelativeDimension d p] [IsProper p]
    [GeometricallyIntegral p] (hp : IsProjOver p) (W : Y.Opens) : IsPreconnected (ptsIn p σ W) := by
  refine isPreconnected_of_forall_constant fun g hg y hy z hz => ?_
  have hW : (W : Set Y).Nonempty := ⟨_, mem_ptsIn.1 hy⟩
  let R := AnRead.all (p := p) (σ := σ) (D := d)
  let κ : Bool → ℂ := fun b => if b then 1 else 0
  have hu : R.HoloOn (ptsIn p σ W) (κ ∘ g) := fun i b hb => by
    have h₁ : ContinuousAt (g ∘ (R.chart i).e.symm) b :=
      (hg.continuousAt ((isOpen_ptsIn W).mem_nhds hb.2)).comp ((R.chart i).e.continuousAt_symm hb.1)
    have h₂ : ∀ᶠ b' in 𝓝 b, (g ∘ (R.chart i).e.symm) b' = (g ∘ (R.chart i).e.symm) b :=
      h₁.eventually ((isOpen_discrete _).mem_nhds (mem_singleton _))
    refine ((differentiableAt_const (κ ((g ∘ (R.chart i).e.symm) b))).congr_of_eventuallyEq
      (h₂.mono fun b' hb' => congrArg κ hb')).differentiableWithinAt
  have hC (w) : ‖(κ ∘ g) w‖ ≤ 1 := by
    simp only [Function.comp_apply, κ]
    split_ifs <;> simp
  obtain ⟨f, hf, he⟩ := exists_holoOn_univ_of_local
    ((CxPtsDense.nonempty_and_dense_of_geometricallyIntegral p σ).2 W hW) (exists_local_extension R hW hu hC)
  have e : κ (g y) = κ (g z) := (he hy).symm.trans ((eq_of_holoOn_univ hp R hf y z).trans (he hz))
  revert e
  cases g y <;> cases g z <;> simp [κ]

theorem isPreconnected_ptsIn : ∀ (F : Type) [Field F] [NumberField F] (B : GlobalTheory.ProjVar.Var F) (e : F →+* ℂ)
    (W : B.X.Opens), IsPreconnected (GlobalTheory.CxPts.ptsIn B.str e W) :=
  fun _ _ _ B _ W => isPreconnected_ptsIn_of_isProjOver B.dim B.isProjOver W

end GlobalTheory.CxConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFlatValuationSubringBaseRing
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ValLocal

theorem exists_dvd_away {A : Type} [CommRing A] [IsDedekindDomain A] (q : Ideal A) [q.IsPrime] (a b : A) (hb : b ≠ 0) :
    ∃ s r : A, s ∉ q ∧ (s * a = r * b ∨ s * b = r * a) := by
  by_cases hq : q = ⊥
  · exact ⟨b, a, by simpa [hq] using hb, Or.inl (mul_comm _ _)⟩
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have key : ∀ (u v : A) (z : Localization.AtPrime q), algebraMap A _ u * z = algebraMap A _ v →
      ∃ s r : A, s ∉ q ∧ s * v = r * u := by
    intro u v z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj q.primeCompl z
    refine ⟨s, r, s.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hrs]
    ring
  obtain ⟨z, hz | hz⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime q) a) (algebraMap A _ b)
  · obtain ⟨s, r, hs, h⟩ := key a b z hz
    exact ⟨s, r, hs, Or.inr h⟩
  · obtain ⟨s, r, hs, h⟩ := key b a z hz
    exact ⟨s, r, hs, Or.inl h⟩

theorem exists_integral_frac {F : Type} [Field F] [NumberField F] (W : ValuationSubring F) (x : W) :
    ∃ a s : W, IsIntegral ℤ (a : F) ∧ IsIntegral ℤ (s : F) ∧ IsUnit s ∧ x * s = a := by
  have hmem : ∀ y : 𝓞 F, (y : F) ∈ W := fun y => by
    have h : IsIntegral W (y : F) := y.isIntegral_coe.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
    rw [← hz]
    exact z.2
  let φ : 𝓞 F →+* W := (algebraMap (𝓞 F) F).codRestrict W.toSubring hmem
  have hφ : ∀ y : 𝓞 F, ((φ y : W) : F) = (y : F) := fun _ => rfl
  let q : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal W).comap φ
  have hunit : ∀ s : 𝓞 F, s ∉ q → IsUnit (φ s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (x : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : (b : F) ≠ 0 := by exact_mod_cast hb0
  have hxb : (x : F) * b = a := by
    rw [← hx]
    exact div_mul_cancel₀ _ hbF
  obtain ⟨s, r, hs, h | h⟩ := exists_dvd_away q a b hb0
  · refine ⟨φ r, φ s, r.isIntegral_coe, s.isIntegral_coe, hunit s hs, Subtype.ext ?_⟩
    have h' : (s : F) * a = r * b := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    show (x : F) * s = r
    apply mul_right_cancel₀ hbF
    rw [← h', ← hxb]
    ring
  · have h' : (s : F) * b = r * a := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    have hxr : x * φ r = φ s := by
      apply Subtype.ext
      show (x : F) * r = s
      apply mul_right_cancel₀ hbF
      rw [h', ← hxb]
      ring
    exact ⟨φ s, φ r, s.isIntegral_coe, r.isIntegral_coe,
      isUnit_of_mul_isUnit_right (hxr ▸ hunit s hs), hxr⟩

theorem preimmersion_flat :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  intro E _ _ _ H l c O _ β hβ W b hb
  haveI := c.fin
  haveI : NumberField c.F := {}
  letI : Algebra O W := b.toAlgebra
  have hbv : ∀ o : O, ((b o : W) : c.F) = β o := fun o => by rw [← hb]; rfl
  have hinj : Function.Injective b := fun u v h => hβ.1 (by rw [← hbv, ← hbv, h])
  let S : Submonoid O := (IsUnit.submonoid W).comap b
  haveI : IsLocalization S W := by
    refine (isLocalization_iff S W).2 ⟨fun y => y.2, fun z => ?_, fun {u v} h => ⟨1, by rw [hinj h]⟩⟩
    obtain ⟨a, s, ha, hs, hu, hz⟩ := exists_integral_frac W z
    obtain ⟨a', ha'⟩ := hβ.2 _ ha
    obtain ⟨s', hs'⟩ := hβ.2 _ hs
    have e1 : b a' = a := Subtype.ext (by rw [hbv, ha'])
    have e2 : b s' = s := Subtype.ext (by rw [hbv, hs'])
    refine ⟨⟨a', ⟨s', ?_⟩⟩, ?_⟩
    · show IsUnit (b s')
      rwa [e2]
    · show z * b s' = b a'
      rw [e1, e2, hz]
  refine ⟨IsPreimmersion.of_isLocalization (R := O) (S := W) S, ?_⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact (RingHom.flat_algebraMap_iff (R := O) (S := W)).2 (IsLocalization.flat W S)

end GlobalTheory.ValLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnipotentModIdealLiftLaInv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

theorem unipAt_inv_liftLa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (I : Ideal (𝓞 E)) («γ» : LevelAut Dw l), l.Mb ≤ I → UnipAt I «γ» → ∃ m : ℕ, ∀ x : Dw.La, ((liftLa «γ»⁻¹ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  intro E _ _ _ H Dw l I γ hI hU
  obtain ⟨m, hm⟩ := hU
  set M : Submodule (𝓞 E) Dw.La := I • ⊤ with hMdef
  set f := liftLa γ with hfdef
  set g := liftLa γ⁻¹ with hgdef
  have hN : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤ M := Submodule.smul_mono_left hI
  have hpres : ∀ φ : Dw.La →ₗ[𝓞 E] Dw.La, M ≤ M.comap φ := by
    intro φ
    rw [← Submodule.map_le_iff_le_comap, hMdef, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hgf : ∀ x, g (f x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec (γ⁻¹) (f x)
    have h2 := liftLa_spec γ x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hgdef, h1, hfdef, h2]
    exact γ.symm_apply_apply _
  have hfg : ∀ x, f (g x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec γ (g x)
    have h2 := liftLa_spec (γ⁻¹) x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hfdef, h1, hgdef, h2]
    exact γ.apply_symm_apply _
  let A := M.mapQ M f (hpres f)
  let B := M.mapQ M g (hpres g)
  have hBA : B * A = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hgf x)
  have hAB : A * B = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hfg x)
  have hdesc : ∀ (φ : Dw.La →ₗ[𝓞 E] Dw.La) (k : ℕ) (x : Dw.La),
      M.mkQ (((φ - 1) ^ k) x) = ((M.mapQ M φ (hpres φ) - 1) ^ k) (M.mkQ x) := by
    intro φ k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
  have hA0 : (A - 1) ^ m = 0 := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [← Submodule.mkQ_apply, ← hdesc f m x, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hm x
  have hcomm : Commute B (1 - A) := by
    refine Commute.sub_right (Commute.one_right B) ?_
    exact (hBA.trans hAB.symm)
  have hB0 : (B - 1) ^ m = 0 := by
    have e : B - 1 = B * (1 - A) := by rw [mul_sub, mul_one, hBA]
    rw [e, hcomm.mul_pow, show (1 - A) = -(A - 1) by abel, neg_pow, hA0, mul_zero, mul_zero]
  refine ⟨m, fun x => ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hdesc g m x, hB0, LinearMap.zero_apply]

end GlobalTheory.OrbitSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreOfEtaleRestriction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem isolated_in_fibre_of_etale_restrict :
    ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : W.Opens), Etale (f ∣_ U) → ∀ z : M, f z ∈ U →
      ∃ V : M.Opens, z ∈ V ∧ ∀ y ∈ V, f y = f z → y = z := by
  intro M W f U hE z hz
  haveI : LocallyQuasiFinite (f ∣_ U) := by
    refine ⟨fun {U'} hU {V} hV e => ?_⟩
    have h := Scheme.Hom.etale_appLE (f ∣_ U) hU hV e
    algebraize [((f ∣_ U).appLE U' V e).hom]
    exact RingHom.quasiFinite_algebraMap.mpr inferInstance
  let z' : (f ⁻¹ᵁ U : M.Opens) := ⟨z, hz⟩
  obtain ⟨u, hu, huz⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    ((f ∣_ U).isDiscrete_preimage_singleton ((f ∣_ U) z')) z' rfl
  refine ⟨⟨Subtype.val '' u, (f ⁻¹ᵁ U).isOpen.isOpenMap_subtype_val u hu⟩, ⟨z', ?_, rfl⟩, ?_⟩
  · have : z' ∈ u ∩ (f ∣_ U) ⁻¹' {(f ∣_ U) z'} := by rw [huz]; rfl
    exact this.1
  · rintro y ⟨y', hy'u, rfl⟩ hy
    have hmem : y' ∈ u ∩ (f ∣_ U) ⁻¹' {(f ∣_ U) z'} := by
      refine ⟨hy'u, ?_⟩
      have h1 := morphismRestrict_base_coe f U y'
      have h2 := morphismRestrict_base_coe f U z'
      exact Subtype.ext (h1.trans (hy.trans h2.symm))
    rw [huz] at hmem
    exact congrArg Subtype.val hmem

end GlobalTheory
end

