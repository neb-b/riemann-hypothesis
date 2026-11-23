module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0074
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0069
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0030
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0079

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatTwist
section
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hermLine_eq_of_a_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {A B : HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp_all

theorem exists_tensorPow_last {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} (hW : IsArithVar W (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) {B : HermLine ι} (hB : IsSmoothHerm B) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : HermLine ι, IsSmoothHerm C ∧ (∀ k, C.a k = m * B.a k) ∧ (∀ z, C.h z = B.h z ^ m) ∧
      I W (n + 1) (Fin.snoc L C) = m * I W (n + 1) (Fin.snoc L B) := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨B, hB, by simp, by simp, by simp⟩
  | succ m hm ih =>
    obtain ⟨C, hC, ha, hh, hi⟩ := ih
    refine ⟨C.tensor B, ContDiffOn.mul hC hB, fun k => ?_, fun z => ?_, ?_⟩
    · simp only [HermLine.tensor, Pi.add_apply, ha]
      push_cast
      ring
    · simp only [HermLine.tensor, hh, pow_succ]
    · rw [hI.2.1 W n L C B hW hL hC hB, hi]
      push_cast
      ring

theorem IsUnitSec.mono {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {f g : MRing ι} (h : IsUnitSec P f g) (hPW : P ≤ W) : IsUnitSec W f g := by
  intro W' h1 h2 h3
  obtain ⟨a, b, ha, hb, hab⟩ := h W' h1 (hPW.trans h2) h3
  exact ⟨a, b, ha, hb, hPW hab⟩

theorem FlatHerm.inter_eq_neg_integral : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type)
    [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (u : ((Σ k, ι k) → ℂ) → ℝ),
    IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W →
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsPlaceWeight y φ (fun σ => Real.log (S.κ σ)) u →
    I W (n + 1) (Fin.snoc L A) = -ptsIntegral W (pot L) u := by
  intro K _ ι _ Ω _ F _ _ y φ I W n L A S d u hI hP hY hPW hW hL hA hu
  have hnu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → (fun z => -u z) (fun p => c p.1 * z p) = (fun z => -u z) z :=
    fun c z hc => by simp only [hu.inv c z hc]

  set B : HermLine ι := A.tensor (HermLine.ofWeight (fun z => -u z) hnu) with hBdef
  have hBh : ∀ z, B.h z = A.h z * Real.exp (u z) := fun z => by
    simp [hBdef, HermLine.tensor, HermLine.ofWeight]
  have hBa : ∀ k, B.a k = A.a k := fun k => by
    simp [hBdef, HermLine.tensor, HermLine.ofWeight]
  have hexp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.exp (u z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    Real.contDiff_exp.comp_contDiffOn hu.smooth
  have hB : IsSmoothHerm B := by
    have e : B.h = fun z => A.h z * Real.exp (u z) := funext hBh
    unfold IsSmoothHerm
    rw [e]
    exact ContDiffOn.mul hA hexp
  have hBA : B.tensor (HermLine.ofWeight u hu.inv) = A := by
    refine hermLine_eq_of_a_h ?_ ?_
    · funext k
      simp [HermLine.tensor, HermLine.ofWeight, hBa]
    · funext z
      have : (B.tensor (HermLine.ofWeight u hu.inv)).h z = B.h z * Real.exp (-u z) := rfl
      rw [this, hBh, mul_assoc, ← Real.exp_add]
      simp
  have hchange : I W (n + 1) (Fin.snoc L A) = I W (n + 1) (Fin.snoc L B) - ptsIntegral W (pot L) u := by
    have := metricChange K ι I hI W n L B u hu.inv hW hL hB hu.smooth
    rwa [hBA] at this

  obtain ⟨C, hC, hCa, hCh, hCI⟩ := exists_tensorPow_last hI hW hL hB (m := S.M) S.M_pos
  obtain ⟨f', g', df', dg', hf', hg', hdeg, hfW, hgW, -, hun, hnorm⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.exists_rep K ι Ω F y φ A S d W hY hP hA hW.2.1 hPW
  have hunW := IsUnitSec.mono hun hPW
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.unit_section_divisor_eq K ι W f' g' hunW
  have hvert := _root_.GlobalTheory.CompanionTheory.Ar.Flat.vertical_holds K ι I hI W n L C f' g' hW hL hC
    ⟨df', dg', hf', hg', hfW, hgW, fun k => by rw [hdeg k, hCa k, hBa k]⟩
    (fun W' _ => by rw [c1]) (fun W' _ hm => c2 W' hm) (fun z hz => by
      have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
      obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K ι Ω F y φ hY z hzP
      have hz1 : u z = Real.log (S.κ σ) := (hu.near σ z hσ).self_of_nhds
      have hn := hnorm σ z hσ
      have hCz : C.h z = (S.κ σ * A.h z) ^ S.M := by
        rw [hCh, hBh, hz1, Real.exp_log (S.κ_pos σ), mul_comm]
      rw [hCz, mul_comm]
      exact hn)
  have hzero : I W (n + 1) (Fin.snoc L B) = 0 := by
    have h0 : (S.M : ℝ) * I W (n + 1) (Fin.snoc L B) = 0 := by
      rw [← hCI, hvert, c3 n L, sub_self]
    have hM : (S.M : ℝ) ≠ 0 := by exact_mod_cast S.M_pos.ne'
    exact (mul_eq_zero.mp h0).resolve_left hM
  rw [hchange, hzero, zero_sub]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsUnitValues
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.OrArch.Ext

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem continuousAt_metric (A : HermLine ι) (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContinuousAt A.h z :=
  hA.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hz)

theorem continuous_aeval_form (g : MRing ι) : Continuous fun z : (Σ k, ι k) → ℂ => aeval z g := by
  have := MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) g)
  simpa only [Small.LineModel.eval_map_eq] using this

theorem continuousAt_log_metric {σ : Type} (A : HermLine ι) (hA : IsSmoothHerm A) (c : (Σ k, ι k) → σ)
    {z : σ → ℂ} (hz : ∀ k, ∃ i, z (c ⟨k, i⟩) ≠ 0) :
    ContinuousAt (fun w : σ → ℂ => Real.log (A.h fun p => w (c p))) z := by
  have h1 : ContinuousAt (fun w : σ → ℂ => A.h fun p => w (c p)) z :=
    ContinuousAt.comp (g := A.h) (f := fun (w : σ → ℂ) p => w (c p)) (continuousAt_metric A hA hz)
      (continuous_pi fun p => continuous_apply _).continuousAt
  exact h1.log (A.pos _ hz).ne'

end General

theorem line_smooth {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (t : ℝ)
    (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem archBetween_of_off_form : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : Top.RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Top.Wt Ψ N) (s lo hi : ℝ) (f : MRing (Cmp.joinIdx M.ι R.ι)), f ∉ mCoordIdeal (Ht.joinOf M R i) → (∀ j, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j)) → (∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∀ val : Option (Ψ × Fin N) → ℂ, (∀ j, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j) w (val j)) → ∑ j, M.coef lam s j * (Real.log ((M.line t j).h (fun p => w (Cmp.joinInl M.ι R.ι p))) - Real.log ((R.line 1 j).h (fun p => w (Cmp.joinInr M.ι R.ι p))) - Real.log ‖val j‖) ∈ Set.Icc lo hi) → Ht.ArchBetween M R i u t lam s lo hi := by
  intro Ψ _ _ N M R i u t lam s lo hi f hf hu hb z hz val hval
  have hcl := _root_.GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense (M.K ⊕ R.K) (Cmp.joinIdx M.ι R.ι) (mCoordIdeal (Ht.joinOf M R i)) _ f
    (_root_.GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main Ψ N M R i).1 hf
  have hzc := hcl (by rwa [← Small.LineModel.ptsOver_complex])
  have hne : ∀ j, val j ≠ 0 := by
    intro j
    obtain ⟨v, hv0, hv⟩ := hu j ℂ z hz
    rwa [Small.LineModel.hasVal_unique _ _ _ hz (hval j) hv]
  choose dg dh g h hg hh hd e n v using hval
  have hq : ∀ j, aeval z (g j) / aeval z (h j) = val j := fun j => by
    rw [v j, mul_div_assoc, div_self (n j), mul_one]
  let Fn : ((Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ) → ℝ := fun w =>
    ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => w (Cmp.joinInl M.ι R.ι p)) -
      Real.log ((R.line 1 j).h fun p => w (Cmp.joinInr M.ι R.ι p)) -
        Real.log ‖aeval w (g j) / aeval w (h j)‖)
  have hcont : ContinuousAt Fn z := by
    refine tendsto_finsetSum _ fun j _ => ?_
    have h1 := continuousAt_log_metric (M.line t j) (line_smooth M t j) (Cmp.joinInl M.ι R.ι)
      (z := z) fun k => hz.1 (Sum.inl k)
    have h2 := continuousAt_log_metric (R.line 1 j) (line_smooth R 1 j) (Cmp.joinInr M.ι R.ι)
      (z := z) fun k => hz.1 (Sum.inr k)
    have h3 : ContinuousAt (fun w : (Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ =>
        Real.log ‖aeval w (g j) / aeval w (h j)‖) z := by
      refine ContinuousAt.log ?_ ?_
      · exact (((continuous_aeval_form (g j)).continuousAt).div
          ((continuous_aeval_form (h j)).continuousAt) (n j)).norm
      · rw [hq j]
        exact norm_ne_zero_iff.mpr (hne j)
    exact continuousAt_const.mul ((h1.sub h2).sub h3)
  have hev : ∀ᶠ w in 𝓝[{w | w ∈ mcPts (mCoordIdeal (Ht.joinOf M R i)) ∧ Cmp.evC w f ≠ 0}] z,
      Fn w ∈ Set.Icc lo hi := by
    have hV : ∀ᶠ w in 𝓝 z, ∀ j, aeval w (h j) ≠ 0 := by
      rw [Filter.eventually_all]
      intro j
      exact (continuous_aeval_form (h j)).continuousAt.eventually_ne (n j)
    filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with w hw hS
    have hwp : w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)) := by
      rw [Small.LineModel.ptsOver_complex]
      exact hS.1
    exact hb w hwp hS.2 (fun j => aeval w (g j) / aeval w (h j)) fun j =>
      ⟨dg j, dh j, g j, h j, hg j, hh j, hd j, e j, hw j, (div_mul_cancel₀ _ (hw j)).symm⟩
  haveI hnb : (𝓝[{w | w ∈ mcPts (mCoordIdeal (Ht.joinOf M R i)) ∧ Cmp.evC w f ≠ 0}] z).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hzc
  have hmem : Fn z ∈ Set.Icc lo hi :=
    isClosed_Icc.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hFn : Fn z = ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => z (Cmp.joinInl M.ι R.ι p)) -
      Real.log ((R.line 1 j).h fun p => z (Cmp.joinInr M.ι R.ι p)) - Real.log ‖val j‖) :=
    Finset.sum_congr rfl fun j _ => by rw [hq j]
  rwa [hFn] at hmem

end GlobalTheory.CompanionTheory.Ar.OrArch.Ext
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResidueHodgeLatticeAdaptedBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

private theorem isUnit_det_of_linearIndependent_frame {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (a b : Fin n → W) (h : ∀ i, a i = ∑ k, M i k • b k)
    (ha : LinearIndependent C a) : IsUnit M.det := by
  by_contra hM
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr (by simpa [isUnit_iff_ne_zero] using hM)
  apply hc0
  have hsum : ∑ i, c i • a i = 0 := by
    simp_rw [h, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.sum_smul]
    have hk := congrFun hc k
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hk
    rw [hk, zero_smul]
  exact funext (Fintype.linearIndependent_iff.mp ha c hsum)

private theorem eq_sum_inv_smul_of_eq_sum_smul {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (hM : IsUnit M.det) (a b : Fin n → W) (h : ∀ i, a i = ∑ k, M i k • b k) :
    ∀ i, b i = ∑ k, M⁻¹ i k • a k := by
  intro i
  simp_rw [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul M hM, Matrix.one_apply, ite_smul,
    one_smul, zero_smul]
  simp

private theorem eq_sum_mul_smul_of_eq_sum_smul_of_eq_sum_smul {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) C) (N : Matrix (Fin m) (Fin m) C) (x : Fin n → W) (y z : Fin m → W)
    (hx : ∀ i, x i = ∑ k, M i k • y k) (hy : ∀ i, y i = ∑ k, N i k • z k) :
    ∀ i, x i = ∑ k, (M * N) i k • z k := by
  intro i
  rw [hx]
  simp_rw [hy, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem det_evaluated_frame : ∀ (E : Type) [Field E] [NumberField E] (C A : Type) [Field C] [CharZero C] [CommRing A] [Algebra A C]
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (g p q : ℕ) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C)))
    (tC : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (b₁ v : Fin p → Fin g → C) (b₂ w : Fin q → Fin g → C)
    (u : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (Ap : Matrix (Fin (p + q)) (Fin (p + q)) C)
    (P : Matrix (Fin p) (Fin p) C) (Q : Matrix (Fin q) (Fin q) C) (gm : C),
    (∀ a y, (ρHC a y).1 = ρC a y.1) → (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A C).range) → HT.IsFreeOn ρHC HV tC →
    IsAdapted ρHC σ b₁ b₂ u → (∀ i, v i = ∑ k, P i k • b₁ k) → (∀ i, w i = ∑ k, Q i k • b₂ k) →
    LinearIndependent C b₁ → (∀ i, HT.eigProj ρHC σ (tC i) = ∑ k, Ap i k • u k) →
    (∀ (v' : Fin p → Fin g → C) (w' : Fin q → Fin g → C)
      (u' : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (B : Matrix (Fin (p + q)) (Fin (p + q)) C),
      LinearIndependent C v' → Submodule.span A (Set.range v') = HT.eigSub ρC σ (stdLat A C g) →
      LinearIndependent C w' → Submodule.span A (Set.range w') = HT.eigSub ρC σ' (stdLat A C g) →
      IsAdapted ρHC σ v' w' u' → LinearIndependent C (fun i => ∑ k, B i k • u' k) →
      Submodule.span A (Set.range fun i => ∑ k, B i k • u' k) = HT.eigQuot ρHC σ HV →
      ∃ ε : Aˣ, B.det = algebraMap A C ε * gm) →
    LinearIndependent C v → Submodule.span C (Set.range v) = HT.eigSp ρC σ →
    Submodule.span A (Set.range v) = HT.eigSub ρC σ (stdLat A C g) →
    LinearIndependent C w → Submodule.span C (Set.range w) = HT.eigSp ρC σ' →
    Submodule.span A (Set.range w) = HT.eigSub ρC σ' (stdLat A C g) →
    ∃ ε : Aˣ, Ap.det * Q.det = algebraMap A C ε * gm * P.det := by
  intro E _ _ C A _ _ _ _ bar σ σ' g p q ρC ρHC HV tC b₁ v b₂ w u Ap P Q gm h1 h2 h3 h4 hA hfree had hvP hwQ hb₁
    hAp H hv hvspan hvA hw hwspan hwA
  obtain ⟨u', hu'ad, -, hu'span⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.AdaptedEx.exists_adapted_basis E C (Fin g → C) ρC ρHC bar σ σ' p q v w h1 h2 h3 h4 hv hvspan hw hwspan
  have hP := isUnit_det_of_linearIndependent_frame P v b₁ hvP hv
  have hQ := isUnit_det_of_linearIndependent_frame Q w b₂ hwQ hw
  obtain ⟨B0, hB0, hB0det⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted E C (Fin g → C) ρHC σ p q v b₁ w b₂ u' u P⁻¹ Q⁻¹ hu'ad had hv
    hu'span (eq_sum_inv_smul_of_eq_sum_smul P hP v b₁ hvP) (eq_sum_inv_smul_of_eq_sum_smul Q hQ w b₂ hwQ)
  have hcomb := eq_sum_mul_smul_of_eq_sum_smul_of_eq_sum_smul Ap B0 (fun i => HT.eigProj ρHC σ (tC i)) u u' hAp hB0
  have hfam : (fun i => ∑ k, (Ap * B0) i k • u' k) = fun i => HT.eigProj ρHC σ (tC i) :=
    funext fun i => (hcomb i).symm
  have hli : LinearIndependent C (fun i => HT.eigProj ρHC σ (tC i)) :=
    GlobalTheory.CompanionTheory.Ar.Flat.HodgeDeterminantLattice.linearIndependent_eigProj σ hfree
  have hsp : Submodule.span A (Set.range fun i => HT.eigProj ρHC σ (tC i)) = HT.eigQuot ρHC σ HV :=
    (GlobalTheory.CompanionTheory.Ar.Flat.HodgeDeterminantLattice.eigQuot_eq_span σ hfree hA).symm
  obtain ⟨ε, hε⟩ := H v w u' (Ap * B0) hv hvA hw hwA hu'ad (by rw [hfam]; exact hli) (by rw [hfam]; exact hsp)
  refine ⟨ε, ?_⟩
  rw [Matrix.det_mul] at hε
  rw [Matrix.det_nonsing_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Ring.inverse_eq_inv] at hB0det
  have hPd : P.det ≠ 0 := hP.ne_zero
  have hQd : Q.det ≠ 0 := hQ.ne_zero
  have hB : B0.det = Q.det * (P.det)⁻¹ := by
    rw [← hB0det, _root_.mul_comm Q.det, _root_.mul_assoc, inv_mul_cancel₀ hQd, _root_.mul_one]
  calc Ap.det * Q.det = Ap.det * B0.det * P.det := by
        rw [hB, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel₀ hPd, _root_.mul_one]
    _ = algebraMap A C ε * gm * P.det := by rw [hε]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

