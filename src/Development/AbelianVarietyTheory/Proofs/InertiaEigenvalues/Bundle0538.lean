module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Formalism.SharpRestriction.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableFromDataRowBRowEntries
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowBSize

open Classical

theorem ratIn_lt {x y : ℝ} (h : x < y) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) < y := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dite_eq_left h]
  exact (exists_rat_btwn h).choose_spec.2

theorem ratIn_of_not_lt {x y : ℝ} (h : ¬ x < y) : Formalism.MainNotions.N.ratIn x y = 0 := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dite_eq_right h]

theorem x_pos' {D : D7} (L : SizeData₂ D) : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]

theorem one_le_b' {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

theorem one_le_Lg {D : D7} (L : SizeData₂ D) : 1 ≤ Formalism.MainNotions.TwistedPlaces.large₂ L := by
  unfold Formalism.MainNotions.TwistedPlaces.large₂ Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem hB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L := by
  unfold Formalism.MainNotions.TwistedPlaces.hB
  have := one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem GP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.GP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := x_pos' L
    have := one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := x_pos' L
    positivity
  unfold Formalism.MainNotions.TwistedPlaces.GP Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.eta₃ Formalism.MainNotions.TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h3 := L.Sc_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

theorem coreB_pos {D : D7} (L : SizeData₂ D) {l : ℕ} (hl : 2 ≤ l) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 < Formalism.MainNotions.N.coreB L l lam := by
  unfold Formalism.MainNotions.N.coreB
  have hr : (0:ℝ) < D.R.r := by
    have : 0 < D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hl1 : (0:ℝ) < (l : ℝ) - 1 := by
    have : (2:ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hh : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) := by
    exact div_nonneg (hB_nonneg L) (pow_nonneg hl1.le _)
  have hg : 0 ≤ (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) := by
    have := GP_nonneg L; positivity
  have hL := one_le_Lg L
  have hin : 0 < Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) +
      (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L := by linarith
  have hn : (0:ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1 := by positivity
  positivity

theorem lenRowB_le {D : D7} (L : SizeData₂ D) {C₂ C : ℝ} (hC : 3 * C₂ + 1 ≤ C) {l : ℕ} (hl : 2 ≤ l)
    (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    ((Formalism.MainNotions.N.lenRowB L C₂ l lam : ℚ) : ℝ) ≤ C * Formalism.MainNotions.N.coreB L l lam := by
  have hc := coreB_pos L hl lam
  unfold Formalism.MainNotions.N.lenRowB
  have hlt : 3 * C₂ * Formalism.MainNotions.N.coreB L l lam < (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam := by nlinarith
  have := ratIn_lt hlt
  have : (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam ≤ C * Formalism.MainNotions.N.coreB L l lam :=
    mul_le_mul_of_nonneg_right hC hc.le
  linarith

end GlobalTheory.NLink.RowBSize

theorem GlobalTheory.NLink.localBoundTableFromData_rowB_rowEntries : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admB L (tabX L X) C := by
  intro D L P HW X R C hD hR
  intro i _ hrow lam _
  obtain ⟨hI, hA, hO, _⟩ := hrow
  have hl2 : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
  have hC1 : (1:ℝ) ≤ C := hR.2.2.2.2.1
  have hC3 : 3 * R.C₂ + 1 ≤ C := hR.2.2.2.2.2.1
  have hrowB := hD.rowB i hI ⟨hA, hO⟩
  have key : (tabX L X).len i lam = KillingConditions.supZ i (fun _ => ((Formalism.MainNotions.N.lenRowB L R.C₂ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hrowB]
  have hcore : C * ((TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) +
      (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + TwistedPlaces.large₂ L) = C * Formalism.MainNotions.N.coreB L (D.nd.l i) lam := by
    unfold Formalism.MainNotions.N.coreB; ring
  rw [key, hcore]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    exact GlobalTheory.NLink.RowBSize.lenRowB_le L hC3 hl2 lam
  · have := GlobalTheory.NLink.RowBSize.coreB_pos L hl2 lam
    positivity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulAcrisLatticeMemAcrisTensor
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrisInt

theorem tw_incl_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

theorem tw_incl_comp {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' R'' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [CommRing R''] [Algebra O R'']
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G Qp LL O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a t => simp [TWincl]

theorem mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hLM hML jB hcmp ε hε z
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hK := (_root_.GlobalTheory.BKExp.exponents l a e O K t ϖ ι P T I α β hLM hML ε δ hε hδ).2.2.2
  have step1 : ∀ c : ι → OA l O, ∃ y : TW (OA l O) T,
      jB (fun i => toB l O (((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) * c i)) = TWincl (toB l O) T y := by
    intro c
    obtain ⟨y, hy⟩ := hK (inclL t ϖ P c) ⟨c, rfl⟩
    refine ⟨y, hcmp _ y ?_⟩
    rw [← hy]
    congr 1
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [map_mul, Algebra.TensorProduct.tmul_pow]
  choose y hy using fun i : ι => step1 (Pi.single i 1)
  refine ⟨∑ i, z i • TWincl (toOCr l O) T (y i), ?_⟩
  have hsingle : ∀ i, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (Pi.single i 1) =
      TWincl (toB l O) T (y i) := by
    intro i
    rw [← hy i, ← map_smul]
    congr 1
    funext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hz : (fun i => toOB l O (z i)) = ∑ i, toOB l O (z i) • (Pi.single i (1 : OB l O)) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hz, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, hsingle, tw_incl_smul, tw_incl_comp]
  rfl

end GlobalTheory.BKGal.CrisInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonPlacePartLocalBoundLeMiddleRange
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.BBSize

variable {D : D7}

theorem sum_locDeg_le (i : D.nd.Loc) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hS : ∀ v ∈ S, v ∈ placesOver D.host.E (D.nd.l i)) :
    ∑ w ∈ S, (locDeg D.host.E w : ℝ) ≤ 2 * D.R.f := by
  have hl := (D.nd.lPrime i).out
  refine le_trans ?_ (TwistedPlaces.sum_nLam_le D hl)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    exact (Set.Finite.mem_toFinset _).2 (hS v hv)
  · intro v _ _
    positivity

theorem card_le_sum_locDeg (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    (S.card : ℝ) ≤ ∑ w ∈ S, (locDeg D.host.E w : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro v _
  exact_mod_cast TwistedPlaces.nLam_pos D v

theorem vdel_nonneg (i : D.nd.Loc) : (0 : ℝ) ≤ (D.nd.vdel i : ℝ) := by
  have : (0 : ℚ) ≤ D.nd.vdel i := by
    unfold NData.vdel
    positivity
  exact_mod_cast this

theorem vdel_le_two_t (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) : (D.nd.vdel i : ℝ) ≤ 2 * D.R.t := by
  have := D.nd.lPrime i
  have h := LargeLevelLemmas.vdel_le i
  have hs : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i h2
  have hv : (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) ≤ D.R.t := by
    rw [Nat.padicValNat_def]
    exact_mod_cast multiplicity_factorial_le (D.nd.l i) D.R.t
  rw [hs] at h
  have : D.nd.vdel i ≤ 2 * (D.R.t : ℚ) := by
    push_cast at h
    linarith
  exact_mod_cast this

theorem blk_arith {f t n V large₂ c A k b v h : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 6 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hb0 : 0 ≤ b)
    (hb : b ≤ c * t * n * V * large₂) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) (hh : h ≤ c * t) :
    t * (A * b) + 4 * V * (k + 1) * v + t * k * h ≤ 32 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : t * (A * b) ≤ 6 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * (A * b) ≤ t * ((6 * f) * (c * t * n * V * large₂)) := by gcongr
      _ = _ := by ring
  have h2 : 4 * V * (k + 1) * v ≤ 24 * (c * f * n * t ^ 2 * V * large₂) := by
    calc 4 * V * (k + 1) * v ≤ 4 * V * (3 * f) * (2 * t) := by gcongr; linarith
      _ = 24 * (1 * f * 1 * (t * 1) * V * 1) := by ring
      _ ≤ 24 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : t * k * h ≤ 2 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * k * h ≤ t * k * (c * t) := by gcongr
      _ ≤ t * (2 * f) * (c * t) := by gcongr
      _ = 2 * (c * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  linarith

theorem col_arith {f t n V large₂ c A k m r v : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 2 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hm0 : 0 ≤ m) (hm : m ≤ t)
    (hr0 : 0 ≤ r) (hr : r ≤ t) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) :
    A * (m * v) + k * (2 * v + 2 * (c * r * n * V * large₂)) ≤ 16 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : A * (m * v) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc A * (m * v) ≤ (2 * f) * (t * (2 * t)) := by gcongr
      _ = 4 * (1 * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  have h2 : k * (2 * v) ≤ 8 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * v) ≤ (2 * f) * (2 * (2 * t)) := by gcongr
      _ = 8 * (1 * f * 1 * (t * 1) * 1 * 1) := by ring
      _ ≤ 8 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : k * (2 * (c * r * n * V * large₂)) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * (c * r * n * V * large₂)) ≤ (2 * f) * (2 * (c * t * n * V * large₂)) := by gcongr
      _ = 4 * (c * f * n * (t * 1) * V * large₂) := by ring
      _ ≤ 4 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  rw [mul_add]
  linarith

theorem f_ge_one (D : D7) : (1 : ℝ) ≤ D.R.f := (TwistedPlaces.m_ge_one D).trans (TwistedPlaces.m_le_f D)

theorem nV_ge_one (D : D7) : (1 : ℝ) ≤ D.R.nV := by
  have := TwistedPlaces.t_ge_one D
  have h0 : (0 : ℝ) ≤ D.R.r := by positivity
  unfold Ranks.nV
  push_cast
  linarith

theorem blockBoundDeclaration_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) (dc : TruncatedSeriesCountingIdentities.Decl D i) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t) :
    (KillingConditions.localErrorBoundDecomposition i dc cB : ℝ) ≤ 32 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hrow := sum_locDeg_le i dc.row (fun v hv => (dc.cover v).1 (Or.inl hv))
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hr := card_le_sum_locDeg dc.row
  have hk := card_le_sum_locDeg dc.col
  have hA : ∑ w ∈ dc.row, ((locDeg D.host.E w : ℝ) + 2) ≤ 6 * D.R.f := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  have := blk_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hA
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg cB) hB (vdel_nonneg i)
    (vdel_le_two_t i h2) hh
  unfold KillingConditions.localErrorBoundDecomposition
  push_cast
  rw [← Finset.sum_mul]
  exact this

theorem blockBoundAtZero_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t)
    (hu : ∀ u ∈ dc.col, (c0 u : ℝ) ≤ c * D.R.n * D.R.nV * TwistedPlaces.large₂ L ∧
      (Br.h0W i u ρ π : ℝ) ≤ c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L) :
    (localErrorBoundPlaces i ρ π dc c0 cB : ℝ) ≤ 48 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hb := blockBoundDeclaration_le_middleRange L i h2 dc cB hc hB hh
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hk := card_le_sum_locDeg dc.col
  have hrt : (D.R.r : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.t_ge D]
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.m_le_k D, TwistedPlaces.k_le_r D]
  have hc' := col_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hcol
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg D.R.m) hmt (Nat.cast_nonneg D.R.r) hrt
    (vdel_nonneg i) (vdel_le_two_t i h2)
  have hs : ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * (D.R.m : ℝ) * (D.nd.vdel i : ℝ) + 2 * (D.nd.vdel i : ℝ) +
        (Br.h0W i u ρ π : ℝ) + (D.R.r : ℝ) * (c0 u : ℝ)) ≤
      ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ)) +
        (2 * (D.nd.vdel i : ℝ) + 2 * (c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L))) := by
    apply Finset.sum_le_sum
    intro u hu'
    obtain ⟨h1, h3⟩ := hu u hu'
    have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) D.R.r)
    linarith
  rw [Finset.sum_add_distrib (f := fun u => (locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ))),
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hs
  unfold KillingConditions.localErrorBoundDecomposition at hb
  unfold localErrorBoundPlaces
  push_cast at hb ⊢
  linarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (c : ℝ), 1 ≤ c → KillingConditions.DataAD L HW X R → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X c → KillingConditions.BBLe L X (60 * c) := by
  intro D L _ HW X R c hc hD hJ i hi hg hR π hπ
  obtain ⟨hB, hh, hS⟩ := hJ i hi hg hR
  have h2 : D.nd.l i ∉ D.host.small := fun h => hR.1 (Or.inl h)
  have hq : D.nd.l i ≠ D.host.q := fun h => hR.2.1 (Or.inl h)
  have hd : D.nd.l i ≠ D.host.d := fun h => hR.2.1 (Or.inr h)
  have hL := TwistedPlaces.L_ge_one L
  have hM0 : 0 ≤ c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L := by
    have : 0 ≤ c := by linarith
    have : 0 ≤ TwistedPlaces.large₂ L := by linarith
    positivity
  have hM := le_mul_of_one_le_right hM0 hL
  have hE : 60 * c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 =
      60 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L * TwistedPlaces.large₂ L) := by ring
  rw [hE]
  rcases TwistedPlaces.split_or_inert D h2 hq hd with hs | hin
  · rw [hD.error_bound_split_eq i hs π]
    have := blockBoundAtZero_le_middleRange L i h2 (X.ρ i) π (X.dc i) (X.c0 i) (X.cB i) hc hB hh
      (fun u hu => ⟨(hS hs u hu).1, (hS hs u hu).2 π hπ⟩)
    linarith
  · rw [hD.error_bound_inert_eq i hin π]
    have := blockBoundDeclaration_le_middleRange L i h2 (X.dc i) (X.cB i) hc hB hh
    linarith

end GlobalTheory.NLink.BBSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem norm_toDisc_add_le_max (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : A) :
    ‖toDisc l u ρ (a + b)‖ ≤ max ‖toDisc l u ρ a‖ ‖toDisc l u ρ b‖ := by
  have h1 : ∀ c, ‖toDisc l u ρ c‖ = gauge l u ρ (algebraMap A (PreDisc l u ρ) c) := fun c => norm_ofPre l u ρ _
  rewrite [h1, h1, h1, map_add]
  exact gauge_add_le_max l u ρ _ _

theorem norm_hf_g_X_and_φ_le :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
      (f g : Hom bk.prism B),
      ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) g X)‖ ≤ bk.ρ₀ ∧
        ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (B.D.φ (BK.hf (bk := bk) f X))‖ ≤ bk.ρ₀ := by
  intro l _ K bk B f g
  obtain ⟨hρ0, hρ1, hlρ, hE⟩ := _root_.GlobalTheory.BSP.norm_E_le_radius l K bk B.A (BK.hf (bk := bk) f)
  have hd : BK.hf (bk := bk) f bk.E ∣ BK.hf (bk := bk) g X - BK.hf (bk := bk) f X := by
    obtain ⟨hfI, hfX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B f
    obtain ⟨_, hgX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B g
    rw [← Ideal.mem_span_singleton, ← hfI]
    exact Ideal.Quotient.eq.1 (hgX.trans hfX.symm)
  have h : ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) f X ^ 1)‖ ≤ (bk.ρ₀ : ℝ) ^ 1 := norm_toDisc_pow_le 1 hρ0
  have hX : ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) f X)‖ ≤ bk.ρ₀ := by simpa only [pow_one] using h
  have key : ∀ a b : B.A, ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (a + b)‖ ≤
      max ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ a‖ ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ b‖ :=
    norm_toDisc_add_le_max l (BK.hf (bk := bk) f X) bk.ρ₀
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := hd
    have e : BK.hf (bk := bk) g X = BK.hf (bk := bk) f X + BK.hf (bk := bk) f bk.E * w := eq_add_of_sub_eq' hw
    rewrite [e]
    refine (key _ _).trans (max_le hX ?_)
    rewrite [map_mul]
    refine (norm_mul_le _ _).trans ?_
    calc ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) f bk.E)‖ * ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ w‖
        ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul hE (norm_toDisc_le w) (norm_nonneg _) (by positivity)
      _ ≤ bk.ρ₀ := (mul_one _).trans_le hlρ
  · have e1 : B.D.φ (BK.hf (bk := bk) f X) = BK.hf (bk := bk) f (frobS l bk.a X) :=
      (Hom.f_φ f (show bk.prism.A from X)).symm
    have e : B.D.φ (BK.hf (bk := bk) f X) = BK.hf (bk := bk) f X ^ l := by
      rw [e1, frobS_X, map_pow]
    refine (congrArg (fun y => ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ y‖) e).trans_le ((norm_toDisc_pow_le l hρ0).trans ?_)
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCrystalChangeOfBasisConstantCoeffEqOne
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.CrysDiag.eps_constantCoeff_eq_one : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (κ₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, κ₀ τ (δ.f y) = PowerSeries.constantCoeff (κ τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)).map PowerSeries.constantCoeff = 1 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  intro E jA hR hM oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ hκ Q _ c y hy τ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.crystal_basis_transport_free_over_prism l a e O K t ϖ ι P T I E jA hR hM oE hoE b hb
  have key : ∀ j, ∑ i, ∑ q, δ.f (y i j q) • (oE (c i j q)).u S₀ (E.tr (δ.comp p₀) (b i)) =
      ∑ i, ∑ _q : Unit, (if i = j then (1 : S₀.A) else 0) • (oE 1).u S₀ (E.tr (δ.comp p₀) (b i)) := by
    intro j
    have hfix : ∀ i, (oE 1).u S₀ (E.tr (δ.comp p₀) (b i)) = E.tr (δ.comp p₀) (b i) := fun i => by
      rw [(oE 1).u_tr, h1]
    simp only [hfix, ite_smul, one_smul, zero_smul, Finset.sum_const, Finset.card_univ, Fintype.card_unit]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    conv_rhs => rw [hδ, E.tr_comp, hy j]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E.tr_comp, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => ?_
    rw [(oE (c i j q)).u_tr]
    exact ((E.tr δ).map_smulₛₗ _ _).symm
  have hC : ∀ w : Wq l a, (toAc t K (PowerSeries.C w) τ : K⟦X⟧) = PowerSeries.C (algebraMap O K (emb t τ w)) := by
    intro w
    ext n
    rw [coeff_toAc, PowerSeries.coeff_C, PowerSeries.coeff_C]
    split_ifs <;> simp
  have hψ : ∀ z : ℤ_[l], κ₀ τ ((δ.comp p₀).f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) =
      algebraMap O K⟦X⟧ (algebraMap ℤ_[l] O z) := by
    intro z
    change κ₀ τ (δ.f (p₀.f _)) = _
    rw [hκ₀, hκ, PowerSeries.algebraMap_apply, frobS_C, PowerSeries.constantCoeff_C, hC,
      AlgEquiv.commutes, AlgHom.commutes, PowerSeries.algebraMap_apply]
  refine Matrix.ext fun i j => ?_
  have hij := h2 S₀ (δ.comp p₀) Q Unit (fun i q => c i j q) (fun i q => δ.f (y i j q)) (fun _ _ => 1)
    (fun i _ => if i = j then (1 : S₀.A) else 0) (by simpa only [one_smul] using key j) K⟦X⟧ (κ₀ τ) hψ i
  simp only [hκ₀, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, apply_ite (κ₀ τ),
    map_one, map_zero] at hij
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.map_apply, Matrix.of_apply, map_sum, Matrix.one_apply, ← hij]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, PowerSeries.algebraMap_apply,
    PowerSeries.constantCoeff_C, PowerSeries.algebraMap_apply]
end

