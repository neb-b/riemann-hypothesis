module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XNefCurve

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift

section General

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] {n : ℕ}

theorem analytic_eval {G : (Fin n → ℂ) → (Σ k, J k) → ℂ} {T : Set (Fin n → ℂ)}
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (f : MRing J) :
    AnalyticOnNhd ℂ (fun w => eval (G w) (map (Int.castRingHom ℂ) f)) T := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using analyticOnNhd_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, map_X, eval_X]
    exact hp.mul (hG i)

theorem isOpen_forall_ne {A : Type} [Finite A] {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    {f : A → (Fin n → ℂ) → ℂ} (hf : ∀ a, AnalyticOnNhd ℂ (f a) T) :
    IsOpen {w | w ∈ T ∧ ∀ a, f a w ≠ 0} := by
  have e : {w | w ∈ T ∧ ∀ a, f a w ≠ 0} = T ∩ ⋂ a, (T ∩ f a ⁻¹' {0}ᶜ) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨h.1, fun a => ⟨h.1, h.2 a⟩⟩, fun h => ⟨h.1, fun a => (h.2 a).2⟩⟩
  rw [e]
  exact hT.inter (isOpen_iInter_of_finite fun a =>
    (hf a).continuousOn.isOpen_inter_preimage hT isOpen_compl_singleton)

theorem form_notMem_iff (z : (Σ k, J k) → ℂ) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∉ mCoordIdeal z ↔ eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
  rw [Ne, form_mem_mCoordIdeal_iff z hg, aeval_def, algebraMap_int_eq, eval₂_eq_eval_map]

theorem exists_normalised {A : Type} [Finite A] (x : (Σ k, J k) → Ω) (c : ∀ k, J k) (s : A → Ω)
    (G : (Fin n → ℂ) → (Σ k, J k) → ℂ) {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (hmem : ∀ w ∈ T, G w ∈ mcPts (mCoordIdeal x))
    {w₀ : Fin n → ℂ} (hw₀ : w₀ ∈ T) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ mCoordIdeal (G w₀))
    (hreg : ∀ a, RegAt x (mCoordIdeal (G w₀)) (s a)) :
    ∃ (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, J k) → ℂ), V ⊆ T ∧ IsOpen V ∧ w₀ ∈ V ∧
      (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
      (∀ a, AnalyticOnNhd ℂ (fun w => valAt x (s a) (bl w)) V) ∧
      ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal x) ∧ (∀ k, bl w ⟨k, c k⟩ = 1) ∧ SameOrbit (G w) (bl w) ∧
        ∀ a, RegAt x (mCoordIdeal (bl w)) (s a) := by
  choose d g h hg hh hnot heq using hreg
  have hX : ∀ (k : K) (i : J k), IsMultiHomog (X ⟨k, i⟩ : MRing J) (fun k' => if k' = k then 1 else 0) := fun k i =>
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, i⟩
  have hx : ∀ a, aeval x (h a) ≠ 0 := fun a e0 => by
    have h1 := (hmem w₀ hw₀).2 _ (mem_mCoordIdeal_of_aeval_eq_zero x (hh a) e0)
    exact (form_notMem_iff _ (hh a)).1 (hnot a) h1
  set bl : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun w p => G w p / G w ⟨p.1, c p.1⟩ with hbl
  set T₁ : Set (Fin n → ℂ) := {w | w ∈ T ∧ ∀ k, G w ⟨k, c k⟩ ≠ 0} with hT₁
  have hT₁o : IsOpen T₁ := isOpen_forall_ne hT fun k => hG ⟨k, c k⟩
  have hT₁T : T₁ ⊆ T := fun w hw => hw.1
  have hblq : ∀ q, AnalyticOnNhd ℂ (fun w => bl w q) T₁ := fun q =>
    ((hG q).mono hT₁T).div ((hG ⟨q.1, c q.1⟩).mono hT₁T) fun w hw => hw.2 q.1
  have hevh : ∀ a, AnalyticOnNhd ℂ (fun w => eval (bl w) (map (Int.castRingHom ℂ) (h a))) T₁ := fun a =>
    analytic_eval hblq (h a)
  have horb : ∀ w ∈ T₁, SameOrbit (G w) (bl w) := fun w hw =>
    ⟨fun k => G w ⟨k, c k⟩, hw.2, funext fun p => by
      have := hw.2 p.1
      simp only [hbl]
      field_simp⟩
  have hw₁ : w₀ ∈ T₁ := ⟨hw₀, fun k e0 => (form_notMem_iff _ (hX k (c k))).1 (hc k) (by simpa using e0)⟩
  refine ⟨{w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0}, bl,
    fun w hw => hw.1.1, isOpen_forall_ne hT₁o hevh, ⟨hw₁, fun a => ?_⟩, fun q => (hblq q).mono fun w hw => hw.1,
    fun a => ?_, fun w hw => ?_⟩
  · rw [← form_notMem_iff _ (hh a), ← GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit (horb w₀ hw₁)]
    exact hnot a
  · have hV : IsOpen {w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0} :=
      isOpen_forall_ne hT₁o hevh
    have hsub : {w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0} ⊆ T₁ :=
      fun w hw => hw.1
    refine AnalyticOnNhd.congr hV (((analytic_eval hblq (g a)).mono hsub).div
      ((hevh a).mono hsub) fun w hw => hw.2 a) fun w hw => ?_
    have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact (valAt_eq hz ⟨d a, g a, h a, hg a, hh a, hx a, heq a, hw.2 a, rfl⟩).symm
  · have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact ⟨hz, fun k => div_self (hw.1.2 k), horb w hw.1,
      fun a => ⟨d a, g a, h a, hg a, hh a, (form_notMem_iff _ (hh a)).2 (hw.2 a), heq a⟩⟩

end General

theorem exists_baseChart (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk) (x₀ : Rb.X)
    (hgood : M.GoodAt F (mCoordIdeal (Rb.lift x₀ x₀))) :
    ∃ (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ),
      x₀ ∈ (Rb.A.chart kb).source ∧ Rb.A.chart kb x₀ ∈ V ∧ IsBaseChart M Rb F kb V bl := by
  obtain ⟨kb, hkb⟩ := Rb.A.cover x₀
  have hT : IsOpen ((Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀) :=
    (Rb.A.chart kb).isOpen_inter_preimage_symm (Rb.isOpen_U x₀)
  have hlw : Rb.lift x₀ ((Rb.A.chart kb).symm (Rb.A.chart kb x₀)) = Rb.lift x₀ x₀ := by
    rw [(Rb.A.chart kb).left_inv hkb]
  have hw₀ : Rb.A.chart kb x₀ ∈ (Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀ :=
    ⟨(Rb.A.chart kb).map_source hkb, by
      show (Rb.A.chart kb).symm (Rb.A.chart kb x₀) ∈ Rb.U x₀
      rw [(Rb.A.chart kb).left_inv hkb]
      exact Rb.mem_U x₀⟩
  let s : (((Σ k, ι k) × Finset (Fin N)) ⊕ ((Σ k, ι k) × Finset (Fin N))) ⊕
      ({p : Ψ × Fin N // M.blk p = none} ⊕ {p : Ψ × Fin N // M.blk p = none}) → M.Ω :=
    Sum.elim (Sum.elim (fun a => F.u a.1 a.2) (fun a => F.u' a.2 a.1))
      (Sum.elim (fun p => F.υ p.1) (fun p => (F.υ p.1)⁻¹))
  obtain ⟨V, bl, hVT, hVo, hV₀, hq, hval, hpt⟩ := exists_normalised M.x F.c s
    (fun w => Rb.lift x₀ ((Rb.A.chart kb).symm w)) hT (fun q => Rb.holo x₀ q kb)
    (fun w hw => Rb.mem x₀ _ hw.2) hw₀
    (by simpa only [hlw] using hgood.1)
    (by
      simp only [hlw]
      rintro ((⟨q, I⟩ | ⟨q, I⟩) | (⟨p, hp⟩ | ⟨p, hp⟩))
      · exact (hgood.2.1 q I).1
      · exact (hgood.2.1 q I).2
      · exact (hgood.2.2 p hp).2.1
      · exact (hgood.2.2 p hp).2.2)
  refine ⟨kb, V, bl, hkb, hV₀, hVo, fun w hw => (hVT hw).1, hq,
    fun q I => hval (Sum.inl (Sum.inl (q, I))), fun w hw => ?_⟩
  obtain ⟨hz, h1, hor, hr⟩ := hpt w hw
  refine ⟨hz, h1, ⟨fun k e0 => ?_, fun q I => ⟨hr (Sum.inl (Sum.inl (q, I))), hr (Sum.inl (Sum.inr (q, I)))⟩,
    fun p hp => ⟨(hgood.2.2 p hp).1, hr (Sum.inr (Sum.inl ⟨p, hp⟩)), hr (Sum.inr (Sum.inr ⟨p, hp⟩))⟩⟩,
    orbit_trans (Rb.compat _ x₀ _ ⟨Rb.mem_U _, (hVT hw).2⟩) hor⟩
  have := (form_mem_mCoordIdeal_iff (bl w) (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single
    (⟨k, F.c k⟩ : Σ k, baseIdx ι M.blk k))).1 e0
  rw [aeval_X, h1 k] at this
  exact one_ne_zero this

end GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalTwistTrivialization
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem frame_values :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m r n : ℕ) (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (cb : Fin r → E), IsTwistGen ξ x L m φ → L.IsVB r V → LinearIndependent Ω cb → Submodule.span Ω (Set.range cb) = V → ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin r) (Fin n) Ω), IsUnit T.det ∧ L.IsFrameAt (colFrame cb T) p ∧ (∀ a b, ((Matrix.of fun a b => φ a (cb b)) * T) a b / x c ^ m ∈ regAt ξ p) ∧ (∀ a b, C a b ∈ regAt ξ p) ∧ ∀ a b, ∑ k, C a k * (((Matrix.of fun a b => φ a (cb b)) * T) k b / x c ^ m) = if a = b then 1 else 0 := by
  intro X Ω _ ξ E _ _ κ x L m r n V φ cb hG hV hli hsp p c hc
  obtain ⟨U, hU, b, hbsp, hb⟩ := hV p (Set.mem_univ p)
  have hf : L.IsFrameAt b p := hb p (Set.mem_univ p) hU
  have h1 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • cb a = b l := fun l => by
    have : b l ∈ Submodule.span Ω (Set.range cb) := by
      rw [hsp, ← hbsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  have h2 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • b a = cb l := fun l => by
    have : cb l ∈ Submodule.span Ω (Set.range b) := by
      rw [hbsp, ← hsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  choose t ht using h1
  choose t' ht' using h2
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t l a
  let T' : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t' l a
  have hT : colFrame cb T = b := by
    funext l; exact ht l
  have hT' : colFrame b T' = cb := by
    funext l; exact ht' l
  have hmul : T * T' = 1 := by
    have e : colFrame cb (T * T') = colFrame cb (1 : Matrix (Fin r) (Fin r) Ω) := by
      rw [colFrame_mul, hT, hT', colFrame_one]
    ext a l
    have h3 := congrFun e l
    simp only [colFrame] at h3
    have h0 := (Fintype.linearIndependent_iff.1 hli) (fun a => (T * T') a l - (1 : Matrix _ _ Ω) a l)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h3, sub_self]) a
    exact sub_eq_zero.1 h0
  have hdet : IsUnit T.det := Matrix.isUnit_det_of_right_inverse hmul
  have hval : ∀ a l, ((Matrix.of fun a b => φ a (cb b)) * T) a l = φ a (b l) := by
    intro a l
    rw [← hT]
    simp [Matrix.mul_apply, colFrame, mul_comm]
  have hmem : ∀ l, b l ∈ L p := fun l => by
    rw [hf.2]; exact Submodule.subset_span ⟨l, rfl⟩
  have hw : ∀ l, ∃ w : Module.Dual Ω E, ∀ k, w (b k) = if l = k then 1 else 0 := fun l => by
    obtain ⟨w, h1, h0⟩ := GlobalTheory.CompanionTheory.Ar.FlagGrGen.exists_coord hf.1 l
    refine ⟨w, fun k => ?_⟩
    split_ifs with h
    · rw [← h]; exact h1
    · exact h0 k (Ne.symm h)
  choose w hw using hw
  have hwreg : ∀ l, ∀ e ∈ L p, w l e ∈ regAt ξ p := by
    intro l e he
    rw [hf.2] at he
    induction he using Submodule.span_induction with
    | mem e h =>
      obtain ⟨k, rfl⟩ := h
      rw [hw]
      split_ifs
      exacts [one_mem _, zero_mem _]
    | zero => simp [zero_mem]
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a e _ he =>
      have h4 : w l (a • e) = (a : Ω) * w l e := by rw [Subring.smul_def, map_smul, smul_eq_mul]
      rw [h4]; exact mul_mem a.2 he
  choose g hg hg' using fun l => hG.2 p c hc (w l) (hwreg l)
  refine ⟨T, Matrix.of g, hdet, ?_, ?_, ?_, ?_⟩
  · rw [hT]; exact hf
  · intro a l; rw [hval]; exact hG.1 a p c hc _ (hmem l)
  · intro a j; exact hg a j
  · intro a l
    simp only [hval, Matrix.of_apply]
    rw [← hg' a (b l) (hmem l), hw]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverse
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt

theorem exists_rows_det_ne_zero {Ω : Type} [Field Ω] {n m : ℕ} (M : Matrix (Fin n) (Fin m) Ω)
    (B : Matrix (Fin m) (Fin n) Ω) (h : B * M = 1) :
    ∃ J : Fin m → Fin n, (M.submatrix J id).det ≠ 0 := by
  have hspan : Submodule.span Ω (Set.range fun j => M j) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hw : w = (w ᵥ* B) ᵥ* M := by rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
    rw [hw, Matrix.vecMul_eq_sum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨f, hf, -, hl⟩ := Submodule.exists_fun_fin_finrank_span_eq Ω (Set.range fun j => M j)
  have e : Module.finrank Ω (Submodule.span Ω (Set.range fun j => M j)) = m := by
    rw [hspan, finrank_top, Module.finrank_fin_fun]
  choose J hJ using fun i : Fin m => hf (Fin.cast e.symm i)
  refine ⟨J, ?_⟩
  have hl' : LinearIndependent Ω (M.submatrix J id).row := by
    have : (M.submatrix J id).row = f ∘ Fin.cast e.symm := by
      funext i
      exact hJ i
    rw [this]
    exact hl.comp _ (Fin.cast_injective _)
  exact ((Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_rows_iff_isUnit.1 hl')).ne_zero

theorem exists_rows_castLE_det_ne_zero {Ω : Type} [Field Ω] {n m a : ℕ} (M : Matrix (Fin n) (Fin m) Ω)
    (B : Matrix (Fin m) (Fin n) Ω) (h : B * M = 1) (ha : a + 1 ≤ m) (hm : a + 1 = m) :
    ∃ J : Fin (a + 1) → Fin n, (M.submatrix J (Fin.castLE ha)).det ≠ 0 := by
  subst hm
  obtain ⟨J, hJ⟩ := exists_rows_det_ne_zero M B h
  exact ⟨J, hJ⟩

theorem step_full {Ψ : Type} {p q : ℕ} (K₀ : Type) (t : StepIx Ψ p q)
    (h : ∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r ≠ some (.inr t)) :
    (t.2 : ℕ) + 1 = rk Ψ p q t.1 := by
  classical
  obtain ⟨s, a⟩ := t
  rcases s with τ | τ
  · have ha : (a : ℕ) < p := a.2
    by_contra hne
    have hne' : (a : ℕ) + 1 ≠ p := hne
    refine h (τ, ⟨a, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨a, by omega⟩ : Fin (p + q)) :=
      ⟨hne', by show (a : ℕ) + 1 ≠ p + q; intro h'; omega⟩
    rw [blkF, if_pos hp]
    simp [stepOf, ha]
    rfl
  · have ha : (a : ℕ) < q := a.2
    by_contra hne
    have hne' : (a : ℕ) + 1 ≠ q := hne
    refine h (τ, ⟨p + a, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨p + a, by omega⟩ : Fin (p + q)) := by
      constructor
      · show p + (a : ℕ) + 1 ≠ p
        omega
      · show p + (a : ℕ) + 1 ≠ p + q
        omega
    rw [blkF, if_pos hp]
    simp [stepOf]
    rfl

theorem xb_block_ne : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type)
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), (∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0) →
    (∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * A s = 1) →
    ∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0 := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ hx hB k
  obtain ⟨k, hk⟩ := k
  rcases k with k | t
  · exact hx k
  · obtain ⟨B, hB⟩ := hB t.1
    exact exists_rows_castLE_det_ne_zero (A t.1) B hB t.2.2 (step_full K₀ t hk)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTriangularRegularFrameChange
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FrameTrans

theorem colFrame_injective {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {e : Fin r → V}
    (he : LinearIndependent Ω e) {T T' : Matrix (Fin r) (Fin r) Ω} (h : colFrame e T = colFrame e T') : T = T' := by
  ext a b
  have hb := congrFun h b
  simp only [colFrame] at hb
  have h0 := Fintype.linearIndependent_iff.1 he (fun a => T a b - T' a b)
    (by simp only [sub_smul, Finset.sum_sub_distrib]; exact sub_eq_zero.2 hb) a
  exact sub_eq_zero.1 h0

theorem linearIndependent_colFrame {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {w : Fin r → V}
    (hw : LinearIndependent Ω w) {g : Matrix (Fin r) (Fin r) Ω} (hg : IsUnit g.det) :
    LinearIndependent Ω (colFrame w g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : ∑ a, (g.mulVec c a) • w a = 0 := by
    rw [← hc]
    simp only [colFrame, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [_root_.mul_comm]
  have h0 : g.mulVec c = 0 := funext (Fintype.linearIndependent_iff.1 hw _ hsum)
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hg.ne_zero h0
  intro i
  rw [hc0]
  rfl

theorem exists_regular_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {p : Cpt ξ} {r : ℕ} {e : Fin r → E} {v : E}
    (h : v ∈ Submodule.span (regAt ξ p) (Set.range e)) :
    ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ v = ∑ a, c a • e a := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  exact ⟨fun k => (a k : Ω), fun k => (a k).2, ha.symm⟩

theorem exists_triangular {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b b₀ : Fin r → V}
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) :
    ∃ U : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ b = colFrame b₀ U := by
  have hex : ∀ l : Fin r, ∃ f : Fin r → Ω, (∀ k : Fin r, ¬ (k : ℕ) < (l : ℕ) + 1 → f k = 0) ∧
      b l = ∑ k, f k • b₀ k := by
    intro l
    have h1 : b l ∈ flagStep Ω b₀ ((l : ℕ) + 1) := by
      rw [← hF]
      exact Submodule.subset_span ⟨l, Nat.lt_succ_self _, rfl⟩
    obtain ⟨f, hf, hs⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
    refine ⟨f, fun k hk => (Finsupp.mem_supported' Ω f).1 hf k hk, ?_⟩
    rw [← hs, Finsupp.linearCombination_apply]
    exact Finsupp.sum_fintype f (fun i a => a • b₀ i) (fun k => zero_smul Ω _)
  choose f hf0 hf using hex
  refine ⟨fun k l => f l k, ?_, ?_⟩
  · intro i j hij
    have hij' : j < i := hij
    refine hf0 j i ?_
    have : (j : ℕ) < i := hij'
    omega
  · funext l
    exact hf l

theorem sub_diag_mem {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} (b₀ : Fin r → V)
    {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (l : Fin r) :
    colFrame b₀ U l - U l l • b₀ l ∈ flagStep Ω b₀ l := by
  have h : colFrame b₀ U l - U l l • b₀ l = ∑ a ∈ Finset.univ.erase l, U a l • b₀ a := by
    rw [colFrame, ← Finset.add_sum_erase _ _ (Finset.mem_univ l), add_sub_cancel_left]
  rw [h]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hne : a ≠ l := Finset.ne_of_mem_erase ha
  by_cases hlt : (a : ℕ) < l
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hlt, rfl⟩)
  · have hla : l < a := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne)
    rw [hU hla, zero_smul]
    exact zero_mem _

theorem exists_adapted : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (w : Fin r → E) (P g : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω w → IsUnit g.det → L.IsFrameAt (colFrame w P) p → L.IsFlagVBOn Set.univ (colFrame w g) → ∃ U Rm Rm' : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ (∀ a b, Rm a b ∈ regAt ξ p) ∧ (∀ a b, Rm' a b ∈ regAt ξ p) ∧ Rm * Rm' = 1 ∧ g * U = P * Rm ∧ ∀ l, (L.gr (colFrame w g) l).IsGenAt p (U l l) := by
  intro X Ω _ ξ E _ _ L r w P g p hw hg he hFl
  obtain ⟨V, hV, b, hbF, hbL⟩ := hFl p (Set.mem_univ p)
  have hb : L.IsFrameAt b p := hbL p (Set.mem_univ p) hV
  have hb₀ := linearIndependent_colFrame hw hg
  obtain ⟨U, hU, hbU⟩ := exists_triangular hbF
  have hexR : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ b l = ∑ a, c a • colFrame w P a := by
    intro l
    refine exists_regular_coeff ?_
    rw [← he.2, hb.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hexR' : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ colFrame w P l = ∑ a, c a • b a := by
    intro l
    refine exists_regular_coeff ?_
    rw [← hb.2, he.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose c hc hcs using hexR
  choose c' hc' hcs' using hexR'
  obtain ⟨Rm, hRm, hbR⟩ : ∃ Rm : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm a l ∈ regAt ξ p) ∧
      b = colFrame (colFrame w P) Rm := ⟨fun a l => c l a, fun a l => hc l a, funext hcs⟩
  obtain ⟨Rm', hRm', heR⟩ : ∃ Rm' : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm' a l ∈ regAt ξ p) ∧
      colFrame w P = colFrame b Rm' := ⟨fun a l => c' l a, fun a l => hc' l a, funext hcs'⟩
  refine ⟨U, Rm, Rm', hU, hRm, hRm', ?_, ?_, ?_⟩
  · refine colFrame_injective he.1 ?_
    rw [colFrame_mul, ← hbR, ← heR, colFrame_one]
  · refine colFrame_injective hw ?_
    rw [colFrame_mul, colFrame_mul, ← hbU, ← hbR]
  · intro l
    refine FlagGrGen.gr_isGenAt X Ω ξ E L r (colFrame w g) b p l (U l l) hb₀ hbF hb ?_
    rw [hbU]
    exact sub_diag_mem _ hU l

end GlobalTheory.CompanionTheory.Ar.PB.FrameTrans
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPoints
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem comp_v_mem_mcPts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb hz
  have hb := Cv.block
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (Cv.κ k)
    obtain ⟨p, hp⟩ := hb.2.2.2 ⟨Cv.κ k, i⟩ ⟨k, rfl⟩
    have hk : p.1 = k := hb.1 (by have h := hb.2.2.1 p; rw [hp] at h; exact h.symm)
    obtain ⟨k₀, i₀⟩ := p
    cases hk
    exact ⟨i₀, by simpa [Function.comp, hp] using hi⟩
  · have key : ∀ g, mConeMap (M'.x ∘ Cv.v) g = MvPolynomial.map Cv.φ (mConeMap M.x g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp [mConeMap]
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | mul_X p n hp =>
        simp only [map_mul, hp]
        congr 1
        simp [mConeMap, Cv.x_eq]
    have h0 : mConeMap M.x f = 0 := hf
    have h1 : f ∈ mCoordIdeal (M'.x ∘ Cv.v) := by
      show mConeMap (M'.x ∘ Cv.v) f = 0
      rw [key, h0, map_zero]
    have h2 : rename Cv.v f ∈ mCoordIdeal M'.x :=
      GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal.mCoordIdeal_comp_le_imageZ _ _ _ _ Cv.κ Cv.v _ M'.x hb h1
    have h3 := hz.2 _ h2
    rwa [map_rename, eval_rename] at h3

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GeometricDegreeNonnegativePsh
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem nonneg_degree_horizontal_curve : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (Fl : Set σ), (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → Re.J = ⊤ → ∀ n : σ → ℤ, (∀ a ∉ Fl, 0 ≤ n a) → ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ geomDeg W (combLine Re.ref n) 1 :=
  PositivityTheory.Xgp.t_nef_curve

end GlobalTheory.CompanionTheory.Ar.PB
end

