module

public import Mathlib
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0020
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0018
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorSingle
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.IsMultiHomogMapConj
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial Filter Topology

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)

theorem holoOn_mono {U V : Set X} {f : X → ℂ} (h : A.HoloOn U f) (hVU : V ⊆ U) : A.HoloOn V f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_const (U : Set X) (c : ℂ) : A.HoloOn U (fun _ => c) := fun _ _ _ => analyticAt_const

theorem holoOn_mul {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U (fun y => f y * g y) := fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_div {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) (h0 : ∀ y ∈ U, g y ≠ 0) :
    A.HoloOn U (fun y => f y / g y) := fun j z hz => (hf j z hz).div (hg j z hz) (h0 _ hz.2)

theorem holoOn_pow {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) (m : ℕ) : A.HoloOn U (fun y => f y ^ m) :=
  fun j z hz => (hf j z hz).pow m

theorem holoOn_prod {U : Set X} {ι : Type} (s : Finset ι) {f : ι → X → ℂ} (hf : ∀ i ∈ s, A.HoloOn U (f i)) :
    A.HoloOn U (fun y => ∏ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holoOn_const A U 1
  | insert i s hi ih =>
    have h1 := holoOn_mul A (hf i (Finset.mem_insert_self i s)) (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.prod_insert hi] using h1

theorem holo_continuousAt {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) :
    ContinuousAt f x :=
  PositivityTheory.Xgp.c_bm_exists_frames.continuousAt_of_holoOn A hf hx

theorem holo_continuousOn {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) : ContinuousOn f U :=
  fun _ hx => (holo_continuousAt A hf hx).continuousWithinAt

theorem holoOn_coord {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) (i : Fin e) :
    A.HoloOn ψ.source (fun y => ψ y i) := fun j z hz =>
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticAt _).comp ((hψ j).1 z hz)

theorem exists_coords_ne (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) {O : Set X} (hO : IsOpen O) {y : X}
    (hy : y ∈ O) (hyψ : y ∈ ψ.source) : ∃ y' ∈ O ∩ ψ.source, ∀ i, ψ y' i ≠ 0 := by
  have hD : Dense (Set.pi Set.univ fun _ : Fin e => ({0}ᶜ : Set ℂ)) :=
    dense_pi Set.univ fun _ _ => dense_compl_singleton 0
  have hopen : IsOpen (ψ '' (ψ.source ∩ O)) := ψ.isOpen_image_source_inter hO
  obtain ⟨t, ⟨y', ⟨hy'ψ, hy'O⟩, rfl⟩, ht⟩ := hD.inter_open_nonempty _ hopen ⟨ψ y, y, ⟨hyψ, hy⟩, rfl⟩
  exact ⟨y', ⟨hy'O, hy'ψ⟩, fun i => ht i (Set.mem_univ i)⟩

theorem eqOn_of_coords_ne {β : Type} [NormedAddCommGroup β] (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {O : Set X} (hO : IsOpen O) (hOψ : O ⊆ ψ.source) {f g : X → β} (hf : ContinuousOn f O) (hg : ContinuousOn g O)
    (h : ∀ y ∈ O, (∀ i, ψ y i ≠ 0) → f y = g y) : ∀ y ∈ O, f y = g y := by
  intro y hy
  by_contra hne
  have hopen : IsOpen (O ∩ (fun z => f z - g z) ⁻¹' {0}ᶜ) :=
    (hf.sub hg).isOpen_inter_preimage hO isOpen_compl_singleton
  obtain ⟨y', ⟨⟨hy'O, hy'ne⟩, -⟩, hc⟩ := exists_coords_ne ψ hopen ⟨hy, sub_ne_zero.2 hne⟩ (hOψ hy)
  exact hy'ne (sub_eq_zero.2 (h y' hy'O hc))

end Holo

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_smul_homog {G : MvPolynomial (Σ k, J k) ℂ} {a : K → ℕ} (hG : IsMultiHomog G a) (c : K → ℂ)
    (z : (Σ k, J k) → ℂ) : eval (fun p => c p.1 * z p) G = (∏ k, c k ^ a k) * eval z G := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h1 : ∏ p, (c p.1 * z p) ^ d p = (∏ k, c k ^ a k) * ∏ p, z p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hG d hd k]
  rw [h1]
  ring

theorem eval_map_conj (G : MvPolynomial (Σ k, J k) ℂ) (z : (Σ k, J k) → ℂ) :
    eval z (map (starRingEnd ℂ) G) = starRingEnd ℂ (eval (fun p => starRingEnd ℂ (z p)) G) := by
  rw [MvPolynomial.eval_map, show ∀ w, MvPolynomial.eval w G = eval₂ (RingHom.id ℂ) w G from fun w => rfl,
    MvPolynomial.eval₂_comp_left,
    RingHom.comp_id]
  congr 1
  funext p
  simp

theorem isMultiHomog_map_conj {G : MvPolynomial (Σ k, J k) ℂ} {a : K → ℕ} (hG : IsMultiHomog G a) :
    IsMultiHomog (map (starRingEnd ℂ) G) a := fun m hm => hG m (support_map_subset _ _ hm)

noncomputable def nd (a : K → ℕ) (z : (Σ k, J k) → ℂ) : ℝ := ∏ k, (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k

theorem nd_smul (a : K → ℕ) (c : K → ℂ) (z : (Σ k, J k) → ℂ) :
    nd a (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ (2 * a k)) * nd a z := by
  unfold nd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : ∑ i, ‖c k * z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    simp [norm_mul, mul_pow, Finset.mul_sum]
  rw [this, mul_pow, ← pow_mul]

theorem nd_conj (a : K → ℕ) (z : (Σ k, J k) → ℂ) : nd a (fun p => starRingEnd ℂ (z p)) = nd a z := by
  simp [nd]

theorem nd_pos (a : K → ℕ) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < nd a z := by
  refine Finset.prod_pos fun k _ => pow_pos ?_ _
  obtain ⟨i, hi⟩ := hz k
  exact Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩

theorem continuous_nd (a : K → ℕ) : Continuous (nd (J := J) a) :=
  continuous_finsetProd _ fun k _ =>
    (continuous_finsetSum _ fun i _ => (continuous_norm.comp (continuous_apply _)).pow 2).pow _

theorem term_smul {G : MvPolynomial (Σ k, J k) ℂ} {a : K → ℕ} (hG : IsMultiHomog G a) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    ‖eval (fun p => c p.1 * z p) G‖ ^ 2 / nd a (fun p => c p.1 * z p) = ‖eval z G‖ ^ 2 / nd a z := by
  rw [eval_smul_homog hG, nd_smul, norm_mul, mul_pow, norm_prod]
  have h1 : (∏ k, ‖c k ^ a k‖) ^ 2 = ∏ k, ‖c k‖ ^ (2 * a k) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, ← pow_mul, mul_comm]
  have hne : (∏ k, ‖c k‖ ^ (2 * a k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [h1, mul_div_mul_left _ _ hne]

end Forms

end PositivityTheory.Xgp.c_bm_exists_boundary
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.WCoZero
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section
namespace PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem wCo_zero (M : FlagModel y Ψ N j) {p : Ψ × Fin N} {k₀ : K} (hk : M.blk p = some k₀) (ca cb : Fin N)
    (m : ι k₀) : M.wCo p k₀ ca cb 0 ⟨none, m⟩ = M.wCo p k₀ ca cb 0 ⟨some k₀, m⟩ := by
  simp only [FlagModel.wCo, Matrix.single_zero, add_zero, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [M.y_step p k₀ hk m, map_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [map_mul, CPts.minorIJ_map]

def mkAlg (M : FlagModel y Ψ N j) {d : ℕ} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N} (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀) (hca : (ca : ℕ) = lastCol N j a)
    (hcb : (cb : ℕ) = ca + 1) (hy : IsArithVar (mCoordIdeal y) (d + 2)) (xi2 : K → ℤ) (hxi : xi2 k₀ = -2)
    (g h : MRing fun o : Option K => ι (o.getD k₀)) (dg dh : Option K → ℕ) (hg : IsMultiHomog g dg)
    (hh : IsMultiHomog h dh) (hgn : g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))
    (hhn : h ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))
    (hdeg : ∀ o : Option K, (dg o : ℤ) - dh o = o.elim 1 fun k => -xi2 k - (if M.blk (τ, a) = some k then 1 else 0))
    (hdiv : divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) g =
      divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) h +
        Finsupp.single (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) 1) :
    AlgSq (mCoordIdeal y) d k₀ xi2 where
  arithY := hy
  xi_two_base_eq_neg_two := hxi
  KW := Option K
  ιW := fun o => ι (o.getD k₀)
  PW := mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)
  arithW := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).1
  κ := ![some, κ₁ k₀]
  v := ![v₀ k₀, v₁ k₀]
  block := Fin.forall_fin_two.2 ⟨Pts.isBlockMap_v₀ k₀, isBlockMap_v₁ k₀⟩
  image := Fin.forall_fin_two.2 ⟨(t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.1,
    (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.2 (v₁ k₀) (fun _ h => v₁_ne h)
      (v₁_self k₀)⟩
  same p hp := (v₁_ne hp).symm
  new := by
    rintro ⟨k, hk'⟩
    have : some k = κ₁ k₀ k₀ := hk'
    rw [κ₁_self] at this
    cases this
  all k' := by
    cases k' with
    | none => exact Or.inr (κ₁_self k₀).symm
    | some k => exact Or.inl ⟨k, rfl⟩
  fibre_line := t_c_w_line K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb
  Δ := mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)
  arithΔ := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.1
  PW_le := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.1
  diag i i' := by
    show mConeMap _ (X (v₀ k₀ ⟨k₀, i⟩) * X (v₁ k₀ ⟨k₀, i'⟩) - X (v₀ k₀ ⟨k₀, i'⟩) * X (v₁ k₀ ⟨k₀, i⟩)) = 0
    rw [v₁_self, v₁_self]
    simp only [mConeMap, map_sub, map_mul, aeval_X, v₀, wCo_zero M hk]
    ring
  g := g
  h := h
  dg := dg
  dh := dh
  g_deg := hg
  h_deg := hh
  g_nmem := hgn
  h_nmem := hhn
  deg_eq o := by
    show _ = -(pullDeg some xi2 o + pullDeg (κ₁ k₀) xi2 o)
    rw [hdeg, pullDeg_some, pullDeg_κ₁]
    cases o with
    | none => simp [hxi]
    | some k =>
      simp only [Option.elim, hk, Option.some.injEq]
      by_cases e : k = k₀
      · subst e; simp [hxi]
      · rw [if_neg e, if_neg (Ne.symm e)]; ring
  div_eq := hdiv

end PositivityTheory.Xgp.c_algsq
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCCovSelf
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace PositivityTheory.Xgp.c_cov_self

open GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

def idCover (M : FlagModel y Ψ N j) : FlagCover M M where
  κ := id
  v := id
  block := ⟨Function.injective_id, Function.injective_id, fun _ => rfl, fun q _ => ⟨q, rfl⟩⟩
  φ := RingHom.id _
  x_eq _ := rfl
  deg_pos := by
    show 0 < IntermediateField.relfinrank (blockFnField M.x) (blockFnField M.x)
    rw [IntermediateField.relfinrank_self]; exact one_pos
  agree z hz F' F h' h g' g τ a b := ⟨all_mem hz h h' g g' τ a b, all_mem hz h' h g' g τ a b⟩

theorem trans_eq (M : FlagModel y Ψ N j) (F' F : FrameData ι Ψ N M.Ω M.blk) (zb) (τ : Ψ) :
    (idCover M).trans F' F zb τ = valMat M.x zb ((F.T τ)⁻¹ * F'.T τ) := rfl

theorem log_refNorm_congr {a : K → ℤ} {z z' : (Σ k, ι k) → ℂ}
    (h : ∀ k, a k ≠ 0 → ∀ m, z ⟨k, m⟩ = z' ⟨k, m⟩) : refNorm a z = refNorm a z' := by
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : a k = 0
  · simp [hk]
  · simp only [h k hk]

theorem metric_self [Fintype Ψ] [DecidableEq Ψ] (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ)
    (hz : z ∈ mcPts (mCoordIdeal y)) (z₀ : (Σ k, ι k) → ℂ) (F' F : FrameData ι Ψ N M.Ω M.blk)
    (h' : M.IsFrame F') (h : M.IsFrame F) (g' : M.GoodAt F' (mCoordIdeal (basePart M.blk z)))
    (g : M.GoodAt F (mCoordIdeal (basePart M.blk z))) (ho : SameOrbit (basePart M.blk z₀) (basePart M.blk z))
    (p : Ψ × Fin N) (H : Matrix (Fin N) (Fin N) ℂ) (hH : IsBlockDiag j H) (e' : ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' p z H)
    (e : ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F p z₀ ((idCover M).trans F' F (basePart M.blk z) p.1 * H)) :
    Real.log ((fsHerm ι (M.dy p)).h z) + M.upsLog F' p z =
      Real.log ((fsHerm ι (M.dy p)).h z₀) + M.upsLog F p z₀ +
        Real.log ‖detFac j p.2 ((idCover M).trans F' F (basePart M.blk z) p.1)‖ := by
  have hzb := CPts.base_mem M hz
  have hT := FibreCount.trans_unit (idCover M) hzb h' h g' g p.1
  have hd := CPts.detFac_ne_zero M.j_le p.2 hT.1 hT.2
  have hρ := rhoC_ne g g' p
  have hval : ∀ s, valAt M.x s (basePart M.blk z₀) = valAt M.x s (basePart M.blk z) := valAt_orbit ho hzb
  rw [trans_eq] at hd e ⊢
  set dd := detFac j p.2 (valMat M.x (basePart M.blk z) ((F.T p.1)⁻¹ * F'.T p.1)) with hdd
  set ρ := rhoC M F F' p (basePart M.blk z) with hρd
  obtain ⟨c, hc, hco⟩ := ho
  have hρc : ρ = ∏ k, c k ^ M.b p k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    have h1 := e.1 k
    rw [hco] at h1
    rw [e'.1 k, one_div, ← eq_inv_of_mul_eq_one_left h1]
  let t : K → ℂ := fun k => if hk : ∀ p', M.blk p' ≠ some k then c ⟨k, hk⟩ else
    if M.blk p = some k then ρ / dd else 1
  have ht : ∀ k, t k ≠ 0 := fun k => by
    simp only [t]
    split_ifs
    · exact hc _
    · exact div_ne_zero hρ hd
    · exact one_ne_zero
  have e1 : refNorm (M.dy p) z₀ = refNorm (M.dy p) fun q => t q.1 * z q := by
    refine log_refNorm_congr fun k hk m => ?_
    by_cases hb : ∀ p', M.blk p' ≠ some k
    · simp only [t, dif_pos hb]
      exact congrFun hco ⟨⟨k, hb⟩, m⟩
    · have hp : M.blk p = some k := by
        by_contra hp
        exact hk (by simp only [FlagModel.dy, dif_neg hb, if_neg hp])
      simp only [t, dif_neg hb, if_pos hp]
      have r := relC hzb h h' g g' hp H hH m
      rw [e.2 k hp m, e'.2 k hp m]
      simp only [hval]
      rw [← hdd, ← hρd] at r
      field_simp
      linear_combination r
  have e2 : (∏ k, ‖t k‖ ^ M.dy p k) = ‖ρ‖⁻¹ * (M.blk p).elim 1 fun _ => ‖ρ‖ / ‖dd‖ := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => ∀ p', M.blk p' ≠ some k)]
    congr 1
    · rw [hρc, norm_prod, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr (by congr; exact Subsingleton.elim _ _) fun k _ => ?_
      simp only [t, FlagModel.dy, dif_pos k.2, _root_.zpow_neg, norm_zpow]
    · cases hp : M.blk p with
      | none =>
        refine Finset.prod_eq_one fun k _ => ?_
        have : M.blk p ≠ some k.1 := by rw [hp]; simp
        simp only [FlagModel.dy, dif_neg k.2, if_neg this, _root_.zpow_zero]
      | some k₀ =>
        have hk₀ : ¬ ∀ p', M.blk p' ≠ some k₀ := fun e => e p hp
        rw [Finset.prod_eq_single ⟨k₀, hk₀⟩]
        · simp only [t, FlagModel.dy, dif_neg hk₀, if_pos hp, _root_.zpow_one, norm_div, Option.elim_some]
        · intro k _ hk
          have : M.blk p ≠ some k.1 := fun e => hk (Subtype.ext (Option.some.inj (e.symm.trans hp)))
          simp only [FlagModel.dy, dif_neg k.2, if_neg this, _root_.zpow_zero]
        · simp
  have e3 := (fsHerm ι (M.dy p)).smul t z ht
  have hpos := (fsHerm ι (M.dy p)).pos z hz.1
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ
  have hdn : 0 < ‖dd‖ := norm_pos_iff.2 hd
  have e4 : (fsHerm ι (M.dy p)).h z₀ =
      (‖ρ‖⁻¹ * (M.blk p).elim 1 fun _ => ‖ρ‖ / ‖dd‖) * (fsHerm ι (M.dy p)).h z := by
    rw [← e2]; exact e1.trans e3
  rw [e4]
  unfold FlagModel.upsLog
  cases hp : M.blk p with
  | none =>
    have r := congrArg (fun w => Real.log ‖w‖) (rel0C hzb h h' g g' hp)
    have u1 := norm_pos_iff.2 (ups_ne hzb g hp)
    have u2 := norm_pos_iff.2 (ups_ne hzb g' hp)
    simp only [← hdd, ← hρd, norm_mul] at r
    rw [Real.log_mul hdn.ne' u1.ne', Real.log_mul hρn.ne' u2.ne'] at r
    simp only [Option.elim_none, mul_one, hval]
    rw [Real.log_mul (inv_pos.2 hρn).ne' hpos.ne', Real.log_inv]
    linarith
  | some k =>
    simp only [Option.elim_some]
    rw [← mul_div_assoc, inv_mul_cancel₀ hρn.ne', Real.log_mul (one_div_pos.2 hdn).ne' hpos.ne', one_div,
      Real.log_inv]
    ring

theorem isImg_self [Fintype Ψ] [DecidableEq Ψ] (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ)
    (hz : z ∈ mcPts (mCoordIdeal y)) (F' F : FrameData ι Ψ N M.Ω M.blk)
    (h' : M.IsFrame F') (h : M.IsFrame F) (g' : M.GoodAt F' (mCoordIdeal (basePart M.blk z)))
    (g : M.GoodAt F (mCoordIdeal (basePart M.blk z))) (H : Ψ → Matrix (Fin N) (Fin N) ℂ) (hH : M.IsFlagOf F' z H) :
    ∃ z₀, SameOrbit z₀ z ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk z) ∧
      M.IsFlagOf F z₀ fun τ => (idCover M).trans F' F (basePart M.blk z) τ * H τ := by
  have hzb := CPts.base_mem M hz
  have hT := FibreCount.trans_unit (idCover M) hzb h' h g' g
  refine (GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F z _ h hzb g (fun τ => ⟨(hT τ).1.mul (hH.2.1 τ).1, by
    rw [det_mul]; exact mul_ne_zero (hT τ).2 (hH.2.1 τ).2⟩) fun p k hp => ?_).2
  obtain ⟨a, ha, hz'⟩ := hH.2.2 p k hp
  have hd := CPts.detFac_ne_zero M.j_le p.2 (hT p.1).1 (hT p.1).2
  have hρ := rhoC_ne g g' p
  refine ⟨a * detFac j p.2 ((idCover M).trans F' F (basePart M.blk z) p.1) / rhoC M F F' p (basePart M.blk z),
    div_ne_zero (mul_ne_zero ha hd) hρ, fun m => ?_⟩
  have r := relC hzb h h' g g' hp (H p.1) (hH.2.1 p.1).1 m
  rw [hz' m, plk, trans_eq, div_mul_eq_mul_div, mul_assoc, r]
  field_simp

end PositivityTheory.Xgp.c_cov_self
end

theorem PositivityTheory.Xgp.t_c_cov_self : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), ∃ (Cv : FlagCover M M) (CR : CovReal FA Cv), Cv.deg = 1 ∧ (∀ p, CR.Re.ref p = FA.Re.ref (some p)) ∧ ∀ p t, CR.Re.line p t = FA.Re.line (some p) t := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hJ : ∀ z, z ∉ mcPts FA.Re.J := fun z h => by
    rw [FA.J_top] at h
    simpa using h.2 1 trivial
  have hne : Nonempty FA.S.X := FA.Re.nonempty_base
  let ϖ : ((Σ k, ι k) → ℂ) → FA.S.X := fun z =>
    if h : ∃ x, SameOrbit (FA.Re.R.lift x x) z then FA.Re.π h.choose else hne.some
  have hϖ : ∀ z x, SameOrbit (FA.Re.R.lift x x) z → ϖ z = FA.Re.π x := by
    intro z x hx
    have h : ∃ x, SameOrbit (FA.Re.R.lift x x) z := ⟨x, hx⟩
    simp only [ϖ, dif_pos h]
    rw [FA.Re.R.inj _ x (hJ _) (Cj.sameOrbit_trans h.choose_spec (Cj.sameOrbit_symm hx))]
  have hinj : Function.Injective FA.Re.π := by
    intro x x' hx
    have h1 := FA.Re.degree.2.2.2.2.1 (FA.Re.π x') (by rw [FA.br_empty]; exact Set.notMem_empty _)
    rw [FA.deg_one, Set.ncard_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    have m1 : x ∈ FA.Re.π ⁻¹' {FA.Re.π x'} := hx
    have m2 : x' ∈ FA.Re.π ⁻¹' {FA.Re.π x'} := rfl
    rw [ha] at m1 m2
    exact m1.trans m2.symm
  have hdeg : (PositivityTheory.Xgp.c_cov_self.idCover M).deg = 1 := IntermediateField.relfinrank_self _
  refine ⟨PositivityTheory.Xgp.c_cov_self.idCover M,
    { Re := FA.Re.comap some
      deg_eq := FA.deg_one.trans hdeg.symm
      ref_deg := fun p => congrArg HermLine.a (FA.ref_some p)
      step := FA.step
      ϖ := ϖ
      ϖ_torus := ?_
      π_eq := fun x => (hϖ _ x (Cj.sameOrbit_refl _)).symm
      line_pt := ?_
      flags := ?_
      metric := ?_ }, hdeg, fun _ => rfl, fun _ _ => rfl⟩
  · intro z z' hz ho
    obtain ⟨x, hx⟩ := FA.Re.R.surj z hz (hJ z)
    rw [hϖ z x hx, hϖ z' x (Cj.sameOrbit_trans hx (Cj.sameOrbit_symm ho))]
  · intro p t h0 h1 z hz
    obtain ⟨x, hx⟩ := FA.Re.R.surj z hz (hJ z)
    have e1 := FA.Re.line_eq (some p) t h0 h1 x
    have e2 := Cj.log_sub_orbit _ _ (FA.Re.line_deg (some p) t) hz.1 hx
    rw [hϖ z x hx]
    show Real.log ((FA.Re.line (some p) t).h z) = Real.log ((FA.Re.ref (some p)).h z) + _
    linarith
  · intro z hz F' F h' h g' g H hH x₀ hx₀
    obtain ⟨x, hx⟩ := FA.Re.R.surj z hz (hJ z)
    rw [hϖ z x hx] at hx₀
    obtain rfl := hinj hx₀
    obtain ⟨z₀, o1, o2, fl⟩ := PositivityTheory.Xgp.c_cov_self.isImg_self M z hz F' F h' h g' g H hH
    exact ⟨z₀, Cj.sameOrbit_trans o1 (Cj.sameOrbit_symm hx), o2, fl⟩
  · intro z hz z₀ _ F' F h' h g' g ho p H hH _ e' e
    have := PositivityTheory.Xgp.c_cov_self.metric_self M z hz z₀ F' F h' h g' g ho p H hH e' e
    rw [← FA.ref_some p] at this
    rw [← FA.ref_some p]
    exact this
end

