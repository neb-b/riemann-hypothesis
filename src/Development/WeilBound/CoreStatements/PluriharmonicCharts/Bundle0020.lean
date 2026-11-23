module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsBlockpos
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_blockpos

theorem posDef_fromBlocks {m n : Type} [Fintype m] [Fintype n] {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (Matrix.fromBlocks A 0 0 B).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hA hB ⊢
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.1, hB.1]; simp
  · have e : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 B *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
      rw [Matrix.fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type]
    rw [e]
    have h1 : 0 ≤ star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) := by
      by_cases h : x ∘ Sum.inl = 0
      · rw [h]; simp
      · exact (hA.2 h).le
    have h2 : 0 ≤ star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
      by_cases h : x ∘ Sum.inr = 0
      · rw [h]; simp
      · exact (hB.2 h).le
    by_cases h : x ∘ Sum.inl = 0
    · have h' : x ∘ Sum.inr ≠ 0 := fun h' => hx (funext fun i => by
        rcases i with i | i
        · exact congrFun h i
        · exact congrFun h' i)
      exact add_pos_of_nonneg_of_pos h1 (hB.2 h')
    · exact add_pos_of_pos_of_nonneg (hA.2 h) h2

end PositivityTheory.Xgp.c_bm_exists_blockpos

theorem PositivityTheory.Xgp.t_c_bm_exists_blockpos : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  intro p q Γ h
  refine ⟨fun a b hab => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
    simp only [blockG, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b
    · exact absurd (show (a : ℕ) < _ ↔ (b : ℕ) < _ by omega) hab
    · rfl
    · rfl
    · exact absurd (show q + (a : ℕ) < _ ↔ q + (b : ℕ) < _ by omega) hab
  · refine Matrix.PosDef.submatrix ?_ (blockEquiv p q).symm.injective
    exact PositivityTheory.Xgp.c_bm_exists_blockpos.posDef_fromBlocks
      (h.submatrix (omEmb_strictMono p q).injective).transpose.inv
      (h.submatrix (wEmb_strictMono p q).injective)
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsFrames
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_frames

open MvPolynomial Filter Topology

theorem continuousAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X)
    {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hx' : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simp [Set.mem_preimage, (A.chart j).left_inv hj, hx]⟩
  have h1 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) x := by
    refine ContinuousAt.comp ?_ ((A.chart j).continuousAt hj)
    exact (hf j _ hx').continuousAt
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mCoordIdeal_smul (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    mCoordIdeal (fun p : Σ k, ι k => c p.1 * z p) = mCoordIdeal z := by
  classical
  let φ : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ := aeval fun k => C (c k) * X k
  let ψ : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ := aeval fun k => C (c k)⁻¹ * X k
  have hψφ : ψ.comp φ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    simp only [φ, ψ, aeval_X, map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hcomp : (mConeMap (fun p : Σ k, ι k => c p.1 * z p)) = (φ.restrictScalars ℤ).comp (mConeMap z) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, φ, C_mul]
    ring
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker, AlgHom.coe_toRingHom, hcomp]
  constructor
  · intro h
    have h' := congrArg ψ h
    have e := AlgHom.congr_fun hψφ (mConeMap z f)
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at e
    simpa [e] using h'
  · intro h
    simp [h]

theorem X_notMem_iff (w : (Σ k, ι k) → ℂ) (q : Σ k, ι k) :
    (X q : MRing ι) ∉ mCoordIdeal w ↔ w q ≠ 0 := by
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, MvPolynomial.X_ne_zero]

theorem eventually_notMem {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) {w₀ : (Σ k, ι k) → ℂ}
    (h0 : h ∉ mCoordIdeal w₀) : ∀ᶠ w in 𝓝 w₀, h ∉ mCoordIdeal w := by
  have hiff : ∀ w : (Σ k, ι k) → ℂ, h ∈ mCoordIdeal w ↔
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) = 0 := by
    intro w
    rw [form_mem_mCoordIdeal_iff w hh, aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]
  have hc : Continuous fun w : (Σ k, ι k) → ℂ => MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have h0' : MvPolynomial.eval w₀ (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 := fun e => h0 ((hiff w₀).mpr e)
  filter_upwards [hc.continuousAt.eventually_ne h0'] with w hw
  exact fun hm => hw ((hiff w).mp hm)

theorem eventually_regAt {Ω : Type} [Field Ω] {x : (Σ k, ι k) → Ω} {s : Ω} {w₀ : (Σ k, ι k) → ℂ}
    (hs : RegAt x (mCoordIdeal w₀) s) : ∀ᶠ w in 𝓝 w₀, RegAt x (mCoordIdeal w) s := by
  obtain ⟨d, g, h, hg, hh, hQ, e⟩ := hs
  filter_upwards [eventually_notMem hh hQ] with w hw
  exact ⟨d, g, h, hg, hh, hw, e⟩

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] {N j : ℕ}

theorem eventually_goodAt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk)
    {w₀ : (Σ k, baseIdx ι M.blk k) → ℂ} (hF : M.GoodAt F (mCoordIdeal w₀)) :
    ∀ᶠ w in 𝓝 w₀, M.GoodAt F (mCoordIdeal w) := by
  obtain ⟨h1, h2, h3⟩ := hF
  have e1 : ∀ᶠ w in 𝓝 w₀, ∀ k, (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∉ mCoordIdeal w := by
    refine Filter.eventually_all.2 fun k => ?_
    have h := (X_notMem_iff w₀ _).1 (h1 k)
    filter_upwards [(continuous_apply (⟨k, F.c k⟩ : Σ k, baseIdx ι M.blk k)).continuousAt.eventually
      (isOpen_ne.mem_nhds h)] with w hw
    exact (X_notMem_iff w _).2 hw
  have e2 : ∀ᶠ w in 𝓝 w₀, ∀ q I, RegAt M.x (mCoordIdeal w) (F.u q I) ∧ RegAt M.x (mCoordIdeal w) (F.u' I q) :=
    Filter.eventually_all.2 fun q => Filter.eventually_all.2 fun I =>
      (eventually_regAt (h2 q I).1).and (eventually_regAt (h2 q I).2)
  have e3 : ∀ᶠ w in 𝓝 w₀, ∀ p, M.blk p = none → F.υ p ≠ 0 ∧ RegAt M.x (mCoordIdeal w) (F.υ p) ∧
      RegAt M.x (mCoordIdeal w) (F.υ p)⁻¹ := by
    refine Filter.eventually_all.2 fun p => ?_
    by_cases hp : M.blk p = none
    · obtain ⟨a, b, c⟩ := h3 p hp
      filter_upwards [eventually_regAt b, eventually_regAt c] with w hb hc
      exact fun _ => ⟨a, hb, hc⟩
    · exact Filter.Eventually.of_forall fun _ h => absurd h hp
  filter_upwards [e1, e2, e3] with w a b c
  exact ⟨a, b, c⟩

end PositivityTheory.Xgp.c_bm_exists_frames

theorem PositivityTheory.Xgp.t_c_bm_exists_frames : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), ∃ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι Ψ N M.Ω M.blk), (∀ l, IsOpen (O l)) ∧ (∀ x, ∃ l, x ∈ O l) ∧ (∀ l, M.IsFrame (F l)) ∧ ∀ l, ∀ x ∈ closure (O l), M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j n M Rb
  classical
  letI := Rb.top
  haveI := Rb.compact
  haveI := Rb.t2
  have key : ∀ x : Rb.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (t : Set Rb.X), M.IsFrame F ∧ t ∈ nhds x ∧
      IsClosed t ∧ ∀ z ∈ t, M.GoodAt F (mCoordIdeal (Rb.lift z z)) := by
    intro x
    have hw := Rb.mem x x (Rb.mem_U x)
    have hrel : IsRelevant (mCoordIdeal (Rb.lift x x)) := by
      intro k
      obtain ⟨i, hi⟩ := hw.1 k
      exact ⟨i, (PositivityTheory.Xgp.c_bm_exists_frames.X_notMem_iff _ _).mpr hi⟩
    obtain ⟨F, hFr, hG⟩ := M.frames _ (ValRing.isPrime_mCoordIdeal _) hrel (CPts.mCoordIdeal_le hw)
    have hcont : ContinuousAt (Rb.lift x) x := continuousAt_pi.mpr fun p =>
      PositivityTheory.Xgp.c_bm_exists_frames.continuousAt_of_holoOn Rb.A (Rb.holo x p) (Rb.mem_U x)
    have hev : ∀ᶠ z in nhds x, M.GoodAt F (mCoordIdeal (Rb.lift x z)) :=
      hcont.tendsto.eventually (PositivityTheory.Xgp.c_bm_exists_frames.eventually_goodAt M F hG)
    have hS : {z | z ∈ Rb.U x ∧ M.GoodAt F (mCoordIdeal (Rb.lift z z))} ∈ nhds x := by
      filter_upwards [hev, (Rb.isOpen_U x).mem_nhds (Rb.mem_U x)] with z hz hU
      refine ⟨hU, ?_⟩
      obtain ⟨c, hc, hceq⟩ := Rb.compat x z z ⟨hU, Rb.mem_U z⟩
      have e := PositivityTheory.Xgp.c_bm_exists_frames.mCoordIdeal_smul c hc (Rb.lift z z)
      rw [← hceq] at e
      rw [e] at hz
      exact hz
    obtain ⟨t, ht, htc, hts⟩ := exists_mem_nhds_isClosed_subset hS
    exact ⟨F, t, hFr, ht, htc, fun z hz => (hts hz).2⟩
  choose F t hFr ht htc hgood using key
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (t x))
    (fun x => isOpen_interior)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (ht x)⟩)
  let e := s.equivFin
  refine ⟨s.card, fun l => interior (t (e.symm l)), fun l => F (e.symm l), fun l => isOpen_interior, ?_,
    fun l => hFr _, ?_⟩
  · intro x
    have hx := hs (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    exact ⟨e ⟨i, hi⟩, by simpa using hx⟩
  · intro l x hx
    exact hgood _ x (closure_minimal interior_subset (htc _) hx)
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsSumframe
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem PositivityTheory.Xgp.isFrameAt_comap_gbS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (q : Cpt 𝔐.ξ), M.GoodAt F (ptIdeal 𝔐.ξ M.x q) → (Lat.comap (fun p => 𝔐.V (.inl τ) p ⊔ 𝔐.V (.inr τ) p) (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype).IsFrameAt (gbS tie F τ) q := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie F hF τ q hq
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, -, -, -, -, hind, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l (Xo l) c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S M.Ω _ _ M.x 𝔐 hβ
  have hdisj : Disjoint (𝔐.Vgen (.inr τ)) (𝔐.Vgen (.inl τ)) := hind.pairwiseDisjoint Sum.inr_ne_inl
  have hW : (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) q := tie.frameW q F hF hq τ
  obtain ⟨hex, hall⟩ := omBundle_dualFrame 𝔐 τ q (tie.frameO q F hF hq τ)
  have hd : ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
    have hex' : ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0 := hex
    unfold dualFam
    rw [dite_eq_left hex']
    exact hex'.choose_spec
  have hO := hall _ hd
  have e : (fun i => (gbS tie F τ i : 𝔐.Li)) =
      Sum.elim (fun b => (dualFam tie F τ b : 𝔐.Li)) (tie.wFrame F τ) ∘ (blockEquiv D.p D.q).symm := by
    funext i
    simp only [gbS, Function.comp]
    rcases (blockEquiv D.p D.q).symm i with a | a <;> rfl
  constructor
  · refine LinearIndependent.of_comp (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype ?_
    show LinearIndependent M.Ω (fun i => (gbS tie F τ i : 𝔐.Li))
    rw [e]
    refine (hO.1.sum_type hW.1 (hdisj.mono ?_ ?_)).comp _ (blockEquiv D.p D.q).symm.injective
    · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact (dualFam tie F τ b).2)
    · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact wFrame_mem tie F τ b)
  · have h1 : 𝔐.V (.inl τ) q = Submodule.span (regAt 𝔐.ξ q) (Set.range (tie.wFrame F τ)) := hW.2
    have h2 : 𝔐.V (.inr τ) q = Submodule.span (regAt 𝔐.ξ q) (Set.range fun b => (dualFam tie F τ b : 𝔐.Li)) := hO.2
    show (𝔐.V (.inl τ) q ⊔ 𝔐.V (.inr τ) q).comap
      ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) = _
    have hinj : Function.Injective
        ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) :=
      (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).injective_subtype
    have e' : 𝔐.V (.inl τ) q ⊔ 𝔐.V (.inr τ) q = (Submodule.span (regAt 𝔐.ξ q) (Set.range (gbS tie F τ))).map
        ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) := by
      rw [Submodule.map_span, ← Set.range_comp, h1, h2, ← Submodule.span_union, Set.union_comm, ← Set.Sum.elim_range]
      congr 1
      refine Eq.trans ?_ (congrArg Set.range e.symm)
      exact ((blockEquiv D.p D.q).symm.surjective.range_comp _).symm
    rw [e', Submodule.comap_map_eq_of_injective hinj]
end

