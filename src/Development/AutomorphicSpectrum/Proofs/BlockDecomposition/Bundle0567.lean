module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTrees
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.LimT

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def lr : {N : ℕ} → Tr E N → ℕ
  | _, .leaf _ _ => 0
  | _, @Tr.node _ _ _ _ r _ _ _ => r

theorem lr_le {N : ℕ} (u : Tr E N) : lr u ≤ N := by
  cases u with
  | leaf V z => exact Nat.zero_le _
  | node t₁ t₂ => exact Nat.le_add_right _ _

theorem leaf_of {N : ℕ} (u : Tr E N) (h : lr u = 0) (hr : Red u) : ∃ V z, u = .leaf V z := by
  cases u with
  | leaf V z => exact ⟨V, z, rfl⟩
  | node t₁ t₂ => exact absurd (show _ = 0 from h) hr.1.ne'

theorem node_of {n : ℕ} (u : Tr E n) {r s : ℕ} (h : n = r + s) (hl : lr u = r) (hr : 0 < r) (hred : Red u) :
    ∃ (t₁ : Tr E r) (t₂ : Tr E s), h ▸ u = Tr.node t₁ t₂ ∧ Red t₁ ∧ Red t₂ := by
  cases u with
  | leaf V z => exact absurd (show 0 = r from hl) hr.ne
  | @node r' s' t₁ t₂ =>
    have hl' : r' = r := hl
    subst hl'
    have hs : s' = s := by omega
    subst hs
    exact ⟨t₁, t₂, rfl, hred.2.2.1, hred.2.2.2⟩

theorem pigeon {n : ℕ} (c : ℕ → ℕ) (h : ∀ k, c k ≤ n) : ∃ (r : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, c (φ k) = r := by
  let f : ℕ → Fin (n + 1) := fun k => ⟨c k, Nat.lt_succ_of_le (h k)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  obtain ⟨φ, hφ, h2⟩ := extraction_of_frequently_atTop (P := fun k => f k = y)
    (Nat.frequently_atTop_iff_infinite.mpr hinf)
  exact ⟨y, φ, hφ, fun k => congrArg Fin.val (h2 k)⟩

theorem emb_refl {N : ℕ} (V : Submodule ℂ (Sm E N)) : Emb V (· ∈ V) :=
  ⟨LinearMap.id, fun _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩

theorem main (hc : ConvComp) (hs : TrStable) (hg : Graft)
    (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ)
    (hL : LimLeafP N Θs Ωs Θf Ωf) (hR : ReproAll E) (n : ℕ) : n ≤ N → ∀ (t : ℕ → Tr E n) (R : ℝ), (∀ k, Red (t k)) →
    (∀ k, (t k).Good) → (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) →
    (∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (t k)) →
    ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E n) (s : Tr E n), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t' k).Disc) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn t R hred hgood hlist hz
  obtain ⟨r, φ₀, hφ₀, hr⟩ := pigeon (n := n) (fun k => lr (t k)) (fun k => lr_le _)
  by_cases h0 : r = 0
  · subst h0
    choose V z hVz using fun k => leaf_of (t (φ₀ k)) (hr k) (hred _)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hk : ∀ k, t (φ₀ k) = .leaf ⊤ 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨-, hV, hz'⟩ | ⟨h, -, -⟩
        · rw [hVz k, hV, hz']
        · exact absurd h (lt_irrefl _)
      refine ⟨φ₀, fun _ => .leaf ⊤ 0, .leaf ⊤ 0, hφ₀, Conv.leaf ⊤ (fun _ => 0) 0 tendsto_const_nhds, trivial,
        Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩, fun k => ?_⟩
      rw [hk k]
      exact emb_refl _
    · have hG : ∀ k, IsDiscrete (V k) ∧ (z k).re = 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨h, -, -⟩ | ⟨-, h⟩
        · exact absurd h hn0.ne'
        · exact h
      have hT : ∀ k, ∃ K' ∈ Θs n, ∃ W' ∈ Ωs n, HasType K' W' (V k) := by
        intro k
        have h := hlist (φ₀ k)
        rw [hVz k] at h
        rcases h with h | h
        · exact absurd h hn0.ne'
        · exact h
      have hB : ∀ k, InfBdd R (V k) ∧ ‖z k‖ ≤ R := by
        intro k
        have h := hz (φ₀ k)
        rw [hVz k] at h
        exact h hn0
      obtain ⟨φ, t', s, hφ, hc', hrs, hgs, hls, hd, he⟩ := hL n hn0 hn V z R hR (fun k => (hG k).1)
        (fun k => (hG k).2) hT (fun k => (hB k).1) (fun k => (hB k).2)
      refine ⟨φ₀ ∘ φ, t', s, hφ₀.comp hφ, hc', hrs, hgs, hls, hd, fun k => ?_⟩
      have e : t ((φ₀ ∘ φ) k) = .leaf (V (φ k)) (z (φ k)) := hVz _
      rw [e]
      exact he k
  · have hr0 : 0 < r := Nat.pos_of_ne_zero h0
    have hrn : r ≤ n := by
      have := lr_le (t (φ₀ 0))
      rwa [hr 0] at this
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
    choose a b hab ha hb using fun k => node_of (t (φ₀ k)) rfl (hr k) hr0 (hred _)
    have hab' : ∀ k, t (φ₀ k) = .node (a k) (b k) := hab
    have hs0 : 0 < s := by
      have h := hred (φ₀ 0)
      rw [hab' 0] at h
      exact h.2.1
    have hG : ∀ k, (a k).Good ∧ (b k).Good := fun k => by
      have h := hgood (φ₀ k)
      rw [hab' k] at h
      exact h
    have hT : ∀ k, (a k).AllLeaves (ListLeaf Θs Ωs) ∧ (b k).AllLeaves (ListLeaf Θs Ωs) := fun k => by
      have h := hlist (φ₀ k)
      rw [hab' k] at h
      exact h
    have hB : ∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (a k) ∧
        LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (b k) := fun k => by
      have h := hz (φ₀ k)
      rw [hab' k] at h
      exact h
    obtain ⟨φ₁, a', sa, hφ₁, hca, hra, hga, hla, hda, hea⟩ := ih r (by omega) (by omega) a R ha
      (fun k => (hG k).1) (fun k => (hT k).1) (fun k => (hB k).1)
    obtain ⟨φ₂, b', sb, hφ₂, hcb, hrb, hgb, hlb, hdb, heb⟩ := ih s (by omega) (by omega) (fun k => b (φ₁ k)) R
      (fun k => hb _) (fun k => (hG _).2) (fun k => (hT _).2) (fun k => (hB _).2)
    refine ⟨φ₀ ∘ φ₁ ∘ φ₂, fun k => .node (a' (φ₂ k)) (b' k), .node sa sb, hφ₀.comp (hφ₁.comp hφ₂),
      Conv.node (hc E r a' sa φ₂ hca hφ₂) hcb, ⟨hr0, hs0, hra, hrb⟩, ⟨hga, hgb⟩, ⟨hla, hlb⟩,
      fun k => ⟨hda _, hdb k⟩, fun k => ?_⟩
    have e : t ((φ₀ ∘ φ₁ ∘ φ₂) k) = .node (a (φ₁ (φ₂ k))) (b (φ₁ (φ₂ k))) := hab' _
    rw [e]
    exact hg E r s _ _ _ _ (hs E _ _ (disc_stable (good_disc (hG _).1))) (hs E _ _ (disc_stable (hda _)))
      (hs E _ _ (disc_stable (good_disc (hG _).2))) (hs E _ _ (disc_stable (hdb _))) (hea (φ₂ k)) (heb k)

theorem limTrees : ConvComp → LimTrees := by
  intro hc hs hg E _ _ _ Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄
  exact main hc hs hg Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄

end GlobalTheory.CompanionTheory.EGlue.LimT

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocInert

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

def glEquiv {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R ≃+* S) (hf : Continuous f) (hf' : Continuous f.symm) (n : ℕ) : GL (Fin n) R ≃ₜ* GL (Fin n) S where
  toFun := GeneralLinearGroup.map f.toRingHom
  invFun := GeneralLinearGroup.map f.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _
  continuous_toFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf', Units.continuous_coe_inv.matrix_map hf'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev aw (w : Pl E) : Above (w.under (𝓞 (maximalRealSubfield E))) := ⟨w, rfl⟩

theorem eq_aw {w : Pl E} (hw : ¬ IsSplitAt w) (u : Above (w.under (𝓞 (maximalRealSubfield E)))) : u = aw w := by
  by_contra h
  exact hw ⟨u.1, fun e => h (Subtype.ext e), u.2⟩

def uniq {w : Pl E} (hw : ¬ IsSplitAt w) : Unique (Above (w.under (𝓞 (maximalRealSubfield E)))) :=
  ⟨⟨aw w⟩, eq_aw hw⟩

def evR {w : Pl E} (hw : ¬ IsSplitAt w) : Av (w.under (𝓞 (maximalRealSubfield E))) ≃+* w.adicCompletion E :=
  letI := uniq hw
  RingEquiv.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E

theorem evR_apply {w : Pl E} (hw : ¬ IsSplitAt w) (x : Av (w.under (𝓞 (maximalRealSubfield E)))) :
    evR hw x = x (aw w) := rfl

theorem continuous_evR {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw) :=
  continuous_apply (aw w)

theorem continuous_evR_symm {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw).symm := by
  letI := uniq hw
  exact (Homeomorph.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E).symm.continuous

def evY {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) :
    Yv a b (w.under (𝓞 (maximalRealSubfield E))) ≃ₜ* GLw a w × GLw b w where
  toMulEquiv := MulEquiv.prodCongr (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).toMulEquiv
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).toMulEquiv
  continuous_toFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).continuous
  continuous_invFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).symm.continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).symm.continuous

theorem evY_apply {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b y = evw (aw w) y := rfl

theorem cjv_apply (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w)
    (x : Av (w.under (𝓞 (maximalRealSubfield E)))) : evR hw (cjv _ x) = cj w (evR hw x) := by
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hc' := (h4 hw).2.2.1
  have h := hC E (w.under (𝓞 (maximalRealSubfield E)))
  set X : Af E := sLoc E w (evR hw x) with hX
  have hp : pLoc E w X = evR hw x := by
    change (Pi.single w (evR hw x) : ∀ u : Pl E, u.adicCompletion E) w = _
    simp
  have hx : projv _ X = x := by
    funext u
    obtain rfl := eq_aw hw u
    exact hp
  have hs : cjv (w.under (𝓞 (maximalRealSubfield E))) = h.choose := by
    rw [cjv, dite_eq_left h]
  rw [← hx, hs, ← h.choose_spec.2 X]
  rw [evR_apply, evR_apply]
  exact hc' X

theorem evY_thv (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ)
    (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b (thv a b _ y) = ((thL a w).prodMap (thL b w)) (evY hw a b y) := by
  have h : ∀ n (g : GL (Fin n) (Av (w.under (𝓞 (maximalRealSubfield E))))),
      GeneralLinearGroup.map (evR hw).toRingHom (thetaGL n (cjv _) g) =
        thL n w (GeneralLinearGroup.map (evR hw).toRingHom g) := fun n g => by
    rw [thL, if_neg hw]
    exact GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_apply hC hU hw) g
  exact Prod.ext (h a y.1) (h b y.2)

theorem mem_Kv_iff {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    y ∈ Kv a b _ ↔ evY hw a b y ∈ K2 a b w := by
  rw [Kv, Subgroup.mem_iInf]
  constructor
  · intro h
    exact h (aw w)
  · intro h u
    obtain rfl := eq_aw hw u
    exact h

theorem evY_pv {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    evY hw a b (pv a b _ (ratF E a δ₁, ratF E b δ₂)) = (locEl a w δ₁, locEl b w δ₂) := by
  have h : ∀ n (δ : GL (Fin n) E), GeneralLinearGroup.map (evR hw).toRingHom
      (GeneralLinearGroup.map (projv (w.under (𝓞 (maximalRealSubfield E)))) (ratF E n δ)) = locEl n w δ := fun n δ => by
    rw [locEl, if_neg hw]
    ext i j
    rfl
  exact Prod.ext (h a δ₁) (h b δ₂)

theorem fv_eq {w : Pl E} (hw : ¬ IsSplitAt w) {a b : ℕ} {S : Set (Pl E)} (hS : w ∈ S)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    seen φ₁ φ₂ w (evY hw a b y) = fv S φ₁ φ₂ _ y := by
  letI := uniq hw
  rw [fv, finprod_unique]
  change _ = ∏ᶠ (_ : w ∈ S), φ₁ w (evw (aw w) y) * if IsSplitAt w then _ else 1
  rw [finprod_eq_if, if_pos hS, if_neg hw, mul_one, seen, if_neg hw, evY_apply]

theorem locCompareInert : LocCompareInert := by
  intro hC E _ _ _ hU a b S _ φ₁ φ₂ _ _ δ₁ δ₂ _ _ w hS hw
  rw [← evY_pv hw a b δ₁ δ₂]
  exact GlobalTheory.EulerTw.Transport.twOrb_transport _ _ (evY hw a b) _ _ _ _ _ _ _
    (evY_thv hC hU hw a b) (mem_Kv_iff hw a b) (fv_eq hw hS φ₁ φ₂)

end GlobalTheory.CompanionTheory.LocInert
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneZeroFibreVolume
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib


open scoped Pointwise in
theorem map_mul_fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    [lam.IsAddHaarMeasure] (x : Fv F v) (hx : x ≠ 0) (a : ℝ≥0) (ha : ‖x‖ = (a : ℝ)⁻¹) :
    lam.map (fun y => x * y) = a • lam := by
  open scoped Pointwise in
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = (a : ℝ)⁻¹ := by
    have h := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v x hx
    have he : Units.mk0 x hx = hu.unit := by
      ext
      simp
    rw [he] at h
    simpa [ha] using congrArg (fun z : ℝ≥0 => (z : ℝ)) h
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = a := by
    rw [map_inv]
    apply NNReal.coe_injective
    push_cast
    rw [hc]
    simp
  have hm : Measurable fun y : Fv F v => x * y := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, hc']
  rfl

theorem mass_scalT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (c : Fv F v ⊗[F] E) (a : ℝ≥0) (t : Fv F v), IsUnit c → a ≠ 0 → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = (a : ℝ)⁻¹ → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), MeasurableSet A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) {y | scalT c y ∈ A} = (a : ℝ≥0∞) ^ (M - 1) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) A := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₂ d b v lam hlam m hm c a t hcu ha hk hts hnorm A hA
  have hloc := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ht : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact inv_ne_zero ha' hnorm.symm
  have hs := map_mul_fv v lam t ht a hnorm
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun y => c * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk1 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => c
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact hcu
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf]
    rw [Subsingleton.elim p 0, mul_comm]
  obtain ⟨-, -, -, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Fv F v) 1
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S =>
    ⟨cT (sigR (Fv F v) σ) g * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) * g, hmem S g⟩
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g :=
    fun S => rfl
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    rw [hτ, hts]
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g,
      Matrix.of_apply]
    ring
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    have h1 : Continuous τ :=
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
    exact h1.measurable
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam t ht a hs τ hτm hτe
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
  have hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) =
      hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ := by
    have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0 := by
      apply Subtype.ext
      funext i j
      simp [hermOf]
    rw [h0]
    apply Subtype.ext
    rw [hτ]
    simp
  rw [hτs] at key
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' A) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : a ^ M = a * a ^ (M - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM]
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  have key3 := (ENNReal.mul_right_inj ha0 ENNReal.coe_ne_top).1 key2
  have hset : {y : Fin 1 → Fin M → Fv F v ⊗[F] E | scalT c y ∈ A} =
      (fun X => rmul (Fv F v) X g) ⁻¹' A := by
    rw [hrm]
    rfl
  rw [hset, ← key3]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogNormContinuousOffDivisor
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchInt

theorem continuousOn_logNorm_offSupp {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {q : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X} (ψ : GlobalTheory.Weight q σ L) (hψ : ψ.IsCInf)
    {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ContinuousOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) := by
  intro y hy
  obtain ⟨i, hi⟩ := GlobalTheory.CxPts.exists_mem_ptsIn (p := q) (σ := σ) ψ.isLB.cover y
  have hu : GlobalTheory.Cartier.UnitAt (GlobalTheory.Cartier.under y) ((r i : X.functionField)) :=
    GlobalTheory.Cartier.IsRatSec.unitAt ψ.isLB hr hy hi
  obtain ⟨V, hyV, hV⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hu
  have hgV : genericPoint X ∈ V := GlobalTheory.Cartier.gen_mem hyV
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hV
  have hyV' : y ∈ GlobalTheory.CxPts.ptsIn q σ V := GlobalTheory.CxPts.mem_ptsIn.2 hyV
  have hNo : IsOpen (GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr)) :=
    ((GlobalTheory.CxPts.isOpen_ptsIn V).inter (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
      (GlobalTheory.Cartier.isOpen_offSupp _)
  have hyN : y ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr) := ⟨⟨hyV', hi⟩, hy⟩
  have heq : ∀ z ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr),
      Real.log ‖GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2 =
        GlobalTheory.Cartier.logNorm ψ r z := by
    rintro z ⟨⟨hzV, hzi⟩, hz⟩
    rw [GlobalTheory.Cartier.logNorm_eq ψ hr hz hzi, ← ha hgV, GlobalTheory.Cartier.ratVal_fnOf hzV]
  have hne : GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) y ≠ 0 := by
    rw [← GlobalTheory.Cartier.ratVal_fnOf hyV' hgV, ha hgV]
    exact GlobalTheory.Cartier.ratVal_ne_zero hu
  have hev : ContinuousAt (GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V))) y :=
    (GlobalTheory.CxPts.continuousOn_ev _).continuousAt ((GlobalTheory.CxPts.isOpen_ptsIn V).mem_nhds hyV')
  have hφ : ContinuousAt (ψ.φ i) y := (hψ i y hi).continuousAt
  have hg : ContinuousAt (fun z => Real.log ‖GlobalTheory.CxPts.ev q σ V
      (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2) y :=
    (hev.norm.log (norm_ne_zero_iff.2 hne)).sub (hφ.div_const 2)
  exact (hg.congr (Filter.eventuallyEq_of_mem (hNo.mem_nhds hyN) heq)).continuousWithinAt

end GlobalTheory.CompanionTheory.MixZ.ArchInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryHeightBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_theory_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact C → ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → Real.exp (- s 0) ≤ M := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le | exact GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le | (intros; apply GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le <;> assumption)
end

