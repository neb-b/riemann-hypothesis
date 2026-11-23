module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling

namespace GlobalTheory.ZonalCellDecomposition

def blkEquiv (l t : ℕ) : Fin (l * t) ≃ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t :=
  finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin l) (Fin t)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mtor {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GL (A ⊕ D) k :=
  torusElt k (A ⊕ D) ϖ (Sum.elim 0 e)

def dcell {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    Set (GL (A ⊕ D) k) :=
  DoubleCoset.doubleCoset (mtor ϖ e) (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D : Set (GL (A ⊕ D) k))
    (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D)

def IsBiType {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ)
    (φ : GL (A ⊕ D) k → ℂ) : Prop :=
  ∀ j ∈ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    ∀ g, φ (j * g) = (ξ d : ℂ) * φ g ∧ φ (g * j) = (ξ d : ℂ) * φ g

def sumAbs {D : Type} [Fintype D] (e : D → ℤ) : ℤ := ∑ i, |e i|

def zonalInt {N : ℕ} [MeasurableSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) (ψ : GL (Fin N) k → ℂ)
    (g : GL (Fin N) k) : ℂ :=
  ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * g) ∂μK

def borelParam {N : ℕ} (q : ℕ) (α : Fin N → ℂˣ) (x : Fin N) : ℂ :=
  (α x : ℂ) * (q : ℂ) ^ (((x : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)

end GlobalTheory.ZonalCellDecomposition
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfDetEqOne
section
open scoped Matrix

namespace GlobalTheory.UTrans.CharDet

variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

theorem isU_one : IsU σ G 1 := fun x y => by simp

theorem isU_refl (hG : IsHerm σ G) {x : Fin n → E} {u : E} (hx : hf σ G x x ≠ 0) (hu : u * σ u = 1) :
    IsU σ G (tv σ G x ((u - 1) / hf σ G x x)) := by
  apply Calc.isU_tv σ G hG.invol hG.herm
  rw [map_div₀, Calc.hf_conj σ G hG.invol hG.herm, map_sub, map_one]
  field_simp
  linear_combination hu

theorem refl_mul {x : Fin n → E} (u v : E) (hx : hf σ G x x ≠ 0) :
    tv σ G x ((u - 1) / hf σ G x x) * tv σ G x ((v - 1) / hf σ G x x) =
      tv σ G x ((u * v - 1) / hf σ G x x) := by
  rw [Calc.tv_mul]
  congr 1
  field_simp
  ring

theorem refl_det {x : Fin n → E} (u : E) (hx : hf σ G x x ≠ 0) :
    (tv σ G x ((u - 1) / hf σ G x x)).det = u := by
  rw [Calc.tv_det]
  field_simp
  ring

theorem refl_one (x : Fin n → E) : tv σ G x ((1 - 1) / hf σ G x x) = 1 := by
  ext a b
  simp [tv]

variable [CharZero E] {A : Type} [CommGroup A] {X : Matrix (Fin n) (Fin n) E → A}

theorem char_refl_eq (hG : IsHerm σ G)
    (h : (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) ∨ ∀ x y : Fin n → E, hf σ G x x ≠ 0 → hf σ G y y ≠ 0 →
      ∃ a : E, hf σ G y y = σ a * a * hf σ G x x)
    (hX : ∀ a b, IsU σ G a → IsU σ G b → X (a * b) = X a * X b)
    {x y : Fin n → E} {u : E} (hx : hf σ G x x ≠ 0) (hy : hf σ G y y ≠ 0) (hu : u * σ u = 1) :
    X (tv σ G x ((u - 1) / hf σ G x x)) = X (tv σ G y ((u - 1) / hf σ G y y)) := by
  rcases h with h | h
  · obtain ⟨m, hm, e⟩ := quasiReflection_eq_tvGen_mul E n σ G hG h x y u hx hy hu
    rw [e, hX _ _ ((tvGen_normal E n σ G hG).2 m hm).1 (isU_refl hG hy hu),
      _root_.GlobalTheory.UTrans.TvKill.char_tvGen E n σ G hG A X hX m hm, one_mul]
  · obtain ⟨a, ha⟩ := h x y hx hy
    have h1 : hf σ G (a • x) (a • x) = hf σ G y y := by
      rw [Calc.hf_smul_left, Calc.hf_smul_right, ha]; ring
    obtain ⟨γ, hγ, e⟩ := (_root_.GlobalTheory.UTrans.ReflChar0.gen_and_witt E n σ G hG).2 y (a • x) hy h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
      exact hy ha
    have ha1 : σ a ≠ 0 := (map_ne_zero σ).2 ha0
    have h2 : tv σ G x ((u - 1) / hf σ G x x) = tv σ G (a • x) ((u - 1) / hf σ G y y) := by
      rw [Calc.tv_smul, ha]
      congr 1
      field_simp
    have h3 : γ * tv σ G x ((u - 1) / hf σ G x x) = tv σ G y ((u - 1) / hf σ G y y) * γ := by
      rw [h2, Calc.conj_tv σ G γ _ _ hγ, e]
    have h4 := congrArg X h3
    rw [hX _ _ hγ (isU_refl hG hx hu), hX _ _ (isU_refl hG hy hu) hγ, mul_comm] at h4
    exact mul_right_cancel h4

theorem char_prod (hG : IsHerm σ G)
    (h : (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) ∨ ∀ x y : Fin n → E, hf σ G x x ≠ 0 → hf σ G y y ≠ 0 →
      ∃ a : E, hf σ G y y = σ a * a * hf σ G x x)
    (hX : ∀ a b, IsU σ G a → IsU σ G b → X (a * b) = X a * X b)
    {x : Fin n → E} (hx : hf σ G x x ≠ 0) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) :
    IsU σ G (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod ∧
      X (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod =
        X (tv σ G x (((l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod.det - 1) / hf σ G x x)) := by
  induction l with
  | nil => exact ⟨isU_one, by simp only [List.map_nil, List.prod_nil, Matrix.det_one, refl_one]⟩
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨hp, hv⟩ := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons]
    refine ⟨Calc.isU_mul σ G _ _ (isU_refl hG hp hv) h1, ?_⟩
    rw [hX _ _ (isU_refl hG hp hv) h1, h2, char_refl_eq hG h hX hp hx hv, Matrix.det_mul, refl_det _ hp,
      ← refl_mul _ _ hx, hX _ _ (isU_refl hG hx hv) (isU_refl hG hx (h1.det_mul_conj_det hG.det_ne))]

end GlobalTheory.UTrans.CharDet

theorem GlobalTheory.UTrans.char_eq_one_of_det_eq_one : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ((∃ z : Fin n → E, z ≠ 0 ∧ GlobalTheory.UTrans.hf σ G z z = 0) ∨ ∀ x y : Fin n → E, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G y y ≠ 0 → ∃ a : E, GlobalTheory.UTrans.hf σ G y y = σ a * a * GlobalTheory.UTrans.hf σ G x x) → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ γ, GlobalTheory.UTrans.IsU σ G γ → γ.det = 1 → X γ = 1 := by
  intro E _ _ n σ G hG h A _ X hX γ hγ hd
  have h1 : X 1 = 1 := by
    have := hX 1 1 CharDet.isU_one CharDet.isU_one
    rw [mul_one] at this
    exact left_eq_mul.1 this
  obtain ⟨l, hl, e⟩ := (_root_.GlobalTheory.UTrans.ReflChar0.gen_and_witt E n σ G hG).1 γ hγ
  cases l with
  | nil => rw [e]; simpa using h1
  | cons p l =>
    have h2 := (CharDet.char_prod hG h hX (hl p List.mem_cons_self).1 _ hl).2
    rw [← e, hd, CharDet.refl_one] at h2
    rw [h2, h1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open Filter Topology

namespace GlobalTheory.SBUniform

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_deep (a : ℤ) : IsOpen {x : k | Deep a x} := by
  have hγ : (uniformizer k ^ a : ValueGroupWithZero k) ≠ 0 := zpow_ne_zero _ uniformizer_ne_zero
  unfold Deep
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 _ hγ, fun z hz => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hx ⊢

  have h := (valuation k).map_add (z - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hz.le hx)

theorem eventually_deep_subset {s : Set k} (hs : s ∈ 𝓝 (0 : k)) :
    ∀ᶠ M : ℕ in atTop, ∀ x : k, Deep (M : ℤ) x → x ∈ s := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs

  obtain ⟨M₀, hM₀⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) γ
  filter_upwards [eventually_ge_atTop M₀] with M hM x hx
  apply hγ
  unfold Deep at hx
  show valuation k x < γ
  have hle : uniformizer k ^ (M : ℤ) ≤ uniformizer k ^ (M₀ : ℤ) :=
    zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le (by exact_mod_cast hM)
  have hM₀' : uniformizer k ^ (M₀ : ℤ) < γ := by rwa [zpow_natCast]
  exact hx.trans_lt (hle.trans_lt hM₀')

theorem exists_deep_subset {n : Type} [Fintype n] {s : Set (Matrix n n k)} (hs : s ∈ 𝓝 (0 : Matrix n n k)) :
    ∃ M : ℕ, ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → y ∈ s := by
  have hs' : s ∈ 𝓝 (0 : n → n → k) := hs
  rw [nhds_pi] at hs'
  obtain ⟨I, -, t, ht, hts⟩ := Filter.mem_pi.1 hs'

  have ht' : ∀ i, ∃ J : Set n, J.Finite ∧ ∃ u : n → Set k, (∀ j, u j ∈ 𝓝 (0 : k)) ∧ J.pi u ⊆ t i := by
    intro i
    have hi : t i ∈ 𝓝 (0 : n → k) := ht i
    rw [nhds_pi] at hi
    exact Filter.mem_pi.1 hi
  choose J _ u hu hJu using ht'
  have hev : ∀ᶠ M : ℕ in atTop, ∀ i j, ∀ x : k, Deep (M : ℤ) x → x ∈ u i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact eventually_deep_subset (hu i j)
  obtain ⟨M, hM⟩ := hev.exists
  exact ⟨M, fun y hy => hts (Set.mem_pi.2 fun i _ => hJu i (Set.mem_pi.2 fun j _ => hM i j _ (hy i j)))⟩

private theorem deep_neg {a : ℤ} {x : k} (h : Deep a x) : Deep a (-x) := by
  unfold Deep at h ⊢
  rwa [Valuation.map_neg]

private theorem deep_add {a : ℤ} {x y : k} (hx : Deep a x) (hy : Deep a y) : Deep a (x + y) := by
  unfold Deep at hx hy ⊢
  exact ((valuation k).map_add x y).trans (max_le hx hy)

private theorem deep_zero' (a : ℤ) : Deep a (0 : k) := by
  unfold Deep
  simp

private theorem deep_of_le' {a b : ℤ} (hab : a ≤ b) {x : k} (h : Deep b x) : Deep a x := by
  unfold Deep at h ⊢
  exact h.trans (zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab)

private theorem exists_deep_neg_natCast (x : k) : ∃ N : ℕ, Deep (-(N : ℤ)) x := by
  unfold Deep
  by_cases hx : valuation k x = 0
  · exact ⟨0, by simp [hx]⟩

  obtain ⟨N, hN⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) (Units.mk0 _ (inv_ne_zero hx))
  refine ⟨N, ?_⟩
  rw [Units.val_mk0] at hN
  have hpos : (0 : ValueGroupWithZero k) < uniformizer k ^ N := pow_pos uniformizer_pos N
  have hx0 : (0 : ValueGroupWithZero k) < valuation k x := zero_lt_iff.2 hx
  rw [_root_.zpow_neg, zpow_natCast]
  exact ((lt_inv_comm₀ hpos hx0).1 hN).le

private theorem isOpen_setOf_forall_deep {n : Type} [Fintype n] (a : ℤ) :
    IsOpen {y : Matrix n n k | ∀ i j, Deep a (y i j)} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_deep (k := k) a).preimage (continuous_id.matrix_elem i j)

theorem exists_bound_period : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n], ∀ Φ ∈ SB (Matrix n n k),
    ∃ N M : ℕ, (∀ x, Φ x ≠ 0 → ∀ i j, Deep (-(N : ℤ)) (x i j)) ∧
      ∀ x y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x := by
  intro k _ _ _ _ n _ _ Φ hΦ
  have hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨hlc, hcs⟩ := hΦ'
  have hC : IsCompact (tsupport Φ) := hcs
  have hzero : ∀ z, z ∉ tsupport Φ → Φ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport Φ h)

  let U : ℕ → Set (Matrix n n k) := fun N => {x | ∀ i j, Deep (-(N : ℤ)) (x i j)}
  have hUm : Monotone U := fun N N' h x hx i j =>
    deep_of_le' (neg_le_neg (by exact_mod_cast h)) (hx i j)
  have hUcov : tsupport Φ ⊆ ⋃ N, U N := by
    intro x _
    have hev : ∀ᶠ N : ℕ in atTop, ∀ i j, Deep (-(N : ℤ)) (x i j) := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      obtain ⟨N₀, hN₀⟩ := exists_deep_neg_natCast (x i j)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      exact deep_of_le' (neg_le_neg (by exact_mod_cast hN)) hN₀
    obtain ⟨N, hN⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨N, hN⟩
  obtain ⟨N, hN⟩ := hC.elim_directed_cover U (fun N => isOpen_setOf_forall_deep _) hUcov hUm.directed_le

  let W : ℕ → Set (Matrix n n k) :=
    fun M => {x | ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x}
  have hWm : Monotone W := fun M M' h x hx y hy =>
    hx y fun i j => deep_of_le' (by exact_mod_cast h) (hy i j)
  have hWo : ∀ M, IsOpen (W M) := by
    intro M
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hD : {y : Matrix n n k | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 (0 : Matrix n n k) :=
      (isOpen_setOf_forall_deep _).mem_nhds fun i j => deep_zero' _
    have hD' : (fun z : Matrix n n k => z - x) ⁻¹' {y | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 x := by
      apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      simpa using hD
    refine Filter.mem_of_superset hD' fun z hz y hy => ?_
    have hz' : ∀ i j, Deep (M : ℤ) ((z - x) i j) := hz
    have h1 : Φ (x + ((z - x) + y)) = Φ x :=
      hx _ fun i j => by simpa using deep_add (hz' i j) (hy i j)
    have h2 : Φ (x + (z - x)) = Φ x := hx _ hz'
    rw [add_sub_cancel] at h2
    have he : x + ((z - x) + y) = z + y := by abel
    rw [he] at h1
    rw [h1, h2]
  have hWcov : tsupport Φ ⊆ ⋃ M, W M := by
    intro x _
    have hs : {y : Matrix n n k | Φ (x + y) = Φ x} ∈ 𝓝 (0 : Matrix n n k) := by
      apply IsOpen.mem_nhds
      · exact (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
      · simp
    obtain ⟨M, hM⟩ := exists_deep_subset hs
    exact Set.mem_iUnion.2 ⟨M, fun y hy => hM y hy⟩
  obtain ⟨M, hM⟩ := hC.elim_directed_cover W hWo hWcov hWm.directed_le
  refine ⟨N, M, fun x hx i j => hN (subset_tsupport Φ hx) i j, fun x y hy => ?_⟩
  by_cases hx : x ∈ tsupport Φ
  · exact hM hx y hy
  by_cases hxy : x + y ∈ tsupport Φ
  · have h := hM hxy (-y) fun i j => by simpa using deep_neg (hy i j)
    rw [add_neg_cancel_right] at h
    exact h.symm
  · rw [hzero _ hx, hzero _ hxy]

end GlobalTheory.SBUniform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAverage
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.WordGrowth

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {J : Subgroup G}

theorem _root_.GlobalTheory.WordGrowth.exists_average
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} {J : Subgroup G}
    (hπ : _root_.GlobalTheory.PRep.IsSmooth π) (hJ : IsCompact (↑J : Set G)) (u : V) :
          ∃ t ∈ _root_.GlobalTheory.PRep.fixed π J,
            ∀ (f : V →ₗ[ℂ] ℂ),
              (∀ j ∈ J, (f : V → ℂ) (((π : G → V →ₗ[ℂ] V) j : V → V) u) = (f : V → ℂ) u) →
                (f : V → ℂ) t = (f : V → ℂ) u := by

  have hK : IsOpen {g : G | π g u = u} := hπ u
  obtain ⟨F, hF⟩ := hJ.elim_finite_subcover
    (fun j : J => (fun g : G => (j : G)⁻¹ * g) ⁻¹' {g : G | π g u = u})
    (fun j => hK.preimage (continuous_const.mul continuous_id))
    (by
      intro g hg
      exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  have hfin : ((fun g : G => π g u) '' (J : Set G)).Finite := by
    apply (F.finite_toSet.image (fun j : J => π (j : G) u)).subset
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨j, hjF, hj⟩ := Set.mem_iUnion₂.1 (hF hg)
    refine ⟨j, hjF, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hj
    show π j u = π g u
    calc π (j : G) u = π j (π ((j : G)⁻¹ * g) u) := by rw [hj]
      _ = π g u := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  set O := hfin.toFinset with hO
  have hmem : ∀ v, v ∈ O ↔ ∃ g ∈ J, π g u = v := by
    intro v
    simp [O]
  have huO : u ∈ O := (hmem u).2 ⟨1, J.one_mem, by simp⟩
  have hcard : (O.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨u, huO⟩).ne'
  refine ⟨(O.card : ℂ)⁻¹ • ∑ v ∈ O, v, ?_, ?_⟩
  · simp only [_root_.GlobalTheory.PRep.fixed, _root_.GlobalTheory.PRep.eig]
    simp
    intro a ha
    congr 1
    apply Finset.sum_nbij' (fun v => π a v) (fun v => π a⁻¹ v)
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a * g, J.mul_mem ha hg, by rw [map_mul, Module.End.mul_apply]⟩
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a⁻¹ * g, J.mul_mem (J.inv_mem ha) hg, by rw [map_mul, Module.End.mul_apply]⟩
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro v _
      rfl
  · intro f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, smul_eq_mul]
    rw [Finset.sum_congr rfl (g := fun _ => f u) ?_]
    · rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact hf g hg

end GlobalTheory.WordGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactSubgroup
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.UnipCompact

variable {n : Type}

theorem conc_mul_sub (c : n → ℤ) (m : ℕ) : GlobalTheory.IwahoriInj.Conc fun i j => (m : ℤ) * (c i - c j) :=
  ⟨fun i => by simp, fun i j l => le_of_eq (by ring)⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Fintype n] [DecidableEq n]

theorem isClosed_unipOf (c : n → ℤ) : IsClosed (GlobalTheory.InertSupp.unipOf k c : Set (GL n k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (GlobalTheory.InertSupp.unipOf k c : Set (GL n k)) =
      ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | (g : Matrix n n k) i j = (1 : Matrix n n k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

theorem eventually_mem_grp {c : n → ℤ} {u : GL n k} (hu : u ∈ GlobalTheory.InertSupp.unipOf k c) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) := by
  have key : ∀ u ∈ GlobalTheory.InertSupp.unipOf k c, ∀ᶠ m : ℕ in Filter.atTop,
      ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
    intro u hu
    simp only [Filter.eventually_all]
    intro i j
    by_cases h : c i < c j
    · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
      refine hm.mono ?_
      nlinarith [Int.natCast_nonneg m]
    · rw [GlobalTheory.InertSupp.mem_unipOf.1 hu i j h]
      refine Filter.Eventually.of_forall fun m => ?_
      by_cases hij : i = j
      · subst hij
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne hij, GlobalTheory.IwahoriInj.deep_zero]
  exact (key u hu).and (key _ (inv_mem hu))

theorem exists_compact_subgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ) (S : Finset (GL n k))
    (hS : ∀ u ∈ S, u ∈ GlobalTheory.InertSupp.unipOf k c) :
    ∃ H : Subgroup (GL n k), H ≤ GlobalTheory.InertSupp.unipOf k c ∧ IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
  obtain ⟨m, hm⟩ := ((Filter.eventually_all_finset S).2 fun u hu => eventually_mem_grp (hS u hu)).exists
  refine ⟨GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) ⊓ GlobalTheory.InertSupp.unipOf k c, inf_le_right, ?_,
    fun u hu => ⟨hm u hu, hS u hu⟩⟩
  rw [Subgroup.coe_inf]
  let f : n → n → ℤ := fun i j => (m : ℤ) * (c i - c j)
  have hK : IsCompact {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} := by
    have h : IsCompact (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n =>
        {x : k | Deep (f i j) x}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
        IsNonarchimedeanLocalField.isCompact_closedBall k _
    have e : {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} =
        (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n =>
          {x : k | Deep (f i j) x}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]
    exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  have hgrp : IsCompact (GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) : Set (GL n k)) := by
    convert h using 1
    ext g
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply,
      Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
    rfl
  exact hgrp.inter_right (isClosed_unipOf c)

end GlobalTheory.UnipCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLMulRightColumnsEqZeroOfRankStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  first | exact @GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank | exact GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank | (intros; apply GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank <;> assumption)
end

