module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
section
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : Unif k}

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.mul_inv_q (q : _root_.GlobalTheory.LatPair.Unif k) :
    (q.1 : k) * q.inv = 1 :=
  mul_inv_cancel₀ q.ne_zero


open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.mem_gluedS {L : Submodule 𝒪[k] (n → k)} {f : n → k}
    {y : n ⊕ Fin c → k} :
    y ∈ _root_.GlobalTheory.LatPair.gluedS q c L f ↔ ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
      (i.val = 0 → y (Sum.inr i) = q.inv * s) ∧
        (0 < i.val → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k]) := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, _root_.GlobalTheory.LatPair.mem_gluedLat]
  refine exists_congr fun s => and_congr_right fun _ => forall_congr' fun i => ?_
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨fun h => h2 (by omega), fun h => h3 (by omega)⟩
  · rintro ⟨h2, h3⟩
    exact ⟨fun h => absurd h (by omega), fun h => h2 (by omega), fun h => h3 (by omega)⟩


open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.gluedS_le_iff {L : Submodule 𝒪[k] (n → k)} {f : n → k}
    {M : Submodule 𝒪[k] (n ⊕ Fin c → k)} :
    _root_.GlobalTheory.LatPair.gluedS q c L f ≤ M ↔ (∀ y ∈ L, _root_.GlobalTheory.LatPair.inX k n c y ∈ M) ∧
      q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
          _root_.GlobalTheory.LatPair.inX k n c f ∈ M ∧
      ∀ i : Fin c, 0 < i.val →
        q.inv • _root_.GlobalTheory.LatPair.avec k n c (i.val + 1) ∈ M := by
  unfold _root_.GlobalTheory.LatPair.gluedS
  rw [sup_le_iff, sup_le_iff, Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem,
    Submodule.span_le, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h i hi
    exact h ⟨i.val + 1, by omega, by omega, rfl⟩
  · rintro h y ⟨j, hj2, hjc, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact h ⟨m, by omega⟩ (by simp only; omega)

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.interX_gluedS (hc : 1 ≤ c) (L : Submodule 𝒪[k] (n → k))
    (f : n → k) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration.interX (_root_.GlobalTheory.LatPair.gluedS q c L f) = L := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration.interX
  ext x
  rw [Submodule.mem_comap, ← _root_.GlobalTheory.LatPair.gluedLat_one]
  exact _root_.GlobalTheory.LatPair.inX_mem_gluedLat le_rfl hc

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.glue_mem_gluedS (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
      _root_.GlobalTheory.LatPair.inX k n c f ∈ _root_.GlobalTheory.LatPair.gluedS q c L f := by
  unfold _root_.GlobalTheory.LatPair.gluedS
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.glue_mem_gluedS_iff (hc : 1 ≤ c) {L : Submodule 𝒪[k] (n → k)}
    {f x : n → k} :
    q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c x ∈ _root_.GlobalTheory.LatPair.gluedS q c L f ↔
      x - f ∈ L := by
  have hg := _root_.GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := c) L f
  have hsplit : q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c x =
      (q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c f) + _root_.GlobalTheory.LatPair.inX k n c (x - f) := by
    rw [map_sub]
    abel
  rw [hsplit, Submodule.add_mem_iff_right _ hg, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.inX_mem_gluedLat le_rfl hc]

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
theorem _root_.GlobalTheory.LevelUnfold.gluedS_congr {L : Submodule 𝒪[k] (n → k)} {f f' : n → k}
    (h : f - f' ∈ L) : _root_.GlobalTheory.LatPair.gluedS q c L f = _root_.GlobalTheory.LatPair.gluedS q c L f' := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.gluedLat_congr q c 1 h]

variable [Fintype n] [DecidableEq n]

open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise ENNReal in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k} in
variable [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.LevelUnfold.embX_smul_gluedS (g : GL n k) (L : Submodule 𝒪[k] (n → k))
    (f : n → k) :
    _root_.GlobalTheory.RootEx.embX c g • _root_.GlobalTheory.LatPair.gluedS q c L f =
      _root_.GlobalTheory.LatPair.gluedS q c (g • L) (g • f) := by
  rw [← _root_.GlobalTheory.LatPair.gluedLat_one, ← _root_.GlobalTheory.LatPair.gluedLat_one,
    _root_.GlobalTheory.LatPair.embX_smul_gluedLat]


end GlobalTheory.LevelUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecAuxiliaryBasisVectorSumFinApply
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

set_option linter.unusedSectionVars false

theorem coe_ne_zero {ϖ : 𝒪[k]} (h : Irreducible ϖ) : (ϖ : k) ≠ 0 := fun h0 => h.ne_zero (Subtype.ext h0)

theorem mem_int_of_psi {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {s : k}
    (hs : ∀ a : 𝒪[k], ψ (-(a * s)) = 1) : s ∈ 𝒪[k] := by
  rcases eq_or_ne s 0 with rfl | h0
  · exact zero_mem _
  have := (hψ s).1 fun y hy => by
    have ha : -(y / s) ∈ 𝒪[k] := by
      refine neg_mem ?_
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hy zero_le
    have := hs ⟨_, ha⟩
    simpa [h0] using this
  simpa [Valuation.mem_integer_iff] using this

theorem smul_mem_Yle {i : ℕ} (a : k) {v : n ⊕ Fin c → k} (hv : v ∈ Yle k n c i) : a • v ∈ Yle k n c i :=
  fun l hl => by simp [hv l hl]

theorem colMat_eq_zero {y : Fin c → (n ⊕ Fin c → k)} (hy : ∀ i, y i ∈ Yle k n c (i.val + 1))
    (l : Fin c) (j : Fin (c + 1)) (h : j.val ≤ l.val) : colMat n' y (Sum.inr l) (Sum.inr j) = 0 := by
  revert h
  refine Fin.cases (fun _ => ?_) (fun i h => ?_) j
  · simp [colMat]
  · simp only [Fin.val_succ] at h
    simpa [colMat] using hy i l (by omega)

theorem mulVec_auxiliaryBasisVectorSumFin_apply (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (j : Fin (c + 1)) (r) :
    (x *ᵥ aux k n' j) r = x r (Sum.inr j) := by
  simp [aux]

theorem act_embX (ϖ : 𝒪[k]) (g : GL n k) (L : Submodule 𝒪[k] (n → k)) :
    act (embX c g) (chainLat ϖ c L) = chainLat ϖ c (act g L) := by
  ext v
  rw [mem_act_iff_inv, ← map_inv, Radical.embX_val, fromBlocks_mulVec, mem_chainLat, mem_chainLat,
    mem_act_iff_inv]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mulVec, add_zero, zero_add, one_mulVec, Function.comp]
  rfl

variable [MeasurableSpace k] [BorelSpace k]

theorem oneClass (hc : 1 ≤ c) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) (L' : Submodule 𝒪[k] (n' → k)) : OneClass ϖ ψ ν n hc L' := by
  intro Λ hΛ Ψ hSB hS hP hE
  have := hν.1
  have h0 := coe_ne_zero hϖ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν 1 Ψ x₀ ≠ 0 := Function.ne_iff.1 hE
  obtain ⟨y, hy, hΨ⟩ := exists_pt_ne_zero hx₀
  have hmap := hS _ hΨ
  have h1 : ∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) =
      Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)} := by
    intro i
    apply le_antisymm
    · have key : ∀ v ∈ Λ ⊓ Yle k n c (i.val + 1), ψ (-(v (Sum.inr i) / (ϖ : k) ^ (i.val + 1))) = 1 := by
        intro v hv
        let z : Fin c → (n ⊕ Fin c → k) := Pi.single i (((ϖ : k) ^ (i.val + 2))⁻¹ • v)
        have hz : ∀ j, (ϖ : k) ^ (j.val + 2) • z j ∈ Λ := by
          intro j
          rcases eq_or_ne j i with rfl | hj
          · simp only [z, Pi.single_eq_same]
            rw [smul_inv_smul₀ (pow_ne_zero _ h0)]
            exact hv.1
          · simp [z, hj]
        have hz' : ∀ j, ((ϖ : k) • z) j ∈ Yle k n c (j.val + 1) := by
          intro j
          rcases eq_or_ne j i with rfl | hj
          · simp only [z, Pi.smul_apply, Pi.single_eq_same]
            exact smul_mem_Yle _ (smul_mem_Yle _ hv.2)
          · simp [z, hj]
        have := opE_translate ψ ν hz' (fun x => by
          rw [colMat_smul]; exact hP x _ (mapsInto_colMat hz)) x₀
        have h2 : (ψ (-∑ j, ((ϖ : k) • z) j (Sum.inr j)) : ℂ) = 1 :=
          mul_right_cancel₀ hx₀ (by rw [one_mul]; exact this.symm)
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [z, hj]) (by simp)] at h2
        rw [← Circle.coe_eq_one, ← h2]
        congr 3
        simp only [z, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
        field_simp
        ring
      rintro _ ⟨v, hv, rfl⟩
      have := mem_int_of_psi hψ (s := v (Sum.inr i) / (ϖ : k) ^ (i.val + 1)) fun a => by
        have := key _ (Submodule.smul_mem _ a hv)
        rw [← this]
        congr 2
        simp [Subring.smul_def, mul_div_assoc]
      refine Submodule.mem_span_singleton.2 ⟨⟨_, this⟩, ?_⟩
      simp [Subring.smul_def, h0]
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨_, ⟨hmap _ (scaled_basis_mem_chainLattice ϖ L' i.castSucc), fun l hl => ?_⟩, ?_⟩
      · rw [Matrix.mulVec_smul, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply, pt_eq, Matrix.add_apply,
          colMat_eq_zero hy _ _ (by simp; omega)]
        have : l.val ≠ i.val := by omega
        simp [basePt, this]
      · rw [LinearMap.proj_apply, Matrix.mulVec_smul, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply, pt_eq, Matrix.add_apply,
          colMat_eq_zero hy _ _ (by simp)]
        simp [basePt]
  have h2 : (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ := by
    have := hmap _ (scaled_basis_mem_chainLattice ϖ L' 0)
    convert this using 1
    ext r
    rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply]
    rcases r with r | r
    · simp [pt_eq, basePt, colMat, aux]
    · simp only [pt_eq, basePt, colMat, aux, Pi.single_apply, Fin.ext_iff]
      by_cases hr : r.val = 0 <;> simp [hr, Fin.ext_iff]
  obtain ⟨u, hu, huΛ⟩ := GlobalTheory.RootEx.UnfoldFlag.exists_unipotent k n c hc ϖ h0 Λ h1 h2
  refine ⟨h1, h2, ⟨u, hu, huΛ⟩, ?_⟩
  have hfull : (Λ.comap (inX k n c)).IsFullLattice k := by
    letI := (GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).2 Λ hΛ
    constructor
    refine Submodule.eq_top_iff'.2 fun v => ?_
    -- Vary the column acting on the first scaled basis vector while Ψ stays constant.
    let x := pt x₀ y
    let B : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
      Matrix.of fun r => Pi.single (Sum.inr (0 : Fin (c + 1))) (inX k n c v r)
    have hB : B *ᵥ aux k n' 0 = inX k n c v := by
      funext r
      rw [mulVec_auxiliaryBasisVectorSumFin_apply]
      simp [B]
    have hloc : IsLocallyConstant Ψ := hSB.1
    have hcont : Continuous (fun a : k => x + a • B) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hnear := (hloc.comp_continuous hcont).eventually_eq (0 : k)
    obtain ⟨γ, hγ, hγnear⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hnear
    obtain ⟨δ, hδ, hδ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
    have hγpos : 0 < γ := zero_lt_iff.mpr hγ
    obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ * δ)
    have ha0 : a ≠ 0 := by
      intro e
      exact (mul_ne_zero hγ hδ.ne') (by simpa [e] using ha.symm)
    have haq : Ψ (x + a • B) = Ψ x := by
      have hav : valuation k a < γ := by
        simpa only [ha, mul_one] using mul_lt_mul_of_pos_left hδ1 hγpos
      simpa only [Set.mem_setOf_eq, Function.comp_apply, zero_smul, add_zero] using hγnear hav
    have hw := scaled_basis_mem_chainLattice ϖ L' (0 : Fin (c + 1))
    simp only [Fin.val_zero, zero_add, pow_one] at hw
    have hbase := hmap _ hw
    change x *ᵥ ((ϖ : k) • aux k n' 0) ∈ Λ at hbase
    have hshift := hS (x + a • B) (by rwa [haq]) _ hw
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul B, hB, smul_smul] at hshift
    have hscaled : (a * (ϖ : k)) • v ∈ Λ.comap (inX k n c) := by
      change inX k n c ((a * (ϖ : k)) • v) ∈ Λ
      have heq : inX k n c ((a * (ϖ : k)) • v) = (a * (ϖ : k)) • inX k n c v := by
        funext r
        cases r <;> simp [inX_apply, Pi.smul_apply]
      rw [heq]
      simpa only [add_sub_cancel_left] using Λ.sub_mem hshift hbase
    simpa only [inv_smul_smul₀ (mul_ne_zero ha0 h0)] using
      (Submodule.span k (Λ.comap (inX k n c) : Set (n → k))).smul_mem (a * (ϖ : k))⁻¹ (Submodule.subset_span hscaled)
  obtain ⟨g, hg⟩ := GlobalTheory.RootEx.UnfoldShape.exists_eq_act_stdLat k n _ hfull
  refine ⟨u⁻¹ * embX c g, mul_mem (inv_mem (Subgroup.mem_sup_right hu)) (Subgroup.mem_sup_left ⟨g, rfl⟩), ?_⟩
  rw [act_mul, act_embX, ← hg, ← huΛ, ← act_mul, inv_mul_cancel, act_one]

theorem oneCoset (hc : 1 ≤ c) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) (L' : Submodule 𝒪[k] (n' → k)) : OneCoset ϖ ψ ν n c L' := by
  have h0 := coe_ne_zero hϖ
  have hlat : Submodule.IsLattice k (chainLat ϖ c (stdLat k n)) :=
    (GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).1 ϖ h0 _ (GlobalTheory.RootEx.UnfoldShape.isLattice_stdLat_and_act k n).1
  constructor
  · intro μ Φ hΦ hS hP h' h hh' hE
    have key := oneClass hc hϖ hψ hν L' _ ((GlobalTheory.RootEx.UnfoldShape.isLattice_stdLat_and_act k _).2 h _ hlat) _
      (om_mem_SB μ h' h hΦ) ?_ ?_ hE
    · obtain ⟨r, hr, e⟩ := key.2.2.2
      refine ⟨r, hr, r⁻¹ * h, ?_, by group⟩
      rw [act_mul, e, ← act_mul, inv_mul_cancel, act_one]
    · intro x hx v hv
      rw [← hh'] at hv
      obtain ⟨w, hw, rfl⟩ := mem_act.1 hv
      have := hS _ (right_ne_zero_of_mul hx) w hw
      rw [mem_act_iff_inv]
      simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using this
    · intro x y hy
      have : MapsInto ((h⁻¹).val * y * h'.val) (chainLat ϖ (c + 1) L') (chainLat ϖ c (stdLat k n)) := by
        intro w hw
        have h1 : h'.val *ᵥ w ∈ chainLat ϖ (c + 1) L' := by
          rw [← hh']; exact mem_act.2 ⟨w, hw, rfl⟩
        have := mem_act_iff_inv.1 (hy _ h1)
        simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using this
      simp only [om]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hP _ _ this]
  · intro J hJ hJ'
    obtain ⟨S, hS⟩ := GlobalTheory.RootEx.UnfoldShape.exists_isReps_of_fg k _ ϖ hϖ _ hlat.fg
    obtain ⟨T, hT, hT'⟩ := GlobalTheory.RootEx.UnfoldShape.stabiliser_finite_cosets_mod k _ ϖ _ S hlat.fg hS
    refine ⟨T, hT, fun h => ⟨?_, ?_⟩⟩
    · rintro ⟨r, hr, t, ht, rfl⟩
      obtain ⟨t₀, ht₀, j, hj, hj', rfl⟩ := hT' t ht
      exact ⟨r, hr, t₀, ht₀, j, hJ' j hj hj', (mul_assoc _ _ _).symm⟩
    · rintro ⟨r, hr, t, ht, j, hj, rfl⟩
      exact ⟨r, hr, t * j, by rw [act_mul, hJ j hj, hT t ht], mul_assoc _ _ _⟩

end GlobalTheory.RootEx.UnfoldShape
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLeCard
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound

namespace GlobalTheory.SatakeBound.Rep

section Abstract

variable {G X V : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem norm_le_card {ι : Type} {π : Representation ℂ G V} (hπ : IsUnitarisable π) {v : V} (hv : v ≠ 0)
    (S : Finset ι) (g : ι → G) (l : ℂ) (h : ∑ c ∈ S, π (g c) v = l • v) : ‖l‖ ≤ S.card := by
  obtain ⟨B, b1, b2, b3⟩ := hπ
  letI : InnerProductSpace.Core ℂ V := UnitInd.core B b1 b2
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  have hn : ∀ x : G, ‖π x v‖ = ‖v‖ := fun x => by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) v]
    exact congrArg (fun z : ℂ => √(RCLike.re z)) (b3 x v v)
  have h1 : ‖l‖ * ‖v‖ ≤ S.card * ‖v‖ := by
    rw [← norm_smul, ← h]
    refine (norm_sum_le _ _).trans ?_
    simp [hn]
  exact le_of_mul_le_mul_right h1 (norm_pos_iff.2 hv)

theorem sum_fixed (ρ : Representation ℂ G X) (K : Subgroup G) {w : X} (hw : ∀ x ∈ K, ρ x w = w)
    (S : Finset (G ⧸ K)) (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) (x : G) (hx : x ∈ K) :
    ρ x (∑ c ∈ S, ρ c.out w) = ∑ c ∈ S, ρ c.out w := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_nbij' (fun c => x • c) (fun c => x⁻¹ • c) (hS x hx) (hS _ (inv_mem hx))
    (fun c _ => by simp) (fun c _ => by simp) fun c _ => ?_
  have h1 : x • c = ((x * c.out : G) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul K (x * c.out)
  rw [h1, hy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw y y.2]

theorem exists_vector [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G X}
    {π : Representation ℂ G V} (hρ : IsSmooth ρ) (hπ : IsUnitarisable π) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (hs : fixed π K ≠ ⊥) (E : X →ₗ[ℂ] ℂ) (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → E u = 0 → u = 0) :
    ∃ w : X, (∀ x ∈ K, ρ x w = w) ∧ E w = 1 ∧ ∀ S : Finset (G ⧸ K), (∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) →
      ‖∑ c ∈ S, E (ρ c.out w)‖ ≤ S.card := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw0 : f w ≠ 0 := fun h => hv0 (hfw.symm.trans h)
  have hEw : E w ≠ 0 := fun h => hfw0 (by rw [hE w hw' h, map_zero])
  obtain ⟨z, hz, hEz, hfz⟩ : ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ E z = 1 ∧ f z ≠ 0 :=
    ⟨(E w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], by
      rw [map_smul]; exact smul_ne_zero (inv_ne_zero hEw) hfw0⟩
  refine ⟨z, hz, hEz, fun S hS => norm_le_card hπ hfz S (fun c => c.out) _ ?_⟩
  have h1 := hE (∑ c ∈ S, ρ c.out z - (∑ c ∈ S, E (ρ c.out z)) • z)
    (fun x hx => by rw [map_sub, sum_fixed ρ K hz S hS x hx, map_smul, hz x hx])
    (by rw [map_sub, map_sum, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
  have h2 := congrArg f (sub_eq_zero.1 h1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_smul] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun c _ => (f.isIntertwining _ _ _ _).symm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem law (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n)) ((ofChar (torusChar fun i => unrChar k (α i))).comp
      (leviTorus k (Fin n)).symm.toMonoidHom))
    (b : GL (Fin n) k) (hb : b ∈ borel k (Fin n)) (t : Fin n → kˣ)
    (ht : ∀ i, (b : Matrix (Fin n) (Fin n) k) i i = t i) (g : GL (Fin n) k) :
    f.1.1 (b * g) = (∏ i : Fin n, ((α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ))
      ^ ord k (t i)) * f.1.1 g := by
  refine (parInd_law _ _ f ⟨b, hb⟩ g).trans ?_
  show _ • ofChar _ _ (f.1.1 g) = _
  rw [ofChar_apply, torusChar_apply, deltaHalf_apply, smul_eq_mul, ← mul_assoc,
    Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : Matrix.GeneralLinearGroup.det (leviProj _ (points (Fin n)) ⟨b, hb⟩ i) = t i := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    exact ht i
  show _ * ((unrChar k (α i)
    (Matrix.GeneralLinearGroup.det (leviProj _ (points (Fin n)) ⟨b, hb⟩ i)) : ℂˣ) : ℂ) = _
  have e2 : ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) =
      ((-(((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ) := by
    rw [modExp_fin _ (fun _ => by simp)]
    push_cast
    ring
  have hq : (0 : ℝ) ≤ resCard k := Nat.cast_nonneg _
  rw [e, e2, val_absPow_ofReal, unrChar_apply, Units.val_zpow_eq_zpow_val, mul_zpow, mul_comm,
    GlobalTheory.LGrp.nabs_eq_zpow, ← Complex.ofReal_zpow, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq, ← Real.rpow_mul hq]
  congr 3
  push_cast
  ring

theorem exists_sph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), IsUnitarisable π → HasSatake π α → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ HasBoundedSums k φ := by
  intro k _ _ _ _ n V _ _ π α hu ⟨_, hs, S, f, hf⟩
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  let E : S.toSubmodule →ₗ[ℂ] ℂ := ⟨⟨fun u => u.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin n), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin n), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  obtain ⟨w, hw, hw1, hb⟩ := exists_vector hsm hu SplitFlip.isCompact_KO f hf hs E fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1
  refine ⟨w.1.1.1, ⟨hr w hw, fun b hb t ht => ?_⟩, fun T hT => ?_⟩
  · have h1 := law α w.1 b hb t ht 1
    have h2 : w.1.1.1 1 = 1 := hw1
    rwa [h2, mul_one, mul_one] at h1
  · refine le_of_eq_of_le ?_ (hb T hT)
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = w.1.1.1 (1 * c.out)
    rw [one_mul]

end GlobalTheory.SatakeBound.Rep
end
end

