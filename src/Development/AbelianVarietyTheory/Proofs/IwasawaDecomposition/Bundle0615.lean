module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellOfQuotientCellRadicalPullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubspaceTrivialOutsideSplitPlac
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantCarrierDimPolyFan
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.CarDim

theorem exists_cell {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ : InvFun (𝓞 E)} {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (hfan : IsPolyFanOn H.bar ψ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms H.bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β := by
  have hmem : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hS _ hmem
  refine ⟨m, fun i => pull e.symm.toLinearMap (γ i), isCell_pull_equiv hγ e.symm, c, hc, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
  simpa [LinearMap.sum_apply] using this

end GlobalTheory.PolFan.CarDim

theorem GlobalTheory.PolFan.CarDim.exists_isCarrierDim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ lab : InvFun (𝓞 E), IsTwInv H lab ∧ IsCarrierDim H.bar q ψ lab := by
  intro E _ _ _ H q ψ hD hψ htw
  refine ⟨carFun H.bar ψ, _root_.GlobalTheory.PolFan.CarDim.isTwInv_carFun E H ψ htw, ?_⟩
  intro X _ _ _ _ hX β hβ hp
  have hfan := hψ X hX
  have hface := _root_.GlobalTheory.PolFan.FaceCutCell.isCell_comp E H ψ X hfan (hD X)
  rw [evalZ_carFun hβ hp]
  congr 1
  obtain ⟨m₀, γ₀, hγ₀, hin₀⟩ := exists_cell hfan hβ hp
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}.Nonempty := ⟨_, m₀, γ₀, hγ₀, hin₀, rfl⟩
  apply le_antisymm
  · obtain ⟨m, γ, h1, h2, h3⟩ := Nat.sInf_mem hne
    obtain ⟨m', δ, k1, k2, k3⟩ := _root_.GlobalTheory.PolFan.CarDim.exists_cell_quot_orad_of_inRCone E H ψ X hface β hβ hp m γ h1 h2
    exact (Nat.sInf_le (show genRank δ ∈ cdimSet H.bar ψ X (orad β) β from ⟨m', δ, k1, k2, rfl⟩)).trans (k3.trans h3.le)
  · have hne' : (cdimSet H.bar ψ X (orad β) β).Nonempty := by
      obtain ⟨m', δ, k1, k2, -⟩ := _root_.GlobalTheory.PolFan.CarDim.exists_cell_quot_orad_of_inRCone E H ψ X hface β hβ hp m₀ γ₀ hγ₀ hin₀
      exact ⟨_, m', δ, k1, k2, rfl⟩
    obtain ⟨m', δ, h1, h2, h3⟩ := Nat.sInf_mem hne'
    obtain ⟨m, γ, k1, k2, k3⟩ := _root_.GlobalTheory.PolFan.CarDim.cell_of_quot_cell E H ψ X hfan hface β hβ hp m' δ h1 h2
    unfold cdimQ
    rw [← h3]
    exact (Nat.sInf_le (show genRank γ ∈ {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
      InRCone γ β ∧ genRank γ = k} from ⟨m, γ, k1, k2, rfl⟩)).trans k3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfFaceOfCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_linForm_cut_face_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (γ' : Fin p → LinearMap.BilinForm ℤ X)
    (h₂ h₁ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    (∀ i, δ i ∈ balForms bar X) → (∀ i y, 0 ≤ δ i y y) → (∀ j, InRCone γ (γ' j)) →
    (∀ i, 0 ≤ h₂ (δ i)) → (∀ k, h₂ (γ k) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h₂ β = 0 → InRCone γ β) →
    (∀ k, 0 ≤ h₁ (γ k)) → (∀ j, h₁ (γ' j) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h₁ β = 0 → InRCone γ' β) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (δ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h β = 0 → InRCone γ' β := by
  intro O _ bar X _ _ m n p δ γ γ' h₂ h₁ hδb hδp hγ' h2δ h2γ hf2 h1γ h1γ' hf1
  set K : ℤ := 1 + ∑ i, |h₁ (δ i)| with hK
  have hKi : ∀ i, |h₁ (δ i)| < K := fun i => by
    have := Finset.single_le_sum (f := fun i => |h₁ (δ i)|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hK0 : 0 ≤ K := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (h₁ (δ i)))
    linarith
  have happ : ∀ x, (K • h₂ + h₁) x = K * h₂ x + h₁ x := fun x => by simp
  have hpos : ∀ i, 0 < h₂ (δ i) → 0 < (K • h₂ + h₁) (δ i) := fun i hi => by
    rw [happ]
    have h1 : K ≤ K * h₂ (δ i) := by nlinarith
    have := neg_abs_le (h₁ (δ i))
    linarith [hKi i]
  have hnn : ∀ i, 0 ≤ (K • h₂ + h₁) (δ i) := fun i => by
    rcases (h2δ i).lt_or_eq with hi | hi
    · exact (hpos i hi).le
    · rw [happ, ← hi, mul_zero, zero_add]
      exact InRCone.apply_nonneg (hf2 _ (hδb i) (hδp i) (inRCone_self δ i) hi.symm) h₁ h1γ
  have h2γ' : ∀ j, h₂ (γ' j) = 0 := fun j => le_antisymm (by
      have := InRCone.apply_nonneg (hγ' j) (-h₂) (fun k => by simp [h2γ k])
      simpa using this)
    (InRCone.apply_nonneg (hγ' j) h₂ (fun k => (h2γ k).ge))
  refine ⟨K • h₂ + h₁, hnn, fun j => by rw [happ, h2γ' j, h1γ' j]; ring, ?_⟩
  intro β hb hp hc hz
  have h2β : h₂ β = 0 := by
    obtain ⟨c, hc0, e⟩ := hc
    have eh := apply_eq_of_toReal_eq e (K • h₂ + h₁)
    have e2 := apply_eq_of_toReal_eq e h₂
    rw [hz, Int.cast_zero] at eh
    have hterm : ∀ i ∈ Finset.univ, 0 ≤ c i * ((K • h₂ + h₁) (δ i) : ℝ) := fun i _ =>
      mul_nonneg (hc0 i) (by exact_mod_cast hnn i)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 eh.symm
    have hs : ∑ i, c i * (h₂ (δ i) : ℝ) = 0 := Finset.sum_eq_zero fun i _ => by
      rcases (h2δ i).lt_or_eq with hi | hi
      · have h0 := hall i (Finset.mem_univ _)
        have hp' : (0 : ℝ) < (K • h₂ + h₁) (δ i) := by exact_mod_cast hpos i hi
        rw [(mul_eq_zero.1 h0).resolve_right hp'.ne', zero_mul]
      · rw [← hi]; simp
    exact_mod_cast e2.trans hs
  have hγβ := hf2 β hb hp hc h2β
  refine hf1 β hb hp hγβ ?_
  have := happ β
  rw [hz, h2β] at this
  linarith

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntForm
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem posReal_multiple_rat {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ)
    (hd : 0 < d) (hy : y ≠ 0) (h : toReal x = d • toReal y) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℤ) • x = (b : ℤ) • y := by
  have hpt : ∀ u v, (x u v : ℝ) = d * (y u v : ℝ) := by
    intro u v
    have := congrArg (fun f => f u v) h
    simpa [toReal] using this
  obtain ⟨u, v, huv⟩ : ∃ u v, y u v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (LinearMap.ext₂ hc)
  set r : ℚ := (x u v : ℚ) / (y u v : ℚ) with hr_def
  have hy' : (y u v : ℝ) ≠ 0 := by exact_mod_cast huv
  have hdr : d = (r : ℝ) := by
    rw [hr_def]; push_cast; rw [hpt u v]; field_simp
  have hr : 0 < r := by exact_mod_cast (hdr ▸ hd)
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hcast : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
  refine ⟨r.den, r.num.toNat, r.den_pos, by omega, ?_⟩
  apply LinearMap.ext₂
  intro p q
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hcast]
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [hpt p q, hdr]
  have hrr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [hrr]; field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveBalancedFormFracCoordsOfCellMult
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

namespace CentreChoice

variable {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]

theorem exists_isPrim_smul {x : balForms bar X} (hx : x ≠ 0) :
    ∃ (g : ℕ) (v : balForms bar X), 0 < g ∧ x = g • v ∧ IsPrim bar v := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, (x : LinearMap.BilinForm ℤ X) a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (Subtype.ext (LinearMap.ext₂ h))
  let S : Set ℕ := {g | 0 < g ∧ ∃ v : balForms bar X, x = g • v}
  have hS1 : 1 ∈ S := ⟨one_pos, x, (one_smul _ _).symm⟩
  have hbd : ∀ g ∈ S, g ≤ ((x : LinearMap.BilinForm ℤ X) a b).natAbs := by
    rintro g ⟨hg, v, hv⟩
    have e : (x : LinearMap.BilinForm ℤ X) a b = (g : ℤ) * (v : LinearMap.BilinForm ℤ X) a b := by
      rw [hv]
      simp
    rw [e] at hab ⊢
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.2 (right_ne_zero_of_mul hab))
  have hB : BddAbove S := ⟨_, hbd⟩
  obtain ⟨hg, v, hv⟩ := Nat.sSup_mem ⟨1, hS1⟩ hB
  refine ⟨sSup S, v, hg, hv, fun j v' hj => ?_⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hx
    rw [hv, hj, zero_smul, smul_zero]
  have hmem : sSup S * j ∈ S := ⟨Nat.mul_pos hg (Nat.pos_of_ne_zero hj0), v', by rw [hv, hj, mul_smul]⟩
  have h1 : sSup S * j ≤ sSup S * 1 := by simpa using le_csSup hB hmem
  have h2 := Nat.le_of_mul_le_mul_left h1 hg
  omega

theorem exists_isPrim_frac : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → 2 ≤ M →
  ∃ (v : LinearMap.BilinForm ℤ X) (hv : v ∈ balForms bar X), IsPrim bar (⟨v, hv⟩ : balForms bar X) ∧ (∀ y, 0 ≤ v y y) ∧
    ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i < 1) ∧ toReal v = ∑ i, t i • toReal (δ i) := by
  intro O _ bar φ M X _ _ _ m δ hδ h2
  classical
  obtain ⟨hc, -, -, hM⟩ := hδ
  let δ' : Fin m → balForms bar X := fun i => ⟨δ i, hc.mem i⟩
  let P := Submodule.span ℤ (Set.range δ')
  have hcard : 1 < Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ P)) := by
    have : Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ P)) = M := hM
    omega
  have hfin : Finite (Submodule.torsion ℤ (balForms bar X ⧸ P)) := Nat.finite_of_card_ne_zero (by omega)
  haveI := Finite.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨t, ht⟩ := exists_ne (0 : Submodule.torsion ℤ (balForms bar X ⧸ P))
  obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff _).1 t.2
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective P t.1
  have hxP : x ∉ P := fun h => ht (Subtype.ext (by rw [← hx]; exact (Submodule.Quotient.mk_eq_zero P).2 h))
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have h1 : a • x ∈ P := (Submodule.Quotient.mk_eq_zero P).1 (by
    rw [Submodule.Quotient.mk_smul, ← Submodule.mkQ_apply, hx]; exact hat)
  have hk : 0 < a.natAbs := Int.natAbs_pos.2 ha0
  have hkx : (a.natAbs : ℤ) • x ∈ P := by
    rcases Int.natAbs_eq a with h | h
    · rwa [h] at h1
    · rw [h, neg_smul] at h1
      exact P.neg_mem_iff.1 h1
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hkx
  set k : ℕ := a.natAbs with hkdef
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  let x' : balForms bar X := x - ∑ i, (c i / k) • δ' i
  have hsP : ∑ i, (c i / k) • δ' i ∈ P :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hx'0 : x' ≠ 0 := fun h => hxP (by
    have : x = x' + ∑ i, (c i / k) • δ' i := by simp [x']
    rw [this, h, zero_add]; exact hsP)
  have hkx' : (k : ℤ) • x' = ∑ i, (c i % k) • δ' i := by
    simp only [x', smul_sub, Finset.smul_sum, smul_smul, ← hc']
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul]
    congr 1
    have := Int.mul_ediv_add_emod (c i) k
    linarith
  obtain ⟨g, v, hg, hxv, hprim⟩ := exists_isPrim_smul hx'0
  have hr0 : ∀ i, 0 ≤ c i % k := fun i => Int.emod_nonneg _ hkZ.ne'
  have hr1 : ∀ i, c i % k < k := fun i => Int.emod_lt_of_pos _ hkZ
  have key : ∀ a b, ((k : ℤ) * g) * (v : LinearMap.BilinForm ℤ X) a b = ∑ i, (c i % k) * δ i a b := by
    intro a b
    have e := congrArg (fun z : balForms bar X => (z : LinearMap.BilinForm ℤ X) a b) hkx'
    simp only [hxv] at e
    simpa [Submodule.coe_sum, LinearMap.sum_apply, δ', mul_assoc] using e
  have hkg : (0 : ℤ) < (k : ℤ) * g := mul_pos hkZ (by exact_mod_cast hg)
  refine ⟨v, v.2, hprim, fun y => ?_, fun i => ((c i % k : ℤ) : ℝ) / ((k : ℝ) * g), fun i => ⟨?_, ?_⟩, ?_⟩
  · have hs : 0 ≤ ∑ i, (c i % k) * δ i y y :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hr0 i) (hc.nonneg i y)
    rw [← key] at hs
    exact nonneg_of_mul_nonneg_right hs hkg
  · have : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    exact div_nonneg (by exact_mod_cast hr0 i) this.le
  · have : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    rw [div_lt_one this]
    have : c i % k < (k : ℤ) * g := lt_of_lt_of_le (hr1 i) (le_mul_of_one_le_right hkZ.le (by exact_mod_cast hg))
    exact_mod_cast this
  · have hpos : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    refine LinearMap.ext₂ fun a b => ?_
    have e : ((k : ℝ) * g) * ((v : LinearMap.BilinForm ℤ X) a b : ℝ) = ∑ i, ((c i % k : ℤ) : ℝ) * (δ i a b : ℝ) := by
      exact_mod_cast key a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_right_inj' hpos.ne', e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

end CentreChoice

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescalePrimitiveLinearIndependentCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

theorem exists_rescale_prim : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
    ∃ (δ' : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ'), LinearIndependent ℤ δ' ∧
      (∀ i, IsPrim bar (⟨δ' i, h.mem i⟩ : balForms bar X)) ∧ ∀ β, InRCone δ β → InRCone δ' β := by
  intro O _ _ bar φ X _ _ _ m δ hδ hli
  choose n u hmem hn hu hprim using fun i => exists_prim (bar := bar) (hδ.mem i) (hli.ne_zero i)
  have hcu : IsCell bar φ u := cell_rescale hδ n hn hu hmem
  refine ⟨u, hcu, linearIndependent_of_smul hli n hn hu, fun i => hprim i, ?_⟩
  rintro β ⟨c, hc, hβ⟩
  refine ⟨fun i => c i * n i, fun i => mul_nonneg (hc i) (Nat.cast_nonneg _), ?_⟩
  rw [hβ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : toReal (δ i) = (n i : ℝ) • toReal (u i) := by
    rw [hu i]; exact LinearMap.ext₂ fun x y => by simp
  rw [e, smul_smul]

end GlobalTheory.PolFan.SmoothEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicator
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.OrbMark

theorem exists_semilinear_pull_of_evalZ_eq_one : ∀ {O : Type} [CommRing O] (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ (τ : O ≃+* O) (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 ∧ Function.Surjective f ∧
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) ∧
    ∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀ := by
  intro O _ w0 X₀ _ _ v X _ _ _ β h1
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun] at h1
  split_ifs at h1 with hc
  swap
  · exact absurd h1 zero_ne_one
  obtain ⟨-, σ, hσ, s, hs, H⟩ := hc

  let g : (Fin n → O) →+ X :=
    { toFun := fun a => r (twv σ a)
      map_zero' := by rw [twv_zero, map_zero]
      map_add' := fun a b => by
        have e : twv σ (a + b) = twv σ a + twv σ b := funext fun _ => map_add σ _ _
        rw [e, map_add (f := _)] }
  have hg : ∀ a, g a = r (twv σ a) := fun _ => rfl
  have hgs : ∀ (c : O) a, g (c • a) = σ c • g a := fun c a => by
    rw [hg, hg, twv_smul, map_smul]
  have hgsurj : Function.Surjective g := fun x => by
    obtain ⟨a, ha⟩ := hr x
    exact ⟨twv σ.symm a, by rw [hg, twv_twv_symm, ha]⟩
  have hker : ∀ z, g z = 0 → s z = 0 := by
    intro z hz
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (s z)
    rw [← hx]
    refine (Submodule.Quotient.mk_eq_zero _).2 fun c y => ?_
    obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
    have h1 := H (c • z) b (c • x) y
      (by rw [Submodule.Quotient.mk_smul, map_smul]; exact congrArg _ hx) hb.symm
    have e : r (twv σ (c • z)) = 0 := by rw [← hg, hgs, hz, smul_zero]
    dsimp only at h1
    rw [e, map_zero, LinearMap.zero_apply] at h1
    exact_mod_cast h1.symm
  have hwd : ∀ a a', g a = g a' → s a = s a' := fun a a' h => by
    have := hker (a - a') (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  let pre : X → (Fin n → O) := fun x => (hgsurj x).choose
  have hpre : ∀ x, g (pre x) = x := fun x => (hgsurj x).choose_spec
  have hf : ∀ a, s (pre (g a)) = s a := fun a => hwd _ _ (hpre _)
  let f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀) :=
    { toFun := fun x => s (pre x)
      map_zero' := by
        have := hf 0
        rw [map_zero] at this
        rw [this, map_zero]
      map_add' := fun x y => by
        have := hf (pre x + pre y)
        rw [map_add (f := _), hpre, hpre] at this
        rw [this, map_add (f := _)] }
  have hfg : ∀ a, f (g a) = s a := hf
  refine ⟨σ.symm, f, by rw [RingEquiv.symm_apply_eq, hσ], fun q => ?_, fun c x => ?_, fun x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨a, rfl⟩ := hs q
    exact ⟨g a, hfg a⟩
  · obtain ⟨a, rfl⟩ := hgsurj x
    have e : c • g a = g (σ.symm c • a) := by rw [hgs, σ.apply_symm_apply]
    rw [e, hfg, hfg, map_smul]
  · obtain ⟨a, rfl⟩ := hgsurj x
    obtain ⟨b, rfl⟩ := hgsurj y
    rw [hfg] at hx hy
    have h := H a b x₀ y₀ hx hy
    dsimp only at h
    rw [← hg, ← hg] at h
    exact_mod_cast h

end GlobalTheory.PolFan.OrbMark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocSAlt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocalRows2

open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult


set_option maxHeartbeats 1000000 in
theorem finTyp_rows_exists_isLocS : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E → ∀ (σ : D.what₂.FT) (s : SplitPlace D.host.E), ∃ τ, GlobalTheory.HeightCounting.IsLocS (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S s τ := by
  intro hH hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ _ _ σ s
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ
  have hne : isotIn (D := D) (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) (FinTyp.conjT π) ≠ ⊥ := by
    intro h
    apply hb
    unfold isotE isotL
    rw [h, inf_bot_eq]
  have hM := hP.char.base.models
  have hθ : IsInfFam R.θ := hM.inf
  have hSig : (Yc D 0).SigOK := D.sp.Y_sig 0
  have hcc := _root_.GlobalTheory.CongConjugate.congConj D.host.E D.R.r
  have hfd : ∀ j, j < D.R.m → (R.νY A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) (R.fdY A3.A.μ0 j) (R.νY A3.A.μ0 j) := by
    intro j hj
    by_cases h : j + 1 < D.R.m
    · have := hM.νY A3.A.μ0 j h
      exact ⟨this.1.1, this.2⟩
    · obtain rfl : j = D.R.m - 1 := by omega
      have := hM.νY' A3.A.μ0
      exact ⟨this.1.1, this.2⟩
  obtain ⟨hHaar, hFD⟩ := hfd 0 Y.hm
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MY 0) (θ := R.θ) (R.νY A3.A.μ0 0)
    (R.fdY A3.A.μ0 0) Y.PY hSA hSig hθ hHaar hFD
  obtain ⟨B', h1, h2, h3, h4⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r _ (actM Y.PY (R.MY 0))
    (Minf R.θ Y.PY (R.MY 0)) (ipM (R.MY 0) (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0)) hlin hherm hpos
    (fun h x hx => GlobalTheory.FinTypesRows.minf_stable Y.PY hcc h hx)
    (fun h x hx y hy => _root_.GlobalTheory.SchurPairingInvariant.ipM_actM D (Yc D 0) _ R.θ (R.MY 0) D.R.r Y.PY (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0) hSA hSig hθ
      hHaar hFD h x hx y hy) (FinTyp.conjT π) hne
  obtain ⟨B, k1, k2, k3, k4⟩ := GlobalTheory.RowLocalRows.form_of_conjT π B' h1 h2 h3 h4
  have hadm : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ Minf R.θ Y.PY (R.MY 0) ∧
      ∀ κ, NG.Cong D.host.E D.R.r N κ → actM Y.PY (R.MY 0) κ x = x}) := fun N hN =>
    GlobalTheory.FinTypesRows.minf_adm (M := R.MY 0) Y.PY hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open Y.PY Y.stdPsi.1) N hN
  have hfix : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f}) := fun N hN =>
    GlobalTheory.RowLocalRows.fixed_fd_of_conjT π N (GlobalTheory.RowLocalRows.fixed_fd_of_isotIn _ _ hadm _ hne N hN)
  obtain ⟨W, hWS, hW0, hst, hirr⟩ := _root_.GlobalTheory.exists_irreducible_sub_trivOutside_split D.host.E D.R.r π B k1 k2 k3 k4 hfix s
  exact GlobalTheory.RowLocal.isLocS_of_irr π s W hWS hW0 hst hirr

end GlobalTheory.RowLocalRows2

end
end

