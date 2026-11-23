module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat.CFac

theorem coe_psi_mul_neg {k : Type} [AddGroup k] (ψ : AddChar k Circle) (a : k) : (ψ a : ℂ) * ψ (-a) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem coe_psi_add {k : Type} [AddGroup k] (ψ : AddChar k Circle) (a b : k) : (ψ (a + b) : ℂ) = ψ a * ψ b := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.LocFlat.CFac

namespace GlobalTheory.LocFlat
open GlobalTheory.LocFlat.CFac

theorem contrFactor : ContrFactor := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν n n' n'' _ _ _ _ _ _ M _ _ B h1 h2
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI hTD : ∀ (a b : Type) [Fintype a] [Fintype b], TotallyDisconnectedSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (TotallyDisconnectedSpace (a → b → k))
  haveI hLC : ∀ (a b : Type) [Fintype a] [Fintype b], LocallyCompactSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (LocallyCompactSpace (a → b → k))
  have hψlc := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψc
  obtain ⟨l, hl⟩ := _root_.GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB _ _ M B

  set X₁ := Matrix n (n' ⊕ Unit) k
  set X₂ := Matrix (n'' ⊕ Unit) n k

  let uy : X₁ × X₂ → k := fun z => z.2 (Sum.inr ()) ⬝ᵥ fun r => z.1 r (Sum.inr ())
  have huy : Continuous uy := by
    refine Continuous.dotProduct ?_ ?_
    · exact continuous_pi fun r => (continuous_apply r).comp ((continuous_apply (Sum.inr ())).comp continuous_snd)
    · exact continuous_pi fun r => (continuous_apply (Sum.inr ())).comp ((continuous_apply r).comp continuous_fst)
  have hχ : IsLocallyConstant fun z => (ψ (-uy z) : ℂ) := hψlc.comp_continuous huy.neg
  have hχi : IsLocallyConstant fun z => (ψ (uy z) : ℂ) := hψlc.comp_continuous huy
  let L : SB (X₁ × X₂) →ₗ[ℂ] M := l ∘ₗ mulLC _ hχi
  have key : ∀ f g, L (mulLC _ hχ (prodSB f g)) = B f g := by
    intro f g
    rw [← hl]
    show l _ = l _
    congr 1
    ext z
    simp only [mulLC_apply, ← mul_assoc, coe_psi_mul_neg, one_mul]
  have hspan : Submodule.span ℂ (Set.range fun q : SB X₁ × SB X₂ => mulLC _ hχ (prodSB q.1 q.2)) = ⊤ := by
    have hsurj : Function.Surjective (mulLC _ hχ) := fun F => ⟨mulLC _ hχi F, by
      ext z; simp only [mulLC_apply, ← mul_assoc]; rw [mul_comm (ψ (-uy z) : ℂ), coe_psi_mul_neg, one_mul]⟩
    rw [Set.range_comp' (mulLC _ hχ) (fun q : SB X₁ × SB X₂ => prodSB q.1 q.2), Submodule.span_image,
      _root_.GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]

  have transY : ∀ y₀ : n → k, L ∘ₗ comapH (Homeomorph.addRight ((fromCols 0 (Matrix.of fun r _ => y₀ r) : X₁), (0 : X₂))) = L := by
    intro y₀
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨⟨f, g⟩, rfl⟩
    have hc : IsLocallyConstant fun x : X₂ => (ψ (-(x (Sum.inr ()) ⬝ᵥ y₀)) : ℂ) :=
      hψlc.comp_continuous (Continuous.neg (Continuous.dotProduct
        (continuous_pi fun r => (continuous_apply r).comp (continuous_apply (Sum.inr ()))) continuous_const))
    set C : X₁ := fromCols 0 (Matrix.of fun r _ => y₀ r)
    let f' := comapH (Homeomorph.addRight C) f
    let g' := mulLC _ hc g
    have hu : ∀ z : X₁ × X₂, uy (z + (C, 0)) = uy z + z.2 (Sum.inr ()) ⬝ᵥ y₀ := by
      intro z
      simp only [uy, Prod.fst_add, Prod.snd_add, add_zero, Matrix.add_apply, C, fromCols_apply_inr, Matrix.of_apply]
      rw [← dotProduct_add]; rfl
    have e1 : comapH (Homeomorph.addRight (C, (0 : X₂))) (mulLC _ hχ (prodSB f g)) = mulLC _ hχ (prodSB f' g') := by
      ext z
      simp only [comapH_apply, mulLC_apply, prodSB_apply, Homeomorph.coe_addRight, f', g']
      rw [hu, neg_add, coe_psi_add]
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
      ring
    rw [LinearMap.comp_apply, e1, key, key]
    exact h2 y₀ f f' g g' (fun x => rfl) (fun x => rfl)
  have transU : ∀ u₀ : n → k, L ∘ₗ comapH (Homeomorph.addRight ((0 : X₁), (fromRows 0 (Matrix.of fun _ => u₀) : X₂))) = L := by
    intro u₀
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨⟨f, g⟩, rfl⟩
    have hc : IsLocallyConstant fun x : X₁ => (ψ (-(u₀ ⬝ᵥ fun r => x r (Sum.inr ()))) : ℂ) :=
      hψlc.comp_continuous (Continuous.neg (Continuous.dotProduct continuous_const
        (continuous_pi fun r => (continuous_apply (Sum.inr ())).comp (continuous_apply r))))
    set R : X₂ := fromRows 0 (Matrix.of fun _ => u₀)
    let f' := mulLC _ hc f
    let g' := comapH (Homeomorph.addRight R) g
    have hu : ∀ z : X₁ × X₂, uy (z + (0, R)) = uy z + u₀ ⬝ᵥ fun r => z.1 r (Sum.inr ()) := by
      intro z
      simp only [uy, Prod.fst_add, Prod.snd_add, add_zero, Matrix.add_apply, R, fromRows_apply_inr, Matrix.of_apply]
      rw [← add_dotProduct]; rfl
    have e1 : comapH (Homeomorph.addRight ((0 : X₁), R)) (mulLC _ hχ (prodSB f g)) = mulLC _ hχ (prodSB f' g') := by
      ext z
      simp only [comapH_apply, mulLC_apply, prodSB_apply, Homeomorph.coe_addRight, f', g']
      rw [hu, neg_add, coe_psi_add]
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
      ring
    rw [LinearMap.comp_apply, e1, key, key]
    exact h1 u₀ f f' g g' (fun x => rfl) (fun x => rfl)

  set X₀ := Matrix n n' k × Matrix n'' n k
  have hc1 : Continuous fun z : X₁ × X₂ => ((z.1.toCols₁, z.2.toRows₁), ((fun r => z.2 (Sum.inr ()) r), (fun r => z.1 r (Sum.inr ())))) := by
    refine Continuous.prodMk (Continuous.prodMk ?_ ?_) (Continuous.prodMk ?_ ?_)
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply (Sum.inl i)).comp continuous_snd)
    · exact continuous_pi fun r => (continuous_apply r).comp ((continuous_apply (Sum.inr ())).comp continuous_snd)
    · exact continuous_pi fun r => (continuous_apply (Sum.inr ())).comp ((continuous_apply r).comp continuous_fst)
  have hc2 : Continuous fun w : X₀ × ((n → k) × (n → k)) =>
      ((fromCols w.1.1 (Matrix.of fun r _ => w.2.2 r) : X₁), (fromRows w.1.2 (Matrix.of fun _ => w.2.1) : X₂)) := by
    refine Continuous.prodMk ?_ ?_
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      rcases j with j | j
      · exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp continuous_fst))
      · exact (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      rcases i with i | i
      · exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
      · exact (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  let e : X₁ × X₂ ≃ₜ X₀ × ((n → k) × (n → k)) :=
    { toFun := fun z => ((z.1.toCols₁, z.2.toRows₁), ((fun r => z.2 (Sum.inr ()) r), (fun r => z.1 r (Sum.inr ()))))
      invFun := fun w => (fromCols w.1.1 (Matrix.of fun r _ => w.2.2 r), fromRows w.1.2 (Matrix.of fun _ => w.2.1))
      left_inv := by
        rintro ⟨x₁, x₂⟩
        refine Prod.ext ?_ ?_
        · ext i j; rcases j with j | j <;> rfl
        · ext i j; rcases i with i | i <;> rfl
      right_inv := by
        rintro ⟨⟨p₁, p₂⟩, ⟨u, y⟩⟩
        rfl
      continuous_toFun := hc1
      continuous_invFun := hc2 }

  let L' : SB (X₀ × ((n → k) × (n → k))) →ₗ[ℂ] M := L ∘ₗ comapH e
  have hL' : ∀ (a : (n → k) × (n → k)) (G G' : SB (X₀ × ((n → k) × (n → k)))),
      (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L' G' = L' G := by
    rintro ⟨u₀, y₀⟩ G G' hG
    have h3 : comapH e G' = comapH (Homeomorph.addRight ((fromCols 0 (Matrix.of fun r _ => y₀ r) : X₁), (0 : X₂)))
        (comapH (Homeomorph.addRight ((0 : X₁), (fromRows 0 (Matrix.of fun _ => u₀) : X₂))) (comapH e G)) := by
      ext z
      simp only [comapH_apply, Homeomorph.coe_addRight]
      rw [hG]
      refine congrArg G.1 ?_
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · ext i j; show z.1 i (Sum.inl j) = z.1 i (Sum.inl j) + 0 + 0; simp
      · ext i j; show z.2 (Sum.inl i) j = z.2 (Sum.inl i) j + 0 + 0; simp
      · ext r; show z.2 (Sum.inr ()) r + u₀ r = z.2 (Sum.inr ()) r + 0 + u₀ r; simp
      · ext r; show z.1 r (Sum.inr ()) + y₀ r = z.1 r (Sum.inr ()) + y₀ r + 0; simp
    rw [LinearMap.comp_apply, h3, ← LinearMap.comp_apply (f := L), transY, ← LinearMap.comp_apply (f := L), transU]
    rfl
  obtain ⟨l₀, hl₀⟩ := _root_.GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors k ν hν X₀ n n M L' hL'
  refine ⟨l₀, fun Ψ₁ Ψ₂ => ?_⟩
  obtain ⟨Ψ, hΨ, hLΨ⟩ := hl₀ (comapH e.symm (mulLC _ hχ (prodSB Ψ₁ Ψ₂)))
  refine ⟨Ψ, ?_, ?_⟩
  · funext p
    rw [hΨ]
    unfold contr hat
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [comapH_apply, mulLC_apply, prodSB_apply]
    have h4 : uy (e.symm (p, (u, y))) = u ⬝ᵥ y := rfl
    rw [h4, neg_one_mul]
    change (ψ (-(u ⬝ᵥ y)) : ℂ) * (Ψ₁.1 (fromCols p.1 (Matrix.of fun r _ => y r)) * Ψ₂.1 (fromRows p.2 (Matrix.of fun _ => u))) = _
    ring
  · rw [← key, ← hLΨ]
    show L _ = L _
    congr 1
    ext z
    simp only [comapH_apply, Homeomorph.symm_apply_apply]

end GlobalTheory.LocFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorBoxEqCharSum
section
open ValuativeRel Matrix GlobalTheory.SplitWeil
open scoped Topology

noncomputable section
namespace GlobalTheory.BoxCharComb

open GlobalTheory.LocMod.Inhab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_box_superset {K : Set (Matrix Y Y' k)} (hK : IsCompact K) :
    ∃ R : kˣ, ∀ x ∈ K, x ∈ box Y Y' R := by
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (0 : k))
    (P := fun c x => c • x ∈ (box Y Y' (1 : kˣ) : Set (Matrix Y Y' k))) fun x _ =>
      (continuous_smul.tendsto' ((0 : k), x) 0 (zero_smul _ _)).eventually
        ((isOpen_box (Y := Y) (Y' := Y') (1 : kˣ)).mem_nhds (box Y Y' 1).zero_mem)
  obtain ⟨s, hs⟩ := exists_cball_subset h
  refine ⟨s⁻¹, fun x hx r q => ?_⟩
  have h1 : valuation k (((s : k) • x) r q) ≤ valuation k ((1 : kˣ) : k) :=
    hs (show (s : k) ∈ cball s from le_refl (valuation k (s : k))) x hx r q
  have e : x r q = (s : k)⁻¹ * (((s : k) • x) r q) := by
    rw [Matrix.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ s.ne_zero]
  rw [e, map_mul, Units.val_inv_eq_inv_val]
  exact mul_le_of_le_one_right' (by simpa only [Units.val_one, map_one] using h1)

end GlobalTheory.BoxCharComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearMapKillingPartialEvalIntegralKernelTransla
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor

theorem fill_add_single {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) (x : {e : m × m' // e ∈ it} → k) (e : m × m') (he : e ∈ it) (a : k) :
    fill ev it β t x + Matrix.single e.1 e.2 a = fill ev it β t (x + Pi.single ⟨e, he⟩ a) := by
  ext r q
  simp only [fill, Matrix.add_apply, Matrix.of_apply, Matrix.single_apply, Pi.add_apply]
  by_cases h : (r, q) ∈ it
  · rw [dif_pos h, dif_pos h]
    by_cases hrq : (r, q) = e
    · subst hrq
      simp [Pi.single_apply]
    · have h1 : ¬ (e.1 = r ∧ e.2 = q) := fun ⟨h1, h2⟩ => hrq (by rw [← h1, ← h2])
      have h2 : (⟨(r, q), h⟩ : {e : m × m' // e ∈ it}) ≠ ⟨e, he⟩ := fun h' => hrq (congrArg Subtype.val h')
      simp [h1, Pi.single_apply, h2]
  · rw [dif_neg h, dif_neg h]
    have h1 : ¬ (e.1 = r ∧ e.2 = q) := fun ⟨h1, h2⟩ => h (by rw [← h1, ← h2]; exact he)
    simp [h1]

theorem continuous_fill {k : Type} [Field k] [TopologicalSpace k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) : Continuous (fill ev it β t) := by
  refine continuous_pi fun r => continuous_pi fun q => ?_
  simp only [fill, Matrix.of_apply]
  by_cases h : (r, q) ∈ it
  · simp only [dif_pos h]; exact continuous_apply _
  · simp only [dif_neg h]; exact continuous_const

theorem hasCompactSupport_comp_fill {k : Type} [Field k] [TopologicalSpace k] [T2Space k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (hΘ : HasCompactSupport Θ) :
    HasCompactSupport (fun x => Θ (fill ev it β t x)) := by
  let pr : Matrix m m' k → ({e : m × m' // e ∈ it} → k) := fun T i => T i.1.1 i.1.2
  have hpr : Continuous pr := continuous_pi fun i => (continuous_apply i.1.2).comp (continuous_apply i.1.1)
  have hK : IsCompact (pr '' tsupport Θ) := hΘ.isCompact.image hpr
  refine HasCompactSupport.intro' hK hK.isClosed fun x hx => ?_
  by_contra h
  apply hx
  refine ⟨fill ev it β t x, subset_tsupport _ h, ?_⟩
  funext i
  simp [pr, fill, i.2]

theorem kerRed_translate_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ it, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
  intro k _ _ _ _ _ _ ψ ν _ _ hν m m' _ _ _ _ M _ _ l β ev it _ hK e he a Θ Θ' hΘ'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  rw [← sub_eq_zero, ← map_sub]
  apply hK
  intro t
  have hint : Integrable (fun x => Θ.1 (fill ev it β t x)) (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    ((Θ.2.1.continuous).comp (continuous_fill ev it β t)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_fill ev it β t Θ.1 Θ.2.2)
  have hint' : Integrable (fun x => Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)))
      (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    hint.comp_add_right _
  unfold red
  simp only [Submodule.coe_sub, Pi.sub_apply]
  have h1 : ∀ x, Θ'.1 (fill ev it β t x) = Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)) := by
    intro x; rw [hΘ', fill_add_single]
  simp_rw [h1]
  rw [integral_sub hint' hint, integral_add_right_eq_self (fun x => Θ.1 (fill ev it β t x)), sub_self]

end GlobalTheory.FlatFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearMapKillsPartialEvalIntegralKernelOfLaws
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor.KerEngine

def pullSB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : SB Y →ₗ[ℂ] SB X where
  toFun Φ := ⟨Φ.1 ∘ e, Φ.2.1.comp_continuous e.continuous, Φ.2.2.comp_homeomorph e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullSB_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (Φ : SB Y) (x : X) :
    (pullSB e Φ).1 x = Φ.1 (e x) := rfl

section Trip
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

abbrev Rest (ev it : Finset (m × m')) := {e : m × m' // e ∉ it ∧ e ∉ ev}

def toTrip (ev it : Finset (m × m')) (β t : Matrix m m' k) :
    (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k) :=
  (fun i => t i.1.1 i.1.2, fun i => t i.1.1 i.1.2 - β i.1.1 i.1.2, fun i => t i.1.1 i.1.2)

def ofTrip (ev it : Finset (m × m')) (β : Matrix m m' k)
    (x : (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k)) : Matrix m m' k :=
  Matrix.of fun r q => if h : (r, q) ∈ it then x.2.2 ⟨(r, q), h⟩
    else if h' : (r, q) ∈ ev then β r q + x.2.1 ⟨(r, q), h'⟩ else x.1 ⟨(r, q), h, h'⟩

theorem ofTrip_toTrip (ev it : Finset (m × m')) (β t : Matrix m m' k) : ofTrip ev it β (toTrip ev it β t) = t := by
  ext r q
  simp only [ofTrip, toTrip, Matrix.of_apply]
  split_ifs <;> ring

theorem toTrip_ofTrip (ev it : Finset (m × m')) (hd : Disjoint ev it) (β : Matrix m m' k)
    (x : (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k)) : toTrip ev it β (ofTrip ev it β x) = x := by
  obtain ⟨x₀, x₁, x₂⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
  · have h := i.2
    simp only [toTrip, ofTrip, Matrix.of_apply, dif_neg h.1, dif_neg h.2]
  · have h : i.1 ∉ it := Finset.disjoint_left.mp hd i.2
    simp only [toTrip, ofTrip, Matrix.of_apply, dif_neg h, dif_pos i.2]
    ring
  · simp only [toTrip, ofTrip, Matrix.of_apply, dif_pos i.2]

variable [TopologicalSpace k] [IsTopologicalRing k]

def trip (ev it : Finset (m × m')) (hd : Disjoint ev it) (β : Matrix m m' k) :
    Matrix m m' k ≃ₜ (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k) where
  toFun := toTrip ev it β
  invFun := ofTrip ev it β
  left_inv := ofTrip_toTrip ev it β
  right_inv := toTrip_ofTrip ev it hd β
  continuous_toFun := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_) <;> refine continuous_pi fun i => ?_
    · exact continuous_id.matrix_elem _ _
    · exact (continuous_id.matrix_elem _ _).sub continuous_const
    · exact continuous_id.matrix_elem _ _
  continuous_invFun := by
    refine continuous_matrix fun r q => ?_
    simp only [ofTrip, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply _).comp (continuous_snd.comp continuous_snd)
    · exact continuous_const.add ((continuous_apply _).comp (continuous_fst.comp continuous_snd))
    · exact (continuous_apply _).comp continuous_fst

theorem trip_apply (ev it : Finset (m × m')) (hd : Disjoint ev it) (β t : Matrix m m' k) :
    trip ev it hd β t = toTrip ev it β t := rfl

end Trip

end GlobalTheory.FlatFactor.KerEngine

namespace GlobalTheory.FlatFactor.KerEngine
open GlobalTheory.FlatFactor

section Laws
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

theorem sum_single_apply (it : Finset (m × m')) (a : m × m' → k) (r : m) (q : m') :
    (∑ e ∈ it, Matrix.single e.1 e.2 (a e)) r q = if (r, q) ∈ it then a (r, q) else 0 := by
  rw [Matrix.sum_apply]
  have : ∀ e : m × m', Matrix.single e.1 e.2 (a e) r q = if (r, q) = e then a e else 0 := by
    rintro ⟨x, y⟩
    simp only [Matrix.single_apply, Prod.mk.injEq]
    split_ifs <;> aesop
  simp_rw [this, Finset.sum_ite_eq]

theorem toTrip_add (ev it : Finset (m × m')) (hd : Disjoint ev it) (β t : Matrix m m' k) (a : {e // e ∈ it} → k) :
    toTrip ev it β (t + ∑ e ∈ it, Matrix.single e.1 e.2 (if h : e ∈ it then a ⟨e, h⟩ else 0)) =
      toTrip ev it β t + (0, 0, a) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
  · have h := i.2
    simp only [toTrip, Matrix.add_apply, sum_single_apply, h.1, if_false, add_zero,
      Pi.add_apply, Pi.zero_apply] <;> simp
  · have h : i.1 ∉ it := Finset.disjoint_left.mp hd i.2
    simp only [toTrip, Matrix.add_apply, sum_single_apply, h, if_false, add_zero,
      Pi.add_apply, Pi.zero_apply] <;> simp
  · simp only [toTrip, Matrix.add_apply, sum_single_apply, i.2, if_true, dif_pos,
      Pi.add_apply, Pi.zero_apply, zero_add] <;> simp

theorem ofTrip_zero (ev it : Finset (m × m')) (β : Matrix m m' k) (x₀ : Rest ev it → k) (a : {e // e ∈ it} → k) :
    ofTrip ev it β (x₀, 0, a) = fill ev it β (ofTrip ev it β (x₀, 0, 0)) a := by
  ext r q
  simp only [ofTrip, fill, Matrix.of_apply]
  split_ifs <;> simp

end Laws

theorem kerRed_of_laws : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → (∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ ev, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ it, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev it β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it hd h1 h2 Θ hΘ
  let e := trip (k := k) ev it hd β
  let l' := l ∘ₗ pullSB e
  have hback : pullSB e (pullSB e.symm Θ) = Θ := by
    ext t
    simp [pullSB_apply]
  have key := GlobalTheory.CoinvSB.kernel k ψ ν hψc hψ1 hν (Rest ev it) {x // x ∈ ev} {x // x ∈ it} M l' ?_ ?_
    (pullSB e.symm Θ) ?_
  · simpa [l', hback] using key
  · intro b Φ Φ' hΦ
    refine h1 (fun e => if h : e ∈ ev then b ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    congr 3
    simp only [e, trip_apply, toTrip, dotProduct]
    rw [← Finset.sum_coe_sort ev]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.2]
  · intro a Φ Φ' hΦ
    refine h2 (fun e => if h : e ∈ it then a ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    simp only [e, trip_apply]
    rw [toTrip_add ev it hd β t a]
  · intro x₀
    have hr := hΘ (ofTrip ev it β (x₀, 0, 0))
    simp only [red] at hr
    rw [← hr]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [pullSB_apply]
    rw [← ofTrip_zero]
    rfl

end GlobalTheory.FlatFactor.KerEngine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneIndexOfOneClassOfSupportOne
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain

theorem exists_affPt_of_flat_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c : ℕ} (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (h : GL (n ⊕ Fin c) k) (h0 : flat ψ ν μ Φ 1 h ≠ 0) :
    ∃ x₀ e, Φ ((h⁻¹).val * affPt 1 x₀ e) ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_not] at hne
  apply h0
  funext x₀
  have key : ∀ e, om μ 1 h Φ (affPt 1 x₀ e) = 0 := fun e => by
    have h1 : Φ ((h⁻¹).val * affPt 1 x₀ e * (1 : GL (n' ⊕ Fin (c + 1)) k).val) = 0 := by
      rw [Units.val_one, Matrix.mul_one]; exact hne x₀ e
    exact mul_eq_zero_of_right _ h1
  unfold flat opE
  simp only [key, zero_mul, integral_zero, Pi.zero_apply]

theorem oneIndex_of_oneClass_of_supportOne :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
      [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t]
      [DecidableEq t], S.OneClass t ν → S.SupportOne t → S.OneIndex t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hC hS j c hjc β hβ
  have := hν.1
  obtain ⟨h, rfl, h0⟩ := hβ
  obtain ⟨r, hr, u, hu, rfl⟩ := hC j c hjc h h0
  have HL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  have h1 := (GlobalTheory.UnfoldedEntries.flat_ne_zero_congr (ψ := S.ψ) (ν := ν) (h₂' := 1) (h₂ := u) (by omega)
    (HL.1 j (c + 1) (by omega)) rfl
    ((@DoubleCoset.eq _ _ _ _ _ _).2 ⟨r⁻¹, inv_mem hr, 1, one_mem _, by group⟩)).1 h0
  obtain ⟨x₀, e, he⟩ := exists_affPt_of_flat_ne_zero _ _ _ _ _ h1
  obtain ⟨r', hr', w, hw, rfl⟩ := hS j c hjc u hu x₀ e he
  exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(r * r')⁻¹, inv_mem (mul_mem hr hr'), w⁻¹, inv_mem hw, by group⟩

end GlobalTheory.SymChain
end
end

