module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ListProdMapNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

private theorem list_prod_map_pow_eq {α : Type} (l : List α) (f g : α → ℂ) (n : ℕ) (h : ∀ a, f a ^ n = g a ^ n) :
    (l.map f).prod ^ n = (l.map g).prod ^ n := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, mul_pow, ih, h]

private theorem list_prod_map_ne_zero {α : Type} (l : List α) (f : α → ℂ) (h : ∀ a, f a ≠ 0) :
    (l.map f).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons]; exact mul_ne_zero (h a) ih

theorem mono_pow_eq {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ χ' : (AE D)ˣ →* Circle) (n : ℕ) (hn : χ ^ n = χ' ^ n) :
    o.mono r e χ ^ n = o.mono r e χ' ^ n := by
  unfold TDat.mono
  apply list_prod_map_pow_eq
  intro i
  simp only [mul_pow, chrPow]
  congr 1
  have key : ∀ μ : (AE D)ˣ →* Circle, ((μ ((o.p i).idele o.q.unit) ^ e i : Circle) : ℂ) ^ n
      = ((((μ ^ n) ((o.p i).idele o.q.unit)) ^ e i : Circle) : ℂ) := by
    intro μ
    rw [MonoidHom.pow_apply, ← Circle.coe_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  rw [key χ, key χ', hn]

theorem mono_ne_zero {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ : (AE D)ˣ →* Circle) (hr : ∀ i, 0 < r i) : o.mono r e χ ≠ 0 := by
  unfold TDat.mono
  apply list_prod_map_ne_zero
  intro i
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast (hr i).ne'
  · exact Circle.coe_ne_zero _

theorem mono_unitRatio : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ) (χ χ' : (AE D)ˣ →* Circle)
    (S : ℕ → Prop), (∀ i, 0 < r i) → (∃ n : ℕ, 0 < n ∧ χ ^ n = χ' ^ n) → UnitRatio S (o.mono r e χ) (o.mono r e χ') := by
  intro D c k _ _ _ _ ι o r e χ χ' S hr ⟨n, hn, hχ⟩
  exact (_root_.GlobalTheory.Fam.unitRatio_laws S).2.2.1 _ _ n (mono_ne_zero o r e χ' hr) hn (mono_pow_eq o r e χ χ' n hχ)

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapContractionSupportFinitelyManyCells
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.LocFlat.CellsContr

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem opE_const_mul {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (C : ℂ)
    (F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun z => C * F z) x₀ = C * opE ψ ν p F x₀ := by
  simp only [opE]
  rw [← integral_const_mul]
  congr 1; funext e; ring

theorem opEFJ_const_mul {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ₀ : (n' → k) → ℂ) (C : ℂ)
    (F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν p Φ₀ (fun z => C * F z) x₀ = C * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν p Φ₀ F x₀ := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ, opE_const_mul]
  rw [← integral_const_mul]
  congr 1; funext u; ring

theorem om_eq_const_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ' : kˣ →* ℂˣ)
    (x : GL a k) (y : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ' x y Φ = fun z => ((μ' (Matrix.GeneralLinearGroup.det x) : ℂ) * ((μ' (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ)) *
      om 1 1 y (om 1 x 1 Φ) z := by
  funext z
  simp [om, nabs]
  ring
end
end GlobalTheory.LocFlat.CellsContr


open GlobalTheory.LocFlat.CellsContr in
theorem GlobalTheory.LocFlat.contr_support_finite_cells :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k),
    IsSelfDual ψ ν → ∀ (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] (c ρ : ℕ), c + 1 = 2 * ρ → ∀ (μ μ' : kˣ →* ℂˣ) (J : Subgroup (GL (n₂ ⊕ Fin c) k)),
    IsOpen (J : Set (GL (n₂ ⊕ Fin c) k)) → ∀ (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k))
    (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (a : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (x : GL (n₁ ⊕ Fin (c + 1)) k),
    ∃ T : Finset (GL (n₂ ⊕ Fin c) k), ∀ y : GL (n₂ ⊕ Fin c) k,
      GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) (om μ a x Φ₁.1)) (GlobalTheory.LocFlat.flRow ψ ν ρ (om μ' x y Φ₂.1)) ≠ 0 →
      ∃ r ∈ R k n₂ c ρ, ∃ t ∈ T, ∃ j ∈ J, y = r * t * j := by
  intro k _ _ _ _ _ _ ψ hψc hψ1 ν hsd n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ μ μ' J hJ Φ₁ Φ₂ a x
  classical
  haveI : ν.IsAddHaarMeasure := hsd.1
  have hρ1 : 1 ≤ ρ := by omega
  have hρc : ρ ≤ c := by omega
  have hker : IsOpen (((1 : kˣ →* ℂˣ).ker : Subgroup kˣ) : Set kˣ) := by
    rw [MonoidHom.ker_one]; exact isOpen_univ
  let Φ₁' : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) := ⟨om μ a x Φ₁.1, om_mem_SB μ a x Φ₁.2⟩

  obtain ⟨m, Ψ, Φ₀, hdec⟩ := (GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum k ψ hψc hψ1 ν hsd n₀ n₁ n₂ c ρ hcρ μ Φ₁' Φ₂).2.2.2.1

  let Φ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := ⟨om 1 x 1 Φ₂.1, om_mem_SB 1 x 1 Φ₂.2⟩
  have hav := fun i => (GlobalTheory.PosOne.avg_self_and_props k n₂ n₁ c ρ hρ1 hρc ψ hψc hψ1 ν hsd 1 hker Φ).2 (Φ₀ i)

  have hcov : ∀ i, ∃ T : Finset (GL (n₂ ⊕ Fin c) k), GlobalTheory.PosOne.Covers ρ J T fun h =>
      opE ψ ν ρ (om 1 1 h (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν 1 ρ (Φ₀ i).1 Φ.1)) := fun i =>
    GlobalTheory.PosOne.covers_opE_finite k n₂ n₁ c ρ hρ1 hρc ψ hψc hψ1 ν 1 hker J hJ ⟨_, (hav i).1⟩
  choose Ti hTi using hcov
  refine ⟨Finset.univ.biUnion Ti, fun y hy => ?_⟩
  obtain ⟨X, hX⟩ : ∃ X, GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁'.1)
      (GlobalTheory.LocFlat.flRow ψ ν ρ (om μ' x y Φ₂.1)) X ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (funext h)
  let Φ₂' : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := ⟨om μ' x y Φ₂.1, om_mem_SB μ' x y Φ₂.2⟩
  have hid := (GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum k ψ hψc hψ1 ν hsd n₀ n₁ n₂ c ρ hcρ μ Φ₁' Φ₂').2.2.2.2
    m Ψ Φ₀ hdec X
  have hX' := hX
  change GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁'.1) (GlobalTheory.LocFlat.flRow ψ ν ρ Φ₂'.1) X ≠ 0 at hX'
  rw [hid] at hX'
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX'
  have hi2 : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν ρ (Φ₀ i).1 (om μ' x y Φ₂.1) X.2 ≠ 0 := right_ne_zero_of_mul hi
  rw [om_eq_const_mul, opEFJ_const_mul] at hi2
  have hi3 : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν ρ (Φ₀ i).1 (om 1 1 y Φ.1) X.2 ≠ 0 := right_ne_zero_of_mul hi2
  have hne : opE ψ ν ρ (om 1 1 y (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν 1 ρ (Φ₀ i).1 Φ.1)) ≠ 0 := by
    rw [(hav i).2.1 y]
    intro h0
    exact hi3 (congrFun h0 X.2)
  obtain ⟨t, ht, hmk⟩ := (hTi i).2 y hne
  obtain ⟨r, hr, j, hj, hy'⟩ := (@DoubleCoset.eq _ _ _ _ t y).1 hmk.symm
  exact ⟨r, hr, t, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩, j, hj, hy'⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsCharactersFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TupChars

section Loc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cmp (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) : kˣ →* ℂˣ :=
  (Circle.toUnits.comp χ).comp (GlobalTheory.LocChar.unitsHom (ofSplit q))

theorem isComp_cmp (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) : (ofSplit q).IsComp χ (cmp q χ) := by
  intro x a ha
  have : GlobalTheory.LocChar.unitsHom (ofSplit q) x = a := Units.ext ha.symm
  simp only [cmp, MonoidHom.comp_apply, this]
  rfl

theorem cmp_apply (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) (x : kˣ) :
    ((cmp q χ x : ℂˣ) : ℂ) = (χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) : ℂ) := rfl

theorem unitsHom_int (q : GlobalTheory.FinPl.SplitPt D k) (y : kˣ) (hy : valuation k (y : k) = 1) :
    finPart D ((GlobalTheory.LocChar.unitsHom (ofSplit q) y : (AE D)ˣ) : AE D) ∈ intAE D := by
  have he1 : q.e * q.e = q.e := q.split.1
  show finPart D (q.sec y + (1 - q.e)) ∈ intAE D
  rw [(finPart D).map_add, (finPart D).map_sub, (finPart D).map_one]
  exact add_mem ((q.int_iff _).1 ((Valuation.mem_integer_iff _ _).2 hy.le))
    (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, he1])))

theorem unit_trivial (q : GlobalTheory.FinPl.SplitPt D k) {χ : (AE D)ˣ →* Circle}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ q.v) (x : kˣ) (hx : valuation k (x : k) = 1) :
    χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) = 1 := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  have he1 : q.e * q.e = q.e := q.split.1
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hes : q.e * q.sec x = q.sec x := by
    have := q.sec_pr (q.sec x)
    rw [q.pr_sec] at this
    exact this.symm
  have hz : algebraMap (AF D.host.F) (AE D) ε * (q.sec x - q.e) = q.sec x - q.e := by
    rw [← hsum]
    linear_combination (1 - cA D q.e) * hes - he1 + (q.sec x - 1) * hec
  obtain ⟨hi, hf⟩ := (GlobalTheory.VacStabFixed.supp_iff hε _).1 hz
  have hU : ((GlobalTheory.LocChar.unitsHom (ofSplit q) x : (AE D)ˣ) : AE D) = 1 + (q.sec x - q.e) := by
    show q.sec x + (1 - q.e) = _
    ring
  refine h _ ?_ (fun w hw => ?_) (unitsHom_int q x hx) ?_
  · rw [hU, (infPart D).map_add, (infPart D).map_one, hi, add_zero]
  · rw [hU, (finPart D).map_add, (finPart D).map_one, RingHom.map_add, RingHom.map_one, hf w hw, add_zero]
  · rw [← map_inv]
    exact unitsHom_int q x⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one])

theorem val_eq_one_of_sub (x : kˣ) (hx : valuation k ((x : k) - 1) < 1) : valuation k (x : k) = 1 := by
  have e : (x : k) = ((x : k) - 1) + 1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

end Loc

section Pack

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex}

end Pack

end GlobalTheory.TupChars

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMulVecMemAdeleIdealSupportedOnPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl

theorem matrix_mulVec_mem_adeleIdealSupportedOnPlaces {D : D7} {P : Pl D → Prop} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D))
    (y : Fin n → AE D) (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem matrixColumnScaledByAdele_zero {D : D7} {m n : ℕ} (x : Mx D m n) (i : Fin n) : colMul x i 0 = 0 := by
  funext k; simp [colMul]

theorem carriesLattice_wittEmbedding_iff_core : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (L₀ : GlobalTheory.FinPl.Lat S₀) (v : GlobalTheory.FinPl.Pl D) (g : GA D S₀), GlobalTheory.FinPl.MonoAt d L L₀ v → (GlobalTheory.FinPl.Moves S (d.emb0 g) L L (· = v) ↔ GlobalTheory.FinPl.Moves S₀ g L₀ L₀ (· = v)) := by
  intro D S S₀ ρ d L L₀ v g hM
  have hpX : ∀ z : Fin S₀.rank → AE D, d.pX *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
  have hpY : ∀ z : Fin S₀.rank → AE D, d.pY *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
  have hp0 : ∀ z : Fin S₀.rank → AE D, d.p0 *ᵥ (d.j0 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
  have key : ∀ z : Fin S₀.rank → AE D, d.j0 *ᵥ z ∈ latV S L (· = v) ↔ z ∈ latV S₀ L₀ (· = v) := fun z => by
    rw [hM, hpX, hpY, hp0]
    simp only [Pi.zero_apply, matrixColumnScaledByAdele_zero, zero_mem, implies_true, true_and]
  have hj : ∀ z : Fin S₀.rank → AE D, mt S (d.emb0 g) *ᵥ (d.j0 *ᵥ z) = d.j0 *ᵥ (mt S₀ g *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  constructor
  · intro h z hz
    rw [← key, ← key, ← hj]
    exact h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hz)
  · intro h y hy
    have eX : d.pX *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pX *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
    have eY : d.pY *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pY *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
    have e0 : d.p0 *ᵥ (mt S (d.emb0 g) *ᵥ y) = mt S₀ g *ᵥ (d.p0 *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding]
    rw [hM y, hM (mt S (d.emb0 g) *ᵥ y), eX, eY, e0]
    exact and_congr Iff.rfl (and_congr Iff.rfl (h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hy)))

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitInt

variable {D : D7}

theorem mem_latV_iff_at (S : HSp D) (N : Lat S) {P : Pl D → Prop} {v : Pl D} (hv : P v)
    (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S N P ↔ y ∈ latV S N (· = v) := by
  constructor
  · intro h
    have h2 := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)) h
    have e : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy i)
    rwa [e] at h2
  · intro h
    exact GlobalTheory.FinPl.KSplit.latV_mono S N (fun w hw => by subst hw; exact hv) h

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_sec (q : SplitPt D k) (a : AE D) (b : k) : a * q.sec b = q.sec (q.pr a * b) := by
  have h := q.sec_pr (a * q.sec b)
  have h2 := q.sec_pr (q.sec b)
  rw [q.pr_sec] at h2
  rw [RingHom.map_mul, q.pr_sec] at h
  rw [h, mul_left_comm, ← h2]

theorem mulVec_sec (q : SplitPt D k) {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D)) (b : Fin n → k) :
    (M *ᵥ fun i => q.sec (b i)) = fun i => q.sec ((M.map q.pr *ᵥ b) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum q.sec]
  exact Finset.sum_congr rfl fun j _ => mul_sec q _ _

theorem mem_KO_of_keeps {Y : Type} [Fintype Y] [DecidableEq Y] (x : GL Y k)
    (h : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ ∀ i, (x.val *ᵥ y) i ∈ 𝒪[k]) : x ∈ GlobalTheory.SplitWeil.KO k Y := by
  have h1 : ∀ j i : Y, (Pi.single j (1 : k) : Y → k) i ∈ 𝒪[k] := by
    intro j i
    by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  have hc : ∀ (A : Matrix Y Y k) (i j : Y), (A *ᵥ (Pi.single j (1 : k) : Y → k)) i = A i j := by
    intro A i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hA : ∀ i j, x.val i j ∈ 𝒪[k] := fun i j => by
    rw [← hc x.val i j]; exact (h _).1 (h1 j) i
  have hB : ∀ i j, (x⁻¹).val i j ∈ 𝒪[k] := fun i j => by
    rw [← hc (x⁻¹).val i j]
    refine (h _).2 ?_ i
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact h1 j
  have hinj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix : Matrix Y Y 𝒪[k] → Matrix Y Y k) :=
    fun a b hab => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hab i) j)
  let A : Matrix Y Y 𝒪[k] := Matrix.of fun i j => ⟨x.val i j, hA i j⟩
  let B : Matrix Y Y 𝒪[k] := Matrix.of fun i j => ⟨(x⁻¹).val i j, hB i j⟩
  have eA : (algebraMap 𝒪[k] k).mapMatrix A = x.val := rfl
  have eB : (algebraMap 𝒪[k] k).mapMatrix B = (x⁻¹).val := rfl
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext eA⟩
  · rw [RingHom.map_mul, RingHom.map_one, eA, eB, Units.mul_inv]
  · rw [RingHom.map_mul, RingHom.map_one, eA, eB, Units.inv_mul]

end

theorem mem_KO_of_moves : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (N : Lat S) (P : Pl D → Prop), P q.v → IntIn q S F N → ∀ g : GA D S, Moves S g N N P → ∀ x : GL Y k, (mt S g).map q.pr = F.β * x.val * F.γ → x ∈ GlobalTheory.SplitWeil.KO k Y := by
  intro D k _ _ _ _ q S Y _ _ F N P hP hI g hM x hx
  refine mem_KO_of_keeps x fun y => ?_
  have hs : ∀ (b : Fin S.rank → k) i, (fun i => q.sec (b i)) i ∈ idAt D (· = q.v) := fun b i => q.sec_mem_idAt _
  have e : (Formalism.L2.Theta.mt S g).map q.pr *ᵥ (F.β *ᵥ y) = F.β *ᵥ (x.val *ᵥ y) := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  rw [hI y, hI (x.val *ᵥ y), ← mem_latV_iff_at S N hP _ (hs _), ← mem_latV_iff_at S N hP _ (hs _),
    hM _ (fun i => GlobalTheory.FinPl.KSplit.idAt_mono (fun w hw => by subst hw; exact hP) (hs _ i)), mulVec_sec, e]

end GlobalTheory.SplitInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

set_option synthInstance.maxHeartbeats 200000

theorem idV_incA_mul {D : D7} (c : D.host.E) (𝔞 : FI D) (v : Pl D) {y : AE D} (hy : y ∈ idV 𝔞 v) :
    incA D c * y ∈ idV (FractionalIdeal.spanSingleton _ c * 𝔞) v := by
  have hle : idV 𝔞 v ≤ (idV (FractionalIdeal.spanSingleton _ c * 𝔞) v).comap (AddMonoidHom.mulLeft (incA D c)) := by
    rw [idV, AddSubgroup.closure_le]
    rintro _ ⟨α, h₁, h₂, a, ha, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, h₁, h₂, c * a,
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ c) ha, ?_⟩
    show incA D c * _ = _
    simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  exact hle hy

theorem idV_le_idAt {D : D7} (𝔞 : FI D) (v : Pl D) : idV 𝔞 v ≤ (idAt D (· = v)).toAddSubgroup := by
  rw [idV, AddSubgroup.closure_le]
  rintro _ ⟨α, h₁, h₂, a, ha, rfl⟩
  simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, idAt, Submodule.mem_inf, Submodule.mem_iInf,
    RingHom.mem_ker]
  refine ⟨?_, fun w => ?_⟩
  · change (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _)) ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a) = 0
    rw [Algebra.TensorProduct.map_tmul]
    change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E a) = 0
    exact TensorProduct.zero_tmul _ _
  · have e : FinPl.compAt D w.1 ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a) = (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] a := rfl
    rw [e, h₂ w.1 w.2]
    exact TensorProduct.zero_tmul _ _

theorem idV_spanSingleton_mul_iff : ∀ (D : D7) (v : Pl D) (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s,
    s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 x hx s
  constructor
  · intro hs
    refine ⟨?_, idV_le_idAt _ v hs⟩
    have h := idV_incA_mul x⁻¹ _ v hs
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hx,
      FractionalIdeal.spanSingleton_one, one_mul] at h
  · rintro ⟨h, -⟩
    have h' := idV_incA_mul x 𝔞 v h
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul] at h'

end GlobalTheory.SeeSaw
end
end

