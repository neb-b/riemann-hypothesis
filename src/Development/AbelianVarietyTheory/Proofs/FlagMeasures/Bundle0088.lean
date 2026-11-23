module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFineSubgroupMovesAtLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GoodPlace

theorem equality : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → S.gg = false → vE L S.ϖ S.G = 0 → (∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0) → (∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ) ∧ S.Hp = 1 ∧ (S.ampSq fun _ _ => True) = S.nn ∧ ∀ d, (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ hgg hG hD
  have hvth : S.vth = 0 := by simp [Frames.vth, hgg]
  have ha : S.a = 0 := by simp [Frames.a, hvth, hG]
  have hvD : S.vD = 0 := Finset.sum_eq_zero fun l _ => by
    split_ifs with h
    · exact hD l h.2
    · rfl
  have huniq := fun d Λ h => GlobalTheory.HL.UnimodTerm.term_unique L r k S d Λ h ha
  have key : ∀ d, ((S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1) ∧
      ENNReal.ofReal (‖S.amp d fun _ => True‖ ^ 2) = S.mass d fun _ => True := by
    intro d
    by_cases hex : ∃ Λ, S.IsTerm d Λ
    swap
    · have h0 : ∀ Λ, ¬ S.IsTerm d Λ := fun Λ h => hex ⟨Λ, h⟩
      simp [Frames.mass, Frames.amp, h0]
    obtain ⟨Λ₀, h₀⟩ := hex
    obtain ⟨-, -, hDO, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀
    obtain ⟨-, -, -, -, hDu, -⟩ := GlobalTheory.FrameBasic.main L r k S
    obtain ⟨-, -, -, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
    have hunit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1 := by
      intro l hl
      refine ⟨hDO l, ?_⟩
      obtain ⟨e, he⟩ := GlobalTheory.UnramOrder.exists_norm L (hDO l)
      have he0 : (e : F) ≠ 0 := fun h0 => by
        rw [h0, map_zero] at he
        apply hl
        rw [← L.cj_cj (S.D l), (hDu l hl).mul_right_eq_zero.1 he, map_zero]
      obtain ⟨u, hu⟩ := hvu _ he0
      rw [← he, hD l hl, zpow_zero, one_mul] at hu
      refine ⟨L.cj (S.D l) * algebraMap F E (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F),
        L.O.mul_mem (GlobalTheory.UnramOrder.cj_mem L (hDO l))
          ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subtype.property _)), ?_⟩
      rw [← mul_assoc, he, ← map_mul, hu, ← Subring.coe_mul, Units.mul_inv]
      simp
    obtain ⟨hC0, hw0, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hgg hunit
    set C0 := S.frameCls S.f S.f' with hC0def
    have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d
    have hint : ∀ Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun Λ h =>
      (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1

    have hm : (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
      rw [mass_eq_sumCls L r k S d _ (fun _ _ _ _ _ => trivial)]
      unfold Frames.sumCls
      let o₀ : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ C0
      rw [tsum_eq_single o₀ (fun o ho => if_neg fun hI => ho (by
        obtain ⟨h, hh, e⟩ := hall _ hI
        rw [← Quotient.out_eq o]
        exact Quotient.sound ⟨⟨h, hh⟩, e.symm⟩))]
      split_ifs with hI
      swap
      · exact Or.inl rfl
      obtain ⟨h, hh, e⟩ := hall _ hI
      have hw : S.wC o₀.out = 1 := by
        rw [e, ((volSt L r k S).2 C0 hC0.1).2.2.2 h hh, hw0]
      rw [hw, ENNReal.ofReal_one, one_mul]
      have hs : ({Λ | S.IsTerm d Λ ∧ True ∧ S.Fr d Λ = o₀.out} : Set (Submodule L.O S.V)).Subsingleton :=
        fun Λ hΛ Λ' hΛ' => (huniq d Λ' hΛ'.1).2 Λ hΛ.1 (hΛ.2.2.trans hΛ'.2.2.symm)
      unfold Frames.nT
      beta_reduce
      rcases hs.eq_empty_or_singleton with h1 | ⟨x, h1⟩
      · left; rw [h1]; simp
      · right; rw [h1]; simp
    refine ⟨hm, ?_⟩

    let o₁ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) := Quotient.mk _ Λ₀
    have hone : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o ≠ o₁ →
        ¬ (S.IsTerm d o.out ∧ True) := by
      intro o ho hT
      apply ho
      obtain ⟨h, hh, e⟩ := hall _ (hint _ hT.1)
      obtain ⟨h', hh', e'⟩ := hall _ (hint _ h₀)
      have hmem : h * h'⁻¹ ∈ S.St := S.St.mul_mem hh (S.St.inv_mem hh')
      have hA := hact Λ₀ h₀ _ hmem
      have e2 : (h * h'⁻¹) • Λ₀ = o.out := (huniq d _ hT.1).2 _ hA.1 (by
        rw [hA.2.2.2.2.1, e', e, smul_smul, inv_mul_cancel_right])
      rw [← Quotient.out_eq o]
      exact Quotient.sound ⟨⟨_, hmem⟩, e2⟩
    have e1 : (S.mass d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then ENNReal.ofReal (S.mu o₁.out) else 0 := by
      unfold Frames.mass
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    have e2 : (S.amp d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then (S.mu o₁.out : ℂ) * S.om d o₁.out else 0 := by
      unfold Frames.amp
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    rw [e1] at hm ⊢
    rw [e2]
    by_cases hT : S.IsTerm d o₁.out ∧ True
    swap
    · simp only [if_neg hT]; simp
    simp only [if_pos hT] at hm ⊢
    have hom : ‖S.om d o₁.out‖ = 1 := by
      obtain ⟨p, hp⟩ := hT.1
      exact (WitIndep.witness_independence L r k S d _ _ _ hp).2.2.2.2
    have hmu : 0 ≤ S.mu o₁.out := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    rw [norm_mul, hom, mul_one, Complex.norm_real, Real.norm_of_nonneg hmu]
    rcases hm with h | h
    · rw [le_antisymm (ENNReal.ofReal_eq_zero.1 h) hmu]; simp
    · rw [ENNReal.ofReal_eq_one.1 h]; simp
  refine ⟨fun d Λ h => (huniq d Λ h).1, by simp [Frames.Hp, hvth, ha, hvD], ?_, fun d => (key d).1⟩
  unfold Frames.ampSq Frames.nn
  congr 1
  funext d
  exact (key d).2

end GlobalTheory.HL.GoodPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMoveKernelSymm
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernSym

def flipMv (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] :
    A × B × C ≃+ A × B × C where
  toFun w := (w.1, -w.2)
  invFun w := (w.1, -w.2)
  left_inv w := by simp
  right_inv w := by simp
  map_add' w w' := by
    ext <;> simp [add_comm]

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem refA_map_flip (J : ℕ) (Λ : Submodule L.O S.V) :
    (S.refA J Λ).map (flipMv (S.V × S.V) S.V E).toAddMonoidHom = S.refA J Λ := by
  have key : ∀ w : S.MW, w ∈ S.refA J Λ → ((w.1, -w.2) : S.MW) ∈ S.refA J Λ := by
    intro w hw
    rw [Frames.refA, AddSubgroup.mem_prod] at hw ⊢
    exact ⟨hw.1, neg_mem hw.2⟩
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact key v hv
  · intro hw
    refine ⟨(w.1, -w.2), key w hw, ?_⟩
    show ((w.1, - -w.2) : S.MW) = w
    simp

theorem sOf_flip [CharZero F] (w : S.MW) (hs : S.sOf w + L.cj (S.sOf w) = S.h w.2.1 w.2.1) :
    S.sOf (w.1, -w.2) = L.cj (S.sOf w) := by
  have h1 : S.h (-w.2.1) (-w.2.1) = S.h w.2.1 w.2.1 := by
    simp [Frames.h, hf]
  have h2 : algebraMap F E 2⁻¹ + algebraMap F E 2⁻¹ = 1 := by
    rw [← map_add (f := _), ← map_one (algebraMap F E)]
    congr 1
    norm_num
  have h3 : L.cj (S.sOf w) = S.h w.2.1 w.2.1 - S.sOf w := by
    rw [← hs]; ring
  rw [h3]
  show algebraMap F E 2⁻¹ * S.h (-w.2.1) (-w.2.1) + -w.2.2 = _
  rw [h1, Frames.sOf]
  linear_combination (S.h w.2.1 w.2.1) * h2
end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mvTo_flip (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ Λ' : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hF : S.InFF β (j + 1) βJ d Λ) (hF' : S.InFF β (j + 1) βJ d Λ')
    (w : S.MW) (hw : S.MvTo (j + 1) d Λ Λ' w) : S.MvTo (j + 1) d Λ' Λ (w.1, -w.2) := by
  obtain ⟨hm, he⟩ := hw
  obtain ⟨Λ₁, h1, -, h3, h4, -⟩ :=
    _root_.GlobalTheory.HL.MoveTerm.move_term L r k S j β βJ d Λ hT hF w.1.1 w.1.2 w.2.1 (S.sOf w) hm
  have hΛ : Λ₁ = Λ' := SetLike.coe_injective (h1.trans he.symm)
  subst hΛ
  have hs := sOf_flip S w hm.2.2.2.2.2.2.2
  refine ⟨?_, ?_⟩
  · show S.IsMove (j + 1) d Λ₁ w.1.1 w.1.2 (-w.2.1) (S.sOf (w.1, -w.2))
    rw [hs]
    exact h4 hF'
  · show (Λ : Set S.V) = S.moved Λ₁ w.1.1 (-w.2.1) (S.sOf (w.1, -w.2))
    rw [hs]
    exact h3.symm
end

theorem kern_symm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → S.kern β (j + 1) βJ d Λ Λ' = S.kern β (j + 1) βJ d Λ' Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF Λ' hT' hF'
  obtain ⟨hr, hne⟩ := _root_.GlobalTheory.RefVol.main L r k S j β βJ d Λ hT hF Λ' hT' hF'
  obtain ⟨hmap, hchg⟩ := @GlobalTheory.T.indexMeasureIntegral_transport_and_change S.MW _ S.MW _
  have e1 := (hmap (flipMv (S.V × S.V) S.V E) (S.refA (j + 1) Λ)
    (ind (S.MvTo (j + 1) d Λ' Λ))).2
  rw [refA_map_flip] at e1
  have e2 : (fun w => ind (S.MvTo (j + 1) d Λ' Λ) (flipMv (S.V × S.V) S.V E w)) =
      ind (S.MvTo (j + 1) d Λ Λ') := by
    funext w
    have hiff : S.MvTo (j + 1) d Λ' Λ (flipMv (S.V × S.V) S.V E w) ↔ S.MvTo (j + 1) d Λ Λ' w := by
      constructor
      · intro h
        have h' := mvTo_flip S j β βJ d Λ' Λ hT' hF' hF _ h
        have hw : (((flipMv (S.V × S.V) S.V E w).1, -(flipMv (S.V × S.V) S.V E w).2) : S.MW) = w := by
          show ((w.1, - -w.2) : S.MW) = w
          simp
        rwa [hw] at h'
      · intro h
        exact mvTo_flip S j β βJ d Λ Λ' hT hF hF' w h
    simp only [ind, hiff]
  rw [e2] at e1
  have e3 := (hchg (S.refA (j + 1) Λ) (S.refA (j + 1) Λ') (ind (S.MvTo (j + 1) d Λ' Λ)) hne
    (hr ▸ hne)).2
  rw [← hr] at e3
  have e4 := mul_right_cancel₀ (Nat.cast_ne_zero.mpr hne) e3
  unfold Frames.kern
  rw [e4, e1]

end GlobalTheory.HL.KernSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMovesFiniteTargetsSplit
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem split_by_target {W Y Z : Type} [AddCommGroup W] (A B : AddSubgroup W) (M : W → Prop) (m : W → Z)
    (f : Y → Z) (hf : Function.Injective f) (hB : Fine A (ind M) B)
    (hm : ∀ w, M w → ∀ b ∈ B, m (w + b) = m w) (hex : ∀ w, M w → ∃ y, f y = m w) (c : ℝ) (hc : 0 ≤ c) :
    {y | ∃ w, M w ∧ f y = m w}.Finite ∧ (∀ y, Nice A (ind fun w => M w ∧ f y = m w)) ∧
    {y | c * (cint A (ind fun w => M w ∧ f y = m w)).re ≠ 0}.Finite ∧
    (∀ y, 0 ≤ c * (cint A (ind fun w => M w ∧ f y = m w)).re) ∧
    ∀ (P : Y → Prop) (g : Y → ℂ) (G : W → ℂ), (∀ w y, (M w ∧ f y = m w) → G w = if P y then g y else 0) →
      (∀ w, ¬ M w → G w = 0) → Nice A G ∧
      ∑ᶠ y : {y // P y}, ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y =
        (c : ℂ) * cint A G := by
  obtain ⟨hBA, hidx, hinv, hfin⟩ := hB
  have hsupp : Function.support (ind M) = {w | M w} := by
    ext w
    simp [ind]
  have hMinv : ∀ w, ∀ b ∈ B, (M (w + b) ↔ M w) := by
    intro w b hb
    have h := hinv w b hb
    simp only [ind] at h
    by_cases h1 : M (w + b) <;> by_cases h2 : M w <;> simp [h1, h2] at h ⊢
  have hTfin : {y | ∃ w, M w ∧ f y = m w}.Finite := by
    let g : Y → W ⧸ B := fun y =>
      if h : ∃ w, M w ∧ f y = m w then (QuotientAddGroup.mk h.choose : W ⧸ B) else 0
    refine Set.Finite.of_finite_image (f := g) (hfin.subset ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : ∃ w, M w ∧ f y = m w := hy
      refine ⟨hy'.choose, ?_, ?_⟩
      · rw [hsupp]
        exact hy'.choose_spec.1
      · simp only [g, dif_pos hy']
    · intro y1 hy1 y2 hy2 heq
      have hy1' : ∃ w, M w ∧ f y1 = m w := hy1
      have hy2' : ∃ w, M w ∧ f y2 = m w := hy2
      simp only [g, dif_pos hy1', dif_pos hy2'] at heq
      apply hf
      rw [hy1'.choose_spec.2, hy2'.choose_spec.2]
      have hb : -hy1'.choose + hy2'.choose ∈ B := QuotientAddGroup.eq.mp heq
      have h := hm _ hy1'.choose_spec.1 _ hb
      rw [add_neg_cancel_left] at h
      exact h.symm
  have hFine : ∀ y, Fine A (ind fun w => M w ∧ f y = m w) B := by
    intro y
    refine ⟨hBA, hidx, ?_, hfin.subset ?_⟩
    · intro w b hb
      simp only [ind]
      by_cases hw : M w
      · have h1 : M (w + b) := (hMinv w b hb).mpr hw
        simp only [h1, hw, true_and, hm w hw b hb]
      · have h1 : ¬ M (w + b) := fun h => hw ((hMinv w b hb).mp h)
        simp only [h1, hw, false_and]
    · apply Set.image_mono
      intro w hw
      rw [hsupp]
      by_contra hM
      refine (Function.mem_support.mp hw) ?_
      simp only [ind]
      rw [if_neg (fun h => hM h.1)]
  have hnice : ∀ y, Nice A (ind fun w => M w ∧ f y = m w) := fun y => ⟨B, hFine y⟩
  have hzero : ∀ y, y ∉ {y | ∃ w, M w ∧ f y = m w} → cint A (ind fun w => M w ∧ f y = m w) = 0 := by
    intro y hy
    have h : (ind fun w => M w ∧ f y = m w) = fun _ => 0 := by
      funext w
      simp only [ind]
      rw [if_neg]
      exact fun h => hy ⟨w, h⟩
    rw [h]
    simp [cint]
  obtain ⟨-, hI2, hI3, hI4⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A
  refine ⟨hTfin, hnice, hTfin.subset ?_, fun y => mul_nonneg hc (hI3 _).1, ?_⟩
  · intro y hy
    change c * _ ≠ 0 at hy
    by_contra hyT
    rw [hzero y hyT] at hy
    simp at hy
  · intro P g G hG hG0
    have hGeq : G = fun w => ∑ y ∈ hTfin.toFinset.filter P, g y * ind (fun w => M w ∧ f y = m w) w := by
      funext w
      by_cases hw : M w
      · obtain ⟨y0, hy0⟩ := hex w hw
        have hy0T : y0 ∈ hTfin.toFinset := by
          rw [Set.Finite.mem_toFinset]
          exact ⟨w, hw, hy0⟩
        rw [hG w y0 ⟨hw, hy0⟩]
        have hother : ∀ y, y ≠ y0 → ind (fun w => M w ∧ f y = m w) w = 0 := by
          intro y hne
          simp only [ind]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (hf (h.trans hy0.symm))
        by_cases hP : P y0
        · rw [if_pos hP, Finset.sum_eq_single y0]
          · simp only [ind]
            rw [if_pos ⟨hw, hy0⟩, mul_one]
          · intro y _ hne
            rw [hother y hne, mul_zero]
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨hy0T, hP⟩) h
        · rw [if_neg hP, Finset.sum_eq_zero]
          intro y hy
          have hne : y ≠ y0 := by
            rintro rfl
            exact hP (Finset.mem_filter.mp hy).2
          rw [hother y hne, mul_zero]
      · rw [hG0 w hw, Finset.sum_eq_zero]
        intro y _
        simp only [ind]
        rw [if_neg (fun h => hw h.1), mul_zero]
    have hcG : Nice A G ∧ cint A G =
        ∑ y ∈ hTfin.toFinset.filter P, g y * cint A (ind fun w => M w ∧ f y = m w) := by
      obtain ⟨hn, hs⟩ := hI4 Y (hTfin.toFinset.filter P)
        (fun y w => g y * ind (fun w => M w ∧ f y = m w) w) (fun y _ => (hI2 (g y) _ (hnice y)).1)
      rw [hGeq]
      exact ⟨hn, hs.trans (Finset.sum_congr rfl fun y _ => (hI2 (g y) _ (hnice y)).2)⟩
    refine ⟨hcG.1, ?_⟩
    rw [hcG.2]
    have hsub : Function.support (fun y : {y // P y} =>
        ((c * (cint A (ind fun w => M w ∧ f y.1 = m w)).re : ℝ) : ℂ) * g y.1) ⊆
        ↑(hTfin.toFinset.subtype P) := by
      intro y hy
      rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset]
      by_contra hyT
      refine (Function.mem_support.mp hy) ?_
      rw [hzero y.1 hyT]
      simp
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine (Finset.sum_subtype_eq_sum_filter
      (fun y => ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have him := (hI3 (fun w => M w ∧ f y = m w)).2
    have hre : ((cint A (ind fun w => M w ∧ f y = m w)).re : ℂ) = cint A (ind fun w => M w ∧ f y = m w) :=
      Complex.ext (by simp) (by simp [him])
    push_cast
    rw [hre]
    ring

theorem moves_split_by_target : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → {Λ₁ : Submodule L.O S.V | ∃ w, S.MvTo (j + 1) d Λ Λ₁ w}.Finite ∧ (∀ Λ₁, Nice (S.refA (j + 1) Λ) (ind (S.MvTo (j + 1) d Λ Λ₁))) ∧ {Λ₁ | S.kern β (j + 1) βJ d Λ Λ₁ ≠ 0}.Finite ∧ (∀ Λ₁, 0 ≤ S.kern β (j + 1) βJ d Λ Λ₁) ∧ ∀ (P : Submodule L.O S.V → Prop) (g : Submodule L.O S.V → ℂ) (G : S.MW → ℂ), (∀ w Λ₁, S.MvTo (j + 1) d Λ Λ₁ w → G w = if P Λ₁ then g Λ₁ else 0) → (∀ w, ¬ S.Mv (j + 1) d Λ w → G w = 0) → Nice (S.refA (j + 1) Λ) G ∧ ∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * g y = (S.cK β βJ : ℂ) * cint (S.refA (j + 1) Λ) G := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF
  obtain ⟨B, hB, hinv⟩ := _root_.GlobalTheory.MoveFine.main L r k S j β βJ d Λ hT hFF
  have hex : ∀ w, S.Mv (j + 1) d Λ w →
      ∃ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ w.1.1 w.2.1 (S.sOf w) := by
    intro w hw
    obtain ⟨Λ₁, h1, -⟩ := _root_.GlobalTheory.HL.MoveTerm.move_term L r k S j β βJ d Λ hT hFF w.1.1 w.1.2 w.2.1 (S.sOf w) hw
    exact ⟨Λ₁, h1⟩
  have hc : 0 ≤ S.cK β βJ := by
    unfold Frames.cK
    positivity
  exact split_by_target (S.refA (j + 1) Λ) B (S.Mv (j + 1) d Λ)
    (fun w => S.moved Λ w.1.1 w.2.1 (S.sOf w)) (fun Λ₁ : Submodule L.O S.V => (Λ₁ : Set S.V))
    SetLike.coe_injective hB (fun w hw b hb => (hinv w hw b hb).1) hex (S.cK β βJ) hc

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataMassEqSumFrameClasses
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem sumData_mass_eq_sumCls : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S P hP
  refine ⟨?_, fun h hh d C => ?_⟩
  · have e : (fun d => S.mass d (P d)) = fun d => S.sumCls fun C => S.nT d C (P d) :=
      funext fun d => mass_eq_sumCls L r k S d (P d) fun h hh Λ => hP h hh d Λ
    rw [e]
    unfold Frames.sumData Frames.sumCls
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun c => ?_
    split_ifs
    · exact tsum_congr fun o => mul_left_comm _ _ _
    · simp
  · unfold Frames.nT
    have e : ({Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = h • C} : Set (Submodule L.O S.V)) =
        (fun Λ => h • Λ) '' {Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C} := by
      ext Λ
      constructor
      · rintro ⟨h1, h2, h3⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h⁻¹ (S.St.inv_mem hh)
        refine ⟨h⁻¹ • Λ, ⟨A.1, hP _ (S.St.inv_mem hh) d Λ h1 h2, ?_⟩, smul_inv_smul h Λ⟩
        rw [A.2.2.2.2.1, h3, inv_smul_smul]
      · rintro ⟨Λ, ⟨h1, h2, h3⟩, rfl⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h hh
        refine ⟨A.1, hP _ hh d Λ h1 h2, ?_⟩
        rw [A.2.2.2.2.1, h3]
    rw [e, (MulAction.injective h).encard_image]

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetInFamilyMovedOfNotLeakStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_inFamily_moved_of_not_leak : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.InFF β (j + 1) βJ d Λ₁ := by
  first | exact @GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak | exact GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak | (intros; apply GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak <;> assumption)
end

