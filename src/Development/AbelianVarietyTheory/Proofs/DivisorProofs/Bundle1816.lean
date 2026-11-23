module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslates
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.TranslatesDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermMat {G γ : Matrix (Fin r) (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec γ v) (Matrix.mulVec γ w) = herm G v w) :
    γᵀ * G * γ.map cc = G := by
  ext c d
  have h1 := h (Pi.single c 1) (Pi.single d 1)
  simp only [herm, Matrix.mulVec_single_one] at h1
  have h2 : (∑ a, ∑ b, (Pi.single c (1 : E) : Fin r → E) a * G a b *
      cc ((Pi.single d (1 : E) : Fin r → E) b)) = G c d := by simp [Pi.single_apply, cc]
  rw [← h2, ← h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem gramLact {G : Matrix (Fin r) (Fin r) E} {γ : GL (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) w) = herm G v w)
    (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G ((γ : Matrix (Fin r) (Fin r) E).map τ * M) = gram τ G M := by
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ := by
    ext a b; simp [cc, NumberField.IsCMField.complexEmbedding_complexConj]
  have key : ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
      ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) = G.map τ := by
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hermMat h]
  rw [FrameDegreeData.gram_eq, FrameDegreeData.gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  calc Mᵀ * ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
        (((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) * M.map (starRingEnd ℂ))
      = Mᵀ * (((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
        ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem lactGG {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {p0 : ℕ} {γ : GL (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) w) = herm G v w)
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : lact γ x ∈ GG Ψ G p0 := by
  intro τ
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    refine mul_ne_zero ?_ (hx τ).1
    have hd : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det := by
      rw [RingHom.map_det]; rfl
    rw [hd]
    exact (map_ne_zero τ.1).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)
  · have e : dmin G (lact γ x) τ i = dmin G x τ i := by
      unfold dmin; rw [hm, gramLact h]
    rw [e]; exact (hx τ).2 i

theorem lactMul {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem castGG {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {G : Matrix (Fin r) (Fin r) E} {p0 : ℕ}
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : castFrame h x ∈ GG Ψ' G p0 := by
  subst h; exact hx

section Two

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem domOfComp (c : C) {x : Frame (M.comp c).Ψ r} (hx : x ∈ (M.comp c).dom) :
    castFrame (M.comp_Ψ c) x ∈ M.dom := by
  have h := castGG (M.comp_Ψ c) hx
  rw [M.comp_Gm c, M.comp_basePoint c] at h
  exact h

theorem domToComp (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    castFrame (M.comp_Ψ c).symm x ∈ (M.comp c).dom := by
  have hx' : x ∈ GG M.Ψ (M.comp c).Gm (M.comp c).p0 := by
    rw [M.comp_Gm c, M.comp_basePoint c]; exact hx
  exact castGG (M.comp_Ψ c).symm hx'

theorem trDom (u : U) (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) : lact (M.tr u c) x ∈ M.dom :=
  lactGG (M.tr_herm u c) hx

theorem ssLact {la : Wt M.Ψ r} {F : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (c : C)
    {γ : GL (Fin r) E} (hγ : γ ∈ (M.comp c).Γ) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    F c (lact γ x) = F c x := by
  have h1 := (hF c).1.1.2.2 γ hγ (castFrame (M.comp_Ψ c).symm x) (domToComp M c hx)
  rw [M.χ_one c _ γ hγ, one_mul] at h1
  exact h1

theorem ssZero (la : Wt M.Ψ r) : (0 : C → Frame M.Ψ r → ℂ) ∈ M.SS la := by
  intro c
  exact ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ ξ x 0⟩

theorem ssAdd {la : Wt M.Ψ r} {F G : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (hG : G ∈ M.SS la) :
    F + G ∈ M.SS la := by
  intro c
  have h := hF c
  have h' := hG c
  have e : (fun y => (F + G) c (castFrame (M.comp_Ψ c) y)) =
      (fun y => F c (castFrame (M.comp_Ψ c) y)) + (fun y => G c (castFrame (M.comp_Ψ c) y)) := rfl
  rw [e]
  exact ⟨BoundedSectionAlgebra.bdd_add _ h.1 h'.1, fun ξ hξ x hx => by
    rw [BoundedSectionAlgebra.fj_add _ h.1 h'.1 hξ hx, h.2 ξ hξ x hx, h'.2 ξ hξ x hx, add_zero]⟩

theorem ssSum {la : Wt M.Ψ r} {ι : Type} (s : Finset ι) (f : ι → C → Frame M.Ψ r → ℂ)
    (h : ∀ i ∈ s, f i ∈ M.SS la) : ∑ i ∈ s, f i ∈ M.SS la :=
  Finset.sum_induction f (fun F => F ∈ M.SS la) (fun _ _ ha hb => ssAdd M ha hb) (ssZero M la) h

end Two

end GlobalTheory.TranslatesDet

namespace GlobalTheory.TranslatesDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem detNeAt [Fintype U] [DecidableEq U] {la : Wt M.Ψ r} {u u0 : C → Frame M.Ψ r → ℂ}
    (hu : u ∈ M.SS la) {c0 : C} {x0 : Frame M.Ψ r} (hx0 : x0 ∈ M.dom) (hne : u c0 x0 ≠ 0)
    (hz : ∀ h : U, h ≠ 1 → M.pull h u c0 x0 = 0)
    (hrep : ∀ (g : U) (y : Frame M.Ψ r), u0 (g • c0) y = u (g • c0) y) (k : U) :
    ∃ x ∈ M.dom, M.detTr u0 (k • c0) x ≠ 0 := by
  refine ⟨lact (M.tr k c0) x0, trDom M k c0 hx0, ?_⟩
  have ht1 : M.tr 1 c0 ∈ (M.comp c0).Γ := by
    have h := M.tr_mul 1 1 c0
    simp only [mul_one, one_smul] at h
    have e : M.tr 1 c0 * (M.tr 1 c0 * M.tr 1 c0)⁻¹ = (M.tr 1 c0)⁻¹ := by group
    rw [e] at h
    exact inv_mem_iff.mp h
  have ha : M.pull 1 u c0 x0 ≠ 0 := by
    simp only [TwoLevels.pull, one_smul]
    rw [ssLact M hu c0 ht1 hx0]
    exact hne
  have entry : ∀ g : U, M.pull g u0 (k • c0) (lact (M.tr k c0) x0) = M.pull (g * k) u c0 x0 := by
    intro g
    have hzd : lact (M.tr g (k • c0)) (lact (M.tr k c0) x0) ∈ M.dom :=
      trDom M g (k • c0) (trDom M k c0 hx0)
    have e1 : lact (M.tr (g * k) c0) x0 =
        lact (M.tr (g * k) c0 * (M.tr g (k • c0) * M.tr k c0)⁻¹)
          (lact (M.tr g (k • c0)) (lact (M.tr k c0) x0)) := by
      rw [lactMul (M.tr g (k • c0)) (M.tr k c0) x0, lactMul, inv_mul_cancel_right]
    simp only [TwoLevels.pull]
    rw [e1, ← mul_smul, hrep (g * k)]
    exact (ssLact M hu ((g * k) • c0) (M.tr_mul g k c0) hzd).symm
  let σ : Equiv.Perm U := (Equiv.inv U).trans (Equiv.mulRight k⁻¹)
  have key : ∀ h h' : U, h * h' * k = 1 ↔ σ h = h' := by
    intro h h'
    show h * h' * k = 1 ↔ h⁻¹ * k⁻¹ = h'
    constructor
    · intro e
      have e2 : h⁻¹ * (h * h' * k) * k⁻¹ = h' := by group
      rw [e] at e2
      simpa using e2
    · intro e
      rw [← e]
      group
  have hmat : (Matrix.of fun h h' : U => M.pull (h * h') u0 (k • c0) (lact (M.tr k c0) x0)) =
      (M.pull 1 u c0 x0 • (1 : Matrix U U ℂ)).submatrix σ id := by
    ext h h'
    rw [Matrix.of_apply, entry, Matrix.submatrix_apply, id, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases e : h * h' * k = 1
    · rw [if_pos ((key h h').1 e), e, mul_one]
    · rw [if_neg (fun e' => e ((key h h').2 e')), mul_zero]
      exact hz _ e
  unfold TwoLevels.detTr
  rw [hmat, Matrix.det_permute, Matrix.det_smul, Matrix.det_one, mul_one]
  refine mul_ne_zero ?_ (pow_ne_zero _ ha)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem independentTranslates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    IndependentTranslates E := by
  intro E _ _ _ r U C _ _ _ _ _ M hL s hs hsle
  classical
  have hB : ∀ c : C, ∃ x ∈ (M.comp c).dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) x := fun c => by
    obtain ⟨x, hx, h1, -⟩ := _root_.GlobalTheory.BalancedPointPf.balancedPoint E r (M.comp c)
    exact ⟨x, hx, h1⟩
  choose xb hxb hnc using hB
  have hI : ∀ c : C, ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c (castFrame (M.comp_Ψ c) (xb c)) ≠ 0 ∧
      (∀ h : U, h ≠ 1 → M.pull h u c (castFrame (M.comp_Ψ c) (xb c)) = 0) ∧
      ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := fun c =>
    _root_.GlobalTheory.LiftInterp.exists_form_one_lift E r U C M hL s hs hsle c _ (hnc c) (domOfComp M c (hxb c))
  choose uc huS hu0 hu1 hu2 using hI
  haveI : Fintype (Quotient (MulAction.orbitRel U C)) := Fintype.ofFinite _
  have hsum : ∀ c' y, (∑ q : Quotient (MulAction.orbitRel U C), uc q.out) c' y =
      uc (Quotient.mk (MulAction.orbitRel U C) c').out c' y := by
    intro c' y
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_eq_single (Quotient.mk (MulAction.orbitRel U C) c') (fun q _ hq => ?_)
      (fun h => absurd (Finset.mem_univ _) h)
    refine hu2 q.out c' (fun h hh => hq ?_) y
    have e : (Quotient.mk (MulAction.orbitRel U C) q.out) = Quotient.mk (MulAction.orbitRel U C) c' :=
      Quotient.sound (MulAction.orbitRel_apply.2 ⟨h⁻¹, by show h⁻¹ • c' = q.out; rw [← hh, inv_smul_smul]⟩)
    rwa [Quotient.out_eq] at e
  have hrep : ∀ (q : Quotient (MulAction.orbitRel U C)) (g : U) (y : Frame M.Ψ r),
      (∑ q' : Quotient (MulAction.orbitRel U C), uc q'.out) (g • q.out) y = uc q.out (g • q.out) y := by
    intro q g y
    rw [hsum]
    have e : Quotient.mk (MulAction.orbitRel U C) (g • q.out) = q :=
      (Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, rfl⟩)).trans (Quotient.out_eq q)
    rw [e]
  refine ⟨∑ q : Quotient (MulAction.orbitRel U C), uc q.out,
    ssSum M _ _ (fun q _ => huS q.out), fun c => ?_⟩
  obtain ⟨m, hm⟩ : (Quotient.mk (MulAction.orbitRel U C) c).out ∈ MulAction.orbit U c :=
    MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel U C) c)))
  have hk : m⁻¹ • (Quotient.mk (MulAction.orbitRel U C) c).out = c := by
    rw [← hm, inv_smul_smul]
  rw [← hk]
  exact detNeAt M (huS _) (domOfComp M _ (hxb _)) (hu0 _) (hu1 _) (hrep _) m⁻¹

end GlobalTheory.TranslatesDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteValuationCentredCompleteNormal
section
open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivVal

theorem exists_valuation_centre (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V) :
    ∃ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)),
      (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) ∧
        ∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1 := by
  classical
  haveI : IsNoetherianRing V := hV.1
  by_cases hm : maximalIdeal V = ⊥
  · refine ⟨1, fun v => ?_, fun v hv => ?_⟩
    · by_cases h : algebraMap V (FractionRing V) v = 0
      · simp [h]
      · simp [Valuation.one_apply_of_ne_zero h]
    · rw [hm, Ideal.mem_bot] at hv
      simp [hv]
  · obtain ⟨T, hT, g, hg, hc⟩ := GlobalTheory.GoodVal.exists_dvr_centre (R := V) (K := FractionRing V)
      (L := FractionRing V) (maximalIdeal V) hm
    have hg' : ∀ v : V, algebraMap T (FractionRing V) (g v) = algebraMap V (FractionRing V) v := fun v => by
      simpa using congrArg (fun f => f v) hg
    have hne : maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
    let P : IsDedekindDomain.HeightOneSpectrum T := ⟨maximalIdeal T, inferInstance, hne⟩
    refine ⟨P.valuation (FractionRing V), fun v => ?_, fun v hv => ?_⟩
    · rw [← hg']
      exact P.valuation_le_one (g v)
    · rw [← hg']
      refine (P.valuation_lt_one_iff_mem (g v)).2 ?_
      show g v ∈ maximalIdeal T
      rw [← Ideal.mem_comap, hc]
      exact hv

end GlobalTheory.DivVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbedding
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EquivConst

theorem exists_unit_constants {X G H C : Type} [Group G] [Finite G] [Group H] (L : G → H → Prop) (cp : H → X)
    (ρ : G → C → C) (r : C → H → ℂ) (mu : H → ℂ) (s : G → ℂ) (mv : X → G → X) (z : X → G → ℂ)
    (hex : ∀ g, ∃ k, L g k) (hL : ∀ g g' k k', L g k → L g' k' → L (g * g') (k * k'))
    (hρ1 : ∀ f, ρ 1 f = f) (hρ : ∀ g g' f, ρ (g * g') f = ρ g (ρ g' f))
    (hmu : ∀ h k, mu (h * k) = mu h * mu k) (hmu1 : ∀ h, ‖mu h‖ = 1)
    (hs1 : s 1 = 1) (hs : ∀ g g', s (g * g') = s g * s g')
    (hmv1 : ∀ x, mv x 1 = x) (hmv : ∀ x g g', mv x (g * g') = mv (mv x g) g')
    (hcp : ∀ g k, L g k → ∀ h, cp (h * k) = mv (cp h) g)
    (hz1 : ∀ x g, ‖z x g‖ = 1) (hz : ∀ g k, L g k → ∀ f h, r (ρ g f) h = z (cp h) g * r f (h * k))
    (hst : ∀ g k, L g k → ∀ h, cp (h * k) = cp h → ∀ f, mu h * r (ρ g f) h = s g * (mu (h * k) * r f (h * k))) :
    ∃ c : X → ℂ, (∀ x, ‖c x‖ = 1) ∧ ∀ g k, L g k → ∀ f h,
      c (cp h) * mu h * r (ρ g f) h = s g * (c (cp (h * k)) * mu (h * k) * r f (h * k)) := by
  classical
  choose l hl using hex
  have hsn : ∀ g, ‖s g‖ = 1 := by
    intro g
    let S : G →* ℂ := ⟨⟨s, hs1⟩, hs⟩
    have h1 : s g ^ Nat.card G = 1 := by
      show S g ^ Nat.card G = 1
      rw [← map_pow, pow_card_eq_one', map_one]
    have h2 : ‖s g‖ ^ Nat.card G = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Nat.card_pos.ne').1 h2
  have ne : ∀ {a : ℂ}, ‖a‖ = 1 → a ≠ 0 := fun {a} h h0 => by simp [h0] at h
  let good : X → Prop := fun x => ∃ f h, cp h = x ∧ r f h ≠ 0
  have hinv : ∀ g f, ρ g (ρ g⁻¹ f) = f := fun g f => by rw [← hρ, mul_inv_cancel, hρ1]
  have hgood : ∀ x g, good x → good (mv x g) := by
    rintro _ g ⟨f, h, rfl, hf⟩
    refine ⟨ρ g⁻¹ f, h * l g, hcp g _ (hl g) h, fun h0 => hf ?_⟩
    rw [← hinv g f, hz g _ (hl g), h0, mul_zero]
  have hgood' : ∀ x g, good (mv x g) → good x := fun x g h => by
    have := hgood _ g⁻¹ h
    rwa [← hmv, mul_inv_cancel, hmv1] at this
  have hone : ∀ x, good x → ∀ k, L 1 k → mu k = z x 1 := by
    rintro _ ⟨f, h, rfl, hf⟩ k hk
    have e1 := hz 1 k hk f h
    have e2 := hst 1 k hk h (by rw [hcp 1 k hk, hmv1]) f
    rw [hρ1] at e1 e2
    have h0 : r f (h * k) ≠ 0 := fun h0 => hf (by rw [e1, h0, mul_zero])
    rw [e1, hs1, hmu, one_mul] at e2
    have : mu h * r f (h * k) * mu k = mu h * r f (h * k) * z (cp h) 1 := by linear_combination -e2
    exact mul_left_cancel₀ (mul_ne_zero (ne (hmu1 h)) h0) this
  have hlift : ∀ x, good x → ∀ g k, L g k → mu k = mu (l g) := by
    intro x hx g k hk
    have e1 := hone x hx (k * l g⁻¹) (by simpa using hL _ _ _ _ hk (hl g⁻¹))
    have e2 := hone x hx (l g * l g⁻¹) (by simpa using hL _ _ _ _ (hl g) (hl g⁻¹))
    rw [hmu] at e1 e2
    exact mul_right_cancel₀ (ne (hmu1 _)) (e1.trans e2.symm)
  let w : X → G → ℂ := fun x g => if good x then z x g / (s g * mu (l g)) else 1
  have hw1 : ∀ x g, ‖w x g‖ = 1 := fun x g => by
    simp only [w]
    split_ifs
    · rw [norm_div, norm_mul, hz1, hsn, hmu1]; norm_num
    · exact norm_one
  have key : ∀ g k, L g k → ∀ f h, mu h * r (ρ g f) h = w (cp h) g * s g * (mu (h * k) * r f (h * k)) := by
    intro g k hk f h
    by_cases hg : good (cp h)
    · simp only [w, if_pos hg]
      rw [hz g k hk, hmu, hlift _ hg g k hk]
      have := ne (hsn g)
      have := ne (hmu1 (l g))
      field_simp
    · have h0 : r (ρ g f) h = 0 := by
        by_contra h0
        exact hg ⟨_, h, rfl, h0⟩
      have h1 : r f (h * k) = 0 := by
        have := hz g k hk f h
        rw [h0] at this
        exact (mul_eq_zero.1 this.symm).resolve_left (ne (hz1 _ _))
      rw [h0, h1]; simp
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.unitary_cocycle_coboundary_of_trivial_on_stabilisers mv w hmv1 hmv hw1 (by
    intro x g g'
    by_cases hg : good x
    · obtain ⟨f, h, rfl, hf⟩ := hg
      have e1 := key (g * g') (l g * l g') (hL _ _ _ _ (hl g) (hl g')) (ρ (g * g')⁻¹ f) h
      have e2 := key g (l g) (hl g) (ρ g' (ρ (g * g')⁻¹ f)) h
      have e3 := key g' (l g') (hl g') (ρ (g * g')⁻¹ f) (h * l g)
      rw [← hρ, e3, hcp g _ (hl g), mul_assoc h] at e2
      rw [hinv] at e1 e2
      rw [hs] at e1
      set P := mu (h * (l g * l g')) * r (ρ (g * g')⁻¹ f) (h * (l g * l g')) with hP
      have hP0 : P ≠ 0 := fun h0 => mul_ne_zero (ne (hmu1 h)) hf (by rw [e1, h0, mul_zero])
      have : s g * s g' * P * w (cp h) (g * g') = s g * s g' * P * (w (cp h) g * w (mv (cp h) g) g') := by
        linear_combination e2 - e1
      exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (ne (hsn g)) (ne (hsn g'))) hP0) this
    · simp only [w, if_neg hg, if_neg (fun h => hg (hgood' x g h)), mul_one]) (by
    intro x g hx
    by_cases hg : good x
    · obtain ⟨f, h, rfl, hf⟩ := hg
      have e1 := key g (l g) (hl g) (ρ g⁻¹ f) h
      have e2 := hst g (l g) (hl g) h (by rw [hcp g _ (hl g), hx]) (ρ g⁻¹ f)
      rw [hinv] at e1 e2
      set P := mu (h * l g) * r (ρ g⁻¹ f) (h * l g) with hP
      have hP0 : P ≠ 0 := fun h0 => mul_ne_zero (ne (hmu1 h)) hf (by rw [e1, h0, mul_zero])
      have : s g * P * w (cp h) g = s g * P * 1 := by linear_combination e2 - e1
      exact mul_left_cancel₀ (mul_ne_zero (ne (hsn g)) hP0) this
    · simp only [w, if_neg hg])
  refine ⟨c, hc1, fun g k hk f h => ?_⟩
  rw [mul_assoc, key g k hk, hcp g k hk, ← hc]
  ring

end GlobalTheory.EquivConst

namespace GlobalTheory.EquivConst

theorem isLift_mul {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g g' : G0 L.Pg L.r} {k k' : GA D V} (hk : Lev.IsLevelLift V β L g k) (hk' : Lev.IsLevelLift V β L g' k') :
    Lev.IsLevelLift V β L (g * g') (k * k') := by
  refine ⟨(GfC V).mul_mem hk.1 hk'.1, ?_, ?_⟩
  · rw [map_mul]; exact Subgroup.mul_mem _ hk.2.1 hk'.2.1
  · rw [map_mul, Formalism.L2.DIV.rTup_mul hk.2.1 hk'.2.1, hk.2.2, hk'.2.2]

theorem muVal_cast {D : D7} {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    (∀ g g', castDict hV mu (g * g') = castDict hV mu g * castDict hV mu g') ∧ ∀ g, ‖castDict hV mu g‖ = 1 := by
  subst hV
  refine ⟨fun g g' => ?_, fun g => h.norm g⟩
  show mu (g * g') = mu g * mu g'
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  have hxx : IsDetRoot V (g * g') (x * x') := by
    unfold IsDetRoot at *
    rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
    conv_lhs => rw [hx, hx']
    ring
  rw [h.2 _ _ hxx, h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem phiAt_apply {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    phiAt T i σ hV c f h = c (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h *
      rdU (T.U ((i : ℕ) + 1) σ) f (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2 := rfl


set_option maxHeartbeats 1000000 in
theorem exists_equivariant_constants : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∃ c', CUnit c' ∧ EqAt T R κ (O i) σ hV c' := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hI hT hpb hO i σ hσ hV
  have hact := (hO i).2.act.1
  have hkeep := fun g => GlobalTheory.T.levelAction_mem_cuspForms_of_action_laws T κ i (O i).lev2 hT.laws hact g (fun _ => rfl)
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_level_action_cusp_form_representation T κ i (O i).lev2 hT.laws hact hkeep
  have hex : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k :=
    fun g => ((hO i).2.lift.lev g).imp fun _ h => h.1
  obtain ⟨mv, hmv1, hmv, -, hcp⟩ := GlobalTheory.T.exists_finiteGroup_rightAction_components T R κ v₀ hI hT hpb i σ hσ hV hex
  choose y hy using _root_.GlobalTheory.ChiDetValues.chiC_mem_coeff T R κ v₀ hI hT i
  obtain ⟨z, hz1, hz⟩ := _root_.GlobalTheory.DictMove.rdU_actLev_eq T R κ v₀ O hI hT hpb hO i σ hσ hV
  have hst := _root_.GlobalTheory.StabMove.phiAt_actLev_of_comp_eq T R κ v₀ O hI hT hpb hO i σ hσ hV
  have hmu := muVal_cast hV (hT.laws.muVal _ (inR i) σ hσ)
  have hinj : Function.Injective fun a : T.Q.c.F => D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL a) :=
    D.what₂.embLL.injective.comp (algebraMap T.Q.c.F D.what₂.LL).injective
  have hy1 : y 1 = 1 := hinj (by
    show D.what₂.embLL _ = D.what₂.embLL _
    have : chiC R i 1 = 1 := by
      have := chiC_mul R i 1 1
      rw [mul_one] at this
      exact left_eq_mul.1 this
    rw [hy, this, map_one, map_one, Units.val_one])
  have hym : ∀ g g', y (g * g') = y g * y g' := fun g g' => hinj (by
    show D.what₂.embLL _ = D.what₂.embLL _
    rw [map_mul, map_mul, hy, hy, hy, chiC_mul, Units.val_mul])
  obtain ⟨c, hc1, hc⟩ := exists_unit_constants (C := Cu T κ i)
    (fun g k => Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k)
    (fun h => (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1) (fun g f => ρ g f)
    (fun f h => rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1)) (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1
      (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2)
    (castDict hV (T.mu ((i : ℕ) + 1) σ)) (fun g => σ (y g)) mv z hex
    (fun g g' k k' hk hk' => by
      have := isLift_mul hk hk'
      show Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (g * g')) _
      rw [map_mul]
      exact this)
    (fun f => by rw [map_one]; rfl) (fun g g' f => by rw [map_mul]; rfl) hmu.1 hmu.2
    (by rw [hy1, map_one]) (fun g g' => by rw [hym, map_mul]) hmv1 hmv hcp hz1
    (fun g k hk f h => by
      have := hz g k hk f f.2 h
      rw [← hρ] at this
      exact this)
    (fun g k hk h hh f => by
      have := hst g k hk (y g) (hy g) h hh f f.2
      rw [phiAt_apply, phiAt_apply, ← hρ, one_mul, one_mul] at this
      exact this)
  refine ⟨c, hc1, fun g k hk f hf => ⟨hkeep g f hf, y g, ?_, fun h => ?_⟩⟩
  · rw [hy, chiC, Units.coe_prod]
  · have := hc g k hk ⟨f, hf⟩ h
    rw [hρ] at this
    rw [phiAt_apply, phiAt_apply]
    exact this

end GlobalTheory.EquivConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoNonThickPlaceCentreWidthStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_nonThickPlace_centre_width : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → τ ∉ (GlobalTheory.ExpTie.Lift.wts L j).T2 → ((GlobalTheory.ExpTie.parOf L j).Top ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).b' * (1 + 1 / (GlobalTheory.ExpTie.parOf L j).x + 1 / (GlobalTheory.ExpTie.parOf L j).x ^ 2) + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) ∨ ((GlobalTheory.ExpTie.parOf L j).Thin ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).w'' + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.ExpTie.Lift.other_of_not_thick | exact GlobalTheory.ExpTie.Lift.other_of_not_thick | (intros; apply GlobalTheory.ExpTie.Lift.other_of_not_thick <;> assumption)
end

