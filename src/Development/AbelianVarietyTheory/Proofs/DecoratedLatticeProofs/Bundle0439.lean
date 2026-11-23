module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperators
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0412
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing MeasureTheory

noncomputable section

namespace GlobalTheory.FinPl.LiftExactPf

theorem frame_card {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (α : Frame p S n) :
    Fintype.card n = S.rank := by
  have h1 := Matrix.rank_mul_le_left α.b α.b'
  have h2 := Matrix.rank_mul_le_left α.b' α.b
  rw [α.bb', Matrix.rank_one] at h1
  rw [α.b'b, Matrix.rank_one] at h2
  have h3 := Matrix.rank_le_card_width α.b
  have h4 := Matrix.rank_le_card_width α.b'
  simp only [Fintype.card_fin] at h1 h4
  omega

theorem chrPow_mul_neg {D : D7} (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) :
    chrPow χ a e * chrPow χ a (-e) = 1 := by
  unfold chrPow
  rw [← Circle.coe_mul, ← zpow_add, add_neg_cancel, zpow_zero, Circle.coe_one]

end GlobalTheory.FinPl.LiftExactPf

namespace GlobalTheory.FinPl


open GlobalTheory.FinPl.LiftRam GlobalTheory.FinPl.LiftExactPf in
theorem liftExact : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  intro D k _ _ _ _ p q χ hχ
  refine ⟨-1, Or.inr rfl, ?_⟩
  intro n n' _ _ _ _ ψ S T hS vS χS χT om hW hχS hχT α β P Q a ha LS LT f₀ f hOv φ₀ hφ₀ ε
  have haq : a = p.idele q.unit := Units.ext (by rw [SplitPt.idele_val, ha]; abel)
  subst haq
  obtain ⟨lS, lT, hlS, hlT, hlSq, hlTq, hlinE⟩ := _root_.GlobalTheory.LinExactAt.linExact D k p q ψ S T χS χT om hW
  obtain ⟨lS₀, lT₀, -, -, hlin⟩ := _root_.GlobalTheory.SplitLinAt.linModelAt D k p ψ S T χS χT om hW
  have hK := _root_.GlobalTheory.KernelCommExplicit.kernelsCommuteExplicitConst k n n' q χ hχ lS lT (hlS hχT) (hlT hχS) P Q
  have hOv2 := hOv
  obtain ⟨hLS, hLT, hVac, -, -⟩ := hOv2
  obtain ⟨hex, hth, -⟩ := _root_.GlobalTheory.FinPl.overBasic D k p n n' ψ hW.std S T α β LS LT hLS hLT f₀ hVac

  let F : SB (Matrix n n' k) → WO S T → ℂ := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose
  have hF : ∀ Ψ : SB (Matrix n n' k), Over ψ α β LS LT f₀ Ψ.1 (F Ψ) := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose_spec
  have hFu : ∀ (Ψ : SB (Matrix n n' k)) g, Over ψ α β LS LT f₀ Ψ.1 g → g = F Ψ :=
    fun Ψ g hg => (hex Ψ.1 Ψ.2).unique hg (hF Ψ)
  have hFth : ∀ Ψ, IsThetaFunO ψ S T (F Ψ) := fun Ψ => (hth _ _ (hF Ψ)).1
  have hFlin : ∀ (a : ℂ) (Ψ Ψ' : SB (Matrix n n' k)), F (a • Ψ + Ψ') = a • F Ψ + F Ψ' := fun a Ψ Ψ' =>
    (hFu (a • Ψ + Ψ') _ ((hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).2.2 a Ψ'.1 (F Ψ') (hF Ψ'))).symm
  have hF0 : F 0 = 0 := by
    have h1 := hFlin 1 0 0
    simp only [one_smul, add_zero] at h1
    have h2 : F 0 + F 0 = F 0 + 0 := by rw [← h1, add_zero]
    exact add_left_cancel h2
  have hFadd : ∀ Ψ Ψ' : SB (Matrix n n' k), F (Ψ + Ψ') = F Ψ + F Ψ' := fun Ψ Ψ' => by
    simpa using hFlin 1 Ψ Ψ'
  have hFsmul : ∀ (a : ℂ) (Ψ : SB (Matrix n n' k)), F (a • Ψ) = a • F Ψ := fun a Ψ => by
    simpa [hF0] using hFlin a Ψ 0
  have hint : ∀ (v : contAutSub S) (Ψ : SB (Matrix n n' k)) h,
      IntegrableOn (fun g => om (g, h) (F Ψ) 0 * v.1 g) vS.𝓕 vS.μ :=
    fun v Ψ h => (lift_facts hS vS hW (hFth Ψ) v.2).1 h

  let θ : contAutSub S →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] (GA D T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Ψ => liftT om vS.μ vS.𝓕 v.1 (F Ψ))
      (fun v₁ v₂ Ψ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, Submodule.coe_add, mul_add]
        exact integral_add (hint v₁ Ψ h) (hint v₂ Ψ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_left_comm _ a]
        exact integral_const_mul a _)
      (fun v Ψ₁ Ψ₂ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, hFadd, map_add (f := _), add_mul]
        exact integral_add (hint v Ψ₁ h) (hint v Ψ₂ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, hFsmul, map_smul, smul_eq_mul, mul_assoc]
        exact integral_const_mul a _)
  have hθ : ∀ v Ψ, θ v Ψ = liftT om vS.μ vS.𝓕 v.1 (F Ψ) := fun v Ψ => rfl
  have hEq : ∀ (g : GL n' k) (h : GL n k) (v : contAutSub S) (Ψ Ψ' : SB (Matrix n n' k)),
      (∀ x, Ψ'.1 x = (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) *
        Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (repAut α g v) Ψ' = β.rep h (θ v Ψ) := by
    intro g h v Ψ Ψ' hΨ
    have e : F Ψ' = om (α.gl g, β.gl h) (F Ψ) := by
      refine (hFu Ψ' _ ?_).symm
      have := hlinE n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ) g h
      convert this using 1
      funext x
      exact hΨ x
    funext h₁
    rw [hθ, hθ, rep_apply, liftT_apply, liftT_apply, e, repAut_val]
    simp only [rep_apply, LiftRam.om_mul]
    exact setIntegral_mul_right hS vS (fun x => om (x, h₁ * β.gl h) (F Ψ) 0 * v.1 x)
      (fun γ hγ x => by rw [om_left hW (hFth Ψ) hγ, v.2.1 γ hγ x]) (α.gl g)
  obtain ⟨K, hKval, hKdia, hKram⟩ := hK (contAutSub S) (GA D T → ℂ) (repAut α) β.rep θ hEq
  obtain ⟨φ, ⟨hφE, hφM, hφC⟩, rfl⟩ := hφ₀
  let φ' : EqForm (repAut α) := ⟨toAut hφC, fun g P₁ => Subtype.ext (hφE g P₁)⟩
  have hφ'M : φ'.1 ∈ Mram k n' (contAutSub S) := by
    letI := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun P₁ => Subtype.ext ?_
    have := (mem_Mram _).1 hφM P₁
    simpa [φ', toAut, Submodule.coe_sum] using this
  have hFf : F (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) = f := (hFu _ f hOv).symm
  have hfth : IsThetaFunO ψ S T f := hFf ▸ hFth _
  set φT : Form k n (GA D T → ℂ) := (K φ').1 with hφT
  have hφTQ : φT Q = liftT om vS.μ vS.𝓕 (φ P) f := by
    rw [hφT, hKval φ', hθ, hFf]
    rfl
  have hcQ : IsContAut T (φT Q) := by
    rw [hφTQ]
    exact (lift_facts hS vS hW hfth (hφC P)).2
  have hRam : IsRam β φT := by
    refine ⟨(K φ').2, (hKram φ' hφ'M).1, fun Q' => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q Q'
    have e : φT (g • Q) = β.rep g (φT Q) := (K φ').2 g Q
    rw [e]
    exact isContAut_mul_right hcQ (β.gl g)
  set c : ℂ := (lS q.unit : ℂ) * (lT q.unit : ℂ) with hc
  have h1 := (hKram φ' hφ'M).2
  have h2 := hKdia ε ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩
  have h3 := hKval ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩
  have key : liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f =
      c • FFStar q (resChar χ hχ q) φT (ε • Q) := by
    calc liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f
        = θ (dia ε (FFStar q (resChar χ hχ q) φ'.1) P) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) := by
          rw [hθ, hFf, dia_apply]
          exact congrArg (liftT om vS.μ vS.𝓕 · f) (toAut_FFStar q _ hφC (ε • P)).symm
      _ = (K ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩).1 Q := h3.symm
      _ = dia ε (K ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩).1 Q := by rw [h2]
      _ = c • FFStar q (resChar χ hχ q) φT (ε • Q) := by rw [h1, dia_apply]; rfl

  have hQ : (0 : ℝ) < resCard k := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  have hnT := frame_card β
  have hnS := frame_card α
  have hR : ((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2)) * ((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2)) *
      ((resCard k : ℝ) ^ ((S.rank : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add hQ, ← Real.rpow_add hQ, hnT, hnS]
    convert Real.rpow_zero (resCard k : ℝ) using 2
    ring
  have hR' : (((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      (((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2) : ℝ) : ℂ) * (((resCard k : ℝ) ^ ((S.rank : ℝ) / 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hR
  have eS := chrPow_mul_neg χS (p.idele q.unit) (-1)
  have eT := chrPow_mul_neg χT (p.idele q.unit) 1
  simp only [neg_neg] at eS ⊢
  have hCc : ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      chrPow χS (p.idele q.unit) (-1) * chrPow χT (p.idele q.unit) 1) * c = 1 := by
    rw [hc, hlSq, hlTq]
    linear_combination (chrPow χS (p.idele q.unit) (-1) * chrPow χS (p.idele q.unit) 1 *
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1))) * hR' +
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1)) * eS + eT
  rw [← hφTQ]
  unfold sOp
  rw [formAt_eq α hφE P, formAt_eq β hRam.1 Q, dia_apply, dia_apply, key, smul_smul, hCc, one_smul]

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHalfEqDoubleAnnihilator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HalfDoubleAnn

theorem frames_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D), ∃ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), (∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k]) ∧ (∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T) := by
  intro D k _ _ _ _ q S T
  obtain ⟨a₀, ha₀, hne, hdiv⟩ := _root_.GlobalTheory.FinPl.LocGen.exists_gen D k q
  set c := q.pr (incA D a₀) with hc
  set G : Matrix (Fin S.rank) (Fin S.rank) k := c • (HSpace.gram S).map (fun a => q.pr (incA D a)) with hG
  have hdet : IsUnit G.det := by
    rw [hG, Matrix.det_smul, isUnit_iff_ne_zero]
    refine mul_ne_zero (pow_ne_zero _ hne) ?_
    have h := (RingHom.map_det (q.pr.comp (incA D)) (HSpace.gram S)).symm
    simp only [RingHom.mapMatrix_apply, RingHom.coe_comp] at h
    change (Matrix.map (HSpace.gram S) (⇑q.pr ∘ ⇑(incA D))).det ≠ 0
    rw [h]
    exact (map_ne_zero_iff _ (q.pr.comp (incA D)).injective).2 (GlobalTheory.FrameCont.gram_det_isUnit S).ne_zero
  let FS : Frame k S.rank (Fin S.rank) := ⟨G⁻¹, G, Matrix.nonsing_inv_mul G hdet, Matrix.mul_nonsing_inv G hdet⟩
  let FT : Frame k T.rank (Fin T.rank) := ⟨1, 1, mul_one 1, mul_one 1⟩
  exact ⟨FS, FT, _root_.GlobalTheory.LocMod.StdHomDown.down_mem_integer D k q S T c hne hdiv FS FT rfl rfl rfl, GlobalTheory.T.integral_matrix_split_place_mem_stdHomLattice D k q S T a₀ ha₀ hne FS FT rfl rfl rfl⟩

variable {D : D7}

theorem symplO_idem_left (S T : HSp D) {e : AE D} {l : WO S T} (hl : IsHalf (cA D e) l) (u : WO S T) :
    symplO S T u l = symplO S T (u.map (e * ·)) l := by
  unfold symplO hO
  congr 2
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  have h : cA D (l c b) = e * cA D (l c b) := by
    conv_lhs => rw [← hl c b]
    rw [map_mul, cA_cA]
  rw [Matrix.map_apply]
  conv_lhs => rw [h]
  ring

theorem pr_e {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.pr q.e = 1 := by
  have h := q.sec_pr 1
  rw [mul_one] at h
  rw [← h, q.pr_sec, map_one]

theorem mul_idem_of_mem {E₂ : AE D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (hsum : E₂ = ∑ PP ∈ Q, es PP) {PP : Formalism.L2.DIV.Pl D.host.E}
    (hPP : PP ∈ Q) : E₂ * es PP = es PP := by
  rw [hsum, Finset.sum_mul, Finset.sum_eq_single PP]
  · exact (hes PP hPP).1.1
  · intro PP' hPP' hne
    have hs := (hes PP hPP).1
    obtain ⟨v, ε, h1, h2⟩ := hs.2.2
    obtain ⟨q, hq, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v (es PP) ε hs h1 h2
    have hsum' : IsIdemSum (es PP') {PP'} :=
      ⟨⟨fun _ => es PP', fun P hP => by rw [Finset.mem_singleton] at hP; subst hP; exact hes _ hPP', by simp⟩,
        (hes PP' hPP').1.2.1⟩
    have := OutsideOrth.mul_eq_zero D _ (Place.ofSplitPt q) {PP'} PP (es PP')
      (by rw [Finset.mem_singleton]; exact fun h => hne h.symm) (by rw [show (Place.ofSplitPt q).e = es PP from hq]; exact hes PP hPP) hsum'
    rwa [show (Place.ofSplitPt q).e = es PP from hq] at this
  · intro h; exact absurd hPP h

end GlobalTheory.HalfDoubleAnn

namespace GlobalTheory.HalfDoubleAnn
variable {D : D7}

theorem idem_part_mem (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (E₂ e : AE D)
    (he : IsSplitIdem D e) (hEe : E₂ * e = e) (x : WO S T)
    (H : ∀ y : WO S T, IsHalf (cA D E₂) y → (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) →
      ψ (symplO S T x y) = 1) :
    x.map (e * ·) ∈ stdHom S T := by
  obtain ⟨v, ε, h1, h2⟩ := he.2.2
  obtain ⟨q, hq, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he h1 h2
  subst hq
  obtain ⟨FS, FT, hF1, hF2⟩ := frames_stdHom D _ q S T
  obtain ⟨Λ, -, h2, -, h4, -, h6⟩ := GlobalTheory.SplitSelfDual.selfDual_lattice_split D _ (Place.ofSplitPt q) ψ hψ S T (Fin T.rank) (Fin S.rank) FS FT
  have hdown : ∀ u : WO S T, (Place.ofSplitPt q).down FS FT (u.map (q.e * ·)) = (Place.ofSplitPt q).down FS FT u := by
    intro u
    unfold Place.down
    congr 2
    ext i j
    simp only [Matrix.map_apply]
    have h1 : (Place.ofSplitPt q).π q.e = 1 := pr_e q
    rw [map_mul, h1, one_mul]
  have hhalf : ∀ u : WO S T, IsHalf q.e (u.map (q.e * ·)) := fun u i j => by
    rw [Matrix.map_apply, ← mul_assoc, he.1]
  set y := x.map (q.e * ·) with hy
  by_contra hyn
  have hyup : (Place.ofSplitPt q).up FS FT ((Place.ofSplitPt q).down FS FT y) = y := Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x)
  have hnint : ¬ ∀ r s, (Place.ofSplitPt q).down FS FT y r s ∈ 𝒪[_] := fun hint => hyn (hyup ▸ hF2 _ hint)
  have hyΛ : y ∉ Λ := fun hm => hnint ((h4 _).1 (hyup.symm ▸ hm))
  obtain ⟨l, hlΛ, hlc, hl⟩ := h2 y (hhalf x) hyΛ
  have hlc' : IsHalf (cA D q.e) l := hlc
  have hlE : IsHalf (cA D E₂) l := fun i j => by
    rw [← hlc' i j, ← mul_assoc, ← map_mul, hEe]
  have key := H l hlE fun x' hx' _ => by
    rw [symplO_idem_left S T hlc' x', ← Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x'), hdown]
    exact h6 l hlΛ hlc _ (hF1 x' hx')
  rw [symplO_idem_left S T hlc' x, GlobalTheory.SplitScalar.symplO_skew] at key
  have := GlobalTheory.SplitSelfDual.psi_neg_eq_one key
  rw [neg_neg] at this
  exact hl this

theorem mem_of_ann_ann : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ x : WO S T, IsHalf E₂ x → (∀ y : WO S T, IsHalf (cA D E₂) y → (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) → ψ (symplO S T x y) = 1) → x ∈ stdHom S T := by
  intro D ψ hψ S T Q E₂ hE x hx H
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hE
  have hx' : x = ∑ PP ∈ Q, x.map (es PP * ·) := by
    ext i j
    rw [Matrix.sum_apply, ← hx i j, hsum, Finset.sum_mul]
    rfl
  rw [hx']
  exact AddSubgroup.sum_mem _ fun PP hPP =>
    idem_part_mem ψ hψ S T E₂ (es PP) (hes PP hPP).1 (mul_idem_of_mem hes hsum hPP) x H

end GlobalTheory.HalfDoubleAnn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairFrameCoordinatesIntegralAndFunctiona
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.StdPairCoord

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_lat_iff {D : D7} {p : SplitPt D k} {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank)
    (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)} (h : β.IsLat L Λ) (x : Fin S.rank → k) :
    x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  rw [h x, GlobalTheory.SeeSaw.StdOff.mem_latV_int hL]
  exact forall_congr' fun r =>
    ((p.int_iff _).trans (and_iff_right (GlobalTheory.SeeSaw.StdOff.sec_mem_idAt p _)).symm).symm

theorem hasVal_mulVec {n : ℕ} (Q : Pair k (Fin n)) (b' : Matrix (Fin n) (Fin n) k) (s : Fin n → 𝒪[k])
    (h : ∀ r, Q.HasVal (b' *ᵥ Pi.single r 1) (residue 𝒪[k] (s r))) (y : Fin n → 𝒪[k]) :
    Q.HasVal (b' *ᵥ fun r => (y r : k)) (∑ r, residue 𝒪[k] (y r) * residue 𝒪[k] (s r)) := by
  have h1 : ∀ t : Finset (Fin n), Q.HasVal (∑ r ∈ t, y r • (b' *ᵥ Pi.single r 1))
      (∑ r ∈ t, residue 𝒪[k] (y r) * residue 𝒪[k] (s r)) := fun t => by
    induction t using Finset.induction_on with
    | empty => exact ⟨by simp, by simp only [Finset.sum_empty]; exact map_zero Q.fn⟩
    | insert r t hr ih =>
      rw [Finset.sum_insert hr, Finset.sum_insert hr]
      exact ((h r).smul _).add ih
  convert h1 Finset.univ using 1
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.AdForm.StdPairCoord


open GlobalTheory.AdForm.StdPairCoord in
theorem GlobalTheory.AdForm.stdT_pair_coords : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ i (r₀ : Fin ((I.rec7 l Z).sp.X j).rank), r₀.1 + 1 = ((I.rec7 l Z).sp.X j).rank → ∀ (x : Fin ((I.rec7 l Z).sp.X j).rank → k) (a : 𝓀[k]), (Q j i).HasVal x a ↔ ∃ y : Fin ((I.rec7 l Z).sp.X j).rank → 𝒪[k], (∀ r, (y r : k) = ((β j i).b *ᵥ x) r) ∧ ∃ s : 𝒪[k], (s : k) = (p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E))) ∧ a = residue 𝒪[k] (s * y r₀) := by
  intro B X I l Z u k _ _ _ _ ι p β Q L hS j hj i r₀ hr₀ x a
  obtain ⟨-, hT⟩ := hS
  obtain ⟨hL, hT'⟩ := hT j hj
  obtain ⟨hlat, hfn⟩ := hT' i
  have hmem := mem_lat_iff hL (β j i) hlat
  have hs : ∀ r, ∃ s : 𝒪[k], (s : k) = (if r = r₀ then (p i).pr (incA (I.rec7 l Z)
      (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E))) else 0) ∧
      (Q j i).HasVal ((β j i).b' *ᵥ Pi.single r 1) (residue 𝒪[k] s) := fun r => by
    have hz : (Pi.single r 1 : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E) ∈ L j := (hL _).2 fun t => by
      rw [Pi.single_apply]
      split_ifs
      exacts [isIntegral_one, isIntegral_zero]
    obtain ⟨s, hs1, hs2⟩ := hfn _ hz r₀ hr₀
    have e : (fun r' => (p i).pr (incA (I.rec7 l Z) ((Pi.single r 1 : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E) r'))) =
        Pi.single r 1 := funext fun r' => by
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs
      · rw [map_one, map_one]
      · rw [map_zero, map_zero]
    rw [e] at hs2
    refine ⟨s, ?_, hs2⟩
    rw [hs1, Pi.single_apply]
    by_cases h : r₀ = r
    · subst h
      rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero, map_zero, map_zero]
  choose s hs using hs
  have key : ∀ y : Fin ((I.rec7 l Z).sp.X j).rank → 𝒪[k], (Q j i).HasVal ((β j i).b' *ᵥ fun r => (y r : k))
      (residue 𝒪[k] (s r₀ * y r₀)) := fun y => by
    have h1 := hasVal_mulVec (Q j i) (β j i).b' s (fun r => (hs r).2) y
    convert h1 using 1
    rw [Finset.sum_eq_single r₀ (fun r _ hr => ?_) (fun h => (h (Finset.mem_univ _)).elim), map_mul, mul_comm]
    have : s r = 0 := Subtype.ext ((hs r).1.trans (if_neg hr))
    rw [this, map_zero, mul_zero]
  constructor
  · intro h
    have hx := (hmem x).1 h.mem
    refine ⟨fun r => ⟨_, hx r⟩, fun r => rfl, s r₀, (hs r₀).1.trans (if_pos rfl), h.unique ?_⟩
    have := key fun r => ⟨_, hx r⟩
    rwa [show ((β j i).b' *ᵥ fun r => (((⟨_, hx r⟩ : 𝒪[k]) : k))) = x by
      rw [show (fun r => (((⟨_, hx r⟩ : 𝒪[k]) : k))) = (β j i).b *ᵥ x from rfl, Matrix.mulVec_mulVec, (β j i).b'b,
        Matrix.one_mulVec]] at this
  · rintro ⟨y, hy, s', hs', rfl⟩
    obtain rfl : s' = s r₀ := Subtype.ext (hs'.trans ((hs r₀).1.trans (if_pos rfl)).symm)
    have hx : x = (β j i).b' *ᵥ fun r => (y r : k) := by
      rw [show (fun r => (y r : k)) = (β j i).b *ᵥ x from funext hy, Matrix.mulVec_mulVec, (β j i).b'b, Matrix.one_mulVec]
    rw [hx]
    exact key y

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainFockVectorLevelLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem levelLaw : ∀ D : D7, LevelLaw D := by
  intro D hgap c hc k hk s s' hs hs' p hp φ
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.ChainOnto.StepVecLawBoth.vecLaw D hgap c hc k hk s s' hs hs' p hp
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.weil _ _ _ _ p.f hp.theta
      κ (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ (h1 κ hκ) φ
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.weil _ _ _ _ p.f hp.theta
      1 (one_mem _) κ (Subgroup.mem_inf.1 hκ).1 _ (h2 κ hκ) φ

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem transport_levi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (g : G D A.rank) (a : GL (Fin A.rank) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ Φ x, (omS g Φ).1 x = (χB⁻¹ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) ((B.rank : ℂ) / 2) * Φ.1 (x ⬝ a.1) := by
  intro D ψ A B χB omh hW ν 𝓨 hcov θ hθ μ hμ κ hκ omS hT lam _ g a hg Φ x
  obtain ⟨f, hf, hfΦ⟩ := ((_root_.GlobalTheory.SchSchwartzAll.schSchwartz D) ψ hW.std θ hθ A B ν 𝓨 hcov).2.1 Φ.1 Φ.2
  have hlev : κ.symm g = (dblDec A).levi a :=
    _root_.GlobalTheory.StdUnn.chart_levi D A μ hμ κ hκ (κ.symm g) a (by rw [MulEquiv.apply_symm_apply]; exact hg)
  have h1 := hT (κ.symm g) f hf Φ hfΦ.symm
  rw [MulEquiv.apply_symm_apply] at h1
  rw [h1, hlev, (_root_.GlobalTheory.Core.Rk.SchLaws.sch_laws D ψ A B χB omh hW ν 𝓨 hcov f hf).2.1 a x, hfΦ]

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommonStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  first | exact @GlobalTheory.TrueBranch.branching_true_columns | exact GlobalTheory.TrueBranch.branching_true_columns | (intros; apply GlobalTheory.TrueBranch.branching_true_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleLevelPosOddBadPrimesPrimeToLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleLevel_pos_odd_badPrimes_prime_to_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι), 0 < levC I.sel (I.tup a) (I.cst a) u ∧ Odd (levC I.sel (I.tup a) (I.cst a) u) ∧ (∀ Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) := by
  first | exact @GlobalTheory.TupLevel.levC_pos_odd_and_off | exact GlobalTheory.TupLevel.levC_pos_odd_and_off | (intros; apply GlobalTheory.TupLevel.levC_pos_odd_and_off <;> assumption)
end

