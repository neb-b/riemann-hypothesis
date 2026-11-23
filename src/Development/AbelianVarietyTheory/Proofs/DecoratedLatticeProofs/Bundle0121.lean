module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarian
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.PairKer

variable {D : D7}

noncomputable def mulRight (S : HSp D) (m : ℕ) (γ : GA D S) : Mx D m S.rank ≃+ Mx D m S.rank where
  toFun w := w * mt S γ
  invFun w := w * mt S γ⁻¹
  left_inv w := by simp only [Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
  right_inv w := by simp only [Matrix.mul_assoc, mt_inv_mul, Matrix.mul_one]
  map_add' x y := Matrix.add_mul _ _ _

theorem om_emb {ψ : AddChar (AF D.host.F) ℂ} {S T A L : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T}
    (h : IsWeilDatumO ψ S T χ χ' om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (o : OrthDec T A L) {γ : GA D A}
    (hγ : γ ∈ GQ A) (h₀ : GA D S) (h₁ : GA D A) (w : WO S L) :
    om (h₀, o.emb (γ * h₁, 1)) f (o.jB * w) = om (h₀, o.emb (h₁, 1)) f (o.jB * w) := by
  have hg : o.emb (γ, 1) ∈ GQ T := o.emb_mem_GQ hγ (GQ L).one_mem
  have a1 : o.emb (γ, 1) * o.emb (h₁, 1) = o.emb (γ * h₁, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have a2 : (o.emb (γ, 1))⁻¹ = o.emb (γ⁻¹, 1) := by
    rw [← map_inv]; exact congrArg _ (Prod.ext rfl inv_one)
  have a3 : mt T (o.emb (γ⁻¹, 1)) * (o.jB * w) = o.jB * w := by
    rw [cancel₂ (o.emb_jB _ _), mt_one, Matrix.mul_one]
  have key : ∀ (δ : GA D T) (x : WO S T), δ ∈ GQ T → mt T δ⁻¹ * x = x → ∀ k, om (h₀, δ * k) f x = om (h₀, k) f x := by
    intro δ x hδ hx k
    have e := GlobalTheory.WeilRat.om_rat_actO D ψ h.std S T _ _ _ h 1 (GQ S).one_mem δ hδ
      _ (h.om_pres (h₀, k) f hf) (mt T δ⁻¹ * x)
    have hact : actO S T 1 δ (mt T δ⁻¹ * x) = x := by
      simp only [actO, inv_one, mt_one, Matrix.mul_one, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
    rw [hact, hx] at e
    rw [show (h₀, δ * k) = (1, δ) * (h₀, k) by simp, map_mul, mul_apply_eq_comp]
    exact e
  rw [← a1]
  exact key _ _ hg (by rw [a2]; exact a3) _

theorem pairKer_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ), IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W₀ B.V₀ Ξ → Continuous (Function.uncurry (pairKer s vL Y Ξ)) ∧ (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, pairKer s vL Y Ξ (γ * h₀) h₁ = pairKer s vL Y Ξ h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, pairKer s vL Y Ξ h₀ (γ * h₁) = pairKer s vL Y Ξ h₀ h₁ := by
  intro D ψ σ J B s vL Y Ξ hY hΞ
  have hn : ∀ x, ψ x * star (ψ x) = 1 := fun x => by
    have h1 : ‖ψ x‖ = 1 := s.weil₀.std.1.2.1 x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  set K : Mx D B.L.rank J.W₀.rank → GA D J.W₀ × GA D B.A → ℂ := fun w p =>
    s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB * w) * star (Y p.1 w) with hK
  have hP : ∀ h₀ h₁, pairKer s vL Y Ξ h₀ h₁ = ∫ w in vL.𝓕, K w (h₀, h₁) ∂vL.μ := fun h₀ h₁ => by
    simp only [pairKer, contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, hK]
  have hc : Continuous (Function.uncurry K) := by
    have h1 := _root_.GlobalTheory.Unf.jointCont_all D ψ _ _ _ _ _ s.weil₀ Ξ hΞ
    have h2 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        (((q.2.1, B.o.emb (q.2.2, 1)), B.o.jB * q.1) : (GA D J.W₀ × GA D B.V₀) × WO J.W₀ B.V₀) :=
      ((continuous_fst.comp continuous_snd).prodMk (B.o.continuous_emb.comp
        ((continuous_snd.comp continuous_snd).prodMk continuous_const))).prodMk
        (continuous_const.matrix_mul continuous_fst)
    have h3 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        ((q.2.1, q.1) : GA D J.W₀ × WO J.W₀ B.L) := (continuous_fst.comp continuous_snd).prodMk continuous_fst
    exact (h1.comp h2).mul (hY.cont.comp h3).star
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ x p, K (γ + x) p = K x p := by
    rintro _ ⟨γ, rfl⟩ x p
    have e1 := (s.weil₀.om_pres (p.1, B.o.emb (p.2, 1)) Ξ hΞ).quasi (B.o.iB * γ) (B.o.jB * x)
    have e2 := hY.quasi p.1 γ x
    rw [ratW_eq, rat_mul] at e1
    rw [ratW_eq] at e2
    have e3 : symplOH J.W₀ B.V₀ (B.o.jB * rat γ) (B.o.jB * x) = symplOH J.W₀ B.L (rat γ) x := by
      rw [B.o.symplOH_resT]
      simp only [OrthDec.resT_apply, cancel₂ B.o.pA_jB, cancel₂ B.o.pB_jB, Matrix.zero_mul, Matrix.one_mul,
        symplOH_zero_left, zero_add]
    change s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB * (rat γ + x)) * star (Y p.1 (rat γ + x)) =
      s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB * x) * star (Y p.1 x)
    rw [Matrix.mul_add, e2]
    refine (congrArg (· * _) e1).trans ?_
    change ψ (-symplOH J.W₀ B.V₀ (B.o.jB * rat γ) (B.o.jB * x)) * _ * _ = _
    rw [e3, star_mul', mul_mul_mul_comm, hn, one_mul]
  obtain ⟨-, hcont, -, hinv⟩ := _root_.GlobalTheory.Unf.ParCont.parCont D _ _ vL _ K hc hper
  refine ⟨?_, fun γ hγ h₀ h₁ => ?_, fun γ hγ h₀ h₁ => ?_⟩
  · have : Function.uncurry (pairKer s vL Y Ξ) = fun p => ∫ w in vL.𝓕, K w p ∂vL.μ := funext fun p => hP p.1 p.2
    rw [this]; exact hcont
  · rw [hP, hP, ← hinv (mulRight J.W₀ _ γ) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const) ?_ (h₀, h₁)]
    · congr 1; funext w
      have e := GlobalTheory.WeilRat.om_rat_actO D ψ s.weil₀.std J.W₀ B.V₀ _ _ _ s.weil₀
        γ hγ 1 (GQ B.V₀).one_mem _ (s.weil₀.om_pres (h₀, B.o.emb (h₁, 1)) Ξ hΞ)
        (B.o.jB * (w * mt J.W₀ γ))
      have hact : actO J.W₀ B.V₀ γ 1 (B.o.jB * (w * mt J.W₀ γ)) = B.o.jB * w := by
        simp only [actO, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
      rw [hact, ← mul_apply_eq_comp, ← map_mul, Prod.mk_mul_mk, one_mul] at e
      change s.om₀ (γ * h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB * w) * star (Y (γ * h₀) w) =
        s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB * (w * mt J.W₀ γ)) * star (Y h₀ (w * mt J.W₀ γ))
      rw [e, hY.left γ hγ]
    · intro x
      refine ⟨fun h => ?_, fun h => ratMx_mul h ((mem_GQ_iff _ _).1 hγ)⟩
      rw [← (mulRight J.W₀ _ γ).symm_apply_apply x]
      exact ratMx_mul h ((mem_GQ_iff _ _).1 (inv_mem hγ))
  · rw [hP, hP]
    congr 1; funext w
    have e := om_emb s.weil₀ hΞ B.o hγ h₀ h₁ w
    change s.om₀ (h₀, B.o.emb (γ * h₁, 1)) Ξ (B.o.jB * w) * star (Y h₀ w) =
      s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB * w) * star (Y h₀ w)
    rw [e]

end GlobalTheory.PairKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PoincareSeriesCompactSupportThetaLaw
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.PoincareLaw

variable {D : D7}

theorem ratW_inj (A T : HSp D) : Function.Injective (ratW T A) :=
  fun _ _ h => Matrix.map_injective GlobalTheory.MixModel.incA_injective h

theorem ratW_sub (A T : HSp D) (γ γ₀ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) :
    ratW T A (γ - γ₀) = ratW T A γ - ratW T A γ₀ := by
  ext i j
  simp [ratW, map_sub]

theorem finite_ratW_mem (A T : HSp D) (K : Set (WO A T)) (hK : IsCompact K) :
    {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, hsc, ht2, hdisc, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T A
  haveI : T1Space (WA T A) := @T2Space.t1Space _ _ ht2
  have hcl : IsClosed (ratL T A : Set (WA T A)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratL T A → WA T A) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (ratW_inj A T).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨ratW T A γ, γ, rfl⟩, hγ, rfl⟩

theorem symplOH_neg_left (A T : HSp D) (y z : WO A T) : symplOH A T (-y) z = -symplOH A T y z := by
  have hadd := (GlobalTheory.OrientedFormLaws.symplOH_laws D A T).1
  have h0 : symplOH A T 0 z = 0 := by
    have := hadd 0 0 z
    rw [add_zero] at this
    exact left_eq_add.1 this
  have := hadd y (-y) z
  rw [add_neg_cancel, h0] at this
  exact (eq_neg_of_add_eq_zero_right this.symm)

theorem poincare_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (h : WO A T → ℂ), Continuous h → HasCompactSupport h → (∀ u, {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | h (ratW T A γ + u) ≠ 0}.Finite) ∧ Continuous (fun u => ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u)) ∧ ∀ (γ₀ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), (∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) (ratW T A γ₀ + u)) * h (ratW T A γ + (ratW T A γ₀ + u))) = ψ (-(symplOH A T (ratW T A γ₀) u)) * ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u) := by
  intro D ψ hψ A T h hc hs
  obtain ⟨hg, hlc, -, -, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T A
  haveI : IsTopologicalAddGroup (WO A T) := hg
  haveI : LocallyCompactSpace (WO A T) := hlc
  haveI : ContinuousSub (WO A T) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg
  have laws := GlobalTheory.OrientedFormLaws.symplOH_laws D A T

  have vanish : ∀ (U : Set (WO A T)) (u : WO A T), u ∈ U → ∀ γ,
      γ ∉ {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ (fun p : WO A T × WO A T => p.1 - p.2) '' (tsupport h ×ˢ U)} →
      h (ratW T A γ + u) = 0 := by
    intro U u hu γ hγ
    by_contra hne
    exact hγ ⟨(ratW T A γ + u, u), ⟨subset_tsupport h hne, hu⟩, add_sub_cancel_right _ _⟩
  refine ⟨fun u => ?_, ?_, fun γ₀ u => ?_⟩
  · refine (finite_ratW_mem A T _ ((hs.isCompact.prod (isCompact_singleton (x := u))).image continuous_sub)).subset fun γ hγ => ?_
    by_contra hn
    exact hγ (vanish {u} u rfl γ hn)
  · refine continuous_iff_continuousAt.2 fun u₀ => ?_
    obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds u₀
    have hF := finite_ratW_mem A T _ ((hs.isCompact.prod hU).image continuous_sub)
    have hcont : Continuous fun u => ∑ γ ∈ hF.toFinset, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u) :=
      continuous_finsetSum _ fun γ _ =>
        (hψ.1.1.comp (laws.2.2.2.2.1.comp (continuous_const.prodMk continuous_id))).mul
          (hc.comp (continuous_const_add (ratW T A γ)))
    refine hcont.continuousAt.congr (Filter.eventually_of_mem hUn fun u hu => ?_)
    refine (tsum_eq_sum fun γ hγ => ?_).symm
    rw [vanish U u hu γ (fun h' => hγ (hF.mem_toFinset.2 h')), mul_zero]
  · rw [← (Equiv.subRight γ₀).tsum_eq, ← tsum_mul_left]
    congr 1
    funext γ
    change ψ (symplOH A T (ratW T A (γ - γ₀)) (ratW T A γ₀ + u)) *
      h (ratW T A (γ - γ₀) + (ratW T A γ₀ + u)) = _
    rw [ratW_sub]
    have e1 : ratW T A γ - ratW T A γ₀ + (ratW T A γ₀ + u) = ratW T A γ + u := by abel
    have e2 : symplOH A T (ratW T A γ - ratW T A γ₀) (ratW T A γ₀ + u) =
        symplOH A T (ratW T A γ) (ratW T A γ₀) + symplOH A T (ratW T A γ) u +
          -(symplOH A T (ratW T A γ₀) u) := by
      rw [sub_eq_add_neg, laws.1, laws.2.1, laws.2.1, symplOH_neg_left, symplOH_neg_left, laws.2.2.1]
      ring
    obtain ⟨c, hc'⟩ := laws.2.2.2.2.2.1 (ratW T A γ) ⟨γ, rfl⟩ (ratW T A γ₀) ⟨γ₀, rfl⟩
    rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hc', hψ.1.2.2.1 c]
    ring

end GlobalTheory.PoincareLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightDerivativeSmoothCuspidalSameLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspStab

theorem rder_stab : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ (A : ℕ) (φ : GA D V → ℂ), IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) → SmoothW θ V φ → (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) → IsCuspFun V φ → IsAutFun V (Rder θ V τ X φ) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g) ∧ SmoothW θ V (Rder θ V τ X φ) ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) (Rder θ V τ X φ))) ∧ IsCuspFun V (Rder θ V τ X φ) := by
  intro D θ hθ V U τ X hX A φ ha hU hs hg hc
  have hs' : φ ∈ SmFun θ V := hs
  have inv : ∀ k, k ∈ GfC V → (∀ g, φ (g * k) = φ g) → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g := by
    intro k hk e g
    have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hk τ X φ) g
    rw [show rTr V k φ = φ from funext e] at this
    exact this.symm
  have hcont : Continuous (Rder θ V τ X φ) := by
    refine GlobalTheory.Size.continuous_Rder_of_growth hθ hs' ha.cont hX (A := A) ?_
    simpa using hg [(τ, X), (τ, X)] (by simp [hX])
  have ha' : IsAutFun V (Rder θ V τ X φ) :=
    { left := fun γ hγ => GlobalTheory.Mem.Lift.Rder_left (ha.left γ hγ) τ X
      level := by
        obtain ⟨U₀, hU₀, e⟩ := ha.level
        exact ⟨U₀, hU₀, fun k hk hf => inv k hf (e k hk hf)⟩
      cont := hcont }
  refine ⟨ha', fun k hk hf => inv k hf (hU k hk hf), Rder_mem hs' hX, fun l hl => ?_, ?_⟩
  · have := hg (l ++ [(τ, X)]) (by
      intro p hp
      rcases List.mem_append.1 hp with h | h
      · exact hl p h
      · rw [List.mem_singleton.1 h]; exact hX)
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this
  · refine (isCuspFun_iff ha'.left).2 fun W hW => funext fun x => ?_
    have h0 : constTermOn (GQ V) (NA (.single hW)) φ = 0 := (isCuspFun_iff ha.left).1 hc W hW
    have := GlobalTheory.CuspLie.hasDerivAt_constTermOn (cocompact_single hW) ha.left ha.cont ha'.left ha'.cont
      (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
      (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder hs' hX)) x
    rw [h0, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at this
    exact this.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

end GlobalTheory.CuspStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
section
noncomputable section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix

namespace GlobalTheory.FinPl.SBFacts

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem charInd_mem (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) : charInd χ Q ∈ SB (n → k) := by
  have : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have hK : IsCompact (Q.lat : Set (n → k)) := GlobalTheory.FinPl.Comm.isCompact_lat Q.lat
  refine ⟨?_, HasCompactSupport.intro hK fun y hy => ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun y => ?_
    by_cases hy : y ∈ Q.lat
    · refine ⟨(fun z => z - y) ⁻¹' (Q.ker : Set (n → k)), (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.isOpen_lat Q.ker).preimage (by fun_prop),
        by simp [Q.ker.zero_mem], fun z hz => ?_⟩
      have hw : Q.HasVal (z - y) 0 := Pair.mem_ker.1 hz
      have hz' : Q.HasVal z (Q.ev y) := by
        simpa using hw.add (Pair.hasVal_ev hy)
      have hzl : z ∈ Q.lat := hz'.mem
      simp only [charInd, vecInd, ite_eq_left hzl, ite_eq_left hy, hz'.ev_eq]
    · refine ⟨(Q.lat : Set (n → k))ᶜ, hK.isClosed.isOpen_compl, hy, fun z hz => ?_⟩
      have hz' : z ∉ Q.lat := hz
      simp only [charInd, vecInd, ite_eq_right hz', ite_eq_right hy, mul_zero]
  · have hy' : y ∉ Q.lat := hy
    simp only [charInd, vecInd, ite_eq_right hy', mul_zero]

end GlobalTheory.FinPl.SBFacts

theorem GlobalTheory.FinPl.sb_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'],
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) →
      GlobalTheory.FinPl.tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧
    (∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsFullLattice k → GlobalTheory.FinPl.vecInd Λ ∈ SB (n → k)) ∧
    ∀ (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n), GlobalTheory.FinPl.charInd χ Q ∈ SB (n → k) := by
  intro k _ _ _ _ n n' _ _ _ _
  refine ⟨fun Ψ a hΨ ha => GlobalTheory.FinPl.Comm.tensCol_mem hΨ ha, fun Λ hΛ => ?_,
    fun χ Q => GlobalTheory.FinPl.SBFacts.charInd_mem χ Q⟩
  have := hΛ
  exact GlobalTheory.FinPl.Comm.vecInd_mem Λ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.SDStable

variable {D : D7}

theorem hermAt_smul_left (S : HSp D) (a : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (a • y) x = a * hermAt S y x := by
  unfold hermAt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem mul_mem_intAt {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem smul_mem : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ →
    ∀ a ∈ intAt D (· = v), ∀ y ∈ Λ, a • y ∈ Λ := by
  intro D S v Λ hΛ a ha y hy
  have hsupp : ∀ i, (a • y) i ∈ idAt D (· = v) := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (hΛ.1 y hy i)
  refine (hΛ.2.2 (a • y) hsupp).2 fun x hx => ?_
  rw [hermAt_smul_left]
  exact mul_mem_intAt ha ((hΛ.2.2 y (hΛ.1 y hy)).1 hy x hx)

end GlobalTheory.IwaPlace.SDStable

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewHermitianTracePairingStandardCharacterPerfecStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitian_tracePairing_standardCharacter_perfect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (M : Matrix (Fin ρ) (Fin ρ) D.host.E), Mᴴ = -M → (∀ c : skewA D ρ, ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((rat M : Mx D ρ ρ) ⬝ c.1).trace) = 1) → M = 0 := by
  first | exact @GlobalTheory.SkewPairing.skew_perfect | exact GlobalTheory.SkewPairing.skew_perfect | (intros; apply GlobalTheory.SkewPairing.skew_perfect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SnocColumnsMovedByUpperUnitriangularIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snocColumns_moved_by_upperUnitriangular_iff : ∀ (R : Type) [CommRing R] (n σ : ℕ) (M : Matrix (Fin n) (Fin σ) R) (w : Fin n → R) (Y : Matrix (Fin n) (Fin n) R), (∃ U ∈ GlobalTheory.UniIndexPrime.uniSub (σ + 1) R, Y * Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) = Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) * (U : Matrix (Fin (σ + 1)) (Fin (σ + 1)) R)) ↔ ∃ u ∈ GlobalTheory.UniIndexPrime.uniSub σ R, ∃ v : Fin σ → R, Y * M = M * (u : Matrix (Fin σ) (Fin σ) R) ∧ Y *ᵥ w = w + M *ᵥ v := by
  first | exact @GlobalTheory.BlockUni.snoc_uni_iff | exact GlobalTheory.BlockUni.snoc_uni_iff | (intros; apply GlobalTheory.BlockUni.snoc_uni_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLoc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeckeSplitAll

def splitLoc (D : D7) : Set (AE D)ˣ :=
  {x | ∃ e, IsSplitIdem D e ∧ (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1}

def modSet (D : D7) (N : ℕ) : Set (AE D)ˣ :=
  {x | infPart D (x : AE D) = 1 ∧
    (∃ r ∈ intAE D, finPart D (x : AE D) - 1 = (N : Af D.host.F ⊗[D.host.F] D.host.E) * r) ∧
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D}

def grpH (D : D7) (N : ℕ) : Subgroup (AE D)ˣ :=
  Subgroup.closure (Set.range (Units.map (incA D).toMonoidHom) ∪ splitLoc D ∪ modSet D N)

end GlobalTheory.HeckeSplitAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl

theorem SplitPt.sec_mem_idAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have he : p.sec a = p.e * p.sec a := by
    have := p.sec_pr (p.sec a)
    rwa [p.pr_sec] at this
  rw [(placeIdem_acts D p.v ε hε).1, ← hsum, he, ← mul_assoc, add_mul, p.split.1,
    mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]

theorem mt_mul_mt_inv {D : D7} (S : HSp D) (γ : GA D S) : Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem Frame.isLat_of_isLatMoved : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n]
    (β : Frame p S n) (γ : GA D S) (L M : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    Moves S γ L M (· = p.v) → β.IsLatMoved γ L Λ → β.IsLat M Λ := by
  intro D k _ _ _ _ p S n _ _ β γ L M Λ hM hL x
  have hsupp : ∀ i, (Formalism.L2.Theta.mt S γ⁻¹ *ᵥ fun i => p.sec ((β.b *ᵥ x) i)) i ∈ idAt D (· = p.v) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (p.sec_mem_idAt _)
  rw [hL x, hM _ hsupp, Matrix.mulVec_mulVec, mt_mul_mt_inv, Matrix.one_mulVec]

end GlobalTheory.FinPl
end
end

