module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7} {θ : InfF D}

theorem IsKerSys.lift (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {V W : HSp D} {M : Type} [AddCommGroup M]
    [Module ℂ M] {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (hκ : IsKerSys θ V W κ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hq : IsQuot V μ 𝓕) {F : GA D V → ℂ} (hF : IsCuspForm θ V F) (f : M) :
    (∀ h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ IsAutFunSm θ W fun h => ∫ g in 𝓕, κ f g h * F g ∂μ := by
  have hD := _root_.GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay hP D θ hθ V F hF
  obtain ⟨h1, h2, ⟨N, h3⟩, h4⟩ := _root_.GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hD
  let L : M → GA D W → ℂ := fun f h => ∫ g in 𝓕, κ f g h * F g ∂μ
  have hd : ∀ f τ, ∀ X ∈ lieAt W τ, ∃ f', ∀ h,
      HasDerivAt (fun t : ℝ => L f (h * oneP θ W τ X t)) (L f' h) 0 := fun f τ X hX =>
    (hκ.derW τ X hX f).imp fun f' e => h4 τ X hX f f' e
  refine ⟨h1 f, ⟨fun γ hγ h => ?_, ?_, h2 f⟩, ?_, GlobalTheory.T.kernelLift_gelfandInvariantFinite_of_finite D θ hθ V W M κ hκ μ 𝓕 hq F hD hF.1.zfin f, ?_⟩
  · have := fun g => hκ.left f 1 (one_mem _) γ hγ g h
    simp only [one_mul] at this
    simp only [this]
  · obtain ⟨U, U', -, hU', e⟩ := hκ.level f
    refine ⟨U', hU', fun k a b h => ?_⟩
    have := fun g => e 1 (one_mem _) (one_mem _) k a b g h
    simp only [mul_one] at this
    simp only [this]
  · refine _root_.GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ W (Set.range L) ?_ ?_ _ ⟨f, rfl⟩
    · rintro _ ⟨f, rfl⟩
      exact h2 f
    · rintro _ ⟨f, rfl⟩ τ X hX
      obtain ⟨f', e⟩ := hd f τ X hX
      exact ⟨_, ⟨f', rfl⟩, e⟩
  · obtain ⟨K, hK⟩ := _root_.GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow D θ W
    refine ⟨K * N, fun l hl x => ?_⟩
    have hw : ∃ f', l.foldr (fun p φ => Rder θ W p.1 p.2 φ) (L f) = L f' := by
      induction l with
      | nil => exact ⟨f, rfl⟩
      | cons p l ih =>
        obtain ⟨f', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
        obtain ⟨f'', e'⟩ := hd f' p.1 p.2 (hl p List.mem_cons_self)
        exact ⟨f'', by rw [List.foldr_cons, e]; exact funext fun h => (e' h).deriv⟩
    obtain ⟨f', e⟩ := hw
    obtain ⟨C, hC⟩ := h3 f'
    obtain ⟨C', hC'⟩ := hK x
    refine ⟨|C| * C' ^ N, fun g hg => ?_⟩
    rw [show (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) = L f from rfl, e]
    refine (hC _).trans ?_
    rw [pow_mul, mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hC' g hg) N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _)

def matLin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A where
  toFun X := ∑ i, ∑ j, X i j • E i j
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, mul_smul]

theorem matLin_single {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (i j : Fin n) :
    matLin E (Matrix.single i j 1) = E i j := by
  simp [matLin, Matrix.single, ite_and]

theorem isKerSys_thKer (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hw : GlobalTheory.Ker.IsWeak ψ S T om) (hc : OmCont ψ S T om) :
    IsKerSys θ S T (thKer ψ S T om) := by
  have cont : ∀ f, Continuous fun p : GA D S × GA D T => thKer ψ S T om f p.1 p.2 := fun f => hc f.1 f.2 0
  have left : ∀ f, ∀ γ ∈ GQ S, ∀ δ ∈ GQ T, ∀ g h, thKer ψ S T om f (γ * g) (δ * h) = thKer ψ S T om f g h := by
    intro f γ hγ δ hδ g h
    have e : om (γ * g, δ * h) = om (γ, δ) * om (g, h) := by rw [← map_mul]; rfl
    change om (γ * g, δ * h) f.1 0 = om (g, h) f.1 0
    rw [e]
    exact hw.om_aut γ hγ δ hδ _ (hw.om_pres _ _ f.2)
  have level : ∀ f, ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧
      IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → ∀ g h,
        thKer ψ S T om f (g * k) (h * k') = thKer ψ S T om f g h := by
    intro f
    obtain ⟨U, U', a, b, e⟩ := _root_.GlobalTheory.Mem.ThetaLevel.exists_level D ψ hψ S T om hw hc f.1 f.2
    refine ⟨U, U', a, b, fun k h1 h2 k' h3 h4 g h => ?_⟩
    have e' : om (g * k, h * k') = om (g, h) * om (k, k') := by rw [← map_mul]; rfl
    change om (g * k, h * k') f.1 0 = om (g, h) f.1 0
    rw [e', mul_apply_eq_comp, e k h1 h2 k' h3 h4]
  obtain ⟨x, d, hx⟩ := _root_.GlobalTheory.Mem.Lift.WeylAction.weyl_action D ψ hψ S T om hw hc θ hθ
  have derV : ∀ τ, ∀ X ∈ lieAt S τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ X t) h) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.2 X hX).elim fun _ e => ⟨_, e f⟩
  have derW : ∀ τ, ∀ X ∈ lieAt T τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.1 X hX).elim fun _ e => ⟨_, e f⟩
  refine ⟨cont, left, level, ?_, derV, derW, fun τ => ?_⟩
  · obtain ⟨N, hN⟩ := _root_.GlobalTheory.Mem.LiftBound.om_growth D ψ hψ S T om hw θ hθ
    obtain ⟨N', hN'⟩ := _root_.GlobalTheory.Mem.LiftGrow.growth_pair D θ hθ S T N
    exact ⟨N', fun f => hN' _ (left f) (level f) fun x y =>
      (hN f.1 f.2 x y).imp fun C e a ha b hb => e a ha b hb 0⟩
  · have sT : ∀ f g, thKer ψ S T om f g ∈ SmFun θ T := fun f g => by
      refine _root_.GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ T (Set.range fun f => thKer ψ S T om f g) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_right g)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derW τ X hX f
        exact ⟨_, ⟨f', rfl⟩, e g⟩
    have sS : ∀ f h, swapKer (thKer ψ S T om) f h ∈ SmFun θ S := fun f h => by
      refine _root_.GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ S (Set.range fun f => swapKer (thKer ψ S T om) f h) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_left h)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derV τ X hX f
        exact ⟨_, ⟨f', rfl⟩, fun g => e g h⟩
    obtain ⟨g1, g2⟩ := GlobalTheory.T.glRel_of_canonicalCommutationRelations _ _ _ (x τ) (d τ) (hx τ).1
    obtain ⟨c, e1⟩ := _root_.GlobalTheory.Mem.Lift.OneSide.gelf_kernel D θ hθ T _ _ (thKer ψ S T om) sT τ (matLin fun i j => ∑ a, x τ (i, a) * d τ (j, a))
      (by simpa only [matLin_single] using g1) (hx τ).2.1
    obtain ⟨c', e2⟩ := _root_.GlobalTheory.Mem.Lift.OneSide.gelf_kernel D θ hθ S _ _ (swapKer (thKer ψ S T om)) sS τ
      (matLin fun a b => -∑ i, x τ (i, b) * d τ (i, a)) (by simpa only [matLin_single] using g2)
      fun Y hY => ((hx τ).2.2 Y hY).imp fun _ e f h g => e f g h
    simp only [matLin_single] at e1 e2
    exact ⟨_, _, e2, e1, (_root_.GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair _ _ _ (x τ) (d τ) (hx τ).1 c c').symm⟩

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem exists_thKer {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (Wf : WeilFun D ψ) {V W : HSp D}
    {χ χ' : IdC D} (ha : admitted V W χ χ') (hr : V.rank < W.rank) :
    ∃ om, GlobalTheory.Ker.IsWeak ψ V W om ∧ OmCont ψ V W om ∧
      ∀ Φ, ∃ f, ∀ g h, Wf.ker V W χ χ' Φ g h = thKer ψ V W om f g h := by
  obtain ⟨om, H, e⟩ := _root_.GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ V W χ χ' _ ha hr (Wf.core.weil V W χ χ' ha)
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  refine ⟨om, GlobalTheory.Ker.isWeak_of_datum H, H.om_cont, fun Φ => ⟨⟨fun x => Φ.1 (toTWsmall V W x), ?_⟩, fun g h => ?_⟩⟩
  · have := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
    simp only [hE] at this
    exact this
  · have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm

theorem liftAut : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAut D := by
  intro hP D θ hθ ψ hψ Wf V W χ χ' ha μ 𝓕 hq Φ F hF
  rcases lt_or_gt_of_ne ha.1 with hr | hr
  · obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha hr
    obtain ⟨f, e⟩ := e Φ
    simp only [e]
    exact (isKerSys_thKer hθ hψ hw hc).lift hP hθ hq hF f
  · have ha' : admitted W V χ' χ := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
    obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha' hr
    have hΦ := (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ V W Φ.1).2.2 ha.1 (mem_ThS.1 Φ.2)
    obtain ⟨f, e⟩ := e ⟨_, mem_ThS.2 hΦ⟩
    have e' : ∀ g h, Wf.ker V W χ χ' Φ g h = swapKer (thKer ψ W V om) f g h := fun g h =>
      (Wf.om_swap V W χ χ' ha g h Φ ⟨_, mem_ThS.2 hΦ⟩ (fun _ => rfl) 0).symm.trans (e h g)
    simp only [e']
    have hk := isKerSys_thKer hθ hψ hw hc
    have hs : IsKerSys θ V W (swapKer (thKer ψ W V om)) := by
      refine ⟨fun f => (hk.cont f).comp continuous_swap, fun f γ hγ δ hδ g g' =>
        hk.left f δ hδ γ hγ g' g, ?_, ?_, ?_, ?_, ?_⟩
      · intro f
        obtain ⟨U, U', hU, hU', hk'⟩ := hk.level f
        exact ⟨U', U, hU', hU, fun k hk1 hk2 k' hk1' hk2' g g' =>
          hk' k' hk1' hk2' k hk1 hk2 g' g⟩
      · obtain ⟨N, hN⟩ := hk.growth
        refine ⟨N, fun f => ?_⟩
        obtain ⟨C, hC⟩ := hN f
        refine ⟨C, fun g g' => ?_⟩
        have hb := hC g' g
        rw [mul_comm (height θ W g' : ℝ)] at hb
        exact hb
      · intro τ X hX f
        obtain ⟨f', hf'⟩ := hk.derW τ X hX f
        exact ⟨f', fun g g' => hf' g' g⟩
      · intro τ X hX f
        obtain ⟨f', hf'⟩ := hk.derV τ X hX f
        exact ⟨f', fun g g' => hf' g' g⟩
      · intro τ
        obtain ⟨a, b, ha, hb, hab⟩ := hk.cap τ
        exact ⟨b, a, fun k f g' => hb k f g', fun k f g => ha k f g, hab.symm⟩
    exact hs.lift hP hθ hq hF f

end GlobalTheory.Mem.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpan
section
set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

variable {ι : Type} [Fintype ι] {m : ι → ℕ}

theorem charpolyRev_neg_lie_nsum (ρ : PolyRep m) (k : ℕ) {S : Type} [CommRing S] (A : Mat m S) :
    Matrix.charpolyRev (-((ρ.nsum k).lie A)) = (Matrix.charpolyRev (-(ρ.lie A))) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, Matrix.charpolyRev]
    haveI : IsEmpty (Fin (ρ.nsum 0).M) := inferInstanceAs (IsEmpty (Fin 0))
    exact Matrix.det_isEmpty
  | succ k ih =>
    rw [pow_succ, ← ih, ← _root_.GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum]
    exact congrArg (fun L => Matrix.charpolyRev (-L)) (_root_.GlobalTheory.GoodMetric.PolyRep.lie_sum (ρ.nsum k) ρ A)

theorem chern_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (ρ : PolyRep m) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(ρ.lie A))).coeff n) ∈ Reach m n S :=
  Submodule.subset_span ⟨ρ, rfl⟩

theorem ptr_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (ρ : PolyRep m) :
    (fun A : Mat m S => ρ.ptr n A) ∈ Reach m n S := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := (Reach m 0 S).smul_mem (ρ.M : ℝ) (chern_mem_reach 0 S ρ)
    convert h using 1
    funext A
    have h0 : (Matrix.charpolyRev (-(ρ.lie A))).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    simp [PolyRep.ptr, h0, Algebra.smul_def]
  · obtain ⟨c, hc⟩ := _root_.GlobalTheory.trace_pow_eq_sum_smul_coeff_charpolyRev_pow n hn
    have h := (Reach m n S).sum_mem (t := Finset.range (n + 1))
      (fun k _ => (Reach m n S).smul_mem (c k) (chern_mem_reach n S (ρ.nsum k)))
    convert h using 1
    funext A
    rw [Finset.sum_apply, PolyRep.ptr, ← hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, charpolyRev_neg_lie_nsum]

theorem ptr_tensor (ρ σ : PolyRep m) (N : ℕ) {S : Type} [CommRing S] (A : Mat m S) :
    (ρ.tensor σ).ptr N A =
      ∑ a ∈ Finset.range (N + 1), (N.choose a : S) * ρ.ptr a A * σ.ptr (N - a) A := by
  simp only [PolyRep.ptr]
  rw [← _root_.GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add]
  exact congrArg (fun L => (L ^ N).trace) (_root_.GlobalTheory.GoodMetric.PolyRep.lie_tensor ρ σ A)

theorem ptr_mul_trProd_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)) :
    (∀ x ∈ l, 1 ≤ x.2) → ∀ r : ℕ, r + (l.map Prod.snd).sum = n → ∀ ρ : PolyRep m,
      (fun A : Mat m S => ρ.ptr r A * trProd l A) ∈ Reach m n S := by
  induction l with
  | nil =>
    intro _ r hr ρ
    have hr' : r = n := by simpa using hr
    subst hr'
    simpa [trProd] using ptr_mem_reach r S ρ
  | cons x l ih =>
    obtain ⟨τ, i⟩ := x
    intro hl r hr ρ
    have hi : 1 ≤ i := hl (τ, i) (by simp)
    have hr' : (r + i) + (l.map Prod.snd).sum = n := by
      simp only [List.map_cons, List.sum_cons] at hr
      omega
    obtain ⟨J, _, σ, c, hσ⟩ := GlobalTheory.T.exists_polyRep_combination_pure_power_trace m n S τ i hi
    have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (r + i) hr'
    have h := (Reach m n S).smul_mem (((r + i).choose r : ℝ)⁻¹)
      ((Reach m n S).sum_mem (t := Finset.univ)
        (fun j _ => (Reach m n S).smul_mem (c j) (ih' (ρ.tensor (σ j)))))
    convert h using 1
    funext A
    have hne : (((r + i).choose r : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right r i)).ne'
    have key : ∑ j, c j • (ρ.tensor (σ j)).ptr (r + i) A =
        (((r + i).choose r : ℕ) : ℝ) • (ρ.ptr r A * ((A τ) ^ i).trace) := by
      simp only [ptr_tensor, Finset.smul_sum]
      rw [Finset.sum_comm]
      have e : ∀ a ∈ Finset.range (r + i + 1),
          ∑ j, c j • ((((r + i).choose a : ℕ) : S) * ρ.ptr a A * (σ j).ptr (r + i - a) A) =
            (((r + i).choose a : ℕ) : S) * ρ.ptr a A *
              (if r + i - a = i then ((A τ) ^ i).trace else 0) := by
        intro a _
        rw [← hσ A (r + i - a) (by omega), Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
      rw [Finset.sum_congr rfl e, Finset.sum_eq_single r]
      · rw [if_pos (by omega), Algebra.smul_def, map_natCast, mul_assoc]
      · intro a ha har
        rw [Finset.mem_range] at ha
        rw [if_neg (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    simp only [Pi.smul_apply, Finset.sum_apply]
    have e2 : ∑ j, c j • ((ρ.tensor (σ j)).ptr (r + i) A * trProd l A) =
        (∑ j, c j • (ρ.tensor (σ j)).ptr (r + i) A) * trProd l A := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => (smul_mul_assoc _ _ _).symm
    rw [e2, key, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hne, one_smul]
    simp only [trProd, List.map_cons, List.prod_cons, mul_assoc]

theorem trProd_mem_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (l : List (ι × ℕ)) (hl : ∀ x ∈ l, 1 ≤ x.2) (hs : (l.map Prod.snd).sum = n) :
    (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  have h := ptr_mul_trProd_mem_reach n S l hl 0 (by simpa using hs) (PolyRep.triv m)
  convert h using 2 with A
  have : (PolyRep.triv m).ptr 0 A = 1 := by
    rw [PolyRep.ptr, pow_zero, Matrix.trace_one, Fintype.card_fin]
    exact Nat.cast_one
  rw [this, one_mul]

end GlobalTheory.GoodMetric.ChernSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationEqOfMemIff
section
open scoped Pointwise

namespace GlobalTheory.ValuationOfMemIff

theorem le_iff_of_mem_iff {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) (h : ∀ x, σ x ∈ A ↔ x ∈ A) (x y : Ω) :
    A.valuation (σ x) ≤ A.valuation (σ y) ↔ A.valuation x ≤ A.valuation y := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hσy : σ y ≠ 0 := by simpa using hy
    have key : ∀ a b : Ω, b ≠ 0 → (A.valuation a ≤ A.valuation b ↔ a / b ∈ A) := by
      intro a b hb
      rw [← A.valuation_le_one_iff, map_div₀,
        div_le_one₀ (by simpa [pos_iff_ne_zero] using hb)]
    rw [key _ _ hσy, key _ _ hy, ← map_div₀, h]

theorem not_injective_pow {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (σ : Ω ≃ₐ[E] Ω) (t : Ω) (ht : IsIntegral E t) :
    ¬ Function.Injective (fun k : ℕ => (σ ^ k) t) := by
  intro hinj

  have hsub : Set.range (fun k : ℕ => (σ ^ k) t) ⊆ (minpoly E t).rootSet Ω := by
    rintro _ ⟨k, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero ht, ?_⟩
    have := Polynomial.aeval_algHom_apply ((σ ^ k : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)
    simpa [minpoly.aeval] using this
  exact Set.infinite_range_of_injective hinj (((minpoly E t).rootSet_finite Ω).subset hsub)

theorem valuation_eq_of_mem_iff {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) (h : ∀ x, σ x ∈ A ↔ x ∈ A) (t : Ω)
    (ht : IsIntegral E t) : A.valuation (σ t) = A.valuation t := by
  have hsucc : ∀ k : ℕ, (σ ^ (k + 1)) t = σ ((σ ^ k) t) := fun k => by
    rw [pow_succ', AlgEquiv.mul_apply]

  have hlt : ∀ x y : Ω, A.valuation (σ x) < A.valuation (σ y) ↔ A.valuation x < A.valuation y := by
    intro x y
    rw [lt_iff_not_ge, lt_iff_not_ge, le_iff_of_mem_iff A σ h]
  have hinj : ∀ w : ℕ → _, (StrictMono w ∨ StrictAnti w) →
      (∀ k, w k = A.valuation ((σ ^ k) t)) → False := by
    intro w hw hwk
    apply not_injective_pow σ t ht
    intro a b hab
    have : w a = w b := by rw [hwk, hwk]; exact congrArg A.valuation hab
    rcases hw with hw | hw
    · exact hw.injective this
    · exact hw.injective this
  rcases lt_trichotomy (A.valuation (σ t)) (A.valuation t) with hc | hc | hc
  · exfalso
    refine hinj (fun k => A.valuation ((σ ^ k) t)) (Or.inr (strictAnti_nat_of_succ_lt ?_)) fun _ => rfl
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [hsucc (k + 1), hsucc k]
      rw [hsucc k] at ih
      exact (hlt _ _).2 ih
  · exact hc
  · exfalso
    refine hinj (fun k => A.valuation ((σ ^ k) t)) (Or.inl (strictMono_nat_of_lt_succ ?_)) fun _ => rfl
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [hsucc (k + 1), hsucc k]
      rw [hsucc k] at ih
      exact (hlt _ _).2 ih

theorem valuation_apply_eq : ∀ (E Ω : Type) [inst : Field E] [NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : Formalism.ConjugateSelfDual.G E Ω), Membership.mem (ReciprocityTheory.Gal.Dec A) σ → ∀ (t : Ω), Eq ((ValuationSubring.valuation A) (σ t)) ((ValuationSubring.valuation A) t) := by
  intro E Ω _ _ _ _ _ A σ hσ t
  have halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact valuation_eq_of_mem_iff A σ (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hσ) t
    (Algebra.IsIntegral.isIntegral t)

end GlobalTheory.ValuationOfMemIff
end

