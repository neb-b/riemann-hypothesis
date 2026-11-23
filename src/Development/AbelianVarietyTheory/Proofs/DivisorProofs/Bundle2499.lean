module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechRepresentativeChernClassTangentValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCurvatureMatrixEvenFormsEqZero
section
set_option autoImplicit false

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

noncomputable section

namespace GlobalTheory.ChernCalc.CurvClosed

theorem dbar_dbar_comm {n : ℕ} {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (v w : V n) :
    dbar (fun x => dbar u x w) z v = dbar (fun x => dbar u x v) z w := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have key (a b : V n) : dbar (fun x => dbar u x b) z a = (1 / 2 : ℂ) • (dbar (fun x => fderiv ℝ u x b) z a +
      Complex.I • dbar (fun x => fderiv ℝ u x (Complex.I • b)) z a) := by
    rw [show (fun x => dbar u x b) = fun x => (1 / 2 : ℂ) • (fderiv ℝ u x b + Complex.I • fderiv ℝ u x (Complex.I • b))
      from rfl, dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul Complex.I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul Complex.I), dbar_const_smul _ (h1 _)]
    rfl
  rw [key, key]
  simp only [dbar_apply, fderiv_fderiv_apply hu, smul_eq_mul]
  rw [hs.eq w v, hs.eq w (Complex.I • v), hs.eq (Complex.I • w) v, hs.eq (Complex.I • w) (Complex.I • v)]
  ring

theorem sum_symm {n : ℕ} {s : Fin n → Fin n → Fin n → ℂ} (hs : ∀ a c b, s a c b = s a b c) :
    ∑ c, ∑ p : Fin n × Fin n, s p.1 c p.2 • (dzb c * (-(dz p.1 * dzb p.2)) : Alt n) = 0 := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  have h := congrArg (dz a * ·) (PullClosed.sum_symm_dzb (hs a))
  simp only [Finset.mul_sum, mul_smul_comm, mul_zero] at h
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_) h
  rw [mul_neg, ← mul_assoc, ← mul_assoc, ← neg_mul, dz, dzb,
    ← eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)]

theorem curvEv_apply {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (x : V n) (i j : r) :
    (curvEv G x i j : Alt n) = ∑ p : Fin n × Fin n,
      dbar (fun y => conn G y (coordVec p.1) i j) x (coordVec p.2) • (-(dz p.1 * dzb p.2)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [curvEv, curvPoly, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, ← Algebra.smul_def, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, sym,
    Fintype.sum_prod_type, curv, Matrix.neg_apply, mdbar_apply, neg_smul, smul_neg, NegMemClass.coe_neg]

theorem dbarAt_curvEv : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n),
    MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => (curvEv G x i j : Alt n)) v = 0 := by
  intro n r _ _ G v hG hu i j
  have hθ (a : Fin n) : ContDiffAt ℝ 2 (fun x => conn G x (coordVec a) i j) v :=
    hG.conn hu (j := 2) (WithTop.coe_le_coe.2 (le_top : (2 + 1 : ℕ∞) ≤ ⊤)) (coordVec a) i j
  rw [funext fun x => curvEv_apply G x i j,
    PullClosed.dbarAt_sum_smul (ι := Fin n × Fin n)
      (f := fun p x => dbar (fun y => conn G y (coordVec p.1) i j) x (coordVec p.2)) _
      fun p => differentiableAt_dbar_apply (hθ p.1) _]
  exact sum_symm
    (s := fun a c b => dbar (fun x => dbar (fun y => conn G y (coordVec a) i j) x (coordVec b)) v (coordVec c))
    fun a c b => dbar_dbar_comm (hθ a) _ _

end GlobalTheory.ChernCalc.CurvClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarOperatorLocalCalculusComplexForms
section
set_option autoImplicit false

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm

namespace GlobalTheory.CxForm

theorem dbarAt_local_calculus : ∀ (n : ℕ) (v : V n),
    (∀ α β : V n → Alt n, α =ᶠ[𝓝 v] β → dbarAt α v = dbarAt β v) ∧
    (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n),
      (∀ j ∈ s, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α j x) S) v) →
      dbarAt (fun x => ∑ j ∈ s, α j x) v = ∑ j ∈ s, dbarAt (α j) v) ∧
    (∀ (c : ℂ) (α : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) →
      dbarAt (fun x => c • α x) v = c • dbarAt α v) ∧
    (∀ γ : Alt n, dbarAt (fun _ => γ) v = 0) ∧
    (∀ (w : V n → Ev n) (β : V n → Alt n),
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr ((w x : Alt n)) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β x) S) v) →
      dbarAt (fun x => (w x : Alt n) * β x) v =
        dbarAt (fun x => (w x : Alt n)) v * β v + (w v : Alt n) * dbarAt β v) := by
  intro n v
  obtain ⟨-, hsmul, hsum, hgerm, hconst⟩ := GlobalTheory.CxForm.delAt_dbarAt_linear_local n v
  exact ⟨fun α β h => (hgerm α β h).2, fun J s α h => (hsum J s α h).2, fun c α h => (hsmul α c h).2,
    fun γ => (hconst γ).2, fun w β hw hβ =>
      (FormMul.leibniz_of_comm n (fun x => (w x : Alt n)) β v (w v : Alt n) hw hβ).2
        fun a => Subalgebra.mem_center_iff.1 (w v).2 (dzb a)⟩

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPullback
section
set_option autoImplicit false

noncomputable section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.CechKS


set_option maxHeartbeats 1000000 in
theorem exists_isRep_eps {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (DeRham.epsRed K) i) (hA : IsAbelianScheme A)
    (L : LB A.left) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (hu : ∀ a, IsTangent (u a))
    (H : IsCechKS A A' i L u θ) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (e : (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') =
      (constMor A).isMor.pull1 (Form.cl _ ((fibMor h).isMor.pullForm ω')) +
        (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b)) :
    ∃ (J : Type) (V : J → A.left.affineOpens) (τ : J → L.ι), ⨆ j, (V j).1 = ⊤ ∧ (∀ j, (V j).1 ≤ L.U (τ j)) ∧
      IsRep (fun j ↦ (V j).1) b fun j j' P ↦ -∑ a, (∑ c, algebraMap K P.B (θ a c) * dlog L (u c) (τ j) (τ j') P) *
        algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω')) := by
  classical
  obtain ⟨J, W, c, y, hW, hc, hl, hn, hd⟩ := _root_.GlobalTheory.CechKS.cechKS_lifts K A A' i L n u θ hu H
  obtain ⟨G, hG⟩ := GlobalTheory.T.epsilonPart_deformationForm_class_eq_coboundary_of_lifts K A A' i h ω' _ b e
  let J' : Type := {p : J × A'.left.affineOpens × A.left.affineOpens // p.2.2.1 ≤ W p.1 ⊓ i ⁻¹ᵁ p.2.1.1}
  refine ⟨J', fun j ↦ j.1.2.2, fun j ↦ c j.1.1, ?_, fun j ↦ (j.2.trans inf_le_left).trans (hc _), ?_⟩
  · refine eq_top_iff.2 fun p _ ↦ ?_
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hW.ge (Set.mem_univ p))
    obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ := A'.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (i p)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hle⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ W k ⊓ i ⁻¹ᵁ U from ⟨hk, hpU⟩) (W k ⊓ i ⁻¹ᵁ U).isOpen
    exact Opens.mem_iSup.2 ⟨⟨(k, ⟨U, hU⟩, ⟨V, hV⟩), hle⟩, hpV⟩
  · have hin : ∀ (j : J') (P : GPt A), P.In j.1.2.2.1 → P.In (W j.1.1) := fun j P hP ↦
      hP.mono (j.2.trans inf_le_left)
    refine ⟨fun j P ↦ if hP : P.In (W j.1.1) then (liftVal h ω'.1 (hl _ P hP)).snd + G P else 0,
      fun j P Q φ hP ↦ ?_, fun j j' P hj hj' ↦ ?_⟩
    · simp only [dif_pos (hin j P hP), dif_pos (hin j Q (hP.map φ))]
      exact hG P Q φ _ _ _ _ (hn _ P Q φ (hin j P hP))
    · simp only [dif_pos (hin j P hj), dif_pos (hin j' P hj')]
      have hU : P.In (i ⁻¹ᵁ j.1.2.1.1) := hj.mono (j.2.trans inf_le_right)
      rw [add_sub_add_right_eq_sub, ← TrivSqZeroExt.snd_sub]
      exact _root_.GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd K A A' i h hA ω' _ j.1.2.1.2 P hU _ _ _ _ n u _ hu
        fun f ↦ hd _ _ P _ f (hin j P hj) (hin j' P hj') hU

theorem eval_eq_zero {K M I : Type*} [Field K] [AddCommGroup M] [Module K M] [Fintype I] {n : ℕ}
    (f k : Module.Dual K M) (b x : M) (c : I → M) (θ : Matrix (Fin n) (Fin n) K) (hb : Fin n → Module.Dual K M)
    (α p : Fin n → K) (t : Fin n → I → K) (e4 : ∀ a, hb a x = α a) (e5 : ∀ b, p b = ∑ k, f (c k) * t b k)
    (e1 : f (b + ∑ a, ∑ b, (θ a b * α a) • ∑ k, t b k • c k) = 0)
    (e2 : (TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (k x) : DualNumber K) +
      (DualNumber.eps : DualNumber K) • (TrivSqZeroExt.inl (f b) + TrivSqZeroExt.inr (k b) : DualNumber K) = 0) :
    (k - ∑ a, (∑ b, θ a b * p b) • hb a) x = 0 := by
  have e3 := congrArg TrivSqZeroExt.snd e2
  have e6 : ∀ b, ∑ k, t b k * f (c k) = p b := fun b ↦
    (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _).trans (e5 b).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, e6] at e1
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, e4, Finset.sum_mul]
  simp at e3
  have e7 : ∑ a, ∑ b, θ a b * p b * α a = ∑ a, ∑ b, θ a b * α a * p b :=
    Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
  rw [e7]
  linear_combination e3 - e1


set_option maxHeartbeats 1000000 in
theorem isKSValue_of_isCechKS (P : GlobalTheory.Published.AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (DeRham.epsRed K) i)
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hA' : IsAbelianScheme A')
    (hg' : SmoothOfRelativeDimension g A'.hom) (L : LB A.left) (hL : L.IsLB) (ψ : LinearMap.BilinForm K (HdR A))
    (hψ : IsPolForm (dp0 K) (𝟙 _) A L ψ) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K)
    (hu : ∀ a, IsTangent (u a)) (H : IsCechKS A A' i L u θ) (hb : Fin n → HdR A)
    (hhb : ∀ b, DeRham.IsLieImage (hb b) (u b)) {f : HdR A} (hf : f ∈ Fil A) :
    IsKSValue h f (FlagTan.lieComb (fun a ↦ ∑ b, θ a b * ψ f (hb b)) u) := by
  classical
  obtain ⟨v, k, ⟨d, hd, hdk⟩, -⟩ := IsKSValue.exists_of_isAbelianScheme P h hA' hg' hf
  obtain ⟨I, _, c, ω, hω, hch, hψf⟩ := _root_.GlobalTheory.PolForm.chern_eq_sum_cup_form P K A g hA hg L hL ψ hψ
  choose z hz using fun k ↦ H1.mk_surjective _ (c k).1
  have key : k - ∑ a, (∑ b, θ a b * ψ f (hb b)) • hb a ∈ Fil A := by
    letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
    obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA' hg' K A i h
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro x hx
    refine (Submodule.span_le (p := LinearMap.ker (k - ∑ a, (∑ b, θ a b * ψ f (hb b)) • hb a))).2
      (fun x hx ↦ ?_) hx
    obtain ⟨⟨x, hx'⟩, hx, rfl⟩ := hx
    have hx0 := hx
    change x ∈ F1 _ at hx
    rw [hodgeFiltration_eq_range] at hx
    obtain ⟨ω', rfl⟩ := hx
    obtain ⟨b, hbe⟩ := _root_.GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps P K A A' i h g hA' hg' ⟨_, hx'⟩
    obtain ⟨zb, hzb⟩ := H1.mk_surjective _ b.1
    let ω₀ := (fibMor h).isMor.pullForm ω'
    have hω₀ : Form.cl _ ω₀ ∈ primDR A := (fibMor h).pullback_mem_primitive hx'
    obtain ⟨J, V, τ, hV, hτ, hrep⟩ := exists_isRep_eps h hA L u θ hu H ω' zb (by
      rw [hzb]; exact congrArg Subtype.val hbe)
    have hch' : IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (z k)) (Form.cl _ (ω k))) := by
      simpa only [hz] using hch
    have hr := fun a ↦ _root_.GlobalTheory.CechKS.isRep_chern_tanVal K A hA L hL I z ω hch' (u a) (hu a) J V τ hτ
    have hsum := hrep.add (IsRep.sum Finset.univ fun a _ ↦ IsRep.sum Finset.univ fun b _ ↦
      (hr b).smul (θ a b * tanVal (u a) ω₀))
    have hF1 := _root_.GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero K _ _ J _ hV _ (hsum.congr (F' := 0) fun j j' Q _ _ ↦ by
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, map_mul,
        Finset.sum_mul]
      rw [neg_add_eq_zero]
      exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ mul_right_comm _ _ _)
    have hmem : b + ∑ a, ∑ b, (θ a b * tanVal (u a) ω₀) • ∑ k, tanVal (u b) (ω k) • c k ∈ PrimitiveSubmodule A := by
      refine Submodule.mem_comap.2 ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul, hz, hzb] at hF1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul]
      exact hF1
    have e1 := (Submodule.mem_dualAnnihilator _).1 hf _ hmem
    have e2 : d ((liftMor (epsDP K) h).pull ⟨_, hx'⟩) = 0 :=
      (Submodule.mem_dualAnnihilator _).1 hd _ hx0
    rw [hbe, map_add (f := _), map_smul, hdk, hdk] at e2
    have e4 : ∀ a, hb a ⟨_, hω₀⟩ = tanVal (u a) ω₀ := fun a ↦ (hhb a).2 ω₀ hω₀
    have e5 : ∀ b, ψ f (hb b) = ∑ k, f (c k) * tanVal (u b) (ω k) := fun b ↦
      (hψf f hf (hb b)).trans (Finset.sum_congr rfl fun k _ ↦ congrArg (f (c k) * ·) ((hhb b).2 (ω k) (hω k)))
    exact eval_eq_zero f k b ⟨_, hω₀⟩ c θ hb _ _ _ e4 e5 e1 e2
  refine ⟨k, ⟨d, hd, hdk⟩, ?_⟩
  have := (FlagTan.isLieImage_lieComb (fun a ↦ ∑ b, θ a b * ψ f (hb b)) hhb).add (isLieImage_one_iff.2 key)
  rwa [add_sub_cancel, _root_.mul_one] at this

end GlobalTheory.CechKS

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.CechKS.exists_const_isKSValue : GlobalTheory.CovTop.Hypotheses₂ → ∃ s : ℚ, s ≠ 0 ∧ ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A), GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A L ψ → ∀ (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → GlobalTheory.CechKS.IsCechKS A A' i L u θ → ∀ (hb : Fin n → GlobalTheory.DeRham.HdR A), (∀ b, GlobalTheory.DeRham.IsLieImage (hb b) (u b)) → ∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w : epsR K ⟶ A, IsLieComb (fun a => (s : K) * ∑ b, θ a b * ψ f (hb b)) u w → GlobalTheory.DeRham.IsKSValue h f w := by
  intro P
  refine ⟨1, one_ne_zero, ?_⟩
  intro K _ _ A _ A' _ i h g hA hg hA' hg' L hL ψ hψ n u θ hu H hb hhb f hf w hw
  obtain ⟨u', hu', rfl⟩ := hw
  have := GlobalTheory.CechKS.isKSValue_of_isCechKS P.p5 h hA hg hA' hg' L hL ψ hψ u θ hu H hb hhb hf
  convert this using 1
  rw [GlobalTheory.FlagTan.lieComb]
  congr 2
  funext a
  refine Over.OverMorphism.ext ((hu' a).trans ?_)
  simp only [Rat.cast_one, one_mul]
  rfl

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaRingRegularAtExtensionPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem Tower.map_mem_O (𝔗 : Tower X₁ act) {w : 𝔗.X₂.M.Z} {x : X₁.Ω₁} (hx : x ∈ X₁.M.O (𝔗.p w)) :
    algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ x ∈ 𝔗.X₂.M.O w := by
  obtain ⟨U, f, hz, rfl⟩ := hx
  refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, hz, ?_⟩
  refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
  rw [𝔗.p_pt]
  exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hz⟩) f

theorem Tower.stalkHom_stalkMap (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z) (x : X₁.M.Z.presheaf.stalk (𝔗.p z₂)) :
    𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) := by
  obtain ⟨U, hz, f, rfl⟩ := X₁.M.Z.presheaf.exists_germ_eq x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ hz]
  refine (RatModel.stalkHom_germ (U := 𝔗.p ⁻¹ᵁ U) hz _).trans ?_
  refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
  rw [𝔗.p_pt]
  exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hz⟩) f

theorem Tower.regAt : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective io → 𝔗.Ext ev io ev₂ → RegAt X₁ z₁ ev → RegAt 𝔗.X₂ z₂ ev₂ := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hz V V' _ _ _ _ ev io ev₂ hio hext hreg
  subst hz
  have key : ev₂.comp (𝔗.p.stalkMap z₂).hom = io.comp ev :=
    RingHom.ext fun x => hext.2 x _ (𝔗.stalkHom_stalkMap z₂ x)
  let fm : FractionRing V →+* FractionRing V' :=
    IsLocalization.map (M := nonZeroDivisors V) (S := FractionRing V) (FractionRing V') io
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hio)
  have e1 : spMap ev₂ ≫ Spec.map (𝔗.p.stalkMap z₂) = spMap io ≫ spMap ev := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg (fun φ : _ →+* V' => φ x) key
  have e2 : jK V' ≫ spMap io = spMap fm ≫ jK V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    show algebraMap V' (FractionRing V') (io x) = fm (algebraMap V (FractionRing V) x)
    exact (IsLocalization.map_eq (M := nonZeroDivisors V) (S := FractionRing V) (T := nonZeroDivisors V')
      (Q := FractionRing V') (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hio) x).symm
  have hm : jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂ ≫ 𝔗.p =
      spMap fm ≫ jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc (spMap ev₂), e1, Category.assoc,
      ← Category.assoc (jK V'), e2, Category.assoc]
  have hpt : 𝔗.p ((jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))) =
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) (closedPoint (FractionRing V)) := by
    refine (Scheme.Hom.comp_apply _ 𝔗.p _).symm.trans ?_
    rw [Category.assoc, Category.assoc, hm]
    refine (Scheme.Hom.comp_apply (spMap fm) _ _).trans (congrArg _ ?_)
    exact Spec_closedPoint
  intro a ha
  set P₂ := (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))
  haveI := 𝔗.X₂.normal.isIntegrallyClosed_stalk P₂
  haveI : IsIntegrallyClosed (𝔗.X₂.M.O P₂) := IsIntegrallyClosed.of_equiv (𝔗.X₂.M.stalkEquiv P₂)
  have hmem : ∀ c : X₁.S.R, ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) c ∈ 𝔗.X₂.M.O P₂ := fun c =>
    𝔗.map_mem_O (by rw [hpt]; exact hreg c.1 c.2)
  let q : X₁.S.R →+* 𝔗.X₂.M.O P₂ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom).codRestrict _ hmem
  obtain ⟨p, hmon, hp⟩ := 𝔗.om_fin.to_isIntegral ⟨a, ha⟩
  have hq : (algebraMap (𝔗.X₂.M.O P₂) 𝔗.X₂.Ω₁).comp q = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om :=
    RingHom.ext fun c => (𝔗.om_eq c).symm
  have hia : IsIntegral (𝔗.X₂.M.O P₂) a := by
    refine ⟨p.map q, hmon.map q, ?_⟩
    rw [Polynomial.eval₂_map, hq]
    have := Polynomial.hom_eval₂ p 𝔗.om 𝔗.X₂.S.R.val.toRingHom ⟨a, ha⟩
    rw [hp, map_zero] at this
    exact this.symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hia
  rw [← hy]
  exact y.2

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueGaloisConjugateExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.GalVal

open GlobalTheory.Points GlobalTheory.ZH

theorem valR_spMap_fromSpecStalk {X : Scheme.{0}} {x : X} {C : Type} [CommRing C] (ψ : X.presheaf.stalk x →+* C)
    {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (spMap ψ ≫ X.fromSpecStalk x) U a = ψ (X.presheaf.germ U x hU a) := by
  have h : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans (Category.comp_id _))
  refine (valR_appLE (spMap ψ) (X.fromSpecStalk x) h (le_preimage_top _) a).symm.trans ?_
  rw [e]
  exact valR_specMap (CommRingCat.ofHom ψ) _

theorem jK_spMap {V' : Type} [CommRing V'] [IsDomain V'] {X : Scheme.{0}} (z : X) (ev : X.presheaf.stalk z →+* V') :
    jK V' ≫ spMap ev = spMap ((algebraMap V' (FractionRing V')).comp ev) := by
  rw [← Spec.map_comp]; rfl

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem specializes_jK {V' : Type} [CommRing V'] [IsDomain V'] {z : M.Z} (ev : M.Z.presheaf.stalk z →+* V')
    (w : Sp (FractionRing V')) : (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) w ⤳ z := by
  have : (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) w ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

theorem val_stalkHom {V' : Type} [CommRing V'] [IsDomain V'] {z : M.Z} (ev : M.Z.presheaf.stalk z →+* V')
    (x : M.Z.presheaf.stalk z) :
    M.val (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) (M.stalkHom z x) = algebraMap V' (FractionRing V') (ev x) := by
  obtain ⟨U, hz, f, rfl⟩ := M.Z.presheaf.germ_exist x
  have hr : Set.range (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) ⊆ U := by
    rintro _ ⟨w, rfl⟩
    exact (specializes_jK ev w).mem_open U.isOpen hz
  rw [RatModel.val_eq hr (RatModel.stalkHom_germ hz f).symm]
  show valR _ U f = _
  rw [← Category.assoc, jK_spMap, valR_spMap_fromSpecStalk _ hz]
  rfl

end GlobalTheory.Poinc.Sep.GalVal

namespace GlobalTheory.Poinc.Sep.GalVal
open GlobalTheory.Points GlobalTheory.ZH
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem exists_mul_eq_stalkHom {P z : M.Z} (hs : P ⤳ z) {a : Ω} (ha : a ∈ M.O P) :
    ∃ x d : M.Z.presheaf.stalk z, a * M.stalkHom z d = M.stalkHom z x ∧
      ∃ hd : M.stalkHom z d ∈ M.O P, IsUnit (⟨_, hd⟩ : M.O P) := by
  obtain ⟨U, f, hPU, rfl⟩ := ha
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  have hPV : P ∈ V := hs.mem_open V.isOpen hzV
  obtain ⟨g, hgU, hPg⟩ := hV.exists_basicOpen_le (V := U) ⟨P, hPU⟩ hPV
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨P, hPg⟩
  have hne : (V : Set M.Z).Nonempty := ⟨z, hzV⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) hb
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, ← map_pow, RatModel.res_apply,
    RatModel.res_apply] at h1
  refine ⟨M.Z.presheaf.germ V z hzV b, M.Z.presheaf.germ V z hzV (g ^ n), ?_, ?_⟩
  · rw [RatModel.stalkHom_germ, RatModel.stalkHom_germ]
    exact h1
  · rw [RatModel.stalkHom_germ]
    refine ⟨RatModel.valF_mem_O hPV _, (RatModel.isUnit_valF_iff hPV _).2 ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    · rw [Scheme.basicOpen_pow _ _ hn]; exact hPg
end GlobalTheory.Poinc.Sep.GalVal

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Points GlobalTheory.ZH GalVal

theorem val_galois_conj : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → RegAt 𝔗.X₂ z₂ ev₂ → RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by
  intro g n F W Z i X₁ act 𝔗 z₂ V' _ _ ev₂ ev₂' σ h1 h2 hr hr' a
  have ha := hr' a a.2
  obtain ⟨x, d, hxd, hd, hu⟩ := exists_mul_eq_stalkHom (specializes_jK ev₂' _) ha
  obtain ⟨x', hx'⟩ := h2 x
  obtain ⟨d', hd'⟩ := h2 d
  have ex := h1 x x' hx'
  have ed := h1 d d' hd'
  have hsp' := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have hsp := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have e1 := RatModel.val_mul hsp' ha hd
  rw [hxd, val_stalkHom, val_stalkHom] at e1
  have hne := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ _) ⟨_, hd⟩).2 hu
  rw [val_stalkHom] at hne
  have hb := hr _ (𝔗.sR σ a).2
  have hd'' := RatModel.O_le_of_specializes (specializes_jK ev₂ (IsLocalRing.closedPoint _))
    (𝔗.X₂.M.stalkEquiv z₂ d').2
  have e2 := RatModel.val_mul hsp hb hd''
  have key : σ (a : 𝔗.X₂.Ω₁) * 𝔗.X₂.M.stalkHom z₂ d' = 𝔗.X₂.M.stalkHom z₂ x' := by
    rw [hd', hx', ← map_mul, hxd]
  rw [RatModel.coe_stalkEquiv, 𝔗.sR_eq, key, val_stalkHom, val_stalkHom, ← ed, ← ex] at e2
  rw [𝔗.sR_eq]
  exact mul_right_cancel₀ hne (e1.symm.trans e2)

end GlobalTheory.Poinc.Sep
end
end

