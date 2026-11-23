module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModerateGrowthOfFirstMinimumAndFlowBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.LieMet
  GlobalTheory.LocM
open GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_self)
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.TanPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
  (h' : IsGrpPullback G' t.G x φ)

theorem toUnit_specO_left : (toUnit (specO R R)).left = 𝟙 (Sp R) := by
  rw [Over.toUnit_left]
  exact Spec.map_id _

include h'

theorem exists_lieG {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ p : LieG G', p.1.left ≫ φ = v := by
  let p : specO R (DualNumber R) ⟶ G' :=
    Over.homMk (h'.1.lift v (specO R (DualNumber R)).hom hv.1) (h'.1.lift_snd _ _ _)
  have hp : p.left ≫ φ = v := h'.1.lift_fst _ _ _
  refine ⟨⟨p, Over.OverMorphism.ext (h'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hp⟩
  rw [Over.comp_left, Over.comp_left, toUnit_specO_left, Category.assoc, hp, Category.assoc]
  exact (epsZero_comp_of_isTanAtG t hv).trans ((unitSec_comp h').symm.trans (Category.id_comp _).symm)

theorem isTanAtG_lieG (p : LieG G') : IsTanAtG t x (p.1.left ≫ φ) := by
  constructor
  · rw [Category.assoc, h'.1.w, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w p.1)
  · rw [← Category.assoc, Hom.one_def, Over.comp_left, Over.toUnit_left]
    exact (congrArg (· ≫ φ) (sec_epsZero_comp p)).trans (unitSec_comp h')

theorem tanForm_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v) :
    tanForm t hv = omegaBase h' ≫ cotMap p.1 (epsZero_comp p) ≫ (epsIso R).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso R).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ unitSec G' ⁻¹ᵁ φ ⁻¹ᵁ W :=
    (le_preimage_of_comp (unitSec_comp h')).2 le_rfl
  have k₂ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ sec (epsZero R) ⁻¹ᵁ v ⁻¹ᵁ W :=
    (le_preimage_of_comp (epsZero_comp_of_isTanAtG t hv)).2 le_rfl
  have k₃ : v ⁻¹ᵁ W ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W := (le_preimage_of_comp hp).2 le_rfl
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero R)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl k₂
    le_rfl a).trans ?_
  refine Eq.symm ((congrArg ((cotMap p.1 (epsZero_comp p)).app _)
    (omegaBase_dUnit h' le_rfl le_rfl k₁ le_rfl a)).trans ?_)
  exact (cotMap_d p.1 (epsZero_comp p) k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE hp _ _ _ a))

theorem tanEv_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v)
    {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(omega t.G, V)) :
    tanEv t hv h s = (Scheme.ΓSpecIso (.of R)).hom
      (dualApp (tangent p) le_top ((omegaBase h').app ⊤ (pullbackSections x (omega t.G) h s))) := by
  rw [tanEv, tanForm_eq h' p hv hp]
  rfl

theorem exists_equiv_of_isGrpPullback {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} {s : Fin n → Γ(omega t.G, V)}
    (hs : VB.IsFrame s) : ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) := by
  have := t.semi
  have : QuasiSeparated G'.hom := MorphismProperty.of_isPullback h'.1 inferInstance
  let e : Fin n → Γ(omega G', ⊤) := fun b => (omegaBase h').app ⊤ (pullbackSections x (omega t.G) h (s b))
  have he : VB.IsFrame e := by
    have h₁ := ((hs.pullback x).res h).map_iso (omegaBase h')
    have h₂ (b : Fin n) : resM _ h (pullbackSections x (omega t.G) le_rfl (s b)) =
        pullbackSections x (omega t.G) h (s b) := QCoh.res_pullbackSections x _ _ _ _
    simpa only [h₂] using h₁
  have hc := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom
  let Φ : TanM x t.G →ₗ[R] (Fin n → R) :=
    { toFun := fun v b => tanEv t (isTan_tv v) h (s b)
      map_add' := fun v w => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
        have hpq : (p.1 * q.1).left ≫ φ = (tv (v + w)).left :=
          (h'.2 _ p.1 q.1 (tv v) (tv w) hp.symm hq.symm).symm
        rw [Pi.add_apply, tanEv_eq h' p _ hp, tanEv_eq h' q _ hq,
          tanEv_eq h' ⟨_, OmegaGlobal.fst_mul p q⟩ _ hpq, tangent_mul, dualApp_add, LinearMap.add_apply, map_add]
      map_smul' := fun a v => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        have ha : (dualScale a).toRingHom = epsScaleR a := by
          ext y <;> simp [dualScale, epsScaleR]
        have hpq : (ptMap (dualScale a) ≫ p.1).left ≫ φ = (tv (a • v)).left := by
          rw [Over.comp_left, Category.assoc, hp]
          exact congrArg (fun r => spMap r ≫ (tv v).left) ha
        rw [Pi.smul_apply, tanEv_eq h' p _ hp, tanEv_eq h' ⟨_, OmegaGlobal.fst_scale a p⟩ _ hpq, tangent_scale]
        simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LB.resG_self,
          Iso.inv_hom_id_apply, RingHom.id_apply] }
  refine ⟨LinearEquiv.ofBijective Φ ⟨fun v w hvw => ?_, fun c => ?_⟩, fun _ _ => rfl⟩
  · obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
    obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
    obtain rfl : p = q := tangent_injective R G' (he.dual_ext le_rfl fun b => by
      rw [resM_self]
      exact hc.1 ((tanEv_eq h' p _ hp h (s b)).symm.trans
        ((congrFun hvw b).trans (tanEv_eq h' q _ hq h (s b)))))
    exact tan_ext (hp.symm.trans hq)
  · classical
    let coord (i : Fin n) : Γ(VB.dual (omega G'), ⊤) :=
      VB.homMk (fun _ h => (he.basis h).coord i) fun _ _ h h' s => he.repr_resM h h' s i
    have hcoord (i j : Fin n) : dualApp (coord i) le_rfl (e j) = if j = i then 1 else 0 := by
      change (he.basis le_rfl).repr (e j) i = _
      rw [← resM_self (F := omega G') (h := le_rfl) (e j), ← he.basis_apply le_rfl j,
        Module.Basis.repr_self, Finsupp.single_apply]
    let l : Γ(VB.dual (omega G'), ⊤) := ∑ i, cst R (c i) • coord i
    obtain ⟨p, hp⟩ := TangentSurj.tangent_surjective R G' l
    refine ⟨tanOf (isTanAtG_lieG h' p), funext fun b => (tanEv_eq h' p _ rfl h (s b)).trans ?_⟩
    rw [hp]
    have k : dualApp l le_rfl (e b) = cst R (c b) := by
      dsimp [l]
      rw [dualApp_sum, LinearMap.sum_apply]
      simp [dualApp_smul, hcoord]
    rw [k, Iso.inv_hom_id_apply]

omit h'

theorem exists_tanM_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (n : ℕ)
    (s : Fin n → Γ(omega t.G, V)) (hs : VB.IsFrame s) :
    ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) :=
  exists_equiv_of_isGrpPullback (isGrpPullback_pullback t.G x) h hs

end GlobalTheory.LocM.TanPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicDescentPunctPolydiscLogCover
section
open GlobalTheory.ShFam.Hor

set_option autoImplicit false

namespace GlobalTheory.LogDescent

open Complex Topology

theorem continuous_logExp (n a : ℕ) : Continuous (logExp a : (Fin n → ℂ) → Fin n → ℂ) := by
  refine continuous_pi fun k => ?_
  simp only [logExp]
  split_ifs
  · exact Complex.continuous_exp.comp (continuous_apply k)
  · exact continuous_apply k

theorem mem_logDom_of_mem_ball {n a : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (s : Fin n → ℂ)
    (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) : s ∈ logDom n a := by
  intro k
  have hz := mem_ball_zero_iff.1 hs
  have hk' := (norm_le_pi_norm (logExp a s) k).trans_lt hz
  split_ifs with hk
  · simp only [logExp, hk, if_true, Complex.norm_exp] at hk'
    exact Real.exp_lt_one_iff.mp (lt_of_lt_of_le hk' hρ1)
  · simp only [logExp, hk, if_false] at hk'
    exact lt_of_lt_of_le hk' hρ1

theorem logExp_shift {n a : ℕ} (s : Fin n → ℂ) (k : Fin n) (hk : (k : ℕ) < a) (m : ℤ) :
    logExp a (s + Pi.single k ((m : ℂ) * (2 * Real.pi * Complex.I))) = logExp a s := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp only [logExp, hk, if_true, Pi.add_apply, Pi.single_eq_same]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · simp [logExp, Pi.single_eq_of_ne hj]

variable {n a : ℕ} {ρ : ℝ} {h : (Fin n → ℂ) → ℂ}

theorem inv_int (hρ1 : ρ ≤ 1)
    (hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s)
    (s : Fin n → ℂ) (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) (k : Fin n) (hk : (k : ℕ) < a) (m : ℤ) :
    h (s + Pi.single k ((m : ℂ) * (2 * Real.pi * Complex.I))) = h s := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    have ht : logExp a (s + Pi.single k (((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I))) ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
      rw [logExp_shift s k hk]; exact hs
    have := hinv _ (mem_logDom_of_mem_ball hρ1 _ ht) ht k hk
    have e : s + Pi.single k ((((m : ℤ) + 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) =
        s + Pi.single k (((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) + Pi.single k (2 * Real.pi * Complex.I) := by
      rw [add_assoc, ← Pi.single_add]; congr 2; push_cast; ring
    rw [e, this, ih]
  | pred m ih =>
    set t := s + Pi.single k ((((-(m : ℤ) - 1 : ℤ)) : ℂ) * (2 * Real.pi * Complex.I)) with htdef
    have ht : logExp a t ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
      rw [htdef, logExp_shift s k hk]; exact hs
    have := hinv _ (mem_logDom_of_mem_ball hρ1 _ ht) ht k hk
    have e : t + Pi.single k (2 * Real.pi * Complex.I) =
        s + Pi.single k ((((-(m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
      rw [htdef, add_assoc, ← Pi.single_add]; congr 2; push_cast; ring
    rw [← this, e, ih]

theorem key (hρ1 : ρ ≤ 1)
    (hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s)
    (s s' : Fin n → ℂ) (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) (he : logExp a s = logExp a s') :
    h s = h s' := by
  suffices H : ∀ S : Finset (Fin n), ∀ s s' : Fin n → ℂ, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ →
      logExp a s = logExp a s' → (∀ k ∉ S, s k = s' k) → h s = h s' from
    H Finset.univ s s' hs he (fun k hk => absurd (Finset.mem_univ k) hk)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro s s' _ _ hk
    congr 1; funext k; exact hk k (Finset.notMem_empty k)
  | insert j S hjS ih =>
    intro s s' hs he hk
    have hej := congrFun he j
    set s'' := Function.update s' j (s j) with hs''
    have he'' : logExp a s = logExp a s'' := by
      funext k
      by_cases hkj : k = j
      · subst hkj; simp [hs'', logExp]
      · have := congrFun he k
        simpa [hs'', logExp, Function.update_of_ne hkj] using this
    have h1 : h s = h s'' := ih s s'' hs he'' (fun k hk' => by
      by_cases hkj : k = j
      · subst hkj; simp [hs'']
      · rw [hs'', Function.update_of_ne hkj]
        exact hk k (by simp [hkj, hk']))
    rw [h1]
    have hs2 : logExp a s'' ∈ Metric.ball (0 : Fin n → ℂ) ρ := he'' ▸ hs
    by_cases hja : (j : ℕ) < a
    · simp only [logExp, hja, if_true] at hej
      obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hej.symm
      have e : s' = s'' + Pi.single j ((m : ℂ) * (2 * Real.pi * Complex.I)) := by
        funext k
        by_cases hkj : k = j
        · subst hkj; simp [hs'', hm]
        · simp [hs'', Function.update_of_ne hkj, Pi.single_eq_of_ne hkj]
      rw [e, inv_int hρ1 hinv s'' hs2 j hja m]
    · simp only [logExp, hja, if_false] at hej
      congr 1
      rw [hs'', hej, Function.update_eq_self]

theorem dom_mem_nhds {ρ : ℝ} (hρ1 : ρ ≤ 1) (s₀ : Fin n → ℂ)
    (hs₀ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ) :
    {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} ∈ 𝓝 s₀ := by
  have ho : IsOpen (logExp a ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) :=
    Metric.isOpen_ball.preimage (continuous_logExp n a)
  refine Filter.mem_of_superset (ho.mem_nhds hs₀) ?_
  intro s hs
  rw [Set.mem_preimage] at hs
  exact ⟨mem_logDom_of_mem_ball hρ1 s hs, hs⟩

noncomputable def logSec (a : ℕ) {n : ℕ} (z : Fin n → ℂ) : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.log (z k) else z k

noncomputable def logSecAt (a : ℕ) {n : ℕ} (z₀ z : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if (k : ℕ) < a then Complex.log (z₀ k) + Complex.log (z k / z₀ k) else z k

theorem logExp_logSec (z : Fin n → ℂ) (hz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : logExp a (logSec a z) = z := by
  funext k
  by_cases hk : (k : ℕ) < a
  · simp [logExp, logSec, hk, Complex.exp_log (hz k hk)]
  · simp [logExp, logSec, hk]

theorem logExp_logSecAt (z₀ z : Fin n → ℂ) (hz₀ : ∀ k : Fin n, (k : ℕ) < a → z₀ k ≠ 0)
    (hz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : logExp a (logSecAt a z₀ z) = z := by
  funext k
  by_cases hk : (k : ℕ) < a
  · simp only [logExp, logSecAt, hk, if_true]
    rw [Complex.exp_add, Complex.exp_log (hz₀ k hk), Complex.exp_log (div_ne_zero (hz k hk) (hz₀ k hk))]
    field_simp [hz₀ k hk]
  · simp [logExp, logSecAt, hk]

theorem differentiableAt_logSecAt (z₀ : Fin n → ℂ) (hz₀ : ∀ k : Fin n, (k : ℕ) < a → z₀ k ≠ 0) :
    DifferentiableAt ℂ (logSecAt a z₀) z₀ := by
  rw [differentiableAt_pi]
  intro k
  have hpk : DifferentiableAt ℂ (fun z : Fin n → ℂ => z k) z₀ := differentiableAt_apply k z₀
  by_cases hk : (k : ℕ) < a
  · simp only [logSecAt, hk, if_true]
    refine (differentiableAt_const _).add ?_
    have hq : DifferentiableAt ℂ (fun z : Fin n → ℂ => z k / z₀ k) z₀ := by
      simpa [div_eq_mul_inv] using hpk.mul_const (z₀ k)⁻¹
    refine hq.clog ?_
    simp [div_self (hz₀ k hk), Complex.one_mem_slitPlane]
  · simpa [logSecAt, hk] using hpk

theorem descent : ∀ (n a : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℂ), 0 < ρ → ρ ≤ 1 →
    DifferentiableOn ℂ h {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} →
    (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s) →
    ∃ H : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} ∧
      ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → h s = H (logExp a s) := by
  intro n a ρ h _ hρ1 hd hinv
  refine ⟨fun z => h (logSec a z), ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨hb₀, hn₀⟩ := hz₀

    have hU : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0 := by
      have h1 : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.isOpen_ball.mem_nhds hb₀
      refine h1.and ?_
      rw [Filter.eventually_all]
      intro k
      by_cases hk : (k : ℕ) < a
      · exact ((continuous_apply k).continuousAt.eventually_ne (hn₀ k hk)).mono fun z hz _ => hz
      · exact Filter.Eventually.of_forall fun z hk' => absurd hk' hk
    have hEq : (fun z => h (logSec a z)) =ᶠ[𝓝 z₀] fun z => h (logSecAt a z₀ z) := by
      refine hU.mono fun z ⟨hb, hn⟩ => ?_
      refine key hρ1 hinv _ _ ?_ ?_
      · rw [logExp_logSec z hn]; exact hb
      · rw [logExp_logSec z hn, logExp_logSecAt z₀ z hn₀ hn]
    have hD : {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} ∈ 𝓝 (logSecAt a z₀ z₀) := by
      refine dom_mem_nhds hρ1 _ ?_
      rw [logExp_logSecAt z₀ z₀ hn₀ hn₀]; exact hb₀
    have hh : DifferentiableAt ℂ h (logSecAt a z₀ z₀) := hd.differentiableAt hD
    have hcomp : DifferentiableAt ℂ (h ∘ logSecAt a z₀) z₀ :=
      DifferentiableAt.comp (𝕜 := ℂ) z₀ hh (differentiableAt_logSecAt z₀ hn₀)
    exact (hcomp.congr_of_eventuallyEq hEq).differentiableWithinAt
  · intro s _ hs
    have hn : ∀ k : Fin n, (k : ℕ) < a → logExp a s k ≠ 0 := fun k hk => by
      simp only [logExp, hk, if_true]; exact Complex.exp_ne_zero _
    refine key hρ1 hinv _ _ hs ?_
    rw [logExp_logSec _ hn]

end GlobalTheory.LogDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundary
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ} {y : Sp ℂ ⟶ Xo.XF c}

section Directions

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1)
  (hW : ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ))


include hP hu hy hW in
theorem dirs_exists_comb (τ : E →+* ℂ) (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∃ cf : Fin (Dw.mult τ) → ℂ, w = ∑ k, cf k • W ⟨τ, k⟩ := by
  choose v₀ h1 h2 h3 using hW
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 w
  have ht := t1 w v hv
  have he := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP w v τ hv).2 hw
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [ht.1, ← hu, Category.assoc])
  obtain ⟨cf, hcf, -⟩ := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hu k1).1 ht))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1 (he b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hcf
  have hc := (comb_iff Z.m0.toSABMap hu (fun k => h1 ⟨τ, k⟩) cf k1).2 ((comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) cf k1).1 hcf)
  exact ⟨cf, (t3 _ ht).unique hv ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _
    (fun k => W ⟨τ, k⟩) (fun k => h3 ⟨τ, k⟩) cf _).1 hc)⟩


include hP hu hy hW in
theorem dirs_span : ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨cf, h⟩ := dirs_exists_comb hP hu hy hW (e j).1 (Pi.basisFun ℂ (Fin g) j) fun k hk => by
    by_contra hne
    exact hk (by rw [Pi.basisFun_apply]; exact Pi.single_eq_of_ne (fun h => hne (by rw [h])) _)
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)


include hP hu hy hW in
theorem dirs_basis : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W :=
  ⟨basisOfTopLeSpanOfCardEqFinrank W (dirs_span hP hu hy hW) (by
    rw [Module.finrank_fin_fun, ← Fintype.card_congr e, Fintype.card_fin]), coe_basisOfTopLeSpanOfCardEqFinrank _ _ _⟩

end Directions

theorem Inner.exists_lift {x : CxPts (genStr Z) σ} (h : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  have := Z.jQ_open
  have hr : Set.range x.1 ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact not_not.1 h
  exact ⟨IsOpenImmersion.lift Z.jQ _ hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_dirs (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) :
    ∃ W : Letter Dw → Fin g → ℂ, ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ) := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  choose v₀ h1 h2 using fun z : Letter Dw => exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) (a.2.v z.1 z.2)
    (by rw [(a.2.tan z.1 z.2).1, ← hx, Category.assoc])
  choose W hW using fun z : Letter Dw => ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hu (h1 z)).2 ((tan_iff Z.m hx (h1 z)).1 (h2 z ▸ a.2.tan z.1 z.2)))).exists
  exact ⟨W, fun z => ⟨v₀ z, h1 z, h2 z, hW z⟩⟩

theorem exists_per_of_isPeriod (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) : ∃ Q, Per Fu a i Q := by
  obtain ⟨W, hW⟩ := exists_dirs hP hu hy
  obtain ⟨b, rfl⟩ := dirs_basis hP hu hy hW
  exact ⟨b.equivFun.toLinearMap.toAddMonoidHom.comp P, P, b, y, hP, hu, hy, hW, fun v => (b.sum_equivFun (P v)).symm⟩

theorem exists_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), Inner a.1 → ∃ i Q, Per Fu a i Q := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a ha
  obtain ⟨y, hy⟩ := ha.exists_lift
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact a.1.2
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  exact ⟨i, exists_per_of_isPeriod hP hu.symm hy⟩

end GlobalTheory.ShFam.Hor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsEtaleCompletionCompOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone GlobalTheory.LocM

namespace GlobalTheory.MemberEt

theorem isEtaleCompletion_comp_bijective {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion φ) : IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

theorem isEtaleCompletion_comp_openImmersion : ∀ (A X : Scheme.{0}) (g : A ⟶ X) [IsOpenImmersion g] (R : Type) [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ A), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
    IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  intro A X g _ R _ _ ξ h
  have hiso : IsIso (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))) :=
    (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
  have hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp]
  exact isEtaleCompletion_comp_bijective _ hb _ h

end GlobalTheory.MemberEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModerateGrowthOfFirstMinimumAndFlowBoundsStatement
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderate_growth_of_firstMinimum_and_flow_bounds : FlowMajSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (w : ℝ) (φ : Frame X.Ψ r → ℝ), 0 ≤ w → (∀ x ∈ X.dom, 0 ≤ φ x) → ThickBdd X φ → StepBound X w φ → ∃ C A : ℝ, ∀ x ∈ X.dom, φ x ≤ C * X.la1 x ^ (-(A * w)) := by
  first | exact @GlobalTheory.CuspDescent.moderate_of_stepBound | exact GlobalTheory.CuspDescent.moderate_of_stepBound | (intros; apply GlobalTheory.CuspDescent.moderate_of_stepBound <;> assumption)
end

