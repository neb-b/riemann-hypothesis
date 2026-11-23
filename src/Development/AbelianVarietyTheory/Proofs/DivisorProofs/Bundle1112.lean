module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullO1ToProjOfIsLB
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjSpace

theorem lbIso_pull_O1_toProj_of_isLB : ∀ (R : Type) [CommRing R] (N : ℕ) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (f : X ⟶ Sp R) (s : Fin (N + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤), LBIso ((ProjSpace.O1 R N).pull (ProjSpace.toProj f s hs)) L :=
  fun _ _ _ _ _ _ f s hs => GlobalTheory.ProjSpace.lbIso_pullback_O1_toProj f s hs

end GlobalTheory.ProjSpace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfIsoOnAllReductions
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LBReductions

theorem exists_kernel_approx {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) : ∃ e : ℕ, ∀ v : Fin a → R, (∀ j, D.mulVec v j ∈ I ^ (e + 1)) →
      ∃ w : Fin a → R, D.mulVec w = 0 ∧ ∀ k, v k - w k ∈ I := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range D.mulVecLin)
  refine ⟨c, fun v hv => ?_⟩
  have h₁ : D.mulVec v ∈ I ^ (c + 1) • (⊤ : Submodule R (Fin b → R)) ⊓ LinearMap.range D.mulVecLin := by
    refine ⟨?_, v, rfl⟩
    rw [pi_eq_sum_univ (D.mulVec v)]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hv j) trivial
  rw [hc (c + 1) (Nat.le_succ c), Nat.add_sub_cancel_left, pow_one] at h₁
  have h₂ : D.mulVec v ∈ Submodule.map D.mulVecLin (I • ⊤) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right h₁
  obtain ⟨u, hu, huv⟩ := h₂
  have h₃ : ∀ k, u k ∈ I := by
    refine Submodule.smul_induction_on hu (fun r hr n _ k => I.mul_mem_right _ hr)
      fun x y hx hy k => I.add_mem (hx k) (hy k)
  refine ⟨v - u, ?_, fun k => by simpa using h₃ k⟩
  rw [Matrix.mulVec_sub, sub_eq_zero]
  exact huv.symm


open GlobalTheory.AbLaw.Seesaw in
theorem mem_basicOpen_loc₀ {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {N : LB X} (P : Perf f N) {v w : Fin P.a → R} (h : ∀ k, v k - w k ∈ I)
    {i : P.I} {x : X} (hI : I ≤ (f x).asIdeal) (hx : x ∈ X.basicOpen (loc₀ P v i)) :
    x ∈ X.basicOpen (loc₀ P w i) := by
  have hi : x ∈ P.W i := X.basicOpen_le _ hx
  rw [X.mem_basicOpen _ x hi] at hx ⊢
  by_contra hw
  have e : loc₀ P v i = loc₀ P w i + ∑ k, cst f (P.W i) (v k - w k) * P.u k i := by
    simp only [loc₀, map_sub, sub_mul, Finset.sum_sub_distrib, add_sub_cancel]
  refine (IsLocalRing.notMem_maximalIdeal.2 hx) ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_add (f := _), map_sum]
  refine Ideal.add_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hw) (Ideal.sum_mem _ fun k _ => ?_)
  rw [map_mul]
  refine Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
  exact (mem_basicOpen_cst f _ _ hi).1 ((X.mem_basicOpen _ x hi).2 hu) (hI (h k))


open GlobalTheory.AbLaw.Seesaw in
theorem triv_of_levels {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥)
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [UniversallyClosed f] {N : LB X} (hN : N.IsLB)
    (P : Perf f N) {Y : ℕ → Scheme.{0}} {b : ∀ e, Y e ⟶ X}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} (hb : ∀ e, IsPullback (b e) (q e) f (thick R I e))
    (ht : ∀ e, Triv (N.pull (b e))) : Triv N := by
  obtain ⟨e, he⟩ := exists_kernel_approx I P.D₀
  obtain ⟨v', hv', hu, -⟩ := loc_of_triv P (hb e) hN (ht e)
  choose v hv using fun k => Ideal.Quotient.mk_surjective (v' k)
  obtain rfl : Ideal.Quotient.mk (I ^ (e + 1)) ∘ v = v' := funext hv
  obtain ⟨w, hw, hvw⟩ := he v fun j => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_mulVec]
    exact congrFun hv' j
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P w i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hG : ∀ x, x ∈ G := by
    intro x
    by_contra hx
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (f x).isPrime.ne_top
    have hsp : f x ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
    obtain ⟨x', hx', hfx⟩ := hsp.mem_closed hZ ⟨x, hx, rfl⟩
    have hIm : I ≤ m := hI.trans (sInf_le ⟨bot_le, hm⟩)
    have hr : f x' ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (e + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hfx]
      exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans hIm
    obtain ⟨z, hz⟩ := hr
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hb e) x' z hz.symm
    obtain ⟨i, hi⟩ := exists_mem P (b e y)
    have h₁ := hu i
    rw [loc_comp P (hb e)] at h₁
    have h₂ := mem_of_isUnit h₁ (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx' (TopologicalSpace.Opens.mem_iSup.2 ⟨i, mem_basicOpen_loc₀ P hvw (by rw [hfx]; exact hIm) h₂⟩)
  have hid : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine GlobalTheory.AbTriv.triv_of_pull_id (triv_of_loc P hid (RingHom.id R ∘ w) ?_ fun y => ?_)
  · funext j
    rw [← RingHom.map_mulVec, hw]
    rfl
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hG y)
    refine ⟨i, ?_⟩
    rw [loc_comp P hid, ← Scheme.preimage_basicOpen]
    exact hi

theorem lbIso_of_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProjBy X.hom → GeometricallyConnected X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ M M' : LB X.left, M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b e))) → LBIso M M' := by
  intro R _ _ I hI X hs hp _ Y b hb M M' hM hM' w
  have := isProper_of_isProjBy R _ _ hp
  have hN := LB.isLB_div hM' hM
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R _ _ hs hp _ hN
  exact triv_of_levels (IsAdicComplete.le_jacobson_bot I) hN P hb fun e =>
    GlobalTheory.AlgTower.triv_chart (GlobalTheory.AlgTower.chartPullDiv M' M _) (w e)

end GlobalTheory.LBReductions
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAlternatingOfAdjacentSwapBlocks
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem perm_submonoid_eq_top_of_adj (k : ℕ) (T : Submonoid (Equiv.Perm (Fin k)))
    (h : ∀ a b : Fin k, (b : ℕ) = a + 1 → Equiv.swap a b ∈ T) : T = ⊤ := by
  cases k with
  | zero =>
    rw [eq_top_iff]
    intro x _
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; exact T.one_mem
  | succ n =>
    rw [eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h _ _ (by simp)

theorem alternating_of_adjacent_swap (ι : Type) [Fintype ι] (m : ι → ℕ)
    (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q,
      L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ) :
    L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  let S : Submonoid (∀ τ, Equiv.Perm (Fin (m τ))) :=
    { carrier := {w | ∀ Q, L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q}
      one_mem' := by
        intro Q
        have : (fun x : Root m => (⟨x.1, (1 : ∀ τ, Equiv.Perm (Fin (m τ))) x.1 x.2⟩ : Root m)) = id := by
          funext x; rfl
        rw [this, rename_id]
        simp
      mul_mem' := by
        intro v w hv hw Q
        have : (fun x : Root m => (⟨x.1, (v * w) x.1 x.2⟩ : Root m)) =
            (fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) ∘
              (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) := by
          funext x; rfl
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [this, ← rename_rename, hv, hw]
        simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, Units.val_mul, Int.cast_mul]
        ring }
  have hS : S = ⊤ := by
    have htop : (⊤ : Submonoid (∀ τ, Equiv.Perm (Fin (m τ)))) =
        Submonoid.pi Set.univ (fun τ => (⊤ : Submonoid (Equiv.Perm (Fin (m τ))))) := by
      ext x; simp [Submonoid.mem_pi]
    rw [eq_top_iff, htop, ← Submonoid.iSup_map_mulSingle, iSup_le_iff]
    intro τ
    rw [Submonoid.map_le_iff_le_comap]
    rw [perm_submonoid_eq_top_of_adj (m τ) (Submonoid.comap (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ) S) ?_]
    intro a b hab Q
    have hf : (fun x : Root m => (⟨x.1, (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) x.1 x.2⟩ : Root m)) = Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩ := by
      funext ⟨σ, c⟩
      by_cases h : σ = τ
      · subst h
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
        rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
        by_cases h1 : c = a
        · subst h1; simp
        · by_cases h2 : c = b
          · subst h2; simp [h1]
          · simp [h1, h2]
      · simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, Equiv.Perm.coe_one, id]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro e; exact h (congrArg Sigma.fst e)
        · intro e; exact h (congrArg Sigma.fst e)
    have hab' : a ≠ b := by
      intro e; subst e; omega
    have hs : (∏ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) σ)) = -1 := by
      have : ∀ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
          (Equiv.swap a b)) σ) = (Pi.mulSingle τ (Equiv.Perm.sign (Equiv.swap a b)) : ι → ℤˣ) σ := by
        intro σ
        by_cases h : σ = τ
        · subst h; simp
        · simp [Pi.mulSingle_eq_of_ne h]
      simp only [this, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
      exact Equiv.Perm.sign_swap hab'
    show L _ = _
    rw [hf, hs, hL τ a b hab Q]
    simp
  have hw : w ∈ S := by rw [hS]; trivial
  exact hw Q

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAntisymmOfDoublePointSymmMultilinear
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.MultiLevel

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial in
open Classical in
private theorem exists_fin_sum_single_eq_of_degree_eq {κ : Type} :
    ∀ (n : ℕ) (m : κ →₀ ℕ), m.degree = n → ∃ s : Fin n → κ, ∑ i, Finsupp.single (s i) 1 = m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    refine ⟨Fin.elim0, ?_⟩
    rw [Finsupp.degree_eq_zero_iff] at hm
    simp [hm]
  | succ n ih =>
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
    obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hm0
    have hle : Finsupp.single x 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hx
      omega
    have hsplit : m - Finsupp.single x 1 + Finsupp.single x 1 = m := tsub_add_cancel_of_le hle
    have hdeg : (m - Finsupp.single x 1).degree = n := by
      have h := congrArg Finsupp.degree hsplit
      rw [map_add (f := _), Finsupp.degree_single, hm] at h
      omega
    obtain ⟨s, hs⟩ := ih _ hdeg
    refine ⟨Fin.cons x s, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hs, add_comm, hsplit]


open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial in
open Classical in
theorem _root_.GlobalTheory.FlagPush.MultiLevel.antisymm_of_multilinear : ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (A : Type) [AddCommGroup A] (n : ℕ) (T : (Fin (n + 1) → A) →ₘₗ[ℤ] ℤ), (∀ (σ : Equiv.Perm (Fin (n + 1))) (y : Fin (n + 1) → A), T (y ∘ σ) = T y) → ∀ (u v : κ → A) (L : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (μ : ℤ), μ ≠ 0 → (∀ x, x ≠ a → x ≠ b → u x = v x) → u a + u b = v a + v b → (∀ s : Fin (n + 1) → κ, T (u ∘ s) = 0) → (∀ s : Fin (n + 1) → κ, T (v ∘ s) = 0) → (∀ (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ n → L P = 0) → (∀ s : Fin n → κ ⊕ κ, ((T (Fin.cons (v b - u a) (Sum.elim u v ∘ s)) : ℤ) : ℝ) = μ * L (∏ i, X (Sum.elim id id (s i)))) → ∀ Q : MvPolynomial κ ℝ, L (rename (Equiv.swap a b) Q) = - L Q := by
  intro κ a b hab A _ n T hT u v L μ hμ hoff hsum hu hv hL hmix
  set w := v b - u a with hw
  set d := u a - v a with hd
  have hcons : ∀ (x y : A) (Z : Fin n → A),
      T (Fin.cons (x - y) Z) = T (Fin.cons x Z) - T (Fin.cons y Z) := by
    intro x y Z
    simp only [← MultilinearMap.curryLeft_apply, map_sub, MultilinearMap.sub_apply]
  have hmixeq : ∀ t t' : Fin n → κ ⊕ κ, (∀ i, Sum.elim id id (t i) = Sum.elim id id (t' i)) →
      T (Fin.cons w (Sum.elim u v ∘ t)) = T (Fin.cons w (Sum.elim u v ∘ t')) := by
    intro t t' htt
    have h1 := hmix t
    have h2 := hmix t'
    have e : (∏ i, X (Sum.elim id id (t i)) : MvPolynomial κ ℝ) = ∏ i, X (Sum.elim id id (t' i)) := by
      simp only [htt]
    rw [e, ← h2] at h1
    exact_mod_cast h1
  have hZ : ∀ (t : Fin n → κ ⊕ κ) (k : Fin n),
      T (Fin.cons w (Function.update (Sum.elim u v ∘ t) k d)) = 0 := by
    intro t k
    rw [Fin.cons_update, hd, T.map_update_sub, ← Fin.cons_update, ← Fin.cons_update]
    have e1 : Function.update (Sum.elim u v ∘ t) k (u a) =
        Sum.elim u v ∘ Function.update t k (Sum.inl a) := by
      funext i
      by_cases h : i = k <;> simp [h, Function.update_apply]
    have e2 : Function.update (Sum.elim u v ∘ t) k (v a) =
        Sum.elim u v ∘ Function.update t k (Sum.inr a) := by
      funext i
      by_cases h : i = k <;> simp [h, Function.update_apply]
    rw [e1, e2, sub_eq_zero]
    apply hmixeq
    intro i
    by_cases h : i = k <;> simp [h, Function.update_apply]
  have hposition : ∀ (Y : Fin n → A) (k : Fin n),
      T (Fin.cons d (Function.update Y k w)) = T (Fin.cons w (Function.update Y k d)) := by
    intro Y k
    rw [← hT (Equiv.swap 0 k.succ) (Fin.cons d (Function.update Y k w))]
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [Equiv.swap_apply_left]
    · by_cases h : i = k
      · subst h
        simp only [Function.comp_apply, Equiv.swap_apply_right, Fin.cons_zero, Fin.cons_succ,
          Function.update_self]
      · have hne : i.succ ≠ k.succ := fun e => h (Fin.succ_injective _ e)
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) hne]
        simp [h]
  have hw' : w = u b - v a := by
    rw [hw, sub_eq_sub_iff_add_eq_add, add_comm (v b), add_comm (u b)]
    exact hsum.symm
  have hva : v a = u a - d := by rw [hd, sub_sub_cancel]
  have hua : u a = v a + d := by rw [hd, add_sub_cancel]
  have hu_side : ∀ s' : Fin n → κ, T (Fin.cons w (u ∘ s')) = T (Fin.cons d (u ∘ s')) := by
    intro s'
    have h1 : T (Fin.cons (u b) (u ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hu _
    have h2 : T (Fin.cons (u a) (u ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hu _
    rw [hw', hcons, hva, hcons, h1, h2]
    abel
  have hv_side : ∀ s' : Fin n → κ, T (Fin.cons w (v ∘ s')) = - T (Fin.cons d (v ∘ s')) := by
    intro s'
    have h1 : T (Fin.cons (v b) (v ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hv _
    have h2 : T (Fin.cons (v a) (v ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hv _
    rw [hw, hcons, h1, hua]
    simp only [← MultilinearMap.curryLeft_apply, map_add (f := _), MultilinearMap.add_apply] at h2 ⊢
    rw [h2]
    abel
  have hdiff : ∀ x : κ, ∃ ε : ℤ, u (Equiv.swap a b x) - v x = ε • w := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      refine ⟨1, ?_⟩
      rw [Equiv.swap_apply_left, one_smul, hw']
    · by_cases hxb : x = b
      · subst hxb
        refine ⟨-1, ?_⟩
        rw [Equiv.swap_apply_right, neg_smul, one_smul, hw]
        abel
      · refine ⟨0, ?_⟩
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, hoff x hxa hxb, sub_self, zero_smul]
  have hchain : ∀ s : Fin n → κ, T (Fin.cons d (v ∘ s)) = T (Fin.cons d (u ∘ Equiv.swap a b ∘ s)) := by
    intro s
    let Y : ℕ → Fin n → A := fun k i => if (i : ℕ) < k then u (Equiv.swap a b (s i)) else v (s i)
    have hY : ∀ k, ∃ t : Fin n → κ ⊕ κ, Y k = Sum.elim u v ∘ t := by
      intro k
      refine ⟨fun i => if (i : ℕ) < k then Sum.inl (Equiv.swap a b (s i)) else Sum.inr (s i), ?_⟩
      funext i
      simp only [Y, Function.comp_apply]
      split_ifs <;> rfl
    have hstep : ∀ k, T (Fin.cons d (Y k)) = T (Fin.cons d (Y 0)) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [← ih]
        by_cases hk : k < n
        · let K : Fin n := ⟨k, hk⟩
          have e1 : Y (k + 1) = Function.update (Y k) K (u (Equiv.swap a b (s K))) := by
            funext i
            by_cases hi : i = K
            · subst hi
              simp [Y, K]
            · have hik : (i : ℕ) ≠ k := fun e => hi (Fin.ext e)
              simp only [Y, Function.update_apply, hi, if_false]
              by_cases hlt : (i : ℕ) < k
              · rw [if_pos hlt, if_pos (by omega)]
              · rw [if_neg hlt, if_neg (by omega)]
          have e0 : Y k = Function.update (Y k) K (v (s K)) := by
            rw [eq_comm, Function.update_eq_self_iff]
            simp [Y, K]
          obtain ⟨ε, hε⟩ := hdiff (s K)
          obtain ⟨t, ht⟩ := hY k
          rw [← sub_eq_zero, e1]
          conv_lhs => rw [e0]
          rw [Function.update_idem, Fin.cons_update, Fin.cons_update, ← T.map_update_sub,
            ← Fin.cons_update, hε, Fin.cons_update, T.map_update_smul, ← Fin.cons_update, hposition, ht,
            hZ, smul_zero]
        · have e : Y (k + 1) = Y k := by
            funext i
            have h1 : (i : ℕ) < k := by omega
            have h2 : (i : ℕ) < k + 1 := by omega
            simp [Y, h1, h2]
          rw [e]
    have e0 : Y 0 = v ∘ s := by
      funext i
      simp [Y]
    have en : Y n = u ∘ Equiv.swap a b ∘ s := by
      funext i
      simp [Y, i.2]
    rw [← e0, ← en]
    exact (hstep n).symm
  have hkey : ∀ s : Fin n → κ,
      T (Fin.cons w (u ∘ Equiv.swap a b ∘ s)) = - T (Fin.cons w (u ∘ s)) := by
    intro s
    have hm := hmixeq (Sum.inl ∘ s) (Sum.inr ∘ s) (fun i => rfl)
    have el : Sum.elim u v ∘ (Sum.inl ∘ s) = u ∘ s := rfl
    have er : Sum.elim u v ∘ (Sum.inr ∘ s) = v ∘ s := rfl
    rw [el, er] at hm
    rw [hm, hv_side, hchain, ← hu_side (Equiv.swap a b ∘ s), neg_neg]
  have hmono : ∀ s : Fin n → κ,
      L (∏ i, X (Equiv.swap a b (s i))) = - L (∏ i, X (s i)) := by
    intro s
    have hμR : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ
    have h1 := hmix (Sum.inl ∘ s)
    have h2 := hmix (Sum.inl ∘ (Equiv.swap a b ∘ s))
    have el : Sum.elim u v ∘ (Sum.inl ∘ s) = u ∘ s := rfl
    have el' : Sum.elim u v ∘ (Sum.inl ∘ (Equiv.swap a b ∘ s)) = u ∘ Equiv.swap a b ∘ s := rfl
    rw [el] at h1
    rw [el', hkey] at h2
    simp only [Function.comp_apply, Sum.elim_inl, id] at h1 h2
    apply mul_left_cancel₀ hμR
    rw [← h2, mul_neg, ← h1]
    push_cast
    ring
  have hlin : L ∘ₗ (rename (Equiv.swap a b) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial κ ℝ).toLinearMap = -L := by
    refine (basisMonomials κ ℝ).ext fun m => ?_
    simp only [coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.neg_apply]
    by_cases hm : m.degree = n
    · obtain ⟨s, hs⟩ := exists_fin_sum_single_eq_of_degree_eq n m hm
      have e1 : monomial m (1 : ℝ) = ∏ i, X (s i) := by
        rw [← hs, monomial_sum_one]
        rfl
      rw [e1, map_prod]
      simp only [rename_X]
      exact hmono s
    · rw [hL _ _ (isHomogeneous_monomial (1 : ℝ) rfl) hm,
        hL _ _ (isHomogeneous_monomial (1 : ℝ) rfl).rename_isHomogeneous hm, neg_zero]
  intro Q
  exact LinearMap.congr_fun hlin Q

end GlobalTheory.FlagPush.MultiLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeveStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧ IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧ IsLevel (MonoidHom.id _) (globLev S (KL n)) (globLev S K') := by
  first | exact @GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | exact GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | (intros; apply GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel <;> assumption)
end

