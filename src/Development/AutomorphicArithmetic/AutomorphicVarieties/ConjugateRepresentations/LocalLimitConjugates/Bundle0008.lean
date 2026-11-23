module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.KugaSm
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem kugaSm_map {E : Type} [Field E] {a n : ℕ} (e : Fin n → Herm E a) {A A' : Type} [Ring A] [Module ℝ A]
    [Ring A'] [Module ℝ A'] (f : A →+* A') (L : Lie E a →ₗ[ℝ] A) (L' : Lie E a →ₗ[ℝ] A') (h : ∀ X, L' X = f (L X)) :
    cas L' e = f (cas L e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cas, map_sum, map_sub, map_mul, h]

private theorem kugaSm_A {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r : ℝ) :
    cas (shift (smA Ξ) r) e = (cas (shift (lie E a) r) e).rTensor (Fin Ξ.d → ℂ) := by
  refine kugaSm_map e (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)).toRingHom _ _ fun X => ?_
  change _ = (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)) _
  rw [shift_apply, shift_apply, map_add (f := _), ← algebraMap_smul ℂ (r * ell E a X) (1 : Module.End ℂ (Sm E a)), map_smul, map_one,
    algebraMap_smul]
  rfl

private theorem kugaSm_B {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r c : ℝ) (h : HasCas Ξ r c e) :
    cas (shift (smB Ξ) (-r)) e = (c : ℂ) • 1 := by
  let f : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
    (Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) (Sm E a)).comp
      (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have h1 : cas (shift (smB Ξ) (-r)) e = f (cas (shift Ξ.dmat (-r)) e) := by
    refine kugaSm_map e f.toRingHom _ _ fun X => ?_
    change _ = f _
    rw [shift_apply, shift_apply, map_add (f := _), ← algebraMap_smul ℂ (-r * ell E a X) (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), map_smul,
      map_one, algebraMap_smul, smB_apply]
    rfl
  rw [h1, show cas (shift Ξ.dmat (-r)) e = _ from h, map_smul, map_one]

theorem UpperTheory.V.Cj.H.kugaSm :
    UpperTheory.V.Cj.H.KugaSm := by
  intro E _ _ _ a n e he Ξ r c hc
  obtain ⟨a1, b1, hab, -, -, hinf⟩ := smAB E a Ξ
  obtain ⟨-, -, -, l4⟩ := ellFacts E a
  have hA := l4 _ _ r a1
  have hB := l4 _ _ (-r) b1
  have hsum : shift (smA Ξ) r + shift (smB Ξ) (-r) = smLie Ξ := by
    rw [shift_add_shift]
    exact LinearMap.ext fun X => add_sub_cancel (smA Ξ X) (smLie Ξ X)
  have hcom : ∀ X Y, Commute (shift (smA Ξ) r X) (shift (smB Ξ) (-r) Y) := fun X Y => by
    rw [shift_apply, shift_apply]
    exact ((hab X Y).add_right ((Commute.one_right _).smul_right _)).add_left ((Commute.one_left _).smul_left _)
  have hcas : cas (shift (smB Ξ) (-r)) e - cas (shift (smA Ξ) r) e = -(casA r c e).rTensor (Fin Ξ.d → ℂ) := by
    rw [kugaSm_A, kugaSm_B e Ξ r c hc, casA, LinearMap.rTensor_sub, LinearMap.rTensor_smul, neg_sub, Module.End.one_eq_id,
      Module.End.one_eq_id, LinearMap.rTensor_id]
  have hdel : ∀ (q : ℕ) (X : Fin q → Herm E a),
      del (shift (smB Ξ) (-r) - shift (smA Ξ) r) e (0 : Co Ξ (q + 1)) X = 0 := fun q X => by
    simp [del_apply]
  refine ⟨fun ω hω hd => ?_, fun q ω hω hd => ?_⟩
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaZero E a n e _ _ _ hcom ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply] at h
    rw [app_apply]
    exact neg_eq_zero.1 h.symm
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaSucc E a n e he _ _ _ hA hB hcom q ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply, add_zero] at h
    rw [app_apply, AlternatingMap.neg_apply]
    exact (neg_eq_iff_eq_neg.1 h.symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OrbConv
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem norm_tsum_le_of_encard {I : Type} (u : I → ℂ) (S : Set I) (N : ℕ) (hS : S.encard ≤ N) (M : ℝ)
    (hM : ∀ i, ‖u i‖ ≤ M) (hM0 : 0 ≤ M) (h0 : ∀ i ∉ S, u i = 0) : ‖∑' i, u i‖ ≤ N * M := by
  have hfin : S.Finite := Set.finite_of_encard_le_coe hS
  rw [tsum_eq_sum (s := hfin.toFinset) fun i hi => h0 i (by simpa using hi)]
  have hcard : hfin.toFinset.card ≤ N := by
    rw [hfin.encard_eq_coe_toFinset_card] at hS
    exact_mod_cast hS
  refine (norm_sum_le_of_le _ fun i _ => hM i).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM0

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.orbConv :
    UpperTheory.V.Cj.H.OrbConv := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f f' hf hc hf' hc'
  have hi : Integrable f μ := hf.integrable_of_hasCompactSupport hc
  have hq := GlobalTheory.AutomorphicL2KernelIntegral.integrable_descend_orbitSum (Γ := Γ) hi
  obtain ⟨N, hN⟩ := (locInt G Γ μ).2 (tsupport f) hc
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hb : ∀ g, ‖GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f g‖ ≤ N * M := fun g =>
    norm_tsum_le_of_encard _ _ N (hN g) M (fun _ => hM _) hM0 fun γ h => image_eq_zero_of_notMem_tsupport h
  have h : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f) := by
    refine ⟨GlobalTheory.AutomorphicL2Unitary.leftInv_orbitSum f, (memLp_two_iff_integrable_sq_norm hq.1).2 ?_⟩
    refine (hq.norm.const_mul (N * M)).mono' (hq.1.norm.pow 2) (Eventually.of_forall fun q => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
  refine ⟨h, funext fun x => ?_⟩
  have hae : ∀ᵐ g ∂μ, GlobalTheory.AutomorphicL2Unitary.lift Γ h.toL2 g = GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f g := by
    filter_upwards [GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.1 h.coeFn_toL2] with g hg
    exact hg.trans (h.1.descend_mk g)
  have hk : Continuous fun y : G => f' (y⁻¹ * x) := by fun_prop
  have hkc : HasCompactSupport fun y : G => f' (y⁻¹ * x) :=
    hc'.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
  have hint : ∀ γ : Γ, Integrable (fun y => f (γ * y) * f' (y⁻¹ * x)) μ := fun γ =>
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hkc.mul_left
  have hfin : {γ : Γ | (γ : G) ∈ tsupport f * (tsupport fun y : G => f' (y⁻¹ * x))⁻¹}.Finite :=
    GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (IsCompact.mul hc (IsCompact.inv hkc))
  have hsum : Summable fun γ : Γ => ∫ y, ‖f (γ * y) * f' (y⁻¹ * x)‖ ∂μ := by
    refine summable_of_hasFiniteSupport (hfin.subset fun γ hγ => ?_)
    by_contra hn
    refine hγ ?_
    have : ∀ y, f (γ * y) * f' (y⁻¹ * x) = 0 := fun y => by
      by_contra hy
      exact hn ⟨_, subset_tsupport f (left_ne_zero_of_mul hy), y⁻¹,
        Set.inv_mem_inv.2 (subset_tsupport _ (right_ne_zero_of_mul hy)), by simp⟩
    simp [this]
  have e1 : ∀ γ : Γ, GlobalTheory.AutomorphicL2Unitary.conv μ f f' (γ * x) = ∫ y, f (γ * y) * f' (y⁻¹ * x) ∂μ := fun γ => by
    unfold GlobalTheory.AutomorphicL2Unitary.conv
    rw [← integral_mul_left_eq_self _ (γ : G)]
    simp [mul_assoc]
  unfold cv
  rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, tsum_congr e1, integral_tsum_of_summable_integral_norm hint hsum]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hy, tsum_mul_right, GlobalTheory.AutomorphicL2Unitary.orbitSum]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PoinOp
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

private theorem tr_tr (q : ℕ) (γ δ : Γ) (h : γ * δ = 1) (m : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :
    G.tr q γ (G.tr q δ m) = m := by
  have hδ : δ = γ⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hδ
  ext v
  rw [Geo.tr_apply, Geo.tr_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one,
    Matrix.one_mulVec]
  have hv : (fun i => (G.ρ γ⁻¹⁻¹) ((G.ρ γ⁻¹) (v i))) = v := by
    funext i
    exact Geo.ρ_inv_apply G γ⁻¹ (v i)
  rw [hv]

private theorem tr_coneOp (q : ℕ) (γ : Γ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) (p x : V) :
    G.tr q γ (coneOp p w (G.ρ γ⁻¹ x)) = coneOp (G.ρ γ p) (fun y => G.tr (q + 1) γ (w (G.ρ γ⁻¹ y))) x := by
  let L : (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ≃L[ℝ] (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse (G.tr q γ) (G.tr q γ⁻¹)
      (fun m => tr_tr G q γ⁻¹ γ (inv_mul_cancel γ) m)
      (fun m => tr_tr G q γ γ⁻¹ (mul_inv_cancel γ) m)
  have hL : ∀ m, L m = G.tr q γ m := fun m => rfl
  have key : ∀ f : ℝ → (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)),
      L (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..1, L (f t) := by
    intro f
    simp only [intervalIntegral, map_sub, L.integral_comp_comm]
  have hpt : ∀ t : ℝ, G.ρ γ⁻¹ (G.ρ γ p + t • (x - G.ρ γ p)) = p + t • (G.ρ γ⁻¹ x - p) := by
    intro t
    simp [map_add (f := _), map_smul, map_sub, Geo.ρ_inv_apply]
  rw [← hL]
  unfold coneOp
  rw [key]
  congr 1
  funext t
  rw [map_smul]
  beta_reduce
  rw [hpt]
  congr 1
  ext v
  rw [hL, Geo.tr_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Geo.tr_apply]
  congr 2
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Geo.ρ_inv_apply]
  · intro j
    simp

end

theorem UpperTheory.V.Cj.H.poinOp :
    UpperTheory.V.Cj.H.PoinOp := by
  intro Γ V S _ _ _ _ d G hconv q
  classical
  have hD := coneD V (Fin d → ℂ) G.Y G.isOpen hconv
  let f : V → G.Om (q + 1) → S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun p w s x => if x ∈ G.Y then coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) x else 0
  have hwm : ∀ (w : G.Om (q + 1)) (s : S),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ x ∉ G.Y, (w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s x = 0 := fun w => w.2
  have hf : ∀ p ∈ G.Y, ∀ w, f p w ∈ G.Om q := by
    intro p hp w
    refine fun s => ⟨?_, ?_⟩
    · exact ((hD p hp q _ (hwm w s).1).1).congr (fun x hx => if_pos hx)
    · intro x hx
      exact if_neg hx
  let K : V → G.Om (q + 1) → G.Om q := fun p w => if hp : p ∈ G.Y then ⟨f p w, hf p hp w⟩ else 0
  have hK : ∀ p (hp : p ∈ G.Y) w, ((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) = f p w := by
    intro p hp w
    simp [K, hp]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro p hp w hw0
    apply Subtype.ext
    funext s x
    by_cases hx : x ∈ G.Y
    · rw [Geo.dOm_apply G (K p w) s hx, hK p hp w]
      have hclosed : ∀ y ∈ G.Y, extDeriv ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) y = 0 := by
        intro y hy
        have h0 := congrArg
          (fun u : G.Om (q + 1 + 1) => (u : S → V → V [⋀^Fin (q + 1 + 1)]→L[ℝ] (Fin d → ℂ)) s y) hw0
        rw [Geo.dOm_apply G w s hy] at h0
        simpa using h0
      have hloc : extDeriv (f p w s) x =
          extDeriv (coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)) x := by
        rw [← extDerivWithin_univ, ← extDerivWithin_univ]
        apply Filter.EventuallyEq.extDerivWithin_eq_of_mem _ (Set.mem_univ x)
        rw [nhdsWithin_univ]
        exact Filter.eventually_of_mem (G.isOpen.mem_nhds hx) (fun y hy => if_pos hy)
      rw [hloc]
      exact (hD p hp q _ (hwm w s).1).2 hclosed x hx
    · have h1 := ((G.dOm q (K p w)).2 s).2 x hx
      have h2 := (hwm w s).2 x hx
      rw [h1, h2]
  · intro γ p hp w
    have hp' : G.ρ γ p ∈ G.Y := G.maps γ p hp
    apply Subtype.ext
    funext s x
    show G.tr q γ (((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) =
      ((K (G.ρ γ p) (G.act (q + 1) γ w) : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x
    rw [hK p hp, hK _ hp']
    by_cases hx : x ∈ G.Y
    · have hx' : G.ρ γ⁻¹ x ∈ G.Y := G.maps γ⁻¹ x hx
      simp only [f, if_pos hx, if_pos hx']
      exact tr_coneOp G q γ _ p x
    · have hx' : G.ρ γ⁻¹ x ∉ G.Y := by
        intro h
        apply hx
        have h2 := G.maps γ _ h
        have h3 := Geo.ρ_inv_apply G γ⁻¹ x
        rw [inv_inv] at h3
        rwa [h3] at h2
      simp only [f, if_neg hx, if_neg hx', map_zero]
  · intro p hp w hw s C hC hCc
    have h := coneLim V (Fin d → ℂ) G.Y hconv p hp q
      (fun k => ((w k : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)
      (fun C' hC' hC'c => hw s C' hC' hC'c) C hC hCc
    refine h.congr ?_
    filter_upwards with k
    intro x hx
    rw [hK p hp]
    simp [f, hC hx]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SqOrth
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.sqOrth :
    UpperTheory.V.Cj.H.SqOrth := by
  intro E _ _ _ a ha n e he Ξ r q
  obtain ⟨G, hG⟩ := admEx E a Ξ
  obtain ⟨H, hH⟩ := petEx E a ha r
  have hv : ∀ {k : ℕ} {ω : Co Ξ k}, Val (sqSub E a r) ω → ∀ X, ω X ∈ tens Ξ.d (sqSub E a r) :=
    fun h X => mem_tens.2 (h X)
  have hadj := ipAdj E a n e _ (smLie Ξ) (smAdj Ξ r) (tform H G) _ (smForm E a Ξ r H G hH hG)
  have hdef := ipDef E a n e he _ (tform H G) _ (tformPos _ _ H _ G hH.pos hG.pos)
  refine ⟨?_, fun ω h1 h2 h3 => ?_⟩
  · cases q with
    | zero => exact fun ω _ _ h => h
    | succ q =>
      rintro ω h1 h2 ⟨η, hη, rfl⟩
      have h3 := hadj q _ η (hv h1) (hv hη)
      have h4 : del (smAdj Ξ r) e (dCo (smLie Ξ) η) = 0 := h2
      refine ((hdef (q + 1)).2 _ (hv h1)).2 ?_
      rw [h3, h4]
      simp [ip]
  · have h4 := hadj q ω _ (hv h1) (hv h2)
    rw [h3] at h4
    refine ((hdef q).2 _ (hv h2)).2 ?_
    have h5 : ip e (tform H G) ω 0 = 0 := by simp [ip]
    have h6 : ((q : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero q
    exact (mul_eq_zero.1 (h4.symm.trans h5)).resolve_left h6
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.WigSub
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

namespace UpperTheory.V.Cj.H.WignerSubquotient

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private theorem relQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (S : Subalgebra ℂ (A × B)) {n : ℕ}
    (X : Fin n → Fin n → A) (Y : Fin n → Fin n → B) (h : ∀ p q, (X p q, Y p q) ∈ S) (v : ℂ) :
    (Formalism.REAL.qdet X v, Formalism.REAL.qdet Y v) ∈ S := by
  let Z : Fin n → Fin n → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((Formalism.REAL.qdet Z v : S) : A × B).1 = Formalism.REAL.qdet X v := mapQ ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((Formalism.REAL.qdet Z v : S) : A × B).2 = Formalism.REAL.qdet Y v := mapQ ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]
  exact (Formalism.REAL.qdet Z v).2

section

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

private theorem intQ {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R (Formalism.REAL.qdet X v m) = Formalism.REAL.qdet Y v (R m) := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | ∀ m, R (z.1 m) = z.2 (R m)}
      mul_mem' := fun {x y} hx hy m => (hx _).trans (congrArg x.2 (hy m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S X Y h v m

private theorem intQop {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R ((Formalism.REAL.qdet (fun i j => -MulOpposite.op (X i j)) v).unop m) =
      (Formalism.REAL.qdet (fun i j => -MulOpposite.op (Y i j)) v).unop (R m) := by
  let S : Subalgebra ℂ ((Module.End ℂ M)ᵐᵒᵖ × (Module.End ℂ M')ᵐᵒᵖ) :=
    { carrier := {z | ∀ m, R (z.1.unop m) = z.2.unop (R m)}
      mul_mem' := fun {x y} hx hy m => (hy _).trans (congrArg y.2.unop (hx m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S (fun i j => -MulOpposite.op (X i j)) (fun i j => -MulOpposite.op (Y i j))
    (fun p q m => (map_neg R _).trans (congrArg Neg.neg (h p q m))) v m

end

variable {E : Type} [Field E] {a : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

private noncomputable def res (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (N : Submodule ℂ M) (h : ∀ X, ∀ m ∈ N, L X m ∈ N) :
    Lie E a →ₗ[ℝ] Module.End ℂ N where
  toFun X := (L X).restrict (h X)
  map_add' X Y := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_add L X Y) m.1)
  map_smul' c X := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_smul L c X) m.1)

private theorem res_hom {L : Lie E a →ₗ[ℝ] Module.End ℂ M} (hL : IsLieHom L) (N : Submodule ℂ M)
    (h : ∀ X, ∀ m ∈ N, L X m ∈ N) : IsLieHom (res L N h) :=
  fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hL X Y) m.1)

private theorem res_dCo {L : Lie E a →ₗ[ℝ] Module.End ℂ M} {N : Submodule ℂ M} {L' : Lie E a →ₗ[ℝ] Module.End ℂ N}
    (h : ∀ X m, (L' X m : M) = L X m) {q : ℕ} (ω' : Herm E a [⋀^Fin q]→ₗ[ℝ] N) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M)
    (hω : ∀ Y, (ω' Y : M) = ω Y) (Y : Fin (q + 1) → Herm E a) : (dCo L' ω' Y : M) = dCo L ω Y := by
  rw [dCo_apply, dCo_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hω, ← h]
  exact map_zsmul N.subtype _ _

end UpperTheory.V.Cj.H.WignerSubquotient

open UpperTheory.V.Cj.H.WignerSubquotient in
theorem UpperTheory.V.Cj.H.wigSub :
    UpperTheory.V.Cj.H.WigSub := by
  intro E _ _ _ a M _ _ _ _ LA LB hA hB hAB N sA sB τ x z hz
  subst hz
  refine ⟨?_, fun q ω h1 h2 hN => ?_⟩
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a M LA LB hA hB hAB τ x
    exact (wigHom E a M (LA + LB) α _ p1 p2).1
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a N (res LA N sA) (res LB N sB) (res_hom hA N sA) (res_hom hB N sB)
      (fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hAB X Y) m.1)) τ x
    let ω' : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] N :=
      { toFun := fun Y => ⟨ω Y, hN Y⟩
        map_update_add' := fun Y i u v => Subtype.ext (ω.map_update_add Y i u v)
        map_update_smul' := fun Y i c u => Subtype.ext (ω.map_update_smul Y i c u)
        map_eq_zero_of_eq' := fun Y i j e hij => Subtype.ext (ω.map_eq_zero_of_eq Y e hij) }
    have hL : ∀ X (m : N), ((res LA N sA + res LB N sB) X m : M) = (LA + LB) X m := fun _ _ => rfl
    obtain ⟨η, hη⟩ := (wigHom E a N (res LA N sA + res LB N sB) α _ p1 p2).2 q ω'
      (fun Z hZ Y => Subtype.ext ((h1 Z hZ Y).trans
        (Submodule.coe_sum N (fun i => ω' (Function.update Y i (brH Z hZ (Y i)))) Finset.univ).symm))
      (AlternatingMap.ext fun Y => Subtype.ext ((res_dCo hL ω' ω (fun _ => rfl) Y).trans (by rw [h2]; rfl)))
    refine ⟨(N.subtype.restrictScalars ℝ).compAlternatingMap η, fun Y => (η Y).2, fun Y => ?_⟩
    rw [← res_dCo hL η _ (fun _ => rfl) Y, hη, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub]
    exact congrArg₂ (· - ·) (intQ N.subtype _ (eL LA τ) (fun _ _ _ => rfl) x (ω' Y))
      (intQop N.subtype _ (eL LB τ) (fun _ _ _ => rfl) x (ω' Y))
end

