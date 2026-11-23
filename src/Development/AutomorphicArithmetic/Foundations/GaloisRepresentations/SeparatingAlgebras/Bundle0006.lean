module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.AlgCPf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.algC_pf :
    UpperTheory.Gal.Gen.Alg → UpperTheory.Gal.Gen.AlgC := by
  intro hA l _ ι H _ _ hp P hP hcard
  let P' : Submodule (Qbar l) (H → Qbar l) :=
    { carrier := {f | (fun h => ι (f h)) ∈ P}
      zero_mem' := by
        show (fun h => ι ((0 : H → Qbar l) h)) ∈ P
        convert P.zero_mem using 1
        funext h
        simp
      add_mem' := by
        intro a b ha hb
        show (fun h => ι ((a + b) h)) ∈ P
        convert P.add_mem ha hb using 1
        funext h
        simp
      smul_mem' := by
        intro r a ha
        show (fun h => ι ((r • a) h)) ∈ P
        convert P.smul_mem (ι r) ha using 1
        funext h
        simp }
  let j : P ≃+ P' :=
    { toFun := fun c => ⟨fun h => ι.symm (c.1 h), by
        show (fun h => ι (ι.symm (c.1 h))) ∈ P
        simpa using c.2⟩
      invFun := fun f => ⟨fun h => ι (f.1 h), f.2⟩
      left_inv := by
        intro c
        ext h
        simp
      right_inv := by
        intro f
        ext h
        simp
      map_add' := by
        intro a b
        ext h
        simp }
  have hrank : Module.rank ℂ P = Module.rank (Qbar l) P' := by
    refine rank_eq_of_equiv_equiv (fun z => ι.symm z) j ι.symm.bijective ?_
    intro r m
    ext h
    change ι.symm (r * m.1 h) = ι.symm r * ι.symm (m.1 h)
    exact map_mul ι.symm r (m.1 h)
  have hfin : Module.finrank ℂ P = Module.finrank (Qbar l) P' := by
    unfold Module.finrank
    rw [hrank]
  have hinv : ∀ c ∈ P', ∀ g : H, (fun h => c (h * g)) ∈ P' := by
    intro c hc g
    exact hP _ hc g
  obtain ⟨c, hc, hbound⟩ := hA (Qbar l) l H hp P' hinv (hfin ▸ hcard)
  refine ⟨fun h => ι (c h), hc, ?_⟩
  intro h
  simpa using hbound h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Combine
section
noncomputable section

open GlobalTheory.Cong MvPolynomial

namespace UpperTheory.Gal.Gen

variable {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type}

private theorem polyApprox_cut {η : J → k} {T : Set (J → k)} {Q : MvPolynomial J ℤ} (hQ : aeval η Q ≠ 0)
    (h : PolyApprox η T) : PolyApprox η {x | x ∈ T ∧ aeval x Q ≠ 0} := by
  classical
  intro ε hε
  have hq : 0 < ‖aeval η Q‖ := norm_pos_iff.2 hQ
  obtain ⟨s, c, hs, hc⟩ := h (ε * ‖aeval η Q‖) (mul_pos hε hq)
  refine ⟨s.filter (fun x => aeval x Q ≠ 0), fun x => c x * aeval x Q / aeval η Q, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    exact ⟨hs hx.1, hx.2⟩
  · intro P
    have e1 : ∑ x ∈ s.filter (fun x => aeval x Q ≠ 0), c x * aeval x Q / aeval η Q * aeval x P
        = (∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q := by
      rw [Finset.sum_filter_of_ne, Finset.sum_div]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [map_mul]
        ring
      · intro x _ hx hQx
        apply hx
        simp [hQx]
    rw [e1]
    have e2 : aeval η P - (∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q
        = (aeval η (P * Q) - ∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q := by
      rw [map_mul, sub_div, mul_div_assoc, div_self hQ, mul_one]
    rw [e2, norm_div, div_le_iff₀ hq]
    exact hc (P * Q)

private theorem polyApprox_trans {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hS : ∀ η ∈ S, PolyApprox η T) : PolyApprox θ T := by
  classical
  intro ε hε
  obtain ⟨s, c, hs, hc⟩ := h (ε / 2) (by positivity)
  have hM0 : 0 ≤ ∑ η ∈ s, ‖c η‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hε2 : 0 < ε / (2 * (∑ η ∈ s, ‖c η‖ + 1)) := by positivity
  have hT : ∀ η ∈ S, ∃ (t : Finset (J → k)) (d : (J → k) → k), (↑t : Set (J → k)) ⊆ T ∧
      ∀ P : MvPolynomial J ℤ, ‖aeval η P - ∑ ζ ∈ t, d ζ * aeval ζ P‖
        ≤ ε / (2 * (∑ η ∈ s, ‖c η‖ + 1)) :=
    fun η hη => hS η hη _ hε2
  choose! t d ht hd using hT
  refine ⟨s.biUnion t, fun ζ => ∑ η ∈ s, c η * (if ζ ∈ t η then d η ζ else 0), ?_, ?_⟩
  · intro ζ hζ
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop] at hζ
    obtain ⟨η, hη, hζ⟩ := hζ
    exact ht η (hs hη) hζ
  · intro P
    have hsum : ∑ ζ ∈ s.biUnion t, (∑ η ∈ s, c η * (if ζ ∈ t η then d η ζ else 0)) * aeval ζ P
        = ∑ η ∈ s, c η * ∑ ζ ∈ t η, d η ζ * aeval ζ P := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun η hη => ?_
      rw [Finset.mul_sum]
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.subset_biUnion_of_mem t hη)
      · intro ζ hζ
        rw [if_neg (Finset.mem_sdiff.1 hζ).2]
        ring
      · intro ζ hζ
        rw [if_pos hζ]
        ring
    rw [hsum]
    have split : aeval θ P - ∑ η ∈ s, c η * ∑ ζ ∈ t η, d η ζ * aeval ζ P
        = (aeval θ P - ∑ η ∈ s, c η * aeval η P)
          + ∑ η ∈ s, c η * (aeval η P - ∑ ζ ∈ t η, d η ζ * aeval ζ P) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [split]
    calc _ ≤ ‖aeval θ P - ∑ η ∈ s, c η * aeval η P‖
          + ‖∑ η ∈ s, c η * (aeval η P - ∑ ζ ∈ t η, d η ζ * aeval ζ P)‖ := norm_add_le _ _
      _ ≤ ε / 2 + ∑ η ∈ s, ‖c η‖ * (ε / (2 * (∑ η ∈ s, ‖c η‖ + 1))) := by
          gcongr
          · exact hc P
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun η hη => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hd η (hs hη) P) (norm_nonneg _)
      _ ≤ ε := by
          rw [← Finset.sum_mul]
          generalize ∑ η ∈ s, ‖c η‖ = M at hM0 ⊢
          have h1 : M / (M + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          have h2 : M * (ε / (2 * (M + 1))) = ε / 2 * (M / (M + 1)) := by
            field_simp
          have h3 : ε / 2 * (M / (M + 1)) ≤ ε / 2 := mul_le_of_le_one_right (by positivity) h1
          linarith

theorem combine_pf : Combine := by
  intro k _ _ J θ S T Q hθ h
  exact polyApprox_trans hθ fun η hη => polyApprox_cut (h η hη).1 (h η hη).2

end UpperTheory.Gal.Gen

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CountCore
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private theorem sq_sum_of_subsingleton {G : Type} (F : Finset G) (hF : ∀ g ∈ F, ∀ g' ∈ F, g = g') (t : G → ℂ) :
    ‖∑ g ∈ F, t g‖ ^ 2 = ∑ g ∈ F, ‖t g‖ ^ 2 := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
  · simp
  · have e : F = {g} := Finset.eq_singleton_iff_unique_mem.2 ⟨hg, fun g' h' => hF _ h' _ hg⟩
    subst e
    simp

private theorem fibre_sum {G Y : Type} [Fintype Y] [DecidableEq Y] (S : Finset G) (π : G → Y)
    (hπ : ∀ g ∈ S, ∀ g' ∈ S, π g = π g' → g = g') (t : G → ℂ) :
    ∑ y, ‖∑ g ∈ S with π g = y, t g‖ ^ 2 = ∑ g ∈ S, ‖t g‖ ^ 2 := by
  refine Eq.trans ?_ (Finset.sum_fiberwise S π fun g => ‖t g‖ ^ 2)
  refine Finset.sum_congr rfl fun y _ => sq_sum_of_subsingleton _ (fun g hg g' hg' => ?_) t
  rw [Finset.mem_filter] at hg hg'
  exact hπ g hg.1 g' hg'.1 (hg.2.trans hg'.2.symm)

private noncomputable def mat {G X : Type} [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) : Matrix (X × Fin d) (X × Fin d) ℂ :=
  fun r s => ∑ g ∈ S with π r.1 g = s.1, t g * m r.1 g r.2 s.2

private theorem mat_mulVec {G X : Type} [Fintype X] [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) (u : X × Fin d → ℂ) (y : X) (i : Fin d) :
    (mat S π t m).mulVec u (y, i) = ∑ g ∈ S, t g * ∑ j, m y g i j * u (π y g, j) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mat, Finset.sum_mul]
  refine Eq.trans ?_ (Finset.sum_fiberwise S (π y) _)
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [(Finset.mem_filter.1 hg).2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

private theorem mat_hs {G X : Type} [Fintype X] [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) (M₀ : ℝ) (hm : ∀ y g i j, ‖m y g i j‖ ≤ M₀)
    (hπ : ∀ y, ∀ g ∈ S, ∀ g' ∈ S, π y g = π y g' → g = g') :
    ∑ r, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ ((d : ℝ) ^ 2 * M₀ ^ 2) * Fintype.card X * ∑ g ∈ S, ‖t g‖ ^ 2 := by
  have hrow : ∀ r : X × Fin d, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ (d : ℝ) * (M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2) := by
    intro r
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hj : ∀ j : Fin d, ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 ≤ M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2 := by
      intro j
      have e := fibre_sum S (π r.1) (hπ r.1) (fun g => t g * m r.1 g r.2 j)
      calc ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 = ∑ g ∈ S, ‖t g * m r.1 g r.2 j‖ ^ 2 := e
        _ ≤ ∑ g ∈ S, M₀ ^ 2 * ‖t g‖ ^ 2 := Finset.sum_le_sum fun g _ => by
            rw [norm_mul, mul_pow, mul_comm]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hm _ _ _ _) 2) (by positivity)
        _ = _ := (Finset.mul_sum _ _ _).symm
    calc ∑ j : Fin d, ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 ≤ ∑ j : Fin d, M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  calc ∑ r, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ ∑ r : X × Fin d, (d : ℝ) * (M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2) :=
        Finset.sum_le_sum fun r _ => hrow r
    _ = _ := by
      simp [Fintype.card_prod]
      ring

private theorem sep_eq {G : Type} [Group G] (R N C : Subgroup G) (hN : N.Normal) {z γ γ' x x' c c' : G}
    (hγ : γ ∈ R) (hγ' : γ' ∈ R) (hx : x ∈ N) (hx' : x' ∈ N) (hc : c ∈ C) (hc' : c' ∈ C) :
    ∃ Γ ∈ R, ∃ ξ ∈ N, ∃ k ∈ C, γ' * z * x' * c' = Γ * (γ * z * x * c) * ξ * k :=
  ⟨γ' * γ⁻¹, R.mul_mem hγ' (R.inv_mem hγ), c⁻¹ * (x⁻¹ * x') * c,
    hN.conj_mem' _ (N.mul_mem (N.inv_mem hx) hx') c, c⁻¹ * c', C.mul_mem (C.inv_mem hc) hc', by group⟩

private theorem form_val {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {W : Wt E a} {C : Subgroup (UA E a)}
    {f : algForms W} (hf : f ∈ fixedBy W C) {d : ℕ} (B : Module.Basis (Fin d) ℂ W.Sp) {γ q x c : UA E a}
    (hγ : γ ∈ ratU E a) (hx : x ∈ infU E a) (hc : c ∈ C) (v : W.Sp) :
    f.1 v (γ * q * x * c) = ∑ j, B.repr (W.rep ⟨x, hx⟩ v) j * f.1 (B j) q := by
  have h1 : f.1 v (γ * q * x * c) = f.1 (W.rep ⟨x, hx⟩ v) q := by
    rw [mem_fixedBy.1 hf c hc v, mul_assoc γ q x, (f.2.1 v).left γ hγ, f.2.2 ⟨x, hx⟩ v]
    rfl
  refine h1.trans ?_
  have h2 := congrFun (congrArg f.1 (B.sum_repr (W.rep ⟨x, hx⟩ v))) q
  refine h2.symm.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.countCore_pf :
    UpperTheory.Gal.Gen.HS → UpperTheory.Gal.Gen.WBound → UpperTheory.Gal.Gen.CountCore := by
  classical
  intro hHS hWB E _ _ _ a W
  let d := Module.finrank ℂ W.Sp
  let B : Module.Basis (Fin d) ℂ W.Sp := Module.finBasis ℂ W.Sp
  obtain ⟨M₀, hM₀⟩ := hWB E a W d B
  refine ⟨(d : ℝ) ^ 2 * M₀ ^ 2, by positivity, ?_⟩
  intro C X _ p hcov h hsep V hVC hV
  choose γ hγ π ξ hξ c hc hdec using fun (y : X) (g : UA E a) => hcov (p y * g)
  let η : X → UA E a → infU E a := fun y g => ⟨ξ y g, hξ y g⟩
  let m : X → UA E a → Fin d → Fin d → ℂ := fun y g i j => B.repr (W.rep (η y g) (B i)) j
  let ev : V →ₗ[ℂ] (X × Fin d → ℂ) :=
    { toFun := fun f q => f.1.1 (B q.2) (p q.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf0
    have hz : ∀ j y, f.1.1 (B j) (p y) = 0 := fun j y => congrFun hf0 (y, j)
    refine Subtype.ext (Subtype.ext (LinearMap.ext fun v => funext fun g => ?_))
    obtain ⟨γ₀, hγ₀, y, x, hx, c₀, hc₀, rfl⟩ := hcov g
    rw [form_val (hVC f.2) B hγ₀ hx hc₀ v]
    exact Finset.sum_eq_zero fun j _ => by rw [hz, mul_zero]
  have hfix : ∀ f : V, (mat h.support π h m).mulVec (ev f) = ev f := by
    intro f
    funext ⟨y, i⟩
    rw [mat_mulVec]
    have hop := congrFun (hV f.1 f.2 (B i)) (p y)
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul] at hop
    refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) hop
    rw [hdec y g, form_val (hVC f.2) B (hγ y g) (hξ y g) (hc y g) (B i)]
    rfl
  have hπ : ∀ y, ∀ g ∈ h.support, ∀ g' ∈ h.support, π y g = π y g' → g = g' := by
    intro y g hg g' hg' e
    obtain ⟨Γ, hΓ, ξ', hξ', k, hk, e'⟩ := sep_eq (ratU E a) (infU E a) C inferInstance (z := p (π y g))
      (hγ y g) (hγ y g') (hξ y g) (hξ y g') (hc y g) (hc y g')
    refine hsep y g hg g' hg' Γ hΓ ξ' hξ' k hk ?_
    have e1 := hdec y g'
    rw [← e] at e1
    rw [e1, e', ← hdec y g]
  have hfd : FiniteDimensional ℂ V := FiniteDimensional.of_injective ev hinj
  refine ⟨hfd, ?_⟩
  have h1 := hHS (X × Fin d) (mat h.support π h m) (LinearMap.range ev) (by rintro _ ⟨f, rfl⟩; exact hfix f)
  rw [LinearMap.finrank_range_of_inj hinj] at h1
  exact h1.trans (mat_hs h.support π h m M₀ (fun y g i j => hM₀ (η y g) i j) hπ)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CountGen
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem finset_sup_finrank_le {ι M : Type*} [AddCommGroup M] [Module ℂ M] (S : Finset ι)
    (A : ι → Submodule ℂ M) (r : ℝ)
    (h : ∀ i ∈ S, FiniteDimensional ℂ (A i) ∧ (Module.finrank ℂ (A i) : ℝ) ≤ r) :
    FiniteDimensional ℂ (S.sup A : Submodule ℂ M) ∧
      (Module.finrank ℂ (S.sup A : Submodule ℂ M) : ℝ) ≤ S.card * r := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact ⟨inferInstance, by simp⟩
  | insert i S hi ih =>
    obtain ⟨hfd, hle⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨hfi, hli⟩ := h i (Finset.mem_insert_self i S)
    rw [Finset.sup_insert, Finset.card_insert_of_notMem hi]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    have h1 : (Module.finrank ℂ (A i ⊔ S.sup A : Submodule ℂ M) : ℝ) ≤
        (Module.finrank ℂ (A i) : ℝ) + Module.finrank ℂ (S.sup A : Submodule ℂ M) := by
      exact_mod_cast Submodule.finrank_add_le_finrank_add_finrank (A i) (S.sup A)
    push_cast
    linarith

private theorem part_le_sup {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Wt E a)
    (C : Subgroup (UA E a)) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ) :
    part W C (fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) ≤
      S.sup fun w => part W C fun U => ¬ GenAt w (Φ w) U := by
  refine iSup₂_le fun π hπ => ?_
  push_neg at hπ
  obtain ⟨w, hw, hg⟩ := hπ
  refine le_trans ?_ (Finset.le_sup (f := fun w => part W C fun U => ¬ GenAt w (Φ w) U) hw)
  exact le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : ¬ GenAt w (Φ w) π.V) => π.finPart W ⊓ fixedBy W C) π hg le_rfl

theorem UpperTheory.Gal.Gen.countGen_pf :
    UpperTheory.Gal.Gen.Count → UpperTheory.Gal.Gen.NeglAt → UpperTheory.Gal.Gen.CountGen := by
  classical
  intro hC hN E _ _ _ a w₀ hw₀ K hK J hJ W S Φ hD
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (2 * ((S.card : ℝ) + 1)) := ⟨_, rfl⟩
  have hc : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have hεpos : 0 < ε := by rw [hε]; positivity
  have key : ∀ w, ∃ n₀ : ℕ, w ∈ S → ∀ n, n₀ ≤ n →
      FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧
      (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤
        ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨n₀, h⟩ := hC E a w₀ hw₀ K hK J hJ W _
        (hN E a K w₀ w (hD.split w hw) (hD.apart w hw) (hD.hyp w hw) (Φ w) (hD.ne w hw)) ε hεpos
      exact ⟨n₀, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose n₀ hn₀ using key
  refine ⟨S.sup n₀, ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = S.sup n₀ := ⟨_, rfl⟩
  rw [← hn]
  have hall : ∀ w ∈ S, FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧
      (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤
        ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := fun w hw =>
    hn₀ w hw n (hn ▸ Finset.le_sup (f := n₀) hw)
  obtain ⟨hfd, hle⟩ := finset_sup_finrank_le S
    (fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) _ hall
  have hsub := part_le_sup W (lev K w₀ (J n)) S Φ
  refine ⟨Submodule.finiteDimensional_of_le hsub, ?_⟩
  have hmono := Submodule.finrank_mono hsub
  have hmono' : (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤
      Module.finrank ℂ (S.sup fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U :
        Submodule ℂ (algForms W)) := by
    exact_mod_cast hmono
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := ⟨_, rfl⟩
  rw [← hNdef] at hle
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hfin : 2 * ((S.card : ℝ) * (ε * N)) ≤ N := by
    have h2 : 2 * ((S.card : ℝ) * (ε * N)) = (S.card : ℝ) / ((S.card : ℝ) + 1) * N := by
      rw [hε]; field_simp
    rw [h2]
    have h3 : (S.card : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hc]; linarith
    nlinarith
  have : (2 * Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤
      Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    rw [← hNdef]; linarith
  exact_mod_cast this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CoverPf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.cover_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.LocComm → UpperTheory.Gal.Gen.Cover := by
  intro hL hC E _ _ _ a w₀ hw K hK J hJ
  obtain ⟨hlev, hmem, -, -, hsurj, -⟩ := hL E a w₀ hw K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have ho : IsOpen (((lev K w₀ (J 0)).subgroupOf (finU (E := E) (n := a)) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a))) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨N, hN, h1, hNC⟩ := hlev.isOpen
    refine Filter.mem_of_superset ((hN.preimage continuous_subtype_val).mem_nhds h1) fun y hy => ?_
    exact Subgroup.mem_subgroupOf.2 (hNC ⟨hy, y.2⟩)
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E a _ ho
  refine ⟨S, fun n => ?_⟩
  choose R hR using fun q : J 0 => (hsurj q.1)
  refine ⟨fun q => R q.out, fun q => ⟨(hR _).1, (hR _).2 ▸ q.out.2⟩, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  obtain ⟨k₀, hk₀, j, hj, hjJ, hkeq⟩ := (hmem _).1 (Subgroup.mem_subgroupOf.1 hk)
  have hcomm : j * k₀ = k₀ * j := hC E a w₀ j k₀ hj (hK.one k₀ hk₀)
  let q : J 0 ⧸ (J n).subgroupOf (J 0) := QuotientGroup.mk ⟨cLoc w₀ j, hjJ⟩
  have hq : (q.out)⁻¹ * ⟨cLoc w₀ j, hjJ⟩ ∈ (J n).subgroupOf (J 0) :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
  have hq' : (cLoc w₀ (R q.out))⁻¹ * cLoc w₀ j ∈ J n := by
    have := Subgroup.mem_subgroupOf.1 hq
    rw [(hR q.out).2]
    simpa using this
  have hr : R q.out ∈ locU a w₀ := (hR _).1
  refine ⟨γ, hγ, (⟨s, hs⟩, q), x, hx, (R q.out)⁻¹ * j * k₀, ?_, ?_⟩
  · refine mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hr) hj, ?_⟩)) (Subgroup.mem_sup_left hk₀)
    change cLoc w₀ ((R q.out)⁻¹ * j) ∈ J n
    rwa [map_mul, map_inv]
  · have hxr : R q.out * x = x * R q.out := fin_mul_inf (hlev.fin (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hr, by
      change cLoc w₀ (R q.out) ∈ J 0
      rw [(hR q.out).2]
      exact q.out.2⟩))) hx
    show γ * s * x * (k : UA E a) = γ * (s * R q.out) * x * ((R q.out)⁻¹ * j * k₀)
    rw [hkeq, ← hcomm]
    have e : γ * (s * R q.out) * x * ((R q.out)⁻¹ * j * k₀) = γ * s * (R q.out * x) * ((R q.out)⁻¹ * j * k₀) := by
      group
    rw [e, hxr]
    group
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LocComm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.locComm_pf :
    UpperTheory.Gal.Gen.LocComm := by
  intro E _ _ _ a w₀ x g hx hg
  obtain ⟨hxf, hxa⟩ := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  have hxi : cInf x = 1 := hxf
  refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)
  · change cInf (x * g) = cInf (g * x)
    rw [map_mul, map_mul, hxi, one_mul, mul_one]
  · change cLoc u (x * g) = cLoc u (g * x)
    rw [map_mul, map_mul]
    by_cases hu : Apart u w₀
    · rw [hxa u hu, one_mul, mul_one]
    · rw [hg u hu, one_mul, mul_one]
end

